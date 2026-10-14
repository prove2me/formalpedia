-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2137
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:45:43.916388+00:00
-- url     : https://prove2.me/submissions/af219df1-cc32-428e-b377-be0ccb6ec97b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 384172661 ≤ n < 384352517 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 384173911 1250 384172661 384172667
    0x9080303190207140c120f19050a021503010f080102090307030201030c09030f0b0109050f04051b180412030b120a030f0e060304261c09030c081206040506010519 71
    0x2641c21200d80006080616070340e0f6141d0000d03980703c0307103e00d96889038500c40028a440d01182c8400d0030a000203150701d0750042181501c40040220002c22060905a81428000140000ca2070168010a107075801c00d01908481c1040d002070158a5020310326550109242d1014405c039021014000c1c0240002032466004401400b00005201700f004801940040011304842910b2141c91040c1510354103981007050300400c030b0390300414808140c000503051001280f0042030740300032030f082c116454401c0c0c15110007140ca401100b80c1d441d20541846e20400003802f9007458003d248648a42d42404100030010800c03c18810700342d80c1e02c60f582c1020840301e0007c1c0c011103002502e0070b181c0c148020b41010f070b1000250f1603042101d055030180700100890114591588426070340700c941d0b011050404a1601c84c85124a084603181805966503813445024540949500075049a100700030554914011003c444039140903a070150081c3e0505012511031740c0620103817410074410340300e50346195888002c00c07 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 384175161 1250 384173911 384173941
    0x1c03020705070e0c0c0706030207030215061e040204080a0602030f010911031306060f030302012324120d0c03030501050a0617071404090614060c070b1803060f04030f09080303 77
    0x83c0740d01c0d42040122185178030b01840658020040d9031001038460f4003c1c02e000e402c0035400c1044c1c00c0c800c2155000c200c05641d982c240c40811100a03a2100f0800d254180814000d20568000b0099031107101c40c42420840c95800a611864004122800756642ea2114200b9140c004854402c507800074400206c105140030f910155141c0281d1011034069540c4405207490306c0950000c0d00140d44a820f42241814400c0c220501c021219030184014907041031440c07800c00c0203c1011001704928414000280d40310358241c40c01880070000e0359a05a02c449000d00b1418028038228082401d00000042919003600300310212107568803000c10310b2550350040c0280060050400040c4040001c40c900000922409003014014801c800950641403200300c00c4410b40f1000500c0c0701d030004011202c80090085038200403a00800203a80c0c864950103800c0003000b0341070705035680510a075420001000c00b080900c60040380691591980c1c015030038811a5800c0241c018901aa8010070220b44020900702038 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 384176411 1250 384175161 384175171
    0x60a02031207050d110405190501020c0607020303040816081e1c170103030203180402090a030f05100f1d010e0d1d0d11090709080c010e1309051c03020705070e 70
    0x3003c0e107040141c0d80b400040300c2800410360320030400420706000609140e954421140d10082c4590203803407034400000c3d03507400105411070180308003103940011900c00f0000c0c0c80203014440306407014003d48122009030907619118000852185001e40600100c041c41c03030140d00800d000c05400e44200e11070501d81020000c45004d4204501c8015016500d003603803404501941c4251301940c0d6451444021146605020070454411441007250100d81d90742c50040008580e40a002c9001d142600d04042d8103201d48950440c0007241009540304a900752075200c500e08040700c0320b40d1129042e11703800440c00ca402d1510324114030b5105000045e5200d00480102c02903007640d0300040d842c44e00980104003c00380c0010100d80d9545405e00d810a1071074080d40851388006a80b805840d070701d2402907560355440c502c106050602400e4401d00c24140ca03412007400c0300040700c04051060180714540640e0f100b0300d1085c2c01304c14103110000c04000701e200c0e0086600c4207401c10300500c101401e02001c8207007103c021705 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 384177661 1250 384176411 384176417
    0x1005100509011b0b1302030607091d0c04050a24030c050304020f060f0c010e010507051201210f051014010b07030509120105040f152a020114010f060e060a02031207 72
    0x164800000c00660707150f44181000c101700880c845252060510f810070281c240401e012403144140243c60f01c0e082d001817202c841605154960702c490f08951402e21803504100c0c4c000703e180c20041030550821070b4120044000c40404c82c0f800303c003450114100c484001170390000840c1000800c0140c0390070b402102d0000001400c1c0b0b440e0600c48900c0c1f00555000c440c0a0115944600107442414000c1c0314856108a290402e240340400c0c07804a148060014080c90207800303641c1108100c110342076810380542a610800030b000071107490a20341d0361420a500446541400d140c0b40001c5078604d820428100c900c0e0001d5036040030043d40c0c0648080d000f803103980f070b0006036040790908400002d010713050240d8000c81c0250b00d0003140b802c005002c1440c07200603208003030800344014412824103048283c00440d4132241489080f90b04000c82c09070000003400075070300c4d4521300082244003400621400b2182c0703607200c0c0401e0300403d8007070280070b024040c1500056041130045a5441285004003603000340070345 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 384178911 1250 384177661 384177707
    0x12070e0904021314010f05091501020c0909070305030403033c0c0f020402220b0f030f070e0904111003090c0b0901112a0103140c0d091505100510050901 67
    0x4032890484d8a02680701c071a201180f1507040102d401c096680b5504080c041040c03520203801d52001035543c984c1103904a00552001002a00b07011043c40701c1ca02640d400016607036542d81d07a00340100724602d44002c4091803200440c40580d16602d00710051702d640c0168a0340845030460401c1603404142000003510700301d0b90086480016680c41c402028500d4915024220f100c08000303482d58044610740040000c48170401c01d102c9000002c000340c82d486003412508407020351390410b007152045405885241c000f80d911003071204025404607644c90010342540e801c1c0700d205d032400044041c1c5610203005042c080a5020520056050500521034100b06050030070b1002c501c1c20180f0300d0000000c800c06580250032480300400685503180d544074000919042c040f0308103210580310b0301c4802402c410141e842c005985101c0250039040700745500d4000c0c9050b4402000c11656901420003100c50ba488913a83c44004100e510300b141a109880348107503176040c140380d9031600650300c041c041c000d480f100100d21 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 384180161 1250 384178911 384178931
    0x90504051306020c330f04080d05060609091005011d010c08091207080105060108070c051504020f0301060f05130c080f060105040b040305251404050c04150512070e09040213 76
    0x6000c5d0340b0666401d44400700e0003002100c0c2c019440500500420f030114850b00501010544140a49481c40444200011103464180005100303105188440e5045040c0c0800c001007850302900940850380c0c20380302c0307100245164020a9080a401070141c0c08100400d02440200d0180340c0500192000501005100301c40c2c80e462918100013548139070038583d101c404100c019688010a160820310a0a140204062315030f51651210b40c40010400d0b4498500c0002e0706559469801a9152001400811503191542c21804d000c1d41d0703600425020740e114001214103180c90380300320f8400b5203140d529140349403180b00c000d01208001420203410000d00307100114142081500810085205000074a9000010503000380001e00103020710100d0207101000700018240c0c0e03510b84550560840e8006200e40d120030589002d40104c0c2c0111010801c41210482c03403680000013009038803d000302640090351081c0c4100c03844c3d96030445940c0c10404113408a001818107810008814401d004046860045 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 384181411 1250 384180161 384180193
    0x40803180d02180106020c04090c0501260c1308030c03031f080111041502010e0714120d0302040815100509131403030105041d030403020f0a03080403060b01090504051306020c 77
    0x42c040d03003d120f80903100104103103501044090f0103034a003a02c040c420305000741c40310051100107200341e40c1440402d40881100b403d50304950010400c803850541c11600300033500703162640141001c023224190401d004143d50f8800800d403145c1022180c0158516510144100c0c1c020710402c20141190141c0e03140030a814500b03004045d60101d081881e60b4950f4900401c0d40c100f038109042d60015a490082a04001034004c9030b4074081d10603141841c0028600700c00403a0342881d1800c0038250901a40042060082c0d02d46c00820407124964100c951b91722101d641000300c080c007a81c0c400500d90740c03001e08210b01e040021010f0741c40580d180f42c003804080329407501c1080e202144c1094086820000060086282c1481100314008201179190700140d411110b841c0d0720300c16400042e104014008811440e55034102e01c00014507071211181e46c45a42da840c162000d0309100340071350f000c20380c0c0c4140406c0e035041034402c25105205840290f0351181860311240020741c8804c1e000002c40c01110750b000c0d0807150b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 384182661 1250 384181411 384181429
    0x126070e040809011d010c14030d0e01020901090b04080a021c12021501080109050601051e10030603110d0803070f0203221d010e0403051312030320040803180d02 71
    0x2000e610b000780c1e0b0311000c900040201c449907541d2440c003d1001d038800f100381d0b0b106030040c00143d80040346490705d581c62240149103025942e00103040500303001c06404000c8040d000b03010092400c1c1c854070810f030b0712540820002d020354002c0200f258021038010000d490000b491125881045001101c01035140d1121a01c00d410000740c4400b590000c0d0465a891810f50b07980380c01010444004c01076100aa0340309619040c0601c01d00780314440064000214034401a04020451401008540e0740320b0546409400391035148415207107101c80c911075032418203000501c010150340c4544900c0c81c660b10310000b175842d03d540f84401c504503c802c1c40129007c071809800c00115144401e468000345180178030b58500b40c1e610102440e07200d0401d82c01003090015110705590450303854146a070300c41000707005040d00b40c0380716800140c10303901e1001e50405044c0c055200d400d800242d420016403d5641d98100a40d0344903a00c0f070006140e0040248918a14084111017007198009158010200d200c2c0c0000b00702c00 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 384183911 1250 384182661 384182663
    0x1909111e07020a05060334021911031f11071502070c09021b10060302100f170a0b01030b010f020c060903101125030e10031e020a12050126070e04 64
    0x907249042547d07090101c41e4800441081501c480703c90021301c05002522020b0340548240100001d001c40c108100d01c1c0c0c44c02d01840d1308080d0490741358560841e1803428040841510b240c4243c41c0907014000e1814000840303555a0300068002d540400d0042440001e61100000b95600c00096401240307440e480d0009100c010b130f030344d082291002e0300c481c03c1602704500300e044004810300d490401c00060311200c01c1000d0b800180e040610803131603040b6094034280d80c040c0215840c1e0281404200002c1181c1d8000b4807000b03004e90b410001c4442103c010346e81d0a2040185001507400480c4103140ca151403001800f11200c00f805582c19850200c0000d01925540c03035003281c0c500c0000c2240c0000781d0511411180180421001034a510040c0e14040c2607207942ca01719502991340780400500c854000c0d0480c90144d1f02e0503602c06040072100c440d80000790491854040041c0761200f154080482d54090076050b10002a0307e01030079000804c240580491550b03080d0110b000700c000004840c040302807550320032 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 384185161 1250 384183911 384183931
    0x503090c0d120e06030411040519020a02010507271e08030c2b0e1306031a0a0e0106080309040c02071d09060c0a0210090507051909111e07020a050603 66
    0x20354540014282c58500c0f01524000c1c1010b0007000045202c0f0403c0000c224410f860000309a15529403810386038510100f40f0b04d400d4000a9110700165055204510556460b81e0315400000c40034000034003961003c103403500303c0c00800010b006100b403e20030500c0c503003c0b106404c46026502e2816500350342100010002e0398001d1508081418050f10350218400b00c41d001d0398404195103003026241d6014000c030f082c000e9808404505d2030500a80c00381e00555000074400c2c0c60804124062008044100d81c4001e04504242c0d828030304d000140103040984d55030402441c2041030090030b0200a0410520ba0401c61103051400245040402e2800104040720307800350b1300b0362503ea46117900d001406007400340c051038100920303d0013030b03404180014800c80f0108041140ca0840c01c1c12803405c0d4007038200503448904c9010740441c0c40410b0300c1d0b000480d040f000d001e201c400d0908150400e207028499800003908641548502c8840340c0703400404002d44010310b001e10321a15803000c107409410840d000011 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 384186411 1250 384185161 384185183
    0x40b0406050c1e03010e1e010b07110a03120e030304051507081b0d091a0f0d09140f06130309120503130605040806280c0908030c060708070810060503090c0d 69
    0x4a483d0101055018482c41081f103540b21012110110035501449009090381010030749004012144400400765100104800e001d80e0b2241040401c14480c00c0e8001d0200da80a90304240d1420040103503412958010f006d02206400400388005030303071008030200c501101c10031481c40c9c0c1c4c00045000c220900064001003c0082a812001d030000c0c481c1d80012001810203429945080c00b0301080329600071100c6c03c9103844115844800005e800003a10051010411901c3c0100090700010740200c00c586c2a412998540c5401281c2055010240b401500003001d6003818486000350380701c20380c1420300c68401c8a1130161000102000d04000b40c1240700040c0c1c00103030800c0440e0040084503000285241104904000700c90500303880100500c240c200b40d40c85c0c00b00e04035071b40e0181000000a05200b0160390303450199680240d25002c049804070040303107420001c03030360080c400e14a081c850380302c00c0a100c2c202400e040c400e850307903000104405034034410402c1c11419915094161640382d403007600c030041 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 384187661 1250 384186411 384186419
    0x7030e030601061403060409021f120f020f0a200703110a06020d021b010306030c030803040c0e0112111c03110f030a090302120c060304080702030c09040b0406050c1e0301 75
    0x4100207042c1e01c81e00c02c111101080860054020040329000f10013164006052800303440801c1024021010b801e0812240070364100c82560170620000d031406400c2e41c01c014944940035028124054004080302840e004d20209500c00d0040c040301000709003c60011010815080d1407510b0018650011a0340c11180d4044034002d00740802544050f0045002030503040c5844140255100c3d440349155406030941e0144001030703402944030340041e5400045858481c0d8490814070b0980e4003c0e24100c0b8002e080d58000504965403541b064165102960140000c8005864801c05800001140d5a001c4528042c0d0400d500d5032802c8258118820345a80d2804203403103100e02e08058005281c1a51a0030802031401482d600010700c0003504e0381282c03100011079182c0b484600c0c210749000c0342030308076100200344003d001c02200904046442102142c006091140920000076019031700204414103080204001510310342181e9880f202111107241003400403c8c000302c00a40443c04c25458400002c0140 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 384188911 1250 384187661 384187663
    0x507080a0c080f2a152d06100309150b15030f040201110607020c0d1e0537110d080d140c040b07080c0f01020d05010801050a0b06030601140d0207030e03 67
    0xb000804801c1803005010828009507196a10b0326901d0086903503240014401082028206074040c171b03410f40c00b404500e0104000d021150050302d42c640304410841c0050001c034442e001c0c1520300ba81c44800108034091040010001c0c10210480c40c0e8091001019011261038100240d4400d480841c1030034800d04041c00090002104425075101d00d400c00301c01c001c80c01d0b4002aa074a0740b80030680ba40d402c4071206080075410032541281c105000058107100e00c003030100010701c0e04401d84281480e1010701070417000c85402c492504610701c1c0324454124108012074031446a00f08035440140c0082c2090302140d55154441d440602c100c080745660751000e4624544101d9681e510149034101c0928050415522040d24021840010200d60f000552001441014440440305101c0c41000790b49030740d41c0760304030340c084c0c002409000025840d240003e425664a03015400ca2400040c0c0502c0c81c45d160040115031441d4094658010040104406211b16a251005001250083d62248041c40d0392200301 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 384190161 1250 384188911 384188947
    0x3020a03051308030112020409060c090302030727092406180917031003080307081b161104111b06090609030306040c1106040b0a15060507080a0c080f 66
    0x80c0c424800b699403441d00083c1c41038110380c1522607500f1203554500c1c45200040250406213030003800142000f0569003810740010024007540c0c421800d4500c3c0ca41c5808199003200505000c002640e85450805404040342d94481c20307005010704002d0340740c003000e040f000d8100c00c0259060300308240d072140104a195103503c40e465602c4900131061000a8440d02e441d040450100f20304c0c0062440000424036850b2610300c100300131640000765079141c0ca040c5801a10041c400c4170f05001407402c1125070f8407030000d100c0880d03d40c84018400000740b49a00d80700c840741800003600c065007050360f560b0a8000030f00b01c200901603841810541c1c20b0309007110800c0702d051180141200d6901d038494400e104038404080b09982e40603400380e03400034800c0d84120084130014a004800c0c0180d0103600180414010000c0140303218600051b03007407081155503403010700580c1c414800c0000145081c80f034000010000300c001c01d030f4049680b03460400da40d041e840d100e0f243e0340b0022800821100008410044030304003561 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 384191411 1250 384190161 384190171
    0x7020a030f090b07060f020408100504050106092714011d0c010306050618040b1c020f0303090a030b0c040324060e0103080a0c0212010513020a12120c050a02060a03020a0305 76
    0x3201c02c80768079048400c840da002d40380300101116150b0803003800100103a4190703001800c0000403a030001c6600d0041ea00100010780b400d95055007005004202392265005100001c070700d02e0b480692a80c1c5503401e0704103603d50103c2c01c4400481c0540580341640e801d008244010302c180003088020b43c10b40390a00e20300442312042d03606160809a04105540e10740059950b00382002500c0c00203900c0200000f40146211505d41d0303446030448009030500d00d154071084000504c26542100900096070405370740c0e0040540d41548000400d00500004514a0f40036410410107081c180c04d0940b03031350780e00004400044203034003101c12110790810100d803070380144401041c032021805000e5040d5100c40456100d0030114400b071100040f0103908649175940c4400300200782900810486c282400800c1d107074083e02a06a00c6080c03492000725480c21000e18464420358029804101c45600700000d07941f000e8000000d403000c0c09044d02070405611070380000c04840310244e0340107a031203c3c41c8001804403040646 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 384192661 1250 384191411 384191417
    0x9071809050f1b040b120f0a05010302031b03011107030305160f02071a121501020d02010b030322030503040f0911120c090402090a0e01030204050c0c06190608030307020a030f 77
    0x4180400800329064568000000382c0c1078128000f504040305030a4031540d030000703074040f0000580a10440da0403070454002d4080c04031510350754030f5400c0c5503000d881c000c1c00084d6040d00442c1c5880c0e5400b0001901343c244810140000c01c011031f1041321b410303050704000e070140c0210740c40f00c00f08409000d000f95803211a44a43c20b11000051071b5030002503a038215400b801050a01000c811203c0e81d07400800d40700710040c4104140030390300d00010704901d0140230350081805803003081041c082c02c43c0180100151018082c0043d03003010400301d02415284003011248182040e05000880411000c0c4003d1014069404003200e4103403408103160100c03a2400000da03800701013840340f820308160510250b904035002a8015440c0d0001d8070005000b842200496540010010000204641c1c1011441c2c100e9000711001c015036030300e2082d100264403a910214050340c100c6400101080d0500c40761001e00520520000307412a260b1440c2c601e90b5105032400c4001d40d0000e2280002c0550090f040460182036103 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 384193911 1250 384192661 384192671
    0x3150a090f0b10080c030703021204050f010e0a031b02060405030d0c02100503091e030d0f050f0703060503100e1c0315050312040905060607060c05221202040f0b09071809 75
    0x100c0f0041940602402c5050b04581c0040859040d030320a80540790307000c00300e0518416600b81031030115950101c14065800b55400c00401c3c035031242e40170400341e504541540710010144145007154040d582c80e048102da12010a000104807a1801c00070101c1442013038440307110301e420500400a420302d00650000c2000f0b002c0003001aa0440841d41041c10444e0201e101036285038124018254014245803124441c507121348624134480c00d03040302c0c0c024468442c1c01c60458840c82c4044054a846001d8540c040c0d220003a98481d200c1d0f154801d00c81c4800341350588401d40301e01c1000340e44200340d07184851700003030710b452045030040c81020740d00000300030840003800c03918083c82420209018030b11421020980e6880000c00729240d04049a80c80c5900c2001004403500c0d0400141664020400210340c8004201c0c000b000361002d03440c04002c0c1d8420030900c1085400300d900300000b0b0440d020400c02d40c60384501d00e08105840f03600d2114041d140503201d01100e1460041504000d41c11355122801040c10a = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 384195161 1250 384193911 384193939
    0x40606090614010e040603050f0102120c030721061d16031e151502010606090b0c07033f030b0d111002070b18150306030d030203150a090f0b 62
    0x2104080b50011081c2002c8111070314880008004140a510261040c00b0740d462020b4030081c19401001c4806104112420503142d40344102110300003280c009000c01c448a0007070425261490712401c101c80c0807080420695129a20f0131f91500044038a85d00b641094000e020089010121081d400482850204081c60300810001c0d800340019210141c07036540c0c0d41c10098003040e040d000001800072601e40443c1000b0401d0002d00a00c0a0312a05d40081d220210120760290308108a800707407283c0100903d13420b41192034040c3c01c081075121b04800599105501e925404101240c0c00712001e002c0c4a954402030942005070580c2e00c503c8290744903400c40c41400c0c1c005804201400f40c505001e4804025028690b0b000b40d00d80941900010a40c01d00410b5000a00001c00c1d0703a80d41d07101c5c06071800035860400300b81d10303030b290702050b5141541034000056480b5464440d07400345d0341c000a503801c04201501c0789004151000c0f090b0b0410b800d440d031a8100710700150b205020701001401c0540e2030018010359 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 384196411 1250 384195161 384195179
    0x9061205040b0105061303080c0f060f01060804030e1f0908011a06072a1205100204140f1912020f030c010503070503150a140901080601080d0c02040f060b030406060906 74
    0xb0500601717109040200d2603078104041c141c0154007655002503569903c000041e0181e0350b4119421580d10144104070002d2101c00405080604031841a11010603a8546a8003524111101c1c0241c940140500c40024008072640d030003014a081d540d110068013604104004d425103510480f035005245405031911100d40724031044980c5660814001048640c1950004080151100007100d0000401402090039202c030788444a071648903108445181003402c1c5100113034012842050341c50704c1e65072a20b010b607040030256004454001031284254413000b825201c8028000d4210910840001c05090114240383c94072600c1030404030000c09510384150002019071000400c90f108005c8044089030310b40d00c0c031101101101800405842c2419150365121030b043d10030001c92846049420000074483c01c001c1450703030503201d201c0d01a00001e0140311065030800805c450403a082907990f40000b0614142d80f19480282440c044a907690341001d041c41c1c02079030160307040100300701d00c0e02c5810014000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 384197661 1250 384196411 384196433
    0x10f051014060f13080622020111120d0e0f030906090d030302090d062307091502151612020f0313060b040f05160c0203060c1e0a0906120504 62
    0x140407807101e40004103040419240d00500050120700ca00204005101c84110489482540d400c2400c64146039541504610b000315400c4901c040c0c1e422851041015500c01e140301d400c03010360701084481c0f00929081a0300d050344031809042815545151640c0c14400902c4060850501d80c0021420540e00d80e00280703891003100d0360544941c0780e000844003054001d070140c0c2c0714500010143c19901585003040c1d8054050024903200c41600100b200f40880310501ea41401820b82d86d8580c61420b0400a0ba5503807084042c0c0e000003580306480c0040050004880054414900b0503600c0340d00d040c400e20050078841c28010380c0b20101e4014019400c5104c114801d49602c0a0040b114080c0c800e15410200300402c40382d41c2d99a0028207050802d003201440360040c0d401045201c4c90001d805000380c0c2c0880c0c02c032080a200942c140c00c042c0206801043e50b102174001000492907071800c9000f855000c80d01d66000f1031890300411816402080855005500182002d01c0c1a00c00e1080d440c003a036810080c03403 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 384198911 1250 384197661 384197669
    0x312111c0203060a08070e070e0103150501110a0b2a0712080a0b030f07050108010506040b0904020f0909100306050a141b0c100f0b010237020a0b0705010f0510 70
    0x55000c00000c89a0391399150b203000905510064891413501d130040c00c00040800c80c0c45001080482e41903450030352082c07107501c0c054603556100c006010300701001161495400c20701904284a40104400883c1202c034405003c1d001700142400140306440070081001710482840100c180140649030125600b02e030140396094181c500308500c1e60741d00ba00c810080180119054051048000c8a01080300c00114041541d03003d80b00c103803080c2c0c0da5000b00251b511031402250714001003800710385861708040c3c002e04290b00d032000240341022071403400b00f0071205080b05d02c4c55a80184840800a02c0124825240c00041458080c05181620606924401d82c0070b0043c0f80f44074a2401541c02442c01002a5082d04d1004415205070310043d0303203c4c0004e4032040ba01000c0c5245030400d0410b640d80006900c540d03c184601e0a841d0402c18900200c280024524045540c111041c507044016070b1005510005041c07902c2c0f20310703140c96050802d030f82140c0c4181803900c6d900d4500b400b80000c062406107220221 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 384200161 1250 384198911 384198967
    0xb011704061808030408180a0503070306090c030506070206240a060e03010f02041e12030c0816080304030c0302010e0105060a0510050c07090912030204050609040c0516031211 77
    0x401040704048041c2d0403469020704050408402c0c0310400c01d02d01c00400801d070295100c41070b8524518100f043c010b00301d105041d4140c0c004a010400100759800180119004800c010b108668946a032414064111030082c0160441030410186285444a8000040740f01440d1420141150f003c1540d00450740030741020301c81e00035410010740d03400b500f290405440c41d100941d21540d55071007041054001e80181c052041d4000070109618101201c0e030100380f03805544000395200a502c942c030300703135100321041c4004424031888040400c0c1c8003401180a94841e035605900c14996003402030031601499020402a41814248001036680c0c404020555030b007295160f880411600c0140c442d442000792076100340c004c04d1000602c04003283c4c0011000c03405042d01c0400082120700c00c404030b11482c09220392080d0b06108603c0c0c142002e6010310408501400c0075840c21407140300c02c2d445c40003150403c80004500c07030f040d4440455a0300440103245402c19401d42008003000150070403480301b406c40005 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 384201411 1250 384200161 384200171
    0x5070314030c01090b061003150905100905010b03040b010509060306011406070516050111071a070c26010b0607051504030c0b010806040b0601050304030c0b09100e030301090b01170406 81
    0x18014240101c2e1004602240200040201c0d46010890300c0001c513802031040380e0005654030102d0203405088516110710580208282c1801c200ca80200700c00740000004030500180170400244130303c2030a018003003140c0030b55200d28192401140031441600401e01605c10303e800e1050390344001641c0703419200c064901e400c2c00092040412690300590078042c0c218400e02d1070444140b030380c1c0241003003a10404e90b0b441645000c5114119620348442c03280641c190b0380340c44160145000c1102510110344516071880c41e0556410001d41c45a00c1600990a0045c0d00741903548404000d124410380988281c0e07456080c44059100d15803103401810510b108404801d00003030400d442a80e2120610790700021810480d41c40d0100c4560750141213a0440d204035017500410850b6002d04240c9200ba80e065485d40c00076001070340c46503001500a49030301a5841a07110b40c54000c2c4041c05082000c80d0b258004503242d6140040c1ba03410b99111241c0300d814032561768181e42c1e003058802c071641d0f40241c002e83c5c0424 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 384202661 1250 384201411 384201443
    0x4030b0610031a0108041103030a050d0e0109021f0221031602010c050d09051e0a05010b030718150b030a020903060f0c0702100909020a050a02011424010c1e0b0a020304050703 77
    0x4940c40440840760323040c080024800d03651a0130001400c410701da81c1108101a142d103000700c42c22a070440340065808000c051040c6001d9482c40c40f440c44c0b00070944182c400d551301101c0400315220706038002c10040c01c4c0200030084840b41c030601d43d502c100f08600c020b00812481a00143c114030408400341000760326192503400f4000c0030402ca0b14680902d184e09100043c40f040c09580310b030580c10b000c480d55403c102023021546000120036081d585200a203e44a84100e070a550040044005203500244141070001d0f02c0030f034100103940708414207080540e41d011103208042c10010003c01d82040c0d1790b043c80034041c1141c030303000a03075180c2d41d415a03038061440a210030170703184011194002400c45000007122840194444040c20340b0552640007408000f81d4080c481c102c1450859900090410b16440d95151030b501030745505070f45006041071580c504943e02c0320f81100041d0b081e0040e00c2c3c0107081502007000441c40c41d01d80d00c01d034560030841c1075090959a56032244490710024006080c81c1000e50 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 384203911 1250 384202661 384202673
    0x200703020f06010608010806100e0106180f0b040317040302060307032708040609170a0201031503050105070c0b0109020307020d050307210e06100803340b07450302030304030b0610031a010804 84
    0x24010b805c9a4ec0e50780c0141303a07501c03241240360703006000c1141c0c0d00e03920080d18049010000c00703039000d40303900804141c21a03071000e004400500181c4001d031b0b60000465102c84a49c3d20070746c01c01d114140503050060365141480d50117800704c174181d0302800b07040c0032991014000b09404200241c0282d0b09180216000c450314100e4031003424240c00c01781c0706502c0d01051020550308001c2c0301d000c4501c58006044180e982c0d109907412400300b26a48400342c2c11074079220101920070300085900c80800e0a1015020034203000084290010b2108045d130580c0d01c09480400003c10811950300c881100e003030f50781e46030619850039128029040c200d0b000041d61f41c0240ca80b0594290041c1c10f15903c0c01865208103494104245103004c240d844001149403061110a4002d07070095100030036031503c80303050755450021000010764801c00381030032400000031000302c0180c2c0d0900c01071001f140500d40f00300850034442c0400005040e181d14440030b0501d840c290b01120091000b613500017800908020b400780d0780b82c0c2414 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 384205161 1250 384203911 384203957
    0x4080307050403050d0f0f05030903091302040909060905010614150c0c0909010213060801052b080a0f0e0307050901091a10030c020709200703020f06010608010806100e0106 76
    0x1807003800745d12115a180c6034040700000c00b00409944401c1c03c001c40306816a490320064840020513042040401d1880c01d2100780c000e0365001d40303480180b40940d6948110708031210440c4c200e81180d160403071442880824012940035104030081590341581c1803002524014184d5000361070041d0120f83e88201c2c00b8140b0030103510704c901801414013440d04241d524001e501043c0c070402030310346110000c0341300703849440f1139411303103101404245c14400701000c2c2c1540c8443c40840400480d8413481c0b81e40006180001900000d4a16168100314140011010706000b0321641c51a0207603000000070000d50b565410070700c3c1102c01c003a0000400402c1c8142001808040d2445950031581d00c4011a26140e85944039801c08100c84c0e00383e65000c0c0e201c000d01c2d026035002000c48001454841802880750818a0082420501c2130048440301c1c4602100366080507001d82c0044041030342d2800411034018240280b036803003010700702003641d09410302100565094042c05208200455810001e080b81c200e0000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 384206411 1250 384205161 384205163
    0x1140a052b1416030506060a1209021509090106030902090c030603011d1f060302060f0c070e0108030403060606022d0309040f05090706111c0912300804080307050403 73
    0x9202150100c010700c1e504203410f444102503412059480d0400358480c1c82032a0189038010181d520b80002008120b90780801141d03190300c12036171000c0d1280181c2d40d80e0443c904034032820640d561160002c0c010402107150580c051001d040c00e02052030300681d00c015420364003074003d014140d140e03141c403004240100780790b5000361681c5a03580106c01c0d0b1031500041c0900084400080ea000c241c411940c81016201240700003034022800b40020310103165114054110b071505141190900395480303803811003044003a803000100c1d404c001000d0060014074081c00c0c2c040d0849000502000d2940c1042280c21340004103921105026210080c1401600b40106c1d0400a0000c01c00d0000924041c4000001c01d01030740d00c40c0d040d205644001600a004000d03c031400510714001c0c01040c1403151403c80580c60003050b0f101088a41e29003c5400c1c840705045101060096006410100c10645030904452101070b1107080801c1c101236059156034080da9850b80158000c20710350700e940b034840c0d094460f0301035600 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 384207661 1250 384206411 384206497
    0x100c1103030408090d23010b041a1c061803030204091104030b0610050d020d060e01080a02090a0c0e040e0309030c190501030906110705160909080306010c0f120c0201140a05 76
    0x806c0741581d12054000342e0030601c0c11103003048803001c000200d031004034203400c102c1c1d0004005000c1481440b040c0c10300c404014013443d4040364800c1803085002000d50441001c030041380d4041010300402c10984100b2054400d12034845180c2401c40d1a078038044200100480d01c503a89255016031524440c00070380b032107504450000d40d03c0d41d090540b0400a805c0a00408aa6080c940c000040ca1240080d40e201c0c3c0326005032400c11310b40c5424403980064503540e6103600074020f03080400c2c10345071a0b5100350480544100007443d01e55801808050820788181d03035152007060704040a52914403c1c054030030403a5003d080c0010150003c0c5800c00203880c80c00000704860030040b851800380400440d603803e150380324a0307034914030684440e81203048134a40b0303001421360708003030000903000d50084101c10780490049100d1800841d03540d6400190340ca02100718000540342c0e4500508550f040f501000e4000680f035070480c01d20b91860b4008115002e40d00c62107460704203040385d049100516046030f080703800e0108 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 384208911 1250 384207661 384207713
    0x18040f06090204090e01060e040f0c05030d08070818070b070c0b120106020d110309040b130e0d020111091c020d120507021c030f05031008100c1103030408090d 70
    0x445100000d4109118400b0075505040b6030b2951440306116045c25148d40e01c403040304613280d030f0300c0d81c05403200b8100d03080300d544402788000b00c3c440d6030400c0703140c1c1d40c80510703981d65140d8a04100000d040301c2010700001c0203520310509141e80c3c44c40120304401500c404507046074450700581080501000e56600140d0202c0002590040d42400b000e2038a050302c616800300c502c1c0d0208080104c96140d11801989440d4109000002d02031a00344c00900080c1c10007031046199045814200040342e1a055000040b60f100f044140c045d99028003500055030000c00f942424120410007181c210344055014960000380b107090b05046682d10b4a07100315007900420403203106013054030082d105500c1600c00303910070104144446103520400c50b00f4084540d040c2d4070007041020a61007500c0942029102d0020b030340c003100780400d41d0354042002000394004010041480c4028000c00341c070803032070074550030501d400c100108008640090229071100c10706a8a84205002500740401e0324124100507080c210044 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 384210161 1250 384208911 384208919
    0xd0e15042d080a0305010602030418150806070f021b060f03070302070804081501090204080a0b0705090d05070e06010c2d15090b060306130308040c0911041e050618040f06 75
    0x25a000c0c0c6280c0c03c00340c40c10405640c83e007005a83c1c900580c46840c4008070244c00ca45802c003065040440403110880e099010b4648a1151f0307410030b442200e05c5000110000310318012990b04200224081000e00d050024181c50700020944c0b038403034840345180c4c0020000c0802c104a1190341110703443c4e81c000d004940c90326110b00b00d4588400c429000f02c0003000304000089001c0140d8800c642c116a40f480080130400c0c13540d50b4800310480c008140d6428000d0a104850b81d50b250381d0010500c40b40315002400c8400d09040200c0b030002000b5041904001481100d40c0020340c10031070300114215852026201d250010090300c04c08002610010300543e10b030170020800010f40d41260300704c944560b044100c2e0703540b12024103548032011034000056085d4003600c800804d00680f012a0000d019519604c080754031003d400c41038450798000200c4072900040c0030062041d1102c05905021080301801480e240b814000800c4c0b4054040e00414510014128004507038840e44651188c14854109010581d51 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 384211411 1250 384210161 384210173
    0x81201030507090203160c020a0302130b03010e0a020a0509040f0f11032e0f020c0a050303010e07180501080603010e010501080318060906030f0c0706110d0e15042d 72
    0x1080c403003118948921000898048070304d00a43c0e100701101e18200034411245441200c03418054038060360440041c1d81e02101684030f40903540310042c502400462052900d0b03090500b1180603a507441e98035002540c1d8400146c2d203902005040707900840300060141c680e0b0418000392100f1820060a400c40410310b80104814036803500c001010460580d68071a0f19503005400e01074031000b030034803e0301c0e0615004030500042d600c50000c07003103c1c0400504080340b841907146041a400c2c2c2c155041e920120040000e403010800607680300075285004203150000034404041415039009071814840d084c0300040068070254404451064070500034030480d69205000c603101d5201c10f04405a80e0200d0071607880314100b0030102c4ea41002d01500c10361860362075480c000e01d41c503c0508004d20b0100d0821421000c1047e40c000d50800ca540750003029034032000c1004a1003107030300c002085089600310030841414500540792141d8482c6c1c11100b4101210491091015850343e411910f03a0618400300185040c050 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 384212661 1250 384211411 384211447
    0x180e0702150f0106080c0c0d0f0c0c0b040f0605131203030905030d051603020a08010504020304020111240a09050d030e07080114061806210c090703020306090a1a1c08 73
    0x11054417981d04a4461010031510f500c146200802a0752181005040e040e104442c01100001903140140d02454165a0010980d0355039010320300d40d0001140522181c0032510040780204018103000d0719281d0011190110126a0b1140c1040ca91007042a0b005250003030f0001044260302ca002e8960f503000c000f0b1074800408041d5400b500614022800700c80180c0030f4400c0302d1144800d03449403512a840d000800002e940010b00803810041c0700130081e4241c40080010391141c0600f200445802c24251000028203100101404021420304000310042040490340c02d0050149160105408292184185c6800a1640f01100030361801c00c0221028100481c40c500500e411904100f211482c800c0100f171102c010351341c4942c00100c504101d00c0011140a03004844221803058804c007916600006010180031070718440800d8000041118910340003688070381c042c0403031a040207030090044014060701400080d66009558180c40c030100c1c200e40204d840c8480368000795460361a0000d0f410410006 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 384213911 1250 384212661 384212669
    0x190509122a01020a0f0806011704110a03030f02010507031a090a060806010b0714010e0c1323090c0306040b1906091b08090d0c0f080c10020a0e01180e0702150f01 71
    0x45c0d450302c00b40034101e108004c0300e40103040503512024400d0f0002891b10100d600600304440c02a00d001080c0d0b05501c0b06403485000b036000340c03582c06880c0ca0b0a4406400d4540003441c0d02c0030145003146060b01c100507410281071601c000e80b8039084950714803910030010b02c2650000940d82c450070000150190003030000b001c41500c40c4c0310803049251720b9002c0909890f03a420003e2025048400070a44c03508201d524042049500d05000c140e4040f641006002c20310a00070340c240682c1d00380100084203004001641100c001075004141c1440c203503c440c8881c07200546080c0048880c140c40760103070310443c0c21103800781c00b817000100405003a8065a08021420032000d4003c5868130002500a0380c0101c1c5060300544c44d610b4014041800c0d40c2c94442c882108101203640a6042c003c902070650100f000c10420201c40f080180e8034070b18090003515801c14090580e0400c051000450391000c003501d030354000ca50030751918499603141c404050f4208028442c0e55401881410200030f00d541a03130a01d02c0c122 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 384215161 1250 384213911 384213917
    0x20406030503250803010b251b0e04030e1909060b070b090a0b0613061707180e030403060b1c08210106021e010e07080303190509122a01020a 62
    0x6030542c2603c9580202030a101034400c01d01800100300840d080001481c9040440200c80101c1003031800c0880c14446104054861000007043c02240400085103580a00b8090340100030b10f10f4190340040c11483e1402c81940511a604583c5034a08540800100a0b04980d0001c2c00069140c08400307820750005034090361521034900c0440c2d242c15010036a400401e030044154070050780c4000c10310030307851218807918000030780e2914002042c811205144450110075000342c0300c0a460112665072084d01c060040640038030304544414610400400c032400c403640958081341e024641c03c0061814070200c022170101c04201002e2508004400000b41121a001280c20718070349810b04903480b4100c02401501c015030f102030754001c9001900890124141465800400e05002e42e40c03003d420007450754020240340d40080148042c24894010700307031b00300300000000c1001c3c4c82d004816550f200c008400c608035000000445143c40d004140c0f110040006504070101c8001203c0c03540b5000f035200403001400 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 384216411 1250 384215161 384215197
    0x110417100b04020f0301120c0b0c0c011202040503190213050c0a030606030c14090f0a08011d0a02030a1203020d0510090e0c01120b04140703050609070203120403110109020406030503 80
    0x5a480d0901c00e0342c60b400040303c070701d900b168208000110324607c07224042e2100500b080001480740c460130300401200b080c000282c24408807500c00074140b413018110007102c2d140148018006a10002490351008025003942d04c9078903c00e00118107a031400600c0c6e841e0741414101000003110080b4010045942181d40030480141c0d1080101e0440301d40903518000120700340c40f80b40c545410f40020b8032045100410304400400940c0026451542d103902c442c2441e5110000e50030405c800c40000d8a044048801401c0c807a41e480c0d001030745075121018014490b10501074070540c03040c4070ba4107071818128480c20802160500304100803125041c0e2049072041410006071203070318400400c6086130804181c45407a01c021308035083d0000f03080c00e00c40c0d00c0d0b0025502e1302204918041100014001c03071607500d002906003000001c0c0620300c2c40c0100f01e10103560003040340b1800c07541000c190640c05030309032805000e509070010381c46014058074000039601608148001c804e2100c0030000303003440003401c008600 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 384217661 1250 384216411 384216431
    0x5102c0f0a0617071814030f06010612110f040b0c07081b040c0e01091505090d0b01030c0806010810020d09081c06080d050d09061e020307030b0906030c0411041710 72
    0x2880412608081c69170010050003040366001c4c0643c03a00940900506991030000320018561034103000764021000210500881c07001400320b44502108520b1899003036103807907403500d001d140c580305600c01c61a07841c80010790f0100c404018450f4001401c41d204c141c40864001c0007060500a4000514500c1103181880c1d00901c5402008091000034041e160346600c1c40c9428078083c0c0015a038100d4009104082202c005141d03251444164242d100e110350441031750440c10070300b800e450603400169050344403c0050145d0200000c4183c2c1001c01e800c000750ba290300700340041003c0c001a0f04020030014020032003c03000a9107009129915070034400801001e5a80c50303202c0d58541d4a5003582010420801c4840812502500000c034071500604021520300c0e0104080c2100c401030740d80d1454000e40c04400c3c410956414011048158802c40d2040d1136800e080b80007940b200031285005110b260b68024000c601100442a40d0040008400002000a900060540b10203030b500c807043c6503c4c600903401d0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 384218911 1250 384217661 384217667
    0x6040503030a1b081b19030501172d0703080403030c050622030305041e03020a03080601030b151303080c030a0306211e081305102c0f0a061707 63
    0x1a030482103075903404601d500c17100e8040c1c00c1c1c0c8880b400388a910140421103900401444506040303600116075000900390725000741d985d0b4090315102000710035040301c1500441071210090b40c644208040300342002d09144050788900c0d1401c65480104140c4010030000241a00800105081400f0301e007501c0312076568140d03250003680c1880650120450720003040c0d002ca031007a40001e40c400d108100d502e42200380001d0640400e060300c0b4045006134807840ca01010594003010f0303590040b00a0805116642c02c4c4400140300c40c1e01010744049d007100101b50304422440c1c80f003103140111b401c0340c040c03592244031901c007680b03130f134808004000842d00307041d8001940700b000c51185810000d10341c6100603115859070340305901000b00f84c44803604031248508002040800004290031034140070180400b501e010140032030420300c40d0300712051282487d0741c05951011001c9001c622403000840781142a549400a0300c0701c04c030084560703001907413841d020440541003a800d42510700e0131048440e007603580c44012 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 384220161 1250 384218911 384218951
    0x13020d0f09120513050306010e091c020604110d0f06060f0806040809040914070602070608070f0207030b060d0807060e0609060c04090507051c05060f0307142106040503030a 76
    0x2030a81c064180c884881d0b501c00c001078240045610320f0012513540d210006407600f0420303000452580011b2090111702401041400149542800c1c10800c025050038040c0d1135180090014014900b441141502d640d208800c50380c244d175110300030003002c110340d0070000e0040120380201c803e020413100001c510050b001139030a00c102d500540700c5240c00c243c981407001909004000b11564851030118000d48042802030501401c011b46c0203150300ca180900040c841c4001402e083c0c1071050b040310109070780c0d03404143e000036a6040304100e03110351910008038010301c01030344028148141c08140a0b04100c982e400c8010301d60311100456a640c3c4451403415220380c1d0584200c444004c04100400c185922504516071000382410603c1c1800f0382c200d00d1102502e074804410120955032410080a40362001c0515007100040c0e0051000b141010f481002c00c100c4c07500c5240c4103010754180404002105540815034060107020b440790350074503240c030f643c0c0d0760400e42c1e030a0380c2c2d01d08110024900c1d5108000d4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 384221411 1250 384220161 384220163
    0xc0f030f031b070302060711031603030e0d03050408011d010e030a1b03020c040c020c041113090b040603050f0d1407020901211e020f032e02040513020d0f09 69
    0x5107151150101c0c9500584030b0000caa1820b60158460000150361260050b288807802807030400e141680103000c050a01d4141c0520701d0a103d1648000e001003544141c461003094025211000071501d2030074190380a010390760140c0003544c00c1a0f2180c0781d08030280c86a242c00b4203840002e02c1402c01c5c4000c0340303440b400382020ba030000a1210b41044c000c2c2e1501d0111842075802030056600da040f4040205090790400d81d804009a0b1144907083d11031300f4240324032503011582e25211030a02c03543c201400f8545809220b000c0d00d05840f0800c1a0703440d901d66100c54001c42c0d01c6400c80300701e41da01c108000e86807550b17a0302450218412030310b108043d5002404a9909942c0100700b5103d6a0824442a049000104013111440310702d80503c400141303004903188054000e400c01050301c2000303204120259059010050103600140c00c2c0240407414007041040f55a1302481c10210b02c1c1c0c0080c40c20000f80a0b40d03111f10b520920544900d404802594020071400003501c03405d02c214a0340b2030b410070035914501f030 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 384222661 1250 384221411 384221413
    0x1824070201500304030302040e25030c020f0303041a10060e04020a0c0c0e010f1205060a052a03011401300209090103060b011e021f06170c0f030f 64
    0x11088820080802400302e40c0d080214485000c22124040c2519400441d022004243c0c0040c0a001031001c0c12a0b543d400f00d180c414602901030b2078146000385100c2119820700349038580713807041c14243c000c1c09452076859004003200e40b00c0c901401c01300601c0000a00f2490250401c402041d4201e104a01150585403c0d85450310310140e4041408000c0d400243c00d0b008101e01c1201440000e12880f018900070a100101c1003525414144e0a1b459030304681c2c04200700b66420100200000c0c4003150882c1c1c400c148040008442d03543c3d441800e444401c1048601c010110f560707285044a4041000d14180c844401064103102e00c4030005503040035403418402c800e0301c200d01c11000e1061440c041441104d104210160601e0380a2011948406003a0000c407445030301c568000145580c1300304403405004c400d182113070035440c10440c040c0d11420000090f441700083c4003094550303010950058801040d802c0310701c040c4988414816501e61b05a6010544521940c0b40366040f64540018030340241c1c00304030 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 384223911 1250 384222661 384222737
    0xb0a060507030c080f19030b0a06080a020a020f060903130506210703060b07030e15040b0403030302070201020307141507021c030b0f031f110304081824070201 70
    0x1440659003a0640c8901300c5050404102020500071800c0107400360301e088810303604e5601500c0001501f0b449002c001180220400c1d1030801c50b65a01a410a8001e800c090f001030b62046034400032420192700d688844030a00c500b00600c134031040d00000400d40030120240d00c8a4850321030301042418411030030208079541000284511403058081d6080e080805800c001500f26501c0480d8162504644815400f150383ca030700c50044d9050050f442c0782d021014100017403074603013040301e051303080c0c011400040d0800d80d01140140440e4001c100312240242c000b2505100000403107042603807140f60981418000e48280c0119901d04d00000307000c10b005240b901c003044015a0f40404030b001708075078860070794050042c40c85095141c4050210000d85c1c0701e01d03000355032901003a030a40000d6801c00c8100341c008190400801010034515030a0700ca20259982100c502003e55000184014904007211030f40892500200d04001d1801401880418800e8984000a0700c0d10f0381000e014030f19119140d21041010 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 384225161 1250 384223911 384223913
    0x513080d0b010c050d0201060f050d020105040e070201090807061e050601051b101a010f110303190e011a120303010509060910080f0c1302130911070602030f0402040b0a060507 77
    0x5070400d004100c0107161a80300b041c8251919460160340c0043c11000d41d6613041c081c040783c00002c05410180200340d03051000074a203980020b020703100394402c042000303a40c10081940540300b03401c50100680c204001c1510b03490141041e030010014422400740110781030b00219221002809124491a0f058503481d0511408006440d8444041c110041c0180501e252180c0070b4890342c880c0e00a83c81005018031002d20800001611120030700c2608401c0c460102d07100641800004100c0c0d50054140380301d42100102c8103590b50180c24483d400381415420b0042c0c100d080f000142c1c1c0500c81e10011204484140d040d891a2030300e9100a000d40c5820403040c1000440c68100b80c40c1c1c098005078202e01501e0400e54818126051412a01c14020070b60804c1c3d02014261900c91186580c01e9940841140343c200345504a0050b0034180c4126a4000c0c8c0710000e183c1c40e50402c405440e00c9642250040d542c900d45003040009082040398100d200301c1c606403c00849092804c0c4881c20303581a51105481c01c01c80d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 384226411 1250 384225161 384225187
    0xc0d0b0604020d0504080706050105030316080a2606040605010504080c10270612061d0a02091201060e13050601030b0c1e0309100c021209151c051308 66
    0x200811894015400b0460400c3d004181d00c2010321660140320025102c80d42031800800399881030740032910030362091014881e5000c0b4001000d09141d0b01002450381c03210301c50010790382c007042000100114039162829044100707120000510441045a0400150740c5480040d20603004a0060503181d42c490f500f4402c49003001d4110055103107a03400d1032007600700482c01c0c0c00c2007080c640c40c0ea21444480440c003005001e411610703d40100310300b0341c41030040c5170400704840856201e44080601c00c0000001180041220358103c0d11481005000d52000c100c0c2e4940d030307030b02a2096200b52200100e00e40001000e100090044041c0c15501c00e0144c80140d103152610105048041c1c505d01958004009081c528190000280d20720115074a086440e8900000560706001c02c000508820f41e060402014100d070b804110b042c80c05c4030085045031190520804070362070761081c140000158400040c1a0902548016000c00d80c0b80b00e890240441d64803842075200482c54044010041d410601010a030561 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 384227661 1250 384226411 384226433
    0x10080105010602030f0c0c0409080a0801051e09040c0509010b1201090c08040f1a0f0702061003020307330810080304050a090908070c03030f020c0319061d0313050109080c0d 76
    0x800885d01e203e4140d400103811104500300130ac82510b80001d03014855038019420500510040359042c05081140c0e0b24809182c2c00300444500c203814450020b01001810343e080000b6100c0500018265a110003250a860340081c81080c0c00c100088000203c41c0c605001d402419807aa58518903151120354921852541e140340803280341c0b942c020759071024000d20701002d200305801c290b194268144400c01a00b405c201404411041c611004144090b03200050b00100305c070140f4441900082d0a45480b50681c20f0000216840711100102d9404059001c01601c0c010b4105074840c540c540e0b0754418256880c803907807090703e403c14003248041000c02840c0d800a202540502d030800d150941c01d07070391030701d0444640d0002c401181c000040b24480c164100401d402800c0103800812401d811004011000301c0342e5100108002e440c0c60101e1903003401035444641c4070550008072070701c806480d04280446000c900030320b80000c0b46488006980c242c0010042100440504100b02c100103035243c84c10303091 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 384228911 1250 384227661 384227677
    0x21c0b1f031502090d0f08031006170c0a0201140f04031b03020c060d0e0d021005010b04140603040203030405030f0c010834090b220b0306010203250b01080610080105010602030f 78
    0x4581405c036171001c01d5120401c06c052601c9001c81e107950303103480340c2c2c031049601603a040700d0200f002403145034024031000d5841030f0f08540a00f12650300c0d8034038050100e014224074901c5024800303454003402844500c3c0d0580394011846a110407480e61622813030940701203103a5034050010b0f44842e41554082c02e01000034400b040c444803020034030060420140789050340c4c06030354000680c01900001e00826083c8100e601600c05c02003d5450a841d010280204210f10b05185224080000114046690400c21a0020070018090300c424241c21071f01291a6043c586500340481c00d00b00014102800368888503001040190441405800665440444440400c90071091060a40d00420b0140c00b0350090400004106a0804402d0052560070742000c0e5652080054810500034030403541c0e0080306035002001c02c0c00800c80c1d410000814660b80601540018007169900c40011072044000b04401c1e20801c00d203510000510b0f034803007078242214402d201c0c5600503042881942600946000200b03415 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 384230161 1250 384228911 384228919
    0x1b0309050a02060406080708070201180b061f0809010c020a0320010f15080f0303090a02060d0f0c0c0203151510030b030f0106051002010c090b0304021c0b1f03150209 73
    0x604140d42c0494910380c070503082031010407020f60401c0390140e405110f003070340318465200920a1325103c0c0c0c692103440760f014a0042541540000080d400c1e00c07460030402d00c09400810411341803051304409060b4800c1510300d40815400c21502c100381500000311400d01643c103a0700e050309044000c0719004604961000ca42d525503c800118071282d00c01d0192800c1d40c0c01c0300d0790100800d803034a5000c52a0445c20600e9009030707007007402002100b000c0403405c611640e4051700c00076550705d0b02003d501c008040d40c0c40c0781e54049203008080c085155000103040041d40c07090303088403003c1108501074170440008440e803407051a610120300d00b4500b0b110034100e03d000e01d20709001c00c4000c055030009007000b04200600107030747e42d9240104141d103001c071151034000c0b51300d0000301f0010008100007070240c90903000310740c1754050005c0410308540391503880a9003541c603072506400c80328440c03409031544241a10703d07104032024200c4446c00115004840e00c01c82e0b511107901d00682c02d113284030034080c0d0001c03c481984 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 384231411 1250 384230161 384230173
    0x2b060e190b0a030618060e0c030d0207080303070c0302070e091b030a0b0a0e010906050f0a060e161407080d050f10051c060b0d0807030813020d0204050c0d240501031b030905 76
    0x180d0540140e0944404403405802c01d260b286c2d00345450075001c450ac440c1103501c00e01d410860b4110100445e0380040c3d6500c0d2500100a02c0e0500f6442c0c03190030741c04503403565403400030402c01c3d000104290880c460302c10015000740f0b038608101990b880300c0803805040c3c8050703003001c1800b000c2c05900c809103d00d03c40c8004980440281c035220116a4101d490407042e11007201049502c10f894030400b00a1302c1403d100390402e0070600c82c42600d1800c4084404280000e2810b0f05110039500000d94401a40c80040c4594a80c240f4a0392000f800d025148022841c90010100c1ca054040e500b040e000c2c0c1e18042e1a040c1c941420030310400203e180b0f08400e8810681c0c4040880254031940d40030110325000362400c075a684c0301031a00070204003004101c1819803401c064001c00580e5407a020002c0e042d0115030106031911034aa15400a1090f0004c00c0035081c603000c5048150b0390390800150308440701441c41c00d8400da441c4015010ba4481049043c81c0740007601e4000501d500075031001600034000c4044680d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 384232661 1250 384231411 384231413
    0x50a0c03200705040b0a030317040c09050c071403210c0c01020f120601020610050907030f060f0f140108040b07020a02030607200c062b060e190b0a030618 68
    0x2076403060101040d031904030240c1800142410300602c500c100007035901c3c082c02480c5840040403d40c2400d030b49914040c5031401301e8140030f401c0040c1c9014006121080255040c90188484030740c2c0710100454038000c0010044410f00b9001c010344801c2000380403480400f000610302e81c3d074100c40090403602d03911800e210316801ca4800740302400c44010a042c98a41c0c0d202d0342c1c0a03202002200412603030442d44001d04010508181c4d100002c05c42d0001d0307a42407455210b02c4801d50103801302013070340d02e40c0f585007d0000a81c0c041c052284000c659003940c01a203d642c5400c0b1880102010813600e5022410749004140000c0c2e40c15046c943c002818816a40084411b500085c01c0407000d0f90303d00d0009240e8030b0200b50540b03034411020722218040008182c20783c041008107209028001c0701840b007a804001c0f00000260046600103040d4005d00200840391721010700d030f036410f10141c80c032100040e6040d12244607034a1502c41c06e918004000c2000a50518564a402c064106000849a402c5103140440 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 384233911 1250 384232661 384232697
    0xa0804062007080102040608011a180f100e010f170412050c0105010b1207050a0f08060a1e0806070c0c0308090103021b0f01181505040c0b0408060610030c050a0c03 72
    0x402070f00e0144005a0b4a920f0603a000300049010b0f04010100b8103959001503200d80350038216010190b0000040c1400480c0000198a019441503126080041400c1c400891980b2030914584d80109032a4488405458030003140d1000c01240000d58050b11400490046680354001c80364100d205c0c6400ca244c1307440e030180c86007940c900381d014a02c085404980d50303041c6082a010254882e04625145c4c1c1444007030303030000703010082e0b9104042c00d118110010846507140e040310600580000704d9141c0c2811100c840d4405105564401c070281c502034000400c04891143d18080c044e1604210181d05990540e15118100d80c09403d889040c16804c10092484581f240a80c04451030f88902510041040c0700e01c0c5801d5654203c1d1f11004580c0000b9044000385400960324004d640b8020300041c2680e5501c3c000000c2d41540e007000c1c5c040c40d404200001c21400000d80f1501c83e400558609513584000b1005a0540314441c00748804074005200808046206e10701c41c0507a5070281ca088452182001210 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 384235161 1250 384233911 384233923
    0x30b19110c16060e091b130605190801050108011a04090912090504020307050d02070606050d051c0503061e01031b092d1703210106020c030a08040620 66
    0xc0c1859802c0702d810b1000030b885007240003004040c40d04103030814408101c005901c008008100340b00000c009074920000c01c1400080e2005841c013000200e24981d00c580001d001900040442c014003402146c02c000038070300c2450040d040314410b8607060016420144a4860b40d103400c50348441180c000d01c1f0024550807207006103c4568002c07940585192018000200250899040a03000fa0300420900282d0366004080740c61040c0c4048006032640c0742031420101414070303648074950080c00040f1000600401044030a00d410850000302a5520301503800d03034041c00b04684480d0300048110442e07103030b4005d103040002c1c3d2031014500015000024a02042002c080718004c0c000900341d070006100300d21040c0e0140b42c0d9148a83c40b11b14a054902640740150fa9040c00b60a0310580010008945400e08000784d990f00040c44100a40d0018001803a4070080400d110302c200610980c140e42c446410045040000190000d0b07003546002d060000a850501400807203600d01d0000c1040d603201c0160520074 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 384236411 1250 384235161 384235177
    0x20111270402040e0415020c011b030e1f0c050403020d0602041d06010834051308030405030319021002040b13050909060a0e030408010207060209040b06160f11040f050a15030b1911 79
    0x35003000c0c2450810041c11607903405030b210843d5003703080c0150052101c1c00da01c030b0031410085001c6480450754100300c442c2d000741d900013900a5403194070501080b450341c01074800d55003200799100481000f04207542c5140d0041d1829404101041c000c01d210b60004502220369100070400031507180004040070b94209010540c4c1800101c0200f1095402c0358489541c030014507a00f4019801c25082000003506c0384105141a1481820740b00e455500c10700074000d10701d200f80301510454a50340d8883d8940e41c1540102004900880140000700d0b45240001c03103c4d0007800007070f001740340a03130342c6200030802018042c055a9580c0700c01e02000030030340c03801d0000f0300489100b4803000d80c81d10140c400340002e807600114418405e8405010161000c65800b07460a0610b800140800001255003442c205261294145903001400e00b07038890120501604020b001d02d0b04d0410801070031000304003c0bd581c1d0594000103007482005008140640101c01d0400000303800180d001813402e1405400c0f041036440008 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 384237661 1250 384236411 384236441
    0x120090d020409141b03072601060506031015050301061d0a050d0302070305010c11060403050d020f04030614011a0909061302070507031a15040507020111270402040e0415020c01 78
    0x45045d10850405000c60201d46055000700b5041d401d10700300400503403070982c520101440d41d4071400d01e503481c00d400c1880200030281c1519900c0c1003520b24141c1b001014003c0c0341075004214440d007140c41c4100c045904850359603840c41120040611b071a5510380f0500031640d40804200c9000c01c183d51805694403c0f14400d4004007005407552078014290741480784900b09000c6a220000c24000020403c550f01990525201340c1d070b0080b4072040700080c00b030702c04d2516829174042001b0080203515440304100411102d0392251a80e070341c41e14520013004107085c2c0414000d041c0000b4501c2d05000700040d8000d0750060949200307030700395500c0e141240c208a20075901c1c0d501c5034408000f80300e191800c035200b06410110820701481c10040ba10400d50101500500039640d640018842138403c1d40000010204007254035520401c00055941c5010000c0c1d2a204e0400d441d5007059a42c0340c54400c4038103c40004805000e2980c0d2512a10001c2680e440705100c655000c01690441e01800e204412200310f01c44 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 384238911 1250 384237661 384237673
    0x180606141206010308070b07020a05060c0a02060f010f050f06040b073207210204060f05040b04090203151e0a1a0616140109060f0c020120090d02040914 67
    0x1200700140d103000c1c91500c8000390008801400880d40707000458038003030b400944403006138079020b804900d030880b503030005031150040005102110090344010500d82c1c43c5a80ac84040381c503062120701c00400c080c4038541180c0340712442040241007809103501940402884c1031705240c2c2c2d43c401582a60311010341250150019449032407903013400403004419500c0d10150780300748016804443d40c1c4179618002c404407160352910780541803502d0540d031024030b03a02a04c14880c450352500641102100c03806014451402c1c01000f4030030381090f20440e000c45800400501004110401f114203014001d0820394285604201100c8100002c1082e0360264061030b10006050b8a40c034030403c044000009018402c0d03100f00702c898003641540300c4008030300b900128010300ba960080015030040c111000014203d03814019540c2d03200321940c0c4032403407000e07003138000388800c11007842c102405680c2c03040301c0d9038030440c03d04c00703241e1504210155250880c0701510020380b064240d11241146244040c2e9244994415 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 384240161 1250 384238911 384238949
    0x723030a050d140423040b040f0501061b08030a0b0102030403021507051b061803010b12060609060d08041401090902072f0d0201050d02040e0405031207090612180606 73
    0x8490302d070310700403000400c0d1400c1c02d0419401e01c640c05c0d83c04842c08008102491004900e550b20b03404050ba402005008100f411030406a100103002c1c02d06c9000c0106201ea00304000030684003038000c41075540030001c41e2035a56040040f10040142801032030440c0700501000c40140c544902500050102c0802c80307440e46c0c40741c50598580b600c0c070307050380241c0642d81900150030307114201030f10103182c10079840014120800d004a0b00401e2180180d651041100761280320210380880c0717050180c1380c2511b040000e0b40d9900c09000000b081c842d802040610100030400100b2101d0b0b0701c690761040e0500d080110990707030b4036180e01aa00081d0007a1207440b01300f20380200b04020910382c02d013070420240f141085605041e0005500d00fa021038040c0c18040001046084594150b0459014103a008120602420607003010780d40c0340c000540c00800213100380045406a80516000c0b8111403455a485104019412091010300b001e444040540c0142e410341e240050700720300515014043c40380c0200c07612941 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 384241411 1250 384240161 384240167
    0xc0b0310080c13052e050909060f071407080a032c2505120a1403090a03030f020a06110d0f0203130602091c15060501110723030a050d 59
    0x365001002951040950504075100c0d01c4510000c81d40380c0c400010184d0b500180c020b070110780c0c031902c0b0090603681000d002810869069400c10740304240c3c0d88000320b6a424031415510300c03003585d002020140312000a0f4485205098100a5050400b5a10308104031603071602402c0c2c2050760071346c0210703840f00c00c50108003544010181c1c0c5c0000c1d014000b01c3d0b00c610340c1000e5884800000c00414600c94010345452170700f4410000034000c084c080c1c101080ca00c0700d2100d141d200c81410400b26404441a801034081c120000292003181200421035407110340386a80584984984c0c151312802d6010791188000480c0702441510b0130214000140303991000203009510032100c801140005103032050090200181800d40705400c21948840016a94112100029032a01070005c00040c541c41249030541088003100c4401641403d02d042400543c4d1110015250400c1c1400340030010350000307500308000f40c005e8202c5603070051140c004414441c91074000c2810007400070000d48156002940c508045c1e64 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 384242661 1250 384241411 384241441
    0x9071b03020c0f01050901140d1e02090306130c050d060e011b0f03020f0f0f040b030106030903032003060910080114040507060305010501120c030f020d05151c1401090c0b03 76
    0xf00b4a0700524180644002070446191101007151640c404201d861001401d90303c4154905048403142c1450100e0561000107940300d242c04901038024140401e0700524550805400761b0791080b113640700c032414a8240404645640000e0b6040c81c1ca44000344000142031107000f11003017124901c15054250400080d116244209a00007018410020307ca5141c5800d419a03121030b0701c43c0392860f5186e45150b007003811805543c00c2a09042c20000000640340d42603402200d166120751004e01c020a8010070303030a80e912503c030805643c41020000607840f481c004503542d0344511110560081c0e2a01d401c0360508588801403046000e020b890305000600c10b0070450309000740042c0c0340c107006941c10900000c204072040300a4200d041c3e202c090480a1a000b60001e00219011810031501c580d800c61803680504000e6036030325400c04400e40020f02c20300b880d4900e10f800e55488121565401140c1d940d40c84203840d005094004d55580700c185000145100c40c05800410301038031384684a09111100c1c604101e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 384243911 1250 384242661 384242689
    0x903020705010e0d0609141c08010801090f03030b01031517010b030d0c1b08010c2f06010b1305040509010c09060201060e0106050d02160303020a0215010f0509071b03020c 75
    0x200442a0401c0b0558405101c0e001360380e4042c2c8081410340062418904038070440c2c00e0031400d800340310440c245640d400e0250903959101659190f03800d9981d2080607089890340e0030041c00000c1c0707001180d0040703030194005130400d02d4107150004a13020303100c400410080c950307080b85402d1041550601007078502401103142d05881180502401181741c0b070040e0007419802c900500000106103450fa000c1c5041c1092401002014000e11260114400040c00b601c03105910001110b2078084e50b000440b0b040580d06c1c0000041c100924141e405d019040030160040c2105030030301e00b5a00004112131b107170340c05250f001e41c50b4103001240c0c00c904982c001e030065a40d50004001c5a142500070081c0c100c001101c1811200b40b403c00595991607681200082d2007880f180e000072403084000b0904156041c2e0080c09034020560990701011307000220603641000a02c21002c050151076014821448d08290031a00702907241021303001105026016050f40e90752140a401503080319070500f4803814140100e6a6031 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 384245161 1250 384243911 384243917
    0x1207140f21031902010903090618050906040902060f0d06051f0305061f0908010c0504080a06020903030c160306050c0909040f02010201110d0e0f06010f06080c120109090302070501 79
    0x2800c146004508910a4000c0740500e00310a0212078221040c1030086900f40003041c444140d03001100c2001038060025844111b001600070180090780380d20800040000f4500911004055890f140070007080003005041550700c5581c0b1040303c1d0059603010000c00d600c01c014544182c035601c1c88110a41124460703446280104000040c80280f4048061810304419071030400244a823600000b084007234200d001c5003140401c0c20300740d2400e443d4111030f906048681110003809061000201144d15010310312410503240c0c0100543c80c0007d14640103070856040240031079080c000e20b0ac07200da18004820000094090104400340b00340b24941c028664015480c02e0110311b005902d42c04500d20030f10080010f1700e40d0702c08400d601e04581c0700307400420645064140c210345a041c024140f4000f80300d102d9600c94548507014411003000c10101c3c1d02030482d0080405107950030b140140580c0d0610000341126180d41d401c1024400751010031542a0192000ba10001240c003480e1501030b29000007504401c0c14 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 384246411 1250 384245161 384245179
    0x11817150601141912020f0706052a0f1306050a09060201050c070803090703080a030b030118050a0213060506032503270507030203190210090302010f110c120714 71
    0x311070b40700d085a0315282e104010340c1d070728607600c1800c4071704907456025a05002e00020700d9040701c440540c05007450900480b000c0100c0d407501070444030390440349061031641c6881c1000b4000781c0c40781d10014183c03152800000c149024980600205001ca842d0040008a0004502c410000354800070840290069000800c02030406031a82000d40c00745600091510000100246200c0c07400e1100000443d0303c941102d0300c1c6c00d800d50340034014000c0c1d86003044c000d6107050701c2c900d2254030240c0d0750041d0329002006071440700c500323800f8000300700030031004400259141c210008d00d545034403008620841840000d020023a04800e054406684e41c5000701041606002d1307410900800089096081200e01c034a40742e0301e0b1158580942001c030a40d002a41c18080c00a05141d05210b441004a03154422100840300804101059034150000e00001c0c2c0020103000382441818011144038840d050a88212007104000c41c0000351003002152240740c080e044141c0c108080c450303038440c00e40107250403190804 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 384247661 1250 384246411 384246437
    0x518060103150e0309040e010204051c020a06050a0c05070609092a0e040b061210060f120207210c0b070201020a0e0d020d0b010b040302010207050402070b06011817150601 75
    0x10302c2c40070556410400580d01e04107030100075010000c85204040150042c0465080c0c0d0340302d603000703410601c01c031805214000481050b040e010005020311540c010b207a0401d49042c02c1040f41c071a00410140c00034803441e4a40d44001c06d90401000001305070300d56504250600b000902029070b100043c0c1e1a010300384400c808000c3c42200c0701405c1c115040d030714014000c0e00300c160004020709032405050f0b8000c0400582904c00814109400d840782179000d103c440741c20b980c1c1c1d008075800b50f51000d00000280810414007103156058008003001806001d05c602803080c07440d0140c14031030a202d0200082a43c0e20500810082114502c1341d00c8422030000f1404e101200402419a08800c8076452060740c6c0482840119550104d0503240250002942081c942e112010b02d029580203000c1a405403148040008942c9450300842c1c03200d03070b0320036810000d640b6241c0055071110414003016000c100c0540011409192201500a80034a100300a0020340c103d100d06142d4805c01910403410808004c00102d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 384248911 1250 384247661 384247673
    0x103110d080d0e0c19060507030e0a0e0901020705160501050702040e0304080f0708102c100c09090e0f150709030804030606090507170a0c1806030518060103 69
    0x49001098030084400303440c62801e85807611641075281c24240c9820301c28495058000341c0c10302e03241c9003502d069030203101480720f0320300d41c100c90f110720400100200b0000300007070320407004010300b12400303031a1803481e41d19180700508c40030040f2007120140c3e5000c107200051050810440d03981c0000d00c00038140c000c2c0ec0c000000c00ca40300303600019000b00d444414000811104000b110002c1908505450070000540c8d80750307494454511075400c1603c02c03038144100340d5410388201e8040d20520181c124821401c001100880130300d2000032455401080524402d0a490340140314074695155aa4500d80e82403004003001c032124420120040e03841924902691140060b8201040b4515444800c490307941003000c4403485040d82008000c500302240020420000c1d412078000c4d1003030340e030f4107210036030710700354200e813109854081034002800510201c1e421005582c070580754403146180c1210380c6011001c1a100a02c510750041000030341e2003007003004e50078103500040e00d0100b900001e0030143d491501c0311 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 384250161 1250 384248911 384248933
    0x60501120e070806090a020a060201060506070f0812070908071d07030b0312120709120f030f030605060f03160c031d060409090b060f01050c06011203030204030f1202150103 76
    0x264026552040d04a0001404004603401040b441003202e111789004407810f6200c180540040380603034007141000c0341890041c0540400d40b000902100c1c280f010980701e00d11050842d02040c0c40d01082003104002605490108510400d4540c13618940d584c64811440d00d17015003940310b0704442c410b0640240302881415a042e4000d41c0070315000c80c407802c090000a08041400100ca141140005000c80e00e4100e070321045485051982c0303400c07114039a144007052542d014000c009103c15441740c04a40064003c050001c4001214070740050903644800c081406503000ca10034544005012042090f0b11416103440048400d0503d000da610720300c40c0d40d000e8010042068000c94000c00c0d100c0c050f1a54a134002500c0040516050500c80c0d8081428005280d24007501c0040c0140d150708440940c5501400403600e030349020100400c4181c1c0b800f403104240031340d404c0c4202d080503000c000000100b15690420800f66020f00c2c45203840e0680032501038500803000c0921040510b0840040006c01c80c0d101e41 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 384251411 1250 384250161 384250187
    0x50402011209020105070f02041107060c1b0f0b07020f011d06011401091809020409120809030307050f0306030102070f03020303010f0e0f0604240914060306040809130b10050901030b04060501 84
    0x47c410b5443e100740f00050117400c8903002d040e0000c1021603103100340304094110002c2a16651150b1692011010384075050380c14962021b0249000b02e0032060000d07148860032548054640705440d0180f5060b1030460940f22000c0e2011802d00b00c80301c00303c0c03035181f0074810030b40102494481c65050f80d049071b0018051403087e10a0002c00d0f9003420001c1ea00100340e41003858042e0340104200144c441500e1300f40e012880c103203d0100000d032690006040d40000004890143c281c44c0c5440c0d040914032101d91015900080240d80c055400303110080c001240c1e5104075152034440e8000c2e580701e41c1850000c01d01030007140e02c5041001030000601c01d20010030140c05800030070550300419840000c0f40c1071030f12020301519100c4040b52081d00000d0000352680503e03000d0500c94801c42154842004040d516041618090003128081121095030b02e410382c1012643c0c050240c02141d1032600d800000e4801914041c04804103900164401996a040c4075030700360703207008942c03c000369420040024070040404030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 384252661 1250 384251411 384251423
    0x1021507080105060a03090f030c050105060d05030f0c010905030403050a1e0c0b0a030b1203031801020304110121020f030703060603020c0a06050705071b031403030721020c03030a05040201120902010507 89
    0x40c054802c14070a8008046040d002301d601c0b1500151464000c0c440e410500c400c1d1015441c05010a4a6140072410355072416040740042d07080007110b40405485074000f4420401c1e81d9a108000d10000d4000c1c009080114000c4c00075007042130903810018403030102c1c1040350500c0c0241b54940c00c00961a4404142912010806d89440d408040016401031989640c4213501900c250241440044004015441403400c20f4003030095080c0712003080d0913030000b590300401a80101d901281e455120340c2500201c01d11200e080f000f8120a46070813404ca91003040a00741e0f0040001c10131210701e0b014020b0030014200ba10f4118941030800051603290314034200010849522400414041d80c1b1410980ba4000d800c210b089155070901e880d1419420030300d10046809003400d00d0708008460000c810703688202c07210b459aa015190030740381000000b00b0031540e00d404540c00d03c28bd0014079810005035101c2ca801c003000003900d040a0002518038240d1b1544640d4890a0404000c010b0f43d001050320941e640c07001d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 384253911 1250 384252661 384252667
    0xe0106080415050a06060e040b0607171c060f2c070201020f04060302030a050106030203040510020f0f0a030e151b030901060302060a020604030905060307050708070323090102150708010506 83
    0x860003142000014141c0755102d42820140030100c2e0640e401441110113640f580110200302034140030950740d1050b241c9a003c0024070a0401040071580c010007182e44a0085034034024144002d00b8400302c3c2c0d81c0f40454411b545240a00c280080255400058041c54030140c800404c0b070800ea109c00d103a800c010448003081e040228100798003d4040c0c0750003180410380217459903141c40004009401c110b070440d8040e81000c00008486000c0d1003243e008680000c007800c1d10000018450300a94408031000040c4402000801003103003c4102806c410409546e01240300f03850182c4a80c6001211118001d801288800b84240e00c900001300c0034070001003000e122b80b86e07030f1404440d84c01440306030701c040c0d0041c80c000742a4448503800b0910358425482a103964120540b5241400013500040300d042012030001c2200401107070a09001c0c1200758401e240c16a850600c0901c2d05810058424500d0001c40000c14900758568040c0481e080740e00c4044001803c5180c500b20041c4148018401c15002e46000 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 384255161 1250 384253911 384253913
    0x2c040f03030b0a17060a0b06040506070305130b070302060f070f030905070504020a0305090f030901020d03091b03060617010b0f010e0321030402040605091317040e01080105070807090e01060804 85
    0xe0300400c950a030002d242d41410380d501d010810302440b20030f5184425001713260003c0e0790001107100d0140c002d240640651304042c02c14007800b07041d6000c07200a40c14060140f107544800683c3c101c117507000e003003040b0a042d2102698034000c0c2ca803100c003810030164103405000704880640d00180701d82d481d010924020441e000c0307a0030030303034100700d8107400080c0c1007800003444032100b43d0550000c501a0340d05c10210342030f0804000000c0d0b200c0c01841609401a0440441019824841d4000440c164002e440c0590702d80340c0380c60341c814007005079030003155001c0d1103540070019003000107a030002d021800c03c024400324000301e00040701c6100040c0c82c4c50500902c0503541802d0788080109041d03980440b13258100d403620b40f001c4030740341d03400843c1c08910035420840045002d0811004050140310f12404182d000c4109650b440c00044840290341c511850034400018548000c952050003010803000010b07942c03d01c0070300241561001000082440880d5000f00704c149071900a03075045801c2e82ca800d01c000e8580b = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 384256411 1250 384255161 384255167
    0x60e0f090a020d1b0207050604060221041e080d1d060f160c03330903020c04060605040f080d020d120605040e030a020d020609030d0b120105010f2c040f03 68
    0x55040c40034101490b0418260036000109080c480fa048285c08840f40c0a65803010401288070b40c1c091240180c019031880386951500d50b824004c00c00500200508282c1c032120140c05110030b20340100d4410000440c01c0150145c18030005600ba03c0528001d1600c80c5400d8500d0810401110502e000348000110025221860001d4a2211011480c0e40098254504081c1019042804240c6081414100001242512007445c80e00152510400c19050100c150114018526040198154040c041000c1417558443c03054002810140c1c03125600c032400c00c60201c07545c0440303401120840c0d1004c2d00d165a200d40003c1c0d00203c0c0001c611304a12006400c00580380940a40c2c0e009903001400c1c09007580200102002605c030966280c0c0c01c072840740707000b0316040760754040a445030001c40d0020810000100710035004010403600280192000d4030010800320700f1118240c0c084040845201c809104800001c11040030312000540d0440418130703648000240040082d10042641205001d82410180 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 384257661 1250 384256411 384256417
    0x311011b05130e0115020d08070906181e140301020403050a08031f150e0f0f0d060608060f010815060618041506020105061207240908010f0b0a060e0f090a02 69
    0x1d01c680b0b03e1180d40d407241114000c07072082e03454a0250140c40d8080260300e201e501024420482c640e10b03118402e14080c800d6031134080943c603a800d0051034000c049822602040032040f020400c00301c000700c66181948030b01c3c0240610011130701c20307401044200082a00015000c9050390040b40a0f1380d06c0e10f40071480c0140c925441d2079000c1103241800c0004d445983e81d1324041c0350011640b07680300e508000904219000104d42140c55200c0d400726110100350502001900c1039038440c1c980010010703150502c240c80d14004441030071800d40c00400611804009004406104100c00d4200c81d1a04103100014824014501d40c5007044154050318852556150042d1140d48a20f40c041c080d403548550009001c3c14007101c0301030060008411400c0c441000041c21070440b400c0e088080d444c0200350302501141d044002c03090080010030b2a001c540e038002842440a5000c54050005c0e000716400240402c0d403000d98400801d100c29076076020100d4503050903440e040c503002c035460000d13603480d54244c4000340 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 384258911 1250 384257661 384257669
    0xf0609150a14090907111e0a020a0504050f0a020918091605011115061c2003030405030312090114130611090108040311011512050f0a021c020d1703040311011b0513 72
    0x180445685a41001f00441e6419542d4002c0c0d6901f10200d0302c8005200c00d0b40d909560b02d0890400c9a00041d418503941d034054007400000a1042000113209900c003000c506007956001444d1700122405400d038086d540d440320041c070080c02e01d6000710702c1140c4d174961203010140d03400074420300f0300000905941c0c513000004c88828403100d0864804585042a4450794480042c0340c11466103010100d045142c000151030807034200800a5251508190100d800b03003101a0203003000790740381da52140951144610b000d200300441e401c0400d540405080030400e03a441150995507031075040080000070b0741d225402070f0b400303501403c007800500c2d2880c61a900400c0c0c008030f0188503001c41080425040500304154414901400c11100c0300d1104c240c60b01e44410000c1d100035803108103984c40041440044009600850005061003982c84058480d540030385c000c1400c0158401c000800c0004050300b059000030090084c070002c02550250340480104602042c10b003c0c2030010204015000703070b9200039864050 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 384260161 1250 384258911 384258943
    0xd06120c12150c180501090f03150212191104060912170307020a03021606020a021201140a0504021c0201050405040213091506020f011a0f0609150a1409090711 70
    0x51004441c010091520f0030302030104c0d44141c00002407290702c00c040b03400070354100b03104031140d040c80c642c0ca404220908408004025800f40402d0220080840c0c005100c3c031a031140e10f200040580c1880400c451401c50800c0c41c030030081c0820302060b644648243c06031960614011521600f9003007150802045290306001c3c180300100304100e9503070100300880018400d80886900070480142e08140c90400d004010041c0e000408140242c541100001ca190520a000080703c100d0288008c81282003141c007900640e48a40c01d001c02c50a281c1e40d0120f81440d15900208403038003d80c0000d040b0320551043c80d20568011404070445004014450000c01000104000c20030620400801c1c4052910441015020788002e010094006000300b03424400c17090190384088402600f004811644503000507040341052101520940707990746140c4103005651070300340c0c44403054a0020700071071030300c040b5540284040c01940180d03154038410035000308013402d00310003003208100f03010318041c0c04104145034 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 384261411 1250 384260161 384260171
    0x6010c030e030703232a01120501080d0e060903060414101b0201150e06100516231203060f0d080d060e0105040b030d0806030712080d06120c1215 64
    0x200442035042c1d61000031035000020341c90b0081c00f1780c181c444529481c6150348480706c0e81146154508013075085403424050510240c0000f403080c0b20422103400b41c000750104d0b80b050150410060304501d409011071001c0301c0c000d01d0055001c8c0441e031a880d01400040458130240e00c420300056091006907005034a003d001c102159162110b100c6030340c103000c0c020000d54600585002c00d00b1051840c01e050b19200180008552502c0c01071240300c406541c0e501d41004414030008a6001d50001442c41c1a80910300e08101c2c150300359810340d00d0010f6102c40f1034040d0302c07400001a5000e080001d60b540010101d500b65408140c0300003040d48064034130001440c03030900181c019080d0300164000ca00741c4001e0220711640742c0e00c0d2828001152518582c03c0d034136038008284030b0000c80c03144190030b5210f0805001d480f6065520408084004405882150340080c04550317061071101038440c00b0001c00015611451140503074443c0180c0c0d80d031600840040c0d514a16030b5400340400c0a943d410701c1c0707100301c0007040 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 384262661 1250 384261411 384261413
    0x1060f031110050915071502040f060c0203100614310b0607050601032306040b0105090703140c090306090c06070f081210061b150c0c1a0702070902070b06010c030e030703 75
    0x246c0c409031089401e2412500c00d80e20651347c40c0f083e60180c42c01d581c1e1240c801d0303051190903a09000b10303100480c1e151241d25001200d07600d01c0d000c2c03040202030581c0003221502014040201e03000342504051030a4101c1e02078043c0040c0c0000da03c00d01215590f0300051600c2d00d91000c80c0c65885150000341c00d512480380000204050b55000325a100c40300c81d81d220040c031001441070784a00090b41c0c00f83c00707003042500602203071a14203103c50b00300a2500303000810310202d40441c0415032049545248500020034040342078101403200b1540038200c0c0d4007404012401b0000145a40110700020304084901c1d45d40d402000020403c8407002c100790440d4101d14903110b4038004904241c0d001c0c80c00001c8443c81c500201131100d00101c01d0700c03035000d12060100c001221611009040000c4000e04010002507c0d6003c00d103403040c1407200707404c501a00d6005181031040a45040540d80c08990401e03c108001000315104a003440d030841024641603240002da800c0c1221001c21580103280e05010b1268004 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 384263911 1250 384262661 384262699
    0xe0a0b0a08061f0c0803060d020a080d0212040b0d0c1110020d0c1e1b0816060c0503040f030c020a17101109030c040b0109080d050c01060f0311100509 66
    0x28410b2204580c0b11240c640d001038443d0b00003103108100b601061031030721040b0006400c1c402a551007840a050b1607050001da400045003980246e00c01301040c1c00111071300806076130621040000c0c00420342d1441c03400780780054086003445125444035800b036480d0145c0e0a03980c4918650003a103415901114200001c000c1e62038006c2d4005c95040f030103107103001605425503000703c640710880841c04840c4403501c004c0704810380350030b600300010300300f1800440081400500700380040c0c42c94181050082149024610303006007141c40450320141440010f1080000141f9500103100701c0903494078100c404000944080f4404000641250110002031080d00048800000d00b003401aa40f050f030910200030301c1500050300384a145401900f58000000e041d00c181416002001280010700d001e40000341c2d40ca505500340121030450300c0005000241d071a140b080c090141c0405000c000340c1a1500e2031543c0d4840005100329440c0c4c138068010782012007811130240060340e808140140003591440e50107040d00b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 384265161 1250 384263911 384263927
    0x50717010b040504030c060b0604050a0b030a0e0625120c020f0d05162006070302061f0e04120201060801021602090f010803030c0d0b0a030b01150c11010e0a0b0a 71
    0x11020540c0780407154500391405000d114056505912070b00b214116507196240901036020340c1c00d401034010040041d107511903007040b000074503603404229281d041c02c41044040c0c0307004000c140c441c0e610075401e00c085400b43d87c0d00c000820481d103001440d400c131403400c107030341c14110f507403080070864a012100e48545402099142c0004254002e80780294141d00c01510a0700603800e244400f48004807109001542c100e02c00082c81040399440782122440340005401a0300002044005800600510a420400d2500100003d02c0c9900f803400050400104803282c03100200050000e03494859900400c500030742c0800c0240905100030356450b03501150541042c98581c0c0100c0c02040d2081c002400044180c03101d50580380f20b9409140303152952100d080b41a08412912446a82d43d00c0c0902d005580740b030b1031000194420381c290001d0750f01d001e2400090701c40c40c00302001800102813010f000a0349a140c004c0600100742400c2c1c440c1c2010b5800302c0d0031041d682d0002d0001200007d5a040d01030707002060 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 384266411 1250 384265161 384265199
    0x1050711150a03140702060a0905010f0513021305060603040227070306150206010503030f030408130f05010306080109030e1212030103061a03030717091f080105030d022a0402070507 80
    0x20600c41c0240e1550134640705a41110765100617048040401d02d00c50003500305030310940c007074800410902e401c0080307041111400c4c0c4201c0c2c1d940d0030040e0031804604080a6181c4084c420100400031031500788007092580c40000d10007889141080816026620150f040011404100700124000d07c0c00840203401041349024500c019103a40011144040c400510541038910160145003000303420340c0800156040980111500c5100b403240e0190440d1442422004124200d1000c259900c2d00c000501102d80320780040200da4100003441c80440c1c2c21030490380203c2800e95440d0307001001d410700103061524807944d002003c18000300004c240504c54000920180c0b9140d030307004d85088030304101940c92140502c01000201d1414610703880302056009080403c001502485446d010040400b0703000c5c02c900804008900c1352001071055040401081c442e9000c139000070304203131850200316101c0c220308030b902188000100520000350707240d0f42c0646403000d03805801c4840752a19000505210350960340 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 384267661 1250 384266411 384266417
    0xc13061704110a3609030c02040207050f030c0c014a1005030a051305060a020a053c1804020d09060504210f1209050106080f03180301060305070501050711150a 70
    0x103200080e0204c902c600d15980c1d906071110349800d01c0070740c28800650031030b901c140c03a58001ca850080807004180300030840b212802000d0041815100005424000c81900303c003020280105996030750803100442d1609107400d550780c001c4401040302000e003c6400c0303040c520b03040500c10043d90f4038642c2160155020312a500d409000990390780074042d000244059010b4900d600c81c1703011600c08106070740144076403411803a1042c0f50030744401a1254010064403059040e04a04507041100300710044d5641924080e080000e01d4890340324090900510b0f00004184034541c000742154600070382d41e0000c5601540604240510b14180c10302c41e46a42059180032001d0002000c06c50f00c451044003500d048016948a2414010000c0b402c00d000301036045003281c096589a13404100d90308208081d20007501b0f050003e40e86c8550007a1a006501481c01c2100e01076814042c0500004101041031804d0710703820721342640c03149494200309030800026000b4581011001190b45d902030344d110010030810741c0c40c0d2 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 384268911 1250 384267661 384267749
    0x70504060f090e0307110126100303030e010507050901051602040f021306030e0703030e12150603010b04021608090d0f0b180309010c0803060d050102030c13061704110a 74
    0x110b12652a8460351000501480303900280315007e40c003440729040d030050020242c07181414142120303801414141e840c440b0807074102404008240d418061151000103e600074801d500700341c040907000d4060804d416060101c00b154151010b01135202a05a09800034000d2140402900041000354451302c207950306100002e0004c42c44502074001d01c01403061150091441c43c2c42d58804580303186210079010362060404d1205c54090004000e0000e00407400e5801c82d40e0b40c00d042c001c0600710354140024a00660040c85008201d505070488908456080705035255180c00700f0f0001000c511600031b008060541259185003400801c0548912914401140d6200c1e05490414107540780104402540050741500a20300015103e80213140c00c450050000040c10803996152070982e0400c0b980f04100800124071040f035441c1d08101d4030001c004500301051040d81c80c1000c0741c000c00f401080074003040b007503c5540f21280c4038012298020119031140c60281541801c464018104a0004a0390305181e0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 384270161 1250 384268911 384268931
    0x190501030c0e0f070c02040c0309080d050f01050d0209181e0705090f06031c120216170f03011502030412030e090105030d090e0a0b040c0f0206071805040e070504060f09 74
    0x40030f5850242e074160302c80411401c440c1d420000500301015068041507110601040081e450710058210030216000100303440c03601001d6090129416805a4462082c510303103400036803a00d41c0019004001d00305007840c0c04074408203080c41c185110305020319003202c0d2001038641d030320085050000d48000f1504104142ca0b0f07042040c00041051b103c0d141c0c190015501548440040c1072018a019140e080003600201040c2d0f070354040740c02c00a0142900c00c41da222410410000702e42240d801c00c0d00c2035200e07007032561104035100d1030300050044e020300b2041840018100ca000300140e600418106035600c0e80041c0e5440c008265009102c81c40d03002e0b4a20700004506854003003103e60f803000c3d0076590360380780c01d00d007929030840d07003001030035082c0c40981d11041c00c1d081c3d0702e560107840c0c90403030306da191190301150059009152800040030f110400c506000244000706240604008440c0115000700d0110003090006003400302c55400703c0c3d03000e071800c03000054406403168040110f40d200303581001012a0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 384271411 1250 384270161 384270181
    0x140102162913050c0d02010909020307270e0c0c07060f0207030506280c021c110106060203120c040e010b0721091805010b0409020f0c0d02151503060f190501030c0e 72
    0x12005e402070100d0307514a810702421010354042c1d90701000c5454003c00c00c000c1c28111740d02440e2000342d10155800042800d11555400701c005a80260306c9140092404141c40400c603194045400b8120400010303044212440e0701c00c1140c507000d0358000058882a090a5041d441d08190221381c0720800140400b640380310003214482c00720140856000b90404400151111102c0f0a0f501210310034004a000640303094402441030710302501c0c054000390350390113502100010441c0d0040c440c05100d081040f061112005400e0050f04681c40e46d00100e03226481c038502138021840004640d034283d411440841c0c1c3c1103a1140000c011600b540c0310301860a12508910025984240500542d061080004008040740d5034004c101c14a440c0200c031b81065a1503a0443c10580c4040c2440300503440b83c29800c19200d5100501071b001480601c03421220500107000c0703907d401d0010040002c0980c0400080c01c0e080c015004801c032058ac500042000e9038581c0f070300808240441c003d028024001d08000344184007 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 384272661 1250 384271411 384271429
    0x1107050105240619210f020304030e0d202b0209090111180604080706090504141303140d0c0c0510050601080103080f0f07030c140102162913050c 64
    0x413803400311a8440c83c1c0190142c403c1d41554508150a06240d134102c00c844046100d2699004204040941c3e241080c0c00c0080c2224207c0c03607994854081050701c00e0000708010000ca40144180f06d0310881c1020890006580254010202d0f12807900c031844043701c2c01680743c107560141d100712880c00c2e03a0744485148508075040b01c4040c0a40d940c08101c040c90200c82c403c1111500a8010001407030281c89481c0141000d401d03a04c04000311b03ca540c010700152500703000d40c0c0b16542581d1031103055464604003911050700109000f5003400750548520010300b800d8000c03181d0700740e2404400d01004d200401c000703000303100400094625004807074800d201e2030000e006480c020901656000f070241d00b95141e1108a90041c4801c40300c4c24000c1005c50700c0910381c01c0182101500a8541d206120a1410015042104100c0024075640b040019110428220305507521060b000f120450030b0060b40c0c1c03814120120055006d1002000310707030401030300300240c9176601c00581c81a0181c90180017080c0510050003 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 384273911 1250 384272661 384272677
    0xd0806060a08060a05060c060a0e0a030f0f0c061506020609060906060111070e240a08030d021305040525030b09070804030512070f0201060b07080d11070501052406 72
    0x3482000314558a03442200002c1d0056001898050040d50f038400050082d4041c5440d0542e6030003c00c01c01910708190710418a2214101010b0402040b15a078002e084841c0b0030074110900c80d4210724182018403c01090348c0d86a030043d02003090200385059094081014070415005120340400205d6192011803054020011b000007007509031640703001034482c42118211001075204410000500c003a541d00360380c2c06204111079140c1c0e104841481c41d50311501400901c1d000b9941104d0402c1500380000841c0c065102c0312000688070f07102c442410583c440154070055005040c00144041a06000c2c4100c4200b041100700d5514000c5c1031009170305540c03214418030750124013840006c1d43d1034015107a81c2e9000c2e200b4a405e515121694a1001188109940c85400240407404001c0c9a07502442201e011301243c0c0322203800d03c0c0c465500d07680548582c0755401e15007902c0b000381345034255014050341c000d294018002e1041d0f00d00f200c01d548601545410240c011054295089094107004c000c80e4801 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 384275161 1250 384273911 384273919
    0x6090d140f0309030708070b0f011d060909030d050a0510120305040b0f0d09050c030d0201060f030219181e0515101e0302041d071b050109080403050f0d0806 69
    0x40c00c02401501c4680008000f2011404100404070000d100f0000501c055440b400d0900c1a90405181680100340305800000518401e01244892035050180c0c1c550711240803540c00c2130b2642d135110701c60f0543c041d20408108060810741404035540d07030360300054421002c0c0c1003c158229030b111300c0e980300c5a02e4410082c3c08104c0c20007081c0542042d460052120a2803c111645440d10005082c001c544c000d80059540b5001030525500b145420720a84241c0c408910003880090b050000741e084102c00c0b0700c0000d00c9071082007070054660480440079001824011105c0d070303000b0945200c0704c005c0c185068110052000301c070301ea90210b42c800c1c42280d003d1310039901c8800c045150f0b0340902800301d9007024908203012108405244400201c0e00e159480c4c1801d5a0141e11b0b01d10740400321082c071910700e11100490343e151041203001588403100c1d000c00c03c5000c0d00b0500030503440c00c0650040404460241951030006008014003000040a0a15101340021070b02e004030014002c5544210643d10035a01c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 384276411 1250 384275161 384275167
    0x1205010515180c030402010513030f12020303090c09041407060503250905060c010b1f0207080a1a0c090a030305041706040b010b0708041806300305220806090d14 71
    0xf00342419009540d01501c18140342d032404000c40b904003070389240c40e4000c948003200d43c10021b041040c1e480592018412074001103044d410800130171034803040c20440d800d0141c12064005418030030400907841456034884280c0b2529501c8800003000340d8030449040b203501420020240c00009207031a0700c0d080c800981d5543c2035444c100402c004d0554090000c0c0f0342250340f82d03038001d401c69580c1d00800c01c60503041801d1485003c00c1c60406814440d65501c5550950004c001250200e0f60030340d101001880404440d000b142d032400d014103110b0003052191a00b104088401004051700400100196164041031a50003840300c03004545d610001c480c01000e11815000400000018001031b1152511074a61541450784070380081440c1020846209509500c81c030301003048144980b00d0000010780c280251004911444001058820845009041283c00540c00d03810108405001901a02c04dd120989890f91032148a90b10f43c01170312409000d008039010f0700310325400b80c402403140030088148141 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 384277661 1250 384276411 384276421
    0x60105031905010f17010509060f090a1712011401020a1e06050f0a11180d020d12091406070c15031401031b0510081609120501051518 59
    0x2429800c05096860514141c90140d0808492401600d002e8000c031401d0103030b02c42c50000005038840300d4185003031060745084c080c8242d4a4001c601d144c4d01441e40440490580c03240d024481c0b8000a0820140054203800c85185070742d080c4034010280e040c001c41d440701050341c0350842d01e00c0700c40340028464090fa10052105c2c001940404078000010a1600b00c031180e0351840d101e400554100b1030b4000c41c8910341c50204141d420680c419204412901030145080103584404140c0d1408144000d80c40343e41e155221404554410240c411201da01c014500743c14094604040c000302a540034000741c1c2400700c035440c1c105061901c2900d112a0b00081903011492a080c0304100c4030045480c56400c140d1507000e045d0300005400c20700c60080d84603600c0c141c4e82c0c0c0c4180440088001841e04408d124140b01c18211302e503668080b12864002c550007048210703000c460301e0240e480e1902d9a108203c260340200d0740d8024000194070061060840300781c002c020030740c010104140900d041440e103420200c034001280b = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 384278911 1250 384277661 384277667
    0x70b1e0708040503040f0b0903011a09041b03080d021305100c0204050901140711061501080415090506150103050c0702060406180b04090207050c090108120901031b080717010602060601 81
    0x50340040c090f00507607240649858200f580701c0c0d4160020380b90b050380002e8030729683c00c1c00d00c02d0944a09989402500882202e80019034104e000703030024010186614001c0c03148420440030360010b507801030182e41d84147e4003040d00d010703401c426030460315000c50f1a0001260b05000e0302032a8103101980c0d403800e008007590708100092102038140c004545d40c40640303002e005007030180356002705110b4aa900d040c00c5146038007403806100034940c035070080c07015910360b12690700b1500c000c7d0071a80c07100d048a0360400505402d0f0003403080b032001924601c66581070140e1081403559618045e0f00a99051000b079a991400400318401d19100a4101504100070048130348240c2144590b5400c00c0d6810141964a19403110280c00903001151001d40c00101b640c00c000c003c00c5071600611080d202800301c0e61504040700c0d1a00c3d03869491004030340340020711a04513803091344003004100c92203450211100480000404450044426038081460708140b00b11108900034954129a859401010350b550303040011 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 384280161 1250 384278911 384278927
    0x28020f030403260f0a0e0a02100207050312090a0312111002030108100b06180a17010c17070c1103030906030f070305011d04061a0402070b10060f020c0d030c05060a02070b1e07 77
    0x3118280c09038403105001603842c5007a004003020312b507009041e40343c284010542441c90261500210400421500c4501d44134000c0d410100d030b0f04108180c1600105e1201943c01807c00c1000c1c00f05800f41e000040921f89007540614182e409400c1242c0c19107206030740c1d4030100c45c00d0485950380070070140400e50300307035000181508150101500605845940780d041c0141c00310102004003040e5191081146404c3c2d225088001043c40036032001c0c82d6080191700500216041c507000360048451686002c880c1c0c4040084803004a806482c6c0c1da0391b45041e070004a04031506444100000742410000200a1000651294501018562900d0a031501e50362100248034000d40c000c80ca0404a24013019507950f48050710441d800303050b030400e1a18181000c2c0d20b181c03459800c181d0074082c0c2d09441c5c9001c981d0004042254001c01d4840d24080d460500f0256004c079011030000307129102c1c1004000e0040c42071303000b0300030b50741c0301e044620242c3d243c2c246a10036054140b07161040d034081490009861521400c0c0c1 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 384281411 1250 384280161 384280181
    0x4090b040209060d0c060806042d150510090311060a050f0306010c0204051905090d090b0c030d15030c050103060b2505250504020328020f030403260f0a 67
    0x100002d813141c19a180c01d40419150300c040040b0b19070004009082c1000d00409107134180b82464a441d8884100f440c1e1800511900e0803d0340c1541c03081104a20942c4503404005840c00030141004009900c000502840b1240800c403602c22880c0c034103c0311420300340c0903070f00203071410748813070b8100312500d4103201083d04003c10485c10000c40804c000050303103552040c507024012452411505032060f9046900b41c1c0c101500702e2485900c205180307045954032a003400c0035188107949941d582c19218601e9813a5019101041e4030461401c180800106800f80f420700450f4401c00b000c480440c3d5070001076086a0b014800c010480e001000b2076000680c04020440712800c21a52504230782981d5147c0c2440d0808911510010b8151405100b5035201c08698000c01060100ca0652541c0341601e00e500100c20440842c10318440000501035410806406992854403070f161066224501800c004110319040c21012025094a80c02003080d04200055203226842c4103043c0c0c880364170f8004500340185440c40d0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 384282661 1250 384281411 384281419
    0x1506050a0207030b0a0b09090703050d0e15030108010615030204080c010f02010906050901050114030a020604090e0a0f0602040f140904033608150403020606010e010306030816060b04090b04020906 86
    0x60100003d007002413054041c00382c504001440d0340311101401800310029003036030015030008404100203107001407150703410061850042030410840011a000381402031801d2011040400082482c0c00158085001c440b11a12644501c002d59003054080b40301c2d43c02596115009410068555400354500c0c5803040c060740700024800f005500e91408a440603075140a80341d440b2001000141000b550680c240031088014084d902040d50002d04144114400ca130492901c40340200240344003480b84a102581000c0d01c0c603070b582c03e035107403110081d440346c0990344401034501d1000c11401c4204012001c00000030300321000135191501c0503146004520b11129080000b124280342209641c2000c11801080300c0c1c0c02a601c50a0122850400c4100b2003203054452136002004080307070f0f000907219004002030900012010f01c00c0012806401383d40c10290088000003440c42c410740c07202c00b07a102803d024010410040c50100100b10940d0301d081c00c080c1803080c0c035030b000c200513281102d555074011000038 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 384283911 1250 384282661 384282673
    0x19050712030e030d0c0308010b09090f091c020a0501050c07050d031505030109030809060f1014010e0607051c0503191d0106081005130804090504020102071a0a02101506050a02 77
    0x3800084c07800c0d602c400644001440000345600b0180c02000c00d501510092403420b0071b0442d003001250f40c043d401040c0c01210340e80c44000c20a0040c06100324113500b1568400c045c1131a904c090040d56072840040f046078958602070008450303400d800c0903544001e0707101c0040c046062400c2c20840c060000021803a1082c10003280008555800f4464803a100307110303441e0341c521490942401070403d80b008002c8500c0500c03230f50030060102614031099041c0c0304028042098504070740012600354414090320b542123100081c4200a010b40003404207048200210064903080303105e001124103000950f52206541c2c1d800386900c070101c1081d000b016000c0c0401c00440110400140e0301c034251900c1c2d60281d2065008250450355001e01d03801442d9002118480741c00c0080c1260b5145400d9114601c8cc106284d55954081021613200344120b000500206c0001c02c9144907510380c510705a40101c88020251280e410100c803001010b00843d01c1c50a0312801c440c400b07510301030303013070714558030440740305085005003 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 384285161 1250 384283911 384283937
    0x606090906121c0e0d020619030f0501170d0c02010504150c02100f230313021201050a0c0315050d021210020429090f0f03010605180601021905071203 66
    0x100f0140280000c403101515120860300c20107005055080c42d000d0140000d03541000140e182c91085030b4442404c03012a8541c03920310702d03045006146584540810a0825000041707000144140c8440b1185c0103060f1070074001c1c0b10500b03840c03d110383c60000b400303d881030000704000c1803110780e80c4180b0b0340340c0c0c1004140201d290740080c0d402c03028200c052002c030308460102c4101d198000a651038402c0c101900135220145024040594040201840c040001d0307040203c0031501c9111541c4d1035040040001e1001e4100490150080c110003d8814002482c014160030407001c042c1d0044101e400103000c080444040d9002e020400c0040c50403440c1c0ca210f100d85660022480c0d100920003840380c001503103500340d440c00d500d00078528428481c5003c0c040c1130154107a160b82d240c0b000c040d445000c892002030b11242e80c000c240507251690015a00040c500d10008084181180e42440b449003607090fa00d000c6a01072542c1202e03a6184405002e40d13000300b90601602e1543c1070080980d42c043d00b041c0440c0900303 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 384286411 1250 384285161 384285163
    0xf06040608100e060f0709140d051506010e2209210807230a031d0106080c09010e01080a0f02041b05070219080c15091026060609090612 60
    0x442c0e02202841c41d40c0e21071041d0810707018041143c115100800c0d0310302c14240280003c055020328012065030708405045001141c3d80d0003480c98083e6804001d40360600c0b4039400540720140200c446c940414111a80070286140c040d024a5090118202c601025001181d100c0020007031030300100d4007403040039810501c02280e0104425100ca943d5180a200c4c0781031072004102111a82c00d803030003010184081c00704900c4510036034240981c51303e00080d4040484c80c001240900c1a0a0040300d5403a1550204104401082840464006075002c100699803034002030100d100c24445c60707286070048455540050107810101052900060010400d050b0b1240004002c40c02d891050001c01c01c0028894110f04003c003a110300603001d4044020150b1400344d05640f190b030606140e511030803c60b1f08030220590a00d007920040007002c1e082c44443c45400c2d02c0a0004402c0000001410105101300c000d80e82c40c142c00303148282006001903040450301d40a220800c000074000c1c41d8030009000310a294050 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 384287661 1250 384286411 384286423
    0xb0a0314060103061413060b0a0b19020715090e040309050a0e0a0c0305160e0301020706060b03061203040f0513021204110a0816171504111203120f06040608 69
    0x6400d01070406540b540c900b510131600c20a0000003858805c1c0c041000c64280c4441d1800015040f46000c02e00106510004600c03441a4006a40181c0081000200e01d80c48000e02e503030303840198003260051030715100c00d60b030210f01e48804480040d51075142807144400101c055134115100b070801c0a2065102c000003000c032041e981010041080c1102040174208560040c03509240365414108514100001d20725403600b17a03000c0b4030050108600007900540c40c2507045440c9281c00c420704002241d2980c40041e640c1e030081c0c0d1160304c941d14502e10071400b07079800b0088508440b05000f03045451441c20080c419040422a80700d080141d0901c080c2e1035800351a0109031040d8410b020000b18035028400b04944041107030040901940101d60000051103602080d005a0b100264441c10680710045070926284510700c8869414000d203081c002000741107459403501050440c5d03064400301c800100b043c0c1d02c0c0105921400840815400f040c103c103449950650001c5c8090000b050fa80d03180c01c100d910b801707 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 384288911 1250 384287661 384287693
    0x12180305010213060806091537050102120d09030905030a0b0406150302060313050109170304020a2102040914070b0910030204030b0412020106051005070605010608060607060b0a03 79
    0x70350002140600c610351401da81000d421a401c0011041c101180440c24001c40108401e041d8140070064100c155560014411811003445000c81d00700c410b000001a54401c00301403164031180c116020805600100385500c000020700b080500b886072800b080303c0a08500303c0d040d024455483e0010031161000e01c5000303021405000080107904040c9401000c0b40c0030b000c40740200e20320100080c00140d0b1041c0407039402035030b400c603411480d03482418a5401040304600c001c01c106080518044c003080d188004c1c1d407007a070080720440c0c6819951011001b0500d180884001e9820a5240e00c0d030052400354000c6842da4095018940408002411645810788a0700804591a80070619007054a01274aa254110b16945410350905255a8684442400160000701041940716070720081034401d502840051500400a0806010010018100307038005034060300c0650a280000c20380500034049680641c4020341460315140594030750800901d003111032035900c41620000000800c80080f4454900 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 384290161 1250 384288911 384288913
    0x31109071e0e090f0709050307060e04020706060b0403030210050a02070c05091306050c27060306120a30030c020715030213080f0d031802060c010b210c0f03060412180305 75
    0x2030410400c060b11b482c1550344020301c00c0e4840141440600d51100c03d0307046000d0191000740c0c480d00703103240440c0a8a0039801160301034901280001c1031640c005028448010b02c0c2408014503202c400040007644031320b580140420141031001c00450615226181d8009919101d40d401c41c1815911041920800c0e51680440f2001103924007840f80c050001248041640303214980c0d8121410100700075020003444148100d20111003e40142002d20039000b030715038450056014ac1c9080503000f00080c1d5200034010202c1c07000f1207070301c400078000e11403429182c2003034000f0520345152540701659100d032500b050007015000e004800c0c90300c21004010002e003640e40d000d0005e04483c2c05d4154030308a480d414200415090540030340510340b802580000702e03601501c030107a42d00c4480c500c550141101e94030075a0040100c1000f100810346110950007403c0301c08060311380010802080050022101c036040340d26401000101d00001c0c0c64240324440c1c0301c070340e007041d0703102e0008483c4208816900380c1c0306441b1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 384291411 1250 384290161 384290191
    0x182134080714030a200a150f09170a0204050c04091e0e07060f0e120a030305090f0c0105030606030702070e07030e07060f050711060f13031109071e0e09 67
    0x141e202c003160810003000c2c1c00030100e0903044d442d042c00460240c2c015560902d00e10340c40c1c1c0d003c1d4a410100c000541411094046134000c41c0500501164451480e41c002402045002c24400c0ca2411340350083c9041500401400001e902040b006205c0a03081c480501c8003044000f8003c402e078050204140d00801c030400000f00740c1c1c5040c20903940015403e2020307402c002002e20865400c0200070248070400d140001c01e9110010210303603000d0910000e4803e910880c1100410158550401c6104084002c140c4550119650381c1e5036481607041040ca001c0b42c001d0002811900748200035560090661048a08840e0760b2480040b10b040700780c5841300000c4d1a51040320091004120b1140103040b9458480c3c100c101840340204030f401403080042208054191a2007260b41e01c0040c0c84014150180302039551003a43d01f1441da403a800d100481c3c41040780e4155585600d0028841480b403443c0741c9031104001c48080c1f1007070031401c680601909003e200f400100e81d0707071148080700740714070038008000325 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 384292661 1250 384291411 384291419
    0xa080c010b0f031207170c010f06090204080304030f060906020301080318090105090c0703140a12060b070c05090705042417090d050a020a081821340807 67
    0x800c1d50800748101e401042101d00c2e1400a88001034960102940440120780713450051500e44c040d0100c5180c3d000e40c0351008500040c0318070741948031000d02c2030f590b40704100c01d83d0f444910350280d00440c4181744c0a90028407040011601c00c0078031800503846a03d00150500085d540e101c200d030402e812100c1c641c1c0c00441e401d00c464810224140714003c046030703240810b41c9014000350041300001c112114062010400e02c08040c003903111000420142c031110390b264030000c00010110134520700075500e030504002c0b0005098100c0ca0840e802541c205040010342810001805461040585007034100070b410080016288501201a6004d1036121001086e01c40c024800800e4022030140c0d10040c84020b03424007109610010342080e010003d4100700340c441041e50300a038181600540060030200001400c0c4c0d80d01b00d0401160050110704403048410a612014407014200000041c480346078000b09a0141120349002c1c0e00d0455184c0940390720784009002d050004040c6203600444107503101d40ea040c8 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 384293911 1250 384292661 384292663
    0x20f060c0304020931020d05010e0609070e1501030b0316092315010813050a0b0405120412150207150504031409010203070618051e06070e0105030601030b120a080c 72
    0xf03074000c40b680a580741c0700f0030014924080c0706400300d0a01d100c06145d01e00d81c0210b4841c0380c1c2451900d508070008102c1070707410540782501c84d001200c089109000d80c0002040225012003910702070548803108082d025080700055000700011601140c5c5403140100240d180e1250703800c0c6801400c46c0c20004030380c440d014510045010307001000320701400009401c0080d000440404505954024a065001500d544003500c034110220440502311340a80c19500090000b03044030340c2e001c0d511074030840704d041014080201c0c041c007407401003c003044902e80700303c03001c07070060342a4a444425001005240c0b90070b60b0754102c0c0c04240900105940c60301d0f201084281504281000401c0c040c622500d4503000c40000000d40340e11403c1c0001302030554400c40035010381038103861044040e030301a04032151044140c0c818040c80e082010100d00500c142030000b425544660100c068000c0180c4445040d6240c02005402402d01884116042600040d81500014040185a903283d0242c0c440c5540c42192075081 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 384295161 1250 384293911 384293929
    0xc0816031b02060928170c03070e010e070201020d0c020a020a0503190f050a0b04030203120106021614040b030d0e01020c0d08040e070203070602030f1e0709060f020f060c030402 78
    0xd458031106000700700d80942c80300000c5403003030300c01112522540d042ea43c8194030b40f1180c9091115002200310401b15806100e11152940d000d0480c0858281411000c105603880c482400b421308021400c00c0108074803403294034803580100c034900000d810003034981072f590f04454468014400680c0034450f03600550500a4864001d01001e4002e0035004620800c2c111032607039034030310040014140d11258020310100740842811140e10429409141c103207400d00965a030081c2c8000781010a0741c0000044d65400010440c0c1c0c040c10214550071400d20340480d00c1d2030340c5010715405030096111000142c00da9400d00540c0786807071542e03ea01c00d0304030034000028030b0403020030190360098001d84400004584000107890403907503c001d84080c0d541c0e032400100d040d8007846000400c40c500110134800707070100407100c19100348103480e02c00d0b000c210420317840c0703444107015600c00e004180d5811003070200700d1043c590071141c5d000c9401242c540c02d040a408601c1c200301152400c0c0300708004010300c030840c070341a0300c0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 384296411 1250 384295161 384295187
    0x20703050a0c151112090607050102030408120a09020306180a020a0306020301090c0801081b150f0a030b10120b01090b070b010f1d070c0606051c050d1d060a0c081603 73
    0x105038810700d13601c00303103580d102904802484d03140f01c04182426070f40d444100720754886510500035912824035103003110003078001c500840c035601101800140c0c0b01e5000e00c034800e80ca80d0020000c08160301d41c030490104c90b4090b0b0395450610b010700340c00540580c403601d88000086202f400f0050741d0390b1411410300120f0f118080950b0401c0800c07801049100c000103102d40c00300e5111200c0c120307501200030000300214208076041c0e48268005c07031642055403a00010708030184d0140c5060226104207070400112119030842403020076040444003884046682c0a400851810b04040d400107840709100c0c85117400c02c2d00210303507002c0d44000601414080b5840b80c4014140d0300306045121209019200355040001c0c1030307074200600c01c1405028000c0700d40100c4000e0074080c05010300b0350060003107018100c00586058840344100b10300030300168880d014140004800c400d46109001540741001a1980701c84020010000d04051a802142481000300b040b104642d106034040c1c1441d290280c964001741c08 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 384297661 1250 384296411 384296417
    0x120c0b01060908030d0507030b1203040e0f01031a0c0903010908180f060a0509010e060408010506030105180304050906060706061203111605121510090e2b020703050a0c15 75
    0xb02080351200020699204000d801d1020800d603603410303030840003020340030545648282010b1448003420f001100070b00075035480c078164003070a40d81e403800e00700c10031004e22004000d90081c61020812411401c841908121aa00138901d004124800282501c848010941e984100056500c29070300d142201f0f40851002a41d48842d400180c80c0001c10f0750245caa01601400340000c0c0c210900e81c455011041062001402961207a481e01c05c068001c190450b049400307980fa01011410b0f10441520148625140200552503e414401440005000582101d801440500c41c0c10001500c0d406444041e0807161404003100d08103007001000491203034003131501a007003280d030700c02d00c0707000742e25260306444040c1d92002d010b580c100c511a00d85200e08490880c40c0b48c40c102807180008150812404403410804107000300324200586035214a10b000350784210300c0c8101501488072142041d0702d11580014010740e10300c5035403521004d00345050f100040710045551403051168a07c071010442c0045ca40d89 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 384298911 1250 384297661 384297677
    0x30e010e2a18060d050a0215070308060108041e06060f120b15090103060504020d0b100503010c0302090a0501030902120f1011090109210c090509011d071e03120c0b0106 74
    0x1103035035803021101821040c00307000b80134110000c0c0071003008100001c66020380344584100d400d43c001805608203003001c40c00214100f010a403a58400e03d40c85006a07005002200b1f291455000d5000c1c03540400d070f045a00d151281d13800284000d00c10b44400060800910301600215580b0700b04520784e900034041b01051280305003c80c41c0ba110f03482054103403580288005407648882c000160032842410b40289103084d03c10030000111034a04c81c030350445c0d90940083c0150720f20f82000b5000e034003510418903040700c0128001c008541c402c4c1c05c052401400544400503d103100a0481d042c04c6e41485440480d60100c40c0303070b04500203680304158114040c14981c5042c0f180713000008060760784500c1010710300c1c002d1040d1002c4c0003402d28500b2120682c82030207603c049a0340c00e14400a8075045500d04515413801940b054102002c91501d4004000280580070380c50401030900d1610032820380906070b0090000c40880000c0c0d0940031a590422a41c40e8a914055189060200d03214160404002c01c200c813 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 384300161 1250 384298911 384298939
    0x203010f0515040e06151c060f0537050d080310091103070e13060807050307080d02030a05070515090a020f061303080f09091602010c0f050a030e010e2a 67
    0x40f8205e03009030040700d400820707988070b4108a5283c0600005013111040c1c0c00949541188564447c0303040391000303644003080a941c0d104100c2ca20325504442c1a44501c90300c003442c040e44040c8040140e2140495282d00d4150701d50000c50000e40d4100d00c00c84a00034000240000105458600c20042102c14814800401480a41c0c1c2e1b003400060020824808141c0d60400c0540c1c64104c429068030b28484100011a5151285640c441d0284070703541c0680907010011408000208441d000030b080d50300214580039920504442c01c0c0d000c0704080c0e401e4002c2404109052000d401034501400310350004117a0285203004208962a41d040403074840d440c03c000c80c0f40114010740741c100441c6e421400c1d41707880340148401000580706c1c41e50043e03402424601048001e41c600001112911081da00030414001381c1c203000c2d91119100160b11001c40c01c240702d403040c50380c4a030b080708040c44485000451510954a040c510300101041c922041070f0171115100f000007405d060350f0401070002c41d0100030101e41 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 384301411 1250 384300161 384300179
    0x40311151509040201090e0c04031109131b0b0a030c11150604020a120c0503090f03071e020d32030f0403020d1e0f020112090210051c0203010f051504 66
    0x1c4040154051521900090156805101520700600040601000341d107485d419042d00da43c002e010803114125139404072100c074103141da11a4801d12039100d01f1a0030112540702d4009040303080c443c0344030050040710003041501c3c11201401c10b00b0b9143e100401c5000c4101d402905107030400103400107640c00803030320300c1040c201c00d4400c5800c00402c0d2070050390f5540084045031217401ca10203003d961410030034016101a80f00d0019880786500300c0070780d2004038801d000d079178807841402c50161912040c0f8290001c06080c1d0140149000d100900c55901a006640d03507418500b40c0c0040511503880180d1898085185010070040442540340030350300d8100c480c1d034620301c1401707140000382c041c40c0600c004000f0445074400961075180341c0084030030908480d2801482d803c83c1ca00080340091524418020040310358080c1c261940e500811280300c0c1c8000300b00031210354103e00194000660903246a40c201401440114007a01c0001040060581000c092005603100f03851500030101d400c010400c40402 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 384302661 1250 384301411 384301441
    0x102130815010e07030b03150103030e06040305030901080a0207050a0609110103140a09020d0506010e01260606040f1b180b03061f02030702220f0b0d03180e04031115 73
    0x4211000c050f034540b01c03541c0c11401000b000c0c641a81511620a8021140c01d1010b0740f03504891080d60340c01da04001440c144070240c02a0b2000034031039441480080201e6005490180d4007040c3c100005040000c030313440761884c0082c00c2d4070503280240d680ea541014002002c6034000200350a003000d220440d800070221082400041c011582d00d90345034401c80031913843c80c190002c107a80000860300c940d44c590f00380c1190303118284910382a040c0059402c0e03160b901158030842034945c2180103081143e48140070701c4042e00c6010000c0260070341d501c0c03407031045400003400e40c1c1c0d22020b41d1f5115085092003a078040041d01380d13900156060b540920401c075030395842c80803e12484407007200024441c1120311050746107028580d0001e40c0104003440410047c1e0454005203c4c984800c00244440c07500140080112001448070700d4000400030601400700340100281c484441c143c040407106160b03101d031000c80505040c3d40840000701c4042d207440c00058100000803410340d0240100b6000d04201210300c0b1526 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 384303911 1250 384302661 384302669
    0x1300b0105090d0314130b1306020a12200712140106030b0402060a03020c0106060327020906010302071a270c0315071107151103070213050c04080d02010213081501 72
    0x3080504a56401900d680b00b03a442c20000a001b401c2c04070344807030003c21981c21040300200c1e1480788150000d0170904c0066110021a044174403541080c0d00c07984100d48010f00041c83c03000e80d8000704401c1c44030400401c2158000c040c0d00b040503022040524015407014902101a01c0e640e0401c0424000302c0e0705203401d544c010b641118401e954042510301035010b0301524500d80c90651038800d0010340e0b25003581185d0307210888460000c01c40e0400004480410340d01800103504081407200040495009600801c1994019584600024185402d50070a1581200c1c0c3d114048080080b840030280100c0703405044500860143c5032881a600200340c1d00c5550344500c1c036210035240702107000c00340107454042107180c0303c1080d10085034480240550f055042c140c2d400004828a0200d481d149001c0145c540c203075070044c4840494180018800c000c1c02c0003820701c10010408210000b1401c0c82000702400e034080580015032160141c01c000603480c2c03044da20845d51500b02c1c20031403072800380a00e03205040d9 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 384305161 1250 384303911 384303917
    0x504050c18120a030f1e02060606030c070b0408042103020a080702011b0b071d01021009021f030509010501050f1804140a031d0102010204060207090b01300b0105090d03 74
    0x301407000d00080201181429031201401007030260000e040d80920a400b0220707003030f15181c441000340318001c10b02000d008002c200581003200441d0389450298015504a1102445c0394200802a280e84070402b1041d5406c440001000130b0401003a09407034035800900070390542c00c0841c1c1c00700da100692500d0800c2c41c01001e1030710014080d021a80102804030752580b008518880341d018070300e80850b49200c1035404d078021031907040c42d03001400c00d000d010f608005d5041e40940030200c2c0c1e041c40e000c050555104200e13404840081007007000c081d080303d506007a01702964081090300380001058211001a0002ea0249842d141070365515214065400d103410310030000340196658038107001c0103402d00d4240144642c0280642c4c035090503882940c044030008010100c40c0b803200c541c80168202d11031407145c1009a000100c0802c07000c44280d104881003072040c104a007004858408249104058120070f0843c3d01d0400d01201002c1c46520030245070007400e0070081d140c00a40300000710384c3d50791110f0050030 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 384306411 1250 384305161 384305197
    0xb0a090203060402040b0c01200307170408250c0b07030f0804050f03180a0909020a0b07031103030a0f18020112111b0f120f0f09030c0a06050d060504050c 68
    0x11511254101c0d4020005200b003da2646114981523029019150700c0c02c00c20b95401451068082c1c1600440b0700581702920b4401d5030500e4041e22071a032400c014030030749030900b040c0203d4030740140260710510075507009040905000c0042c0740200b051000e5400407002c044051102c400069040800800a00c0f03e0b81007403085076503140b5005240488020554010380000301e99207500d80000d00300072071051b4045912a01c001d17101d001c400c04942c40d081001e940007600007010411368061300018102d240c0a403810f1382612300c41500461655106030307000c0c0303541030780c60302154004141da21510a031007610241090481d641e680000b040000c0d407500440c05581e441580000d5031281c241280c1d451032204130000c0c070200300021490b846c2c501040d030380d22482c081c2c00c112401600c01d600031588068400e90300642007829841408940d40c004401c040d40502c54500465800e907030380d0792240002c210582c0e404e6541d814140700c000a540c0558451405281040300b8040d101300e4801c25228a030311a001c00314a = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 384307661 1250 384306411 384306421
    0x150b090f030708010507110102090a0501031e0606020c0405010b0c1b04180c08191208070c05150a1a1309021903110117070503160239040b0a090203 65
    0x1090912101e915118201d400140160190002481000540c81e40f0b405510340b11010b40c284d201e921080b0340c0c04011300e5402d00203503029070f00c50b50209400141d5144e00d05040c100800c00c031040c2c3c0e0024005039006102541c2d2900c1c26004403405440f4440643d0705007800e4146140c3d0f01d01c1c846414500c09580b10711302c030300a42ca4960203409040082604030034110300038148042c894995000b6100d242c0074450304007030400d103036004e0340c1141c0c1e84c048500c440c0c0511391a0201c603c1c54003d0101804c22900f003145401007441040442500400d0800c40705039801c18042c20340840e41400c220540c60402c3d44007401d4140d44080340880d17030040340c00d80486c07890708034800a5003940b100b0026407146c440c00c0342e010003400004810780d000310308280c85444203420401010403000b901211144000b440c204001980320000d520440c1041803030740111b4101501c40d12059088002d00c1480d03c4002c02d10542143d40ca1000f1112400390003002e44041101302141001b2903040382d01401150b000b540c001020407 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 384308911 1250 384307661 384307669
    0xd0b060d05160b0c24071d2e030e12280f030507210b0a0b030c0d060524180a0303030c170f18100c0c0312150b09 50
    0x10001c0c40d512080746505616900f1240c1d0b80d8012888403103592081d81c0c00c060520040f20040c10310038103000c0b03180341c981c1c0d240031007200c03205401e241d032141c3c040d186400310003e40c1300e03070348450368804412480d0340d00000c40644580c6101024107600007058103040804d441203201259004050f450f1001041c0da6810a51420310744101d40040300050b00151801c809070380d0b6000d41400c081010071341d41405252521030080320001e010208088038240000e030728280664441d4071514140c507002d001e21481c00e9446224a030382d074004580410801e43c00084d0000d001c3c1440c401d0be070140030103c82640c0d04d05800703000116000c0080d0100300c00058000340420b90400c211311206410748000b888000800e449144c01030280c1400c148150200e40005020b00d9040603160a4a200b11461001c51030f95039200c540b01c0b02e10300d21030045c040480c000c5142200180c0e02030700580d448032400e034494000098035498002d010f040205020400c6a00d44000c85509400080070305007141d40c04210562500384500010b = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 384310161 1250 384308911 384308923
    0x3032e23030a02090736120303091205030a0606050f032a03130317241914120d09050d02060c0105071e02030702010504050420030f01090b0d0b060d05 66
    0x6541300490b441000b051a074085c0109031880060690f28000c00c1811000880410440070a404050a038031803e201340304091502c4681280a86004640100c00d92030b00d4800a07000121040001d80000c10481d40300c49038010b1000401151500528042100301000c040c3d00026014061410580103410009944080302403028141c40a1155032400c14034031016045800318402c034003103000c00341c0303441b14000b1209a00b4481c03145c4c4001c4803507065000b61b159030b015151a440307550103015600140407960240c61210301405128a4409013500030310f04100b0382d007500c80712445499001003815554141d10030244003c942060b50781d400489050304c00200e4500460003040c18662030881045001503105003020f2401030b0941c0144801311101d801243c0783d105206001e070101e0b004006c20010760516600000d0001150000d02c265107000c0d400c6040d2590056884075a50036094006201c0100180b0078846003000c2112419545100f44c4e031030f4808444010b150038400c007610344c00142840024455 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 384311411 1250 384310161 384310163
    0xa031106090f031b030c0904050604060504031107030302010902040f020901050d0f140c0702040e371a190b0d030806010c0803180c0a06050405060f090303032e23030a 73
    0xb59181e16040c04d003070404c0c00d656903080d64030074454407100100e80d08021020600458005010f40b640d60758a40b1031310080d0801a10880821400074260101d08009011403000f85119600115941c006401000191000024610440b61040002042c160703048012544035051103480800c8410a5450182c01820804080c10b4170b1030340d08003040b030001e11210045c40740c00d100321001c00c208812a01003da82c0c25803000d036811220782103010180604a514229444811a080d81d2148101140c1d245d42c41141c0101e03070400006404410303c00303180c3c861020803c0ca45c441480c20406040120001582070032105030103010301804102050140c2d12441d80c1d48102d90304015003594030f0609001048a14492280201c2c940c040c20f54900d185240c1068604111002e9030f455030306050401c0100801548a01c50b000d90a640411221119071410700c003440c440c840400c20341191907248000054100347c0d00308040b00401b5500c400344802c8014501000b601c0351207101403c1c5104412000ca0301c4c0101e0940 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 384312661 1250 384311411 384311413
    0xf05010902100e030d020c060906070c170114160f0509041404120f020a05030414032401090b0301020a0f0302030a140a0501090b1002070e06010c1505150a031106090f03 74
    0x100c0c074400345400c8a01c0f04000d44081d012101080b81c043d1040740c03200c0140c0040c82d030041041114040782c0c075128000d0400203008107001110b0583c0e0f25015504480650304405590751602440d5400c03048440007035600540c0814000b00504c0c0e4090010a1034280a00c900c041c0301d40446c5540741ca4803190302c9400d146810425031034071410310b414481d02c0305d981201c0d1440001c100c9000103a01d60f10101d800d0140650000085051a04180d210101a130188054179014442c2c0c5442c1100255581c1440c0032480381c8035054aa254100002d03001a0f0300946030880c081e038010004004031551007800e14040308103500e030060322500ca9401280c09031500001c040b40007254401030011420555224074100c0302c01da0810400c05007007105020005003188074000250b000300204002c00c122001c440c80e44608149004410754000c0e641d003160603400c1c1040100615074650400042101031543d0309002402103540b4040249569112040c02803510582c89c01070768042840d48154459242d58268140010 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 384313911 1250 384312661 384312679
    0x81006030906060e10090614090412020c03060a021909052d04021308070504141303050f0412050d03021e1605010509060f0a0c12090f0203010c09030302070e0708040f05010902 77
    0x402120b02484090141c1b85000f85481c400007a4020002e12058445c03a0142c401405070340d0784e0700c0302d0a180800100d41000c1d4051900c500310141d90070301600c3d100780611f02006849000c400c2c076103401c80c4110804c80e0b0520200b50010301040d580d1400648107a189030707040031000998a030400d00041c143c210f00903046800032540900c26958010340005aa010a01301d0311026900c1c020030055444c66203029507000e40c0c00303000c180da071540142c05a40c0c0501a050043c94406031008000d03003035203e640201001100c0d90072103001c20100307000501c0740303480b640750a50034401c07ca2000d605c410904148c1d144007003800503189812790004441300d0840758206008000364540340c038505032030723101c2128044104082440081c8801e11140300d00e0b00550700700d42d6024080074403088004000c000440c0c0030b480401e040000798005a0b001d02a041038075a0a07911546442e186160181c038014064010a51280c03080b010400c2140d40010f1040e40581c0210303217003000001758107000380104003841002c0d401607020 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 384315161 1250 384313911 384313921
    0x71109071e050c010e010b010903022b0b070f03270201020a0c08011b050f041202300f1507051b07060207050f090601092303070306090210081006030906060e 69
    0x4500501003c1c03181400a1020344011031203182214031003004240403a4501c0800d10150400c0c440207020321400d01e842c07400000060030425011002404115010f070741c41000c00852551040710303540264910b0400744030550401d00c960649000500c0103e00c04079020064105581c820401000c14580081c014220181c8492020303010b410b50b00480c1c14211240d1401d5500280b080741110070308544507540a04003070601031441e1401c00c00d84416603219501008a85a0064410505580900d120b070051005121902610706100c042c2d500f0b5480e80d0440324203540f000140c1c00c81c05510600c5450102d130340e0b00880c0c210382e0101258428a07852032080c448082410b94001658205a507011921035180d0407241c4200901035204980c0c0c3c90001d62107000c10000300c02100c0303010100d501464101d2110361156404a440c4c0707a81a44251225901c9003440c50a608042141c02c022704007500c1c107034034a4600481c0b00841c5105c5485858101669542000e06100d41980044007901050310403908600345 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 384316411 1250 384315161 384315167
    0x2160302121e011505010f0903030318080a0801140109050303070b07051626190807092304050105030105060d0b0408120f1b130302041a090415050c071109071e 70
    0x60b03084c118500c041094000c5801d40c000c84c6906184580c2d5600d00c040301f81035a804070058503842403160203000306440c0700c00c005042c41d40076280c101155502c480e410340c504104110108050034031141031000040050001d40c4001c0106d03410f0130780100701c038202ca441d440011a05441a800110500c0b00e029605904004001451200c6404041004400e662107071011450038803500c0c01d1026425041d005013100203000d208020750104030750502005440c1d0701d07030420361946100424404102c0442d082200c00b45803900c42d46016200690007003103540b80c10030109180420f0b200000c0d121940810004040064140494604111589001076141442d1800210070102503c042a04c180000000550815050240e41e0801155544400010310790740a11001701103010941d0010b0b6140c0000b0b0200e610343c00310482c003640c8180380d1540d280000c2c0303503504200c60001d029511084000c008882c0890320782c26140f005064122210200ea403151082a20620103281d403940c0d4900c454811001c41c1c41e0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 384317661 1250 384316411 384316421
    0x5130b0c030301031a1302010e010903150e010e07060801180f021602100f210603050d0c03020d110706120b04050f0a0b031203040605090304080616090602160302121e01 74
    0x200c2641e00905c0b81c03001c01c02c0c4610880d400c0350810f40c1040101144d40241d0303c10041c03244054010705003480c81d03036101d440c1c0302580c2c0303148800158902c0d16811b00e808906024480c081c21079000a000d03080301400e04000828251303040c415104000c1301340c0070721380b20100150f104520108481d00219603078500304603403a188940175103041e4841c0c10003180000750079010f41c145003226003082d035030201c445950310480340c2680308150540940300e0741c030700000c800a9810041441441003903140c100554500d0301c2c0003440c240603900c00300c0c00c210a480030100c1c2c84c100040d102040e80d151307041072120417915820810040640ca22520f80c0700e81000300b4451081191a002401161050b509016104461040c9590b60300e0740e0300703004216581000010042240c40c2d003d10b800c0001e9006a91400b940c0c0c006207890310b002600c00b66903070701c4007041071004190041d4408004107550b00141500d00d41001c0709160400c42c501c0f002c1d000314038020000410f05420301038094500c1c4000d804421104000c040503000b00 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 384318911 1250 384317661 384317663
    0x7081b16080c0406122103091401050402030705031b04020a030e0a0606032906060c03040f0f18050606070212030d1a0906031c030c0c2108060f060a05130b0c03030103 73
    0x54941080822140980780c880c003070b80c0e03070010042c0381b06000034001c040e20f05e209001420100340c2e656500000050300b114034006500340040020409090a004044c1840d10a0303000174880e52000c00e100c144165690403a60f511309040b10016103e215907034055001c0c10026520b40c8450041c8454642000030745d0740400d0035203000e4800301482484c8000d40ca0719803802c144c4094120f0000e600024094030780400107080d45150103007034908055560742c1d8a0f00c0d441854019501d481c0358460180018200c80245000c2c0c10224034052080b0301741400482e00912600e00c01078044c00c1c05143c80c60a0700d01c100101c0748041120001084141c409001d0303420911400c0c5507452141051001160340340c0b03400980380c2028402072854004c4c1e400080b40c10340080045800c2d4505000c4040700c21404150b94019140c0202902c1d100d02d510b44441000017450020010560351050440e0070809400f512141e003500e100f600f403400c15550301c81c5040c002500d94180d50340301841d00e0f00d000884444046020028504172 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 384320161 1250 384318911 384318919
    0x919150b04020a2c060a020706081302101101110d0b010e0a081504150c0c0b060a1a070317040f210503040213021c0b031207081b16080c 60
    0x4049084100401e0380700303d030041c60000e0020f03004082880400700812100d04c110b4030140742e08490f04c0d00071a400341c00964845025070044d450812601d03810a41031a8807100c000700120701d0701950380c005180c1544540041c2c0810280d00b03810824030800f5404049401c03000d400c40e1340c6079000c0d001c1e801e01a03d501ca400900003461040340d0001c3d41022182c0714103581c603850103400510b8003c80d0513040088002c0082da0020202c040e071540784400c602c103c980c3c05c1d400c0c1e515640400c42ca402c08510b42d01014101c24041d03d9085c204000d110f9401d01c01140700b81c00320207100d580700e060341421103200300c441e00d815440040e1081400100304101c031880a042e4442c0140c080b05101c0700748425007038000070f964540820010000600180b4000225440042d4500001410920085515217211810200a00a03199075542d940306a24041180c2c2c00c00f598049040341c508802ca58900e8814090145951030100105690416481e030034481d0007001d00c1013002c50fa260035514003d05694040000c401805 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 384321411 1250 384320161 384320171
    0x10501021603051b06070b0406050f06060c070504022115150c0c0d030c050618060c040803191412071e020d0f031d060f070305060904030305091915 65
    0x10841c4010241102d4118025040c20440b604010700c40368078040360241e00031000c01c00c00c400a400140e4040c0154041c1000050714688102c502049860191030540b003022b00b88081e02c10440001241820b48005480160b00c48006401191400e90181070920b40c1e2440c031030400095454245200150480444054600000d0300400d04003500c10a08103014503000008080b2023403c0004181c17250728030030706e000200100b207500c800b41002800e8981001a180c0d0a840214501c03040280c0b54008040510f580d1900785000d020955034481d000785082c00c812108071040d8058025492040e10301c115800b29035a4041c9900d00b8581140c003100c403880458483c40300c0c1421a0703840e262480121020360010222090405820742d0004180c8007014105a241e0502d25841c02542003025000d82c08a401031400d800d0a00c5086d99810000704048100341c980b00402c001680c8580c107840e00320b60141400151034551224040c20020000c05407100124190704030030801450f213000001c800307410101044 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 384322661 1250 384321411 384321433
    0x30b06030c0405011508061f030506030d0f1209110306072a031727010606030609090c05060708190801031101170106270b03071d030d050306010219060501050102 71
    0x103d960030f000303000802c0203075100119070f54000c014168000b00018800c170202030281281155800e60740d0000d80000361600b0502c407090a08001442e101350642c101440700220181009103194407601c42c00d503609840f180174800b40940b1315001008008050251405c5240514000d80750400d40001e04408041400250481d88001910003809681c9961100c02d0002c0e440d42c80c82c82d1042c0a40003840040440e50304c2d980340041d16002c0740f0007542d8a4004144c6a2400b01c029080361702542c49690700a003440b09540014031410760420540303000f142c401d41c40f01400c0c18a00514095003d100604c20403a2140014aa40040b8610f040324414038600035003071402170044031402400e522405100c0904001404141c1c0250345191900340e0f1148041042e480c1c5100ca03200c0f1014230341c040030700d400000051068041d405000f5144890303031524107810403144400801c2d600c021403c481410844040003090940c1e01c28003900c00e000d544420340c4507d09400d82044001040c00303200395130140c4070340641b80c8 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 384323911 1250 384322661 384322669
    0x4180611040515041a070201181412030c03030703091403040617090f0a03030e0f250b1303060519091401061d010e0402060c0f0106140d0203030a0e0415030b06030c 72
    0x74017a90b00a40014040c40c0c00c040a41d19107400020089050003500101515046400103103080200925406100380019940910100f1170b844110342c0f00315041080400002040081181d070080d0b094030b000034601090b8103100c1102080b6401020303c6000000d0300080035603000f44159503d095224200c903907034403a00100c0d80c3e5031108403202200340c0c108100e51000f00f03000758030600e007004000c0255004080c2d25a0200d0500034090344002d8403100e0684120031413128588088060403040f4062490f100c682c0d916071300b05000610004018036144c00026440800b00511441c426009420901040a2138604004644101d07030418886602e4503000080701140f03110f480021004891144046900705011a004420014010b907009078040282000c444820058001503e4800380001403c600300840100c1e011148441107210301000c6c1c80241c0903950101c1100c0003600e490400e00f044940880109001d030103044220b5040c6504000c000050248140401c1d1203400100c09690039600c02c5c0c4200 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 384325161 1250 384323911 384323917
    0x131101050403050d0836060601020106060909050424091a07090506031005060705030301090e032701020708030d090303110c0312071b0309030201020d020d02030904180611040515 78
    0xf903d2980031000000341280030f10b140c903410868001007100e5170b5182454070705810b461513409a104e010720b043d8a100c3d40c6000d10840307030020800d200034000315292890040030b410b4039000ea0a80c4513a0b51010404100b0300c0c0ba03481c0301c80e00c80006d080b600d03003141a10000003410409030641d00c52040c213180300002c542131020319100c3c0344a503c44107400e6040406102d41174200030f081c5103080000c0d140205056507000c0103000001d2003040155a07039030400c264070b41a1a0135076480d1559610a0040a0a07803d042c0054802c41c68001c50b00c42c813002214004031320300b6400d0350041c44180400203000c540b02c03036190011045076010f51010301003603c14030040d4201d84607001c24a400ba410074414111001e0040324455080407440c0740204892600e01807a0203420032540c0c04501080340d5070410411960180414070580d903240c009030510440301d5401035100d20811103154030036903032001450700b09840709841d01951a08034030708108a120360700095070168483d008140c810b60501c40c24044c1440341d0411 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 384326411 1250 384325161 384325163
    0x608070815060a051c02040b1e04030302030d090323040603060803091302070302030708040e04020109050d02130c02100608030c0c0d03050d02030403090e25020106030323040e131101050403 83
    0x101440c3c001e00300c1e41150160001d6507010504000604002c0c90250703c4c1c00604081c100215815546880c5d03000140190740914400080e2203405010800109070040240c82c03c11041c006c01150385c00032490125035084880040301014010866080c03000080000a4401e03030304240c0741041101c2d29004031556a001d0601c032680e001d034601d075080d0009011600508442d5102e0300459042c95000d41e202007054102c0e41241c21545c002604000c19907a019540d000109000e8500311285c0070390780c020802030004951b400e0051500c4c1c281240d01d9a01c00c03c001c101403024140c0400016440d04086074030385d801010015580d1045801c042850b01c3d00340d0084560b280d0544aa0346003034107159071803000c1d40004000b9410f010303045030001815005640c5092040c091110403042c1a51109c15041d1000c5236207414004580c58140c0c2803001070341100e50180c60700311090056000d0404142c07112064070564001d8078041500d038091113451a04d2150064034a8803400412a181d0072280c0110380b01d01803844 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 384327661 1250 384326411 384326419
    0x10b01030e030d1a1c0204060f050d11060c0118140c01020318040f110703090e1608040501020f0c06150105072a090501060c03080a061508090a05070608070815 70
    0x83c1c1c8070498554000d42c2294000b182d10250b06030004001502d00710242e070025001024a01c4050843c601803242601070404d04c250300c600641400003040b841031070b9990040c902f00418400724095590003080d9071900c065640280320148000c0749400c1c0c030504d001001c0b68200300c12248407180b480007081c01000c3c1107040c0d00446c00e102110000300c0d0f841a40c12002c07a0442d5440d85140da8900c910302075442c902014842242c2e031601145801030261303030947c6c0400c0000441c07809000c660000b5140d800420101450244602d45403400c0060081c4510700000800140001d1028003409003c104140700784c20221880c41c15410b02001034601e8416841c0c010609500300380d840350f108030841344406002069007420700c12107443c1c03c081c2040381c9081c0c12950109000d24250300401d40d102c481c182d0301018032041402014504076101d1621103104d0000c178148404100000d507a10001c0042140440e00310f8112620655100c00180c405030301600c3c824001080c4500083c0100004c4200c00740200340a8 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 384328911 1250 384327661 384327667
    0x3151410031226010b0301080f07030c0603021312050706170606092116050312090f010e01050f03010612110c0a0b07020120031005030d140304080c0a0f05010b01030e03 74
    0x1030380c111500c0402040c0c40c0c00f405542e2044006100c07542c54054040d1400c2d0034010f6480d4140400a4600342c121b00e45194594081501032000a007141d03980003c0b152070341005605c4040308600e108256245070004541010314040580501500045101c120340451315000e64204502503000f444041c119000740c3c10003010010301601e807d24100d11031034100000c05010b072a20159498506241d04e44d0030584040c10340700c0b0113020529003800b124044030700c2624203c1c030f060750700c031301280a00000030314075814080002d002070300b60390042c41212624012500020303135941e159080900500f0000768810205482c00307096201252400c0203d65045103000300914151580c1d980d4000a9039009262800715500c1307a15074042c14401c1c4440e84003ca2140014588914151800941c00c84130360b44542d1090b8001c0ca1409012a04004c0240d440103c04107010303540e07640c0c0c4c18170350741620424120b2007441c030510100601348075041c240e030346465100e00000c0c4000e210300e00c011030964a1942c68061586c10070 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 384330161 1250 384328911 384328943
    0x60303042114030a080601031107031e030902031e060a020304050a0b0621010603140d17060d020d11040b030303010b04060e0d0203010903170a110d02130315141003 72
    0xa0140704508910600503030300000c81000c01d0a045030000391001d000303d80c0f4041802600c0d0307014000d4001c29003191100c0342c2072a20a0b14010854119080d030b90f03100c00045000b4050382440b13600810360007074001e0200c401440740003d05524600350001500c64034059880030a410f24240c3c001c0b40d001d541c0160003043c0e289055102e00b41d2100f00501100c0e40324141401e0100c8101c0700442002c503c00b0364000003e0700b80c0c81c5003080709d00702034103c40c50280c940001c1c0307180700d419402001c994021020710800141c0c0c1d503a030b031010a406c1c02d111103010b980034806400c42c204000c0000101e1138403e405840030701c0702c0849207040c5941e81c0001e0080302c004800510050240c0340c455605060816801001c2c90007111064000c603084507a02101a80000ca1a500c2c015582c80803c65030ba41010311100d0420030305040706440030b914080e80002000e500d400060b948104185580401701075908103407090b1400e064a01044c00420002001010f410303250030024126011300720b00b040c1203035007000d42c0004070000c0c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 384331411 1250 384330161 384330209
    0x2010b0303310e0a0204050307050405090d1b0b16020f120313030903140a0b0717150102031c0e011103040c03020904150905031324031a041e0506030304 67
    0xd00a60042c07981c2d032580014805082444060044084041c0141d585082c00241420400c003904030a000d5400d000a01c00c81042c00036a00410301d8681c680340700c01405150041c0c205100190020b455202c0381c60038090b018a4100c44480170302a20f400f200e1004c1e002d081c00603102c070510f400c54614400180700040c0340c400003411302100c00d4420714214000319102e0b42c03001c2c5d10300006008401d499002c80405010460808060b64018490b410110802210005119050400140300003201c1c0305441c542c1c840ba03402081a617156004c41200e20343c9000c40c82c002d9500911058003000050b6081090340081b510805080b68000c4d03800600344a40e035411038007071190340070000e00308640c8108511a240605400c1d40709400080d84200007031a0340c0c18064440d08a107121540040c08165285070300b800051190740946008030041d4140840c10b0a65002242c040000d040f4200f174009003800003501120307461544080b00394000d613004000b29103802c03091645d42c0c0903901400c01d0000e01c2e81d8154005a00f = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 384332661 1250 384331411 384331477
    0x8070c060510121515080309010507060b060c01150b120a020f070f051b10080a0b0103200301150806030a030e03010b06070305090a0608071403060f030a030f02010b0303 74
    0x20942c5000051540d0344480400005441600390f50800d140301e03680098107028011300c3c42034944582d43c8a400390401d034250b9281d00c41c1080301410f0000015040040100c0c07a045900201c0000340425110000010722070b02816041300d40c801c0b4207442042c00308100c03070080d040d209880c1090911070869510160000025442401084560202844a100041c0303c80011400407403151001d014043c580182c04240e04000d80031320f0b403048951041d208031541d40540c4481c1d20441400c0d0200d65044c1801c0141e00a1103038883c0020030300500900c4080102c5130400850407915600c2500c4511581c2110445045402b920060f0f07143d000388480313401191041180603a00380b801000000c0f03400c03880c400914030790b1000600700e000c150089801011482c01524440090205061460941c6096640188840320011180c003541402102003401600d6000c081d01040c0d00c050211071028606040283c086a0702e0440400198242007512805060200680700d0f400a003038000041421880b0245002c10 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 384333911 1250 384332661 384332671
    0x15210c0305071d041802030d020d03060906050904060b0103090b092b0e060304080d1508010b040606140c101109091609030b150910050102010e07050f0409150c090609050108070c0605 80
    0x1707a01e01a4907026980c14005540000456001022008110800038042c0c1c0d4559002606243c40c03d40204503a032119943e441d4042d030300406c005000300e0307030400682c020b0880d81c0024005c800b46108208017500001540d6070851103c080070300030200110840464401078040c000002403800c250315105007007240107903030464807400081c4d007044484d4001d442110080c54801074000a80c1404105602080c0700300c01c0c00103016602401490305004000d4940c40c01030580304d0010100051401e4008020700c0f1094000005000c24808a58074458202d03a9070804600356200758401000300341c0c0391311000489402050300d034403226a001e01d952a01200e042006200e4082000c10120751088c950742d2200c41442800c1d80b41c0a004c0180c00c003030009003118100c2c82003a030141d2244d0000d018a685c0c0c1c0c2e04070300f800e8030101d4011940c9851450302c0c800b024001c10b44400a1400c0400b511451600080c8400595040381d50b107881c119a6140111096001507034040e02150440c50160003040d01904229441 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 384335161 1250 384333911 384333941
    0x309030723030d050601080906101a0405190501030b0307030506061905040504050d1101020405010503130302010603050601030c0e2511010b06130e1f15210c0305071d04 74
    0xa4111a49860455103c1c00c1200c1030f550343c0d20b00f00b200560b0030002c11071304500403c00802e2113142c1442110b07101096405802d412800d03800c7c0e003050303161506040b20080c15001d130140720402603038100f495459040c0d0003060b02003808e000451109080020701282201d13000360003840c058903480700784020742550303650340c1c007840d0005d160100d10b9032101d016440c0128450781c0100003d9501e0b4000420b001d840d000b9640007a40100300030400b0b0303079020081d40d400081c40035038511190418a000d9005081c030381e0005185004000001051200543d284022501096105961542c0e0003c0000d424010440c5d07001d01526118000202c0c3c83c40703000e407200e400415100024014a0b68400624075400107042c3d81c1610a000e07105224001008101d00d03048240951042044038404640307455110300c3e0b006401801070005600408548500700c08a003912072040d11096004010400c040a850000d203800042400c000101e03e542c0d10503031041e03420799041561084d9648900701008080c0ca6502642d140e1 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 384336411 1250 384335161 384335213
    0x101112090a03200409150b010503090705012105182104170c040e031b2d07150e010e10091a0702190305150108060c091306080105061503090307 63
    0x216407224402e204d603960207280d5103d40000c041c6c03032010568100c0100c0504205c4144140403a4081c0013610b00140c8a090034000c1000480d03400080e4072210704840c10490b681450140281540c51029010315a4544d0041d00e202d0000c0c103c4c0105c801c0144423903207040e81ca04000070040303d6007a040e0081d0303400705803054892030b00d02c0b0000107040c0ea000c8002c0415907040040c400840006641e42d50f401042024083c21040c041c10503401c403480a00030a56140d1807a444209034810000d100782c20151909043c001e1034849007a50083c40b8142062481e40441c038001181ca02500d00107000e01ca40305010350320b6410381402d02d14a50720000c000088400900004d0091900603aa19800340b51030403040d00b81039010a1450505904d04000b040101d034046503010010b000701000464155400496516070641d604502008140d910689804d04404907181407004107052030103401550090004440b6032501c02c080300504120341c0320a6481a209034810032006000550400070030115a04041240c00 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 384337661 1250 384336411 384336473
    0x2b03051e04020f0909330c031f060e090a2901020a08030f15060307020a03081e24040204060905131503080301030c060503130f11101112090a03 63
    0x42070b41c0d05482000c030a410030601e64000c1c10311680020104400a06d5004040304900d038000d0f4030100160012002d8400000001d49503000002c100c2c281c0c004803d0829031030b40d0745e644000c00302e03068200c04c0380c03040140c0000710b00090103902079481206a00001403c1c5164842443c0a1340d92066481e1810342c0181c01d0b54101044102003e07521400c00d07205050828039010721184081402c46100a2150300103009102003140d00080d580462580b500f0700750130b16103883c0c40343c0e000406060400700501c80a1420406030090034420310a035420b0300700140484a00c0340c0300f00801e900943c091080001ea03507210400071860706000302a0940c1403c580000c01a428042c00e110584454206072800140040100108012011000f0080c0003500c0c009065007000d02c0e070821060304502c0040c0660444000f5072090000160888401140042c51121181503071800a00540310044005a65002e00070041c1e03070400074103044805410b40145070680050031951128020302010241c0c48401c0c1a000b0030319 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 384338911 1250 384337661 384337669
    0x70e041a1e0316091e06031205090d0b0109020702010f02070b09041a040e0703110114091e060a020706020106050f030d110c0316052701090e0f2b03051e04020f 70
    0x102804e25120041a40b8049001d903490710040094800d404514101080002c90b00034400c00f00480c0e028500780390344035441000691200c0300c01c40050b095040090000883c07100d00d03801044d200e0310030303206c61214840c01402641c0354211403241c030400355010882800c41c0e00e00396015502904812800e10600d5581d40041012030f00c01d0300100450ba400b0032014000d1101c200c2203080d0201d024030b0445c07440c0c00000d001e44918001e60801303a0003500303202c040e40707062480718203200303c0b01c50003402c0c0c280c9604004400030360720840392007104055441e141c0042a1814807081e00001143c0c050014134050020260484401e0300480e102c0f51103020b07100c240142c0740c1d4180070540112040003418001d841c00d00e03082103080c4001d116a0480a4600c00c2c41288480e030050320b081c1100d008240016600a15180b45420f0070242c1468104600910b40101800c004202e449083c0484060791440b00b203d5a13481542229070a5490001100d054400e1540c5000a00b00b003035072061010b4550b9501a584201007 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 384340161 1250 384338911 384338953
    0x30c050d0804021305010b0d09061b120c030204081902010903050601030f1101022d0712120801080a0302030702150f070c180c1d04060e070e041a1e03 66
    0x6000003a41c0c1d00600040d498950440310000501d1441007101e545400d00c94540ca1060141c1d04008540358a44101400b0541d032080c402103151801203100f803240184000c20520852594070701c110b02c1c1000c1000018424404e41d401d980f8130100401031104056056058407030010740407410080c01c800d010000038024094a4001c52140b101c103a000e070007510f0004100c0c88899450b50456100b01c541c401007000b00c900300c0d681010300040204c0003040c41460b050034041355400070840c1514041981d000c01440106110062100381d581c4429070741c88694480d1103803004940540140c1c018050107025107440005d241d4a2444500e209190003003100701c46000e034100c0b64040e9005003003080100400031044e2204010840b403c0320800c95000e0494002d400319088608009403182c070f88030b07002241d0f112a0320040240101c801c1c229a545403400008011088801e5139602035420300c032001201c003442903550744a10b03000500091010a012012a8240400c810400c0c0e15109200082440100d02c80f64 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 384341411 1250 384340161 384340183
    0xf19060302030703050f07020c1e061b0601050f1302090609040c030b01030507080907090b0a170a030e010c0b0604050402010c0b430f120c050919150c030c05 69
    0x1da16450640b601804a92008000030b955107030440400c40f1096000c65950b880c40011560710f186800865018000d0b0203111322440d0304900000303841d440c401541c40c4105c02d244844002c5985603a00c070030a10400c1c145681c030300e0b034108020103803190341c90140360080d02c105840a801c5c5030402080700d0001e000d56100c8554040407035a1140100c4a80d645402940d61024281c206001607041645110f130b40c407200f03403003035404a5a40312842da0751540c0d101c821368014035105188820303503040311202540341da44429085010540300d5001c04000d5006060700190640c000840400b1030b03440c40c00b401301429000384203c2c100040d401403800044c02d89100d050103a48502c01e1a16941c201401e18500702c000f401020182030b000b6182032202d41030742ca12030b8503409400e02d4201082c420000c8180d50901d441c0b10b00134122802c1000d0a8134890f401409800502c40865001400c02440c1c00305800341c00307403400343c5080084002172141d0007500400310160010b1182c5411030f040c0c11103889103802c0419440c8 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 384342661 1250 384341411 384341417
    0x9090114010503014a0f0c0904090516030308160801060e1309060509010e0f160311130e031c090b06060307050408030c030a020f070e04290a0603060e01060605090f1906 74
    0x84040c3c1700040c882035071000030f41078401400e040c00312850b550b134007405440a07c116100e801c100e04022040c8500d9800e4510f0715060a80381d6220700d4090f02e24041152131f800340313210f2200b010348034034400c0503254103c500b6a100c0c64030310542039091102100981c81c03500c44a645a441d800300060151144501c5600102c00001d084040c8014840c01d122038600d80d40e0b000e034003000c1c030b0071034582c0040081c1084950142c19048140c01850201300882c2c2011107040c006458240c031000101000300080401c140703206540c03c9112007002ca10030031914a031030090140c0310250000707501070402c0c90042d80c0100c802d04005042c555a19000f03403035640710085584c0c081d0404515401803c0e010080b4619500041014040f03650405444031745510b40204080e01c180981e4400607034010300102800e41d00c00514900c0220b40c80e0840c032001c040c1070079100031100c091500595040310302040c80b805041e100d19580340342c5081600300801c00000b081410b01503008043c40c20140c2014031a554440040000d40c0b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 384343911 1250 384342661 384342779
    0x14040f181406011e0b030604180303062103050d0510080f010b1302072f0d0b070f03020c0705011404050612071d0a03030818070b0909011401050301 65
    0x101038507082c942c0c1a070102c50041c0c3d00840440042a510702c80300180e03116909420303240e0f03071817000140191071092000030150200c040100281580f5030060429200445000201ca10710003041c20741140c441000940015000c1c496040e05036019004290811200302002e42510385a1380300608101103a83e86556603955104040d02c82d08100d8540c1a5082d41c1940c2107003010040e1301d03680084462108000b888402110125901041c115032004e20510b014025840381d005038580407410001c00d0700c03082c002c01c2d248161900103601c240204e81882c0c9212003e001c0d400d20700401502c2d03039244803c18a202c41424400403500351580303030145c6140c1507000b03810025030809a8024019070081154a404601c2111040040d80c58408592040700d40c1450b00c020f0a5440f440c4461a40c50304a803003210a0045010014050748000080c0651440465800410342d0381d0320820741c2468001409140403941c10301c010040a03406900100320706003484000e40d2042d074118400c10040f40f0400054085600d00 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 384345161 1250 384343911 384343943
    0xe01030b1c1406010501020d050c12030f010e0f04080a0309020d120201060e1509070c110306090705030d110d0c051c0914010c03020601182a03051014040f18 69
    0x500040036400b4402510b40c0e0b50400340003c0d02e6400b802442401d020780000d0114442604000c01c40d440b0070050103c0d82c680c2071070041c004940d0400c2c032548580c240180c02081c241c0001d15100c9000320783c891601c82ca441e458003002c1d4094005c0000070381e40b2810120902d40441d10080442d00c00180c1ca90001600c1da081206400d04901d01030810f00c000281940160000c1c3c9860080b141c00c18401d08112901c86040d1074510114810640c03200d405014400070b0212504c00020000162503041342035645105c0084002c0342d004410009101055000f8400e02010754091030050003194000c00070307110744c1c5240000b03440990046240323000c00141c00282c00c000a980400c08100b60000901c2c0c03031084a5446e8030025a140340c1805076105e24a61000c0340f0044188940c0400c0801c0e0030301c1e44d551040080180c4040040b409201d584021904000006000f0004050032005880e100544158070000e2035080c803004100000b11b0104090781c1b0540b202d14030803402c1c06840c00c2c0788034031003021140500e = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 384346411 1250 384345161 384345173
    0x306050a02091009031203051302030a0507030b01060309080910020a0503041e060309050c193c080a11180c03070201150b0d020c07030b07050409150e070e01030b1c 72
    0x3c86402003080001002051000a0b035280e56000f00380036030301e0081040c0e12440404072189091802c002d5051240949900030040c0c0030900404a074012980030000d82e03a102c07403d8094494842c00200300347c404004075a11071810380c603480016a010301c100e81c2481c1d1690f80301ca18541c01b035000028405401c655031a0360403001c40d02d400c098580c03854284071000d09551403558038803a40321514819110360740240e204904030440c107801803030707000100c1c42c81440b039120f50700ca1481202d842c204004910104108190320301c0d42c00104461070b07d0028840701c0c14984038a6801c880200c01164000c1030700740580100d03800c040e039441c01141d004c607010744da03810062000f0b421210680122000240a014204034040f4040152000540f00350009a52803100341a810300b424610780008250b041326105005001d81c3c4a005801a01c0c0b40c0078080205a400103001000103901e4802d12241e02808070024546a118500c0c88440a806041c0800d208c162640000d07000344014103c08031101c002d1302002d041c000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 384347661 1250 384346411 384346429
    0xe0a06021c06120f030e01020c030d03020a02010b0f090105010507081606060e090616050d0204080304090e121201090e0a05010e0c011d0f01080405030d09030f03050601031a09100306050a0209 84
    0xe5240b80c000d01c031440d00d6039290740301c01d103100000c0c5c10f1103840000c2032100e9009202c0464540d10050641f200c900700300300058002d40021482c0d80041d803074072125003802d0030113105418104000802c040640d0703180c1401107415078000b0f81d01311511803003440040030141c1d0344144208998800e500c0841d0213414022800a59007004120100d16401035050001a5900d440004402c1d410307494035958810191200b080079114551080311300c0d1000280001e002c40e0503500032201543c2c00030542d44405100542c1c0c0386c0601a01880c40452101740c0010041c0c80d03082c0d0300000004401c40c1c00e450540700507031602821507044200705041a0007003103c1d1011582e21040d60300302c6400b0401006801a1540041803a0500c80f000c8541800354000c04102401420401d1b00c202000014003408000340d10316000300000d0301d1070000008a410080425429030290103200182003004520300c0780040284100141040050000c41034803001c804003001060030780c028248603482600300903986040260902807405 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 384348911 1250 384347661 384347669
    0x9150306050f0402131d030c0a0b090303040506130f1506170d0c0f2619111009032c0907020712060b031204080f07060302090a06030e0a06021c06 64
    0x10b441030810005a0b0742071201400c3c1d112482c0001074640481d502800f0b40c43d005030110015120120f036020707031860001100207455201e01d840729903903162491710f6540d9001c01c0d50000c00c0340e045040040c0c4c3c031002029040304403030301500300c0350a1034041e80c48440481e4641d0441e1280b507512a813042c0120303440c3c2a00c08440c05000401800c020010071002403105031004001805c0c43d0300301d2070102c00c3c0304801e15031901c1411281c2d0761407190700903413080240e00d03400f400030503112462010070140750074060006680c100c8000b601400814120212400c014070071a08204c042c4031181c81c1a8609201c0440016002c400d040f14615a10304131001300920721a0043c0a6000c552140409100030000c8060740d03512154040c03008100c446140c1e000900345030300c0c40b080003c0302ea4003141c0010b03004030016000100340d0018050b41c2c2c606880d10022000e034807401e60825000075000404014441c480d50040117a60383c07040a994001e8110355a5000b40d90100310212800e04074100754041d407410610a09000b0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 384350161 1250 384348911 384348931
    0x703020409060b12031c1107080a170a0c080c0d060e0117070905040c231e12060601023d021b03030411100302070209090102030121020604090c090915030605 69
    0x41c804080c00c003c2c00010b1b4036030015140c002c01081203e041c1c0584e42c125a010b191a0b44417000280020b020010103460049801840004907070b02d0000c500c22030740d1910b41542c628441344c1e0380c802d0218a6510812214900c1039856100040e554588982503018029035844007003482c0359021064900301c2da079000071141741d281006100000f121011a20203d91112041c034400d102044c2079042400050501c140e00485000c3e596603000514004010121f1400c6507000e401140d00340b0b100e513444808030341550141c0e10286141c0c045001d2003401e0740c90940c84005a0b50703843d40130301454100301811400d0403c8140c0100e1059031031034111031482c2b03e41075008000e60841c9826110301c45001d003c000b04c14050070b4200c0e0080d8802e44290125000690082c0c86d001c5a4148080514001c0d4404d1142150201c00304107a124503200034440d1042442e0010f14160a01d424540780600400ea001100010300090a1000909140380c2c0511f000452101c0322084e4000d10f503003491400d07100010300c98444 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 384351411 1250 384350161 384350167
    0x6050f0315070e011e0e09090a030c0615050a0308070302010507110705060904180f060b0f280f060c110103020319050408041a1e0705030d0e0703020409060b1203 71
    0x200381c03241e00301652111161070440701c03401550307005803180248012200d8400950090068449810690200040c0010b5640500b682e80e420b51b883d44403111550014002046040a0800f2441c1c5821409900c074000c46600811590303080041c41850965000721844040441e4107000d0640a110b03280c2c2c080c0c014144030709040801030b0241c3d11348816005441c8128808500790440e500c455100c1505050035059903a03c514150034210b1b00d8102000003110780c1418641c10070018144204070012618015005607455542c840260000e83d40c0526040c1200e120441c0000d4002c000150b048002c00c101c2d161a03401c00050308110107007a4401d07624a05141c010000c1c000052580082c0c1c1215010759070000401da1600d213017650365403150786c2c8104a51041a80c04848080c44c140040c8484109410100039102d940454500036001d0203101401a42040c0400501c0b80381c9a007040040f01c04110a5034002511b9030300140c12900c075070406403181640c0d1006100c681c03c292000c0c2c00385846d0303a001035007 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 384352517 1106 384351411 384351433
    0x40503040b032401031a21060f070909060302010804030f0909020417070504060e0402190302030102130501021506030706031503020d080a08010906182d06050f03 71
    0x83c4074003070b9011448096002c0d104081c0d048003400c0c00c0d50318900b08030341000050134184c041c1e05850b01032204640300211080c84403500c14841015407038140d0404a1005044041c1031700b0a407a514a000c0302400540e0704001641d5109a041c07034103007d50104c2100448960660360300c040f681d1400480c01240c1e14180e4903144210612400c21200d9540e940e00801003520720f03a00c10031208000000208000d800c04100e203a50b103d40d440d03441409183d1320b03030105c0d08981c0700c6104840c80c5101a00144201c3d07a043c4098551180c040c02000d0b024241507000a84a841500c95001810b9a0311a100c1000581103050802141c00600c800e01c144003506012280d0f030300a0b0305800000c2e80d01c00002c500c8041a00c40c0c00c050344c0311040840d40c0545404900b0009180b00e0042d41b41741a0518008802503020021031100c4040c1d461012601d18680030900c23103140d044003200d600c01d810820b9240b03 = true := by decide +kernel

theorem cover : BRFrame.Cov 384172661 384352517 := by
  have h0 := BRFrame.cov_init 384172661
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384172661 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 384172661 ≤ n) (h2 : n < 384352517) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
