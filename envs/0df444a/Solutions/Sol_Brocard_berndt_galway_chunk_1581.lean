-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1581
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:52:57.165447+00:00
-- url     : https://prove2.me/submissions/ee8c35b5-f6cf-4827-873e-84638cc18605

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 284172661 ≤ n < 284352517 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 284173911 1250 284172661 284172671
    0x10e0c0d14090d110d051801170910060819031b1203090b06120a2d060e0601080601060210050c160b010f1e052404080106050910080a06150f09 63
    0x4503024102546481d512481d5502061078122900d80c01b00035500201d11003078100b03400103110300040e40d10b40c00500031503104403e545c04000a07850300040c84c1290b8000d41c40c04106040e1116007040e21020700303a0701c00c209090154441000248558120000701024805c508030065403543d420b012aa541c58940340082e403580728a60502c1254003010f0703001041150281045000c03e40c1c1641c5800c4000070241100e551000005894400c95144569160000c080d00000ba08145410300081481d0401c0694a2050303000204280f04002a042d043e40c02c40c1d00204404030303080c80b480002e04002402501c9031a010b112401420081100d070191140c0720b100090490f6042c4000131045443d2584865040e40400407210141e11450781500700340c51007500e80414420602000b545045020100c0c44203811000500080c00e100c19407111b400d441d421100c80b401901c526050144c1082180101c0240da04150041c00000e1642da00c01030303104d40070034114055070303585020101c0c078619150f219103843ca480b0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 284175161 1250 284173911 284173933
    0x206092e03140708040204090618060f0c0f091703090405070c0201020c030d1407020303120903070b0f0403080117010b100201021309110301120609120905030d0206010e0c0d1409 78
    0x500411031009005842585a807a03d0300b0b008103006400b0340082d000d00d0365040f1200610043d50081840807180c4403601c0e40700e500c84e1400310700400d980c640c0d82c0e0b1400d1900020090340da11400c810780040713000f03030b5a5400b081d041020754800059004035261203440200540341c16903d9a024803441410207444041d5120920700002e03040c4148105070034400c0d002130b50010341050700700307412190300c0401e1111a501c8000074804070385144110741158881940340301c00c00517001ca00000400c022440380c0c005801c26106c00c00700c8865030b0001d440041c01b060815006124151895194807441225400040b91045000020810381080010307502c0050b50000303240c0d4514248051000020000b42004002071490515451014003040c01000103174041740980009014182c4c1000030583d4002c88a1400303e09500c4001e404084144161400fa006007903110010034000b01e090b038100e600302050388080365224103401c41c2c41d50141180c40b0040e9501e21030320b00721403011111213110f07101c101c00608002c114 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 284176411 1250 284175161 284175167
    0x3021810050a0303050316020f21160804080f01020a02120c0c12010f0b061911120409230601020d112a150414130603060c090e15030a0206092e 63
    0x80c200200048d03510012003028450320010301075162140e80701042c08400c000360000301040c81401e10f041da169501c5a06035052100040080c4120743c05071088172404242c81c05054203071b000e00f41110015030000e0085d0010441e41000901512085c08240d0750505149400981c00b0005000f120325103079560004007688206c144154003510004403402410148082c0c0406030300256040b5200401844402e0058072180030030025901c520701145043c0c0340c0ba01e1b403e0f030600510b0f0217118aa080030f14051120302014107000e9540c0102c0043e406032680722507075602500c411400c19480c0d1854802c0703119500c004c2c0b108010070784041910504401e0002c020303904100300e40904d010018564032041100308a45104007003032178150f5109031032a0071031100b0704030b1250040c0040e50000e4807581c00c11820100140c0e1008001c800e8883d02080401340c0c0d01c65070019030503200d514203a640c242e440803001201501e4118042d000c0340c08000d08600e20050b8180784494407103078485001c5922039840022070001a0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 284177661 1250 284176411 284176441
    0x50306160e01020a020609060a030e0604030e0306060114030a0504140307060b030d0203030705040e1315090b28050a150303020d2c06031320040e0703021810050a03030503 75
    0xc4240b0042510084c1030300000e480384924400103100303e0b000038180300d555010303410011540c069402a0313466850a42005070001c2038001e5050301ca0301851002401540c02103120304c00c44414201c04609660b81d441d501402810054815514610607031881d555000c0204024010984100301c00b0a2050b210418949812038a4040d001590002d004001c007040c0d1040580e0103e85461440e1041a1079071110a9440003441c107000c1c00c0580001c2d20800d42138050341000041c035214504215103070341d543c0d003a8500c0d42103400e01d5030705001c01c922200d044100e00b5040507030440752490000440008102106100160307130b5104602580100010a01542e04684080c400c0380845009460400c1d040c602c070380002c2c4003a800b05100300c0c4c0120100b200c000c050103104410981c800f810300a461090403140e0980500100c00d24422401c0c140d0075080c0da4004039203681120703030207080b42c981e0782e280d0070411000a40050001c40100c0b0b500c00d0004041d9a0b481503100114000e80307515580e4105900d00c040600 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 284178911 1250 284177661 284177687
    0x406030e010f0501052d09160e030c0102100b18090109050f0307030801060c15060311100e0d020108040f15020403020103050c09090121050601150908070b03061905030616 75
    0x64039043c0100040d03280c0d000d0011000040319003410345100008192800c61780d00a450316000303101502000703100100742c40e51401c68004d40d203070041424500b8080650301d03442d1841c21801071b04003240113150701c00b4a42100400311002801031071740100c040c0d8000c1226004551010580c2e456844074001e1200510003c104d041c0500051860b0503110345020b01110410b2050710100300c0c21402e03034418070a03400742000003e010511f007403024960300d0400040642c0c007008003c1c824202d03021440f03003007800b5021240000c3d4016042c0342d10148140c005480f0000c1c01003080c1d60130180807107102c0c001858200d001d541085c0d040b40c01038071785082d40001811540010003103501a0f4007040310f04029554a03484a0441315030081288d84515003d1944004940c43c00005103913112f56800414080400c2586900921555982c100303500c0c0c0c0c2d070b40c0d0503036195051701c5000354610b0100003140746414410b0503180e025960b0b000d0200307400c1d40e400c04a49800801c0703540c0180c0090614141d064aa40401121441 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 284180161 1250 284178911 284178941
    0x102070804051212180114070c0602060c0c0604060e0313030303140705180405041b08061b0a1e1707020a030e0f0a1e08240f010b04120204110406030e01 67
    0x80303412440f45030128401c01c090101002c0303045e03030081d11681c0310300c804100000700b071000103884412510345510703a10428000c91000d4050000012881a424000d4403004940100202142d03100d40e202c0c02c008140741e24100050740010400c141386c0c02c1c6a4100b080081d8800d60f00007031800c0e902c0345030814400014094900b0000104000003c00071000c40000f10303400b08030303000175450b02c4514080f81444054403c940c50b815001c40c0000d8808408641c180c4a42c0303c2c0b490b24084104e0b42010410300d485001c602c0404586000951038000c01e5403420a40c6045040c00c0c10b038010040107034030300490304080301c030780c070040e4429040c0340101070740014048860181564442160780b6041c002501c00f0700c03540184241c0e400041d1507500741602810142004210300010358442c4600c5860101c8143d1800b214001a059500003040801c101000010704030b81b0308080040c20141040180499061880d60682e0704c0f94580c0e070750411004158000f40010040c980f400910352108140290a40e03495070399000c10 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 284181411 1250 284180161 284180173
    0x1030207020607021e1e0102010501090203060d1223270102031903020403020a0305070509070c020a0b0309030d0617011404050a030e150f0a082512020c01020708040512 74
    0x1a2202e5003511000c0368111030410032505c0c01040362a41032401c140203075205088440381c0c12014003420840c00755140a90007400300e681c840259005074401602d1503501f1192010b08803010800591001c040000742e031900c40110701b40224400300c82c540d068400101d58000198648201000c441c8075000020b10302084011008102c001035140c0c026482044000d4840300c41d050301d8075100e541114043d5900910990000d40c8030700304159a11544c0c01303001d005529400200300554028103082c031403d0360080205072103074200301c40401550806008052940b00900113943e0000385070183c640074005403068a500707021003003070550030b54049055108440c1c4528052002043c00814400c68450b05410f00c03490810300740e07000c00c40850400144010b5041d02144071407104007940d004100383c107842d0303072045880d071100d9955908200c954105145012440d4481603c0319000d2926041e800d0304c3e80d4001820030003110441802c1e6404080103d99103d000102071003103240103290711110003400402420 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 284182661 1250 284181411 284181413
    0x7050d0c0e0108070302090d0203070e0708011a030c2b1a1009050603060a18020a120507020303061306120c030b0a020928050d0f0b010501030203070c020f040e030f070302070501030207 81
    0x1203c4032000d04020100b540000b01d142840d04e80341c1d010b41d60745038094101e9490a50310003002483c1c51040d9000e0700010201e100000f407285241e426401c103400178410081c595160992002650f60000c1075121039010600c0720303002c01c140a4422284041c451000104214600c416152110468400c010b0b100f080800544a0b400e9071106e5950300703440b0700355485580d07a01c5510010710815065031000e90f803c220340620760904610b43e0060242105036460f8610300c115000f0466080c3e80b0100c4102c001688240000340103480e0403d0b1540742d80000000c00070380c0603260308241e81d043c6c0b10b840007980e04503c1140b00b00208084508030036440b1000c0e080c11400c2100c4100010880300381c150351a40200c14401403000d822540e900d81d140100001070800392802d0302c40c50950411048000251545110a80001a80d500038022203215071001e0307a0300386142c24181d08100d110140039035020307042a036a502d0411042d401b0001055809000328040da29008546402843c010054200c84c0c109030040c0071841c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 284183911 1250 284182661 284182667
    0x1b0b070e0306100303030b060d0c0216050609090a090f02030f1b040203160f1e0c060b0a0506030a0207080421050714030c090702030d09061e091a0603031207050d0c0e01 74
    0x40c10b4039818600490341c102490700007038441c05040c4c9c00105161074a00c80d00542d68002410101001d0301003003403201140c2d210208020742c040c4683d410b810441b49400076108200b940d0102c150a449031038045400780d41900881c3c9821120204404a5405807007100c80203502c140021207410710407142989140ba028102c03045102041c442d007001e214081c17242c21541809040200f081c000607001d01c01e44418881802400101180030a8600707524099134640c0508000c00e089040d00c0000e8a15407441c3c0300c40760176170029170100006030307034128040c403000c5055a081c0d01e12607140300616082120f10030160400c2d034108203a40c1e004070310210ba0311900709a075072404602005d011504a031000f80650345c00009078118492011202d458900c1d0440100400c8842da01903884050001c0c0d02022a103110202442128004d25010344034503c0c00440c441801005180194800d9001d0140c1c3e052040040308003a50410a61740340b80031036008101c20120b400d80d403241307140810041c03400c00007000401e4006 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 284185161 1250 284183911 284183941
    0xe0d0e090c0a0c140d20030a09300516051806040207080c0f1608010c12090203070e010920030c2706040306090b07050408030f03071b0b070e0306 64
    0xb1000e100301c00c4810001c0c0311034071448243c2c2c6500e2a05481040b10510002030002c2040114411082080401da030107028001090303400491894803003086140c100800c150305034817003501c0340001c0300604420b41e04041c02440302000ea140710700010550b0340442e40e04032030104134603048a070046165503d8001c1c01c1d0311180c4c906401460a0301d0050355011a4103190300c091090540010041c07007030000f180c010000c0014031010310304207003100360034598503a409982610108140940000c04a40c25280e64050945c4650851480101203800040d502d66044548203000d0344002500c650301d1000400321000300c02403802e0001c058030321500e946000d55071040103029840d13021055034648010311400003154100d9a0810354000d10850300d07180c4d20300d0b10078050650280308448030700c284800b20300f03014029000d4a0035a1700340409541400c2454800400390b0304000c0419041009a85c0c85400f094031020020440718000c002050191800200250a00c181d01410602a1344008100040c1020080003 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 284186411 1250 284185161 284185177
    0xa051203032811030f0a0b0d080306130c0210060f03031407020f030601170c030d1413051e03011b09091e021920150a020705010e0d0e090c 61
    0x505185002c4403001c101d01440ca01c41060700030324140100094000c4a000355210700f28800c610a07042d45c0d03404d00e4100ba16294803041c0e030880d0300640b1840000308024040c6a0084015000440e150840c60072502503440c01d41181025820075150b0780c1c03031000b280c0240c0c006400081d1511240380d103982da00610040100d281800c6411000c981e802c01c56507018940c03121654002e048800f20358480c3c0c0d0203400c0b070008900400044c4501600c0d0019400c01184070016007203d40c49000e100501c40c40c142c07519a200000c0035003400c140305d1000c00d59039074036940c601e09800070722501d0382500a0b8000703250031038a103100401001540444440840d50380131481c0002c1d030381e07180004904d400000c444070601d42e02c0305507800c80c0c541c0042002003014a0810fa080b400d948141d6481c00e14a91000d601183c842e03042807291600d8000803210917005101c900b40e1030308242c100f400140f034009030361036103401c46458640340c48a1303410543c07290001503401070211079008001c0b07509007580d0900380360f10700d01d510a60310 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 284187661 1250 284186411 284186431
    0x501060825050a141b1614090105040e150702100621060b03010e03040b090f01050f030411270906070513050f0303040308030a090201031808120603030d15050a05120303 74
    0x400011044504c070150b4401400c000f29800f0300c1402c8628131503c1d480c5009a868190b540840009403901c80000d000f0340c0c2d000040c01c420714036400d1805210140c0080d8030b04041c0c0388240d005007109090003003100340c030132a00345c5c1c0545600803000004e003003a0b503041c0d0720a410042d10400030314004910058961050790703001000107948041c0c180400e01400c24608000c41e02e01000ca00054050400ea0003080b12030811180c10601c1d1424400540e0355003d002280442c00f60305100050002d2516003048540d60030040404a182c050446079410101c085404088840d0390201030001c801c104114041d000811130602d207041032500204200307a120544125441402c240034514410384041c02114041c60700080240c2c0d403031030700c4010000501003e80c0128002231030702d042d00e000100a5001c40320095400345a2910b010355800c1c40b60301050380544402e40c1070008010007560307100302d4440c5080d50301c076101180305a11b14103420400588499030200d40a125525120020014040122580144010 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 284188911 1250 284187661 284187677
    0xf08042402251805010f2111030705100201091203050c0702041a040528140f0403030e010c02070503060105030d0c080f040f03060f0f2c0c03010501060825050a 70
    0x3a0841c2c10000300358090100420482c40c1c40503600003641000f4140d88404500c1c902036507441c0b6904908030315007006204090041c80c0500005080100714009859004007112640c0da11880041c1180b103540d8a40c1c80983c0d540e000420802c400400701d030361101202d0408002c940b60015a506003031044880c000d20590f5114444403455034040e8107071126110291041100f40b9000000103004052180700034401c0901444001001807107000c1c2010490522607034400c6501c454000d00907441c0064402c409050704d8448498803514240b0480c17000d02110380c0104911071410342030504040e4180c201e0740c06904000040292150030042c0d0038a00da501401090340c0d00b041075403070142c0380580d4003e0b08284906540000c00d2180740d421445c0043c000090411070074104024500847d82d5214007101c2c030510000c144111032511100181290043c9802d84102c050100006030854000741c01c244081b4200300103200c017945415080e51155044078050f901c1d00e840800b800361460140035000720803c1004 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 284190161 1250 284188911 284188963
    0x306041104030b07020d020f070501020a03050c013804020f030f07021f0f0c18050118030f1b0503030703020307060b0d0605150f04060b03010905070c0f08042402 71
    0x101c41c01580c2020a11486090000c0000e4940c2d80c0aa40d0700d00501c24903052220321348012802c0011103e050300103241ca0a0103540a4a82d5040100c5000042d5a2144c40d1212183c8014031508014000001c0d0000140019040b48409241000f01c900583c03050000c505548480070480fa00002c1110804200b9560b4000403403800d10050102a00360700455280ea40d0b149194202c0d4044802130b14040c002940f544604032601410110403403400c644410b400c005a500440c0c500280f00c01000c030741c000f481e0312610703041c90880b174402c003c4900c091081002c001074550585904e000c1c1000b03d02a5203800340c070b518020350702d014090000d0507981d41e9900341c002ea0364038141e48a6516a010100340281d103452010007252800100902d4010341080d1140c2c5401d1900e0700c5041d090303800c400c0701a82907900b40040c0c1d0001b080b00900740810710108406a001003815200c0107c80107200b00400c036540c90a190900800801c4600c0380c014010011400002c007640100e2800780c0d0380d0111180442481d45 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 284191411 1250 284190161 284190191
    0x6170c031302030d080708160509151306090302040615080a020309031b03030a271401060306020708040303020d0801030804171c020c0909070609061214010e06041d03030604 76
    0x41c400029403612950700700c4a8003540000d002d61003506240c480307150302d07940c4a4171a0b1700840c034503d1078000284100007042c00c61a00e41351010b03007058825903150808620381075400003440340d034000501203441b4070b00800031458940111409040e0340504080d0312803040e10003500740700b03014101b001155004800203005401c02c00c20f5400783e0315144003000004003000c502c1e0343c07642d0069995072416802d003003480811094682074140b580d4820118154050800d40300c59034041d00881c10141d0715501c800000000c0344640c0054401140501441595149145006480c100307032014036800340654000104042840c4a0035282201c103d621624030f8015010200d41c103001c0091444070001454224205c0c0300c0740c0c0060340340c01480003030303400f500651201d6040507603c2110b4031030b01c000031781030401c1448031030703c80c20b04c040352901c210001041860002d0022901c0117402d0f007000400341c03c0ca00800c038543c5854042c03101c82580c0141100324200c0c900600903101c0c80001c0800e4001e503158038589280b01c1c6 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 284192661 1250 284191411 284191441
    0x61d071e1e0b1e1303110102010608030a0f03060f091401150c11010c020414090c030604050c042d0f11130603021305030102040906080d0807021c03020c0303070201060302010906170c03 81
    0x42681020744e0b14000820074228207000c0c1d00080e2015411424019403c1d4014415201503501000c0250f0a0100b400c80c02c56280b405510480109a11038800186001d032400c64100988000040495a00102c010025051005038042c25141d80540560b0803582c2d00101e0803103c0326045008001250100d0f00140c650340320103140250450b180c040503000c180303450403070345018001100507622800021020540d6078601524060700c1e68101004501075850300e82c0c002202101c09101c9400799950040c14680c0c5007502d44110f0390102d031a0045206c41da60940300d00c0128402042c50b07141010002d41140c10006a507014a0040c942d00103100e405030340103404014010000140255960703a215240c0c080a4001c612a4110700d114102d80820b07040d0282c20300520911680d802020405201c00c000080c042c48a80c0f841c0074140c0c00c100c00266000203200a51081c5110b070000300b0210701e1840011b04030145640034004020f00e03035846040c25840a04040c2d00002100c2866844c3e80703e44a01c90645c1d5 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 284193911 1250 284192661 284192707
    0xd021b0f1f02190b01090531020a050609061803070815250f0807031104140f060903100b040b041a032a01080a1407170108070b07061d071e1e0b 63
    0x1041231a055030000b140081040f5006209031000c1081039924000e104c0386014080074103a202d40d0a0009d004030030407040d00b070110104020101d43da4542c1e5100d4044c180b26912081c401591a024108000b051031040030100313100308000e0603210700345015001130a254a4405680811022a0118103030300e03c0394018510700c004414699130344030703949d0318040100b29040303120500900c09038400c400740303103030040c150303100c0000140241c0a0007500a40d5180100480020158841da86141503503042e10355210f90074541001e2115100c41034060340805181101a60440720284103200003080d00c54410000c0072180b400a080c50002e40d100d2490403806001821004a0f03400d094404004000307030300000041c0384252002c1c04030426601d511420b502d0700e030079015a13110b9260400c03080c000202c8681c004010104032403662081c40d40350502035401c002d029400610808540300c0d04c0924007201c804948014100302009018401c0b07003220005000e450392165202c0c21401144560264224440860b502 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 284195161 1250 284193911 284193961
    0xd110103111603140c0a02060a09030615050f0301050601021902060f0304060209120a0c0b03040206090a03061e1a280e180d021b0f1f02190b010905 65
    0x10b8076120740055403240141800b500081c240041015000700c504007201e00c1c030090312026101c01501078084c002540d101e100a03104000b1940c00000100c2c04921515261180a04000c995540f4100410000a8210088501c00d0349401e01744549603030000344200d6811b4008040341c50828907070000400c1405660440110f034540003003000204a0b03650b0003000a00001ca440c1480e552401007256070359008041c0044c9069004841070010b0040540a10b611030b100400c1140340026210120340051620f40c070803285152a2a14052103048050700081d034044110001c00031500010a036070b80500c040061705001300681c03d8110700a400325465600c48602c010403d09038903685068200c2c208904682003150004005400c41c002a0017044134800c1030000e90080000000c411100100d842d440f07a100f590000e110f03403c0002c0c41c1c50700301d030894078403040c44d10b003a000c10705010300641030001e204804c0041c441408058000565501c0100e4151248000d00240075545c0d030b90418603200b4164120040 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 284196411 1250 284195161 284195167
    0x52e030602030a062903010608190c11010b040b03100f0b0d0506041e0506070e010207090c02071a03101e03021e0109090608031c060e0403051905090d11010311 70
    0x2600000e400c0181240d51752002c1c00c0044000300a40d42110304041e40c0f0302e0380d41c0ca080004020350391090b01c03038076045040c04034441940b00500801800715000400b41501092107208074612034482031003000c1c5620b00c152130a021800840c00029200e10b5000341a00c10580d641e1012a012035072070b03120800d0008040c049401d00001400e00c11b41d0ba010498085940640101800c101a43c00c2d20780011080d1b4000002d201c5034450910642c1d01050545200d0304502c00c080001031058140d0090909003440303038000d800440e0400da07a80c103162007a9210901c1b400010005c2c4448000e5903080ca0048402c0307940340104004148848004d00016036101950000d40c000241c50f41d01c004204c107e4810100740c03151070000daaa500b0420654002d80303c1c00700c4581092169203050101d607607c403124090031807070000d0750b03030388405400c9080700e4262010703800102d0214140121100c00c0321000c40c0c00d200c50408504101c050030016161246203680140f01c1c4000110226080e4065002030008511544110b52 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 284197661 1250 284196411 284196421
    0xf070504020f09120a050f0d051215190e06030c06030105012d030b0910151209151b09080705040f020c0a060c090608011a0703120e10050a052e03060203 67
    0x7507110001417040d2068040d070390f078008400d01c0c00614075087c00c0254031183e007014280d102c15500240020078030b2000b020755004140d01c3d0364484841c42e0a25072402c9950515a041c100035401404005110b94003990250340744141d19070b112011349044076803d10f020010041c17a40203061580c41242045980c20520000d07800c000341e095000494801c1090780c48180680c0c50011200000d001e9210b441e5402414203074800250b07205000080340007038440c4005c104041c1540d11610901202ca0109080d65078074502c100c0304003e40141500f03544250f282075001fa40c14a00801c0d216080c070700c5914071071a580d801200011140350107a6071600c00027400d55828603600e0501e440507200b080321803800100208404100c0600034222a810780380703001e90b815040158803066089980c007151054040c03240c1d141c4c2c1401c1c40d42080c0120f4020b04001030242c86000120840502900d02c0604010944c1b403d2800300040d032281d021480030215850707180b040070000d0f080d201c940450107541001d410380b400001088 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 284198911 1250 284197661 284197663
    0x11040b0c07091119050f0c030d0b012303150a030203010f0606080c0f0d020a020f061302041a030c01120b060a17010b0301030f0b04170424020f070504020f0912 70
    0x80116a01d540d8103001c0342200d050542d0040c807829000c404a1030011303c000c07820750b104a02a0002501c0110b00f10700c2c16034100380e030503e907400441d41d01004644801c6040c030a96400302c0888003841955603d2441900038031a40f01705400001c00704807024042040e52401e07542c03860612801150090000c024840380003038944c0c05400b841c041c0c440460050707408a4105107502003101c0448a0085016003020860403100c0c0295004070f806c80110312401940b00c0c0c2c4000d040c8a01d60168010b8001c10300341401910500c8184c504054080b0441100d00c20000000d490100741e48102c910700f4030780342c2e1b100c02003c209400100360100c44180c00013008510241030725001601c11f086038007680580b926030781e40e1f104195a10302c0240030050841140c2c101d04c0d80000e002a000980040c030072800b130a907101030201005400d8115600520070810b6400314110034001088004003901c40340e20140031001d0641600b1540e81c24644181c90185600044d0035074003007411030540361000300081611000c00c0b00c22920b2 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 284200161 1250 284198911 284198923
    0x405030417160303110d1107030813031b03120e0117070309120518030303010302181806040609060b010e01020d180504020a0203070b010906050f130e0a081b030909010911040b0c 78
    0x340880d200e06c5510035080d0b0300429500e100a44254008c0010900b582e0700d000098020b5148002e0640b8650350110010780061643d0842c1c0342800700300c002203455070401580a49030b01110303006100c5c1a8140c0000e9907030103035521800f070500e0701c11380c1040d88800d1400c5001305681c4102510903429200090f0283d43d00c28010030aa03940303000025517000201040545074402840001d40c044482c0c1c000e0400c00c100c0c160b03038650020b0f41d81c82080304080901d1015052100c1202d08540156030b950702c00301006402c0c4a220f40c0c1c0b400a01e00f20128420030000030759038151401c038810910084483d40d5100e182c3c0116008007074607010304155110300f0b41d000301a54a07040311004031450080300c400400c48029622072003080f24001400024201c4142c01804010015011769100d0300d1744849490220308801c0105c1580390b40b2442000d6600c14070742041041096503d00400f02c0c0d500100103140c450b07500c00c05417034155603014100081c5c0c420300f0107100d0301038410741d880b0303030141d004c04241d00e000102d0210b03507 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 284201411 1250 284200161 284200187
    0x90201200d020d0203030c03070305091606050d1103040c0311030a020a0b0304030f140a051605061e0a0905120904060e0a15060e01020d12020906040f090606080405030417160303 78
    0xc03105072840003c0c0aa80741d0000305c03244480b164040c80055020b40c840c0c1c00050b00440c041040c1c880c0b01c0a603031041000c82040c2d800c01000f24030700058240c0984501d1140240303802c405000c05003107003000d40d10302104030502d102c080d20560704008841196030f8288050f103851175004041c07612450799007030503011a0704100ca055001c58001c0d0b603a6191240240c00304d0054840e0580317407600c1c10820081c03d58040d0492000c214203c20b070103e4002c00900e04000d02402008402007990068038000c1030749604c008000c04100c0c4c001e0820310f1b0310b030015000281421141e03040103491612140c0c003201050003480300760302c6480070312904d0b024004025082d500615000f44007650340c0004545542050322825004900f640c0160b0000b4042c209241c03040415201c80d0402640140c030f000c4010001405541150b007111243d0300c0030710010440e00d20940719140060144c0d042150311450320303031180303600e0f4000c5208007011982a0280a0020602400a010340b004090100d03d012512070074020b18207801010 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 284202661 1250 284201411 284201413
    0x90213090b011e050306180703060f09050f01020f0d09060e0604030f080a0b01080601032a0f11161a041a0405030607020a0c170a02030d08040b01091e090201200d02 72
    0xb02501c4548090348001c415144d018000381030644800b01d0602e011320031950b1401c01801018400f200141c00c502925144901c045800710350400c1506149007804280e9401d50001ea1040010780341d0600d50300292180907000110000d081066400e11401401c0003030301c0c0c01d640d4082c0c80204010590412901300f103545141d0742d00301490b6214002501110300d038542a40c0070032249800030350150304c2034111003050381c64120b40503440906043e54908082d0a80c6022011030303040d4001c0c101c810350002c1241c031650030b40401000149030a01c0103103a280c2d040c1c0202100021480c060303000b00e00788841120000d10745170900c0c4034420b48102071b12005420a015162280c0201030209480358800101d21342802e8110840c02d01e802c0c0780910070000700c04814545015409050300c100e0151b034003030250001c055680d8072030280616003446c0c04140000c0c1600034080c80d610f481001400d03540940100c480c614000a00000c1500c00c2e80010b0721103900c0c840408005c082d000c1d246082a4401140710801c0e000c540d0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 284203911 1250 284202661 284202689
    0x50a0501180b0307030803071209152306040b120604030306050f010f120507111f0b150a0f030906020310060e010c031d061b01050709050a03020d06090213090b01 71
    0x1081e010990300000e03003a81d4198480e80301400031410702d0b002585c10642600b002d82562881070803034000e03248061030548800464200c01d001e000c520b40903c10071441007400c00d901000715000b400d280024060304041c0203e03030f00d0f034480006031180046140d8000b901021a40c2900e4580f50042c050030341d90007014015800084140038170f5008020401a0381d8a548442d051082050102e5005001c01042c1e002001040b60390049140c3d414041030240198005580000004090401e0155140c54584900409a80100756003010448041d01c01d00455894401c601000480044000d0030390800040c00091001080c480248161040002260503a445109010042d6001505c14407212007001c0c02003002d2882d1904070445450b40c64000d40001440242490800c2004035071848180c44004000e83d03460b000c0c044050303040f0445c480103042c00c582c44401903041d43e011030000282494014145500e501d40740c400c55481440c20100765861150400040c40d141c2442080350400f0b1081c150880405 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 284205161 1250 284203911 284203949
    0xf150204050f06070308040b04050c0d05060a05070f0915092106050a02041a0309032a01180f0809031f021210030804051215010608150901180c090504050a0501 70
    0x264040c2c0e13015035059295211035540b0341c1c9640e065210010011107841c028a04900541c1e07076620441003016004500508141c900361588200300c90000e429502030040c400c90000c506980301108500f5601c07484e81ca10040c4807991301c282c03003080c801d411515444650380000c024000800c03052758a501e0140f54244800d032211030101d400c80c8902d02591548501460054100162480007140c1200d91030084038607107121410244101101011002849907510420440b12740003401030040c100344040480301d2340000c0356228490610400b00003032042c00d010525910580e01413000c4e6080034140c440440c60101480107980003507000006c1139101d005500f020603006001448030380d0580340c0c0301014500d418100b00c01c0110308280391076403035124410078001d01d0100c8400d00b00240280300c02d427100d84190401100c1000d9142200c00102d00a030080340042201d0b40d1880e981071900000c010001441d03e0080c4422504c81d49542c12442d0018200000e01900317940a0788018100c5580c6100407440d1020 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 284206411 1250 284205161 284205169
    0x5030403080a11041202030312130c0e161d03060103080a030f150b0c16180507051c0b0307030b0c19021f0b060910020a030e19030f0f150204050f 64
    0x10b4014800d004040c041170002c0340c0c040d40f902056900090403203090009907090302903c03000841d0b031040d40e503840d4203d0208000780810703804003801a40007101006d152040c00400412103601444042103a503852000180041008040c0000006015684251b071641080c040c2d0780d100d02401e10003e85481c0c51042052014490000001c3c0703480c21140d405481d00e0314210b295001800900d0050098070009940860318080b03080003043d107501101a151888841041100d000800d02820700100308030340718541220104401c48011304010004190380c054012a14180e03550f00000c0018080005101c0d0001e20f05014042c0201001e000c248103481e0340c001240c44641729602c5010490358003c1d500d01d42c1110750000b41d580600504854145103e640026648c040c0c0c044070940560402c0102d40c06041d0b100060700c040900070f954451114005541e104e81c02d038210312001d0700740325525000000f0044030040101411b0303002a19100c00420544401000303512070305c1500e00c141203802540e41c860030 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 284207661 1250 284206411 284206421
    0x140a1a010f060206010302060309030c030a0e03070e0f040209040312020706050603010b010c02010c0b130602071b0915050616020315070e0102011a040906091b05180610050f070b010605030403080a 86
    0x42c0e6078064030780c69107180e007484140e40001c2c0c124280c40c0024840b07055100c1003000030301a499002c1d6142e44200b554001030505000c0139400c9811310f22000c0c0c00704070b0030303201c420603440c0c0056041d41c100c03006580e242011a50b9a0f03200441004450000503060305004260700094081c42048008001e00c11380c080054480341d81145c402404500c03080b0200b408103c204030340702e602c0494103100042d0300004c1d03590034080740d0040d84d046070300060045101c01d4a2011001c0304000c2d21a60100300906440300a011000c4580c0c0d2040c1c0740f1400c8001070341550302583c01c031401c075a140d015040f141c3c8122410366283c0130007021609440083c0c0c0c4c4103210300544d0301c140074415602d404621803091a4180700c041c0800b80c00703803210566a0343d865504e54800201e803800303260055508010304142ca00d0503c01006450581403641045200a007021f001580e035850120038400c0c0d4a40c1000d60b915201100410b080d402801005845003106400010ba0a50804000e41c03007070340300340e441c4543c990350103140700c2c00c4507 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 284208911 1250 284207661 284207669
    0x12020f0d03051306022802042915160b04050a0c060305091005010b0f1c020412022704030305040305120f150103022104020d0b0103050a06050c070c18060b03091e0d0813140a1a010f 79
    0x404190313801050f03102405a130464010ec007550504203098640c051041c05603481400029550410045c2c00a814003840319103155141007031026502d0000440198081c2408052810749c000651640645c81e5003540784441980300c0c01591650341d2403c008040399440b05003030340940f0502d8004882c21022202c01881c440e504084800181c80d240c90840007044000d00c118188141002030a0141400c680410301c00d03050650b00704901e24100341003180301d50140144505150052141d4034031911038070803040c1020524481081c5035030b29030000500c00c10f6002c2e03014007000841e00c004400c0c018045500c0d17101c98020442404940c40e52025401c442c410090b0180c0401e0200030188a407112030300600391035051814010a4042e214000c40071541d01c150703409510340d40034299008801d81c010503038941d00da0480028040c500c001101c01340591100404151003550390385528002c1111200006141d090360600303c900080d20380c907280031841d00d184c03070700e40ca90a5600000640e00007498240c005607 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 284210161 1250 284208911 284208937
    0x602060c040308071a09010c020d020a02011205072a020102010b01090503060609070203090a061709030f12040305160605072712020f0d03051306022802042915 70
    0x119145494442c01c1c4d0700042404c5416225801c000c601c00a20f50041030300440c01e900c000948503428400c0680b62210502d40c0340d096400621040c030150380c10080040501d080d10344041000d44c1d604004449007042000164400601a844070b0401c2041c0d9540c07813500352003078000300b115000100054941c18401d12030380d680341c1d00c010001025800c20703010f95900802d15004036804d0546503800030305101c03201d421200000381038411804d05c0d00c9404d03640a4100c81c40c2006186010b801300c80b10140c0d485152240011004040d01240403d403041c012218909105024036501035000d151100161605681000010b229028200f05250f5202210fa0281000d02107242d1460304d4480101c3d08100940d409a0340030365100c51104286c0c480040020391603110b580c5055480104800061449140f038026104640c01403000745440119003418a83c1c011820062152010301d03440040c0107007002440501518422403800035a0340303030110341c0c3d00da0007000320340c0700c600822100258541c0d8051000c9410f51 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 284211411 1250 284210161 284210167
    0xc0d0201030e070504050a021c0c0503071404080318010815030601050f0f060d0c1b020d080304060905071e05010302120705070c0e01060807030e0a050c060f090a030606050a0602060c 80
    0x1580690320000b10412000241c69030241d44100050445000b11400c11410f40c0000d1402c40c0400392035890f20148000040030040c5291490f4000c0190000409140500c140040440703500ca412000b0380d001444c001044a40d14a0390401310b510424500145602050624003c80c4010750041019184008040d004000c2030b881c0c5420004001080c8034620b40110360300030028241e841c1e030002004a40c44100c1d001c02c1e0020704c908010411410341300905081c1c22035101560041c0d9600d80e0301c0c9241604050400d0b125115420309100500c44100000c066120b1018001000b5020303800315021703400401c0031a00c1d078a039202c0054043e4800c003000e010395289c02000190041303018102405a0380c1c0202c45981d1159210300c052a0004000c1c3c0001010540700420400300d40c0d4107010380200f800c3c10601804890780141c2d5095641c44441310641d00c100004644900e24203100420383d090104000c294201041d03484c28a50000c044034080c00d40100306c81030011031003d00018420b4041d000c20814945 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 284212661 1250 284211411 284211413
    0x110904150b04020d060b090a36272109180b03160906050406060e040c0e030d1e030b06070615090c030222060203090f030a08041e080c0d 60
    0x420040e07940d594019400d10902480e4072040c443ca4001d40200c000003541c402030281000700d10202c42d0703c8200200c1102c41000a080c800c80b410302c0c44401c84082c402001d5441420740005092003881c08103031111103003201b110502100d0700100c840e500444051040c40400746101a444002910050101d0640b07602000360710075821030702c2d2000500e44000507414044000183c2071284c0091128040c3c80310390380501c1024118440c1100920044038108001450110060040d214542c0c28030f10442d0340342003509a1a00400020040c1c10009098a115603c1c1807005081e0840904550b00750b1070b24040540c44460083c800c541d800e0030000c2405041151a0342c80030080e0608068140321222031440000c0c00692034000d40c0101003413500c003d61901c1e941900c1e003c5540d24421050054911801c041110f1030300441180d092400c150348140c00c040d5150081303880c103042c02000a00f50300000500040031000000760059228050a004030010360700c0045a41c0c40e9804605a07601c0512040d10780 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 284213911 1250 284212661 284212703
    0xe0903091e03060f0f06030705090a02070c150f0206090312010513140709030201021506100509241b0105060307090c1b0302160602032d04030b04060603110904 70
    0xa4046003142a128119181c801c000c2410180250b0340c40c2c0103001c0e200c00b40300c4e0f5031801020b8103901400039402008081e107041c00045400c20042d1040002c01d0340001d0081c180100300301c03464041c01000080034094560450010b0081250206100050080f01c02041e602d034004021a690400c0b030120030050340e42000c0c200003191010f071121181d0188d5404032a140d0308202e0a54074402c1143d9161000314a107940006130900f020200b0300001800c03120100445c0d40d442c0d030340b00c031031080039481c0140d05c1c0c100d11008210141300d00509510031180c4100101030140d01c2800809441041c44000c480440b41c03035402c907090342d40550780300da45034210344020b10a9410369440000300c5030080c51701c401400c144141044100800900a0700141c2190001204119603102588000c2025200941c0f810082950080ba1400d110010007201064418a03000c2c2c086101c00b031381c01441d0818003626560602e4174215008084900c0304482e144800b81c000c20f0680742900f80305115582000080703440c645200301c50 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 284215161 1250 284213911 284213929
    0xc050412030503090a0624080604230304030c08070f0b04031703041e14160e010b0a021203070503060906040207050615010908030c01090606050402192105040b0403090e090309 77
    0x1d038040e8450580c0c1c420101b40b01e4001c0ca6100691015a0780c49164401113050301100141c004102aa11040902000607040004c000e0421602000000d40c4441c00e08058118821944050400c4000c06004606000f000c15a8001c85d0850400254815a01c08400c101801140f202404034100c981d01d41d0480c14800c0d0041d03030700a01c65036000c204091400481c1820b46012081591094458081c00c3c0d6403003001c020702e074012009410410503103460145000e520000500070310b00b010b0300c08215000d1050081005200c8000c8220007241c40303161041c002040c2d508112501441104d4010100d003da0520b1f01c00c0b211580c2d0040c1c0a00038541d00c01110301d518401c0f10040d00d042101c0d003980018400418800f810806c1c4084001140c40c201d0360030079900781c40d403e80007140f1440c4100020a94184c1c076a4801802c8403280c1048904c5070048991111510141c1001d800414201810041004a504d640c01d00c00c600c251100c510301a00c400120004c12021103000010358002c1044078690300e081850 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 284216411 1250 284215161 284215171
    0x1b0f0e040b040908030402040507050427060806070c11240306030c040608150a06050f01110f07060906031b1d0d120c03170f0a020c011b120c050412030503 68
    0x7098904100300032504440c0c040c0320543d100034010081c0030451600e0300886403c44010b00d05141401d040c41340e8490200e400c2215000b807070240f280480408811600604000c4c01e8110944407140b400001c081d1178818418801c86820075940c41500c40e40c079108195402c00050441e109111501c035014040c0c60b58005412a40d05104a00602da41660f40380680301c003812510000c0e1048004510242001b040050002c4045074248002070000d915116204e00554209203060803040398803541442c10301019074640c1009000d48400401c4c1030750801000310465a0f039076000c020360036030001ca8108001404d1030000c00507501c8940d010340400c0c0c2d120110a004002005803510300300390f1340c40d42c0203040d8403010840071a520000580c00d00da0020300c02c40e0324200d4520fa5061601e000c000045007010007d0004083d03560104085054243c25840340d040203034402113101e00403e00388005007402d091208429161804c0640c044045ea10940588003140c072074944100180c803940e60281c40c16040185 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 284217661 1250 284216411 284216419
    0x6020f0d030c1704080a090506030402091b1b0705011101140703020c030d1e050f161d030303040303060911040305122b0b1e06030403110c120106091b0f0e 68
    0x8200c103000c10f00207403518012071207140b50950f01c01d04000e0142c0a40c1599210741d209001c24000c00000d600c910811550145460100304450001003104074005e0140381018400c05a101481e600c2e0540d0018035141528402d0300e03071140f501225542c0501f6580c440000c0d201030b0308a1004a001d15020745c0113440104070b0f0303c00b41c0b4201180c169150040740c01c0f110001c402d0841400302984401007901c58070742c00c0b42c10390b0b4102070a81b41c1500c0b4511001d4950401100b0400240103121101d10005000c1380f081d1001010b4035501c2c100b6041c01001f800346805101810b903d00201c3c205401c5a0341d0845040702c2e480406025010b60005115a00d0f41100d2181c00890b90080c403c10140c0003140c1060508110340040040c0f40d00b200000c0c4152100c003540714144c07003900e03480d420803213544810a503a803290307146c6445a030307044405070400e0818a0381d968a03034100b890100300f105403010641013001560758841040000d4035485007048035480b101c80c4440c0106403000124000d4a100c0c0b070740300d15680340140c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 284218911 1250 284217661 284217677
    0xc021f0c0b060303190e0a080c03071a040e0103080a08090606030703030c1a040302160b0306091303141b1209011418060a03052403030405060d0b09010305010b010906020f0d030c 78
    0x5c400d4141c000e000000000003d54800481c070f4980b030007000700c0010b012500300802050300c041010035030340c1880e405040c20928290a84810f0310041604803000317408070b42c00c0d6850a595034900811181c100c41c8507540171400f500c0018800340c0002074042d10911000f00105405461601c050346d44c1d0003070440684000401c901c502420181e2040340d240034074425030003840a00350720344424134000259042056060300c01c000b0300135180d031604421134124110003841001081070345000d4442c40001c6486c492415008503c0c1c050034040390460080d9089504140c4501c1d0324210310100380d0344540401c0d58003050a5084040c0e4800740a0f000d00703491030158403511903500c8590b002944a402c40c80c03049002036150000c01600c0030951f000440b032030303c0c506000700001000c800066200d0007240074883c051000495100b000c80456001a241300e40c5c060a280450358403420514042c201080c500d80c00300d06030312000565940300044403900d841d0681c0c007030300e82d021080c44110064020001070800b00301d081 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 284220161 1250 284218911 284218927
    0xa14040314070305062202040b12070e0105031b0d0f02031f0203010312020d021005060d0c0e07170c0405040902150d06081e031204210c021f0c0b060303 67
    0x500c60500054118002d20700c161552600301e1a1000062010b2000c440c228020580d100120010710f1410b5811500818007604080100d07844001c040301c3c00c0c44911810310005042e8200300c00310740c1a2442501a110541d04038a41004400d501d480095000100c64502d0000310700948059180d0510080680d280d040c40d1243c4a040c2d104540f040c0d000c007540c000010010820810004502c4106c0350001e081d03906c020003c0a529103900303030b02c1040155103076400108141d840c42840c10381ca03988603c1d040750f19a00c840c0078046020045a00c4004901400040d1181c1895894110700c00c410003907055290908000c140806080000b900726040a102c0f0142c2c9a950303111006480000f02c26040010024680040a031920360b91403041801541c00a4841c6501c480c00300031a00c01101805908159481d14034240303405140c0009965042c0603400c0341c01040f281e02035a2312035014003c58204051165055101e101104030403020f40c0411980725031800003903015030040e64486001400d0301c1c1480a5 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 284221411 1250 284220161 284220173
    0x20702040204121118010308090d050721140102121303051b0a060501170a03110c1507060b010305160813080a02010b090a140c0d150311040e010c050a140403 69
    0x7032078040701c0c102d0380d101d481c80603410461105d4161140c0740080c0c0025515640f10b660040c86810920380c003861284410809100b01044200300078181e054000c134403086641d001c0000c81c078180c03c04480b1b64810b9101d02c81c89071014000eaa091035920000103155844001280c00400f43e00002241031000a009448460038080403002c0407002c0c2002408481415107094812914140c008000310300c2c60701032802c0349800c00542001c106501d03052072240208200c071001e1800400d402c001c0e03480b03c1540029030048203500040d00d5040d106030f02c240020040d881c010341c20780c0e5040340c4c150000114500310145080c490509250081c3c0e20900d401e41c01202900e81e888280d010741e000a025039190b0180703000c0350500d50728142c0e10842441042248840005039055001e40191080660b400d010400d103407420040e0303100440d60420441c40440e215030b01d141800c2c070524095507080c0304500e454407075040c001c0107000e00905403100eaa601403414111741410380350045c5510302c82c0100401444003100040e1 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 284222661 1250 284221411 284221439
    0xc0f0709091208010b03180a17040806010b0a122d150501020a1203051e01060207091b080610050903070305010b030616020c0603041a0a0c09090b060706020702040204 73
    0x190080c085409142410b002000d030400141c07a004100503034004000c0d8221500c1680e4000c0001020f00241e400c01440e414a050f001da18007070031a0180750b43d000c80c03c4001c10010f10403100d651003641e016130303a00c0d000c0080358060b03a071005000ca000000401c01c450510703841240305d0140522504c4020690580c6004020041d00ca0301210039926035000c1131207a1821034500013040709200804000801e6038038107e43e40c2910090310185515040070a4540d0040219031501010b18060030106686d2150001d540d51803500c90004454076000d00500001c070090080030180030701d41c49043d05a11500e040c409403540000e0044208a014401ca0040b40e805000781c0d80214000d030300209240d00d02030105414008094046c4001c400b25104036a94036402040e41001400d044941d1034486d80c0740d050500348109c0c01c000c491305103080b0204002c0005080da10101905003a0765841420a03110a002d000701d503000e00c00307954054018008480011415002008464400781001d4146aa10f0041c003500c49 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 284223911 1250 284222661 284222669
    0x30a0e0a150b0f0d060b04090203030d050f070e03060f0a1503031107091b030207020f09040605090d0906120b060c0a08030f0c070f0609030e030d0e031509070b0c0f07 73
    0x22240038802515444540038460622900b220f415001c40540000905100200c0d60003d00107600d4181040840e916a81b07c02c0d101a0083c05a079650f42c2c800c1c2840005100482d070721400b845c40c4ea0041905244100c0d81c400c00200064000c00ba41c1e180e1901c1c5803900c00000f40302144080d20307178040305800c400407a59a0000e61103070700c810520b010003030161410089181c216901c090700c0e1965890448100003c910002251030800594641890000c10082800d903101d00e50401d0006040c40104221540107034031541404050794880c1e00a240201c0e85801248101c80004c0c040e9a00d1401085103580100c0803000028040340c0b6040c1c0072801c040c02c14a0244003070b0b40c1008088200080c284c4460b418560204414510f06c1c580382d041d580d001c401074401100608410f0307a4040e000c081601806001403081c6004044a00c3c03041c0490000303203020103500c116401b90103602d54000d0703005101e07040503005825000240c5a000e045c00001038040d040f05610769400c0c8641d031191640e0710400e0000c5c030701174 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 284225161 1250 284223911 284223923
    0xa051b0c0a1e110d0201090509040813030c0501030b0312040618080706020607120207050a080d020904050c0d1401050d0212030d110304061b0c030e030c03150907050a03050c0105030a0e0a 82
    0x141c007550516a90051404801138021102c4841940060ba8006414015104202c601080d991a10b060040d0180140c0314282780401101c0ca000c4107002d4244032400840342c0980e01403110316240b00034107032122014803014210b5801400f00784102801100700030030042c0d10081503080c465031051201e1038000245d01141c050b030481002c0c00b21050b44040e04801c0180c002c0803d6282c07c1c800c1c1e4a503136844c0080d02c1c4c003a228150120b01203400045e10380480b861302000600030311040c10600e078007040c40d501081c03600020610f002079115403110b09003140313412170382e00504032840c5080a80030b01142d02283d100007010f070700007000300d005207021a20072402c0c9600b110310600c0e08c1e858186001000c90f44c420112444248114100c88101d640c002d5680c00d070158140391040740e500380400860701c2c01c2140c00200f40e0600690031600100e10140d140544201c1c1e01504881409594400f03011504509004c003400d5900101c0050031954001c00c010b43c0c000e90b07003801c0064901d100d02e19507814280290300403118 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 284226411 1250 284225161 284225213
    0x30309060f03040201030b0604031709010908012306010c021c17030106091e08060a0c02030d090602120109060b0d0207020f0406082a010f030e0106150809060a051b0c0a 74
    0x25946c1c1449505454503003610040e11b0300e81982c0315a01e024082c68003081606000080c40380917a44520480302c001c002c03a1009010748410403001c1c08914031081100e4114928450000c0e6080d8441e841c0b80d0305598000e0821070304030489081c02c1c01e24100c040c00a903040540288070012000341080103500900310f40c0d9488104505181d01c5814002c02c401035010400e218000902810001003842504552541400907860080c05400d9065004000794071401c4c2e840c10200000b4084150001c18400d25411000c840aa8031420103d00b04d40c524024070820031400d008641c05041150b00030701c03000c1c0c00145404c0040c0c3c04d150005040c1ca5060300458001e1b08030384090a1b403010320000d0702046001d42000503113010a030000003041c4a544100031170030551120301003862000294811001740c13403407500042000d4060200035200483c10380d040c101e544180c0000581007205441094003600101559050030305d8104043d08132500000340481d141c1c05041c080400140110084540c024006104001 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 284227661 1250 284226411 284226413
    0x41503031d060c0d1115070c1401150f0503011104030f03091e03032c0d080c01060e011a0c030403020d230f0c120a030c03111603021203090a14030309060f0304 70
    0x1020768503803541c0e00d82951110354405503007100301c03000d1b0342d010b00ca80c500002209441d0405640101400c890211213529007091080d20b00301c21402c46003a508080c0700d1038001ca50341c0d01030508035581c05002003039810052005000190740c1e044010711482c002c0c608007030040d40321240c203940c001c0068400003011120b2002042096000616604a030890880c0b91724540301c640d400017030782c1c26803070620b40c480c8260315014010006402c3c1a03a041c2e803000e200030031500d81c8454065134410000e00440003c08400c420b1003501c80e11920440c0c12203c40d0300081c44c2800d1460b401d02a00c489402c50440341c02124000320850f0300d1420a0107940030700c2d07030f9000b080030001e1000035500300f1041d03131007407400390311002040c1c0d404001c006948540e15138180392480c2c9101e11810122000c4c110000005c41c103024400c02c00e000c0d00e48003207025069038001c4032544001c082c200d40c0b059032407007103044842d0005101481002000e0010000407211040075040c0d07842d0041c403600082d6103070b01032090406110301c0802400 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 284228911 1250 284227661 284227667
    0x8150a090f081b1506030c030a050c1e100206330d03030912090302030601060302040e041101030b040f06090608011e181a070e041503031d060c0d 64
    0x1940148251604104408881c0c5440415807100d810107404a000000d240d5a2071441c0203a034102404890155551428000501a03440400340c40c02d900c60300c281b60600000d0329000c81c44104065200e030042c0b64083d8688180300021060141000c0c001078a648200c0f0b15848028071910324041640c0500f8061904482002c0c015200560002c010f41c0040880b070200d1460382c104400c3c1c1641111915070b0031000c3d00e07080300503101d0903000a001c2d88400b8004107025402c5200081900d108900f034441580c0c823a40c040381240198802c0490103000302004c5004202403c811801034032040c5404140c18001ca0301140a491040c8091210b0b1982d402040290310060b115101c05040604000d200025151041103003041030f03800540030a0707a54101002c00e0142d641c0c5030100e0036500860846103030700540504c1000c004102c03004400325911400c01e0185283c01e108901d200c80e102041d00c0d07142c50030342d102214107400401040080001002c000c07200c6a5508024140094011008049220a1103402 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 284230161 1250 284228911 284228953
    0x406020a020f0d12020d110a050d050a09110d050a05120705010e070503070512030415030209091b0301091508031909080703081206180718060c0f030f0c0c08 69
    0x80541604070008205403150304c02810403555051102c00768030390300050604d500078601c409054040303200004071042c0140c0c001002d4618a04d070002e00300501e03641d000c0c07980c06941300780e00b0003040e0100001d14241d007480d2480140c14000e010f0800c4502c45c00d880d075034180c602214850072190802010034034000704042406450f01c21006000902001860030010950303486080c06030610441c20350076564103203e402c209407002010782c40b5048a001e204c8060183c02076010913100c90107400705400064144280c44550f60400c241c1c81c9556145070b1030155054000c0104e941102c9800010110009452030108007624110300440058007241c0121b08010305000100d911200c5540c100000c104049101501070f148a0020801c0008081d92810001380710f500207002c0a141c9502c951040c00016540302c212121400306d8485404007035901c2d00d506507034040b0b00b401300030078409010700d0b000c0009100b402e001d41c40040318184900f00c7c01455862004444941c0c2144a00d90f12102401304507407001541 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 284231411 1250 284230161 284230183
    0x31b0306081b03210901080c09030a06050606040e1617010b0d090807020d1a0106020a050a12030b0907080405060106081e1005060408030705060c13120809090406020a02 74
    0x304941840c00c0002a180c00c1c595200040e802c12a80d411601c1d600c0034016103aa46020704034400182c0324224415402d500003202c1540054040380028130740394401e0049a2507018006c00034088400255075200260000a0805030411414000001c89040b20044030f0300400c0c008c40c005001600025005080303014040d529000702280400411415010408488940e00c40c100c0200c6c104281e8100402c80d880f44060007900240711712016000c2c02440d0615580d041010f2079000020390ba916012039480d4542c440140590300f0490b01800001c20448064408070301c50300300031030324140c4000003500345803080301c2c100007040809003000304028040c01114090911401d214070181486c00401640a0003454410304102d0668085048940c4008007040207020040031681d54544800b20a41c89400035a01225684035000c00724041911110a031600c1042c103e0401d0041e61510040b07500d2005d03008800e94116100f002201480c0d00c0303100d2050700c928010720000d03a44c0e00340307408020324060f00390030 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 284232661 1250 284231411 284231417
    0x220b0405010f09120e0a170f07060306061d040b0907020312061e090411090a020c0f060c09150f0711030d0206010e150103060803040e0403081012121707031b 69
    0x1c4500004c0d985142e60000c134215843c04201308a045804180640542d8010040440310050034030350706a8001011038940b40c1c1c40086e102e8043d51b4440550640c1d55901030000450764015480e00c441d26800340708000140e0042000c1520300103040458051403086d55410016080080c0200140094519850f08110299243d258510003410141c0c1030340c41c0c6d00201880340f00c1c0c5501203014801083c0c0031856000f0014195145420201c82100003580311201090040c0100b1540c000c0c44400852418800e020005602d40361050344010800c4003907940904000c5040c0c2030000300c0308409585d000d085280d21500e1098003910300c400825151007140e68500381198001c0340180419012607040d25003109135100480c0345240508016000703848036420114a6100c085800161a5512000c080c02240242c1307411141c0e03242d040c2c82c0c2d1070020042c0600d040b15a000c80b991400568032080d415404602441c0840100740c0004003460441c0c015204140003030317282c0040d113540410103490503c0400c101e003 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 284233911 1250 284232661 284232671
    0x611030909040201080601030b030f100e031e070203100c0503100902031302060c150c18031b150403060f09060c030e062e03030206070e0f0d0b220b0405010f 69
    0x2000041c404400200001e041001c5000402c4441c1d0003900500e2040c2802010341c0c803107a141140080c0d4580310154030301959804d100200b106400302104407000c54001c4c60703002e46d580f04039180c210010750080b80200c0e050712621a50356403011243c072400424900d50b43d9129909e0409014248030300003690044001c181c070400501c00390b840403500e0b840040d0707810b69015440f81c0170f0010702c50030314003500714118a100c0350004002180d40d104004050400f0520100000c0340380000c241551060f0a080144004514600c00074240c40d00300e01c0d05c400740b40704401135441c02d61130307985031015200458260800760383c80c4c6110804000c1b1900880800045c07506c0c04015030706008180743d0366070a01030034001036144080e079111140b03160b00c4803941000a40411102c0410343c0ca1800a560b044112030220000d911103000505a290802d44402c030510018130545090310191506002200080c0c052021b40d40700184000d0000c0104204610ba1802210914010310b4035090003400e454030038442c144520301d40303 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 284235161 1250 284233911 284233927
    0x80f011a09090307020d0501020409020406020f011d060a0905070b07050c2b0b06040f02070c2d0b0a0903021c0507171914060a0e1917070201051903020301061103 71
    0x4103945044d0303011150b60b245141305060207030081c17240d0381142c1c0c03515000041c007144460f00002c10761a58403018000700081101e00c2420b9110300c400b0005149290050008501e603100b0681117483d1140c01402580c0c00b0720345c0c5003180d031019030142804503081d4009030591b88051500e226642d02000a003805141104100c0000b007061400d68003000380004a003001081e00ea4407541e2004c294203d92141c1150745a003a410314900da0b42d11032141100c880d25402d429800003040c00d24019140c00c82c1e02e1200c660b0f500303008030100c07107810810291b810065400c10000240c5c2e00e0044422915600e000241c01105086c2081810074a258100640c20042c4007841642e0f54000900000c4100300b40540b800504001c2c5052800705402c049020780754480c4000780821130050780e0201c131909002c101110394400045601504204501c400603024414080305c61418140c03003001001c10510503d0200c0c54200300d4510a0448100c0d124441c001aa01000620009400c210038419070b40030f1a00070b504158074 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 284236411 1250 284235161 284235163
    0x628170d090b090607030903080d05040c0b180f0102010902090a0203010f090923070e040b0601030e150a1a04020301080102130f0e01060309061d0d031b0e19080f011a0909 75
    0xc90a0f0f041c000d032400507110051610401005000e154041c046030b039102001c800031000380038150381c01d56042503032800020f000301040c01250b048050f4140306107130f40c907400c00410402021159900d41595203410a1000585e18903003064812510040c0040c0ca0354106609040e4841d4503801c140000b07071801001402090120540041e4644004400301c09110081c0d039081c213110640d4408007146c08080140030801c40c100360428420182a6000c008206101c00141c1e41c0d103030001c0c075808002514801044030851303d508042c200f04020001224034a8180000c14100d900980c418503403070b50301254040001100604000041c40102c443d10341c52424100300840082e410312032001403641e40e6080004002141c0c01c00612500d941c44094107900e16548400d0322896109424000a45040401400310121031000c0c044401d09a6410303440074010804c0c0080282c65180030104a500608000b0700681c00304806c1480001100002c500b110440a2900b4460802011144901035a1003002480741c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 284237661 1250 284236411 284236417
    0x403020609010c0e090a0212150405061c150b060d090c0506091302090d08040902070501050a0e100b0d050703030c0b0705120a0f06030803070507150605090628170d090b 74
    0x403013104c01d1030942d2201c89440000f886603403124140015500c0c100a120b01d68454200b44102042c2c4041c001335032100c00300080b4050011004074001c1300d400161000c140c0055004155030466540010218100800184d080d0004100c41c03200c0d94a900110080003400c0c11640010308054400c9030a010543d400a01d02070301d040d10b85403d0740e80c0404c001c423480c1c2d20403005440154001b0b42c210364441d1a80b0248010b54071801c4c040d500d56081c8008030345022181e00c1403000301d008284c003404001c1c6058030100e000e0444885400c1d0300880a4182c0c1010800c00c0c0441c0c03000710701c02e464207800b5002601d41001407800c0201150305110060280004403002c040001c0d03840b8074043c03000100e81e00b0024690f0000e09054002600c021004010003e00c1c1d900704d401841042e005e00c200d00e00b11041500c100090310424010950061034400119000d800d10700c0ea010750708017803204400d01550243c140350005c15456800780c0c070b00100314820041c400303a0074044501c00342c036a464042c41103420189603001c02c1c4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 284238911 1250 284237661 284237687
    0x801121a2802091f0c0c090f05060102070f0501030e0309040f020307110309060a1b06090b0105030106170307120504091e0e01140408030601090b1306030606020d020607030906110d050403020609010c 87
    0x14801c4029917813040018000e502d50040503100031940380c0c28030382c00800d8101c3c1c2c104949031804000c12860f40c000215441283d400c148103c0501e41803c0045026003015070500d000f6200c02d000012280c4e8540c098280740340c01d4401c0043e203901d011741c1d009100c20502c071084041c6030800c0000c002c0a4a41d042114039800311070400451041641c010801d080d0a0450b02804140c40e01240004004001c81c80a0480d04224000e00010391201103984080900c1c1040050b2039204102c00d50000c3c034a0700b0f04600000c03590500c0e6080681d18200e4009403140b4110001401d4400c0407940750071059032058003c5804407030001c011045e003100c82c01001c0c0002400142030500048001758140e8841d0917202c0242a603059950b8440c2200c20b840207501855010b6079010034146000424040c1c800910210740e024561300900c01a11290030035401403030070b16002e4841d103494003803054195150000800d403c1c0344080c400a11403405050090620101a01094136030f41070100b07040410b42d2100a41043c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 284240161 1250 284238911 284238949
    0xb06010c20061b011505102304031202010f050a09020306040f11210601060215070c0f06050705031b0406020c0f0406081e1006060801121a280209 64
    0x62480c40062203500881072410050f403425103500344040019009840040f5180000c0e82d081501c0d101000411110509198001703840d1841c0c0000b020960243d10412001c0b800109140944a0719070245c3d9661900c000d10141c0c9d10b034944482c0901c0c9a110361540005201401c120810041c0d000940f0f0310000307000a00412010800d441c00d00800d04a030000d81c284c01001c00d6035070044050641f54221104010450703031b0250800000b46180045900000c90a000d90107140583c0d405030107803440001e103801611400c11a04142001a01c0f178440c5501406140d101e0750f84078038101e0540c00054441212104004000380020407825400042e018002401115845d80c01e1109801280c000c100c140c0c0041c2c42449400412800100303030880d4090301c9100e00b003d9a080c008130585100545e661441903100007620300004005915030401c610000512a600013074008040c2e200c603030080d982c2590308000303030199145003181012808030000c41c0407000c03410a50402c1a00c2c0009012003070a2070303103c1d0300 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 284241411 1250 284240161 284240213
    0xf0d020c01050d0203100e1302011419081f030c050f0a0e07030b041503030f1e0e1c1407090f050103080a0302070212010c21180303021e030103050a0b06010c 69
    0x60303203991b04019000781107403040d00084c80ca40901070208040e6500c809030f000c50701008421078038600d03600c200c1c0c000918150228080141518084a128200808145a00e01800b040802c0c0380c00391100c0304000c0d80590314010b0312a081c802080042000c0c3c81025205e0450600100241004a0b1a6940c85070031410000382241c41c0c1d5010401500e02c2550b9201d20010201c808010960000105030000c5255902e009000e0700500810110a9003810380b500401d405200c00681e600d440c4403601d52408000f640200700c004140c0e1107904842941403202e145801002007400031501d1441805541d68202d041440700c6e5146444010041c41500e15070400c0540004001041d900c888041e41d86a428140c020049060801d500400ca20380484075894003090b249074140c010180d0340144a0810300441d20055160801e940a5009500c00d11020004030b07000841100d1650389a00994000c0d80107101404166000707242207881030320000d0526050040401c00360780803d40090540f41c00311941c0b10f141c80e03 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 284242661 1250 284241411 284241421
    0x10f0f050a0207050a0308120606040b030a0c0e12010c1103040e01091d06071214060315070306090e070e010608220201020307020d081c0605060d020310080f0f0d020c01050d0203 78
    0x304004150b0441c61304400c039107100108004070365001380000341042305002400c1e1106010401c0d544a54494040e080d8000d0020a511440951040c0d0208105040115110880300007007425080c0140d80410565904c014060409400401d144a082c084101452405040114001200c501801110f640039600c40042c10b42d1608a462140d03045403100c01c0f120685440e4100402c1c3e8142c1644880041d410982c0c10081c0785c0020206900644008011f8103803e180d400010700800801003440040540324036000800c000381d8490f840c1e060315104041c0a0042c140522a2000e07070040e0311a204010101081041c01c0041e000e0900c2c2c0105118071083c3c1c10085400106d2460140100103036009050509100401500100030202160801000d001110003004040103d0301c1d0783c400c0380d4000134100711245a5090b035500566006211a0301b5058068031581c0c21446d05910742c96000c20741d40050b4a032810154100410340d2a1045071006100003005400020000d008074070003d41100c0c0c010002c03c1c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 284243911 1250 284242661 284242663
    0x13050c0405040e0d180b0901181a2203050c0105030403170f01090c1706010c06181a0f070203040b03090f01050c1902060c0306150d0218010e010f0f050a02 68
    0x2402000700070070900000d180c0310a11070b16001a40601c0001c0f0b146130301250004090028003c045038504030506041c212103c00550702800c0321050050960310010003c40d150b00c041c1c42c4c2601407101c44072010788a40c0e2000561610200b8441c25880b213243c80e510400010b040015111000c0070280f0b000c81d00c81d116882d0079500080c0a206141d69503860200300b200130116030001c0e03030484401141c2400002c010250030b403580000355a2141c200061f500c001642c3e5406040104600c41c1700b11400111603407109808890306100c55002c450200300c0110001104403188113054100d10217442454031800c040d03030083d50b01d209511605185810210010311801d41c1800b1092016020200074040c91500c2e29103844940c0c0500ca03d920100619102c0d480510b01c001515481207a074805554610307281c0008000122584400c402e0f0f5400d4100107000d04507840b40003070038400f01055444107000922000140c512210f2040d018104200311140d0786000f603121489032000b41490402c0d039034a9203a01412 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 284245161 1250 284243911 284243917
    0x6050c1203040501090c0e25020a0602120109060b040b040e0c090315060a0803120406090f0203031c0513020f1002070b040608010305010c03051e0709030c0b091e13050c 74
    0xd5151000101c1000b00380309064000b4442140301d04800c805081e128000c90032040701c2610700750136410f00d608030001c0d0303801c482e92002c40500050044908501882e600c100036a48000300c0300d40312280030710040003807a025019210240884a17110b07418182000e0241106004500c901116010b203400850003004105045600d406406002d54a014100311710b507440904080d640c040c0100555031000072480c03404415210b96000d4040c118066880d40c1c5c4500e00a042e80d004191414203041e03d6402c01070350204005c00d00f03080140180008907444c03d540001300c5500406d0103100c910400c40000041c1c0d02d001440e14010070031034175004501c0100004034601035440d0000300000c4030000300843c0c410703004100e4504130b078840c800038001d511200b00201c003500d00580c1c88401c80480c0e0314402069130181e440c110f03405200e5160001f0794594039102d0302c0c2000e80960101a4110000650110700d0420f05036076020b5400d44070703040a040c80c0042c0071941c03030f102c4050200d8219540b0304c0400c00c024030342022 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 284246411 1250 284245161 284245183
    0xf0206030c07230706110f1e0c010305070c0201050318071d0901060302090103030f020f03031017070e2d040308100608061e04020d060609050f010905030706050c 71
    0x6160312890010320003040742d4085402036880c1d50440c0d10940c4007092150444800ea040b81018100040ca400c200392510742d5140e00c1510180552a8040308194041145108014aa040145484202210444c01c01c0202c600442c1010f05020412523440e8126810705c180c154207280060b41d0382d40380080d081b20f500303403405c0c04103650080000010381c01710040c1d044402e0103990384040d00c2c6502d03100805c901700d0307415120080d00400f00200401c04a0b00072590010100d4103401507943c0911401100d90540e8000c03152102406a6903070706106429009251034040300904d0003c00e4843c0c242a19540081001840741d40c019a03c04856198003083d85401501420711880044042c1401d00d400b60034080202e82c0b03440100c5592000241c1e461085042500560015000c007001411031040240f0b81075060041c030f034000d6020800c54210070080d02c1200c0c000c4c60710741e4800707a83e6800d0108204180e03c1a0308003d0402c40d8104003070010b079901081c02022a0314900340f080e070381d00d400c49105c3e0a001010302 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 284247661 1250 284246411 284246419
    0x601020c090a02030a0e0604051b130903180617150a0b16110a0e040305090d080a0206010806010f23150d060e010b0703021510091118061e03040f02 65
    0x7080c0081a401074000d1805403240c25401d00c60400c40d500707410355402007181d01600715030180c1c509070a07401d907020b0620602d01c0c02400180410b0f40313054421040d00c601c4501280051604110b090116078620442000f420040c43c0500004460f0340200320108000b4007000a5011601d00c1d050b1140c1e103c401030320060085414a54480c61401c140c500340341c048603070503180b00c5880c1c064400c4074544407041d5000c0c2e8251901c540595100c54800700c5690b0481011103030480340c400c2c0c4100114540074003402c00041640e000340295810a62236504009060b0b002c01c9003011104424440a510a1114603002442200c0c0d654251400c0d0001110720850047c07010303100000103070340e441540154204400b52004095540300a90780c501c0748a01030b200d401005001070300300d0031710041d0107030800d407885801007900c51100e0f9410313440c1e140740c10450323048254480252400180f509403440d112480d901c40d28200b2500282401140a002c440d159100390004005120000004e030030082e5940030480c8654010b0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 284248911 1250 284247661 284247679
    0x1209020906400c030501050901030b0c09090108060412030b06040626010b0c16060e09070e15091c03020a121b03030504060b040501150f020a060c09050114040b120601020c 75
    0x50b1001030004401c21041c03018034102100907281a009001d0f03603040314400b404000f40e81c0e00e1031300c480032000d030b002e06440080c00003048110003984d210056a800f805001c00a0300a908040c034202c0c000001075001c010500d400c01c030b6811820f903500c10658046600f2810100e96442c07025526038449201e003422059038011882c00485d192003010003403c5066410001c03a401000300700304014071480e0a101b040001501c1d41c64400381c2e03003002480c203a0030100e14104204405916000140c0510720306d1915001c001c000329a10059161100300d000000b00705140d0301180c00c4464500035116080b44070040c0031801e07071544022000d44552036520004c1030505900e005a50302d13240c0180503150985040d0b50190405180314654030700b070710a8030304940c2c000c05a80b1101300510405d4401d264a0604101903004446c154408201d04c1e000d400c1405910399207109141e0f0a01c3e0024024001c00d40e00c00b203180509120512120480d141110800c21b002c0740502000c3c2d07503c80c0100d00d80400a811540c11500300c1d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 284250161 1250 284248911 284248999
    0x114031905060f01060e130218131b0e030c01030c020a05030705060103030806010e0f120102070c03050a0303050108300403021807020d0e030c0d080c06161209020906 73
    0x4182e29010f0410907040380c2069980d890111220740c1e0401034198809040c2c055a0b014103080c1e4020100d1074021200c40300941d0040e0300154003007018401076054181c4800389100a044000030841070b50100741000d41d450300c1c0e2003005c00d594540868400b414159580180805c144c001c00c120010113910000300c0e5502d00840ca09941c6400c42880114041001c3e0f101141240d80568114090380202a101030080c081140412640740c200d040003d0032035600700810008100024954805113011f45e005201103181458000c04482c8141d11140241e001844007502c0526081070a001c2d61289000314883c1403c3e08540e850b6034840c40c0c2c0002e46c00510750300002c1076009900681449204590244d401c02c9820010a03944040904561581a041404d4101c0546800c613080520b2900642440c0c1c1000b5113590f40620309074003a10310342c2c00b00410909103014981d005030500706c450450714060080d40f2881d40407030980d80c2c0142006101c0c00d0b0000c1c070710070300070a100283c00182405030b07004c3c0742d44000c2c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 284251411 1250 284250161 284250163
    0x914060f030c090616060f0c03050702152802190302030f0109050933150d060525020318011d04090f020a0f18020403050304060c030203040b070b07030516080114031905 74
    0x1f4003103069146501307041c00d03402090f00074820306104038002c0d0003400005440400814410710700074082c0c002d44815044014040402c9400040c2005040400681e40c2c6016614046500d0f481d03002c4a08041c0100b0800ca00700d0700070311900d4116045140045001d803903800ca031500b0441000b100c00aa64039aa458603800d040701040c1b181a0800200c1103656926848444d098001c0d22580040d00100084106000078100b6840030740c3c030003e450a9104010b01c403030303050b40c0444410b050b103900583c404140650444501001016107a80c00d0030180b030940130394070602c1a110503603040b0620841c2d9504000c018449503080341044554010703d02c140540c0c0300c0d130035101c0c4648140901c001d0410285c246d4980c441403482114162034100c8000d41c00c062401c07404070354a042c80c6800310218081440001106611070003d030011620460f0740121520740140c0082c2190802031240fa03848004804424680b81c1015010303065403105182c80b0b8030000c0480c0440d1408008621240301584207550400078400 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 284252661 1250 284251411 284251421
    0x90a020d1a060307051602100f02061024170a15050103090506060f0105160b0f0a020901090603050601030e060a0501050f01020303010602150403110105070914060f030c09061606 78
    0x6401001005020001201e51012050401005070041030400218030075900580c00b0f0300854036800c00c52007240e0010740c0403d01c6000da201100700440d450301d4507062199018402c0c15031180c1c1c66000c12018600e001c8820841c3c51803040d801c040050402101480d85104a000d030040702d980350a00c0e00303281410b928440040603101e40440a001c1c02200214503580700e0b004084903260460000d081c19200c013010010442403001455040c000200300c500c0e4240f0404000721345280c0140c8000c0001d24258070a410504802400380314000c0c0f04208140c15a07030803c2d4008282c1d042450000391507510000144d00801400e10600413074414901003207070301c512030342206058440a6036440300c4800300000590340ea000038000c030005604040035400d000c0382c8030341c0e110344c1c814020314050b10016801444070742100c00c04e686e01030009070b80107410f014400d0410940b9102d604151115807820709559800c5200d8003001c0c0590340603207000500ea0560b6500c51090ba01c401c1800c42c10100425500d02d02800202 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 284253911 1250 284252661 284252677
    0x101e090c17010b0906070209221a07050f1905042d090902060415120c1106010b0c0c0105030603010f0e0a0c050a0509161101110706060e130f11090a02 66
    0x40140010038a8000041071301d0f00d000026045c40e042045075420000410030040600c03200808001a4004541e806441480b950340140130508211007400d80d4032085c00002070150041c001c040190642ca200790b101154031400110781483e00800c080798084a0510440d441409542c44403428680340d1124405a580d0f80803000001055213035070380075480159000d010000c1d602070030610040144840e100d0043d1030840c40c620b409000303410f18000c04012203905104250001d181001d4541000d1010000d05015010041206090003e40c086440d03a1b181c914035181c0c104030740800480d4441d10250080124a46d2000c41840410750310b035825680e4914084d41595040000c400005035400c0a4040e0001e40308040d11303c0303c0e0f540d11045852000f0000c1d400a000700300c1d070042c1414480c8000e02c03400540c4896580034aa442806040c03810582e4107640100d4018281c2c3d4090215590302c02e00300f509400d604c0501503468200d14107090522640500340301d5007280f07005040003d8804c9a6009040c08 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 284255161 1250 284253911 284253947
    0x206130e0105090709120303110f0903191e02061603020f0d090f06030203041b060f1119110105040f0b0301031505060f010e0a0b1206090f101e090c 65
    0x280e030b0720710400442075030560305074010900840742480038600c0c40722031085107030081c00d010842d40340106100c3c280b5032000c0480c0d09110400305510380d4030714050084140c0700140c1422700444078016103e40ca40300e081c1d0720389180e010f040000654115102d60b0255102c1000c008003c4440d1603d50402a4541811056908440c000c0400a00c00c980c05010302c4019540350141c10741c9150b0030280154020344c8050b00544d954003480448101d10000041114003500403542c078402203545150b806400d00165203802603003500403c0d8820b60301d56422100b10030041e0002c4500b60506007040050340e0340c0c412900080ca00d800007180104403880c00c000114105ca02c01c940200002d4004c200f56001c48030241c4242e988846801858010741d840760008126a060061042240d555628102805035001524000b19502d00604120940c60078203140b640c8886644041010361401804202000d0b8080c02010410f203031003034103240c0020130004080040c05095100b017050455400b0050903009001c04682d100e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 284256411 1250 284255161 284255189
    0x31801050610082206091103071d060d020f060301030f1b150f02010b060a0806120c0901030602030c07020907051201060e03030a0e0f0306011211031c050304020d020613 74
    0x114100740111240101c82030760750a00e00d0300c60034200203003d4407042c1360f011100251241540410f1503485001c48180c4903078580e00c3c140c1035410916040001d00c1c0d00014004581c1812111954404104254400e1040f1055041800e140c8001060f00d40b038084c04c25000f0710040008010001d1301191410341500030070040d0854001703590019058030403402014048000a144070b019335000b0079030005012114000450302e001607002081683d080300c1070460004160400744000d5082140084e040e001400024140c0c03600100c02051151f80b0600c40204416800000900341f504043c06440f082a0f00404981c001d08100780000d1032900404c03914540350f00b200000003a020f00030103031010b0a8002078091810310301c0303400043da1294681380c1202c0e04024408900758440e602800305502a006035103020360820160300b0812100520307100b1541c026403180d0b550301c40c1c01c03000794074030702d0b42c640345d85846541e990300c52010030070813640880000c0d00900040f90b89e640754030030000d03840c050343d40741c402c0700321 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 284257661 1250 284256411 284256421
    0x180f0a060b090a060e010c051f110a050702010c0f0f03261b1c0c020f120301060203090d05010209090903030723030a11040e010305070303090e06090a0c0e030303180105 74
    0x14601c2850b4040350301038900310040100c00d004009560f0b000720f05041840000700145c6a4509200301e03256405080082a0800d908224082c0301d0b101c910081c440525042c401c0b10080076015205a80b4064140907440000008001102d003404003074030ba014002c00390004049c81d0240150a503601044103c1000405a804100b04440c0c1144102022942c0600301c421942c508921588030307566104180414044244d038280060041c01010301d1240c0c002c0000c400d080c082c2c4e5040c459072501c081418a010401080b105500009a40d04c148007142c010000c448240b078028024862400d20365040150300d0304001440102002441c440c030140d85440d96003001c0c0c80d1181c010b10f04400e40b07409015030184042446040356922207056907601c0c4c0c0d400c500c2c041e260600c144103d0400da02c2110705a01c80716041c0201076010941400070440c82515020900b0502d000803400000206119881a921418502e540f4454403070301010380d030058145c0355281007040414070b1440b0b0035281c11100d50b007054003160b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 284258911 1250 284257661 284257679
    0xd0809100618050705070c050909010906061d01120b060405060f040912110d0801090e031608070201030f0506030a030c1113060906050d050a0803060a030b1e09010c02030403080702180f0a06 83
    0x24840387c0e442038001d00070310308003001c00c07840ba8400b902c061019940c45a00c1c0340011b54900c08d040103041c1c50840c090300324011500d80d200c3c0c440305800003c0e440441501ca0320004030211035107138001604070340101d000c8d41ca510210350b001c046116100d40c8141071640d400103101a90419064603c400d13903130001c4441401900701d40c0d030315010340c0302c00c0000c8407500104200030305071b4080c4204041203c1074900c2c25400d1189868100000c0e18148c50a400000c5c0540456806100300302281d00910300a0002d0320708030001945a40721450042d06020030440d5040400560756403a05000c0001001041c008801a0007180100958011203c11900d400004595423038110440c400b081d50000040c8000f42d0aa501c080c010703000602070940001a1070004000212400c105a115400e250808880704d000800340c00e18442c8090405140303645450328502005601000300c03000e49030440e000b540c0d20b034078502c04609800070030314150310310446000030b220b40b800308c035082d250207070104100034400306440300d402c4 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 284260161 1250 284258911 284258917
    0xa0b0109080a1106120f091b010f0e120f070303030e0a12120b0a03080c0606010905011407080c0a03020a12020105070507061d060429090d0809100618050705 69
    0xc01c0560702411095002074100e85110b0740720b04014260034246144038201d41d01100080e101e48418498400402007506002c001d640b00c241101e400c13550428024000182a00c03507120f0f408001c001c0068a41c030520341340d08001918030711004040b50103071103c0407002034840445010840c00030341459040b080c00038000900e01c4503681c00c17590084a00245c148141e0342081c1004c880d5401079102e2000c03209070742e11095280002e50041000941d0b590a03c0d60740c5040040080a040c1030005950043c009a40c0c4402d600c0c8500020400c41c903a00c210700e0801c84514001c8030102c44992152030f103090100741d070100c0c480349900c1c45003803e200ca00980d500141c3c00d0f160101c1e0301e05c0001d2028407254001c260075400404125640f100a0092006220a003a081c40300490f82600c400c0300243c1c0c001024079a8500e070740c600d070489130840320050804001d00c3d51a0441c0e40450400c011150001c112040d01c148911610304c5104c140400c5001e9860144100240982101d00c0d10645000c00040c8020302400c21 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 284261411 1250 284260161 284260169
    0x201003060b0a030203090a0f0302010212010512100b1315080d0206091b01030b1008040c05040605010512100f1502010605040219030c0203090a1403071508181011030a0b0109 76
    0x740e5424070302c000070120000d400003401c03041c1c540709034001d04011a540420000d15140658009a903840c0856030b06258201d040c1e00480c00b681c00d0401210200d8008100c01d841c8901c200c20225901d940c04001840c41901444500180d51420604001000000e40c44001300d58604084d5110036051600603138541d07100320707840d202d5074010454218849008002500d0710300702c141400264200d52001107224a5443c80000b004964401c0a010610642511200080200b103409010007420403000030a6800360301042000b5014880c0850550740c05031200c0406071983c0805c18018507a1013408150b511074800d03090015502e40500410719003458007c5a400f0300405a810084075030610080703000f032114400341c20440c042400281c42940d079100c10040240031511541c61081301d00f108041c00c2a04640c02507801c0d43d400600c094200d500b0142890380b013a069a0001c0d64061326a40442c20308895034034040b6000c0c134089500030481e01c0c41c400b41d4082c40401d54200014005140151076403040c0e809 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 284262661 1250 284261411 284261429
    0x14150405011707140301261908033403230106120605030706020102070303110a09031716060203090d0e03060c09190f03021c080301091820100306 64
    0x40070b29491031414840310381200b40e034030f404180c02c48000b051440e29002070f0440d0a0800e182c01452000165008252001c0f52209000d000700e83c0034601e14140940c141e44004054082c04400201d80c0d01100540c02c040a41c00c101440d0b6100130b01540100c81003900c2e0040010900e44007600d4508402200b030905202680301611185034207002c0280c5410305000303005016540c944202007042e03141131040000030000d81e000541c980040380b602805692400301d00300700c0c644042c4900700c40c290b40700f4600801c072900900d20500c03000c00b00d865100144201d00c10b11902d000e90b20350500401083da80110322402d030110944a00c05004441120050f50030a04103a040e07000030081400000e41ea0024402040001c2030301c18801c500404c40c01d07c103481a400807000403030f081010000d5007030002040089403100a044201911240c0c3c0e1110a800107004003900140c0d02d19401c0c9810700606110705201e81c02101c40000203030000304100c0000c10314111140101b1140c1c440c11f1101f4001e0003103d0030365010310 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 284263911 1250 284262661 284262677
    0x170c031302060306032505011403160f0927050708040218070207120615080f070e1314010605040b061303060504020126070813050303041104151415040501 68
    0x90200011608094134060741809600f2854100002e288004d50078a41089805803d80740380000241c034104110b00800c1c4215400c00421a00c0050300d5905002c01078030703041080b111074030030b6400c55230542d441d00001c0d00c49080ba01105164039001130310b00000d202140b024006503864400484650005540003508031040c0300c050140340b80001503041d0b000760a841120341c1c165581d00d10342041d02c1040403d480069807100b44002104811140001809006000f031100019140c2d080d0f03950b43d4648a008640c410410101d15000c0140007280c3d80d203600401c4420041200b680341c54000c1c440e905c034480c071449c81c1910044843c240b941c01e0760499800c40707011040d09459505e50b1005003200a204904203c071903c61111005080c100740101c1c586000c0074104240f41201014000c1600500400f00a227102003207000000d00010031a944039a01c0700c10151303240c0801022401800c00401c1401c070a44a0007004183c15801d84009120250100d40402070854804c40c3c550082c806ea0044500140c010 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 284265161 1250 284263911 284263913
    0x305071d06091f03030c020f01030e0604060f110c010b1003180204020304050109080f0a02120403020a0342050a05010308120705070803070f0e03010c020717120703170c0313 76
    0x1200e11180d0203240c910050510304070b14250142030450f542c00480209024248503419818034040d50b601444088c24100501c100c0c1c02d0308141c0d1208020001000b6a84600d0b1a0036141140e4110900b916815900d00351100e0356212660b0117803c03103044a6004107202ca03510000b951103406020000b0202008030205000580c00740006948000d006454564903021100000382c242001050070901946038540c0710002094001d05144000e070141000c560248400e001582c0d40382142d5003101d5020a0f0082c500b409051401c2d144000c4520118100444914070250f000d0794180d002d2088042e504104207913980c000d40401168809e000c09001440248240d03180a543c1c5a2965084185420104d0610500380d481c003550b0392040706c00e10002101e1460511209411400803800540120002d003c80d01d0686802541c8000e240b148805c3c1c40c00010542c1040c80040c2310349254000308001c036650301e52483c14082c0c881c003001c3e070307403c038050384503400003001c800340e88080d2802004d003121008040805 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 284266411 1250 284265161 284265169
    0x40c0e150903070807090603140105070e040e1603061b05160228080304090e0303071d01050906040f140d03050306220e0d03050709060e060c0a0b0c040305071d06 71
    0x11007503203415100c3c0c5080425110130411291004144080c0f000c2400e034250f15043c440004180120700c2d09a0402c0e05002400e81c100494070040380003610002480100d042d83c062910428100b48549082104008814030400d070b042821180f1601c0c80c90f840300e030784041c421a01403081c00801340e294882080b423000140b52542c001c901d1045504c1c40500712401ea0301003c90003d4141d40300d02d10030741c4002420801280c1c1402481c0d4805c000101079421450000c5001d801180d94440304407540040d0a603641d802c7c0c1c0500300380c0e0000795014001070b40712a200d441d134001c3c4103c0b6001d810011880c5282500701d81c078000120302d24040c2d0642d2264110f441c3e0358244160655805c80191010315641d1040007484918450b038201804000d005040c0322241d040050b045480c068103007000c01c5131564040c8000340c3c00421244945109a966070368036020300010506100c000711000744503200350300901248581107800790060320f009030140d8040d15030b03505183d115401301c081d0054a0b040300d4400648a031034 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 284267661 1250 284266411 284266417
    0x909250f0905090708120c070f05010e13020c030c0a0606080c012a02100302030703060905010f060c1e0515060103090c050402130504060f0f0503010c02120a090806070e040c0e15 78
    0x803924220744d01c803616062154200780484541c0440d091000c229851041002c100b0300c002010032a001041540c02c0000091000c1214242039014103040303032206580440c00d03030440700c00a0391101a01d80f1031285291442c2c440d1350b500b9090303c84505160300403600e49030100384215001c07016105c50540c10340c51413110411103801c44414004000e900c1d804070160b108c0150003402c0740015030f00160740e860444806011280f240e0888890986800014445248000c4062094902c142402c4621080300d1403e0b0007000c0d00903854052010300c044030b01c4200000002d203550200d0410a042c01300340c3d2404011800c98030342180250007032840c01c1c2d00b0170080c20542d008044c021320b80300e90004140d031200c0105055030081e03805820400c0805904104c14150b01790100301400f002c400910841c0058039000b50754083e001404400d00e400068502e126601510704900140004c0064407500e01d01240041c248101100c0342c3c9000b00d04041255036140e01c518407841207204014501007030701c0c858076420b01e1590 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 284268911 1250 284267661 284267671
    0x804060b100305070f0f09210c0b0301052d0d050307060614040b1804020108130c08070e09010c02070e0901090515060301140411150403020909250f0905 67
    0x59580304009800c0c1c54a9020a00c2039403240c0b40810705042607a00144541040d91002e41000010f07201141e07019407201144084131201c044034106551156125801103264180042c9059500c07600083c0039540000070794122a000c4520031440038404510110210f2245942000c290041c1082d40d99071030700c002061601130040c01100d003480b0a07a40e0b03030000c881d0700e50811580310040c2d000b407078402d18007402010a11141503c01e100c404035101d600240604c400381000f81800400c1c00086c40c0c0595404140c3d4826400509403611075540d4409207031221014002e841203513001400280c44101c0502601d8403c41059005200041c030b07010f1840c00360100584146490b54a842150001c15001c000d54400032a04400000f01810b100c001c140c216128554400300100c1c80c5010880402c04c46040484403907025154080c86005e0700074503440e01c0c415074000075031041304107040c020300d1980019601e22400c00e900d105c21840702d2044401040c1001813241e4044606440002d00c030700245900829004 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 284270161 1250 284268911 284268923
    0x7030f050f120f0d020c0a03120b060c100203150d06050105180603030a0f110307060501080d0c0b0c0a050d0c03020702040e010b10120204030c030f05060708010e01050d02030a02040f09050c030316030804 89
    0x115046e03e450f805c1481c05c15080d400220384041c140d10480c0c2c584a685890f1200729034003490710758646141c6440324620040f096000d81c0c04000070780300703c5421030040320100d001400d0349100f00692410000915083c000c6134058074141840b000301c4403411b09144d0140d48000c0080d030070185200317400ca409508040c043e500700b2064200034000c41000300090540d080c031411002c5681d604000300e40f803825002041000030080c0d0042c00c1d00200720f0301200f20341c20180649010b40c0d19508a503058945204104111150925003200001030300e505a014280312842101c05000c0e9902100c00c0900b40d07041080000d6011400701610807601d8010300e908140c8c070204080240c140b80c1d50342c917003400001035a44140c44440400080c0000c21030144281a40f20b00242404a4032794108001c824101c40e050144501500c0000c1c1d0a00c02d5641c00c101013010240d004200b8480d003545410350001070003929800301c6140c81824401e010b940740110136180030030003543ca8080d444001d6202203036071f510042c00a50768 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 284271411 1250 284270161 284270167
    0x9090f0803090102070201022512050c060f09040c0306030b07120e01051513020703091419080304180e1504080c0a03030902090702010e0d05130807030f050f120f0d02 73
    0x148042001c0c5200302d10341000180c4820041c00068100442441d00804543c80d0a01d181601d2000d1400c41c800d0b07c0c224000340a6085031032404a140101c00d03400c5940c01080415030b01c42c00d400600003070120100507030b000d101003076280005030140c8100c0e01004101c000e01c28000360807a403083c042c180c0d038100d2003640030a5400500d8406400c482059400c40807403e604040302e0058281070300300f0f2122140090085241c0b035901e031002081c1c4102c500625001070310414811107140e5a00e640e648060480c40c801c9050140c2d01c05240b640d9a00c0381c480e01400b911a00b010300030601c91445020f4010ba22000036113200942c010401c01081801002101c010a0074003805811030020410442068440c0e1000a40c10030706004000003c10010404004c5a042544c034400968001c100880c40c5141401d00341e45404601e4802c01002c54180c100d06181e2040781400018800300b6840b08004a0040701551882c10141c80d0803030311611082c003507481254080150b0520400d005000f08411002e140c00182 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 284272661 1250 284271411 284271413
    0xe030609062e0f060e0a03080708030c0f0d14090a05100506041d0c0a090908190207080a05030910081b0a1707080a0e0616081812030a1104030c09090f 66
    0x49202c010b500b10300f07020300741c05209010180d0003001103070a9140845151820300c1c41c6540e4800c10303103d0080010500c440210200f11581c0c42c081c01c0d01da92900380da80c2c00780c4403400942c04200511a0010000088036000041607080070081441200980c0060103800035107621410b44d0050040a410190446d94032090400741c2d0b0140c04c47c640720303650b800c0b01030819035103050100881b08803242c2002c000c05190503e080c0c0011840b604030362103400d1702440620b18640c0140c0c01d908008981c0d222000034090040004200302000c002001c1d0007204540080449040c0b05044a0380c250885041400440005420000900401c06050011811b180003011840c3d00c41c0c100440d00e4003621440081000c01052280c404024066480d44104000042c8020f1808290f0500d21b01e041510100070301c0485008910310b084c154403903098919241007201d00e40e208900480080b50b00448141c40034a1405032100780c0203902d40b0407030342100e03040122201101d0030b104449004200c2814101d41c52904400004 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 284273911 1250 284272661 284272741
    0x30d110f030106050d11040b042d09060305100c0e12071809020f09040210121803080402090708060120010209190f09060e130201022103070e03060906 66
    0x50701a09150355481d4a81c803118150f6000c1d00c0220403920294a0240300c2823016110010607201100e00c400c1c94842c0800e84844610074004030f00600c200c001405500204088046402030011644140c0c11030b00c3c0d60701092103d00441c1c401c0d14085d8009803d070b07a0558914584031040310909030221095078001c80d81c42d0481100003aa08020407461600d9100300415842c03c0340f41e0704103019040e2081803107031a069000428042841070510248041944040200f03c200e0380503c032003541a0680b147c000c40d1038240035003070f40002c4400b02c0c42600e044000039900d52180070f10a00038207060b1503080007100790010b0b207100c1c503047d40d010044944d801d014042080c3d45045006541017080c1e00240d25190034010b0928901e074039504190821030500038100300d49440566000c0d0b200c048071440c400003500c0d603c0100d061010341c0755295003402064103192521086040191b00614482d00c1e44074100494009240e2943c90480d0404403035040b5000203035004420004141151581100d903202d8082e401c1c43c10 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 284275161 1250 284273911 284273917
    0x806070818150720100f020d18021914040c2c030609010c0c060908040b040308030a060914070c050708070806010e2217041701090203070512030d110f 66
    0xb040c1101050424082001e8000f10050071508021807118040480310500703580d110fa05103480f0384090794540e0b50114000072079060721a241d01c0040180b0826049407070500d4682104801a8800d0907160b130208001890403480720101ea001b41c1040300950090401c000042c01b482900c0c0c81440050725101c10224403220b5441801000c1c2d4030780002c1c9990361018503203400c100600501c80360b0b1624003540041500a4000c0b00381c0b640c003443c0803a80290b14070f4109418081d5601a41c1071140100703010040100c0fa0000c0d504c1400490010001c0075a1003000c2800c1d5041040540500441007000c40d00d014490242c02485030300841c11500740d00d54580d000c0d80340c540e40c0d0780140c11641003400140b1071408842e840d075800c042c3c0785208d01704600e84100c9180100310b00840c01000e4940c150104120480303454190b03030040c040020119048540785103640d019001746d40b401c83c0300c0d0091403008500c518040d10076010300110a4011402c1070840e9490300001d1813044078241d54501c050012801d103403050401 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 284276411 1250 284275161 284275183
    0x40e0c0a05040f230307081905150c0a0e0603040309030b0604060b03090307060b040b030d08090f060414061605160201121d2b120b040903030203011e0806070818 71
    0x1480444c0711521200140c84011004024425000301d0002c104400b000607032400ba0303046108000080e030110f8030b08076250408164a0408000700344040102c68100d040240c40c554540b41c0b40c822aa5690404000f8148003c6034000d0208240a0341400030480c01000c1c01d902800140c0005100c94036690304e20810b40080741c04110642c80051504108000ea016419a801c0c059a0502045a1440c0040d448020f400030510801c55800005078003800d042000d82c0301007401c01e05940d034074203080c2030441c80080500120800d521440c3c003c51904400c020008540072403507903500342450511301a42031040c00348542079040010f14000ba0207040c003180f1903100088020104040083c4c0b0075600141000c0c41c0040b0302c0b1051b501c41d40001c1d120042c90400030341040c401d1400e605140000844800102003c2030660f1304649030143d0351080503010ba004505a91141c249130400b41401034a4100c42d074014043d03880c0325001400400e801c2d5001c1c28905812500b00200501031100540c0550b01d80007500034 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 284277661 1250 284276411 284276429
    0xd0f0507020414150a050901090c09090911010305010e1003081305031b090c0a050a08130516030311010b0307140301180614070503063f010e06010b040e0c0a05040f 72
    0x1d2200301c00c0c0e07480e080d8505180a80b031000d5006e2801000603018507051003848006601c0300202c07034115210b80680c0000d8020b808081103012000e041c03c28040010070079460202c0d161000104944010fa10094070901c40c65082022140c2190351381039854000081e51318582c1c08050340401d43da2390910048a0f9041c850812500d034000742000c01c05d04800c09031051002c144108030200d90103a0080844070f1801d25070034440c64540f50981003200180c40303e84050071502410704944c50020b030140300e481c2224041d60b82c40103010b80c0c8021403402c803808001490744c168807089013080400818103208844000003000091600d0314211102c0c04c43d580084204c1d0403aa8407144010403441449081e9008040e5185c01821031811070003290000180b241c07008041120089030300940c0c032070318070102181d41d9101e0003030f81882a600e1a040c0a820f00c0702d103a50b000d0107074600220702190604180d134115000030507402c005448030a0064042e5000c0c04c951420840b04000c040364104a4001035001440241 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 284278911 1250 284277661 284277701
    0x40506100e15040b0c190302031b0a080c0f070806070c0204150f0609031403040302180415022a0d080c0a050409060b0403120816140d0608010905070603020406020d0f05070204 77
    0x106006040000310312103040e640440c2c6c004074000c00d43c00015100d01d0346860f220640400305190300c483c508414010000e20007400009d0300a214003004c140060f60f03083c2c52084032242a152580b4507107038401266080300190640c8076840142c036041d0000b03006800c2104108500ca9102c500d0210f5020141d0031800202e81140c200b001006020540c1c01c0a803042a00a075060509560000e0032000403001060005140100030900b8030074a804215250401349504540e03816201c0c008a00e100454940c8541500072089540c00503c4041484062441190b40c4d541255035a4100040281c004201c60300404c001840045900c090b035204d12006040c4284d0180e440d03501e1868004c0c000e4040904010402c0319140601c52440908900c6a4650600c1c2c1844402d40381a0341c4103a015010f9a0000c1c00c400f41031420024030b015045d0300200c540c5004c0e0b41079841003601c80000381e00343c2c440c0d803041e400140e00c46a0b88034441442580e01041801c55460841e2500d0001c1e0006400e41d40358428042c4010402 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 284280161 1250 284278911 284278927
    0x90f051608060708070507030201180b1012080702060c070806070309060b010509010f0509030c1302130506072112020307030506030f0f0c040515030d0e040b040506100e15040b 77
    0x4044000018807100300242a2032400d84802010400c002e0840c03420b1010100342242094001e40000e944481040d8800d469000f090501ca04240e8003036640c9601c01c5051400070541e440400d02c545401600700d1003581c5003101943c00d00c21640e10040000000340101c40021031000010f1001c180580705540c0c0c0400c01d6545030038410f080380c00040d465414007508100a54840e6041403803610443c002c0d05281e5203403440391000c01e08007425230210329031100560f031500040d0740e065805015520b02043c80e0066054441050201510918030007400307a0f103030071500c094102c501c42d10b20b0350000a540f80c0000880c15402c0070406036042a104900404d40300c00401006050412800d0b1000d07540300002c040403a100f0300c1c0c06881d8089500024026600e9000003800082105031034405a000030301110500c8011510051282580032600d07031090b41800207403020361905000f028040c0308001c02e11070070500b04e0402074480d040200300c0240c001d00003d40a404003840840900024003c502445a4031824 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 284281411 1250 284280161 284280193
    0x31e071502071109010e0412050c030a1e0201060b0d020306030a0f05010b01030b01090b040e150d03090303080f06180711070f061101020408150907080601060c1a0601140d090f05 78
    0x107180410f43c007130026040100440002c801c20903802c9a000700c5c0c810861007000c6800c9030a0703c40c03860744040707510000030640c05550384881014000b10910803001c94403000810120b080e250303184210a0610801c3c003104000f203186600454000300300404550103580c1a40d140751082148110580c2e103a59920484a6103503058040c81c4034800b02480c010a500e42400302040c00c0740260700940440c0010280000e48441e00507016000e501c00007041c024450031140740c0185105550f0200300c0000b0a148042072225458180e640e0040400418146440011392100f281c0e03500014040020001d0300d000703101b100c0005000420190501c0c8202c02c448504000c00075002042d07040303003682140c2c81004100400480802c15036096140750b22034449646500010614184054102e2801c60041000005000b40c01c01044a030f9203100d907030601850314a214181305001c0c0c0803180a030210300c0d0010b203882402800e000030706208000c9000042e481c14a03481d1445000c850280803112980805680d10341a58 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 284282661 1250 284281411 284281433
    0xb0c1f06051008010e0c0a0e03070b030712020405030712050a0c0305010507090b0702060d09020a0b27010e03070501080c0c0627030a0f050a0302070b0906150111031e07150207 77
    0xc0c1600b0f0050282d40b400080344010070f4001d100742c1048001095200c1c0711441403d0407114100001c045603c80c540703502030400c0704e52090b10f02c0e101091041c980030f10001c2845c000d440072104002c0180c5041c515004107002c114451400c100d03003a0186040c03c0f000240c0da00e8542c2c1c0614041e000001d001c0c0380116000d843c00003940c1000407010400c1c802000107a460208403810f0b6486071101184a915510101d8a0746589800441101d140400c807000001c0200540010768000b210035211003021507401034070300449030092241c04d03800c42001407105500a00804c2d41042c100424545801d0305003160340e041240564202e02d18107408141000480e41e4a003800c8002ca6045025602e01340d02d003d40904115481340a01c02403000c00b1a0014040b806907055440b41078010841c246a4540101103e031955002c440c00020b003c05030205500c5544200b07051510702c05032034000c2d80342000100b01403060b0b00030704510244880c0100b02d110300060f1160b00d0708401781508000980c580f45585850f0500803 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 284283911 1250 284282661 284282689
    0x90305010c0c0c050f041d010917040b03072f010e010605150304030309030509040c030b030d020106062705150d0f0c080c1b061305060109060f0b0c1f0605 68
    0x240d000510b1020501c0b8408030b40846900b251010340030854040460003408044045101560400c010700340c2c00801900200305d2507102d144007101c2041d071803228942c180142e00070b46c40041c0c824000240000c0c0212a10580200c00e000c40c108140070542b48580c5004030440c080c0b40036511040340d0341c1c102809008040107804120f401110100701c415090003540030050000d010035440d0150340c0141802442200e41e4500040c10600245100c40805005002000840c1740a441520692040180706218090541c0d103d9a1500c41500e511201e840d0302a046441803004161340000001d11f83d518942c2080c0d25145040d64151201140050101242e0300110380803203450505240760046940060141d520826110050f91a0401c81980c0f95416000201d03c81c0e0074454002401130015801200303690903807094007240c400b6070b00d0b40f2030700f07054a80500c50f0010403410003000344807800303030000505501001c0c5011549040100003868034810a207010b4092115a20803062100781844240b1602c40 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 284285161 1250 284283911 284283917
    0x30c2701050a1409041104080c010201090305030601030e0f030a02150c0712080c070b0405101a090f13150b010f020a030f030b0627040e0d052205030a03090305010c 72
    0x14049000040c00c2486207044280810100d0300c84004040d02e02810343e044084003030310030005803001c95841b80c655030050041032054814004112100c0d03105000e81340c95650b165503010305548a07800150f01900d600d82c66041140101d10f00183c5040080010b801c0320700700f0307a008165500c0078000d0444d14a10180000300361541c10880e10700818a440c002d07030702060803403400001c142d46040402a5038010041d000700343c616a0000e0100b0710000107005910718119400030490841c0310610341c00d520464064268001c50341400244a5594000c4041d5010320700e420090b00807005039880300081520382c4801415103558820031441d950303000d0080e814520031030008100f1074005440c05000c161004000c0010103894003290021515244245c0c0c41d10303100740030700c2d10424525018070401c51504040c00790040c1d1500030000308404002481d0303007460742c0c40c1c0c491078038000b01c0c10301d081c0360320f0314200c007882c48200000b0001840c0c3c0c80c10850140664025521100c0103825807401c80e0945010742205010 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 284286411 1250 284285161 284285227
    0x510050f150a080628030b10051f0e09040515130506130212240a050c030f100e04080316030c050f0c010f0c200a150203040203010908030c 61
    0x11040c40070007162441800760030800ba1540d58100001d001840c04400001e03401102c103040798051440001c0d041c1580e00c202d2801100b6642d0403e051a982c0c0203116007580400304804c0c0640e00b010366081c024044c010752070952528992400030600c4158180c804581c1940f003840e100ca0b003030881920035908440e150f86e407003140c035805071165a59520090102c0c404e10040d558080110b43c1c40e030354086e0590070607a00351f40c0c24025082c04040c64072a1049d050204820b81e10004c3c80c06402d611803148a46020900c0701d0450310784401070480800010000e822403040070710041501010500c40301c0c820b034458007a8540d03d14014011200403200303182c8000c1410f04062143d0030854020080c1c9046030603200645494504441d5030074090b044607000010f541d0f18040b000d0050685c403068041240fa200c00c0c445024681c2c5211460340c0342802040a4154140e0070003090400d05d640d001540c01074002400801c100d0341c1525040c041d0790040e02c10450024000459a07000d155200903191840005200411 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 284287661 1250 284286411 284286439
    0x3100305010f0912110c090108010606021c090b03071407151a0a06050a0c1205070c0b0304050a0201050f28030e0111030a09080418020a03061509090c120510050f 71
    0x124a2043c030340c1c400e090100815190403c0c040401c1246c0c89400000c10b040b03210350355004000c0c001c014502441e40180a088041c965000c440980406452019601d07662281c0c58480500710541020b40f040b400c02a6204104081d99895800390600b18000c240c0115464100304056040342e0320060900c0c041d01195207854416650001408101c40840c24000c1c2e072000c1d801d030f0440e0b0f01544000024100d4a191086120040e0322201505c000b52055410703000607620307424054468001103d0041c001d900802c1094010f5104a001e0048070201c40d0382c441c20001070b00154091003040d0120000440084450400e000c0d600d8029102207115000080104082c0c1039441c2049110040c5094242900c4000c0c0cc8104400c0b0011035000703003409415560b00b074107008156800303507105420000000b0301341100032850000554140c4500402074844000c4031f8a40086000036000c0c02e02420300b4004060326018442c0310901031184200641441485518100f40800401c0000d0a070514001d003029200e0072 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 284288911 1250 284287661 284287673
    0x40b0d0203060703050c1c14070203040803160f0503120a051b04030b100503060705120f0603060402010e031903030b12010606211b02062406040303050f0405040203100305010f09 78
    0x950003c00e1072a0208045d51003006510b0b080c4546d0146200300f602211500840042c6540b014000b0b4003040085805030321801400c07030340e80c010347c040c8040980003005810324035051000b060510621a02c1b0024021407a6155542150001418540d24002010030414511510f00c245544175103d88807100c65460a41d82140241c001c9010007014120b24101185d038501e102d002c01d40040100904680f00c0e4078003c00001c03d80c1d00205016080003a8a2010a018031503818403140709007000b07002060036503104e07001150b038000c40f03000d500d07010f000f280605803106600d000409144d40c002c0d1004280001c845081c00a84084a40c4e5600c0c0b69160980510186a100c0c682010724602d51580c0880e00b1b41aa408000038400c40012080d1b0070281617100015079008101c982c415603a5010201340e080403903640c1c04101d0f451516a56000c1400c1200f8800030b40a40e014003225180c540300d0a06250b00c0780b01150807a401954101002a00780100304200142401020010003c44100303000c40509650384c4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 284290161 1250 284288911 284288923
    0x9010614131103010f0608150f010806120717120f0a120e0a1109090a0b01060c031205090a021309030504050402030a1e02130f0810111308030405040b0d0203 69
    0x2092085101c1814110046400e4100540040c803825003181c1d81c0d41d588800011040f1399214440104e0012000119884418440c0d00403405001e400030b9404020180111900710005240980c0140b4272052100d401c0810080382001c0d21010305400d44101080d1003140c03801d0140cc3c0ba041700450200300f050b8010740448143d940000e420304101d014040003501002c0946440c0210748420b1051908000a02082600864121740c0039503008510352500e0a80640f6108480c2000c1d0011558600401c1414450414002c0c901d000e071501c43e0015554010650a4030001d54601d01268003c40e00081503203010351714210b01c41070528040102c002c6564003d00f46000b20f103c0c3d2440380394040700280295046400000009044540d041c14800f03c080780d42c8000c0d0820f07a01140000c04031f000104001040300d601c0401d035600c02c402040d4002c074030b0864401508030b0702c88080005001b0b1140b2101a00300c0c00e0158007a08a40780074586440c14001800204c80c10480b44901c01c2785200c00c0d840140e1404a24 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 284291411 1250 284290161 284290199
    0x71205070909080f0f04050f060c07030308060a0e09030310150804060c11150907120809060a0201110409050702060f0115030b0f0d0803061503240f0d1208090106 71
    0x808100e16a041c207280b40b1601511074130f6036505100203080d0079404e4000c1d0041050380d030100c0ba009a00c0c40e444081c840c0a000c1d61489500c5944020400e10103c1d02031041c01e540520002e00c410340d050746440d002a85c1c02800d94410a49030710100c1804280d41003102ca010103041404d62003520306101032002024100054400342c00181c1e1100c040d011070b403041070a0390042c131481d411144080384040b841e024030841203c811025014030000070448411410a448002e500680a107090040b20300400215902602840003599640c04c08041d50560340d10142004200c0000002030300c0c0781644001e070400b480200b00d0380d400025500148000c80e00480000d800c521907142c00100007660f02c1c0411210715502811940c0708c0541071550040000d00801035208004c15103e80f540d01040e0bd440030f180340410303994443e00f8000c0b0810b02040390744440e401d803081c1000910b801502030030700c2c0c0442d80526400e04283c60303a0120303241d0740c44015000547c00d50009118070013040070710319040d00344d0840c1030040c038 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 284292661 1250 284291411 284291429
    0x40302130b031f110f0d0b0909030901080604020408250603050c0d09050c06040801020a0909140117070306020a111605031c0203040f080c01080a05160c06090c090c0207120507 77
    0x701003c8034610f107900000b04e08202030401039a80c04103c5010310300303801140c0c286000c141070605d007112130306144100a00903d1070800560400711060010b45c0c01240c001c3c2048c0c8c0241d424440055504000c1100d00076031003c04503409415445441c4a210020307170f942112007803505100504c42e8150098046842200b40034a0000b940c004900d400b50416008a00c5654407940104020070b5689040d402450382c101c650b00c940442c0e81d03546c2c291205862501c4003980004110000400c844100c54240700f06140c004019604681c1e12903862104170b80000c106034001846042005010f04000c10440854108520400030b419103490f0000381d03100e030440080c2030102c81d503002c80031483e030080042d0b030040c2c8000f4252440464a03840425550390303100d015030b4002500280030a216003a188141c03406002d901d88030481c400000340c000d6801d0311a40308101e500c0d42c0d40d140840041207501c4100700240070f010f00c0c045104581e140000749044101c0e002400c001c0b610098031800642c00113044821200769030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 284293911 1250 284292661 284292703
    0x6271204030215090d030509030f0f0709020a0c0b0c071101032c070e040b04060b10230909090618011a12070e1602060c0c03120a150902040302130b03 66
    0x10052074070b030081a80d155004000017003240105500000030f0855010b094080340c000043c0c4e0341c0215580c0e8042c00718806035400446040c0600c000c0b03a0018000d6240c43e0030114001401c0da80c03888a80c480440341e45600481c013084000030048405220100540e00346401c2c001e4185001162408410403100b40c5082011070f0346841e00f41205000800051002c81a03511040c40c6c54140340c0340040049a080340d00d20320700b09115010349400315032320242820954a5103059007040001000c207140071218903400388818003018200c0e81d12041c9651040100501030007803402c00c0c0b00724040e114440140704600380d05100d9000780c800710070811411750002c00c0f1807400d40c2c4c800c000c2100c0d003009000e4004418184100040100031220f10030420744c103071030300d82c211080741d0707521320007117155010300400c90300150410000003503060510320246401c110b05038000a10b828040340341d6012802c095200c0f05546401180400c20341ca030000c00c8040488410400b07201851030700300026141d2030300741e0001d60000328103 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 284295161 1250 284293911 284293939
    0x21009050f0a14060601170c030a15060f09290913151703030402090703020901030e071d010506070f0b09100c03062103050307051b062712040302 64
    0x2041102040c0c1d20101c140d850554850900180c800d6207a20026958461580412a01c3d4458102103542501241c0d00300c076503450b502000d2680da440509000b0400d030701d850030401200c5150441c80002c01c0144c4585081c010000d0380504200b2050340034481500a2aa4112500c40f54002a050310b02c508080315070358400c10350000744204009205a94060718040300900c90a40c1e0f02400c40c1a41c1031050380d180383d2680c60300225540e00c82124000c1d0001c6040d00031620311401ba070043d00920350141000b1600d012000d28091500c2d600398070543c1082030207051262041c100e603800502620040e500d840c42c100300303501e842480c0c3c25500002401480001c0008184803018000a81003e9080c4001d003c072a50309003008000e00010b003d04034500da480b10400714400400b079a56400d042e03250700e4080c00c50713440722000c0e225a007066403052140022400814902441448094072408680b200c640c07042c0069082c20b203c010102c550178446511501040303940244040c1a07408030380d4102c84034248810300d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 284296411 1250 284295161 284295163
    0x60e01210818030f0106150309030e1f0e010203041d0403021006030803041103030c070510090314060a0c09060801090b0402120901052d010b09040e070803040f050402030702100905 79
    0x31800025048410228aa112018003200d400c0481d40d002c4040707648020540401c1801c8401c41d00c01c560350b80f500020708005950203500a015002d01034141000c281c0d05060208804c005942d803101e441c010041c0c003010034079402c0503060400c00f0081c8000c604207801e2001029400d1070601c010717000900c0350f10004003050310030003140f02080d0100b071051040b542c0c3e81c0b500d40320503002610700701e4504c2524141c40a003800c0c00000d841c0104c00e640300402d16546080140a5000c0410b807080c3c00700250904003102213a010b05641904a4260004109519004210a0864075003030320102c20807640305420018560300640a0f415154078440008400000c0000a002072264103006080d00e0001004c100e150394040d4030103441100d0300050764003e4002e003014174000c0004c5c848440c100e40b1800c00180202410100604480d2402810010341828860b400d1841d20160344e0000080782d1000a05108441d80081e000009183c140d41c151b0950901c03042c06521560b00d01c4400300c0c21591161800b05000e0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 284297661 1250 284296411 284296469
    0xa050a0c120207141b03190b060d02030c040e0c0f0a0f031101050d0c0f0215010506070305031b0724060e16030b040501060f1704030c0f03030e06070c0203060a060e01 73
    0x4c0c0008840c000c4110b03600040420300e6040c2103034400c4c050003016080e241000c1200f101c02c1c5074000c010160641d149000c00600d6200030b0300598051140c50304d003201507241c42c0b05221022003950b00408600305014100030908a0b5480040d0251440403420072407484d200c40a042070b00d03840f00c0721a9000c128500101c0312070007106082c1000c24100316868020035003100980c0790f40150380e401e031042c240160070482049071080c401c054112404006410104c2c0c8140041c581001c4480c080480036803000c1d0311220250011035080d1a021041c03086413410a40b0401c2400e001c00e81e4200c20301c80e59140429038000f80d07200402c00444078004104050741c3d00d200c1d61103074907070b41c400400c200b0180d41c40300c0c8014003c0400d00c400c840819030707405007414408006e551040c462035055680c0d65544803560b42e04103042d5240e4000b142496250795041130000b1060240511030070082c2d469070b0b0707501c500d4010540741c000040c00103541d4600c0c0c00c0040c0b040401c2226120b049d5180301080d01c9241c01c90891f075030130b105 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 284298911 1250 284297661 284297693
    0x30b09060d26090405060d0b1614030c0d0b0102060108100908090d1101080a05040210110f0607030f060504060503100b011e0f030b0613030305300108071a030109180501020a03050a050a0c120207 85
    0x34ae400405c00c440c01c036031341c0d0142030911000d05040000c80184001642d0702d8200303018070041c03980420740c10340f1404a283c000240880c440c1c9565810b10315440c000c14001c0301c030400100e5001c4012004101030707503448943d040d4081d089400c01d0007942819000b05200c0007a43c030400e0104030039015400803944080150802101130202251498500150010010800b08c0d00760b0010754103003540052135282901801c03003581d400801418081110781c03000c8009140621525052040d010380b40350004200194401003000c840e101c0705406498181f004040355400441a403050708188803040960b00348410000589505080465403071401e100540c1751250f0700c10102c08a5400c0f00084207030608a0350902e812100300b4402c65000540710030661030440d401110786c0104280500042000031540e41181c010b00403e90300d00712440c0440d44034242664050140742e808603481d8030a00a045186204da44c3d44800100f004206400c0760240c010045d0020541103210141c0100d004001d008170a41000c0d808 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 284300161 1250 284298911 284298947
    0x1d040204060315050a0b0d051c0306030f08030a0c080c2703070303090e060409080f2a031201050f0d030c0203010b03010c0c03030606030b09060d26090405060d0b16 72
    0xc0b8a030f0803108019040c120b80040b515810078462164038200071b141e03142c01329840b0700508036040010400c081d260740924410800c2585806000010500300000c1100150082c010b969a92400e44600c100b035491100300e08040151000400050f0141c860561f940142134283c083c091203012640c03081d011241c0f5079455494081c0f0400001015000425a8111055802e0b01d00160741e0380c4d400c000480c0c10b01d80c0050100001006803000444200703008029101140051002d003014104045840c2c80c070601d142e50343c81d88001440103640028050031070040100b10b500c0501c07071851802041d510300740e0910080c240070a1075500c0045660039007004450000c0030f8000c016008d04850014046414120150003081c601312011a18600c24020b0044000d409081e078201078075901c0074400c1000c41e480c0140c408043c400f40480e00c0c01c040c09411203070301991240d42d0392600c0390001004111030003e8181407280783d0000b020400510070184082d4031038018444401c80c8800c900091710f1319404110a4110 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 284301411 1250 284300161 284300183
    0x506180a1e240e01051f0302091909240902060a050f12070e100c0f0228091508060105091f08060403031b0804020a2306030c221d0402040603 62
    0x101d1100d9038000c0d00c106080100174030598441040e6451410190304c4916440000500244094103000c0348594115a0841007001c0c02941501074a08450140c03800702c070b81e0f04030942001203c240c4080504603080c0480410000301e0b000350300244940c4250710180d81403100119140041140721400c2d42e20580603004442c0c1c152070240350003082214100741c4c05100313159016285240c0b5101d0440320300e00ca0341c04882c1079401074454081281105a9220405600000000c00b140020900496070014071080c540483d100203400088101c8a602d40c028406541c4244010840e035a5a1941b0381d80101000720ba800c0d808500d242116040704c800c0e082154a07100340010321040651540c8001d010803000d521583d043d10b12004100c0359071030107680195125900220030721119118044001080c401d00170103460808091000c2501a002200e0414a00fa000304131004180440b540140d010025200c203030720205d0070807019480100c01c5003e0700f1451085a00010210348490740300202454001c40d207074407 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 284302661 1250 284301411 284301473
    0x170a0b030f0f0d08010f03020d2409030207060201020c0709150509040506190216120201060522050702030f0a0f090902031f140112020313020d0506180a1e 68
    0x3503100c40030321400754035200f02120881078501c108001c5069440e5503910b00b1903e0301c1c0d030302002400b070028601aa41040c034078400388051484141c0c4a42d582403403880100300c81700305040180c10401d05900000a59004015000d0402c8021451130140c649075280004c04889550710b684400c8030790380256070004415030038007041c482c0003d10548a42403841c102441c481d9054080c2040c3c1c0036003024140b180c1f1001c940300c1c0004404200d0312034100d24910000400780e5503500041c15021621200b41d60039803840c28071505180580c050307144d00c070700d00b0b00003140b03030080b014002c1041e80b14040e400c0317041100618990510a10032105480105840c7d1025922424568044042d50b4914143c01c4003a6590090024080c0a042520300340e1000c140c54144951111180c102d0180d80b000740b4a0300880d11404103400103940740703030395188854000c038000c0c9454580401342040321260011002e8980c0d001c114150001103a418003a580c820100d8011a5031510030300d004064400f80c49210080c082031504461 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 284303911 1250 284302661 284302663
    0x307060207090c0c02060a0e12100b041415101403010609150e0102070b0d020403120507030f090503030306042309011509050103080d0903020a17030f06010f170a0b030f 74
    0x9400d4904101c030802605000c40c00c141d454003032940001b500001c00b8000c038000240910703948074448034041d20302c00920340340151280c20080c0b14004003429540e1500303c03400a003003501c603005850700601070041c5d0b80d09240160069120110401030300c201c400c284042e10080c881d00a083c0c40101c0c080c240c03512561988000342c041c0c44103001e82d00c034001c3d2602080f01030b00d100c2c6864003140e01060700505400340c03c10301d8884050341329440304050031b502040000006000d210740c07190419040d50b101a219201450700401903a80d0482140401c820200288660395001c001c403600003400b00c0d4005205039200303402e050800c114803403610035217940f102040344040c0c06410103941404500c101141268807035440400701c5100b804040c2894000303101c00302c5183e080d0b07885808154041e00407952641101d640e9001d520720082419403582d9004010f01c0818104030400c1f60300b10009003041e180c558265080240401d000c510000036640154000c81c02e01901640100002c100c080c1c2034a041e5910300c80b00b1 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 284305161 1250 284303911 284303923
    0x80f0705070e3c0604090c08030706051006020303010510110115091b020705130603080f070209010f180c0932030c030a0308060a050a18052d0c0903070602 68
    0xf03400f50b900c4403018403052409840040041c9a90010160007002c1c64040400400500c40b507000395880344036801140500e069032006088c007a00840e03591141e0300e000d10075030720083c00c0110f0409150006100554021013500c0c15140c1c25101c22441e14a1404125008a49108405555481e28a8802111181080369030540301c0d1050140004441c0c840400b01041d820070716840140c203e07013003d028928203c0031403801c659070b00d01c002c1103807a240d880718102070740004c5200500b1200095041d0841c1007000c0e03024014064201c0c140081840c2503007000c0c0481d80d04a41c921001d80d604509445540110602e8014180081191060b01c1c1142c1071108006508500070031240c500d203555041c50719000811100846000d0040c10542ca82039501351030500c400307003805a10140710500400c0c20f40ba00401a002400c40b4000d01c0541498415550708481c0040d0020101c54100d96041c0c3d0603e543c145000445c44404000c0c00943d622143d101090f0300450800700d81c540644140011400d03800244 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 284306411 1250 284305161 284305171
    0xb150f10030c0f110d180e090f010f060f1205100203070309020a050319080d181109070e0f100201060812030711030702180612011d01061d04080f0705070e 68
    0x80c000301c0f140030f00c003e6a1002d00c410007003810341d2144c02d207013100e5882115540218202420044403642e1110451030f81060115030b001c409521501591455103024014603400350741032081041080d0070042d802400d08150302503c4d03183c0d20001925803c1120030401002c8440c40304000319100c3c14001c1000b000f8084000090b0302c00c686014010805190108101115441c5401c0c2c0c082540e5440d99104207582100b141c0c0c2c03c2056a606200380d08600786c54030038450342d00c80d83c801c0003201140410010110b001515404c02c05c60862411050f0b901ea540303182900b401c0c1158039590070854090204e000d000d0079040f4000f24010141e62003070010a4202070350003040603844500c075151a030815240e681c080c031600694002050b400014041d400d401c012038000350064444c0f50569081c418260a440e4900300d80100c10f00c411582d030103020400e208807006444501da5141c42c0010203056035500003005000031305210300010700f101c0d0542400049031103080e444425214004c0d50303490300803601c80007110 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 284307661 1250 284306411 284306417
    0xb01180305102306040c090305010608031b150114310c1b0b0a0e06040f05100213052701150e040908030f070905030f010519090b150f10030c 62
    0x64103031100800000103c4542c222522107000075a01c3d00100710103001c190b400b00060014100003c804540c00b0f01603040039001d10300003541d564078a00c045041200d580700b9a103200b900800616202480b100d51154111940410304c3c00d42c041c03010300010001105190440c00e0f00a15242400700442e008915510210710500100f0000c0302c00641910f04200c0121510348808282486600103801007007402d42005020000046400c24003170031900c0c21000761020346c0e1300c400800f802420490100b0108a002c6074140e411750034a02d2031050444121014050140315501800015018281801c0710301d0324000d47c4803418106503174811000c2c0c5000701c20240b010000348140f8060780075040c00e0142c265103980c4049240d03d90f665041001358000c1001d441e80e01082004640007405030307070410402400790264400015203080400700584400d110004c1068214140074109003c04d80c035030303621540000011010f0301942020000540c80f1004030008541c800c58900c007003400301758541d04c66003900480b52 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 284308911 1250 284307661 284307671
    0xc0f08071a0301120303090516030305090906030d0c0f050115180c090308030604020913050709063513020a0f08060a090b01050f03011401030605091c0905040b0118030510 75
    0x700d00c100e00780c0710900481c0c074155102000ca40001b0b1081e40034003007031170198084d940003955414440101c48000c0d481500010070100310014245451b41d44250004001c0300149040c07900b840c405400340311101005070585901480100c1404802e420480751014a10340261100c1c0c1c42c0e803066000040622140140d40746001c010542c034500405000c0240c176007007402203007950380328420040a94850525190001e452604186a580060103a640219210b495010503d0304040004000d51404140707860390509031700c0800c001e4440800b12034210b100c0300b1841c00640d521850f5034003018440810080d040b00d1044000a004400c119110302611420700590f9410f40340c2c201001c041d13402c010006084a040003004008070b00d482d941220090002400101c0c407c012545241a049400d0340148d070011f40344d81c1000382c0c129040c00045030203d1003440385040100c00c480014500318145c0100750040b42d40d01c104035240c0c0c1c02110707101c2040d151516036200751512440c145464071000d0700c150202c2d0b4148 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 284310161 1250 284308911 284308949
    0x1006080d0809010203060901140f18090f01050606030a090f0510020301030c0605090f0103020901090b130503071a16020d0f1202010b0418060209010c020303030403030501150c02011b0c0f0807 84
    0x600031a0f00031000101004c1041c1d003014601c0c0f151100440c60b152b40701b039505c0c0c0c1215a1341c44114201070341010b4a2030041c01451300b02001420200a00c0035205140d240c48100442a625441600d42100208900054500641c6481300f0001103442010309948210410248003040d65001035041c0d81c456030b0008845540c42d00259080c0c011401d0051744181410f0215a6030751081d070181007142014505030b0003803540d41074040d205602110036844d242d40e41000c20f2001d0300341005680e00074804e109030041505d0094807070114a0080604420440116040050640da90300142c014929009410f245041f00d080c41c144a5007441c1c8520f04003d2350070400d501c41c1c20701e070900c100441d0081c09070107070001c1241d5a542c0e0000394050300c4260f041c0041d041c2a5005a28200080c500c00ca01c20344002a0f154140303202110201030000c100b00420207900c0c45140144d90100c0d440c2002000e42030010711220712882c3c41940d2045c07a030005500c0310350b803140006002c58001400e0080340c0079040c014000202e0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 284311411 1250 284310161 284310163
    0x10e0c090103050a02100e060f071703070c060f1415090711070605090a090c02030c010b040618020315060a0906121407080c0f030705030a0f0902030d0309051006080d0809 75
    0x2d10001d016904500d543e50090300740428101c5040a25203400303142108808000b500d00d40015400d00b108038400b0801c1c200f0081d82059181c0d650b2150803086045141010000305500c2d550b40700180907684032034464082c1d803082e0304041d11142c40c10103e29458940314400c005c0400d400000c42d4401e00b2079001080c1154041e4034500900c03808407015107416400c100c801c1c0d0b8142e010101c8280c211050301400108045280300700d6445004d01e5000d95620b91420200302c2c02c1d141c640c0d8640d44140d18018041002c154242d40007040d40b81201d1000d42c480d44c8507180c0403400d2010040164004500040351403515910004280554003107840721a43d0842e4540b1030000c503101c00704142003041c1c01101103040a801490005d46c0714015a0b41149851400d07982c0880d50342041d03401ca8081140402480034120013402410341403444200700300513565003500001d5031184090080000d066072070040c102030100512504072500010001031010650b99151195501c1c04142503100140d40340c000b04d2425030f8 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 284312661 1250 284311411 284311429
    0x11203051629040203030901030c09050d06060305070e06100f0c0605010e092b0c0f080c0106151107060518030601030b09010507050c0a030e042304020f04180b0a0207050f010e0c 78
    0x1070045c00840c1460303004d80054000f00030441c0d03540b0611004a500056030354402c503240071154419000821030070f04e14a019484d1409940029200c1c0c007203042048000d4494207142c0c070090740b880c94a0340440544060a44c0c25110002000e49814100400410507501c3d11261030300810302c03041100d80b0401190403288681881c1d146070748243c428690407a1300c0500c190580049a130041c9a10310705900d940c1e0700c1c0c01180d404501c05145036512080200f01c420229a003100c0702410a081c1200c12900c2c100899032944518025101444000304030880301041c2c0110080c4210009030840d806540c4a0a110304088012a042e003000e608260000c0d0508d84160103031102d401481d8000c8c00d8440c1196003c0d00c640014850246e0000d0f91244200180d07502c85101441805014446010500302401446668015641e01901031414003180c0080c401000313001300789454111100914940714032500344064806c00502401c01d01c43c01580386104e213410b6214030041e00e0004103e9a00e22300e03030014450507079 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 284313911 1250 284312661 284312663
    0xa03050d0b06090612010302090c0403080d0c05130801020d0507051306111914060108120d15080d020d0e03070b03040f020f1009030201020f1501120305162904 70
    0x1650902a00c5040d40541e0012504020010305460408016101140c51900070510200d10058200010802e608040c00a181c0203a4030ba01124602400d5499030142032241c0300040340c07a00e6580e2000410b440c440d4054503282e51411186044142e07440c002117010790000c0314070721031842c03400380851189402001281c075600588080321381c3e00e138600001540c02440c4401c210b0941d002c0d0035064682031440c0d040b413105440c4941c074603540f60030403035402e1443c00b50160003510003540005240c0e80c1380303001c010545d00801e003075000115003203144154541505000340d001c09040c0c0f0a407039040d8015034000c00ca85003440c100c0c0e5258011140c0303010400d40e462190380304104800d04100042004191151354400c00306002030702c8420348038940720110382030700e064412000004401c60414401c6690604c00d0078070030701c0382070001d1441c9541c045020114810621488142d00352008451080502a1080c0c41c0c481c80d01c0c140300801c40d180f43c2016108100051100000122102000e040c04240125110b02071 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 284315161 1250 284313911 284313917
    0xb0307120206030907030f0818040c021e10090b06090c121504090f0b090d090e01062015220308150609030a0f0309080604080306100311030403020a0b06030a03 70
    0x55207602071101c0340d400030f000500c00340110500400031038041b401c48520140314039030079a07444007170f115001200b21007064040d101d1410f207045621626400546182d11103207130342a003182114403030007051500e00e13207501302420303981428101c2c400e1029043c01144581c905540d4054250b90300c961545561160031010481620204041a1401a07800e0403520064000e000014580c100340c03030380d0300208107052045a4110b01a0b08202180030180300c0c0760f05010203418442c140c2c504280d07410941500500585d010440241c0000094600502c0300c006c80b03480d5001501e904840e0480f5002109a044034655004800c0740a0340d0300c44080d1041620a0a8055807407202c56294039a14245d0013040c03560196105105001c0c008003950240035220480f44160740100c81040341740f40c090000c4030150702101440d00400100000728503204100c90703210504032640d01f44004141819001442000480c2d04203a01c00b20401080540009101060340c2c01a0f000054039a14501055903c0070f44080003400 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 284316411 1250 284315161 284315189
    0x80f010b0313060216020a0501230906130906050925201009111c080a200d03050a02030108070504020714011119020c060a080a0605120304090b0307 65
    0x29061104041c507002802c000c4410124209611020160b80004400e010410303082c552a0045150143c0c0c40001080d0030709200c100300e090050b4948040c0b04c444600d42e8881c000050782d0030103940d003504850822520f400701a40c680e8549022800030049405180c0c0900c01c04800f02d10710002d039802581580c080b81c0d920211110024404541101d400c020410704d00c003d42c610802194030034445511401250340380022881c07428103040d12140d9820009a0298641001307084040d4a0440400d031003a400c0381c8001c2d41c41e001088200c40f00c5aa001003c010b081d08040c411208840116003990340c042c266400744100d840381c2c0300140880c8001c0c464105150708c20b1808200604040d00608050350090f0308240c48498202e4595003520303a8481e449100d00c20010f1405102424982410444a010710060115051100120300c540c4140049001800040c00016903100c085070401e2000e80009410718850005503400165660824040d20301c5403402c2c16442911b9090005440d01203416a91040034 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 284317661 1250 284316411 284316419
    0x4181811040e2a0103060f0e070c030903050109150b010f09140114030f160302040e040204050402030f0d02011b030b060406030e0f01090507030201170f010b03071b05010f0c080f01 79
    0x200410300180303101943c2c0140300800c0501c2c0503004002c11203200a021005030798010000041c01c84549030001c900340e0140103400c0c000015541002603208516040001540c034007402d0a44010000c1e91000b00250b082c0104203003040b420303c1c4c42d2142e800d5402c4c000d02c924512400103681140c05000014000703000010304110b28412041d00516168040c107041402502400b247c9003540e1044681c918041808024010031141c02c42c80a03594000515007141002c1c0ae00020040e030a80140029110342d0b2988041000d5603001d1041c2804504220101c40d07000e0100800607018107141c01c100d00242c001c2c4214105141d01901540f4a00c8000a240d5032505041070300980c002c104020241305984030320142c4140685091154800e480d01030300003017075194514400101551030034048000c510030000188040340d519114128103640d040744c0011780307941d6506400ca0340c0ca4801c101c4a807282d5500c54400041c054190301130070700d0705150365041c4001081220240d13a0240251070041c01c180c80900108 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 284318911 1250 284317661 284317669
    0x15100305130b010806010503060603071a0a050c030a081005030c0904061505030a030908010507140304031103130f0e13022d0d0b0f01080c011b0807020604181811 71
    0xd0380644121001e035881449502c40061004003600034040079888031005111919040201552080048008105140c240040d1084007014040740d800f8400c404124030400d2800344c6c050b60940b040303a00c02c032900e60079080e030300401c00321090303840445500c2005d00102e40c504010801c583c031020003500318201d0743c645039200d400810004200c08011400d041012800d50780512041046034000d03500c01000b1130404c98003d00b112000303814841809014603100d891841c51100b82c3c4d50068060a00c01203115071410620f0540c41786074903050015400b000d0209009001030f01020a88000c03211030f000b999141465040b400601c81c0000c1d5010b42c0360900c54181841030351540032003d1500c442c41c210882c0800104402000b20002218950619030030490007021100c2554010808500200140c501040c00070f004a00714207841c208458084191005105903c000c403045039502408035036642d80e41d2030102d020000084441034503181488211406e24010300f07621221160080c101e5611702000100700 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 284320161 1250 284318911 284318921
    0x170d05090d0b01030b18030a0f080702072d15051209010b030607082202010e010c05031b0a0b1e0610021e0c01030605030601080604062d06030308151003 67
    0xc01d61203190101e18100062030028014001d40c890500c0b55840d00f0185c12440e400c49500c100e5044a071b00601c40009140c0d0700080101001c40203045c08a01070b10b810104a00349002c075040480f00041864107500403050804031a60300c0181c0c581108002a19003407480413040e90004054000741c000d010191000040096094010189a0002032a00a90320210381800005c88401011820782410000c8803803c40f010300749002402e107007035043d0039039950010340102d0f000c15a0504000a8408600401c0030400c11600c84500411003a40300301c5828540b666a401c0b0340c0c2c070454044006001080154524040045038440c0a1075800015038031401809a00151080510110700c954408241031041c203510700c401805030309024007c2030301c0f00f0002506961160340308a0195100300010450814082856070300f00760700001c00315881c80201c0468203894076141120348a80b5000d628000054a5940035004803842910f58141c141c0c1d071030800c4540c0c880481c0d100303500314041400c4070820718441da01c4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 284321411 1250 284320161 284320177
    0x110c0d120f0201060f0911040306050112060e03030f0c0d0e0a050601080708070e0402011b080d061a0a0503060409060b0312070c0603060501020307030c06060b0705010906200d05190c030213170d05 86
    0x740710f040554a031502c0c41030f034be400c0e8403075401e030341000c40406d051005074001c1e244040b0761400114903605045404044810b0010000c0729068408030b00e03400b0744103003a0442002d03002468115420005541080780e00c07040e081c4901340e41c40c811003600103405040070428008959001c3d0b404c03845030342d664005480d4030528910540030b20417901000c0000900e0300b8040d00d02c42090b104001095420303d114082c00350003000c007001c44800144070304190b89900c10122030303102d01d05507000b298903543c1d85400c03805401d440581650600460440100e140c84d041c016006690250500082c6559940c03000c0d411550359000c1e0b18010703003040003003030040f034091441440414800c81001905035500c0e501d520480d0070581003110140d46540c4800e051000340d00500d0b41c0300b800502c1000c45c07440c40048142062140340303d411400d5451f100014894400185080803601d82c480040c0b0030f0b5015094020000e50201c410404401c10300b0f8400300e03100341400d4000f4a0001418001c3c08801c2c0e00301400c0e01d00e41c1111034 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 284322661 1250 284321411 284321441
    0x302070b03040807150b010f031a01030b030106050a0b030f0604110f03091c03020903100c080412020705030a14150f0c0f0f070b010e2203110c0d120f0201060f09 71
    0x400b544c005208085295500c1c0b4102c2130020301100c2c000001060403082e03910310070400d410a100399221010a10400c00790f51000d00700006d048454501103809880301e544015809607802c40c0015030740030348600662080411580320300d1196280c404100848140e000081d00c400f84c1400a01d08540a8500a60300500410103c801002405a40c58007500f105810341000035004a500b440c9801d007080100c046204001080c01403420a6000070314140004001904148126410004850003400000090000907054900020060801001c0b0420b03c03c451002446901089000c0094800c095400f03425820202482900d4980e180c0f00d15400c8000c030002800e404015032040304000500030540184200f030011440d40c0752501c03180390624010f180f20003c0010f190780702c41c10340402841210b042e5050901d007180741c0103003508910340703540c405607035400c550302d0350882c800d08c1443c205400700000310790307203905003e861484100e00342c503090305c25120400705064092045024a4104500c1052012 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 284323911 1250 284322661 284322667
    0xb040c080a080406080c270a060329120303040339022724090712020715050a0501050f060c0c0f030a0b0f0906130206090d02060408010911090709030302070b030408 72
    0x1103847c8010300e24015072102d1104940707004075a060a42044005100c107007020042c046a46c0100c0c07800304585114070134032440c01c91030300c0640e0351031640d074079109000b60086036100e01d02450080c2c50140801c615441e4542c07072078410b0300b000b9108242815903040c250300489902105500707108a25421042e520822005454010a110110094075100b6a445003448045081b6640a414904030102d8940e0140c1403050030402856008a00306043e0144042c0040e560312031404c01d4400c0c607a000d11981c3c0380134105404d02402410b9601300038142c800c22a80c00b079039401104100300141c41840b42100c91500305e0981c00d02e203440c0c100400030f030b294809816251000d0701070f070350754580900841f0741c10145080e03142400090701080140c5644105804811100714651342c0000d00c1601440b000741340302b4003c14000d0811034a6500903039000b051214000e100001c00c41c034104a5034030703009000300c0c010042c000015038074038070034268003048a8250300907240c424100240010307280d000034020380d9448010 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 284325161 1250 284323911 284323927
    0x501050609130b030109082104030c0f0c0e070f02070602010203010f0909060207051911010e150a0c05030c01140a1103061315060c12031b0c030201060509040b040c080a080406080c 79
    0x380602c6c08407034810041c150752030100b03d400c60110b00c010007000650070414408c010000b40c014218101081e0010607560402c000707440c1c802a40007013a08a6000701c060f01040c002c2c500e40125034021241e200b42c007907960054131148101c2c00c070b0109200e021111a0b21203401c0008100551000d020140a8080546491490b40315285801504400321070a0403080b09a90207002d045e03034410040300310900e481d582105a000004460040710132443c01101c40024440d90300d03a01507406221010b500800f961f07201e031040da009030b000308840e0b03140c0f0501d8070558001401220061003801700c900c840c8602d050460312003205011495140199190b4925130307540b0004a040000c2c25070b0341c0205510780e00c40743c1d0f0411324034003450b42004200c100710605091565410214122440f840d0144150f0300c0d2905241106007402c130301510302c541c095a04003c1450900060004103602144258054203400102e1030323880f881c03a9583c0f40440c00152803880c050200b8413100e4440c032040c0340c001c14040c15060412040c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 284326411 1250 284325161 284325163
    0x519150308040f1e0b0d05180d0201060602010e03090d03210609150501020136230f12040303030203070c0b0a0615031514010903050d020f010f0501050609130b03 71
    0x54201803249150541c1c2046480d14040d50521310301c150f00e10400703040f4035156035403145020b000c0342c4292007070702d50002030102d2880740302a141c102c404a01b26071a00400305400b07402070505006680040d400d040c0401d50a21000088800d208005891012180a1500d0072107440311548400c582c540404801464243c182c3d005440c050302240800142c405480c07000400401aaa80070505590618014420458540c004074a00c44961800b00700d504000c03e501014040b0018402015007035a80c07078410080071054404505000d48004464034401101139960355070740940c000b0540c190040100b072002134825005550011810f0400031141500c03903580e0300700c100040743c400010542d120b0f4200f00101c124607102000051900781080000c2000d001000a40418019108080400d0445032180d922681d1500015a0400181c901d030000c00c1000a44039008000222229030a2801400304005d86103d81070403200024003203407410302e04a00344000540108070f1320300350998601000740744c6d4034 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 284327661 1250 284326411 284326417
    0x1090e0a180309080c220507020c1003020409050603060f0c0d020405120a02040f0b0d030c020d05031617040f05040c02070e1504060b03040201140d020903010c0e130519150308 77
    0x210949860318843e0900e80b0713061410030403040c0d03203125544010391055202504110300480314210080840c3c83c0d502c003a8280d2174418020103071a000b00f28054049070b2194103901400680e82c19903c00d10103070b00c0c0c00041540d15241502c8080c107140e400c0d40420460502031006203001d254940c00981070503a1240005e00c02c050954030002135401a180410840c0341503c100d08c038140c0d02c000200410890000460001e8078050801024007902c81120b500b55568482c91444003035000f0b046a50300d000c500140d580c00081120700320303a04950203840f52001b4004505a509886040b80c4026070309182404001c06041061905000d5004100000c0f50310340d15242000d215041c1c0d081188505416030041c00300b02c0324607a004038008141403040c440103070b030b01c05103201c2c0509800300c4040d19110760b018404003d11810602c544e1661078051080c8055803c044410000c0c0720880701664010b44031740380c20003039420868103205080c501101c102600c10541d07004940300702600c00440d40050700da0b03883c041158 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 284328911 1250 284327661 284327663
    0xd1704060302040905100303020c010e01030b15120901141b1314011805090f0c1306080a0509011b050c03070c080303041e0b060628080f06040b01090e0a18 68
    0x82e0001001d1148241a02400e50001c035a10307078607070100e403031a10000c0d02e80400b060a0380c1003000d0300d900c6040c681e100e6040100d120600410310040c0352043c1d0890700e85a800030041d07990820f0100c0c0042c52003041885000c520340e4201580c0700c51a0f80710702c0d02d207004407400c00310712004400500444640001c4020b2070000b60444401d04c10341c4590390742c00500300030703803038403010541e40d441041c2400a51645071358070390050859040c3c2011521912101c000034000e40c1c0c40e1030326000400d03000003001580880094054904481c08002980300c1c44841e41c282d40824030042075502031601d070192241e12581c0108101a10f070340580b8142500c60781d40d800c5080300c0b68000f0075140d00200c00d001c02d01180b180c568125024200700744000500e95529544081001000d240c418000840d003550784800d00a10784110700303103e010180c0d03070500345178001c0d003d001e0541701000004c101c000000e036241400e104100910074140c40c0c2c2d2403000e00d80180305031f28680040c800260261a50032000915800b0341174503840e5 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 284330161 1250 284328911 284328917
    0x4030f170f0c070503011b050403060e0c1e0a0603021809061201090309030215040e0c0f040b070f03080109060b0405151b0307120e0d080a0306050603010906140402030103110d170406 80
    0x44c0361100301803c1d21102460401c111207031189160101743c01104950480c2e61080300414181ea401700c8060915031810202e0341c1050100602d1002c00c001c40b084111740240441d0074007106500c0352022000c034040c0700c403401801000b54076182c10900c0d0903005076070b02000041c07070182d100c40219502829505014022001700700908014801c5280008201850083c1c6060340750a051038002031302d26a180240107228484d40c00100c140c601e808070400c130740241c518a100350741c0e40c0c6510b184c450b00c21aa0003c0c142c00041e003001c00032403a03102d64000d1000300d40101c0c101d0707400c06091070704104d1400f80d40c5c904030348940c2c010440032400c81d07540e184c104074615201000d10707164009410704402220b07601001d41c04011003510360603c0d86d6102c049181d1415040103920f030300c4145c400c0e010ba005102c1900400d0307004001000000c0d2000058009105464a05180030b103100010401d0009900003804001c080620750780c680429800c1044148140d640a4030782020941000240c81c481ea502c190442000 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 284331411 1250 284330161 284330173
    0x4060f030606080316021e0301050f070210110315040f0c02010606020d05090114070201031d100f02120619030c14101107030209070201020409021b06090304030f170f0c 74
    0x6200e00c40c8140c8000f024070703401031440c0284c103403100103100740e000e0700017480381103c1c128400c07000e41d100c0d4407155103850140c020400c030304141114800307810040b10300310014030441c101074074070358600d0240708122030150b0203080c10354881d1822034800914141c0401d801076911134403030301078030401d0143c846100d5103074000140e11030510900a0401145000507000c0c003404221460490b60701050748aa030912621b405070300d448080c401280500002c0608007000c403101c0303090201ca12804a81001a60002102000130340802100391090b40141c9501d0001250590002800c03402c003948003144600300c1340056812913480381d56040e0f40c200260024040d1012003081e15009062042c50780101780d0303d40c00c01c1030311080c0c011091540d59a103408000d000f40e0034a400700d24510b000750140c1d0044e00c1d81d000309644502d208811401d202c0714845210380c0d07912840300820010000030085409580d045045021501c0c6139882d00410441c440c1c0c21505141c50030002c0d05000c0c00104050070300c1c071030380b00080c004c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 284332661 1250 284331411 284331413
    0x1c0f020a060503010b0a030f020c1b190e13020103090c1e14030316110414041a0705030705160b13020f0a0b0702010318050610090c0804030f03020d0b04060f03 70
    0x810400d80d0804000d200d0b00700300500c080c100103c107440744207000746000b03e110b510301c1581034064000c400640c41c96120308a5041da00c0c2c03940b4100009510020394406d8a00220b0540e4411142410320600007c00100c0c808030350304180388501380e50301e2030041c1004100041942c0e01c01240702c000b940702003e4000c02c001e0407410b9990071103603000244505144825890304800000f40c8910641401003010781c9c01c140c9120401c041c0d9401000d80700c1c001081040080020300c070443e8001c000b12011965000ea4440c2445400300c0409068021103243d13507080c1c20342c1e9aa04065a07590310071100c0c041c8102e294031941001807d0a804a803150076485071210f10402284103100000001701d103410320501c03510400344150ba1340c92081c2c45516809203000b003130500050000c4480080f61001c0a401070180504000380c1e0300c400c1000f0070480d4104601001030300c200103c111003036030381a01c0040c00548040000441940309070007401001120310000222501f000d40000c049407141d6014405016148a00b04 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 284333911 1250 284332661 284332669
    0x606090f040b122b1701050105030604090b07020a17031003140a0c090209010e01230f090a080c030f1c030f020d0501060207080706091a13030506090312070c02010807030b1c0f02 78
    0x2c4080d51841c242500f000c120409005c140c840b0500619041240110008030340b07640d50340114140b240c104040d00135600f0118802500e4440f0218156000c222085000b0640c000020441e40320300b5429150100580c1140e44142d401e4021460010700da2080d05003540c046940c83e1940c4d0028130b018140180c6e01d0b18514005030498181300c1e070b030038180081c0074103600c2e6075248a5854481d03e038000034666030303582c030501c2c0a4103180a400ca80075080ba940410200d14460002124644450120100d4886943c04603e15984540300f00492010900c14600d421180d03000e90000500480841350260805030020408000ca500c240c1c040c5005900410042004240601000001d0072040c41c0c010798450400101c4041c420851900b83c11003e00000d40b4602d128080c41c405002c1c50340079013a50303000d041051000c2d1741d0340c2001504256204510000c03c07100d50280c21005881581078482c6d025074be440710003d500402c02107802c01c1d080520300c00c451741c0c100703400e8200508682c80703010401e042d61010b0041c0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 284335161 1250 284333911 284333983
    0xd0f02011205161215150210020f0307081612051e040c03020109080304050a050d1403040b0d05013201090b070303091202060601050f0a02030d05040b0702060606090f040b12 76
    0x113140c4491400001d580032441181c4014161035111788881800c4007480e0040349490501c0038094403151022581203e140400380056020703080c51354030844152205031410041010a5050708080b8500d0320700d038400020300c0e80002e60300c424040308181c4060800901c0c40321081040f58116241c01004a0910840d0382004005001d0701c41d020096003040d0500c008100603d01078010a403003a00c41c5001c2d041005040504200d4899805080d252504d5035200c03441600d030070a807400415903040100114050305603100c94514018180c1c41080f80b080d20ba40112b07210405040c52030b04014004101041c40d03981c0d00020710314584030ba60000b0382d200860924284050401d4100002c5410420500049a0340001a50044100c1400b0140d64040c1c04805034954400c0c3c000110340c0743e0500c01000140000000c0c110711400c02c940941e100342da150010031a107482003640844d8040b0317210310141c0c2203040075030201c0c000c8900580110703110030a401020345403814909003480002000b0318408107805001c421 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 284336411 1250 284335161 284335187
    0x4060c0818070501050d0e070608150d02010c110301090803070509042909091006180e01050403270504090b04021c0c0e0916180c0503060d0f0201120516 67
    0x44041034241c0408240c42d802e003807040d1410002c01050104106c0e10030742c40025414201e60840d820140d9a000181150703e00701d898101c00042490700188500b00002141400e0354140e4490704c3d00140c82e51081e0210407140c0701150151f5a4051410000d4a02d0740154000c0e5481c4d100c0603203d450000030802540c810f01d0102040e0f02c203e070000d07081c418010840c0f03500364800310b66812080d582d4103a402e1516000100c8a03890a061180010380000200e090400c0788403100d8007446040d01d4101d40b14241c840645008002403420340e00b01401d00c52600c14000615024803d0002c0c4560748c40c005000c3c2d03a034072101555804c00035010706c411480d140700c0c5e81d0b06510716031030825a0b1405e16103800c40d08100c4ca10501e207558001c4800038402034002d0100d1500105103041c0318040d252180b0300e40d29030071912070b02e0140d024600081607144900410a07240300d42e800601170505e80c011555070700d0794204940c8049041c0a0862400b072070030281030040510130207114000c41203801081d50004d06081e00855 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 284337661 1250 284336411 284336431
    0xf0b130209030a0f03110a0f20100f170414010b03060415050a0b030327010908032212050f0c040903050a080c0906072301110301060f031404060c08 65
    0x3240c040e49407004541c042c5907540007400c03c131070309029013000c0d10000c101d00780b03020b094002c902c08081040b41d400c510280da28082c080d8192401c600c4214008210700a16003150b0100b84102490140e52003010811013aa855280c4104804040241e03c28603040640e03081385e034070540d000c203910f60003000d203e410900740c0c0880082940381400c0d2683c6100c003074443e00012055840744005031221006810007002014060300700ea80c2d0b402c2081d59510444100c50500b94200380729480410107600c95500c4000780c500d000040c510741a0302100c010354802c6c500c402c0120514120100082c1d000211083c24282d5014901814041c0b902441c44d50405e40110102e61207103141030940404241c4c071a0507200001c049042c42c40b4982c07500200c2110070302402c04c030b655001500290b031900300510750b20840c01c03991b0a0749a00300c1203011803030030500341d40e100b8448034918107043c0700400145225403002c040c0c1c2d051034200000e54160b000caa0f0100401d044a066441c0b584640c081c1880aa0000401d584950004 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 284338911 1250 284337661 284337667
    0x12309120306130207050102040e0c0a120b1507050106050a0f0e01120308040b0402030705100f090e01030206070314040323100e07060c170301090501030b010b070302070b03040f02040f0b1302 84
    0x38001900041403d285200c40607408100341c0c041144c25030460f000740407c1c5058984510b40b11061459544c0300000d4240054141c1c0c2c011084000f650148410b03104004050341000d240380380818865070450003050b500f942d2181c40c001403a817218182040502000d01c1401a09402c200584400c1007042c0d000c1d402e09890000d00b000800d92111040d078119911600c851035640312800001d107440c0e166049541d1003d042c518045003150000d43c0220311070020385903000c000360385140c03100361220248400303500070008100c00c0002030721641c000da040c000c8815490b428140c0301e03100c010314480400c00c0642c081c400b412444001400c00c108a00382c4401720301d014840321140520702a26001144222414000b403114102304001c2c041c00301070240640000d0711510ba41e074460f40301c0080c28081c071059569000b840008109031158204030354080b80c01d40c0080a1203450f061070dc4142c0ea02c010829603440d41c44c140d90100607600d82c0a0402ca0019022003c84c03402a02d10800c0300d1016101031403500c030341c410 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 284340161 1250 284338911 284338921
    0xe0115060801260a022701240903050d0c03200102040f09050601170915090106170d1d0f030109140622110607140304031703061f020123091203 63
    0x60b00c2c010281d044d51144424101103660020440307032806e008103a0018000007041c100440110880e001c5e00c0c03400d803002c001074008004d0390000054040038103d6000b504405603064051150038000b00d100b40303050081c524440726410300c0301510303100c80c900a0350001020004944034074034910203454050310412a17800c107040040c0c05407104101e004030303181c1c11070006034155809221403a41013146a0f40400c581c500103210500801741401b4000b10040081034140094070b0008456245d0034081d1070300f50710b403044412154044034036000e03110380c04000240145c09544081c0145030b04148116a89450b21480007126030502d14001c02d0b8403410310f002000a102038040c120703801c1c990b680108542d0402015500071440354807403040b01504000540500420880d0004010030403603000d03001580c1d1102c1c0c6201108440e20064a02d1075100b10419000101e0b01410b5074081c054003168000010741440b840307500c411814a026420708610b0100d410003d4902c0b05000703910100107003000c15480d503e41 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 284341411 1250 284340161 284340163
    0x50c0901060e031e1c030f1506120207050705041407020d020c01090611010207080a05120a09150509010b27060402040b040605070c03020d0821190e011506080126 71
    0x50701c20008501c08100c005000c104c28404200d9218401e100d18800c40743c0c800d400740240200301d0aa07038405140030710003000c1c2c2c2c82e00070404094446680d00c83c40b114014841200194200710400d0764103001d5078000003034a0b41c46105d0614030464481c02442140381800700a814007140d140240107640141d94421300e40c0e030781304a10400343d0761103050038180394040c00c600754028080c148005001e0f07400021031450040e00038000d00940d0030010500c1c0340603a209210380c82640c072064030080c1344444418001503503d00c960000d1358044c81480001441c03c403100001518002040c42080c080a10940c1a04011224400c66980140192010340c03805142c10a11401c1d4071403489103504201010031903404120587d82104020354005280d600c1c6000d0a040c030404907809002040328030041500407000000788102c50a210741403102142010120058110020b00400c03502e00c0309a558859200f0310303c1120205030fa011f0121a914141daa604008100380b901803110110710a071005080c0990380328030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 284342661 1250 284341411 284341423
    0x6050102061f031406160912060e0307020406090203060111030c0d0f020304030c090f061d01050f04020d021c0b06130506070f050105151e010507170705060103050c0901060e03 77
    0x241c88008003240c14408109100420540d00004d00b40c0300724a0070500b58200000f0742601030388081380c10701e50302188885c09980d0b01d0001d00c1007002c119094851200030801c168004000d032220300f03003540c1c541b6030350303a000038100c5050340c0100e001581e0200911080307507844020f81882041c454015803424900c0c69940c1d0740c0d16000004031003000b51010804007601d01c203006a50003580d006240c007451546030150724000e0446c030060203181e0ba1602c140080c0c160845d203070280c03902c8400d80c804c0c3c000d6400c0806001d10415801c0855400680030001034600da82c03144001c24140c82c5002c5801600711000c00707054152422100da10f8443c3d68288603a0b8008a2940e0180044407000c42d000b80d95030180b85840084c00001c0c22000c0c05a510302403c2001c12422000c40300700d0030400b00d0300310003604510668560401041100b40d80010014440500028210404284448603035150a4103051495031124074090090300308036801d8001c298031001c00c1c1064000c01d400340c85141880608620000c1c042903a400c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 284343911 1250 284342661 284342671
    0x30b07090e04020f0409021504090c0c150c030204080a0b01140a0536070c0c0b030108030a03021b06070f23090f0f310e0304120311010203040c180605010206 69
    0xc00b1300d09045002d130b0b41d503510040c20300e50302400381140c0d25001c02c0600c031507800a12070309410720f0078450700c0e80754680315005d00c02c481a408603c143c520030201035901e0040c440e03264030009041e42044003085c110300c01c000e2400351900c103140c400c0a035814103103000a51210178134820b01540100c1002d00003580c50404a4490090030002000e00c20340065940380c2c64000504100c060021050038401490740c0070f006180c45a000d80201003100781c0d5100d050806c0d206c00d10594440341c1003842440d446c41d200350010b24561807070f401d11072040703d001081c0505140050303c00304085509803052502054020610030380c04146900d154403440304444e0000107510030207201e50306c00e002581c025800ca50301c1c2682405070035000340c128400b907805441070b481c40c11341141043d0010341c4412603c072003041840c011162614286000355050600d00700d4175000a6030040340403024804203000f0329441c440248091441540103401c082c1c415450010f000d85010381048614001e5820400180106c0e600054016089 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 284345161 1250 284343911 284343919
    0x12181009030f0501140a050f0f040b1f050910050307090216032001090c090e070f060807140c0304031406040c1404151e12030c0b04031e09030b07090e0402 68
    0x2c00218a4030030700610100e070140d030700720340c4038001d204244541e603010f14881c18000718500c0b4151a05205044010b02c22100102401180d000140040003031007641c803031224081040c8400551076200207003a040049486079058244140100294070313040007124003e250395601149024452007036080170103d451005000c1c0641ba241030307502c4495400e071444210b030004000700004070f101d1814079040710080c803420003214101900005090030105500742200c941d03800201b545446c00302c0584030070100400d14028040f10300084440342c0510340080c000b175280c45010f944d44501303628080e00300000c0a082c1c90040c2d4001c40811000804004407002aa54100480301e5180045000100640600550140c540003038410000b0411007039800380c1c4500d440c03000700c0c05500d600c1e00c00c1404400d04083c070250000d00b00038500c00105070052001c9401c18041d1400e4400c180b800240d9003840705018200c0c800164540038100203020b034001e110b98214000307190a14140d07103003200f829401c15000d440a032003 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 284346411 1250 284345161 284345183
    0x50d032a02040f050907050f090f0403180e011a040303050a0c2613120308010605090d0c0b07031202041401123b0721141218100903 58
    0xd01403004220035040398000c006000441e4003460a0020388400c0d00c1058075071003000d80c0480c1e1842c00e42d248166080c00074200000503581d46810002404020304142c1c24000c01f1800256154409100c2d0f078003034a0601d0448505500d462480104071852100303807603448905100600020b42d1201c11540640950b18040010814904103d225911201001c1500b4080d114100f992421420050074403400441c0c2503d1040d5036618040d1840d82040c82c0040c0001c1440700107011103030190005d404c51140c041c0c1240811000c5070340381c1c030418101c2d4101460840c000700e01c86041540c8141ca410300181c050f0802d600741443d00140542d900c8001540c2c80c1413150038242060001c001d503005c1c140b49a92181515910b40301c0c81c1188042d800c140310016007251b1956141917820500045040840fa020303010444030221085115003d1080c1d40c504031240300752030000ea018144204602821030300c80c10b040e2581d99080c00b95144003054218006400b03001a9144201040d81003049202205c3d044500090 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 284347661 1250 284346411 284346467
    0x1021b09100906060306050f0406060203040303050d060e0c0301140f031b0d0503030f0907080c06070b090c1302091c0f0209091009050d121a0609011209110a050d03 72
    0xc1900c01e6003149082c01d19060000503110303450740001c8121001551800302c600250750500c001d0320441c2c014840560310811003040000d100e1340081c4094180e070781c1c0c0083d40c144c44120390107500c1c03801d440c142103204010006001804845405180d0b070316007261541c81e00108032011039154802e0894000b150103c00000e000c15890b0f201c0f441181d590300a05503580c81c9030180e44091890001c1d03c18100921904e80080741410000880d0300d00c4900060250b424850b20359241d0b40100801003141070b450162600f01c03013079615210a40c1805620109016848100417000d0010305012900415404018807040e4004a000b000500000030b4058030901016074503c00901c4c640302204003040703032251906001310203022020902a003110a160340d441c0e580008040041c06864071410480440360300c0600352501c40c84e044004100d001010b0610308140d07800011041c046031b0b0510410749418442403540502840e10340840c0307024040842d000d1651503402d03280205001c00101508501162500c1455 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 284348911 1250 284347661 284347681
    0xa0602030603010f060f0e010e0f0118020732010213090507030902150703080c04080331090203150109030512031509181005070c020108060a030f080c06010501021b09 73
    0x3e0404c0c40c9003c030030b024003a40da60720070107015505d1180f00040d48500001080b078120084400e0b0140120b00c048000070713403c1c14000e4003440c80b03414001c0511642041290300103000440d281031228030a584100040700410f50a050011202c1103141d5a64410810170540a107490840400e58900580c006610703a0b803001c06400404400354082e40c4a0341d16405051041d444038018805e0510980e24002030351185000d1003080d0180d405019101e030024408681c0b0490f201c1c0010304100c40c01c200140ea501c8044c4042550201160060b251454000040000c840606c00d60300d00c101400786000f00c1c0041c91902c0d6a0f466083da8140024484000800706107141e5000c41142603150b0010803060180c20b04803540c0404540d0180c1e02c0c0160b000b14811075411101c1441928441c01c1c058580e04022400c0b50700449100d07030020310256101003c90310100c0800e014040440e04648220011640c034009000c0640c50072405031312040c1103520010904c4100481502881156201500c0c6030a050302d81180c44 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 284350161 1250 284348911 284348921
    0x70b060d020a0803070512040e01050d020112050c0d1802090705160b0f1e010308030a090c0e01090c090807210204091a15030303100303081b0a0e010906110a060203060301 75
    0x654046100b100216080c03074003100038481184900b0456058128850301000d0764081c2d44540072040c1810f0004001a0804813200c102d894414508007a1040d4010704850494806a6051400716804034074101d515500303100d0365001100c918181401550740d540040c2c010071005103100104100801e01d44005d0189040284111b64001250b9549140c0844158040d0504442900102c1705507402044d4145540b10680e042c0c0384c21802c058607560307840381031801901500c0c000310b4020070305a200280d012550384d0013a020b442c1511010916001401004100c8038403508242110f400101080240301100e03800d4100c5c0010181010820524900000300204900304028100c6448190030450740d030b010a80c102d102d1114054501210400c0c082072542d40d0000f01c850f11510000c040040c80800e000b0b880c82d603840b244403500c690240c002c1103400380143d0000081d0340d0214000007125480c2d0340c1c02402c0580900400e2620718002443d4461407552070701551400344c40b05a0000100e40151006c0d000 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 284351411 1250 284350161 284350163
    0x90902011b032607120b062101060201200d0b0f04050a0902090106050a08181903080114010c0503071212140a050c16061e05040303021914070b060d 65
    0x10801c29039900d0700700507210903810740410202400c2c00408000400b200c2d00500d008040596510301c085182d0030300c03800184181562140e00400a00000e00141ca0700c50b19452000801041c40910354508840a402d43c0c00c41b03002074120740817402203822040400016501b83c09042c9902140601110700411002034500703800f5500a07040c041000280c9001c0d030488101140b0a8401c240e0030f81c1d031418200c50310300800c1d102400103200d20001c101210300e40c604000d0704a0301001035441051801d40c20210801e15050b04602050030440104030700c15185407d40f003070701c90030308000c640c040003aa621901d03403142c400d00400c8800c00c011103942441c815850002d49064000e010041000c0600200715400401c44001e04264100070008001d06a40001d613071022218582090b00020659070711006001101303a041d05900c1d011043c1000d0300414052180070b03a0080d200143c0c0c8200c004403161400504040314400d00c000700d544000c0c070040d07241c21103080582111a0003000c3e190800010750300450008 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 284352517 1106 284351411 284351447
    0x604030807140616080a1404060e010b0604080c270402090405010f0203070503010603150b0418060b0703030b090121080d1d06150607080409090201 65
    0x3030040c9900c40c030002002d079075412804500d40070003100c01c40050450410358424003030308100116040300c908982031080c1d5092001503001c00030b014000030542d40c0d0342d141607840d0900c02e43c07107500301c50401071036155110f0381c400708940d4548860442c0703485458901c4440115050194410040c00300c64407010f20130f42c2d16502000540d4000900c2603610355242c40c509425460184010751040f100c81c0c94081c2c0701e5040200040403103002c4070842460310403076403061008880701e109070750841d01f401d0007003007140e20201c42c040040c00465010380105100412800308154154101212b110025612300302c0d280c1e84d03403060b800d4420519540c407520304128940000411603280042c000e4100011020034401060300148900001029500070250003400130f000040180306010340209038121101420006991039220081c861032242d0411141c0da25071860440e4010050028000d074850 = true := by decide +kernel

theorem cover : BRFrame.Cov 284172661 284352517 := by
  have h0 := BRFrame.cov_init 284172661
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284172661 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 284172661 ≤ n) (h2 : n < 284352517) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
