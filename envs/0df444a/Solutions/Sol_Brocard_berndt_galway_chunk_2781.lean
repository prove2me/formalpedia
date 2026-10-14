-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2781
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:43:48.052607+00:00
-- url     : https://prove2.me/submissions/03438dd1-ad74-435e-b9d3-581f713f954f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 500000000 ≤ n < 500179856 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 500001250 1250 500000000 500000003
    0x10170a020d11032e050424120f1e050105040b0609060415150513140102100204030b0406050402120d051206100801030803090316030509030f0102090d060e01020d09210801030206030106081003 84
    0x10441c0c08101c0c402403d800b14090070600348087c441c1408a5444040400c0d00c0c041070f0480c0c06850007162941c4c402c0c4d5660100145450304000d412211000500c090055610032886450031a00c01c0c1019424071901000140c000b0748100e09060045140302407000e040350807034400c54900c0c84800c1c0b4541094440c2c4c800d04c2c001480440001c00041519102c90039090208442a42198268a14803c0c200100e0240340001410a011780c4045030224145401071600140002c08054000700032900e541e2822250120080c0071500c089610b9840d880803240c1c2990140058840303000801142c0c1d00108040b00500008150000200105480e604104160b84003110000e8000005810b40c0c14084c065800007008a4803034882c1c03500780b8001810600968044081c003a0401050001c15550400505584d05150f8a190f50a1111111580384c80c041c62900600655920b80741c01d80802d000305200800c10781503401c0c0700c5080010001a121442113a0440d3b0f001d02d03080800d9101c2c1c84c03035050a400e82c0d170b00 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 500002500 1250 500001250 500001259
    0x1617030a0503041a09300a03090c0816140402040e1f0302151b0f060105040209061201091b0201020307020a030c031b1407140303070210170a020d11032e05 68
    0x1c200c3c140303c000400d0703603c4014245051b030085008807103030204007040c42c61080e0b806c0c100707014032621580a5004102043d10920300c0580442d2100780c0d4a00c2c040910074100c104c910203440c1000000b0303004130400b4110a055a09601e41401c03c07008552101024002d02d645030640c0b101c41500340310b91a00f0f50047d40d0b00621002e40700f0320120401c8525080a403018800340d4800032400c0c0b0307410b000a5030b00f0300303540b0b5200030705840d030300e000104070003504115202034100c0d00400020f200070319a40d15040c043c0002d030000262b0303114010b00c9070380403100700300c541c0042da841001404042900040c0d061826070745440d1007402d04515190440b20912182743c0c03e8450403100f60b00fa0104100000202c074500400011544643e03542c05811314801c41e038040981d01a0000c00004001d42002404040740c0b04840c142107000c0200001c03180049a003c65180300d0403540420801400000c80c01045040500940061304600f044003104112241c5040403c02c105004128840b880c0722400c4a070004040040 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 500003750 1250 500002500 500002553
    0x50301112a1203180c01170604230a0c0804110d08090d21022e14070c050c04050c0d0f0b03030f0d0b01050406050421141617030a050304 60
    0x1000b1212641040e5159110070441000001400c0c6001580b6a080241655095164251782d9046603c210b005000c45401644991120328801d20101441568055041820320580b8000b03176900200c2c0c0801c007401003040412010301012070181010716002420441d07503000c078850356240059107413140060042d04010079010344c200b4400140b040e042c24904111003000c0c21585600200d803246000070340c28400c28202e03004480944a20b030b0800300e4602c607064001039002640c140c450100c0d0b01c2100d4044c0020421850481002400d0224649000040c0d80a215905026000d51254000c0c00071445003155101e802500c170140381e401c0380c00ea00f43c018007541e650b11401c2900380620b92050080c10903103400d0064005207948a08215000c81d44665110780c205824401c951980c0f0300b0f981380310256010b00b02d00d18008034907451400f60034a0b032800000c010304089071180d520084410b03032294003540c1d1001200000c030b0001004864900a03a80b80a44c2d50f56184e10f81440004000981d440f21040c000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 500005000 1250 500003750 500003773
    0x40302180708060a0501090e150405040803160509010e1c080307050717030411120109080d09050609120a0c030c0b0a05010501080f09330f10050301112a 67
    0x44407802105a6542d0380d8040d80c030b0703809100c1c03000310078818240007402281d000c00caa4036904003001d030006044181c04404003400c50015094420a0303906841540000080c0950a003011409466505540c01c000c0d0419581c1c100281440191407078085c0174541d22220f031034201c030f80f8402c00b4140c1540100c00680b2403c20210080850b0061b20b4121020032040002c1c03044001d0b000d042d00d200e15406001404083c48540c140001e48010003a0f0448075902d540403500002c40c28401381002c0e1040d6080081e040c082400c203180f03000700c00340019005400141c0442d03c00c0b046801254102e20301420715280100107803038112140d102540028001125450038001d041f081074000c941250403d90f54103e2548400d6404a91804c082d9411401e90b44a0240900c42c0140280710381d940d000d0a10060080307928441e0074025034141210307101c040b400b41c0f4080081038003880702c8a101030101034000300220611541000e001d07105140c924110f0303041c0200701c3c6160f44080603660134030b41010400d50b102d40450 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 500006250 1250 500005000 500005039
    0x2073302060a0605120307060209030f10050f0a0902030705012001020d06030b1b0301120f05010c030c030e031c0b1207090b040b0414130305130807030b131a090102040302 75
    0x140d61902d64182032040c0084c207032400f503842c0b4a0070039000018500d800f4141da80c94000358030031211140c05018005c08030300945020701c00f1811180b0300d141c000c82c0c2868007800000d41814010705451185181c50741100160b140010604181c031800c1c02d2008520b0030000a00c00081c1e03400982c048958000034001010075560380082c82121321400c4130b0401900d880720880303007404400340007070030b4090140010410468414507040c450741c0184840824001c4a0325030500b03403449440318001294549a4103401c659261141484041c0c10310007850615022540322075800103d40301241640362034802d00012980e40042c1c000c03005500c0b200311140c00ba503036002c00024080300312001d48200c0c6451019512810305000321001860800f610803010f9a0301c510451198010038015010003405100c400002900c0c0b1b514a030250030030780c0c000c00c440352940c42c0886c40d001c0020114a14100809101c40c0002c5100d0182c0f00d16807000403000b09159221000f00d40240225880654004022100140700c00381 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 500007500 1250 500006250 500006263
    0x40c050c010c091212050f180901140f040b1c030c2001050a0302070f240e150f090f03040605180103110d02070606090c0224060102073302 61
    0x18194001c1c03100b06008042610250020710130382d642c04460b03c0c2d00e40001401e2121240d408072080c10410300b0062900c04420300d5812400e2061040d0f51100c5510006142c2850030900500c100545e40846d08201400b142c07005920042aa014070344a100030115a9981c11407a440c8200c489264150300b10395081c01080403c0141d02664007450196401c18440109005100c400b038040c0c40301c5d0725083d1031010450007075121100a5461107460030460000805080280c50900c00d6010312000000545003450700302d07030b110311188015604c00f201380000e0081805e2490381c81540001ca1074000ea540c00849800d082040482088a00000801140035030b00000500301040707520510a11108001005504071345181101d0b04409206201c60900c13507100d0740040000c10f10641010a5240c0d690383c1400940c0c90303464040c0b005d604071840400440c108000340310740c40151500140050b003403540001c1c0d2944002c3c040d400c2d59208030103801a481c1031072261180c03404c0440081c81422301030b00300c0081d1542d8 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 500008750 1250 500007500 500007517
    0x30a110708100506280302130e0a11010233040c090c091a070507031101020c030f010b0f060316030c0e060703020705190b0909060f150901081b0703030504050c040c05 73
    0x1ca207901c1140c1c1040c1c082004482c00c179107100400d90f516085401300007035007540c105c82008541d140c0340c0511200138184503820085104480603880e000b5941c00190034a20100004280902450552418490310400701c00c3c450f901c2092500d01512581000550502c07960000100d040c103000c01401d47c2503114104200702c0e5030500a030803068000c0c80d0030740c180384960302014200c0d034030901007800820302e2240001e000320f01c1401100e07405403804c00440c0c1450742501e4419016551050403120a041030400250846421103100c5d14600d8001000302a420700d07610340e0000c050341c0389564202d10307008125407503140300004c06580d101c98040c6030081da40c0c605801528042c16081005640401a0f98070b9642503c901207040c0303007407000c41818415109401048181d0020034201c1068103601d41c0807001d211401c00d00d03520fa603034069080000d4086200903101c10b4000e0111400004040900d80a03954070039450b14010501d41c4950400310714160460412980c440e01c0c3c003a5491074150411300506441 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 500010000 1250 500008750 500008759
    0x6150f0e011e050306071d0d0f05070b040b0a0305040f06020c060402120d1d0604050a0806090106060f0e0d0f0203120c06090a020f31020702031608030a110708100506 73
    0x10362102c000700a001040c440d1580503444103001c00d800038012414819200c1248032030b034010b10807001c00640c802d211a40c050f01e941141c1d0405100380402444641e002c0d090101c9401d261903c0c207420100c140c0700f4000142d08060f81d90003c182044140303a02c000c9450b800c51410b5480300182481d2030b403a00000da030200d00c40d001c1088280409200804e50880401294441003490540700d461080050301c0c207892154485000c020100d445c0d84e03201084005055440018065843c203d926035007103401a41181c0c0c140300501540006050780462800b0f5180d505440b03417041c0b030b403447c07a10301d1160381c4006c402545070090820000c5265040400b030000c41e000c01d400c031206d40d26030071002c6455511202019400c080000703280102810043d810f82240e881c02d009400c4150b20092126130440c002c14100400d140d0002038442c194a0100401c88907180a104429000c0345000200c4d943c901c5290300c030a0038411078030304036821010180404401401480c042d642007210036401c040c000c0c030b4115000d611a = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 500011250 1250 500010000 500010029
    0x21009080d0b0d0c0b09060f03070903030f020f0604080a020f010f2403050d0c021903032d0206010e07020a06140106140f0f1b0a0f050714010203030406150f0e01 71
    0x3c0ca0208240340c00c5981042c0c206401d98101440c03100180c0c8003242c4190401420021401c01c00e0003803000b980700c0c0103103a8410954608600d0010164042d5248140840d8444840301c189610049403c680107607008800965410030310b64160b081100030300780300d0415460112030102e01e800d0342c0c0040029003608000300704094a412042e200841140c0405001076100322440c201d40c030701401964020500050901c2070580140c030ac045486022500124009100006619100810041800d00c10041405080d4007494900802984d42d035052003038880b00d50754440495a41c80c0240280c5142540150062000f0340d011400b601100a080c8142d80c001200305110362031005442064403c2d22050845007403410140a101802940042c0381e80002c400d0480914110a40208940b8500f03038030800800b0704622840c02c2082c180406640212182c2920103030300120b0342e0f4080202e1740c0c0154000c9002402501c0c0361441d07070ba41d815035001450501080d00020518800000c4294100c88813002d401d9132 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 500012500 1250 500011250 500011271
    0x6020606060406051806090607050a05070e06180711070e01050907020304080d03150f090b04290918010c0507140c0904020402071104020a1d030a0f0210021009080d 72
    0x820348110b03c14a800280c040c8a10003220081c00c68031506280010915803c2200f4900001e0440d80641c004035841d600c190041c3c400c01800f40700c510014445400701c410305140040210341d0512140746100d04a203550000590400d006000104078105d900c81200c00080d192420344404800c203000d050300c40c420200005044520000c205c90940e2100405051a00c40a00d0168041d0221130400105c0d10381d00a80402c88544106400000b0400c00c9000f00b009030f200c00900081701c01c0c228103650540d21009008500e9290203a0744040c81d401a1044001071741c0d5019003448040c018078100c90300354200403483c4c503540c0c1c0c45000742c9120b50081c142130b1024006155115612822521110b8205841c80c00080141c41d05034050b0482c40d01514541900c0281140010100d80c0140c1c45040403030041e86c20500104850603004c4021481680241b40714902c0d5150003202a08201c1c00074410a000e404000d5440e109000140c0c0310342c0c40d18424040c2010b02d26000d2007940041030500742640c0b40886112 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 500013750 1250 500012500 500012509
    0x5090405100803121308070f1a04080313080c1b031905120714010504080426060103061112130b070e010815040e1506100206011503022a0706020606 65
    0x241154060b60082d0b280001d50303001018024030080000c51000424402580481c400c013000b00b02191052445040801c8240b91003845c104801c40502c60301510f040400c00061401021a40c015825201408030040e1620f0701d40c0c114814098002c00728042c000d1115050009015240b042503011410360340c01001c2290140c000030325002c0050078550089152100310102c0c80000d010940c0940300803043c0440204280f829600c0c142e6040300c8a102c00901000000340c3e0000c420b41d501a03501d6600341c180e00c10041a5901c02041c00043d040c01e944009860025000800f01c40002d122040c1f413803a545043c6d51040d9600d610003100361460010340c400039075058441e1307040003c5150140c58030140c3d034640003079403002160050316643e0050b5a40d01c0b1001420410000d41c140f9400f80e5071528910710b4490180442005200e60800540d804880140450500000034280c8100035140c01a19035074080c240001ca90800d548100300d480c032074001c903d05d0543c0400c25000340c0718190200c40c101d40702c400038407 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 500015000 1250 500013750 500013781
    0x90b0903120109150909030807020c03070605030606090d0b010906180b010f11121210120b040609080d02030c0705251a0c01061502060a0501050108041506030b0705090405 75
    0x300564518000140941e1140d41e00c106200e502881134110101c1e101e0600c44200c0e0b48802d41500440d402c08200009182d041040070008241503014141c8286422009031050202602c0640701d0003005c80d10754039035100d1549100c0e2440c1c0140c0f0907841940d5032044040180001c0c000d2003846604030303150420b141c0305070083d03403118041a99148881d0307049910072134640b1099150039800307005814002412031444800350501102c6400c0009281c1011507031070351241c24950000032030081e881400b074041a01e1604803076001e60040c0000c966008240380c4518148560b6070380c002c000d4404010b120f580d4066901510480d841001181c0a0007400b01034050780e40b4051550110313482020700c0501c020161401d50690206200084038101110365100c0360940e15030b6000603100139544c008000400e941001487d8000c90b00d62010060755041c2000245043c100400c00b9214448900310000c8881c12980688001d50300b041c1c0010081c10322010040169022105040c1306a081c1b50200313080c1c05015044 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 500016250 1250 500015000 500015017
    0x7150c08040b01050f030f07080d12050705030c0705031c1e110a0302090109050405150108153a030503150306090615011e05041703030709060e030a06020d090b0903 72
    0x140c3c80c0104010b40b1105c0f000701541c16009100ba07030041340e94104280000b40c03882e000500050560701000506c4042c01c5c0030176444190904051016541d00202183d41150382c1d004483d940350f607581410703441d40c172450410b60000140c01c2c8005511190940c0601c80d03a42482400d581343e804015405000d513900808015020a4200203010b00c3c540290300820b28400181040c420040e030306d0000a0072107104035401041e904c20801d20042a680c02468a035021241c015802c843d08559070214800c242001c4440c10460501d41c0c2103680340060080559200200108013554502245001803c0d40c206942120141408040041c400d19011519a1290100710700910040e540e254000225509044506041c0a000400452949007013109071500030016280c003940c80d86042664141502c074542e03a08502d070414030030b20070300300d41c06090322045864501e0034080c14460240003900f0505000801810144002008048a595504004419805070207842060394500c4c19031900c07842032040 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 500017500 1250 500016250 500016263
    0x1080a0b010501050a032c0d110a0f03031113030309080708120f091503191109040c0908190b09030901080a0e010902150c0d0f170a0b040207150c0804 66
    0x60015521030005800080d4403480c020850741d010b00c07110483c5200202060084500006c01d0394040c01041000700003d23805403078401000c0c90f04280007a268506450700030032030102e40d44100180b41c800c0d00300c00b02900864017195528002d074022600052803510080380420000c51b030000f0302c450b0200b494000c40c0c0703110002d807542540d154404c004136031002c55141141c21061100d00c0c503948402c100c26048030560000c9c00c0d43d9081c54001e1543d010b1020495a082c541480c60300600d8043c41000d544503a1070540d00492503501b80034007550304142c2d9800c000c880b803154141c030324143c1000786941c410950103000d01800c0c0c0d0700c6928580d5101d01c00c01081c90702040d020b4001c550f280e2559800000503141c190700000d4859525800100038404002c40b0700d05000700130031414800d0100344072194007071910303042c0b842c1500d09507540a806c07100c2882c1690030728a51f2100007481028182c00c00f074000b410080013107658050310b1800c0181030824002c0514007a142c0105240b4a50050001031b019540262 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 500018750 1250 500017500 500017523
    0x14030c0d020c01090602040f090f050705040308070201021005070215160516050106030c030308151819150308030f10030302150a15140f0402131707030b04050106050901080a 76
    0x40e04010b03600085281c01259a161500e101080c901e10140c405400c0c00148101580e00d052040002d039210004240407403460a002d020402da080720443d402c41c4e41c481901c907111903040c00117034100b40c00c04080c140c1460501042001895011501380c0452241b0b40029981b91203002449011502600c0d420020039800c00004014140781200340e80280c0c410000800c05644a5070390342081c210301d40c401c401040d41c48040c005a6500003103007250340c40c001c0e48c180c135401041080300002000d001c0c204070742d01d45011140211980141c0c008180f03004403014445541c07070b900d00d4941ca4a81c0100d50402402c120900440c0c101c0b655035516408494059000301031603580d450340d046031458084c00b140800c90366241c080c00c8800003401d2039802072000803035100d5458a002d091210b44004902010b2190b44100107501c83d00d4880c800900075103404903000f08007120341d42405880d0428680010300711b280346008000401005420440a070b030001d40d40f0284a903a42c20b13083e40e48416180300200740c0e40350703107 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 500020000 1250 500018750 500018767
    0x10e06010509040507150503100b07050c01110312090c03010c02120a0311090d030f120c05030117010b090a0e0d080c0a031a1804050d1809050606190c0314030c 70
    0x12030002e4125001d0825076403820ba8485442c0e40d940515205c80c030203c7c001008002d00c400b000c9500301d00911a0701045403801034195142502c2c5e61001c2c0e04a41488516143c02240b614208240c503030031004041c03c008036052070706105660b131075046112846903081590181c500ca1010903c518240042c1e10040c6c2080d2041c8415400ba0621040c401d625010502843d003240e550009400c4405000e9100c80341c00c46401079004003500080c50444c100281405204006d40c0e13030207000c582c1142c0303540c607012600001d042c0810f0302419104035055030001440062101210303a90744908040100a012250304070032405003a54075070812146184201824005607141c64025004401039084000001d02c2d010020070004c0c0042c101b000c003426900c00c4440401c02013000800000000c0d2499040c1000c0c090795020724006030000c54003d140d606900c1d24089202a228902924400c4c884400d05040f00c030250078004242c2584110103400149550502001340c80240c012a030203031110740040d5107030100c030 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 500021250 1250 500020000 500020009
    0x9021603080a140403050a1112090d06060e0421020a08030f1f0801021e040b04061803020a0b090906150306010c020d02120d110c010905010c06021c1d010e060105 71
    0x8042a10036030300c80a003500f80b010404000e91140c0e200b03459003034540440507802402e00b42e20250b0001c0b0f0394060782c80c1d16540c1d0950b00a42c2c001c1c0d407044500c0c0c85100024070f002800303040070f903000c081000d19810a00080040d20740801d40d141d01c0d0b0302c106004030200c9420490317461001090140c11004208003058055815000c403039448440c3c0c200e0050701103080c030426010001e00d41d2043d42e440c3d50100396010320000d03e0000603141244d60410500b0542803044440191095214000911280c82c40300300b01104c074488158021600107101c043d40079600c1c40e1101d1264400107800d07118a075480001440d03840d1542140c00c60800001c00541507507100c1c0010345001040c07c8060703038820031031506140169500c504600d01a1000b178040c0828100161001d040c06605590703110164001c1c203070890890343d101030884111030003403820703030408026814990000e101c2d900e2100004c614410040006020715000313407207a440a040440071002905260900b00c81da400342c4500250040001040107261 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 500022500 1250 500021250 500021267
    0x9111b06071b02030c131523120708030708040501090603050709030b070c0f060b030f03310b0706050115170c09030f1005091c120c0e04060e0f0109021603 68
    0x1000e01180d84c003205c0c0200161150440ba5a407001c182c0c0c0382c80070480d00c00d00e016810001482002e00c40356196000800d0218181c070300e04e40650082c040445481a650f40802581004164500c20749503504074509000d030341c50703100380502c6010032031440c0001089403080c070400b0f206000380d9481d0781d03c2d03604560741c40044c10400303085c0400f080900d01c0c01c00c000c5184100d030351010134410700b80000e000150a0a050404d44407400100c2e0b1034100b41301182c2c20810301030381310600d01e5402c4200c0c0c030512959041c5042c42c42072504400c811310001b065480400003140e110506807010f080c0c614003861103c84003205c411504640d40016211090301003070824a289001c1c01610314018162070034039683c0701d00c05250030740c00e04000d6696510380050056400052120103002c1c044480c2095a4544000f00544018820b03284c1840140c1d403010a4004180300c1e10b0000301d1048001c10501c11a03980f985940804501580d107203143d840d0f03032000041c4141d04d074130817200903210321011211407003415281600d2410 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 500023750 1250 500022500 500022503
    0xa03090c050301020f07140606010206150102071d09160f03030e03070306020f0d050105030321072f010506060702030604171c05090d0e1c080409111b06071b 69
    0x90103040401c0c01d50302130005e04140009006900d031142c90341e08080841c50345103001c034603190300010301b44102645d000c20240d5002c136550301e60b2030300d440f20500105c2c5890401c1c0d11407042110311112400d540003040c3c1c032460048000c14100d800e1403018009588050929206541c0304c0244840c0c1000083e00860300c1d07103521000202910700c40c3e40c0e2074840c0e01c103076070061040f400240400200804131144501c03130180500301c168011420410a1400e07080c402c4540c0010103903a52090001490442c8280700c3c000e100100300c112103100401001c524040145800388800095007400c00050341424000103590440d600100200059261a1250071240c0ca80d0340c414145000700300035100102d80310040c0a4a04590781000241c0c07850040703150750518006104070410425440150f201a64541c3c519455050020490309802d4501e45081b00452003550b110100103410039029801c40c00c8060040c003100114150b0707411080b9001565240c654030100c0c2c4810205d03590001200c0b810420355081c1c15801d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 500025000 1250 500023750 500023763
    0x7200601051c060f150e1b03010b0d0914010b041116080915070302150a05090604230a0c051212030f0a092f040b010e04050405071a12011a0a0309 64
    0x2504411303081c0070354075a00c40c01481070307407010707020844480c03810810740e8015107030300041e00c18110100804602c0c0c0710600c510112227030041205148001103620805445501c2460400356080681a45020301206090075201d04c0c9071000500c1495a180704842c0b8001e220025200f040025945503440d40e08003403001600444880420171001000c1e000800c81c250094006000c103106c0164150701a4000616006501c2d090506120042e100010080c0d00142d10803918015182905240034200300a40015882442480a980c05120081c00c0b040c080d10004d0710482c942c0314800d03240030b66501208100000b074000800006000c2d42d83c110326150032903110076012038501c007076854200c1c10076443c2400e92a4a1441a81910000b09042c0300c000d110500b640e00b07100c0c5500312400a0581001f0944450040d0380340c01c0042c2c1040000c0c04120040e1542e407036251880700c02401e00c0d4a898200c107410b55032080e000d400100e402c040806030200390b5a4040041841d049a0b0081140501500c0d2001c4401 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 500026250 1250 500025000 500025011
    0x180b1f0306150903050105070507030e0d02010e0a030c0e13020a030b040503070807110a0501110a08030c0c070320040b0d02010e04140c09010311070305070206031008010507200601051c06 82
    0x2c1d80344001d84540c0240c0d81c9078110703d401c5052040c216840a844071040c410108907010010303800c2401400c50440864080000000034001612a140c00703481c901d40c8601c0d001400700c20040d0b0600c2c44025a41c52400000746552043c84c40007200151143c080c0d80691200020000650f200d05078992041c1b00c0c41c1075904141c00c0383d6542c1165040010103c402c2d40c41c402d155540c504154580800a010918140c0460000f91b0003440c3c96564414015140000c0000003c4c0924401000c540002010b8802c40e0140350b5030b0305141c3d408604818581c942d040800c07081301c1d80d0b0300c2c05002d400304041d0024405816120103a006580300c0c000c070030485030056241c6051000150b00b4440b42c074440d44513120203940e41e6003200001400c4130040141a0709428050241c000401c0c2c1c8902a41c2d095070341550050790f20b84690052070803208469000301260340c205410464801d90007101c211080368980c1459a500503141ca01d143c95400900605801005000c8400200303221b84400500240c000c6200081 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 500027500 1250 500026250 500026259
    0x61e030a060618150f11070b07171305040b040b090702010e0c0a030b16050c01020f0703030b0909060c0a030603020a03050708071a09040c1215180b1f0306 68
    0x5941044912480305656440300700702990b0000c40d888000001548000d007218142810740b0600e40131101d07030004000482030001d001e140112070031a000d00c0160111904c4070b40e1065450020744c002c042c12100c801c4a4440d01c56a00201015a1140d404444603040503509000038800180000040c2d0381d401501e60f0340d50f103107540762200110b004100301e90021681812518a40e4a40321a07460710b5400f4000179031080001c1aa040b141302d4000b0701003101c4601e40304052000b240c1c18020880d1803141544002600d07010600c5200081164174800d407805d010303584c1c414040210702c000440301000c03139400040000e00e00030501c60040a210781203040c0001d4554076074003c111540400c1c3c1080790b82d41d001380800e0118403020450785000740700350110501c000d140789050b89010b0007400c05260050f9201c00f511a00240101032a048100f2541000c00240400100d000800c0f1114840e02070f00000c618103104048000e401002041071002c0c5c0940e04103405204290380e2542101c1c0d002e010540e0f903030000305 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 500028750 1250 500027500 500027557
    0x609121203112503080114180705040506040902031909080304110406080706020708011d0a0b070c240b09010b250209040f030f08101205010b030102030123100e06 71
    0xa81c0303080f000000c40009181850090060359041e0000743c11820360350600c00503603031a5406030340d40060f0307148145195110510b0640c0d0714019034001035800240410081040407540d0b014511072004138070100e4548850506080c00c40d115850060140c0804200103030100e82e40608028280e14041c00009072140d83e51500d5041c400c40782c00c000c0058010900c1004418001d02508068026004d1101a041503410350325a640d00d503070030001d0404491200103074105010f074082451543d007200c9483c5a400000700d04030794003001001403605062400100c00140e08200c802c0301d0507151882c900c14038006c03040201c805441000c2c0011005540034001260040e02d4021041307000f07070321130b801481d008002c41c0340241c030142640c2003610800803038a080200c0c03140085045811102001020701b809405420305034090090620040d802d50300000000030304207002050f07040c3d40307207800761000c0188000030700704100c071076240c002c0130005061218003c40c6031901300004d084140302400a4a03001d1505221130 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 500030000 1250 500028750 500028787
    0x80406050f071d12011d070b03060a1203030e01020301090b030609070303022d150103022805060a0216030302100608061b0a05040810090b09030a0807030e0c0a0906060912120311 78
    0x701b500e081a0800350324101402c000d00001740074002e140304d0443c076007900031030046507943c496000d030f0355006242c110502d8040ea00509612844200a40d40c80d070f1034901c1c03500079114a842681c001d200306070015203454400b140c0e4400f6240d00d64007901641c000400c0308408190018041d510b01070302c202d4106c10060b003c110902000c0e81e0080d44010079071440c0101702c139941a00c02d460b10815401c101c000301541d5204581c2c0247e03102203400030744032103040c0b1040349000c0e41001d07c0401750288030750220038180c000030b24124992140c0c0702400150b485116480e12040d00b45d0300d41005000040603542c54141243c09401e001015203803460030290350b80e041318581950b0460040b0620340c0e0341e00500c140088602e0503680071600e0001145001c5550100900e0000e00812200c100740c3d45050000540c40140300b110b000c1c42d40284280c0d200385d203a1480c40e00616642c451040804c40d1000005040001c505c001c118994010007400c0114080c83d0741a4090180c00d840c4884cbd5520400040345002c980b503c00 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 500031250 1250 500030000 500030021
    0x405060414040b030307080f0d060306020d0605150c070506070807050312010303021605031b0a08100b1207080604140c060c0309150418020d020c0607080406050f071d1201 75
    0x14a41949190018481180d102c0040309000c0d8000f01b10650100da545403c4a030840c43c0e50100315175540b8484a68030080400703406c020240d034000680684c40c03207041d41100068400c1110140446081104030118500c00e50345242c185400c00d0034100141e20b400e1000d04140d070701813080e03035280c1105542c4041c01c0d580100c070464402c82d032240c014002d241d07041000096030f4203040701c941c1c6290304010002c0d4ac1c0e80341c10015000465040490542c2170b4482d002d02074005d000c801c0c200d5009010440d24000640707108070790f080c0921030a80d011011018001240001c42d4080000f519544c0c03240d0701c8540290404260045103485000d04180c000d0329850001d0243c45894030244d9211143d402c104031215001904103040000c0a0000b0301070380c2c811252082442842003c0107a8400101c400d91021f070244a1a8680b10b0003041c0c04c0001c51a00840c00c20310075485072404001c269100341d000750341d40da07040c0e80316800980038203811401a000910740141504005092944190407010b0090a49244a90 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 500032500 1250 500031250 500031269
    0x160305130f290114041a120f0f0106050f03011104170118150c031104090c0216170d0503040b04020904020d05060108010c030b0406050f06130e040b100b0c0705090c04050604 76
    0x1000860015800d043d01e41d5000c139170500c40f0281d91700d00c4000c4000e4500c107291154004d200c50f110640800c002050719103880300250340054805d100024024201c91207024041c0b0460502e0903401c0c039040c8038101d15502d4110005007071604055291140d010340c0c03814040c05650702c0328917587c072607001040d04003080e104031840205038030071a07004000c0d1040c001d902014581000c2200303065800c0b030300682d0162903c0c80f00015401051070422850301b40704907281c10780000d1009000c2030030504042c80301007007170100d0111880d4060210341141c10380300840d00907000b0a40c1c84041401031a0110005400038002403403565031071a0741d00c0d041d0610400fa0300c00280c44c0c1d074074400404642e40500854010040460b020000a49400c021800d0ba140620f007041c41751400103504910203000d2426040503000d0a824080702d0703d00b9103400c1c8030045040d1412040c4144565001030703054048004c42d00c034040711002820701940b03060244103410001030a80c5012076014840410503440306009800280324054 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 500033750 1250 500032500 500032583
    0x30c0901300b0a0c030c0f050c0a0602040e040302070f03050d12020903030c0d0e01020a031202071a010303020705130207030c020d030e042c0319080603100c020303160305130f 77
    0x10743d100300c0700012140d00c18581000c02044010b9041002c3c00a885407074100382c0e60b552105000d060604541c1e4800600d1944045800318104441400c0c00307214a100350220343c0d5060315000040207030811844000c016602415050204a115140ca00445004500c0150905140c400003900315003210702084010780c044004038081e01e500000c6032503001e50a0015064000365a03e00a090442e4908034080140e0000707100800c2041101c40c0b90180401c020413420156100c1c90000e445d9541841481e00c90340840c01e21381410310540c030864841c5581a191510107401d01ea09006442c6810b900c180c0034410025500031054942d0300420540d1512615403607050490b401c900441c0d8150002e10032065030040c0300200e150300c0e82184040d1581c01e5410a650389070f446400091828014840d070f1854241803100421380d084c3c001000e90700401c00c19041c54900441000f089003103d404480c046040c40b150544540410300c4c01e80040c003d24000c44c0c151040000c44044280003030b00000440740001c6650 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 500035000 1250 500033750 500033761
    0x50909010c030b06040501021515040c02070f061403070c15050c04031a0702030703320a08070c051b0112110c06011202030604060b010c140d0e030c0901300b 69
    0x1442030f11910041181c90908140c24140004d54907500400035000210605003c109022070308510100003841c0140140003164568000a417903148900c81c0011202d90b00b207022990f6409100414a6000c2081c92142165100380b0304603800c0403244404c0c4c43d0032081d540d09a00003501400f0b040d1142030401c43d441e0b582c6155151000301030080c2c03840300380d030720f43d408050201c2190302000329025a078062810501200340b1031600b52104c2e0784c020078aa03021011000e58a04c00700744174040e08980d5400c0e11038509586d91080195120058500b0051407504225400380003800e41c1351490020704018541345a0a40015680c9030845a440045131035546003c41c28041100c810070060340940101c5580041c004034507400b1a5548001a00060070f40392203140103241e5074440d0030000d1400350000c40400c1c071034800e20907058603000440341031030000703028509140e03c504000448202a03c000b07030078460300b42e28004894841180c84a0466076091206151111100d000c0d440e000b81c541c007940f08220f090400 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 500036250 1250 500035000 500035007
    0x70b010f21110111030d060905061c020a0510090b071406061c020409020f03030a0c0b060d030210020c010b10030f2018011103210106021f0b0a050909010c 68
    0x403031401c000781d008000d0485000908020341401c00210a00700503802160300d40d090307400c0d80200054009000c1c5440070010b136640301500030500400003682c04065580e203911304003c1180312408007039001564103602304418100140800701444a602d4807401003501d403040055150706c9078800340c80030348000d06018000c3d031044c4a455000360b4100e85104940d4454041000460741c2180083d100da541e5401c61015903c0c1d040c50340c1401c9000406072556080c0600001d80301d0142d5031010f56071504080000340700c034282032004002058268000b841e40707200c2010b0304400b031f40c44600405065501c802100620b51a135140326041c089050714045907000c0c500018100325010040d241c00e405441c1c50382e03604144016401c48540322a41e258600c200c2903100010b864640d0401d10425540c400010a02d1154182c40007019607100d0a40b604681c5981c5d44508170380c2e9010004000c03c1200507031082c2110900e0a41c0704d00350300c9102030041c0c1d44190b615070001d003d0703240c100c031a8244c0ea5103c40804036425130 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 500037500 1250 500036250 500036279
    0xf04110a0807050a0f080a031d0603010909060b030f0c0603060a0e0c030a1b09060302130e09010606030b03160e070e1509010e0d1502090f0607030918061d0c070b010f 73
    0x140d82c2e480c0111103146c00120b40e0f440040c440090180501c011070f00c2104d00006202841d520340141c0303141d079a03503900c000c110b00922a0700410340e103052600c012000c0501d0301196580030b08003000000c02d000c0450780c040080590016150940c00700d0300c40800281850a46042d511031085a44560f0310ba10740740e50008184c0e00c40c806200c03e100321403030030200b800e41c100042f14103803211403030010386a10500c45c10701c01c0048242c001d41c8686c1408410420a8a415005017042da055641c4c10300041ca401c0090594820b0003291240000803049414080c080b01e003c18940d000e141803a11050382c821480118206440c4a0240c060302040064a0203003541c0013002c41101c15000e03141e00b4941c45054481c1d02e42c0303083e41d106a14445800145109450b5112114441d181d980101450f54031134084c038002c0c0ca4039410348503184201c1c44101c6082000304480c420b0f103080b01e000c1100c101e00c200402d4620314035101c1c0100f01d4102c4910902103880443c1d2a003c03980d0282400c042043c81250620701d003140f482c403 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 500038750 1250 500037500 500037509
    0xc080f01080604030507120e030a1b050402030c0f0a0909090b0a0615080f0c1e03010929040207061d07210302100e010b030a030305040201030b060f030f04110a0807050a 74
    0x42c044428803000952207400c507010203800c112441080710078204203c800390400e0290f10703490b210381c3c00300e42d01f07102015807004040e041e905801e005003592402444145d00040300c03140d1020105204120a9685060003040f41030301d141740587e541525a007100003118882c0b201580d040f4840410454821100d21400c005403812000e00088800850001001800010300403000300000b000450010701483d0b0641d61900c1c0b80ca005071180501c2d04200d03c0c100c0d0000d1040e6020390341805c035a103104c902c07681203445014040b0340004200392040d0003408080d43c0051000c0f24001d543c1c04040c0c2e1021034034110340d1414140d1902602007945000503400124150b951141c11100744c041c98880080e4000a05180010080c6000b050388000c07101b25500625194a5181d0940504c003420020941d0691280b032080d4402d8904200c5914100d06100980c05140592589924108041101c1645c1c01d514298010b104080107800c1d95000d00110314580490340c407034102a40141024089413521002d00b50250 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 500040000 1250 500038750 500038753
    0xa060203150d050a02012a060207050d050310290c0a0b0106020f0309091b030705250308010b28020a1106090a150909060e01061107230a03060c080f0108 67
    0x1c41151540f07074035903a810354000d0501030810901c1c18561403000951f00008111441d07041c0c580740e241441c401070750180b4400c480500603030301d00c5603c1c41d01034801c3e603000d500303819156004581401403800315969980060b81e10111810201440c8825410040c041d8002e85005400e400e0020b18043c80c00142c10b070440c4003903404c0442184150580001601d2461204945882c00c6480d51040070701540405010900310384000020405100d0b08500180440a4020078101c042d003d03910700d560001d00034040c002c0c00900f5000c010021001c4400243c90040154002c0d012911003200300e8510490b014480134004d81c000b05030f80c406200303d010404034200c0c41a903c851801d0290400101d444c002030080031007125050300110f500c1441500000058500b0480070004103450740300c1c0020104092003800d00265440001d4039440b0f0010452008a4900c40300320b034a03888006070003031041e1140091264011080100000114400d170142d4205403895841c0c1c1001c5060417201c0401c5a04160040d0645 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 500041250 1250 500040000 500040019
    0x30b010f03052203050715150803040b120c160501050615070b0a020a020f01180c3317040602120c07050607030504140a03020f07151b0f050a06020315 66
    0x50920035107032060701c001400540c40000f5150318094905011340c1d03c01529540180d000400581d010741e110b403030f2403580108040d24960b5695080c950743d220314000c01002442c01d000110b207440190005075080b4101003821420450b14040e508100c0d08640c9050b90169164070600c081c60900c42410008120010f102c645403c180c3e440340a200d49008e420b409449e40c0c0082c4400405209000340c03120550410001e02c078140c004802c1c80d00c5103150480036111010f0480c0001480340004043c41000d0340600f11401c0b045400c000a02001c4080015507024412940d510024a14480c0001c507c200c5c030400d001626048030440c4410407030303c01041e03007214000801c843d070040b60f00000c0301684403600e4600401d207541c543c40d011000c80c4140038241d941d881022070f4042055004100035504540c80400c40da10f00e540c07007000c070524000c401103c40101c5c0c001c640002d00c0d0140042041211401805038401000243e5101440d01d001d411059400940c003100380b0040044181592006680c1158501358 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 500042500 1250 500041250 500041261
    0x906020309060f1602150703080f04020306060918011104080d030209030712170403081b0105060f0111120301151b020616050f0607020d02190f1203020d0507030b010f0305 75
    0xd54481c120700c036620010f0110304400190160b00004000c0c55010b080200c80003038403410101c0c580c0003502c1c00c0300480c0b00c510018400d2a44403002c1c80c03041d41c00500500c0152904024801c1039100a000c04100c0c000724151440b0a210034004d81c13000e01d41801c0300c50b6549203403481c01414044440100030405004020014044e80c0004100d01a42d03525101d50004a1a2380b8010410702c5520001340b0440780c01060010500405802406043e5400000d45a403d41250341c481e080b00c0d4201d800c1ca0340b241c0c543e140110720b54400c1840c09100004082120713004061541200403541090340f285110384503114820380040e500103d210780c0025904a0982c98002c6540090340707602a21800e0440c240c885106002405402c08c00a2000c038012000d84bc51402c10b090000d48404900e10316002500c00d43e0b030500075850b0241c0c816800241c020700202116007156680030703820050024546c1c1015002d000324840b000b400c4c0328540c000e560a46000400c2100d0304005054a070210001c202814070300302c100f04 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 500043750 1250 500042500 500042509
    0xb03072c1c14210a05070c060e03060f010e2e031211030c070509060d0f03030f15050f010e010c120906121a0f01030609050a09060b0d080a1b021801060906020309 71
    0x1440c40c90042a0030713150380f6881d40840c0c40e80110140600b0075503203081e0000340e4a4002014140c0308005900395905540c483c0080706a43c8020b00c1002d40303200c040740009180d00328500c40c0504002d800c0390906032038442d441030103020301519001900d107010322206039611540c0002c0805040c0e10400c0285003490801c0b134400d03072604814401c0c1c90007040401c0004009a0300c800364040400d6129400b803030a404a070600400400889046034109440c2000b42c1ea04040c052564208460004104c80018030b024401150700014400074035050140b102c0554001030017109546410000641c1c602c01c00d545031180040582041c1030051000fa0324040d442c074446007021607804902103041d50f608104480d1000100c00500c0d0351b9020a0446213054103120b003408070ba41106048500450301808044105410000c6400000300e00501006041104840c0d903402044040b0101d2070400400316401c006402142295030350840c0d45588042c0e80d00107100f07a60f000030380c0f031000d40003d200560400c170041c000714 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 500045000 1250 500043750 500043793
    0x80712050318010c0b0a1e0207020306060409020a18020d1506080f0403020f0327010f051204050c040912020f0c060403031d0a03030f090b03072c1c14 66
    0x20030b2050000305101140364010000015025808030708030040d440c09002c018000c062000c1c44000d0b20001e50b1b04001084c50b54001c0d5030220360020003622268586804010041c0700190049800840c034400c0083c60b0f1303550000b001c00e1201c9286c0056525681c0d10b00800840d614506003c20915002d0400c1c4244c0d40e0011501340d1202030820901156201c0c0d0409925101c0e5503120034540380300008a000c03040c80203410103801d01042d030000140511120f1f0045d55240206038120f80004e03003e0091160482100303d166401170300501c10355001f0301404010030191341d4440381c01e50b010050421180001d070f03030401022821100000c064222051010000340c91481743e448043e04102004c2c00c000382c0007a60105045001d6001013841d038a0aa0740d1034041d1042100750401e90121300e98010004083d01c8510889110f907401d07540d01c03060120008100303240c6240600c00316480b801e000400c8490340d01e4010a843e16100ca02c40002d000200d1494802481508010303010f400d40c000319450780450b400e200306c5 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 500046250 1250 500045000 500045017
    0x122e030b0c1e0307021606020c01201203100b210a290a1e180c02060a020a050c12040503070f12230a0b01030c080613060c0309020402030901060807120503 68
    0xf03903681c607078450891401140010102c05850401c40000305181c000407049090b810a0707c40402e52038803040f00360300c07410340009265001e0304020426030401e52880001e650110103009002c04090320b402e00c10314143c210050301d020300d40c4507081c03084405000c1d000b141d0b8002035050080c4500702c2c04603050f401c42c0f49008510500c22000482c0c0302e40c00c0d0f6a55040102501615980405071100d9801e911844c048500c51400b504204003242e004406240c000c0001d020455001002d041d00c4c0c042d6440002d503c405141c00400c0000d1103032840c1d6403011301282221080700380c00c0f20303121802c00b4205400e1040ca03a01844210b0b41040007000300380c41c0341c5460b0702219048044904c45680314400c5403244020500a400c080c00b52081000400c5070440c1c256050364041c1400101480d100d0301c1c155910030b4165580c050200c208500940000d0003030b001144a0780c40c514000c119203503240c1c04079041e81c00550725032440d6511250180041c5108001c000010044a9120f100ca68041e842e01c64492184040 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 500047500 1250 500046250 500046307
    0xa03020c01140702181e040f080a030908181f09090b06040521060a09080d110d02161407030b0406020c011e05060102160b122e030b0c 59
    0x30502c104405095401c140d030054082c4460000c004003421340b07101c003101e254221819a0480256100d10000f107544101d0b800816080241d1858035030700501e81216034031404241c0c895072501c0008510802500000c0900068045070080a07c1040468074800a41c001c40001588810850f59409541a01111040440001c83c6005900411481c0c46540c0103a40c01040240c40304419141c040c808955501e0524241c600c66114102c100096803040708028116030340c00d02c020302281440354020024481000403280c606400541880141e0f0031900240c00c06c103110300100d42c180501a0b00070106043d185000e00f980364256a640043c0c2d480241004d0081c582c04103040791042400d600c900708184803c264a48a440d2280032400a0302040307035014014024640c01419a24038103034680d0580303020030011170a25071440058000ea0a00a1409100c003d102043c442d00806191045140f20100395424a00c282941001540161301400c807050040d41086072481c1e03070303452846c2a0840c20507102c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 500048750 1250 500047500 500047517
    0x30f0f02070519050901081f090f06050a09060507020a03020f0309091f05090c0d0b040b330c010501030309060e241e0309010c0311160305041d07030b030a03020c01 72
    0x103e4000380711000d030700600d030006103600011031425400542c0c1254a03800c440035222041d2840d8040040d19000c1e04014415007001300d42c42d00040c0384e5000f041e40024101d00000e00c8640e1910ba440640300c080d034102c00540c02c079414450505a041c85143e05013031540c2c000318a4850a400401c401480c01446507603003040988601c000c1c01070b0004144000c050040401c0780c6810034419001e1940d0100c1c02540d00d240c9881071000231420540114110a10000c1009262020f5020f400007041d2480f490350110810002c0980901c04859001d405690121000084c0e83d41c10f520b00545040c49503004103040c403207085420605039a42038114140050042120305c00443c0d0b02510f50726500401c0800c580c100c80180c800708852036410003961042c0c1e0348000a002c00e800d25072003079003100d0401400baa95000c00300508880c04100090fc030b101d01c0c1c42032804906c0d00c2c1e40c03040f10780b800584030040180908405000e02c41516232500444020341012070252840015179500a5501c1600b2403003507040c0080c09 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 500050000 1250 500048750 500048779
    0x206100b0a020717012c0a03030b0409061e050106090f1512021605060a0b09130c0e040c0302010f0e1f2010140408120406020d0612030f0f020705 64
    0xb4060200281132a0390000b000201d01c01c031042c061703c40da03090b41400304014007420034040c43c01140103c440c06d4110141041074400e84044000e0310f00c0340381440c1c1041d21810000c8c0010268440c0c12480800b1385200c3c2070510006000c2c40c1030340c0b01a4440c00070030070250420b203c1142d0030351545088949064460107103900076201998030703100c1d844081d40c9917031002c21032081001000c0c8642050074402c00a81d401760f90f95158a8086843d240070b015081044040003801540945000004060090701002140d50b694194894413010855044a11070381011040046507080024018034040906004044036104408034026603800c60000b00304003800200901e0703075801500b81a107510412520f00303000032480415039580302740f210408151036103081c000340c004200e060000d40c059603001a0051910f0940b4850038070681d0080c00941e04141d00300140b9038000c020f80b003010004d04081c4060300c203946840c2000707070011000b1000c8900307010001ea10542c541e0b50110300342066403001c07607c600070040b030f1 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 500051250 1250 500050000 500050003
    0x5120613060e3106021602030303010f0e0903030606030c16080d022d0702010c0c0f090605040b03162309090609070609080319030219050a0f0206100b0a02 68
    0x1142080159140740910100c1d850900c29411445001401900409203410b51280c8400c400ca401c680541c2252240002d000540190014411209070034400752806005400003411907200b80e01440d5030000650003000340c0e0201c7c00d21107a00416990240d401c501e0820003103a903e10004180c407001d42c00002c0c07000302c042c0b041300b05814240e40188030907880b240c3c00b0070180c0095201c4034150450f0891410441c0e00040d01104031603144003409105828058140c4c01990580d48480c42201d0030310005da0041100098400f650008000e5080301058007032a02060104031221211076901a81040044c00e168854030011142212005001c145150492200580f81004e8421500350301250700300c144a0a5400003541034041c140c2c803820707079000540da583c081d078103000f845c03140404903003051020040300c0740000305060701400780d410701500e401584079003604c0c00149440780c00b0104002140085289034441600008802140007d240d241000090720300c1500140c45042c0300c00c4000105141400d10 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 500052500 1250 500051250 500051269
    0x90a090816121211090607150c02070e010b1303150209040509070911130303030f06081c031d0703060b120303070c0b071718031603051201080607051206 67
    0x70000094000340d01e142c502240d003400207035848000203805420542d00d000b214403800c00d825a0400300c035450f20001c40c1c00d05c8015000301000361082c0c0726080c03c07140d021689000e04413995000e41c1c0648500e0782010746100250006801c440007041c010700050400c10752501014041d2030704416070048800e19400c000000c0c0c403610f1040341c2c00038242801c0c0030412000007041b17000e892600e80c045c00a02d807180702c210304901822080020420441100304007090090780f14032154640500d0100310661220040741c0b504c101d0444002c105000d1454030f100345940340c4030326809400154200b807a18194000060340d50003050001400b0180e91f415190318940d104004044403c1c0c1003c1a42d4803440c2c0648080c241c004200400c1d5a40d10034a0002045544a007032052804009480000304a07115448400030004441070380f07031420f10003000000e102c0c1c48104003044070f080c400d64405030380704440304c0e20003450350060303025440c1503000d002405509034108065410240c0030030030b049080da444000007022004e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 500053750 1250 500052500 500052517
    0x6060307140d020420040b03040b070804032a080a1805040605030c28080304080708060403050301140f03061609090605090408030403051201030b180c01080106050c010e0d0e130b090a0908 82
    0x10028000800c7d000e501e024511490040120140c00e550303868040e281c1c448100c3c0c00400240000030300801d0660311880000500c0e00304084201c040e22160754107100d0340c1c0030328030070f4000c1804404c10005280c1400b54180103032405a0b01800903501d0880031941e0342a4840c1d000c0c3c810505801000d11042d004483c01c4400081c0c04032500e84150740b290f0b016104c0c0c0c440d0140509a000f4000041140b0b040010042c1c0a6989a586c1a00d50380c44c03d03465040c0000c480c1000c1d03500a06141c81320704c542d501000003a000da00100b1f94072901c8079008202414000c4e040c0c0c00700c14910f040450405c2541ea859075041da100c4d8010000e20358a44d101d1804072520311640d40312042081e940340001c010300c80005800c42c45020001d035030100c001400101e21b966001600b400600023003c0b94010f00c2068841c0c8040c00d06006c1042c00800d8140102910038104458840d103240000c10482420026160030022940c2d501d000e03c0c0200501c80004c0e0200d0440ca10082400d102c070380e100c0c807142d4200007900303040320b0425 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 500055000 1250 500053750 500053811
    0xe041812051b0d110607090501050d0504050c12160f03050a03030e120f07020f041a010e04110d20270a03050a0c0302041104050109092a0206060307140d0204 69
    0x1c05014805043d000300c40c026100c05105d840c0000d0b510718021030307046094806c16181c8074240001000e5170700113405d00500849550198104034881a10b0340c3c881483e40b4000c100c00740103a50415004040daa18403544507031406200d11204101059001c0340c0e41c0d40c10fa80502d80400c41c9045403c400e840c1c02108140141040000240590b048a01d01c000e884854821180c1e030320705040c94802c10050314030404142001000d441031240980d8090075442041c031f40080e02c0410b5100310100070302142d80002003116080360b142c12551060340c0c02d0400880d0070404590b442810000203001d82044601100111990120208610405561421071b0030f0000c691100450741c070007090340b0f44181d61056070702c0103d018a0900100d02420072000060701e0030764106a5800e08440d01e0074400740e002c0c040d03400130303013021401e07811083c13401aa00030701d0b01a045070150024113030360507d40f041c146010480e500ca0080f403105204c03054201e5481e85a80b80d40160111404104060a006401d00002c03030300001401c0f4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 500056250 1250 500055000 500055013
    0x1e05070b0f0415030204031110030f0207060f05090a050a0f050312160206010f0b090919050f01030308060a140609030106090f0b01170c07081605030a0e041812051b 72
    0x3400000038400d49480c0e4901c800c0c06443c804095080c1c0c0218000204250940c0c4115040c5040c40b0589c0540d41c6c0152402141800e4034056a004a0b40402c0c01a00c0e0301d51980003017002111180222504840e0100040c195044070707403140c035114a440d603c000c001c142d0b0030805c0b4041c0001001074031207140c90204180c14500301840960b604600c50003060016008100001a800c510412100c0442c0c2d0300002e46490500090100440702038010319540e104d00c140240c1342e81e40000392148c40d11500365600100555415424007074160240102036500c116107100c420310003249440d002a0801000342e40850700c1d40c0800c400207002d01115042400100d1a20202c00c03e03854960304502960942030300c505e0740f02d408a41c1000c0550b85d0482e005880c40100b0010361000a200600812125034401c0246250907410f6440038107585c0043d00000c0040e04503a034440045c582481740c0082a82114101650300c3c465668148800c0e842d0651038050040c04955030300010b1500c1800304d5041c1031203069803807 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 500057500 1250 500056250 500056267
    0xc04050a0f1503051b04020f041517160c03030b0925030e0c010c03120905030d0f0e060f060d0203061602070828061103040b0402030c0105071e05070b 66
    0x5100c4440401c1c40903042c1100039241e24a49041901501d421201802d1030f42c00d01620140080c00303c03100150082e07400c10068840103e404003402c041c01c1d0003820100e1174040300100a098405e9080c01d0080c85060400384241c290001090303c640d10300600705544009280c0c2001e4000309409203056420140040c10044590302420b6166802c40010202c1002d0003042201101110459246251710381d01c59680300c0030543c01030381c254043c28824940454008188400202650840182225143c0c404140140100c440d8003400387c40340d40c0d0352810454108101c46c000c0da5000e000d00341d0841c0e000303420040746030781d00c54120070050680c01400b140d400d414100320701413600d203e8403000030040c02948400305413990049000c8141d45500c3e000d80302c50034842000360312251105107040b6a055650a00603070b031030b10458051445103009200b80304061406005060800788141203046c10000e0030841c1c03a0005901e03021001c0f0021002002d40308005152400c90314000f001e4000710a640f001040008 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 500058750 1250 500057500 500057521
    0x605101214010c0f0503130f050706050405030c01031109040c201510050117070210060e10050901120611070204020415320a0225030605100506070f050c0405 69
    0x41c0304848400080018860480c8115030021039034440e038000070010004140008401d00c0344904450044100140e0300c0c0e503d43d0389601d402c403a03510800c04079001160411892078180100e2600c4030b402e08082c403841c07040e44140c00281c800c5405091145540d410400c484d41e119042c07400d039074a9030307d0a8800038200712b0401503031061941601d004030811440010403030000d0740c541504545045e1a0f05030314081401d10148101c100400b51b1045206e103000742e032f03040e1030240200c02c01400031501c030340c0103810282568456407100b42c100b80e008508600c010081140501d11381040103800600000e03420944a801c1c0c143c0384030f1581c01a601c1400440d0101d40480c60480000c4040c40d2a2155400d040c4000010103c14840d8a51501c50b0b6032074020581400e16100014150903c1c54810707940324440c200c0e002010115a0003085081503250300003801007103014824141c0200030400d8140100b880e1a00041e03940c882c041c4002e016602881141c02000001c01c040708031603000920510451601c0c42420 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 500060000 1250 500058750 500058773
    0x71e091a030f0c040605040e0706050c010b0a24170705160b0c0a18140f010e040e060910020c0a030c020a0306180c060507110f01112d060c0706051012 66
    0x2071303114a03c0d250340014149040d2040410450040000c0d103d06490030700151003d410180c5021165500d80000240d03950354400b080300944000030010f84400d05101101714141003010a10b8103005000d6a410f400308000300d01f4131781c05002032912660b02d400700307030210030040c5200307500800809101003400070444142000d0030796070b140d03540e400d410000040c807a038950400a00c641f4160400f0a406d02c441d41c10202001c084910041c1800f0003d8003141000c5000c43e010140c031f00001d60440803c0c86900501800440000d1000d07200a508002000d000c05464000004005080c009281c01090031074950440c07103001560048003c00c00001207154820607044401c41c22a08039054400108a42d80501c06a0729034036004090703480e14942c64418450006d10507600c860600229080e1201004803c009000149144460140001602165501009888040c580b620b508454100018809200107560035181c0141c400b0600d615035034110b500100381c0345c1024000c09035101d040c109001082401 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 500061250 1250 500060000 500060023
    0x9020306091b0d1104050d030309050f01092406080f01240b0306040b0609040e0c03060109050105060d0507120c020c0307080313030f1406040311071e091a030f 70
    0x103001d03a0741d581d000c2030310b0040300502ca049100070a00a58002207482c1d4030014444805214a6250644500006401124802048001070344078128241000000e00482c8060f100303007002441300418507036071059010f4542040429a0b00c02e0004c0141000c5036410000080c85000d0a6410709940e2134480f46c060f202d4000308010345006488030841503000b20781c1e01b4040314143c09104d0b007591206000c00010f4241e884440b54403100a101d204602e585034810411001c00003c01400d040900c6806e02d030510360160b016610042c070b04001003000703803201000c913a50b03100d00440004d00caa0b00e002099030f10720b80c004296038009285c14541c10382d81c3e40001e02485030440c02c9084958003643d4114903640c0388144400640e01071904403041000a010700f9020700880c1c8a600e048100c0e100c5110310341e107050400c0b14150005003568103070501d141024080e40003e41441c0c0741e1035030b610740300003001240c080070340c4034988095660b101d481411081c06104003802d030b000101900d0403002582c6013150f480051208 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 500062500 1250 500061250 500061259
    0x20283002121008070501080c19090b1306080c09010503220c060c02090a110d0207020301060909030509120304080d0503040222050106020114010f03060b0307030f0c0317032a1309020306 81
    0x100805d0960103920524803d032510301c22140f81c1820100696000c10700888003c060124030000030440c0c01011010300041c0b01c40384014054a0b00c0c0c2840102400006845030800b55410481190760f80da010b02201e0307102003100da022543e400f50074145130b00881450806008903428403001304000d940a035202105a0003255005400c3e280c0c01404400c81c2c0f0604594540c0da50104030714201000d154020304802c500003800007544c90380c0d800303100d4296400940c044000400004d25130b100d500d0201a264400701c0114020b5041130309041c150741e41c9005d0510080b0501c0000300c0001c0031503680c56140900d5031403982c6441182c0c4902d02c440009020280070f03200243d404d01c1d013503656802e44848024101d451510402e0300c207034035580f03030080180b000c03071510788d05401810700200201d0340203450402c019100b0864040c0700c1d46513061034082e58054480321290b58601304140410550040201d8800c2c0aa918415400c0402d444000c0ba030b51090004801c1003000c514000a1031510301c1c0c0c0518820034040d107 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 500063750 1250 500062500 500062513
    0x20a030305070e0306010e071734080c03041118090601171905071a04090605040c0c02040e030d1811010c02010804030320283002121008 60
    0xb406aa15a00e8000d0050700744e400980100500c03003142625075009a582c0c207180507010400c08104411f00b07022150b880c000c0541d8601c900020219500ea41420504400035090740d048044004111060242c0000c410340d03030110200f8140686440304144450000f0302006040307100b4440c0c8a41000101c40704480350155400008500140f9148442565010400f520150031a0030110b084044800001c4c1d0301031103058000b14207021102c0d40544841d2000c0328a64a0707a01e4800040261007082d00181d01460410400f0300210b600700d0301c10502590b0482e004282d00b006000c0071851405001c0458108604005107800000c09800f8046001c5000d55450340d01180d0603001074a10340080ba0000380052031460000d00840c1c4a54030148840213140c020000644034101800e84070340100e04c030801a00c1c0d4200001100c80415802130303c0c102da00c1d0800b89505003400c032a4042c400c401c000310003503042d04a0308800403441e03503034101e4003102c1c15241d103002c050030081d10000004526000d8031485220300c2 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 500065000 1250 500063750 500063761
    0x90b040b091605012703050303010e0702030a050f0d091e05060109060b070210090e0c19140f0c01060306020c0c091e0105010f0e220612053a020a030305 67
    0x801c8002c1079280d41c82c02a22068a03110046404000051a0040c2040704403181e4100700000b605c00401140134000654403941041303400400070303034050040c100399401004050340c082d07000b10644294244100100b5159400d60364844050206194010704440700748000b0340c4809401e14140c6c40700b41c000d0044412030b0780c070780d02c1150841d0301318000c01710b0360341c802e01840006150191032040c510311340d4036140d41c020f0faa80c018200c0b170340c000b40c2d500c02d060310021480200d01420305400051036040740c50510a40c070703000c103403001070741c4985000342d11240c400103155100c50800350440300040d544440210340e18042c40080c0350b210510814486e10032440c010110b5801e400744c51030600b01c2c801d801100b8085034604001542d134501d961b14402d05003c1c06c0d00f88061507640b0104800d004500c010a201d02901d400445282191401d400130105100040c0301040441d0f000264101c17148645801c0701c9003121140301e40d40c0303100c180041c1c8012001900d003120310441e5020400c40b4929120382c078140b1440d103e4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 500066250 1250 500065000 500065003
    0x307032405070809010b01230c0709050c07030f03140f070e0d230303070905130b0910030302010605060705030720060a090503070f0e070c140f01050108060901090c060c03050409090b040b09 83
    0xc0113088c2802c2c00110080c1540600500000c00805000030100ea0352513564280b41000da40301240c00e90300489001c5166820b0603089000d62850205504d0f04011154544003010700c2024080c0c101b4003624104400204507a014290780300d02032a0040040c5441d2110340f6044186420080c2e01c0032412050b030000140c20740c80003041d280500015203807100748504003414050707519640c2c00640860394603007403052129110010403a0107682246c2d1043c3c9520306508020382901e40035405140140d40070012000071440c040300b5100c1007a0f10241403116521081c280c0e0480c00715074107515501080003c3c010070f10b60380002c5420f0864030b040c5c00303840020b82e0f540307640c6440070400d10030442c0c25005c0c000064402445048009a030034854803844500c03444a01d680740c07504602ca0b9000b00640e540758010b004001041040580c044c000c00001e21141c402950b408003600c1251003a40240b20395090304d0f408040c082c40545015281c124020400b410482c200084000380581d8290703076503000d0201140500a0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 500067500 1250 500066250 500066267
    0x316020d020a0f03090504050406020d050c0f120402120613051603150f060f12020108160c0f110402070b15010207050a14010e060310031a060307032405070809010b01 73
    0x540c001e0212042c0366140d01c4180e03850b6140031010040000c6001c0390980e00c0341f290700d0066001c0e07440103032240b054070074003000c858000e461000a0702e41444071000c2d074443c0d08211410f00342d05241442441d03c0b2440070a00801c1c0e0200d1003a61409010100012040786214004900d80541e003150b02d075a07510325408000b040d55020203000380f846254080e41515203600320000d0215007690000301c0c03590380c101555554030300e908080c28940d0000c25020940d03074480301482d040030080f0b049226040b40c4640142c4046840ca034024040c0c40c00c0148542402000125842e040c60b01070800d41d51104180b4090309203400071198141000607074510805070703500c0054200c0a0b920003801e050080350030700c4030003413850f000c100703040c0e0421510701d40c040c5040d143e110140d401807100e0105c03008c6da2070451504041c1017201c820324000c1c4e0300f1101d040161580e000140003080340c0d005031141c2449140040c8082c540d810380b000b408155410002445510350b4806845c80c8100507080081001c1d80c03148004481030503 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 500068750 1250 500067500 500067523
    0x715050405060309160801020a02120f040e250302030403080906060102060f0912041509122d1e1e0308060909031207050d05010f031a060103021e031602 67
    0x10810300c02480281461401140c11403030b000200d40b4200080702000315003403801e800c4800c442e5004200c03113006c40c2c0c040210f01c00c1b040c4100800d0741459240d8542c0f010358040c0d446030380d40f0080f00002192142204200d4503450505501e0102e040d807c41c0e25000e8040c0d482664120001240900002c1e0b8043c0c1c00300390580203480c141d002e8141ca49820080380301d48000508048180c4c09012407015141140000903c01080192a200381038005088003401414565100a2403402102c9500001440c18405000c0003070300008860740906d02031f0701c604aa0440304400401052015a811051003840c1c4a01402e42e032080c00681d601405d001e001180540503141e009010603d0007011500c2407030840d85940d48201c008080382d0030902c1c440000d0442c54000d0311043c001c90350000c0c804d00f800e025802203c0c05800f00741c2111a01d20710715a0740c010345c1011405202010f05243c40400c0060388250105c81136140d015000c0e1141024080703541125a10075142e5681007492130302e2409400c0e0000c039403081241e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 500070000 1250 500068750 500068757
    0x160803030f09013201090e150a021204080903060a1817210906060301020a080a1a0406170609010c0e0123032502070819020f04060e0402030715 63
    0x6858540c0000c44590000c0c0c4064201d54881c42501850300b40c0c4402c040d400309250201380050f181e01c01c1d000c65840fa040e0002c25003c3d040901500015600180304886046007152880303d40d91650303402002070144040040458002c0070030b12050020b0900074014203d022029103810340c40d007910400445084038960f103a541e2208000d0400309030480b982135449801038030401c0c6090f001141c40440009200e20400300d8040f100c0038040381807820006250f014409400840c50042200d4010f44903400080c1024140740c2c5510200100b088a1141d1181c17644016206111850b2150841010071010418510a500c03410000861180050044903041e20150b02c8005d0301c44000170045407101c3c0d0345405001074810301c00586041219460045105035984207940c20050502e80f02c590b15451550781030011544801024407040e80e01207408600380740941e9403112054003510109192000242c100c0354024548140003d121043c400d07081d00c41c0d0f02c00c030103952800c1e403074421681c1e03500d1003804e446000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 500071250 1250 500070000 500070007
    0x109060912051212010f120336090b01141201030803180f071505130612060504050405060105040e030301080309092e0302101407110d170c160803 64
    0x4814030300e44254400742c0a10309840f2210112206460030358001d90803446101140ca00401000e1544031420380500000d8000f510200c90b140ca000307000507401342d24602491040940f034056140c65010741003107044d044203030041040e9a2031409004101220314a40171a0503880304d015500005400c4900b181811140201d059086131107503001c03074000038018101142c222040c0304114404014031500e8999010003042081c1c207119404510152000c030030f409100081c0714a0b0030310f04081e80390700d0650340e59103808004880b15100c090003030401c1d41d01c8140c2040c54082072005001010a2a5050340c3c0150b0b003e00c540441411007070f0380d9101c02d2050300780c1c0e03800070709ca00e480728a02190000d41000030312040ca0346004d4840200403049004558060403600a03141c204110b040c01400c003c1401e142c6c0c00c101c440c1e10810f009400141c4070302c0300c0c02020402c2002c1142201e507104c001c4044029086604401041501146424540d126280480b01c51054a5000390b10821300c990120030754111102842c01c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 500072500 1250 500071250 500071259
    0x8070905101e0c0b04080307090509060d02010c0c0b040b0903120a0f03090f02100f0e040e0c0112021e0c010f06030210051b010e0c0a05041803080a180c05090601090609 74
    0x214089800b500c0800c110714400c010380483c440c0701c1c82601690280c3c50f11952410000b202078008452a03000070b019100c01020820103945064004d84055020309104c1039003002442c068003008201e400090a4080108000c2050200d000c0905241603064046801010040008241500815080100050b101440c011000d4440d03082545054440c01d004100750304c0e9540064084003c2c822820000b442c070140078011300d54460a21070248109403400c01000c5081c184a907100c01d00c07070484d01c1c14007008100745003504840d941211020700340402542c50304180c68080003d6617004e01d460010560805a41c86c0d0f514a80d4490002103c0d402000707414143d0328400150f0380c0d5000345800d94190401c5001d40c4144800c04c0c042c1c6440040e0360070280c158645004204100d0700074a800c403c0c011440c004900709408645080072680a80500b000e000301d6172110b101401a1030b81c0141814849084400f40e000c00c04005000b8044e50402c513800041541d85800458080c1c0540c0704840024030345800800 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 500073750 1250 500072500 500072537
    0x10e0f04080f040f090906051e13020f0603040c062d031d0f0d0909150b07020604030f0c1d07120e0309090c030108010b060f0d0b0a150807090510 64
    0x30440c4074880c01420265600d0781d800d204c9000740d120b02903040c1c4800b80d14003001503c2c070030550b01c107154040c0c010042032260400849a04010141038080c081000d0f2081555540c000f5103410311070080c03185580740340502c0c0c8403a1080051140001080041228803034000031880c4041c81d00c00ca43c048c03066544000d1400b2009010403900603409405030020528454609100e28003143c0b030383c031008200410201c0720082080d503a40e4400404140b4012180600d4503142c1c140d0b000700d0303503407000c000e032141090300014106110f1680000c1212044540a01c20800440072990443d43c480c154002d1007501036007260b04584080b00c07140001035019040a10305040360344801c01c84024041102e003000100004141c5000c0300740e071134803048000440100b2544c0c209001d040c00142d000e446090130203191031b480c81c881e4040c0c00108014151180030101c950b031541d5104c04014003102074211700c00f110071100a0103250381a903140d0000b4078540c80200d042d06044240104d90401075032015503480e5581070b00c2 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 500075000 1250 500073750 500073757
    0x170d202a0a231e160f030f020105120712050c070b04120908030f07050c010504060801140f0603070c0606090e0c060d060801020304050d030b09010e04021c0213060e010e0f0408 77
    0x8141d82c482c8801c0c41c240403c00c0982c10320b5442c5016003228507840b5144901c0c260003010321a01e801a144014058107450032016011682d1008043c4403001072480140c6242c001c44250884d621f00304800c200b0181d0b400b03903c3c80c20b00f483d0315100300060b8845450ba05d006205841014094030607000200b80013990410202c000c6160600d40402040c0e1030b5607a2038255845040441d540860208005040c01428092052b207a03034242099854180781401c064640c000501c0344001e501c1d5044280d8449031035191420315408001814682d99180013040904010b440c180c054480c90315240d804206d0000510440b10340c1905500100805501001000103d03841403001c202e0303880d06d442001401038424006103014034031400c05440c03012951040101143c014041161050968400411050000008c0190040c0d015030f01020356406103180390a400164880094002070400d81101c8604016400041a02c1c0340803981c1c0a266641c003e4040c0c1000c7c03da0f8003242107561107005c5000503000e00d00a = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 500076250 1250 500075000 500075033
    0x81606180b4203160e1303020d0f05070b04060c030e010603030503010b07050c03240c180d11030d0302040914091509150103061b0c170d202a0a 63
    0x401041c0b1503240100e030402e5190010748061418028050150510000c00d9550000300b1648001e50100907490080d9154980c9540c10300f44010165410491481007003241c81c42c81c0c001204400504080c5040da0080c0406281307840020314003080f003400c101d018018801240c1d0982e03503090450b42400310074051948649000c079564821022856803d880074410ba103160803c8401c0c04100c800440c48004001400500b074100002c02003001b8049000b2080c4500429130068501013400d5160b4502a112050401c429540c075214400d154000280c0c1a0000c1c025180034000604c15500001400103126100351561303010f5820580f00f070031074680841c900da0b03440316580084580a640300461500111006c6e081a950305031540d40c6c402c501608001114903803107107450500540181c6450b400d44016140c20681d007201400203000c04000841c7d000350316403807042110400340200c620b0350715109900c800340c0d2541346c62500c40d101a0b421800021040040e42c400054111201c0b266a030700b034564040b501 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 500077500 1250 500076250 500076361
    0x305070512010f06140a0801140402040803030f1008030a0e09061c050a02100c050a03111608010914070501050f160f0308090c1c081606180b 62
    0x1141141c01e1000071101e00a000c0d00c0e400c544007070f00385030f4000c01900200940341c889070070401c625203a055001c600d040c1124000a41c0c00d0703585002100240281c40f80c2c0d44030120a21010040c0003001107038458643c040c43c102801704d8519640d036144640c890085000c220041103603603504083d14240918282d9110300000d00c029088610940c00246c0d8509100c4140c0d4264052101042142001409101c2000c11418244103401041d640c00e96100b03490a0300a042140c005400d00f00304d442046182d0021626600781080242c0b03c105081c020f001d615410355408102c625060844035000c5001c106544060f51511301c1d00003c20300c0005190b20101200c07440c40e000380c5001000c901008035001950b0320a80e190180c1d410030800c43c524020140e183e40e441004a40d0b0380d07680301c45148203210136071988084160388a41c0c01d8054807044c5240c0301405000241000d20001c0d05070f4441c2d40c8507000034440d0348181d2075a21000b0820f0740c41c03800c0e10301042102c038111360314503580c00c596000e03001031030980714 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 500078750 1250 500077500 500077507
    0x10818031806070606120c05190306021803010c050c12030708060105070f0503030708061e1c0201030603050f1c0201050c122e060e09060f04050705070609080909060402091003050705 80
    0x1504c820859410f680020f40c0029907660070403c118101c00d00000070201220500300d14400c1c4150520410060300c8010012a400260a0000490240b0410241a00800800900e80e607024050030035801480080024014401c0140740d41401400385c0c1d0080c03000e540c0b00c0066907a9000150b40a9019900645101041e0600000080c00400c01140304000c07030b60354842d81c1d09108051041000102d80d110010782c04480326880700c1d45400c05c0044606001e0301c00b4140c81440b40c00160010007050b0005030060150150448140070300003100e1a860045040c9202000c1446504a003210360550310b4007410881002006006003003c00c3d600d0f041041088185d880c1c41d41556070b9982181b121940201c40e4110344030030803126401c43c8280200180a44440340c00f0f01c1c1042c002510b00c000403009910841d500c2d4081020305100384195140c0980c4204200100402c2d410700d80300d5500711040083c491180799000640605050007900c0c1c0c2c02c3c0000d02084110031030000b00b940a0940140004100881403 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 500080000 1250 500078750 500078753
    0xf020112050a0204060e22020d140103050307020102070503060f0105041109040c0f0305160e062808040606060c030f1409130b040c2c0d060906050601081803180607 72
    0x51041d903006111601c0016921803814002a003000b4207602042e208401e4411182c0580c400071240805c545c100c0703440140d0350501d81d603600c40142207408080300c000c1c117048000b000b008000001441000d000340c0840e90300301e0b0b4840405550fa2811a00c4c0d2080762010310040105080c00c1d00f00403501c0341c0e68000d0034141101540410121001049450006182041f111505980510078150080c80ea85068a400d40e100b000190001c104d0f030742c100e8041c0743d0015880c203040d18100f00c0c480007201d171444800120f0191441c0100b03142007c0d101135030380c246030134030002c0c14500512001d25256416114504e40c582c41c5a0151822011003401001c851410000b140c00c6d690307401c0061040a0790b14400140c4140707200140002c85500441841c244a540040c80355282615213041c0c01d0035a50014400b400610140400c1e620442210001d00c4d0700d09085607602040419004144202000c1c0ea48114aa5130100d8400b1003e1039465074071080e4000b0805910703800b0800081589603030740600741c50301e0801503 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 500081250 1250 500080000 500080037
    0x30d2105070804060c050a230f1315020102121f0506041706153a0b090c1e01030b060f0a020c011e0207180905070609051804050a0f0201 60
    0x845408000510748400c010404c0311900c180480d810040c5045410f204040c0006040d0075448110311039a603113415500484034040100b00c404c1e6140d07032001180c99a154581001c2d2401950007148012581400048945441442035600b0649200f03c1080f0718ac80b408440c442180e601074210608070a001d501060307540360710303006000821040300c0620100c040f01d0862070514502070203000040300b00d0076510078203540d09880d40c1001402510010300004140c0c212041030380801c03400d04488032a005c0d49070180901190558070070946082941c045022010801241e095070a01203d104d0b0304807a4441405e5100e0380c8800d40303100300039254910b0910407200c0104950426030401e00103074049403090651396403081004c00320703200215802c03004040442c0042e40b00c001c180100d850358144100b09140f004850341105003040d410000340c0d48a65221000140030814a00616000b80c039801e000c1c095040d00702140364811504080948010013481c0c0d80d01c0c140b8048200107a042162024600f1819948d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 500082500 1250 500081250 500081261
    0x306040b04050106080a23040209071e0f0e190b0f0705011104090b0a030b01031b090c090603050718050f010c051e06101d06060f12150906030d21 64
    0x6503803174180b150315060b050141500c0b040c1d100030940c02d884c201403803000b51301080c280d50032960441d5402c000d070342c0d040400c41751196290005845188680100c1010641040d0f4000c14025240d44003c8451070a50a00c001c10720101d02518030b081c0f0f1074100704903554482024100175026040154901002c5480d501c1c01d450800c600008a180005002c2107000c040e881202d0075400151030984400345141c9490b00400740500c00034000f59a000303105000504000710b0b09000e011914000c001d1440d034400000e1620200c0d0140c000800e1030034012480903402140d603140003074039030b00e41d4005841c00c10003808010b280c0b50b08810306222032104801c0001c0d90901c103003035114090841d8004140440b08950f0b16100026060000708000c40300705128280c000c3c0c0e0301d109801f03003070300c6100525161480403400e40d110b42c285414181d1008141c001c0321030400804036015946281c08400c01030000010011000380680304250b140d40701580b400e03000c80c040e091001032014000c0c213002c512a00c03881c00e081541c4 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 500083750 1250 500082500 500082509
    0xe0c100305011403010b03030a18031a040b0105150a050c190b0405010c0813140f070602030c0610050a1509050a15030e010903020c0f220509121204080306040b040501 73
    0x2626180184a40a16503000f0805000d00f10300910050804002007078882c46460180020004201e00b4219100380107070307100d4000c44d444100013103c0000c010f007011250310250707012199080081d000084600d442c118619904003c8100607140c8140342c00b05890300c1d480a0480d00c02805007140b074001401d20b42c002d030b00b010303806443e0312200d6242070300e8900d013103070000f03440720703040c0030005060250200622107070310716503603105080300c4013215039008040c54948860012030580c0704449020a0700390340072000d0901c40d41410211405d6444088000224148600035a07411a50041041100c01c5014030b040f003621255043c4502501e0321800030550044403500701d0400000c0c03142d003001500e50716100d600b18070f4030110020460500345660094a941c2c140d5141e42c400c03920840c60710010707550b00c1800c2c4c40c6c00d0f40d01350384c00c5500c00300f4042d29400b921080300d40c0c2519015105002009074210b8084540b0b900000900d4041c681d81c0d9510a0841d81000d04150307000f80e640c50b4981c01940780c40c4103050180 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 500085000 1250 500083750 500083757
    0x512070303020d030204060e0d03031d070f080f030a0e0109090e0604020a120b070f0522240e13020d0e01090b01320f0d0c030b01060f0804060e0c10 65
    0x4604604000c1d10f802c8901000008042c4104810804154404131000c0f040c1030440e0700310007034100741c202200034102505210550020360403000c0003000c40000e04100711200c50788040d002c140c4d60b4078455158480c034546000907030000c110102001c2d2042c0400c0030710a005040114a00e9210307500181290007401c09521590f01c043d0a210543c6080034205004201e01014500103501c00c0d5140d03400c1d02c3e00506410103104160650900304c40c0203d00769440c440103070151048003003000c403100701d0651544c810012882120805d140c1940015502c035042d01002e506c03620052042001030180d04212000766020700342e4240025400c1000320301812202d111100004640000c00d410006101a41a840340c009030000c1d51040c001e503400d100c032021084140d01c084141d4018a07001151500c3c0d00f4560b91035121840302801002c000b40c0c0350007541681c3c0910304400c503982e200d40090301d01c0d083d440030700c50120b82040c00040003d503858000064240110f000c2d50700000c821404200c60510381c604c84800b1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 500086250 1250 500085000 500085013
    0x221100203040b06060403110f031023090a0b040b060102100903020102030f0a1a0d110402040b0c01321801020f0406030e010504030f11010624030c0c110d06060512 72
    0x34040301d9030f50903800c003004451a510b46880e55030b4803040160f400c444107002d00c03612444451a5a8280011001c40031501401d0001000745a0342e540e911501140c0d104441085d0000304242c5070002030008e4070954000e40300a81c50b180c035142c2c00c2c030410004210604510841c000e006138407c40d07000b0303000e03054071a80005d600d03410703d10f40c100d10749000246200c0141d0715081100c150004010614020b6031020fa80c0402e8418850800d00d051010807500650441e000003130016030101150011319030105044001c006e07018100e040c1800d14060116841000482c002821074000e45018020f90054601c00c0110005400428006d00303982003400c2e1540100e030b010804100942d05406201031b00e030b00c110003c0101c0d143c669005000041821a040200030244810f207034000ad096001c14054a000d4070011100199480341d80d034081424905640000d060075400c1c400130b40030b00c842800041d40205100d1140301c161080c00190305034440e05a40e400d495110000352901c4954001a40c600540c016001 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 500087500 1250 500086250 500086253
    0x70521030f100302041a030c1005031f0b0a0206010609060c0b16050d0507110c0a1a0f0f03090703110306090a0303022a030417070b0d0209040b3f030304022110020304 73
    0x3000023124504c0d000d039600c80004115180e01400312940100003c9100802482c0c1c007512010360403680c0c200310742c000320001e50928441e8000401d03030304a8070780790303a842c1005448070000c0b101400d55400c0107014481d24030109d40d518201c2e110914903000d05103403040c280342d207400c2040c054031800c0c0d9a100201d4aa05210080c8002c144404c550030354050b2101040c0c6450168003540300350802d50842c64074100810022000e4400108413400e400c5118040760b01c034201854140d444103054442102c868582248141403824040345551040032920090859045181c800760041d41c82a62620b12800840100f4100340001c031002d4a43c0c084143c0007981c5440c10808110300b00308800000d801680e11110080200c0700e24a81140c600035008880540c4800f640804100502981040903034810800350461003941c842c1d10000844986000c004490400c0d0907148168003001344200001c19001040050f0140c102400e44416041d40d00300c0e404991411200c109040500c1e51020081e42a0000244170 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 500088750 1250 500087500 500087503
    0x402031302091506160c081213062124060c021002060f37020a090501050414013c03060504060b1c14070203070521030f100302041a03 59
    0x140d00c11800d90240703520f011100c0002d84c80703026034020300c13242c040030b01c0b045000c101c20910024010002041180c145c0c685608884209400aa2141000321055100000c20b84c1c4980d6403107100c500c2269000c2d603400d20070040e5001a044c081080940c0013040381080c141d6411003815100203054070b54408031015050710401c243c04030400c10701c0045611080a200e101c0c018203404075042995280d030094003580d098000d40e9403056003644442003159000000d030f003240f00c0350000d11065000755035006101e80c076100151143c1c0642c1c042c0c0310b407100110f039442103954001c50721000003d800d80003c403110502c190040484441c51513a08038034051584007010401c5d0180a40000f904084505100b51410b00000c45024054640d00301c0d68410700310144010903840d40d02c07102e408251000b14415034544014080d64030741c89040f044030035104d4010b000262120020540001548400200303245403103220760043c24040103000128201e8101c071001005030f03070301e20462058040b00441081c4e41c00e508000c16 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 500090000 1250 500088750 500088769
    0x30803060d05071e0f081504050c031515030d020601091107080d060609090c0f03110d0603290903070f030513091514090406020a092706080d0504050609010c020402031302 75
    0x9041d4540e05c0c9420320024402242803005035041721407000042c0c0d80c07810810b00c0c001d00041140d0301802401c10040040c05c041160301d01c00e811100880000c140c0004c103155654681e20072110040e040100140030416243d0424819052807203002d030f0408583d500c0b108201d6100d20a10803005980340340401526230003a0991000340341160040041880d00600030700004c0400c01034070b00305941c803000c803d0500509070680f1442c0039040402c2100503168981030b01d91000c500755041d01a0324001030400109280c0c24018400c1c202c0e503000d51704000140c0d4811410b0b40e40e0541c01c405009003884100040c1c0f2044113150b0040c00e03086808611800564400c07c403102c3c03250013507000c1a846040c1c004040c1c1362500c13001c0d0459800140142c2d21885440100d84842080d04032540569540c480d4070a2901c0384400c0f0030510040b600c0030000181d071101801d0340c44500302c4881c40864070a0008010f580b42c01809001c1101040c10143c6105105500040403640115601e94498181141c0d07007065007001c0c03164 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 500091250 1250 500090000 500090009
    0x50f0f030f060a150503040212010504030c020f03010c090e060a0312120b120a140f010f02030a0b0307060c14070b0a11151e0411120706080606090604030803060d05071e 74
    0x30340418509001303107445040d0010740c0f20401d204001011604548405484407044031119000300614113080c60018100c001c18502a449200304003041140c40c034046c420102c8142c0c064480c9090b0604d42401c102c64204001c00040d072003103844c5c0000020070110140c1c10461105aa03a002496111000c1d9404403903007007a0a07070013041e091700e0042c846d84000407040320883e0051a217604800078050390a141403040828035440794240b0090311314911a540145014070f0595000744000f60914007072540e01c0c0789a106d800c1c0007a00440201e0081202d003018100c2074401744007910b17001034441c1c03007a01855010b29000d100007010901c60070941d1000380b00440078a0141120b42e8620708050942c885113484500000f6041c030703080c1c800b1404000c01d01c0030000d00914050414132041c00360b107448a032141c50a104000100d07007070b00001502c5281900842d0a0800010649420070b030568407614100e0300018101500032106100c840007084042060100805026141c0a460030004001c1420418523500 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 500092500 1250 500091250 500091259
    0x150c04030309050607050106050604080d11030703020a0f08160c1d0c04051507050d0905100305010501020d050c01090b0406020a1b050d0f090308031006030e060601020a030e01050f0f030f06 83
    0x10610010ba40082040c0c1120002c0b2180d5032a00c0c15424260300400050340301c03541c0601d002500241c005408600850301e20516110b02038400e4102c03958030745900c5105402030050300811303c18400640b010008200180c00b54072a80d0412103101d01d06000040084800c0d242d0303900f896001c000c26411740381529641c60510006000d0360078100c03d140c3c01400349020302e502c00c060503511132520003146000e4400742034008040720044112140e0180c800002409040c0c01745108030032480d89035020340900e50486006900800c080b001803107040f83c0682140358100055503d5640060104d2004002240150702503140103070b40e10903424019008200150705898403003412909140407940100e0b8611403c1d6071801c0900d240001c00508544845858000419550300441400b40c9000d00303005900c00c1e0740342d9071070401c0011200c00b4060f95461044800701d0050303202400c4240001d00c1810883d07071046040c10103d0401e13841011404141d001100c88070341c0c5030804010000300700400c2400369000401500d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 500093750 1250 500092500 500092507
    0x2d010e2b140a030b04180201080f0a090503041403160602030a18030f05010b03100e03070228080a0b0c161104110c010b09180a030f020c0a08160501031a01030e030705010509150c 78
    0x1400270300304032001440c000e490301c0f0550014842711141d0b008807080b15807000c25a0780d1551181c1c4203d0344580000301c458000c0c8105840c00c541c001c1c1003264141583e449400842c10000c040070112440e05007615010403044850f10004005404001d6107041d080c40340e0001f06050100303005040c0303040d03281c0011223686410080c0c52464030f10084203c0d1011070b0113441d0000c980000604510100380503502100000806240000b2a243e01203844600544030f005110240d4a450701a800341d03004803d1441100d00b081d0b5500c9002404520300041c000c0030241000c5801c40d800d0180c4030b0540c01c0a0b40d0036600365110228495246401c24005503c800d00c1403094103c41c00216510303503a41c541c6800102400281642c44821030f008100c1442039180c018281d07010fa680b9068100c0d10348040b0105014520407442c1c012445601a0103100381c8440d040c60b84941540040004601a20000410b140300303010401250000c03d9080c0620b41c0b080911038020903e07920a11107814105100510389040500d052 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 500095000 1250 500093750 500093753
    0x9130f050f130201030b0a080d08010e09030f0412030c020901180e030406020604121403070f030f050903160215031003030206070503090a030c052d010e2b140a030b0418 74
    0xe5440482143e02843c00040d044101d2000c15803000190300a0401c42c460380100809080d480040c003410703282c4c0c5400c00d100503203d40d1155527a030701680c150070b113500300300340000d000301c2d1003480b46014561f000c2d18081d42c0002035600400ca00c01400e0b0001f0b007800043d9020760401c1241130140e01024105100214500707803270020000d454101c00707007000b010303141ca2446001640348034460100381c1004444026a803400c000d100584281b48500c040008a0704001c0300d50101242846641e104100c0c0c680558074155403d9500400f001c80c819080341e1114040e44600800480c0c600a1880350b00e110079844103032402c60501070310340b01e80104800100701d42007003000303882c0307102081001d4039990606000444102d0380c641a402e0011105c6c12403400e0031403000008000012642120001c40b500c0020046034800056242c0c41e090741078545000c0d48181d02d0804c1200700800c209551200451400440001d0112541c1d80c05501c01c81d201130000b600d13061550100e251512501d08000e964190914440d00f49 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 500096250 1250 500095000 500095021
    0x3070303030519020f0904050109050601080f1e040602090a0506031e040606030807030201150b28111603060501120f0f05160e0f01050a030503190509130f050f 70
    0x12808000d08241d00d600100700303068441d907140590070643c01c1055441e400d14400d01c60241d004545c1c01442070341410000a1442424850b060140f041079403010310595441015814070b00b030161440c0b0383d0f00c4185440d6841102c98243d080e000c0c07445440f000d41e4820010040011480290b04128031561f8104103118410792900130200682c89814484c2010340e540341411740c004d207890760002d00b19090004600d42003583c1075000088644d030220a04000c2e5482e00140411402045144181c02c100182e10070054804000031100c074202c3d81c038044100e0503908014505047d031980b580c0d4801d4070340c41000d100300320f000e0284c6805070182603d0003034542907036101c401f081440d094020309038003200c0820400f405020b0280d1390020099205445540c0c1c0d5400d10050144022a81103103088590800410140307081c80e80401141d0700710004600700012081d91a0380c2c03070701408600c0c0c14808100905411030311400f5090002d10014040040d9082c0e28500c01070690703c0c000c0c81c030070394000090204510600d0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 500097500 1250 500096250 500096263
    0x307060f0c11011404060c02091012020105070203010b0a120506070815010521010f09180203060622090804141801060e060423190e040807020118061e08040203 70
    0x204100d210240c02d040c03a00580b14130607405042c04240400082c0072078950703002100c20f4081c03842a030300f0b080c00e40d56004140400c14524018806e840e0040d842c0440598854005056003034002400060608040c3e400500006481e40c481d80e0105090344c44030082c0b10003030180c60741c01055828024a10300c0c110540810200e01c040c03590313050000205028100c000c0c2d03ca044841d00c2e04004440c100355131110b04c101c0b0602058825034618a0030914404004040301c960b100900c0e601034020b0480d5103a540410100f41c100b080e03410300d030141603520602441c4981c02440c185600604c1030b295a1403c0c00c3c044142c2e4003051140714000c00d81040071070300310301009046a04445445c5001c858039113680000500d2842903612440c685294900c00130745184c900414400b040204440410101a0a4003451006010b503c02d8601d0110600d001502091031100103284051051400c8002148800811000400240c00450016208040100d41c480c290000c9242030306440c1400e01c0c4a29083d8002a40c400c0d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 500098750 1250 500097500 500097503
    0x20d0e07081c110d110f0d031a061315120207030f030c0216090519020d020a173c1302010e03120301090906090c0902030a0b0a03030c032d05090307060f0c 68
    0x1445c0c83e110b0202c80002d020b0f41500001e01800e4512400c5a500020f0140400644200c0c0b40c0d0201030340c1c5061803401c1001c980c607025050328403c051030f26082e10080996510300808040c000d241811007101c1c20148001d006d018030980b640307900b1400100004080303440d04002d02e010355000452101c40010920010800c42d000f10001180c0c580d582155811911354500d08091420f0010030b00441c0c401d030300d40160000c20310740ea07146945000c2d80030714071240d9902681c50000c41d588040d03850b420785070500401e59110409840440c080d100c500a81903104804641000303d071b44000100904660b8807003490f82003000704070000d0250440714072104090b0710040c81a0201e0342d60342d48960042000d1030300040340361904003404803201030365a10700a01075070041345d0340352207149000490842032600704a42407c1e81c3c0c140d80c030045242c0c0241e0f41900e101c2d001c00201c0044648110070403150842e014103452403040b40361350300d40c2c4400001c1c0c1454035044282d0004030501009100441940d68411071140109 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 500100000 1250 500098750 500098757
    0x250f05010e0924190315020301051302030903090607081b12041e1d090705010306031104052809030e0303040e16050d020a05031504050415020d0e07081c110d 69
    0x1000c0080c01810080000c182c3c560442c000c0ca0020740c51091400114007202e008050201080941c44c0605003284024040d243d4059810006112212010780c05950b011200c4001c482c58081c0c44000a05180c0000e0310449a60750b00054001c160540303907031031860b8074690304014094000345150840fa5402580114117214190002d50103440e0803400e0044000c140e00505040e0740074802d11480c440d04401c03502900c0c1071041000000351035202c1e03c14201101e4200b9000469070f02a0005c20001e068050300c40c0d840c0c2c1d0018170070300c00000b0f900481240a0b40050700300060400302e0380b0300a081c62400e0014a44241c100340001c01c0001001c0c00e0160344548032a0001d6508514190140e80d0750040425042c0270a2000c00c000c0729068100c1c000314001e1000a200f00d8064243c102004159402268010050084809a044200c1c4103801415102200b01008034484c404007030124a84002d41d440b1202645c00368a0200c00307101842240440010305252003520b002820580980d604c4000c1d4050040 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 500101250 1250 500100000 500100031
    0xe2202090102071208030601080c120103062408010222030b07050319180b01150914030f01050f0417040e060d0816030e01020601140a1403250f05010e09 67
    0x21680b003488a000648154070081440490504001110360003c4941c980850040400308a5540e040da0a640e00c40c002d2044803c40c1740e0a590b94040034104103407146014840c2d00700481000f0700400300340005018004001600da10361080f401c64a4542c004145000d0010036900344042080440c000c2d511140d00e0034019540e40350700c1c00c00c40e000b081c2040c41c2c166003854680c100301e264500544801d62103001d44010a1507980b80d425000040384880e185c03001040038680100014904071580300880d9000405891845508081c03103801d4480c212030606603440414100300802031080800541d40c100804c032241400c0c01c20421590008018240381e1069220400c02030821008004490900c842180c0700700c0c5a5000b4a00501500400c0c80c040e40540540c0c4004035100c02c5009600405603001400000c070b003441e040219000d280340781c02c05501405030345403009501900f403808550b07402070192032003415442d2440001c0d041051ba008241080700d41058402c0964480300c8058000c01450b010909 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 500102500 1250 500101250 500101267
    0x1503070203041e06030c030506060a03150510171005031b04110f1207020c030c12010f0606261e06040e060118050a0b06040e090f030403060605010e2202 67
    0x91401650b01440460342d001c80b82e06283e030310070b14000d02140e503140c07000e1080070340a0310280e054039011030759140c1040050000d140c0c1203100750482001450440f284a088944400205520781c450944441c0442c1c0701c5200e6401854110100c6a4440051040140501d080c000007a4456220460303d01e282c6e0341c42d10a80203da511036000c0348030583c004000c00d035141070014040156070840740d808000204500000b03001c0a0011480341000c050041c09045e00c180c4440c20400f9442d01c078820345d0700c01d40d80c81e40c4010010340144594000740550743c4545e41000900c07007160312a1103c841d240e00c200706035070003401a070b103440c0c1c0d0860300e000701340f103042e030b02c4959404011030010401001c0f0044140701310760000482d90050014200000108030040c443d940e0f40b2020710065035018950280c0015041004118142440101343d030050b9943c41503030202c10000003441c0c40c41d0080c0e0410b564181d40c50300100540c2d80c00161b4126685800d591080d260341003040000c40420041035a40003c0e40c00244114 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 500103750 1250 500102500 500102503
    0x2070e06060f040e09160906030b100b040b0c011b02070f2c040f0605100918110f030a050708060a0c0f0c080904020702041e0b060712030911030a030809011a15030702 73
    0x12901da21411601c084540e95421400207411144415243d6240d0000422804000702f218070054071011840f06240c079180008149083c0e10865011009550b1041001680c95982600c03181500d2550300404000f410f00c005860360000a60200e80500003854526202e0104100102403601111403005035640d504d0420001050b10088001c080700c0c035081c20004018a914646400d50340c002500300b0034102142150007413480c030848050300c00174a4445024891a01440f1041000350103400e80310001c041b5a2000c4c6802c85642140b00b15410150030455500710522907c600310369686030200b0070300203818024180820800b00070300b00040c001017801158071603404881000364064410400600d5a44031310400840501c03a41c00d0182c2003e803c4510f624100041c1e072151500281c0e00799039204900e01c180d00403c043d800032640d00402c5801c00000e542c06021800c0824040c3e01c40e00b4035450003011003030841d03d0220300318060143c0720382440700e0354075803000c0b07005524039000328140c3d203456541d001e9 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 500105000 1250 500103750 500103763
    0x3090c0d08040e0a1b05090105040308090a050310020705190308160203190e0a0504020304030503071b230c04180f1407180c05030609060f0d021002070e06060f040e09 73
    0xe003c071070b50070620003489443c0c2e0098154140d078030180075401c040d207501200c0c0b51145c0c4014a000500a100510100c0c2d01d00c001031148801c020700100020390f4802c040b0342080e0f03c1513510b00490f5400310300141485010320442034000c8120043c0c40b084600c907580940b200c4005805103980c000c9440521481600800c11900204043c2000300a902c06610004103e008407050b01800b803800118001114140b900076280900c1c0d151b01c80327500319614200704568a910b42002d20301850a40c044100c0841c040300c0c404000c040d28604421109042082d200e880c0000700020303140100e1801c03086c8200208400c110002035640003080e414840c0940c20254407800701100c040c520350003800b00c00541002034903803400d20314000c0702052003406140c41064896000446015402c803112000003019460004c00690080a0007041400340e009284c01064460048184000160703004400502002034501001548180200c0d0702d54a070406903800d900b614001c0e41700701c41c8545070240101d9942c05051044 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 500106250 1250 500105000 500105009
    0x60305070e031905100615141215190515130801110a08101809140a03030e0705060705031801021509070f080105281107060504061103090c0d0804 64
    0x2180c075a51071015010f0352990200c40304a403684501c000ca00f01e0b03001c15004e00411682005484002141d00040542d060003040448081c415000c01100544c010b4082a03d40248010b10b1042011592101841403014110450510300480040c08105a940b103001401d000d51200c0d1603140c44851320300041c00700700c0341c031341110003d035080a5464041d02d0204029092850280d81c0340c00d01e5480301092844191494003c0100c10a2945894080044141c0105141d90300c90f442e0105100542052242481801c500880c0040d0700c44000c0010a641045020050003003120742c1860441540e481c2c603681e00c124111700c0c110941c2881d100740b20741e00a0008207808407a43c2d00714842454160681c83e2114081e000d600c00b43d031140500031480b01414400c0600c151841241003520200d541c00207000703900642c0c51400380c84e8903410701601415024010308400c51003038501103004d003818504942a07540e91011102d9029041c810000400b800060318525210103440d004020000f40c1030415051013607410 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 500107500 1250 500106250 500106253
    0x90a020f09060f0342010507080d0618060e012105070308070203060106140a030e0f010606030605130c1d030c0907050d0c140d2703050d0f15060305070e03 68
    0x1072010f81c0da543d0200130361164040003880c016140c0c44028600f6520008203410f0100d000358254005034981c1001803020743d11050425509094803941c034030001768441c0c1486145152202d508000c410300010400c403c1600440c0306004582c1880c07440303021007405100d80521244107001e15480c1c43c030000300a582c05030308001079804054607818007040507807148070300301e00901c1130200004000707204001c030084910381800c4443c80c06284420440c0075181e550300c903400c0c6014a40d44214205424805c1c180209056180860705500e01001c2001d0007600c0b00318808202d06045550860a0b8403240ca0203004060300382001c41004034401103490301c03083c0020103410224100500030050307008409041c244886001c2440340c00c2c014041200c1e002d0030515141d0101e030040c0120011003199402042404c1019242215481204980c100074a0301d020f07030a602181c000a21404000d4050084245038042c0e49428007507461050a0042c000c000c0340704460815030780c1c1c008164400d01c15507040c80040d40090 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 500108750 1250 500107500 500107507
    0x607020604030f0c0909020108010501050901110d0c06201c0204120b061f020d0507020f0a03081324031a1302091813030c0302031c020306120c090a020f0906 69
    0x98442c1c11500f0190040d90740402402d40050603140500407030b108540c1c10394421980f030f440c003001034803580c02c00c001490504c0b41591503110030910801050311800126991218060703980d05148084640c1d00d516040755045501941d039002800c001124450040c0d0710b010f407000c144224030b001c0240242e0300300c03000c3d60405842d941c0c244100b2f90303a82c501552007268088a81c0c150140540140341d5208280009a085110b0888005010300054454940042e1103298510b065100088284040c0d410440314070700302080401003400844810809000002016002d020504a4100f26042c200c2c80900425440f0b50035841c03880da10700b00c480c1c00a64040c2c00e40c11081103c42ca01b5000e90051155540a5100403800a580044201e00140103441003403400324248000e490481c1c61240410080d015440100300406000c45070320418156001d450f01c0040c0c03203042880800c02d5650049144d00700941c4104100400b6603105508503800c00c80311140142e075203206007021400350180e0112a0751082c00131 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 500110000 1250 500108750 500108753
    0xe0402191d010303030c0503060f04020c0313081b030604110607030e061813020703081f030203120a020c090f07030e0c040c020303011a070f0f030c02121c11100506060702060403 78
    0x50301e40c9030690788a41c4040c000919080b40407030312400110307140c030f90000325403180600d181003580c0100040d0290400f40c0303151241403400d030400300d0b11300d620180d990b86c801a0b0520310301113056120360460100324080e204d242419241c080d0040b6040103c548078080000306001054006c90003502040c5014040a4a0344001055029142c0401450f54000c2400030342c0310101c1d1074140708591400ba41616080d5546d20392403e0011010070340a026640355644160102c0980da0400c00b1408545400b50041d0f9581120040241054080e10900340205815814001c050030142caa5a62046c030629001035149072a059052500721600035040c2c000740381032064420a5404002541a1015111501038160380200c0184051281c2000980103d81481e0100d001403080420b0b010031a01034036011107035510a4001480402c2c0d10402c55005521013480e03400010a400040740d891920b0741843c04d0039218440e134441d243c0c80e0003c41c982d8070039621000240c80c0c0c0d80c0c40c0b044d91100e5070040c0030030361259101d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 500111250 1250 500110000 500110049
    0x20c0a080a12140a050f0403081b0d05040b0a03021e16051905030702101412010e07080601091205101a03100204060905101b051c0305010e040219 64
    0x461401c2d0390a003040000100c16500a8080100744110300d80c80340d2a2580003602156a81c201018024188000b0003000010680071005007609a0240160031441074454826070702e03150b41d42c4070f51020b014040c00b0411000e10140280c0b0111403460501503561401d1030080e00110790b0701c4c8441003820340049409190070310203003900c4400c540308030201d0751401c68100807014002603519001f0000e610070003400005007015404c1c0c103055443d6003000c1c0d03003254110b01d5002881d040440f140d06040003d4004024480d000b811880d001040b9040881d05070034440c000034015401c50251001706e9003c14210b1040101c10442da40000e2003c00007007106414401c28001010714040945111f8414050341c030064005510848040300d025488404035146007005200080d42c000f030629041c049440d83c0030001c41d050141841d6040e1060780900302000c440c07000bc00740503070301c11a45e008040ca044014030500d020303c80e00a8207d0340484000c80103d00e00d440d00350582d00709410801e1040d08203c91001951b00 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 500112500 1250 500111250 500111263
    0xc0303020c03070e060901090e07240e010503040b01090b0f03031303050c0303040f030605070e1207090c0507050c060c0109020d05010905071d1f05031b040516050712020c0a08 77
    0x2000c505540c08903035160310069003040150740c5d01d6071114040c801000384600551120000d002e252051340c90150317440410188440c0303e40380041c000d0844c1d5002c050400c0d4030a40a0205510900b8604d041d410140c07200529110140100b1405507661400e4080c10368800d035040c50a510000c046aa03240f0500388640e00c1442e40348401c490034841e42244a003686000b0054a056031229158581031034916102c0c50064400131703000b2424012019800c04403a2140900e0715110b02480c0020f000711442c1c48840c5040f1600000003d013003200c188510780000364041a4080720550440e4015100d01643c5801401840a00c10080d800340c41d044d0074000b003040640001d4001805801510f0090b036568008207068141072450315800841400000c61058040143d00b0045003500902d20045450700d000c0f0b0303d08100800001105056401d07480d030300b0716142c013903039a000b81c0250803100c8079120080060041d02941d480240400c1101d10700c0041c0c0c41c800c00000383d01ca4001001c0c03060701590750306030580303800 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 500113750 1250 500112500 500112523
    0x6201f0e0105010602030a17041704060503040302161505070c0b0c060403020f12160c09050907050f0315040f14060a0f050a15060f03061a0c1902030606060c0a0c030302 74
    0x50a080002480e11700220a4400204281e00c9212011004541440c07140d0002041110401e0448141000d0201141d02074400b8100390744443d903a0313041c0350074081e00e0b100084842a40004a4200a02141d040c0a03442a03101c425400c001c0e1311011a07260020202c001034015040c842c0300410124510140000c4a5005a00940a540081d450000305e152900201d61000c492400e04000040310303240c640d5440784905000704901d50425841700605030540f54262180907180d030000302c0030f100c0c5103041d01c00780104900450042401400011a0840d030410040015008450045541081c8008440d040220341c8509054448901d4403000c9880206014140c601c0820701d4100002c102135118456802960303060b2501d521224900310041b14180448041c0108050301c0303c0e0300141c2c5101030130303060010122115a040c0c60784100303201d4078075000f850300d9800d4181c001243d100001d070310041090ac1e0401425684269584c2d00e1442c0b071450840e001200078141e8440020000625902054880d0103d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 500115000 1250 500113750 500113753
    0x11b03020403120903260705010e060105030c0109080d03021c0212040b24040203060316090902121212130f0f060f06050303030a0b01090e0702160f06201f0e 69
    0x1600d0b038080c1102c00c03107900e000040004407040c14201c2c2582c2146032002501103040b1b0914034003040e0341c1c1d42d1825644c00b20640d0086a000e2001400186024014030407440c0080c60601340d09440c000c010356490786022000f5040c558005081c140c06150725030746d00c90521b000803065689904e0300b40d5225000c03400312403c1d150f081000300411804a20030800381640100d200210140c010b8040800000703602c081d06041c1c0c588210020034000000940c0504000c101a03000000c0d050083d006010044184030017805c4207801040070f24610f1507207402900c0d030114110000082d04da4411006e402c0e102c0340c001010308590b0289622004120b541c003030f0780200500c0345400340234020210705005d056030ac41d030240030350540050000529240d2039500000071280e0500d809092544d98000d460150f240c141c0c1d0620050f04500d480551407800046103000401182c100700460a190060092603420102da079034400065400741e072882640c00304644104920301100d02041d60031400c0307000e00181280c100e0060b96 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 500116250 1250 500115000 500115023
    0x30c090501051e0307050d060f0b061303120536040b0f04110405090c0a110601030f020108040c18060306061202031f091e03110a120f02011b03020403 66
    0x8462803030003564101c920151001d6440c0c2c0c403018904000c2d0b0101c00308550140304203140020706a03903840d4403514580c041c1d81c00241460780304422409541281030500e00411040203581840500c41d104042100d8218800c03140c0703000700c2c41d01200c0501c034a80b07615a03840154440007040e25045c1024030303500c19203c1a200c20368140031052205890342140c4855014150a001b26404d00300341d00207c94541a4154240c5000c1d00c0e2070010765041401e80e1001d01d043c03030124201c2c00c07c1d5080039103907240c410103400030000c1c1e42c074603030b90b01c1311406000074020704001115000c142046021040840a0482290321904104540300040020300b51840159000c40c04e0800010303803c68460b141e45d100c01d4000e0082c111a98001d0744d004c500c20718142a0341e000d950381740c44920204c0d10f0059800714140b20426420450801c0d0704005096960841084640360040f0403c0c0000500024a060901401d414400040d0001c41c4041c0e004004000d440202d030310719429413280c00b55150380280103403481034510010 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 500117500 1250 500116250 500116259
    0x1e0504030209040b4f1505040c0b0f0d09060e0a11280501031805060103081224100302091906030c050a0801060516060f090c092307030e0f0304030c 65
    0x401e5075000034400c0b5036000c1d10040b00e07003e1107145006801c40790385c01da4030000b1011503610075180c641102c418141ea19500d006200410000201c0c50000b0881d90b034503181425010344415a603807089140542245544442c07035010040d0a4122051080c03501054a582c0c0b099410143c0011f549010303168841c1010001c090010002024241140c081d46a2014009410100103500420080082c40f5540c040a004900050400c008440c0a50311448440c0e8440c1c4d410400302c079482d0f030041c0c00b98a925210300002901306c0000c002503064203400710350303080c0710034000a0305130000d06c42e000c0c41c240c000c070f00d113020840803050050003001141c0b81980d00308952460460222054001c04d01e00b400040e4250004000c090300c9000a458290b080100501074807203030b603944100f1a41c40340c08110301a03071140d01c01c4042c014070030040381c01003100c1b20b0207000000070544070040403818204468650440c1030046102d03d44242e2040d0000500f03002100c4d024018441d1060780e940142c4400ca5404520440215 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 500118750 1250 500117500 500117551
    0x130b0f060a05030604090816140d0f022a04061202030c01021501030807210206040203120c152502160617012303030d020408070b03071e0504030209040b 67
    0xc0305820995101030039500d1303020400014280444064551410074481d0084080380d00b103800ba500c40c81500310715400d10070311050300d042a0400c0c44200901c80e034030041440090300807440c200c0004111929412104030023200d40004048420141c0c1c0142c90182d000c540094050788949255001310200e840c00100c80c001240d941c090707442d038010940841d100400c00206010054050703181300f0704c6e0040c1403036051003640341181c0440004030300513882170080c082503040620500e00d4089410981d60b01d02200031101c41d5550009400b2203000c006071000040016000030100240e952072903403900710b100940000203607900480185443c00362103c01c00040c400d402542c2c4441250208110000b46a203844202e40088600050141e0304121480c200b4180303030750900040401c441d9903507005840e83e003410043e5151249640010001d07501c208140115181c206220703540070030b10310f00201842ca4035024103d03414000d42d4402504418800140801c0050180000d4403444182a0500d8034010b41c0c802031 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 500120000 1250 500118750 500118757
    0xc030905060c190807020c1c032006010618050a030303090c08060906040305030903091207090c08190917040e01240c08130f08011b05031023130b0f06 66
    0x110f41d10300c142e80310a10001d0283d00070750342c0324207540152040307030781410f000c10100c0c0c01c04540038204038101d092120815800500801410407039039410202050f04840e03c82d5205418040c02c002d004d000e50b2000c01c03844c071495140003e8000a0100d542e01503407450050054000071104030f4079481c0f500c60210b2580c000041c0c0601c02c600b010010b01898855450035a40c0380c0c4064440c4656020404c004401c035103c0343c0300c81300c003c40300800800e562440c20130310300c01302d40c0c25141d0700080000f04002d000140444004241c65a81c030404001035074a440e24180072003071b00c9100c150340984ea01080001e240301540c02124122510035014004003000d4100c0700c0f030b0040e6011002804110703d00c2c51100418242406806014590103040b04020345403104001d1003241d40d0f21a4023103039150b803505c1c0149141802d80c1c02e16000036040c02421420802c46041040f07166000d071801c20510a040300d8120803100303050410380300d00508056072600c81085060041c24091482c1070003180c411220382d02901300700048 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 500121250 1250 500120000 500120017
    0x6040803090f1f030f020d05070f030c03020c0a110a0806190c0906051c02040906120c1205060106050c100608030712021b0409020a052d090601050a0e0d05010c030905060c 75
    0x3156940c039070b403e1090300200002107006175140d5007441241c0e5843c6051003110701038280c94403410b50b11104548000e05440078200c2e81c0c1d0815005008110b20040000742c1c5141c1c66511031a6901c0d144a000c010a50003000760780038405c035101c1c101c107000b40b400820b44a002450503d1006010803000340c0000d0300e10158510461001031810415026203101c00b03143c040c02d030880c0303540151520f41d4440e804c80584643da044640000c80d00c0c1c680104000d0708403021001440c9281041620324250f454460300c801c41440740e002400f0300046c802da5200001d20141c10300c410760f20b03403c001c402d4980260995035004200c08075004521f5031507400b00c1c10b00010f0b01107280b81d003641e00d90030b407454407406110141c030b00003400301c0e0046c481001c040b40756910380a201c00483d40101c000b011b041441050b401402e012440803030b02405020080c000707a81d23404402c07100080c4031030500c40940203640020071006402c1240c098010f510b0400c401c0744550b071540000002074040c204540e115200d00c2401501307489142407 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 500122500 1250 500121250 500121289
    0xc12050406080a0b01112d060606091011010c05040618080c0d0c0e01030b090d0f080a0209221a060c0706030b1305010915241d06040803090f 62
    0x10f0107410b000d03003040c0b140c198180b401c2110161014040b80c94403210b0390350030808400862207904903141c034405080d02e464102d0001e203e142001e501103171580c8103507690280242d0346011a04100303030240c0000c041ca1191a070003005038683c480c100070f085401c20b01640000940c0c0440c9850062021810780b0240c5492402501d0594001c01c1044008540c08030300702ca081c000b1440002e20b0001c4008494005c50086954001d2440c0142d421402c1c000110259001c1c481041c402c803039500c4e484031040350322411450b8010790740c0304c001000070203c0046103414106010200d9449840c0b00e400d400003103c0c07101640003908001840020041c09010f03e140c0303a0820b5000d44010410540b083d0094820101c5c090b001d4040c86414a11580540d1426000307041c6042c3c03110802019158100144e40080c8990b0500325000498180316407003415441c0001e1041112940401d0b905220000d20724403c010002c12441d40c841d41c41031859203a40005483c0b5100312041e0ba0300d2001070820301c1802172082031184 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 500123750 1250 500122500 500122517
    0x180b03060610110316050c03060103050303070e0a330e06090409030e060c0109021906080412031b1e020c010903080d02040308400302010522060c12050406 68
    0x502120038001c0b5105401c001049900d0201e0391020310003032040201241d491003501720365042013441c0040c9050410f020394006001000881c90110581c1d802840500d81500c010710340400040d20042e0f960440350070030b000e204000529003175800d03103404940c440980c48510481121001d98900d45c0c00c21107560001c10400500070185821b81c001041a0310078109509941c2682010407119008003200f904d40342c1d0755401702419881c0001180c2c3e1016804007400400e9070818000404042001d04024045001d070500c03801000c1c041e401031001090b12002211250303800381070050910f0305424981e02c501c4034207203e07908043d101180c66034140b441078580d85003640c51507441d11075a512052100c110316509120200010b0342c504c004005103420036a1208044003002c44000245400b4810038000303c1c8041d60b034020084241708d40c5001c407502400e19070344071841035404141c4010200c0341507007843c507402c030701180e056040092040036500a800622200c22841f03015143c1e40700714001c0318003144014 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 500125000 1250 500123750 500123761
    0xe0a151209151518050c0714010905061e011202010215072a03030b030a021507030e0d0501060f09090203032a060403050a030c09050f04051816180b0306 67
    0x50300310401c894482c074407205110b904240010b04903100780b070900036121202d100030000e00341c0451000360500d142c950100300c45d05203c1035407038151050b4003008081843d0522401d038002400e600040c201c43d0810241d841da85000902401540e98102411240c01002000070582c140700e41c1c9914080396040c0c00500c01010448204411080d00510210421500d589100d00c00100c10f1030842020311400240c03a03e040145c038011303058452540090780030f980840400400b580e81c00e0303800005c91140c505030644d04e04450604403005012581d00e103400c120f807821102c04001c81540b001048480b610b06551116440340030308000e454040c1c1d0040e51580c02480f034010b01101c4070103480081d0961482c4070f02d07000c031160001c0c1d08041040300c056002c94804902031204070340601038684907010f14580400710394100400038100800203c103841c0196a0348000444202d05030030705000c00144101100e040076228410345074030004d540505820880201030400723185000b40940c82c070080e8000c01408155488 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 500126250 1250 500125000 500125037
    0x30b151e12012d050c3a2712050d140903070203120a05370306050102070503210c0c1908100501050603070c0510020705150108030705072903070e0a15 66
    0x1141510a441b2400c54440444800594100c030280718143d03000318000b141c0700d600400300714402d250003103034580c4240140c0c00038104083d4404e005100381441600e81030b072040000028850030a43e00c800f03295800034480d41610002c007520a840c07003101152401da04154024095024030a07008000c65000d1010500f03402440d007401c400320500f00c09000e200e508000f40b0b500e070310000250311030110f40d82d14002c1c016546d06100c80c001819050300100220003030741c414000190b44140011003942c178045800032810ba001e020318006c541c8010701d00f01e00459904e082580a800c2813195005074402e01004403402d00b5580901c504a4070018095030865458a40c265511072540c803040b03a90740a03401c480f500300f5505101400019004e0802011028803c0c0c40c03049500a040e00000c03147d03401804203400103180000c1c1d2070141d800820403008035490100404032000d414a2400e131030b4500100410000b2030780041c6e06c2102e90b000f00c820914295440b010701d400d00c0080f5134810005180c000d0380282d00701c2e4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 500127500 1250 500126250 500126287
    0xe1305030904060902120708070c03031a1809010b1009060c030306051512010e06030c120a05010501170c04060608240a060306030b151e12012d050c 65
    0xa041503a00c1d0480d00800a000c44455030081c00e4080d40c0450000321018444041c5a400300c0c02d410004114200b000740a401910320080040c2050b40ba014111410280d603910300031400d0f005010003122481da42d0a071404901704940c412510f610f48400d14000e45405003d002c050b240070340b00e18554905181045945c150601c405505041d00c4080004141c4c440401c0d40701c44402c410340080d26112088216a500c02d010b90154041031410700c103000d85c6a401041c9050303034150031101d802c0902e0500003003500380b0340005009002c651034000009034480200c02000030784d030710840541c0c0200c61480100f104890541c0140000030312441c0c0041e01d4560000c9000007410549000011040d800c0ca0000c2d4103030100340c005800013900c44404004110340400e02c1d903004198901040c441d1240000407958044200305520215500705402800f90788400c240c42c8200445880203200190305051401002c1c8401c3d85c20310800030220038940d141503031900c107040c01a50041c110600d841e1220300c40b8100d80c403 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 500128750 1250 500127500 500127503
    0x10804021512040c18090804050d0507210b061012020c0f0f07050117130816120e030705120318010e060d050406180320010e0a0c0312020102040e13 65
    0x481040169040c00c610090b06210304d1088030a01d20003418116804074000c04180740200280c10140e0708000218a0025903003658820341d0108030b001c02c81c1c10124981040c941c007140c103100d40080401c10076410980c0080007030340103e003605c02e180c071964180081c949242c0440d03000201c00d1140300b10340051711380042000c080d00310111030441202c0c507205800e02001c6580d071225940424410030403540c0190301c0241d070a403102400140d51410100780340d441140c80d10002e105041c00a041c180c403c03044100c0402680d04038010400440f008103000d484401e002000034446d209550300040c05203050440304001180090140d41400c1842586010090303980006c203050081113a8017004079180d92010b000c5484c4040030110750790030030f410103000700e0f001310307104607110440c665000780400e4000e02207124204001c04031840700c610800b0300b9401460710041d49016070050205907018082140009415030303001b40c2e4030207408103200350164200d22503031041c02122451240007410600e0401b051141c0507 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 500130000 1250 500128750 500128789
    0x15070f03031b080103060b0406030213020f0d090b06210703030e03030d05040c060320372f120a091d190c0e0d020a030c060e0306130201080402 63
    0x10710401203580e1500007660901000211484010002c0c00461300401d000700c00156020000300e404d68020070380400358800c4400c0cc1c1170300050521011100002120304074090440c040040544628251080c124180c4299110346901211640391426841000a0390708044000b0003a0625503582620400040e036001ea030305000c00d100707081900f0303010302400b17100c1c6101e40aa058203904000c0f01800311000c076840f45260150444400c0810007107141114624205c0b2454000042844108403200c1003a2056122100a00e00105006103410004140001e241c028412008070f0b06103006d444016007100c00402168032498070180c0f4861030f00018031146030310745020301d03619807208413114a86e03141140640c5105543c0f01040030a5038141d0300c11082e1600ea5070f06000056100c03800401141c2d1000181e44a560709484ca134045544848250000315032040c40402d100b40c0c0c03407001905c00426001c21074064011100003035071540998101c0c19260354140c48105083d02e8580034400b15074440c1402400700e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 500131250 1250 500130000 500130011
    0x607051605011805070f0b0c0303070e0d021201050109180206041a0d0e330f06010504030b0c030f06030604320615031608121e0304030e0301050615070f0303 69
    0x4020302c1c0e1600c000018020001000d82c9864000d40481b0810b041d440080707116028401201018000b00440c0d41014a621303020107807a85020004a4440d80361100950005840011031010103042d00014104c865480c3e0030054118030b03600003011200e10f014001d5110004120902c0030780e408000701054103142d05061400c0030400b6545c0022110b401c0c80e00d0031207038000c131801c00480006007074210400c00e014500450311100781504403941240079200c645021050070000d040f40e4810020344009680240d0b80100d5814a044e00c80c01690040c1c661910f4810b070140010860b060000b200344c0030b00e50150006420300d5514280b442c0c6030a08002d404a000c55482c0c160318000710070081140a029043c0035244401e608000f05072810001d000142c0030208000e100f0044020080348450f40460580c424a588000c401441c0c160303501746541c85c0321001c0010040c40141076010b034112030004c00c190020481c0e600c0c0c440c10841a28940e18010036070300410020080010060040500598820b0501152 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 500132500 1250 500131250 500131271
    0x902090c03040b010506090609090c16030302030603210414040609020d1e0e0a0f0218010803030117030313021908030a020c03010b09090304051012050106030914060705160501 77
    0x54204003a00c9030016000080148010701010000c2c4a0040c503048880c0c130f20307203442a400b0990f5800744e0040d162003041000d0000b45041600340455000e0012000c0103245800a031401900139041036600e00e0192080e0440c086090802520a440a40840481034141890b184140390310000c00d034076a981103074447c84001000e101600190944814800c004980c00b032050039010035000f02800b1408800e820028440d0603038101188240505410404507105049580041281c039401c5585030071220641c03000020b038071040400039505807200860640105444080d40d1a83d80c082541c400700c42c0c0701c080d00c14030300502d4035595190410007102403e05490b5a103032030b61800d64001c500e90902503003000301044010703d03083c8540544084119840000b90420081ca21741d00d026901071940500340c0225154001806160303071403048030394074006000035a100c5200902074029120215043c84482612034091100070449601c40c80d03190f660302e030802c0d0034007045020910710b070503050703c1f95541d800d41c101 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 500133750 1250 500132500 500132509
    0x10030b010503060f01260a2910090e150a0b010908061b09011e0504260d030207020112230a0219200109080301080d0206010305060c03060109120507090f02040303050d050405010902 79
    0x11f00341c010349220a90140380300c00d0040e400a00f40712107098000040810550005a0b8004400d03600303040c0f40003e0000c0b00340700040c039107000302c0e24181820380f000040010095a60b00001e41100003a80d8000c03403a4ad41e0f4115507038039132081d1421081003400c0d10b490040754902c1400741030702e060140750400710130f5074603417090048c5c503030804205e000244002414030442d11000000092980d20402c080304da605040f8802e1b40b83c9194022500030142c00103021000c0da07210303118005070045480b60802101c80211401995074000c43c90500741e81c04554006003544100380b003030324046603000c0841a0782c03001030001244d0030810b0003c1b103404102010341451b8408400d22510802c540f203180542e0752941000c000070715110050010070115800f940042c0001100400c04581200445405035284e442d14001616401255003001c50303030180344601c10040c0300000449104036400c0ba00100030312005c041c14841607105500015011601c100300751182c1500c19400654054060780001418450660004 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 500135000 1250 500133750 500133763
    0xd030e0910051e060405091003300504060c0b04020102030f040906091a0105041202030a060e0607031a03072c0c04060305011d041e0b10030b010503060f0126 69
    0x80540c0c1000700000e1016040c46480402121118156400861000b40014400344a03501516010b20410404911002e001600c1c0304095a884007100e54071141482d600f41100003007040c500500c105050280090b00e01400032542510500d540791030600c0310640b40ca070b80100e800f50040b8110720042100820441d24403002e000038100c0c02c000440c15504d4185440240e0303458403444640c201ca90100500d107aa00700c01110101c1e001044001c140740400d0001a00b40031080c3c1002d400c0c0e600301820152410804030740c01c0e109000e0754608200d212a80c1210b81a08110800300c04e4065001ca070090048199007001d6000f801d403c8183c608203543c0311400f01c0c1410306c06030350f07085092002080504c41c00c0c0c1c05008a0b40580700108010451032441c148000c0c00100c0030b4005000c10301da46c10841030b4204580c5050783c901c2d0300071030030301014248040c008070010194803040d186541d0f980b0006c161490042a158045c00d000442c3c1c0b040c41c0d0808020080c1e005030031407a50054080b06481d14204441406070 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 500136250 1250 500135000 500135011
    0xb030a0b0a06060e270901060e07090303120603030203040512010207050f0a02100e01050304120c020901230d0203030306100c05120a031d0a11010c0609050313120507050d030e09 78
    0x450003c0c41c1080150109003040041c1e44107000c001e50303c82d07414110001603c07500d00010310040580c2c840340c0000b4010300241d0000010070800c3d1040104040d040a88102140c1c402c5d501c488103c40c0d808820012a00d1074040100180c2080004100610741140343c210160303281e02c00140f44c40c082e5910b213441e04071a1a003402454106541c000150303d4a800410b4008940c0c3c01c0120f240c0e01c034000001c00c6440010001440c0c100300301041c03080305124a03d00405a640071f000420742d540c40e0007800b00105032462902031605e0340b080d026951810842d0790204d90315030240055003581c071200c6c00c20482182c014207080801482c0b50011b00070a00c200700716016456060307612a81c40040c2040101a1546004c40c055070a0403045658901c5800155404c00290003481e038104954130440125518400c0b124048e142c01e0600c071600041c414044024901c5040360074140d00041d030341e00c07140a05408401c4002e000ca8000681c2000181005060285501d1081c546100c100d80410001140241d05031070 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 500137500 1250 500136250 500136271
    0x1090b03180c010516030c08040b03150f04110702041d12030f06010806180406110c0c1c0b04150212040f0606050609060a12020c1e160312030b030a0b 66
    0xc031024101c00c140300b504180b00d020300c0c00910b041030718a00750b1240c01ca01000102040301c1d41060000f848604000e40d806042444078003503a03401c005c03a4040d6400c0c1808a440d10404485141080c42d152500c51100e84884c4c504400741041c0d410f4003080028400308030b5412001c04e940041c0c089141c0c0a1011019070950f0300c030400c1d100e080c503264054100d540205082e042c0805001400040c0e55481c142080825a800c0c50101c01d541d41d103818006801d404542c2c0d003005802180751401e00c100810352298a48081d82c3d10480403000d0040c00f0080c0d0380c00040540400010340108001c10f501d1281c08204150381b10b000351401c81301004e1941510320454007540c0410b80c0458402c03c000c0c69014040c000c107401c03540c0c2410514603070006101ca03c00e40029906114845501c4041002c864041e16140c25005080c0c89600404040c260a10410081c1c8030740e55014200703901517140a0b00a609040d41d402c208580c40150400c1c0b001d41c0200244100c0f540d1500c0348100110000e0100301c0c500d8816882c050 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 500138750 1250 500137500 500137531
    0x6030f060e0102030f040b13021f021203060f10030603020d140c040c080601030b040b090a0213060906050711280623160212010c0905090112050c0f01090b03 69
    0x20014101c0700a80c0300307685140d00410030311000154044e00d09801c030350010750450480d10341142ea09103070f02d0140d034025004542c031820340aa004180814030350103c00da8003a40c59000d12071000400c3d5101c101c900d13a520200250103640d003402c1000c00d520020ba414140020225100d40000b2010200c0410803501d6000f4084041c2c1c03001024042d50000150549080c0490700ba03107107014100401c005c100a0400d90b650404010315034541c1c00c085c00d200c10184c000091801d2a50000b0042d500c1001000301a08050703800089441c0301e04818800c44080d96580390070b145582c1c1e10800d404020302ca0181d48a1200307030202c90034418000300a14015440f41c00c0c5d0215901e044006080380c00c030a01c0e074071072007600600000c0480ca100c20850b207044052408050b400d03002403000800d1003064280c107128030761a0204282e41d981e00505003405540e0100c510203201d030303078420b40c1076070f03480c6898401000c5400050b103406060504c00103040107030314141814211162a4984006c8540048888008072241d04 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 500140000 1250 500138750 500138753
    0xc1701020712030c020c01080c1c0b010809070f0b1315020a1401020f0306060a050c0f0a0201090f051e030102040504090c090b0a03050a030c02040207290c0a02120c01090606030f 78
    0x490780c41078a0011818148241c000e050030103506c421031480ba550510908000113031882e81184229040b0b02c1201a12000240700c01d6000001080101c80ca9801b084000010a541c8080001d0040490f11001240d0307904a0403e00d05c44c610703401c440b00c1c0b0720544140746408503058501092070b001c81c4100794014101c5c2c0c6001d08003e0901090300c002258584d104004d050005084070044030ba1001d0180d8000343c4d5482884002c580b50310460000c603805001d29080c59044004c0402d140c103000d4000d0741d40360701e415210004000b14400c0e91048c0780d4440c03680200c0b80000454845e000404500c0100011308080d45d0345d01190035540480710840d07081c4205102400030355100d1184d04840c1d0420360360071914508660b94182d585c2801200075060246110090045503100e804880d0311b9a0300031720000d2145e000800e03a4004248204000c403402000400180d6a4044d4206451103900603500401c942c102c0e40c0c1c0704610503030002040c0c9100d9521424004041103040c081e54009512950b41c0304a5200b15 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 500141250 1250 500140000 500140013
    0x408070204061712092407111f0309020f03030d1d0d051204080409060f03060509010b1e01020f0d0e031b0a050103110c01050a0605190f060c0c17010207 67
    0x11504240c40c02400c403160f8500b802c0e000075412140841d81210569550b0704ca10000c1c0e0882042c4107800341002404e980010300585240c05013041c40e2040b030896800d401035a00300b00350040300040d50581e00804500f00f00103148607400440300c19001801240c0507640c0d42000c0b9040da03000c6400b030309d60070381c43d8050764804548071480d6032400e1000e00c0c081c0c0b0000102d03002c020601c1c41041900541101144007180a104030300c0111401010311101c100503a560350700c03001040340903610095030030ba464200003c000d402c041c0101300701e0703101c024141c2d01440360849034200d4140318040494114401d84000c00703100c80e01088401613441042e150b078aa1020104100f40c5402507000b95002c03001e801400418081d00c0d1000c4040c03d54009090104812081d101c10306003500600840804039030a04d41401141c0107a540030805581064846074810184c220b5240c0d1001c190b407194000340e2548810400003140f0803501d030740001d44a030342003816090342c030521858143c40e50410040242d40c0040c0103c05c000300c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 500142500 1250 500141250 500141261
    0x80313080a0b010e1b030106020115060e01270e041104060611070603110c150109051003210201020f120f01050d150f200310090203060907030b06070b0408070204 71
    0x240d1402030414507a640d461901d00801032042042412640c0081080e140394290b696000141300c00f9502c0c0c807580e645100a0280c16001c480c00c0c143e840707503a1301068141c850121700c1341d4010183c4a44800342685804054560407080c1204110100350401049504060f0282d602860003060000b1036484110100700031604554051400d20078003440c00620600085041c00c115005c0f82400152108090500c089030300c03034141800300500030f044240408090070018103061300c154031030030802d41c2d590031525a804030450101802154488204001000681c183c24a50210780c0c40003505213507500300058034030b411401040c40301d00001000c000900c0c810071081da0052074111000790400803151240f42c0c1c41d0300100502c82c559501d48205054890046d0495940c5910a42e40004600b20040414005030004d0f102240c603a0507400f40000c03c10710070b000b600e020703c03401400b0680d0b9444900b401d900400c1d01403c11904070600b071203414040b07036a280106128600411207241e582d03005104106c210380 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 500143750 1250 500142500 500142509
    0x20616180f0e0c160807050111040b0703180b040b0f120f16020a0308040209040c0308030106020c03010b06041401121103040c03140604050d1b0519050d030204030305030f0604090b01080313 83
    0x160f09000c88410025000740b41c09040b500308402035901e00940c104107014089c000b4501c1c105c1600050700040d02c02c0728000070404075000b6541d6044c460380d01c0a0582c0042101c0c4100d110700b100a000502c100c402c558002d00e0b085044108040c541012000302c440214002c403107040c84030040c0700402264103007140040c0f05198061029042201c015580a001e21902400281c06880344038006820010110f2400d0f01440c0c00141142d01d07903940d0000250b503080d03414001070007942001c00c60a0107080120950317041d1400d0440f80c2c0b650340740380340c0116500d4510780740c2c034200140c807000d41d84904c085680046000300e001e1110300750407506605010710085d0740c481244103654060401c00c00450300114401c10b0b490424981108045040794210704a9403070220054954090380215541c44007100309046034103841030090301d0000401d00000d13812070140e4800980030a004100040d02c140490480c1a482000288009002c3c00151260001010b0903000900c107580001084420401c1c0c41c0c44000041 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 500145000 1250 500143750 500143771
    0x180f0109081804230105040c0801030b04030f09121104050601110d0806040b0915010801230f0604030b0a0b0a12050703080906120403121b020616180f0e 67
    0x9826540d900315441422456005540e02da11102d481d59629001101045043c2d50000d0032500c150300342da4510102072103150301c03592401c0001c1d5011400ba10b86503040781d4000d00905600c0e9902d880644601340a800c4640403c552074a001c00c6d42c0707030b290070165041806100b00d004e50204110900c0225a0040c00302c905001e41e98603103900c40d0000040d441136070030840c6820429500c460021802510f2507040c2c0c2030b44602c65004018207041224010600300800f40c0c0c4a46460b640c40b8005031132183ea00d40350280300c50b080511032207030341407941c2001102e2402522103494155603440e400c2d0a2002541c0c04481544c41d0780d883c05040c0340a0242102030107810301000070045135503903003c0d0b880203240f0004003108804542e1194039a6600259099100d11130040c0c5803e140c58030700240b240440006901003d4a05400680916a0942e600506402e40e800400035910364560f40441184c814501c10108845841c518a5038100e11403400020449200c14580356800c044c50640c1c03040e001002c0c107115 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 500146250 1250 500145000 500145011
    0x30705010609050c18040605120606100c0f0b100e010b0c0c0f0a0e1801020f04150c0b190e01110403050c0f03190c050307151205060102031917180f01 66
    0x850300721412145d80c14200320700c40d0a00e402240105016001580c400c560201003a843c00300403240104035144107440c200d40d84041d1407600c640590301414030b42e40c05400302c1c7c485940071002600c007809054021460107083c00e10242d0380d28001850203001d800c220300c0000040707010741c440b0354100921003c071101100c260008910174804182c03607001034881c9903152030ac503038082014064a00111405007a0460080d9034440c0e044c0000d2150f50302c0b03841030441d4510f094400840342803013003180d050b000e0f90100c0810b03000d0700d41c04654072502403c9183c15070307559950b816420441100344100700480141d580c03d107403180e00d141400c0741412582076000d8003c060840901d80c8030303600480c1d401454011120b24208540e1f00f0700b0505502034142c0c0150382c25100c7c010011400010007422420b0b5810709650f03000e104a80e820310a030036200140c0756680035902c24011142d1031403585441101c2d030442e520b840d074400380002c150b19500542c00d850b980490701c0f203039000e5100d0410038404050b07a54003501c001c1c002c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 500147500 1250 500146250 500146261
    0xa0b040e0a05363702130f0b040608012708090f041d011a01030203010b120405071203120506030309031b040207061e050c0c0c1003020c01021b2e02070317010803070501060905 77
    0x6c18680100e13800d8007031f40d54110140c1c4540e03076540310824408000e0000c001442e2200306a900a04071110a044d0407036030b114004c0303000407903481d11003450390b03101c07800310704281c076103030500c40043c10b025100f560041e01c2e02d4803410000740206002116013418000031030400030151269112130090600c13141010b004000500548560501700c0d1100500521912040e0713403035041503420000300350400d120304c0c9059440354080c1648809201c0701e500c0258030400403600c0e010100343c0e503849101d01d40c076015040340e1384d80184c0d0001020020b0000e0b1008d4030140c50640035503501011610040307044c1040f5a00c8100030020340c101441126805100481594a01080100d00560b103602c0c001d2080c1c86101e4281707010301d20302d20a030159011603c0f03400095403120016007202c120450072410300099403145e07446030030000032a104e0324103c64184c450780060802c03480580c3c1c0040d42c40100243c080c00b080d80d06070080d290480c90032a0003020581c012f107443c1c80719450030031300355102640003141c4641818141314 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 500148750 1250 500147500 500147509
    0x605091516081b040509010f0608130201080708190905100c081b03040309170f0c030102091003091a090d0e09040b06130b0a0b040e0a05363702 63
    0x41c0c0003000150b440701c0700f8204041c010b0301403046800840d00000da160000544110f003104e54015a0056203528505540c2d544800008000050010340010020008600e240e4018500b00b60414040c0d00c485000124110411061b01c0c0200c004850b140d000081030b4507240810320400406030702e6850403241d942404205401e070f81c1003900310440300c8800040480c0805000341d0b0350700d0080098a003801d20700c0f054607101e5512000c1602a142c0c0e64018844440b1a5103018801c480180c0401403150810710301c0e0660450041046c008201c90384034000101101070110074142a201e481c001c0000e000580802d0340042ca61a1440b5219024108060900c40012103000d40b0759400781095a05640c038030240c0c0144009404a171071825046410240003040010301c003002803003a60b0314100000c09986520718040c04445080300c1610049060040785101062030600c1041c0c00074650300408441c1154032005803c1580154483e1b000600200c0960340703248001480d058101981181c48011518903008074 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 500150000 1250 500148750 500148767
    0xc0904080310090e2508120307021c1d0117150a0807140a08071215090b0f090d08240112150f051f0f02010e031b01110a02031903090605091516 63
    0x543c7c4031802000048040d071003000b0051001820300b54209940113610000f40c90458040c100d034030311034100072260502d540207003543e840c99103029401603255516600c008010324004840e913030f4480c0c203403140002c3c510303002c0008802a04000b022140300003000c9007004000701440c1d00103501a04541c5040104800303030814800d40b50381210101c031a03500f140f00d4000007000c0304800103059001c1b031030602105c80803a035209849030354000c044540802a00074191051b150496445010402084914000c2000719484884601c4103040c203c5290558010440950b0804914110a01c04d006010818130104040000c0101011b0725038801d6030001c2d5001d03000c4a0b1803203424a080c480e44038295071100e4400d620190306130804900340e0b6140c1e5603100c0c04a201c04200c0b203885a4640c00d142d9003444a9030800e00312035018034550021403802c1c80041c0030000142c504d000f07a4003819074900c43c04010403180e00985104000d0b01000c0c2c0810342000c145003404401c09400521f801c1395507100ea642c1181c2000c0c0d039 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 500151250 1250 500150000 500150023
    0x50405070f1b02130903170717010302060c150a200f09090919030206041505010f060f0e0901090e06150f04050402130e0a0507080c0904080310090e2508 67
    0x306160442c0301c1c00810a40020300900703d50342480c1005d0304040c0751780183d4404040d2404c0300d0040c0701d41c4804c141115098011000040c038401d0038001000145055001001614281c4007690140b40c01407803840806401100c80c2c01c69541c603045005481c8081d501c4100300c41c401d50b082d1038103011902e910441d090140c3c00c0e89a00607103403400814811344080026000c000d280380780801100e4400d02c1e0080d100c3c482a80c08590030841c080800041c140307980540781c1600c000c1d00003159041e1800500325603201c0b0303200240c2d042c4100d6200340c03009a210851038a0180c0300c130440201e41d00740e60b400120f18058009144422000d004404d00e0902e64030084142c150200440d0042a641c84500004444903c5603841700720281c03415151482203034000c1050b222040c0503a05440009940d48440c0703844032844c2c2c0c0750b07a510004000018001405400141d82c00920034900d081c4850b8440981c00203e07040342c044a0701c4d550080141a42686a2004103101744440c01c000d0b490091805105e01c1d5a988840003 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 500152500 1250 500151250 500151287
    0x1f08060604180b0111120d1506210e1203270309040f021606090c080708060604180c06020714030c030a080c151509091507030b0d020301060f050405070f 67
    0xc3d00040c0741c0c41840f40c0c032010f500b60340c00e036079030240c810520740d41d141d1081c2840c1c0d42c828113010310300c1d00740317400c0103d10411141d098a07038401a0918081811003600c11084442204e40d590040071410b8908100c148842d14142490035a40c0c18240411101d00301c01c0002c1042d4080030f0002c21100c6500841502c0b040074041d180402d16451154100c0e01a0082002850715400700450100500619800001c1c3d124040c44095410603140d0b40015141c19050003041566071102002c24060b05180d0300c2604501c01201d40220501001d94400d44043c41c9a4070010050340802c4c01806070810dc201c110f012810110010103003100300c507000ca42c40325502c110241030046c0c0031074003052020301480221281c3c0c40d49410f000759490185203580d029a035511215004440c00400074404550019502005006000b0107284664032040210040d1032041c0485412840009050307005840900071800a03004101400704003d0503c400e00046074030051120703042100d0300e1544144a0303040108002e44c9503240c031 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 500153750 1250 500152500 500152511
    0x240a0e0a020403150c26040803060d020402180901050a0e0109020304080903060901020d05131e03090803070828080c2b020307090b0408030d0e0109021f0806060418 72
    0x3030194000d00031580050100c1c10040311030300203219694481402100c4a44079014404034000050700e036405003007501c6900c00c2910001c2408500c00c0300103158402001070640c591488a64041001d903001390314a0300b00d601c03610402c00705629180e201e5a0241a092300d90000d002e280c0310181c2d65800040c4035821050703500001050078829004100d40d00c9050107001c64044e82003511000c0e00079402940e00c080654500303130100310351380d0a0f118100c0741580c000f510040d054108280403000b55105a008a0034011072840000b00744809001406010b4042e030042030b12850000d1711059040405c440d10101c1116001100100a811603800780d0002407210701651200c050000034001c0407007546030321501a00c480f074030b010b43c0c032090b40080d8030550b078030f40c0e418640b950f071960890300c507000d1401403144a40051000700b021312001d5000d203060200070000030510702c01d2900451107901c400140c0c0780705104941f420510703858204c040c058001400b07440071480c00e0320b0f040c2814068142c41a0130034444d9100e8 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 500155000 1250 500153750 500153761
    0xb1309030e0613060c02030321250915030605040609060515030405060c18060301030c06030b0f011d01090b130815070801090504030c061a03010c110a0b1905070206240a0e 75
    0x400540b401a0003126030b09c0050350b0382d0091507035034040481d20101c100c208030f00346801c1e01c4401821420780042d00d84910940c035080001ca01d4140800841c07000c04c05549080026407644c0301d004420040c03403100b42c0041e05600b4013080c840941020664525440d1040017800005040010350541c0000c0540e040c80d15031020200442c0424901c031b6000c0c2e0f1043c004000842484854003400c001c486a03910100803c001210a00141d014840e503002d010850b6030f180300e0a0880c00843e14505182c1c14500045030355203400b06103d458001c81e8030784502c450b01000c24040d5400400c24070044c175005220020740f41c544004020050081401860206070300c80c4045800c0500400b8041c4283c1d901001c18458001903071401214000d0b4120f43c184a50b00b00b03405200d000d03020301d1030102c101240e400a07000103400d0341c55880c81020007400c0c40c000c01034912000c1810b4215442094090a09a27000e4004c909100041c418400c5460803018002c0b00004a85011076442508035000c891039000d030100c05a960307 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 500156250 1250 500155000 500155003
    0x1006030605062d0a0215090607082e0b04050405070203071e02040908030a0c0e0109080303160207030210080105031509030d0e100c0201060e0a050702031c0b1309030e0613060c0203 79
    0x106440a071800400c10001d083c0d0040b94035000300c1c250354a400707000c2e40d0380c1d071f0866038a02d029503a890101d00b54201103000d402400d28081c0f03c40480c005c003e880e21255a03d15004800f107544160117009000ca800e0050345840c0c003541e5040b4026100031030801800e1303100c00c8100024448080002c0c0344500d000c00854942e5003266040c2a080981d141c0c40745000c010410240910107420070001da042082c030002580907065500c02e4078040070080d4110b81e80d45000c0786141418440c0c00040d485502e000000607986c45040e1020300c1c00c00c0e0b6a00545514120601d483c1003000d080c81080c088001e01002201d040c000305a614100b00d50002103903060807031720b0b06420004580042c42d001070a00c140480c0c41c0b40c0540010003112103c0084029560f5494210000c460050380c0e20401608200031040081d01450820784800000c1c0368001a640e042c2000160441c0550840694003510782d40d0040906402050f2041816410740f50107240000c0c034000340311100464011501400402004101036450 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 500157500 1250 500156250 500156317
    0x51309151109030105071e0318050d0c03020c0a03021e01090504020409060f0504020702030a030f1106071205130206091003110d0b1c03090b0a12060e100603060506 72
    0xc000e0303810001c00c59075101840841c0c0c080059140a03608000c04100c5452186e1020b50f0000240e590b440f000c83c619580440c094030341e01690008110740103903103030081242880750559000540e21084080d03201031074003900305018401560700c51032200d0350400c090703241c1c0800c41003030005440c0300e01441302c100da006031400007203030f000103800038400f240102e4180843c0c0e00440a4030400c00c8400310742c41ea41c1c03041109912035224025019049140d0400009006449040b40c3c0c0b10300d4241006940b586503007807440d120040341c000700002e108040d4061845030301d10509030000c03560001000c1e11511a00440c413284525a01c403801000e0b00400c2c3e1004134440d912080d800103003181000c0e03444079601c028201401110030558032030904400e10710704141044418440590f0306407203c40b0000d02e0b0000c203c4154100300c0f004018080102c0569a102040b8400e03031028081445003102241030200e000c1070042140d0b001081071503d4200140020b90300c403800d45690307007021320b1585410204400201c00004 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 500158750 1250 500157500 500157533
    0xc080c010213060905030c0402070f06271a16211806060626010501030216020603040308010311040908041502010905031c050c0f0304060c09080f03040816051309 71
    0x4031042c502082d00c0350f0104002040303500880071164040310500400049102d121001130581c1591000d1a00040e00d5421104802c0031041000580e00c40c0d020402c0c80380c1c10b903400c1c02c1721145404404180d40710304010074541c00401510f800c000d2415112400351100c940c02c13608111120407881e01410b07410007a0410f800940d81c80070f00b0184800b0500e084030140c5950300412011441203d070b5001c1800c4895602c0070380b030000d444200426441d10300150700130b510035200c0c030701d5001d00c1c114000c002d62101002103020301c2c130076603440c3c031198950708014000c0381c0c03414582e0b4031490416149601166401003510309850300300c0725007507507428160400c0c3e0040000c840000e10a00000c00e110340f02d00140783c0d1190701401844000c2c001c03680d81c07604000807841218010000c1003c03d00104020403550342c0200705040031800c207400c0058459040741d00d8015116024034081d800023400b07105120301441034104d623175030545410701d20508100000e841c0d80c20640c81d469034281d0301c607000024440706114005519 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 500160000 1250 500158750 500158777
    0xb1f0506040b25020a1703121e0106050309030904051305060f181c05070f0605090109050c030c0d0f17031512060c0f130b0301090b0a150c080c0102 65
    0x81d59074140c0000c464104100c03441482c0244040502c1e40300c0040d4004842d1036000302901806820b00c141182d64414041090403540710074000b404480b210904440c1c081c035800c41e25803440030a5034090020701803050b04040100041801071102001d0000286d0780300c140200e80108581e078814101d820422151803020b8128800d807014000c1480d2040305030340c0a1000b03c190400e81c01100d10001d0754411100c07145a016000303010a12081b83d11074005084d41c00c1c46608003144104840d25a03600b92842a0380b410b145035500e444a00802c0010445020b030208143c0140400514250000d289080440f0740607010000103580c24042101c910b40301406400c8001c3d202e500ca05241000020440c2c2020f0070a001d5080c403045441c05078000200b2501c10030102505501d0035422500e00e070556040100c201c2d070380c0100711300302042545140010b540032348130611000070401c0144040025107281c03940b000f1088070741c4107120611180c1c020b40001c80190004140c659414001542ca40240b1650f00b040e5a0b5 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 500161250 1250 500160000 500160007
    0x3010903030605011b03080705180a0f090f09021305060d0c060839130b03040822150f051b0c04060605040b0417070e040f0b0709030b1f0506 62
    0x4168141d80024162142a6580d4175a0038006040100074443c030000503010810140010750007a1140e001800c03c1001c44083e4040d00d1302c00c1000c100c00b481c00780c1050300c0540d14840300b803040007014841c10041e8490300c001405801b1040c2c012420f91500469001101600c40000410075221040c000c59182d50043d81030316515030350600140840c00c1a540340e90300e03601c04240009011201092070408402c041e014001540989264068030391040c0d2550340704074081c84001521407101e0002c1d52049000d4080c0c1c96507002c0d2800816041c0705048040589180c3c0b840042c020701c5c92080c0d50306c082050504040494000110040d201c9028001c0c0a10303d48070603d82a418070280800c65800c016000d0f1010f011081e22100f064807a40100c0c001c031101200103100820a00401c4140701c490f9101400a403012180c40350f809000d528411101502c1c50381c07a050300c010030405000c0480d64003800d1490a000100c0c00d56540040d500d101901507040a1070a640b030b209651008000300000f00300061810350b4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 500162500 1250 500161250 500161253
    0xc0306020408071a0a0f141246090f060905151506031b0c030a17060108060f03010f0e1b09011203080702100606050405040510060815030a02030109 65
    0x20798407078024660507004540c80010381c608906030f05440d000e01c0f031008a080803500001103901d80b8502c42d1850030840203e411240340360a0000a180c264203801d448026460101d10005a0041b81501405055552034140c41c40d04200142c040120704046000e16815608412850142c2802c20b4040d00d0011001d43c04400c204059001d820114032410589451022041082400003000c50b900800c543c5100950000e5140103001140d100c0ca2407681d48803212849102110340c2c0e0045100f0343c60907440040e664071002d80100c2c0320326042140b410300b00c1c0303240360020000307000110180039107000d5204107115803010707502904030041071034003072808006000c242c5040e99075031001d0840d5801c100c2c1030105584951b003001031503181642d8150504482a000c10b940c11100c060b0010500d0302180651054440e59a4071070060310000c007003581c0c1c3d490711030342468200310884101400044800307400800c104100c541020206034400491400645c484d0480d0000c00e00307010003504000c1d419442e1036564030 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 500163750 1250 500162500 500162513
    0x1b0206040b09010318110607030309120905012705040e0307240f0b060a21060803070b010806090a02010e010306030b01180c0c150b0a08150906070216030204090501090c03 75
    0xa600409071380501410345040d40000d921320940e013002d050030640c1807201031035090110080504a04ca03150001d1465115112464018401d15440000880442e0108000d41e800302010140e43c0b03140d404070083c4240c180005d0302002d028400d180c00760740c4070348070000707002c80900c00d5400c0250054129a101c40e0005403501100c07801043c0011503c1c0b901d0007514403009207204801c1c070508003400302031500649840075034200510300e030038800c5840c400080c0c500d1034405004200040100000440c0c544500d0300e8240c05480058000700c010f50301000811081c00c0001494910180e02820107281413a18500100c01500391a08043c107850000400050100521180c0d01040440755104100745042e095040742c4000c94940c001d0030382c0c80300d254104c1c010f401d160320078080098000e02c0740824903580c114040c10090366160100840c0a00001c00400020a0000070380c8402c2e1480541100d07025200c030b002600b0032034080070340101e40c8c0d41d08140030064250f1141c1641c0e41c101250408295681c035000c0c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 500165000 1250 500163750 500163757
    0x801090c06030615020a3306030302100209012012040b07050f0708030a1817030304020901080d1b06061e1d010e0f0a0b04050a061a0307020d1b0206040b 67
    0x7800103032508074000380300c94030308103c1020503400d60702501508029031100802030045100c0001ca510340c100424000d5101040b074100440c107142d0020480e9403a40c240039080485160080c1d00c00e030b004010024290303070b004154400d010301c1441d0401410b0510074195180c0f140d5a10343c0341d00180006404941d8000110103024501c1c401c0c030803511951048074009403202c90f50f10884c003090f401400b0125685008a100b2600607140040c05101255a802c0328540803254a80203c440e42000040c0015410496659800b6140180041c04021480000189082e41d240b000602100340320321418200903c94009000505180c070315880c00c50400d21010304040002e110300c48602c19000009810082d200418504864901a03070741038564820640c000c0445d0000d2905020a030307180344001c025910361141302d026140c4101e00081c11400d020500202d20b60382daa041888210501c200413a1642c00150300c040342040d45000440c00d000e0f038180c03005050060314029840b420111f00860301c44e0321440038 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 500166250 1250 500165000 500165009
    0x241b02060307031a131d01200c0109241d060115020a050d021509010c05041a1c0509070f180207020315160e0f0d0b063007051008060f01090801090c 65
    0x4d4554281d461b40c0741400c0b1400302c1d111402203903114040c40c80e103020030320252014461b86030000c10b106000755104a41c040c11458400c0e000c826aa13441580c2100d14440c500803500b07540540040d080352040529035503d014851228902c28070a807a80c510b034030030700200c070846600c20100c41d40b03420f04580c003075103c140e12940d115113580040300050040c40140103a2000214540b00e80c2c0c0741500b414001f040c0c0d00080e01c02e42585680412011148802e080e200144100d040d02c40003c0310300780b2a81c01410a6a140d00800c20031031015030502c424180c00c1c2c07111300100b80340000182e9510061000c00c2c180001c80c4010000d400350401008009400c80340c040030000141d9031500050f1001c40704000315042d010481c6904100301c045944005400c14184503006174006002d9191000240c0b5404e603810380501500b40610300070102c41d1030010f81000424041c0c5030071030b58100b6480f0808402012284003e24840c4210401c8804030030590141c01e448024106140083c0002c0081c4d04010081c580c0c107204 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 500167500 1250 500166250 500166281
    0x50715050a111b151509061f181508130218010305031801030c0f1805040218090108070b12131a1e0c040b0c07241b02060307031a13 58
    0x20342040180b41c102510740301e004500c0488517100200e000b0710110490007444603411803e03e45000300c140580c00042801c14206548070054420000442d0004001c5540076041d0410a11100d44070b40da0000d89040d4015440e000406d038944203400002e08034012405000c10602509002005001011000384810354840500e5010b0f40c6000004400f11210780340d45000168400001e11500c0784112945003400380008502d03510f8540310b60014040b81c2c048042c50384070180102d02000a0304103018106e00400103680941031440c078221954a0034491045a124030100200000c4c2e2081030054002407840d0b003140c403081c003585560101c040c1c84101a21341002034014120b0500c11030803400d0005201d14024414207040c10314001503d00c075904800c100e20294054024085580303c9440890b00543d0329100888513981c142e0308001e8009004084611070104981c1400805070312503404403030700140e031440c00140101c034111034100b036544101002503101d0502d0625500c4032039580c0040501e1a80043c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 500168750 1250 500167500 500167513
    0xf020a0b033702032a030103021f0c06060b0a02060c0f032d040303020306040b040b011b0f120f09080102070203030711031e0c030c010804110d03170702160501050715050a111b 77
    0x1504074502c1c0400d08c0004d501c03101012104800c81000d184a450040041c14a244140d140b503585a0a95000b81c210100034100030900c00003030b940c100002078024080b80e55603482c3c0000300000110038800200351150f407103884040340215494040300000300d494031110707003405401c041c40d009020354425540c0a204030308200c0300c10058907140c410005110706c140c464259050305810202c0c24203044010a4803036a10729510071020550603d406003c03401907590b064001c6494001c05801815a070308801d1007a80305001910040c1c400000f29000303641c10480d46411200803100080c40c205002910302c5036038a82e0407801c3d81900002131600719a0400701c0030b9840b41d04408004540d606001c603000f5110110001c84584541041568034980c035010b071800380120302c1c03075072004804101c042e124240180c0c0f00c2c19000001e07903607541c40040584400d1914038170341450390300c0d058414003203644200e0311036641c3c1d004109080603c0c1d00440b0301c1d07440030726a5901d9036403082402c801c5512048078140c0600465 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 500170000 1250 500168750 500168821
    0x3030b01050a02061b0c0105090c01022806110f0c0f1b01080c0705070806070915080606071704091e050a0612200604030f020a0b03370203 61
    0x1c400755107106035a41d00824560f034481c4410625075010300000140e03c0c0302080201d4030220f00707004080c810b480c14030007001d18107a0180024a001702d40000d4040010444042c1c91240000190504415402250104400c2d43d50b0030250101d01ca100d5100903e10030008500d02c00e0480499003840c180089003c3d076040144107045801545040b900883c002841a00012041c032a1300d4003506a15000d90300b180c070b500392140c911900d8a201502d515002c0340403884100445104a03100d007449442c0707443c0610960400e9004200d650141e420001c080380c01c0500480d21000c42007081d100107109411040c001240c00d2107001c14401060f524081c0f5060520340021303580f000d40c0c05001c04480c920140c0208404c219250142181081e00110f1034a15189070701c0d2000d650f481c8098809075004992170b45c802c60f110710411031000304661040540c0c0d01d052081050040032100101c3c004546c0100c10020161560b0058441008800031080f040c1c0c4044180101c1040c0e222940c820b551b055076095031481c844 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 500171250 1250 500170000 500170007
    0x7120c0e031605030c13110301061128020d110307090e060a09170f0715050106030b010e06270a030b07140c2e050411040b011e05070312020a050703030b01 68
    0x20f00803a900342c2d02140340d170001c6040184e1018100c01e40381c03000003040d0390150105c1e8015030081e841040090311050f4199901941804400c1c048070a2600f01d14414007943c3d0035242c2201f070403c0203841400d03a4049401805011880d0380c0c803100004051301c0244c0d1b11015020002d00b40344a00c2a4507101c2e06c000920070104c0b0784070b80550643c22105240c0e21200c981048170943c0d2142d51075554401d0240701450000741d481030641c01c105203503c0f000c181b5604010b0000c0840c2c041c045458100510704404056075160300d0300316600c003601400c00b213217840740e00f102c40194070710305136010b0b50040000900003090282d074643e800c0c083e4020b0341d981840c101c10541000344500880c83c950010350042909051118039580e0074145030744c0e801280001c071101c200c4c81e407811a40211400ea4070382d154400c4820440c0340c24498866142002d0070070380c440020300074403902030b042814031341028800005014030038540500c103d034501c0d00341c5140c255565144820003c01d2134001000440120b8144081400d95600 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 500172500 1250 500171250 500171293
    0x181e04060c110c130c1106070e01080901090b0c09010309080c03040f05010503011a13030615050306180a020d110d03030b0f010c080a0f03060b220f08030d020307120c0e03 75
    0x3002003000001c0f4108800350310003171495035000018000900380d142c1044000b401002c0c80ba034155200e543c8070340c0f91000050004000200f181c569a494020301000091030240540d0300503040e0103203035445110510050b401490440d49c003800180000c1203414414100000070419034108144d600316890762170005407210b0101b0300484290b42000d00b24040010071580c041c29441e0205c1c4545221580d41e074071118200d8a0f4518003400c6000c009000b4485810304006030743d001440a40017510000300105480c1d1985514035000f4412512002c20009015000001d02e5210130010020607000d03806140280c01001070080b054091100d1103811aa550f026900b1400c1441d0030a807110f00d807a803d00012104003424200c4041416aa1003000c0b8040d2030350307805800b500300d42d00d8004d500401501c141d0103820312a64811a6101c1800c84103000c40c40001c41624807134203144401507120f03241c25105413201d0f2241072211044030311b4040ca00d0324060b407042c5d00001848042e400e6495403500300080160654 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 500173750 1250 500172500 500172523
    0x8031617070314090103060314030a080603030a020703241b0801091407030902010909060603020a030506030705032505090a0501030b0631020d2a0509181e04060c11 72
    0x30a40900c04000c03d103c20001c0000003014540010a1612a41c81c100768200204202009520214007200c015801911094010900300c1c0118180061004001d54500392400014a2014042c8581640c42e4145086103051111844140030840c0d1036061040310003041d800110004d0301600c0001a010801e10580c1c082d0580c40c55104d00950b5001019005820002d02c00ca04010b000200058950441c0c4140300151400da5005030f914a08800c006096480c042c1c51039109400210b020005a5030000c0c505016100c1da0b1101541300c12140c282c0320b20540907a00154120034a20304000c141b8201d944982d043e240b03e8071107190103884000078003100031f82c0d810020030646a03400e6050802ca0103440c1c21400c500c40d920000d40b400b0080c48003070003601c1c81c1858104000e84044503400c0e02d07103a078540e080120092071a08500349240e00000502d001844145170120f09040004501c0301c1c120722504841103000b90740210000c0c102840c004000700705401c0300c18009100d0419954080101040c062400d0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 500175000 1250 500173750 500173757
    0xf030803010302120a060c030605100503010b0403140313181a0d0b18010f20130b0304030509062205190b0d0b0d0c0f1a030412020106080316170703 65
    0x5a096038207101402c0003820010a041c86604017130703400134030310707005100c0ca000e0140d8010a40c54038280910003040700c615001c4080c41800d01c01400900d1305102900c0c1100e40104120300c0040c0c0341e140c024194864054982c0440c030312828041017a0640941c5405480d5207600704000080021074400303505001101410340c400c2001c941d000118401410283e04200c0150341a2f155200075000130382100c0311021510f1203182c55009230782c05003402030440001d000400100c2460a184075105c505010183d0107000d00368203004c00070500b0316100760306480c140c2a02601c516175881c10180b040040310440c1440101d80e400c3e8000210300f42c10004019412040b040f40070b0810f243c103003040b928081e0480310041c0c105e155201140e82c0150340b428548940e0600501e2200174090074280c0b580100842e640088201001240c1881c84404806d02104d5005802c02100162030f041504100d015103101d6020048511020540c0c02020840c01c0c07c00036041d215041d5110f103600810302e81c0105000341c03070002c4c022 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 500176250 1250 500175000 500175007
    0x20c0d02011b0507170f120702010906031112180705030102180f04090c0b0a03050a02071a04030c0b0c0d0e07050303040315110d0f0e07051011150109090201090f0308 73
    0x24282c2c2c108405556841201680c9000b51035944240a1413400128803080d54042c2d2003140340f000301070002150341e0b22540d00861400381c403500023900315034091107031801309580d9024148086040005440c010302142040540c00c0c20b10010213541020300710303140030450140401c00211450144201c0b10b44081180040e0722045424080050701070002c900c1a130003d40b1480050001100b1030340c0c14020304116100603031920340c0f8000043c00c461004025500051041180e42e02044034442c2074803115040b66007505643d039035450103d480c010700f000010103a0480381e0a00c0002d5a116000d4211b0070308a00042040010b042c00031079440369035200340e58264108000c14400300f41c400844006004c4080302c082a007420140382c251309a40000c0200c070318a569200e8044501005000315070146d1003640007040414100310004c1d007901d85a568042c10701c000004109280b00d0705020070308410508820200302e81d13035608181c030050507172590121b0025040e000c0118500348039054550039a600841000d0a = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 500177500 1250 500176250 500176277
    0x2010210020c07091107030f1407140f0d03230c03010501140c03030f0103030e030105040c0e10030501060b0409140705431e03020c0904020d0c06050a020c0d0201 71
    0x1e6200e426410058000c3c208089804a0980642452103c562803401e40e90000f504006200d00d00303842c5030303500308440311038898007a038408400e486c80d1320f80104240f42005480e909040ca0600050701141c2d01d8052549110051034260380102561601640d500c03000303503040080d134000d04000700c0d94008006001c1c40103019a5104001003032585501d245114501145016024078541080342c01202c226110401801010760110a5001441c01540284800e0030715649043e105091805a038980f00c805030700080c4e0700201c800d1980300031074000d802000200d4440030617940690050213003043c058204100f9428919442400d03074481d4085654990804694043c07810000705d8695030503d40005810000c183d400300511402c0c2c4054844811003c02e62851522608801c034100b82d5100c00118050700e100801e402060175000308104032425143c555071440050026404410301400b0605c03540700c0424002e0b081402080c040c0f1058085580c600d10303c00030485e980c3d00e030950080c0002c00c0c0c1110b001 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 500178750 1250 500177500 500177533
    0x3140d1a1509061e1c050118090308151306030c0306050609060a06050c030d0e160b1603110a08070807061406060409020703120509160902090f19050402121e04020102 73
    0x880341c0c0d415a40340e520f400c244178400c4028001192840e6142c1e5542c000411203007000400c542c0c5ca03040e4420091140d0076041d00c014207a80c10080c9400c4c2e00380e80480000c40141d41c1e03146008034440c40c80c41708020464803821308030350a0780240002c8071542d1500010401c64500310b28100e04c10b00b001088940f219081032011600c03500301c01d40141c2a4070082c003196590f6000c03401501900781c112002090b8030302c10322100504010707895215070b849010800480d4041e880c06607400030401c0d010b0405070190304e03089030701c02e1621030170700c038054801e60000c00c5aa041240003001400c015025090500c401d02d81c551607070305005800d403001c030b502101c03c000030459140d560b0054468280a402c19000013030301c44044c802130312004c8481c02c80303580204140c002c1c10055080c141c0c02500390a402103040c0841c80002c40c5854004011b968401c403960040007504003043c03605007002e004094020344d225509542402c51007401541c0300030901e1030b100c0c2c3c2c80c00d146082406251050790141d004004a030041061030 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 500179856 1106 500178750 500178787
    0xe090a05010303020d031a06162a030201030504060207050a12030e030f0f070c0f0f0905010504091505060d0f0506071b0f03140d1a150906 61
    0x10b10110f940015525000c407a00e040002d180d040305088a44082c00441040d0741c45000011000d5403100c459032075220462240060700030300160b003c03032040f0007180000b04084e80010350700100301641c42608801e811900425005150800f00d44500742400004001550b030146c0c5d2156101000307501d841040842810391002d0740c01c003c3c0541c47c0020718803c002c0700d01102440480c9503c00c0c400101c0d01d500040403c510140b07441d80c1e440c9400c2c1c0c4030341c4a81c403840000034030700030002401d404c0c24051030480035404000403d54203a1900031200901002e014160000c1040311503d0006842001050300180204010310301031500203001041c000d840284608243c8201200c81c0004903075007e40001716501d410000c07000b004030280d4103954020711500080c458200007580107019000486500d81050682d40c01c07024004c0d2107d009901c2c403862950540051003089038201d503e92b00c00d85d8 = true := by decide +kernel

theorem cover : BRFrame.Cov 500000000 500179856 := by
  have h0 := BRFrame.cov_init 500000000
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500000000 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 500000000 ≤ n) (h2 : n < 500179856) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
