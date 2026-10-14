-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1985
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:23:14.410154+00:00
-- url     : https://prove2.me/submissions/cf23a994-4121-4b55-b449-669c945a9386

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 356834532 ≤ n < 357014388 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 356835782 1250 356834532 356834551
    0x50a020a090e061f061d09091f0b0d03050a02070504061203021b06030415060506030c0715060803030a0e0c060a050a090602011e05040305130e070908150402010c02060d0f0203 77
    0x4000540881491411042c805813680e026002d65240403001c0b43c1c1d03022138140001d0841c0340f0744941074003901e452070403500610340d00c8050003034440b1140d040752900a5080741e01004a0510b9801c204644411501c00310759a09843c10641c1c07000311110903031401030242d10241c4c1040ca0440005109000301001c0402a4801c0d42640e101601150f07446282180380c482d204c0c0d0160b410804900060712992100c0c0c84010036000c0450010b03580c1c0006002074100315840e010001e00090010100501d040149a2640f60f4071410001e05080038411380d52404000c0c815042ca03a69185171021a01c001c0204c12106207000b4402540c83d120010f0052180d001009007001084a8a001284460040c0219015190003103181c600081400c0c0d0790b440034107070150081c2c0521004200440c4010002c5014002030308110116003024201005c005044000d1507216002a8204000041200907803075010340c2c01580929200d0b08052050001495611440301284401d92411035565020911a0040c5103c0c0c140360 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 356837032 1250 356835782 356835793
    0x408160c090b0105091503280605011106240301020403050319020f06070c0b0709090c030903021603021e0f090703151202092701060b0304050610080607030504050a020a090e 76
    0x290300542d8680a804503060340082c0206d250141446040041c1d44d00c140444002c9002101c107400b003130320034210002079501c903940741c071414022960084645801182188010403507460300300752200160202c00b11032090f500c4c1e41020103c050f94250181d07070107980c00030142c82d03441135164002041c0d45004c0440c68050301803651601038407400454113a1003000c260b114001888a140d80340e0314803e80090008007800b1207418003107420740301c501c10340c41003400b0794034000740c416030b58180a46006c02200c01303059000040c00c024001038481d091309211500100340502944060306000503008000c11201e60b8001c0361000070483c1c2264140c01032001e82d031240110720704890b2070343d400704154802c40c08042c0d00100c2490128121200d11031b0001c10920a41000a21030402e1466050075540c540e80008501d6030301000340001d0050510910b500070704800f0704010014908074503240c45000040c940418140e4400025044c01001e000200009a00400034003643d0b84401c030100041c0450305042d686d03880f80 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 356838282 1250 356837032 356837051
    0x121e06090606020712020d06140f2413110304150c0203040b03060d03021606180e01060207171204030f061a13090c0801020d06180b06070206030408160c09 68
    0x354420101035500c0c0d0360140c40480e040417054651300c40303100c1d42240c1080b1000303244804248148640310b40300343d2865240c05035087c401e5462007491405040b9202070301412198130b1342100b074440082112001541e00100900c64440407100400d00620300300040a40001004100443c009154441d40e5066004020b241c0c040c00c0100e81c0d80c0a5170041c2e80d8000320030000700b8150324080ca0f84038040c902c40d01c115241c460390303039200c070704655000c1d4841004154096000c00e02c2100003c255805801c0b064205489136240120081d658191441803030808100f550740843e540000384000c01c4104c180c0354100359195a0380c03030300421003855803500780c901030325040c1c20f03040e042c02e482c0d00c02110313801c0145805c80100c880440f03000108000001218035550855000604402c00e0001d0314102e0000f83c1d00150300c52800551031141b081c02c05141c840540b078010240d0315580c0340829120602e4042e039090b51650344038903002060b40f01d180307613184044032052300d0701041002c0034124109a849031041801131450 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 356839532 1250 356838282 356838299
    0x114120c0306031516050c160e15040504080403170f0307020c090a02090a150c02040e030316020a0302071a0f0706050103020a0902070b1b0f03010e060a0e0f060d03121e06 75
    0x50545c1e85816900c2130040e8a100540b240d405001804452010b441100808048459078514183d2007502c0806484e000c1019102c0e84042c03601e54104182c1d024026443c00c1d40d102c1040e44584c1c0001801805150401e511080388002a250041c8181002c070b81e0364108900041c0d600c10301d603911248500d5041c800a0401350860095848002018015024840c03c2060410041003012900c0d1f080103c0c2c41c00c40340c0941c0e60350180000c0001d004011703640d01c5c00c00c00904040c8610f003400da0b40541d408506602c00007a40000d030041114030001024400140054501e4480d01c03c0702807810082c08045219814404d55078445030489108584c00701c0d075030b5030300c01090040c6d004422002d01412807440c0020784214031141c00b161052180c0290350701c1c080c51a81a640341d500283c00850500440740100703d590304100c6031103005042c03211081c0c1c1444c500341b4409010044010544c1d070007582c4540b06481014040c8409a41084a145e428440e0007a407100035680c032a45148060305090404000040c0d030034 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 356840782 1250 356839532 356839573
    0x8010606111e0309030d03050609060901051e030a140d080a06060c080702040b061306170c040303031a120c0310091109040c05130212090f0c0114120c030603 69
    0x41100508904141078008030003034070001a4600b4540001c2001e81da4070341d8107002d801c880d06103549000810381801f50601c001040000c18080c01540580c0040c00141d5403602442d2408410172114070500f150301d00807a0900c1c01c0324070010305040031000c5042603242c012542800040c03566075030520582d10a203c00c4140d03020707071040c500852080120440420780c003000404e1882d0003d80045041c02040001c02da00b41d200b02d102610452400780d003441190f511060380045201140c0074103446040c44088a48103108900c0010103141c0d0b02c078030f400e940103240d60b8184101000184960300103e5480902c9441e030740c080d07405500c680241c42c0c041e00c03000c1c4184a100c90060304005200004c814031018800b048a01030020365079021080d0b00040e01d507903030340440d03038841c0301301940540c503003204c02c0204000035800703441541d00d03400c58008140100d81c00240003104031030920384600200302080741e10419200700c10351192502419810030880316550b0f0025030080d2415803c4420350403407201c1e0000c941 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 356842032 1250 356840782 356840807
    0x20906040b060a050f040807030515370e0607051e0301030b0106230a051305220b010c0503220e09030409020307050f070c0311040b15070501090512030108010606 71
    0x141c0500005410f5480303038024062290010403158902529409400d00c0c0200644c412203007a13004205071040040000c0d000b5401480c52070403400d14103001c080c0d510907542120a003c4018012010714401c074a29500510b00d4650300c00d06503003013414000d400410581c071280e1206035071703101504c01c49020b001c5078003101d0490340c00041b11111a4200142110900c00b1454a02d94012035400103d100420042c000c010307040c040e4580036510340c4109418032008503954403040c0301c0e00320305802c11980c0c90030340d0b4000d900742014000041d42e40444801a030301040c6500000e4203078030021480d0000d1448166020700e0203485181c1c081a002d556021400d14a48101d030482007541007407200704500c5126401558018145080c080d013070000e142e0b90080e0b1741e000500b055594006410080003805410204c0c180c40c4841618103000e103511202c0403d90614603160765a841d031800044150074003c0079070015007641d070312006070351030000c4103d41c1008a1304207005a48040d40381450006513140240e50a0000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 356843282 1250 356842032 356842039
    0x1060c080d0203091c0c1109130b06061b0a150b060d0528140a1b0509040b12060a0507020a0215070201030908030a232e05030105040807020906040b 65
    0x10200049681c0d406900040c01080080c45484044a504804c0358403104405115a680c5442a59541040f503007032040200000e0040070b4030010305c465042c0c2c3c4074004d0030842e004400e090762510341001280c2107100b0b48104520541c0c10020140c1210408103800c001540a403405003000d600701c40008040b03400740c024040d4070020400206075407023015002603901c80c018414540b115103074a4501941c0d01031070480c8021080e0740303513021100041d078014810740217800d58201b08007050048161007409800d86140700207001c80424010840e030385a41100c02c04c4c44024105c00e865060403400159503100590f016050346080c000001c0b0143d100098900c3d425400174403139510700c04a9446642240d0081006070304058954040d41c01140c0b0f124011800f074202c400c070024000480c030941d09207802e0318800c100c14580b00a8140541001c141a685e80d0007001c2c2d0b00548403c141140d640d2034000340540c4840d80550800c01004203105c42c0c4005060031900a40741d003001507a60104010480f0504500581d0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 356844532 1250 356843282 356843287
    0x11205040515070e011e0816021c200a02012c030304030c03120503060d020f0f04060609170a08090118090e03040501030506030312070503150909030910020706050729040605090601060c08 82
    0x10184026601c100d00c043c009c0c010703918588061040c0d00f21481c5507902030b4000c92320031310001c0031701c540503006207008440f0000903080c4060303a44e0000703103001d0340c008200c4d40d82098846a0741a50a6a00081c2d450b4003004040382c2e074840d500c0c0352035020715034580300c160f54003010380d10b10202242c012011640b0441004001191191550342001104217880c4140c68008074009144c2c5040d480e14841e980140c140c036128032043d5464120f044410180b074000c0b02410350418290400081c280300700b030300c050410900b4103941d11241542130010b050420307440220854181100d451504c01c0200007030094640a0f601444140e4680d001d26907070344074031408610301c0c0c080b110001d00c1d19071180e0007031a040300e000441d02916510320790010f100401e00781e0358038046d40c0000a40781c6192070b00084d000c12015250020f404014074100014006010b941405060000c03411504403a50001c40100f8003010248060444141003030708281004220843e03200c240d600c1641c001140281c0500e071401c0200381d110b00e40d00d1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 356845782 1250 356844532 356844541
    0x30f090605090d030e04150e0603030f070605060d080418061d060f01140a0203120a06081b060d0509060702010c090b040315060f031b09050105011205040515070e011e08 74
    0x30342092440f025030400030304012084803556079000b07001580307402020030f8520038208412050360890140c42d152095000304134400e01090500d0503241d0040d00014006401c1d42c405020030b4184000c400300400620700028049120204c4000b038100a1045890400c841a04da45d161580380408250341d080100144001502030b241107032140380c3c5201c4c1803425400c12001a08040d0f1660842860400581c001052401c0e44000119035035034014440384082c4103c9142c2144140c6840080b00140300c500d0b190b1120a0040e01c9000448440302e24801c0d00708407510788050b400d600c074082590700c00b0041d401c00018240c8c2c1846240c241d81a84c01c4103055038a45451980e48101000c0030602001d89152a08000108900300020315001103000d034914a546000c2d00d0055203200b0300c10340040412178a0800184a0307668090060704200c0301c1550000b900742c442c1d040c41840c1409410141030010945401c01240c15403025130241018001c9c1c1b9843d412001c1c0a42d0145601c03a40314415000071240000107 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 356847032 1250 356845782 356845789
    0x50f0118051302060a090515040e0402120a0b04060606120504170705010e0f070e0f04030203031305010f09051e07081207150f02090f010305040f11040e06090109030f09060509 77
    0xd6070418030382c044000c14804140e001c20460f40202010101264074544d04001506060b40d25030319483c680c172a4586000e0030200810220440584003030b0055070980e01c1c250100c03008005440c0750a4000c2c0c1c200d03a01e407030305203800c402030a818041d6500048684402c0c50401d403042c000c40d4000e50f40500080240003d00a0540e02c607017007a0b20940c4d00390b4850455a0165a051081800900d4070b28081c0084c5400c01840082260300602071604100c031300000c21001c07035400300580e0380041c0542070500804056081003405402103202c544006440c080e00d02040100000755096a5038114603502c11301120302140d943c03207950b1486010b0301900a000c240980d1644a0b008003032191254407040c003644081d035a1724084500443c440c40803642e0008a01d5000c0c540100d40f0001810240713014442d52400f81e840101c842c60034100204221180105404681da0b10340002007245955000c4801c0e600e01013000c0d5000c0c1561147c141c01180c01c0b5071044605600c111590001d650f440e490740d914203a10501030 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 356848282 1250 356847032 356847041
    0xa02181614090a080d080702120f0702060906031806070e150705070806010906030201020c0f01021b0621041a010e0705030a1508010234200306040312050f0118 70
    0x80076500714007004006042e556840b0440c0240c07421030700400042c03114a002501d40301c0090192000d5600c0007a168040c66000b0040f500410b00c041115511902e00c1d1010440c54002c0c1c00781254800c001108100001c000104020400580582126400c2d115201d050b608051803016164001c0c52114810103076803400390003840b0851040c0103c80700c0c40c1d5680580d03402d101d17080e00f10310052500c481c000c02c2990f80c100000f5081c4041105e805010089480020399104c81c540c03600b06040507110044c41442d540c2405841010000d01041070244c104000c2d1040c0c5203004482c225503100b920b481c0000d04820014031541a2281c0f001080300e9511002d8099603950002055617500c0c5403204000700128080302c0405000f420a44000b588031400d84a5003038403070125842101001c00c100d9100001070810300c030b01c1800245c1054504525a505030f0700c552aa110104600d90144075104c140401c050f440f0811102e0f10724040410040d50b200d03c0901c4005a10031700c2615202c1d540e0500c2101c010340c03582d11 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 356849532 1250 356848282 356848307
    0x120a050310140f1c02030a0c17120a0818120406090e0f18010609090b0403110115090207020a03082d031311030a05060a0507020d0201201e0c0a021816 66
    0x1300802c0c128041c0d40002d1410310028400c07118800c00041c200050040c00003035511000c000d2028018200c00c0045410031806000300e084200000d40c00443c814001e000c0b030341498241004250340c3c6040078810015003650091080100107000703c200054050141caa9050084000020b24951911040d2204015403695802d210b02550380b1440012440803c2c400c800c02c1901c54440400507107000e0901804101002038081c1c1503905000044480c2d81603400c569080d00c2d11800010707210b1880740007188160545d904028008500019006100c41c85d0585032a1088a00f00401e902c2852041e00c2140a000c10303240200c042c59000900700001f110441845e940e03442c082e0840d02c051045459241c5014010f03140c45070134903952000c1c0b0003000c0d0f06000000d0b203040d840c0024050303d20125200002540000c1c40c14203001d40108061040d6008601e00c4011403079120036840d200d10110703e071141c80300c0c050b5104030301c507010b482001c41003105420a124403034425a01ca071141c86c01d0b140c40039101c1060006 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 356850782 1250 356849532 356849569
    0xb0f070908150106030e1605090c070618050106170c06090411072a08070b070611030c092b17090303071a090307020a0605090102120a050310140f 64
    0x80041100001000b220080d005800d40c070304040e500d082d40181c2190008102010a0b8100022500c0001e442c912110200e401c00e54a1a10640d0765451002040c0540e0400074605420720300c0c050440700c0480300a1150304d0107040200003007699410841c0d0040c1c01c48081c0145030b040000e404000b441e103480070b05807018010f040400da01d880100409010303440b201003102c010741903540848a010600f00d036410800441c0381429141403c00201650340e685611030a61800da000466404200711034000210404804848589034200f41d144401c3d10740003248464082c0d420b06007036544400c000c103801d000120000d09144108030355500c603503541c1c188a800f12001040300300b24031b500c140c50400003000d05501504200c5032640c60103400d2145584003a0884a050740309110210240c0c5e141860b040c211262404d0003507a8002090041c1c0c14110740c0d0f09a400324081c007007034110003a60032a00441c4140224040c00c2150360b11a0813032507103003142c0c0030215088000c082a030911401d0148001e50f071214141c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 356852032 1250 356850782 356850797
    0x1051201090c0c02090103050a14060606040e10170a1202150604020918130204050a0506010e0d1b1511070609121b0b07020102100504110f120a111c0b0f07 68
    0x1074002c2890b505c000c2c0e004541e50350182041b2000d00007070004440b682c106540141009040044c0010b4450107580a0990501500700108042c40d0b24003040500508441d542d004c400070148001c16218181e1800030385140103a80520f950325071000c00d0b010345030100d40c40c1001a0741c0710542844000e40203020500e40000559080001010448030540d01c035801101603041400294414081920300190028032450b050005000f4240c2e0480d11040c4082019619500e100081c0e05240c000300c010681920a101c0b000c1c0300c041240e2070f44030001c1d0a0164262074081f00d48030341800c51079032001c5902c1040001344241ca41480040c3c03101d0310a0800b180211034240902d50712010703808012815501003000010009a440115601030164036007051072071604210320310340703911060020250f511106104821902c030781c03c42680c41044681d80140200111000200e4500d0181b41c4d41d40c21544080c8190801c0390b503c009000c125445c8120242d108080000984506921080c0e83e00d0240120f01406000d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 356853282 1250 356852032 356852057
    0x5011409220e012702150f0307050306041b02060622020c071a04210602040b13050a15050f13210c170c0f0103180c031101051201090c 59
    0x14001c1514501c0340c03444001140002e4125590848600080060ba05450707034502030504100700c00c940802c1074041d610b0180c555000c0b409403080d0300c150090321516240200a000c20b080d4400c015600c141c40c1503c042029081202c030003d1241e1102d001d00005a000000042e524105006c822a02204c840c8849141e80d8144140a069811203058100c503130380404010048443d80d2401d20819040c0390300660b00c1c0c01d042003114081885048119050080000c44203c1045900e604440090444c0600782c0d495803a0f0004180c02c00c005485010310404042c02c2c0842c009104402105100415450b02c0c0c0c80e1a56518070080301d504007103031f51a0b10001c190000030300f05a81e00401081200c0c00c0031000f035021100d140c200c5071142e080c3c001c4084c2c4030076a1040302600d100040c0444900c03204503040303000d0490b5240120054035415405c0c202d0301040314603c8007000104044881602c0c440d42d88a1105204100116031a00170300c0c7d40e6840703055030a40108880d600a0340010141c0c20725103881c0360a03009 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 356854532 1250 356853282 356853319
    0x302030415051210060804030c08070b04110310062615040506090106090219030f09290609070903030f020f1e1c020303010510030b0d061e0605011409 66
    0x71940c01c4030300412400034240610304169040c00c2c1d4004441e9010384c20940c01d0480081009500070070090600400d00049818022400b0035120215480651403d05161520741903000c4515454924041c1c495001c01449145060095000b650a2a03d054412819882c0410445202d04c0702d803200a0140056912080e0103810145100f58001c000800990074402102421582c4a6018101052041c03003d6141c1c0c100325001703142c030ba00d6545404100c5210290700840248000700d0020b200c115a14403249043e40544803100d24114404400415541c1c1e510510404030f804403504c00004e03980e040309000003801f40700d1380345460056204440c80c0020b900e015501d08002003025040d003191110007214483c40c00c005402c8807020214903c1003001e0031040180d41e03800103029041c446c4140c1c0e40c0b440b24161183d40304241c4103a0080c010700201985003015801481644071075003095042c10303000d51482200e40640f004656042e500c8400c00740790f4110380100c0d904400c083c02d0f440182000394190741803 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 356855782 1250 356854532 356854559
    0x2030a0c08070602030c0c0706111207030302090409140d171b040320090105010203070b0121050a1a0606031303082d06091f0905070c05070e06090a0908030a0903020304 74
    0x340782c840d0712036a400081d0075a51032300341698480c0041061402240315001e4001c1400203040605000194403001546400d4003c0e020301c0c1c0345d4a4001d40340c4100e40e03003440aa07009009039210180141c40700d20b00c052104a0b04014118684e0f0b20300321100000c94a01c03080e00c4114490b400802c1d00f41030800e82c89580d8100714441504c0d4220200c8a00c0540442500d0220076003401040240010b510745005c0b640d55154101c0144035070480301c2600310030101211402c0035a45042030b8072805884c42e00a551800700c2101402691903040380946400151103805e2220499002e05030390403007001d611045640481704800d0062030200c01d0360f5404504072000c081404218160000704d00d2583d030303610f03040003400b2a81c08014041800d8011041000d4051400c400c0b004d81544d200310404103107079039200c0d02516080200c0c10020081c3c400e50400144060004144074012001152000540d03104d10319170340107540c410300002e010004e0402c0498044241a844520464428010341c0d0030140e9401942c03d008 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 356857032 1250 356855782 356855791
    0x132a0504061b02062209110c1c0905060d0203160206060a090203040201140711010e030c18090a05030c15011d1303090b03010906030b06120c010513030b01090204230102030a0c0807060203 82
    0x1090000810f01148001d4043d40000d0010a0b25048c20445901c81c41e964401950741070225014080d05004906480782c46520080c21010300a0b0f550740708480b0b1000000d500480c1c41004141792400000079880c80803411a00a81c40180407105441c01c00801000a520140040341031008201107a0141440d0901411842c0d0041842041809200c1c00150402100104c1e0074840d4203d2000000c040d518410340f4100401d085030007900e960365007200c281c50710843c404094030902c0041540803a401002549800c07030201061000c8241c6da880c070004856000d02000f00f0440c1400a0000e075602140401c61324045010b0314221071060f6860500c42c00d143e1081c0c0244004907224401441445060181c1d650001000ea4a6164004107580e80fa038a80070a1030783d0360704210001a1034210381c0340c6c4041100c007031074010242d4603455035203d41e83c1c0d009611512031141c0c0c03004084240b6491404504c000d54041d403068000d140f4043d14180100c03204e0068040841d9030744010722a21020800714805184107 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 356858282 1250 356857032 356857087
    0x506040b0c1903091103060408250206070503031012030504090b30010b0616060509031b060103290604020307200a2604050f132a0504061b0206 63
    0x10544c0e5424440700300203024521038040e9001d8010700c00090740c032008851112111700c0c00262100c403a1408005000c42c8440302a5000d0320110301541401004002540600c00d105000711220b5601d80c00700303071800030080c40600451030a10003081100800c1c3c00503004040c006140c0036048000180741649400f00d582ca00714016600c3c0305a01d0414402d201e00c1145003030403201941011101c2c0c420404006240b0030007041213072078402041c1c0c1b6150800c280c81c0038407941e40d20340030044401b040d1543e40345024030068810703107a204102c44444904010200349100300070118800341e0341c0c080600000c0c4d40040d107a0300130003000700da81c1c204606070f0441d000d01e0000360300701170b01070348040d800e00340030708110340b2415044450000b81c00f00c2040040c0c0c0c2110200c4800365017180300d9841440008280c4152103c1300350a040c2003d40c3d040311140c0b04403a2202581d0040760060300c40c003154104403401d0150b8002c84c400b203512400480003400d41d1a820f54402d074801401c440c9040341d1868032401d038074030b00d8414912 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 356859532 1250 356858282 356858291
    0x130302010c03060b1b071d06090a0509060a110903030703090e1006080f0a020f031e09030a090605030405030427060b19050913020415020c09040506040b0c1903 70
    0x40590a0044403141d640624050280504100e000d103100d110318001d04d440b0800882240004980034480c0e0801040002d40c0316180c03a100041079460714404135210ba10420b1a00c00003501815075120f0309000c0e2030048010246690740d0079401006140024045002200510000e0380c20341c0c1c104000d1100e144a5a00c19110074501004600201c27806092508400040001071100e070f64407490055006145144040880e111618801c00038425503c02031000707440002003003e502010501c40c00340c010a05031211155450350700c50703912806200c81000c00107840d01410404d051203400034580181c090400e803071501e90f0794030032505680194156000d01010b03c2c041c1c1c0122909500c154402006848050751a0404004d500010001c01018400c1030040100303000e44643c9031050071069036002508115070700c541301c44000009003070b194901001440341200380c60003030821809442c0100d5104000341281d0310345554501d410080100104030f0420f0070700c8031519a00d41e11003846040485a1000034 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 356860782 1250 356859532 356859571
    0xc0d1806110c010b1206190204050a0e01062327030a0f031403090316060e0105010e0a180b0a090f0b10030311150408130801060b0d0507090303080c0a03060e 69
    0xf800c0d2598446440d20400098680040f10f001c0030541a034080d015140c0c210b5034459000114009004c1d0741c101c5604005060404a50074180b0f09403d4162541911200c80c00540c12001c850444981e008103203e0b01c2051244507220303d1009407a00d0201c1e0b9601305d0740d07070026505000c245048103000080d00c05108600c440e0041c1500711003201c900c4002c00011501d10b15060700040d1b40ca02c1040740c50302c40c0b040c05940020030b1011650021b640307402481c00a0255594480c8511020242518101940703440e000000c40c030b10401c80416641c547d0f000001128076a900390100008000048099404800740c00c1942d00050b10712014500c59100402c420002c40c1c2507003001081c00034000ca4901f10b039401076420340c4500090b1032040d5401507205403c2d5903501c1c070b4030140d61820005903200780f61540c00c051000c2040001e001c05821303510755000d020040781d5140141100c541c200b44c4030240102ea40c2a0118030f899108800030702030140c407420081942c96482c0611130f6030307040c00c9a81007151581c01c0d4800c13 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 356862032 1250 356860782 356860807
    0x5010306060e040c0620010f0c081e04120306030203150106020105070906020a020910151d030c13020c0109150e1b01021002030a06090207030f170c0d180611 69
    0x30780190802500150143c64941e489011000c041c1c012031007442541c0f00b5286040b200d503c0e00142d845c40a04c001e1107200d41520440001d0010842c0c940007040159000440e10701540560540501050031b600a0343d45a5460701e0348069100d1030729608054440c40c0110160b2010070281900c8580c501e9400850b42c5450310003400c60700094401c0381044064136013000f100c0e5002078414000c0b50100e030100029222107801c070300c420341d1540c000c0c01d5100d00d8001c0601843d400c082a400280c061410600061003011b040680350402c2c042c0040c2c4c808042c0071194104070160307002e40700c031b0f40d400000002c106071706889480d5120115041d0658503a1030b00c0d40d00c0e503240d9080c460b01c1d60300140702500003011042000040c0d00d03651040248440f80703a0100000b171600d840c81d0000310060070101c0f0704540e03a1703515040003000c42024500b03280100d148800600c1d400d81d44500030a10942543d15018101f100b10071040f40a40340744508a40090a603110800104181d0322800030a440c0e502c00d00d0b80da80070041c250 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 356863282 1250 356862032 356862041
    0x30a0f06121203150315090b07031a09010303050406110a02040207060b1216060302071a04030903050f07050310020702010201090c090509070920160f03030204030c05040e0c1306120605010306 84
    0x703200070541441d0070040c0380341900b84c071101903a520183c01c0066098180c18a4000e040c000070250940300c41c3c10030b00c04026010380c1b24480d80701c5c203004503582c100191021b10448407420f10004001038010081001b0a81c070841e410500384804205a40700a29140c0003d0180d820a440c207407940742d0b0300c011948841c58031368140c482e403003a00ea02410f040b4002c2504441250440c0c4103000070f2580004035002001a000400a0800c040900720601c0b0300b407604004040b04860301003103d85215041441d2045140002e110045544c02001082182803045294001c1e40004000304d043d0f45d02c841a660024141e41400c0c400f41c1442ea40001d4103141040340c0d01e02e085929030041030b6451901944840020400202c05520301c003890714190740d0030001d0203d403540c601540b4068146011841240d082540c503030010030490f80650500c26507a5114001c120441d000c029030100f4640c80080c0403805400d02104502c0604519880040c1c030a42c1c40c42c04a0342c80c903110104458040d0341d280103008000c0d03184035 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 356864532 1250 356863282 356863313
    0x61701060c121805060c0309040b0d11060703140d0e0d0f09140d05030409020c0607030618090305090a1e0801090b010b25140c010e15030a0f0612 64
    0x20003840c03100301d60311404020301910290104000da00d41c84000d5540f8034034203003801442d014286035039410700c100c10700da201e401c01090740b446181413003660318607440c4c0040c801c42e0300d54004050072000390a250030041250b0101000b03c0038040c03138226800f80b4511540c040d0500034103100003c110b4449150f504c50410309444010400d03c82c0860508056550058a02040c0d400508005884c1d14608000880381c03218480024018400091701207041c01c020307005415076500070700031200141c17203100c0180c1c00e171140c9005a403020520101c400030031440070340201c03048a0080c100103281100e140045150740145400604003081d410007400c00c90100f921002e802095060020824904165600b2004500612075180b03400004603000700001034802c101d20094070303004c0c400992000149005c24400302c81c80d50912050188141c00c07051540500754402000000070aa1007103554501c0102550340c00c080d00d203000440e540c9541c2103003105e95110b00d1028004069100140007a0b40c13030001c50102403540c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 356865782 1250 356864532 356864537
    0xc030f0302040b0904020702041407050a1404050d03120b03012c0c0904140708010c03060305150702100c021627020405010c020904080d15080d0c0210140c01020406170106 75
    0x2c0200071084001080c1d45203d10111400b59881c01d0ba400040c000e8090400b00c940022500000d0054440d007242c000e000c5910151039040c9075521303040c04d03143d00340540e10506811008500d07950000034440c5403409005a41c0d031a0011380038802e035007c80d003156840e0764001c8a82c101c55101d800314000030721501070014110001401030030728400c04510f0101020b4402040c0c4c0190490034800d417030003880b0080141000d40000c02c0303060500d250080c003401d0148000d5070b0034051041c2c89425160901c150900c602019001400d081900c10241402403c7c1d45181b50f046000310742e0215080c5188610b00001000030b0389450a00d03100000c10030708100142076446a04600c100003c00440c0d0300b2120683d40e030342c0c04513410303000343e42e0f2400c00e160103224500b410084189040e100c02d004002e1083c420003035070b5020f4222074003406245000d403450a00294042c0d400700c404480b0b10030140c80740000f1083da03181e0300407441c1480c00010343c0d07a099810031f401180104900280c40722200c445210520f0040c5040c0c0b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 356867032 1250 356865782 356865787
    0x120108030c011503020d14031209010519150b0c0a02090a020307081003050d0804080d0e010e07060212030a020304020a0e07030f0c051204031d060a03061d0412080702010b09070c030f0302 82
    0x590006d03e48404440005080f84141103141c1c404900c1401564600d040791600c22044d40743c29400316008290403220342d4003540350035001001034841031090380152410b011941c0d0005003003856012158100c0c01d0381140d0381c41160b258074010703110002e00034060381180c1000342c0c603070600d54005481d80000401590c103070400703a00208042072001440b10141420b03810103042644590030101050b1040c0604d46656600700780100100800560080310545509800d4074441d50315403200b04c1c3c50301080d9941e8505003c00344045801698903a0046070068030080135103000c1651a01580c400e244100c1e034000202c0c0d030f68001801901154010451441c01903e0194a0a481c002220190180140001c1c04002c10165401c0142c122007855400c4d001004048548032030041c94010003070402030203500b400080c0c1451140f80e5481c22100140540c2d400f50071505100c444040440e140d05005004104564991143c904603895240015000e001580c0c2c030038141d04042c1c100680704c1210150801c0816104 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 356868282 1250 356867032 356867039
    0x604031b0b0c0a0611040905010806040b0f060102030d0f021207081918060f06030506090d1202040501141606060306050604050f0f011401090b040803040f0611071a120108030c0115 79
    0x811040c03c0d866100b0800900450b00100c41409800303580c00c082c40c56850103001290314200041e90134462881130a940d0304c96504c1c208802d80d034800a45010380540d0052250212021030360704400c0c00c51207204001420410000740c0640c121100f940c04c1d102007202d8030184000741040c00340c0c0b5030850090610070301001032000c01c59901078000354409000c5543e25002e90105ca040c03034100703000640e04841215401d0900402d0a620340c5620342d1680040b0780403490103a45140c2038000d86d011118147c5881c0301d00c0e02d170320b418000d05074428440d030341960344c00d040342c20001758181c402d03800514091000042e16180c20001d010480724041e000081d48010407003008440b145810400703041d2a1514408625404548011b07103101e00d013500400c45100e4003107404241168000003400884030f0103c3c200c4502c40d901d4030306590150344c001d50441340c0c0d00060814803c00280f6001c1649509003401441d00c2d14030911300d9120a490b0a030803044844e0000181c01420180034064601d003600110510401c4600c0d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 356869532 1250 356868282 356868307
    0x2070e070807210906050603010e060606040e07170a29310e0d14120f15031609230604051510091d04080a0c0c050604031b0b 55
    0x40181000c007005190b0112141c00100300c0e030002d5101c104003e00384401c4540345400c03005800111141d43c069868880741080c2d4901c0014160b000d50000b8041500d0b00d800c00700001c0351140000c042c1c2c014068000c1a41d014851441c850b180304084c5548001110f00040c81c24030070f101440340340700b203000440701c80301e1081d5902e54109000d80044116036240030706440c900b21a40f091400c0c0d00c4040d40345401e01e041641440403403401c403c0c021980d21405010015085c140b01d07406007903103440459880c200080c04c2d01016855060300511010200018400c0e00300000b403601200029090003000d518104219004c00c500034980d443c9542180488070b203494501d450988640148141d1103152200301080701d103590020318050444020f071181c055801d10800107014101c880c800c0305a011480200e41c00010444401c00380036950014140e0b16040308040c00b250510050b8000b541c140c466070100088641c0e901e00180015849030a00e6045009030100c601d096070310390f502c2101074100400c46800c2c07020 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 356870782 1250 356869532 356869547
    0x216050a063603030b030a0c090609140f0601140f071a0147070b0c0f030f0403020705060307031401050406080319050702060409090506060102070501020601061407150c02070e07 78
    0x1041d106038112a4841800c0c101d0103450128117058141c001c0a4000c018444c8400f581c0065851418040c40b4140ea902142c0d0100d6004403807000205220401055280c3c0901c000990000c00525080707001880c0303a0030300201d662010480410801000800d00c0402000b118030300c0110130101c0d540041c1e9031408044c881c802c412401c403803105060030b000f8800003079041070082c14213000000010301d01200342843d000860388842030030307200d08411a0024640e207180c24110b4181d00811040f440c00c40c1c55005202d81040400307801242980a40500413907907498003030255100e8120b03036a0210b030b2540200c1d2a0070181c001a044140910300b01401804007000001c203c1303410b5400d803400c42e004051003590032650fa000d0141e00960194000800141d6106a5003118400500940644841707417980401a640d0752a80e101c0e00c1d0150308030790b004000590240c20040c50b10040798920914001d1280c1da1011031b16104802c00811f1991451418601c560400550018010002d0341e034846080c440e80280144 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 356872032 1250 356870782 356870861
    0x308133f030b281e18020405060904020309010f0509011d0a021807090312081b1801081803120108120a0516020f03010203090c0f0a030807150216050a06 67
    0x507140c503c40d801004540e001580018a0a612030001a41031660032905101c20b0380706820030082689101200c1404a10031241120002460341d03240500080501000e5000280100a00d550714407542c0550001801103070704c00c2411600024424500c400031300c40790802040390390117a501c00300c041c0300140c403084017040381cec00f040160588050742c07841021120410305070002881c80c14403d107244d20903a04105a40c0c01000c3c82c81012040d0306140b24030140500482c40c0e0b48a500c4841051a0b400f5401046941d4101c804100000b049180c5500907074559400840684100c10b140c20041001d0b00d41448000651030b900142c0c3c920f420b400030b000910341c0c024140802c81e144403000540c011941c406454484000d00500207544a1902c051200d4944081c04504c6000c2e01c52108540400d190814452003a6540701c07291034144012070710b030b40000b009000ea040e07a003507608010707107248140e41c0c0d520300010600c15402440020003924250080c0d071300c3c0b48281c0d900c21103020f480ca004e42d10002c4503000c44 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 356873282 1250 356872032 356872069
    0xa0906150e0a090f1202010608010b09070c030f2303060307050429011e1d01050405150906120c0c0c0d020a0b0c10110409180308133f030b 61
    0x38103070f80d003080748035a2401d032801010101c811040418468040d040702007151804002008400c41d08010711a065038202c1e8008001017100b00110000380c001c40040c1c0f0f2118241c50810010b40708440c45c504500c0d4000c002001e008800f008000c1e0f1854101300030740192009a90500c00d0090068010b4100300d0002c0c9440074803603000803180c0cd16403003080c2c14181500000c00c1403000300d05002d4040d00548421340e020703100c80000205043c1c03039405007084404481c07015240743d004003034480c8400110b81258450f940e1080b0200502c0c00c40f1100400c04501804a032268183d55813800e8040a00e8900c075402e0355802010741c1d02031040903945c0c83c1403500884117100b2032180ea412140d9021b60800c1c2460b0b420155a6207007804400c0c1035100c00d03014009a4811200420220315244050401d21003541c0004000400b0800050004000b07282a004024032600e040301c00100c2002810098200840f4000b00c0000d0304580080304503680501c0d55030700070007070030100102089200845c0116800c034054110 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 356874532 1250 356873282 356873291
    0x5010524090421110f070b0a0f020c0612011e1d0406021204200402040b0d0c020307050f0615040b0f100903020409080c010e0f03090f06070503030a0906150e0a 70
    0x38080c03036100e1000009540038031240304040c020406080420080c84e00c00142c4600240122140c9002030504180d55041000c2418030500000880c1c1c202d01c03446010703045015a022840003621514081c00c010401d884001940750b04010745004004000c0b500e150100c02401c1040180d0181010341c150303142c0e14500c51642c2aa1181050006403041203041043c10141204000038083d400d07110141908240c20740d036120160b4581040b09a000343d00541400c540204421441000190321008a604c00350040d281015119240d2034148422650780c401c40740c1058040113540340ca0042c0c4d00720108400c41d0108034100030b04000c600c4051300010141e0003003010b14a00071060b401104d180b40115030040092120003001d00d001e8000b074020707078082e412544c02c1440c1001c440d040850070145040c010780085003012a000100b1060803001112150803510400080e00450342c2800250300c50b88a090010a010449141c40c008894540380d0b03550140311200d6050041614841d40d4507003010103c0030209 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 356875782 1250 356874532 356874541
    0x3100302011d09040f02040c050903060609061c08030601030c0f0509040b12190b09010501030215030c044106070b1504020a0f1d01050702060c070f09090501052409 72
    0x6444081c00d0b1405500c82000e00401c82005602850314840520980b018401101d039401c09451a00804030080c0d07041d0081d00c001500707400c4c02c0d0b880a41c80b61000b010307485c076a25018141403030701081100596003894004200640b03540c05005040310b050080c60040309500340b038040180503004080c0340520654950384c191103140c2e10400d050034814410710590b01e50fa21500e101074008039038144200c81555030f5000080c8100010322030070b030480e5009001c3c400030030006013109009030700c020801d070b150341c10900c00800c1e1046121041e060400c403048041c0342c081c100e0316040c003081040e502390070014100054442c000381c99801c181d031046944004003200c580c9491800c400d0000039031040642280c408210024100c0d8030144040c07003401243c82d044a8080040176200c00e0000c090314042c0420700400a0000500f000d00061000c0c0c401d42d02034624554846030a04030011195001100a0b5150440c0109009080c41040d8105862010f507082c00c1058008100c506e40480310401e1282c0801130008 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 356877032 1250 356875782 356875817
    0xc0303050c10020c03070201080a0e03120a021903051e04170a030204030219050108090102160803151221031003020d03020f0307030815060a080c03130819140310030201 74
    0xc0140c8610b00c50203548610307020380351980c0ca0700b0142050b4001101c070008100d02c00002e100b928400003100c0003951034901c501e0340c00885458080c2904400ca40d00f00031100100030b0f682c0c21008001859035021509040c44000000c15012110301e0b042d0740340440c1c05100000382180c40c0d41c26802e012501154859401d078905030000e00407a480607420481c403420414202110034280d00c2555001d8071402c6043d102c055840e0b00b02d0040046216004a4810b00013001c00c103808050750b400400c4a0b01d81d403802c07205d1004500c0000c1000c29041403503212100c44545900680300320000a815108842d0542c0360610b04801084100c0c40041d010303281d00011b0405152083c0900d0b45c201c00c202c0e00b141c0d41e9450615004001c4c80044451860484075210203040a18180d800c45007404010b80c0d0f101310549485004090941c006000c050402c030700c5140720400103c03000080e0004000704018924990301c010070145c800380e400d1441d1035101c042041040b178030242c0076070281e00340ca8080c43c00300500c40c61390441 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 356878282 1250 356877032 356877043
    0xd0b041b020c1210050103080910050a0207030209040807080c0c1302071119082e05090c01030b120a051b032b02030f04120c0501020601050105040302041a0405040503040e010b03040c0303050c 84
    0x604c48403a08000000c0144180c0100904000ba019118041148001e00084030301d4000c002010f001604150420009480c0846446400c180941c131810b1078844280e03561840380d0300030318862295800029260040d0700d0030071a0341c54503c034150001e61901109540d000e07034455020507150710400c0032450b101d042081e0144298040d1418400301c1e48614620b4024101000002c0454a40d50610100701038000300a409100d011300c40d040010300481d003420340150045c0c01d40d02130f025040b544140210a85280c200304100681d4050005084150700360b101c00f075400321203011340318042c0d40843d01022145c02170000100303030600700c0840300c0cd41588030035040782903200d52040028214804900402c0b1031084900740100c05100d140040070071555140117a880f41d1003440707003e001c90024001000982050740001c241c2c004800d4040000012400004080300d0707083c0c1d000e427096030010806001d8004050380031405400c030000c0c0c4034154a050360301d900c0d200165020003020040041040b02c3c100e0401c000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 356879532 1250 356878282 356878303
    0x12051009050a210e040504051606170c03040302030702010c0f170a08280b010212030124020a081b010e070b03091917070312020d0b041b020c12 63
    0x1031140e40d216007803107903440440010580b0019058a00211050303600b0441c0407030099a519600013040c050f000f003000420340204295280d00030201d1100300b1031a2202c0702805411a6106d201102c0982c400d05084a80000c280a026402c100240000700e500001036644042d42441c00444101c4a8601280c12030903909008110305400010003505240319000f50050000c40c2d078a5504903a6021005843d42c0100c0c1050712003035100400d041058035250300320020301d08044c01198543d0394400b110070b400703030301c03da10200f0751031000c5191200807105046003901010707140c0b00070701000301c40b525180c806100d070400401d0049101d00c0030f441148801e411044c1c030104c4440c152916070b5540c05001000e40c0c8100c6618100d0300035940c2c03420129600380f6a4a0b5040d4000703040400021429004c80165842481c0940030b1240e440c000d404003200c6800207200c0200c0c0c0321004600e00b5144024441500c06210f4249145014800f164140304d90004042040340c00840c5d105403400300000d41d0307030306259840c00c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 356880782 1250 356879532 356879563
    0x3080a03060914060d03050a02010618060317120c181002010506091b0702100201060f0b090a140d0b070306080a06061d060d12050f0715050615041205 66
    0x182025695030903600c01c00844a10303a90034080d400d2110244010f011007200c0041d403080002910901291041c00504508070040c000040d240d6140c032085d08a204480e4040f25405031280360502c2045107070402d504041d00e104094a0070021210451419840c005000161011010601d0300c540c040303800707035850002005090401142c81d1039a009000e0300080f11003074003030050309010408801240e440300c1c0406400640041c2804240c0d820060b0b4450304000460466484280214001640714030810082c2400810a0380e9004034a081c402c000207207034401e0501102d0032080318501c0e100c941c1000005a03100220309000d580e0f22200b50000c09c8582c01c800b419100b103a000345c00704416a48403030240d03880d00308494002e140c90455190700a400310b42150b04030022628240014441044403102d0303c0240c146075040c6586981c80140c0d03a003101c1020340b401d410317074070000c1500380c818410780c0d808c02e0301035440c1c1041c4100107907109502e10441c032030550070001082c020300a11506021001e2002e9094 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 356882032 1250 356880782 356880787
    0x7020d02040c050d06080706050a081f121205030105090105190806070c050c03071a0313050303072c060f0d06050904051507030203222102060916030803010515040308 73
    0x301c00030f10380e4201555048000b8640303100412801400900c40c4210b40c032a9444519280000e1001c40740301e0005000c502c407010401d011600c4114201003000c000c0d002081c0e40e03103850100342c100b40c80740598122101041c030004000600c10703034442c10540741c1516801c1d80c1d000788a0b540452003030449031a503402000710b80034070b405001c02c00f039008115a60302809007007295014001c0318105034840e0500d1003500d40340c02c3c0005151030707001c0d0540d000e154400303451824400301c580c054441c2429580111070760000980301e1100c2450b8015000c044600039001c03061034140c0ba41004c0007040c0c0611508030950716611000c02e03240380c6035006401c00c00c080d210250544203113080c03600e4010342d03505581c0d80f0308400c0060709000840d04d511a1003500d105051801c4c80c9820300140c850410020000d094065901d00c14295405103640e100000d9200700c1c0016600400181c50050102808e140750041000d20141d0384d09400c0003c100400c0c20342e8196041258000c0c020782c03400437151094481d80e0b100030f01d5071402 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 356883282 1250 356882032 356882051
    0x2100215010803043f0813080c090703140601030e0c031c08060d03050d0510032102010b01171f03150605010f0e06032e0e09070504020304120507020d0204 68
    0x21000e041101c1c3c11107601c001c12840401540000f062880e0741070745c12201c07032161a100c85820020480068025903480307240541460f0386008810154100d01042d41c4080e266a00a06201d64000ea000080e40b07020896407601201b0700b0f01000c0068851410113484458400d90310a051240ca2000c190080031a0541c4480c01071040c20440b00d030b500c04001c035038803800255940c205100e000700c1166241d590141703409081280701c401824013404040400c01000030200010b02203041c1140d0204180c5010404c124904600a003540c0d0742120150403c02490000500b04215001080d003203e00b101d11850503a00d58049404078030390681c00070b4400800c03d0b848074051800ca5100740c05440003a45c1312050701410480944141804201068100c00104002290400030640500c144103400c045042c000051040c20f03601c560f042c0d0820603031503513413006115000300100240030007014240c40a50851031700c0e84645c103000c182c886580040c8440029460119a00c0214040301c05600510410680301c4 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 356884532 1250 356883282 356883299
    0xc050c1011060f13030c0807080a080906010801020913090212120705010506010e0616060908030108010e101a090912180118180f0b031002032508040210021501 70
    0x80301c000040300d601407000030544060340152241d11030a6101c2c811a0b61101c80d640840e420b03e02c50b0303401d9504640500803400059202d0009044003c800d6880d11118202900d4460a040041c0d0126a03580c1c8104480000c079121854001000d00c0c0403440001c0b0750320103002186102403900c90300c4c0c3e064040c001641c4010152a0081c2000c0d6005200810080c0d46e40c00c01503c0d80c51700718407050350000c8203119114021203a0708101005901c00d2501007065251036561101e10340082c0c02c084050f94503042c0034003542c281044952400300481f5811f03c04420145c288220703040c00ca40a660048105000280c8491010081c200031403004e00500340d9076408082c01c20b001405181c00301d80c001154603041419407020451080d0603914108507403003d80c16117059000041122103c80d00159481e000c0004a40d601030160182081c501c1501507a28174040c1c0a0700742200c281c4044007142e0407240c80183c0f14543c404900c40c0e01c03990550702c50f019403280b11402e80c80c01400741000941035a41800224140a = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 356885782 1250 356884532 356884547
    0xb0903190614070305040201020303010b07030201021b0304060f2c01110f01021e0307120f0e010e0307020a051f2a030f080109060b18060f041401080a0c0f0c050c10 72
    0x4000b00ca0b0b030081d1507280d0f0403070a984043d14040e005a20500050021070203210007420120303c607000042c54203040c40d003110385840c070106c0f00c07080c10307000850104820741c0c0007180f4620309125403804400928400044948451180e00083c03c4408942c1080c6e07510390280c440f0410181c1e0345411160003e00200300c1c58040e610007042c0f443c0142021800140e0f206020040d01d003c0d007401d0301c40d142100034968020008200c5000350701d0740141c44a003000e5510600780308000900907450041c0d907840c8654014001d040c903e81d4000c60044090911030441010503800d01840c0040c6c503d01440d0300020582542c51040401c05581f84a1445410081c00c140d0014180c80c0d09a44685606160741c2e030342c050004c200c034640d204070007144408020200903c1e800c000c60280c203400042015052008070764240080d50040d401c19124038040e180407143d25078005194036400380b52090705010385912443c00a22030010100709005110f83d10200004100f13003848050b0900038054092118900180c00040919 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 356887032 1250 356885782 356885801
    0x5151003060c0e09070f020c0a0612150b0f0309010209060d0b030f0f030a03090507170d0e03070b07020d060f020c03071104060e010506030702030f040902031602010c090b09031906 79
    0x250b241041018810b4016542c80d0340307100c001481003e440d43e480b24140e0b00e40107204005030850103005541805943e44d034480d600030303080a948000200d003941125100321a01c55024000142d8108000c01c1880400811500024240b4418076200c1d201c00c59001e0190103040e4007a540150040340e00781040120342d10400e40f95004604036030b55000303807600340b03a00d402c00e2000c00d00f03154000708119240070b4000e1700030b000c00c281304008813500155500c06100003807890000010903174200003034043d0303115030000d0b440c600401300f00c1c05410321614003924000a0311850400134040d014511221040c040c0c564030041c0f2804450380107540d60a0034001003034580c0d002402c21140b9180c0036240c40640e050601c280303003e6844900991010364201020040c80d030308000c201004502c420030140c440d41c08100d0141000b080072480150312410850710501c032280440c010b41045a00d854180c1c4c40f420740c07250680048400d40612554cc038410240400d0a01401c2d4010b03001002142208070104046035000e20b041c0b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 356888282 1250 356887032 356887043
    0xf0d110c04050103110f09071b02010915030c090e0915060607020411041a07170c03070c0f0302092505090105040807080d140f120601052208060c040b04090905151003 73
    0x4e00980c2401c00082c4030083e08d25000048200d400103401f41206003805280ba03005060110321150358030707480c0032039170845595034000070380391422078401a81102d0703020040d1612031048141440d1481a90b03640e04072428400b6908881880450015144c2e1011104d45940251040c040e0100441640364568014840c1000f0151191841d103c1011b400c001da42c0c650f0360040c2d660580c1a4030150360107980c0c1000780d0b00c007060b002c1001600d00280702000500000c0c0351080d120682c3c03a2450041180040c001442000c1110302101c2001c80d035540741e24503510b420700c40e09000d502d45021800488840c007680d00301c020f2522a04001290410b800144400340c00701c280e98244c0c0d03a52560500e00d015008903004010010014000c10900e81404041981d00c00010b140850400b800342e0509641c0f03000c4d1a40c03d681d4400b1151090010711803d02102d40c0c4070f40c6c02d500d29440c040c40c10f28208090b1103180b15000345169581156410401c0500000c1d100d01c92030141e4840324244003014011009091004440 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 356889532 1250 356888282 356888299
    0x20105011e0501020a0f0302120d05010302030d080c030402090414120301090c0c0201020304060c15050f0a0509010605220e030406050309010c03150608040507030b070c0c080f0d110c0405010311 85
    0x124868409a500e05850041c4c1c003400d20f0b540f89a89500703c612100000301c003940150740e0340ba8096914403000e451200c2203c6c0c0082255491801410f040c4007041003964100000d241c00c010233444800708494106506640c0d00c00542d480b0305103110701e0140e0140d0100140660081d81d051600c00300d000d141a1135426404100c1c85881450665824000b10f030000e0240e0001c1c041007043c0c41c0928810741041d030080c05101280780e00c001004040780c0d0200c4054000010399401e008041000c0e10942d980b00e250007000308101800d1000160f0341d020712529804003034000c15400b4a032100340c0d410010303201103010201c83e2602c0c2c80702c6000d46150000c50301e404241d864405059000d510a00690171100e10300820100580e09003001164000303401030058405108908001000485800c9001d02c16201030307850480882d61032404021500865002c1d128580c041425440320207000f049807030b5a034810381480050724489142150401d0380318002154042c1c80c0c0b10001040c0721002e00c0303144640c2c104907611503 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 356890782 1250 356889532 356889569
    0xa05040f080601050307260a0f0501050f04050601090c03020c1009021f1407020f0a06020303070909020301030b0105061606060303080a05070f0c02060c01060b13050906060c0604080a090305060702010501 89
    0x180e80b960240328080d4140d002035000c1000d0355205000800048654216040d82400e42e000030307190800c880b1003103682061602c440c0d030900000703205064000f502404250442d0a158075090b603101c006002d010211981c512400a20034007a40c100c8140c3c1c0c201100365096070000e802d041000b401416000d03800743c8600300510150082c0000c1040c039040080e10792016061060020a000307410208040381c02110001c540211030381c54040c075070002c05065004541e41d10704907600411010301940125540c80c0140700600c0018861422641520415501180c894030540081640004c0300715010348403520300340e0080141036206403042e203c0e2003030764810b12044d16501d01c100c400c110b520400c0310019202400e8400103140caa0b0040501c000c881c0b0020078055151000384401c0e900030b02d1079403200e001ea000d040040e0704005804c194802d408403403280c203183c50035560a4aa01b8000c2c0024802400020051551390156040002031604a002c0f2a8140381c5084080d000b810280180e180380c0d0b603a145c004 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 356892032 1250 356890782 356890799
    0xc01050912030a0c05120412090605040b0915130f2c070f02100c0206160302070816020303040e01060c03080a1107030507110303031f0501030b012109080a05040f 71
    0x8030155081c249416145940fa98000e0000302100041c1c0001c01004001803698403420300d142c1c03070046000d104405c0c94003064542c0900307020703480d41c003000078410280800c0043e5403d0f0402d43d4410700b001d45402c442c20040c5c0001e901244608503000e90400c49100c0c0211745070003919500001e84a204404c82c1942c00c0c94441c0c1690402400740c0c41c0034980081002440c80c074400d50341c0f0095290030f0300484a50940c501d02c503800351208248440d0050b402441000030100c5500c4101101c1402400c04500c1c04099840e014400c1c0b01d50101e01803091507180a071011920b00b0012034005100800d0000340e5541c56000060103401c203034000783c000680c0c138808500c100c0c482d0701c40c0c071f654802c0c030009180c030341003e81da415152034101810540e0808640c0301409882d44082c0300039480f603c4507181580c1c2c1c25801340c4480c19a50140c4d04820704051810f80703140c001e640c010945481403003800304404400301079600c030a07000d0100b42100828841d4003140e561596034100c0301510641d0b55180c2c0a440a54803242207 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 356893282 1250 356892032 356892043
    0x15030f0b011e0b03070e2d0a0f080303060108100308040311040f062301021603080a020708010e07170a1505090d0201090206180a030f0f1e020109180209150c010509 72
    0x7860301503c0108041070405009a141e9021100041c1c0b9000028120080210490100090035500450710310042c0340a4a0008124409407071504205110701f8180f5544540d2800010020741c10f100240b00415004661041040000e6a0210740d40782e540703441e0700c0e144032400c80b00020703075004900304035100c03c0d049442c0c02100141c0300b640b060603154803500800800710312401170300107040d40078140c11000301f451030b880e070900554004c1c40307160b5640c840c003c030082c07400045074011812039140541c0c0d80203022002c1101b0080301c0010005442e00d9412841c1c403030411040903802001508940c807040c00c6501c00da04130501c00d40c5504255a40c900600c1001ea0036569241c0c1c0080d03000d40700308a07210144212400ca00a0b00f1780207088200c2d4152a0390301c1107148503003400306460b0a403450442b681040700300541107600f20750141044c80825119800a4941c00d2140103280790481c6c86a07655604015640c1940c1840d07030020b19503030010354070801e8642c460b0b00c541d42e000011b500b031400003103058a00044 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 356894532 1250 356893282 356893289
    0x60f052e090f08163303020c060c1210080d1214090105070e030a0c120f02060d0207060506040c0f030f020904230702060112172808061903030315030f0b011e 69
    0x202128525040214207415540312001642450ba01340294518803404000c00b500c150ac541c1c4800d07a03075094003094801e4601c4020968800c840307040f401480407903000300f1b05400c51140d6040142d00c60f03402c1e10b58500500515810b010580c41140100310900b001504294002c41c943d4590071604142c0609044d00e8190206d000307400751110990802c00345044070140350000d0b005096241182150345d00050681c2d00004d4005203554000c919041030020521a80d41c000c03a04540421124407803000103052900c0000c50107050603035659041402500e41e40496411140041c020040d0b280d1840115a007050108020203295420800160303c00e4000506641a0f44060400c001100c0d1300b40e0300c031085082800441d015981082c41404650019842c52480c502450f241041c0f01003141c800c001c149203401001e0b5031007000f0341c801c41c5401790498040d00b4203498040c680440c01c00702c00c41d91840078108031390008041000c0442e1103801d12045101d07080c1a030f5259445485481c1a1000400600c0d000c2e00 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 356895782 1250 356894532 356894579
    0x20a0305062412090106080105041a240405090c0a1d1e010513091a0115020601060e010e041b18060201020f0405010809010b0d06060f052e090f0816 65
    0x70040c0500e0503e1140380360322615100001c01c19585820185081d103000f81d500719413442a44a40184510003002c2481e0312040403940401820034502200c0c1442d0210310566004554035008298204400e00080139092005418030b980700b83d407a14117010b03099014403a122900d0201e4041850180c591404240002c01524401f0403a4200410001d03200d0b14141c540e45002c0e80c07804080300240307014007039902c2080000010b4000307615000a11004080806040086400400040c00f00c6a08405900503010080c80c1480b983d200c80c0001c04c00403d2501e800c81c00282e00c404080d217080c0c0e8000c0c5200d1103030b085144848036503580c1c0c0d442a8240c0c000d00131600c2c44124180800d1105500ca80b1709558000d11031400416100b106801280007000b1206081c0d802685822091085084120b4404010641070321451501c4030075030410b40840302c004c0c03112400341900c82030514078644500707512005820b20f0181c4407280c50307803130000d1a6510101b078803000c0c2101600d400055540072040c0400c2d190305041 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 356897032 1250 356895782 356895787
    0x90105090603030d18060605040e070b09060f0d050601020d08040f0210051c06030c0f0f0b03071707020606150a050a0e0a0f0905040c380904020a03050624 68
    0x10010900380080c882601031105200d01903044100e8002e201c003101d0480620601c420719420040184c0c0d0340c6802550041e030409070a0001001e000401400711417600040548851540c00080e03044c7c451307207945e081100c00100322440c441105a000303e000360000d800700c850700721105105550b1900100c8014103c10750002070748001d424003c0ca441011091480d125182850403d00070445200070b090710300005644003002d100308800070400178044c02032a0305c4040581d00d03141101956070b50030b02403507401220200c0400c3d0341501901d0420340310454040000098908048000c1d03640c030040303905c0ca100c2d0b4455a0404418444030341100c0400c00c0c40e41c0c07100d18002d0241703802d54052140030030680e0004189607001640c0c0e11391410364409011050000304260420b0309100002c4982c5400604113426103c0c25030b000d0302d0301090b91010304070000d0300d0748042f14450070440e28140210240290080e00002e152140282d25a000034032442c003c542c0490210b00407400004494118460344183c5d8808 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 356898282 1250 356897032 356897039
    0x604061d0a120303110405100804020301060608101202060909010314060f011206200a020a2001020a02130b1305180c010f1103070515010f081f0c170c03150f0901 71
    0x280e00035000c2e954564090500d01b40e0f4410100d0350400e000d030a08070000d400e00052004501c1c00703000d00f5005114615142d40a07062034028840010703054403a1000c0d158096102004640f1404d00343c82c804480100b084203d5070b9241045002c0b01050251000700d4021000040c010100c6100c256040c1c880080c0c42510200103542c8010003042c846e2100081040c8002039890040c070300100424403c01d05901500c1c8911440c541090b04180c0200c803552240b10001140e000c0341d90000781b10030490303011508044001250000795005100b20301415800203e240c006a190610a40005008640b1995600d485c00c640088140c1c076803e603800c0207400100141050308000380725900380032495141c20241d0f4580f0405503a09032501c40e41c0c3d103646107001d204000421030700213140204001007155401608030782e0542c20b085c203800c07980c000b00d00100f0b40c0e9402d07003c2402803003036150040e800030100d8060094100302c080034040c0d400c101c406800b8810b07000d401c20040c1c01d014407000101c5502402041c643c2c0d00303 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 356899532 1250 356898282 356898287
    0x3091706060307080a0317130c06031a01031406190e100617040f1104110c0109031404060c321011070506010918301403060409050c0604061d0a1203 65
    0x10090304007d03645101e003408c60302081c507645010300100359944000070514807440880204c0b00b5060b0800703045c189003e0b88881c0d00100304031256403140c4100c4a4021120f036041ea46d0004400035003151303000301c02500070003422910940125054500685403014010180400040503070400c60740204050000c0c0340d9240051440c60f514290780030010400b082180070b100c64103500340c01c4120854200e0707445034039100a168000c60101100780010b880382d840c0c47d0501c0300280c0a80c1d8480340040042078294852298880446442c01c80c002100010b049075641c04030107240e48400c0040d000600314075203102e02a04800340700c2103402859000300a000300740c1ca0490710000401d18080380010000780c1c1030048001030261804030903891240c550320360075400e01520341045454220305c10414004031603a4514031146200c1902c0c1c3c450000c84000c6450b0406145c0a800c006002e40c4140d00518086004110944c11002a198034000700c440d900d030503ea0f05040010000a512400710000e2080381c10f90003003031 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 356900782 1250 356899532 356899577
    0x103060b0a023d0b0f0607030c082503121b2a060e0304031401090804090e0c0603150301050a090b010608040f050a0803010806090708061303091706060307080a03 71
    0x140c0490708840703141d103240950b400d070404081c603003e604da980340c24443c14a05441c039545501001d41d07215081000540d40540091450200603040d0302c00894051444080202d440d20030220201240000410500d40035010070034541e094000541000c0e5a034660856940d441461a0300c10b0344c58100e91100c0200207410300c140d55040300c958a20580c03148002ca26036000e10481c1090f48002595a5072450404114a51031281c440c16541d0420306401c010925010994040d0303035070b03440c000910b0b0040440c6140f404031042e15081e0888008001c1014015440310902c8078207100380d00034481a583c08051100705c5803c00d00007000800b4a000600c100da11a6050781c2d071041c03145102e88550015034558926000f011041203508400010041c00001418081c0b25001122000181310082c1081030050720703910000c0c54007a642210a0b41c8030145845a46c0d40c030300908202002400030110040041d88840d002c460307483c003a100300b00c4001947c410000e40401001d42554650080303480b0017507a2915074 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 356902032 1250 356900782 356900833
    0xd0e0f010e2d011505090702030a0c2315220b04060509032104031d0a050112110706090201020706050c06010b181002010f18170d1808090103060b0a02 66
    0x30b00d10014030000a8000744200f004c04c0d50400040703036000c0d150400f081807038800208004119001446034004c0140c0060003140070300d50159841006030300342107005000514440100742c0c030340309444101010252140030580140d003003003202e1103840a0361a070b50751480145180107113214082000200884c2440e88210341004e180b8003035a1030800c10300d07840c0407606107108002c03400500c0b1400380f20816030000c1c20042001512011070344218003840c0028607840091142c50b05010140c1840c1c4040301e03580d8440b40c05440380b5200d0340c0c1c0b10006030524400034400d001c1c04034051310942c00c002c1140d6000d0401c2d074481219503402070107240c0c240310f0400126003000d0f010b18281c40c0380004040140c1d54180c07456800c030869500020796481c00401da0b6041e204c414100c0d2604044044188000c922041c64950003c03442800c141d5030381944c40c0041c1d001344903060100806214004561040041d0302005255014003642e00b444000d4403084540024800c107844440583d0028801703020824124280240c00c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 356903282 1250 356902032 356902093
    0x30b0301290f03010b0904080a08060a051e13020d021b030f03180a0204020c0c01030f020f0a032004030b0703050a18020d051c0903150c171003080d0e0f010e 69
    0x203d0a034041490242c1c161008c4500b043c1c013040203041c1c558084a039a070311401c1260045401807030400880e0314044d0300011000211350340c2038026501d440da0111800000071480d070440d59821150301c000c00a4011151001070301014940d0b280100e480001503503200304071b00081518540b51404010400b01000b40b02040c81d00564180c140540c2c0c1d2840541448440e500241421b0f042100004080700c0c0c20140080241e8414000d03111400396084c03c2e12880300540c00c001410b41040d01c480004035900740b11040d110000080c020040015581c80c480c000c128544061209407280f40104040c2d130701e56050890b65101c07014110f40940740c440c5104441c0d5014800341c6090040011800e07105401c80142e0f040418a02a410010000341607074994604403510707401c00008039004002841c142020030180c1c07402007042c01140304000e007200000021940110a02c1c0d90350540e40d0407801401ea900340f0f0700d280d8060311544002c20441805041911858039000d4160300300131940703000c0703030481c0314002101 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 356904532 1250 356903282 356903291
    0x18091a10050d03050306041d0318011e090e0f04051009080d09121b08030105041e05010e010518060904120e04090b0402040c0504080c0f010e0301050403030b0301290f0301 75
    0x1a15114002e0840110303019540f040e40d28605082440705496117007501d005030134602801000e05413008000c2d44c9210450390380344142c40d4103003401221614005030f1a41400f00090f0382001c50143c02c51006c900725404414802650307030700c40c10075602041003101c1c05892508080c1050b104a0f104d40d02007034459101d098a00c3c10550203400d0743e01120035a1004030780781d10f80800c0c1400081e4001c8107401d2140501070108410030b00942c1c510009000c10b10030b55001eaa1250503012880303002d4070004503070035168001000340d580d42c4c1c90b0412511000303100300381c020300341da0001038046640785e41101e00c2204098038804c056180c5540320310307d44c28017030248030070011151802d40a6a443d4000c0c00142d034004d84800f02c06041500401044440d00ea0554081c08400c0101b0452400042003541800c201200c6c4203404460b01303001650110846c5030f100b6819440c000c1084101601540054a0b414081c1c00800c000b142c84000b0144203d844d00844c2c600d001840c07551103241c60200381400a20071302030300118 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 356905782 1250 356904532 356904539
    0x70e0c0403060f05060f0d0c031202250f060e0303180a170604021003020a0212070f08030f09010b0a050f13110a050309150415050a0b0a0b0418091a10 66
    0x100320f410712114601056210014001145420b0020302c01c001d004680364070a02c011b030b9503211030325441480f00614041c44001204111402402005580d0480c5505102019001c4c038842249807483c0c003030710756507004115000c2282d03442a0b041460384d0381d001e40210310300704ea603000c8245002500c415580c1d010214003000305101d40345501a903904801ca2000b4000c5041c244104841d601507a912013007014810b0101f0540664001801d60120300101c0102e43c0c0ea0400c3c1c1000c0f00c074010301c0600900302d0b000000c1032007000c5418241c25840784070118001c001c450a2001000100e40c51442010362042120710105d00c54034100e21a4441094403c800064075000070110b400150401c0d440d031001300b0b001000f0800280c1040c4040090102d03101d1280b0403604c0c180d941d100080c030078503da1550035507076007000030780541070365115004860000780441c40d042d5856500d01d1880d8414013031790740f111a8061746904000c1d603d0040d0321502d0f60029034013040104c00410060b01110007410524003518000001 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 356907032 1250 356905782 356905793
    0xb04060306020c1005010b130e04050a05030415080f0c0f0f07050a030305060a0b120a1805060907060306060918090201170a09140d020d0e010905031204150f02070e0c0403 75
    0x503e1800c0c205805441c0b00e003c0d440441084400c140c1c000c5009100401611082141803ea0f000a0304c0f00b4511030406600c03117007440f0385485d0f000300c0020620b100c005404107268401d20f090f15541c2409684058a66444088134070031400c1c02d03030700c2d41854041840b464101d0400c2401a040000011003074a0501927113071070b03040c54802060020381c04255124144003690130300c0c0c203051000d0010f40d02c4051030841182c1ca83c803010078000f00007015503a41d44d80c80100051410f0004085103401100f11240d5042440d100ca0b26005c0c140b103500003103454420700041c454020340c008400c59500040c107410405070400181c020340007401c002c9040000b0740e44011004009000c195008198104000840c03501e1440c107501e0600030608800b140d45d200c020300d1040c1c4c56000880c001d205880c0e00d0001100b9400c0c0d801030700e86000e541c012950500550f5814083d203103d540252044030341d0300440c0c0314071400b0440c1c00d0741d5445c00103048070016005290107101070700b115203140e0b030084503100c1d19915040d540d8440 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 356908282 1250 356907032 356907037
    0x20d0b01060806060406080a0f020d02070606080d0201140f041a0703020403031704050d0c050c060d05040c09140a020f040e040f031706010c02090c0408161e05010c060b0406030602 79
    0x84480aa525006200d020b0b0b200000550141050716100d1826003031400c06802400e00030041905280c990020043d0400c0a0301601e032192608207080d9112022803525a01a10070342c01070143d08d01c00e25580d0032405205000300c48407a0b0308043d01da02d480d255031102600a010061090380c840d10040e4100c00c0c10700400c2e44507882044c46a0340140c03540d0039440c0042c00704883c904101004031849040c0004540302040f0304035000864201186484002d103012800c14545040d41503100c400811078240c0310b140f94001c40d2181d40b0880a40740700c2615420040100d88000c010300c002540b103040006e0003104258001d001107010030345a1410160b60307490818041408940403110060051a19000c2603040584001c5220001c5003410003850700c500024540c040c041b00c0a0f100d011148049080f02d1b188004580145c8000019168640380c02c084072041e6041612070b110075140a000c804820858800d50324098600517075515590442d00d0311080d000c0c1141900072a805552200e0010004525100 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 356909532 1250 356908282 356908309
    0x8010c1413181b0f1701270b0910090e1605060c0f160504050f0f07030902012703050f0606010816030e101d010b0307060f05250b0606190e010c02 64
    0x160350b004100307000d00c024464610180b030104490009170040c01004001460f80c02d0030000c401c20b07840404219200d0030041c00080c2082908422400306200b0203201d40041c14044c0d507240c45042c000d00040c6a2019070f02c000d401090206107072a824107129030b14001c0010540c04050030120b681c1618420401d50804640006004105100700340400150406005090b0f11880038a1305105e18076003500c3e852a450030050941040599130181c100031607016051001011003110041c2200c1c0304c464040503841550760005469910030310050001086000918510406040c2e440310003640303c909030031020140c24000d0f2020702d6101d00800050400800000c0c400c081510008124000005503c80c0f041b50320280800e4244d05001c3c50075059207000800a0448001e8913041091084000007116240552a07940c450700d242c82141d5400c1070300e52071051520318000c09000c41c480c0c07104d1080100034811f00340220f0800700c090351100c4955015161048106c1f60604180d00d10f1043c548c00110301c1d08003802e = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 356910782 1250 356909532 356909537
    0x3190c170706050a0207020907081308030108060a110f04120c080619050702010606080408030c0f2206030207031704030207170303091c021b040b04020408010c1413181b 74
    0x1511205100e070b41d0040b0ba41010b010300c01185403004540200d855100001c014105000c0d00c5004274615074058540c4030101c513040442182c032940c481e0562612581d09a0758040c00f14100301440303400d80b6420b4103da841c80710070350003e440c4c10718046406440c3c4070120420303619200e1701d030300009620205204280c0300d44c95001711403689907900b140b0720b000c4980242461045a141043c2404091f400c41c5c3c0b00c0f034200ba005040c50743c40303a4940c80d81d400c080c032a0f41040200180c0201c1e4684185413440c00c00303280380e8644400c2d000c0e89a1158012030803405032401c05400116040c204403200788004048907001406481a98070a0362548a00703510003450031001c10a50344004104075a00005118000000c450500101e54104041c60025540c4240000803030600c6032000940710a656107600445816401810542d1a1a0ba801d1494020720045040001044030682c121040400c0c1d40112180544090303840e032400c17400c00b40e00c0b0302003100d618600c440d00c69880d09154240d4941031412030a0f00c42a0713 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 356912032 1250 356910782 356910787
    0x30504021203031b0304060f0908120a0507080c0d0b1e0a050307030525050d0b18062a0d061203140702010c0308062e090f03020303190c17 61
    0x2031041c003029505501041d91150414000d021608100c805604007658000302495200d45950510350010840000d5801a1901d480c002800300036544000d804103c0200c401d01826940b038290314000da80045070034800242d12800010740140c0800003070002c0e00d1010000007040c03558940812002610302d070454010000207034400c0440e1512040002c003504041d4081d00e54240f440e5213040d556003042e0071900401c46940e202c0c190365041440148000d20340108406043d1202c0c4c01d0614005400755405034404070011088154a0b50000d4918060380d45202025901c0c0c41e140701c80da44448080061500010003001041100d1806015000190002e62010400c1800324038002c0c219044c070f52443e4004240900888015070380151100000c6900b60400302d816542e00d4000504002c0220b604410300d080250b00c03040b2140c0800b19050322070300203848064070303591121a030b00010382c00c6200c0290325600410000d61984102000d5000d03c198a00f808007500c41541d64840100801480000004201 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 356913282 1250 356912032 356912041
    0xa050d0509160f08070306020715020a030f06140916090e090c04050601080f060d0303020405040e0c0f18042a060c0213050c03070c080c0304230306090d030c090e070305 74
    0x8a084150080580b4203c4260b05481e00c80143d4641c2620320018107403e0340032070000c007404016000c8070841c00c2d00c5682150303107951950b4041c00600011420350016843d0420104a1101c15035001d0004000205900b800796201c22815072000c202c0c060101c100708520b0000108001e401c4855030040d81004090302c2e624460350240400c48070001d0030141000503090502114440f40301403140c003c1c070256a0b10012a00508055020381b003280d02680d00103282241c00098200701240722401c0386c4045034002e641c80b4003942080703907100c0c0d4140488107031000400810005008038547d03018444000400094191510015001030030b0941d0103500441c641703506400461a00c0c00c40c0a5500c44142020440703400c103903000300c80b81d000040041c002d11160360701c0c0e10103000705202960240000002113035501d030f444d080003920705c10300c0840c4142e0710317a0007002400080c54041810391260b00303044002c003209d1502d003504230b001d031501940c10410b0112032800802c0107020807006901c50752460b100400c0b54140f = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 356914532 1250 356913282 356913313
    0x180503190905100c020a0b0f030411100e1e0a1502010c020304120f0609060501120c0e06030c1009050405070e030c010f05090103090809090405061e0f06060a050d0509 73
    0x2a1203000303800c1000384101072007580c0d0769080d21901044a46010700c0510440c0c40403901d148000d803c107402c14a008034504280d50a403000440c460340c4900201c5401184038020300003124900e0602e2404102000038004039800c00c074485c40f0000290001070412411034001180703508030705400c00107402480c506600c4901d03409015010300d6010600c0118505494031445402c03c010200c0003c024940c150f0403481402400d402c50224039822030020013065960f0002a9030071210090b0450743c11041203000582c3c14030100007a403150700040d001e040303a44091003c04c0f0300902034020700020300038042c4003ca211b49031071141d01d114070415160181c4699031001018501261140102e04110100d002071a0199121040d6001c11000f805e020a0310380151420384424003407005083c0d00145080200000d20400007a85030007007891b124650302d0141c510740e840c90540412204002d16076400c1e00403e1890400d4401451030301d601d440c103079081158540c016025181d0545140809600c8295100150790 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 356915782 1250 356914532 356914567
    0x4020a0806011b0201020d0507050139210921020102091f090e0a020c0f150606040e0f0411040509010c080601050c1f11030405070320030c1003180503 66
    0x14116001550f003c00d580000d56a0f20f680c01000200100451088100002504403074071346080680b0003441c0074410142c05440da000c90942c46055903051001d104400d014481c00c2c00d00b400c02c20074400e05154202c80e2000074051700b041c1181c40a5118448079070368820540c001d48426590f0b400960740340040740c10083c80181e190100b08c60400c0806150801c4d0b600032180304100c80b00c2c2e039804c43c0184d0700c010303101d0300900450714080624007880410b48544200440c018400703c01646003481c080d29400c0c280f10342c0380914041c0d400765283e00380100d1a800c03030440c86558810321134110072107400c150301f020405403101a1807051041e0744600c0c4c40e1640c81d401c0303505a50311010038030301345007492201084959a003000441400c0c140303640813898030480340c02d90017400000d03151400c4940e5070309052404c1075407001144810b0305e4050006a00b110b0810200c0420340001070004c1c0200072002c3e0100c00c01403003900d4018004e0500d551180820850401c040840c0c100a01440107907840c0c0c0100b500c1200703141c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 356917032 1250 356915782 356915807
    0x4020310050603060604052703040e07020601081002070c050411030f150109030f020a08060f100906120605070c020a14031608250b190f021b15070204020a080601 71
    0x807418601004101d03200060120380c4203404a41c04140790b02c030041c820110110390a6505445d28a586114000c04c000100400440d003080c403100040d65074048040340c446e0750a00481c00340c0d0f0000000586516126000b41020324003c102209450b9aa100001d00321602041d8406038402c0c08010440c03201c9892005617031065034a10710108140b05940028030604143c00001c0469800c0010281591185942d120141a20204036211804d00c6003503c00300b103504680d01c10140310000c80c08600c40304940103180444920015107002c4c014990703515800307450000d0510040100543e40d00002d695616404001015500e88068072001d4500c01c0c50f080c104004030203407004605000820460100103180c00c0c0c858101400b80340140c580c01000c2040140541c8009100a80410101d600c2d801b0b21078201516441c50f00c4840c08a80516010390312411503040d5400740d180000e1a420341e6043c038205080700711407181c00c00341c0b070042e151340000e00703c0e0040085180003c00c0750080041030358004000c000d40 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 356918282 1250 356917032 356917063
    0x1f240e060a03020609060d09061812170103240903050306040609050408040902030603121801120e0619060302030118060b0319060209060c010e0d021b1c050c1503040203 74
    0x140360464004c240140f081c034010500419002410042d5003d6a030300c04450a94884e03001d00807100c1d03101003190340e400c0150085e0b882400c5881083d00460188944104011007150702c3c00344c40c0c0c65038071200424040d83c0414a07104801e20b54030500094103105d056031070b40c825112591207003054070a0104640312a0080020343c2e2521080c00041150792003130358111072a030761000da13603a80c59201107420041801c0c540380304100081040b4400c0207240c070541c2c04041d803c4c0e81c2c400e40d02e5108480381c0290f0340b040034101c100c1d4000c0008240c010b003859480b03070b40c0c5510085012481c170307079a41d010900716242d203040110351130303c51402c01c02003040500401c0c41e4031070120018a01c614032214580d00c01c0e000054001c048660000d40d064241d201c8030181c42000780075100070442e054401c0c400580710450301da40000103004801c104648000520104025860003401103c401074405000048404c800841030f1014410142c45000c15680c28452940b0201607105460310fa05092060614040106003150380 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 356919532 1250 356918282 356918299
    0x1b0f0506090a20010e090a02070519020d0b0403020f0a03030204170d120f0f0504080909091606200d0c060b09160315051302070b15031f240e06 63
    0x4120f05042c040c054207041206a2001c155030001601c1c070081c2c84000341e0b0448003602c01c101d07000d038040d03020b4404180110240c0b682c82c0a03501d90900004110b402c025809140780350001c0103d00c603582440d038003600c6401143c1d824410700400743c2c64500d00c1841140041d0b0005014010400e40c1d2000340b100d010b807c4000c11260340d103180080c0c0344000828034501340f00c0c0d40300a202c09031842a009429030310b0300050200300d079007445d041000f0140d0001c0304039030060f00034501184044000007540c110303210a91203105481424003008498600c400c2d1041c9155008002050320010b0041c42407142e07100c102d482e248007001d42c2c0d160400503104080501c41c411003800007040725020010703802031103821083c074000441d22840e2003081d0003603490b40c00054101f0f404000b0040d04100a81c01004000d000c1d400c14680c0c2d69130b0001e2414200d071b1108407560136401c41130a680d89806125007000c2d0320100750102181c01a00180c0b03101000355104400b070a941441c1c01c4c00c00c0001501c0b449160000001c0d81c0285 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 356920782 1250 356919532 356919553
    0xb09010303140c01020d1e0c090e060d030e04060f0f0812190513270e10090201110d02031306020f06011a040503160302102a02011b0f050609 62
    0xc19010b840d0010000c2000002244a020f01080d41100c62409154608120503030034a10502c0085284500d05102e170f030328200c00904803a002c1c7e0403510823961111812040caa076414248066451413403c210305000448450070f189030350f00c0c040c180190800c8246030811074504540104126401d07880792409410900f01c495504c03003003030125041d401c95101548004a1904002c80f610311030301088040d0b0b84500440404c40c00e2103a2219640417400c0c10340e0100c4050420401000c80d05802d01c0445c00d50702c10703a0f01d0550b4214a80150b29810700504100404c0001105a40d09004c0114030100c0103810000d0402c4551825070340c0003000c5e2542c6c1c40200703204030b00b11204a5a503003041c0a41c03200d01c008000d0b5841d0050303c220455000d880040c00b59034004030b40c4203034980400390030302040380f06019816641e100039100b075030010b18a6a078586070890800e003080f01d615031058403007400e80c1000b125052403034005814140c1404000d02c00c1d4400c188500c403c2c01c04ca41030442c0900b510704540c200c00700c0342 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 356922032 1250 356920782 356920787
    0x506160809030909060607080a090e10050612180304061707090303020c13060f1211061201030303111b1e07050f01120b040504030f02010501051005180a0801051501030b09010303 78
    0xf076200c0802941d810f40c06403181c00018070303c0e009070100209507800010b00091100d9100d0710b00000c94820416014146d212080764040d0b4002c54090a03412100c01d001045e580e0000c000c0c07694020642c95200c403c080b414186140c11540705d50404004642108024400c07141e030306810950000c0c070b0f4070b400560395042d070790001d45840c0103410091060102460b20f101450440c1e024000405c91500d85007061540e482c900908040c5007842511446542800480d031030402034112510350402e0011402c040c0e086035826001072024061501c1042401d11244081c808916096000610014014516000140c008034a017042c0358510902907040004104440c0c2c8400c0310780d45e030100003400d040070b88040401d5441c008211236902c2d164441d003030105000616030800450b5110603010350081c0400e81e203980500641d801c0c24003146c40015010840d01601194500000800000051000c050790b941c2d2903120703081d50700c141d54900d987c401da420b851060b5038052103080c150711400c2d910b14070203603d542c801 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 356923282 1250 356922032 356922037
    0x32c0901060e041b020f120315011209080d091b0602030901120e010c172511031603030e01060f0308070618080406031406010309112704050616080903 66
    0x1c803000d00c48807000001e010b40d615007180c00b06445844501e1001c0526034802982c0f4003500103a1355030f90041078100041c80001400b120310a000d038443c50720101881d1001100c016141d1824000c2c010f0751004584000380c40500140213003401c1440205108035581484051f80081074624540d0a200e02d0080000580120075504000b5090030040303464030310503c0d0b0002030000307104000b10039483c04607407280080d0480d44100150315260b0b042e1482c1d568410100d070102203900c03803442600380e07003100b00c8020314810715a01d04094400f41c140d9042c2000b6601c01d10148847e902d00b200881d88843c1c0720916102c091003040004d241e613540d00c0316054550740340c0d100c6601c00c5590242c80d0540364140350502040d100725012825030701510307055403280e03500c4005000744a1146680d040703105640c08241c0640c4280141ca10b00307074000c20005540d00c281c00800000c0080c8500002801c8030980704508000901c08009110701e008001504a44ca4100005e04112000303509080a000404090101c3e54500106 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 356924532 1250 356923282 356923289
    0x14060621070504020f1c0c0215010305060c1309150911180607060608030c03090109090e06070c1401020409150b030403090312020304230109050a15051312032c0901 72
    0x280140c1d01c040382540070f255845480d103002c040003a41250051b600c4021f0303102689031403a40e42034940100d0201c941100440c03081c4800f60140c0c0c8030401156100c648140145030151910322403110082d560600b00068030500c0030041803250440030104180341403405030400954080c0c03811403825418017044036000300715180f001e004582c08200781c41004900e50045000d04440000c503502c1d8541900d44076035a901c0b01c9146400260352603400260803030580140304600c130344100941019641d2440468081c050418140d031105000c5021900c034a20a00c020000383c10f5060011a920008411101d0400034682c000e002a2608108110110307030300400c44000d696003c690360703950f18011207080345140560380002c000401c5c1e1344d400c100e5005030a4003220391104280c880210f0f441c0e440c4100a030101d00c900c15220019202001060309600c114003c0005d52444032141c451a070702e03580381800702051000101c0106545581400041c90401d2000d480c030702418800007070103000100800c958140611 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 356925782 1250 356924532 356924539
    0x20a15060f17100e0d14030c03070c05210a1103040501200102130b0301180c0806011107030f05060f15010c030c1e111c050703120c140606210705 64
    0x506901400c2d020700034030028041c41c1c142803000e4084499007a4884200245003000b080403c9014000003010703c06507441070340c2c1005d800303085076140c031420781d02004280c00858250284411080c1040261503a52900602c402406234940300409406814400d20600e401042e510520003044213a0780108500100b101d00f00250f000c0c04903500d0101e0180c050804c0e0f502e0300942080c03002c55400101c00107103040f40c0c00d07102640c500c1306982000384202c402804a4800183e540d100060303a95008c0c0c0040307034070700c60000300315103805603291a8a8502c0051300700c115000d030084024041e0300d56a203409140c020441c0101c000c0c0b0a12a040082c26050710404000c080c0080c4074400c07004c1c0940c0c44d40c1140c5000040c4090001ca00983c60a103002c100305807081807254280f0401c14542d4000060b044030090b41c400010b00d001411030300c50090a00c40710382c81030304000341c0010200000f0400880303400010000707170003044242090000c11001d110b0b82081c00d00e03408501034080f00c0e445800640401150303002da = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 356927032 1250 356925782 356925809
    0x702071a07021e0a090203130201090b090306010e0c070f0b0a06060807050301050d1e030c0b1f09020c030c0d08071d01080a0e03160803040b060a030c1502100c020a15060f 75
    0x403404200035003140d0744039038041480071040158058408983c000b823039100740d95898405890b0480ca10241c096100400e4042e8041001030004001c1d050320a81c1141c848207500e82030004680d90041901001382e411980c10300000188100645107000340005448141440d14080c605000000c00b41e02052042912074050340800e0000d003d0211080c0001d003120722412000c1200fa0b003000f600c0d405007140101c1e16100480300180f40380503204c0305004d408460098000e00103161540300000382d00040309280080c0000c01010341c500328200051030001205032508074162408803406040c00d030391480d2803184172240307640760203280c3c1c0d010071070035449440c4050010314890300607103540ca54081c81d4280d0548412100c0c0d040c00388001c910103148683d10440d4280e0041e80c4038400c0c04908a00c1e0300c002400e01e10340710418090f502041021280070754440c41164400b80381810100309882200304440d0260b0080c48a0b00188860400d68400c80c00b01c0d40c500780000780c81c000c817544d101c503c1e9114001121079203 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 356928282 1250 356927032 356927089
    0x2132d020343110f16090f060f0f080c01030515190305072601091101080417070f0b1305070909020a0305060a020a0f030b0a0504090311060702071a0702 67
    0x1005490203144050750b540000c000a2407102038200b1883c0580c000c500d1003900d9240d04c1c1c180340043c0300d4080204070640040828980002031000d0150000c0a81f40d040c0c440300d000c0b44076150042030000802065021820302842c2800440c144404080028105401e010800404c1c40042c90000c09644068402e003000a4185a01c130304c1c8400c154000412500600c580000d82038284481c0d0440c01c01c6281079401c81030001c11103942250100b100052104600404e2407145600450085600601545001c601d03039180d4502c0d0355159100600c116100007500b01c0240c1405090800c0c5907110719440702001c000941500d895644100500c210411580c03a02070302006c549480c00c066000315881000c94405051900c4410041d4010540700c000107441d440720134106520902442c2d80084000e04011141c90400301800003030303e6181c8098040c4061100f02c41444081080f0304e07440f51f00c00388d0140c02c040e41416020000d40080629240c0824004d00207280907130f555604003000d5002c0e00c0d00c140b004048 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 356929532 1250 356928282 356928361
    0x8070c0f020315070e09090a141f0f0c05030f060415050405090d0f170a0c030e0316020a0609050a090203040f150b030607050403120c02132d0203 64
    0x310500941502910141480311003003250750a001c0e0340d00d07445c0c140150301c2c01c5c0140f004500003200c140103181e01c103a1503030010039084120505042c01142c25612400b100c120380084642501e101e20150380d60310805608039003681d10540c1d01194162400314a0340c1003240103030b040100c0241030b10748075903502c00035100003511080c400801400c000c1c00c1031200340751040030207840b000c00c1c02105010500c0c5100c41803019100d10502055050005003070301d1252504040880204482c00d001c0007410f0b551040929a00010406041b5103081c0d900d0148c0d180c0558410300000c82d5003644140b062200e108800d0103103030703155100181500e40520340180c50f540c41b410a807000030041030f0301506e80b00701c000401c90710084c5504454006d11041d0100c1d0b011f07403075801c0c04030b0301c40c0701d244400b410900c01941c10406041c8034100804009000400349070611103010400412601d41c05014028956038085810088885020750060b0303081c2840214110303c1e00c518403402800c0941200803c1d0040020011400e42c03 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 356930782 1250 356929532 356929553
    0x60803090f04021908011401030603081b0c061b1b030307060209040207022101050f0408070b060d0b150f03031608030c0f0a030608011505030c100c061a1f08070c 71
    0x11911300040c2e050081c074401c083c0c0800030a0141c0fa07110b003041c0c0c042800c41c2d40280141001c90740c1c050419480c00c0c2721410b84003442c2546400c0004031b405400d01051150f40c500d000b4210906a0340944181000020b0801d860310402c074500c0e0b01003001001192a8507503001c415901031035000070380560394140d003000040080c4242007000350b006183c520f25081d540340030004c010300701c010f0b500204015100c802604511400440f0000d00700c40d4200b003040005a0203001c01d41e08090040c00e200c080c51034654840e000101d04640d00c510025103103000d54442e04d4118030b107080b11001900990300e03102000028120380015101d0140c80c00b0000030100d4510000d00307080b19120346000c4d00c8203440300030b48040140030f8401442444020342c00c10504011107007800880a044800040050036842d21680a1004620000c8031100038000c000c020880482c0d1180100c1e03841d145000c2ca8015000d00000c1000055172071681801c0410708561048003820303070800c03903040c1c0050540c08c1200090f0908d00c2c0202050 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 356932032 1250 356930782 356930797
    0x90d060204050607050304050306070201051003082d030702011a030a060c09090f02041a090a06080a0e240c040b090103020d1d0601170d12020708130f0305060a060803090f0402 77
    0x41030004c0d19400740080800a4002c0d43c10450a407030b240e40300e2540803401e0351425903601e408815106010000655a1700041030341503036034407902202c4c3d60100b41e4041000401014900c410390000200b050496080c032072a0410050401061000d01e0b101003c643d482c201200020481c0f60350b04451010310340564054001040010000d20081d103038811000e019400c54800e0303017510b200f129050a1703165500030503107040d0320b00600000c80d070340d1511004540040000d80311258841e40c07098136400c0420f00b403003a080c07400c0802d088918112480b0030146049136000344481582141407205200528085040f030708454424a00983c5892401d4803500003441c81510070041c9039030441e403002c0c0407000440e41604807001c00210b0891900302c956003603180c03021003480100003016600c0600300c10030954050000640503500031030429107403d10b00c00d640742145c0c20940c200003c4007010420030008000295000a520000380f0034185000d91050340c9002e072000e43e0344558040b030145403241d11b4550603900d00 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 356933282 1250 356932032 356932039
    0x108120c060f280e0705040b010f18180203040203060a18060e0313180b040e070902071e08030a0c020102070b0f06151306020f010504171b0307060515090606090d06020405 75
    0xd25004084a000780504c1054080b40d0003030500004031454923210b800b0b0010300603100c2c0000205800c2040756084003400e24a045009071038404100140d610545070040c0018001c016030360f0615004240ca0000c004080640f050304100343c09243c3d601007941c01102c6c590005010820360b440f203d515056000d088064034a000b5401d0b000075103005400c03000c080c4505050000c0004003100c000f840191180c0b6240828075500599080110011239402803400602411500d00c80350a0804074108992030781800303503000300303002c0140105948140310f540c0c420403c0380000c51502540d90f6801d0032441d0010000a04c020391800043c40300c1c0c0b01c406035219040e5085c84569034904511780c10042c0700030f550080c00010700c07035102a04050341052090301c0c091500800181207040061101e03002a500241c01c5240310520f20300c1c071081c110703800c002a0512a00c602408034052400d6810000c0004204007814411aa51000c0c0a00c1d5150b160495414540a4500340f50348196414404080d20480c0e114541 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 356934532 1250 356933282 356933341
    0x7020d05030f03101d090303150307170c010216080c010c050c120706020c0102071d04030207121a160f0e0a0e040b0414061006120e0607080108120c060f 67
    0x841c06000d07103001d400e6881002c00c00e145d0444400104200280440317640aa0303a00c20004100702213000c0e614403106000080444284c1500d800503144030160031704451a4a61220a003840310f0341c3c050040c03c1d01c0b4440d0b010110303001c40c07801d642c07259030324010300d0000d051140d49800c417001d00c80c1c107201500c0003c901404c07528200c07103010360807942d816051182c2c0c001800303001d100701215880410b4440c11514188000d1341c40703104502d45000c2130b00019208605610a410300000e018248203800c2000c00d019900d2049042c07048000e00c82c0c0400d0041008060807000c400c01010141c2201417031104660354035200c80c2003007150001c00c4100da0705800440e10310405400308020840c40c28030f410b2080748210a0700d540d6110090110f645d410054880701848000014240b1a8603c5440d040e81c441e207000174003043e1070103001303451800d1038020b44060001801500c014000400104004540030302001f90082ca0401d21100441d00c40c00040e03d80e14141410402040121540741038240710421005071400 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 356935782 1250 356934532 356934541
    0x80d09050601090606031e0c0908101b03020702031b0a050a291615020f0c060711070f050111070302150703120b0913140102030108031e04050607020d05030f03 70
    0x580d101d40910074a00390314140040420440e05c603004159190196010880c80c40c4100c541000261500005580800140382c8001880380001c00590351110303d1f40100003500f15004605404030f00c0c1c0999110140350042102c140161400070350110030034500d9030007a50301440107000030029a0942e00251703001c80d03844000308051101d100c41d48c26000000d1b1864449440c000c094507094055100c103216540700000000c0049404015030160003040120300600c1c08920928504e12a04002c00550440c0e01c8413040003803150700907030113982c808415402440340c00e1911b01d1600502115024550400c60001c90780071a120301000b00310042c59009012540000c1d00c2100d0241c5034101820a90006406048050038030b4850702c51280940401381c84000181d84040b010543e204801c142203030088126507030540072210a20245002c0c0640001841d038500c0c54a141c0314403015560390b5220308010403c010411961054100c0b0344c038503070559890a21950905119086000d0300e15003440c1003000000b0030 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 356937032 1250 356935782 356935793
    0x30f121109030c0d051c27060806040510090209030f0d0e090c030405070b090d050105070801090c020c09220602030415050108031c0b03012004060228060504080d09 72
    0x41c0441c0c0c00550484100583d21810484482c3c0d0b42040900980c1101940c46101d011100c2d5020300c3c0701c203e040c00008503000310712018900300208000a6220801385060104c60751000c007035600054112014005410011524200b21865100701403600d9400201d400ca20f450a100d9400e5500300c80c01503800c0300220800262104010804a030711584c854000510001080c1080e03901654004000382155800c2480001d0603070300040b5040c3d401190101540c0025000340140703031140540b0760b0758a8195150050359801e442c41c40d40a001550410304044601c0d0f180c1d400b8203a44844041403625102079480028500300c0702010300601414000410801404280700c041140c0d8003850b4000c00003607980b117035500d44900507450048007282c6a1210081c50f68030b190403d00109400400004084200720100003941c01c21090001c602c0c0c038003040800642e238040c000701402106481004014618051104c29011480c480c0100f8481d90750b00400d090007200700a6410900072070104020000960502 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 356938282 1250 356937032 356937037
    0x17161805040524030d02030a0e0409022112070308190e15060a0608013203010f09020315060303030c0d15030f0c0618030b0402030a0f201903030f1211 66
    0x440b200204840302003c907600700052400740083d02a170145092600242040b1000d5011190340b42d8016180c12110300503075151107800111011540b2514007408800707022504040c504078410010880034401c010100340c010b014113500042041c012140d01b07041c82da01c1001400001c0ca03030720152186034241911404120201d134085c00040300e4180741d00b542d45030300304e030202401d02402c1490712080004101c03103190280200c14002c03035100003550f010b03410fa0119003181d4030b240709004030350784807030420040d41000d010076000c0c0040009203800c2458954040390340c0340b00103010500c3c0d010b0005121204581540e1241c690404e0704c1e003c0e00312890b42e0b0308110007101c10802081d0740c91500c0250010b00c0e00d001d45c0300142412a5035001c0342e40c580c076580700c00c1c0400300010410b0b0b8040c0200c408120010340070413802a4000d01c6180000700300580b1000b2034030801c2600030305500400701c14000c1a1807505144142080381e0745483c003210382909812007101c50030441d151100d11b45051030800101d00661101 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 356939532 1250 356938282 356938321
    0x120f03040e0f0604060b1813320408030c070c030605011409100e130c0b070f1b06080a181502031e010312110a0b0103080301030201171618050405 64
    0x441400d90f0f129a0204804c8522a1140e182c030100100409544498062004102d02200038030520f0b1050203984000261803c0c110301113468036240c0c490460b80300400c40e21005c46814401c1d130000b20700d080d507101140c074840985040b02c00d41c0040f84c07220801c42840121006141d10440600865954400c0203804003000715140f480760700003000068280071415488021601c01035051103198480340310b240001d2060743c0302983e02c0e104010b03001c504551200c008100ea41e114681490400465007412010b106d10f440e0240d418100140d000c00c4559402403007560403d108150000c1d6504240c03031039201081a6031002402e4a10030480985001c0e12640510311032409052145802c0420000b4a03e0344007007400000c00340c4550001e95103495104400c40500c81621004484080c00036480b50000c0143c00d80c82145e80c080c00000600855034014142d07034065130300d00d201c10703031508011440ea500450200d80c1d13801040804d146008100c03034004c420300300404016004003e0f5060444000d40f54414401 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 356940782 1250 356939532 356939551
    0x90405060603090715052a19170d021c050603250b070305160503040303170415111c092102060c0d021c0b10031109120f03040e 56
    0x20001890341c10201c0480b0b1044000a0107000440d060002d448201031101c0681420001c00340501040005141c0e0408114040c00c84507941300d502a001043c07801c02212403912902005056100010750700c0b100d050b8001051880803511030707083c0124038009010303c100b1070010050b00b041001c035403c2280e003c140160300903803d4035040b145018a840610f910304042031000f503940881007081c0702c260300250440c28031030701d4203600d000720300c005800c001400240c2c2580d8581001404204150b044441045070302d044128144480c0b5140c0c85a450010045400800309a25034840c11140d2034900304944070700800b468090303070740040560064000c008101e4103c0302414201822209503d080112800000113a4000c00155507284403007103850b0000d0401c44100c0d60240300b07104021085a6000300d0141ca401000191208904200326504804464400034944ac00409184100c00c05c5c08440c0360103400e4602c070441c0760712088014a0060040031081e020702010401140003010b0781d203160302404411 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 356942032 1250 356940782 356940791
    0x8040311012019020a030b0405100c18210615080c041a0d06110f03070201050609090c0d0c030c0f05012003030103030c1e060b10030b0d0303110c030f0904 68
    0x75240d00c00360b1122a00e0300810b58011212503034035201c030040001400d48080d041c4078455130b4036075401c08000700a44044600d60007000c07002600344024070403400c6030748552610520080000c0c0c500101c40c01180180f00150641c006c0b00310344c035a88041c10082042d44100c041000901110307842a03048054012070019006100303032100306c3c0c60a400f4101044181c4c0707981c500300000c00020000740594800c8101d4000e5110320b01541d003054010054014801c002001c603549103421903000f802c441004100c00d2080e986081440100140022007249244090301c030312984070182e0403c0b00325850f03170350320080104820a00204a0b98030000803002180c50a80f5280d1010344420f00c0044110314420181c010b07a4020700040010a100d08526100d241c06511048000e034608800702c0c40320f0580550907104103031031300107041203810901507501c0a00031a14081154200c07a5000481c4800c078103070040c0816454045000c01c1d001d0b6941203c0ca258010411690303121007041035281650003451580f845103143c03 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 356943282 1250 356942032 356942057
    0x2010c1727163507030609030503040b1303090e09030c03030907080c090106050904050c0904050702150108070302030303190b120616260415060f170109050d080a090804031101 77
    0x3c0900740e42006040004034203080b440e2400c0c54001d048440d4001e08900c1480f60000214400b071044d488850300030380d100c0d55685400e0400d4900460040e040302500d03280b0f105e000012070b0b40401c0c42c000380c0d00306000701c030280e841d080210740ca14050030501e00042c0c0800000d0050900001800c0070031a501c1c00c05660340500b913078003000141c4400744589008108100b1044123a481c280e80500d81c02494210b85c907041c01070741404541262000c0b10143d0150340082c000c0800204e0b600b01541c010001a402441d02508540c0032a480340005480703156030384801502c034025402240c02150b094100035140c0d0344e00090803561030f5901c5005581260207290484110491a44100300c501d2104040865100c203100c000d031324010002c28010000d942ca41c4000c000742d0750341c004d68014403004144075888a00604d082040203411819040b001b000d440e85010004000241c0c0071070b21600310412810a0115aa54070f0b00740d80207131400000c000d010590000e0080b0400510120b1050605802c0c1d8445145000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 356944532 1250 356943282 356943299
    0x10021c03050f0a0c0309060c030203040203060a021606090224070308060f010f050903010b12010209010206010801090c051909060f061209050705100903050a050c01020d02010c172716 80
    0x1c26106200c0a000203000560070000300d070030003410346903607244c0020741d5140c45c1c94220072112031100800001c1d4002050006514040006e1038100a612600310716090900b01d0f0f41c90f425400c1c0da0000c222580341c890b80000c0d50395544200b0035000304900e030703015041000c24400420740d00078607046001c600c0d910003107429400c0c8592220012101a182c4400803400101c0641e0030ba0459601268103640f41c00d81c43c00d440d20b0f105001010007255000158513944030400190801005070043d04c45a80f40144000c08900e002d07110782d00700d44003541e2910b94070840300e040000d11481508102401410214001003406001c40301504890080d51081e01251510b41040c0c00e55902d86000740c0250700414003845140361805034038100082600786040000c0ea25951527003040328884050316103401114502d0754a50f014003003000700c80154402003080088100002d041c0c1c540040409010400c06c0c0c3c000340c046510b05446e41b110b1030f80c00282d1402c42501c1540e641c0e9801007801004114542001d00045560 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 356945782 1250 356944532 356944541
    0x2010b190f06050d15030c05011205061806010207030f0803010320220906060f06020d05120a0903030e010e0604050c0a0e010b0d150609030c050603132010021c03 71
    0x40701524000e81d42442c0100c110b5903034120150960043d959607500108159400d126070004501c500d0908031258175100c009484003401c820384203096803e09080040d9541c442d81d0620030078030740002100458a507030700101d2401805801c0180580301a8400c81c0c140100300c806541281e01c0303009160300c036004000010708401d03c504405038001e05002d07080190385008509004d802d60784440d000980c0b4000391544410380e0007513070000d048aa100203051220b0783c1c0c1444101545a034a0901c1803800402c2c01d803401d5000c9004080c0320003e50b4400600c020075103e5001405e10900044c0240916160101101c1c0c44170b0081e5800c407810711036070f1407007001ea051180070740d001c4401080d4590401ea181540c1248035500c020080c8241031341d5800600c10700000c0c2c03100e00c40640340d66075580d140e0312708626040b552000790790043d503c9440140200910015914a421103044c2c0c821110034140e0015a10750501203209030100b50b00c000c160100c01e0b441d6900148105c0007007080d6074503c841c04404142a030881c1d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 356947032 1250 356945782 356945789
    0x902032401050702010c051c0302040f090608030d0c021006091a03010509070509090f120301081b090112240b011d0d020105070507151e092d0803040602010b19 70
    0x2c078280f0105001d58010414122013a0003241541c50aa25030b098a80400c1e1080c2e100d0800711360b01003810301c031010120108401800320380104000942c10251282e40c1c9001c2c1100c0c1840b4140c94503518080c00c0e1083c440d51480c0045c0072000d00c02da50315002c440000d0640d4112181e00e41103044d01e041c0217031405020340c1f80540d0000024208050514041c014008002880d0508610444084071a001c3c0208929480c001da841105030301d80d410201c016051a01c03070607074210540b200f00c0ea444032980d00e0518480c1180e580c501c1f0010702c9e004500e080520301c902c60b0040380c4850715101d5808280741c07403038200c04007420742644c520340d00c2140e04090081b500c80f401d8909801400003016000154014402013070114040c0c02112400c0b070741c584051000f422542130000020b40c4e2542d00d092040c03458246607640106504104031200e080c0500000e41070a4a024280c500c0c441e02c80603102c031000d42e240782c80500b01480a4a0b6202d0312200040d01174502d071214540516040c03c506029280300000c180241c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 356948282 1250 356947032 356947037
    0x91505090a02090604050612010e09060402011d041b09090b01110d030b06191701120b06060a0e0414040209060613150509030d080402010807230c070305070902032401 73
    0xa07198201200001d401c9540303555040f1a08003c045480d40c0c69601500b5400c007020181c491075030400c00300391251180030708801c59039440b8509000050382c006010110808030085c1c001800030990b80010b01401c0000d0070340d04001140030742190758650240494040d01c2d214102071000303824502c011120a502c11100f0195030300a0124215550300c240c000740c4408a00030300721414031003001180e030024458125030501181454041c2d944162086080c2401010041c150380c1803480030340c50701114a44e0007402c55120b800001020054540100c0743e454a0640107042000604c0c40400a030400c3c020940b01a446007031214001074161800c003048420001c0c00c40d6101040ba40760034030b4540c40325040c0045000f8080240010b80e0240c80402507a0780b80c1140340d45005190500d400050100107000d45900c00704920030030b0649515410303002007003400702c1482456649095040c050b034100007094100510b00c0c040ca440010344c00340a40c0141d0b008501000124489804041c81c040030000b006280c1e601 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 356949532 1250 356948282 356948299
    0x4050d0b0615030a061a0307080a090819050d0b1005180a0e0f0a0c0e0307050d050a0803010f0801150608010509152205010905010e06061308010507030204091505 71
    0x5008020425040740c0c0160601c8070340b5041d0036a55403a80c10840d050380201c2d54a40e03003003112600416840e245025561031a52545c241443e0041541d0001000d5040352074480c0c0b000340170000c08904403810106a8410340740f4007411900c00401581c4040c5030b0b60121800c092191516242c501c40b00705801005444081c07070070110080380070305807044d0301d2450f5004900700070001c2d281d044541854443c440002c40b103d1a803500c00c0d044022180012000810440004415040341d20002030600982d00c04840c0702d00701e41c1c000e2410794500748603e603004010f540c0201c000944c3c03541d41108041aa00329100910240709d04000010804119200380070000f0440c100400c294180a51300d66040981105841c0f01c241408002c0b880c0940d07100c0281c020170944000d2800c0d01d051520545000d403c40080c28030030355241042401000780d000d0a02841800c000031415081c68a442e080f50040c152040240703c1450a04000360080d0054032548030203034245000090f80347c6452180e881581c400030500b01 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 356950782 1250 356949532 356949559
    0x30406090317071509020103050f04110d05032a25051314090c0109141e0a030609080d1d0601060f050f0d06050a080f030909220f0303050c0405 63
    0x2260700c1c851000240254204510b00c0407810388454074441310150000498581e03114070005040b10001081120900849014400001c0081c10300e40d801100c12a208010090750341840d034294400c81ea81c41000204101070040c16502d1460b103a840b540412041d218220225024040d81c240c589030386295038042c10a01780000d26103600070b13002c0c031055120001400005090030b0743e101041558603021950001084003425170f4030240c08000307854500c0c00740c0b02180c0240702280e050340300d458200204d14000710590360f0580f503441c9840e000b1900142c00340001d41c05401c01c01c0d01a80600f4109040c0d6041951607965114904101200307074400c81c00900c51a03107048011945e000c1e1440c124010000100f08041c540c80400000d445030a24031240000c6851518041184140e120f90100f8015003000158184c10880403081e2252881d00303482100e495035414902c40014401c94900981d003032010380101c0300b0710490785079191969100b03442c2041103860307249018030303980038074407505902c551a040100b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 356952032 1250 356950782 356950793
    0x80405010f140d060f0501170f1e010e04150506010e01140c12030a0605010f0917010b040c0f08060a0f0902180402070311060c0f09060304050c040c0309140304060903 73
    0x50a1680e2481d02600780c08828110b2250759010710300c4002010384600040c0030072100c1030070702c60040c2024284952142c0e1100f10300350740d240c0000c0c1007154174911b03c030010780600d00c40c8024000d0840380d80c100c0b041642e1640120300940f5010748080d40c4424a03941c0d8200d42c10001d205240c0200c105840700c043c44001ea0b401154003050442c0405405c030380034001910784002c200700c041040c030803260210b5281e1411000d00d208468490740851f040002d810fa1300808240c00c42480f4080d11101e0f035001518041d0324070072a0140c00d64011403900070740b8040c0c0d96450350b83e2160a1080034450faa81d40c43c00d40e2100c10030072240007020302600440707204070391080200c0c2019500402143e82d40d40d00740081d8540743c500150498110440075030120b01505280e8140310720502009612880008031607040000c80c0003062000e01441d4001801050004040740074003004000d1070f001c1e694021b100b84004180510018050a4035902c01c40c4c0d074401c0c085546003544004000c3c5c605981c4140e4540510b00e1868444 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 356953282 1250 356952032 356952047
    0x12070801030b190b03010203010821120606070614070c021f02060109020c150c03010501020d0906020606061b0a150b010206060904030c0f080f030115031e05072006090106080a08040501 81
    0x8044060390783d0075181300941c0307007030001d507001340303a03502c09040d60a4481130300d84240b21f20350001e400240800c00081501011010810790400010707560941ca600d45480c04400801c0d00002020740e0b015501c080284250380a10181c5c8481c0c4250740060403c3c500304440d058540c0605a5600960440b00c0144100c071511b602400d442c00b1020704032000c80221603610003034900159108001c4103000001408696010400c01c554204546070660344c203498224003e40b0b07550081c000c24420074001071103201d1241c0001c5043c205c00740c1c0708291a01d00740310b490100c07440da0029141192403810f101003111190f001040d8948a00d41c040c1c4590044d99850380c0485240c42c0414080724004804640f00e00810202005402c0d000892060107503294140f0900c1c0041c201003040030410141080041c4c2c15011b08009058459940f0641c086115107403803005a90b128550111400402e203024204a05200002409405140302c1c034020801145c0b503111075921a50b002e0005050400204030400031548903a80 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 356954532 1250 356953282 356953321
    0x90c03080a0c02060c0c1206160c02010c1208091b0337050313230907110a03090e0115091a090409060b0907050c10020c0c100512070801030b 62
    0x915444002d0a83c0c0050160341249081c80c0c5180e00004c0c000c400750500c5511a540031b84c2e403c000b00f060f840c2040001c403405000c2d81c003c0017004512a981d1701164001c000d00c1e000d1540c0100b02c1503203800142002061800222303410109885460700c0f00302c07030612040342240c90910181c09454844041c407052840d9043c908020311102c2d105982e21000c01000ca071f00703110018842c40c0510ba5804543c80c09200704201a0040203405015800da80b40d0120301104000f1103020980b440f44081c1d455142c29980c0e1642d03009080758034040c50744044205603012001a054800c258080819a6240c20080074180f200800c5c006c007042410b0700c1401a900354116a4840001820510b49083e07a400b011900340c9090820488850b92903900140c4145003a45080f40c1c0403203240b60450400320401c01d20f5590b084080086c906059000038403610011052050000011010340310324070300320803010000d100da4852031454191131650300208107242d00c41c0f540e19040300e400001300300441c1c071a00c084450517090700f503 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 356955782 1250 356954532 356954537
    0x150e10120c05180a05090705060d0513170d1a10050c031314030d022113050a060504060f0809070e0a0f0e01020a0f0c020904060c1206030b070909090c03080a 69
    0x4000030a9641c888800d41c076606105072180d058105440ca140550b50086c0008140b03070001c80c4107005541702c800c242c3e018052003003030110b03890722210b18154502ca15039038050300103002148021400d10191008001c0d07103000c21002c0000d031341e401107840740c3c01c0c8a44040b207038406400380382c10707200ca44202d02a0441d480e0031000d0700c1ca8100f08041c0040c89101e9903002d1030f42d03031040081030340b02d0345805d2040300c28080850000d07102094003030701e00048071660b4002d4049480c2000c07504903202d03e004842407010300005403041003c180c881c1d101512581040c0b04090024105840c000500361040d24442e010300e0141008000d002d003040308454500e203009001d0092607544158845000026001e00c040b40d42200c800169603000302d4000410170300c101035104d0103114541200500603100d8210044c7d1207030700010001080c90700104103e0304c405c5418000307400242801d0010040c0851044001c1c020451600c0c0d03051f40c181d0f00c1104000340e4000607806004000da24000b0008035903584010301c4600546d1 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 356957032 1250 356955782 356955803
    0x9070b03042a15080411090a090b19061205031e0c0307030306080c040b210a05061f060c0b0403031a04090804030b010e090a0f051c03150e1012 63
    0x742e41a0006849920400e180041440341c1007100207203c003041c1525000f03034508010949481c2e111940130080324500c442c003408600000884408207a4048541c582c4c0c0007030781714014108420103085640900e01006c0782c2c18500000004c000d41d410706160449680311001d1420204481c0c14024255a110003d402c039450170001a180d206090009183c3c02e80319490000e001802d00303020034902002001024050380ca041c04540300d0369520600d8103281500f0085140c091121011600e061a113440b45c014428441c000500c0094a05140b04500d140c1984228800065607180c080301c000703400b03000140c5040322080114010a200b40c20002841d840200021038032680b1201080032505200825140b0200c007050030b20802c50816481030046c500c1c1d05402a960518496403a00d03803100541c01041000b042d81074400700902400166800111240c071440c0f0642d0600c0042d000d80bc414011030a004155800443c0a4075215115030045c47c00c4010700a4841c03c0c84204640444100070035100c11062 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 356958282 1250 356957032 356957063
    0x60910030308150901080d020f010b33040b040312020607080705031810060e0f0405030a1d040501030c050f01031a041503050a0632040303230705030613020309070b0304 74
    0x80c0c2e0304e407a000384421001007001c0944594024104821000c0d046416414003000103071031f5440e0000700300d4001601340d8002003940c1000030141c080384903001180d00c00d100850002254032081c4041e008580c02103201e07140d5403080f00812600e8200441c1c0040203c0c0000c0b02181005210340041c2d507001320501d5507050511040c3e1845460007140c06071040e0707107c2e00d80307209010311f03180845441d801007400f5042082505156454070f4890060b0603900042210b5500d455510750302994400c400000064000c0009503164242000451352600919000b1181c540e900c10302540b00b07200d400c040507103181c28004a03820710b208000151041108261490804071400b0021603000e20200c51114462400014441560074000601d2031031800d400107140a00c0c600b0140d440d201c03601d5580c0c03081e0b140c90000f030100d0844e0a908203100b008156030501002c2030b010801080d803c00000c600401c0c0c11522140131100c2599184168802100c40c40c6058002040c10800340036040007840d00584509003582c1000d80 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 356959532 1250 356958282 356958289
    0x1312021207031d15250503041a28030501120b04020f0a090509030702030d02060f150d05100c0305010504020906041701020705030d050402090f1614040812030f06091003030815 77
    0x403100c41283e202e90010f0841030181c2c01c141701c00c1e0007100000c0c40311004245512031076104c0c000c0384200d41407007118040b141715150003002190711401d086d8228284094440818004089a9401070408649050004989041541d8500c030303a05a01c02e01030200c0d03594503800e200094200040868005408040102e0540150b000300c0380b00c1e1700ca81c0001c64803a40f482c0105031500f44c0211070601950849024425110b40030400c003644520740100d0540d800e503d01020810008080300094000c0c0140942c4841c500c1060f04489641281d5a80611542e43c03150200000ca02c101c014883d80150200700030040300e648004a0b429032407a1070b00045c10700859884030b07421a808012000f229a68800803c01103180018203075402003004080035400b4605281030408800303c610440d011701480015203031a080f1203500b210040e080c002c1c165200f0283c112000c110319001a2402d409102c0310100040e1076007070090f01144120741c01c4080a20207172458405a9030700380c015160300492406c03080f80d11256103 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 356960782 1250 356959532 356959549
    0xd091404090606081209040c030204030302030f07110d1b2408060301090b2706060109091802060a0207060201060b090f0d1109010608252a06051312021207031d 70
    0x41d03100781c4046d03403585240104021a001d45920900b07040c4140418404a0b40c008203444510007017540050740d50742d0b1400d00c0003481115940750782c2d003c1c42c0303190000100500381464007503101c0445914841641c40301503111030007900203107040881184505140c5964030900c0c0c05504903202400020f42c3c010755484500d04036030225811400510701030b40142c03070142c0d4042e0000300c5024482c05041242002070008010745024800e0040c09511350000e9003584541c07142510049038010052951407031012030213900e6226520902016500c1c07e500021070203030180c2180c0350300d180144848a0007103031204108540c50030400903200112814501061034130b41c10203550207060300340c5521a1074a403061a00c0800c200c0b403016083c4520f41c00410b8941d107a007010600030400364144000c0c403100c0e1661540407000401e0100034003802d04000a01180d6a51340b500100b8050068500c1c41e40c0d240584003c5e0b80e645a10004407003544c07010400d540c0460b1051503560741420951503c148510f003000001000301 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 356962032 1250 356960782 356960803
    0x602091203040f150c020607020301241e030f03030c183b0a18060f050103120f1403061f0801090b03070b070b09012403050d09140409060608 62
    0x1940001420703c103040c0e034841a0301c000e0030301600d074500b1490120b00041075410304000090040c1c1000c0790351021940c3c02e40003283d400e0b620440d2041d19040c1d200003051003c0b07052090031042054480b000c00148400031040040c0ca8001e510700c1c039802c2e1107940c01c50040c0240d10305141080790028154644c5040204100014040d00380c141d900300c9034402c0a02640c998086048441882681d0001036841010300c515034000116180020560140400d4544201c0c8044d030060240e8540598070b0440c040a50040d4140c80c02420f00714201c1040c6070007900c481042c103a0503004680c01c544d10360403814840c00195400700001c0c09403c4541104003520311a103900060f08000310f412a00148440b083c03602c00da54504100b217005001c0545000600b07a000d1081080140807090b0620000b101002c094101150f11858014204118800c40301c05401c2086c00d800111428011620a100283d210b1105001a00ca2121114005505030030411000f040510012a0303040e0706c80f03000103070043c0300b481001a103 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 356963282 1250 356962032 356962069
    0x60301140c0304030f03060302100c0204020d060e1501050c0a06111606020924122212030c0302130608070c050601060c0c121e0f021e01080703050402010e010c060209 73
    0x703e0401d46000340c1603400c01a00441014035001041016a541b42458428840c0c1c60909808241503030000ca0003034030442a100101030300b8064001a0b4001c4450040e10172064580240f170b00c494600f004617091312500140c09400d512a48002010a81640c400e241541c05c050440d031418882207050082508442001d81d41b2580c0800d1001041c1881008442859a0071000c00c0c05c51192401414035401550203c24001d00c50000007506280344015201c0d4049104000c4d5402d40340610b09481424008004900040d05000f20440040d00034001d54040c040400d440070022800d15204555845009040c0380030040c5c1d00700044045242030110601030041c6523542c9210000f01c0c1030440181d4007540c003044001e5072840b4803178042400e2820300030315100c03003102108124400b07060540c919441110040d5122140400104c1100000320410900040a0301e441442d0754038804140c0c1101c0e801c84029001c112030a14005441d8400c117500b000061045400600b002c14400100307115014400300d10383e1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 356964532 1250 356963282 356963287
    0x8030108061005130c05070503040306060f090603020603010608131a100b070c050f19060c0201030609091104020a0306081603140d090911040b070c03021002010207031403060301140c 80
    0x4008000c1c04800d52000441d8030010301d481c90140441c4400c9104491000b200350b54914050700340b8491000c441501b60400102d90700d85031a41400e00c020081803240c0c24074221103020024a80da164025901265001480c950a40e031a1000035500f07a08000c103000d40c0741103110201c0d00080d000049215001e107042582102034034204446040d102016085a65641000d000070309c0010140c0040c10203840050310b00c0b01501208001041ca000c8100e100c2042c208400c950102d03205600007540c0710454000d0340c09103c0baa0390307010302d0310440701d100324050801c0e21458238614607420300750014000d41c074407481d00050f45a0b483e0405c0b824a5060303044c0c130554144040342001400f00041d4260543c0d048140644140285c080d0080e121220611440307041c00c0e147d00c2c0421406144809880050180d40e0703807141c1d1080b44d031400c00482446e03404124820395681841c840132901c1403090755045981503c5038040c4a80030710303910341c5507000200840c0c1d25640318108900c204024140071030049080707031070898 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 356965782 1250 356964532 356964539
    0x806011b1b12230319030507020c0d1a07050f0a201501060804080d020406020f0d050a0e0904020a03060c0809010513080d020d0f060b04030c050301060b1207030216080301 75
    0x1c20500295100321080312207500705001040b0307981800080c0b040000c20901e8000182c40c1010708502420f1481842d040000c3c0700c09110760780640110344a400c0302e41c251980d000305401041213912103884041c140329810b40388102829000032030650822282e00308541005520070000c1601d900c014040c2c000601c081c009280c0364006100e281c151408804040e2040f52b03002070180001c01c105200320700400ca9800d0124081c01888012a040c0c039804843c19540c0d10789604029583c4c0c10420007550b214840c000100c84181c1c0f2a03410b4802442c0c1c2075a501d203100c3e40c00010808075000240050361300c00240f120020000e4281c0c49000b400a10545503601c982c5810701c1060b003140d00007002d48800881464014000852443c220b030303e2003030038140050321000340380002c400038003150348150009440e0080225603d840d40380540120791050700218055520b840600d42602e03c1407061600008040c408407040300c091b5080144e101e506443d006081c9103074004416010001002c0c03e4410f03820000060 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 356967032 1250 356965782 356965823
    0xf030c0a0c051807050d0e070f031118060d0201030209030102030106020d09080a08070f03021905030c0d0e211c050d0605120d08070c02090f070206010510020d0806011b 74
    0x50300402e8102c56003030203166803d50501540c2001011141040000181803003501420f030702110f800300701e000890324041e0701d400d01480000003d000c20b440d5000c0700b119028251904501200c4d00300d0300c03600e04140e1910350005005040c510808124103060302400903100301d0b02c0910185008210070f070f00501c0500c0804074050549152a00451107641211840341d011032281d0045a41060703000e00014940d95480c2400ca00340780400000d500031a1004222030103001d0000041d00f076119071a000c0d00d00035489840143c410580c06c0341c8542d04080c0f07005070009114a0070800b00406840002500c17102d110312082d102c050f2034400b0340c04021074004030340c200500c081440b405000d400d084ea00500d03000b10000019a5034100b0209140400a4410000e9221485080d14520310340d4050b0041d401030400100400c10780408440c00d600510507140001118039007080c01c0f01c5c42c1d4526401501550425042c103c0c1c4104c2d0080140c0d0502c00d41002403403481c3d0034141505c040b20b015007022100b60b00800c3c0f95 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 356968282 1250 356967032 356967053
    0x1815061c050106020703080a0e011101020309070602060a0902030c060f0f0d15050f0105070b1512060901050f060a0b0a030b0607080c0d091815031410060605030c0a110f030c0a 77
    0x3c1011980b00200c2030002602d06000c8809400d11410000080b18160300104c42c966107003050958203500201c10302020f44400505501030744d489809880143e81c0380b0072188115425110080e515a020314203800c45410180300800480c849240007510f000c4160f0312002c001d03403120aa403800c8695a41000ca80c03c40001d4a40001d841d0846150480100030300000b8940c1c0240344c00a400c96410102098032039501c40b41c2810000750107405680d40c0400c201d05c46450300821100d0301219400c000006103210a2000110310641d00241700242503030a000712480150400300c41c4100b40340d07454042c0d250650303a1001414260348540900e9549003105201282881111031540041c442e000a0130321400c207542c41e0b04201c0c4405e05c900090416500560040a00526407010b480d01d40c064180741c265440100c2d0302d00454408120602503503546e240c1c122485c0c442210310403070700c1e0002d100304584a482041c019903448101000c5a1141071208070490035a8031101c80014154481c91090080100ca10300 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 356969532 1250 356968282 356968289
    0x4060528020d0f080403170907080d090e0c030705040e0a0b030105010e0108010c020d1e020a1203052406030402040c0c05070f080106050301111b0304030f0c05120604021815061c0501 80
    0x4d080784241850350380604094607408070000310700005400165488010072008000740070860444040d410500005004000a40a155002c00c0b1140c0021900c501d0601240e0040304c6590310103103072901e4007042c900c09200242c03050000b5070302c0788890003072a5000d01405028010b0a03845d8411545003070f014a085900241c803900c10341d00310102c41c000d91034210540704804101050a180d8a040b0a03104901b41540b29400400700c80811000c8100346515034400341c403a40c00c1003204d0300c405108422420079074080200f51548450200002001402d00d500140020010350400e41c0840c0d545a4415080c42000e4015541d002000c10003001040800d02508004110070340003000107500419100a081c42448065150158107548400358010100101c600840d0460308603142200b031440e1584009600384642e51081514003c030340292031004c100240101c2c1e0041034007400d40c2c2840c44021400390700400c121002503519684ca43c0341d80700c0780010904051181c00d100b0890038602004400c4170340680 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 356970782 1250 356969532 356969537
    0x5040606180e06060121050906040210021903180e0a0c030c090803070828020d080f06090f060a15020a0b0c070b07121503030c020301050f060604060528020d0f 70
    0x3040c0e0001c400c001c01c01c42e811400070b10388100303006006e100055201850700a400ca1862810041104c200800305946000e24408c8580170303070b154140c1700101c1e56868089410590070305a0a105800640158007080320842c1c400a0400072507074402e801c14940008075501525183c80b060301c81c000b90ba040c4071b1409000c8083c1800358400707040a80e4203075a03000304440141100c0c40003812020200400c9400402088200d800d02825003c10300025150365401c10003002250719000801c58511001c103000d4400c0d40050201c0141d6500c03161000489500600856000403184c02d000ca11100004404426061160000c0015034030034580020040001402c1545141c01481481c0000e8581d40409800800c0c5140006400c201100144000c0000813520055441e0a1a0010402d90040c0fa1442168000c0b0700030007807585c4150842c003014904030340c0258070400c05c1005125541c041c5020340007203c500341c0040035103044010f03d40d00d00d0061454503000741c0c0c042440b14010a034801001c281050061 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 356972032 1250 356970782 356970791
    0x118060219050312010b0c0609030f0d200f090306011508040201081806041410060810020c01020412051f0902010503062101050411030708030c07090b130504060618 72
    0x1c0d10340d8550070780c800341403240704401c40c140901041656a81140084d81414070f50b511000c0301455409445220054020100022410b60000c0b054030301001040d113205203040c000842e40c900030f040750044503c1c4030304003c0500e205c01000c0300140c00b120114008c2207940fa07041030105840c2190507403050905543c400049454240d002100b25041582030802400648401c104100d442960020b40b03000762055034108414020369065440b50340003000250703000c2400c03aa61140a80d0342600070b001e02c0f5405a11004035030700c1ea950040064405403000141440e0321010709192524981000b81d903264414080c01441c602d5031842d8010107455a1f404000034806940080c0050200800700c0e48508024249a00c840c08121b20750f42c01c1003c120020400b6140901d080010301e00242c207100d0007440f0f85440410354110000858158004090040031010714000d8142c1c00341450101d203a400650a00d031b00c1081035062302450303002d54403920002c22000e0406244055030b40c001110310282c0d5090 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 356973282 1250 356972032 356972039
    0x5070203160623031b071a160e010215040b0a060801091202060c0301031106030402010314040b01030c05060705100f0209130c1b0f020108151021020307020304090c090302120604020118 81
    0x944400c205221268101c680300d0669080107c007803015542810f4814017540200400350165a001c03030001d644984580701e045840302c004a81e20303d0050f80c08424180d0080204020030b01c404e085551104078500007043d40c0b91919502400d44603c1384086814112409800d21104d406100c9158018494941c0c541150b2568907502c001405051b0524002d182c008003003000d591003500008560280c080c040300c01ea00b0075140c0b160308002c003440b055030b009103648408136a52400c60200c4030041d130020014840c61100d00c24000003840f0a0300c02e012032540c20000b40e0b006403a5051610880840c44000003001c0d00046006011180104181c00c1c05a00a2407100f00013410040307003000c641e40a00c0d00103101d07503a45000300410f1807040342090307003c130f140c0c4440115180d2180100c2200c880301c149482d41520b88805100a0340001d0f40c035240942c02c00e01040c81080c5403036000381009103980c038144006554a4000c2032448242140c0024a82c004004101c150b5800c860705008072131040d948460754916 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 356974532 1250 356973282 356973301
    0xf102606090c0a05041a0702132318070e090105070801060c0b04020a2114060c09010c0f02130e010b030a0305091302040302041d0d0203040806010302010507020316062303 75
    0x14001c00291880d400492001c440034031a80a48014180e54143c200d0701207a425069403640e04000c0c0c01700e2140703a1500d0440311801d298003420260010001e0ac00384441c104400031440e0311340003860382030030004000060741005820400000100881c507202c4400d401d050102c80e0030358000414040c28051074100400c03c20ba40010804031968011508881c0f0b500c49100040100c02c0650100c2d02c0c0d14814401081085501c081003811148994401c0412415060b403c944600c82150119640c0340d0603c032890441d400340c1c281c0c0024500c204081d800c0d40003198001030700400e007500c0c104d01040d44d4030510150101b0910402e4a01c0e0402c40041c000490307941d40080c140e01c01ea1070101c0c000c04001415010b1f0044540644007d075a0040080c0001c4000e180020b00481500e02091410301c90142c000c440680003008440c1982d0222001e007000d40e00f1500103466585c801d420807a01403194030b40314141c007100701180b403001c3c01c0e413991440d1580081464100e061010318101d84918a810403c0c4001501c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 356975782 1250 356974532 356974549
    0x92d03060f090706030c0509130c26041127010e07051e0d150e0f1e0403030c1e0816030c0e0906031606050409180206180f102606 57
    0xf4030171320b000304410005036030495580c0501c105450700014405001c1c607000f0029044103010765004d42c0d408100c0426402c549210002e50244400c1030911800420049140076a01c4551000e01524810050340102c0b81c0e032503a5850408010740800305240140200b4419803861608200c1d14503103241841c040304035522940e100c901e0650b941c0e040004075142d1030805a0007982c40c01102052080c5001d03070b0394141c603140001c03c44030780407000b0b200c20006142c40e0032204030446100015000c0011075980340d4094000b000f0f502106014065644000f00d40c4028403840c7c440b442e49241c2c0c074429503041c0b40030760141c0212a0001141418140303000e040e49154044803a1142d45021aa421900d40b905408a0300f440e0f00c6428846000030410400710b512500207001f071049818a1608104d0506d080718115020082204000e511400800691601e00240580766881c00b02c010100039025038603a0009054400d0710700c1e204c010400308c2241610300b01c10b684080c4140b101210350782415140183c001503800703 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 356977032 1250 356975782 356975789
    0x70605040215210711030a12050705270604030803040f0b09030306060702090c0d0c08011e060c020402030406110d0f110a0807140c030a03050402030c0316050105092d03060f0907 78
    0xd44206000138043c901ca29000001119070301c099a6441071101c5000780f000340c0c1021481192404d1070003050342d1034461170803101075503081c0b205000c400551545080d8000c404c1c00300507900480a01022002c0b03528800110b00851283c00c0003050849903180040040000503e9035807160001d004100071900d5000440e000c07150304484100096031003501ca03551501a491040ba1940d1406400225480c4c205418506807000c003207001d89050000300c800d21030340c0c14500484001445000d03000005041a801843c0c02910504c40400c1680342c88d4019141d540100142648154440e4a8419194124820201401b4403940d1440c138022125401401d40c030405085c60003045400703000c103a040360b06101502c000c000d054040d40d03510720b034101300100030b0102034800340d00c01d00401c0006a101c1c0303000030384024070982a60005101c00d1a040054449810404016800c048030301c8584c041c0ea111401913012a5040d0748100381a140d0500074180b230402e008180381c22070040c800601064210005000303044 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 356978282 1250 356977032 356977087
    0x20f1203180f0102031807122006160605061305040503040524040f15050316050901020703020301060e0718080c10050d180506090d080112020312070605040215 70
    0x80100c902085242c01078400414445500c0070040c0b28078507814101c9205c100914904503444952140400c1c80c03564100c1310300902c1e0540340c62041c04074164101d040e2600f02d20040019080569030300c2142d4846180d803404441c44c80d80c603070800001d0300c0c082c14004500305503801c00f000360b40b8080d036415aaa10560050038450001035280e9911142480820812082004205619165030b0310381504c10034102d0103100084546845842c2000d84100142da224035147c4070318100713540f040c2c5030a1720107920049199046000700c160200241c0c03400d006600052218550511a034078007808024100d241c0c1c0e2000b00a0311400007004c201485002450310000c400841d00b155920b002034506880728403900c03d542101500301410000d84601c50703240b030250180100150b600554403d04415140c0303e01c050036101080000c4c00620107401c1000002e4a40c44c80079003168052203140ea0840c502c0c0d00001c4048603001d44500811007141410031580e001c2c400841d00d12401e00000b1a565961229582068400b = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 356979532 1250 356978282 356978311
    0x30d09140102130b090a17010c090603021c0506061323030712080f0702150304050c101409120118050c0306060901030f020f091918020a0e15060d0606020f1203 70
    0x4551b9140e07490001416449003882d40e140070482c010f0b001e0500c168454011540945d0006138150083c000c440084c03414034046540134038203203910001800f024280d503401c0001884003a9203000030084e07180142c804480310b07070345009103000c0a00321981e440700400c0c000e40007a04100b104200020b05e12010383d91001006440b0070301150840f14a00030180c4c084d612000810380e22031540c0e0345000541c0690300400c1a00c0b102d41100301403291811084280200051204a001c1840001440900f2903500e00401d1042000030110045094418501c2d640849031500001c031400c22404108034803511105401a100c01c0c0752060000302c500c041480040d182025000c46030085681d801850180d00000410403400c0342420f4070071280c0b2841042070515210702d0100e8401c0d052180002c078041c408d40c0208003020746810903000380c1640401805d1031303110b0b000c0c10956031b07510341d00d02000d440214900100080d005103000402403400d4881c00141115030000810440209a5242245d9101c481030002a0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 356980782 1250 356979532 356979547
    0x30304030f110a0c0e07090f0b0904020706020d0606080a1b0309140d03050601090914041e06090f0b010b0901020a062d020c060106020319030b040e030d09140102130b 73
    0x240c0708942882414250b020380d1030b0000030400c40d07980c00419120030008850191b40c0340300080d02c224003140a0641c4980310030fa02045030400050040c62120300140c005403d1100300d40d103881c08e9030801d01c0c10741c90642c1c943c4c200b80302d46a40030703890943c0142c0300502400512003240303149002c1c0a0f5110101d0426440700450f8080c0003c041c0c0d0b002002414030221014801c2e06d92000b0010402650350600080d0036040c00200707041a40940c0030740704100342e0000000d45441c2c1e120324098800e041800480100c440341940841c009100d00c1e0348240c002d452041e401800c0745001540740c001608000c2c1c8012003449074064903607001548400841c6d00c148000740c0030450502c00c43c281018021190350b0301210300114078030782c5038075009440180300c42006c5039200e90300ca1030242d0b140e00034032400080708412a0500344d000c2e40301e0340000f80748840140c0005001c825241200342503074403010032203149645a419401c208159034242e20a9124840001c41c20492400e404400905492007031a194450216511 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 356982032 1250 356980782 356980787
    0x61f030b0d080c06060406081519060e041a060105070f12030e070602070311010905060d110904020a050a0216050f13020909040f03030c03020a0c02060715020a090f05060903030304030f 81
    0xa9002900041000d8580383c65030500707503540b0800c641072406103044c5100001d00c2d21001403d15070365039000541040550700d41c082200b041058000407204945c4602001038a8400041c11a0090b4001c0a5000c9000e404081d202060080076001504004081040703001090030384105058a40d40322900e15194070890600300c001e0191100309a000380144140001d00c5500020f861007264441d0000c07183d07248003600103460380841481427030b400c00310811a031024804180e10405096a03c20041e500342101403000c24200d8119104000100b50000b4085070101d404000100d5048810b564605146007403201084061407044210fa016007090311409540c50082d030107450030b121014200b4a00ea242a08100e14511803115007980444c2c41d0540c240c042920034003c80f828400e1075110f0400203051036003841a680c0c891002507620340303000d4054011403d42030000b000048503559406195a0401c0101d40c1031121560080e44516010401c00701151408015a0741c0305405080c0508003c2c0100802d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 356983282 1250 356982032 356982049
    0xa050105090f10180e150603070908010f05010518190b0307080f070513060b070f02061e3004140a0b0c0a0905040905071e0302090f0609061f030b 64
    0x3540c3d800300152003015150b941c0484a0001a0114031300030301c07225510800381070b102c0b00548142c403080b40d1107203506034a41440e40045410681c1407500c0c0c891141c3d00c20b006400c5456400140d2a400e0712140104901c3c905040300d00018403180c83c848445080c8400c5810b0848501c00240320120740f14002481d90740d80c00d002c1c3c1402004000f0644044141407500d01d82c0760f43d01d50150520940c1e0141441c034502d8564070400090700c000160851410040d500c8100c650407403840e040b40e010b0170410858074040301441c11078100001031070341141c0300e401c41038003100c9600444d000c180d04c14000c110410300040d44181c03003a4205030401c4508007110401c011241c240170701c046e0050001c240c00740c00e000e8548811070043c0480845980c5108020751070340200820b40d00054806480c0d644683c00c1880280c01d4007005055088202020082d160b076207a000c40c20004003101c6240480c0009410049181400c1303500581c440c02c1181c0100d4640e550040022000b03d1481c40d200805a450b104c00d69107449070f080 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 356984532 1250 356983282 356983309
    0x2010b0d17040314060a0c0c0b040f210c0309142103070c03030f080a050f0711031902010603140d0801270525020c0a140a0504140106020d050403020a05010509 70
    0x130400c0128521060080d5151015514415118505041d048803131744210500340015600074900c4030326481d2603c034801c00d0030b004481982c030031b07044810103c000030140340200e002924075202c06103442102c0c2000307400086503a01c0529408404400c2000503601c0c02105040c03001c8a80c0c000044145000d1210726500400400820701c520700140407080c075810055141d590740d441c1c4d40e100344913958010034030140c1d5010380d0b2140d402c001580120754028011030105c0314035060501107d0600303c000c244400d10304d12800760315002d41d541d1f80c408d100748603030390007002c0700e1442c000004e025500304030030020035001d0140b003003581615000e005610160b03070100303900c00f03445013644040c0070718140140400c4013000310b20f01072000240c541407400d9807c0c1c004500b8490134034006101d012501c1ca00000c05012a07000208554031000248000c68039640d40e103d2a011680340310b50701e000700d41c140175010b89801403a80b403820a01c10140010401655038030104802e40304203186c03541d1903910303410106090412092 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 356985782 1250 356984532 356984543
    0xa0c0f0804080601141c0b1509010611010e0f06010b07260d0b030c0303091314010306020a021b03331503070b0316080c040e01030c050a0602010b0d170403 68
    0x15000404200008005041c1c40f4954102104a0720040402c0480e5410728070030403060030000c2c51b400220346c083d400b80f07512003092318800640d40c014100248200109800c0700b40850b035900c0324925030400c00d01c56006504441d80040106080b000c410540d0b03250148180008680e0029611f4108070300d4102c0e201d14152445d41c0c2882c5000300c81101d8246070402c0d400810f101c1e00d00801c140300c0c0e281c0020122340c00c00010300074529000a4106004100140f21300c43c4150705d4441c640c074840000d11815441c0258012070b001030f150004100000c1c2007045521a40b0b54001180c0110050b90340e021841c0102e004070b004600c180c4051941c1111072140c01c5503010201060080c1c00c1041401d80ea1308410b01841040307056031b0441e501c1c0d04404c60f442c08155202c0c807002103034145008200c1d01034110746c0d8103c0c1942c00150b0520751f440122500a101c01d8000310f031403444101e030401050404443c00d002510242c0000d000446402c804200b10384041803003d480d2900a02c89913250380506ca0489000e180c102 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 356987032 1250 356985782 356985787
    0x21509030709140402120a0f02121f2301030309050409230a1203140612071806030b0c031315110409050402090a06050d1202100204060f090602120a0c0f08 68
    0x3d051100880c1c800c68013603018155890b40e60b1896800441c40280055104035111b410310744640902900500380b4101210314461105106a0304d0880305548550001030180030425106464810305525403900071480e602d01d495005000117074200e021a0b040d6981a01c0004418032103041c500030300d4002d082c141d0a10034a02054010052012404c07034149401003c07605182c105940c0100c084070428041600072440460119015140c0121410010740840045414450b00c4100c440b060094a400d4411902c0c0e13158010010440d00900c900d078410800b07400c0740d0443ca40145649541020854000c000b104040c80302810310040394004050598048059a100c81c1c59401c0c410007000d0948003a0702c90341c603404c0003403520040ca01030743c415603e01501000c0c0c0b80c0f119075100d100c101c22840d100e03001c0d8003071003e1008410320144080e000034031a82d03031184c6502d16030b40d8015010800342d801020454005050b032039803030325581d0226810a0301c9460690000401d505007d00507081d1050010500c8000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 356988282 1250 356987032 356987051
    0x90f02160602180a0b07020103050c03070516050f03030c030415021602101119060506040504050d120b0405040c0504200315060f040e19021215010e0a151803021509030709 75
    0x882d000d0b0109507c00e8804001c83e442d200842441070008840002c0040c40811101303401030340d070b02c0340c10003403c0c03090049956034140c035051542035400885400360f4410000c0b08000030712080c0e80303031154030b805032510031840c20045a08610070b001107005d0283c002d11007589107840b400c0c4918140c04501082000b69048042409a41100c0c064019020b941050500c404038186140030310540b8025640207004101d0140c4100040e0750002c110303901c40900c1035075040400110388450146074411072042083e0400b40e8241003c000c01c0b90801084011a04030b600364503a10023006c003003141c0e0840c0e8400c0e14031648001c1075000401a22030180c1d600d1400700e0224000540e40b040d01340307043c0205422022182410b02c1d600041040340038142c45c078840409d0840100700741c0c0001c0c030744050740054180343c030004046100e000324241c6c80441e0f0041c100080142e04141c0c0e1280e20188446c41c0e111030113902c140c81451a000a00003d0048145080c0d480f00040d800070150f4040280e0401000448070038001c0446 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 356989532 1250 356988282 356988299
    0x909031303050f0c120606010305190519060b1809060303040816060f0f0206070509010e03030a0e1011100c0507050a050a050705092e0f0f090f02160602180a 69
    0x41880c59003050384120804104c403413405005d80300140300384000a16281d0756a0b0f0046000e4403020b071040c90104000c21307145008400034002d151184d8141e01c030111248900d01c2d07448045903140c1d840301c8007599041c4600801b0810700200c6404400c000c4410615039103440f00028158071456004813400d20800720019038004494107540c08555040c2c5544a103d6800780064030351100b0343c072910300140c00110014595500500c017410310050189000544c0b82180c10229107141d10444000c5c02080b0081c9461601f450000a480e100b0b004070701e010b11900400451441d80e4603c038005030a01d50707440c0c81c0300e0740c0c6151240d801d85111542040480b40e070712042d820000e0311826043c4096405005070840418103091a1240600441528120481c034640080054001c078507504e8100c8a400100d5034001220f8540c50201400b42102d03071584000c0a1620004000300c6100005100d40c0318018402401481c0100d41041c5040b5005000503a4908040c444e01c0e00b0300c42121062544080e55500200d040c09 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 356990782 1250 356989532 356989543
    0x60e100b0406090612060504050c090403020a120504050a0e040503070206031e06090c071e0c080c01090503070803030403180905010e07030c03270507091a0a060507030905090903130305 81
    0x3039900b000219180c111120648040e4007910105403102c00b280c400046040d406143e0242c002d0b030542d44a4400000000e02c0740300305440940060707001d0794401e02480503911009003e403000e809c0144c40c040c5044003003880d0f00c00c14480e00303164110302c100281c01e01800748103d4030303030541c0105900d0386c074034002c1d01500c03002805910710f81e680e010303030f5002460a0420900c0d0501440d10003091a04001195072240300010300c00e01088000b0007507481000c0020f2403000001c001c1c01011000e81545078002c4d0004020090f41c1d4010b503c02d910026040041800120441e41c00540510b0f001d03e1600d07600090010f0000c0a40c040003055117021700000b203900d40b0310b161034044c6056a800384000369000c00e044050f10119080c505c100901d04000290300e911202403105c40c54420811f40341c03800c1d510740b0048125481c0e00c5041c4c00386000d0101881841ca000342c4081c01911f031509017075080c00800d4a00a00c00034040c040d01c0c3c060a00349002c107441c41020401e551484a0601d10758603102d40b0303858601d0721034 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 356992032 1250 356990782 356990801
    0x5090d030e0f01020318070e01050d080921060615070c060e011404090c0f0e030606101403090d020c012d05090d030f180b030a0b060c0f0703051c020316060e10 70
    0x1401087e038041026541940081d040b0341c4000c1c000345802c0340c1074641103141da00c044601c41d41f2500d0b02d189042800503200c8c402100d046078001414140c40c0c100184801440240d4045884000030407200c00001e02c10000441900d0b9940b9100c842c401d812001030b5141100115400000300b40801e0005104040781c202c1c1907100c015544002000a281405450000780c1030b80885c0c0c180c0200000810602386400018459012850b00031600c289640d51520301b5801524198103a800480c0f101c49100d40400800089900038030785407a14840b001c2c0380c45402c0d01100621845844454042c4440d0f078401c00c01d03141003100040c064401c103200da01d009001c100228000c01e010030f9a05200f903001007000d840c0f040c00c0710716601c0c5491559481c2c5030343c078005180c240a01a8040f0091000e204215010005070704108000e500411303c850460074140e1a0040b04079540d00b80d0799940b01c103001c04135070200a4410318801351a00d214980d61502c2c01d4006058102c102c00c141d4807444800881f00d03c0307541c1214161 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 356993282 1250 356992032 356992081
    0xf080607020c060702100f0201110c0105180f0307060b03150901141012240204080f010e012c0f01020a0f0e0f010e1504050d150f05090d030e0f010203 66
    0x200c9030b4000621445018550002c1d6003c280d02c0504046203000e006104444102c62000090304080000040c50035004910006030310ba641c4c02c00c000815450540c00c0c81200044401000000010b54080d50b4038440e018009161544800d651441c5880c10408110f403d80402ca04101e03604d4400300340390092203d1810642d0300c2400402185810203000400310034bc40c91021541d012217402d03290b13419180c04070607400e4a0b58002032030070802c101042c400362010b410f004010b0141040681e51560a496509130074090700d9250186082e20240e046c1181c003584400005915420a908100c0e0780c14102141403c1e0010350002501080301c0794000c00b508083c8032a5251698202480004c1c042a00c7c07000369281d02143d521541c1d900e0368541603811007100d02843e00e90f0f0b46082d8840000c583c005490407000c607488103500441c111000e0907405441c44d0440760324410005440c02c034007015910700303842c103004007810369520340011115414010b48802c0e44000c00299541c3c107110340c0c001c040b6981c80c2c040525 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 356994532 1250 356993282 356993293
    0xa2102130f05070f200c031903271401051201090507021540050d080a05070c1202010e0106170721121b0317070207031703060a0f08060702 61
    0x5060b40075600c10034115903a80d5840c10281d000425909807405e850702c4c1100c082c400c425220540d9035042096a041f1820b4041d9807180e68401d142c082d0640f442110718000340010744084505601c107079001a001c441c0c03d1541003000020b40d90050f1814819803c0541016440d0000410000f080d43c0041d40100e40d50f600700c5880482e1101e0000054006444078810000c0500b840441404816101040500425201c0340d40b00c0c40070084800c0d1400200c0c3c11601c40d0400004030700041d82010803035510080882042c00740307160060004210003143c0600071b080348a10003c850005100754004540d02c00180d000300305007600d44021801c102c46078040c082c418030580c0004a1041d6101213440700a5550000c05005078080d541d91029210010022808000c40c0d00071440d0002d50382100ca82c0114040d4a0789040d8030901c020031000c20303c0c000e00b074000395480250b082002452586a032003100b00b04006840e160340362100010400c150540c4140c00004018001107007644010800900448142e0200d44 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 356995782 1250 356994532 356994541
    0xa180903020d0302280e030d020705100f0c06091104021617120c0702040212070c05010c02060c12060301020d020307023913060905010b0405030f0c0a2102130f05 71
    0x28140e205025501c50402e074050714045108401c0c0f0711102c0c5c0d44030b041c01c0c84642c8907408400b0130301e040da9445200c001644403c80030490707820310b4450b844e887c2c042031400c0f0200107070005010b13249000c8800d001b081e880e5100c2c0183c05000d40c9042000c00141d00400c15561f0726202010001d1441684405441c13511050140c015426803400458103042d0602d14003144507035401c9420301c440c0c0c0003410140e0304181c082082500102002c0304291060243c0d8503400300c6440c880c100942180c1249001030309660041c070a2104842444003525000e03000380c00c4285d0144d481d1008640a405406524002c1e41c0c0080103020050307401090001c5030b03107036950b0010159994511100000326400031440c540c40e0f289005110a03050003a080d9000620001c03000c21410b645121440c1229001d90000310f1507031000c141031200d85402e000703281c1c0c10000030b0010070042c001100000c5c001ca44503c00c4c40800d2188181d4808420b020640c0552642c0c0c000b046a14100301c1011400702522518032001c0364540b41c400042c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 356997032 1250 356995782 356995787
    0x90112020c0a03050c01090b04060e0606120319020102190503041e02130218030a031806030e0601050d031209080d05090a050d0809070e0a0c080108120f090a180903020d 74
    0x1e440c003889180c000d01418007152801d0303c0607030000340c2080155490360700441c0429803032040c1c14080e034491341b800954001382c074454900300040641928810001140f4034010070030008203682e1480c00307003c01c5081310b80c80300030300743e0091044910381560f03880a003c10f400c60541000207036100d0350007204006000c02e009200480c51580300a0000d612101d443c040010714a02ea9002d400034805541701c0c039400c41c0d400340c0000d241c05075004044000865a01d865074801d60a000c2040041440d400d051144102443d041600c429050207400d000c0d881d404c0382da4042c1072280c5100170205101d25020400043c4905020003ea840f0107001e11072142414040b40f410301c80061040300990f000f802420000382d1584e0101c419080150464131030b841a60800303d56034a815540794001c540300800051a40c0001001402484050b4002d010940142001100b4040c9420884640000240703c40b9074456881001600b0031000da003081e0701d102c8030207010205d00c8542d40e11204540e03001c5c0d000c8501c0c01c81c10303000c00c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 356998282 1250 356997032 356997037
    0xa06050c030d0f2a1d01020c100201231608160e0402090303120610080105010906030c02150411030f010501050d171b100606020307080a050a09081209011202 69
    0xc03045581c801c0012107104560b90744074503030700c0d044048003040c10b000d0a041000380f05a8444448102042c0a41144000b80c004c11400344d010750074154804940d50500000c1c3d2034801c006400ba0290b45800c00300c0702c00902c00c0d40700021240b1540c40d441d81080342c1185045030312a0840d904c140c5d00b221000746440c002d0240400c82d11802c51104a040070030261101203403d600e035845030340e4100b6001c3c00950000e40c2c00b80090841c3d031881d400310204900c1d00000b0409140c4910450700148140500103000076681304a160096034454140030a07071885451049140c030303841c1000800200c14900030700040010900e02071080000840840f180490030051450890794203124943d840000d1014540c001502d00c4a1019110f8852030f40509001c5241d1120408540070141400c49410042000420100034403030040980843d100a50030001156183c101d0b40c8240c40b080b2060000c045406c10216103e20340000240480105036918814440e9891629412190303a050119588440c0b102d04420248203 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 356999532 1250 356998282 356998297
    0x807020a0b160e0319110d03020624030703080d0e0c06031305030403060203010b0909010e010302090720070807062709090503160b0f0105010503040f1b050a030c050a0605 75
    0x3a10689a1641104007904800e03074084003003848142200c150056030240b001e81c0103501110000201c420140c500091b03801e0070150528403031000c813294000829400600264070000c84400e025103500c620b105032003447c0e0801406a414428103001004200e4040d02034001e50805000622400500103001a1102190b035000380e008030042c0001000700381b41000041029001d40152490316842e03489070010b0780c0c026002512041c03000280201c9600f40307449031b50b005041000001d07000354110b40c000b400f2001c0c0586050208451045601c5001c1c02402c80c004281030b5032802c44401711b0b5110045d86e05c4400300d1080a01240c41c550444010509940c510f401422146522400e4942005540c1c2d005060a01e0f05458a1105100040d12070708046001c85d039440c02680b0031102c81c0784c403001c101140e2005030080c504010041c800e000000b000c042c0d00d0703411582d03c80000200c40404d40d210007035000a603445503901c540c90502c00018405c0011407130060310004e55400d003103d030b140d40d4140c0c3c07188039862 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 357000782 1250 356999532 356999543
    0x18150f0909130302120a0908060c03011a2104020616030e010909060e0c030a110403140c0103090305070f0311030a0306031b03020d081305041a04060608060a21020913030807020a 78
    0x43d85d2810841900000c1110041500f0400c10b050b4990300520b1500000303e50018107080c0c00401800042494809424687c040344111840c00d0a50710440705040000c400d12610314035104040360031591180309440741c8504456030103000300303d141801050750402031040e5000c141840d401050328920744c058542915410001d260f8141c03995494441c40c0d50000f01401c4001da03032071810039098400710700100010f501510381d41550b014601d04003030924a544404905040c540500140081d81180075101260380014001040490b2418203039501c850103681600b550000180e6000341c1c3e6003544c452015240144c6024100d0380401c0c0400b180650180401f0358458001801d01002031484001824180a0702c40d072207000360b9403500030800340e0703c1100c40c440408000c1c50304c1006505051058034020600b51074541105c3c140000400c14052881c003400103035054141002c0761001e000c052a0164030350207840c44482e07103441305a00c5012442e070b9108070002403c202c08034060610001c1c11403142c03500700 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 357002032 1250 357000782 357000793
    0xf030f01050405130230030a0206011d041412031f08060402031e0708030301091409010b0a12061d060103050625030b010e04050a021b030f18150f0909130302 69
    0x5070201301c0641040034020020b5840800708241d02c42000006c01500c1000c000195280d440c0710b00007a09042d0141c01400364058860300440c1901030140305140c21a810036140c0040d5030050307002e1820200c510403103001c1000000180180603032006e4400d014400103a41d80f800c02610b4040329612018103130303400b03980365100700c0040d03e403c5503070136804103151000011160000e544a402c641150002d903c0900f05551300e00c18185442e561895403076110081c80000c104440b8858000750846081e40901480d4050030b040b01010014507500c400714000102c914520b00510f50301c581513540509000849031360042c00003041c02c0000c1e000c105038000d280000310101e800c007402d90440007062a010a203040000d107000c4030440f51514801c40e40611407100300907940d07a81820090383c2500d030106a20f40c45034020000f01c00407038044820788200483c2441540c501c1c8280c080002ca003459465241e050a400004d40e4370304416080c40100510001a1004555542c509da041c5003440304100c000340260700070 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 357003282 1250 357002032 357002071
    0x3071407051506130e010228080c1e0403110a0b03070e04020706020f0c0c030c030a0213200c060a05060a03080702010c42020403081606060b0f030f01050405 69
    0x40002c8150700c814054a644103c24a20b0b040505031102410306801c142d50019121324040909502c125110300b5010301c0c52001107121100030600c0740e00508466080300302003107810004880350007a000d81400501c0701a11141c50303003015031800c4a03410441d40b1580460720001042c04040094a119030219207445803065186004d1002940c0b0045048541d581d0030811072001d95282d4005c0d0100c0d40c500303401030a440600750b041c5880e2040c0c4d524103510a038030100341140140d40700c1000281100340e02e070010036410101c1503c52911280e80c4800940b814020070038242585c8002804c0d485010050000d11550312003609201040e2094080645507640030031070400554007070a074a070b1810340b065162078400c140000c0c90b6880c1c40040e1300050744403204403427103d81d15803107918003483d22130200500b10b2506103075035a1410144140035a20f081c58075408200018444c550303208800400c0102080c664455440b00456000d41c012a001106580341000104a904052017905d1003107440b0745004018020 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 357004532 1250 357003282 357003313
    0x30b1e0c030a0f15090b040501050922050c0d03170f100608090c09090115050312191809020406020f010905030328020706140705090109060c0203160b0307140705 71
    0x3c4800884419070b40b1014441c84003003603280d01e0301c0144000440019008500703010401a03500c180d1010748110b40c0c010078813080c00010031a0300300d03040c90440c6001d4010b10510f000350404651010041d8426040c024a10a1607000492079805914511030501c4a80d291211044135400c207507810301d42d0101810043c0085802282c44581200d5290101c400403104140041c3c49004d003150343c10503a9464145d101400044944884041c11046026002c41d06011000d0714a03401041c85603d289801c500e0110002030060b0050038504114016510307040380c079021003070003a5005114a0300188924010b064150720b061003624074076507104001c0d5146031120f20401c0e400c94007514011b00800101c8100f003411a0f07251000f080741520490021942c52602c181c071082c00800107200c4010b1281c00c10544c02035a0740003549905503003480c05c0c0190052660b00200b460035010203100d0040d0800c2000204080c100040a10301c500c0d000d6840240c0072031082c03070818040c042e502e0f004216034005246800500b0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 357005782 1250 357004532 357004541
    0x603180210051209070f0812090603130602030406090b060603190e0304050307090e0705060705190614040f0c0803041805090118080301031e02010813020118030b1e0c030a 75
    0x2407040ca80381d070a103410078404070a44002580d000105038083d48041041c07400c0c0d80b801d20000c1928001400b10854101c001c50703183e1090b54032180c13003010004002032030061511440f19446070031a0045440c3e11740b51030904020030098409030f4040c2c6150380040c0141c0f6110f8222441076401342c200304001e601d008046005481e10100310401400140301c00701c1e0030b032410490040100000d000c04960000740e80030250400340107400003801000e04010076070101d100000c1c50030344040010005151403a490408400800f22940d0500c01c52004205100501c031240c00c654040700d000b9020b10106541c2d80e40d625070750748203601c00d1300035003010040c21018100c1c03c0c0d8403c80d030041d028000030400f440e025056000f451030404c0200c408107404001441840124040d441c40c0107000c0989813a0b2850580010b01194001041c0350703003000350091000b04592040340f00c90f0b94100c1400e420743d00180c692600701c02c100002c4400748404080b4031407044100b403401503114028680c8500480c696107480c400b050140 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 357007032 1250 357005782 357005809
    0x120f01060c02040f110a180807030c03141207050a021018120807020607051c020102043206030106090509060f09040f050708060c030106030b0108010503191106030115020706031802 79
    0x6580d0b00c1035202100840c0000300300060f8070396a81400410150500120f901f096000391601b58052481400041d004000305025a6008042c081100860060440c50300e11003440745041c80c2408070315082085400101c460083d03100325001c41460304c0003102116044841803407500ea11001040800103040110a0304840a00904080d442c00c03960742c0118285510400084509a016000781c85070801d5613500960003881c40d1000394034162074603030700901b44824001c0c7c003d240c501074485860303289003c2011442404021309a07507160743e50b607003016000049912440703001c1c2101c440052034525000d800101518402400d290041d15140c854490580310444211032502c60000b01055120042104034400c0c10042c58040d80d03503043c8080201581c01c42090b0a050000010050000783c0c6c1c0402e14003407000e00850044064001800e1a2003404a068045900b1900c00000401d01071030707116543d1400e440503005c80301c0060380c4880c110b0807a042891980c40d002c4000e4030030001440e10014a401d80f = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 357008282 1250 357007032 357007061
    0x2010902040213240504030b060105131419080703080f0c072310080609100e0a0906060f0602070513022205010801080111090f0105041505120f01060c0204 68
    0x269009540450100c0e40646004000b070243c03040c040050020204841950b00030401400413400000c26020300b5500403404001c0c042c5c1d8244001880c540d100b4016546030842d280018600c003540c908281c100c07201c4050442d40a40c4501c042040007020402d4000c0440d0403290017450720a183d61204440340d04002d60403024440c042203c54190241004100c018080b04254000e0b04500500c16484010040c242035016004c28002c1390768142d0803002003035001909403051907a40c1c0d900840d102000c40d15410444078a00039600b4041c0b010340315072280c400381d41308030020070100c1d84a05030303488010b880c0d201e41380050b44107010500c010f00700700070340484e074950882015080904000c100ca8840d03485107200846504a04820442503034800c41c450f00500e1840003c0200b40072030b85600c000d5206100d002d034010f40c444130b400c0005911074030484001384018000030004094442008025610001c005002009803501103002240c403001603504031a040d846e01c2e082c05c0c005a0920018001920302c5207103 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 357009532 1250 357008282 357008291
    0xf030703080f16023109020f040c0e130606020114061c140a15060803040302030307060f0605040906020901120e0a1e120c030e06090607020910030804170115060c080708090607060f0c0c210201 84
    0x140341c83d026004338003c1041d800104400b802e014000b82128100b003010640d20f5440c2c01446101e45404070f8041d1280c42c5061407400041880c203051222650461032050b841c8207010000701880601a452500038060b208103000c0c4980d40c03619655603002d01c0c00040d601d508204215000a28140e2140c0a103041001021400c0b81e0748200240448654010956040d500010326000941e84400407034002c428800d8104003400e0105085551642c1d0300c5030050240710b090f007044440010b0740c1050060250300100300c450800307031440000c100243c0658103c0101d03940c0340300c1824525011080c5c0e8568900a403ca0381044460303020031050520140c00040d0501d2070407004400b040030300004001034405141c0e00000070f6076070950309086031601314840c0140c0d040c1960a0249036030081210082540140b25035450b0344450802c180e0034407490304850b510440024103001004925009040303907000414040148880c188026609410005401004900e2035a041708c02410840c5100804404030b100015 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 357010782 1250 357009532 357009557
    0x70509100305073f11010305010e0a1d031912050108190317070201200702090f0402060c0d0e0a23060c0102070215090f030703080f16023109020f040c 66
    0x400b08a4201302c00610100020259401d002c0350a4a20075000003c2c40d080000350701d09000317004002d1024142d03004454079a542c1403d043c8140b041000380c030a51005071703650f520400c41c0c400c0741c5030103514014000c50003501c4003803010b8440340f152078100e0308500701820f6101600300400340c0c2000c0d040011424055040c80724081c9900005100b40b0400c2c030b903000040c5076030444540c070047e846041c03488400000100584d00050300c41c80c0c42c560300848017200c01d1405440d2480000d10600808a600040c0d200340c181c0c91800070b03031018108c0000541641c0c5044420f131503e54803250142140d0b42581d080c00e8040032016030b404c1c104000c050a920a1000501b40b003c541d0000e00034542290700e002c18080301017541d0056141401450000c0d5800718024411030f40303140d59201890095003103440e8a50004a00c0d883c0c03c01da004c2544100139801130000c840542c949403940c070a00041217403c0c48076032003440c241030701036000d2103a4806c15400a00101c034905002c07080001030244110554204952050b005 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 357012032 1250 357010782 357010859
    0xc02060409020a020c19141e12030a080c0306240f04090f0e060103150902060d0501030b4804050a0b0c100b01050316110f07050910030507 61
    0x20841e07008254044c000e400c005174200b2140c10a0508010501c0240c524108040c02d03041050944a80c2c041c2d501c180a10905045203543c400b14002243d0011240e845851000d0707408001002011103544515160b03480300b00d0341030000e000450300c1d235410282220507a078500c034100c0702c008000448100c005203042501805911560415030041d00c001d41c031a421044440428043d6005c1800c0750310060031a91f1440e1545401c0200e05199000030f1030340d0300d0842c425501d405040fa01c4107510000c0920195940745400810300504889107401c0c1210500e51080c030300c146819510740c820004828062100c5620202500a20f401c510000e1820b0108400100364484449205c0203198182c10f140e100c071000541941401c0c444c184218a440c602650300455a8001c0160703500984140c081ca04008a00c884c103450180d50020111114864015500450040003d82c0ca0039100c0584450f6525202c910020720310100f10300000344107030480001804080061180041c0c0d040c1c1c03010006101c0040107408 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 357013282 1250 357012032 357012037
    0x60203060d060f1d060c0406050a020a020301062601060602030901030e0717060106140c0d14071b18050f0a051315050a05090606010c080a0903020406120c12030f0c0206040902 77
    0x40c4110342c0c40e00403006a02c2d60020380c440c3c0104d10003014065501d8000001d5805114a000740018800045a402440303031003040780082c0d007030380038008000d00c40d116130408408441d002494540451920490448480103004035022501d00d500207604004da40d20054000d0710004c05884000c2c400d14400244440c114450304e80d00050700e00c01f80c5a01d50500030000e000c042d00b00c211010900b0200a00060400c0009541c5500b060901d03040c00c48000741449260b140c4200c00001d024101e600c60304a4150b04045a100222035082c8403001c1050b10b25100d5106a840444503c0c4003254070780009810650f81c0d4200540c8050070002c1c00001450940e07401d0305140140014590f12555141000300401d890310800348c10040c020002c10207860500002030403080080030090000d80042034021002d03014141c214082d581c0140203111b0700e5156091b200c04c1e5801c4000503508034070071400000c2c0301951074101d07402c00c0341c0582d190088030404140c01d9410141c0c60707c080741c10030700411000a050741c0b240302 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 357014388 1106 357013282 357013301
    0x3180a1a07111b030c0a05030703110f1201020c1018032129060a082208121f08210409021201030b0a0204050d060203060d06 55
    0x402c031030030505031600311100d1203200c03d0710100032264040b011044009504644240310132104000290103580704464054018110600100703080009048105401403c08102d500303a0b9400b02c1c101c001003a8051003640d502040c580d101c072005028542071b640c031800742803080b100d44c2d001c2010403d54039040141403103048099501c803072056200310b18001c3c1203541c041000690300070402d40301c5940301118910941408540809610b85401995480304140d0b507400c07001d030381d03582c0810004014003440034460034000c524070b0b0008005000904114045004014881c00c1c410001091801c4d0441b0081e00c150b54130b80e0a0004010000e002c417801014500c0c00c0e4031b49048440410307054826034000d0080c250000420308080714a0b0240d96049902ca80300340a4960340b190303c070030704902603401003da006207010030707550215002d40c000c3c6400130b200800c0c10605800d642e0b00c10084a14488 = true := by decide +kernel

theorem cover : BRFrame.Cov 356834532 357014388 := by
  have h0 := BRFrame.cov_init 356834532
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356834532 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 356834532 ≤ n) (h2 : n < 357014388) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
