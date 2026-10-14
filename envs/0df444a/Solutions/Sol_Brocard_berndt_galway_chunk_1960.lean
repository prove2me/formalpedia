-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1960
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:18:29.371105+00:00
-- url     : https://prove2.me/submissions/be314a83-f281-4267-b51e-225a438d6ed5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 352338129 ≤ n < 352517985 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 352339379 1250 352338129 352338131
    0x50a0602060f0c0304030c0b0103111c030806011413030b011a04140103020d0209030d171005092a07141603110409060f0e2407080f0606070c03080a030b04150603 71
    0x1e0030305104001216447d076102e2228442d95a42c4d040c400e100b40a8200998880c4503951805100241100d800303051065040e100c06c5130680d642c1c40150b500d40da000300c40d0907619004002a603000c05101c075890020714460404000294180303030031440499032514005410701c10800043c081c41c651165006d0140109203005640c4040c481540f1003e070040c26030080d094442c490108091980006003807030a420b00c034402e400142d603148401076101d0340034883d2507004184480441e0300e00030b0441689040042a9811001402107121010780c5035202e0601136480c0c00c040a00c42c00341040a002140704c0c1c0c804004410409400c585440d00500121800b451050790b5541040c0c1c10130503690880c040c40702c0b49400802201080e045002c1e29600310030310001860400d85ca500150070340e0050314500039109507413001040c0d42c0e01d0100340340c50040504190380c4a04280150000201904010f02c00f451265485a46607407007400c025041d51412044607200d2801c10a0007201c8031800c0040108070b030340c2c0b450 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 352340629 1250 352339379 352339381
    0x3090a0b1023030c04051608041425122f040e160902030f010510030b04051303080709061e1b03050405030709090803040809010225050a0602060f0c03 66
    0x100092800c40998424000b6121800803105036007140b01d00881142c0c0203a0035035007281141400c2004440e005c88041c4481c1c040d40c01c500201c0c40c440e0380710310383c80f42c454140c01030303903e046855051501e0080501182440158050b81d5184030210381100f00a09010404280054155840b1002c441d0050305003101040c840c051440c6003900c00d00301d68490640504104110315004982c5503d48002001c1410855120701d40002c510032140300b103070701c140d0381036248110342e0342007200700110300207080d01010405448602140040d0354074450240120881c89581c540800e40e4600682080402062042884450b0808204480d00849800c02c4800340c450462012840d00205840f29011031007140c1c1020381110b1038504158200000303009843d0103d0884440540c3c44512405981c40894020204030003440418000303142c0001425010505005507480104111001c83c0541e003428043c0103001c2a5a00400103814584a843c01400c06440035011500d401c1c220b2034000c0301c006d00842c0c44004008 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 352341879 1250 352340629 352340641
    0x30b01170a020910053307081908040221060c1b0303010902040e06120d14090d0c140d050c120307141006060c12200d1d030303090a0b 59
    0x4095030300784990041c21003040b810000113440c000d19050040314003c81d014803c0d07824038941000140c09085c1010b10501d00500164842a05034001c010304440a80042c842d400000f00c4040d01c4900507600d980c0c40e00079600c1c0a0041140340582d504100b6605040300340040010440403d0550748092000500c1e9a259a41e10803205e01560300d031030f0065a0301000c0000b150a480d603800400440c0c241e629002d010381c030b079681084803c0940b02843c01c7c640d03100a01c48032025002d504100e4010003a004132a00300140d060120728259100ea00c101c41c142c200c0002480035400c1e480c0c3c0010501010b0320305241d840a241d4410382d0390515910041c0c4160344441001c2c00c02e0004104454205a00080e0801140040048242e031801492503001005040c144040781c92403140e01410740c496000b04d0f1541900b01802c000f6100740d5a8074018100d151004005541c00f0703002044031401110055985050b440605d080400e600b480d1080b050748280c0080050281204000030818a103a41165400c885a161a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 352343129 1250 352341879 352341883
    0x7020904060e21090f010e01080f04031707020c1206060a03060203061212030915061806041104120303050f0f060108090c0301090f02091b19050715021c0501030b0117 73
    0x200d6030500f00c60034021071070000d44900301400800000782c0d150000208440c005540310840361b9003640c0001c840e100003c09e8090003c07141600180a42491501482115002e4100010482c0c21034003503400707218440b100f41000c01c1c12518680e2107801500e000e08103400040c0d500400d038800900344a0b000702c0801c1c41503a031000070720201ea801c0307002c4800d441c070744c0701150380340380c00449880145000c1d0300d108045469120080b2481110010440000a024030344c9403c1500310284c50260455038501c1d00d003101c540d0b1440200090210b6400000d1680c010340303001400d8400080000c1e5050380b260040c8010518011101d50b0491002d00744039840380d5600036000e01e003048901e01280e0540c28880ca10b02400260054114440c0c000d4501c40c1444e80c0c0c00410b004048403401903031094050070028a1100c420342c2d90070320b2085c1490b00d0554540361864032003030703481d0000404c3c054540d0f5001440780405103044201c03084c0c002c4400000e01c03642d1b00d19100c0d085180c8051180b8405495141d01481c680942 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 352344379 1250 352343129 352343143
    0x1c1a093a1403011706010e01030503030a0504061805010203190605030d0f02030d180204060e04050a0314070515060a0816060c030509060a03050a050c13051003020c0d031b0507020904060e 82
    0x120740503182c480d039403000301c0307500703e1a5140400e825006503400414001c42a801c081e044c2c940040040d031643d25004400402803030020020386456665600c1e071040340c82e100c10281421400f540025880c0e0030a8041580031980a8040f108100c0c82d001c0c041200d0703280460446070307900c4107040040041c0400203003a400c43c440c5501d01c00c2000d140c0130240d00c0001c2540f040d40995802540d00b000040d4540d00703844005030054070007600301d5010004800000307200e41c038207a899071069040c0c1804c00c08542e1b5564600300c0142e202d00d80c1c82145108201080c106154050020882c1c2c0700241806070824010701c1c0c81c03130500d018000c20401c228900109050081c8103e81d01c0c5036000d064540c1c1d1360307104900280144404d643e4000c00c6030401c80411902e002c94000d0301c0300d5407024130010f44100d140130304214540300102b504030141a028408d0881d014014480e950321242241c6002c100c0f404c0032484140c044203201c804030280541402044050b0302d0320460282d02650202c0006450070381941c10f90b1030404 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 352345629 1250 352344379 352344407
    0xc0703020717071509240210090c030204150b0a0806030102070c030b09010518070509130501150806011508010b09010c08040807050a090b010c021c1a093a 68
    0x10399000850034002c0000c0e100c0100c842d01c003000b1003603407080c5100701c031059110300c910740b064242c211140301a6088910345010401040c01124004c042640004084e25a205000c0e144c0d4803402a0400660805010b8a038204141101030400242030994000e510f0180d02c02d0a000c120000c00080c07842e490940c1125500c42c0c0081c40d80580d070340e40c0d1800b264001011a0811411350034040810a141c1a8640384407007840144003820805007080103020074100001c1c0081002e41f584240d130130100703000780300d8182c5c95288030304440314440c10119402c0c90101c040e801103849128006003968540d5200e00400d06407001804100d03a10409000101d82c00680454060040030000400284001000035401c088500c04d80b607001c2e0784d96035a0200c0c4101e402c00c10056012640b041c01c400018030745035101e03510070020422540048142512505071a1030882038031100e03109a401403080c1c140c005c000803800420449030a110351011016418a00341d0070035104022241401c082c1014107006110ba000450 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 352346879 1250 352345629 352345649
    0x207081207090e182b030c0c021c0308010b030712180c060e040f0b06090906010507060c09030201140901090e0a060b0c0d09081b0d0809130c0305010801140c07030207 73
    0x1007092082c0c01c19000342c040308444988034004035005e0360425140c425030306110380000fa096081d6400015070242c01e41090034010000700c0c071085401640d400441d48013441665140c00d580d10158032340600040300617008580150b005208100801d54405820444407040400c0820400c04e0b81c02c0a005e100030654004004480070301000c6261940001d210750060310485c2c0c02e0014a00d8482000102c070107000c001e80d0446410400034069060542d080350700144189440c901e0400d05403100001c80d0f050b065a40d002907661182003003550380c07000101c01e410110070902441d02d603683c00041c0024074940b04261203003440c0000582c0d08500760340010010010984001c0d9103a04126590703886400340b003044000f203081a000819107080019907070741125018021118100703d842e0070418080c000d0403085460107020000b2450640740e5041d051081e9140c1070020402d41c2081d400502034a03016000044268501b2426841c105000d124407500007040c0d942c910340d1115942405c03400d201040d04941401 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 352348129 1250 352346879 352346881
    0xf0816020d120f0c020109032d03050a12020412060b060d0e0c130203010807270c050a11010b060a0c110301050916140901090c0c05060c18040207081207090e 69
    0x3000d14509150311440b00790355440080d402d250701c10740710b202d4030b001c000c1d0018944141c2400000d00c41e00e110a03000000b03d8540134a05848a04110302e00d600759803c900080c1d0104480d030041e40c211483c0d0184081958040d8201820607401c14003044503c400a0301d84c0303480f040d680c11551150421a1410051144140600881161216650040101041d02810501d6810100c480551098905964008003d0000f00f07207000350008030702000c000c020721484a00354000c132075500703540b0503080c0b06405c030f4581c15110020001702809400742c000c8586856414405a882035941c1d40c400c0b245810001d0404074000cad5101d0500d20000701c00d50b0055130701503280009024480c113000407414015003200c0e034001070302503d40d0a1014602101002036406c40c0d01800180b1900c480c0ea004502c02d000d19140010080045031100d034075111081e2528004602c000400c00e584007180a00b03260114015202580703404001d540b01042c611030310380f064040d206d002010600c1203104040300710091105401008035 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 352349379 1250 352348129 352348133
    0x204080703140604081b0c0604030b070f0c0305031308130305070e0c1306080613110301082103040b090a080304061a091009020a14070c0302030c0d0f0816020d 70
    0xd10340d41800700b0340b00c095190920002c2c014000510600c80c9500022583c1441c11501d1003102048605016400c01d0103107200e5400682c0f1480098001980262901541410042400f0313247c1010140d455042105442101011075003003c1161380010903800c0500294040b810b0090181c003c42440c0340048036052400801c3c0000050010181c910204414040b40c4402610902038407501110b58000d42e66050700304a25400b400c06198005030152040311452200400e00044601e0b01201c00f0f1b0341c0c2030110042c81010780c200003c101c204840c5081400b07800c070320005142c01e070200a00c000c100103203007000a0321410b01440b02c2000c240c0d0281d01a030303c13800c1c14681403000e8407458005081007428109200f03440e1a0203070000d401120442d0145007400c1c10003914001035400000550207001c80f0261441c81155844010007100380510382e2802000e066104060510f10300e900400d115250313000141021410302d10001d410b19074440d040950707070328803100d54460141c03500da0003039401300e10380d814002 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 352350629 1250 352349379 352349383
    0x609050103030e0904050604020108060f1f0206010506070c120602120726060d1209080d0c05011d060106030207030e130e010501061b080705070b0a0f09060518060304030c0204020408 80
    0x1050701d200340c50392180e1001401c1480b0040100301c1d409010b95000c2e03030100d000765008d810426049076000d89101d0004029102080310b40034821728410881501035101802c05a05000c000e004d4042141d14500d40944c0341ca80d096401e005020340c0c11110310b10400381c0100001681220207250040c00e4150300d503d411030014203403c1c001c44c40c108155803100f000988001180b00f0740c42c8620700050100000b5651078540800d001200c001c54801d200c90804041500c0c04200700420140400e6500d00c00704a10700c0c9041401d4841c401103400e40d00460300072940c0000c01c00f280c5141554407503d40181c44400b1418102c48003000c86101c1b0360003da141c1078100c01140c0c290407288604400740021700071641c1c1c400040f20704240b04103400e94081d003100409000245110000d1001901480480300d0391a1a4112482e21f03500078050a00801c41c6100030841003900480040014a0203041c07541c10207102c81140c451014240c0c80440c070a080000000b02014002c0654a25664000d48115256a100e9030820707 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 352351879 1250 352350629 352350631
    0x71e0f0e010816030f0f020a03021e011805011b15021207020c0108090304120f050d02010b031005010303140309013c0b150309101a09010605030f0c0c10060905 70
    0x349030b400b5116038841c0900000b03d2800441354800111a0a8101600c034004600c0507550304070303844800c40d003000015964803050240d40760502c202e8210710045060024010002c00e01d40c1040c030005800007007003142c4e0402a41c8149440c0381640e00b03c24022840c0c43e2052a4100c0c40181d1000c1c40420034980020040781c0746841031256400316001c0d058400015a2402d00c102c035100155881000188110141325441e0100144651504404051660343d210b05102c0d0a400200c0141e540788058000d510301041540c5002c40801c00412170313941107480003010340c07810103609208004000007060300200c0960004210303544241c4481001004079222106950791100c200c4118500c030801c1c11540310f428462007900c044010729581a07031040009045060300001c5c50b88119026440c46441040c01d40d016600c0c04034074001c180c03c080c40681c010803101c940c06070001700410905000b04012111105009a044030b0403116454455441031802d502c1c144425010242d41410700d14000307103513240382d0416 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 352353129 1250 352351879 352351889
    0xf04150e07052101030b070c21050d0203190b0d030f03020a1214180d201c0806040f050c07060902041b02060f060402070804140604170c0a0602010b03071e0f0e01 71
    0x100c456071603c1c035045460402d80040a41442c52049a02076034110b08a40301d4020802713400c082d42880044103d010480c0c20441e0f0910711076071b9010f400021400d480c07107401d500340380459000d00109026200101003441480070303c02415800544214118011032608500c899040818052040480e13503c1c05807400980340c1a0a0350051129442c81070404120074104514550310b00d1690402d01c810200310b0031021070344540324040e200c0c0c581444103045010020000d401d0b210303159242400010300040340d6070012075507211440c007014802204e03545002c44444682101c004500344102d800014000c10b000074030f44044901c2c101d107081e00a5004258a0302c280816030303111842e03075241c40600c400e0744120140144140b00030442401012040c600b10600007a0143c01603083c02d84440c03c0351551072490740044507550160031204002d01c1c1540c035080141c400d91000344600861100401d507540ea03a4000c1780e040704d82044512009100c0403c0b1940105006021480c1055803187c010425402c28054 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 352354379 1250 352353129 352353143
    0x60902041401080c21010e0304030312090201090512010e06150f03010506030d11010605030102030a02040302031c0503220206120103021206071e0216060503060f04150e0705210103 79
    0x24000d00c1c2104400e218100e61202e8003600102c00e200081000d0020000346146641140ca1002803000c2d800340324424101042c0402143d07a1170660401800c0c0ea042d00c043c50007181d091445210050742e000d6070850441d0790603100024000c1ca83c60000d03014210810480c006032044401300f1518410354000d10796114001d0b1509616450b8072010304d82a140112641c0350103500034a552401140301d007400e40610761b1418000a00161138a00007801daa106541c1002d240d0b40100b024800c3d450140180d181c002130850400c140c8110394003002e440c6020062108601c0181c840d0710307100d90781c0b40802e10400c0e03541c02460303580d071103114000000c240d440a0005034007503900d80180503828800012581d004c0c50040e203400c0c1c584122451001c8078880d4000d5880110f000b034403c0454044c05c15440c0402504464584607183d00c1c0003403c1c488500c0710501020322440c14200421041110f020496003030718a0324180d14007590b1142002d40d11803258802c504140f403c410725041a100cac003844900e060b41d1180074 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 352355629 1250 352354379 352354391
    0x6090b070905030a08070311030408070803030609070509030c041112180106150c0f0623181b06160213150909030e0d150c0207050f01050c0d03050a02090a0306090204 73
    0x2c10300d5640d00b0042001044540c0402c940781c0440e002d4515580c0d00503000c2c2c1200d24080c0c4506c10341d400c4c402107520110481c0e03c00300030b01400d0b180403514039070300c24414070306241000108030009503103c0d110f00440d07005503915070300d100761042c00e03800300c480b20302030074820450a00b00b8558003032421001c020261074171f5280581c04034528800c2c00e074145280042e60741d28050200207481e401440b111214007104c045541e43c145800c101c0031041151090103808180c0c0c03171303030317203011422500c04190050981d486030f0025641c032a00307040803c054681d425400d840e441e44610141401410a1043c0e80c4060b51003c00204c0c298250040354100042c03821300560025103040e652011041603942e2804000e003c43c101400192041c24900350340034006000d041c101c0e410317020344440340c0708580380c0b40e00c000d0058200b020140b10500b0701c1a010b5010a80a192181c5030641d2407188a8442c21600d01c104109030312200851450521a0140c0b02e030502d000300440c00807a81c900d4102c005000301c84089000b241806 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 352356879 1250 352355629 352355639
    0xf0501050301080a08180d06020c1c090320151309091502030402031c0909050105060412080a02100c030c0e040b090606071e03030c12090812060d06090b0709 69
    0x10559040703e01101c000c01034500035039200402e982007034020104410103540c1840c00303544c40381100030149000e80f40060b500e1403449001c0d0300b040c00507200002e92200c10050a010365920101c548211b0b900115407651003814400400202c06c190420503078080068030340d4169200d489001041e00103425160000e200d5a0364089a040d00e919a6010b0f21314800544c2d580516105500150342c0588010290744610b8400d1181102c505000324080c000601907890034007800085104031409824111129400c052a2a0340f961031941c0c0e40d10010b01c0c021000c01c0322070b4058000c110034020000001c00c01d220001403800700600401d419204100000c500c4920b01143e800c1521400c2d1211700003030a1280c0e00e03a100ca0070f00446a20451003140e62100200410039076240310462120f08501c243d4000c80c200021117002080400ca110791008514a400b034500c0020f090740302110000d40b10200303550b00d40c0da512000502582c0600f03c014090f01c1c1030003240740411004003403d0b03204141c2911021001a260 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 352358129 1250 352356879 352356887
    0xf0607180602120a020f0601030c0911090d02040c0903141f0506030a03030b0d08070f03080601050c0304030b060f031b1f0203040b090402070206040f0602010c0806090708090f010606090f0501 84
    0x16200c0c120140c1c00c8482108070000c2e200e0f00500e2514000e00403030701610680385525180880c260310903070366002c100b1000e00003000d160150304202d500300c60344941802140400a40c00700d1131507030004d00c5640e03502c907c4014140108a89401135030094030030030101c900c40341015200c1400301c1c2445111900c540307200f0040c901a10030b560042d5800b400034115a48140d40c190000c003804201070303501505101059002074207480088c03c1407031003807541c4080910607190142c1740000c080c2ca40740c14000140903494000c9000415501203079084a8040400e849aa010803125008070702c0d07540d0140550141d0507210800c44040e502c0080003910250003080302d002e840d641a4100752290001078100b00410416a480b902c003a113176120b001000189415819400a881e0f170740b06a10035201d5135400b90007045030640a109080c000202410a402030746003550000e00310300f100070b280710180051440410000c0504010f2110707103031640e02c000c01840e5210b40018082402d684101d000b41d02814070007240799442 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 352359379 1250 352358129 352358177
    0x203040b060d0f0308190e0a021305060114130b03040602120c0f040b031503070303181a1204031809140c0a170a09060906061403070303051603020f0f0607 68
    0x820042d5110b40f100c0d139012902c40344040d00a120403803030104440c4851500b4450700b051440004020114064240306006041035025007141e00c00b40307407008118507070340c0041d1810000f1014070303051503885904c0c1c00c81e1402038040da00440235101c0048200b2003084219401004011000b5001c160a40d403041880780d418842d071400180360314002c0c0001c02c00030358030300c01840c0c1200c10108201282406c00021924041d80345d441900000d4000d040c001c1e14201040c8504040c0466114051400300b82e08203a13a05485540550b02c141d0040034001800c2c10f115100b003200b034503956104078001303507680c00e0640040c0c142c06801e801400032000c0400d03500c410b40005c40f10100c40703644400c85001310282210101850003420382a18548841919000030864802c2510907440b541c1c001400700d041500e50a000384002000a0081d4003c440500100390080141c0740075840e030031490aa484c0b52032404034180010400f1801c141d10030195070506a5001203034280c0704103182d50b00c85682d18541801c2c0804411 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 352360629 1250 352359379 352359383
    0x5060102030a05090a03080d02030403080a050106090605031f030c14220b01021c02010204140f0f040b04090c170607090f1a04031209080c0f03060105040923010203040b060d 76
    0x1208002d1544207a010310043e04514200800c10320b6883d03941d469030140c961104a141c0c0040768004100020140c0101c03200790814441c11040140c4d41c10b06002400c929541c0c004c9400b4440080002203040c100c40010040103051b00300000b0030241d0b24a040300b841e465501901c004159001c0c14000c15007001c038040d07804400302c011412243c29090104500405002c803041d411400303000311216590b254082410200003956000580e11440c02c19074805910201987c40d108144134a1048081e0b0386403c18002c003124201d40c0000c1030501040003600030040e002c1e006000c2084000300040c03104851400880a1020200340c51701e56450500031619811540119140c1100b5910705015521888004008040e05082007910741038880e29910204400750b40104001307455205e00b400700e031500f40314864008801f915040c001d5460800081d8445005000303143c00b4542e035460060134808100e00590390711044071540d464100740418914040d600807030741501c421380d2803404038100d420300626030351a107030b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 352361879 1250 352360629 352360633
    0x911010e06040b0705250305010b09010b070b09010605120102031024120b040203091b010207080c040e0304050409030801060e03070506370903051203090601170a0807030305090c0405060102 83
    0x241c104910200c4942040d80c045e03880d842a90300e60350b00c820280007900e000d0564005600040392035440c0c60786c00d407120704004034042c003034000c010040000d0303d8090b651500e0f80003c4910f040c0d96198642801000d9503071003190303ca001c0c3c3d11040301d403240660055010f5440001d1415070b06898003d580c061000342603100030014096078010312140d01c1420454074240c0c00031004201c1c448a000000c05a800c00d0f5032803136558100d01c1c0e5115400042c00100c110540081c00a00700c8a49800d4416407070301c80d44039025018648540c941c000c121803e00884010344001042008420224100288480d1007400303400045140b00042c4101454001201b204035072008225a18107005402c00325405e804002c01e49100440d0080b10704620b0741d800180b03580b015081c0c0e903441620740c0340d410168540700001e4258503a101007001441341410300810041c3c150b500070444c1036000c40e60050103511344043c042d40540f2030440030941c50304045d8950402030149004004071842e0700441c5081108540054030841d0141e = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 352363129 1250 352361879 352361887
    0xb0c0301050a050111120315030105090c010e010e010c05010c02030a1101060513020f0706090303020c1501290712031e0b0109050f0d06181a04030e0d11060703030911010e06 76
    0xd6224040f04000c903045d0030207558041c3c004403a032042c00e410a64007400400501e1000781c100e818244901940100300400804160341c030000060842e88501c0049810800315003030900599001d00706410200758010000c00400040c03000007505d81d00b000095100040340c8007620458820140a4981030310801002075071080071a68042c1c00a41c080c84954654840c18898900814691300c100c11040b4020707100540c0d07038103840f140c4506140010380b43c841a00000c00c0107000d40070f40c1e0034610030f010818841c1d04900d00960204000b850144002c018203d008043c407900c2c0095050304103058000c100542070785a0f0325009008801d680030f42040a0000b1200c440800292510b08021180301c44040c0103140e901c1003a4845400380d426640c2c0d15020002840f84500400080c20420350304405114888049810141d500919868010107a82d1042c01e00c40224002e210039000c140c80030341c82c010300c039640d111018600500604407402c0d042d03a40c1c1c141500d44290742d50040740020301c0550014951460 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 352364379 1250 352363129 352363139
    0x30c10080f134b0210020c03100c08010f0602100b1c1a010b070b07030b032b03110f1b03040b13030c060c112701120b0c0301050a 57
    0x500000070300316502080078510440c00b103015020b890f055454885100c641079000d80b105148400103140b80c5925104080d44480300403444441076402041e4120b034144181d504040040b0328240c524511260300d030181280c1031158a485a103c004c1028481d02d0b810003aa03079410048441c01c01c9846014056040307036062941035003043d1311031600303401c1c0204454a8801d10f0034980140420300344c03044902005000c0402005a5106001801050100f41440c9054030a5880540390080030700040c00703242c1ca6403001c0e19540d4007442486260051240c2120368104402c62040c130b140c0000c000c95011038a481e40c080c0144190030104c504c409151031101d45803a00f01429440d044038810a2001640828003010a00744881401444000c85000d03412806d00d0035400c1204482110340c1c0b00c2001c0c080903071425800101d02d1a503000c0042d004170380d1003038000345124180310460702421080d01c4001c0044004944814821150b0b14807a004101d148041d5880c03140e40f600c544801e000322035020310301c4401000 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 352365629 1250 352364379 352364401
    0x6022a0109111c0611040f120c1e0306020708031f060f12060f2402030304030806040b1f080a0b010e090402100908010f06090c031a091b0d0902030c1008 67
    0x1011a102c01d004160080d075a40b559005c464089030060341a82000800704044900140e80070b000d0010440b10a800104560703441181c0d000ca0702c240f5000840c0600b11051614201381e80c1d20040d80c204106555480d07042c94810040d506c2141c000c2003402164a00c1c035410030100040c00242e88090b2100b1045004a80081e6411800d4080c0c0498058441d000801ca40190900140007005055902414141e06c1107825080d2002980b445085620500801001c3703648468125003200007520b000401d01d0114000c00c0d8107000800040242c0c00b508913508103031540c03103100240b203034121000400c0004e030303540011110390140c0c1c6040c43d40070011401250152403d103c568903480094244050b446640d503200320309450042e01080700459556008101041090203440e2104071035217002c000d806141c44554141d00400358206011b1203181300001c000840c03d103800491341501003061603c400c0c12036140405486101c0e0200c3c001c0c0107019020195040ec61001010b100792525203000f280e4461121603 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 352366879 1250 352365629 352365649
    0x2411061b0d061203080f07091e03120c020f0d0201020309090a02070b010b0705060a050603030a030b04022101090b060309060a050a200a032406080a0906022a010911 72
    0x102514010044451440c200384920401821480c50f040320410040c00d000d0071140006103500c01710b10f0502c04000105900081ca44103581900700010407240d504450010b045a16820081c02800d0030414010701a0b040450060f0043c0b08a514a080403081d10030b0002000007014001e0150740b00740854603030b501d040c100807540901a80340060401002c1c0d11000d142078400e13030008110040014080c8140710080c44081d52080a21b0700038041410050301103030f40ca102d9154540b00b0141d413181e850303856540c0c40d012100c0d501c8440c40d4541c138489200700511900300081c031545840e5407030321007190343d0384c2004d1040e28822203451010340171664482040c0c0c0c014260003070a400d660b40e500c02c0c2d010458a000011426100c081d6020252513080c1000042c04581c0d0560f81000050740c0c03520486001d4040344004015a007141c540101d0640b150280b16001c0c2001c07500080075140003007454a0841da02000001d060700010040300c8000007003081c40c030700320303914000042d095000b00c103074005460800981b92 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 352368129 1250 352366879 352366921
    0x6180f0b1503031c05061923010e01090b0a1701060f020c03060903040611030706020a031d0105040503040b07140d030b090c0a0e09060d05010507020303010501020115050a0e060607050304241106 85
    0xb00902c1d084810b0780c19008051600072114113801c800c22315062041c4e9400483d0f0080084c2031101e00c5050b4840040c040301ca89108112500000142200d0040c0c41a8111700316484c08070804640c7d96140d41d0081c12441440c607030540144a20100c44180d440e0015500340a40c1048014614003424160304036070341d13405088118103a220800c4010005001e501c020310760310902e41e400141070b0f400c01c00004099441200350300c00580c180420700c00851008002c450450b02c1d25014a5036440c002d01d07016a071150515040c170482e0094185502e4041d4140d0455506c0a030111501190f51340c2d203140c01c4100b4000d81c00403400241640e01c6075400e40c10285251504414000c003080100e802940d101402d4a10440b02140181c0001c0010080e5580901403290f001e09040096080f250a000104e09090201e10410b1440741581d0045100c03070b1600c1d0116060140c006040d00c1d52a52640001c080558010f0401101c184541c2c1c0c540160350f226040c5880104001d070080d0100d44c581580780e0741d01d58440190 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 352369379 1250 352368129 352368139
    0x18010e01061b1401090605090102072f03070f09140f0610050c0a20150f0706090803100f0e0c0a0e010e131a12070306180f0b1503031c0506 61
    0xc1d54010811499043e8920554640041900d00040c5429420742d640074102c04981d070b00501c00c40c000114055032a10401c40d020691a2a147c00c402a210400004036a042d07094010420003007003443e0400003100643c0c003c800c040c840c0d41003a02c1000c40c9204200c0b841d40b0980c00003c040b50b0546002c4a032001c1007160341c40d20b1402c1c481983c6100e410085843e03000c84a14038075280e036141e6a60003007481000b01400b22440380a51081c0c240540f914030401e80f2192103a0310000d0207804100440c0c3c0b216a4541d040700340d4513140c1c68030340240c580898441c09070a200001d181000144000394078805481106e0207a150f90800c1c801c00340654000d140e103c480e40c1403045e460703062515038540c0d460f0000c1301d680c180f42c0800c415500c0c0200701d41049040441c4c44c000c1d07442d6400c1c00c02c1e0413800207012089951144001500c2d80b58044031080c006d820107002030188800003002024040c0701120140100e495840848500340c100c010196244140f1740010464902e04081003000c000940c001130340080003130f01d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 352370629 1250 352369379 352369427
    0x41b0303211e0c020c0301110a0806030f0708031c060506270909070603051311090703020f0703111912030b03100608030316090311040209010c02090403030b18010e0106 74
    0x1840d854420980442d040d0040c1d529080488020b80c10400e4010201050b4020040c02da40241d8281c81ca200d8110800f05002d054004030310151020018200101d4031401035440c40c0b9100c0c24100d40702e50011817151070410f8103102c0028013501d944100000c4070001080346191044000308812907c0071000921000b049402880c1220348880c54680d10a410410141002c1400c084014080b500e000d00500c800450410459000400e104441041282d04031001d0000755a00c61046019100d07408034080c80210100e03181e0700301500718682400c01214401901c3c2540d8001c0200c420410309640e0190200c604000c80d06207040c000c0d40107080c68440a800d235410154071200d00d00c00d5034029401148503510020420150b40b184100310542145285041c946c0c107451626120002d4507a0780030180700b2507000070702c1280c6a00600035200902d034041d19190300b134601424080c0040c001c1c0103a075402100c061001d41001c40c0790900c101e040c1c440b5071540300f00507402c003002102c1e400284080140c071013030085 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 352371879 1250 352370629 352370651
    0x916180e0a030816170109110c1902040501151409030106080304080604110d08040608060a0e0414010e0f0307120905150301080c06090306061005190206041b030321 72
    0x1200c84010345020f51954000381c140903080183e02e051000c0e07140300300f0418030000141c0360f280b070107940c2c1103880500000c50440c485111410702d40c461819001e955200306402410708888008145213524000c4608000aa03070316030540c0b0300d02007410074100c000350389484001c6900200c0001b601c4d0151001d000060010b880307910403895580306030440c6456902c2082004100a010021392586031401d5a0300d140142e1180c1ea100c48600990140c04240311802001031a0380d16640d0b01e0f80002c000c0c06e400343c00303e8181400c15400003002d0f040b21642075420b01e14014040341001900988070007201008500d032111035181d41d082c2c00e00b00b10700d030000c0141e07211001800e03030b0f5400d0a4001d402d0f203000519589500d41010180341c000f074060380344d02410b0180044041c6a8001c240168025001e54001c1040403581c0c81c01c490038401e9010320aa000160000011030030342c0010701900c614400c4403c032464924403032606081100503c402000150b05000103018400425036141c641e20714080080b650141c25 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 352373129 1250 352371879 352371883
    0xb030106050d12300e1011040e090114130501060605040609050d06020702061902330a0603140a020108010905270a0503040e16030903020c150702040e150916180e 71
    0x13100c04082d40d440f80c03801c003c00181130100c456640e41c0c8040c04c025103140e4440c5841d01d40154421000003450600000d072035510290041080e00542d034500741d03007624015080012841403020240c900f5860f040021504e58050003c940648030107442c1c07a035a19203071000b081540d12203c042103a40c41c0c0c00303011a000580315980541404003021103d909040034007200240b405120202c0f199403001d1900555a070a46030314003021414011034180324039030307541031100c2000e0040d80d80020024a2440b0302002d0180f00030031034000d80c600c00d0340c2d001500c3c2d9032181c00d0030540d41c1c140c40b99901d12011204c10301c5050701201d980088400024103031400d052458903040d003190030980c84081100c1413102040741201c900b41c0311030f00c281d015041c01c02610100c3c0e14001d60300ca0078510401e00442003e031814561860001c1a241c100703500510600010061810451300c400c51100c442c028030030a0404a000c41801240070341a2840341d180308402ca6240400500d56031008074200d865269903004a07810075501 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 352374379 1250 352373129 352373207
    0x37020d05030d1e0b01080a09211e08100605070516080303010302040e1623150a2303041209030b04060b09071b080a020715030b030106050d12 62
    0x81c2a4000f8800a01003c00c0e00141003440c0c2e4040d00e0707850100041c420781c1e04003041c90b4002c4040e09000400d40740c240b400400a010b0f02e078111160507030140c544002030303602006021601c0d510134652901c1c00303900b40080d0b5901c10140c070300410b001c00d402800d12031140320750058018540076004940c10003024921071411a074503174110034505c0d00004014419802c04c4c1c014240003010b600b0013800c289400d90200c0304004c40ea4040d204540713201584000b1030030f000c86101004148000c020f403d40c1c0103590801c0500381d0007c515580882c141d00c510341e41d120a030098000c0e503881031802051a594507551010091407042646006010a054011021800c1003128901c114424400018501d00c080200203000c01c00a2121081040c0441c2407040b41e0218003019071000e621918080e160218001c0c1031342800391030340114600c0d034007000c51000e0342d550542006040850030340081010030f41310024001d00ca04c400740090801c1c041c8602254001f4410000c80050040c1c16102030f84190785098100c0c40641 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 352375629 1250 352374379 352374397
    0xa03091712032e0605070f080d0c0e030105010602060603070e0a0906020c0102090102100621020402121003031115060d020d0209070c0606050405060109060c0c05040603031137020d0503 81
    0x64a10b201c100307440c2c3e581c0484501a0035441c02c05001e80c0c5000c1005240c1d1003160300040000743d0003040071003000b040209846034600901001d00c106403804800800b1a100d040c95113101c0d6081400002c4d8480c00407414034065040035000d40202c50400b80b41401d01007002d0540e40e8642c0e614800d00c8007060b141d2011b407610045450000d6a160304403400240341c0708030f402e24001824a000d81c2080800054880c8032000340c90b09184a0182c90035000085c028042c074204040036914002c1007104000c1d41160710700a40e4403030703280c00002c0705a50480744d03074420090105421030885040440c50b03d280482d071620645200030120910886c0d42c0d4042003400300b0035031b0b46801054070a6049420003001d0300134540a441d09881c10041c520300b00c000200704660030310841060000808040050183c4d502c564400f400b00a071080c00f01c03990340c1c0b500030310300900ca82c20b0f84c4070ba0040030004078070943c642c071510001c14421102510348412100c08502114800c0310100c0e0b0158030072240c074000810905c00340a0000c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 352376879 1250 352375629 352375651
    0x9070e0d03050409140c16030909020d0203240f09061309121b02060412031206060c021807090e070201020c070b0a02010c020a120804020a030b150109080a0309171203 73
    0x16141013540000d85514181e0b040603402e120042002c807612a00982e00355080060703e0100d40c17000c508090301c1400860b00301c1802180001640d0406510640003140a0ba00c1e522403800391124200d4401400010703c806642d00a6418010386458a01814207940201c001040b0424903802d03c40380004442104604460710246011000303510b0750004aa041406203510480000c0c20030fa0380062643e2184d8000c80c1e5155030398900340000c1c184218224a5a0030315018104012038503800013806043c82490124811410300502c0340d810111701c0c444502032080c42e11144883ea06141c104105154000c0983d81199070a00c800000c0010800441000381040f1052a96600ca400310003400d40e104020b540c0c056500c041451000502030309196440720320343c0d25064602c0d403204c2c400a619020303907600180c28460040d0a104002070343c00039840d02c0b6139090300d4840f4141d684100c201d4542ea03a14101078007249034070304100030b20040351101070880311044066555010440d40700c1c030f106802c2502c0c605140 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 352378129 1250 352376879 352376887
    0x170904020324030a0b0c250507050922030c02030c03150603060105030120030c040f1805060901061403090703022206140f040e010e0304061d12030909070e0d0305 71
    0x1c40b84091098403034142075018000070306007500d40981c68003010300400801140007a11000c400010503a45100f0130440c0511a220704035401c02550b01c03d43c602801e44203903031075000301d0300c0002250b194060200a441c00d4521030826501d040e43c62464425060381c15001c0c0c1c1c0211003a5507802d02c00892032a040301d41200b003a09210040c18944003058101a0003a03140c9580c00410614204283c0c003019640c503117070b5a0781d0b990021002102c0c05140d00c03101400481e00008117640c0b02c403035407030500340030101005c0145646040801031100c00c2881504d01103200404900d00303035203d4038015503200240b50111003241d80c0d60342c0803541c4200344250b070010b03030310005c0103541101c072850044c44010041c00b0500005000540006400d403400312034114819a500c045150383c00400f0741200d403242c1c401d107041c1d9460b166185e0740a0b190705d95200a0120300c04010200840c2498200102049400500010340c240f03840d80382440000b007000b801190070b000c0c0c070740481d0380941d9413803032000f400522a03502c003515 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 352379379 1250 352378129 352378171
    0xc070f080703110d050703020d0f08121f03030503060f180405032205030706050d09140d2d11070312020c130c080f1b181207060c1709040203 62
    0x3e800d05004141d840345002a0800020400c0000c111302501e070100d501d0f1003103600300d14110040403e401e0008000b00c1c1c0118071100d511086d0076140d4070030b0020b1200c2440301c1c002e415400c00440a103010040105005202080580c24170051103070420b100600110000c2e035010721982001801203608403000c1d40700040702100c0b04040c0c0c00b250030206844442048890a24001940710300441c000c0f076007080001300d0442080055900071111950304011302c408000c0c007102105449100d00b44904e40030914485800300d01742c649003400030300c0801d00e03007094841d00b01c00041203500040e2800650401e120705200440440d8a103070f2282000c620a40062009a40100501c001382381d04d4280020220303d0060031407250380d045041c0310760210004014458543c0c441301d400d9400600600b2078588108007080c00000380c00c0c901015020000200d5080721031a000c0302c995036451526006840014405039030807000920101590000c141040444504085001c0c0105049030400c4480000000b00c1c07260010b4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 352380629 1250 352379379 352379393
    0xb0a09080f0c01180807050103021c0507081b0705033f0105180103030522090e0c0a080c0a1806050405040f121e0813021002060f0a0204060c080c070f080703 69
    0xb03204c42d010031001c0c02c4185040703040ca459201034440e01c0c0c1850340004500280c24141750080300040c080300f004004d50304047d080241507542c01c40358001944030141c0503c141070b4150302990b141300d910000442c5801c40310a8040d850561240c0041100c5182c07172246100d942184d07603040450f180c40700c0940d49941c9040104580718078564500e4940350826801440440d5004040f600c2403d003031030400c003c5400a103c0c480b4004050360003280442d181c8508a108914040303203280181c00d0032a20045044d03210041a07841d01d007104c4007291f01100e1344004000e94248083c7d41140c2c030460303141c0012000c1d60340c008a001e82e50221000c039200c48000ba00c0508001a848102100d100d1615001c200184510f032002c0d07000c5500301124040c45402c50009481585060092860300c1d400b40c40305603c200c1d241c1019542301d80a071501c034940c0e40d04100040c00000c2520030360f0101e400a03940c80c2d200348442c0e01c986150340e00a01da08802c81c05a610042411213900c49500018a51140100042072460a09407 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 352381879 1250 352380629 352380647
    0x506060d0e0708060403050a020c0d120f11060108031b070e041e0b010b07020102011b081305101109030f0f07031218080c030c0301020909010306180b040b18030703090b0a09080f0c01 80
    0x544a0a2f9038a552004241c55207148254840740b800c2c02da107600f11001041d21b1006503d0440c0d1031611071680003040150000c00503280c581074a0300d040c001c040c4504141a1509103502074482d040c802a00000c002c00c85120f540f00c40c3d40c824a20103484081144c44284094009030820304500740005076074821541d09220f4622002d104040c41d0301c4100070520001c0140701c0c094a035103040303060740c0014801d000382448000980000410200258058440d10040940110031418401e01815282e2038000001140f481d022560000c00717042c2490455031030443c40d1155001240810a0880d40d8142c0c01041c1103a18000d0400300d0020013042000200b01444c000b1a203d51a000782d0040c400c040440e2903141c0d0850540303900c1040850415014076204c030540001d608040c1c030b104100360500007880350251865000e001d00d40500c110b80c0c01d0301c41c1003d42c0d0744030301c410040020300c016000700280c4c02020003400c0601c580c0d1030b00301c05c0c01366105400d80c98800d031481ca551641e00128172051440d038210044d1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 352383129 1250 352381879 352381903
    0xc0602030316030b010509090a05060913080a0c0303060302030d1e0e010504090c0302210f010902030402130f0e07061205070206070f14210406050601030506060d0e0708060403050a02 80
    0x3185146064040301042050000307105052544514071300015078060000c1d100c5801c0d0103080740b2031a15001c01d0500150405643d081e01410b4440081414080811001c10016401840140c034040342e1407400c07610040200402c1e410965a0100400181e80502544100009980c0d450154120000c0150b18001c10440ea14003030040b6910980c01d42d907004070a40b01254a50f1000080480b035880081c1e02a11400084031511201205184005508880914000c103803407040654540c2c0ca40310100f0407488196006944030503200380c1e0320031522483d044010040c0c0044400710780000e03000740746407030480130f0303002800824001100d4410480b030070320582c1d6001520b8030082c1601d081000c1d02510307050110f00701400b0429106640d2440031590011a40f1400d032040c0c1c103100c1116100c10012101c1400d540889900342003001040166200e405200d0240f03c0007449a458100004200c01c024107000d803c0c0d0320a8010008005045401880100d00c500c0c001e4171441e40d9542c2142c0c000781403449100300 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 352384379 1250 352383129 352383133
    0xa23130b0307140301020c06010803130603140f090a02040e0114130c0302120102040b1803100603230c1002150c12161107170706081b0a1215030c0602 66
    0x102044960340001e021003110825542448401c0f00e042c046406031041c070b038121b065032086100001d00000000700424800807441903544c1c14586a40003207007942c55151081c9010080c80b008541c03c0601d4031815a0001c440008445134411190301207410368003982000c0b6110796580700c103400035168a0440039406260725110500c0001240c0da0030020410900010b80140d407103401c0242c0504095041740c0c080d00640058684810300040840c02801c0d0040d442c81c000c2c014260f401c1c10b00307290ba0007084103030382d848001c800f41d540c4d00c906000d80f000030b04011003215201c0e0146515503925005484040c50f00a46d01510000c0e071018030100224401502ca281724000810900202c4500008982c2d00700e804104600450b005096044641c1c01ca00490704540b070142d1040010502d100090240195003503d0644081e69500c0f101640d840030100c0d10200d8614201181c0a1003014010007801c0f030605a00b400307802c11111065440c1110360191002e4101c1103480004d00a00030300c07071200310040a403440 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 352385629 1250 352384379 352384391
    0x2100e01030b0301110a08060a1208040501120c02120c1501030606091803020a0803071403090d080c042402031e072d111216090e07050907050304020a2313 68
    0x40000715031061022030410491f100001c14005e50381e03486544010f28843c82d008200c0002410a10201e5000e44107040c0890310083c00f04889001d0f80c020106490301d6900030301400510035030721070120781c800d200e581118002c0200c0b0b003510740e1900107100c2c041c40c003d102c001401c50a01c42a0011102da10701e150000f520504ca100000076400600354420940c0500c1d410b880c0d07100c4520a0f210003d250109070240b80780031041000000c400103004203080300641d110507040d112154010310520550040102005d1090144500f8480d0070840c24141c0c66540b04503894411401000e82400000440001404e00c0002c0c291062101c40920141d001a40c0050f00b006c00c0004c000f602c5001c0710030400105003805050302d980d2561b5801d442c01c000c5a218400f65211103103204815007090425010301810f280c40d20307040340b21030300c40007a607141a220090803443d4551694001a519500000c7c81241e00c0380100d00086211030b0390740c07101103411999110403400b107072490081000c1120b869031360800b0f040c9081 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 352386879 1250 352385629 352385651
    0x30403060e01020415030908040e1f21020d14031314011d0d0c030b1003030215040c170c060a030506040507081b0a030e0d090e0907180b0d02100e01030b0301 69
    0x5c0f809001d002130340c0c100010903030b28a25014086000c1e07603000000e15200d500410032408a80d46c845504030040f4250b6104180d1900010b412b454441c1ca01100540c101408020042c10b2489800161600a01304082d09241a143d0240345a0110220f03407120603482008002c0349440c001c04c0b06100e042401c104500d4045801ca4a090380c00161100f481010810118802d214194501d080591f8200c5540450341c9130414040a82c150b8a20080300144940d003451640382c18085001405541d2021210000c5882c018010aa0b07141000d4540207074090000102103d03600c0000410b034201b501d80300231a541c41c10404001c1200c3c0000c003807005103c82c0c003041103448013030a000303540c0c0c5c14612144140c5074120390704210000d01c03886850743c11030301c074126041941c0c6810440c100111900f4021001c1103945a000780c03500c8100c0c52241c00500c444800641040c054160007001c801c4501510282068105400050000b005400304a01080341500400015640f5002e1907103215820741c000e0000d40151 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 352388129 1250 352386879 352386899
    0x30e011e020c0f0d02040c03020c070f140f1906210903120519020c060f4f11030d050c073819030501120b04030306080708030403060e010204 62
    0x802c01c0540300e84003580e5049181e13075580c8203034042c15402620401c5801c4006102a0003513102c1c00f8000b525121700040090141582520a030585440c9c50041804040d420248480441603c98071a4004c100d4442c0400d89040c0c100401d000f450b1070760f6041c0b140100032004100c8001c03181c0b05032181909203080003000c26007004a900d0396240b01c80d4002050303682c589014003d04070b2180c20440250000868040c0614002580703400350998846280044e112a0003103505288a015140017403a64203c11292642e036503566040364002201d000310035407001400c0c000c05200318120848000c405405020709030708040000d920000000c0c01d1544c034003402d052485680e03c0b00e40c0308124030900580c220070360300c0c2844a852081404030141d500700c4640082d4007a00e20350010414a01005030140010702c1e418800d0041504031034090b00f0880380c00205071200400358000420036014152250400030741c8003810401d000041c408080610b031109e08514109099841f0300c1404e4050340c0c0140420301400c920 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 352389379 1250 352388129 352388143
    0x20303071202090a06090f1215020c1519110c07031502130f1508040b040803041407120309091a100e0d080702010305130b0105010c020607050109030e011e02 69
    0x918240000c040c0580144007000c0d128010074650032085185000031070680000c4400c0a48046101080c0099116420310440581d40080685018903c800c070580f850f01030f9009100014015003039071203245010346c0300d0f00420420388034a00c034034104140c2480000034520403502a000d81d20115407414055861543d0b4900c003900000d400340c00c0c141f00d0030740041c41c10350445400c0c0402600c2c042000ea682d61240c000f0100d144140d00400603c0210003402e540305030001c03481aa80302c0f85030740b604d0310b9913101c030365041d00000c000f01c541e0803800c0141c0032503000410001c0001e14206041d0100003c072842e005050001c0342e4090300c0070609001c0d589000090410202d6092407058501d90002480d04000704c86200c0a403a07141d800bc6031010500302442109001800c07002d0007a01d00b4042e03504e500800141901940c600134000c0c0d809203005110541c4a1142400190b00082c0200c1c02c204c60761300c1d071900b1a01d45a00031000309000207196152942c00c9030040d040228514250200c000642c40d020f500d50030 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 352390629 1250 352389379 352389391
    0x606040b0108270601080d090b0301050a0b070f0f2001020318040c120e0c04061e0312050c03210c070506060906010c0b0916091a0405090c091609060f020303 69
    0xf22072481844803204240456058203500100c90315941d4a924454640001040e110300042d02c00301c01140081032002124101c91001d06941c40140c03403d120010590030640381121030400c110039200224286900d44941140242c040c52070fc24800c58500c40c0612042c01c0d03180c195001070010500c00307040142c070901c1c200030076580440c5c100d044c5841250181c00e00325035403158030725001030768190100005a03a01300040585082051070717202d0500080390f001400040c240703800210390600003c6d010070703035200d49916281005070410440491090858000300740081003581944601b0340c15007800c81d0351079000180003140e146017803c0741c3c442a03282c907001001d40d805160140c02091f034613442040c90901554203d50b0000b1107041c0035910759160030810700d20b030324014105100440c14202c1071003442c55003182d00710004040c1a540007444003515004000341c8890140030242c030401d44446500c503215106c08a800700c03040101400180c0000750580003801042018925181d0070790300001142c1c0c1000d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 352391879 1250 352390629 352390651
    0x810031e03020f0d050304020102010b0a03080a180504020c06041b0e0a114b0409050406090602040e040b0a0204050a05040203060f19050411090102030a0c031205010303110606040b0108 81
    0x2462030700303041c0e00e06500e9100710f003040c2c0b041120400c0b000e90711002660256100741e009121600808080168240c0c140c08050610542001010001801045aa07048e03c1c0981e50020140d95142c00150480c2c0241c40d01c0c921541101c0c04200801001e8240d42d1202480c554620040038141700c0a0154548000c003401070950380c440210b04140070700c90550b121031400c0c981c82442c1100d40ca196050790700d580000c0e0b401183c81c400303000c2d194004840d0000c04c3c141c1d060780c10074145850503641d007020b808003130400e85900b07680e1f9102c0c00c0400d0050000348080c000e49103500456080c1032411084210b4000c2c69064454818042841240d0741d0720b038020229042200e0260712a01c82d00005100018110061548040d2840c034070341201380b1500c800400c03103004442c01c021845441510009501c90011002e0060b0420803251081600414902c078109020703107015000d41001c400c0c40c2e4200c3d8001c0e0070540204c2e60381c20120504240c1081381ca40d0041069805002031402240042c1034004080d000000030 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 352393129 1250 352391879 352391933
    0x1050913080d0f020d0f23070c1403070311060c090d020f0f1806030d09050a05010c031202030702010603110f010e0609150403080c07081501031709030a03030c081003 73
    0x700c42d141d0000000b0b28085001159202c80b002100c1c402046e0300e0f5042c4400300e00b84000c11110003841c6c5181203003500a02c2508400b40d85440e0101c81c0084194402c84070740710740007000480400200007820046200792506000b00e401f100c14030b03107001401042c400c003141c42000705002d01c1d26010a14000070754151403200120700e007540065101c0321803012103038100d00b01c0045081c0324203650a03041d0140700e0580950303c50800600048407010464010607411201007032040103154403944050103000e00900e08200000c0190307200304140d80c020f50706000182c0d11803100303000740128a564214004000c84225001c0300d0f010001801591280c403c0d030740b01d40000700fa142c40f035440d030824450385215004041030381da40d00ca185c09810354110260781082032080c2c00c40403815040000345c0460303880c002544205607138070703550300c2d1844c411a00f0b800c042614424000e00109450800906031202d10a1320301050400a5040050031010010511203903000c8204003040418a03500d01e003803e505020300d9803010 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 352394379 1250 352393129 352393147
    0x403080d060909060f0501050a03020a120f1203061a0406020c09040314120f0109020301080604060902010201141e09070b0a03020702180709030b0631091203060e0105091308 76
    0x20a282e5000340c2141c0e0602122908000480d801600001d640391410082e90340c803134040c018460128040207400001d40f450500080d581e403a004000d451160711480340070304440e40c59000c50040300d158000441e40390281807044520004a090109040c1c628039402d00745032100095071115000a213501445410011800303240c804d80d2200c0e045282605041e548003808142a09a00d80c210384103451a070307407070f00003088211079402102d040701c44d80c034028041500d9548410001345243e110803410f644d84c0c0d4440c00b25842006480300e00c0f07014907558406024004203800150304000500806040e08010740520001c0061016505403041e02e10303005850324140e10125140d800002641c406108601040210a580c440d02500a59120b40c80070b01054075140144a0105504600c0b603601d507060041000200c07050b0383d8041300030344244802040c1d90046071a9003122030a01d00010b00000d0b1100c0d824803409000340b00c03040c0108001d942040c6149043c03201c002c00075503900c0c00100540000119001 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 352395629 1250 352394379 352394381
    0x20d0308040c0308040b130801020a0905061b06010e070f020a0512090a0308040b030106180e0414030d0f020307020c03070e07183f020108041203020c0a060228050403080d 75
    0x80510342c818030132030351542c6a14641c2d105400072103110407245003442c0041420a418000d490b80b0b03040e2519602c4540b03080100f0824190403254141c006600c110f690304180d003400300b203100c0c001e00002c00d5484032070820100081100d01804a0f040941d44030703000480c002080043e5054038500ca1007101c90b181c455107800141260304a03440603107605004100407614145407801141200c00c20380701c0d0054a982020f0f02606154a84102c81010f10942c000801080044015401261f40181a6480c01d0411558001124081d44040c080d4941c003204002005030104010007000b40700701d000340305e418902100b0700350b1034070020405001c12200b0715140031450f031102080006810341e0903480143c05106000310f072032204080042140800c1d001c0070220440040c0034107540c10b46d01a0743d035945a5a1303540b50350030141850700c40c20082540c204041d5508082c1800240d6581e03101c0d40b030142ea16804c1c0a684841b2582c21101c1741c000801c4600d018030b1464201e400c030303007c8a500c03490072511503240d1001a4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 352396879 1250 352395629 352395653
    0x412080612030324030f0c06030601050c0607030603150605152503111203060319020a08011e0e030906181f170c030105180a0f060b0d1404020d030804 66
    0x180701d220103c14030a002c20403140310060f1000300c20441c2c500403a003004066840d1707140c110507022070f0041c0e0783c09411420410011a84070b01d060505030700d02490440d5140c50918202d6042e0006a903c24060007000680c143c640d02005c0000e206103e2b0508010000780d54141800300c2e80d505590019200058510880680704000700c88074545403229414140507041307408400c04901c0070700483c04040110401e8200360f9018100c060010315035000480150020600035800503a4440c811910010b9484424000c0e040101d5014000704000e410b0080c1100135074002810925954005108028540d00c0b01016610b0640414510710300d880d1955020403d0034980c06040b004003a1560211006690004100303811000340c04486107041d5075142410300035020a00072154802c0054a00d40080c201c13030510140c0041000d180000c00c03d0700c9102040482e0010742c0304220f811000310705902c89a2291240d112881c0f9007103240745442c5480ea0000e42c0d03600499800505004185c0085018404441c402c9 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 352398129 1250 352396879 352396909
    0x21c1e0815060a020d08070201090308011806030c0603020706061403120d0902091302130e0607030c022505030607080c0f0d090b0c0306040b030c21100f061d04120806 73
    0x260f03444080420003901c9121401410011604240200d0307080c920500c6050720f0190981d9131411140d081a960001e80000341000b404603549407940440450100c8a2050003842c107900d0041c1c6e80d000340e140250070313100998080410468182447c400325240428000c1c5a103410b2400130765980a0a40080d00070403071148060740000d01c200411201d802e40c1e2000141160089440302c4e04698814006801d030b460070f17801c112060308500c001c1200c1c0c0d4001c1d003101c90121601e0040d5003d0100c104c590640c0410411000300c01842455410803480c1810300c0b940d6000074142c5000301561805000210044c0f0801c1c0b0034501c2c143e0009407800122001303a000020a940c00607801c0e40c0360410400211040d0820780308644140e04d003082c02c00c2d50f0700d400104140308240240505a0b900541051450b08904843c2c0b44501e9018040c0700041450461003001d29070011640300081e0a410130b1740714150300d41b1604010901161368401e0101260440034441c44100c1d540c0740c0544203913286004100c01e0030350419a = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 352399379 1250 352398129 352398139
    0x40b03150903070308060306100303051c150905010806010e160c0f060e060703062d1a0703030605151c0221041406130b04080f0a021c1e0815 62
    0x1442035001c0040000d00c1e02ea4040e40d00d908a0f80c0b28101016160304050b120610881c14610b4100000781c00ba501030030045000b4800d50011841d540d1040043d03a10405058410002c0d14100340003060072442403a002d0300b0500c0c02070007550b04000b940c801f0780c4c2000d4214440808034015501c0c10324410040030341d0840e4484014203046201303142c00c401501d6440c0050220380902070010f002d5602ca2b00ca000e04a03101c51651083c09100180d41c0d07006c482407098454480c007415000032822071840511080c41ca03442a06055039010142402400c8070b8043d040317144100020400310343c1c4100c41100351000800021070401d00c80314a0b0032188000c0c400e02c405851040c40750340d0f80c0221070746051003803032081d0b00032400000e0f80c0442031403c03603c1c0d5008480500040e0300c41c03003000011501078421243c2c05031082e01e03810324280340c0c1e0b2895401a00b0041c180d41c0180e00c4001000c08064034145d44041070001401e0480c482d0380501e1000c01e5011001e402101007203410707800150303403004c0c02036480102d2070007902c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 352400629 1250 352399379 352399381
    0x50a170304150c230a0f02040608010c080702012306120120040614030106051207020f1e190302060a0b0613090204032303070b0711250503070311040b0315 68
    0x1c09040815003c10641d5016003082c0c164801c5000c66000040310403600015007a1720b00156030b194009110f13000140d0f00507646040100e0300f894244030340304a40c1d1503500c1e1411a0b15003840020309503010300314010000c070700d00c00d442c0c42c24441244051760803200c1103542c2c40f81300c000544098010040c0c2881c000640003950302d610451420000140141c80a0380d440d035514800c01c1c1344000040c8403e100f050002541088842803000b42025101e40040c210300c1035802180001000901c8e041c142800100700c0300c4244100c0c0030001080128403841000c845c0b10f016411242c1d24003070745541c1d00401d04140030f40c0b0f40085c0d110541e100c6048a01c1d02681d88a61008652150b100c60300a42107404111048803000304c03088858454000020000f00000d4015031501e00703aa5143d402508000d42483c0c0be006092101d0300e0070003000c3c840501c03170401e0b00007040450300d409031603481104107607807203640240c10001050011503510950140c0e8500140e402003002c20b038040c007182c60003000c1c149001d031480c000e00c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 352401879 1250 352400629 352400669
    0x304050c10080105190f03110a090f0203160c020f0f03070e0c03040b0708091207110405042001110312090f0a03020609122701120e1510050a170304 65
    0x400c050584000745c03100000b034200000a10200c100c035000d6103c100b10054401c10018058400816010344042d140900140e520140c0c01c2c05e4950540ca2030007241d40110822180f101012024844540b840c58403090903895a00030410300001c42c5421030244909001490b40c43d20300700b001800601d218000c203155490701d1303511034143c0d400542d001c907a42100b00021400e01481280f62900859041018114a40454880e4400c90380001801c541e030305042c03000001030799214422140302c2c0c5d0060130300402c185c0205030312010080105400358144100d40c00d00641e003200c000240d60817144622810303030386512082d50052824130480d402154522404104600309680425464022410102154130700011200541d560b40601c2941a0421000d22000d05081080c4040e5801c00c8006046c43c3c441c0e11860006e000c1518500004105d9541c0310800c002081c01421310303941d07031144941403115941c07404d01c0c2c00514085030a1141006000300c900c812000c050702801210024190481c86014540d010 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 352403129 1250 352401879 352401887
    0x1503030d0f0509070305100509011401140f10090e22050d230304110d02030706030204030b1b160501140a0606020c04110912010f11120901140604020304050c10 70
    0x74100840c0c10480442c100740c10001d0044252544175018088060135031450400900004052296543d221400d1001c121200300907240600042c0d03050f18030b030080070018000c90000f117641d903034001c0103080d10f0303062074a5110a41401303035950001d91003042d864030742c9240400608410700d00d441001410041d01049000240e921011455850b1003900415080031150700b003508110307a90165a0400004000a03003000c0700700703c50a4010441c981c0141c068001c603181801ca6000100844c0e40002d05200380102142d034503034404400003a0090f10302d06840303020b040d0b003e5282644400c20b41c407400081042070a400505802d40242c1e03041c90030b89480e0341c142c8050480d80c480d0001500941600f031040d810305020710f102441d510359801c0d00d445030542c10b0000c5004141c2000701c903035583c0c003d100d40c042c507039004100c4403d4500742c0180d110311f5920300c1100400c0b4003a29880f100da150001145060707401002c030540c0040308490040c1c490365035042407814100c2042880c0e80c0305012927a07001c0f8461300 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 352404379 1250 352403129 352403141
    0x90d080313150b0d0206070f0507080619020c0a06090804090905010b0f06091e030c03160f0602030a081303050f071a0a02070302190303020c0706083301081503030d 72
    0x4000e81c01c2206042c2c0384402c2100c00080301590040c046024940150a01000070700403a80b01c3c0d0640380e81000d040d04d07a141000c1c0325411014564004800317010110b200d45c0021f92400b11200303411032401204010311039903a1280440145410b0701d0b81540070a0240c0e0030281c60080514110a000780009454028003c042c940d0400d0310032a00e201e15011241001829101c01040290440b00210500c1c3c518410604040c102c05516100303031406071060740c82c04e120300300742030f64400c0d070012074541019040c140c95561508007800b10744c004c0c044884038a610514542d003044000c0c0340c0c00f080c80414201100c491085914554141c100041c070f100800040000101d5400c00d0071301ca06003591141900d40003a0300c1108005030050740211022070a0035025002400c645219040061030500180000e03810039845a10101c08076442800704091101089203c1c08109602c0e200070041c0c40c3d014020b201c0869003c0c0100781001092000240c40822080c070b108009440102100d0f150344a941580b005443c07 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 352405629 1250 352404379 352404383
    0x201020a080f060607020909030418090203010516080103030e0112060806091006080304030b06030f06040321060605040b09120313060e0604030804050907020106050916020d0e0f06090d080313 84
    0x400980010380e4002d155408030301601c00140164070f0010743d42c0801001c1d10b00540001d4060004000010301c4414000303100188000746500800c01d032125004260845000900800e09120307002c615400c61036010700014150781d45030500c400c2980403400100c600d40e14240310788006904c1c010f4041150180012918070070000700c0103c66600c0c0c0030015800076507983c0e201e50710b40c55005000c01e01c001803041101d582e0080740030f012140c081001a503818075003841550141d000c40c000c4d42007200c0c4015010001181c1d4460403405001c42458180011300d00d1041e8860007202e42c0e00802d502d0307400c2d075484028129142070304003203c0d2100c01c4603200e261032804611030940490b694071104105410f004095500326030304000c5560070103150909101600d01e00500c1071085550f2004040307502d50300c98200c3c41c040c08080d9030701c06c2e8203c042e44010b49080b14200c50101803003018480d11080d551500d00320b107001d850a451071600e4445000124034600d60300c0000800d0900e01000300325400000d850100c8100d8 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 352406879 1250 352405629 352405637
    0x302030a061d1b0f040b040515090f0415050c0d060e0726042a030804060807110705011413081018050703170f18010206061e04050a0e0d0201020a 64
    0x100040c1642943d40d099030304030611101200b501d44529142200e980000100003070408074200300c0700c10002c0c00300c50301183c0e4140302d13508420289025082c5400c0a50f4000c00112100c21641170035180c00f903210704030014100c14162200c0005000d045088140c0300d440c0458a41405104d0320341641e0703c02101c003125000c1c00620118035529100c1844400070104c0c40e00f00c1c0b500070307064460307031581883c00524000310001412501c0d0b0b29040c68014099110003140038500ba10380b02d900300040213010020241002c0b040004103451312032101d10200d4000101d5a003424181c400210100004003d40681000c040d000c202c54007000614070f0b40401c48099035922032208100c2e41c04000c1d89002181030139103028040da40107400920018000ca05020300030314110707000c0382c144030502c0f40000c0c0c60342c0800d08486441010701e141c0007165030104030850308520112040e00006420a400d52690070b049072626124507210404120384c1100c40d800803458807030742020365000d0505003030b020b07020b50301005044c4001 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 352408129 1250 352406879 352406921
    0x108010c050703170c070c0305060f0f0103020f120c060412170319050601021c0c02010311030105101d0901030c0f0e070507030f030b060417060f04020603040b040c0302030a06 77
    0x14612a0003114946030341900c0d102c4250392070301136911580320000d20b14003140c2420030940c40850012001c200045204400801d02883d040d038038640c450300302401c0030000b450705a00620041e07981c01c198000310312058a44d03000c80c01c0c0c001c52561600b41e00c0c4c90469000400040c0101d441c0c54040b0b803400019020b04800e20b044403100310b00c108a484115030f00201c0489004541c40d661000f074104a0b0000d905104851803040080c030036102c40041409010085182100400115601402180808400541887d0556260401040007032048256040400103007203414480c0c0c2013801c480c4545008003034910a00c40d0b849180003001c0780900d0045111440c40c0c0200011a010361041c1d00b44104501d81d2030030b0a0564654040c3d5a29000796281000c1c50b0311141408920b0329003401510003031a0703180030003020700c0303907502d60a0400c880501601705c04078203942004090b888580850342c0182e408207000d00c0da0343c0c541c20700c01090f038541d4000030b50601491880c030080c0016900021204001118a0280 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 352409379 1250 352408129 352408151
    0x14030c07050618010f0908070603050f07020a0c151806030605210a0f050a14031b030412020108060a090e011b08280f020d060306110307300212010801 66
    0x31030300500e40c029429520f440320030001540b1400f003691a02d41c482c204254100d0700d4410b03041c1041219081140029601c608000640c07540f400b440350844443c1c00640b82040c202e40703d034003d000150040c4009c140d031070185101c81c140709546900600c052592040c9034161501002005480c4a114051059041c500b041160014a80c0e40d601c034100144000c0c040e5000e41d0355154a0f00030b0945e01520300d80180441440411113281c640704803004200051941c840d03800d490103880610000c11611a9401031000b809102c0c01d81c0c2d02d100d0b0058090900c2452a62004009441002645c0041d009181080e00b520440b16054200c8070743c40c140440d0903036a0010120040300c80030402c40307105151f2007030410040e0300d0102140480201c0740c00103002203410343c02c4612000030781e40010a4094000d95400c801c100307101a501c40e1011514070103070040e1039800c000710000c08034001c0c11240803220301c0c2005907003002e50400d515003840c040e2502081d512030b581c0c80300803d0050400d208290b4203500b0840b0758a0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 352410629 1250 352409379 352409389
    0x20a032d0203132001090b1602090703110d0b121b0904050f03270609300a0b040b09010b0a1a1e07140304180203040f0b010e090f0109020d080306040914030c0705 71
    0x40410884540350f0745000480c9c00704a2011009000034051680e103190310760134440306800400c5814203240021505800403030502070442c13000c1c055240d0681044058035603081710380e00a4880d0020850705640c4a8640781086170401e4036a49028485100014407007003400d011091400030714240f02c5160a83d45c110100348002c0d840780054642d442254400e102c503544003000085100944580b155000da10300b034501d400d19250b25403c098400c40b8018041004001100a600d940004014001d004da503400f540440e540207a02e01448418662074044140180b59440a503120070184051292446180e8049140541d04c0f041c4243c601100131031035040c68240010440d801c540030302081400015050011400940011b4030440c2c040091604a03000702d080d0052036030203454441507494681c00c0103011783d4503000141711f0000850b41400030305070151752090201c0d0318080d040b203019943d90307481d01c0000b002481401d01c01408501d03450031446001d440000070780314a02043c01112072007a12002042 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 352411879 1250 352410629 352410637
    0x316091517100b0f0a0905070c050d0e040b10020d0c05100501090609140c040501050702040f050a02120a050702071a0903060c040503070602031c090804090f020a032d0203132001090b 80
    0x1d402510441703040002c0b94895005130350260b03071403622070080f6110340e50703240c10115019240c00004111b0030084640e0b10740f0784125104c1c020100c909501040c0902c1c1c02a4440294600203010300c0484840c2905000c01803061081c4800c0801e4100030135a11030f619100240424050044003919100d070212300c00041c44001405054803d03800b504041c501001160146d2002804030b23002900c0741510060500350b07006482c007030140c40101603101c0c03883c440700c13014044004100d242001e040c907050006840d00854014192a44182e40900141041805101c0f80c801d0310003c0e40c05100d0720382084007c02c8400c1c080c00c151003080781510748103540d80d40c003265a40144000407a01c584280342c40e40c510056503002c8490340c0c0c4900001410030307640c0c464000c12508800001c1481c1c5d6000158940402c6e4544202c01d4085103160014500ca00c45281540034001c0d812000407826900002186e884107a011800c0005071344142c507902c50400301c61596a5090410f82141e000c43e03003144004c42c8041c5d901c420f1b2 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 352413129 1250 352411879 352411909
    0x609040c0504110d020c060a050c0703080403050d02041d0403021e03031501020106030206040303090302041103010e0f0403031814061803250807200316091517100b 72
    0xc0656903041404001c01000c00c80b22480021000308208803062102d030001e8a541003140020301101e02d048288003050b1407006018190440d400c01c040307800240c0040c01c031a003068041c90030589030a0384140d540000d10464100c0c181c0403e800d41003009440c88000010b1281d88070360b0a8910f01c004589003c11411140401c99016030030a00c00104841c44260301d0a040040510011903140d076243c011590b19486134000f5000124800c00030300643c03c02e8000e00303130740405240540386198541801c40000c03000c05412194a080143c0c086401e00d80b0a070420b1070f0140c540000210300344160314210042e1001e80a02140e140034250018051508401403000d6060000c0080c51a22502d44420800344011180d040261040310b0342c00004903215001612400380f048a240b40e2010305034000104400d00148101d20075408001260170407400710712024100c07114100e001c00d0106400d0708140ea00d05580d04030880410b1240310404440100040c02c001e498824042088200d440d00140a100311240d649 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 352414379 1250 352413129 352413143
    0x15090109091101021c140f16140604030c031112040b090f0901050a03020909010e03030117010e0624040b040c02061e13110f040c020d1205010f0303141903060e060904 73
    0x45030b61958003801041100d80340000d1551f19000181c988141d15401803010417501d40c00c0c0c005030038108110301c1c50b030110b000c00740001480e40b4500399034002d003a036014180040c2040400b09000b211b4540070401c4848020031489e116484540f01c0d1003015140d005004002d1140c041803043c04018180b8108582c141c0e240504000c22080c00d603002d21071f414402034030550ad55942c442551240500034000381d4003038a905412080c5a401002405094507660051505a03800072000e102d440741c2c48041c6a00c2150450705601d200681702c000040040401d408580d41050411184210b003a0b40803038494460384440359889190b441fa0041c001642c04e040700e1850100c1244641e950100c2c032547d01d0240d40302001401c0340750429000f000704e401e48415041d0380380540d1001c0d42031480c45810000284034a090301d4401c024030361601441402c031100a100c00790901188a071280f2006408504940207050517074100a603020030f081000b002080035118042d040c1c0381141c0464058604200720600560308448 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 352415629 1250 352414379 352414423
    0x1b0a031d04020c060a110d060605070204140603100e190804030b07020d02030a080a110705010f0f090201090b09031e0706260f0c0c0a06020306040c03060302100302031509010909110102 81
    0x2603000c001b00058100603604d14410b10801410503240d01821010b04079950390750391205824030610003510400da070300c42c50404805040103200e480009006484c22090013010603450020742002d0304007400010300ca9500200321080105106600300100300302ca00c10000c1c1c11071652403030070403038907010301c030700140016001042480d042910130f8601c150000c2002a00148803c03404d0094481540404d05c100d89994441c0d0b40403155403224440c00c0241036801d042482400700d19030000301008000c1c058231203000700c04603a6406984041000c1e0140042110200000c9850200c50983e0782446102e078000041c00c4002343c4203005030105100349214910b4030321121685943c410800060401880014082c005002c6102ea20000f0803041104178050140182e503401c0a10501041d0b44450305030301c3c14103042c0a0200010381b40c0c80c41411401f40c20381360042e1a80c0705c03c0a4607600c1e0304000c03400b9034441420703400400d00400ca41d20004c092031250790326a28152401006986509455402104c0741000032 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 352416879 1250 352415629 352415641
    0x8030304060b190602010c0314010b07020105030405160b0c0733170c0403051c0816050c0706120b0f0303090607020d020604060206010515040312051b0a031d04020c06 73
    0x380150082c11001003909210204042007000d14442c9a840440180e440f803a070300406a40500c105999006078103e680103035810309001103640e03ca00c150090412034000000f8050050a0025542070303043d580c1029220b03903440c804020140c01c0b0a10bc48000e003d0a04000f40036005a00f0610328074001d007010380c0038110f08961902c08903411488120a0020940e00c2c400050b513441c2d40e25100d42c0600c1c030425200d0381141441e40c58045200062070211200c002d49118040d004401c0b254001a9043c0b040706080103600e044900d800b450a504a441c41005e01c0815550307000039105001c4841600c0820032403030b0f03031010840e1032101c40300c01c0394154208200b0703100c4504000000703100749030000c0c0441e07000a40a81c045103080d1301c507500040068000c10010b2000f4582500c03107240700d580012440b41003908540b114204803800d0340440c0c007070000c00100d00c4107240d0302010784c0c120500c160741919550030080c01c001e80401c0216068400c0700c0042c40d4a2545071400d8070a41d44034180210007814107640340 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 352418129 1250 352416879 352416881
    0x23010603021206040902190f17070503030d09030c050a030c03030c020c0a140103150e010303020d0c08160c24030e28060b03030a020c1c12140c030c0105180105010803030406 76
    0x40101a031f04606455510f07150101c040200500803d502100e6110140c506440627904180001165000350032018082043d40c0d000815150000e1980b42e000401e070450785010f840002c00d00c0401059800b4001e0714805040e00241d000b03c0e4580261000e00c00342071a1070040340c689110145035584035003442d07018405004d90130040001c00006040000752107100300c000f12060b49003948031394002900715006004060741880400411a103500b40011002e00541d240c00c40c500400c101e0360031000e0180741880a004600700c010f40141500004540d031858052015041c101014110f10302203403c0911071000d088002a00c4a0ba5010a01d002100d040481030f12021040d80c408064a9842e21140d00c0c81544c0d50910003070409518a8000f44900030f202018803110300e0300540ca400b85080d481090340e0208144c1648100703d03808921309289084203004403080305001d546243d8507980301c00f09482921070030550200340078180c4c0703050012688401100da2070a0f40c909001e0042d480d0003e00100e0001411 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 352419379 1250 352418129 352418141
    0x40b071b23040501092d0e0a0f02030c060901090b030703021e03040302070605041514040812070309050105070809060c0f01060914010504020304120c030915170906090d0c0c08012301060302120604 86
    0x400c1c00081407910703903401f20301e1800000c4c20341591252900c407804c2301145820041840003000907a0310300c1c103203924580040c03c1440a8071900201d03520001c00107500c54401c0d41110480903102105000000c681891400c41e50802c4030114058420b1080c04140d460041c4180c900301c070b0a00c0181413480c0031244040381c07408903082d01d0341d560030b40c02d10010944210a10207485130f1216134100c41e0b01c035041801d00905c0030090764800340c1444400c00079240420b08050440e039101e001501c1890340c80c42181c3c2074900d46208814004c1c1e00c0d519003030000c09c6000881d00f01c0c0013060b0b020a15003010381d80300d1082104030f1005441c000c081c0540c1c11b905401c0035000f50380065040740203060441c1d160f6139800020709a0003990010b00d000400f0381021584175140c0c003c00c00e8021000380024062840c1a0301040d54490b0f4820111040c010204030060811900001e43c0014022240003402400c0c14502c81541c80c030007544011480b000341c0c0c40040340c07445c400e10a80e00e500640d900710308042c0d04e884043c0002016 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 352420629 1250 352419379 352419461
    0xa0b0601030f060513092d02010507050c1905010215060315130b01030b010608070302090a0311120f030406080f0411011b050610030512040b071b2304050109 69
    0xb032150b1001444e9504c03400900209444403101140c200079524011007518042d1158603105020044a1040b50215240c82c0d054654203081060340c42030103050051900440020103907001c03890380350b0350b0f0940c407012560000f2100c0070703001c440b00040102030280201100301d48032505684440089010350401b0b02c400c41e0000289009880c144031740c2e48680c898840241c00c01d5510680c040d004200655206400550003000c5140450900c40c0000001c1d8003401d50b80710141c928007120a4442203a070341d03082c1d24039601600108446205c01111440b0b80c40341c1180c4101408911102c00150540b480c107444548100e40c000701c2040001012001034074007080d1800c0010441050040c444005a400c006242c003070302c07604e01403010941c036510b461407034100810080d50309440705220810034840000305980043e58001f01c9001c201000184411084441d41c0c400220039020100d408101555020744900030314080e2002d0007960f886507000d131b064400703240549100d00c2402e2022011800c4000212800318 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 352421879 1250 352420629 352420631
    0x51204080403050a1b0b0304020d14010e0d030b09010603051b07030c0803011409070221160f1524031101090e15120d08010b070503070b01030803010305010e0a0b0601030f 75
    0x1a1251109480d0030b1400740105c6003e4000003110b820b42016490050003002c0724080700c2e1440c50030b0b50106204c120688001002064418592640c4520039040300540c140924100c600c52030510341d0080c0501006604c0074003600c900c00012520501c6030203240e11a03d00146034185c0b030023260b4048482a0300001080c0c08014984607880d0004022100560003081000d890302420f030381307181c200400349a0261144c000c1d540860411910350304c182e000c07007298030340b6a20090b03260810ad500004148151400080c00d01c407082c41c2c0c0e07500304912042c41d0407030051048410440710070000c1e0003000607034440c803501c400040c545104000042c41da8048224410041c500346e0f0710650ba41d100640782c000c0a42c2e0303400410809001d404007a09103400a031301c0c01030151000b49030850309031201074051031040c05610741440000407041e00348407003041214801a4014008401d0f5a980c1c285000f4070b401c00c1c001250341c1c1d42000300500d070305600018440645a08501b041c1e8840d1182801074000b0941840c140c00c010f = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 352423129 1250 352421879 352421887
    0x120804030b0a02040b0d0c11010b010e1e0925090806060f180103030201020a0f0509090c0304050a3c031202030a0e10020a09051903170c10060e01080304050105120408 73
    0x45c00080000d010f0260905001003a0421580005002c0441200c1c481d9116031400e0b41000451b0303031180e5042d0b04c44009480030414031900841408265000c4d000b526004554041807010150030400c016040741581d031010135401500300c0342110b81c04283e20540800e07910034004500c01d40b502c034240b0640017000a10124a0702c601c4091943c03090000d030f100fa000360b5030100390f90460540007920741412951614283c1e00c5c0c40310482c0001d1075510701a1955140c2d1002000140401c003080000e21645508800c42051050501000600b540b10503107011781c403c00c0524115042000c0324081c04203040d0706440c0c08a081d050029130a0081d0401080001410380719485910016801d00002543c0c004028000d65a5a08502d0140c00d05800d54401d07070044903403041954a18078401c0071002030300c0d404100c00d05443e03c00f4400c88401d000b9040d44112901078081d0044181c9071581c0304000b201c12088030110140c1c1d0b20070f901d80d102d02951003101c2c0400c004000d011a0001044211980300d4070450040d810 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 352424379 1250 352423129 352423139
    0xd0906030f09150509060a06030b042604120203121206040506010e0a060329100305040507031a09060138040801060303051b19030f021e0313120804030b0a0204 70
    0xc00e1402c090448030310b0744c1d00d034240320720040c051103500d9105940201c1440304a15565402003203410081c030103000500d079810103c40e10040170781d10440c4044098080f94a07191965148110120380030402ca2080c4600c401c043c2803858408165031b03120420710800510342c1c0d100400e01c00a04001801e4604102040e80c1500450b560006c05201030065546e0000e03604d40d448441c1c90205034410243ca0409000c6488010160b8660314081c201d52124540411251103500d01a481c1c01310b070303400c000c15200340f5034001a100e15004400b035101d1b40003032048403a140d9952781411158400d0405140c40cac0b1642007001c825007090b050110115100e108207440c500b070303070b00d10009084031000e8100f24002000007400e141481244c03030101d0380600e10301000c1e120079041c5003802022101c02d0400241070144005242185500030b120100e0b8034618401024413001000315825241e621400000b103100305541c2001ca1810803c036206c0694941c009a84da26150954440c249030060080103114050780800001c15 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 352425629 1250 352424379 352424393
    0x1060e011b031803080309030a02010f09080703140913090b0a1a010c0305070c0f0503070812040608060418061b0809030306010c210f0f051323040e060402030f0d0906030f09 76
    0x3c482ea00d20006161511309c8141c0080c04c1da0b00919542c07100c44e047c1030010022234990700890b100e907581400c1900d641e07440500c0c55a954090000c1e059840407400040010404a5410a02001d803103041d2884440d580d03826404121120136510700d070b200c40080300c040000d500035111010f5450003400c025040101e159580c050842c82d541205c2d100b4000400100b10a0804014610180031290040c004010300f0b0344600500d03019a220302010020345ca4003140c899140c51748003400d485103c2105841d407141c2c50800e140074180d01654285a202589814003006109008171402948810040e40c5540c948900440c3c040c003040c0c400b1340d00740c000c004204805820780d2104030340307402e1207032541030700032180d443c014240d034104c040030006204007000000811111103141c6c03016518070700400b41c0341c00041c0084003130703200a915400e50401d20b0001c201d8507030100055018852403085040754068200082441d440c3d5042401d4107000c11000042488101d0190300b04441a89000c1d03030000780d0211580701c180e = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 352426879 1250 352425629 352425631
    0x604290901060816030321020403060f0c0801140a170c10020a021503010810110d02070c0305010c030c02060a0509280c06020106060c02010813020a03080301060e011b0318030803 78
    0x1022580d03640408100024040c00300f0130040d05002c1c0d02031022841c584010342080141034040e200c1209003180110041d4181d070541c2c3c0910307040101088514030403203d14009004200754900450001c400029907240c545500c1408503202614040b0080e10b0420100c10300100100724150500624240c6079590b04c032910600003821017907006141c40305031401405164a5106012801c10303c08000601210704005180d40050701d40410010309004880c0080d4580d010f42e2040c099110300006211051124109044054070701400c02001074038000b0909070b04907658038061001682040e0000703040e0300715603480603074812150016100308140041203000041710369480c01e004a0341a03600756062020218909001c0c0003940000c04c170082c1019000b8000c4005190024108204040001c00d40104082c888044a502130404290b00380c4900d001042034000340034010020701500c820300e58641c0726800102d0b1104407101e04042c42c140342e40702200d40542c01680d00d200c1da0b180d48000400140400025 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 352428129 1250 352426879 352426891
    0xb0309031207090303080c0c0f010617070806101802190c15200c07050a080102070b090c0a0302040b040b10022d060f06120d020c21060429 61
    0x51507540c080c08600381862600034148000f045109441031000940103480c00f504040070300b140d41c1c0c5401a04154a20b0886103501c03001095013041c0c0005803002403081403400d04402030060714801a241e10015a0b640701c100d5480d210307510051020084d51441c40742c281d048442449001d1320704028080316100101c100f081d070f0340000700e40d0481c01042c0001404040d0b0340d4a9845000e00070000003417140d0101400c01d07806107910420000d950084480d081042d540105000341c444c07400d19560f420701c0f034000d4001c0101504c0b4540c624000461121001c144c3c2168090020403406060b030554082c8401001560401600503981e52030794052039844408881e0105999401004960511200140500d8401d000c004c0c2079035041c402285010310110b04c8551106801138601c0c1156102030005090b020140e070340d1503050184101c00724190740d0114004203020420b0301e01011103090242c00d207900b0a82c084800900d500140042000a10010740145081040310380700f42e2020b1003460031000700e00c0d0503254 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 352429379 1250 352428129 352428133
    0xb0906010617070e0f040e010e030706150b0a03110708030f0402040c0903110d020103060b04080312060916111609200f07061e09080c120f120a02040b0309 68
    0x400056070b2200311042c00104152200440d03050034400076001145000309a845100510000c65561b00c5550101000340d103200000d010082c10404040d4070799100c0001510b0340c0e4207198010300d0309480f144a500803206c408100e0f52038089038030300072402040c1c00408030340c9110381081000c0204840d20040c5026418104565042e41818810001201c031102910814408240010404900014031010800b441614114403608091004900611894204121818020801061618001001e00340610212114001a484180420800c030404840544850b0348401d460080240710f0000c2543c00c00e15802129400c94410003403e150750003c1c0c100c80900da40e50003016400c5076032203050711190103108c01030a28185445500080d54411620f01808158881d004c03001d02d00d03c41035401200030390400d4100aa1a80c51405800691202005290902c181c00003000340040725011100b0801c00c0304403852500e160003808c0b00c07810340c000f0484440340b50300313020008011107280d00451140443c000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 352430629 1250 352429379 352429381
    0x70f0b031312030c090f05010c020913050a0b1009060308040501050c0f010e2802090f090a020d150b03070b0d111909180203010f09050c0c011a0102070909120804020d0b0906 76
    0x402030941740d8603800b42d1403071501044200038503600050742000060301039a03125907075507422028018508441301c1c000c00301d104030600001484410044a8064441050918401903440180360180c440902000d8460081040104060b6000310010416155401d040e43c0c41c40d803503445018211020341d111740c6920f8002c000744010702c0080780c0340c030b40e00c08030001c00190102086401087c06900001c0550303080c0445000440c10b1440108001d01041d0350041c11109201c81a10b4070545411179101000411401c18070303007030721924002c9000380c1500c40c0c0440e800d09202c00c01000a01602016046140d2501c0401200076040d035500c500140e6040c05440e6a481c080c40e104000840d0b03207898113a00492807040c00140701c00c20503510003408841e80d144000c54182c4400c049007085125030b061134162907181034440e80f0000d51007048041100c0c403d03002e960149556196150940d034019074002c0c00400c030908000c2d405801026459002030024002030b00c0d0071103540d135140343d480c000e554030812580200 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 352431879 1250 352430629 352430651
    0x40b090109020a0b0c0c0d120909051b07020102030c0a0f02040b030607082e080307110d0f0f0215120105150c0606040c11070f051e01230d0204030b0103021002070f0b03131203 77
    0x789c1800c0c02002c040d10104031170304c5c0103568000d0b5095111601036a10500080c640c081d03a100304141e60000f103840c03082c0c40ca2040c140c50b06502c103a0400038124001d0303042109516003450003084003031003803000341c6400c0042d0380d5040120a212903001800781103038a86400c0940391260b445800005040e03250025982c4182d28200074808000084c0141e04c039050101d03d040014199621100c01e0550110a60041448600c0025a4820648540450a1030101d105003404125030292812200143d82d00d50802c40102c01152452180100320700d4076030b000801180d128180303540000414900c0c1c0c503140b426010001d6866040c55031035406085004141d00051015181c080d10740c170584120601c925942500b0b00f000640300311400808003c4800850400300340421621041300c401c208004411941c458817450240705071b240a0000b40d01401c00304100018003030000603c0c1061701c4104031423603002c901d01030400d0010b600090241c01552035810f0207400044c00100004e268051035140819101c49103 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 352433129 1250 352431879 352431887
    0x204120809130c0203070305030a1409010b100203030705090d0606170d02240a0b011101110703090e0108070b031302100e010e0a0b0417010603050312040b090109020a0b0c0c0d12 78
    0x25800c2c0c82c403103441c10046403245074000044846917039040c20815203958503804440c0040c00c139034510420110701802003106020040d031001055507001c54404000d0b40c2d5121040360b40e801304594407804940200b00848191805e00c0e2564542c3d4030a0320041619520380412500d4064141c3c0035400b142d01c022001124282c05000b480e0102d2104201321000c0750a00343c0d6000e461a001c0e0003081c0c0259280d00000c500e922a80c0b00c4000c4000c0680240b1441c0800d070004111544070040541c0080c40385807012407800c0c0d011100504844c80c58006220850410414120301e50010701200c50901140140c0001a1208050742c0c5061700c0c241c444001d28035802001401850110310600c1c82500611010b0011505000645080c4c54140303808202440c40f840007603004100c1e0380c0015240d4800030941411080042c2140f510a0307203e5030a222203900c455928a090301c003100300c000d5100115007418440f000f000c1000c0c203000010070085414031059034010a0401e420b551099070324802d0700041003105600 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 352434379 1250 352433129 352433149
    0x506070f02030d020306030f0601030302030408070602010908040501030506060706050a0504060b0111060f091908030a0606110a080a030b120a0308090d1d01090b0a030209030c04050408030711010204120809 90
    0x1450034150010900c400000b51644034422100c41d500d54040045041c1c0c1e1010002d1075480c41c000d008403846540c507410065941d40292161005904c240c0601207174451041c011100140c1e404060242080d0400e070064000d483c00501e0036400120500030900446d14601680380108020b800000712401e00c1c0c00c100054078070058603541804490300e000ba216400008030a5404640c4504070304054440b01880d034181202142101000010005058140160b201c0103601070340902004006841d510b10f0140c558407000c83d0000495000b2000c0c0601092050b401000c12340007518000503c0c1c0300b00400220342c1e0400041c410074551140f8080c0d02015007107001d854100a034000144540d0020000090030180340140b142e1440b03011804454140c3d020b2800f0701d01510700d03024100e0321249503e400400030340104200c94468480c230300705201c00c7c0c105446058001c1c3d422101d0f8915595402c1010384048400100c480140d41d800c000005601201c2d160038549207120701015036803981c5603030410801c604 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 352435629 1250 352434379 352434391
    0x80a05090303220b0901050304060c1407031d091611011b020f0c0f0f0f06090d03180f0f0608150a15030b030f0d0c0302070e18010c0e06030703090606030c090203040506 74
    0x4c042214805c0c50b07800c8000e4a500c0340c0e0040010441e002c0e07041c021686211881d048049629012442e0300030940c0184c811401505c0381e070000c5843c41807140c100b1407160030603103100d1004658100c4040c8501d201d0b104002c2030a4142c0d0010401102c00c9075080b1105160726118030040e00000521641c03044144000f8408003000c44104003203032444d00000c0c4400e03102101c69845100008226041074451400b642d803140c00041c0951a00e024504001d00000c200c3c421b0850440b181410200c0c95200e40d4000d54140c83d04640300c040301c1401d146c826505040094495101c0110000603100c4558412400001510f400340c900454108002d40107016540c000c80b2180c0b00780c02136101ca51010324002116201d0000501d00701d40b40e40c100741000d80c00c100c0b254201d41d0603100d09030104005400c00c844600c086c0500313070008000d09099254103e0350002c45400c4641d104404101050000d84a83c0140b001c2d90b02920f4002001da03660703651038441d41c4007903200814003900842000b00707000051020390390042d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 352436879 1250 352435629 352435649
    0x30908120106120c05090103021606061e0e0705030f090a052b1103030402040b01140a030c1409010906080a290301060602030c0a080d020c101d0c090103080a0509030322 74
    0xc5022130001e4054082d001c03600e4101940403402c000011031501c03888000a8010004011581d1070b00000d07103602495041203004e03284920700000308031100d0141940f02d40c120303a84460541d00c80055180d08080060f0884800d442030b407070b2407004140d0030f0044150848600c030700c40124820001e60601200720b02c00100090000526080b40f00c85008030850b0b511503411540001d5030b034a070b4401640d164100b5603001c400031001103190343c031103501540320000d184d0064448802481c2d6828004c0c2c2184100c400c02400140c44043c20404107000d010001c1d001044004049405040300c82104005c0f000031050305045119000000190304080c40f03010054180b502c0698945071020511a40d00e10720204010861680080d03104054000c541c1580c0404120009031162001c105103030001030080c101c034401c040c1c5c8400d40c48845003000086c03411039015000d884c84150385c1c6551902445a04030503d0a001e01108002c444a00d46e020710083c110300c40e8007034400000d0b01d141c116080c51503001d170301302e09940d03 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 352438129 1250 352436879 352436891
    0x4090e2506020a14030708130302090105061603081b0a020703120207030c0e0408070b070206060f04050118020f0714030a0212130519080106061215050f1003090812010612 75
    0x10560105400d440a9040584a07000d03096180e0200e245d441406400751002c40085840000c582c204912a800c5034001c96840100340d8031141041680e104d05072082002e0300c207840b43c0400007409601c90640c89010030543d85250600044100e82c0c81c0c0c007201070400180c2000300d0a20403c039881c2020351412040d440180911410755032070748800480c0d802000280e45460000404002d03040040320080340d80b03c183e503640e6003481d2501a580e090b00355500340c41a4062107d64400341054418507040320078946141815401760a12130000f54071131a03401c1100304040110102007030401e400f00800b01c0b62074000f955030f0790110100a0a0a401e049072a071604c004011b032040510240c0c01a4040e50b030219031181604140744400d0305c07000140d03804000c142d424420009080b98000a1401c1040140c1a06010401c0c58440902000215008056005c0d0343c01500c9200390800640840c80b1911a040020f4041c2564135000c0003500140650101d00c074603500184812940294030b200003a411003010302c60 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 352439379 1250 352438129 352438139
    0x2b0206150a121103030a03060608070e06030106031e0203010308040612090317191a040c171b16060b0117060d061505040908041d191104090e25 63
    0x84880180300e881040c0d510b004004081c84a00d99076540ea18100504413507541800c4580540588618880c91300466070210010720020f02441c10703508900001404c1514581c02e0207000d40040192091040711300410050b120364030205880294040c5010300851912a850200010301d50903001c8424090a41095482e80011380c010005212000d10845800314940d103000000810400001c503140c0100e045c09901e00060118003004541401c003502d0a101c6014861015101600d0321030790b408514895800291170100c002000c03150303a24140c000c00e482c1a2140c207403800e4545210400b42c42860303582405004139a0400d00070706100c0d0003204801c410340381810000e02c0c41030030420007a05140c2c88101a90900e801c056848014240042c000c02c101c100340d040451550300103015150141d40119601040e04492020051180300048807515080d944180c05c44060448c6420907580201d00b800f010640a982e406844503a0008900615282e001e1460789070303042d903811035040d0302e088051a041c45 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 352440629 1250 352439379 352439389
    0x4060b01050708040b0307140304030e120f06010b030702070e07020d090f030b0403142b1508030313020402040324050a0204061b020f1818071206090201022b020615 72
    0x858038000d00c807540342d031f803401016a0880ca4017600050088000000c0104240c3c01a00700d20354004c00b911342860140704c10810395644c500d01c400c1d5031200d60082d0300400441420400956006d15284103032541307165a04841c030119901a104c12000da00004400e411b0f15500c1441c04005203000c412091980d03185407500d4900d460050409402c01914544d107083c0c0290000403129a54484843c2d41ca080045040c1306e2048091030010341070580c10400702100025105407902d0950b4280c42c060340c50b40c3c51f80d0900c0c82c040d00e10380400702c0c2c1240e001c0c000080851019041024000b0f42c03980c054501490712180c6104135040203003c039150500c140401d2004a6028414110140c0c210358086c54810355400010500d101105070190311860307101d104100c015490461901404040c0c2850700c1122080701400d0720390300c0a01800d5100c040c2180000301240054004000c00c90060064540001d00c1107411403054a000c021104035061502c1004840380d810010158801940600c4851200c02c040c0010 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 352441879 1250 352440629 352440637
    0xb0105070816030e09090f0609060405060f19020f03060102010b0a030314160b070e031011090d060e010504140c0603040804050609061c0b04050f042a18020304060b01050708 76
    0x74102d1001540c001e0b08150143d000d8040901e80201600054a4143e0400d942c0d007190444910032400750034041140384a0000301117000e80c0d4407401420140d0b582c2c00c41154440002000e10742c01c104000b0301000c600300e05100402c1d500d00b41410b400e03503d141841c006401c0d03c448150240c0510404403081011030b0380849010740401c3c00540d69035840404135004041c0600c4414060408100a8103000c121a0040c2c07401c2d00b015401c0d01a50450000801720500b1641350000044c0030b82d804001000840c43c2c0400b1b4000824800d40c0000b8400410011007802c5400031034080342c0228503000181c113155010064a41f045c541112014514078050707680310010302562281c940100e00215000109073b66002c2590200320503000d20210201e4103958440150210b2044140200c1c5404003040010781c0344114107105941202d246c48815400311000c00206c0350161640f25000031580020031042445d40504002e202c0d4943c001d601c1e400c10f030904e041155043c0b1007250512100300107070703800154400705031 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 352443129 1250 352441879 352441897
    0x240906150b1c0f150801061a030106090e040606121a09030a020309040c090e0c0d0f05072f0d0302030f01051c06050910060b0d050c0a0909091506080706030b01050708 73
    0x200703251100e2400c0704084c000300d1201c024401303030018012600050541c49101150070755140048026200b41040c2c10901c02030107210001b55401e070050140030800342c2d0403a0854401c84001032070513600c040500d02c0402a1030704541c40d00c440742c50b07119080d00c2516040d400c610201c015524104840c40301030340c0d0303104140400d80030304e88580e80d01d504103028109040c010711140340c0c0c00d44245040c461405041c0d000001c80d030801480c040c01000c04103107510545120741da1030f84803906101c0c2c8641c2010300c0302c3d8902054680c450b91285054849c00000e10118005614548000d0380340e0074982c421041c2180e058000f2170042c40301c40602c074806043d50104c036100d1508540c0015540d12040d0607d0b003404141a19120600d05040300000d004407d0001007480304000001040700e601c85150003011481002d0011000842002c41800040f20342c6c0e00c41c808035840b03280c0340c60780e0341d9142c00e002040d40c415900c0050180c0000d4000c21034550903024580041c00b00346001840e010b40f41d6260a441d00500a007 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 352444379 1250 352443129 352443131
    0xa0c0f0804062f030615040f1e0801020c101b2f1e07080606010212030a0f0c2006010303200a050105040614090304030b04061d070f090f0209030307240906150b1c 71
    0x480002701c588001c2e95020304013040080d99201125405903580700d4901d44540ca1440c035004854071000b0b001c1040c0072031011755550f010f540c51104800042c1c1c0104001c41c0b40c000d440f1039886121403071002c109000b8051440c00103400c0d1203104040711030422250354072440054110804008581c0c2e40400c06803804000c00d0030b01d50704c9490314a20b03080102040c4504040003072400d9070305421300390001507405444010068821008000550082e00c0f1a001c0c0b100402003005030505003482e4441803404044841d221045070039004060301e60f6802d555003601c040e134506659030703003001281d11040300c025441600180194a881d142d5910540c00c200b0050010748601d594440c41c039881c0089451081d100342ca01402c55003003903110340d841c501265261142d840814502103240d11302429500a03215201c070000c0282d4104201511481c00030745800d40c110032070144041c0903559010043c8101c244903170148000049207808041c007405803074015001820500c1b41404480c1e000038142617919400a000c0d04 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 352445629 1250 352444379 352444409
    0x30507180f03081b01060806010302101b02040b0612010b03040618050d08130b042301151406070b09070509060108090303041212060e0a0c0f0804062f030615040f 71
    0x41c1c139280700480d0a000c070003035402e14800141c400d00002e8650b05030ba00840340b1912001400c40180c0710007000c4010641c0c034502d446908405440e095000030580e040180c0443c1ca012041205001c5d401b009801003c4030507030100c18801484150711410f001003150b9588000f2606039519641d035900c28030181c1c135080180100c0080e003000c01050003000526030044215146040c50f10f00407403904903c00891185540c5541c1d40036048005004003002d014114228510403401c00300d4024074180400b043c19004501002a0000100c450020a2041e8501000740031868242401c0001c80d01e80907010790304203e448014041c03083e8000c41120340007584403807030103032484a00805580c0d61003041c1003900500c1c40c00030006042c07020a14075511460740507400b080000d400300426504142c20348030243c000b500c00390000d000203007268451960380418410524000b0340d0103044981d441c0110680100100c0044148042d07400d0000c070a90201b09100d0100d81040e041c040c400c0e00c1c8035002d2244c0c0c03817842e040300 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 352446879 1250 352445629 352445647
    0x41a0403050d08040f2d0b042f06030408090a060203130b04060503010e04140303070201060f120f17090d0c030b060a03110f040e03030406060528060f05120403030507180f0308 77
    0x950b04800b100c00400105031b100302c250610700c03d02001141d0a40b494483c03880044000203920781401c000390000315501548061400900041ea00000c104031920f00c03040245415641d54000c3c100c000304140c1d8000c40c0d85a80d100e00c120301d401c46d5a4400074410605010500a05802a0a60381580c94070b80100e4040d0f47e49003400501d0f054007070034100060200009000100794190000425640c40041c603004031079850b0882502d1130b00e0420050f140303030320490741507001521080c3e1804800c0540902603003004003000019951001c9901e045800c400c0ca500100108008400020743c040b40880b4542c644904e9500c5a80e215504005140e2103800100c5040321156250f9100c00b10003c8d024003200e80340e00c3c01d49403c0e030060040f80a2644500c4182f00c03d420821983c070f0101c411100760000300d80c20140380c401c058401001421000d001d00c801404050951a0810b20180c841d60080c1c2c0c000c07459080200018011058240d8581d00080c8020020701c01e41491108540c101c0354411080c80c3c2d145a14 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 352448129 1250 352446879 352446923
    0x903030d091509111206010528030c090519051b2512090506070804060305070908010203070206060406090b0d20090f0103060b04050f060d020105041a0403050d08040f 73
    0x2c000e02180c032901d00703500b500a01521104d400314809090b03922915201c1d074101010750700c400034030941e9880040301c0300041c4501c0d08540c00c282c2501846004403c01078495075031070744440c8181c200d81540da0795030040146400b02120070042c1001c03c1c4c030080205060100301109040720001d00c1010f0a440040c86041d402c80e800f0001003141400e00c5008145641454038a50482d0300d842900c00203405484042080c2c0b81c064100d0320718a6000e03014a02c1c0615000b415005084000d180400f0301c1410640058120402e0000318031850890703000c0c040e01d1520300104000c803041604400c400c0c0d89007200124054641d903600c1814280c110607410b500003620280303003203a00c281c4041903421507406024408400890200203041e00c0c8607074003e00c09201d2440c00e02044600c211820ba003a000001e01244003410140c0c444808a40185072003442c081d260510408a8002c00c4400740315000e000a04105000ac10f001608041a281c030301600c0c03909064890581d239159008003d000c030303c6003520b840030403080 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 352449379 1250 352448129 352448153
    0x11409060a03020c06010509010b03040f03030209060c2401080d050310080f0d0f0507020d03030e010f051017070e0f0a060f0902091206060303030117010f05100f0b0903030d09 77
    0x801414580d40e0044000c0050194200200449681c0f052500102c0c5d10715120130f442c7d0584520b680050300b5035450361039010390104480b2003501450342c02c10010038075444850040021034031500017045008540303200840c055440110508102580800601c66540081402d80c0007a0310780c0b0b00300b9203a480c2d107050041c0240041c0d00100c002d02c00c244800140800114804402c100c4588681542418143c1c0555a40c4200e81000754080b040c1c1f880c880010303019500050781801d00d00000200514a88041404c0310001e542030940c0103140d400402a5181c1400b400d10980f5641e00508003192a140100e10581d10140c180c05d00b05402c1c10000307000301441e41c0218024070840b40c441009a40e034a210400070352040898901884101070140125900000e81c1405410f01034015440c50386040c184000d00414250317208415500c1d4280740c01000001c3c0500c038022018500441c044130b147c0880c4548003020344d405444044010f01800003603940101c141c0319410245500445c050342d80c0c0c5040016110 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 352450629 1250 352449379 352449397
    0x31509110d021f1809020f0a080a231005041401030b0603030c2b050a020a15020f0304060f0c180612060b19020f0a110411400302030c0114 61
    0x21034452240549600101d60240c113005510459621030f200c0c101030060f071040c6031000448071020030180b05000c2c412003403076912030306200d4000303101c80d4800c1300f030240c020a007100c6003900762920f02130001c144250700d203d4005040842d0100103241403a0b001c00740c4403805210203818400c0c207400141803901c0a000b00c46100c0c51060035105030104101111040313440300b0740051500302035119420302890003401100d44000864005001010705581c03400d6404500103c00040103400788400860703068054050742c09548188408070304d4182009111046841408140003084668100320b4000304000200c0d000792801c07485e0019940d084004894060003643d44040203000c0d000818a42c901c0c0301d004e0244041c0c10540c00d81e07602e103000c540c0141c3e075106003d0001c0c03c084691707981c20a040c90701d50f200007c5070281154031824054608130007000f0142e140003d185203080030084850541c0310110030041d030603407410041081c034250f4021070b6545411145590500c5125094550780030717111030130303145918 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 352451879 1250 352450629 352450669
    0x503070501050108010b010c33140105130501030b010b07030e060304060c0818030414041104060c060615080a051008070f05040f021207050d090501060b04031509110d02 74
    0x1091a01074002c15007446484002e500e4880c4084c0558800c2c41c0c46207881e500700702541420342c207503080d40548414100c03801503003481250300480b4292540c0107100440324103040012903907142c54140110b00c0541d10307600d11180d00c0d003001480040c42d00031141341503500458406885001c24641a071b00300b14095009a0b004002108000401000e03401c01d444088803960f481c402d640b01d08802c4015005990100a06a003040c0424010000f28000154086000410200f2740c010036441401080c6e000d40c01c20400034946259100900255015420007003400c11031a0188840c0100000c00552001d03020398403c50301c441c080b44902c1c24040303811000d895040195444140ea0304560940344907070f403040b90700650174144141700b0b802c903520030355007241d017480003041d41d5584043c0110340a030311081c03c9540141d82c940d110004201c0034400c8401600001510b15511402e6081960400d007a0a888141803420180500b002480c4119822282181503030507000d21441ea20000e103400c41e41c100380704089 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 352453129 1250 352451879 352451887
    0x507090207060506040e06060a090c0512181b06090d0f0c0608090d0c050601060c0309030c081b0907020a03052b0f0605181911160507050406061b0606030503 69
    0x1010466200c04d008020403101001510300070740c1703a0b40e200e04080303070781d81da201890f00c004120b0400140c020944052503441d00f94035002c0707900d002c5646554141c0e4905144102a40d0341d032403e610410130f01200c40f902e40c90140120000310001803191045000d901d00903004041c8900801181d01d5003503052036404014141c1310f90f1910b6000709200b108a5070661940b084851441c016401082c16052254200c00640703103903030916909a40310440310380d00b1000c00881603800000f1030b9142c44403030003610242c1c01074114040c02c000c041e140300c02003404071803180d0045010712001039000207000d02c3e070765450300f0101d459803841c2c50480751000d800c10440861085110b00e203400450694002114a980344100b04812a00c40d002d00c041100003401907491304640c06d010a061010b0030f9006800481d4100340800e2900e15032401141503005101944000004480d80100f080800d100c101c002d0102070f5002c100311440e0160082200402d492859051420300b1482010b0010580243c0003858108013101d0740c0d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 352454379 1250 352453129 352453133
    0x60408180409020d060c1b02090a020f09030d021c1403190e0d050d050108060906010902030a021318050901150306021803150a0b0306060f010305090a021c1b06020a030c0507090207 79
    0xa40038aa400f07500140d00041f2510407000c0c0745224600080e0040c01681c4103a60b029100b43c0294040c42c0362000301e09040c49010000d540400c4006042003455000d040044a0180030102e03043c541a80c50060120f0b5003000c2502070503840540782d01c00381c82c0000c00298a03020140500030000340d160003d10340070b0710280c0c80c00d140d0418010301c00024846c01c104156a80d030342d61a038583c0c1050310024400d410040040120b81400d401460300400318140c01843d1281140d502807000102d580911760400c0d400410b0303050205544916507000c2040002800400c43d0a540c800c4c1000450000510305c5601103600b28458826464000b042c0074090210341e021a140c0361101c585100071100c070300e0ba03203040c908040c20078100800c0c001c3c010340d0090200c0c0b91859100006402030003005103075003440d1007248403000144e0740d015205401c041000c0c13540318003482981004d40c01c42d82031008143c021280da450822000c0d600295036007099405160030058900585003080c2007003126800005424000305820341 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 352455629 1250 352454379 352454381
    0x5090f100c1b0512010e0607050a050405030d0c06150509010501050d0204090c030209030d021212040f050619060617011208120a1d15160c0501140612060408180409020d06 75
    0x1083d94411a075001280300210506801d0f601c0c11084a60a84c00100105840a000c2c0010b0503c0c5449410064149900c60020034642401c205000001803480030001013405480e01c900729002680c5c244105ca40750401021624507001031244504204000581c4104940a0740c10384019242c903000c02e000300030852200901a410a81c11113101e03014491100d2040d0340001214844081518060b0341080440d261180000400601c261140b042d1107075007000248060108520540c107104010311041c0d15000c40200300c0700f00d0341084043c4120002c1c1c94022220042140d41161a44124055511a6072810000700c1c010481411003c011000070710400081e141c010018a62280ca859807000c074440d8a06a41d50002c0d01c02e25040c44050f0340881e0324206c1034103840c48070019034180003100c00e81e10382e61a404c454202e007030164103122020511040346412045600031034104002045181840d8541c0480c1e0710440390041080c400720080e548503622244c0191001540061994104415600b4518 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 352456879 1250 352455629 352455683
    0x90a260a0f05060702070f09020f09060304032a050601031e1a04030315050d1b18050105040f02040b030a0e1c022d0712110a0f080d05090f100c 63
    0x1101c502500001440740e510000d00001111551600103110234030344a0418002e42c0701c410710b02d1044000b000b40b01c2c0301e07846450065000303a219035141c425850503101c5001e082100e00790920305109200c00000c006c50b900240c42415240c0042a03c041103041407110030602c08802e100a244d0084005108c41a0411902c00c51049019440910080c0c4055641700419560350192030b40c0300b840c01c410700c00400c8004803418071078a8041d041010140d21060202c0315a4000000848859164401400f050409008586034010144419810b21703041000040f81c9010080818081c10b50b601141141e4600403c008220034602c1061a1030304102d2900003502c079103414003c0d106051088521922082d80c0840f40c2c00c9401560010b0800c030b50802800314581070f0661000c1c1d8401500010040d10741e680c18200da8018a101441142c00c01d00d4103030581c0c246521201c1002c00e222007881400c0a98135400c906035510101210082e810100112080d20020020790010f080d50003001c40300006d500c1074000c09 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 352458129 1250 352456879 352456883
    0x30c0305030d050a02160b0405120412020112020304020a06050c150a0504030f0903024002070b0106090b07150f0e070512070f0e0c041502060a05010b090a260a0f 71
    0x10f00c10355a40310714202c00d900c14804040c0e8103641c82290a00071907500c40780150401d03c12000d440420361600c41c001c2c05604240c00902903601003103a520300311b41e00010400c503400f40021055046241c01e800060b5400744030306c90310043c8040051070301070641c1d042c01403414005441c50102e4080c10308100c2c4500030002200c0440210725107154880f54140214008070890368000d180320f10491410000180c0c01005221468410104804410000400144500b040c000800f00180c4640303480c208021100e2060b4000024410800003e022100e2086e01322800b20340c100e0585020032400380c1020008000f01e0307401107203051420b0b03040180100301082c4501168001c030340c101c4042c0110200c1e952568070b20b00c90109a02030400c41000f00c25400c05005501080f003401840c10300f950f030b0380d805a82d0140c684a440050b0002c20070000010950f200d1240900b20b12020f1030300f000003d0340030034a1003826018004040b60110007101c01030a001d0030708074000400e14191000c882003882d110640b03406070401 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 352459379 1250 352458129 352458131
    0xe09010617010207020a060e0112061d0f0c2502040903080405120c03090d030e03030f0c1009050c0d06060f170f06040309091512030e01090605040503030f13030c0305030d 75
    0x50700050080500940c2d4001c3d0b0001c040110700c80c900b4400b5100744454049040c103000d15400c5040c1d243c6d141d0b20407030780102110010300c01211024542045624002040b6128240c541750030f000f4201c10100550b80d61034003072010b03514003040e01803509843c4e0914580080d07016003031840f080c003016482103406010701e12070720485110151242210541e8001c4030100c0d4a240d009101c0d0990901d802031b43d080720382d4080c4c10400390040040f80401d00316488180040c00b0700740e0029070301510038810003c24001d40d120003001c015522030b5940d070720744401240c00b0030b5100700c16039001c0100340300095022200a10002084581c0a5a07404e0100d43c0c1001c5400310960034003400f1101c0720702c0c070b401007851403080d64542e540b43c0215040c44001c0008102c1c040300303010200422300c0013050f43301d81c031b000741c07803c0314003e4480075964089080010200680c0b40c00038420003c0500040005450010984528107604c1285c95110125100325014103100c0742d001800c2c60400041c00024004084024000c038007080b88 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 352460629 1250 352459379 352459409
    0xc011104240807020307020f060f031f090605010c060903020106050405160216034d03061005150a0c06060308032d060d050a05011a01020d14040614040e090106 70
    0x381c0b20741008a03100c1000d60401c004074001440c0c050711003080040028155424200c0300c80070100260000c41e1582d1441e034880e019540181039035409400104500d070b60a000907403c0900080c00c047d11190000c182548440640301014000c1d08420042c140142040140d45415041081810750200513140540210f42d0500c044a220105003410f83e500705494240b8140c1c086c40000c44022071140c4031010000c07010f064100704d60000070552a04600c1140d03402038406070f83c201820840080e0046413030400032141000241c840040030100d1400c248402e9032548244902034800240300c1d00014072051511001208125021000e54014220414012070394405400320500010040555460703207000c100000d1540e01c0d0040c03c042e80a803143d01a80c00003031442d03881a0a48001013a8005410b800107004240c650341005068a00440303032400265240e80300394201c0741c512075405038030304110000c000500400315100c1190000c00600c00000c0d802d14000c40c9050003421780e8040c0845c4070407450 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 352461879 1250 352460629 352460699
    0xe0f060709090218010f020a050a0804090501060c020d031805030304080102041d04080f0f0409151415031302010c150227220e0a030905040b0405011a0c011104 70
    0x44241ca0031100a0a060b00400d41130b4801964101071800070603007188281043d0800043c0c081c40038240e01881560700390b4947c0c1c03c100c1c154094900c1600200d042040005840d000360352054240320b901600b5042009103a03810700e000d034010405070740185400d84400100011104c40550040c800c444500705503414556901c0c80341d1010741c000791400380c0200020300c404910305107400018403444402d19071b02ca1504c0d0360380c0c4450043e031711400c101d0a003500c03441100300280c08602c40c18440c00c0d603003107480e20080d1800814490141c000680b28031100e0302c000d4645021640501c00c6002c80b03940002c0e841e5003400810b90000b0103036000c4407103041d048542d50380400c01401505444074444100030610708640300d02c1140d4083c5418044000c0b90b0898962481001c0a607041c414285214000d5650300c1d035060901040c04150f860a8400714003403850803004001c10740540e08408a0002c200086a55903940080c056000d04490f203101181c3c1900010001902c65641c141a00050b00003d4509a800504 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 352463129 1250 352461879 352461881
    0x308070e0a0521011a0d2a06051c0605150906040909050609240c03130c080a05120301030b06011202070204230703060803090d0f0b010902070c080601120b0a0e0f06070909 75
    0x104121790304400b29114610026480d2407021400c021400070540480618a4959407003121035845500850381c0001c2060000017040805002544007210501c4901e24002c0443c03201e8103010381c02c210b0181b010030b0035121036031980c003281c0040c86401c03020711540030141030454480c04203450101c8144101151108005076400e40c48140b030f080c021444003551341d0012184e00d10b0348001e141045000c84048118001404903031948040c1070703000001c00700038400386056841c05007807550504031034409000402c0021642283d060b44803d0a181240a08449110700c0000e401a00402588035043c1548050007100c40c0400c546542d0300f1103001c81d025120000180c0840d0050301402100750400c01c81c002490034400d10310401107100d82049a942012074440c01c04005003030300180d04081d000140c960600c4000d80000026100240c0904025490503e58010b02c81d04500d0040c182507007503001810145666002c104210070038029518418180340221307460340011120100415a030150215150f0b000d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 352464379 1250 352463129 352463171
    0xc0708010b090c09220501060f0806060a030905030409140406050708041a10081c020106050102150105010305040f020d0327060903171909031109040308070e0a052101 73
    0x101604002140d00c8100c90851180e1160103415000782a02e002a020409017000360040508840d41c0041c0d9541042c0340203000255805d01d85040125801c240f00e01a61208101d84100b020350500103054280e0b45425811400781c0c1d03000718085407500c503200c2410728400700118456403007400200007a9a4010b03059502c01c40907140038100120701003038101e1054070410400c1d0040800300c401e0b0612580c0308425480c00c10440700d0400d5000da1094820301058090040760003501003400648005a003840c03071882c0001d0148141070416454402180500400d002800140b540140108801500d0707070170050300044181c0c0200900d40d001c1d8000c0c00500c004d074011a01501e103256218a0313089e146072202c0c03015000c0a031121021140c10881c841000c5031500c1c4609007000152260a00c2d58910706102c071140518400b0305020f10b4402c410040000c0e4031061503030f8441e0203802c0008061903c8004500900c0098000c1038106030641e409103504541c060848140441b114000d020481c107034401c2c00d911401c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 352465629 1250 352464379 352464401
    0x1002031c0618200d0e01153204020705030304030212180d08091816050a0f031d0d0201091b0503190503070b0403050a0305100e01060516080a050c070801 67
    0x2400d15038424008054016500841c0d0600f40c0c64038440d5203509111480d8420380d01604000c1d036500322001240c00030301a001014056528144061349003a856510342c1d0a041070300c003551420710070245603c41c083c400602200001030802c544803101d6141440d5281d03c15a01030700517200c0d01e2000488113512104032440d0801c2400002c0c4a042e0403003d01c00d034124030940461700c102051003040d40c1a202d03e0310030580e04042207800052401d00031003003098103a1004119007002402c0108054040d0481d10074031129025180010f0701e9450f000c030806d9900c0b8200c4894050b405807064159909605400c078200786401580c06072070f1500c4410a200724481c5030701ca6250103400411010300140000c20002c10864024019289080304a98039a4460181103400318040360002c1500d08080b035140c444c442c0d02c0b916601e9070300c26141c1000d0b1400c4440c0d40520410701003000c0003034001c0070070f400480d07044001544070003040d0700c0f05c00c1c102001e011904054410b16142c030803050005410801405508040d403 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 352466879 1250 352465629 352465649
    0x203010e130507060c020d1a040209070512060d02030c1f022401062006040b04031b03020619090c0b041409010f0e041703040308060415030c051207051002031c06 71
    0xc4d00d0110180d84a02800300241d030721806460f111000300e103140221000c1e00c11032030b19150507450540b04210203507101800c50801c101081c0092882c044020201a0300003900304e40306540841c3c2840021310785000c03480500e400184070800d01802a18a444d191a80c144980079981c3c800c0b040c04c00714191500419615600c0c1034083e00401c50f03540110f001c80c140421000b08101503c0301c003645145404804d0314100c0b4540148800c0009040d40083c00b00104e00a00c15506502140d544000b9580e180103030846014095041044075200c1d150750001c46842e5100c444a6801a0340e2410a242504540304003440411202404074140c50194643c4e4161001c1c200f40494090030025280c0000c00003c2c01100d9044400c049800c44110501c0134602c076500c265280c4005203415400e200030344440010250f070450300e48009000050b0051120800e0350f00c2070b01c00f40940d101c030450072850003095512650b0089500b5080c10100d40d8080002c003000000340d2140d40c040f00e400003100c000c443d00c41c42000c10303074 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 352468129 1250 352466879 352466893
    0x51503010e100803130e070305060618010509030f0f0d03020c0709150e150a0503070f09050916030506090f07060801090c020c0307170616050304080a0c0c090203010e1305 75
    0x1003480030064940001e600b1001e0680d003a1107405252031075015003110034036a03461100402120a09854981e441400c5250501c00ca00381040441c086001d0344845142e45260541600680d074820810344401c820024121a517031050041300c40d0320b900e010703500c907005401141088030030385009008071403d205810b402404414945403452000340b440803410a2440726400c03002034404821440207000c0c1401000030491414100308119001031180c2c8000d001b50031504c010044040320203d00d00441e951000c000c1402d65820158a050281c2c0941c0300543ca1a80f110220a10000049440c83303914410b044842c13505080000542d102074521800c030010b0640c1005200c9980240c01031220344459004503600800c0130000241407250580000d41003103414441141018810000c8076081140301003003401e90050f6081c01069844008d00281040c0c1e800030342c0089151241c031801e0005508111030b1144039440301c17500d1029600c288910101c001f604030100340718002480380422010740c040c00800301 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 352469379 1250 352468129 352468139
    0x60d141509071812030e12010905070b07030504080304170f1b061c06060815040504080d05090a0b0405011b08071e090509090a030201060b0a1209140f010902090105150301 75
    0x1d000200100a110900e0b803ca00198140d182c4240407162442501e603804040d01e04c0051194010618000c101c00d0382c1021b0040c00440d001060541c10354180182441c3d0b1140c29042c16901846a0703404103c09200024000810064000b0389030030038022072007952030500540c28182d590351075040d01401803540c0300784008403900d4804010a50310400794044d41c0c0080d6803004410490f000b0b54062400b00f0588800c100b01d0003180c260300c9042d0300307080781c1c00c00840c02c00d81c448500c01e000d5036042c11201c40d99a400b1800307410007003003181d1031140c1c0444030046601e030a00c4d289011303040c04c19050500c48205501500d121b40902d100a1085055030f0f1000308042624011452941c0d1104034601882855640482c1d02d031a00b02000f44680078250080014050300d103002401c41d803280d40442c10054050016502c1c0035031244ea0f00c1b014002540c000300f20350b28241416081c1a000d111800c119100b0b500ca4800b4030201234200071a12030084441c14296030b83da006103c05840303111010300340d4160030401400 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 352470629 1250 352469379 352469387
    0x51b0906070212100b0307060201020f120c1909180c0806090a021905040512030a020307290708060a080d050d0f0b060301030f200d0f060b060d14150907 67
    0x16186000500c01c030f10b21210955041e0400144840b800780c00c64449607040d0660a042010000408440c802185407190f003d5803000e5a0044a46d540010075489001c0703041042000d082e20301e20201c41e90408550100a070707000d49444090301c201011011020200350200200b44240c0200103100e4589451598902c4200018490010b205014090303003030114422440b0580784030b800905554036203540e00c03800c1408211141e40c24580160340c550040007100311099010042c0d44180e64424030400c1ca84140e81a502c440d413109801d9092006103c0041005481d0301c0f5480310b0007003030241c82c0c51220070388601005481e404000298408640304110817115494a07500c00100c903d200c40c4005400000f80c80014195072007030b4810fa55521440741d00c03005004080c20800c50300507a040002a9501c90200414180002c0c1000034004812942102c400d01c9003030341000c0025403000300011f517280303503103200783e8010085a0a0356041d1015400060340d110f06441e010204020b008141240640c2c03180c20840d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 352471879 1250 352470629 352470637
    0x20106060522031b05011715060304050708010f1a09010e130c03020d050a2003060601050a030f051008010c080c0403110a081209120c010c03030f0209060f030604051b0906 75
    0x1c102d1001190000205582001c0320500d00b05059150606524200c001410303d028800100c00c45681c150510500030440300301c10782e40820035107501b510382e81d45041450806110303901614165080c40c040714060200d40c1c0c002044810b85414250741d200c0d0395400d00421300000d015000180d50204041180312401410400f035280c03040890850043e03e83e070110300c1c0e00021f0b000c200c0341a88400203070402c000000c010b0111903038084030000b1180c0780c0b081c0060b43d10000a841c160611030000794041c41940310703810054054500078130038045070501521010642c0c1413403140a945520707110540c1c1c0e42601c180c60642c09000320071703940c0d0700741425625041d40642c44a00000d5010303100c01c4c00080c0410080c4128454090300440d400e49803007194050040004864001d020310360000c1000b070020741e030003440d40aa00e07500344c030300010401180400c01e0020f10a108900358403640c049401c0d04509100c0c80110f114030b05c00d80d0184056203503641c9a8510001900340d00490383c8003408003a4150a140c8050 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 352473129 1250 352471879 352471927
    0xa0b1e1608040e06040e0607021209010306081b1905030a060b0402130611011a0303030f090c030f0703140304060512060a0b120609062d150c0d020d0201060605 70
    0x10480c210020356808156a01c01e501442c42980c030f00d802c101052502d440740c94005004034015108515040038002d440e401807502c0c2103032100f800320340006645d210341d00c640098002c00085548060081840c1510300034100f02c0346200d007000307200d40d01350051500020000c641e0040c0c01000c0d0403c50b44e48907005007080c6000c8130380259081c0070046283c046443c1c0b050007400729031202d445241100b58a2801d440c05c0040702240c01c41c0000c20a0322607140001201e80c03082d580401c003400d070b4a032501070300d05000250911503898440c504915030010004030700c00341228854010b01c1d42c03c100c00361031143c480c0506c1c42602d002c0740040c0100240400e0f01c80545902c03060040c41303a640b81d500c4038186100c40d00410b001d000f5a0018104014841c1030a800980e00070804980c1400e20f00ca2007403034907803c81c2005406405482c00019240c400c0e480309020280a20600144c0c543c44000707003081c2d15540c1e5140500f5074014498001100d03581e50041c4034a100b0781d034495440d5481c1044e41c50440c0381c0038250700c0700 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 352474379 1250 352473129 352473157
    0x60f0b011e0e040f061203120203010b030103110f031002130f0e040b04031b060207021305010b030109111b0a050d05040807330305070e15160516060804020a0b1e 71
    0x1071307040e03416003407045002400c85074980c4003010400e41802400c0c03012a407019207107a403040005115003281c40050300e0440b0b038090058610b02d6803040c04030b540c0b40580c000141d014881c1c1c07840b001e1007000c41c0c2c018102078a008180045026503d00031400450701611606ea29108408042408240000181c950150080c1040d51014070b00082c03015225030300350300c140c5900d41c0c04100310701186400b450100a100882f1b40a1085506040000010f0302c0188940620b0941d2842d42c062240f07540c40507641d01d010000c0d20802c103541c0c100e1140e5141c117564403048425001e2805003090450240003550180d07083d0100030286141840615140b140452001146241c0c403846800c480e00710b10800030300350700e00b6554049010b0070141c1c009017502ca500d4075128410a40b94400400d080d07407140640d40f01480d02001c0410340702050802d981440700600c0d012a0400360240003140582c3c02c4801203004501c04d591210115a80f800a4201d42c010844480f00c0182c0502138005203217201c001a050034090001c03 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 352475629 1250 352474379 352474391
    0x3110d12050a030507020606090106030c1103070c0e0105150a18080a0c060f020d0c0b100e1302010207090c12050402030c03031b010b010203191416060f0b011e0e04 72
    0x21200d4210608000d030400040001601c002c2580d0306015080d0000c2c0130b0b0000301103901381180014130b0b504050040008060360b80c04487c203500c0c81102800729412220042e60b81c1c3d000390341410000c024050040f0504c8a00b040d00000d841e0a003000f1109124240980d05800c0407030011003102c01c07a58510703c00c060818001c0c0d0210f4062418081000780c1403040440016192600b04040e0114228600000641d04445078016403a41c003d50750080d155403008552015541d117054004840e02203401880740100c0420401066554228000050341d00036021612602d40e0f80c180542541c1c104d8072810002590007c00c03a041039076507004560043d1004003600c3c01010744201092071a0000140e142240318071205602c0204008c1c03180212012081c40074625048258036114000c41c440c2084404110b0000c4101d240f80101009944a80c1ca4002008500480c1c43c141000988010305040ca101464100200c0040d801b6440403510124200d040019441c0c803210300b6200d51040026054100d41c42d00c0b = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 352476879 1250 352475629 352475633
    0x6071b050a060c06140112020111030c031b0f0304051528230c1c03060504020a08011503050126011d07030312050f06060d0207140c1206060a03110d 65
    0x40d100070090b2102e6038480d0480d04003401c0610076030711440300409940e1610300052003812101c00c68110310680a00b00440070000d44800c2e1451482382141c035569601000c5008003000507041a510351403010743d8110b851980e41c14034215100d10507446020703840031100d040000c6d1500e2500107088011106d15070090401c05081412440c180d048131040e00050b152041041c51101c5200329403c0254120281800c00b00a003156030f03a22500b5810341100720000b045050499442038102c08003a05c0080d205544505101d00c002d00084402e000e40f5940403215180d200a00b072180c850581260368000110060201070180e0703040f494104c58649109542342c0284142c0c1c910a80d0858414035008402061200d1650a0051145012051900e0118101801e01590800c94810303a90051411201540d036072140780d241c10000c0c032902c540280001c5041c0342e41e601519000c589156104020343d520315070b00c2c045160301c80d180e101c00c0f2101c2d07a21000204c4144081060103400e0410700d40090607104a4151075 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 352478129 1250 352476879 352476889
    0x30e0c0406060306090e0601030b15150a020d030f05070c03050a05040f0e060315091b010c02120d11240c0405060403050102030403030c09030f0b06060d0609090c0807030206071b05 79
    0x50340110002c251501c100704581c80d02d80c840c00c0b0141c0002c9000d007c2a50440d0340f030440110010308400141c0d03000c16280305c159030b01c0034294a400780d030300003a0300e41d40c5200d0320b0040d448200101600700801e10703008480c118504079008040c840d02c41c0e9900d452000b00c003541c0c2031ba80ca80007a03c2040030030005010101c0c00b0340c21000700a0141c522801d4044031072800200301850411400710384001c5541c180c040c0400005c2c00145a98815440040998081c13400301c0100d51200943ca0080d46c07010300c0480b00c9894060200e6128900d410b135941c1ca8051072140c0705d469a855803c07401d0261a40f40d4203013040404165800c800f900600c4c5681120700c0c140d5a480040e886030042d82003038825075400000e01c0209601071260446d0740b852418003840b403500d1520b8500b40307d079111030b02404035485100050455941c250884100303560a071402c0050742d850b00b00680003461410003c8070408402034010460b40b0001901c2c0e030451b41d0060500f03240a4555031603031010058200340d01e103034000e10340c404248c590f90 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 352479379 1250 352478129 352478141
    0x111e101e0c05160f05121504060e101409062d0c0706020c250e040303021c020d0905060105030f1207030219060911040c080601030b2707080108010e030406030e0c04 72
    0x51228030714030354103000070403c0b055003800e540e01b56540880242d10181e108003a403194800d41200d000030708948040c0c0c043e030402c08a081e000e2100303032804280c60b12065480ca81d0900505e000821108150794004070303551220009070242d0210000d40c1c00f860f10b04803804604561280c1084240740c1800707a590785100903030300513020fa5801d41e00f0009052003189641146003e90f2207103510075440d5507142082d4002da20f603024001804260b000074051258100c0b04102410020300300100315950301243e48050001c000c0540112101d0207040000102840d00281410704c400021025003414642000d81c0c8135141d10002007102540a01c80400800f140304119120703070b0900900c40481c4455643c5424152682061200c1e07115a00c0c20050b40c0c002d030390008aaa0b8090400e00740080d141455100003081e000f5480c40d0105d215065480c050701c010680200580280c049803030720b801d2a62924209400d81d0394007815001d81d03610503c07042014610940080d0041d03000c00e019119135026442c0071405440d4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 352480629 1250 352479379 352479389
    0xa1103072a050f0d0203190605010504141014030a05030703050901090b070f031b0819030c090303140702010522060207050f010e040504111e101e0c0516 67
    0x24440380241541c81941800306a0062080703550051a810003000400307041d81403030b00e03c3c001c1c81c8a8081c0f2045480820501c514011313055111000780c03142d890104080c0ca42405558061070030320b840f000f121410003050078040c0c600300001d411000e0504503081c00160280b40860ba140c4581c0da40c2c080450001c0c0018a2041d00275030740c840c0d03144183d500141600c082c5a02200441d042002040b0110b2184484a00520313410300e080c15070580407807030104a03141c00307020140520030005104901c0388011070305010b47d5001900c091003c1b454212080d91911010302c40a00494094103040004001000003481c460f031050514a0905030000501480c2900501c00c211200c5401c204c05d20000360100880b0005200442d0543d201c050a00002040a20350400c000c0c00340d42c41d40c011900b04400695a01840280a84030040e41d42c00f8541c00303280e288100050601410031040c10b48103041c85011107000407800741101c2510b12441c190103c03540010b2000c2911240101000000405440442035000701 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 352481879 1250 352480629 352480643
    0x2090d0303051006080402030a06051f0b0705010605010e0307060f02031b0105040339060f1506081003110616060e0f25061b0f0c03060b0409080f0a110307 68
    0x3c41d08500b030342c8100301d16400c84010321118004010041c0c1e00050040d05a5a000c0030125440e1100d4460303603244240c0030980140341c00d003854041103042c0a500078108840c058402400b10a40d00e1006480804810050b15055040030206019460089222511200c007a2040b03d02c1c0c11040b400856210080c00040e50882e5143e509200031306174816443d00c20a4075400525000800c61100408000c1411001c3c100011250a41409021040e40441c104594601c02802a142080c0300c80714606114000d001c00700e4108008111041c00501000302520381c030411400610b4110b60420859400030303807a400342d01907030340710140014203140600041d104494004010244c0255001424000320707c200340105000102d001880d181c42469080031622142400f00449201d45881070800404520180c031042c401c8041030300700040a0b221008072806242d0420180f50f111381000240d482e164030250000000380060940c107003001c130090003000c1c52400c00500d9244071018030b80c1960800346045d903c1c0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 352483129 1250 352481879 352481881
    0xc1109040807050609010c0203191103030c0a0801080705030307080906090a0e01060f11071e090507020c0a0b030f0105060f0403020406032009070f03050a021b07050102010b0f1305090102090d030305 87
    0xf0800034035401c401240001c1c0003440c05060300039078a0144880180301415080c0340c2d0101603001e4510900720000c00c0081e240d481c036085c83e5018440d070000010070000b41d050000020b0703042011401c2010b603100107000d103140048a0701c440030681c0008503096442002040100310701d2759130954010050000216580710381d854100701500d81d022160201050044001d01d0250888000c60f852050700e10303000d01d0a0100d0030040f900e00145483c1e41000a00915010030321075490740000380707913a103d0802c61b00c0e21580c035240c441c400b10901042e140500842c1010340180103914118004e45010380c1c1188030b46091a54a40004050380d10940c4280e40900c001444a50900d06240ca030b10700e8601c090b105a152410326a10040612449034a410f003050750b03c001003030880c90250120f4031500c0348100400894200d8001e1261100c00d40d120b1980958642281c050311404e0561003074124440080c45405403280390001750006d8180205101c016550030068035141d0f68421440700803c5010760340004807 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 352484379 1250 352483129 352483133
    0x180b041a04110921011407020606100f08070e0102100908180d030206040b040203030d06170708010516050c01060e01061e03050c072603010816090203040c05010c1109040807 76
    0x44034a000074400781002d0030010008a51030701e0340c403e6003003008000500b05a40c010740c0310a00500840c00041d07420540d080c103002c00316900050540c09414211142c0c06800d01c5846c085d81d07903020034000500450042c60003d100e00780148a1001c5250040c01654416130306415601c0444410030012a0324407000311310b08070f811141c1058142404400c0c0d0f4148114120390320082d540c0e000c0140005d08921200703000a046440a0003514907102c0041030034070075140c03221421718101e071420590381e4440c07203400400640d41e88140102d030300510010014608540c0d035600c040f00c9590105152050564944000213010070b408209030340203018a90300c2c2018251599189410300104492800408d800c06041c4003003442c00404641020b603011401d9840c001111449a000401482443c202e210000c4000102d0520115504007900300718485810007030b4445400b00300b01d00094601500784080c400c028030241d401490200500b07801071600900e84400f120004040c10021030f0102c40040001c916582 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 352485629 1250 352484379 352484381
    0x50307180f0e250305100501060e030c0f130615051e0a08010b0304050c10020318031b04020a0219050c040e06070806100509030a05010504030216030c180b041a04 71
    0x201034120207042c0001c0c190400d0381c40e40d440e0b811030460340a16080d91080180080800408011640081644c51000403000800d006002c2449040c01041030b07642c03400340f00c3c40c011420100900b002080080c0d802c0400040c040038031072103014100010759034000498804030208940d00c00c040c003903454680d1107038800641e24407000c071400ca500714520180040072103207030462040c0d41503500c0148503a449640341d090580c03404600303001030382e008003081c2000c820103070380032008000c01c403004c040340122040b003402030560310311030030059101424802030307064aa4078154008001030503440c41151801000c42050b6001e482503a5021a5983c2c001c41448400d400c0902070071510004200c003400301031402c141d0240c103845004000d94400c2070030600002c1400e0081042c2d9100010150443c1d2814800d031a0080c020081a2000d50161240200c2c4141d00d00c0700b6000c03001a2a8011886c1500750324082501860310916016000c41e15212000c61b9490303195403142100c40c203404652503c0c3c10004d102484 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 352486879 1250 352485629 352485641
    0x4050f070f02120904050709030b2406040303050d0207050f19170313060905070807090e10110d0b0a0e1e010906050607110f040203040f03030f14071805030718 70
    0x1c4195003120742c1d20f10400c04803000303940440c9800d440c0451785a541c0c941c22100e40f00e01d500010100c811344018810310620600701403a0070250f894a59035500c0316078042101a001c0d501c0010300081042120b603a594400d5005404803912071000c131014502a18100c6040084000400c600100284d0b4a00c0c14000c40c6c96a00c214032074000310092031070800c0340d16402c1e1086c094001620f082d846942200811008100c000f00806125040d070741030680352503045001d0800301e41d1041440c41003442640c0f01204500c207841510310340b0790000740f0781110881d070742010b44201c0000c550300004e42c0c00005a1800722540d02d41c0f040d00d144251300215a0345041410511006070421800e03a803500c071060000b510744104890115420010030700324070b0708180000394410005805603410034008003c0c8020001e10354041c8080500ca40c90038069040040c3c009003c03104510010641d13254844041031210740070301803222011943c1000028100e0b1282d000ca0320300032095202d004180000100f9401303805040c4111 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 352488129 1250 352486879 352486907
    0x4030206071e0e190b180a0e0f0a1b08090d0207060801050d050c1309120c021c0807020909070f0e010e27070608070914030604150b04050f07 62
    0x12810002250285141000302404604240840f1821621156403543c0680a4002c12440000035842d00c03200d07000b4143d00440001088a10011682d84007464a003207100140c422540f038802e11550781d40030004071004080c4c60800c0300f680c0e50b080004080750002d000e0720700c1001516a61464180600c0d43c40c80c3c1440480020215000041c080c41002c1d40110f110341100c07822641030b50000c0f560708009090440100401c5d5024010410300542c2c0c4110344c00403078226000718003410301000d041c00103507000d50321140001e60003204444088980403007840500f110300d0166407202d04165070f582c0490242203080d82e0544c2240d2260104000c2030300d0000d0088083d000444030104a0751400c402c0d00c030a0031001d01076500a02c00c084606c40c0d02451400c8100c403109000342240c10f501e130f0707600004c0c0c4500401d40b000c0340000d01218004c243d02000d00f18190a803100900180300300e990b01c1e1902b207612201900000381c410348503141250f80f80e445000d02c1b03018103084076513102c01c2c2c1000f08018014210881c91 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 352489379 1250 352488129 352488137
    0x409060303080612120a020118050a0506090f06040210090e04110a060e010e06031b0d050a1d0a060b041503050f0f0d09090506030a0804090b1002031806070c09140403020607 76
    0x140c000307240860352403045c107400c40d2013645840007418282d01502400c61100d2203905400b003100706011000500403201c2c1d011748140c84158852100107a119607020316503a100350b002c3e0000c100107060031114120201154541101c0c01d039201c0301d403500d420105480c10ba03041d100b0019050b09a10f03003001107d00410382814200c40200c00f1380000f0b01003451040c040c0f03214101c08000100010b00035628105042e40b80181c556603502c4c422000c400800060b240b148400340341c5101040380340e0f2418190f00c000f180b500014880c0710b000b40e48800160504140c0d16401a880d2000c4640c2c0c8000ca9003c20084c1d88994040c0c0b02070b400c141c85907450900e9690229015501403101150f082d5006070801c1e090b10104000443c06a5444c2d01081c0b070b085228000401200000400080441040c0c1c007080040c42e0490b07160400b03101c1b043c422070b42d82c010703000c44802990030340700d8105903454844001d0101601c191505040359a0303c072110001c072044050001210408241048101541808001d500400e5414 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 352490629 1250 352489379 352489399
    0x5040201030c090602120d02040e1305011404021f02010b04020f0c0613080304081615060918120e0415150f1803030807020109021320040b090d030c050304090603030806 74
    0xf00c002d64456a43c1d201c0c0010a40010341c4c0744501f00c840d011500903248a1641c10814148a000300000a00c007000a981039440c16203603000390794130740800714019030b0018691004020300303146094034481740340c00b035500750b40d81d40c0ea1a00064417140090040320040302003050f11910100d0409040820040164860342c0080007020005003545050701e80054104683c0c079101c20b0210400c041e1000c45a00141c54060709140c81c6c580c555540c1c00c5402034031a00d240c24819850b00510301e911800800340000e040c60102c0d5104e400c3e461140302d20882c01400104007045421050141120341c0c1642e03002030003100e15503c01c40059540000154192402c145481c011b080e4070321103000018004c500009080159010200300707a213200f50041d0100c0d5030020202861403541454101c02400001040b2454500c49001840f4900310101901d0840d20f00a00c018034003440d0344104a4090064101101400307001140030f400702c0c1c0c0820140c0050149403500054582c08d600380604280d8000340074911820f1401 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 352491879 1250 352490629 352490639
    0xf09050304081014180a0f0c17030c0c1e09010f090c11030f0f0d05090c12010c050304170c03030114030106050d081602150d0f050a020c0a080702010c140105040201030c09 75
    0x1425207a031100e05d0304042100603901917482410618110b402070410b00c80100e0031414010440d0f6a501140c144843c0100300080301048542c503070180310403000c000e41014150f8103540c00e2807008034600148140c089207104482c580040c1030f901c0c007a0000300180a081a00303020340032240c4a140c201c5d149034209580101484030b5070300e0f41c900c9081c1c445100c503040416000700c40c40c0c00d0800d403141110081c0c400e0000e4504021724555410384a4881485407020a41c2c0e40718004040c4600184140c0300d44da014555a1942c440030f00b40d078501c03183d09001034420000490000024009036000e003003211021854040d01e08109400c3d11000d4100030700c02c5807070800e50310016483d50115021000c0b0888520400d40c89400091480302c417010000d00c1da12070001f0070a10a8400707620820790705004e0b107c100038a40341c403602d540c1207014500c0c00c4240c543c01007041c5d4011900e2039010381115441458151000c07489680c3e50b81c0c41e61422103007556280c1d100e0051108540c0c0600a1580d0107400d8607002c9060743ca80 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 352493129 1250 352491879 352491911
    0x23150405010305190312060902070c060509060f03090c120723100f0905030304060c03031401030203210f0403030807020f06070815010c08030408070b0c03010f030b06040f090503040810 81
    0x444030350601e544c5021a0341054060070388205180e090540c20402240d8400a900203507002d41702c12551051000e10119455008030140c800c640300240c51113082001c1540003400c0d44d8400390003804d10303118443d11654942c2c1c4005a000e0301c4a603410141504c9494100c1c480242114030f50038460a50402c007144013151aa002e185010100c146400d000c0d420800e0000c6d140f0706219005039405000028001c80c0740c0f900300c669410340038031070341d42001441000784025070f580310203010003507158100d40c45501103030101d4001038a107902c180184501c1d06000b0880c3c0a40d1b81c2c815801140806c2c1948200880c03a50140800001c2400034000f41c06d0900d040c1c7d00c000e002d08002040c000c0c0000000c000350240d80d1084000402941d4088030060b5a030500f07040c540c403070b900031f003004a807104944800034030524030141c03d4138104c810120304594540c2c1035585040c04510020042d42c0c210740c0d2600418010340d00350003480d0950f402a006540c0e030340e040201080c103000e401881450130360704268510a0b000c240c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 352494379 1250 352493129 352493143
    0x1090902063c19050d1e05090c030a05030f22030f02010e010c050d1103090909150105060c061306090807120f05131401020a0512130504050f060f030123150405010305 73
    0x104d260a80d40c58005111060040c64940810040d60000c0c04092014600b103610003400380c20b072041101c000b040100c2c10180e40326800100200740e0f4100340590b40d0111165800f400079070050410000344100507090311104003226920075104007046021910955070400c000d0b80f1900028a0600302c0700409480700c50b910302c9001200703010806084a501c5c030250052040e5040c40000070503070034880c100404202d940d108207140c010001c800840001486d031500d0341c11108000d580c10301401d02e90740c0d007042140c108088036000340c1c1d10700d4032a0b56140c00100200001c0490750320a1303c0c00c0c14042c0030010010104210030102d0400d000b030812240c0041030b0302e40b18000449440410144004100341c00403810a06c0e0072800030a0b901c1210590704d841c40704035010b448245110b01f00103481541d10700802083d503c2c16240c0d105541c20540209145080003080c45210710301c00340021076038041050f603945981c91100080810242090180109004441460f4007980f030700315824484d40d4150b496241d19005 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 352495629 1250 352494379 352494427
    0x150f02121303091814090a051b010504030213050f1005060f0f1603110c0103090b0105040b220b180606030c0a0c060501030807230601090902063c 64
    0x805941c12070070140301c2c0b0640400351030038401041140c194000d120001d071041080c0400117840c1e00000600c070f017000280307517104950002c0051984002c05d0040401c0174054503d02c40c100b04003088003001589445c5152440c01c2d1400da40003c4602c8c04010307840b10f5140c0a85035106091440604100584d14030341510342c08104200516130710211440412007074171488030485458101e041103d0203041d00090450300100b41041518210403001004404450300d0050052950380c0340f1005012500786640820030560000e001a803250120140d185000400e1182a40d80291108402c080b58201400d803444441010035403640300e418900e00044590100400810b924180481c00300302c020310400c0c0740e43c10650021020401941c40c1d05040e243c03a07000c100b003514141c125000480308203040720f00341d032807441a8201424169080044a00203841154820f030fa22080c28026010507d20b0801c480c15000e024026803880c007942d200c0071b010589000c1040503044001403000301c45003860a0341e00d4801107 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 352496879 1250 352495629 352495651
    0x2030a0e040b09040c03050607030e030a0e060c0718061a0403030507020d0804080d1e08040b06040f02030a02280210020708270a0f0302030a0209150d150f0212 70
    0x200858018000414080c0d40140b1580c01c0c4004c5c016120703c034009482c054003d658056a0700c803800e6040c0c0d680c0c5100d102150f4800c121130001c040c42000000342420000b41810314100301d03251b0305450496036400400180c080034a01d85100c0c40c4607c01c01008100c0c10300510001c103d85803420308280a2440050140040010034808541c0c07411754503031503140c2c001ea102d901d40786c650304190f603610080228000866049408000c4003941ca0a07001c07070b500c502d50341d41030942d6556600e00607000c8010300090740003512882070180c140042d0016522030042d0000040e1141c8170315400340e00d200c8000b020440c0014100043c0c4020540c00b01c0c1d003540744a128540541e861800d0b141140803881500204c2135071250041e41c503815003441442009151508403080314540c2d85030402180d001c0b1042c40000d606501c50720100e00142007241c40c082e0310011040d0304030001d00030300b400300f49002900340080b5100300c494115543d020b455441014064a00c00000b1400c0c500092100780d521030300501103900c0e034 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 352498129 1250 352496879 352496897
    0x2003061303020604110a150201020909010b0301030503191e03150e04030801090504111201022a03090111070302091305010f200c012d0b0306070e01050a0c05060112150c02030a 77
    0x82c2c4c840421150042c141554141c47c03144c59248001d000350030070500d05204d00c0400340001628624003003a241602c0e00309001e50320300203a091303010780a404500c00a9041c0b0101d000012110380d08502c00c902300c1083d0b51804184240c180ca00e20420300501c1e003000c29200c400c8814400440d070710031100c6040d95000040000c0980359401c1551480a4200000340d004981d43c210030414007064000c0c09913034101404141d06800c031480f00010038583c21044c80b070705034000e0001030143d43c46440c884860500203402c0ea801241c41e86c0200d0542c00045400c40545c1c40c0380385100080100911810030050035400c410440001d41c1144001445c0720600b41801101011818030705401d020341c001080e0042c0580a2031030142811b9401084600e4181c042e1103d62038000c462809080209000f403040c540b590ba800100c1d294040190750341c2e0801b1042008000e85c0341c21000c0020810811030b806001c020715070050f0302509107400e80745040240104100300c0d05040380b01c00c405800100b078a0040c0c581c0c6c1007620072 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 352499379 1250 352498129 352498163
    0x120106140c0303070e0405130206090f010905060a080910090b0403050f0c0f010c030f02180d0507030c030501050411030c030d03050703020d05180c0d1109132003061303020604 77
    0xea0300828a148055000010511940a03000812075440032816601481203540300a60740f00712111000019420070300030801e494151a01c0b00c08a40c0c7d051050401c0219240c460012408540181d195100820405001d20004d000308004440c04001c01a5003400314400949d9078000204001c1c1006040c44030102d043c40300401488195000810906c048800c005505000140070300440c01131800401c0c0b80c0b814109140e44a8001c544013010a50240020340c0e80010521200104a400903140c03801034401c0800051074414101c80254083c4001140c0c0e41050308000700360806d40d0403aa4030952104601d81002d8401180c500c1e510620b03400e00242640e80c100c400e6000e031182c988204240f5103401c040102d04416140c0c1012040701c4030003103c0e00030203000180000c6030001e40025003034005038a074003c854601401481d82c03040710300d60501c03140607140c1d42c0c0c1203607404150b4071100f0380c0142c0c03200c0491600703040003003e03480440c6400d100003018240d280a5201c00010308040c0c0b14401c80c00352181 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 352500629 1250 352499379 352499417
    0x20f0103020c1c1e05090f0f120106320d0201091203121104050105042c1305150606090906040605030a080a020105071e030b0a09020f040602070506120106 68
    0x51622206425160038103661400f00c0c0341c141c903401c05a4085443c0e03600090b009151303041116085a403907121507180081c004104407460704100405944032619250b281003688907600d4001d10684040000b080050807c81c40705817090007001d400d40300340408007690018050303881518a4000d003d850740d03184821180012511040743d50013081c0b00b00012103000042651152012000400c070920401034220710b85c00354000c0303105521a0707900088040c04180000200c0300c0c880c44009407012600c01e0494014080c0054034030044400180c00d032a20000c9009014080c400300e60075080c009561a524035107800010702074003810702401e02039440310340090050348840d40801c02401e0014100c03948240a890b102c00640d0105105030015400d02e800300c0d05290144030349030105e4600d11a001c4010f103c1c4207044000702039414599074450115980001d03500e01e01e02c01840c12580840c80c6c2ca82d21400c0030000307484d001e6203070b01c100d008600401c00301005210141c002c40c1503490b28904040d105084807902c103 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 352501879 1250 352500629 352500637
    0xe0409020907090518130311070f1401032f0915030a1506030921121e060807030809060c070308030c07021509130e0307080d061e12020f010302 63
    0x250003603080c4082c01a525000110201200d00413128900116558512071961a1054940c220f0700e0300540300300d000180c065038010310b52458401c110341c8026aa00064184805103500402800c01c200c2014180c959050050b0007141da180720030710300034090740e200c6403d0b1500243c0f14085116000710301075181e9030300c6403024256001003403511512400d1000c80b070360090010504025510725a240001407141c040d001d500240c0d50005c1840b284001d440700d0302400e21111007100780410408080021751254244110001280380a00e50700f0458102c264040c225801074104400940c0110020000075004104565480c80c0560303100c1c0d129104030045600d000c107a0f8100401e00000030041100044651010b880b040b8000c03103908488049503071602402d803248800564002c54a4030490391080d0494025020f15102481107074607196442d00c0301c1c9210741194440748081e45e1200020010b4441d2100c00342130184014950300c0c0303818a0f00311a0b094015032420002c0c020503141c116150a42c0c0644d0582d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 352503129 1250 352501879 352501883
    0x15021002040b0d0501150e010309060b040e0a060f11091306030c1701051003051b190b0c0c03030f07110307050603040b0402100e21030f07030207060905041103010302010e0409 77
    0x1591507588030440041d41d5004007240030181031400c8000281400440203000181c00141c0300ca51070441c4c00801140680314040c41503c0361600c586030a0721a8840c2c0c42900b82c0c3c8103809020b03221660340d0b85081c4c015602d0810307001c100a400d10850590f50307041082100c14040044410344003090204000380040e003030704d52000d030211075075134000158400040088004001000001c002e941d540c001500310510003400050305079070000f00504402da4a400402c0c02e85c44008105004600402d80d10b9410748000e90000c910300400414aa10700810400200302c246038100d01550500c0ca9141d101e64090107880e8016006802c0d00d50f40c0c4541c0e480a1140c1c074003620000d040c06503249041c3c1095684050140c2d0228080c0910203000c2d46003c0c460f020401a03c0d600800b09800554008840e00d031028030f9555500326400100101480d43c04148020030403c0e200c1c1d00502443c0e0701e4190302038001c01c2a584440c0c020750400300c00ca25005c8035030307045905481d82401e0120407403050342e0105004240040c40 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 352504379 1250 352503129 352503131
    0x9031e03150d2d0c060201110304150f0524040504081608040902070327050913020102010f1a01021209030a0305030a0b03070f090b18010b07050f060708060109051207150210 76
    0x8002980203580e5180c074905030040308004c200c03550300e580481c221040040d0080000c0b100388007090002e02145601d140300d240d5030501080b4450364a0300b60742120700542c0c01138100b6104100400340703244015484900300c802150108090300e019120b002c0c4030301c140e01d5450a05940034100d98200b116001c1518040e095a00e401c54031600c551501819150203940e00055512002c00c80300c044100340c05081c801e07141d0241410b00705884034881821000d104c0f038030403810b40d52502480030704000d5512484222090701216420307400b1911002a08181451040c40840d100802c100341a90b100050301011280d8103241440c0d50f0b5072100c244000421038280003540c18003030307003600040ba400e00c00c21080035620301c03100030000440e200781085030300c400c0c1444002c540300034400100200b620070703c080d000c05030003942502d420740d02c0a02101d05226007240c020010070560303401c0c824556400b10042d0060f00301a20600702040198030741c250366041d2485242c1c5e00c2c0380420561035030380d0b10901001c403140501c0c1034 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 352505629 1250 352504379 352504433
    0x7080405041104150503040209090616030b012c0a0e04080a05030604140405060703050109061d0901110c010e0c0d03050d050c0d0204091b0504060801290309031e03150d 74
    0x4c01891580156000d138412040301001c549018004240d040c01140880200c00d5680312140080c0c0160005103d040d0500c664001e10000080342c42c0e416242503d41480c3c20000e00301e01004104c0301c1e410b00d410260241c40035034200000121090212403008403d401c09a40300d03a41c1c040060027a040e002d0500010b40203400901c804c0040000c0c1480c0510b440d44c60600c41d503a21000300c44200c07641d92140001e0880c50004e19034001060301401500030300998000719140d010b60019604a5005c0580043c06a551b07145202c0940da0602004001d00f0341111122a602d43d581c400500364000d40088441c0c041c3c0e5100862010380304041265106076441805548542d60380741d210006100c445210865501e192191380c50a40c03040c8211400c0c2c40700e68440715602c1e4201081201040c0071044d1070501103c6500c51407000c880920080c1d4400c5460710000c613942d9552821246d13036066000d10310f800743d0401703205015490100c000140c402110540e5004481071003070608043e801d0081e40e1080195800742 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 352506879 1250 352505629 352505669
    0x204061d04030305090f030d05420303070c140409021309050105011a030106050a0507050312071205040c12111003060302011b08030f0405030909070207090e0307080405041104 77
    0xa040e45100c0d90103602e081200d9650340d00750544500c182c03c074a11140e0006c1080c244e486403240d029540000030b19603412801450519a02c3e241d80050301500c40c882d202e03404442d820741c0c40d20202d119405c03082d0042c50501009568030704204065005546c00c0c80080c1007844955256644018211038005160900c0115088100d0000382441e81080d03401d5400c01c800403807000c01c1d070302e5402100c060241001b495a881c04004130341a0300500500300c1000420030201010503420005891041710b2103030220f400781401c01001e02620500101c84040c2400c2c00c0403c400705175015145802c5580c0184180f035065030703501c4c9c40340b01c402103012000c0c0c0c071201104181209650691001c004d50b403003070301c0d0244842443c1c86050b064a2040e0300c0101000020400034076242c01c13070080f0780c1c0c000b8428011242000300e88000128420300844001c0010b03480240c3c1041140c41c1401001c2c080301200000e0b618105003502c0303006041c400c41c01980d00803902e8083c2540071050100c00c5030010580440d11181504240d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 352508129 1250 352506879 352506929
    0x30d170109020a120c120b0607020312090307030b0c0d0506041a102d030b0603040f03030c110d030f0b0103090b15010c020306010b0406021b03061501090f09060821040b07020406 78
    0x14803002081d01c0c0c9451fa02d0b0b803845c144802141e01b02c503002002410f038000c0f40e8000e41a80d40c4910611391f018003455600200062020207038034003c6014521054480480360002d00880f1030003012913115a05196010360000c0092307407100e0140006076141d0306050f10b108415504030544c0c04044040c054010405142003000c80b600c0d0021208540e4140540c40b80c540c10002c20740001d5a01a200307207442c004080000e4000c0e4002c0f10201140e082c441035a1900c40e1115041281c80000c240c04a03486d4812103003500d51510482c031b1040f0003401c04210740b031a0794803070054000d002005903010b0500c180f4400f4040c1c0c080c94040703e00030b600404176640d968545d03543c650385422074490040580700d0f43d0300000d8905000700e240345410074084d0003442e4a640d2823400340080780d4185100da0601841d0640032489051045400300540300e038400101d48586800b8840e490181c24001102074aa82203081600c074924020407682280c1c4841d02c8240c071a005400040c00808041e48400500c003120f211090724075540e = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 352509379 1250 352508129 352508147
    0x40b04081501081f050a0906050c190212120a09020a03050a171801030c12051503150106021207050709052d070206160509030105070905030d170109020a120c 69
    0x800c40030700005903600e090f607981c3d034414280c03c25244070251030000c0310f85106901c502d6000304018404500014583c4036502164416141c1c46403600740052680c00328500710400d41c4064840e44014400e500c1001111040b5005000c0240040d05400d404507030b14000b5500101d0100e90014107900c0300726a2850420343d10070202c841121240c4440884454807888042070724018403d058100c0700d1084c490380110010401c084558091083c40d2060b004a03403864810244554181210102016000406c1502c1c00d202665400d20300084000184021a030200784898004401440140c0b540c8251800c5400c00c43daa40000d04914070300020807031100b1000414442a08410031124040f50054200e0105401c0403510403001d03078000008112101d4250180070b20f012010300e446410442c100c0d002a00f500c1094131008001344070080180711600d814000c83d03c42242074248441022007881030410101e40510800030495070100700008624007a2148042001143d0000c2100c0300030390764082c4c80103c1c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 352510629 1250 352509379 352509403
    0x20d0c060e1c1413050103181505060a24180801020708030114030f0601051e060d06083a0c060c030507110f1005090a0c0311030c0418060908040b0408 66
    0x14030074400880d0f11040c1150502c001c5074481214090503c40150040c044a05900c2021040c031071200000c40c0f0701000f0500b142032440800f03c0d05007010300820514650bd50000e4580300707402440e03850483d00708940305150320345a042581040c0d110b00d02c0c884030180c4c9a4052900781d40002599403c202036400154184c849000b07400740420889401d041d620001c170900c04107942d10920060001e07141500034010194440003928942c82d26030004920250040c0150f0050b0b80d403204801d02542d10103228500a901c49021542c2c0760300c522506035603100300e078014841451003c5007000c1c8102e5114a0903540f9082d0407400074468a212114024020803003200c4010005032845400d2124040c0450824500010140244031072100361207440000c04000c1d001c0f00d090301c0751284000006406083d403000850080080e2084a2607100c141803c0c4102c911105119525200c1203003994500a10a0841a03801000002d03410585181041d00d07441190000802c1681c08140000e00000025421089035 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 352511879 1250 352510629 352510637
    0x50412210906090611031c06080706020c0f010503090607030b0402090604270507020d1107030215030103030e090f0103061d061f081b0d060209130209030d0f020d0c060e1c 75
    0x40d03561340080b600c1e0600d50070035400a403c00c1000f01f00e8030368090400e00d032098500c00c1c001040c0d03a51b40403491402c1260340c00400540c2002d00724016a281510711007126210a0914628603c1e00035403507521514000e001109040d41d03085004040c0c4c9465040e03071b514600251403a9512600d41e4180309185850b90301104005103403021a4082d00ea450186c02d000762016001082c041362105030903241c001011803203030740d284640038002001d44d5540d060103910140090304c6956075411420001c2c208001610107501500c02c8200703200900d4414120381d81145d402150024900720070813483c003070040b801c175004209803003000709220b03c214107800c0c0c82c030780804403034640b5202a554600b1561500b9121840a0865103210400c0c945030811420400380a4401d00b0010b1500a10200003407040c1e4209240a01c0d03240d002c160642641401c1040e02c1280c00d4130308018007041c1c0c581074029980c0e404015004d04001c0c020501c1c00411040f6040104c1c40361103e401d54640321841d1400c2d035800c2407144a50070000b = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 352513129 1250 352511879 352511897
    0x2c04111306080118050304331e0504060c020f0409060c0e030d03051b09010915020601090c0e0a3006020306040c0801120803181e010c030b01050412210906 68
    0x4040341001d80c0f43c0caa005c0302940c01c051400c0c555003848031502c040c0c864000b5124400c400c0d0b034001c3c1760503005081580c0e107407a12404000c5966055940800d101c450920504100030710402d5004003035601c0035541142c62400704030100d808140a49010f80c4d00624044c20b0003241203005812080402c02d0744c1c025012a0a165400a4101d0680d982921360301c020b21036080d40d0300991190400184010001810081100c550b180c680c0528004c003001e0380801600140014008240907029803136000403580f80c00700c00d1840346000100d42c041c1502c1032070f0002c500515180b0010b249281207403510445510043c40100d058149040070398000c903451441140350942c000c60140c0a134803102e0580f49901c14440071000956695000c6510142c00c89030000c1030700040194a403810841149030825060710224101c0003001c01d1030a42e002180381406150400345050601c0c0da02c0f40559044800c0d48180520000c80c600304a00c01403c10700034960041c903040303a0743e50415000b4240404403180c0e41d85004207 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 352514379 1250 352513129 352513151
    0xb03010f0605060f030702030c06040506040209060402030f070c0203160902070204050907080a0303090302100c0203090a060e010c031b02090c130b040b0a030b0103061e030501062c041113060801 85
    0x8960990007020f6015009100d09801c4050034005164072515500460749031005031071800345000350482d030480b204c0e03012204200442c00c0c02d00b44142c01c0314081d2415811400c250841e2441e50000510a40400060300402415980c040003404440d42c2c1d020700c000501d548034130001c4080d5000800580c019030030240880e520140c000340500860f90304401510389a20300303541c200c001d0003014806504502c0340c81c0c01c62210342000e1142c18003002454000310794400c3c04000f88054580d090780413205020081d0b5401e4640d98200c140c040d4110381c54540f40d00045401004481c0028441c200a0340107000c4108112022504400402c200e0160070007500b0800d40c1d41c20f100290f4401d50291000320b07041448004103036800b82d0807109100205060116000d0744034010b10058055030140003800c0345010750104107101c1d0078030034140500f100079561011840080d1103070300c1541c5403100d501c80140c1218001024400c41941080e131180d40101044429103c0c54024000340610b030255401039403902c141080 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 352515629 1250 352514379 352514381
    0x40222020a02100506061602091308030c0301090b03010504030f0f11030a0c03120501030201230915030610140304172b0f0903092601090506070e03070e010b0307090510030b03010f 79
    0xb5145900500c0c524040101d542404402788001d07014810b00190b0325100d900041806010354401c01e0380c002c4080c0c4940c941030841d41543c0100350b9041c048c1e4507000c24400070030350181c0681c02c0c658141c14a8080e0b548013403c01c40d4081d0003c0003100700c601001c82c40d86051980314414036010b0f4080e5940034240da0612040c281210707000e102c02800b15030350350711003440a00c2c03c1d0f0890b410700214103c01410210214007041c0c42c2d0900091411030204000100070107443c2811240313011000300d141c1400382201280c2c45282034030010304068407071361440b4100040e80d4481d0044540e500003002590710181e03810388002001405015002c045142481d181d80e141e604148640e01c000c03074143c2d0705e60000c0d5240c04078441005014041c0360243e07440501010301c0d20842402041d8010b841007000301082e10300396000400b4980c1000190380f0940122104110000d0900d0210f41902c102c0c600721982d030346502500b503404031100c0d486687c01510b24558035144540681c4007907826a0181d0007480b820a00040c81c1e8 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 352516879 1250 352515629 352515637
    0x93b070e040b010b130501080727030b1003080f07230a03021216060c05041d1608070f08070201061703071b050310021606110301080f0303040209040222020a0210050606 74
    0x3212a0406071410021b40d0302c11019545c1085c0c541c1040040b4ac0040c51144840105440314260b480d060140204204184252045c1d4401c140840d00c080d598115a122003051181001d6840d0082000c5107031030034041240c9604a01e40c001500078006454200d0b02280c440c0c4800d40181c001d80200711074180b5040800f021240c504016006159001c92039644505c004c003003240c2074a0801c032050202049030078004c207480e0350101003c641140145001e0001d600101d01400103d402c0207940c1e401c0c80002c2e604404d41e0364800c05581021030301b0b9a03841104900508080c1c4c40b11740d441c0c0c0b004210051010021001348101802400d09041c9028401314071114a0111b01ca55a0194810a608041c1c076086601801200c1941c5100070303102c80081d10360b00103403041a204400400f800100411a51200308100d040600c141b20295045180540001d003011000800103070207032501100180b03004441017911040d00c00c0c3e41d40c003103450311a4404004d44d291412000c0b00c0030f20f46000d0220f2070a207840c01c191 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 352517985 1106 352516879 352516897
    0x602010209130b01020a0f050a0b01060c02100c030807120e0304172e090515070915020f0a06270b0f01093b070e040b010b 54
    0x3041000c9011220316180242c0c0f1800341e600400c0900a041d0032006100344622207090041c07c0c2804824000c0c81c0201200001c110709801c0305181c1c151a00954110f138203d018000259480444140080d001c60000700000310114030425114441d401c2180000c81c6030b85412608a00d107410a400a01c0920115580000b841d4410422049042600440d4000f4542c07004030100704904a0081c03101e015481c1d40e0250180305007000b48105c01c0340340740700c0c2c855a0714180b98024620350071401454402120280e40b202d0441c0f00040c03c59074003018001900d850740440e80d906009203a4254003028001204440001542d4194101c4141e81d024400182a80c40c150f14404c0c064101600180d03001c074500404022003d00d0b04c2e900d0030030310403030240380e802e00030a204106a255510700351008241c41011004030741c402108840038081d511601c1d500070240d0702c4622a8929000d21505 = true := by decide +kernel

theorem cover : BRFrame.Cov 352338129 352517985 := by
  have h0 := BRFrame.cov_init 352338129
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352338129 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 352338129 ≤ n) (h2 : n < 352517985) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
