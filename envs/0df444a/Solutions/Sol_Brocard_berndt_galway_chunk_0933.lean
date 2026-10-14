-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0933
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:03:35.079984+00:00
-- url     : https://prove2.me/submissions/14e714d6-7724-49b0-965c-1011687909fb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 167625899 ≤ n < 167805755 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 167627149 1250 167625899 167625901
    0x30a0204021b151006050702030615031f0207140303070c0b07200706080108010c050409090c120308150d080702010c020a050607030309150e06040305090604030b150f2403 75
    0x1844181901c2d80c41021905446641d210160440644000510804030410307401341c01c40d1151001c89440c440e6050284d41607015001280803100035000d80708181c00004e08641c81c5110040f26440c5d039040b090b00c2c4810741903010510009005800340318a408041600c007952075403404500c06070140780c14650240c4170810318000280c090740209401003103004964500d2460400070800745072758805501032280010510800019032040501502107000c2094540608150600c01d61a00400600300b05032030b9400000400200540c20b0f9034000c3c4614040d82c1c0d40d40c900c5ca08000c1c81080d9450760015907004010907008600420281d00c2600ca5403682468200c042c40207600019000d4055a00800d81c032407400070b401c10406800d80d010306146446101c000480ad03426442240440d4100000c0b445541c0112000a000a1141000f400900e01c02040c440c109038494517044488402204c4003504030707902103c002528035081e004095483c000701e80500c0212507020200303006900f181c65101c500e640c080 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 167628399 1250 167627149 167627167
    0x1061e02030d050a0219030b15210708010303030b01263619020918030d15030201020f161701060b070c180e060f04211814030a020402 59
    0x841111400b4003140e80a201c14102201080d00a40c481c6800c5511038040381c041c0f00c061400f9004440c050640184064900070340300c00143e04540c40200a08104060303540000c00b010700c050700803801005142c0c2d42c2032996065280160031941c08040780c9040c0b0100822002441d20f0070042140703042e0b031140424525840309000e015601410b10600882d07004088188080350003030040f498185007410707049a00f004030540c1c1c0030b0761017192000c001e9089060540020300701030031442001c280c00068012240780c40d500c051503004075289401f11441e504515403040096603810008043e41d8040d41c1c020744001154510300c40c2010400d4841e0220f2004440a0298600c0c002c1d84000c004010114100795600300c50320742102c02c21040c0c044d11919000204990407000e00302c0c451800780318900e8004100d55100c80d042401080310082c0700700d410380c00c0721103c040031007145c5405a9030300301503440d241081c0c584189c03c040c40d040780303400142050302e20350200412a90001202c08103140c0655006a58290f0707c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 167629649 1250 167628399 167628403
    0x9010201090b0f10050f060f030c040306052404140a180209010f0f060215010e0a0912110d020a0b06150712020f01060905041a1906080c040501080601061e02 69
    0xc1e00140021001900300241054070350001440382001c46050140240c8913000c02c15035410802000703810410501400c414401d102c40215002098001d10a00701b42c0d6035544c04c025603c0c12540907006400c0c00c1e034000302e000706070080e44d052580121030501c140250300c81c4004450300000d100110003515404100c0040c1070785000f16141a4010b00660440d6031a00781421818000344100c00c00e004107503000250051012038409101c02c101c03072202c0460f034a0401c800d40d4000024140c408a1a80c03034014500084d412201c81881c4141c50b158440d1100f4044252800c05010391f02000640d040300324000d000406ca4103003584d216408440320001c0d4801c5545001050103461030040040031b01e803520f1010380d900013070b100b00c00311100c5000340702040c1c07a1039004040d211300342ca0080503d43c2a4500f161902c1d0b004101c1a4000d00c0d144507007681c8018040d444080d24141e502089898010342c03010010350605008813400f620210b80181119450840c004000c0d681c0c0d01060280d000070311012034220352003 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 167630899 1250 167629649 167629661
    0x507030c120f02040803180a050108010302060f0306030c0d06140f0105131a190e01050d0c050603130c090c11010507050412030908060f0108101401050d05070f0306020913090f02010509010201 84
    0x1200840e9142c140244800c24180c0d04072051710b00c40c0423666000142580305160041c1070740d9000d0111420000542c4051103903410181100b581802040c0e584200e40d00c407100d0441c446802000d011403c01054512201c020f200602900600c0c4035280042c0300e561280c05140c2c0440f0200c480000d000e4868460f041c0c1c03900200d0346069130200302003141e4603030890108080000d8030403003100c03e0b0541e41d0790030400081c0000310704011301145100b40c04000501e0302e400510f610445682c0c2965402e0706950fa041002d07005038100200060f6508038002e0171075880103100910004010080000d800c241002404034000c51250020200404542d0720030984138015100051411500300c64441c18030030301940024909014240c25885140904035034401e91340960340d40c40040d52165003807130b400d0400713000a00c08150f2094070688144180000d9000c52400501d000754051440103844600e040100900300c8030424518030001d0400445202191052909071011682400e05907034800d0f03400300503409000d03 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 167632149 1250 167630899 167630909
    0x51201021303111305130b130512030a0b010903080d09080c030a090311040524010c051204140d0b01051c0b13030305180601181119030507030c120f0204 67
    0x6501c1c0003003003168181d5900d03440c42c011101c01198450b204c074240d04981d02242d00d0261500605d0b000b034082441920410382100728500c02100803801916a1450010645050440d410002041107942c0304284141000d0f5a002d1a0207406113281d501c460032a4000c00720000c00081da50f040720802c010045003203580804c4900e00303580d10380c91800c4000d400e8120a200c1503a0300001084028814078061040ca480b444003a901e080d42c01da000f0642010032a08070030054180004d50350342d040494030801848100b0403980c02003c1d903407400c0131036000c045076540303042e14050140707004201d001414420040d41920000c5c0c50f00210b402e4010701d082240c892009018105408401c1400204601801414111400303520144640d407144100300c800601451132280c1c8c2500b00c80014000d40003000c142c4000d040d06500007142011022107141240e5001c8074000d02c0c40c0c40301c0102d010301590180200c0c2d61024150404100e41e030485000a459503003c03e50441040b90b8800d11001d076407a150b41580e000d49 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 167633399 1250 167632149 167632177
    0x7020f0a020108041e240c0903150b01051b0703110a0b0a080c070c120224090d05030705060106120510050108060d0f06020313021f14070c05030307081809060a05120102 74
    0x15810f01e10010700f81070a4110035184c5400e100103c10414088c4c000c42084a0344a421b000403d9442d0a103000104000120a410400d04001d00c890200c81d00680d401030307030642e40141000b545035142c01404501074100d200d0240005400400208038040d040d1114242c05007010b488596400300281c0d540d1050450091181008020110b9030242c3c180480006600c00c0d500340d0300c01001004c02d031000040b4100441c482007010450f01c001414104080201c544c840d004403070420740a80d40781818482c3c00d801040000b11011114240c01c40d032805100d07004000302d075504446905280c002085184024007060190008864400811a15901100c80f03150410000c40d100d0034540c0301a04840303890310060307101d103041300100f1075120072482c035250802c1d00c0754584844012074903029050a80000c542170724449000b450004164400344005c1c240380f84145a007c0d0b40f028103030741c0300b92507500040299006140c04800c00041d41c481e44840c0d010b0722002c03196610080e0307102100902910402104c04104 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 167634649 1250 167633399 167633423
    0x90c04120c080610091805030316030e06010e0601020d0f0c0201260f010603060b0301080a020108040510091b140f01142709010501020619020304110409050607020f0a020108041e 78
    0x2c0c1c60041d2044c007550440b190074003420888001030b16140078041c80c00b9000350000c10108002103000e02c090300100c1403500b00810038000d200c3c2420306051007640800700c010b008400700308556906004c2c054055a0701c0c1400401e09001d200300501c10070541030002c4c10f0003e08100103640503514224051492101c101c00c0c4224070700302c0c40340c000c030140030312620f00480d040400100340c2c0200001500d0580d0403c90003045202031640044411110240c01034660b405180800442d540b001d0007002e5109004000c07000b034002070030000344401945640959041000d24901a00a0f564a440700000020034a8024441d0320308100c1741c10b051150031015181c8441003104484011180614400c680504494203800c5030390b0f1b1070059854203000c43d520350b085280001e00c4205d1350781075800b56800a00a41d201e84881c0141c0c008a02190614102a603031540628100b142003035041014009840b440c0010700007550f11340d03001800e8000c02500042080504507440003000031220403c1d4032041d00000c02c2800 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 167635899 1250 167634649 167634661
    0x4020904020d241a0d0908030c04050a050a06050a030504140f060412031b05130b0301182702330c010c02010203060a1701060911090906090c04120c0806 67
    0x43c00410300d4251205607680040e00034060710f4059500b00c1d01d0034094907540e4022558203044581c00103000c040010340d100b130305002154820780518482c032811021380b0381c2d541c01d00f000c101c0700070030991000e407091070400030601815a004080d00c1a900d101d0402003225122868000c007540c64513200b8000601c9006c902091500c4001390141c050ba0203070b2013003580301200c49021801e032040400d407107500003040507030103040038850b03001005100307402003264581a480d042e020103180c1c003c0e400341100601400184120300040c2c1701d01318008540710b00c201c0d000020648610000c88000ca4080d01c01c05010048640b178144285800080d0651540000191441d5400350130064100c082d84540325843c003004046183d0051084a01900c4014014a041454a2800d84480c3c03c4e00f1603001c25552200030004690750307036018041d00107602406140e114200b0109000d8907000040c610f42c8181c014a0a2104082e400c60455065881740c00302c0703141b004100e0902c584808519071019a49124040400103 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 167637149 1250 167635899 167635901
    0x1e1508071e0c031202070b010b130e07050a0219020906040f0204030503030c0a0206010909050307290702010e0d03140408070c1205070509070e01140a02010e0304090e0105070c2004020904020d 84
    0xc12803090703c400c1841906803810398224018024000c11f0369042c140180044550701c00038040c0d1000c1c03007400d1456a501d4013010021a202585d05102246c8042040280c05405005558600d080000f1041200d01d15800144414401904a50245a4a2423506146420b07601240c01940c0c0040450b5038a06107040390b5040346e40300204100041c0941000030a40c1c089a0040c2d07144190480c1c019803c00e40c8be07490302c14500400d14480c00002514406400c480c01a0840e458400d042d542c0000072903141c4005020b013041d01800900b800c062400b08142c2d9034041180c0c034960440d81107036100d502c840d0103203020440c92440e034100114a00b12400d26000b00400065003e0541d141940d0926880d221b082064803805450100c80f0f003c00d80782000402007030314013006494035140502c00440c503140c1c082442811648a0b0308524600c90721381d1918284100c0901803a80c10003d1440c03c801900c000e900c501582130501c02e007905566148000a1a030b60383d0f00d8065503041070703004104541c0ca110b41a2000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 167638399 1250 167637149 167637167
    0x3020d11040f090b03120406030b01050403020d0b0a06090213090b0d0503030a0902130902011d0f0a0315050c090a03062409050601090503030306011704140a0c1e1508071e 75
    0x1000b038a00340440f61004c0d003800b04c0c400080c0d5020458140c2003d05011040e0b01800c041c40c4c01a0411500707210010160791880c40d641004d500036543e03024142058005402030303410981260a10700d004020240b51044441c560b9411205000c1001569403880d40c0040c114041c5510041e08c18072020052040104165000c48641d510840b03080101f4400081d030542502c583c042301034003040380040c0c64058003600303840d440001c243c010308c004d44c034130019070000c0c80d00313140c981007900c0c03400003114505c4002c3d0407071140c0c54000050081090900c000c800024091188030300005080035210070b48000800b901c101101e0801c2800e6102034030007521025450020036045582e60700248403a48006024240401281e000301d006a403100742101461802e08250800a0002c4900c0d41503282c1c11801050280080400f05104002c08004c0501e4800d85111482010340111001c90b0020380400c0b03006a5010309603595021b5042100540d0b6a0040a842052001d280c048410301c1e100d559040003540b21040c0c03 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 167639649 1250 167638399 167638409
    0x2030c0f0133050310020d150f1e0e010b0903010b09062103040b0708091509030604060b01120c08011d01082e020a0e0f03061603020d11040f 62
    0x11034950325200c00490981d9036688014104004808000d68600e05510920314042c1c0300d107002c00b06107543c3d08082450300810010551030301e40e0209401c98110294041d10901080c1c009407144042c0c01d01e50945000038030744c4181081c00e400c25080450008902811030024158951401c40c25a941c11900100340d002c2c2c0c4182d4429480e010950303446107071a0001c6070060801800c4965501e0300c4007000c00000c1d05101e01c4406034402480005030080c0407d0060101501c50300070227484031514028000c0c2a400d006181c8080441400b2881c02c0f03440002c0c01560254200c4404103400101038010307107001100c03481c2c0794805070902c0001b4000e1600000b081e41280d804e41081140d408800048011204081c00b8012954108103800e8101341c00c00b4140250494034002c204000310600a000ea0481c1c0c0720200d0b07000400e503020120780c101d02c0c000d0000c00078000f040e40500f1036880d1020302e40803072410442020b021305601241c180c24200702c640c441c0c40b000b03100034260355aa40d107800111840d11582d10070 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 167640899 1250 167639649 167639653
    0x60607140703212c01050903011e05060a1206050406091515051002070302061e1602030709090f03030c09091a03100204081c03020f030705030717011409042102030c 72
    0x10f002c0d99a1081c0c41141c03407800350074500c08010b0150750700c04140300c1240c9000d03410010144110811a5801e1007020b962120588039107540c2140d5190030019150020314180c880c4a01c4a004c01c440715865400c0c407100c03a40b06070001502d41e11481d29100800d0203080181031100c41200000035032180d903000450054041e098480c2850f030714400c00c000c0300e25a9008100503081008104018103008014040d1913100d410720085120f48141c00320f96907000700d4548071096400c1000340c0d00f903003403d11a4070050102542d042c8645101c030341312204102c441100c01402c141e41d4071016610313103100750f5400c80500800342e02404464480e554a807040341c824102e00744203015607100500300d01203510850b001c8036001c20140109201000c042d0030940451010403007416006c00c140004201c03414010352003400b80d030300c52035240d041100c0c0c001c100190600d482c0d007e420198005101c034500e04010845104170440c5c8140c030355500c515103103442e1040c08401d10800022000c889011640200251401400c5402 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 167642149 1250 167640899 167640953
    0xa02130f14180610050a050103090507080a0c0609050109051c0203010605031b010206360304030204060605180a0f170f0319140414120a0b070504060909060e060607140703 75
    0x2c0144d403004143d108a96103c90420b0701000b595000f070b0016603a0600030001c0d200d031642d6032125503052507441d0318100c441d404880000c0c800e0b503800c07511030300c05040c003031034014aa242402c1c0441c2144841d14a8031441ca00b0441010003190f809400c800050000501070b17914541c4041807204012403032001d0b641c01341c01504000b810003070341302c0720202690301d00e500c95a242011410056010100c45803040790b650004000100142c1c40e5070289000400d03071035841a50711094142803a804d0540903503014461940003504101004601443c10184d5019910314180e100c100d090282ca0840d81c8210107440f400041120f0284280c40c10f03819040791040d4441443d80004040055400d111714015948000e008079503500450810781100d034440340b803c0c400ca465030354064580d0030306810100d4103a80000c2000034244116584060700300024080d0f00c80501065041c41e03641c241d03140b0002d100ea402000042059030502440003201910100c0c0b050541c2c19050f183e00700300d03d14100d00d101c900c640c401440 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 167643399 1250 167642149 167642161
    0x105010c23011a150306030a020108041703090604030801090b0d08030a0204050a080309120604051c050d05160905030109030c0f020109030b0108030702090c0a0818120409020310080a02130f141806 86
    0x13007243e11540008000e806201075603401954035100113802a108070681e1f2200b10174180c00000114000c9988000900203450705140c000e0040707005030455000641081988246074488201ca01c1001d50312020240d200d55a4182c031400900a580c050f44e405a07a004000548840c00b000a00e12801c0075121410100c5c0d86a40703c0e5591001507800800551000c0700f054000c229070292210a0019454440d1074411341030300c8001611002e5035440c401501100c040354003681c20404410060800307800901040560380ca024003041c03141200500000c006d5a1003108582c4143e001a02450340031815030420b5031500e280c5035990b00040c50490140d01d020000c40d1094000e8000c3d04c6410b40344e565000c07400c4ea60030034002803c500039a002c45462066403070700c0600b1080d990240020b44680380c401a01e0f4940b07010174650019259001800c0c6400c10900400541c681c21040c5035810340e800004602e44134400720080c01004010583d8001040324820b01c213100ca0340a0b85240e1484940c81140d20b42e4681d5 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 167644649 1250 167643399 167643439
    0x6090801050f0402150a05160302010e01050106111209030a14151302130e0a0b0106030915110a050c10020403060c080f1009090309091d150105010c23011a 68
    0x3510083d500c29401e614a00007140654010010054079143c50b038203000700c2300008500c03004040c0b02240543d440d8021004030203024414940104058509010406c4a071285c0c1520703001c2402d01c0c42250a0001140745003500c0800c40052404c2c6c4c008401c200b103131391414416880f40265098051820171550214203241548004103400b250004d00340b4855031103600e8200010803804016031a90b00039840d142001c0f0b0b0075222002d000788265140130840c0480c6180c440d52011140a150384464a402c0d07620301240c902d4030035911baa03040d41c2052650303030000003540f80c5030408115017411141c0c0002008410080140c1014107114203e8440c144182ca490301640084001100c816061401d550010800c4109603048100381c14028100019102e44840d10b50058a0060010f444079400e221555811400100105020ba00b617552140445504050000f00162540c0d00060601c0d4981c646000710120038101c5050f04100c0d04000300075021880d070f4038550301d200a004861140c041c01d00006260740d00 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 167645899 1250 167644649 167644651
    0xe07140c0705220509010c090501020307080901110a050307060b12010b0d03080a0b0603010f0303080609040c050d17161401020702010c2604062c030a0f060b040606090801050f 77
    0x304009440407a0409081c841c05011100d01d41441004070710702d080620125200e00d0740101c09410000c981b084060101604080c0c040e402141198000c20440010400202c2a1980080300f441d080500e88403e114280c42c101c0301c0003000d001c0380070000b0307004104881a4003200c5880b40503a0a040846000c1c07540c24201d0350020681034103c44444d0715a00003901c502c01c00d541c0114071150019041155002181c0703260000d0b0841000b14480d000103205141c0c03c06506a0710410464400c00149059a03a148034403056100c1c6070b0080c2040d00d41034042040000c0aa946512000388135a21420700300445840308840030300580703c2d5804500c4905002e00c1c18000c64040702c3d01a1540100f00c0c01542d208031036046042a40302e0b5100e950161111402c4042c4010300003010156100396044665103040014010a1845c100016005020510094601141d04c1441d07507000b041d1a0640c0001e07040140203050400a042da005103000c101240041d000081da80646d64150000c104966544203501c1d41800 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 167647149 1250 167645899 167645917
    0xb0105040e0a0c030e0a05010501051e1c0303110d050f010902030919020a0e0f0106090f18020a0e040e0307140f06060d03050909040b0406050a1b05070c050a0e0714 72
    0x104000000b00e09403066040160404024500001c1ca02d8040303038540d0400307440c441304441c0d070b94603900101700d13a14080c1080000d100e44484540004071003080010b503ca0b20084492011001210b4550305160007640110280740c990351b49181e440302c2041c4171a001f084203c401da05440c92420001c500f0a401d442601d105000d46c400406240913400c122103454ad038048000c980c054501c007000b0500740310540d026402000038200b030340300c194100500a01440b846401403254031030404030402034503c0d084a9100d9600081000503a1641c2c808030441d1551400e100c801d4115042c54510010468004003e000c00340c09007240480c0e440c0802e807407680f6005d240008140da54045c0c80880c0c1d56242a41c0001016071007420880d14101c010404149550310031107080e14021140720800c01803040501485034800c0d4004020011a034440c0d0700d5407001407c0f841c4a000300b22000c5100b0040240c0c10038024003414004142861180e91034180444108003225541c0003d50b0032070002031407400300025030303503504 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 167648399 1250 167647149 167647169
    0x140319030f0c020f0a0b030906090102090a051e031506040b0102010219081e0a021b030909010303030e0705060309031911030f2107030605030705010c02010509121c120b010504 77
    0x200301c00d00c0807210484108410399021601022280030b56480c40c003040000e200e102c05139912031134032541c0c442c01c00500600f0500680d00410801c0c0d01503403521441b0381a500c089528002001c0100603001c20040d081e9800c903094030812807640001e20700c032030380207100380011581401320f4101080124241d005100510b131144020343c09034422070380601200c44d032200f40d11240d1450310001d5981d1007091103040d41c00101555001607603a000007258824014a0007007800118a40310100f008140c460f4014031024081558901c80810756440500c401c100400d0000e000c140c0700d0070101749103a140e0780b0880e40d40c401420070000c1d1001841c0202078481074889104040c604010f02901c4190066000440300e02610240f4141605080f90000300303580503030501d607000202da60400c410b05143c400c09410960500520456200050384c0c40301c1254a06901980c00c0980414000c02151400d00d10340203900c101c03100e901d00c295040b50300ca030300380c103a204a03200b0511656000d40c00649441c4114090700d4200 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 167649649 1250 167648399 167648417
    0x61401050a14040c0e0307061707030218010809010f02071506090e0601060f03020d09030c0309090b03031605160611070504091e0212030307051b06070c0b071814031903 74
    0x2e8502036108000c04010360500d0718111441c90002410400b80741c1101000c9901514121042c0c801000d080b60700407034609085160007400c4003010042c2500d4071665041200c00030028400030401c0d00060b022042c1d41c5002d6490303034214548240c00500c80310140d400c43d072408000252013661030060150082965000c3d00140c1d003000411242e00310b08510000c14140c0070484100395141c90311441581500030756440c07041c00241d160040c080b1049a1101c0d0f1041d00f0140e18804540e000f004807003554444c4182ca415040b9140340445c00d00c443c006100b40403405203000010101d811000c03210882e1190020b4550f42e940381e030100000c0303070003170100603182c2d00501d0122501c003180c0c0080003000c180000e25180c103442420444510399402180e071580010004a6440c1100805034000d6440541040150540b85400d0300b009080301c1041e80060449100940450f100c14043c24110203c01d5200c948940e030192100e8007a03c1c1410101c0b5118082c0c4250b01010601a13000711303410103681c2d1b00d9500e403548 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 167650899 1250 167649649 167649689
    0xf0c0d08030a060803160203060f07142b05180609070314010b090a0b040b0409020603040f0c150e15030411060a0302092709120316030204030f061401050a 68
    0x1003504000c0c1041402a5103000c00b050603139041018001d0000c40701200102800c0751b2061500301a0081c01c64018500504203001680e42c114101000d02c00c3c0c8003601c40d407143c581100070000300190340a101401d12200b41040c50007030300d0341c00c400d20a40c80400c03892000c803842c080c03855440b20b040756058055003000200380300280c03e05201e045d05c1daa0010012407907080f00390026186440542d1100d2045540d440071030001c0c24603004d010040c182c2206e08001c0c281d4a80c01140c03c44c030005100501481110b480344081014020707180307003d4443c980f5280120f10009201800e858111031400e84154200361524600c08412000c41744203560000d51815441102d000b4421203401642e8a1030034541c091040c1c0c0740383d864000d20750030324600803014100c0c4103031a24481d03c00d108010340441d50542000700c0304940740800e40101c1ea0442d9038a000c840e10408d00c400708070024002c5400043c032140c000c440c90030600500382c201208540c0c0d017914100550741c5e10401c0110360305840c420001118540302508007 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 167652149 1250 167650899 167650913
    0x31a090705010e1f03091403091507030c0516031a0106050702040902060d091112010e0a0b0403090e070f031407090303030b0a0902040b45012f0f0c0d 66
    0x1000d04004d4070306840c800c1c4001d01c00725030481820100c00040d41d42c0f070003a000d000d0b0143c02c507900c0c03010800141d45444040e002007846420a076040c00d0380309200140b01f1080501c5010041035042c1c016054031300050503020740d0144007600d0301c02514500141c0a910314440303102c0c03030800e04071903860711420b1400e150b40d03081c4005400040007d07079020400307100700b95030306800303020b050307683e0b807086c40d00e0b468a0780d441041115403c140303032588a0a030b15015414855100000b400b504294202424800d11340d00d51800729801d20054000c440b0b055005405c5c400d000e81c201c040d05090400360384041c040a4540d03203450500550440e10480098510241040880d00a5204000b80000500030465885d01d40150402781d074400c0d8886c0381d608000041c01c6104030074841d10f5428103200a07008004486444681031080281d40c01d4004043d46402074110507a8001d800d4401800841403180001c0d44189400d24401000d80720381c51f5860040e8030b0b9408400501164000c403400300180040d41c42c01068860700 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 167653399 1250 167652149 167652167
    0x12041103010f0203010909021809030a120915230702071206020408030c07050a0902040b0f0a0e10030b01020708210c0718050403090b120103030e01021510031a09070501 74
    0x190595a118405086035100f03000541c045c259440000c18099014410300c0016031500d441852014064001c0c010140404070807284400d40f41c0c60000b070b401490007410801003503034420003030543c500c1078104030f02c40306103422003203a03030002c142031030781e030344a0000c48206140040b00e52000613000980700f44146045035150045141c01018010704098592150b545543d0082c2d00070b20850b440300104000340d207031800200b009002c0540c1c065003054a045560040f80c003405030708491250b4040b4030244e13100d1050000316940c0100401510209280000180040103032003000d600600a4840110780c1c1e00000511340c0f000300d07501003e0740000d840c410507401240c01c240300481a0307000348240000ca80034016040f08881c03031511300000e0b90b81824a000740c1540075035841007041070810300c0144042510a20094116905030030304414603154200101c2c109017080251345c0c0360110440900c0750f5041c0540010041da40305075480714070728082004062080404171030460b2280d000c0d003424405540714200d86 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 167654649 1250 167653399 167653433
    0xd06020318060c030103141207060c0e0415140d0803060906011107090621051e0115080303060f010c081e04050a031103070b04290d0e03030108121204 66
    0x40d5a026503422009030a0907426180c0f2562498080f00520034091005400b0000c3d08a200042101a040c000300301d003613004552024040300c0d500e212140500b4010341148d044418000c00800814452450000c1041054010820342e451f074160700031124101404114007064200e900142981c4d0303600200f06508500514003030410032900307030700c03034500300200486c40103005148000700b030b0141400c0e0302c84c0f40958900b4100c0c66051104018002041010078102040c0c0c00740b048880e4400c1914109501400d41120351348840030512000045210020002d180603243c12505900000d40880045452031030480d001340c00d482c01089082c403003070780c441000e000390172441242c507061a90350700000d64010195481600c0101c03d1400e28101d62a0034080760b03000d00303141145a070406080036086000362004041107003040b4449039440804401c450280d86d902050303248180079000c89103800300e0b1250400c2c0f007040074a101d8980c3d40d816044600080c1c49001c0a0003120070225900d5444c0e94121190744000c1b = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 167655899 1250 167654649 167654671
    0x60702030705030a0f14190201110705090106020a0501060e07090510140f030109050f0c0a2a030908071703160f05010c030501060e010804050606040b06121609080307020d060203 78
    0x70018041c1c4081c4501152580038074002c20700c40b5101d0500d0400015600300500706504150781d008111524862040342c00e40d020300c1c052000000c8445824540007540d0011a03000c501d03c070001488541c00200c103803d1504c1907009110007a5141510000c03103000360384400200c4c01541d0144034505060005c012165024038001e400824040d48941a136448a101c0c0402d401e000001409948294001c00740c05c50040006c07400580351550f1030380c456000d0350340450104001415140e0215840c00302e0910a0781d0752280b0304401005a00d80a4034102052181c50054010740a002440c0300d22100c07441c00501e945e001851034000c0c00760098400c0300250004480d50882078120b9800300d0030903c135005140c486500c00040d2541802009440002200712581c108088507003040005107020402d5500124240ea0200c0c01c1c05805000032124090491008440b40e0300c48204950700c0d010340d8010403141d506489880915880310956600da12a84e20b019400c0b940900e0020009104d035402560b10445003d4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 167657149 1250 167655899 167655913
    0x140d09030c080f13080609060a020c0c0603010f17070311010e010903060212090f0d021c050702120601060e06070506130804050d05100b01080106140a260a0b01030b01090506070203 79
    0x9140314803508510683c0c1642500821100940440c80020101800c80d00000b00140d18050710503e03600c020090211a910707401281e050510034042118a01c07075180240042c2e241d68485500120315100c51003032240b602102c0c2038a40140c84041620010349801c08513000d00d44152800540d00c482ea004c200c00c0c104640c4000c0080842c800f440640b40d4661201341400e02c0303051a460b414a0b00d64038040d110017641006003032158290700041d181c0801c0d1030b0513528880e000700020781a00d00c0d00070316401a410121003c0e41d40055800490311606039003054886c00081086101441454041c00030010b22136848070001c05e0f101d4085500e010141380c8a0303403402d4601900c4401040314540402e20489a17544000410002c51005002d6030305c1c000c200b0710b800c28080d032415100a0048010541040f04413900082403948103100701220108900c026541d02200b05600307003000e258280c00c80b00c0321713400c515042c0480350030341c4280138141c58050140c0d031380b01c6284d0514013082400ea005030812a071601c41c1d02 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 167658399 1250 167657149 167657153
    0x61805032d03041407090c050717070b09150106020a150f090623060d2609030a1a07030903050406050a0c0507060e1c05030301091109031b030d140d09030c 68
    0x54001e511481c4510300340c955081348120000d1070081c2c1070700511800c5040401c0c4031b10859002042d80d04490304214940380722461200d400c0402e1158080141540c0703a420104880200c1c0081c25242303001c00e09298001c16a0380307803c00c0382c649502c5030000b0f1044181e9144188400556088101d500441030f00011f601c00c801e82d20300c3c04071075a40390f501c440f0129245003d028a010700c161582d01c007101f41c0d48500f5044c0035030380300351001039150036800c48480c40c0068988401c100321b007039a5880102030211219006682400300da50307408a00d04800d078650ba1307400501510f1203802000740e90756040e1200b03030806082141c00d50b05c5411860b6510108920064010041042000140c000300700d03076168004c80039004030a21000320380308560990442d82400d5580005180002103d0454658201c000303290408010350229034458603410300e5141c81224000b42910440c03030903220301171b103048003152514545000d05036001c0c0810f44480300c40d0b500c00c1c000c0341d000049541190398183d10074a48903c510348a6 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 167659649 1250 167658399 167658487
    0x41103160602011d010513030521190605100c03030c02030d050114030d02072102060d090c05093601020f0409020a090b04230604081906180503 63
    0x41d9001d040180e46038980c030031001400b00c40010070141244000d124502d0400010008440c2c59071000b070400c000051854405c1c41040340b807200c1208010041401404d100c200d05081002d20a072800c02d01d454103000080c0c030328046070000f68003c0c003610b5120080f001524260000d107203804600c010350004008000241c4814440c41e800f0b03000110203903046460703003c00d0614084507000900f0a5601824060111581141d04120f01803083c45640104001030f01c0800d64070300811001442032410520184104490b1701c07901d0b8199030007982c090304250360384c1080d05511074480b511200001c9140d142180803440c00404038070030112000002d442d120181583c80c906030b0081c0d2200d0112030b40445c210095a900550007801001442445401d007414000a112031042e1503020342413503000100c0d003203503585850040d24000c1c000b190a4480f034074070391b00000e407082c451440201ca0551a040019400e2000300c14948007075600000194104680b40c8101601c030000800001002000340d6a4400201c0f00 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 167660899 1250 167659649 167659693
    0x30703020a050f0604020a270e0604030f1b0602031b03010f0f050604030305030c1804020d0207150c0e0907020703020405070c0302061005030d030b010e04020f120c0c06041103 77
    0x12a5006103048500c5050160412811032000e0a0310742040c018070000daa07800020405480f0f010b40a1a8950001010300c03003100c2055000c000e0b200d0400000b05141d07000440c045201e0750182e12019004800c40e802219403030420201c490885001c0d1017104082140b5074065988010344150507035501800380003041c8250026030000b014200c06d46c2050001e030b01505408001000203a07a65418142103036005072250000074070b513604080700864000c0039501080800344001401034011942c6401100701e45019500140c0141c501c008082d000345e503040c55500c600c1d20f00941d255104449401904c00f0062100300103041c0308110b104603040030015a6483c1f0459000300d50b070380c032611000041890080c0c1421801880c411065040305030806c5a601d000c101c000b10b120181c5070000e17015080c8030040c2c51002000c981039802500c04100c200c16401004010101840018409003165031628003800c0c3d0303072040802c1d0556a80041002c200010003a2424050041d002000c0d111009903071000c0456140e4 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 167662149 1250 167660899 167660903
    0x190c120501021903020306010504051c0c0e09070501090305060705030705131508071803112b17030108030703030b0a03020916110c010806100e060406020a03080a06120609030509030307 81
    0x1500040d00c007840606405002d44904050a0543c19031030007d0018203a80214480c072401442d03240120020071800e400411111607000703100d070501c0c58491268450860040740c1000c86489068000301d59907000d140300b1000c680e40480201015a280d000898044d000503080d00d080c0b207024445030103111410150300f00030380b10a46170500400304c0100010110341011f498101030000f03060190302c5d42500f0140b40000c1e02d40013420308840e02e240f0342c04180c946a006a44200701410881c404003138044c404400400d00b40600000401d4865500703110001d80300a2094188540c400c0024600203400394010071500e810044c00007440d16625008100c0a11003140c0e06140741c1009000a21001d8006040c4a10030810000512610090b44006041413078050320461062800c1d03280400e0f00c6128120010303032024040c101c207884603980c040180d0385484409080b0041084000003c10520300e5205440468100c1440d1640f008240e48409000b00107040c07040e000c02c6410007610320161820401054098 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 167663399 1250 167662149 167662151
    0x2030307110102010507050309150919030905150a050414010903080d0c12060612020c0f01090c06031413030f0c0b100302040e0d0f050d0e0d090602010b0111190c120501 74
    0x200c41c00000a003140d500070103800074402c050007840f60030140052007010301c1141100134140b40e144c200c5918030340401c82c0712004000b20304565810070540c1c0280810120380701900d01000d05000000000c41e1405a420400001941440b0801044204006c1c03203601180604088001300d4813510707110b029038040511180311944540041c044070354043d615028560015004018880c2003880007803454101c0900c0010050b00420320f0b440011060100c0d540400c0a80001c10a041c07a074603010021510a2044a0109142c41108003200305504d00ca984503040c8030406400100096030152481d6180042000c10050107540c0d420009000c5e03141c00e0b0160341304454800c10540ba610403c0700b524001d1203052001c4d003000364800b2042e42c108121500030515800d20b00d48400c0d00080c000014001e51040310600d00c0f910800e5407000d50844103450955246900a10441881c840103560155809400c0f44460b840081c01030140c0b012150b0807034405106100d5412105d035101c0401e122054a5401078500d6 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 167664649 1250 167663399 167663423
    0xa0b04150c052502010e060901170f01080d08010602060601260c273001050a090204050a0b010f030c020705040609020c0610030c0e041401020c01060302150c0a08090d02030307 77
    0x85203905140c042c4801001e01050540f44940c0e00081081c03440800c0280a4603010510002c1603004040503520f09160303400d498981d24001000410000b004e11070041140255101c0e280e10500c65007003541660504d40007440f254950344011a40041500845001c514541018010002c07a00c2c88860180940c0303000c1a071503503c8030300404414004d0740d550035020001c840c4e801c50682c0300c0c461000c500054404003800c481e2240c112054041354120329501c215480c290800c00b248119030b001c07a003060700036601000283d030b404880c2411240031070b1500303000c9021a2401041141700e50030064034000303648182c8501c01e6075840850152001a0020000a034011400015602d010085183d000c95075450001d612451515640c21007030b81030007107001560200001130300f40074070200c03551120b84e030600003103595142c0541c80b9070007040140001c0340300b0300c40342c00b10340d04c2081030a05448440090902810108401d591944000d0384600c0d211a00400c0320440ca9025a41c01d0000d0605c090061106402c0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 167665899 1250 167664649 167664667
    0x301020d09050d0903110409081308030703080a0203241906020c1e01081503070312031a01021b09130f080d0b19090e010605130209040f09050a0b04150c05 68
    0x200206055803000b01300018a0070800315170b100c0100d140d00501605c0c0003640071710310304081f2000c2c41021440e52080182c906d0000e041100080145101402540d440c2c1064035111518402e13840140d071410f4549a4004198400b4411940004000b41c00202100c840610104100940540cac551044000d80c004121681c842d0a02c41c2c10000b14141c541b011041e40c46400b40041d24055010305016240070481c000c21056890800c1420b014541142e000e40c0c010388010f400130b001e482c10b50320039099021012240c880550001441c4820707242c15100b40c0712408100d1081c003904000080c20130441c41008402c00c804607a8458086070b0487c0103580040e03540716501c0c01c0b24195a4103841d082c0c0031b910f00391010718030010040a8803041c1c410301400400c600740c1101c9014050003458200c142d000701152a4010030700203e50081075a2127042e07070103014441c0040351040031103114045c05001500002136041c0002e255191485d4054401c405440c41400c3c803084820469440ca954000170500024800d51 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 167667149 1250 167665899 167665903
    0x1109010e092502100e010b0a0e04030c080d0209190513110405090103060b01090618030f080d0f270c090b03031b03040302090f24010c0501020705030901090b07080316030b0301020d0905 81
    0x1117070b00030035402846944c2000c1c01040058065205811981c3d69030340c00304040500c60141d0360605500195010740b139001405110009500100c01e00c1e100303803081c0250145060318907125608494004042c2030303a0070740245042d400761440d440640504141004003048a075074a201160185000704400650030384800009031003030603a50428418400c0c1081d0811501d041841070109903644403c0412104129140003c568050705c100b020b943e40c00c000020089840300c0d031101228018000785298159140046000f42d560034240103090914058814803006890b5000700c0066074000c0c04803484d20751002c0a11880080d082c0c0c0c0c08034150000034081080d481c3c200380c02c0c1d41103112540804550f0034585203e40c000b409400c0ba0010782c03410720000400980c0100010a151074118000350350766801460b02688035408409042d02040391003a02003269100801610700490b84a46e4191550320b40c0c90a810b4440d0501d029801003680722040c2c205240c80a001a004c04210a000803503030b0200c03894454 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 167668399 1250 167667149 167667161
    0x9050106031d060c0d060e0414010c05090a09110702030a060501050415051c1103070608040605070e03150a09080c0102130b09060711031c0801091109010e09250210 72
    0x2c1c5400340b00c41d03500140360b01c007050164004902e10102c030fa5460100080c4c030082d100729804602c00c01240c80c00c0209101c1000c120142c01c03074500d0020400640385150603a15401002412a040b00c5241402e1188501a0b40028104650301000c5030524905038000317403400c1d01c000002c4a0403901c80e0010400d40c1000c5c029413000b41950600101e44504041c0403070903600c90380e904082001c5415401c4414402801003800300714501609448002d5101c200140c0317030100994044500c14a04070001c2e0005110b14500048034200a001e030000c030b42e820b2544104800042c000d1003015039a103031484001949030004200c03013947d00e0000b507100d004000c01c414002901d40d2000010160400001c0c98550341e040486802c035a20180c041d060051840c0401d2808d00140c0300b2030940c3d00f188850b008135540042102d4101c43c0414001e01018000307211500305409001070881c00304100990402091078107038880c55101210040307800d8135400c06841041c12101000701d800140e04003180840001c0f0040c00b81d8 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 167669649 1250 167668399 167668421
    0x307050f0a14030906070f020a0b0d1e060602071703041212110706050904090503071505160c0c09050919030815040615050906071208160f080c03060d0209010905010603 74
    0x196003000c00c00c101040c5c551107407042c014401002e8540f540115500c240160016190447d24140c0f1080c0d0300f00d10000030000ea0561880500310460a8085410705004240a45405502520101c0d00d04a200030048406401ca002507002c140008100c460302031a20900d591700076039000a0b101c800c440094003c074219842c148607500200800c1c080550003004445604909540000d901415414040d055002d0400000d00c0c402c502407000704118000c1d00894004c60040382003207940005004240c1c0e800340b002800034070580803084c0030080e80340950b011603480120071058030510303d000700e0358050248607140100e02054400043c04441e108048141c200e000041e40c0c100140703810604c03450a05081081c4080801c0000902002180c8607072080d1110b4a5201000c4401402c08030405440c60000711101e45a26078601200000a0f04c00c1c400000c00c03400310b40310a45281c03074118200801d580010b20040e01721401303013865001a00d0b0b2031070650013006283c60001d00d65041420040030b441003e905 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 167670899 1250 167669649 167669653
    0x50a0305010e150f0a05030a08090406051f0c020f06130f09110f0d0b13060501021212040215130306140702010204060f0c02010314010e0708090f070608090307050f0a14 74
    0x10010310f00c03410164071035014001c8804405180c4c00000203104440345030442c1c0d426019400101c010400300384060007010b44205d03001c2c02000d03103890a0260384440041140510514602d5040000d405000d00c01c02640c0054100240740391100003003203503a030198500c581d40710741d09901040001c107400000e1029003624070080c49483e039040080c4a03640501200300d0100400010717050070150041e84003c0c080c0d60082c2103403003003005407070038000140b45511540f400b50041225440e0000100003c07280d00c4180044400302d9074aa54003440645600301c40003115205080045035000558098450000c612440d0003003080c03110800b801d1008280500340d04d0543e0b005010030300155030486500140c111a82c85c0c0711307401b4820350004070b014104100c0c0050f20300100c1e100100745441b240318031900c241e03401c0c0c84042c0c40e91200c0c0440c560340c3e0036031009500c041e040b140c000e01032188101c8180b82c10100190480703060030526200c40b070400d89110b413649080d500000f40c540c10040a00355428404006c040 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 167672149 1250 167670899 167670901
    0xa1208070b010611070e180a052103040816020d050f0109030314070503010e1909080d230c180907020604030801060507030203090405040813180608010e1c0519050a0305010e 76
    0x1843e03aa41d064140940d5158070303400300004000d0380087e10781401c0e1a21038011505244058100281c07500c141e021951440071800707202c9905042540110390050f58013040c82c0c1d01d0402c0c500e01403000001102c4040b0ba00801c20902003004c200d0802c0f1030740c482024a0300000d01041140b402404407181c3e0040f101c2d810224108106c0e40d90382140a590448400030614081582d8010503c03590b100a007050044542c900f045540902c20144050001403002005c10040001010158560303415941e8460028850040004000c0300300c0d43c0240c0b01c4d0714640250140d0041c86440002c185034000c640e55030045c3d1100e0104018154030106450041c801402c0c92403404102d528001c2d200c2c8900710280703000d0354980021600700101c5408840c1c08000c4118140e4140c0c1d142d0001080130600300c812806100e040002c0402d079281d040c85440603800407480200700f00303141c210400c4c504e82040c00c0c0f440d0510a09200c0e01a42e4246181d2000000c1001c2c0d0702c4950b41d1081d41005421140c0c180c000e94000c08000c8 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 167673399 1250 167672149 167672177
    0x3060f060e1302070515070309171305010f030b040204080a11060a080109050c090904060c14090604090504240e011505030a02150f0a1e0201140103030804020a1208070b0106 76
    0x984182c1501604060140e5100e600b03041c090310f082d040c0504441c00303803015401c008420f907050b4132003101e861082610803c0c1b0b500c1c01c1c2440ea1356004a540c2032600b40c6001004000960251114442c01c0c1494100401c0c600701c2a00010202e80150380a428941c0104012104010071424582c045100c102c54150a000345042d0080c0152414050340a8003541e070030100303520207814002d5840d1408018290141841c0c0382c540b010142001100340c0703000c502240414400440a1000d07503101101c09007041e801c0c103182840b0280904400b40c400e48600040e2200c155464103003c181ca401209803142c0812034403482c100050840b40d45c4c014000040385400001e11055038085400350742190102e8851188103162a007580840c420b000c5480400e9100041c507440e00340d080640440c80c1c20b51401030741d00e071400b04441030382a261620101d04d005140e2100600c000381c000c5130f059403c1030001d0800000e442e252544000142040c07102076032035000c0440c2c4842042015441c2a014065902d4454030001e800 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 167674649 1250 167673399 167673409
    0x2102060c030406110706110a03061a18040e010c0c050601061814011e020c0306010b0a140d0e15221101030c110a030c050706080c0703050f130603060f060e 68
    0x500000e01c0c0c82d44034210300707122110350000c1d0b40c0c178035400880c10458910340d4506401302e9803052464101083c04c00c6400100e4115030012011019101401c65151020303500101c0c41040041c1c401030b0340070745e03a00040030b1076000034450316400a00740d8a0300d955021860406910340381c1c05038481820400102d41039410b441191b001401100c0101c4040117510148500503121100042190503040707440c0c4100c43d0390103600103842c1550510070350540d0600e0740c031490004034511821110b8004114085d15a020b8035050400400b40004064000141143c0b807004081c102030900100c003800c190f02e1414800c40c03040002d900d0004500c0b6010b0020b00044e01d075520140955258520780c181942c3c1c0b0f2644403054050300070000364007600302c2582d40e0f0041918019102442c00e24041d65580f1038200042811802010440c0c06078103007070801170502c030040d0350464003030b07000d40d04450803c00301f13118000c4c50004031a240c1020300410748011071030fa4201403c2e0110505950b000c0c0080041d0f2000c04d00140c0c5035 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 167675899 1250 167674649 167674651
    0x1090c030b07120504050304090606050304020f1c0f060209010906030c020615040603050303040b0a050c180d020a09020307020c03010e03130b03041b0608090601121e060e07032102060c03 82
    0x100c007419003500d9650071010b4402180200301c40c082541410100410800040001e0051303a4076224208030494035404201c1c0c60f4041100c000b13400000350403110110b8900240c0c143c2c07070407001000c030b404000140c0c1d40d82020200f00b21801ca400300c3e004035044200d0f68110448401501c80d41c5070420885801300c80003584d500d0003402105006103015480c400540f2036402243c040c1d500710040303951742d003098900040b03485411200c449003d440c0c100480e08038078804080307c9035007241400d00200c0c0700f040740c20441180c44807070003241e005040e02e10004401c1c2c0b690018521944203900a017101203c001c040c503081d03510444500d0101e402c100084541d0030843c442074400c0c0c42c601e4280503285c1e80d80740b5200c5142280b420499084507580f200014100303030f0005081e0b110340c0740318003660f403540d0307131f540741400885043c880050441680681c0a10040300c980c0d001840703240522404103242002155081c00c1440642058070010300107074000e600d44d14684a107804142c1540300030401850415550701b61404 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 167677149 1250 167675899 167675903
    0x71b080615011d01020102190206100522050c090d0302160902130b130f2d0e04030f020c040507020708120c0706180b040b030a050901061a09010315080105090f01090c03 74
    0x802600d0b4203400345d01c02d5064034841201c01c1511f440001c0750710300c041c0d500c00c0211a080d10203407070070030701107903d0074402501201004490a08901c0300141c40b2a00091701d00200030120403801030124034403994071070f01e90540b545d0107a00a896464001c03001c0d280f0041950b0030501c800d500400981840344d0b0a40e8907402118900586691500c4001051042004c00c0703621504400c501d801000c103400542102502c44150306034118145d0001180040c401c800561041022190310340d4005004207004100f40c3c0e038804014411b903200f0489190000342101c00a860300001640191130034002c0031420010fa1030b91120202d43c82d400c045542c44180d5880b60603010311810020007042070b503060b12040b48510090401198540c3d110750b22082816100e1300101c81c25103480d41440301141d40c4801c1841076805488901c0803c05a10070150b81e024001d0744103503241d904041c0d81d40544000d0740c0142d9590406403904500101c0c0c5420b140340034601d0304075110504c1315140d14203408680000c403540302c0314003101e07 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 167678399 1250 167677149 167677187
    0x503030601210f1b0c02010c02040207060b04110c1018140304031403030402040c030e0d030209030f010617010506030601060903060f02250209010b070c030611071b08061501 76
    0x182482641c2c000741c0340c0b182c0d003040c0260401c01c00c2154800143c22801c4450899902c1302e200c1000000c0441c0c0e0780e503015001a0100e459000401b0140c00c0580003070104030700030729020900700100e1000c1400c5600c40c3c14ec1000040c00890b210700100020b101205c000d031070609050203c40841e41c54008503840c902d90041c0358040704241310141403001c0c01504d00942d04000043c0b401001d8000d01c0d030300c81c1d10449003244950b281107000c803421406481151030180e0410000d00030745a90714401e8001358022500c0b194144105014110000000d020300805009441d40700000d02820600403820354201506151194004c540180501e07688442002c1c01c0700d0308450003007070041c80038441400a228440c040b8505020040301c0c1142030b20446c9903c0111807003075a210919a0b6141d0002d6001e014016004110b42c000304010004502641c10800140d0040d100140c5030441c0d641c0c0f000e00d0703640840d80344890300ca03a1810400c62504140609a840304401280c0e840300460500001c1540e2004200e0305440 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 167679649 1250 167678399 167678417
    0x3041503090c0602010603031719090501060909060b090105040c08040609020d12081602012702030709021209010509013b1e0106090905120f071e1e0503030601 70
    0x29109400240d00c003908190800081c03078a03508000d02810340390005a003c600112500e45044886024080c4100b82040c07002810706019803550014000480d8250744941d04c541e03011460910170701c00d9a404030b01c114800201c603c0c4000c00e101d452101648028421890304000c0c00d07200c1d0b00b101105502540c44040043c3c102010310010b45042d809500213048142159881c0c0b85490700048900d01858402401c1e11000c260144124240d444000302295160034000080307148042d8800090100c5200409682c000f40d11502d080040360446c4100304030200c1c01c2414404254000e200380c5030031049490007805170341c1034114000f00425151940c0303a1811500c1d103a0310f180b508100380380e480002e0036034107444014003042200b800c2c2080c1c00e18158075a518006002036892030510481d510180d110002e8001c40440d1001152150040301a180840404006200c0010b403519100440d08100400383e00311740005090176200e0262010b8a660589001a607650202c1c0c8000709403980601d0928215a02d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 167680899 1250 167679649 167679689
    0xa0902031513050604060207200f0d060f02031f1d0c0d0b040903051b0610030201200106060512060102010507090308090303040306090c0603151508061507050703030f050c0304 77
    0x148030080b80a0050b006040900041103401e4000f031183c1400f401c0d405506c0c0344054411401038291104140d0302c15801c0035654120304082c4401d031080e6005900004d06140c9000c1002e0913030380704485440c18240d2005088203d0070141c2c07450f901400380000c0065014520009084960340b024140000c40540890300c0004044290411010544003030018071441e8010716015069800041038031300d001c002004040c00381c41c2c0026086101e20038105514a200f031568006507603e00038840c421030401c5d8441c0942d101c10200340100303402000d01d0f9840c555503c3c1a40452440d03001c0c06014a41164100414001c05607030060080e426660401152582c40e1400000285144a5640020005030911030800c05001c622011842158419201805000b04484140e12080514080c400910138006240a00c0b64422030845501910180c42c444c207000001482e4005500030600031a01c50740b196406001f0544e02c18880700048410b03003040340c10065040800c0e612800b40340a02c0b19444036017008002c03 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 167682149 1250 167680899 167680921
    0x301050114091216120209040b060a1e0303140f03060f0604091409060606040e0f0402300f03031909022808010e0607050403030f170703140a09020315 66
    0x1800002003080c0e40c1d20645003543e03520782580c025007250303004c04034500240010f228807003604800c0c0d008091034240d41d0f66640e604034110019042e00d8000c1201c0d02e01041d02900545000c4a030018160702111044c51031400800a0020b0060220020303030602c10321211286004c150b070b40100080341d40c0002d03060600003003141400740f41c8c4011049810550b41c0d002100c1422041800703600c00b0026a4415035500b41400300b41c4c41640724400001410000081d02c000c0e03080b032102e401900c02084802c0b03084401e510030170400e0038814242c42c01c0c1004070b010b000c3e4800c10419400c0c2140c240c40914250f1a0044900c4100d4151a842030300726610341c04000119a03c111448201007080c1c24200a000c40c00e04903651028102d0041c00510340c644140000e00110005156200303040d01d2303807030510f05800c655049032a40041d40080701840701d21800346406260a0600c1c512a2489940000310140d000a00404000703000d0400a15a0303c0c00c12001301503103000c1200c6010194060b42134400f501c440e00140 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 167683399 1250 167682149 167682157
    0xd03060e06130f0c0905010210140c1606092009010b0417031606150f050906130b1008160c0c030803070915030f050c0325030b0402031003020a17030301050114 70
    0x10301252604104c414050303000300341d200a0b544207038222a1464980300b200c004403040c4254142e501c4009100069440d840032004159040e690310081945501c503564000a03214000000c44d1310a02403241c0d5240d40c00d581500c00980c503070031542c20005503d01041010f86124501134a401c07078640e025050842d400400450f00f004080c2402c0c20324203002070600d000107002c0d80c1c0950035040b00042c800954062482006000d580000b00381d079a054813000c00f048980c000c1c0000310041c0580384c04180c0415a0788103584401890261181401843c05e04020442040d07910360010034010f494008001240c0340d2150394099a40c040c00c0319680f41c071941340c260740f020b44644c040fa248680c0056943c403401d5041e04072100c41076241400b4051a1503040640c142c44c041102e20603240d030540e8101d102a1071211010314000621814005004034411000ca0283c0e88111121003d88166a50401c1141003003c00000204a802d0141900c00c3c01130380d0990b102d1106210f2181003240315140c00c07414200c180e04036 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 167684649 1250 167683399 167683421
    0x30f200d090516060206070f08060105090409020d0606140303041410020111070303020c010b1e041a06120609060607021008090c0d03020d090f060c0807140d0903050d03060e0613 78
    0x120444038960f1803d20000d85039000d460018060304000c0707241240102d0b81d4a12854841d1580c103243d65070700004442540040082a50090700c5802450140c0c0720040380b425a10301039000455000c1c1030040c020010f42201060900940c130400c810410001200c04170112500c0c1252180b015601c00c4204038003404400d055410f0148c00011070700c041582560007080241d0700413000384196032600d030801003c18443c103000032104826428004a52421b6482031b00040901c3c0001181804140c0108400703421451007046180c01d001c1c00d014607403030b1810026034011800ca403014a40035059001c50400b020480c0741009002071503002c01c2c0089002c0c0190b4142c12002b03800c000381c0e4281c5c0d05000f951140d00d401c000303010076035141011070048002400a026982940c0790078086a0aa070380350310003680608815540d030300440c0b03690301944005200480f01c202550362402c0c5a82d040d41400d909008211641e00c00b8035203003403000c11000941405035a03002c0002c507450139103126001040701c042c12a007441 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 167685899 1250 167684649 167684653
    0x90a060b0a051513060c080f0c01060e07050d0b2e030b060706050609060306040302070611010b0301020f0703080109020301180e01090609121404030b0f1b07050304030201030f200d0905 81
    0x1c12008010301e402400540c044c0c3c030010980c04e139903450142c40d42e024409024020001c10000c0c0301c003c0203440000c00589594100025600d076603000c0380c0710610426940c0d88005a0001008040d00543c4e0188220428003242d0392a5030030030505005a101e01c600400740361a90300d00e044400c00341d00075800b4103013100e405402030b42e4480c19450145c0040c08100e52003403041c03030300c600843c1040c00c00081080c42180d1640041c0031a85c00e000c8190740340350710700728110a03a40d203565855072981c40038005030009101c0300228031740f21041c0b8940074002101c140c100c420911b206100400c406115000e0740400000c80842c00545129501d0703e5602604113031034041d0001d0b00709100c1100300410200c460000d03080700c0da9040519050701d46035024a00c85d9100107060315004034003295400d402d0500c00c580002d410003405405c81008101e44195802c10710b800e540503000403030208103658040c0100d2405281151003000020302e4007561301e940d004100210b0141c6a40820600b60b205050350058207c00d0300042 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 167687149 1250 167685899 167685919
    0x14010b090f030a0c14100309052808040e010e0105060a0c0b0613021603020c01030b0102100c0509030a0303052a0a03092402030105212e0c0c020103060b03090a060b0a05 74
    0x2842d1801105283d2070070b0090791900390b1b10241520070300c10301204a60050140076150a900040c0603400803c084540140c480301e00c1e44000600510000c000500b40c01464820940c54203180c403002040590006008a50810805c0c860582c0034440c4071101d03a00400c00105500c0e84800305841c1c0340401b01c0d00b80303a64030004095462440e10802800010301c280e00311030000d02079000440c241c40c64000a503016a0011a08005810140c0c11402180c21303513203065420b160010380060b18004140b9003e50101355640103002c0710510800303020b105106c01c03080400742503144000d008814418158108101591b806800c0c003080103240900c8101c40380d00d82148100e210b0b10860600951003846054444d2008880101c2c80c800c03200e0b4480003d14011020784441948010b0007860b055121391b584805684c0e1101040022240e4440c00d0542ca22995949602d01b645100160882d0003039049207107441c1043c410424103c0b0000307a80c40043ea44000d002c10504101c0c0b011944c40c1e40a6080140d0180d01e084d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 167688399 1250 167687149 167687159
    0x20d0c050702090121080706020f032406191b1b0602060609090327030307030305010303080907030c0b0a02010f0c020102071505100b070f050a0803090114010b090f030a0c 75
    0x400584003060080700c10240070f9170ba90319540c581c90a80f106444444442603110b001240c0000c02a10f1078034021040175150a40c0401410841e6104407121101450041001810300e0700d44018800c007100192080345c9002c0d81040c07030620100e0107a4208007009061200d05801044e181172500c14036038410050301c0340b0046111400c00301c610900400c001403249a001514030302d4400601c1d03025052280141d0301e0030310130544041c074041035040c0c585041d01a03440e441d01580c9040005007203890080d41e0000f81c40d411803400420440000d4102c0985174840c0c1000e00214030412000070458030380c00b007440e5a80520381c80980c05080c103014440001464860103c14160701034000f8031450f4441e800e5420300010400011003120f1060ba04000366080412080c0003c001c06802040b1841c0189124041c40c0c150369260740c0740004200c800c80d003044012051016022007402a80b5100010b030728030085660508800f442e003030290800c10f900ca0500010003032200d0720180f040340011604202c04054461f220 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 167689649 1250 167688399 167688407
    0xe030601081e0a0c03080304020d0c03051e0f0d081308211311101710091b0e062208010e070509090604020d050c100804020a06020a0b04080c01020d0c 66
    0x50004440b030040c1c14103880d4002080c1103400380d90010180035500d0851711007040b690030040040703070050b510098400c040b50300d042e0040011031040c0020010400c490344031501c028031101ea006401d80c01b101200b142c0040c08901c80c2c89000403490a5040c607640c95521843c49210072002400c0210b0008540c2445825220b050780120031250b1200440d071101b9001c034850500d010006042c80b90720444030009803600300c1500121503550300d88000700940f043c108541140081e5010940100442d80c100003105150188040d0340c1c011905088003c801000041c1020040040b40d5100305000100340301d1540710240840c61400090100c0c1d03001c40c2d1182541402082d081030015054403d0020006880c5001031034184501801c038090f020701d445590034450b03010901300045409004900c402c240701d0f216000e05c481c0b444559514014181014010300801c1c0500b0f40165045410400404011a03000500140c015a02c05082c2e90349143e10034801f4028000c602d1022040c50400a40000d0b06900c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 167690899 1250 167689649 167689663
    0x13020f09030d050a080106050307050403170c0606011e0302160c0e10080304142101020d090212010c050a080a0212014212090602041e080c030606100e03060108 70
    0x5070115500d0704582d00050302c4a000c0c45401c07400048511005100c4603100310040d64004420381403c500b460788a90f190101541e180d071058801200109058981260800103e9044ad200303003010941e450110003208074175500c0e1845081410780028511803443c018500e00b84440c1c0d001a60141c40b16260107061841520a9480d0320140c1d19424011a04d076030080112002c40d0b00a00c15146d808183c03134140107440702a01d1118402991402d483c0c07100c24420f000070002041c405400003109452841040028029191826050b07850050840c041d590004100c1d8440c00660034000e01030798580024074003034420404c89111565410000003007401106082c140c0010141e010b100b0340c1420a43d030640c0c0300b000c3d81d825541007008500c1c0006441c0c061181c480d24540312903000700b082c0c51716450704010390703010f640901c42d2045110401035017001550b200324050a0070b0340151003090000400641d40d814003410003445170340300c3c00d458824140194098882002d0281c155241913070740744801a15421 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 167692149 1250 167690899 167690917
    0x50d0c0e1f06140901031805062502030405030601142b030e240904020c011503060606050406021b12100902090112020d0602030702031605030d06090b060306040b13020f 74
    0x140700070010a0301c5000300c0300c14803030340d1445900504010751100114050461040703414008001c001c94400411024004544901c02002041a01c1d446035401645812995501c24003190402d110078007c0f5500480c0d09811114800d14900309182030740c0009004244510f94841c05020a2407018550034601040704c0d940d03802902d40d129402030f04400c1c4030304805002601d05649080d4146203940400c448041c4c82804400341c4010f040c02c680e12130081c2100c29080031600220780e004400c100b040541e00502001e401e091070070506042c609580a07558805081c2a120400082100c0180c95125540c180660203100c80c200c808043c40ba42980d001016813a0741a8095800c0c100042010340103c001c0c3c00920f940607000c090f5110041e15800e00039080504480c0842c0002c0101103078481019a14078051b9020707070050344c2d50b1641106c1c074101f25290703640032031801814619450460350341d01003a26840003068801140c1c0070800f000065040300c82c02d242c545000d2022904410040b49100a418041 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 167693399 1250 167692149 167692201
    0x705062b0213080c030610050f010804050c122805060a0f1103160908030405010e01080903040e091f0506090712060503030d1e0504050a030f090b030c070302060a05040c050d0c0e 78
    0x903d41f0300e09444122528064690001610072012040d540308204055003d8041c1003681c2040e410b80d400911501084810243d240d80842d1001c11110110389804082200ca10f0003000d044d001562814ac80c0c0c00d00401040c042c6540c2c6940c110321600c00e4000c609841d8552103e29528a01003800302e00302d5413008411000201e05d03120100301a5000012242a201c0c161140c000148081004480b000d4000709404410702080c00001510880224154010307100d94010b000061081000050455000b0380a1742205080c68180581900c6519502da0454050b1034800c5074810f05840d81c1c0c0c050142584010f4140c0300019404074003007869030020280d03454100e403210603200146068415214141d070003030802c3d007003082d2017000a0f020b01001003143c070503030070007070502030307aa030303190482508100c0e074a034405d02c00011050201903060022543c0210301040070401400c0035120150b52030302d0b5005860261454403100014450300080d038400504241502c03191928208851058106050700214426 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 167694649 1250 167693399 167693401
    0xc091305071b0819120207030f02190b070c0201111e010c050c0709020702191206050915070f020f0303040f02010e01020a0305030c09120609010e0705062b0213080c0306 74
    0x20b49000c20030501c225080b11255040c961044000c903072a0340819805010302404455040d80200b160010380081802616175803100e0440002c06420035002e10b0000c801040782e40a420002007070000f5850300072401d458940b11410704c43c401030710401030000c0c41d03411350311460a81030840c0b03c1c82c0560340385d400141002030014205c0d041d4183c4003809100410b000ca40c229003000d1201c040568083d0001c03078001040540c14807404c0008035a80307401034100e118066400869001400000c1c001c103904080860000d00c004403510f050340e0300104010301428100a0414106030001d442004820180c540010969640382000d00d0403039000800d0581c1203010990280c0711100319030001c2212115070783c040c0c5500e45503560b040c0c07400440ea40094607440d80000d4243c51901491300400455110703417400b130000111010102202c0740740171143d5101912620307041002031814007040d880701203021340e86441444440d103500f6040740607000c4c0c1300d600440c030f855001000456050000c2c003111001820317400c0d1001 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 167695899 1250 167694649 167694677
    0x6020c030307050c120a120503010303180e0a0506040213080f10110a0302130e041a16050715180f0611040f050f010e12011a03030703020606090c09130507 68
    0x4900402c80040d100d41c000b100c0c8030610f42081d0070711000c48402d407005e0325a103280940d284544500b910850200240021005108140d0424107030502c00c1c59071501d00c41c21514000d80d9290540c00108070700705091300e5102103140c50303d49405440500d42c22903180030205440c1c0312074a07621a0441603c030500e2268000300b10303560720603100303000d5160302030039040b49000648034041d0f01a41c0324a060f00080b01c8003500001e00f2001c204065401107104841e0480407002441e50030340303146c0c40509520050b40e039000c0101251600701d0225011146c0c13104024080b1014032a54000170a11650308890103141207449004210800c41d01248080c4610001c110212107071415114501179800342001c5188148401c5c80140390003003400206100514000702d10021510120f64903121214107050316079100e00b9100c2d00301440d0b00800e8803080058000318203084907500e000b95940d8003e031440780034100701408101c0103101e171000c940000301d026188212a021b40d440c02070090404540707a000044501d805290 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 167697149 1250 167695899 167695903
    0x1020705011a180712060b0d0f050907061107030507030305070302100b06040b030a0b040c02010b0324181c0207051c0317060102030702040f0603020901050108040c031502070204051006020c03 84
    0x100810003402c0e244070b070441002d50b0f42e102c5001a042500344a18034080e0390100003e402800c1c017411040c1d00301c1e0345079005c0014020685110300c8078059a1428a001c02c52050300000b01581182c801d41391441d5211485001ea9003014020b40010700a401400d402005141d004401008030910079402c81d0f810740000c080c50400c0b140d80b6034450b80e000c0c804020400801056074055900b00740c0340d0300002165291000054200ca10604050026075180c00340c0e440c2600c0d090240d00e80c002d440b500c060001009000304020100380c010200601040d880010780307190b6000b0010600c030440c01300c00c0d143e1285a5044041e5070b46131503100b03880c440e004101c180100b4806140c1c450268644c592205450900e01032101d0b804002c0c0207182c28110f202c10f004500150341e07180079003c030142c001c40d4001449425401030250340c0c48140c00040c1888000028080016207244001d400c0307030b400c405da514a0340007503946640030303104004c40654413904042c00e00c519441c503215150112a5250201d07128400c2c0801816 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 167698399 1250 167697149 167697191
    0x80105040c171c030f0b0d0b010503060c0f040b070602070812040638240d0e0307120c0503041a2d04031e061b08010503010b06030601050912010e0102070501 69
    0x924055040c0c1d107008940650000740c0002081e845c0420b07100c0040c2e000c51615215048180c540920300001000030341003d1011075040780d801d440070361415540c000c80040740e01c95841101c0701544009005400e11150354182c1e484154412003166842824103120050100103441c19601c00703140c01858a010704505100c1172401a001640e080e5a400110000d00a880103241283e046064004469000b0382d841c0566138503104c0e070103026610b9001d040c103c10129003080444002c0d50340200700600100340c00c60002a0a403825142400040e4010300e0068154010f60717010a03801d030002842503002c0b2002c5009000c00c0101c180d595081c0c410400c691004c1482c00401e402a40c42e000c200c01d101007008541d400e0314800c401e06c60040c1456039503850400b140c00c0700215603100121059040c1440750704c603011900404045000784081c00a003400107000e0700c0041e0040c0c0c103000000036000410703291440c5006d5500031141c020040c401c412808107010750301c046000c8455500c1c044050090002c0c1c0f003052 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 167699649 1250 167698399 167698423
    0x305030c0307110109050904030c0f080d0c0e0906010e13140403031b090e0c0904020403080a180e060109090203091c020d2706050901140a0c0c0801020a022104080105040c17 76
    0x11f00420f49950714161404a0032817000d840202e018411807020910810051101050086002031182e80c0c201d0000e00031022954030a218180350400e1010707581c2d0140d51019151000c485a071420000c107941d0704000c1c5010304090705041403080c00c00c000e2541661002418004107401030030b49031a405411112200540180f04940902c080401c8100d5a1007000d448000300281006103815242e171260101c6030004400c680020f1207000f04402c00040040e400c1d002040111045040c5080c44030010780580100d020740c00c0c0c11303070340800043c50b243c1c010805150b0000408000c00d4140c40324110007501d840e104081c00010814890941020141809014132968640f84640d040c40f8189242120f241d171041079000d0411500301081c1c42603040c0b800051100c00320b2030701d0303000c402003042c80d150442d501203500034a00c41c0d00c1400546640c54021a0140101403907240c4064000e070880100c220900130ba0b001000c0c03540c40c00b800c102c10811f40070b41d04015180000544d1801d1408215000e645174a80002 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 167700899 1250 167699649 167699659
    0x270e0708180a030f05122d0f0604050a23010905090a020f0607030905330a0e0f01260108011b02030a0f12051302120d0c020603040203070305030c030711010905 70
    0x95140440c1c418050b4440413045890060f1070a0004411122210000d40c0c14842d00400303005a0111078120f2800000c0700789400009103402d18010b105210300443c010081d0b40195110780007c2e0403201d0303079881955102d8010701c0d5400b4036080d001c1103611005013400303400318640ca460003040c003040f0b0014078070b40c00b02c1d40107007401714034440c1c0418040f03039421004c0200c0500c01c0c04400400c42e940d03141c8084c99005e04200849a828500351007401c0c400c62480c40800340784504100346100c45901c9400d00c80d030010240d45102d5281119070040b1001c900e010602c001c408030090901c0c1c11550315103105412145480002d12001074159105074083c0d1111050070056881040304a044900501d544050301000e03040480c54081401d10b0341007600c4040b1028135400400c60328640452400f000d03420101d111480042a1502c40728a010b00414100c1002a10074030010001034115075081120308051030380001aa922100074200440d035030b40000008544c8581524041c80007944142d4044048031070042c6 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 167702149 1250 167700899 167700913
    0x30e07030204022a030c1204120b04050a140f071a0a0f030e10050703180b130503090d11011115010605030a02090405190b04110a270e070818 62
    0x1081000075130007000c0c40c55014510310350901340e0361031000c1465801030340c010185540f0100c2500b898100940410002d01c007405c284014400c148200c2080b0310700030f0307104000c48081d4403103040007481c1c41040400182052240e101c0301d040341c400460440c02c08016003044a16442d01e6030701082020006d024840c0031640c09100041a0511179a9603009142444c00e0000d4811a81c1032100d003002c0c110100e00900700e88070024000f90720380c94410918808002500819410041e6171011880320300681912044501c42d0a101700707202c0d05000319280c03030780010400180680c1524080940c190860700081c0441ea0361000c14101500100300d0b514503141d18883d41400381c3c00c000041d60a900702820407110607509002c0d14045072240e00c540c502612402d8000c8220f170541ea2001c1090390107000540740500d050034002528005100151303011500242400c003c0310b2001040407000c8880740b028024004030354600010032580280d034050199011ba50f4002c05983c584560105020300700c1000e106036400b0003 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 167703399 1250 167702149 167702153
    0xd051b0606060d09171201030c0902030402030c3016050904050703021e060a020106050415030b04020409030e0a03081215011706121608100e0601090e03040504020a0e0f01030e0703 79
    0x913014050081c070661469840391045007000c141030700a6024032040546040050040c41000124a002006030340f40552451400d6800310351250f9000d108103001e2051107000607005441540510607e0148081c40c104c0e408003c2051551070003144200c203c0b0048090300440d06083c40b120140c440e942000080050900d90760038000540c500f040c0f4104440f070364072284245603494400805113402c0ca5400400c0b00b030304040c20401200d2400a40b0b4904246030141040014206100c49601c07d804880005c2c80b00c0040c00c065984690b40b0380101e60024413160040200001440902581c2e1100301206a840c1d8440c0c0d40c085842c4601c4034101d0124000480d980d541a07580000e00c1d03403110001c2c20f2001300b8030008542900d00100e00319411a40a030040701888500810841d0b0b64804590480503c041d0740d00c0c1c2002c6c2d40fa0740042c061020b802e6201c000c90503401004004803401450082d20842d61240b1019008007565018120244100006003000c0d4556119026111184107064060b04d002455030b = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 167704649 1250 167703399 167703401
    0x70c080312220b0c090901051c08030a090212030c06070311030103020603040213020d14090615060a0201090804091a09040209061903050105010605040f0611030a0f0507050d051b0606060d 82
    0x1c600840d505081c08015080003c4055411a010710b485002c516200c5205a00304038040c0e5058001c0307030103110302544031076498120100c0000ea80c0e4000c03240503641d8a0381c42d031040c0070342500ba070301070f40264100d107150054900010082c50b560240c0c0c003e83d9425152413000301d0980d04880a4a50044400d00051015103400001150854070050480704450304c40900102660401c2c8842000d40d552400d100560085211170140c0c44920b40000c1e1000e481c103103d01c81c04a8031203421a41c042d1402050b1503003228000d500907200030307400445450320395a560b82050050400107600c26141c02100c403a0714114240004114003445e0b005085266503907804003400840d4807600d0071510820a90031000000c02c2082c42600d018041310780c1c2c3c156465080c01601c0051481c2680040100605014460754082d404030988901d107845240c40c0b50940031200e4210f485000343e4001412602030b1407009003105820100804200440d12001107168040c24103468484000b11602c1d5045801000008960409 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 167705899 1250 167704649 167704681
    0xb011107030f051005070c06111317010b010e030d0c020102030409060b030601030b19030b07120509030903060f040321090519110409050c0d1a0a0207020f041b0c0c1a070c080312 78
    0x11150105040ac8204100080e007941568090401d49403440c0100031400401e0142042045081c2081ca40c0203055030080703592140d500042074100a01000e0700000c682c800e0040340c00404514405020107500d0b884d150f449540259502408030b8501400000107040c100c440c000340d8595809000c0c00d8910b0750319800d280794401400071007048500c004940d0320840900c2190b0150000c0002552188000c2084c10704c0c009000d04116881c107a0b0104200000394480d10400002002d11001000440001c0e190009030906150060043c021074084000b41292091500c490034003500600e826103001c41c0c00e01049503e06480500180c0248045e903441f820b01001e09002c16108140703010a05040c4406c0703102c1c85c070068a034150300513000121603080d03280584540b41b13070900494040001659598681c00060421103001051054440ca04014050112a803c2c014142e004444000b44100104c0c84051340c8404402c07105100d90046c046840d020000c10b403040603032070a2100c14070340c441b9001d44488141c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 167707149 1250 167705899 167705921
    0x31709010216140706030207080304110301110d0b10030e07060309080c0d05041404050105010801091a1002030a02010f1407112104030209070201050610030b011107030f051005070c06 80
    0x74003040b440020780742c0b4600000d07403140109030103154011428032541c01c10005500000c01c160041c0b012101080d1200b02b145c0d00a42c0c040c540849a82000c00400e0140c031048440312100d030801704100000c854141c00003084013000310340002c0c08080128003502110020b144c0c040c00341d440343e05e090103881c0c0203601039102c850040207207606202910000d1440d005860b02240c1c001000800d04100c1c41c0e110003541d005c0c958048405001960510300020982d0205108000505841703002c5150172030002c40c0806101080034056500610716054080d55035844181c062005600c1c01c40c0c040c0c402c550030321904030f15a1051280030b80d282c131801c0742101d00c2d0150000e4000399000e00e0005503041000d1121800d403030a1040c146580b540e246004000c41c140004140c441075904150810940d40d44071181c0140b2454a401d00040c1e5290f2035004803100e8014042441552042800100611000d520520b05240c1b0940480d050480710680c4071090f25030940d00d480201d00700304000400a840c941007070403140 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 167708399 1250 167707149 167707151
    0x21031e070b01090605090c0403080f03060d0f080903150114010503190609061a071a1f03060e0610060f0507030e1f0f05130302211204140a0303170901 66
    0x440940c541e510180020b900c6503c030720781d450100b0000303802c001e10700551102c110440d090070a46140c60f021030a11450302c820b04074010003c0001c006a940064030b9010304e40212941e480c028040c58a44050303405140144e100303114085507004001d0041d9102410b82c0d2100c00e00b000000c0078000107540399000a03018102d00c0300c2c840d80345c91a0200c0c6108400060107030000116000349015200117640102200580601a040101e0000b041356000046403a818540c002c40c0c81395641c4030110340c0901c1c510b000c80720403207000000000303110650708106025205842902d1f440c1d112018100e03003450141c8038000c0414515011407230000c0c01000608071b400c7c024200f0310000038000d40042e064141403c0e81001d2030b4075082c18400d100d070707110460142c8101107060583c03074440d0850104440c5851440001c1c481c166084101c144030042105d250200d0540d801110511008070301d0321030181d000350007004000b40c00b042d40c21078140361070f00f040700840303030540c80d00540c0c0c4652070000d00c20088000c1c510f81c195 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 167709649 1250 167708399 167708407
    0x50a08030d0509150702060f0c03160f0302160609200a030807080409090f0b01170a02041e060e0f10060c060e0f030a030f05090f07050108102321031e 66
    0x350103504c9401d00c20035056015001c2440c000031000800600604181c4401005104200b40d890382129016105281c504103085906d5200c04228080e02c6800c0c0741281c00da0030400603001300072445c0c000700012881000082101d40c0d0181420a40c1d000900541d5400f52500004001140020008028050003078100790b00c1c058444d403c035801c5e20034a49049a0581824105900b4821700d00d0a96015141c140e44c500e1150141111003030399601002c2020b40b03d1583d038060920401e5180c0410b01158910880a0015581e80c0300c0c03024294004490390703120a0702503400241114401080d52082e40c000352500700b90141c41d511054010302c90700d520520188510002c0d074560080800180020486681e40030035102204200201070f1000a09045c981c2c2d0b000340e14048600350042088426030300c0c280707444503980c1c0c3c0d2558600c1c01100258003100342d070340313000900d500c8000c8020740d0030b400c05600392a000d00802c14504034000154807a56003075060b82080c0701250150601d040c1100140310408441410 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 167710899 1250 167709649 167709673
    0x12306070609210f0206092d0105010605130b07020d110607020307030528020603060111030d060f0e010b070308010504050a0e01110706050906240a1701060609050a08030d0509 77
    0x88a181d2240c000481c608442c3e20f0b09103070b0201440003e4141c1d071018040500302a50501d81c1c950224990000b5400c5040e249000718000d1000c440424002c1d038024840c1d56910f003406010b50f0f0061240c805503481c901d0300810f00c1c0011900721980c555003e040d03441c0001150311203c03500c03a2080c0103d0307030080041104102595040010304090b502840103043c1d47c6444d0580d1031509000c0441c03c0d00d800e10780d003582d0310159941c1002e49074050001e080c240801c2400f4040b01d421845070542e41d001480c40d00c0000300f05541d40e400e5038001e0320103190081041785d0f01c541411800d8003038100f00400085e1103d006110700d0400f900401e81083c00305030041014007001c0509829510b4038181510b08070400310f00b100a119144c0540d81d04029400d01501050420704d003c0c00c4200c41d415040030310083d50700c1450f07815440d81d500e03220081c001803e025514100c0802c04a019014904c031316000520301541c045040e2809000350b4040704c1d03c2500171441c1500155404001e480010950102ca015904072400 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 167712149 1250 167710899 167710913
    0xc130509070908100b040b040603020a0b090307030b070f02120414040c021006061106070f0c0609170c24130204051506030f100b030f1f03050123012306070609 70
    0x40c40d030302118004141c05c5d68410500c000c0321018202c4500c100d0400e60104003580f2840c249405481c40e1522030f0355a6054040440c0c5030030203a900c000c1c0927100010800445980c0301902d210300d245643e00342d5010140c141e085402900440c01000346a0541d002001c095245c107901c01c00f10001c4030b00540d002c1d4072902204108841c1e0960017100401c0e00880ba61260400501002d9485412070500e07202084078500000c01d20003084030020103a03541c1c0d914540900c0350700410784d440441600501c0d5500c05c030140780320392220030048514500e00da116181d04003446c50248883e100707001d400c0c0c070907983d9000758081001070301010380718642c50001e0070180c40380c980320000210702c40c0b095401800d501d030a182d50003080c640000c1d4400c0c0b6426030281300780440d401840c0b69440d042a110303011074010355100c2c010b441900d000c03948010715641c40c2c01822045c00c4420403186502e4950030560310400d0380e0752142800f040e00003591942c4c0c0080302038250380c0c540c6418000340c0006801030702c00003010103d5a5500c2 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 167713399 1250 167712149 167712163
    0x130501060305010f0c0215070c03140405060a21050402030d120b090103110907020703020616030509030604110406080601030b0406020c0f0d02030d0b0d0b040b061c0b06090c130509070908 82
    0x10984c20b80365214240025010045080502e82d91131818903113191132503004044400e8580c0042c00c00039084003291903d0880c0d41910050300d0003d12150b51011011805804592000b0540c25044042c1162054100c2c1520411344141e8001c7d0182c603041900000890b01c0303910303808584000c107548281d500003a80380d0b00203041c0610f210703403000348511526400b04220070310018506030455001b8a005d000503100c3c0000c3d210300c40c244400718424041c0034501a52640102085640c1521404041009111030389401a020714026901003010a488041ca10340b101001d010146c030703201c81c1c1004100010b03050340c02002c45403104000c6c0c5030081d00c182091420324120f0000880181e20100c0c4003040000148140315a01000b26550105c0d0300165a588140b010001c0018020007140d000040141d00c441a49040302c00007010b00601e5400103244c10444e1071400d8030303924056414000090110b00c412012a200c41d40a100d08455145c0f900b01008000c11008103101c082010040c8000359269040001d0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 167714649 1250 167713399 167713421
    0x601090e130614090a0f0804030b0f0103060e010606021c02010e031303150e0c010e012003040f06020102090607060c2312090d170a090b072001021213050106030501 72
    0x20007107440d400c2c140403059a000e0600800340d2891002401403641c40026810060340d4042c42e40c000d958200d04060005014591000d496074036507100b0400c01580c0a54810f059a04c158000c04c4800071909502c0e0032601c8034000e00d00582d010005808881d58008400301020201d84008182c560860050a00750340150300d94100002c0420402d00401849928070741500b105031104101c442100c40d59282ea5600c1e040c00700e810300407078901c41c2c041ca9202c1c0401682042d140100e60400840c0744440c296647c5c030a100740b0700408444e01020500c1807040c0226800340b5030040c4414104445510351500400f03100d20a0710602c21003d2454410300d4029182003040000c0c1034a140d15500280c80400c1c800d0001400d5200c0c42d0400c0300c01180c0ea41d00304000c41c80d204100620083c8e1a51814604001010f0596019000340d0800d010400301c00c1e40445207050b40044400013250a08050b84207600340c0c05500c01c619224558000050003107403181070201d20300340c007400012031002d80d03a403138450840d0030030006 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 167715899 1250 167714649 167714671
    0x60406080a050a05250306091103070f030311070e06090901090605040f050f0f250b070606080d03050606070b130f0507051008092e0609020d1803170601090e 69
    0x800801d001085c051010031000d2401040c940b034900009500d070385a01400000c10762545c0f1900d400506c243c034003040034030030000303000c5034030b01c43e05d41b07290000e0508684400c50014501060f0100b40c000042809000c45071461000d411681305d100c108101200020f040710174965a0f160b51102003041030040d05e0207140641c00d61904800c4906000b82048244400313008241e200310b50680501c1000a49007100411803001c003a800050512041c602e8404e0303a001c0c000140d80841d592040c006148e1244080350090012a0400007603020241c043d548100d8030103902000c24055000812210208103030312804025410900e0358141d40c80c250115440306c0c0031303101a0f101000502031807c0c9011450418103d500788603625180041805641d021000b0000300102e4083c50206840001890701020000303504c9014004c403038550700c90f0030003508400803090005050810706c0c0700c4409000c402c170103445d0305607403017a01492902d0141d561141d8003801c1e690402502032000112406c0e003d00342c500510040309 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 167717149 1250 167715899 167715913
    0x5070909050901020c100e0a05030f04170f03040306090f0b0f0603010e03090a051c0209010e06011227020a090e010504050d0206071d04020d0e01051b030106050d05060406080a05 78
    0x900c8003140c4000304030b089a60b00c10019180315a10005051101c40f052140200e403114442601508201044000522501c0003086120200e001c0e00040e200b500d0950051802280b005000566540192009074125400c20001480821b40d02c2c0c20040c0386038003403100051110076a42d20303094441c00403035039014580a808280103040c40c00f8068034154a01490046045c0b2495800084a20103140306061290842e64005d0040140e40070300255110780040409030107613982c5211804500041f00d41c140021802d800140301c00a00b80310304903592104404100f0303050011040c03035466009102c81641d02525540d000641c8005500900d01c42688c3c0200100b4a41814508149442d4558100006542260742000310842c0e104181e03010759141912100030544207072020400a20545949004840c01c0100c250792140054100b60f000350070b483c2e11040c0d1034104040c014001d000c01e00850001550402442103034401d250042900032500a10020712035036290b107858a031214580040310180c000310 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 167718399 1250 167717149 167717159
    0xf1d1201021c02182419020c0d0c090f0603080c07082b0807051201030c030201020c01020d0e01110f010504060b1305060d0f0602120c130f050a0317070501050709 71
    0x201260700250025424920015001054026400c4c50380f401820038005000f2001099030203060316004480740350360b8646440200915241c40ca070300031030252198110f00030180c145691503014280e0040c0c0b2190700c0c1d60500a00a001c2d10301006240b65560303d811011003c15510801401d0251421009016052404d14181d050003000c4020900f00c190700c01040310300141d1140d0700f0410030b210786001119a6109941507505000d254480d851725030b0760800110400c40744500c5901924000d030215440c074000d49004903640d941c03078001c010004000c041401020f5004807240748220b8094429210800c5828001500b1250119416201a41c84884c00641030404048020315800c02c42ea041c485131801d42c020880b10990031a000f09015030b9207030042d00f8062641c0c1540c0401420030448805c03401e01040c040c4e1542c001100c070040c0000603680001c1c0c0a220f8410f480d080726800b0b8440c0000a10f0354031022528500281d21482801c1c00b049040001002071040358070500c560341318a0311080c200 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 167719649 1250 167718399 167718427
    0x309010e06100605071e0609060b040213050405070e0d05010c0e0a030f1707080a0807031104050f060310030c08013206040902030c03010c030207110d030f1d120102 72
    0x416039003034140c01c0352051100c2e0550450250083e12114100079944a595241242c1d0f240c1c0540b403d6040b0100c018084420050f084c1c0290f10045d02803001032045c0c180d030808000c201c0c82001e000c5410350300c00d0380040002e1304050b00036942c012440e00f040080704c040c036404903180b03040e003034400c507640e9545002005800b50842c0b40d0b125140300940e5000511404c50b40e805224070205c91700900b20384000d10400291015030801c072906140c2c840e00741d540721002000040c02001081e140640402e040074105040c0d00c0708101901c1c11610020015016601d025040c0442036102a2900d0101d055a01002c030214031100f10110003010880000921ba071158140d0b5840050b6100d030300c2580c00e0501c914a81640c43c440300d0a070304914115070000d0101c1840c800a45040009400241c255003440c1003c003110760154003502d000c80c0104c081d9890303482072208000031f0307800c01000140032403144100b2200700c522070103951400c500358443c907450610208000501050120300c988405a40000b503021114184c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 167720899 1250 167719649 167719661
    0x7031a0d23010f05010605090d030305090106150c0210050309030f0d020c010204080f07091b050c1c0914030d0503010b030702070905100302210d0f210b0328150b03070b030901 77
    0x306d03140103810000e68400088507c01505c1e000350130903480708082042103a0a41c41840148501c40120b00d5460800d980a03010f9070441c0c1003688582c00f0344282e004401d00038801c9a10420021000c0c525042d1103404265181e00180101071690340e0038080c004549100344001e202401f07682008024200640c2020761401c10190400e403900c4c2d041a040c10182a40e00111441100160400c2a00c40501c0c890561400700900c4540141400881c0803032141a0003410981c1542d080840401e540e07a048001d00d130342c034442d030041180003501c108010448504107401954003c00c4910640700d00640d034140079000c0d1402503413010914190180d0410851502040d1807001c41c648406000c104c40721985080d45840d0703030300031540600408502d502800c901c01e1511050700389001c3c0f02d0b140309803100e0814100510203050024028030640429182c1c030202e03030210054100c2081101c002201d11542d5150080000d48481a05113844080c041c0c010b607402e100b418050410166031a0b02c91526458003825250 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 167722149 1250 167720899 167720909
    0x1120c03060911091c02091512011a0a0b07020604052101020c01020a0f0c03080115050705070803090103060e0c0a211a01020c010c0209040f08040f1202010807031a0d23010f0501 78
    0x134090982001a103407d10242e0748160703600054081010f5030004103043c0066584281d1a40d40717090b000d0070301109428070011042034152003030405103413035008400c0c0c02c3c0300c2c02c00081c3d400001440200010310b0b000e2003c15001c800004c00c074032140c1140d40c2050990b08960a1818076940200300c1603240340d84032280c40180c14440c640f01c02c070040551000b41c9903040c18010204010042c0c403254901502074411200003d6000d82142e22065955241c04d41380c8e0050410140000d081c42e600249075007650104a01410f0900d01c4a80b403c19034038002d803151402100c001000c58184079048001301c10500c1407500d43d0710600380501000d03400000082c01c0940c0c40705400c3c14003982c51100000750300c450400c5039109500040d0b451090034141000000c07401142c0c00040e46035041c2c000410304070b0224040b207251620031307214642c917611440025819280d4140c140e840c8140c803070b000020b6500d00038a05441190080c003411003540d04450211190142c0c0030810505a9101d00620460301980e00c00c142c0140 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 167723399 1250 167722149 167722189
    0x5031501090c1d0405180a06240e07030203070c080406020a0209011707050d11040905100c0503150f15030c180406030b040b180a0b1806040201120c0306091109 70
    0x1d02144881c0082c0440d43c001e141c0215918030014100c2c40c0324500301d5045d00321050840303183e88480d16140d006007080c0d0412910b10342c500f6508869261358030303400c0c0050300c081c0e00051007030340d80380102200203400c014200c104000c245841400402c0405000384040c1c606a405405245458010b04c60310740d2040e4418048121803800d0f0400c4920042400415100100ea84042150981c00e25030107012656018941c060b19240303102d800c1110004448641555240040c007541e81039000c05d480c64001110060008000c200000b21303245040b03001c410031315030014000c890404101e0030b084400d420031100c060680000180d002c0510b1201010362002c28011501401100e055581d00d000000010b80010100040040480c0803018030306001c1a982c40341c0404c481c4040d05c1c1c0d080c9006e65034000c0c0c4003504401e010b0b5007449030402e00490f82c0c03845507806031101d401c1190000c0f404001400d80c1e2500350308040d40c0300408076030440c860155080280c040c0e070740191103500903810003104520203540c2c00c01c0c3e4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 167724649 1250 167723399 167723417
    0x8061503011208040506030f0403120c0c030f021f050a0b040501030f08030402060d05040501090b06120706261005030c0102060709030b0a020d020a0306030539040605031501090c 78
    0x1025220212815103441c0000c0c9000300d50b0900d0060b05501a45d00050b500c600f0202c10441880b40741440f251140c0e000340d0b1110b4100f60501505d17421562141e0013180090311514000011a003d48146c07000340d10284112251400d52410320740807002c00e80689000340b506c406c184060101140140e136100072003100e0030059945507a0300e0b0001c0303601031a0010110031001c03002800f5503981c001130300d443d0309040307105001914080c909180200342406080301c41d941c0d0203000c01c450b410104081400d11140400400066052240c240c0e0591000481d2002c1060061166844401490980c5004005900c50641441d04103c201801e10441d07040050465000004001145500c0001c001c22250441c0420a1a40f1501030703e0000e07108040f400d038141400064500309855159000d9000c690050303003500c042c034030084401c5400c006400c80c00e030360500082030120403170488070041ca50000c900410004000f9510404a8148040b541c00000f42c44290001007141054078012891010b240d45014600 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 167725899 1250 167724649 167724679
    0x50c012c070e0a0510030503030a02121008030a1d150c010606051615060b030f06030c0909030919030f03020f10150e0405010f11070c05061216140304120806 69
    0xaa4500100719444560f210808206a52025405c00c00915082010369135645000000d110103540030010244103008220300040c1c1e02c44114406005803010400032b1032510601000c111801c040000c114401061400180d51240e40c5540e00c0103002c03180055000e07128806500900d003120010340c040b40070f12404201c507280e02100c190190200c0d55000320303840c2c40c0c1e80c1d40549410042c481c44e0015001208004107008070311480064652246504070b0495404c0e1042d54180060b901044d1002085940240008801071400540052107029441e0a220b2140d40e80c2d00c5072151030f83c00c00300c00d80158001398850340002d41c1c14041c034001545004814000110300509060100a09103d480483c0008030046000c008081d000308069801c15041444003c4031018008413a61180104445030820002c0000b41ca0410000780e4611030b800c15806c916079990413401c022080c034030340055020042044c03c01c4504100e100c014600031070107116410282a00200c01403c2150050401c0b441011040c0c80004 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 167727149 1250 167725899 167725919
    0x20a0c031e1b0510110d0e07051c02030a020301060b0c06090d08010e15030d030b0a05010306030b0a0e0a05060702010227030601170106090f02030709120507031101050c012c07 77
    0x18001c1841080e04030ba1622800d05604180c00c03003c203603846500700126154210412005000e0b00302d441501003103c40c075100c20300d80d0384a02d81c0c4601d070341040204510710f1840800068050601e40040e003958001d65056000908495103900f0020001e0400300d02c540c058601084400d80c80300d420341c0201480e64110001070076141052180c00000c0d02c15000040c4204800c1000c0f61044101400711601804071180250140408041e003a01910302d212000481b90703c24010038048a0300085500004e44403e02800301612038001201443d104082d003070360005600700300701445400303030b90f00050700c1e0320b0400c03c6840560900d8101c2c0483d01d0038000c812445e0b60340890041e04403118060f51a2900a08065882c003506c0241c0c00701101600d0f10381100110100b5800952003070429540b00d114a6441e0409228050b074284d0300901198803d01041c4005590420319a0090105040450030171140340d201900f55a84400011030480c2c8858480d10110710005998440d206d1070406022060300303000c8000d07 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 167728399 1250 167727149 167727167
    0x60b031b10051612080a11030402060d02090303030106170c04180c0201180b041106130e0c04030b09030c013204080c0d0f0e01050913020703030b04020a0c031e 70
    0x80c458411201d1094295000300d00b11181e155001e030210701410840e00f40301c402d0b0713060402814042500703440010b03074a004070300c0790b5a9503010783c0036007904680b941e8080c0300d0f09800060720004145d90802c1050802e68081010703500170201540c0300040001820340700545160090080901c5010900080c05058502e440b01400e15820103c00100c048030807408034050601e01c0c0a5200c20b0304601001c038148403251340101d1080380210503c040d030390101313024045544143c410040d4000740e254030a10505858200c416008003103129894145030305c940b203c2c0041141610420410f078000161146903103402c1c05844c080d0f084c00c03088121a0f04040d40006507a0881361189188012100001801c00007400169909461014215811003450a0000c0d11201815004002054000c0c940560030b61180302200c0d07011002500352454500c0d911943c17400b03500a504c0c00c030305064941c2c02244a64440384080d241200c051303a1103800c0f410301401c0180982c030100c0b109180c2c400c1407031800d480e150340042080b = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 167729649 1250 167728399 167728453
    0x30b06030708130b01060203130503061e0c0c01050a09020f040603030e0d0f05030d0204060206010e0402031b010e0d0506160503100e1b0310060f03091119031e060b03 73
    0x10b182d260b0b1a48032007040703002801001003c441ca86000403c07030700d5000003c0c020801c1c4d10701e0450b071595121010103960b408100c801c104080c8100380d005800c0342482801540002d001360446081000d421020741c25200112038002c1500c0c0e44188a00551510704041843d04038292410041c132400c640f0010004002059102c0c004c494800c4403204000200007207050f180c2d040b005603502e40c4000f0840d00e020b58090301c40c3c031005204000020600c07041090306980215401001081c41404141c1041e540742c4040000b00d041c031120005504113601c405600a90203441500601041d01c0c001c00c2440d10340805603200e50411200344204404401c7c03803450a001d441103884141c903071340c2d50345400300505000328209a669030400b01c1408600e00700256280d050368100e0f00c51480c04405100c0880031161540006030448000381598109030034041c0c000c44591650310307004482240c0383e860314052440c909034050506d008a56880042c40b100e84290080c0d48000c030301912180d00d040c00800103504180e109 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 167730899 1250 167729649 167729657
    0x90c040b01090801060b030a0b0102030a0f0804061e1410050d0b0627100504090f1112030a1206060318030302030c04150e030105150d031101060306020c0307060c030b060307 76
    0x400349441c2c1c010b041c04001070103010001c0c08010b0311684069001e0701b00ba02c0d100304040c00d04070b000320355600200503140c0d081403550300c0041058410000300c80044000d001a41c2c619961540011012828190080001e0228201181c086500725042c20f046600a080c4001c01d40884828049980d55083c0c0090310b94100601044589070140000e001002d1002201c501c0c0501e200e078490040c0b825614944100384150504001596035802e0106541d490000182281c4580e4910000101250381000d20960043c05845c044500582ca4900d90351102c8641d0b4045904152068051290350190b079000d40000d00d02808007028080080c00c90b1020920010305141c0c0110000b21401580010f44000300100503241c81c00707000300c003409001011811b4809000c1c3d420b11002a00541030340c45040c2003400c1c060b20442d910202a14100c0f108041030403502401d5494540000116045001030070841c01113001440d65040e541c981041241ca404510005050404d81040c219a40d054141d0350f118443d410 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 167732149 1250 167730899 167730911
    0xc0105031f03050709060b0301030201051909031b1e06020703030518060a080106021e0601060c0f061b020f0f0d05030a091b050a0506030919030203190206061305090c04 74
    0x9420203002441d01124a9420300500c1c0010500c40b0000e444811190410f00c1082036030f4803001d0742506c80c4401d00020740455401c216104807100100d00c050001c9000303240c00040b098480d40d4400c07502904522945840e41c4100082c403403000c4400704080e007001328582c1481780c3d0789486800b135142c005502c400307400e000020920f0500c0054240b544007494500604555a4038038590020f054100e0038041c441c014421090b44039040161103610340e0740c6010310001007020782e1070110103d440b9920f10f4811181b28480038208c03000036100380100c20142018103106075104000c480001d207403034451030a1806580c03108020303610880c408071b0341c001890414945299261340e00d080721005440d058a0040c040104910500c0c0ca031442c24848105495040b0345808a550703840c0100030b080d0006a40754003954010001c072214900320028400000c078400c0c015a41410f0200c94600100c0f500d00d8040d00150304031208020720f9140040b46c03445803001401c0d08100d241424440c00d50780303400180d402d901603a43c40b5 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 167733399 1250 167732149 167732161
    0x20904020a030c0e011a0c0c04050604060e010b04030210081006080717043207120c0302100905030d09080a030e21010902040c020c090a020f0d1d0f010e0c010503 71
    0x12251000303540c1050180c3c910650310607840c604040244140da400000381000c2d0000d10303034070b141200da0031284100144640a14901004000c6c0000303050300b0f40c007655420001039940e440500442c001d00309400840c1e111440c0d8010b010311820a2164130040280d49001c00c081400344194110585030f2520307180c44160703505a001d4801500000100c0c44008554040204100b103210003032049117210012010760250300c0d1040100104410281c0c50160400c0e071007030010003c000d8048281c2405003040c005079542e01c2c4c010a40c0543d0700c110140005070303030761018002410100704842c041022458400c04192800c6007981d00d034007050300010208041140c41c0c69503070791098502500b005c4030038020000700191070219402400e0408049000c2c50505520f2246030340081021860040050150280d50b9603044110009511207144041c05c20004d102d004015505d07072144010003124480340d450303000000034030617103440400d80207802183c0c1450000050400040380a100b80340e801c0c203042e0f444ea00c40d2 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 167734649 1250 167733399 167733409
    0x510030204050a03080a300b010203030601321303110604050609060702120d02010e0601080f1c180303081f0f050103020711031203041b08210904050c03090f010501030f02090402 78
    0xa0300000801005503c10040301f420000144c0d042031a40802c010b441d80000c016601c82c0011078a060120b2003907461621041c11880032401d8800f2454041280805400c3c40d50301103810a9481c28261802d001040c4100b0a41c12820300e0b040204a40403401c0610746070000314141304155985000e0007001c0f03044000c54650600c00c0c40308007272003c2594818465450024000c1102e10310314007843c82600000510b6241c042008143c2c12035400c041c080c503e50703080b42240400c10381e555800801c03281560380445407607104491b0b03020f140b01e651200c00504280f41840401002030005000c0c00200344803c020040d03205c04035604858080c20003580711100307820040c03c900a50103079182c142c06000056003c00b41402d000350b200d10312605008034a01e01c1d214828640a40a0207440351503070100c0398007800358101030280f00b03c5840403141c40d881c2441060107d8191030041c1e03080380102e4804018050030300c200340070840701640c802008201ca589144c071070b070005500c01400a07001d081b404000c00d042d501d030 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 167735899 1250 167734649 167734667
    0x2010207080d2c010b030d1d010f020a050a0302060f06010203091e0402070203060906041407080606061606020d0f1b02030913020f03040b04020a0e060d1704120c0510030204050a03080a 81
    0x1c3c1c001261404940c0c00000750180c100504010311034000d50f44050313151802110485240d85100c1142c100022200c40151400075484402d1019032080301020710004501300004000a48283e0280c02d0030704200c1d69800000c07002030304407419500240496113254030b90310101c2c6020300b01c054411a2508012020030000d100d00b00010b5090301132034080041d0204009003260041d4425001c03041c00380d0407600f8441d20b0303001034058002c00b03400800c041401440c10f00042c001081c00420101c80907016951903100b00d07031060489444950b103a211802441282c0d106411a0030002d6003000720400307403044000d44912420781564450b8168586026980250ba8159071400301d02582160790703030070700d41009459440200c0d022441003440110201d0780002a101d864002c01c005018500c0c4226541d4a51402140d614468880c481d001d001c000303030b900400303c0011001030180007058241350800c5d09024914501a800000341401040204065120701c800c0804607078115180e07503118511100c007220f4981d0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 167737149 1250 167735899 167735951
    0x3010e0a24030302010209030d0309051e1e010b0907050a120f0207050307051b0d020604051e040c0c1b140607050703060203010608011706010b03070c0c031a1602010207080d 76
    0x19007401000301501507008103d416800c401711010030442c01070031010340c0d04440c0000c0a5400c10451000915042c1d4255005011b903d0291510007560711691070305c2040c05121480d4a030b4507145c42c1c0203642015540940c02255074030f8050326003040800d0241800814203e0309182540d1078609a0518045030b0658400d940e10109483d035440c05400c1540ea1454644240c405098080403494910725012400e04d0140da8007400b01428107182004110003505c0d001c9444420081e643d0314210b65540d20300c03c065072800750b6140d407242d4200e036003040600d25841041c0145006058041446281c00300f81c45a030742d07480100c42156850080b1300e062403c02e00b007540700803e194004400801c00a4104800074169101301d00c03603000031710464401c07582e102000c2c0700700c82140c0410004150b01e80d10801e0b000b000d55003c0c1050003400c070f40d00d030380d400e01c0074400f004910312641030201170000d083c820141c100641d181920003942000b2164560842034850401d000710001d030b4919104001c2200c1c4480318803006 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 167738399 1250 167737149 167737211
    0x60603151206070302040e0a0605030d031a0306010326030f04080f040f09021c0b0f040203101205010209030c031c031d06090d030b06040308070b07090b0c070501090b03010e0a 77
    0x1050410f4064040d42180c0a0403040c0b00200e000100f420070644240001c90702d0050040c1100980c06c803040d40208088900342240c00c548590b41c0e00c1d41e44040007031038000c0d481a901041622a000c503000103103152034502515014017001880700b0550410700f41c0350410340001c80c16503269511811801c42c0d00c181d90100e072503050380700c4000a00381c1c4c00e40e001d0842481440105403144800c50b020008a03044c844049602c40d00c404c404a500c3e00381540590b0303120350381e5a0180a0702e0303150702d910b100c0081c401c0303000c40e99a9000608218107003800d2009805039401a0000c052030781407a50486c3c60882c1c001c0907141050755560fa441040c5d08112841e02072054203200307403000f50610181143d110596268544040b0b401c0c8000b0343c4080c14007500b01c400326608003041500740320702a0395094132844042c2c4180d08108820318045907a43c00c04d00241000c1c00c1000044c924030303141c14000b414a43d102e0340113480321074060004024128100340703910350103440c00e000014a188035013000b0788038414607034449400e0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 167739649 1250 167738399 167738401
    0xe0901030b091f0c0f0c03020312060103060504090503030402040e0102190507060f0c180b0307050726040b070c080106060c0f03020a050d09060315050319080f070c1409060603151206 80
    0xc500c3d90018181c4e9040307688000759901c41400980e180380903d000200141e0040104404080300d034400b054001005240224900e03a40b140007500351000c0341c03810b40d4150400014041185002d12a149034130b0144c3c0020340c10640b1210390010030140b031030000e405210000600700100301095000300051200c8080c2080600381081d001811818200183c07410484490004203041c5918001c0e248981c012b0307a106890040c190340c40f880014508114180404c40c0d40c20b030040710171000700180003d03100c1c00b11010380700d800c0c505040d05e1703204042e40b16510340d9141400611190f42d02c140d00414050b086043c030b042050243c40d0480c80c00400c0c4a01030f2071030088401e032000555010345460304a40e442e0340c0034490840d440031032454070203642c032980358158400c1c1d8000c0300b20900506041d0045000d00344480c20f000d020404006a640710b68030850780001910028810403500e05042c0c0c136034240a60f1040310510b03080001c28030382c0c40083c0504601580d030740f968005a50f58522401b0040c0d64140c191011 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 167740899 1250 167739649 167739703
    0x50109061d190302040b01090e0c0a111009052b05030c0909240a050607060e070b0408070e01060c0b0f091002070b0f0718150c06140702010c0e0901030b09 68
    0x400540350004905c11428401065010343c410b028500030703240e544000e080c640d22802c85182c003660103071504100340100703c10075080084c024800342d0140c401c44580810711500c146000d6003402403403140e000c0100c4d004000c6001c10032130120000f180015500f0302650740e0321303103008840d014060b100c81e165202001c2002c015140700341c0d40e40c0c04d0ba141440085c518000c251282003104002c407501900740c1004040c000c0d00042486500490001e030f800400fa40c4542d625528218131f90fa00030b82201040380e1081200f000954900200c030750042c060fa2609044141066603181c00a00000d0b14040c1c8080d4000e0124801d00b070305000303180e0b01400c48441190340e81882d1801000f4014104c40c0c0c50807401c0d050300010f010070701494030942c0d56204068090411400c10380b1500101d09004204402c0021400101c0f002408074070511402034409400c000035480c2040c0300030709407450b0015550130400c038070b8058006a1540850181503d50004001119a48081199281804104215808070240580c7c560 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 167742149 1250 167740899 167740939
    0x516031e0c03110a02061207090e01151701050d120302040f3b0f0406140112050606011806050903030d02070f0b0f130f020f030708070609080106050109061d 69
    0xa58180b10b5110080030854501403a916002e039024040d4001104000c0c40116041c9602d4056000300103080920910761203002185540500f41c000074556421245c100780c0c0340d81c024215603124200030341c2191a940c1042c0c0800c1440505140080c482e0010344840702501e0b00030740603100074100303044070b03c40718682d6134051914501160326210f2008492015640f03800a001d0520021055a25208540c58944048200b00302c40000e1003501d07000d80d610013002500f1003400001d8020180c60281d40085000e609100b403e080016007020b0501c541104240461007115116000b280c043d42045c44e290007a04010034154440c95001c617854a200040b4901040f2841502c1743e40d5a000300b499900f655140c520301c0854880c00c0d20200e901041c800b08280025081140d50103a45201074513084038010010042441e043c080c0d04201d10075044142c0074402d2031303400340e9074000901c01500280711451801002038a4680d8500450b000c014000a80441c21289403c04000b1345d0b10190884080c041a451081 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 167743399 1250 167742149 167742167
    0x100c03020405040e070b0f070f051207051911040207060e06070225050a0b0c01020c01090308090f030702090c0f070f0c0303031a030601090e120c0105041a01060516031e 74
    0x83d12503460714003401d107414000140f0009881c0c02040341c5240c01c0d400001e0310540d4100003000c580c426110402840007510902c4007142c002c0040088070f07150321141c6813040c102641220030310303113003407643d80400003040c4400300000d040030003540c0050342c40c11a03040000c05481c94101010480c0b0643d404d100703c850b40001c100e5030744c0e0400582215202d65501d0300d280c0c904450320039981d101d20700341c0c0244007141072040100203a00a8138001454107008050b52401d5800e80c80c0107030f0101c1c1c3c54404210411074280722a030340072490a00a03602c0d0492aa0000d00c0406015042c211000c401140606441c41c080c0c040703540c8981c104000c1c000703841c810303c1d0035481c1d12498081100002c1c00e06900264030004d000020300c0d5410010003802440c4e0030400ea400c01032218213000c100c6442603000f2000712030005402060301924880010071140340900b0190842702c81e11600c0f080501440c0010441c40f40d010081c1c400c03130001010103170303c02c901508080311101c9001040d22100c100c030060000381913402c100302c1703 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 167744649 1250 167743399 167743409
    0x703020c060115030501081207030e0a150c0506100b030f060a0509010f08010b060703020a0f02060f07080306033f04090c20071d0406020c031201081c0e06030405100c030204 76
    0x505c140c2c0e889011440d1140852000c2c403401d90b03c140640400203004081c0d410b0728440c050120005d41da43d0340342c0b90b900b5080e0010b111004c18410350100050000910009a0085803000b54403419407400402110302e2100500300019000c04a011840d650b680540c03403801020018075a80540d40c47d60301045201980d403103100c54941c82c02c10444014100f1a00340c6601c182c154010704403501e500c1c0c40b000484600800200d9000c00304000f50409614540058289540124100c035200d1a091003454640851240301103214030000b00540c038002248214621110f160a2810070044c058900004041c0540d0300444000760401030100c0c0c1c9281e100c00028106100c0100c1c0070100e5480d01400380e03d60310103000d180c210075224410341c2c20090040381c0c81c0b42c1043c400e040042c82c000c1d10004140c15504801204102a00080010060351808002e240a8031031101b00020160520342c0000d44010034646440e40101c03400300004050190a10001d0744d5402d080105004031350740004003e00a620038021 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 167745899 1250 167744649 167744651
    0x20607060615030c09030b0420031207030311090a1806080a0303020a022e0b01020c0a030c03020a1a090f060909011712030408160203100c020106050f0916080703020c06011503 77
    0x20089109115039064412a47c019042c07000c0f5846541f1100e03000010400c0041c2d14082c04100a0845c4d1010400c2c5d040d000d00b2610707007a41b81d8885180080542c0d0307120b40c61440317008041c441c1d91401c5d86c0b0000350000300c44122040304a0666840c2010700076041942c0205072074001c00b440082810b80640041c46800180e501340d07080040010180341e00c05154001031000118404484072090511341c2c040d0101d128140100c0d00f86050316400118000482d410485410101c1401041181480c1c038034840036040190305400b10914490845e041d40c000c000c01c0c148907006100419140b40c989800300c0b1421500036000003a19a15090011400c8512001c0e0390396910034004422501d00c5110240c038002e40d40b1200301c078540500460ba2014001990b642070341d15005103829030100201d940b00d440d1a07112a074001150a501c0e003130411000c464220f503590f0103100304c10100111816201c00da9000947d25051552440d110444114004d001c0c5c860084064407072440042180505e2400d5140c10b00d140d994 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 167747149 1250 167745899 167745911
    0x60f0105070308041101140408030c061815070e040f0c090b0a0e042304060606021212161b080304050f0307030813080d05012303030306010f0c02060706061503 70
    0x401111107114009018000441c9200032400203480c8441d440706541e41450305684803030000e060154243e026a0060541c0d901c00160032040d0b07141840081e9100382c8501c0c01c00b007580c00c01c2c540b00303413200300e442c0300040c200c0a9000040c1c80030f4016083d001c01c109002d80100f1040101284480c02843c95141400c0441c00d1900d000540302c00d00c40846a0140080e036800c0c07241c07180300703003480058400c40800008110b034008424a041c0d084126092041e1f018070801b182807032070f1040c0a07051071111a5800a089020082007040c030000e10745458200c8100300307404007003900142003114020001221100001d8803180c1c01e2090100c1040514001c501a60503034407012030000825560784102d010007004a9040e10001e030b0480c2e00385c264103128500414a41740b9103070540e25500100e600907004244412510204407070003884409000c0d04501c0203500442c030714105000040c1c211260340c1007500801407100180411515a2015506034a50102d014411311307407138049151300c03450000c8141c40040d150a03 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 167748399 1250 167747149 167747179
    0x90f0b0a03060f180b0619020d1106070504060f0228020a091505010503130f06060303120618020c150405070e0c0a050307030f090f1101021e030306040e0a0b0f06 71
    0x850b803d04803180040d6041d5030115402880c0040c020010507075901201c1801414a00046003c026070805031540c090540040300d8540900f40d810140c50301d0f03001e94031003410441015080b50458059032868113000214044105c0e08030325100f480d5000c8e8640803210b0580c002c030b100f20305090181d0540300f150b40005031a10b6800b05000c03501918212081d40c144040c04000c15402040150307046803450504202c4520309403210314101203411700c100c540a130703101401c1003416880303903482d420740b004d1520034450b65280010070f8401d20a014441c0341851b500041c8002003000401804c420105403460316200e52516060454a810317562040203003203401d000001e420941c40f0030484004662548bc1e072411500d4029044004205400a94030319941e201c10301d10114000362a0100750f0307442410110b19000da540700082c100b8410381200c0782000c0300034003154885c2c0d1011050b0307544100203a800040100750015034500d070050703e04014041d180303000b09006d00909842c0d026403017101c050b50000441e0b903070302c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 167749649 1250 167748399 167748419
    0x813110a031209090911010f121b08060d0209040b10180e070b041215060302040504150e010c020a0b07020102130e04110d030f110c06180307052707090f0b0a0306 71
    0x1289000380400401c0105006d107600602c030003100024540380030100c0c000020f850208a0350201c1c02d80c5c0c03004400c0c1e010b880000e5402007206d50b024500343c0300300071809490350100b41801400b41009280303d030394500280c03154080c03400d100300414801064010310b40d9503140c0785000340604240d0713070503e0184c007801185060203142203a00b180d4054000030040030b15038507070b035036a0441001c090380300e541c582d080040565100e00403a80607a01842c8031107001035442500004a9608501c2030813240d0600820040e0b00360082099060190481c104030003980d24200224028850000d920b42070086480b400305a03030075807842192103644030b950301d141030003291800c01c01e01c0c40740200001c2c005201034100d81c410522828446842d2a410700c200c032000c0c0706000020312260002401c1000e9640c2c03100310100e440c6010403050006090640b407481902403110780c1039013031411108010082c1205040401c0d5480d100c5c2c07a441c0b008120019000b03a00a4849010382030660210b481040080e003803c80208030150f43c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 167750899 1250 167749649 167749661
    0x5070e01080303220204060801021306090f030201030e0c032e020708030c1308010c0c060b06030405060103080f0904090c06020d0e03060714070506071e020705010813110a03120909 79
    0xc0e101c01075045944003013207481c0440d180340480306250395041c8142c006071070340d02034003015001000000d41c03103500040c007440f41c1081a922280802200600800a03503201491032010740e42c0a180205500c2400107006160070780700600c05815101d5210b00e0000b0101b28000e00008051408402812452100f40703c82a40907040c0090003841007003020442d0503448000400d0100602d00266102680d5007001d80c0c216014914044045061030341101c003006054400c241407118101d4550741036042c140c64882d03030348405000040084100003488142d082000d0103035204200000c10500848902d842c105142c1d8405208500c05441385c03615014583e40203000320800d100340500101100c4c0e99515049403c8005e180c4456180c8204000c240042142030020310f108000c0c585078114010785045800014005000380348046401045040c8916a0710414450304200b040c8040906c40d40d49040840d0351455180055a003c14010000400c000759181440410304046d21030111803a0750f40c24800565031 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 167752149 1250 167750899 167750909
    0x18081b01020f281e0c151530061e020c0d03050a18020105090d060f090c08150f040c0e07030509010c090e0c071a0a0207020306011203050304121e0503010305070e01 72
    0x501807136283c14031846021442d988030702501ea651524810306002c0c20444d08003600c1e9503030628889109111a000592201030340c0f110022100051043d8205c030f2268148814100401440e11511201004da060b912040302e1108282c1d0119600c0c08c3c841090390b91981c50204020120341448009000403159110300030616000f00c2c2e108840402c281d004507074980c1f00f0805590700400a03a07400010410340e106010b030200c1510f000084910345400d01010340c100381e0b80306600f280d00035074070aa00140d0a0420300c0c0c000a4441d0f46125030303112450642c4840c03009400c0381c00c280c4020700402c805a136068000d03034015445000208886812004c00700c503000310781d010b00015013121101080040703c0080003002102d000700c6111005400540c0e480d41840c009a80e401d602a80200c0c413901503160503c0030b5401461046043c030305043c0070380e40150250000400180807044000035642c0c0381390055504004040020381e10b64103110341d00e44081d02503003081c003003907491b440b400c03001140e020202c1c0c0040d0305a80c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 167753399 1250 167752149 167752187
    0x317070c1a0d0e010e0304090b0a050405040c09020d060509160801050a080c1e090f0a0509070f0303120902130e010501080f120315030d0c0618081b01020f28 69
    0x7004503010500500480780d44076000350f50319201041c0071704d0306001034000b50902800100345190208100031082c54984c001d103104510f00380134800018041c00320f080c1110742401015031030301d00b0420802c0051146a1280350400c03141c0c0200140d48100d007a91490340e40c01c40d03d4a82c0ea903600c500920810403680d01440140740c1c00441040c11a11b07024120034601c1d0308840c401c28510f0b4143e804282040e0041d2945400c000011050103035050b03541c05040c3d4000e070440c1c000e00c0c580d07141c92084020002d8512002d0148406c894059003222180d801500c01c45030060424221004541c1c0e00350b008200007a203040d501d51038040045071240d0003081408001180c580101504030200040b034640394005011038514405600e1072010584007404860907907902c030703160b140799401c4905040b81682c00c16a049152008241501c0c1d00090f140b4041e00c40d0302e02006840b59440340c81c3c4d96585d0091083d00c000140045010503a0107940080054032806400c0709014000008044603043d920f4040c400f804c2c25600c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 167754649 1250 167753399 167753407
    0x150501091412010f0c0f03151502030c0d110c0906030c0105210c0a030501060f0c03050a030b090c09040c090b090405040602090d0b0105030c01020a02091902040317070c1a 75
    0x1c2101004418840000100004a90344100820900b159a102c4202100a482c0c11050050070313084541c4440c0704034035080610905081d2400fa0300109564050703000080b0006400c0c800e03940c4200241e40025050394200c030a0315078045405082e405440405850728451051084094200345c2e06990141101900070403403040000c0064800380c0290043c581c51001d00b00e02c50b05105041c070310280c01403160002d01ca9035003003100d50045c1a1401600b00c00c0900144040401140fa44940781c004400d805141c015240c4101480480151055229156101411005000b071014a603402000c01c203404540c100000092540103542101e5541711f2400c07450402d015205841c1401c0e0040b991141c40b4040c018505202400000d515600520301501c4020b0501e0060010b41010000582140000d0008200c0604641d00280909000030a00c12031402848040c0b01081c0c0280c064401540d4403041070401000c1d000391904c070a8001c10015104201180b4001615036810308042440c48102102d00f8a0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 167755899 1250 167754649 167754659
    0xa0203040b090105070515011d06010512070e0d0503031e0105090403030c02011103010303030b1918090f050a030206040c0614070602160b1003031e020618120a08070315050109 77
    0x2a0401a81e02d818401c08101180c0010005d020340060240c3d0300108480e41d5040c1824815900d840f00049600c0400d41000c0c0201a80c011061f200c225044400d400c400750340e00070085401182240c40207410081d5151407104215010001c1e61084090921218100660804284601d042881103640058501c008640480c1c825080310a00381080d000226403018122400005680709920507030001c0e6462100124518199400080b200030f45200c09a80340e090003411143c5402d214907008610755146a43da0801c030403021107110003078100064860383d04890030083d4940030111030850b00100e07030600200391a4014010403503042c02c84000c80f41029800c0e51036900075403100f504904901c5520459500003031420000d14841d0400c8010000900c0c510324000d400341160b50030303440c071107101540c0c05140e5a500040865201d24019074000d03011010044444c10400346000301c940d2918005070501d0301540250b881030007141c5c0c83d642081155504000340501c815940201400140c1c11141000 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 167757149 1250 167755899 167755919
    0x1b0a030c0b0706020f03070905120721060f2a080408030103150b030708010c02070603090b15060d020a050307080108061303030b0a0f090605090c0f030c16020306090f0d02030a020304 80
    0x2c60070f03114038401880c081307900c00c100c00340381c1040742c001c400a00010b10610150800807900058151080c3c010007400e418144260000204440003650040e120141f560501c040e50b085601e401501e514100329050072030010b8400e18482245446600041001a0409600c20b05485101d19003243c880d5007980d00b03680d1092000800e007100e245080780c48030b0480f00345640a0081c50010465440002540200380c04064100003843d48520103061902c0d01c00c402162001c1c0c41d550344050360105102c00c403548900082c0b540d0161901001296201040a03110715400000540c002c01503911901c090ba0384c0d405080b503460104131050360316017100d0941640064042d07000094064070091801c0301d40351321840d8040307020300b55500410450352235800c00c000a05000071115005650303000d4a40c40e001c242081c00c200380c803010702408005080090090024510345064003020395005058400340c1c100f680b1680e58550390390103501410b00440300d00701401070002003215040722880d0040d40c101444c02200003 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 167758399 1250 167757149 167757157
    0x30106030902060421022704021504081009021c08191b05060a1103090a0b09030708041d09010b0a12020a03020a08030c0f07030b01050913080301081b0a030c0b 70
    0x3e070001418030020a43d80b131400d104007241120740c50b40f0714550482d4010000140041d0100120484240324200c075454480c1204541c05601610b2200001c1e2282000100d01e104540c440d070407074000c840c100f411555140d004040058002c0f05c22090110800d444641c4240c68000001d01c00f00007009500e0b00301c10000300b2541d4440a5090031036901d4001c1032008c02001c2074035811a0580c20070004c0009040c070034401c0041500140605506500c0d10aa1580c0d54102c40c03140035003800451000240e020800300216865a135009080913101c0e42e9550a000b684980c803011511000b070004000b6a84401c144a00c4003a031230014810800c082c07a2102c094106d08000c04140d1b08009a100084007580b14440100000c2a44800450740c8807000d003003031820410356446c1c040c03260308001010004207120040082c1551400c580340c804a0b01d0b00d2382400b254a0400ba030007030014a001c4000070750080040b2f9a6400262500001901414a80104240a98140001000000010f00610088200001034 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 167759649 1250 167758399 167758403
    0x7090e0d08130f080c0a03020f060405120d0b060406030e0d020c280503061005101701060809031b1b06120a0506061b1c02010903140c03041806050111030307050301060309 75
    0x2c500d0f254080d19000d0131a4455001840340758032111010b810198104000084010f045000d0441070420750347d690380f00e42091400000c025004103000e61b15102690003416a000020001035481c1e80d04c00f0701134040e02c240380802c0700c64000e10881c048000c0c00810054000c10b0000c01d03113100e11411310100503440b08810000c0f80c81690140021a0325202040310030300a40d820f00041484d0b9150030204810f0710004403000c030070840416201d412003818618502c1c1903c483d428240b0341980c0342207001d880c50007051651144090b070710304240d0742070740041101c000c1c034104194100341511046041c07001910940c241300700103200c00d034006421042664819504501c005040386c7c5864000140040c07440710f082d82c0d510982c0c21142c038400c0007185101030b008012442e80000d111421880d01c01030700800d200000c0342e050301000140c0000500050080360050110086c0008000c0200c1c0000c00c01024107009103030125070510700100300300c034000003524820281581d03014550ba003013440c12005441c608000b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 167760899 1250 167759649 167759663
    0x614270610110106030b04020f06071523070807030b040b0d08210c03060103050601080c0d1a060a02030408010b03161208090d050109020f010e240f040807090e0d0813 73
    0x80b482502e00a0186070011401445c00090f03d013410300400102c40d208100e5248107400412540c2c00081d00764a00e021355211201c40001c110071420319148100d01811b8088402074043c0b800c0004454020381d02034028140c5941c10481072495805100403600d00042075640f100540303000c0d0000410a00c001c0940392031008070f07514803070654420180c803844240d0365900d46100100420144d541c0c50b10803d58040c000f407030b0080c124240600a140783d0702c40c140300340759001e4607000c4150008442100081d240100688000c0ea1008a03000094813500030b03005c0c41d0343c1942800b10b9002e2030301c0c0000f1080c4038040300c00a4071210602c0c01070100c42200c100c181c21100e980040c4a41203140d50b64025202d4a14000c400200d00381200b88100881c0c150504d408505002c52040041c4c1282c072012440040d0402400c203945180010b240420440d005000c0441c0c0e2240380041d01190318400450100c0448107060000c2c801107244071180e5454140700044840000d031700e0700018001140d00290080101d0003058 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 167762149 1250 167760899 167760917
    0xf0709120804050301090c0303030b0907080a05040606031506030b010b0403030203040e0a110d060311011d060a02010207061a0a090515061606060e1009020408060112050708010614270610 82
    0x10201c1c0c00e41d100b0400542d18181d010200b0802c1c55014010703482f00310011030341c840031031401c0040076066034005011800c049555034006410460705520810183d6003048000406103200c200d100c000d480540000c5800740020340000a4800c615002d072000eaa5051b00650300740390400d09010b40c0c944c80105509201e0743c6075840030500610b031000405440003018400718910f07041d41080b8541d6030400041c54100000082d00d119040c20500c0d41c40ca0014084403e16601da40201d030490282c00b4101c0007070112403070900c40e160700c19500030619600ea0400d407030300e8800f15901d0080404543c4126054021441d50580812043c40c21200a00114000c408030010002494980c0c0c000c40313401ea0050000c2c202e4071400e200082240074891002408590340942c5094180b4140588580d418420050300c14001400442085010301c00c01000d070544038020020190b0b68a508009141655a1540166440644809190400c1c0d2900084101401c550080f80c0c45803c00e10078428081160242008803100c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 167763399 1250 167762149 167762159
    0x30c01030e070b0f1803030c0a0615030206030f090706050f030f07050f180909010209010903060207060b19050405150d1515060905030106080102091005130306090302010e060f0709120804 82
    0x5009000a040510541d0340ca910790120303054000d00d4403403c1280721f030b401404654852440007440554a5900400216914080d126000305515181c0c20095014030b01000b000500e92000078428440e1072245c007194856aa03445c400d0310f047c4a10301118040301001c0000070092075130740b41e042d42c10808524205252031440400400d60b600640c0ca2840424002c22010b406c1d0b141107007109401c07840620085281100c40400130740440d0552000804058001c11402c050182c69801684160f03006095401c10720000240d8200c140744038010188035911348404030f940380c50040c01c01451603001424a0950410035100c21400d0410350348403080140e20b03055884500f5117515000002046036803510700545040008050a445050f0050509684103100b070010030340e90038401e00c0d10b880c12800e000703650f450569611100000e8a8201600c82e50038100c144042686c150b100303a050004003800e0b14541d869400c0908031090083d640342000564180c004e1100070f0107010a10180d601c94110315143c15562 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 167764649 1250 167763399 167763419
    0x9130f0f050105100b030c18060702030f06040c06080610030207050c040615020f120306010f050919140f0112020901092408070807021b01020f010906020c12040302030c01030e07 78
    0x440c1251181d4466062010203500403008801808480048500710324140d859000d80b17018145903a0704a19201805500540703c0004517440710b50041c00352641490301080181c0e40340400c0c5d42c1112100907616002a40e01d01c213008032401564003d020301014032045c01c045002c0c3d0000c01055600d801012044801c075a1030f0f1046d00020b0030180c01e40101030b0131008002e410902e802c0e55001958110705ea10300100c440034003c0b242c0c0141c003420105144011034804481a0044280480d00940c2450381c40314820349a5a0101c1121348403280d412440ca40603060004e2550b00c400c00f1b80c00308500d0151440c0780011500038004640c4103241c440700d050382c0c4218001d2540c09950011281020341c0040000c041e51100e00c0e01d502406900f0040c2c040c1c00c1941c802980c49210011400e034806c0116000c21482c1c0c800c0c040d101021113134400034000c0081d6420040000e50200c9140c804920030749242c0350b5100d2149060b20101c0340c00601034800000c3c1400190080c2625240c8500180038240e40803da00d0b6103 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 167765899 1250 167764649 167764673
    0x609020f0a030c05100507050c0103150f030c0e070f090501031a0d060906052508100305030c070501020706030b031e0a050a06020d05060f060a03110904020403080d0c03090209130f 79
    0xf03083d20b5200189800c060142d070805071120b5904103c001c02020010640c0010811100c8500780390000b42c0d4840003852810011680d040403c5254200300001305104c0171012103019198588081d0b40b1766142c030312058841241c0c648034100441c0541c14200820741c080c0c1c2c00800558030085200050104035400543c01604054013110415501c0000400780070345c511503c0e40c400180011303880400c10190110400c00c082403c85010030421000040e00c0c0c48210304090b00955000040307a49a00a075001e06482d0030550103050300500c1138240010340c044c424020521402d201a026141036641481180309021403d145120b45105100003c400184100031203281c40740940c2d40141c507600c0c0c911b0300b101950006440c2d244125040c0c020184659118070866a400005090014400400c43c5a80805004140b4503035400303171000c1000414004034000821103005422010010380613070346825401c403852020081d4016022100083d100b043c4103001000b202d010704540b02c4034100943e26003244480f = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 167767149 1250 167765899 167765903
    0x703031119080612250b0301080303040b040f060207210503100b0306040e070609061d0907030e0a061a040e01060807030311030d0507090905151c020111060109061a07020a030609020f0a03 82
    0x208404d8103005e290360501d80c0006025411705181c6194500080c603a620300001c0c0002d0900000c1d08013050030000000007141e14241d00a0003907450f9420380c2040c240b049050b4941d0784040402c0c0c001804440c1c8100c04880c420603180620310811030130841c10801a40008003210b40095442e10f92011008041024200070072060391030011070340c02d0880c01070120313400d2980780b000b024501551400e5035070b4444c4040e6222865240c0046c488030102245c2d440e0804c00302c006025207207010200c060800c46584110700c4040161024010207080041ca642200c540e4070920499401984003440041d1007204c400755030740c41c11411039042005406280341150419600207020a49801c2c0c20810f500c040c0c05030591203105105000d16210001e40440d0415001002072802010120514401c580c000c840b048400d0040e039089078115a1214001001040d00d401508191b0301c0a9008150150f8240b00700c2c0c14003075024100011007465079075860061300361008201d0b880082c0030f009141507102c2100720341c0214 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 167768399 1250 167767149 167767183
    0x100f0504030503030c09032802090a0f0903020309010f180b030709090c08010315050603120f0412050a0b0609130609031101150906050102120708070203010b060f0703031119080612 79
    0x80212000c05141c4401d00048004e0396204040c4008c1c0324046280070407146805460181d06982e6240c00c1c20020182074805030702644c9004490001d05a002010300f4000000303072102030b981180003a041d202030700142084044500e070a5010700403982c1c18406950052114100390700c08948a42d203880542e909a03c1d100c002075280c00041040c001150701c9a00c2d0401030315400c01c01c60a020001c00c1e1107402d2071400c00c1d90410006100c00c1c01c80c0c030340000c54000300714010b20740b46025000e242c50fa45500e20803400396a0071b0b0380003000c1540ca103030802c01d00c1e0090071110350b8195540074a0ba58003001d800700a00c2034050007100840a54185070a02a004005540c3e8060035a96400c1131007010485070560041030466011103ca4110344030f05004460790f0503003024035951107802500c00039000d0120803005a4020b500854118007005040380601040e034820b4030240446602894905154002d0094180c1e130003182803003075070306c00c0c2c000e1140701c2c4c20980107441c40361986e40140e0380318a465104030300107000e4 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 167769649 1250 167768399 167768407
    0xd08070506150a0605090d0203030c010c0810050a1503050603032503120b010909020c0c0613090507050702060a08060d050609150604060302030a0312021215040b040b100f0504030503030c 82
    0x1800d074034001a80e03140403c0354414007484c20644010414000c1104450060203582c0940703040d95410015200640c446400a218000c02e00000400080040d01d01e0f41c0290030f8242c000c21107180400340300b415114174078a16040c114160313500301c01800020f007500381c06000410101002c0050141155420700600441c071401c041586070041c5400d001c00381700b1007424a4940a510183c0c6c2c840e2518080342c003282d50150b01d1304c0c44514464100082c00607101d52102000407490300c5102e4002c03200007114030001c8100a02d50321400d042ea094450140000e44c048002c210041402e40500d600e01d0704030b00c014200c0b101d010001d607200340c40d00e00309540504182d400707450400400604252840c1d48540706890a020045c038640c0429501c05005100405219134003209003404000c80e81a1240303048a03600c0e904517410003410740f4044076040c6100900a904000c01e80000b8101030141c1074008074060300c070881410b4044c00071a1f036010080d103200e042090030000040828001c03c090350003100c1c1360300e1903a51 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 167770899 1250 167769649 167769661
    0xa090306060b0c0d02060105030606210f060106120e06010515070f081818040b07210603060f090b01090b030304050301050a2c0a060f0b03010903080912180402090d08070506 76
    0x58402d10540ca0350440d480200180023585010804540009094542034041c5084078210720300711a0b00c01a41100d0b104401c02c9808010b8002503080c121020343d102c0840007040794461b5000e0302c8400c54002c80c103a00c000010071840c01d2034a1841c0e01c0c441e003000d509003001004d41d02d581c8024030840040c0d41d01900070030141b612602c249160a6001ca0440322030030340010390b91aa0088443c000c2000d0034100c0420001140f071070040f030b5560701c8400c941c80d20000c04e04001e45100000d040c640000d60700a40f8050b10340110010701d20a1480b1140c0201300400c0344e03840c200b8440060444c45040d145c0601003031100040b16203013401000e01070410700501240500603100004180b00c03400044402d1a40d2a0b0b0420700d61000114801100b40d070041000b0502c004642c0707861018002042902d0707059840d0400316810b040c1d000c8041c1c1c0c090994a0203035050a400400c210185000f0790202d05010020078035807203850324090b4010501e104002c0c2c40015181403e40756242c45421206082c2c486070082410085 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 167772149 1250 167770899 167770903
    0x160305040314101b0206060904020a17150a0507051801021609050f0604090206030c0a09030b070201020d060807060905040e0a020d0503040306140c0a030e07031416090207050d050a090306060b0c 85
    0xa10301c402c224490010054404d4002d55900000d02414042e03144107003c141036480b07800111011301503008824a00c1c50003010440d40d12220403d010400c0400e6902280780700c1d5481c040e00307002b03e2490f51942d052900d8514288588904900c11a05501c01d4012079020051240c800a004107404100002d0320320300758600165005005140510541c030b40010500180d8509c029240c0001c12841e4403a241c10200d402617801041507003002e01004d258074204907259a054000b803095910405051162a54036505140e441084e405054081f0f00340290910240c10701d54031101024a54104840700f61180d074002c42c626140c28101540d468100080900c1030081e203000d401000d0f01c804071002d486162024100710f0601855017071004068442020f0704003108200100c2000d036070040c50101c800d200551686a4540900e07030140d03801c2406810010b4900001c2c82600e041c1c0f50040040c05440381e410b1000c4031035500c2120303640c0601011002c0840810414410030020f4001111891b56a6004d408468 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 167773399 1250 167772149 167772161
    0x80a060e030405010f0c050c06030114130507140f0d1802010207080304060e09040f12020106140f10110a150203010306050a0e0d0302030c07060510030c060801060516030504031410 79
    0x10045510420040003982d0b4080c850500748051454800051b05240c07814605180c05640d03019445000400003088034100341009042560040b184000360208007000341e01a41c40845121010840d9400000c40d40d8050100a1484c1803448070010300c1d2244c00303103510302140d00e01c040411014110207044811135030104055005808103100031400c142c505000181201113a0406a006004100c04601003000540c003030580507a01403141071016285a40c000e0082c0302c60b101d055011507002200c1c81050604446034404104d01401c080d03030044001205448500308038407100340c1480f4003241a004034680e100c80300b200c2002d00b1409660b9500d1410309105850014103944141c5281a000c058450400110349c0028681ca05000d44c4903960b14007261032501810102400e01420901003000103090f80c483c0740d003643e00c102000140191206011694001c0901940000c174400304038000214848940483c0c80300d1291415514068803907031041d1140c2070344c1d822051280d004a9032003580c24058000d138 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 167774649 1250 167773399 167773421
    0x83609010f0e07050a030204031211011518090f0f05031e0f09010f1803060902030706050a0503010e060f06070b070311130504050a0204031b0905060406031a09010e0106080a06 77
    0x200700740c5414041112001d000c0a80a401030020006108071820300035010368004640054028200c0c01e41c4c81005014941440042c03280c035441c0000c26901803d02c0b0b07200c002981c881541800b0721800c070b40300150051008010070355130107a850740f8200010f800c0f141c0b43c1094502c590083c40e1211309284d4015062143e1044440c1d900b18144812040200110241c0b8000303142448c0418210080c4042078420925001c40b50003001c004450100510500d43c1103410118804d9003240c10555807650212a00d0080e4a03d500001c0e40420040260001a003800c40d0005801420000e40220190005046070f020b644101c4040304440104025036405100d513400c05030b41810f4041ca050b200b07608103080c0c2e0703800c1d00545100e00d40c0e42d40803648404282e41500c2c091540a51a5a4480d81c504209801c0c480144a100001030400c00003030f0343d9040a00a03d01100d911100307001e10584011000005043d0040551040e5036892045030300c4008240a84001001c016014000c0c80c503042c1004400c0e22121144 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 167775899 1250 167774649 167774669
    0x71e06020c0105090103051e1014090c120c0f0703120e0f03030126030a0804021e030a0210120c0f0e09101a04080a030f030f09050a08360901 62
    0x405481c1e0740c02c02d0446651107004d203000501503407144d280800a118100050350400960380400c2805203210083d402a10740d00d83c00405c00825000400550709030458002c04c03822024003150581146100c4c480d600005000310355801c0010700d10800c09250000c0d072003600062001402d280e1007444038800d002c15103500c00047d0501707004400d0140d6413488180b08682055120046502101c0380105c0d00f02c01e040e540805599540f800c0c0d10300200311260940e4140d110f48440058018903e00c8011800003044000c2d001d40000b0006400b041422a024080c0c401032241107038260415807650710809240e4851903e44282c450f414150007420103c0d100912402002d070356080c8201c2403400e840303010844510707003d0106080500e0070702c810f680c00f459212140394410480e040041603002442c2c07043d2481c180d074040146c0304440e110131080e607000c1d500140c4582c00c10b048520201c1d00c1c40000705000000c00300c04181c2141c00c0002010385121301841c048022406407103030b0981c3c1c5004120503005000c0000c1c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 167777149 1250 167775899 167775913
    0x90607021203091f0e0705121507031d15011215090c12060c020c040603260c19020319031d0310061806050a120b09010e071e0602 57
    0x41d650365411401c48072407040100009054910401c071008413407901000d05510740c4e20600d4003001400e0910401360190051803030100b0075003018000c181d0f520051500a05070002c126525126040c0c02070f10000c101034803020310ba4020700340d08101c1c0c0e245c0c1d017000e4000c01440007070496807207504006070012a01559142c1030000820b00691000e450300d058200000380c0d64101d89049261450140c1c40609207403802c0184200380110ba52209071014129026200c4801c1210f00308400c0b0b070a0307808024103850600100c080c07406440450408050f440b82c81c2d883c5880f2541ca02145085083c1091401000000500c1e03001c6080a020500e030200070342442c00c40d11030499a000d0000410402818042c68440c1131034122560200540d110400250f5000c001c41d585450816001e10022280b10700070608150001a241c01c00754040411100c0880100c03080030040d50746c04444884c007800c1040d5543d03c40d0800078907a64107011030340042041800050913403c02810300c800c40149980301e1130564215130b03 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 167778399 1250 167777149 167777161
    0x90403110727020306030a0219060e03060105060703030209031204090608210316050d1404030809060411010f02030c0102030916090b090a0203090a2001020111090a0504021e030a02040e0906 83
    0x42c081001c05001240903840b41e0700e000c00700c0d15051000704040c0d1b200011000c9240b00001c819041d8003544c4036a514000a6038038802456600c080078401c46403c044104001000b00784658003402001c14001c00b59510041c0d5802c20020079002034008401545e0303101001c0192030f00c200304204034441e0543c4007500c4040c5150390740003c1d010080980011255041c107903200c9134800c2d0120b079443d0384500403c10000c400451717427606100c001c980850106130400c01148060300001100740c40f55600188480c002000038004580f4400e04c1035100056100900840a0b6a075080c000785228144500080901c035091095604080c90668800400d541c50914403910940325131038020345c0011040d40140e0750313881e13001c0c1300381c0f400c01810f10207007041c48858003401c0544d0ba080f007803201c4450709a0080c4910310030302d400d4600a01c80c0300203c6d40e0184c0b5900d42080a401d294003c0c00f1a41c03007e01501901c00c0541c1b400c52640c1c3d0003121803524456001405000c002524a201900729500b00c1c02481585411 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 167779649 1250 167778399 167778449
    0x1903120b031f0c0c0f1b1409010303140706020705030316050408070b1803030304060519152603030f0901150b070204051017011a0405090d08040503090904031107 71
    0x40b807600c1080d1900c0c0c0340040201d41c0280c000041c1c00d44e00c00c0200481034420300348600403400340c1c200350003946030340748000070351a010070740328440d0034001000c1c035610340d01e150b805136141031154000b45c80102c024481100410000c0c07025000080c01500956501d2030000c0100c2c00c00c40181031401c050050030312003400780b070301c000440c0c2080d2200c400d085a030300c081c07160310001e442c00c1c8440141c2e494840001007004211080e00454000e116600e19100c41e40000320440003a07a8110300321865400301400d0401c02c4e16140d81c3c003549040d205142d40010700c02c0300c0c0115410341d4412202c0380e0079a90940e041c001001400d1054108003000740b410001d181d410440503600c81c0c070422802034401c94541010451042020b01010020100e820800d0300c03514184c1c80c4203018180ca1045550201111542154a810940243c1c0d00c1440080e020b4031443d408002d00b0340702144c1c050011b40b0684014080381c842c58072070203d00c0e8015030003902c50910b043c40c5031032091724014040d084462000040900348050180c0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 167780899 1250 167779649 167779693
    0x60c0810090b040f06030f0201030510083003040c06140403150c02010b0319031805060702090a02070c030b0a051f0b0f070204090606080d02010203060f060c1903120b03 74
    0x114120100340800900000307000b44c88901504844030745050030000401000103c2c0510451003030700e0074401030b6501016006070162510442c1d11fa5009810310500020100da58400303000000c0240608208000300080420b0700101c1e8115205e00b80d00d0018040b1a801800010050026511080c5080d0940da684140d2900300e82e0440d811540791140c00800794001c1d00074000210020302112100b280c02c075001510f03840c0c1e800040e00131408018200000550000b2044252007028005d5840c11080d98244113869500410341d0845580c01c0c05010001a00040e4120045004055007445400c06035080c07400c41b08068007801441040c20402900610301d404140101c0c0d454945490300d48950804128861003008070083d0701911b002d05c0d50f020068154411010303078441c0c400700d448202080d6400c0c1d00301d100c20f4071440c0c0e00c40b44190261409286c20002001d105000c08240c50201d541c440321140d4107d9109002c401182c64800500703241c400c2c6100b2586502e00031401000b415941410391101000c1d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 167782149 1250 167780899 167780909
    0x9020a0912051912090b070b13020d08070b16020d09060e0d05120309010b060703090e06040e06090109050f0703020607060f0b0604030501060617011d0a0e0d020109060c0810 76
    0x1880001d402c1c0b000034003a0141c0b14000f00d1000248405a2400d01c2e0801c001c0d407803450101c1c00e0b4880120b4800303c04019618036952000f6141119141c125000810844403c030880c0c1c0300a540e41c0c4000010907002c09044258030442d400d141c0d605040a408034080c22150f0b4000441d84648418040b05038070854110845a5a08201c01502c40b0317040481c031541401180500244111041c00c0c4030303203881400451003800303c7c40c000c01c0b441d490a020848135124144020b8001843c0f000180a902d00303c03900c890300305500070300003e0001000582242081c000315074065241c0d6442d122001440401e10200300e04045200c0906515030a40d070004410303016180001e040325580703803490341e45242326a010100542c0001c02c4561155600c4c40e200d400307040c0c94001d500000700352201c816811558100d0309410380f50513241280d03c1440c070901304d02070008001d0a00000c0c6442d5403111100c0c0c07009100480400d84154004605880113080480580c1c0c103100c121002c00403200100004202c0002c4004261a = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 167783399 1250 167782149 167782169
    0x909100902040f02040e011703040f060e03011b020a03080a05070c080c030d09080705010f0606080112060f060b0c12091c030905060412050105090606060f0a231309020a09 75
    0x3452500108004142a52040c58141e200042c082000254102c03064100c552008500340c100080a550a80701d000b10f101f80c50b40d18451010900c16107011310002c0c0703c4420041c2c000a0021044107518000b25198900d030409a0015441c40c001e1550003200ec0d0b078017800d4400103021070704003001300600c0e01031903000243c03506d02c0c0400c0f01089950280100d401002451805000c841c3d01403c10844550012100f200e6540c80d10605104001c89400b5943c211001c42e01d40c00081d0b031801c10f1100b1078a03070501c0c045420944d1803002481503000e900c00e04000d8104d20a440303031104603c0b101c0030300d030842d2501410344d00130040c0f0088940d03540d104518410000f58440aa03c4044149801c3e5150034090b00142d030302040105012403400c500003100e4246900500c000d011a49800c851b80e40c41740d40a40f111034102c10100400101140311000802e0510700740d2510214401c1103110214640055000e424404440001c02c01004c1c1640740c40c1c0400703094803c01c1145880a885d80c007401c51001031160380300d99 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 167784649 1250 167783399 167783411
    0xe220f02040302060315100804020d0f081315090509012d0e010b07030306050d0521090a090609050609070e041d01150302090c070302280f03050a0e090910 68
    0x211501990020756020b01040e48038100b05d81d110f4001c020240f16140500b0714501400b500d1031145091038007443c7c000d86890081551501d13041e481e4161421b045d00c000804200e140300c545410390116008140c07501e030015983c411380200034004000d41d4072942c85400d41c000184041243da29069521b02e0500d041001201147d8205e5940c0346020752005d0b40d8104110000140c0c2c2003a440184121403081d6000c000403900c0d00100580303807040010182c219801081d00810410802401c425008108083c04d800d00010000049001206400917098191034200401910700140140f982119013122070706072900d00390710001c0401e0092103c2c0d901c281e8441038403288580500800b150a01c0e00107009105482542107601401c40c06840101cbc0107001210018240f40703664400c1d64412076043d80035085092210301c035030300c44c0568003030881e82d4030600700ba00700c00040306480c00207103261090321403944440141501030b00c1c1600e0004620700818a0104000004d8404141d4050811086c1800104 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 167785899 1250 167784649 167784671
    0xe01030e07050405131a1b04030503030601080702010e120c0d021f1125020a0602060606071103070e011e060201020a1b0c0b0d0b0f1206070804050c030106060e010e22 73
    0x34800c0c00301700203041001601c1c4200000e0140d5105144aa030042c544510007916007040100389201e1071201500d207401c103002150b1190310401005030000311503c000300e598464009140d00b05440c0361400b004400d000036020003a03030000d105511080c1e400b80003400103582614010416208100c8144041c180d480b1400021500d0140599aa40d940c101c0700d0290902c211881d0031003220f090009921510b80c072180007070345610024400384641000340ca403d09041640d0744802c070201d04c801c3c11035898041c0440100d401c191100409009140c28800000d414002c4100c00c4c80d2010140c1040d0116401080300f0303800700c1d8104100c001d205d80840140c2c1d840480318180f06441030a96004001a600c0001e01c0c031010703075065008210000c40444a100d4207100040c1040401e50803007170369400704c0d00310000107006a80100342c410b5200c0c1c05136080c0c0781080301e584c0001c6c3c2114590b0300a9000705d07501e800068244e5a004429041206080c1d03125641000c901e5682c0c4907a9441c91f52225006481c1c04038214 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 167787149 1250 167785899 167785921
    0xd0f0e0a0210020a060f091509021e0411122403030415110706030b0102070504051b0304050a08030a29150a020f0a05071a03040f0807060b09090d0e01030e07050405 72
    0x403403030740008042020286d00c5078851301810100700d042d2a00d00028151000d0307070189200c1e040526900500c0041c212050003403c801c80402c0b01d00050f4003580d2552081c1c454401200284080f04500c00090300c5450080b004074100c40d1a00c0004089a100c00c00d44021924008100e0b02912166540410b0190311840308841810506d41040001d01803c480010496056003114821020980076a50540e0700c071400e204c200c3e18100c80180300e61403000b0750f1340c141d0312582005582040c0210142e40c1c246450b40c84100035503105851219a1940c4c42c108920b04641d41041c03141500349088200f1003101001001a00c40030102103d02d80d02d000016120310341c2070080064600002c041d6003511528403040c10102d03200c081d00c2c81621802d14122041041802811040b41d2040b41d1001d4005031405980d15008025041100e0481d01140e41d154202da15075036400031281300e032860340c00030f0203042e0324650003e0202d840b2000e800c2c113260419044954101000c100407060301e2007640d000076903071742e0403154030303 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 167788399 1250 167787149 167787163
    0x806010b070c0801150e01170a111512010e01060f0507030e0406080a0b04050606010206090d030203070e0402070f11060c0d1419080a1a06030f040201030b0310020d0f0e0a021002 78
    0x49043c0d803a09511700c40840d00e405030141201c4003118114a00da80c2d030742040402540e42e0124001342d411400c40100010300c07a10342044080405049000d5409008403a45542d50010305020407980300d000c0104407011a00c88094090302280c600300001154590001d0300a0003040001001d0240402d010111600d0b1644100020075032031089402003501ea0403c1d406805040d1004c0d2254090700d00015415400054254040c01c1c17050014060404000c90031402904058607070f00030403e481032100750315503860026001c80c42c0036030100305600c0d4891400f050700820000341c2c10700524061141c0020203001042403400c03c801d600709030308141803034107150318a8840c4060b054010b0b040569401d201c164401d141c103100e43c0c4807c004104042c0000d1460707002050451178158450001c1000406100309044000d0300075106050105101c0f03a4000000c1c03d103200d041a114103d0313070101d22a4240103041c06508810400d0800410600311180c454540760075851002034004d13072410000c800041d208224038 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 167789649 1250 167788399 167788409
    0x2901051606110909012306030a0b0d03051801080c04050423040c060207060824060705011e1107050d030b030f030c012a0801090f02090612010e100806010b070c 70
    0xb0004a8100c2da505542ca40042070300c0380c043e03c0601c001045030365505408000a180700d003070440151a01c00100700c2c4580c0010190442183c40346503039622515600d2a484030144203803a1030342c441810200f558250448182424100f05181c4280702d0b4101c2c000080342c084c1c4206850118840d6500a54220011100090800b551000d0000c000c184040004064166a5280d007900c0415546039030884000d642074601c102c071490308a01000c80e80020040c8610780d558040c110034240351050b1103160031900c12441c440c09036608144015907400244c480d1a0202c00030400840c01d100c00b90b1075540da03660b2034850142c00d15a803145c05042c00d540030045100820941c00490341d80d10000a802e901900c110000201103070910904600301441c6070102c034108150030360314cc2c0303c0e80c1c3c6401c428a001d41102d03a030203802660700308210b180c0e94484800414450b038070405a04980e51400350380c0140d40c0360043c101650410269014840b00c01c0c0803401c24115084076110720f80380c880500742840045019441 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 167790899 1250 167789649 167789651
    0x1030b0a03081b0f0a11060315100f020c01091206020306040b0901090227010203070b0c040807090605130605010503070c0201090b040e040512090a0303180f06080a2901051606 77
    0x3c80c4042d0000064050951000c11040c0e403400294030018903038800710344d400200704606243c1d50101a080480142da8411200d111f00300d0510408d02c08980441559002100088d608482ca00d019980400c03580e00d110300203103860031100e8a40013900d10003a2150b40300400140c0c0000104942e41c0d502d820040929000614041084d40d40300b2a2100940c40800c0c001100400c5081203149802300d07526810741c20b10180c015514201407940c0e90001d80c90002c0410312442420301010448400401010028154020b4000382503810700c01040b04614042d5071541c42036080603001d000c60b9030300c00c007900e802c003559080140404078548016079040c1380540128540040c08200000e543e00c250a4450045000d031054400c0013100c210060007511501500300c0d0031036801042000028400c404100d8034200c40b620aa03905900c034030800c01c1d1a1110345c00300300041c01010078008210f03100c0c49841c08070518114640101240d0f00d1501b8900c20400d010396042c0300d40800c07058400e1a0070300000b45010b9004034 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 167792149 1250 167790899 167790907
    0x61512010f0c0224010e01150201060e070c0507050604050105040e0702030405030a1a0a0908030105010c020103020c07031a010b0c070e040201180e2d040809030a12020a0611031501030b0a0308 84
    0x30741d1041c000303248011845640080480a12130540b035103060b1541103640c03041581c2004894110003611444100856503602e03000903001082c0e441880c05a0040d60780c04580c2501800c000b894540c9540005100c5c1104000420143c1c0e0044121011194140c200700c0c2c0c95964050240c0c203600540e40302c6078050107030b04405402c00c41c6d81d906070380351b500410340703149566100d681070b51044801900004007251000c00c010b0090b50701070120700340034a01c140350140c50101c208048070b0401203194011651742042c0341030681a1b40d20a00800d0261528010f96070801c0790211510707588120314821140300c458004082410b592045418410b981c460581c1c042110f541e4a4400300c05003c100c40300f03410584031001403a8030788100790300032403e4864500c01c2e520580b140e44800c0241e5200c04e0100358540f082c061041c00080d60008207400d20481d54010f410803640c00d0410b5000d84404140c0100c0c480c0e4100104181c0d0907400d41281d6045500780380004203200002c004c105030710b0b803075040a0700c03840f0082 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 167793399 1250 167792149 167792171
    0x30d2706022b0f05030907030c03110f010807020303011e090e0705030705060c070e0c0705071d0604020301030b070f09080f0a11010903080304081606060e1602061512010f 75
    0x5082480007503031208180d081d40e040040c01400341d9240b000c0e500081c4181200c1c41c401d500c91000356401607170040603541140e80d2551840c184041940c01111001c4d00101c00082a10301455401d940c5602820168a589403a0301d00942b2844140541c62441c42c681045240100841600d0005082104010048404c00405007556200c0380e00c24070f882442008008582d5040c03950558242c414548002d040d42070a00701041c031407020080805090003400d02822011420800005008260480d01100d442501503120300e07403203000030078160249004000410000f62103003030a90707000d0802d15020040460a01d012104020154804004ca101d401860180d01c10f02207614010302d4480d108a020360746180c1d00555a5100724800900b000c0018400500481d0706c01c0c008040360307980581c0100404c04c0540d178080480d25581c1182500c0303503c0b801080401200080607846000c1c81e80020302c1e2624148181c0c040c0300c0320381c03230515010380d404460307642810000350801401030b85800c40500c0304110755 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 167794649 1250 167793399 167793403
    0x150c030902041a09010b211902070c030b070302031b03060d060c02010c201f060b04030303060509090c03031801050d0903022d060112020d02030106140f0a05030d270602 74
    0x10024440c4501104400014040000703c1190b094000c81000c000e4012065035189000c042d0007000c1d02311a11912168280c1030100d48020030080e807048048640e00c50640c103002c00707550801014801030500c10000d00110342d40b110600c2e503018510401d4251740c0c1d900c142c04a840d25200c000010001e034100b03600710390410f40640081041d0101551006010f00d44005c0e0301188000402c1008096049510b40000e20383c003c1440030b030202e40031080460002e0303550003102c4080c1d00c154810341c00255030b000d0a01481c94a070321055009264080104038041074880041d81f01c0c0702c1c5031840c40b03111040c0e00005803942d005a054450320030007080204000b03803540c10080e40f641c030080c80406440030f8238080868080449528407040c0f04544005041a81c00d210305600c6280c4604c0044c2e83c84155900c4d03510040ea000d004100c06080e01d820b42f2642900560240004000792024003881540d2001041c0309a860004402910041d1843c0c08130b400d40010701c0707021000c0c1e40703c565000c50540031800800c03600d0700 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 167795899 1250 167794649 167794691
    0x1112030301080d0309110411070b09071802070b0121060603060609050c1603050a050f1308011a03031c1107080702031912081b07030c120c150c03090204 67
    0x2010680d40b04401460084044400800004250941da0312540c1e0b103d05045e40200c40258990046510307000147d12072b00c1d2401e00847e9440541d0780104400d000318030221160b0410340e0300c0c6007810f500f043d50940c0da0000290f014040d5004014122a8018042d0950741c1c440041c1030300507000300302040e120b08003000908031078082e400640d03062401151040d60040300700c95050644144809000180f0342d003c9640741d101c4806001007020134401c1d07801c02e0b88000020108030300d408080803a00d61606030f580b401d58a4480d00314102d4840803010540503200403040711100b032010155107034610000401c440081c940a20014030341d40b0042000810040c4c2c1800070101c0720300880c00c0310380b4805800c50b8032032400200d03000244540d64064071100e0f514054000c1541001042c03004800b01002145210f90507007080e407042d4000b4411000d1a8140300c12140110004402440d15401c030541355120050240040030003880f0103a61071f500c4100c00c0788a44d01c00f210310783c0e00510520141803407040441c19811 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 167797149 1250 167795899 167795909
    0xb0c0f0d0204260604030c020d020a090b01020609010509150a0f1b091a1611090c0901090b0405060f130914060405090705010e012a060c08130507121112030301 70
    0x60802c0748603c4108064007941d2254012001008a0380c0c071036408441c140d04c8800100c0c0c204400386400c80043c0c1d600c00d05c00b400340c07003d944000703850300003030000928144c8042e04418440e4540002e0040d011004110088444684425030b10a5251800458001d11030581009030b840e00d02804441510070800040b01d104a59079224000035450708140118041c2200c039504134150b0800c01c10644179840d90802e00103d0088041c041021451001304043c8281181c0f04400302c0400201c8810703035a00880345101810422804900f8581000082121846001030042d0440808a401c103105142e803400040074101d40c4506001c4100380b407800300c031102000c2e6170242c421400c00740020a0310100255071000c542c0c0582d10451859450001960170310180d0500d41035424086003040d81c048100c0c3e0281c0c0c8250320400c0c00041d02c844890700100095800781921201808880c004804100c002a043d0151554881d805803000c0140c134010740ae44515619103600320305021455801c420000c0040d40c12a1 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 167798399 1250 167797149 167797169
    0x140619090e011707061b0f0b0a0f021617190c060c02030c0a02010503062407030305070219080f09040f09030201060f0f1a040317031608040f0b0c0f0d0204 68
    0xa601c030030480000d202000c1411042ea40085010030000e44112040054946c6103a15070700c144001c1d0b12240c900802e02507041d54a500d0503400e00801c540c00d1f105180100035418000c50501500030f41c81a11141c81d405d02034208690449030f001e84040c51811111024003501c940142840034000280a040100d03c05803015442e00840d612014000b004423280700c3c465001a200140d803660040d160740d0800f8044d123030012400385100100e800c04284900700841a800240d07120340c09481d0080c155a0002c01e08011504102c100c3c03842102002100e041c566030110b070395030700d07000042c0c540e2800f4041e00c010680c0c0181420855101d0f0101030b0311910740745000340d0080c0001b13a1686041d100b07261441c0320f10728104003000f03401c000801c41d64045803580d4010400749441d080d40d94640c4480300c05041c401c42980a000001e00c038000074204403904035503032a17062000d0180780c186caa41740000d80c0c031400601400d03200800101da0b0700e00c030340840e27102d050b203448096116010943c1100c0250841e006101c040c1c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 167799649 1250 167798399 167798401
    0xa1508150a06060e0409080f0408010f06050d0c090e03090904080705011103100302010c26040e28020a1106010602150a09021c05030409021c0c0c020307140619090e 72
    0x101224040c0c1c034290303103160302c134600075840314820b000084c0301008099460800074042292001010b01c02000281044000851714480c030030595004c8520a82c016031103940c2c445d5501000400a0721907004072200c0c100f0015131a03c0c1484004e09503c00e08440e180e208941c03008000401c6001d5003d4010240a03800800c0f010151380e000305d00c030788015078503c0300400000f8400c000542c4100003200b0f01c0c40c8030340741035499a4035102400382141c0c0048500050000b020a00b40042034210800660006210900e0b05119040420420204000d45404681e040d000155000824081d030340401600058004440e159a541d0750002d460f0303403106903401d44180801c00490421440c81c0111151690014940e19807501c10794612070300401c0f07055044602d0b0009001c000b481106030300c0640b8482020208004103d460081c1500443e80456044030610511294690241c5c60000d101c500b6509103400c6010b070340101800007103260040c896100c851030000c0c03401000f081d80c03215248086a401c56003084c61 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 167800899 1250 167799649 167799661
    0x3091208070905100315080304031703010f030303020309010e060406020307090806060306060d05160b1b0105041505190f090204061203051215030a0b01140d080f030a150815 76
    0x14208050381c500d00060b2801d101440a4500080101d104004c80d050004e0f4100c151081d0800c00c12159220206030b0708041010410720840c0c4044a0b601100411200d18540c1800c41c44c001440650001804150b4080005443c04109501107210300c0140422580e4a02d02440c04501a50044400c00c00262545a000942c0c010010307255010b1b800040c0541100e6071400203210601e565500265224031544c00305035004a205c9c44000c018291142199544d0305940c1400754052607040074142c0307240c0c9030000300004034041703000754480b00c0320440c2d0114603610b48041e030a180e1a410071042c00703483e14203c03e5240e0344640c0d62041d0070301482940c1c01d0201f645d032402e590b141c103150544082c000c0b034403c00c0450300900c010704400340e0152000d123100024961040201c0e2400041c032104a41e03030143c000040c816140c103650410820f0500301d4200c000c0490fa6034450045015a5810031088403000c00460762050543d08000e5180845c480c0c3e408015030382c0d11903140d0f2101c015141040a8143d9404690 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 167802149 1250 167800899 167800907
    0x903030b060a02070b1809161d010e0d0809042d18030e0301090f061d0d020d0819140414010c05090d0f020402040f05010206060612061908010903030912 67
    0x120b00c94141c000e481400d140055880c600c0d44001000410aa0203190300c038500d59900a82d640101a80f181010504001c4400071300100c00d21441c080200d40445500540340c1c4e40041d03103c0f85014151220140708040785840012800b07800a4507600605202282281c502c80c03001001219181c071441c443c27104460051030045030190103c140301002c0070801d00300400d010f020794007144030001c0c00000e0000302a49400283c25044c6c13008540180d1180e404d106901d02c40301145c0604c0c01c191001d40041c13052170b100030f55180312900508051001d03c500241c81380403c4180740c5100b0003440b505000c0e41401c00c00c0c000901030112000c03101a0803150320b441c0340c004140703c0c0307007100d4180380c65141c81e001803e02000404130300d14004848948002030360031b0058650340050310007417040824024a16003403000283c100100100068000c5606100d030000c085410105150072900c2514441c01e00424041c450700740c0300c1075405c550460340c00c0000c4002050380c96030202d070b0214060500d50b425400507820440b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 167803399 1250 167802149 167802157
    0x130e01060206040f050a051b1f09170c06030a0618021303020d050109050a080301090605221d0a08090a050f0d032601030f03020c0d050607030203130f060903030b06 72
    0x1a4401d2000400043c3e080d01003e51017802801141c2031210640e0b1003614002190203940c011030815141c3c1140c83c1002000c40f03114550381481d8060f4281492001440b00080c4d100b411003511507601c003000900d106200c142c5020501400150b1780780b0f0403d06003000b420061148108140c1080e4100c103080c0c0d0079200b91980c58501a950440981c0340d0380030009680c1c0c40001c290f0311550382e498000c0010324108018580144500203154403989403d00c07000854102d548402c2c0110a00b101c1c488810551084100c1c42000b903c1c400143d1102c01c0510031000040511601107910131032100005203310313a005010359100031281d05448948038410301101101c44a43c00750014801c8001c100028003846c070000d00350300c203140c12800106090b06507003100042a4400e0b28841d0120380c0390428107505100c150340054054650305c42e0242e02ea0390720359903150000c004000705503000c000701c3c03000300c030003800c102c40076420010082247e2514184040202002c52048001c41c2c640103107100181000c005031 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 167804649 1250 167803399 167803409
    0xa0c06110a0210091d0f061e09040507150513090b03190305090d1b0b12040b06031501030501050f060f01020307300801440f010c05130e01 61
    0xd8080d0028030b80c2401040030510340c0c2101800383e041c5000c00ca500062020580340c094481d010030981c1000d02461000a0303000d04154022130f40407410103840340c404500f1102ca02030030b032a28446569242045402c018482d049601e42007030b0326000201582d84200945031215540c2407d00390b466850303203c1000c84001d44a00c0c2d03050340141d1384000d02d070a405080841c0050003401c10918082c0414000b903406006140103c402040da02030304441283c914842001401c2d41c00c403004e1908001501a1030900340c0100000c01d0461200300140b10380d01c00b0321034102da000512131441e05550b101c2c501b540c040c040864102e00d814034480c0c0001e096180401c03480e04030b080180c016501e01115034071105e0701c00c2841601107425030130a6110f560429540d00003d080500341c1c1c3d98002c21541041050030078409019801806424295802010303e402c0034201d1a00d4140c05491042280320202c0184c1460104040a80e40d13500c4c002c20040c441d50410014070700508982c02c440b14883d120314840307012020038010 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 167805755 1106 167804649 167804653
    0x7140418050c18060a05120a02041403070315020c031903090218040804050d0f020a0f0f0e010e0a0203064e061914090a0c0611 56
    0xc0075001030210180e2850554202e0800a10712518000c0c10f04c41c00000440e209007030300641c00c171008070902e210062000d02d070814010009401030301c02d41c4103d2800c00205c2e041490003140c00f03025aa071000e404440307031100d0f9843c840207410010a00c0c0d4280300800c02100802d00080301880c0d040601e0b40c0105003000c503881440400300c1c49019140303030950080140b100046000303040c0c9060390002c0e1510050b035840303410301440c000c2400d1300194100f400c0d41004680d40300281400c1003078911001586d62134544d00e02c090031000000b403140f0354015940c003010540b08540d580041d508050014032203000300f15507100401c1c00b85046035600100880944407600c0c14484004541d00d041e0710b48094441c9400d4800d00c60380c4840c8010000e000c2900600c240340c03126000c507030084030306071040200414180742c0304180ca903690450b04d90036941458110000594144121800104d06e051800 = true := by decide +kernel

theorem cover : BRFrame.Cov 167625899 167805755 := by
  have h0 := BRFrame.cov_init 167625899
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167625899 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 167625899 ≤ n) (h2 : n < 167805755) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
