-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2920
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:08:22.680813+00:00
-- url     : https://prove2.me/submissions/c7c41bf6-f387-42e4-a422-a6937863dcca

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 525000000 ≤ n < 525179856 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 525001250 1250 525000000 525000031
    0x4120302060906070801051e030c06031810061d19050f180d140d06030c0803030415021c0216020a1403010e0106030b0f060102070e04030503040308010b07170a090e01080105 76
    0x44e5001d411024140c410180144080e010b0b240b00c00d15528131040d281c140d2500c05c1000d40764039562441e004500c12049420805032442c3c20040302e41c40c1418008803075800905000e8144138242c5507484810f01c00c001d404054030b06455400b030a080c180c4043c0c1d24449040e00b0302c010000b02059500380c95004080442e140358400e20000741e01030300c824010f400840050541c0914249500480c0c010306101e0b1240d40d4001a055504e80c0e4050f4130320b2241e40600c00c1c13600b001c020441408000320801512004401c01545405131011102940f41400b02c0343c02165980402c15500d034900340d880f10502d50354007401c0700c500561900c400b18000200300184910941c02d00d035465225801c18018002203a620844107590341d00d03410748121403604002c10031070462082d800002020f071000c5019074003860107034441302c0e603904043c10700400c4610f058200d414500c804102d20800a000c0c5011410b07800300d195a8680c8070b0500f0300084034051440c2d801000002d0300c1000101d192038040d4042400b8800b2027811194 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 525002500 1250 525001250 525001261
    0x7080d0909020a09180b03030301030c0312110606100512070804051603112107060f1701120f11030d0e0301051506070b04081b010c09051207061404120302060906 71
    0x59200e0f601070703100002c60f414001c000a0b10725803601d65456080240100d82d95000101103859a00240d00a07103142288071400c200b4000304401c0e414200c00c80b845c001c800d07113007003e030b5040e6030344006442503000381811100c1d081200d2268090721100b017500b2001c42c1103070410230002040050251800d64050140c03c00302e805118401911808480d071080c480112841c480c410402030380800600516030280244030071b11000c000307000301e45c0030380283d1301c07103540c0b003100c08030010070741203150100031035289010b00140b01c0000052051130f10654051108407aa1722a441c10094a011407089150103214900e1503000c3c0302d070810b600c4444a40260001c104640e41d4001010304141c0900d4144c0d00100f0801c991008129240c5a8641c010701485800b85040d446403560b0851004413800350340c160350b441e01c49148540c1d02002c9030001b00710481d55000800e04c20000c6a8030f801c6103109807000d104041c05000340540c1d2a5058600501099062446c56800c90401948840c03084442d04020b005600c000344 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 525003750 1250 525002500 525002519
    0x200402070311150714070206130e04061b09050d14011a0306360703080403060605040f05010513090c0803160c120f020f0117090106050f06072006070507080d09 70
    0x40c07240d0f0085e45c55590381c0700c60581c082d507180d10104090380c02a80810104548600d0807510340000c0001000302125854641050303c100c1d509142c800d03d40c0d0f01c0a0f0340192283d644010f41c502914011240c00042d48180d103820703015440710328000415035080540544107503200c0c06072550062415021396456a40b90078204032841c1c000e50702606825112207220903030024501102203614041d100315414541c0700c2e150300c0c050750401d6000b22011510b80a003807040e07080600545106071598681404103504200004000a06421041c500c0e1541c0f403d0a10500c240300c2110700050a901055a40c1c0340880000340713400c0c0c03030389a070706840c024a14540010484a14003118051940144410b40c0d43e6145601300b0041945420401c0e040080800403420040c040c805002d01941c0f000c40009038152a0200303201c4642400301950784650f8042c440d00300030544064541020078510001c0208080c00075001079400e004401c0c000d007241c841c04102082d1060002981ca10f00035041d01c0f40301c0e81c0e131f90317406208 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 525005000 1250 525003750 525003793
    0xc010b180408070317010b0304150c0207061202131d060a0803070303020d1113080c010f0905090615160b0c030123010302090d0b0a0f05060904200402070311 69
    0x24400c108000801080c0d89001404025200e8a0000171200c4000c05030141294282c002d4054800c0000900040040c10038261500300c1e165242407001180c2810007a440704014030928043c421034809245040c0c81990442e0f4146840c003040760703151500c503103242c0e55005800c2910201070341e02101195103498282d01440484800d60002c52030005c0594044002c2d40002312118a01a1101911602c0303217095006020032000e5520700d50360403442e10640350b00d046c403002c4a00d418801d440b20f8069009500c06440c4c3c0c203403201520a04581e89a032804100c0101494000e00c02d5402c002c1201e40c0b2000c81d0034240700140d4007481c2004501d0300c0b01c484902d00303440284a059094402c186011151400880c03d5042c14441410010308040490f4041002e00002c040219020190314003000701110041c810203445500c900c5041140703150860208110130400f0b400a400016024040c103d4000b03a240c10400f8100044c1003551640103c0c503019024501a02e4003001c9030044040b10f8034445015681d1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 525006250 1250 525005000 525005029
    0x30209010b0702150f040905011701050109022d0f040e0f0f070e12070e0709030506011707051e0a030f02011106400c06090f030b06060a030e120c010b 66
    0x1422030340c0002910b002d081e0b001c0440c03034070307140f17424880001c5808661144a0007004120078290b02490000701c100d00f191016009080311030720500401030101007a61016000e407034105401c200300b064003211482030703010352046501500380000d000704400b07840c3c0b0041d50013284c8108000149071140701c2e2805a60408a0302ca500149070310343e6500d11440e00014610490f00d203517055884c0182c44084426840d20b0460303400300440d2140d081081000010007555004010443c80381800c03140011449854030340d54442c2034400d0a00c101c82100500b168040103751950040182d400c032680c0c0c0c0307840c02c48000381e5241607020403403036404c0f070182840100751107104014103c0b581c049030003245034007a40108414402c0c0c05205965443c81d90a1002c0050400540c2c019411aa0a10f01e00301004000150755000f03040000c40080b010400503030342540c1035030030100446003070761240c00c01c0000310020554500684101c0c481c0004031060580404010540e0704010002484261028010b2101060f281c99a = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 525007500 1250 525006250 525006259
    0x501110f19060e0106060f090e0f040210090b03070e0a080309150c03040e040c080705060a1418040f090c12020306012108041d161b080c0115030209010b0702 69
    0x2811055812004181019100380b10004596903266892402c480032a08070402140c101c0340703110f01d41a00000030600901014140b2001450940d00c1590280303006080280600389045c01d00706054007503032070381003e000d840c0034854492400000050001081c024a180203071078030303200400e4000020044481402020301040b141040280280d0311a6003c003103840d8172408203010100d0340103100108503004c1d030302840203c0c1c0c0c0d00f401d02d1206401d000b1141d0045105240800a900b4255048003020400302a189609500c62240800b8080c20710310b450b80e0710ba0b005282840107540300b800303544038110702802441246c02c403030780350b24004c81c034801c9108001c1d5245e40070600400448106884c08002c6c0f04800b12240e5910441e5a00c10500e900540c1045841e55045445403d0b65180703203da15a000c43e1003028281d038070310b814002611101a600712030700b040d1558500c2c0021301400504440c101c033000c2c8000c006d140c0051034010ba401307140340000c030720038041c800c000542004803406582010350001d0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 525008750 1250 525007500 525007513
    0x120b0103023f1501110f010c0507051204080d0302031e180d02070803120c04050d1406060d031205100e010801020a0908010e030313060902180124080601050901050408010c090501110f 80
    0x1005482c0b403031780c860394040d85200d0603c611400610a01030040060208e88501d40c84450a240003801c050030305503454000fa10a010801680c00c00207030000e41c500c80c5040046c0d407a00c1d43e40001c20f44001d003403112002503101006200301941d00d00003500503103090300103075680382c001903208030788444503840b460810b0760040c00009088000c4092140d000280c03c4500c038609655000401d50012041a00b07590450b5152800d9152010600c165940b001c011560050b160480b5034001e00500104961b001e140c035910400207400942c0ca41d4014013a12035807070158583d695070000395010b5842189810001444048001041141401010305c410f403110083c50850313991481d108100044c8000c103542081e10307403420740c000d80c9138071001b80e0700300441d20802021036061202d200b58804031003402640407042200c40c846865130015440350021824603096076120342100040b540750149412080c00340d483c100b0400e5507550003011440454100780c0314156020500f003203803901c1c0c12080733071940d13529040b22 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 525010000 1250 525008750 525008791
    0x10b09040e0c09070f110106051305040f02030f030a02070b03010b0d0b011e0801090b06090f122a0108010506040312081803120402041506120b0103023f 67
    0x5800c03041d0305000c120226801451036400041d600b80c42039a151011441125002c403c9591018211000c2d007044402444150300d03000101e00c4c2912480002840d03503640340045010401d81c080d41e0007049070010100e0710010f06c140499070b2654007950724480540f0491800148109140054030304071540c101c2e84906103011170382e44070302810103100c0150401c05101c01c14002d01800b450480b02e02c2c103071565982602e40c107240305001101c00201055100b4501405891600d6a4403620040582025541c0036442100199214941060940302080d43e002140c4442c02c03d45628804c0d0741490030982c1c8000441e41d8030003d010543c816400050113000741000700c800c3c0306003d1030106802940c0c4001d40304480c40380c2c080340707401e542003402ea00b4443c0e000801444158030300740c06010546400c0c0304401e10900e00c0c02101800d00c1a04401024247d92680c12681c5244e010340c0c1a14150407440c21071020090001001083c541440c2c0c00c1c0032000d801000000030804858400140700752442a4640d05442e01d4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 525011250 1250 525010000 525010009
    0x10509060f1f090312080108061819050c061606110a2715020c0a060518040504080d02031003060e06070c02131d0d030f0209010806120106080d0503090d08010b09 71
    0x20b40301e00742886102e0b040000024400314207200e113540941c1c0c07075103d95410700c1ca40d1800c11001034034400c1d07200840040c5042801c0c2c00304011050209602110b16104041c0c42d02d1030404005584141c0c0c00315001c03485d02d01454000e103004c803629108a804003c0e00c0360984001945014030024400000d21100209414003d120078800500b1070307001c264600180c2c2e5540488940081c902054010b03002a150310025040452604015100c0d40c24482e003441e8403509070f00c00f1112100c21130707442152034102180c10b02c180300341201d15040003001e05540c2d0385040d80107000000401d01c800c85905103800e14100700c0b4070340411002d02484c440d648942c44145c032030b0200725035100c41004039092940d84800e040240245400f950075103801d1030303018220112920401404580c80c0c2c692000b5603500410056000d0313a44103070780d160b001e4000c4414a054018103d4450b00401c2c0503008841c941c461080038160b415000b40c091841001c6200454440411202049540803070a10031400c521500384400041441c1 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 525012500 1250 525011250 525011299
    0x180f02060c030f030a0b091e0c0a14070b070807080f0402010c03020c0d050705130519020c07090c0203030105040f0b130509010222050a0806071d0d050114010509060f 73
    0x4000c81140e05100020b8070701c81c526407040e1741d05d0060659581ca04440340c10480126640040002d20390040009813001469a11034018141c0840150020b40858101d0086550744001e901c03084120391901102d20301103c141e1000e54070440404c40e144001512144103440940c0b140342c480f82099140e0b03c03554015a83c02c0007544088080d40038803071640d03c09450b86440014680d0092000b0a60035150070103024242c040354091401e09400e19041007442c840040310000c1810050310016958845541401d003010041e4102003841414501154070443c0e002010354140c03081260308006090080e0040c000701e5595480c03407a080307007810003000c46502803980100d50003402c0c0e42c00540340c4000142084089418a0302c118000c0304a00c3c001e100d10300b01079041e480a402c05100418040c10132540151176581c03c000480030341600d0096440042d25541103040302281d12200034800307145100910350081400b4000c0c40c3c016680300000548a00e40500300c901920f0b0702412150204245d2680e41c00d840c1d0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 525013750 1250 525012500 525012517
    0x618031e0d140a0603030e0103020f04050d050f060921091c060b0a06050705060f010503070e0403020a0c060305060f040507050f090406030f0b1012032015090703020301180f0206 78
    0x540d9a4440c80c20220389440c410710401c004030340004c0740d5096180252800c1500003100d4100f520601c070700c0c0d5520242134100c0d420f8031001c4a5074090074030245001032403c00480f00b4109680151800e20000b07102c0011082d01d48409030401d002c0d600311030010401c40740182301d0400e80c4111a0400c41d400a020180a102c1c0b4070700890300070803c5015100810341c94120790388000001034001400740188101880b580d500151003241100103549010006a40c6004074015070076240c801d00040b0f410103000300704440b8080e5000b00502401c1c0e07641c04024001305030803034807240613000e4800421070700d14051003040e1246071191601340c145080c4040d13010315a017051380620b41195131a000803010600c807045411904d0f118002c613500c1c03450000b9007261004e0460b0312101d010a401680240003e801c804042c44845926071001d0310041c444040038074080c242603004108142c803d09000800385c000c42e005003600e009400078094140c40f0180344960300c2d018a00504415000c0c8484c0c070061500e10010070900 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 525015000 1250 525013750 525013777
    0x30f020d2c1e0a09021201051e041d06130b13030e0a0924061205070509041506030c1403070507080d0c050d060905270712050618031e 59
    0x114058041014a0324001899407042c0c1074588000b42d51421402031006031050907400d5040400d100c0c00c0300180340d01802030a20503c200041000d42400d50540e500380300500030014004000c3d03071018580107000081c0c012240f4080c0300c0c00600c0058503e103281465640c8080d00075890742d5032021714442c168000700102d080102060340c00340e039669600700d500043d00540c8400210b400c4554144a81c01c58400301d045012240010100304403900903120007200100e00310045903a40d10a003003103801f0f1066400442e84585810710303480203500c6603007400007910034940382000040800780c3d0940b180983c0505010520900f003000404031442076014183c040d10411006050403da0989103054809200703c0748002503000c196605004114003682c030042007140400c202d00d003400040c0003c481100201044113003c20619042441c1c800c10181005202d01c07529602c400c0d14074a0070545442081e124480030304100b84580c030021801000f01c0b4154020100d5811200c01c980340f903401160001c0ca10352109 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 525016250 1250 525015000 525015077
    0x30515030303190c09081b04020f0c010902030f19020d0303110f0c07060504080c0d08130b0705061803030a090c090c1205010605040f030221030a0804030f020d 70
    0xa880070005180160381c0f0650101c01a6007010b41c86003283c42e00030600c01005108442001000008540c00038840d1441c04428103c480e4107000c500a841035842000c00b02200143c0c001d05a8419400744204610850584400c17000c070004440e03454102e0700e41a0341080e10314080400600d03010000d646580d00c0ba05010400302e02c2410300c134026421484007290200d030000389040e0040d80521005018200c2030810b10309160418035620781e600c03008500035008420044030070043c044d0020030741e030f003c10101c182e81c5c000544880d0924032a400180c01107909108800206030a4072044003002003000280c0300075401d5940c0d096480e8040c00c07401c02d054441003208000801c1e005501c1c0a101d6254500741c0303035209040501c400400032a58164407080400c40e06000a0003144104620941142d030101c40743c80c040d800f00007207444042010301041c00d01c0d120002d000c041890b00f210146105d139020351200c0840e50b00d4588180e80700c030750308503d810009070007030403450315811000c01c8540341449660f4135040 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 525017500 1250 525016250 525016291
    0xc081e040f06092a030c05060a0c080301090f060902030c07021011060f040b07030501150c050c09101e080d110f161a0c0c01050319090b01090f1a010305 67
    0x445258980588800340124111303031425030030040c0c0c0240d00c003412801049451864503030106440389401424450040024440761251150b02c9000115400c48003180c4e495a5501c0513100a20160070310308241820018002655800c51094a00c06d91148020500d03201d520303801c22044076460445001801604010810140e4040003503e01c42c00242d012003c060800d81480101c00c1c100524980c2018205401032050481c0341510341034013061810079003005202031610500340716202502980150794041007100440100c40d00c1001c8820098815492251800304010010401d0140285940c40705007180c10b01442519400008c00c07405055440f82ca809422242c1040303119960120705540c540000c3c04a034a80c69001c1c0420242d078178015250180044440303845c0c17428083e48070705002d0b002c000180d480044469021404206560401c041e41d81f9141c10845244280908040d20f0f1800c2c0c2c0c40d549909941c41408078203000745200e00c6503c14100011805003400070545c41c450020781c1880318 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 525018750 1250 525017500 525017513
    0x1050f01091502030304151a01050f0705031c14041a06060c1b03010609200304050f0f150a02070f060c0306120c05100819050907050a0312030c081e040f 67
    0x41412800c0d80036555904050500c003910341c041d0082c44100e035190615202346a00e003603090451441007800c4c0941c440c0c1d07200e4182c81e418064581c020b0003a010001e900c1e032140d851000800c140ea07049a000b00103400340e176100703058070392411035004100403010041041c0e511820724005502040c01840035290240b1714070858201107071070003c0125802c02081000d10740c6400e01441c00640012030040011b4840e502844c43c03084c00d42210410501ca0000108050100910403070200c1002d10049845010036a80025940c0c4104c0c0b4200700c481c91150003280407212580200c480c5c03070740c004c0c441c0c0301c40015a441c0c40b4028200a0b8001003410b958860000e4804002510050528001c06444c1d850743c0c60031003406158903a401c499020811450200030803408100504201d01c4036200002940d41d80d0441254546040343c1c20007075010441500000c200010a92044981e07180c544c0d0074002c1120b08001a50002e50548420003400c5c5c030360f50a45050700c1d2480c8030780c0d406405644881c69400c01031b200d81 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 525020000 1250 525018750 525018779
    0x507050a09020a090801020a0504060c05011d070f0b0a080105010e04141003020f090103020105031906120c0602010f060f060f0207090515011e0c140a0209070806150c0601050f0109 79
    0xe11982e004a822800f4603088100000285603480007075250087c42c0b030008169210f107005401c1030081c940e02500511009502c070071480e8800340024076007002d89400701c03552080d90303214500700010b0341403010810026203000d0303951025494444d820264288001910302d1402c0c0c0c488150066654882c150100041d040c89500500803c4210703542181140140203d004240c000c13a401891028010001030364000110390348001d207846a01d9084180441500113071030154031001c0381101036120700c814000b400308020200c5400f50020000d4650f168810b1003603030f08c184144240510815010400180202d41c100042d81051041e603103003d0300c0350f00510440d0400e807050084914502142e20322560444403a804010381203680300c0b800382040100528004840034010b18810754610141155002000b103d00c3c5158000d0005480c0e1500e242c00801462044507110f1241d4101856141816520000c6440c6d02580102800181e0308240a00521901c2e80c0031160402c4500380c000695803a00c204030 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 525021250 1250 525020000 525020009
    0x3063905070609170a0e03030715050c0d05011805090604050a14030f04080703050f070b0301030f0206070b04050a0b1807090b060405190602011103010b070b07050c16031703090601120507050a 84
    0x1801c1e1500d980a400400c0344114851040c0203234001c00250010a001c0c011105214008800102d06035440a0000005000382c1c9a405102400c2100100d2000000d000711405140311200030025580ca40520654808050724050200d810100b5550007040c0201c040700001022402100c0c600303501040817880650080d0705c0103d094005c0c070030500030400140020608191900010300c401800c01160300740c01e2106200080c0380c410511802d00c2151509001c1d10a629003004d8115082d00d0b06013000707903c4145824003160ba100480d00083c404410404a141003801c04034000d2a0040c2018229001010541e485c42c0e80441b041c07000141554810700381500e03080041d003010b00f00c4c603d0503001030700b0f4540b15440c51014080a00041c41070703440d01c5065078526500724041c2041529880b000b07440c070388a008100c2c484c6004844103400800080782580c01203a128588021000c69036011449041c0003e82d1078503003903000017004000d080d1020f81c5032001140180180c456003596180011407940741a4070 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 525022500 1250 525021250 525021293
    0xd0302061006090e0a0b0301060902070b04050d020f0316020d0203250504050c0901080a0906051807090b0a030b041703011401020c1002071a07060603063905070609 72
    0x3000500400e00300302100408881c20581001410304d00c0111409900408891303801c2d55683d0300c49084da400f50031a00090034010b070115031750b207164106410b8035101154252101d00c60178082c9004588002003891900c011301001d1800d0450300c51982c0b000100c03459050f039018500444650141c0d90a000d103000c0c0408000350481c00c4000807400c21410150b03640281d11403072a040802ca094441c402c1218510340003441c2c0319506135554000c4000500c0a0b1101608180c54001080407138820603103628046445c5508440391705640304206004d9541c14184a40c02403051201000011154405103070001d00c1500301703014004103c0300700020364109038081c209020703908150100031b5030103100241d402c0105a03214801614035000c0a50307200e07464814021a800021412501d801c0a10160380c0207642c000e1050010b16a02d0600340302401a031226160b580c0400d80201c0000f02110b80e0206980703005030140d19203e640c50320141c500740c201080070396989444880d0003001801c104400301e0116813604 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 525023750 1250 525022500 525022513
    0x609180a051522020f2e0e01031802130207020307091a090106050720040902030304030b01050f2e1b1202120a35010f1a19080606090d0302 61
    0xf00d00603400d8030031400490b00707140b1030001c040075032113100303280d003003841d05440203462011803482e100e000c003c40717113071081e000c0901c9040e0101659100c010440456070990701400702880c0244a81a03841194a0080d8001c8103034120b100b80320281d8020b05859800141541e00c029619041380e4103651a5004180356140000c5000c2180e1508031002c0d03002d8034852070043c2c01c1c000940e8a03004010161407043c641070b40030352141da200e99a00d410851407a036018083d291910750300d00e01074200c11800e00440b4454442c17071800f400385c0e003080c0861007515a80000040c0140341d40090207224282e045021804106000181603841803d0001c0c1201c00d0303126584842110254200c02410200d005c10036414184003000903070b500380d500114001c00c610440c2034060700003000314103c84040c1d202004400102e0401400000d49070026081c2c1c0c0700f180c0c00d0317540c00326840903184420701541c8a00c0c03e03816002c403180258110846e1040d603903c0d274049006010207140a44040010b00782d110240070840043e031110 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 525025000 1250 525023750 525023761
    0x3140c0d06060f0e090a0b0a0b130905070516020102030f030c090406080d0221040f0e0a0b1c1209030b16030b0d0c0612140c0d0b0102060609180a0515 66
    0x384039641c02000c15203000d25014120b4400107180b4580f061440d8800d005075004213400118592000102210041480884550340c8290100980280348003800301d8500303400c00a40401355006551040c402e5a0340d01d0f140410b0711080c02071000e40700005a0440c4820300043e2905400040114061180000c1c5991150503040800c401c0c0c99840d00150303800d03040807582c2c030240750f0002180909444000810024041940300e01256409107910010080c544410006a0303040c1c06c0e140300303000380c0c0303140c8062060442c00c00a002c03c4050341c0140b61060446200007501040c904880c24203049510300e040500c182c0d8030344450382c3d1042d003a80e1b0200c200360981841220307680c05210715510900251213a450b2600c0c95260921440440e1080c2014055001a0124000b1055201c1c90300d540c2c10244c0d807005414040440e02e80d503004500c88114040c54040e4008a5600000340359104030030080c8890180d83d50000f03012100311511003035110a01c110540200020003d029012070000e5880301400d0300d2070003 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 525026250 1250 525025000 525025027
    0x9150804020132071401290f090a0e070b0a09140409050d030b030d090f060c020312040f030b0708040c29121b12040b070c140a020405070212160303140c 67
    0x2001320003546e0314203800c81c0000c0704144500240f1010383c545d00c0c510760296001282030302650510031940150510208a0707500f000364030072040700c400c440488001030f0f120700400709140f1030b000000c1d021a2002c881000b00040e04402d0400300c85000d800070849049903524245003c910300c0e4081d007c07c0e121149407107141010000070503c0311a074a403440701185400c90000802a6074040c80c0100900f140325001591010003800700050700d001d4260741c1c1c403651032030185500c0340c850000300c0d02d00d076081d030201d003645104007012405690400c0c000a021480d00b1080154046540c812003c0a140c082032142c00301404c1c0c0246c9a13000c0320001801c424070f4250b142e0303070780c605140070081c43d0400144000600c044058182a0b0302c81c1c1c4c8510401c0300390721080000d40e824032164400400000140c010040004004180384084900c00d8800340b2183d01c0f400d500383d8894060344280806900d052103400010b08010066159641c041d08000803d030b251101311081210080307a0881d8954070008122108442 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 525027500 1250 525026250 525026273
    0x9030908031b06151804030e0d0b010e061008060904030210140a0f060f0b031504110c121e07080c030a02070f051005090402030a06180902010915080402013207 70
    0x401d0031440d0501c91400500c0c0009200c255459011721080002d08140c022183c4031007400004000c0031030300489141c1020744d0036003406403020003a4014041802414028814110320312641c8864201c5d644d000f05000d005100188260f0451040d1031a07003901100501c100404603600124560342440d01040766026181080d070029401440d0610801105041e4044101a00e1074551007654035280c0c524501401c8144c41842c0d80c3c00381c50410b01c80f0400034010010284840c9190a8441a0100281070b08039406016080d44081c2c4100c2e01000c4120005001494000e100b20343d01414021602613161075504184014070169201c1d150501024000d2000100280350843d020190496001c60042c2140a59440c6a008940200100e40550b21540004019154000c141c4442c04d00140c0d40102400f041201139001c00c04521000c51010711682d0780c0d8180c1c0806407170700402030301d9541c0116800240841c2c200c0324880b00394506071003101640b442413040c110300045140c80354071328204080070f0300 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 525028750 1250 525027500 525027511
    0x10609050c07061b020703081602061204021c05030901050d020d0219080901020c030a120905060a06061715010c082b1b020c010f14030f090c0603040b040609030908031b06 75
    0x1004691040140d031780068003200742e99020410680307683c94004095000840210002d62081000c6280a109689848846d20540c000c81d20310443e030031980c030814188042140040c0c807035001000358482c0755004030000d142101d840b02006280a4041040c1c03022a0440b80c103036091814500075165096500c20320584c2c1001c0c0a8000314030384070b1202e40466491080b50034840a100001c0070103040160541d2180c007944d6001400da5869291600c01c7d20024109400361101045509460301c112580c40c040d043c1c401c1a035107100c00101c4540800540b58400c0c40380044030003010420019100c1c2c0d815440352003440024034440e048690340100600241e5900d03e45603507052404511103094107900252800005000382402c10030b954208004961003c88000403034107608001007445240207a0100c03280c800d176080c005541c0707040780e52030801c01d81e07200a6a000d071078004c5c250040b9010442641c4681c1d2064880c0c03c2080b50140d40d000140d0654004601c02402038542a1503032120f4035061140d40d5000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 525030000 1250 525028750 525028781
    0x9060b041b1b0201050903100b1908030315040207020607030203090f010c050c010f020f0304060503012c07050c070f08030c0601050405011203080405010b06031006120902010c02060903010609050c0706 88
    0x2007030007002c1c1088000c0c4403044846100441055901410450b28070420103000c0c1e85845150404210240c50500c40080c0a104402040c203202d19807003403031000742ca00c0200914595100ea00d560f01c6d08007100c21205600c154200503d400580c0c504004141040c4a60040c5840e104150100018111115449030500c011084110006000071651080c16402400c2c07211a0060a460891606a602842c4029844001001700700590404081d40c122945d0105040f2824030704140c4080004007241c1d040c50340c42c0320501044145014002403c0140b0720704040358541c540d540d00c221800b0540d540300441940000412806c140b1040c000e040c09071005440030b200651400000c0010f81c01c100501904100660000c141045030a400c20090080300801464036810400590031001a9510541010a940505407008104140a511400c0f60141c64050340f15810f40c0034802542d00c4041d08a515569400c1c000c949080284101e41c000d07020500c42a0304d658851401c60704460488000040741d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 525031250 1250 525030000 525030041
    0x9120e06030121050a050601120215121314070e01030303140603061b090d0b01150e0102100906020d0c0e150405031c140d02030417090a1e050409060b04 67
    0x685400740c4003008000c003408041c2801c00f19400c219040101c20b00c402031082c003075030000041440d20424a00c180500031540c0c106456640b108044d0355104040504045051800c00140c1e000c1c0040f1080c020540070303074000d15400507000055410040c80390450604242c1207001401071550620801d88100d11504103003010b8240800000d85e642801070907103038a20181528120f00d0041142a10580103020b40600901d40300362504240c5c1d65005d00407103211012200346a1069440340580c04808c21040c5c0240c00030b00a071390001005400c2c04c100503690140c081001d500c0c020041d1044180f443d8007552076041c47c291074000c00150031241c0343e00c0719442405100611035075601040103507a5010040c2105050a10900c09540011350902e50490321040801c0c0702d880d00c841c030f40043d4070039441402c0250003c845000380c4001d5024100555401108082c014080c4004441c141088200703101400c50a0a5848001805031140e40104594084c1c072000e1000070350402e80105c102011008036696007 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 525032500 1250 525031250 525031259
    0xf0e0328110303040605060118060804171b06090d2610030218150a0e071206091a0f0a06080c161416050603060d0b0c0d09120e060301 59
    0x1080510403415110203000c003003440d41406044266020205441070380d03100e2800381008030080904450305c43c0880c2d2a400250340c10080070042405031020f80d21802c0712510b40f611a410014140034400c035074003600b04019150b4060706405407440280e03003401820280f811403882e600b01410101504c00780300349650b800ca0100c0c0351410040c4c404041555143c010354442c41c03820403180c886e0f40702940100700b0780711076202c0108281c03407180300e5000800e80c01800c814807800e01800010b0761080041310160381d8042850740d4494001100c2d1110403110100f00f45445454540860740310726401400300103482e04030015401d040742c250030501e01c12211030041c1803034400040c041340d1006104440c0600c000500000085e01c11066101c215000501c81807100c1071644001d68030884110580d03004030104100041d02e00d44801240c0c400e050142000810102680c0c940c00001030290001000e000e01b0b1108441020b501e101c0e003201180200c055005031002014050480e003078a86809002d850100300500 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 525033750 1250 525032500 525032527
    0x12011e0503010c090b07050309060f04091b1713050106080c01031506140d090b0705041e18020a090b03090109031106040314071b0b04050a05040203130308060a03060501090f0e03 78
    0x1e048801c5c1d00e03005503640d92140b801030709500c1070140803a4411404940480c414004402170710645e582c103070041050b018401b602d020420390103050940060f0800e0b41c0f0380d0001c003201c0710198001200740350500c0d88a00c15610b031801c0d600300b80c2110030300f540300784e05c0ca100543c0e040c01031141e038243c5000b02548080c1030600042076501c0e80641d00c1c80d0b050300022001d082c007409900101d905c9403c030420001c0b03400d1144005245074050320038000c940060b80d240450001488043d1300844075108802c0e4801a00c140000010b50400e501900030f0003208800014440b240e41c004611a1200030b0000485500b02c0c50090116000d00a4922072640300ca0104030019420560340c030f040419002013503807100c98501e00341c003400481a00d0006103101450000444410590140c800d40d603003103961102c3e0769165400e000407400110345450b40784815444c1000841d00448800750080c0c000b43c02072042607102d442d20800e461082c1d00034640d440d5074400d80c58201110b441070600541030000034601d0015901c0201 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 525035000 1250 525033750 525033767
    0xf2018010e09070f0909020f0a1215061808010204030f020109081f020f16060b010206010816050906010c0203190b070504051818010e01140f0f160512011e0503010c 72
    0x3c03091008455050707202a0007490024024007010f2400d5548454a05030141d2030f402c0001c0b4500411682078003028000354600a802e010710300c40200340d8055140440444420095070800b55500707501d0500442c607400700303000600295015005582030021980f0005005540982c045400d50708000c0090b07042c20900262810141400b00340903803148000c80c070450344d0340305420000d806109103d1801e0100250783d040160101826001e40b0110ba98802c0070686842d885140d15000201c0000140003601d440f041e000c0c0c1100e4189048030621142d6030100c2d18000d51020004490301d01e40e001e80f01000726241c2819031102c105c0c58928200b41c50b142c04503031128a61286840d055a110340045c4010385004207900c64114040000c3c400a207819403494001c1140102441c0e80000700000200c8140800c10b0403401400c0c060241c1ea4165640d07075241d8200c200c08615001081400c01110711420441c103034107400f0b084220b41c3c10170031581503000e00c030428860381e1255000b80d0401402d0000d04d03400c060b11 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 525036250 1250 525035000 525035011
    0x306020c071d0703050f1006181a270d080304110303030a060603180314070516170f0a110f0a0803043c05040f2018010e09 54
    0x15031221500560306082050541006000d030314449a6903800544034620340d40102401d4400300003540754801c001d018020100c1b140910f4008031502007108920814034410300154280b0f03418505074a4040041c410f40d2a078140f66404c6101140b039441000074071040d10203003811600d4240d46981d110340450300d400184c003000350800c8804400a0140110002050b00484000341500e969151041c00e5000811680c0101d00010307151002c440107040130a801084240d401d904d50700c008044d114041c1910390322169040f1882e026105c0d440015004042d1084050151900102c81ca24080008545000e100d1082a1500d600080718080030030000912010010000d8488030002d06480c8003051030308a840d40006120720002500107042010018011000c3e4502c04400c0151210740d030144020490000c0031921000018008200510f2f00c6e034024419410740c400082814407419000304000c042840c000e08001e880000e100b23050810102030b44000010908200c1d401c040280d01140f60804000c29 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 525037500 1250 525036250 525036263
    0x6020601050901030b0c070210120b04090206121b0a020309091f090b0d05160305060609070210021602060d050912040f05090604020c061003020a09050c1207030e030a030b18010f03 79
    0x4106c104c040c800483d2401030700034143e10b180705480c140040240f1044003000300d00910709404100c04d8541130049400740d0b90010112030402c0c400f031700101d822020150a80c5490130500500c400c038444404041d240d1119140c01447c0c803941024140006810020511701036101001010842c00c0500354042c42074174000880010b04580799408070310441034894010301648103082e062042c14083d801c00700d040da031182c010740d13015444076411b001e00c42906544d48400760700043c900d030b00881c0311a4080d0107141c000c003240c0329a4440c19004681c10b0350200e840b09a4480e102d0f001c0000c040c0040106000c0142d0480c2c4651800c0c1c43c254684004026602502d841894040e02051895565406071082c2c03040c8181075031040c5c280490503181240c0180310490103003540790000105128244540c81c0704614a0310b0f07035890441c56806002c20740b0401040c56040c1580e4100c250f05141c801c0019100340d902c142c40010f08008500208035201801c0b00d800c0040c1c20980c00140002c0c1a18003c680803683d1021 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 525038750 1250 525037500 525037523
    0x30a030c0e04150807080a15090c03021011060136060b040b0a080702010b09270f16051906080a1103040f0b0708090714041d030705070602060105090103 67
    0x15001c0354a0000309100550083c200459202c0c218040310310501100c0e0910100d500242c2d590074543d0301d660441038081c01c10750381003080c400e40300e17404d800c182c460900c04c8480000b2036403203900103014100c06650f8080040d96600900d1074243c020003045015144c079071084901d030000008540d60f0000613201003442d014401d40c40c0d10303407120707a508010017500c0303012006611282c07500040d0700c05801c2640e031072002561010109050314010300c180c183e0b2003070203042070425070743e182681d8400d40d0210300b20035200b019190200000c8602400b001c1846002d02e006000d144618900006510b5040e4109034812000001c14440c40d0061238001d00895489003070101c0700b684c846801500a2101030f84013100314100000300f000300400d0380200400d061141d032655106851b0a00c00316480c15044414035080c3d808190144125200c000a100e510900244045109400c0040c56a0180c1d6003840581c4964070210710f00c801c00c1710a00185020340f030540700a01d469031401000410a07141031101801955064 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 525040000 1250 525038750 525038771
    0x6090c03060601030f1d03091318110f10020f011103130b180708281511070c0e1b0711040203041401021305090903040b18061e04030204050f0603030a03 67
    0x190490301b144c52043c2030b0410b5282180210070380b660301480344c00e4440c41200001d020300c00c0c0c0c04e20559680100000e51030f00a08000e135141341081c290940840d038481c1655456829070303034503c088079818800540c0601440084e102d18182511542a0b40c991410014400c2259100032640c0d4492519004002d114082c0c84200340400c00c0a000c644401486c0181c0c400440c030010009130800303400e001c40340b50780410102c1c0b42141200c4d49450100030a10041c41401d40007442c10343c0c0115038018070a2040e140f13010300942d5019100000d82d0720807403400905804120a924040c1c0489284c0c0c0c0001600901c0c040083d5a0007081c208045071052042e64044086070074010002e110400d943d9081c402150381d08a001e4190321074403a98031810303100d0128940003800b078103804402e84040340c584482c1070b4249590040346624140c07010a2441c1c00c200700b400904030ba03e4640d05001c0a840c40b444202d651241180140002e442c1c0c01000c219960010b03800340006038400000301d03032000c0900c0c0f0300004d14a090307 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 525041250 1250 525040000 525040031
    0x9080c060d060b03010b030919052a041404050f0c010503042a080606040b06160b04020607120512060306061e03071806210803010e100806010b030906090c0306060103 73
    0x180d002403c075104080300101e250001c50004501a0820300c007290321071001c9403882c418140217400c0041c00c2da08501d880140700c60402c20b0301c4c0c2e03080800c80700104070007003418042411940600c6103072a966400b40c042c40180f15080c401c8000d08031031b4801501c0c84c05000c00c0080c4c101d00c0302400091402e1034405000d0070f0107650251001d0040940920842240d658203041503071810159002403195142900c1c030401e9150001c216a65414409c0102d100b492443d1126000c400c40104241c0e0080b0081028030001008261040b41100241c0c4132981c07113400800101e11080341c0200140d009510040620109645058804003a9600c0c03522800c1d03500d1314a0080307801e02010b5071000000e0f42e00d02d64040840c10701a008402929000181c5c95008030051038038900c210b461250103021600c4c10801032005d252400e00b95070b404810064039000180c5d850643d00e00d07049090f03000812800002c000d1001d0084180906074015404100030300e1600038007400242c40d1407014000e2418035a0740c510046201e4038 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 525042500 1250 525041250 525041261
    0xc1204120302120f01060305090724050408011407230910030209030d030b010e030601140105160503030702070f090e0d110721050124052103030403030603060c09080c060d 75
    0xf104804160b68103007550796188040082c0101c0000c24204400035170740f602e001480d00115140074600c8030910f001803000204410002440508222080202150040c400d0048600300721442c4802c03169841c0c4004000c05035207242c66070050044040c0045040041d400c41503807650501100d0b03c1502c0410320340c00790028811002c400342c250041e01c100816240d0950310829007280c013a240c01c01e19101c000205611031000b40610641c2a0b40902d0103183d95100384080c1c56602d503000c4002d0740d881421f4403018a19001204c00d140107034800c210501031480c6034803c1000070070030f9040c14455003030381284050301c41c400f51701030108110020818031051082040510300034000d02103100551000601801d50008550b0300a139410342c28a605125200c0a01e06450000e242c0c01da07000c80c0a070704010030004000e0540003c100c0c90070b00001c1b03801c650b24085c801140258425100010b1403461442c0c41001e641c8d8403581c030300921840450402212102080c1c0d00c14050007100c500741d4400c20fa00e4103074020035 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 525043750 1250 525042500 525042517
    0x30f0403120c06140402030601091509050c16050303091009020f09190e0303160c0302070b0706060306020a030c0e06090a03060902131409010f1104170708190201080c1204120302 78
    0x141052030606095003100c907860b0045d8000d4041e03403083d03038860825034203944100d00d0300c07100401040701c2049044100d40c0015001401000d482d480d01c201d550328000c509507600d409035480d800000a10507212820041c4203a006120381051200903004c1d00007848031010842102d0041408100003111084011070110014400640030007003d504a10303165a03075002120020b90040c050100f03182c420703004424401c10168194010890141401c2600140c0d0300012811141151236030320101c00110f590001e45200da44e01d540c0001d00c50840c110040c07000b058903080601609040066000c26101c0d85010419250040004107500450b440480e10700c0030b505e807000f203042c1c3c40c02681001210203030520f5401418800003d101031048040840308079031030800704440c94001003004210783c028001101c12042c0c40902075940b43e603030b90700713200b4100340101e40c81a81038007001144008560b00710303c00642007641c0f100083c0c02c00f403411080d1a0001d1019201510400340e840c02e006289210390101c41c0140c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 525045000 1250 525043750 525043763
    0x617070e2b020103051302060f18090109091b0e070c080d0e03040f0902090d060b12011b170118320a0c081504051e090706020d02030f0403120c 63
    0x200c00507507035154807002010003240001d0030007011031a0f03d100090308200a0341c004000130324050408039854a1a80154003c5160006556005141d0ba03180003c0714002c0c441604041100d14081c604200407003038818010590300300540040c4580800005129802043e5050006206415081c500828090102221403003400d00320544100080807020b80300b00c400300d01e00581d6041d11100804140d0080c0c080003600011201010790208205802c03080c02180d019003844501e00b6483c2009094403044e110034250180c1268044035965800180013203510741808280c6a2541040c0400c04080c1294189074001600e03503c0800c02580007148400d81c1c00e4144803881890351342031041c003030140d4085400540b41031802034510b01d414000d03240030b0302c5107129420000c01140c0030010840208400b0301a00d6840c8c04031207221200c40d660035a650300910280d402801500c2c50028000d1034a500c8900002c11908144282100320145a003500c0640703a0007101105030b008042c20445128000000243c401c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 525046250 1250 525045000 525045049
    0x11100c050616020f0f0c040c110a060c08090c15070c0f0e04030210050103020f0108100504020d0b030f07050604090e030d05190f062114030307020f06010617070e 71
    0x34803502da018008045581c0a840c41c201808a00703e890707040c80c070107820b0390b9003140944524a1030680d03c0050034144e40e050680c02d480441c00450b2078000070000888500b5641c11100309080d40102c82941c0c040804802070002c9850700c03000c02c4a001000b030b09184d103d40301040303507420002802402c0b4003a00c01c514800820f1503858100714071800050b01c0550250154404504c17854100c4d000c1c0d58140c81e0081e00c01c0c1c00c103e82d2200112449071006000d818041e40ca041c0100e07482d501c5000609015500c22000304007550000201424601903490b108040e41c0515000c00440c0c6071301c1c094a084998450001620341782d0440d00a040d481207048003803d41d480c0c4403c02041c072042808881d030480074250700b080382c894244001e0003281c0b0b8074000c0404c0e08a0551450428481101510040c14032903004c45802c0303d9070303c984503e940c00540d0002c0158200c00e0403500e000e5000c004140c0144000d1402d00395080e50400c6501104002402c0507040018007a80703c081a180c004003100b04c001c000048851 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 525047500 1250 525046250 525046261
    0x100c230306211018030f180b090a03120e09060406051807021006180c03060b03012105060109061a04030206030601052206031508010506030c09060d0b100f06050711100c0506 76
    0x10b0b400800e00d0101e0124201e0a41b080805125030150001d03012081112040542081d42c181041d41150b40349580c8040130002c0800055804805c1410148a40d02c3d00d0002c0707000401000074045004001c5c50169180c50000c01c40d076a20710009129042c0100402e001235112007004a0400d0748c0655011180707420710b0000140407065200818000841d4601000006081d07001101561468840e03422a03000510041c010703c21143d46401c80300c84100207009204c403c6945041c03d20400b60b03c401485070303071f400301040048055600c80e075810034405052498582951300181c401e00019003a94104680480d2440c3c6504001c000030350340107a2604007842c03c1d5039640000307001d802c9221045100d00380c01080000d000c001402041e02450009000d0184581d0030f006000320090014050f542c0662200101408201c1c0c40c004640940d00040035540340c0c900f8031405880003607082c0d00100400a082000f1070102d4101020702e100d0103011541c0e0f5003600000502200c0440b140b40015005000300c400b03010 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 525048750 1250 525047500 525047531
    0xc030c0d2a0e060906060a0917160902030105100f0f03021b030d05180c13050a1409030d231306020f0d020408010608060f01140102100c2303062110 65
    0x303203d100b080314400b00903a2030b9810300c6480c0c0503e14400022031003200b418070281d2100390718845c42e40403000490360013983c80c0700342072000d29499101b851000e900000501072400c0c80301c007401c0c000781c032810490090340111000916040000d40094201603010441350702c1d00d1880ea0081140ca4a0340c4103ca40b100207000f9480c006000c159000c5030b4241c24180901c0080700081a06e0080480040000300c500d55051403280203003034000c00b03c003c2550b0741e406604803400d4a50440c4d000317408480c01181c4401d20f80002e2803c403007034201c000115004489145007c1c0e9401d114030360348601e1002c0300b030b0041400d503d04030000e4000c0052031300c0d50310b001160754907002110381d024104440481009000c0140e81d150050303140d00e42079032528803000308030340140484d00030701c0525841483c041c4100c40d050280306ea400d004603030032000303800e000030810074007071010001c0418507000d11000c100d405444d60501d0800a102c0c20300d103440c0d04040001c8045481201d035000e000102c04145980310611103106104047c4 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 525050000 1250 525048750 525048779
    0x1116060b0414060637051201410307091e050103020d03230d0c0f020f07120c0302120309030d050708070303110d1506020c030c0d2a 58
    0x80e40158030b0201d030084441c1c50851514061a0040c108919114014041c180c1c2c100c65400400c042c11101c82d60840800b005d0350301ca00340900960743d059200d90ba403030b0f11145808010790041c0000004409501c03013036012184d03c036680c80120709851000c11a02c2e40240324040a5040e0594940900c2000007204561500407108031300380d403040510007924040d0b01c88202c8000307010294004d81003030100c1d00013034018284504410329907207400b410b00007030107400c00141d440340140154a0380c0b11142d4418103a00701c481b404c41c25186002070540d40d2100c111607580c80419106010418101a07a503600f8011400348040285801500c4180e0201c184440315a407603104220503402881400e00303002d440c1d4841c006039054158030003001490702034152008c502070708041c0d40d443c030080b8080017000c2101c001c03032061547d41e42e07200d00c1d090f4482c0d15060f000390501104543c414080e4115031680c0d441f0340c1d601c0a220340300f25404802200c3c03407420402201d40245a5140b142d400d2445004c02203066a00c41001d0b = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 525051250 1250 525050000 525050021
    0xd140f06010914010f06080910020703120f0b01020a0303020f0d0509031b0607050f070309090c020105090613030207031e05161a0f07030809101a0a05030708030d111606 74
    0x1d001035900034481c1080103d0034842e103400303556801e4007403025510842600d500320b400f0404842e003601c11000080300706d80c40900d0440105d03a020081041d182003900500ea80c0002503401049101c18a10003c0c0d01d40e5006a001020180e00064544280340d820f001e031481d1003d400340401231464864203040e034030762210301d0303039603e124035400744100d11500040c03001d228254503541c00d403d041344400d140442d904148011002d01015100120300c4031018403c2070400001c990001c1901e042034501c4030f0801e00007a15282012210b0180c0f84c000c29000141082181d0f442507600704038481b054013a0030041c02d01701c0c0060150090400404411011031800c0c815100545040130382c009503407200305954030404920f58503086090001d480030a010b070071101d500441c00742c2900c1c5011078840030301003100c40c2600804c0000c81003540108250400182d04c5c405002d00381d0007405103d080c480400d0b40c9018146284c0002500c47d0300e01c2400c5801001070f03909a0301d46c42100e08001d0707024038090018010b003e80 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 525052500 1250 525051250 525051269
    0x212100c0203280c060e0a080729091e0c091602060f010302010c02040207061e321314031c050615030a020906070c03080301150503010806060d140f0601 67
    0x41c00c5200c0d100350000103c254a050310380c692208042e64401d000f038295041410118015940090040340340745d00202034040c4104d0000706c4036030900d51541540e1407051445030007800308404102c058100082d290202852074a102c810400b14680000d141000d0000010f4011002c0b505100d4000c01c0e8000d0545050300c550203480443d84d0b00800d250100809100107400204140048005030410751b004045060003400041440512403010110496004480713032085030b520310321520100c0408560504046003039a5801482820900c05500c90300041d01200f01c1440d5152400200120801005180741c0c0e040d0a0ba0b8442c050b2200c400e0107240512100ca104500707284c0040e074a441d040c24444c86040d03055940354210b860700c0010000940101c00b031603800c02010002103011500304481030b0b0040d80700c0c90102d07a132581070454400b441c032103640705241401400d000503c442a0042515a4010030580b288482240c2d1410709048074585904060018001c1d4199121903080209030039059501c2d500 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 525053750 1250 525052500 525052537
    0xf012019050d0206090601050d080903010608100c05040e0a0c051204051b060307083702030106030605310b181501090602030316020102190c060b04020c03070212100c0203 75
    0x45081e40c0321003017164010501e81281c0014021803800c0c541068013140107040d11818100d010002c00e0071100c640d0044500c0b980110068041d80f2481e01a0000001c55071400300e0615207004071000c0710250103810754120716228014806220310a90036a401c929441944034064146420072640701c6d10b90b641c400a02006603990812507080110460b4012010313540e4400443e620610545000c40c0108010740d4030b08080403102c4004500f8900041c040482c4c05401a56940340c1400070b82140c0481d8021030142c0300740c1141b03051424144007180c0002d4001e01000345034504108602004040c6100c0c0250700003103a040c20340b03669626400c0107106020352241180311a00e510019a200b50062107007800680c4204002440c00c0c0c40c40041e459130711030034000542844034004c0e5007590100700c00f600b1400941e91840e01c4090150500800700b03c0c442c00c3d9011440e0140f6a9001600d070300c2031800190003001c0c3c0d0038000451900821030520284100d2101300168004200005e44940c003d10041042c90f103102c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 525055000 1250 525053750 525053773
    0x3180b070506010518040b07111e01150f0315060f0e1504020f04050f0a0806181603020f190513090605100e060111010204180e0d020c0f01201905 64
    0x403d101c01545c2c3d045500c12000d0f0b072190307070311180290020224010420805c00000f003000c420400c1c0080081c7e0702000c041001c0070301029500f1210340302c003114248002d041e000c12640303036000d81142c140d82c1c00541d10744c3c801400c515101d010340100c0d4821943e585114030006050129145894000d04000c6029168022a03008120507030188880f150402082000108028079210745104111400505414a51641c4101e080e04100c0116000880030810409220041c00300340b1411b49400340300d405900c50300e411a00410008400e4003102405244298485e0825659215500d4020100205004220036810400d40050030341c0740790444209040c400480c01003020711701082c040c1c461940c40318602e5500c12004444004940700c0011043d5401c12005c60141148203400780040f03004440411003020301807203186000700c41c2c2c40c003008641000403294176960705c8041100310040b003440e160a039000c0c04040500440a0b5072078800c1c0c944101c01c4260080c8030150300c04c6054500500540302c6c2d00010 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 525056250 1250 525055000 525055009
    0x30905120a021509040b060307020114011a0a0807032a031406030307061805160302011209051c02070e15091810020714010e0c0a0f0e0402060703180b0705060105 71
    0x40c034025800705046040e040c43c00b460308094800c6400091000c039102001c1c4000c100251300c19034420b0010b035100c190b040130035010700b107945006001220650008104d466440d22590041500c0c5008211180002c10b00c407600c80c0e00206043c0e1600c100600311031348250300c41640031140d45e0005000c2400e064043c0078600c19580082d2103006c028014610342081d0360741e04001030229440a0b15041c4403181440d02180080207891480e41e010509034500504600024207841480006100e90500740345e80d5100055010445c03d1558407801e80c24508685401c0c002d81c00c2981a0308040c480b80c1406080101143c440f1180c80340c00b4400303442ca01c940340c46000200d02c59920032102c0002a07404400120020300b840e078028960746014840200102c0c82c02d0b28401d00b96542081e03c850359034022702c0c401c038061804821242c010842c200c4101c15480ca05641e080d034000c8004d10291107114045a4141814011044a200300d00000c0f4510303d011307100c00348000390b03070003080e0259031503c1240004140b40c02e0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 525057500 1250 525056250 525056263
    0xc150e1c020d081308032a070c030b04030c08040806040308010504090f0b071b060605040e21030703020d3b0a0213020f03010b07140a0c230306090f060f01030819140703090512 77
    0x10045040727405241035440d0500c1c003400140c4210204040b03480c1c1c2c0d001040801014001070101140904440d041a04004049a4042c1c10682c8101d162541110001d80389906448506904c1030040c290b50391030540c1034580c1c0d088403100c0032614160066003820401658010000d545080b80c1c01c000c80c402030780055580d80a460b04070b100384490003890b030361019990000365600107039510b030140c81c04c500c128070071080d10400403801c19504849001c4013216400c0f040c80c85140981d00c14503400e01e003c0240400e544c0c0c07030a0000a0b00a0160020450300c1050907011190a090007031503407a580e5a56000ca00c20a034400c0c28151008122600c0c840070034080410b040d60115004282d50484034102940504465082d010192200c5007180000c0102cad1403e01070240302d00c0380d04020f008642c0742542d1803401c06100402c00d503c81c1c0c05110042c13000403103240a80b03a9489c00c1c0d4403c1c011304800e61a040d503040980c0b009080710303580085000c408041e80480b04005031041500d22242c080340187c10103a0346c08 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 525058750 1250 525057500 525057503
    0x30a0206091504150e01020403080a02060601170109020702060d180203100504080301090e0118230106030b1803070501110304030f0e0907050a0c150e1c020d081308032a07 75
    0x902c045004524402034080700c543d018040059a107031650701103800c80c0e000d0307401120209404075404c1d964680610071103620042c00e0034026802c03400b01e040440c5803d030501840700b08943c081102415034981409a6620f01044007041150041f50341c802c003440c03404800f08a200f40301300b9030351480d030304044c1c081d0038095a40000e61a0540e4240002e200103032400c030040d481c00350743c0d540740c0e1071445940031940444140207460508100404020f00640c420f021b0030156001c0e0b0600400f00000713003903c6a19980040b409001c0c0000707809004010782184642c240180c0550708248500100c00c50307807401180228440e45034024491a01002550490080820503500601e0031002580303072070040c4c000341070060f0103207410f054403c900c1d40c03014246041c00050804c5503130390740345a03032140100b041100b0405c285140c12007442240c40e00c00039034940b5403100e1441005160800b00d041611800100c0041035070020302c4076100e1401c04014180f4406044540101c000b54003510240d00c1013402c108c6460701d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 525060000 1250 525058750 525058783
    0x501020a0c14011403040308090706050f090d0c03020d080a0305060f010f08040528020a0611060c0d0609060e0709060e0a03170d0203010303090311091918021002030a020609 76
    0x78038140c503090002c0080000c0c039040c800211100c20b180028040150b202c0e0380b194032000810305281400501e041950b8008105004080001600455013001903c12000c0c0464030006010704600d4071040300c200c29030000750024001116035040040740809000610b40b03035a01000644c2d102c0080140c0031040c1e224880c08215040704c00e0308182e20646400e43c1c028000c4045070501601c0c00d160020107031038800c0407000d41c1c40c00c003042411850008503400040c412450000400000110040c3c0c4504c0f02800101c040c020029980000b103c05402c4400106070300402041600d545900c1902c4480301180c1180c0021840600420028001c240e0118842c0b009170102034490b00319510764085903030800c010440f080d070500c08208004441d00056001e14469555004881d103985410441c2d204030b11440752240420300304005442000701401c00f004540c198000c91000344441050503a03a00d003c0000c1d40022101401e9045190000300510001100354221426680c1f1000d85a80b41c805102108821 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 525061250 1250 525060000 525060023
    0xc040b07030f020f0709061a0f0906070311030301061706090108030313030302090d030c172805161b05040905030928031a07050c070302011d0a0905100501020a 70
    0x12070310503035100040c42d481d401120140402071007107030f240c00d8a6502c80072115480d0341c818001907050382c40188024203e140b0250414503500c540e06290b00501c0001401030602042d540b0034544520782c0341c441c1d403004c042540da42c3d5031900c00040c942d1416911070072b16080640c001ca55039041c40340300c081c100e0f0030420156056480b103078485015000086400c2e000c1503000d00c02c842441d81e03071144104400b1301c45e442c0d0002001461900e45214a100e28000d642080c01380103079040000221f060109030041e034214083c1200004074203990314000c40d66242d01c0d11815021300400c102d280c442c158000c8800180401c0a546e03544108000d031807102800920a80003070100c0201410602c142142684c140c281540790300840003144c5a2200c0690700a03074040a90352950a89054040c02094001c401ca00d012460404103800040e0f4682d0144002410802c20410000810320442e007030b10520b00004000d061255581c08405c000f420341544d08510100310214002a10741c00091401d001030b9010f07103203611 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 525062500 1250 525061250 525061253
    0x70c050d0f0c140d021513080703050403060f0506041b05090f0307031403030f130803040f060f021b0f01200313080c151f09050903090409030203030a050c040b07 71
    0x1000010714591109018a80ca84100000c005103220790391981c000d0003e02100c60700d4003009242611900b06020320000710000d000b4001ca04070b916504032a000031a4035038540340e41c43c0480d07841c032a541c0003a2000c0c1c0f9121460004c2d09054028601440003210140300545150400d400095100c1031641c010403020000603206040c00c8040e007406a00c000c0c280c4040640d40c1d100c1d204451010002c020440d0000401c1051059501240c540c00100015020300078000346d540c0c004640c40060005002e40d00d00398040310400c002c0703400c08401c094034030301d080d0748584034214031407900001c2d5520900d036402130790040c40a401c8144100d5010340f00100b5040a41401740700c007498180e00103000141e505641d1502e04000c58601001007882044074802444200080072940c240c2d900050081c800c0d10031034049641207100da0b40102020f840142c48000b07503645840d9852450740c0700f1041c54a03006030421082c6400e254010014500c6004514002e11070f59844000e241410f01c43ea000e0304110440a103d03000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 525063750 1250 525062500 525062507
    0x501050301060917010603050d2102120703090212010e1024051005090301021c0b03010b1e040905060106090e010b0901050a08060d0c0b0d060803070804090b0310060803030609070c050d 81
    0x203050f1142400012800c1d248d8441c5400c081d80201004049100c100c4203000b4481c0822030314044507011582141400640e04400d15064400740031502099208d29545080d540c4d100700080e40c540c00c110080124001300ba503c03c1c2c5400a190140c1c0142e860500f600c0940e10f205d103240c8002d03c00304502000800d040c41d040003250098400c0910401400b400340c01500d4800b44010140804d14181d034071044840c2601040a41d10140307250b900a9040030301805054407070700c015000e443c060310b81c940c06140b8220082001000708030740c05485403298500005031250040c64210603101484103a0312181c1e2680403040703280c03184030003d500103403080003400c0d03000748100100f9422600060131100c46c6610380d01c131000031361040c0d00200d198180024212070090700760304c1030000401c01800518140740203911152224000c80c0315018600d1b440e20884c030103a503020702181200c940c108004011054842501560344d400c1103805501403803038207010401aa008ad004210b410b9030000c0204080d15040100300c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 525065000 1250 525063750 525063779
    0x201050c03040b0a050702100c051020040312090e0c040608180a05010e07092003060103390804022409030304080f060615030705090316090c0905010503010609 70
    0x1803a80340024080410055103e00040400c3c00f01543d8441e00d0303942c60700410800c03c000c40d080c2c10502440e0108180001c0e80800c08042c51030b20f1980c00280b00c070500310583c007000310072401c41095082c005800300400c2040840740058944554860516940300c500703135405c1c804152840c1080700001d0104000c03140c812411a90f01a0b010f0a08800c10a40d80c038500b0f10f8240c0340c05048410b40d45801030503182107420002c0a0051140007824003204c5c0300d0004a804021178050715400c1c650300040020301607402500680f407070801c41d811800720300f9060a0130703190358010045010144500b0021000030103200d549680e004d61340060090015541c1c2c01e05625520a04008045040c40240511101a41c050025000401d03450001d030008060303244219007401402010036229595014460082020380c0c03040c1c9600203114108140d4504841c0c0000345016290803001041415001000c2007001031a000b034502e40c5069158804200d0702c54006590900007401124006902c1d45810410300c900303034818 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 525066250 1250 525065000 525065017
    0x50103020612060a2301030c2a060b0d14100203071b0f02060a18090501080a030c080d060312030b1203090114190201021308010b0f01201b1003050112020105 69
    0x1420300d55400e4031139001c035464011349520300317003ca1180300d403940c040c0200d65600d495894501305420702c04410941c440043d01280352122004080c000401c1480e0b4071500c1019402025a02c0030400c030301d802076080020316110103083c050711400f1900c0c9801c50007548e0040b40b030707915001c0c0050072250b0341d036030b640c4002c800c2610429810064000546c5950000744042c10f4180d80f465509000328001e0390900380307594022800703103161034010412514041691911a075051508410040a0381003c015030300a078400400301030f25001001003000803822500b0749200070364034280b014005820400450480700c03078900c01c00307400030400982658801c88410a03107240c1d6001041c02d00c80d242d20304020942a0450550141c0e500150b24813103140c1c2c4100c03240c01040180c2c024403a080a500210760303140b480c4007070719051201c407800800c150034544240905660141003125000105402c503001e20310842c480050082244580c0041c51502c00e0162a05840105883c4c00303510000d0350044520340d005080 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 525067500 1250 525066250 525066259
    0xa080405190b2e090c0207180606080c03070c060b0103021c091403031003120507021002010f0b0402130b0714060106090e06041b030504060b1302120a05010302061206 73
    0x101121500010380072903a078068401c810b05840d00030b0f09001c0b0340074200340118803100c2140c140c040c4002d0541c1404242d801424010540a059000507403410040c0d0f00300160f84a0510700079041c19503580c0c0000704807820755444000585a00300e00b1001e0348416540c03440000c20840c80700e0013245643e00184030041041c50018981581241422038562201c80c2840e64141c44124507024000f551240309001c0e01000c01031481c40c10509400300c1d5995043c4401000d200c80035440741c5c2010b02032800d44020940140c103056030940c2440000b8000c10291000c0600d96141205403040c41c1800e1003560b14198000d09200e82190401c5003102003900300300340444640002e800c02040784c4c00706000f0306008001c90f403502442d15041030700041050f070700103140d103014515104003245422040112040c0a880e50300700040c0c16100c030304089002d440f00c00c40036500301a826450106080300d543c002d10100aa00c0e080007040c0d251307240c0310400d640083c8030181d030101d000e01c03c5030780d040480c1d00c02c00e8101c80d0051 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 525068750 1250 525067500 525067513
    0x18040501051e07230403110310050108030304030c05010b090705030901060605030c09040203130c08060a050a1b2f100509071d1504110901030b0a081e071d04020120030a080405 77
    0x2c3c10324004d0fa0250b0012640610394400ca907038103080c10010f42c03007a5621400240718035810038841c0c031390300e001c01000a0100b00840c140a020b01c082075103c821000d034040c0c501d00c1c0782d2401b4500903103240c1c41591001059840c0030710000703203d44940d080d80d000d80040e00c50546003220050030030019400103011200c7c4003100418020000c1c408510107801020328070f010b4105450004155022214010017401025080000c150000003480d2600e0134913200c28100036840f0380d01d9010603450f00d69000250310712100304c2030540118000004043c0901c41d0011003d000a43c2c54421054a0701c08520410465214050341f1000344a50a0345090f800103468070006030072501d1000040588a041a60b4036002d0300008030648a56854040c203800d200055503150001440c140403d030b41e41d9140d0401640050141c204501003c1090221702c0c0100942201a260002c1c8180300c1004a42c055600302e01007407486000007107032540ca003890031802d00d602d40a10305040314403c065410050040080350940200c4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 525070000 1250 525068750 525068807
    0x1506040c030b0319020a0b070f140c03010903050310051c030e1f031a060324060c101b020601030c050d03051902210c06060409060204030218040501051e07 68
    0x404c51034504920501801da184000d900500605410329000244d210303104210300300c0492401d0010300c54640e80700b4000d034141540c11010360308207043d80030717030030303455400d02c20803209040d0302c840594011400a90351808003655002007161011480b100e1000b166002860702c00403c1c00b03994182c4c00e0b4617015186108102c15056880d94a210074022000444c6c0d03074184041c285200b03809814124a41a14007902c5e50824591000c1d40c3e1510781c400c002c512180c4442c01c00fa1b500c5120685420303c402008807161190244900b0b80030301122514400704125050004500070720014201b4100c030f0b0443c000d07068107030601e002e010440800310320580c103102003042001e00c50405074074100e00801e40c543c0940b1031070052a0321706503a110000100081e854007800302801a100c00308519070011001c90300010f0f17103034040c90001c000c0d001d15031001e5400107040c841e501e10301c40d4000200b0b00caa071040001300880c2d80d840c912400909698804405031034000c03c00070b00d0a0780560901e551100b84805504000c0524 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 525071250 1250 525070000 525070003
    0xf091b08032109011d03030709121e060213270b09070c0503281206060516020a080a08070b09160e0601090801050a06030204060b090102030a140c070905090f1506040c030b03 76
    0x2045d281c141685d10000811180c00c2c5d000782d01102902d01e074100107031600c806441ea034160a05583c0001501c10000701c0080804c9403d50403602903061720095400d600b40c0d07800b94954000d00203074440000340511801d02c1c015010714880c800b01003800800043c42501d60b00c0301100c009200e0107044509100c10004116a00e0045212070480101d070740b0100c2aa006680006180d58503904242c450b050800509114140d04182520302d4203c0c1c2e900d2120f04180603000041054042d42d215240c030703004900030601800b0880d002401a140140c2a00c3d0180d1160800c01e540c44012240c00c940041c5c00001c14004407108001598120405142c03652191703850301e00d26421224282c8107600b072a50380d0402041142014000c6200810801c0101800c10310001c0000c0d44a00c02c9004100070416042c5050311031070158000d560345000318504448455403158000d10041800b902e004a4038440c800300b4201f40d010001e00003c165500458014030340e01c070b0302c0911001d0030090301c1d29000d0503100c402080e0540c80 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 525072500 1250 525071250 525071291
    0x804050d0602042112030e0102191121030a0527010e070e040c0902160c0602060106120b1e012604030f0504061b03030f091b0803210901 60
    0x28141c01680c2c0ea16084103a001c0701004030707000801d4405180c0442c042100d42c400396891245030f080205102c0d9600c1e040c14020710400d4410b020400038005010000b41d071080354074079410400b40c00c46108046801e050708054503241d03000d96100004100040006000d80c100a40142e400c4028030401c1c5030140940074030005003000c41030640e40d01c0c070707800000280c2040120000c0042807064442800d140d210100c1c401500c0c0200c00c4002d80000c5c07a58592003824047d0144190412640d54055031a030b030000707407500303828403902c80015403074070300e405660115200c2c210143c400148041c2c000c00ca40301d07589041d805040902410b000e0200b80c0400030702c0c45c108000d03440c0341d019403002c01d1600d89451f02401681c0c0e00c5e03040908000d000c2c0001d0012640004a81040c2100322081c0f00202010f40b03070880c0a03148488685240a04040c01e0100700b00d1b00300340700c3c45004224030041410586450050f035582c09021030745030300848054050500c210141c000d00f5040701c03242c000855084e5501800244209 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 525073750 1250 525072500 525072503
    0x513050d11010219080304062a0f0e011e0c11030109030c120906021f110a03020304020111031e070602070204110d0b030a0f02010305090c1002101506080408070804050d 74
    0x201e000e18000322960781030041e02c0c9881e618000d918400f00103501c40d41000c1c000104014207095a0b052103160800400e0000b04030182c828175400c0e03401c419201d0013890401c0e003049040200350400c035061407030760140096020003c203c212031304840c0c003428070440351406c1c07099068545080c5210100c03110388007030041c1a00540030b80c5461104112900d0a00e0301c0007040d924100803c52415402c0c000181d02040e040ca148480446090851000c0316143d03008000d403242500a0070b00002c0d14040894054010398444d90003600c0748a85041400301a030307164031480c690801c0e5046026641d849202d20302c8064059540542001130a181c003030381c0480c04540b4100c01003040001e001c500100860414000d29032075000036805403403060b54558441400e1800800000e041c1900c2d840002e014131000c1007032460b00203008002e04454904810003a45031440052030390f90013804d02c4018208074215110f6141192a10781d00c8001c0d541d5582c0700c0c0d94098101040449071a6001c01000680303035501541d602556 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 525075000 1250 525073750 525073763
    0x1403060a05130e0c0405012909190806090a080324030a112805060a17010e070212040510211a09010501020a1109071803050f1510060513050d 62
    0x20342c501003d1460849803940991241d802c000060000c812034486041d4a114031003010004104060300d450000e028080515402103601c507104400c12402d001018211011601509d4684d04d03090140c9840d01020003000d0080300c020008103422540c0502101c0340114811480c85900300b2030b10001e4184020a00151008100700324034600c07c4c542a01c907403182503044070540b42303100385241c000c002c411300380d124080c8110008124414164024490345108004001c4245041c0d80c441c0850340c00904240c84081c01846410040521502030741c0440341645c0c401000309070003c0c0e00c6078084031010390711301c0d084514410344440340324400c0b01d0380640c1200c00761624000708200e05002c203100500030142e100a0456101c028900e01140504611801c01031013039640070001d0ba102081610f030f544058201480e0003072012000414044086001c05410f01c1043c00c0e85e03007485c03031081040402c44013564440c6002d00450400c02031940540000c015051264403035400150b42c0d100060070301c180540083c1c400 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 525076250 1250 525075000 525075011
    0x70e0109050c0412110409120201050a1508070e0a0917072112090c081209130b10050304060f0903020c0301050a0203010b1b070305120a11030403031403060a0513 71
    0x181031401140e0707100c01005052030a251401000e035451103400203015049900c90408460b55445503005160481d030001070711000301d400900028002d060071500303240002c0c904040c010404900926480c2124030b004010102a4102a0801c40b503920161011004540d140409400104e09180703102c407042e046150903440740e140b420f060b40c4202080b0325401200c00344480c0100801d402202c101510030b06044009058480307841c1c248481c0019400003803c501c101070401c9490301810004040050050795821182d4445c42c200000790340e110541d40d80c0c400c0300c0b03038207002d00c880c4140060b5078003030702801010503c50710b180709d003a0480d100b070002500140c000c40b425011a0400340a1250841a80300d011885c4d5850030407902c3c02401031303464090b07100404081c2c880e10200308001c00d0b0007558219040d02c0301c17851544040305241c2d000e50180d2000c600d8500300011070240102c161022070760180c4940c252004c0f411000c600590000b8600c0303904c281c1a54000c2940d40318411403501c200c2e141c6100096 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 525077500 1250 525076250 525076259
    0x151b140d08060928090222140c0901050a090f060504030b090610090b0102010b03060106090e0106020613060b0414040501020322080405091b210109090f030f020f070e01 74
    0xc1e00c40280054003503d00103080c0308130401c80140785902c082c02d922400840b0018800d04002604125102941c40721038180d600d941503a07070350002c0e43d009011241c200f040911b01016480400d204a030140c0c1b0700380c2c0a201142640d40910b00803c3c914200b490040400f075101c81c60364881041c00d80240c0002032001c58140100440ca80c102030304003040b0310003082540f4042c90060407604680c0100400c040e02e4548509041e4004d400440100500405440881d80c407a0001400c5020510440600d810620000102c80c0d00125140340600b0071010300340380348000c0d80c94040241c012200c0c2c40790044d55030300c00d20a41500c200d41e00c2e400b40388504000b5a5908060400c002d82000003001043c00d2803d1840c48000205180100c030102d43c1e0039107800803140d03900201c1e0030078000d0020042c6800c09000801c40d181c0903100b128100d9607100c55000c0c00c0140d032903034000422214960030090075030040a0044000c2030242252820000c1a8411920340040038a000382c1001001c1d8041e008440d41c0f00010b00 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 525078750 1250 525077500 525077507
    0x106050703030e010b24040b0313020f06070804210f0b10091a0d05010e0a0521070201120f0e10050f06010e091b04051f09090204151b140d 61
    0x641082900f0080c0300d951002400240d01003502140c0001100c420084032485070501030564004100c0083c01c0c0b80c481c644851043c006008590b070403407003061550b8014007586058416101441d400850050030b040c244810f0600c00d0160541c21000540ca80d10307088e0004032000201030500f485043d04d6445410560380845c00805a900250790b62030402a21340e5040c50010908607131882c0c100c0725981180c3e0707079041c1503004101c0c0c0c002c030039098050b1950398405c0c01000500740210981c80980100c442c0c0e940341c540603045c040d407400240041c8204090003003040035a0801c000c07905000400160078001035051078985807207214003809440c1c4171020071017071080340c08542d54058428281400181c0642d030003d443c002000b001e00000e000c0d0f100700244188942000c1e10060400030307207003180d40c280039280b9040c505502030105001407c14500820f44941e1402030f141110f01a03c00d0700324412401f1400d42c1d25040d14050502d8040d240d140260100340310901c200c00d414050b60113004a00301e1f126005 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 525080000 1250 525078750 525078761
    0x902041b08101202040203060f10020604050f07060f0c05070506030a091707030503040b130c0b031504090804120510091a070822020609100306080f0708191703010605070303 76
    0x310b6221405804000681035034040d807900c02c2c0d04980051741c079500c0300d000030b03460320980302c240e034025030340300150407201d60001245800346000b48100d810040320307068055035419543c05850005540c01d140308072428040d1203000c81c0340344203400b40c440d0103440b140030070314a400803202542042d840d05d0441c014041c00304125078a1401c1d81c25020701d072075615100600103100c00f0304014442043c283c00107185926808000c2a03090b0322050304880b407562003810000a800c183c411030341a0b1070000100c0f80301d03d454400c1d1403410b90301241003801d2900d000072003d5400a01a000d64841c0900103464141e0071092103070041061064040101c16001c43c0a0854100001400001440314030418441c9421026240c8403d0421070b8070f010360400807500c0400c0aa000716420315400080034130050300c2103030301504000141c800700021a050301d03d41c24021366640b203251041c005681c00020105141c00303003051405a80c64000d40d10b94041c1440b081e5601e0075540300741e02000001d90040b90078410141e141c0281d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 525081250 1250 525080000 525080011
    0x51b0f03030f0f070c270605090f01090c0201021318180305030a0504020a120b15011412090304080f0604120804022d04140405160f180902041b08 64
    0x11030034000b44201d9075200f0301c90340c0f012241010700841c104080007102203c00010303110120304242c000c07011444000089a00b004c8264007142808004211401d06c801c400d40300b00c00345101600964030b05040c806c010030701035118200315502080703044094050185048000d207030707070510b603070a02c2103a00e60b400840b4208131440b5050240c0000320800b181e84881600d8020a0015000821752110f10004801c001d06030300c40c1c5800f4107040d9028040c0a0405422031050030b145c1e132000c041801910044410000c06144604000f00500400c41c0000303034074006644c4004542c080700d00d080c1e00d604080e0310380300f03038034220b42c146c2e0b4022001c0008104c40b036072621184031480e05101c2000d080c146d0025050801144108000c03d2040f0010501c0c00206584044003040c007030002c0101c1480000c00314032803402298183e130312b40700d01c030702c5101a1283c40700f80380c0860300c510300410301c4542044055410350550222000b0481c0c0c4500c1600d000d40c0e168811008800c2135011020a10b0b0311170030020701044402040d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 525082500 1250 525081250 525081253
    0x11060903151009180816020d0f050d0305060d08090f06072303040501050a0c0309210507150804030f0504090f020301140301140a02090d060e0d11010203090703020913051b0f03 77
    0x218507044403445013039200856070051600d40c07203800304226041810000000a03600034028032140040c444001c0303d681d02d1600500503543c03c0c540000047c0c0581e8419140c0e030750005080d4840f080401c0d0032001625100c1d034000d200b020320500650018074207030000b883c16034141c1c61890f03054045043c003980455842d000c0e00065800c0525100010303010b40965092103081c0119001e110341014811028180071b000e10102c4031001c2528000c101004541082c0308880c28031900801107401800c181100c00040341640d569000ca940e07954007191421500d0300d04009000f02440702143d801c4080c09409030181d0300400060322585000717445c20000c1c00380100240264980006005a07040801c2207950207855680e002d40d8a5100d48080344003800d40110250185113402079015580c50007144030301c4040425a25010103c1032184010b00700c2c4401e40321302e042c65218040400c0142000000c07140d0040c210003400b400d0031410744500d400c5c02e801100c0500714140740c0314840d05620307211100c028040e10640 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 525083750 1250 525082500 525082511
    0x150a1a0301030605090f010915111303080a050403051504112205092509150806011505071a0702100c0815060c030c010609050a0b010c11060903151009 66
    0x44a4211888180405480f0b15101c4d400200022000c2114018104900c4000c002c010000d00701724401e4040c00c5280d010f542d00300591070b950f0b00074420548001094400c4803100480c55039580f103000340d00822640080c01800d20001011074028005085100450420101e0724941441c0c02c6441c000040c120506c101409400468070300c0721045000c80c5180f00010010386074649031640c51401e82240418041340c20340c00520400140385156880480742034a030140310240f8440440c15540032203021381c901d21b80c000001044504400c0714415000556030515074900411500c8115084c4018103240030703612918410700105550402450300ba080701e08100b0040300d13490039001484070704054654800040d80d101103520740c1d583c0314201c61940030031504072640d480c003010100c1c0c080c0c17002c0d201d8007481c20b14100004a03090701c140105c03541004143c1d28003c000d42140d6904c81528120b0341400c1d04114284480c1103191410425001062044501a80039207000c89201609107001c1d00000003241c1002e = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 525085000 1250 525083750 525083789
    0x6090f0203090a030c02010e21060a09210c08190e01050f0403260a1206140a06032004060c0b090a17070501020c03030a2406090b07021503150a 63
    0xf0507444030380707949442c0c581c01a6409000403503440551074041a8031020039011140e04074114081e000b0040116410350303804c0c2d5104004001100d8030780e0f00c081c0c801359450801c500b00784817a00c00171a120308107041c07100340884142c481d0551500042c6100d5030000e5015000204541c0019030104800c41c00d01e4080d180001e0143c0d091a540290f100042800111030031405e00302008010703001e2566211502d05441e2410b4138001004418001e0904800740d04c4c0442c08542d41f40d9100b00b142d030803080502400100d9280c882c0c11001004840c036038440c514101080c10b200041507030000c20080c50266601c1e00110755609113903540c0403000d04004269406070031180001001001d40b0620203039005001900c40c1c5080c14404d02a104229811590f0301000081004001c09035205140620b1110750204940c28000d2a21544202d680103110115101c40420404003c1e24002055102d01c0589540c0081240d03240c8088903800c01d595030180700b100000040d2440c100409104010840810a1145089070 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 525086250 1250 525085000 525085003
    0x305090405100b090d0305040306020c010506090711070e07030b03010e0610050103021206061605060403090f0905070e19030506010320030303010b030a050a181a100501090b13050603010906090f020309 88
    0xc43c46400d01031741200c014031046c503001d02c040e07600645d0044001e40d91041c1c403105050083c002254424456680e800c0450340d850710464810301c10351302e1315006250f02420060450035074400101014100341d1072b00b100b1140380c1c40a025501c0305250201c014951400c082d108120300c1c1c082904213904040c41881400b11440500c4111504100c050350765960f0340c3c024216a0b141c003504004007034a42e02c03881c0d0a00041507031086901013152a1762888031940340d190008041500c100713a40010018444410001c031302c2c0341045100885065003c3e0000b0050360300e03942e03507042c400241c2c8191001c0e110b500051100441d25910059944402c07809145158184800500f950101a0001d900d007580d800001d41c5c1072000e0750015080700c01ca45003420b202c15a92030241582c4c445c40034118014075120011822142c8003501d10004d548050311000d2026042c2200040c00da0048850840800d42040d0009003d4540100550180c10040c0009c030316941000803940c00d54a0307040d05410418810000c202c5901c60 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 525087500 1250 525086250 525086257
    0x8061c031e110c060c0a0b010e01051c0308060f010e03070324061809020d06110d0b010219080c030708030c03010303260a0f14071107050409030f0f030f090305090405100b 75
    0x301210320588420b816145d0600d40252500020b143d40c40940c00070454041c000e00440c101c600403284020180c0c03078a240020a02140394005000c92200000301c1c03483e1500c844012184a0103160070440c8450020000e0314050895000380e03940c0031415018544800b106103002e0700c190401d42d05118041c80c120488100e46900c8569154007981ca20302682155542503068032460f0b04088240105402c079120700510303500920900a6031450701c14204a40d5001140f14502d440c9100c18085c543c44580d01c4400702ca03403001c0c80d0380e901d5010400080303001402e42c8024600650740c0a0b1801d4980d8154600508000c101410005241c90394042014210fa2151442036000745405000f00f09c10030010039081c0500a082c883d5490402c0490811442551010b00d007003040e40300000325000c2e00c0c0e403003061004407500c0750b0300540000c08050074100024040c1100d410b0310303071705454000ba200340550f22803001c40e1004441100007400c002030000d0685060f00403a9040402400160806807600c2c45034940b522 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 525088750 1250 525087500 525087523
    0xe01080c061b010605100f080f0405060714160b010e0108070320031e210301050303070807020d0c082407080601110307020613080d020d0f08061c031e11 67
    0x180c003100034a010b0070341210008050217458041308041e00c2d11701600704c13448010400f000400030301c00a141c900f450940680144e0b04007001d03083d282c032181c41c201c030300b40345aa801030038020041080d400850f0685414180c041d000302c0d180042c550500b480050074141c1179020412540c8145814000b1071205000b00c8500900046026242d1401c50701103420090000c5d0300d03882c01a0100c0c1d115604010206469030a0600c0900010a80071225401246030000380035080e015801844031000250311540200302050004100c030400d42c040e591001ca030803155800c8007009822101d040150880320083c3c0d1000c44100c6962030401c6c0c40d06000090401c40f000301105d04001c487d6048944810b02441222545034001c4c001644c1c499a614010607151040d1040c0b500704d100d5541c030041c40c14400310f058000d00e03035180d035507101d40702e554001201c841d0300c054803c1d94011840000c1e07150705480d5914420703916100391904e551040345064890135681c058040c401c248140c030f8184481800cc08284100c40c513 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 525090000 1250 525088750 525088777
    0x20109080d020c010f0c02030d021606030c0503010e0402040603050304080708061e150a091a101704060b060f0412032304061112040303051b03090d020f0114130e01080c06 75
    0x1031000305044681745d00086e80a0340501072180e40c039003c181c0c04210481710800c88030b0510b18141d44e4950480498802e400d4000000d901400184100c42d000c26810ba0014001000847c4042d100e80f58142503500c42c1c4e101c00c545500550041080b4078060152691119203070380852082c00e001c61864603024001030a02c1e10310014a14406c1c1e090b90748416400142502c0c000401092500c0c00c000c28000c4041e01c3c696202e1100c45500100003481284031444512184202c1507141c1c8859461101404bc008106540564148500340700c91030110060300051100600d440c106604a08024124254000c0f0510b603c0c00045002100752001d03d04540440e0418a850102c7d030031464125824070400c600307080c8030000000781c004103040d030010103006c0801501144001101010100c0381d961301c160303280703150402800d44004000d460001481d0b05d0109060402445846150044035803d5020582404110007919024028000580b5440340035005403070080c03c50200181c0002c015003c0c0d81480c4410 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 525091250 1250 525090000 525090017
    0x60405010f0b0c1002040807082a0607050118080702040e0604120509012007030c09050115050f1c0608011103040215130e09060a1118060d060f030807020109080d020c01 74
    0x39110801902c1c15100d180c00046441b01d4581c00e00c1d0b42c542c82180b06100d400e00c105110f40c8041a58a1002002180d0b201e02e040203190507402441381d150006442030381c1c255600da0b0308110815141590b03450082c403031441c07107542d20a140b04200c2160784c0c0b40b0110280d640000104800103850004008501c240c0342041a11141c50600480f245191443e51040010b001c3c0c1180046c1c09001800c1c0c000e5901c901c0c03203001c5058a0b449404121502480382d409400456003070210a58090300c01030020155044c0c1041c604588100701300d14425100c25001201c555885040140300001e11640320581003801103c0c5c40d43c102500059481488001040d5406000180045002038410050001809040d101100c0d80c900b401c000d903112417044900c015000d0506403508800b40c2403008450101115507041c540381d11241090010940184c07001d124280d6480b403022074400d070004140b400552040d1800c82c0c2e0742c10340740300041c01c103009548542c0c0d0950000c0581c000701c1d0707004519095625420b1800001 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 525092500 1250 525091250 525091267
    0x90402040314030409180c0b0f07060c0903050c0109050f19080f0102131421010f0e010213060813060207020a03020907030b01020105010b09030304090b0a090c0c0b060405010f0b 78
    0x344240d03400141101081040081d034550007001910071119040020040c039110450440108460490010b0a2000281c800d0107040041030143c28078804004205003070100503a80c5c7d10898005202803408900212001c004004007080300500c00c076020f1810300b03440e07440d000201e51340c0042d643d03146115142800d041002440340e0003110006054400480d801c5800050b00c0c4c500035030002264000e060721401d000f2460f86115403505143c4403010b481c00301200302d090100c0c804100500341c3c82c04107540740c20a0700c0c03080001e030140000d05100c00000603910b40c9007070741c0c1401d504078075484007060001080410505202c06440310144c3c0f50055405a078a07003c61001400400340c50300020750282002062085060f0715510401c0e000d2800c1c1c0081082e66202d609540c124003690110303d5143c5d000b000b00348401c0d103c94100800b00c040c0a05404050350300d42a040c010f4503900003020000441c2480d03000240045510401e40210080d5003c1002c1e50401c0c0c0301d402e6042090060b949074a000003071409 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 525093750 1250 525092500 525092509
    0xb040b03130f031709010603030e01030902030a0501151d0603060105130b10031d0f030313050106030506040b0f0f01080a080f2b0b040b06090108090a0c060905040c02030c060c09 78
    0x2185540050740d02c0e0110032628025046400d45008141c520000d6030024155070014440c3c1d90941e500f40d05c90400e9580e0000045000d020300c10001c82e00f50103404042000140240a8005600c500c1000c0310b06040c20720422201c8940c004612400c00b604030f50620000b41c8000c2103c0781503550039240242c4050038080c071032016016402400d9013040c460498a840d841c1e2651012801c8003a4502d20140c444012014507175a0500c408070f2704140d0810000f0034414098900c0e4011740611074030010802c141c0d65141e060030003404680c00e442d07000144007005100000080c03115441184040400f1880d4140001c2c0f5039543c1d101c000081021a00080b070192a041c08800d4411402c2c1d0a115003002041449544403605281e41141075054107003000800949007902a4501405000e46580d0a050440c001180c3c6200302420b15803a80c042c003a0300a000c200000300f1403015104c40e880340042e50b49004140070803601d00d0711441086400910410298007004a021908080b015801c2c80c0c0b10000540081c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 525095000 1250 525093750 525093781
    0x1a0d0b01170a08032805071409150c060702150121030e03030d0b01030b0f060306090a0b03150403091a07061d070e010e0606040806010e042f0909070b040b03 69
    0x381c0060070200030440e17100c400ba80c0700070b5545040c4141d415401c0da081c00c0c000c141d502c140d50600105841c40444c00c45000c3e1031000d4075041e01c00404010007540905514030f520ba01c0035042500c10303003180003080101c680402400007201562102d9440d1076142440c80d00a900c02e00b100c0c4108020f0314185c5a051511481c49120b00c070b000103042e00e50300c0b1070100c1e02d94000c00c1c0716030300580400d041102ea1003140c90a50f00e223580000c80075218074510780d501c02c200200030000409940d400340d40c80c080c190103502c042105aa03000030000c0d003003013142012f0a002d0441d5600b0360010500e84c010f64185042210000281e59500b0303804074000c0307180c8400c00f042c41c0804074411200724243c490080005200d4905042c00d41c103c0e00400c4600045481e00814017045208070300400d100c1da82f000004201044006039026030040c0905042c402481c248031603480040411545102c07252011303115240705240c400003040e08804d141c4d0040030002c0c503083d0420018000d0380320745600c250000c00020840b00c5106545e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 525096250 1250 525095000 525095003
    0x406050414060f2b230a02040501020c04110408031c0b0d08070f030e10020d110106060509010f120504060207120804150c02030c01020a0906081b1204021f031a0d0b01170a 75
    0x3e00c00c080500c01d102c05040c07176100265803048424004560400b400e4405c80b010b032034042e40609100d81b035900a12020b0902e1305500d0381c060404020005401d20144040d004502c1076107160346001c1614520001901c010b94040c40c807a03d40141c2c1c940009004108403104268031005141c0320201c0ca0800f9124064800d42a03500301d02610264004ac5601140315041c1014a2b01c0d568030410001080d2800c0700c886004400c0498810040344900e507003d96880c0119074101c0c9080300d05400d58807200f0054a206a80c112200c540101c0c9503010003c201c2005a49903200380741501d02441c00d502e80e8852050302c1100c4070842c950b41d4524800c1c0740c0c0300340122020705502800075540d03041084401000200e05204040000b426040442d000030a1104075081540851262a0522905003084090720340e01902c2281d000164070a50155070310700320b80c0700b40000c00c0380e100011441503801100000d0604601114816003080c5900000075245a4006054406008204071045c6540800d40c0c50103a10060 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 525097500 1250 525096250 525096337
    0x150130150516050a1d180c190915081b0412030806011b02090c090607080c1e0a110406150206071b08160501090804090b0f0105210411060406050414060f 67
    0x4002061f25080e0007002c1440d03403401410055400480c0844140c41c09000325102061058a00000180b1480c819a0001d48198000000f405121038111441e0f0095000902254070406494203054002c018550b0112023801c002e8860070105c0724000900040000c000c4c4511034420104a40e5010201566999503026151558900711400c002c6610707042035021901c03a20419070605902c8440c41e02c10300e000340c1600002c1040c5080341d43c420140c0c1c601e41c8203090300940e41c0d0000140c1000700001c01e405030f003090740150045040a4000400c001e07124007681040000e0f1000820008058108940406821221503170100c4038500e40386015102e0104050004000480c0205400d0415407242c0d801900455412038010340031030041d16203024211810510805000000704d00c0d241404203a58010712074000d099050721703d1400100a600305401034400500013050501065a00591703900b0802e504880d005c0c204000000c40641a201c0c00f00060001442d580e6100c54801003030700c039102c03e00000341 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 525098750 1250 525097500 525097549
    0x14060907110705031618090201020318190b2119091106030408030a050f060901030f11040615030b040204030b010506071b0e0603150130150516050a1d 66
    0x11701003121a415809036000001e044c3d8081e014101561103004400e40e8180c01942c240040340080000c1c5046401d0311540005450303106540c1071030003400c00c0700500624009651590b241a80309220040884298000c12099a003802081e580d09804d000c44521000c0c03020410140600c0d202c401031101041460b0404004014481040a41c2000d5889060140d408120680d1441c45028a01c2015a03415422204040041c0041910300c2e082440f07013070140849664031000780700450211500e0f0f03071000310300c0403008032140c8506078140200843d5090850b0254103190840c0c070f0781503140c00c040c03045c3d41c80740c0381c0050130b80100642e00c1511508904d4041180c0035141e80e0b240110740c0c84d074049410501c05e01030003070801c0c4002d81c60b0522038141d58154060314034646490038800c1d071070030068403040502450360854400080c0010804505180c2c158070225a40c00c10011008100600016650a0003018014144000d0b8400d414404001003c0001c01581038201d02040c08800b42c1f0003002c03042ca4804 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 525100000 1250 525098750 525098773
    0x91203030e191208010f180209101e0509060f13180203060405070c0506160c0c120b0903040605030f131a07110a26040509070c061406090711070503 65
    0x111016281d0b902034140380c8003010740071000700c0d501d00090003018580c06440005124000e10b100b40850300c0f82c4132503c0145480d071140b002450700d842c600d424900107038025586000d6003464000500b83d514441c24980e0501500500162540c015981000500000400e4507074121300054814002040c2442c1220701e20410f020b20040a540200c6485002e00d0908003c0340b04180f2541040c0718484d0000003514045d2a1040c0284240c1446501d14042140d01d02c240000b0600085074840207180004181841c6403480c0f5024150040042c030801b034641090104100c0704e600401180d911200d9000881c1c45591101011003d0000140c0080d00307000752401c216480d00c0030038071403038080c0d075243d00d811404c07041d0403801c0c0d9654401c03040300500c807010f0000b0541120401600020304103c1482185040603103030b80104843d541c0480d0801d000401c81c0248030140b02e002d1103403400310841d00c0e0a0042c0b514068002c90122076010300100200442d0a0001070340c143c5c28048c21019041c0101650b0140041 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 525101250 1250 525100000 525100033
    0x15060302070b2e0b12070905100809240105030105070507020307060809030418020306031b10180b0a08010312050a0c03110106080d03020408070b04030203070608091006030609060516091203030e 85
    0x18244141085c0da42c00c0124801d1802441114104e5500615030030105a1a0b441140d0a00c40604400c81603ca40012400e000442166900300800c5600f00000c2c0ba600d0a0101400c0d598007601100510004000d6000540c4001c29008103541031030074a00c00c99290201624030754804c52340310211303000b00e001a03c00302c1c00c040c2e001540151821002c840c2c401400c40c01c500342c5400000c1c0d90780d030f01c14040b0103541341090041c500c2c9090401d0543d50303104160307a550491040341e401031030712100140800e0010302c20405c0d01691240c0e100d51900e03040d410084403040c0905480b08007540a4113010030441070208441094110401a043c40c0301600c1d0071102058001d00a500b260040300f800c0c1c050200081388040300300e0700703440c222500200200300c01c61501c04141c0d22a6405001111280600c000120b2840e801340201070041d441010005415007035410001d044079409044519503c03c0c0b2035035810100c0d07004c1c00400990f5600c0d03001c05189861454107030010300d11381d00a01c101c1d00404102c1120b11a2 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 525102500 1250 525101250 525101257
    0x4260a030f030b09190b04090c090b01080a0e070e0405030903070f05011b0c050906032112010e070e040b0117010b070201090b0a30020d15060302070b2e0b 68
    0x1e00351024800d80803c0b200300b05500904403440c004000c0780320004444070086400079401e04002a02c000750310300366502c94404004054012810700d81c0c4541c4004401d583c07094846901c910024005c0082c4500b071541c0341d885070030364802c14000302c01070300109007032240a000300c2d108540001d08640d84540d680741210181400c0e40305050115510b51010321042c01065180360a0380d501801006100d03041000b000b44103240070b0000340e0144251f90118045441d0101c007201d4440040380c1441e1250704026420941c0c01e0160031110b000ca4800c014009015084285101c01800c00c032400b04034203228030300480700c1e184c8200394410310509140000030704a04000041c00791a0003a03941085203905c030000c203001d500c9800b980200140000320010040701e0000b5240b0301c3c1c3c4003000302a50211180c0442c1d40160381044180240680d43ca803031480e542000b41d035805005000508056041100c40d85428a510900a02541d038070386440100d0130202c03071242075081c401212012104822078803054500400d42 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 525103750 1250 525102500 525102527
    0x2131409010b18010504090c15030501051504080309012015150109080a08030901020403080c0319020f070501110c031903030606030501050a030f1401020d14010e0c04260a03 76
    0x5191104040301070902040d4120001c3c6044540e040c664a000c0500004041045068450080c02040480e1800c2c0205101800d83d00c181d0303004c03400d9410311080040e6810415218801031000300010003120102000f6241200710900709810039800c1c03040000001c0904a042c2b180e140180050880314000620b111800713440c280c4110b42c00714010400540e800140c1e400782152560120008000203540e1800440d48a40341c58005800c0650325650000c542e0440040c20074a1342001c035403848401d90070b203018810200303144010007030007003140c078110f441c1c007524095581000380452442c0b0441004000b0241c01c0310016040780c030b5421100500901001c10a5812400a41030000000700c00384a40201c505840008101c104e069140d030751891182c0884000c2103414032681c5002041d170340002c0c80508104080c4040200d0715501641245451000581000305410204414080e0079040c40c1d040d201590a000c10014a10002c400070603d01510050a51902c1c490000c041080640c800610b130740c4da8 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 525105000 1250 525103750 525103753
    0x3062d06031704081e1609060305061027060b0c010203040201080a140f090109060507020601081e0304031e0c06031b030b010c0303021605030c060f1b070305030402131409 75
    0x1442860b1000c9a070300c15441104096442409101007802000201c12144407034101200c03200c098500600c142c004490f440100e10030360300c00c030420078071005020030360780510343ea11003036003460034008920b81681d806e02c00c43d00d4521500d600302c54130412980c0020301030111126615103800f800d45c0c4850103903100300c408a00040e40f00c00450b101071018095503d5400807000c8600d025500c61120000402000344000300943d20b039030a001c04110b283c07085600415036540a8191503041154103840c5c042c2c45c14402c0d0880040517150841080d0102c143c0382079942c0503000e0851110b40103d62503031104441d002070003100700e00b140040c403281c050f8405500c07406498009180c00f91400b0055003229840388980380441d48003808080001d103e81e00070302e0b8603212140c4221689504d629448d1540e00301c9400115590b11000030702240442d103c84013a40319000c04030701c41c0070b5004d0115021990090107002030503c44040b0119007190384d4500a070a80100085042100e0021208503c601c0c01064900300540e = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 525106250 1250 525105000 525105023
    0x60f1b0312060d03030b0909010603170a020618010e0f100630080c0114090c030604030203040b072402090a081612051c0914030c010903062d0603 64
    0x4011000c030545600c6035103680d400050b5600c2c0c9090061000c1280d10403820195544005050740d9205455140100200400002c41c5800c2d03141078680c03180e01052910181000303119030400c82e41d00086450f88031101104065191502c0240d40703001d080a12041c0d882c6004a4004028503640003d244200d40302180080c8a995510020500400105c070420108040305600060a8090811040c0f401d81c1c49240114a0550341c200c800742140c001c0700c1800c2180d0400800e1080002040240340722241c1c040300074180505080ea000395272803080384110004c0843c0403a824040c0a1440010400b071409031911980301002c0b8402400294401c4c42000e1081c240008080780303000c800949075500e00e0581c0b1801814901341403120001100e00c134001c03074181c03040d0700e28a10840120600100c0d1a20aa01c5001825003002c25540d0034011002c2c0c000d02070341c04007220000136a0f2100034201182d8220f00001030f00d4005d50200d5a0008800d14210128015010004940001769025200306c070b0080700c2e801c00c0d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 525107500 1250 525106250 525106297
    0x10903020d0f1409090702070317070c050414010e0c04050a0b04061115060d2a03020907030216031b0f05030d06080604050c12150c030a0e060402280302060f 69
    0x682003c156020700700160140000c3d80d017400c1540ea50f6030401160300455015555941c0d501071b802c201c084d10017800b120041100002c0140c5481418080e1104442c180850324400380203207150f4805100b03c404032400c910200b4540e410001c100c401400000c0d20880380305460700d10049a503030082c0f1644000460718210000302c030718081003501a02c039040c1c04505154a500040000c8130305e0000c03041d61100100c1705480059105800003622909600c60007400c0c7c18694010014088002031291060600400964100c22682e0040c4100325070b040c00c3c200684241c0710451585c219843c040200340b400100810320900100001809034480040301c06e004642e1140e035000d45034603003910b008141d40e101c0c2c4180742c41417070304080003070070388030845c0c2144d0358401021908100c000e0244e5003140c00701c2d40003080c04249850fa0003880740c15002c400081c100341c01d140d400304041002c020810070f400c66441c001e582d43e180c0b002e12018000d42c1c0041a0300d8456080c501501c00d56030103a9402c2c03c010041000a42 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 525108750 1250 525107500 525107507
    0x9081306020c091312050a050d06080a020109050312220509070c02030d031814011815050c070b0a0f020c030706151202060f0a0207170102090f12030904090212010903020d0f 76
    0x20503294810329140d020001c5c10000e450540000240e00d06104081c4143c1d010341c0321604c40e0a0050184200400d440f40031800003400c0302c41c840d007289010f5045a00c102c080d210302c0d03c00329481607042c1c003000e518900d1070842c0b001900359213802107030340045480e0030301c20851744c481040310440c1c1c02101501e42c2d10107041070540032181c441407480459100030442c5004a40140c0d0202508400d5000210340310b4918101800542507004040760001e4510b03440f640b05100610850f5405814180b04a14103101503c81d00310102d130083c000c5500980b9520448000c0c2055011b0300c9400c0450412240c135a02c0908e01080034060542c40c01d03d0b070700200c020010301d80d1000410385a6054003d4000380c50b03c040c5062104940c1d0004d4546820b504c03400c0c4000a0125600b906d80c901c4075045400141c861120208011a00e410366081c02d100e10400001c60404000103c1142c5089600301c400103038043d250302c0802c41124182044015039440c0000e504189a00480c08008006440e0750701a12500460400d4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 525110000 1250 525108750 525108781
    0x50a051b090307053303090d1809090302010906110403020906040c2a0f030c050c040905100b1503040b011502060c07300e010e01050c06060409081306020c09 69
    0xba45940101c400704014202800c0624440500140600102000c2d10900c00244940c4268034500ca00000400c9500e810030f01c0642d05035259442c28880640e200143c10442035000c1c01080d00c21a501c040c084200340c000d43c80b0401207580154184201c00003102401002d42244c803041e8050701030407000038154035013407280390303044a0140c8030018415a07041045130404101014a503d01c01d200ca011004601030002502c0000c0c403070703610b10b203501c0c0300c07071411034105901c0c000a180503600344241c00c0300294010031620050b210407400044c140d21400001040903001d85065012114000140022b1104890710203040e42d4000102030000c860703401040341d840130115201c660040090020400140d40d2207100302c4608001c00d4030341942440642e2150203005a204d0100c04507045000908a030b58000d401131601d04024280141070068031510a61100c00c024900c5100300d9462402404000c440b1050300c0c026120710960509060310b940c00130350349481901c50a8804c07610600004d06840c0d040c0c908 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 525111250 1250 525110000 525110017
    0x1f06180b1314060409020f090a080105040203060c0d0f050411030c09011212090902160302070f030b1819080a090504020f0d0f1d1f0204080601120c0306050a051b 71
    0x11664964a040302402d400081c00c02c085501420402002441d0103c074000381c444100030341107181c1c1d01d01000c000c02c4408a05680300c0036423641002c0802c00507a03004100715134005d01c030405865840c0206400c84000b815202c08001a0350302d80000c3c0002d1107180540198029070503812104010b00500820500a41c24800c158043c1c2c0103d07400300010b04c514141903d080d0046c100000010f07220303040a401d0740c00c41500c10030074147c4410341009040c0c2c10016107008064000030445440c0c19615410500d08000b0210300001f481050441c1d50a0420009601285680500b075402503445113010700d100c0d0300508541c030008800b44804901803429100b00d4541414003080b191a0040204000b0080c1201d003581c0c400c04d6940c1e000d2031000392540d01785542107000d040050408498007039400e08210300781c1c40400904034410303c0188006407000508034152103082c00c018030b045415280041e448485508018035441c00e00060060071021074008601071024543c80f0f08001ca580055440c190081410 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 525112500 1250 525111250 525111277
    0x1050c0c0a080a1404030602070512160204051302120a1406070f0309020f09011d0f06210307020a03061a010e0102030307050a0c0f0b010513060302181f06180b 70
    0x1481c0061825001007480d40c0740350525030855128003130089084d411a0b40103544090700050604e04010341031001300d010344003044001e0b003404200b40c0c03a0469400c202c14024052556100401d50080b1901c810300180d940c003d0002015415800c00035403220700c001805c8032044c41018810b018514081003641c4038044a80c2e032156000070264048003e0100f10a05980000e00d2000030100750711040301c241e000e46650b002c1c480004c5c080d44c40c05054900014011400f000000013448155550b007184550350f011211038500b8403c064201003800c601c60904000d41c4000740d05000010000b403900f00c581d2041496462408444003480192603d8103e41c0b00c083c016041080020b400714042d10150035a2446e40c540790f140c0a14a54424446650380101600d211200800410183c60700c0385100c1c1d8802e40e03264051149600d03650100d400070000c0020340d0041c211446c00140c9104101d400e000400c0c09280126018540d07a040183c840c0c28200344880c1640d00007200800d540302c0d5403044134007002c1c00c40d4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 525113750 1250 525112500 525112513
    0x6050a24050d0f080c0708010c020d0e09060d1401150302010807020c09010306051305030c070f17071a0f0a0c030207060c05030f0307020304033c050a02040c030b0406030803010801050c0c 82
    0x19100d44507084400b504031444070040c400300c00130110400992000c0c0541030b000140324408440062f2030015400103020802c4111041c0c40341710785a81c14001d400103800e4407901520182850025280c200080d201295503190646042c421035442d014282124000e80f0703401084e85445404980341c0703141200c09c1e90405074813401000001e4456024a81c0a80010314461028078695034640c150307444020240420742c040b0100f48800e00c1c044100b40020700c2e407030110b0780810245001d516281c400c0c5110341c004640c2094100914a0079903022500100e014024a035590010b43c000680390310070800041d4010701c91a000402d20501801003e140c00350404011418001d105104c0c00071640b0040401007103001c2404000300151900b0505070000000e006140c04403880c2403141d0500381c4034000f04c401602000050707507000c0342c40840d030042201d4043c1d170045590750f40e4200580c090400c058201d50010729003200007090001c0c40740038505854181c402440180c8410756818464002c040c4011801d40120 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 525115000 1250 525113750 525113753
    0x114010e091008100213090b13051005090a0c03201b0705120d03050603031201090902121917070b010b07050a051e0d1706040f02040306050a24050d 65
    0x60399180d50141d40c20070302d01001502c44041c1c0382046810ba0701d04221540200e840d84a01d2a80f1001c10050544000100840d803c0d0a0000300d003403541b5542c007a03c0c81d030b884000c510b40040000c8201c019040c040c1548807141840040c01005250004a2000007442c00d02e484181183c43c0312411841c0c4c00420307146040c0408004c201540300d0725540c10890358030618200290540f15850600c481030188006481008501c003800341c155100103142c944a50400c102c640b800c2c22040102d5815036441c5000000d00c0003c900c0812103541c403107218a60984a10b010240419950500e001d5080e07224100b544903161200403800814041c4007401010500080c0c014400b442c006405004c00c980200f00712800d49400e9201c072030038241c070351805440610560a144003a504200b207130501207800e0b0315180200341d03001c0c0c2603003543c8040075040700e224070340f00e841202102085806581c050740d04101c003000681800105d850003490080444015210403801c0507040c0101c482d045011540098071051048686 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 525116250 1250 525115000 525115009
    0x90d390b0d0f1b020f190b07021609150b0702090610050706151a31051207030b0c030108070612090b0907030201090f29190806090114010e 61
    0x903070180e804003640c888141041d103440f8011640402c40c00a0b58101d5800440c1d0020f0a2014200110500313034840c18059190036008840503079201d4001c44e8100c0280c031800412401c0c0040c6000290000d0070240010a010956074805040c00e840340542205042d5101c803200b01a0144040103580205854001000fa0402e15064510f0050070301c0e08500d00301280c1e503130908807200d440c0c8810324184450000d00074007e40080441840090380d0000e4100015803501c405ca10007904242100842c44e00303130302c0c05109401c480000140038000c1045001c030f1641070130941da0703158a11040d24450504400f0440d0520703400101c03810783e0740702c1000c0c00015041000903945c08112103000d2201607a6050400c012401141e038290160101e60301a10035680b441c000103107482e2403500000c00140d00e1807010004948045191284c44c003041d00702402c12800c000580d6804e0141c12400c40d01100040500d03031200e40d0181c800b0344180d034100c0d410000c990b00d48220b141e80c468400f0155002c260301c00440411441e2 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 525117500 1250 525116250 525116257
    0x15050901030515030d080f150312090d080c0c0f060708090d020f030d02060a150308160305040e0403030f1a1e04020d020c030406030c031103131112011505040c020a140102090d390b 79
    0xa01804102a40334a6a2a004141e020958002054210390000442460501001104900700b02d907058113200c00e41c0c541f81c03124030038200301d01d02c14582e0100c0c42003151a54195852416002010755940e8258042c002c1e40310402113904941c074030b140c440d2541d0300c1d9a40d8013903201600d400c04641d0741003e002a4149141081103a009c1e000c0c41010b00c0001343d000c0c4002c44080c4940d00c656008a440286045c0303060680c2d880d540110121036000d070b0b10000c0c68503288802000b144485000000403d40440480d00030720400d034188050b00d0002034003080c509000070040084460307035502003015170101d0204a00319801d24240402c030700c00410115600300742034a91024814000d04c041c60080a1240002e5000e0b6800d41038543c2c5651602c504140c1800203201c100001d0009a4060000754000ca100a4560244890082c00c1c0c0030665801e045002c0c1c25410f90f014004050086c1000145c1d03401e001000c1d80784640340d00c854050065540d550000503c072801620080e482100400c0340c28071f52202100c0c1c1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 525118750 1250 525117500 525117517
    0x30403081309020d140f01081903120e1f0212010501030b010e04060e0105012a081b01050112140102120c09040e060c0304060615050901030515030d080f150312 70
    0x107140001255080c0c0d54402040c8000c0414030000c0c0020507410070b082d89540c000c14440d195240200108803104011030004131085020b50781845031a245e103015103a1061fa11141c900f05c5240c8803043d8111240003504550700c0e43da2900c5581c10008800c43c1000342e104240320310500c942d46100401a80d40690005a80340105040c461802c0e54500d010600300c400780da1013041c409410030010402560130451112842000d41c01c190582410384104421a11541d00003c0ca0b003500010100e40c4501d00448600c030340d0fa102c2000b8002e650b0346110740001034180030b40c00d44030300c0595030324024115014403c90b0300400035241c400709155038100c0c0d5400d46401c40d001c2c1580007901d83d007030095012000c0c81a20302c143c50220b141c94881c01c203403d100044807216086664010340f4061801c0d855900682a5200700d4400d1802196950f00d07903500a1a07143d6039004a0340502c40c1441198507950410b03440340c8203120b4a5080110350b924040b034905194a400c001907050b400201203c6d0411072079400821846 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 525120000 1250 525118750 525118777
    0x1803050105010608090d1d010c02032b021902091e0702030a0e18060d23071d013c2c070e060c030c0a030f170403090b0304050703150902010e030f03040308 68
    0x7509c141e0046401c0c01580f080094980340c1a036581070350301070090601d03200607456200402e1a880f10b030504d241c80c07400408000e8481c407003501c00204508121003540700c56441c1d90001c10400c2c20140c1020350baa400141d40d00c0082048090301c00f000d414105190b00940c03807c00004102c43d140c03d03042c00320b058032462058801010403116111884c110460903400c3ca2080701c01091100e1030001413106509943c40700715171010181c001008403480c8201a1000162803c0d02004150114000c2e04200103101c1140f041029499000080180c0d45860303c10b0807001910025580514142c65842003407801c903942e0011034000b00240003079040c003030b01600862a0328402c5a00d0031009803450780c80c1034070a4000303c00080041c000303100e14690210100341c040b801c144401059040540e00640300018500800c5500d52010000800f0700c00c00300b10010055401c801d2900100403400b213000c024200c10301060340400c904800361a014240020041c4600340104003071420142140e41e125207030303400b415460192 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 525121250 1250 525120000 525120017
    0x8012009090915100f0509010e0f0a180b15030a0210030c050705070f081011030a091509060515010503010806160908030c1b090601021b011803050105010608090d1d01 73
    0x101078011071140c010400c045070313100060726081d424148502c41c0d80003240038000704c41c01004400d4000340b0340782e00108400c42c040240e0340d91030074410003400324074803031900d440e5080b103448244032098403824020500903099130300f0210a41c0615690b0a0000f1009404c824401c000301c80d80391203980906c81e00c40750b900e411407406505455042c50204550011004642e9840040100c400d003002812600070a804c014411401080521031450200910030564640c036a080c02c01002400034107880481c070007140030485a5020b0524000811040754230400c4000d030342c0344403a0590302070404e4078100c514500041086944140608052801a25406e4280496290003148030282403014142c20f0001d03e00074080f49002c1c0200700440000020554002e100307110500050740d9002c282c201d034001c180c280c18140701104100403641c10b1800c402001066800b440040208030781908000d04844069903814203d80321100340710340360307210450208003140380c00260040000020485248005050600481 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 525122500 1250 525121250 525121273
    0x11e1113090f181109070c140705120109020d170c03160c05040e0c090702031303031701061419030902060304120809120f1309090507080120090909 65
    0x3002250032110481e40c0b61100581a62190700c42e00d4022080c4101c030311003540c115115030800b040c500c9000b6010301c200380b00003942e850058412100166100b00c85004000110b280280c0380d80c801d0045a225499813942822528014021000d00c0d035002040b54811001ca035541352410051002005030205d8184814031a8280501c0505419085034644103800da42c0c070f29082003604103070740225216074642400e4000813800014000c80002c4c0c1603c0c0040c4640715808180e00d5400340c105444e030b40700f411a001008055000703050320540c1040c4a040c03030169885510581e0800402c0500b01e1413660180005c0c203008903686c03c00328441c4601d09001078030140d10b401052065004031825140401d07511850495294400b030301030b85c401d42c010301810321543d0303031070041c00380340714002c070700a003140d0b01141003084003506001c0d94008000b00c440c10040f54646260190301c0700841e200b051030070352908000d100d00080059042e140341c040c3e03038802481c09a1040070441e410001802100403445998890507 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 525123750 1250 525122500 525122527
    0x7060c020a030b1003030e04110a0e0307050301151d0c09210604200907020615040e030703021501090219080c090a030b010f0b120703050403020f0d1709011e11 70
    0x11301032034941594103002800c60170050850b403145000345014a10300705141120040d003c083c1c625241091400c0402042d5082c0080c0c030700758581e04030640c0b55103426481008484410f03007280840360502d548001c02c0031050b4000c40342e003100721280100d1031401c100840722032a00704e00400c040f0740074181c4860148940c00e4110318010b4100c40440b101d40030840d051750300740c058980c450034400d400c40c1d500b100c500d00700314000d40f82d00c030181c0b81c515090510810420166600e400210801111301c1c21242c60384001d040017540e072038840c17146075140c10085001180304580e6008031000b1150354550f482100c60796000460f0048070081c2079041d024021b10540c0001d641d48041d9400a50041000f8011541404448015070400e580b010196010400441c91043c4000840070741c040d15500340080da40c1c1e5141001d80c00d2800391443e00103140941100c0c15075450b000000e404a01d092081003000540d1524296401c03035650400d00c6012000342152a043c503490f40c3c10016460302051196402c060700d104100 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 525125000 1250 525123750 525123773
    0xf030507140d0e06070c051908060c0d0c0c08030c13090e10390c02030f01020403060b090910050601120e0a050c0a03080703080a0b1f090503060907060c020a03 70
    0x3035429070420702403602010f0344580e05194004048410700d01e8002c50f42d640040900b010311038907004d03403050f240e000c0c1d03500001c02400c0c008003101401da07600d900c2c020020041e2548074207100c0403068074002c5030254140c42030702c00d00354a661192200f0301c0c6854107544c00486811580d0301c0504220240d0b00820b10744060f02a1800b0b5203c01c00c000c0c58180c111540d1714065405403141031000086c00740070320800b000300c400c00030702102c1541d01306044800d81080440e01140c035040b02079010705c14180400040503055000b0b000322801010100700610340401000010441900c0d500095840000e050100c49d281d0303480141c22200506080c858140a000d141d42070307624400303002c540c581205284009000003801440d0440b4000c0390200d40700d0781540e56460781401040342c0036081100d802c00144045500d980000d5080500511410105c22040980f11620010186031000502c80600001d020704000402074002c2d10710f04041d040c8903081500032682c504c03040300141d81c404420b2100101040715420013 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 525126250 1250 525125000 525125033
    0x61a0a0608090d0503191a040908070c080a02060a08070924081303091503060905040c05181006110307140c0108010602030403020102030414040f0e0303061206060a030f030507 77
    0x2684071900c2d00e001d03002d00b070619014a40d014400100100700e810006202d080489502e20240011038286591080c0005140380014036003040c40c000ca084140300b1950f010b810041d2180780d911160507210050f0b1521040001002504000184050f000250059900b541e001180d0b14081c00a00d984415104413556000040c1c042c01103c40382103908245d20031034590380035003e2903e0700c40000c055030b401050720106103c1c101d5003d0f202c4404521161007a001030004152a55003030040741080d0904500c1954188039051044100e0340314a07820000c803503007045c850705810102d075550514007502a100c600700000984c405010801c131442c0000c45a07c03104012000540041005004000001d000c0d140d060304000305541c02404208010b070703070010445043d64008640101c208590b580071801a01c100c40109100c0e900b0714003240710b0041c00002030b61103141c040303c02c0b02c00e020141414a440e02d40907150b41750032807000305060000c2080000100002442460001c2c90b007810303501c510788102c244440c0d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 525127500 1250 525126250 525126257
    0x60b0f09040f3b0304030f05030c0714040507020c09060402030a09020618040c05040321030204050310050603011802090408090d0b070e0f100f0f0203090d052b0903061a0a06 76
    0x2400150300540321051602c5510351076040e00320420340d01540d85c0c020341c48004c0c0180c2d40c480036041089002d00955486a9188044a414503180c005000c2c0c4083c940070041e0041d0f10300f6001900161001030907184101e00944428001d0b19000e044c840a03510003006461071944540000005071200304c01010355090f000c4101e11051840301c20081543c8d20b507580d500c03c010b014041030001c50f82d68001d1513514442c200c025401071003100420b4003c4d01550303001d1035040c0541c54400400e44d54940195120f0b007804ca0080100d030440082c1030b801c5411b1030038003070740001c0410005000201e0050080030303942d5004040c40c0700c2900c90ba0b200b0000002c12119440040c0680c00c2e1b08241d820b000c040d12140d0041203881500d010000000200201662f181d00b4003003011a80c0c5141a95009000715400c0b204050482c1d07600c1c03c0503051584d40d81059488000640c0d410513422400442d802103441542030583d074842191910b55100c40d4050b01060f603105e0310f00c15018076500069941d02d42110000d2801d0384 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 525128750 1250 525127500 525127541
    0xf140f0306030f06010b1c11070f12020d170910320402060a0e0111070f05011805030a021323011d07080105100207090203151003060b0f09040f 63
    0x200b03040c103101102d80c0898250380160010700000207400c05a52410345100380000c14a020205c085010340049440301c80c00e0700c03000070850280503808455500c494041c5003d201150100e14049135a0794494451400144182083c9034070110754001aa8001004008654031105c00511000865560400c1e90810b60303200e012031000da40d6800501c40c0700045200020700075103456004030364603102c0d03102443c08000503911200c40310b80c01900d001001080100844105e9a02d5142c1e00300046500d000e50750218101c00d15011810203565904015140c0141c05005080d90550034410710081900a8450b00c2c3d460341d80503c00b03060700100380000d50302c1901c2c648d4010b51419015070001c1c1036001350341c0025040c500402950300e8018026a0443e07105590046040b03030345c0c81080341008080c1d0462440c9900000502c404001003140f000384e15001195003950f0301d1034034802074040f90400c2c030801d040a6001d2000e4a0000100c0010301400b102c05000824030a40cc6c1400c2406c844401502e15400d00444 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 525130000 1250 525128750 525128761
    0x15030309170705191503140109110d050405010203070216030807080306030a120f1202070c030201050d0e0303090d0f021519090209190524120c09070e0301050a05010e070f140f03 78
    0x140041030450020f0701b000c0001910403c00890000c80c14007032403024580350000d0941015080d01142c0c038940c0f00d50381c108000d04081c6003543c040d62054605000602c12800f40d40b41011890001c14100c030b03400074034145808102e036a40d441a4200501d0a54140170f43c1d21400c2c0891289104490301050359078403e6181075518602a0580d04c459140041c0541305014020000d80c8079081e03c426280c0900b80700d6120009001104060800c019500348580404410311a0b94800000c100144104a40b0795101c41c4600800807030b03481c0c0c003402181d0070445007400482c00d4401c2201c00640703402c001c014042045400c94000c03601c42d8a0036503804101000101800360403001c5480b4241e000711110078000c0c0c120454881d40c1c5a0405d00d1b8644911941e00c00c8a1124004030400c1816400180981103000e03d180514002c0d10b0850744029042c0a5400c041c0000c00c020b41c5407140d079040e103501c0c4450100c0f40d102e41c0340458640040034240814803c0540c907948803c04030310090891140c1c8068030325547d2505 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 525131250 1250 525130000 525130019
    0x30f030405060a050402060d0e070504020d1a0405310b0f0610021204031e020406060c050111041511210408071403060408070f0b0403030b01031503030917070519 71
    0x9140a42003844c200912005a40301001c4440c9070348915004161413404005142c1048496400706900501c0011658400601508284404041c400c986400c4516101c18801950030846038400a40c401245a80c104041c00c1c903400c00303950301840b510440d2000e0b556408001041a145189030034880300800c50189042c0c4103001e440d00d1540b000c0c1000510380c44c03074034101d1f000390f010080581c140c030b0800141e1803441002052069400070300c1806412780d142c002038030129660034151803d5092408056050710400202d40441e207001400da00074242000c01105ca0781c2d100c0c070650b4054069940e110b11210240b07641d01c00b0182c0080b01490750b951a04040320b150022540c0510340d01240900f2000c06aa404210700d40c0c1b20740c00c00310141e5a00ea8900d00070000c544286401450100e100e001c2c48103155040e40030f046030180030380741000104e40e281400300220407075110050014000e031901313000222030304029540c0301030b010003280d4095486100007080d16881401c40c8844d0240d80100f042003600 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 525132500 1250 525131250 525131263
    0xb0a0908012a0f140d02120106211d07230d110d0515040b1012021e0a05041406150a050d0207020d0203010f090c1d040f0311030f030405 60
    0x602c1c4180240d40da00400a5420a69018584810f004a14540215841c016010308100344240e01d50386540c0c0d051340d00080020342004480c03542203580c490000c1260350040150221060700c40285480415000030000f02420702e0b41074501c480f42907141c00100d40c010401c4000054107000c1450040000300040c81c240050314081c48034420a00b540c41e000100c2c1d4540890142d58105a548880c0040c0c1810001e20b0107114000c00001c03076000c2400c200600030712840f518007d4170a070a01c00805036807045030340c118001c1c0c0034000c0d61040c050841c24880b00c442c00e0241c2001200a0050400150340d040000c1c1140d0043c610040c03805002d40401155141a8400100847d4198261801e010052a0007495802429100e1210a40c0068a0002c0d56144030701074180130350042c001c0c4290130a41c18040040d0070708440c115400d00055001164103840551803c07c0758041c1400ea142c107035141d40303840c0c0c09404030301c50a60070300613a01901c40302c1c99030a10040400f8121040c40c580e030f0382040d1a200d8902003 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 525133750 1250 525132500 525132521
    0xd050604050613030507120504050310020301081939181401030b071202130b13060906120f1407053601200304090e0105010504270501060b0a090801 65
    0x440a0306140040c0d08a400d54604031f820056036407004174100d10a4500384590b03000b103a49132207a130400390303150822138000710305035034543c01075038403010044401e4480308840100080941d250500c0c190003110700411000710740d80001070b4500c90030f00f4890000d0140d02c2c254000e503004136001c602520490f0014014056100810007100d2003070740c955140c1500c0a240a00b8942c10450b1901d110909821141c06440200d2100000c0700940f5a4030b20f641d005a512000d44501140030080001451900500c03445e0f08888082d21041da401314503200301c42c010100010004206c0c0c0e0f4071060313203002400008001d03202d0303885a00e9091391000300c41c0c80d52942c07485445002c140031445124200c43d000cac0840c3e100c00020002e0801704410070390400d0415070a41d101c09201c0d840e00c804200003582000c143c101d04944079042c2c0007000642d80b0385e020f1101742ca150007411000d401c1d5600d4103910051200c4060100d1500a40001807161b41313402a89103507a11420008000070220407050180c65030a104010030308 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 525135000 1250 525133750 525133771
    0x2040e1b0a081e0f03120105030c040e100902010c0b070e0909070f15020f2b080603060c0f0c01020a0504091107050c0f1207090c0306051009090c030b0d0506040506 72
    0x5525294101d903507054183c44007094140908110071500c1c1d403c20096991403040000c1c3da0703e4030000800011112400d1241c544030740305400040205090071321420842079455409044009000c211030800f1f8030503000224100070406245e84040368484503010302558150380c8540d8aa80e0176000c110100001500b529104e4022038004c202503050f0310b030808202d48265059141c8060010b4080e800c0c00782d0b401c040c01c15401800210902450401075444052581c9a4025155800c40b0f0b02154182c408071407468055002d0804038140d141844050828803405228403450031040018644c2a40c0142112002080000c9024400410701d401080c13030008500d41910f0a002d8142c850696401405201034080c01c88117000d2a11610b840c0c04041c1e140f40c07020100c8221540d00c0d21503600a05039030411a000030324151001c9010b1070304e6000881000307000d54880038164203000c800300042c0940c69525007415503a6401000b0364450702200001030780110050b10161030130341801810498007c05d402d01c0b0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 525136250 1250 525135000 525135019
    0x3060106090f140414040b01180207020a031e050d03090c05060703170a020c0d20060610030507031b020c0a0f061403180f0601030c0608100311040902040e1b 69
    0x60031000c0b03280e50072192000c034455000312500b00410018850403c0d1541024402c004100a001c07851303122034105c0710071030f5615400c1964071810500301c3c010755000a500050705a01000410016240e0540c6801c51149400c28004d50b5901c041c1f8082d03001150f60701103601c81001c07500b0304c00b4840003640280f000307403a003038038115591350010008100c080000340480c00c0207010807010002d65050350300d1160303100212041c2c0b01401001800d01a6424a40c1401c84907440f1800c00c048404510107000388006468400c81e0406810240c002d8040101001c041664500c03d8405c00701d80311112807402e40d5980c02406500d009030041c0504169641c004034503214450408010450307200c40781507182c520404a55860340c607070440100000701400000080d520894451680000020501d181200c1c42003594070696a661241919580310031503406a10300340e400c4080001c1200030b0200c50070032100800001d01c03130040342d0000e0111020402040c8065028500380d001020400c1e1440c0503600d02211040ba4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 525137500 1250 525136250 525136259
    0x1503101e150c05010b060a02030d0509011109130e0a030c0204050f09060612070338010b070609051e0105151f030209012001020a080610090510050d02030a06050306010609 75
    0x201c05001081c1400c00900a2450040c480300b03501208541c2030092800c0d40d2102c8803103000350340e07821224070040a85c1ca410046121001c0c144252042c035188031682ca41040d0b04c0360304114a03156a208031203156511003000201d9003a0502c44040c0c890700c65201c90401c40e00d5401480704903074008201c51103500c4411f00380a0307500c40c00910268484812290182c1141240c0500b5080c003045520040001000c200c0b80396901e1131820804400c03807600701e400c4020004025069034800d40c04e00c580d400c01030b0100300030b0001c02e40765005100028080c2c3d00b1148011706040c00d0071603051f9284070540303459548606005031010740d0b0481400078941140e140c8108000e45040b624140901903260040c9940010210410390103400b0404d4061038510056040c4442516414040d5020f40421000036038030100040d158134000c48010074540640c2d40740c6403400c0c1031805026804010740504428001305000c04840407405000039803046c684010089880751070141032501e8080c06800c09000c4c840c8901e024803 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 525138750 1250 525137500 525137519
    0xb18010e090c09010207031a0406140f0402150f07030f030501090e03030109050a0e0706030e0d0516060905010b06070606243c0c0201020c0a050a050405061503101e 72
    0x2504284040b2859076a40c840d440107070328040079640003d040080030b40c1400a1444641c00052007640187c0042c400c95000300c0160f000800c1c1110b50400c8403208001150140c20081c0398891b42541010385185400c0514810050b0340d00041c0d006c900042080c00d5000005505025180c0100b1070024180704031810300d410f10751640014020009001d5844000440c1140d9980050054011000981c0c2c003082d101d101c028007070000f4004591262080e03084001000b4800d40483d40c002400c0c0758a1843e040e620340d80d07180540300b6004103071460f64940c0f12004655a41000a000c0f05100d031100043e0b280c070702403403d68202d40c00305014501b0f190b04d0b80c010042ca41c0014031406000c0c0b141003000220515082d40c04011202c882180203a10392141581c9d40340c54100121403480d6000f41c00701c03222001c02c0010844080220b002c2d17150402c21b0f07207500304002d08180e00030781d8010100404000d092004005c00307009035001240d4000703000700c03400d0303040002c261284000200702841c0014480071700e09084010 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 525140000 1250 525138750 525138769
    0x121603020d0503041a1e13061211030c0904060807050d02010507060e100c081602031804090b09072c06090916030c0f05010c050c040c09080303010b18010e 68
    0x60700030820031448a080240c244201c0340a800481c0002c2a0702c1550480610745410100340380a1060100d065982c0300c044400c02e980c016459808903020150810404075400300007101c0000340700313844a0451050340c52031000795114080800c0102d46440610040005584881d4848811500001f070700b40716a440f14511035921070b4080c03c1c070903a104124640040204240e00e01101c5601844100305030051103500800900c0200e540e4124443d1030f10341882a10141c098400005640f0421041e00310f420058640400c400340100000340c501e015460ba120342020468921580da00070749401d00c0044141ca810380e01e0150b800e200002440c001d045508100d040191105206403d00d400049107000104154501001c80000c010402603030b9140482080d0250300a60400c40080c00c2c001c2443e52081c010f078004c1e01d0300800103101009280060000a003c44107040c0104501200c0200e40c10004100940c02003440c2e440180d42c03a0440003e42c8107075060461218100100b0103800080c554814140 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 525141250 1250 525140000 525140003
    0x12011e0905090d0c02150c0303070807111c0e0a0b070201110a0f020904080403060c0c060e0f030d0c0915120b09241c03030504020f03010e031210030804080606121603 73
    0x5134290030703940005950035180384882c1882501c0090092400e101c044007030350107403100d41c4441000703807907000f020744841140070400c0d5920b60003d04940405900780c0c040c2036055059080010584400c000402e00d00940d68200001040b000144081103582c0f041007440c040e0301c1d00000c0c040c42c00b80c540d01d25111a0704043d0282c441d258040c0800d0500c10203d0446004590141040043c403451380c02c054248109104156599444c00c3c1800001140211b0b40540d003800e808051450869030306c041d48014898000c010b81009010740340031030285002007075200a5842600d800c00c00d00d00840840b0140c40211507494010100d6500348440302800450441c2107400e00280d110100710f501000c81c0100040c46586981c50034484210300070b06800d40c1c80300d0700031402542d80a214071024401d043c03d03201415082c07010b50380b040107842c060511203060560080480e03544446450b50f80c5e1500140ca07002904140519001281401820b103401070b00c00c4035000078100a05114500660001d080c2c0d100fa110 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 525142500 1250 525141250 525141257
    0x30106050f0a14070f020a092013030209130b1b0403060f09021e0301060902070b07080c0408070303031406030d1e171005030d050c0a030e030312011e0905090d 70
    0x1d0051001e8000c80782050802e40f9610041e03201d1107182041c06a910b001e00782a40100000180490011018002c0042c045640748510302d132a1421070018800b54084201602100110500440103a40300303c120390103242001c00c004510384090416403a800380140608030071070000703488071190401e41002d95007221342141000544807411040b02c0040d00c01064000e602202210a002d0480c0d5110b520406940781a4002c0000684640d21841244242c18001e0000b8083c440001c149601c5044119071249040c0d8190781490f5641000b1441c06c181604102c2c0825110041c451004085e020100d83c0b148044005000c0c0840c0c04030060610003410b540725041e4441d110407160301c6401010543d8403429468245000c80c60484190450882c1d1070203401d209004560306881c0c0300b0300c644180c4500079410070181c421461503540c1510000711890344650940000c0c80030003148490300140c2c90081c025001c484100104950804a40003560780203040b95500e09401d02100307220001b5880001002402e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 525143750 1250 525142500 525142507
    0x2010509161404021b10061d010b030f091e0a11011704060e070308070c08160e130312090b180f060604020f0c0d0c0204060b04060f20011103040c0b030106050f 70
    0x3000031702c50318002041c10b650f214400103d50303820804d600c10001c0b10035200714811952a118450910100d0a11071071101c21014404036040910304071207144c0285404c8220703a1801041c80150401d80d1550220446c0c50700603a0780d030014408030043c0c05040010900e8070041c00402c940075045803200c00340000e04660381d5515544d03800e0320704110f500051504072641c90740318038048c580210540c1d0940622103080c0103d1002c522941004500082522110302d241c081c6a52546018055014031401c02da04201403001072031f8140712148070340f0340040c0c003420304952145460798800c08803000700f082400c40d80d84101c100c1070b101c10004c2000e0340c01038421500076945000c4210750448a000d0111015002d00841c0018003020342c004050340c0d0000e10994060003c1c03035884810f4019400745104800c0800c17003030346844440c40d00c0f03002c4004804c1110240040c002518a90031821a144076080c2042c40307400209100034041a000340f007004011400e65545190b0406400808500030346181990f03803034021 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 525145000 1250 525143750 525143767
    0x902060304060c030e12180901030c03060c18080606090f060112050c130612050108070608151f020309030c030601290409050a0504030e040c0e0d02060706020a0201050916140402 78
    0x5e401c040000c42240b01215282c0340301d4401104103601881525000041d20000c6120a0400c1e91394035041780c0d0025032505c40c09245840380b001500d04040118208440910a110007040f511000390152510400401207850f000060120320000942039440f030f02004401c118590380d201d400c090140712400c4010443c3c2e25080780601c00b9000e4000c0c100c2c80e002c0100d40205034250301c010f41c1180340c2c440030000e10151341d07240400394480e043c40c001c0c03600081014001805280c0c0c030111510301c0b10000b6010181103000c00703103030304818100c0c1140c00d40142c00006a4000c145401c00100018030b00440103170510394034000300e030360038820000481009154014040402100d288003607034024852411305002e1458030002c044028401240c1c214080395030900610040e081500c240500e030b4240d61100202401280304200350044d801c10100e80c054810031442c00045c072580041c10004032160004a01800c00c28880343c180140d441280614108000f020441c0c0c4e0644100300024000940d40180e130340680 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 525146250 1250 525145000 525145007
    0x6030201020d020c0906150f0712020d080112172115060405031009020d1505072705040509073b041101050304080c01090c05010f0f0207140103150915090902060304060c 74
    0x4098051009070008102c2c5002d011458ac03030010200304550907601201201d10064400030428002e14440880342d6034801c001410130040d020032010850384107410800c01001103030102480102042e00710301000203210301e000c14031000740780710541210000d0402d824100804e95078041121420541603da00400040d9180c50024018642d001811010b114012042110107000241e03010340c0041c100444124038494801d803c0046000d1111144c1c510918141c200405040007800c030041c1402001e5000030b4444642e000c40c0b482046260880ea01384d406c00c0c0c0c10035002c0da4050b029002c2450140100b100050386501e030780d9022102420403c3d103945803810104054024200c040d400ca40c40c003950700003403041c251307a48811106c0903603a03406070410381403088441c8000600b801c070160b0302c285000e200340d00320404141e121420615001a001c4060001d00b003180b00300307500900c4240d0341c2c4c61094a60034070143d600b5025000e0b1041c24000d40040703902140e40d0340302c0240041c1940c0c0d910104041800e10 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 525147500 1250 525146250 525146257
    0xa0e04150b0d0506152802030409092301090c230d110301050c13050f150a0f0315050108010b09030a140309120a0c05060714030301030606030201020d020c090615 71
    0x100c0e00074103502d07191002c0d0a5001848107644852003401d20303500c0c56402c0c0454070110303075070303a40702400702c96a07590706d408800442c5131340349021419070000b404081801207192040e840c00c94082c0c04180c03401500c0c0700555074018074031005020b550b4189402180481c80301d076080c4085807148100c100c0e01a030040400303021400341d034000c0b6503c10307104070655045c030107418040d1582e1902203000b0006920382000d500214030a0004043c17180c0c088000030086450004100d072140c06002d02082c03015a00c0341d4443c001c503030022451201103000c100318104615414070924540070242c14580014a0a00d0000307400c0b02c43c14032800102500000310003c8584007032040302d01303a56201d400440821002402d460702ca400a0b50418092072070703241100c841100c0001c08c01c0b0119003004a0b04017050a180a101081e406908143c55080032000d071411745020400055000794004c100006007282548002401c00050140d00800c550280703280040a5480355840c5410000031109000040d00d2100c0001c404d02 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 525148750 1250 525147500 525147509
    0x2d0c0403051c120b03060601030f02160c080f0609071206020c0106090b04111606180f0b040b0a36170c011103130803041e030201090510020a0e0415 65
    0x2000740e844001101d89000548070846a102c01c1c041a1507015540212041104c2d400c1d4580c0c82039000c21082d50295124609010310030700058901030364031035004042284240c040f5062288050700f08040c440502082d0900007800000d0404e40c10490f040d1a510495405040e00c0c00568101030010007025904483c103084000000340501c0b0303030340c0701d0000017400710070f02d4140110304028010340030800d01400c07520340c000d04050180703500085803a85401000c9641c80c80964510540c8034101103070314072740000e5071b1070710941000340d0603c0d26250054007000d0241241180034148003044440e40706200d0421000410909100401c62000b0004145520f460401034408800403190305d0807083d141c0010025010345000a000d0403665903100016840111070091811010440420010b00000c000750303001400758078104605540c070074101008521101c81203026170343d24000101040030034000d1003a04c10442c1c1c0300318204100e495000d02041c0180440603c120381d5075800f00269083e03545c6820140 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 525150000 1250 525148750 525148753
    0xd1a0409050601050a090603080d020a03140115031103042003030409020c0a020a05030703120507111002010c030e0d12050a200d05010e061503090a080d020d052d0c040305 75
    0xc0c001420007980300c620038000c05002c0d504001c2c02044035401402000b04884d4015401440d100c010744c0600002d40220701240d041544801f0441580415020440d01070300e030110601310444c032009000350132a92140d03d001d09a403414403c2002040c0314080c28086e86c030850012060f0344c5480c034002400c0d803243e0382003010600c0c40800d651520840005254640d40d01c03e0b15031791101522030342015540c011600c4020040d10880c0000c40c2e015100320040c10000740b02c1c46c00302e00e039101964001140f8136040084840180c0d0f480400042c2e42da4180190080d2108032406001d04003075140c0c00031b080f00389040100310b480e07071201b002c030b00750380d032168000b034085995240103034803038501403075030081c590702c0011100c7c807840c1802d001140d0381ca055001da034007515000301032445030590003208036603a400003050b040140c000e0440800c0810314420090110300280000142d403941401d024208652001d4030f6411404076201070790600601044c844001c50300300d03d19000640c0d5451700d02e041144074940008105 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 525151250 1250 525150000 525150011
    0xb0d0b010f0509090102132904060e0130020a020f0d050307080106030506100e12150a0609050f0606090a181b0806030c0f010903080c0c0301060b0309030d1a04 70
    0xc1903998801ca03030030342c1d0702100c03c03003410f480c0d00201500303070700400e00812544855644200011a8400400e6040c07559090068558040c03402c626071254200c0d50180000c2044183d0a00a80d070f400741076480c0301d03c040d50802c0717044040400070801c03900081c2038100707000341c2c001150005140204402000040c000302101c0d06a8a00c09008241d0381041c0c42c0440458185000468194003e0203114807810340a8207001c401507203441e0445800005110194208000900815440c0c0c000d0140e041c4c40c1d01c40f11203011060a11780940310448115a0103807420629080c180102400034403241500f100741191315580700e021000010713402601e41e0b0300c2201240e0481d84804400f0301260003101d2690322154481c401e8200b07018040c0c80c0e00300c003200c000fa4540c010200780b00c01490220070301821110180341401c041e5440b90742e04681540840c120b070000e584100541c42e810b180900035440034000d8840e00a085080107408540e90380181280e0341085c0b40c540c1601103030340c404110500051b540c014001d001 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 525152500 1250 525151250 525151259
    0xf07020d0609050c010f02120a050c030c072301140d0e0303070f0e0d050a030f0e040f14160c060506060909040b071d151b0d080a0f05190b0d0b01 64
    0x6291181080301c840c010f4480f42c114a60040c0041c0300805925005041144640010423032a5408011040c080c4003051201f901000010000fa060f145540d1005100c1541803c0b1642d03044180500b025111a8071001c1700703071850b40e00510040e42001c80c00e400c0b9803100300300803182000c0c0c01e03400200d00340b80c072001c4104012a94014081009124181c13103408051000c0c1040c80840d01c1540805455a40841081d40c0024414a400c0100001500c1d04048600c906800a800d0f100305060001c44c940d181d141a032200f082450305c681d0043c01283c03024070408007020f03024000042500c006406595240001000c0c0c1d1030700421103100810050041486240920b07204103d070405448400002d000d92802d441d200804000c0c4008509004245089140c102490319540341d200484136102c1c04c000d800e011301002d00811002600c0e60031519a4102c034a071854084080714910882d0040e418142000c5c0302a24050920402091210000200c9ca4840280c08034006600c0701074005c0944040100004 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 525153750 1250 525152500 525152513
    0x507030203011e18020a050f0409021e030f01020a02120d090606060504140306010e1623030106110102030105060a05160b010b0c100b0a171c02060a0506031f020f07020d 74
    0x2529100350103c104018240300e541813105044108000b034102101043c20b018500e8504002c0c00c3c07114000704041045452540030825003134100c1d0745c043c1420301300d040004240c642400719070021181c14008600301344001e000203541d601c130b449071170002c07540c00102e0b2300d1805100d03000941c038a070b0081c0c0b0a100556075990018100d074820b204421100c41c0c0203906c078466260104020b030480d540a004420140c231211100040b9010349061501804580d80000c1e41c6518080c03600c030803c040c0f0550749910307580b50000181c2445d1032260000c520303074410401484641c0d64007003994107184184c60100c0e2242c2618105118421704100e01070180e0015500000340c00705400e004040808651080d100005c004000b100150703101001b42c40d504c1080d0600a00419002d090032003c4206054203c921708013899a51020010a00c400e04005801c1602002000b4000d07006081c0c0004c8154028085004070780300b400900b0b000179440400d4550006415880b109100d82540e11040d00103142889490191030b240303 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 525155000 1250 525153750 525153791
    0xa0501140a0b0301090b0604050624090301050603120301033903050c030d08040215041203030203040c0e0c180f060a090305101401060e0105070c090c180f05060304050703020301 78
    0x8845460030b248030801c80f41810b0045142d000d50003251000d6540720007081101601004180741d400003903c01d010210302c02819610b00c100748a442c4000d0ba03600d0208145802e40b0f44c000d080030b000b98003200c1c001e170750707100801c0441e81100d07008010007502503501c03a0882c81c100d102c0002c10f07401170192074141e501c1a0004001108881c4030707208030b43c0c0f11919070b800e0544030365401c501940030030b039003100143c05428605581c541c5070b44036020080c5082d03100d0000c0d0402c25a100000e0300000e5001c400c0204200161654802800503a580c0e07508914040401411a01c5144080c0c07081250461010036284c41d1540c00e9040301c000109910748940c0c500c2c10060030001c09100132f845a2082c403e500100006c140f2500e02b1015041c01142d070700f81c0c00c000081c0c0d01c014010344510f0400000b0003001c4041041c0c000700c600604810035020861a002c0c180c02081300c00e400120b40c840395080b820800204800e10440000c55805407030103503c0e075a031070828031f080000d2030340081c0d007550030300390781042c07412000042 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 525156250 1250 525155000 525155011
    0xf050a08030313111002150a150306111224040b1c020307051c17031e0c0f040f0305010c1103090120011109150c10090f0c030309050102011a090114030a050114 70
    0x1004c040d41c5000c282c5040c0d4191074558842d07602c4d0700d00d02b44003284080d0080d00900e076960454514280310304201050060040301c501541a40182000200c0d0b203412060801c1050221402c0c40564005000510310200c441e10140078080c0520680701151070910004004040c024841822404000c40c1401041c200000c01c50302441d4048034100c0c001c4800d03041c1c0b80203130501828008543c505000308054900b0203000314003c0310b01405901d54002e5440020000f40c0504450500164034500d030042c291080c00c0c11041c207109800308100d04001e4008159116640300f4603040d074200741c040c4400400c2004c0303103a641019500701079020004100303031030007802040019035903030201060001d2080c1050007880100d200d560400d0075000010941c0b90002b1720070318010a20240640410381e111074030048540d00c220086030401404210541c2c081c400d26607121b030029001d0150004801c0001c03000001400741040d045c80d01c20f8803a900b520100200c40b92598400e00821011800440f540850b810844d075 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 525157500 1250 525156250 525156283
    0x6090209120105010b030c0304140106031104050f04020d1e0203100504030f050a0210020a030e1b1005210403020a0c1d0a0606050912031c060f050a08030313111002 72
    0x40c88000080c1440b0f52412a02c64407203240c00d5807604410b05280746e1010303000755480081010307000d0a8010a2207184010341c410600c54410000c2c89040c0b20a07a000203003101c0c0142d0701c1004000250301c03a2310032442d105d41e002d0240340340001c3d14020321402104403100a5054803940201328490442503105a01881c00781e1144500d04070340b2034049645214559401c40141c10a4080d002d1940c0c0b107401801c040c100c14100402d40c505141d4a0602c2e110388001c9400d00f1b154044460b9609003440076000110b5115454241e01d40000181c441d000c201001c5210b202c80d180700b800040030325200340980d101895221410140d09660b40c600c111745030703c4481040c0700113041440440c14281140c42014200c60b095102c46040400341c50820554144100c0c9021680c0010084500811080c0b0451a1b600700135001c0058224204200107001114135004075005005c2c0c0304c2300f40004400081940d51007101c021046050b11081e10301409a038054840c02904465004000845c054021440d151688200c84 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 525158750 1250 525157500 525157519
    0x1050105060a0f050a020703020607060f06052d0a09060f060f02030a1b02130606050406110a050309091306060b0a080717070c1a013015020c1006090209 67
    0x40000e1841402c209074040350f0711010300481c1d03034003c00103070900b40c00c4c1b070051f12901540c0740c001c42c000e0360012070300f220040e03036440d4010102c0b0035a04c03500300034160a43c0c981110250040c81600c1c041400255889249100700c285109036540c0c50100024001881d41841850b54501c0140140307030890142a01291100c140148982c0c4000301b66806142c0d10780e140c060480344914000045180150140c0e042001020102d551104c03078010700000700500e0761000c4c0d5980c6400c10060141d601c2001505141d0415644900450b070000150340c890a002c03a46580340e51a1308052007004111102e000f0320b010f040280000740440040060318180141e81c0307a0080c00ea03036a68044626080b1245000404440800840e00c2d1754030640742d17001c440b403003044544400400309000c1401d41c03e00768400b4100d0010b400d41482e04000283c0c0804842c8055459100300c803420f41c0d81c0200f011030407007079040142d9004c588250f80d40410810503103d0080d4002c20400300341c0300c80c07460019511682589000d039170b099 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 525160000 1250 525158750 525158759
    0xa06030e0c33030f0412020a14070618030203120a0c0606060306050109090213030b2211030c06120a090606030f0b040c080f0c0904050115140a24030b13020a11010501 73
    0x140101c80c410841c88440e130a4582c2c40d9600d510001111004a800314400d0000d00380018152808241c50003071450020001946400d40c014100160192841d844108010082005032070010301054001955048951107074403480003101d02003080603010300580c0c2042c100150301609940004151442030360381301203850b04c0300c40c840140c2c4545404104d16045200080002c80c1c0c0c08440c0300c0e00038540000740c0d4101c0c2e0702440d21082c210752104c000c3d0799400c40003407500080e2030100003c07852080c05961081c10041d51310403241e2580001009800515101d604920812071a80d00c400c001d15032107a1821040c00c090b040140039040c0c116001c482022161a001c522410006140401600003600a08013400c140b0240400000e0260003141c8664941112403d0030500c1c56246010700341445644108a004500700005c42101d5448441100d8441d036028544140c0b04041c035100c01e44c1400c000c07030000410f00104008158190720400c14502c08115150701c00e034849103449408036207400034080c0e41d896 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 525161250 1250 525160000 525160099
    0x3100915080d080604020906120109060e09071203090e070e010305150a1a07080a020d02010b041a01050a02101b0201060b0a2c0405041118060a06030e0c 67
    0x398059010036901c0b1080451409119020040d032201c0043d2000d030400c124800072861a812120400030f0300e042c66001807150000d41e200d400f0040145010f004214142050515245c086ea401018441040d110b501c00c185130103418008000d00f02175601e030032146043c40004004154504410740020b0034040410b0000c0d078000420558010b008000f8001545010b075803c440b00a1803040f070208480c18080308001c1000030004e0008182c05070003404130b40c1001d00000b0f086070903143d642c91069142058607218482885001080c4200038241b0595a1144032003d1345003403110802580c03da0b00b051f20f80c440040403042070281c905032a40091047e9529403140100368040c40c8100000102c180d11100700c0c1c0b800200b032031202a07002000c601250070510707010a050328021942a944810f581500d0305443c100030701c400032100c030143c2c1c4240490030b1000025503108014880c4804064503101c42c5605a0001d101220702681d00130301c44102d401d8000c004080c00196101010b0034151091318403802c4001 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 525162500 1250 525161250 525161291
    0x307082512030f0b04180302070e04120c0f060c020f121e0715050109021b0a0c0608060402090405011409011508010302061b01090624060c15090503031009 68
    0x1d0240c1c1c01c020150000038110014400041d001076983c0d1203201d100f015407114401e1042d000c2100c030940c3d08010150074068030f0100d0340c0d40700d4a0141305000c00c00020481c0c003851100c104045140403041070304242424004407420104c05400c481c42c00703251042403600050361121916502d0250f40c0e4402d051202d412403401421480006c10140001016803401c5502c0249402403051200141c200c9011070f04800b2141c098006030502e0354001280010200c40c1c802c0f002e070000c0c140c801443c10856a6444842d02203462045d1f0b0240500d0401003035803662144c040d9140c0d1a40030b40100400c4d80c0d0703440301d448643c0d11088002d000d0040c110020030fa950300c01d085490902c825464070220381e461507003031001503800424800079801e00380088464021007800360b15001400741c48081030b000701c25820010490f620042540484405201c2049016041561002c12680100420410a140e48400381c094400c083c2d000b40130380400001c0160b5282c0354242001070f01d100c11400c000d11006c2e84803144400f41c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 525163750 1250 525162500 525162503
    0x80d050f010510090302040905120408031e271203070f060b09060904080a031407050a11010b0a0b0f0f040305330109020a0201060e1314060601200c0303070825 70
    0x41c07802d10180b0147c01e00d41c000b034425600c89c50403500b04982d00404030200350040c0d00200388a800004101f15503924014600d00321044840f030b078905d0645440000c1310055120091520f018a80c4120b8103c1a5a206a4411403103250816665148614500406030b49003807601100da0b186045403a0190303007001604a0b100c1d810140c810b07200d98450f0380341c01caa00c2c0c005c1510301c010951510f002038420918400801d014031603036151603448114050000c0d00544050125213102e0303142030050041d40d5070318242d0004480e10307180525a90040000250f0079803140244003102d0030340c001800410808000b4817101901c400341d18044420300e440710031a015858070090600720000c20401480048415030042006800038000003420b20398601d164101c3c0d11080b40d555000003884500c540500409500f566490000034010f02100d1820800107403215280e0380c25a0011030701d60413100c7c5203010410050f0313008000103040740e07229003561514201c0c641c8105071403030bc2c1c4e05941c82d0b0000c2c200c5007282c5210155 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 525165000 1250 525163750 525163757
    0xa08160c0c062c06091c0206040609140d080405040c02030c16051c030206040b0910110c10052406040305060109021903050402030d050313020a081506030615040203040f080d050f010510 81
    0x2040c54410000190404419415054642e6986d02c0c01070392804004e100401017a00c600b0500c41c03501c140d4455444e56068114000c0c490041040c002030500f008807025220201c80004030440c40660881c594001c1e084034520700d1050b002a00c072400a26000f0104407402110411040001680b015100340c1003000001c000d603000002050010f921030413002d5001007000704940d1101c400740c8826080d00d20307000034103400c9000014804000702c0b00380300400004104500074030890814200034013034600b1510802480c0c000e900b1300c10007181d8450080703400841d00b141c01c841071541c440014000940c0240c0b000140e0500e10480c1080c01ca009019080c42143c008029100c0316001c00c000b80c130190b10003041000c88030300407404d09006035508414140a0010700e401405804030185606407003540103400c0c01d219600c603104000501340011340c2e607042200141c801617101e84580c03801c0381c4060201a002400d4500102c0e00e02c47c411607642c482840745030400c1c1918030307a99889051003a618401a1040c000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 525166250 1250 525165000 525165007
    0x1a041a13050a181205030403050c0a231914010e0609010209011b0213050405030c10050f0a05011505130906030614100506071403040b07140607050a08160c0c062c06 72
    0x900c0d00035001b46502034001c0c2080341c500a101880207040801c0600f04446000000340080e240039040d04800001c050110024654040011000c07094004081d074020036240d0380c00d09185503508290080c0c4515210101120310505054003194080c1d00002041400a5130030703c0c240d80d00410b1300c0c0b9070004a070b80241144c903034100200c01d02e1001d0310f8010019a0746110400005c4522030080280d8814030814882c001a40e04111500ea0300340d10010304100c80443c2001c0050018600345840c8128080305402c02d940c0d0741300044e0b144c883e21080d50340301c2849140b0f0120000140003180c1c2103a0f025490005031058642e0318081d0544441085000780d0350401814451500050040c40c09c0c6900c4248500440b03007481d5641306001032070703401b000c011180d01440b1480d0b840e000404004071074020f855400d10f1070034003405603001400890003d000a610850401d18001d001e80903821040410350002c08021301141c03034000203400c5040701d844042c00700f0300c0c00410003022100c0d070380100c00110005203058136 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 525167500 1250 525166250 525166283
    0x807020c100e041518060509010f26010f151503060b031501111b12030304150902040b13020a110105061008071701091409011a041a13050a18 62
    0x500ca42d0070103131001214400c3c0418070701250140070301250000580422040e0410042c040059010303071100300f0317090509206000d060740743c2511f1108083c1e2907803c140720310002c140c0980500a014106038500d80b9181800102c1c03412604248180d03100100660a56035203c0812400c40713500d4840d91409000078404211603900d2083d02d50400c0205150141c002c0900c40c0c43c641c104807004580c2000480b03020bd10341075500300300344460030000c4000003a604504e0035448071080460010200700b4940c1c2c0d118501b900315a100e610200c20404041c0c00748a4406245480b00025400900b12401080e4811440c1c0e84030101402018491307074016050b00c10550040a040d00c2c2c1c1480540f00409100040e034200803000c003c030580d680240000703200810300e800d2605a480f82204094901c0701183d04040311008104000e00120100e40c60a5130000f520701e40384080e4080b690740010360180d10400a4403040e9072010700b03800481c003030003500e141000841c40f000b140840020b1030b400c0081040c0981c405518 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 525168750 1250 525167500 525167509
    0x81210090506060c0c0f13020c24040302060403081e15090a0c0203191e170106050702010507150f0f0906050c0703091802041505032403100f0e07060807020c100e 71
    0x411b0034050904030001c540c05070000e00766000109c2c003020503400310700c0341c107002c030003092000784014011000141c06041c542c4009444220040000c1c0502c003d000200e080b2002d03c690700340c1020340a004010080c10300c1c0d42c6003180360540307a034802e100b080c00344007160002040f81711701898084181c000b9482c0043d4a103e0001496a5010a1080c001031501c09000c40300044000f80200507283c1d98000c0701d160050040003118010381000040003400e10076000140d8205040b1840260080e0840351501022000400541510401c1c800120f00309100440700d001e554201d4074419206070070a01c926619129407211a0083e03580c0500050075078030040003c890765070940c005194486001501d02038a810032220242030456000d0300240b4000100700003c100c44442d00041c04000700702c0c1c0382c1c5142c407e0003c0d94982625400e1000c00c2c0e51030800d4281140303a940f010400d5121002903401c80d0b9a03841002d0a1000104c4420000d4024856501240d1600301c0b11500c4044150312101c1c940440c00307042c072 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 525170000 1250 525168750 525168769
    0xa1406060d05060a1d16090f050f040b040c050c010b061e07030314040b091902012c1302070507060c0b010303261006121505010c081210090506060c0c 66
    0x40d084088404c020400b03120440c10b590105560125410310f134240300340105003150b21200b01d042001403a13002030003198281c4407284100d48046843d060f50300d03890390000d0000c00d00002000d9106150040e04450281c020002e0004445000020089000400d052000c01d12801c0c14114004031107111a034040031407900030b402034600034600080c0d000914000319140080c26141a1040c03070100f410814000c20410003020b003000304418080899134550b0003c3c0c04c0d401d21046190001624140341d090084100d94203160f40d10000385441c41d00850b28840100035880a082520b0344c0c01250808241035000b5609400e01d41d50149451505a180d52412034804100c1c6603001c402c408580041c141c03015102c0070050080511f00c01008203a4a807000140100d84000c1d00601e1082c2080e60840b490044050001c003160001c0c200031601101e035140c066100c0c80307160724107484402c00e1000d00111036401010b401c1651440401041541c45440810845004031410b01d089584205040100c0d0305101c0000e = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 525171250 1250 525170000 525170011
    0xc0c051002070c09060308030f06010323091603060b040b060a090504090804080105180c120709050721020406030609180f030e0604030303090221030a0c08090a060201050a1406060d05 80
    0x2840e03c01900c400c3c1c5503007078403d2603000307172030201c008020301510f00009160b540c1c000d4403d0074104103030021200c0d56042e61074481004154405007500007091002c0520510404080103501005419120f00d0000d00802d2400b40441c042c901d400d1341e031010b42c1002821241c00307001945480f01058503220400006d040201d00031101400e003030100003030703c50003405610b00404804e100640214410109149040789040c034030b5104080402e9403814040700415804140c0300e40390f5001c581582c401605803240131f2484c15000041c0e4041e240c4050303044d500d5000d0010755555960501030a0750700c540e80c10540d50784c164074203c0d0114a060b00300000b40d80005c0c4101540c0719090910003070100c0000500f00c0d400940c1709a001c83d46030030800c070449c0350666405920624006040c105001c240d16143d5480c001d100e103507414400c00510031410f0140141c00e0710707605040107054403c8913449403070081c0070301004d0f56181e01c0c10f810200540503c110b9812180e02c1030030301030181418480007504070405020094007 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 525172500 1250 525171250 525171263
    0xc060906130807111e09250e0a08030309030315010306051f03380d030c030c0f0c03150507020a05030a0c020d020406030506160e090c0714010f050105040c0c05100207 73
    0x81c504035480301809241609100012001e204565030306009880f00c009040c2c02c0da0844400c01c115046105003120601b1009908c0c2c0103088000d0803010a83c1081550428017081c800801045036800001000314861008000e0384030300780c9501c0740107400b6104d09018040d8448800d001150305000c0084000628908518003c215224072103180c1300c4400801c01d401011918106580c248428044a014080d40d000e0303940c0801c0c2c810603180240070718200c072002130030401d000c0341810500c0380d140e80c00e03d5500d0300450076002c0d2581d240780c00050030240f58000c40d181810b0200117803911340042502c0002e00e8200000c3c501d0045042c9088074001640310007285d0144140f203103a00542c4861080703c011b18860b00041c000c0c2d0400000b80c1031042440c0004c0010061007015503001600c2b0251455004450b62490b1901c0d00c8441ca40440414154080d40c405d543c80d00450a41700221504500d04a8400792000c1040004648003102c0030114000080d14942c000048180803180f00e5004009203800740c003 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 525173750 1250 525172500 525172523
    0xf0e1c061b02010c020c01081005040b030f03031302011106060d0602030615040810060e04050706030506060c0d08041e0804050d14030c0a11060313022806050c060906130807 76
    0x1050644080c20300501040184c1d521000c50381026010042404000400d081c28502d51070100b1507007902c43d0042c043c1a000719103648401c40244c60410000030840481d0b0103a80e124584080392500305030407580309a0000717181170740010927040c0100e103981c0140c1000d040c0305580d0196407902c034040d6001405454129400c0307030130b000d00800c00002420282c00d0060140c915940a103992000b6584d0f0380d0080c9004800f008140f0000400c000f41443c00ca9210342070104a90361903400103000c0b800303504140d055501071000707082c00d802c0d404488244254843c40260041564070b008103d01004500d0008101080070803007404541f03419050003440b131380b145c0c0b40c807115030040815240c00c5411032010001c80740d000e5094079081000c100341107007980307605842c1c05003580b402d0b0008044841107900d0207801094208403100051b990300c100542c089080b130044107a02c981d9071900030900e6200980e03400380703802208081400013401041320f0340500361140c2c08007814840c43d210b201050b880420221f0b000b01c2d040 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 525175000 1250 525173750 525173771
    0x60503070e2b0b0a0b0102061017161401090902090607030c05030c0a0507090b040207031b03090b03070c0b0c03060108040b1e0f220c1707120f030f0e1c06 68
    0x1080d0541c801d4401c1c0310205882c1410615001501e80d85445e03203055402c64820489074070801c47d03030003013240c821900081d2404000001e06080c041c40b00000d81d4846100304d800308101c44000342103c40c2080c03c0ea1405500c41d0790380c0c6980d04900480f0100c0d50b10035020040c180101c0d104010280d40705010b4401d0707902d01008118201e240140002044589801540c4100700280003803141c0004410309850952500030342e41e4004140c4000d10b21051418490360710520189846900084003a02007034503107590701d0900c140041d01c6218850f10880e103044500b400107012440d0401600e018500c1a12520000d403078540d102a06488020200821000160001580306c00140010360058100c490700d19070600b0170400307901307400008944121a1f0141c01c1d00040020b1240d0305900200c442444100845028526285080c000d907079000c40006c0201200b00d200340112a00b02c220403602c252551090b504842c43c003a100781048500e00d9504c2003a08940040030140303002c040d880c15201790800031301180d00 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 525176250 1250 525175000 525175069
    0x11151b1803060702010501170609070303080a1b0e0f0402090a0605091306031a06011d100903050109080409060e33030a110405071b1115040b070b01060503070e 70
    0x1111a000141e440d8401041801229503030a142c1d5231303a280c09070000d0315003007144a50310841484001d0401c00b9210025114240701d511041031180b001090107034040302254000e00c040b1031100601d12860b4011440c1d001c51416200b121800719001d0560300031280b5140d410f58298103c0104650400803140204480d040c00d4424917001e184540380381d105040e00100c0200611800800c03a0341801421056a5002039510710706c820ba01c1d004445a07045030054240440350101158030003000c80d800c060800d820411828068400c0e034014410401c00c081c5d686100e0402184e05450b40341c025804500705150002030810101c1900e1a4500f01880150645011901d4900f000c4411741d0b4420200b03000e038002e07203003d0085a42258035071030002c05145444801c0d0704503c0200b071000b403014016000c12041d5403140b0402c08900724694100030345490340c48007251a580c0c0807c004449426810380041500c0740240300307881c058020b81d910200d00c0c80c1800d00340541400c9100380382c000303400080d2002c0d07000c000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 525177500 1250 525176250 525176263
    0x3111207180e060a050c1e1306031e090c090902011b060c1215050910080d0908150f0c0903011119090503060124090504090311151b1803 60
    0x507245400916440385001c52800d021010742000c090508000901141c0c440881c2520182c22800110101c28071100141010364401c0403808000104054000038a10b030309030303000c4100c0003452028962034025141ca00412a04444402040b01c00039075010b000300581680301707151a0f0310604020402c0050392018011003803580908542c0561141d0490f03100940c0107400d09171b511111710007440750150107102d036107411203603001d01c07030240014400003204c40c060424041d00030445441039a6993f509210020700c004901c0c00781040c03e200d9100072a640f40540e00f060342c072030541e0618050858840c1c05814000b41d0040ca0001d03403540d259aa88104041c00300e000f401445d1807101c03008801c0c001300710054440c8050f80e12591098200000412602030086044c03031107080418000181001640c4003034031505a2904020b07000b030b1800110208268010003d590445440303402c90380548502040800d1100d42140c81c1b01d01411481800d00240c40c2c1c0e48003a080c1d206940c4020000c2d0031050001c01d05d028dc = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 525178750 1250 525177500 525177539
    0xa05100207060b0103050108190f08030a0e070b0a050409020d0b10050301050a0e0603030d0507110f0703061425050913141e06090a0621050606060403111207 69
    0xd90000d440e404102451103200c440590a0a050040350315102e011911181d83ca0304844c5110705e0140201c0070048403151005006034000744650300d17030401c00b85600050422178800070841c821404041155131100080d152600000c0e9149442c007824030460202035000750314525942034503041c00086555400f29031103800340d02d5a03200e0b07031298500810800201c0e01d950005050310744d1036003448103c1e103000c02154003180390030720045455102d454040b0b07004605003080c02d01c1c1d80582c1c10203865502c0701142005c1143c0c02500e05102041c1201c0a40380301c04e509542d80743c581c6104040790212365180c98184081500340381001070400c00d2034000302d500c460484030840c680c982d5540e03c0d00c6000c0b40b20010700d900700805d42c4d407040d03480c0682038020310102d101074801c1e0b00c900046d41c0042c4084000340c00c03e030041c01040140c44801411b2903a43d10021050800440711740c0600400506981080800d4400300c94100e00036099aa1200c0c0602c0380c0292500010f03441402000800700381034010814900c12070 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 525179856 1106 525178750 525178783
    0x7030f09110f011e021b0108090a020d0203070b1303170408100216060e011e051e09030c011e060e06010903060e0a170405010207081603080c0a05 64
    0x1401303281e105218000700251309203440d40d000c6070f20090308180300ca03413042031180d081c01580d0743c5000f11030940a0360f0005030000e001d850135205503201d05001405690700c172500d0308a055042e80c0140882441c100d417640b404c1040224070301a03510121002c0540070704160170706e2403040d00d03285440c0c1e00d030410b80d0f001700320222003108892034400b81c10745c406020003014a08401990191540c03030140c030462010142c140324260800c2c003030f0a200d28020f0302c810318100d88980d0004581040502404c115200500184e0243e0303c0074490b40200c40c240c802100390040b03018100341c1c10b8031190303046140b6056141045c494266004103050041d0382c2d0280f004100117070800161450041da42d0741c041c0680080c0c03014130450300010b0300100300380e803000c1e404e450140b41c8400042da81c1c0c1e00c0303085190300711740c1d80703424204045221702c4007918541c00c4520640b0f0050f135081d29101d1034202c02e03220010780c0c07 = true := by decide +kernel

theorem cover : BRFrame.Cov 525000000 525179856 := by
  have h0 := BRFrame.cov_init 525000000
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525000000 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 525000000 ≤ n) (h2 : n < 525179856) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
