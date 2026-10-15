-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4391
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:27:59.409564+00:00
-- url     : https://prove2.me/submissions/5429055d-90aa-4b79-b354-4ac674f7b0f5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 789568345 ≤ n < 789748201 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 789569595 1250 789568345 789568363
    0x1818120c0312101406090d050a05100f0207050a0b07090e0115090501023007083f0606031009090f11010302070c090209010215070c050601171b010908 66
    0x8541010615014810050035855006015401030540345828190305a02100b0004d50301803042d400044c62643c2902c408004181c1ca6400070151b8280700b40a0a00c15143d480c00c190b0914414545000841c040c8902d1080e280120780100c0200340c0d511580d81d5030815010302409280c180310900c14005a100c002aa8007406484041c0c3c0251000381c03541d0025140c0321032500914190342028a5444030f1000640e41c5aa041c111480d16489201d070f1200c04008502c11036401030040e5200003030030400414981661070018400244017034140c2012541070b00007016860000c0e121610344000701301c0e81e00c0e120001d0b581044183c00b1078000300c0e07a0340400c042201d280000442d2407450140702c0c0c01c14042070301046030751032030282801d5280446a540b0401c4026040c015014103d5001c10004402c0e4404c110b0803850a048902030441800d20307207001740c1080303045841103560b80b1030351f40041003003c00c004040e1484104c801c014400c1c0c1000307800107850b503c4400300d034a0422084290000768404c08001d0703c20 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 789570845 1250 789569595 789569617
    0x241e0b090d0803070f1806050d051f0605040512061e090309180a0e0c0a0603020d0b190801050c0f0901120e0709020703020c0a050d03120204050d0b0f06181812 70
    0x1460040d10b81701404c5881c20041e009806240d0301c07030030003c060300a000c82d00e04500081000540341d8800076201c41490480800c1000e0301032104020900f80c0d048002402075400031240e05d209021104031155075084101c40d1909195600080b6a103071400c85504140c01c60505001c1d00d040c15400e0003c1103115120038440421008103205003c05000e0700c3c400c2941c903181820192503036904000100e282c2422520501013096030010b5000003840c0554050103440000034416141410b1002070080d8260f198018414507510f8000880c4180115008561403981e8500e07499042c42c0b4640e0066610140940312a07106a031902e03a000a052014010800500040c00006072122101e0078002e18001b41c2c4042103028241c0b0940c1441641d4944d0403011582e60b06241c100c402807400c4141074080d00035a804142c0060351b001003a0100700100f440144601c15210541380203581e4641041038601d109120542ca4008000208034880079100c00e007484406c078641105d200c00404800c000d00e40e4090455a4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 789572095 1250 789570845 789570857
    0x1905071a010501021b0111030a090303090e06030c0d1b06180911042606130b09060f0a0209040e150411030706210f241e0b090d080307 59
    0x802044084242609504048403503800c00e50304010010b9541c12044c0e1924101481c41500c8014581c030401010442002040a9a48a410140001d04140d8040c002100840c83e02070000c0703110003154602134070a40740100109854251101480907920102205482404000c0c80002c00c041000300100000c108590fa0092100359a61070010078100c40d420801e41e480c00c043e141c0407602564001d850580b111040355881005004d950312802c40d0f2441000380c03c4d40240700c20002c0741d0103002c4c14881001d0151260322155900c2050301a02d400d000c40d500ca292101d804040303146640d90f58080d01e0f41482c040c5c400905500300b180c62030301e8040910b01e001c1007080c52608000410080ca42680802d010980050000d1410944c0150140326100384a0410b05800c4407400b940d484690000c506203100f14408000e00c1c4c20200300e21584c010703004145a60204841c900050080c040d800b00e4004c5401c4900e164601401c009890707007164407103220030768044a0b081e000d001040c8000002d5008801c1030300c5503 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 789573345 1250 789572095 789572107
    0x3061b1b032b0902130f0216121d0306160201060909150b10120f0b180403021203060112020708130b03090d050a08040f020d06290a1a0f1905 62
    0xb00000d00c5070b4180080d045030800320014016220b0066504018040500c00f0507034010281c5800000d004035844084003000d811841c0f07090115240076826040fa503a07841840c0000c02c1080d0f8070345155502c0340507816a02c03100000b0120019030304449a4200781348008034080b82c1e00c030505004d0f107110300003d854130380b4014403054008009115140e20100c042c0d0380f808560550040140903c40c02c4c0c10042d1965444495120500c40c0661101c154010b000384407036048210041c1c1c3c441c0c07044044404070098495009051943c0000c6410b5a1050300140d452041041c000c10704031001e500103105c21070b480c01d81031061040048984211001404800080c0740d1a40740c0f405c1c2d2503150441c02e40c240c0e0284081006040412940025545e511a411200f008180701c5588046880c0f0700ca844800b4100c10310781906503210030034101c860a021346058007941c00d140350800801a0382c820301e1180d1085180704543c1c10522040c1100903100400c40398071003909200c2e108400c80400c4212a0117500050800a14 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 789574595 1250 789573345 789573397
    0x2040816050a0303080105010c0503070b010b0901030b0d12110f030403060e0706030203011406091807020c12070b030708100b070b1909241d010506030c03061b1b03 72
    0x600340080600301c5840d90101e1560700c02800d08003040c01000e041041440c901170610604000b19082194051906022036031340c1d2a0189858011a84803070005c1c3c1008041c0d896031410b8901800e1003034002418011080707030340c14103031a6100a43d60300c200070302404043d0300401409001a01c01980554404a000320b0719205141c204200e0780c00c40c00c2071510510040c40000f40e040c40284590344250360403903036004c18900140c071942d01009404120b40341d5100704484c0941c04070745043c1d20401503990452810829460380c5c2c9808050140070328518050000400d0584140a00c0e500320345204035a8010750b803910f80f281d407154080e15003600c5030003042c41488444102d0f01c40f500d0a10b44001c9041084105c2a80d83c4a0340c5840c80031081da44d800e03480e030010030740220765110745058101e0340c039000110f4402c12180750181100f100e207240300e401001c4c011100c505011600b50700c51400001d1680b014141d50f40c118055800103444e05496404106811075102410001800c00d108580140c1000320140a5 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 789575845 1250 789574595 789574633
    0xc131d01032a03030c030905040c09080129090601030b06030709030c0902090f0906010302090a12140f190305070f14012a2a030f0f050712081801020408 67
    0x40303080b4aa0300c40c0a915041500c032070311201c2c10350354940b810000420860404980c440115005654000c3c6403103224404a5001400f940407251010000c0c001e00000d600c000c0d04220882c4001503003490000103000035840c0c20051140d02150506000802800344000701702d0700d8100700d8030007000c0380c00d811040c0188900d8500610040c40009401d601c3c114064022840d05054030f000355020300d114401080d40390f07001c1e8041d1995104003400d000e0125582d40d003007207454184024140c3da080b00c0c407101007051031004501e031501113035014010042505a01094500c8000c82c4d81d05a0800106200c0200010041c101c40c0d8052805001c802e0b42103128441c00d41d084484200708902002aa98484001035229960720003800030142003214440c901d540c92003502c00103d12903004a599148051020035800040324070001102d56181c1c100300f01c400006403103900c00c001014120518100415030342e28416284c2079070203081000015845040010f13a103003a608145c01404d02600f07d018600e10041d42c40c8 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 789577095 1250 789575845 789575873
    0x80703020a1a01050a0302040c090e0c0d06050a05010503010b0d060b0a2f06010b13090e0f0d03051b03060d020406140f0603010f17031e03010f1d0c131d0103 69
    0x41d9000340b41c1d51402c4009200828a848000e0280d510340203410b420038041c80b03036803000f4506031125592502e480243d104203903101d650b054614618003000418503003050b00e00e1105035901a1039041c43d6900309800072182c0c2d00146042035245032500b10120758040c107a0085e024491054031250740846250784c014001c04002100c6503a200d0310001d090704032101c0025064111100303540520394920300520620310f040700c240c100717100080c03e002880340b2030b05000605088108080c4c06581030710700c01000480036038500391044003040416580c1301c1000b80d6003500940d00520300401c4071b5410700b065800b15003652019403210b1017072031881c141000c440c2021442641080d0040346e1041c91581009941c0c09540c0060003072417640700c000d0300c1d1950300d88810030445107100600712040720300700414180300306150b01c2402103040070700030304a0008a070144d500c025040c11071040a004d45998940300000b5580e0000e03441103002c144042c10020b030803451104c8814008940d02e000c01d60642c11814a105411818 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 789578345 1250 789577095 789577133
    0x18240e0d0f08360909070e04050f0708061302061c050f0f06030a030507060911120d1b120c0c090f1413020a0608190c0c060c14040e090307080703020a 66
    0x940022210b02c0e1260070900f035010742c00c40306944c142d141e8040c454036100c12034201d00b40e890207600c180001c0c0800007808501c80c0c1404411a8005c0e0b40b00c80040d5145d0341d040d1082d0342083c00c9007100b8001490060040c1c07260052502c0c0400140417503503011015180c058641c00c12085141c800c0c400480f00740710010764082011703002040324030744690b40240706118150010f490707580c0d140341d6501042a03003c0b144e001604020100e030203424000348000d0b25a155001070501140c0c10450482c0005880322141c6d1820f80c0016140000c0300e118201652901001d1030f04403590801002c011841000038803409403030341e02100b00020015041d10212080d100c0c01b41003a0605250f81c99017000503900d10a040003a10300c1c0c2e25120881b038940b5115020035440f0030343d441b402c490409040c40b030101e60000a4108140c000c00051000551002c8103441d141e41e01007881a04940030401844010018485503030000350360412645490f200da103450b031f100c0d000f01c2403c07001600981542000d0042815040c841b030410 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 789579595 1250 789578345 789578407
    0x31805010206060105090f0f0303030906070801060806132f0403030806040e0316060e010f1e1e0b030705100201020406080c040f0315090b0718240e0d0f08 68
    0x10f500280c440e01900a802c0e00c244480c18940105840e540d0301c0ba01c21100c050100ca4980c1004e10140d030300c5801c101e80f55400101d90a0000031031621541d0000c0c00f401d0b0180000c42328081d5245804080c1c05042169200c80b43c100c015040c47e1b907000f840e25030002040c080f10b140c0303544c00c40c40c005044090203000a44100d00340303035281018480c0442140c0341021100d034128002d20f15480c0c01e80207040401c0401c841c40d4a80707511420080400c4e004070070f04901031103081c80f028044941c00c1c0300f2120079204010500340c20100b10004844140d200c20460328000f42100c1c0040e54a01c0040d500d03e851640e0080181d4001c20300b007068980105400d41c01c051070110b42e506050400800142440c0f1510001e0700d5200010b643d445030341c5403a807007105604e421500110a0785400900031b88180100f005a03612a01e09440000c0d80108544024845060040c4000840030580d00c1c100d690038002391010b85c1c0034056840002c0040c1041390990746040c890350314140c60f85050961241c2030b10a42003d0400c00c20 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 789580845 1250 789579595 789579601
    0x210a0e010b240a0c0f05060f0618040615080111131203020c040b0a05040f1d0a1a0603071d040203070504050108030d0504080f07050303061207061211120103031805010206 75
    0x30070b41c016140030000e1149590b02c4500380e02044810264400000c1d01e0400c681154006000700801d42900c982d6002d042e500031600c40c0c1d020300520541c090011070384003d40c1d8000c10002099a04044401001040070505068860421508650300d12400c0144410f000810010520542400c000200b0301d22103440c1034440ca036100030f5103a070a2810310911890355252030070050307079031840001c01900340503008000d03000c443c0034404003c142240e840442c6500001051080100004140c0b4040f6404001c48da5070821140c80300c41d005d1400342c00c01307605021704100840c4e03180034200c104011002c0b84800c10ba144c10179005040c107068042d000355026609140c01070000080c00800c462a84100d008000f95a503a5410401860300524003032403c5408002002014003500202960180c141101c480000307000e903a07442a52940c040c411800801c10649564003044040c1d07001c0100038045594040ca000110050402d48100907001103020584101680703138040c10031843d040103030000f80001c05441c1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 789582095 1250 789580845 789580879
    0x60b0d050303150a0320010e0a081e010b191d15010509011106131a010f17011812020d0807020319050706230f0f0c210a0e010b 56
    0x840001c103680f00304210b600214485445007440c0c40025600110001045011a5000c4080c0300404810368000399080300100114034002030f41c030040384c04000040c02446504200e07196162000400214070303540c0e4005d614103585404800030340f40c0c11342880b080d0060782000d003aa056510101c1c1811a800c0e03034074040010340703c0034081007003011a00f4240513403944041c2004030398021501d550780c45a8003034813080c45004043c00c86480d000600c9140c1042c000c1140ea490700c94080400d11810074010540d5004002030303c440907140345035507650400407030940f4500741c142000864105003117504e4100076120009203641030100c80240c90051800380000e06200308001d50328001c038854110903410f0003040d0401e01e8012400c031010540c0c4103005120722a074190310b40ca440840402034080a85400d80012104017070001c00621030541300c1d6980b11780392541031900b030640d006401019191002e01c49032580281005490a118100000c00402e40d1103100c1400b41c04d403181c90403501e009101c0c08000404170 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 789583345 1250 789582095 789582097
    0x1140702031905030903071503060501020a052d01060b030a0e1506060a02010603060608071401020f06040308100b031501020d09030c09270602040e10061b080421060b0d0503 76
    0x400380c140400080c148450030103500f1480784035200c0c6d6252041c4d0400241c4035134a0300c1840100c02e0701da10700308a2940c0c1c1d42c0069840e0550b501c002003da030002d1109010301040ea104039103200c00c80d031070611a12205c5185042c00c4440780d41080c0e00c520004000c000b601c0d00b260280f40581001c1700c014018503240d40d24100e0368000c002e42050b200e5030000c228120540d1007580080001c5801502c203001c1c1e2556008282d803034041034000c0600c0742d0001951000a03500006201d80c084025800500117955075440407601d054000d024200b600316968400158901c90401660080c9401c0b4162840000d000001a24102042c003d081c1400101c0078200301160419940408841031200041041c12000d4036228104054200402d02102201c0c00b20f0144180c9601030401c0d282508040c60064980d058140e400300618451880001c010a25114030a0404002e002c4943c0c414540c2c1403e058842c46614a400c1d000c07404440d00d803840710115818000980220340507044281d6071668030149544859881e = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 789584595 1250 789583345 789583363
    0xa480311091210140103050717060f10030804030812010806060f0d0203150106090915150c05151e1003020105073f0206091f0c050d0603110114070203 66
    0x200d034001e070ba4000301d03461052020911200d0300403810481c0c11460410602c404200703010541e800c5c81550f82c040b0b82100884268094000501d0082900d87e492110407080d02e10010308005054405140002c0000d5003080500b0146209070320558413012200010941c2d50703416401081c180c0d0000381404042e48840c14141a85c8000b0744140c45580580d0004c2880c104000300c100c1c0d82200024000104035910425100aa4066180900258540c28110020310445010741c641070000c007010a01c4581c01407101c00c2181d80725009885860101c001c5c400c0458604070381008601c07184248024942844002c400c0c0d01290026498807480d045800080890103075250060030307000e054030317a0840c40b00314800218134441340c081c0c518901182d00c03040304038000711000c516015204001c0414480000403d00791401060380840c8141420119001009823000744032244c10f0050170044980803008500175400618010003070789010071407000004012019041803c2c030899810701092005035030205040c04 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 789585845 1250 789584595 789584599
    0x180506042a1b0302010e06090a1a0601111204150315060e12030d09060c0c05060f180f010e06010803070308010521010c020a06060501050c060a48031109 67
    0x30300140400c00a03100c5512850b110404102ea07580d07014101681504080c41c0c406441041d20800e880700e04040b40e0360020a04000e1403000340409404c0310005085400c0d0348294149040e6024040e8090b030b43e4249801d080803402c1002000a003800b10b1000440703c1d031500211071400704495040c100318032811103180d002d0002000040d07c064601d69443c1c0402d504400700180650343d0751800b100e00b0400616450504076207990408080c107404034080c860620105400101a040c03640d10004418400e02000703040c6185980b000c007400701c0c1040104145221614400000260000e0004100b8a042c0d07050784085120ba00801c10800000c0d4490b5a490440d038090b2005880807070f0320f8001d40b041c1820220215069860138801c0f1160035400119070408034042c246c1085174685500c0110b0361031007080300c2070290341c1c4a00c01080f40c100c003c0d03010007070150028000313107500c1c00300c2d0700700404480354034021007400d5806101c090602000429136010029907407c003048064015900c4058501a0343e041034 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 789587095 1250 789585845 789585911
    0x120c17070809220b101707030f0c050309121c0f090602030a09060e030301050d020f0d0506010e0f0a06050f10171e09010209060412050705090118050604 67
    0x380030810320006030b810125004025102d00e116048281400402030f101d01c80603281000c22010795410540d142d20304240e003542e6a0000d0102c03603c595540e14001401e10010156201d131000f250000512550307640c181c1e26075445540c1e0801c40f8015140004200403022048030401c14207808103c00290321001e9041c4803008903040d04c0c6000c070580140940741c4054412400041044601e0400e40d10070056a84680d03030410101e01061082075682c0001d00405810207801d641040240c074100804080100008021088000c0140d9800d03040c6031080e400301c0b01c81312503641401544241d584c4070507844000070000704038092401c2c0000b0008081707100e049029601002c2a04101d41c03040300c42c000702043c5904d549545080106445580038001c4482d1b056044801380031800300c20040c02207540d40705005000c3c900b0281010ba2111b8404900c5904035120321850300d000641e07403103003201a8020b01c11254000301003601c0031842020783d06d004201c1449a803410303218900640b0045030201d0141c0446000b8 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 789588345 1250 789587095 789587107
    0x120d0f08090123070c0c0b19170121080a05071e0c090507050c0109030207080c09010b030105041d010e0105041e020915011404080c0102070b0412030c0303090803040f120c17 76
    0x70ba400f51504000503000c10701e01781b00441c80000103c001c00c2007189454045001e6050032608484028904c50300c0d03d4018818401006a2024035208040100e014160880000419510004c10754490340b07804020820202e05031091007440e00c800601c0c50400ba284110703000302c0e0354031301c2d000b0007090180c0c1c070402c1c1d500c83c0031a011078800c074150360f40e150044000308a00602c90402a548000d6845116010700c100411804141048814641200c0101010030b045900b000c0030031010b08020000c80100ca10340500b81450f125007402a10721540b00c0000001d494241828808845202e0540601c280309448281c1401038490b410000d610070010f440c001c500e104048012a501e070410070f14031900c0c00300460003280c18000030580c15848103003602240c0351642d0710080c00c10140514860920403030180b07005d040c0828000c0c03800070000303842450002003980e803070354415103150000c1c0c0741a54070700d40303c04505040094400041444c004a418091800903582d561000d14070041482507071208008541 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 789589595 1250 789588345 789588347
    0x9010b04290912070306051005060714030903150a05070c03080412020726061803040b0903010b060c010207050f030c0a061a04050702060a11040308030c09120d0f0809012307 76
    0x6895002c0801030200b266400c1c800c260f150781d40410300050b6492407402c80801c07260320381e18014008569018058134100482900c0d00b8100c40503016030300b00030f4001082301035503598003844020b0300b007071078216801c54605201c110340f8200c6030010194414024002000000304e500a00c1d115031007940403040d404d4115200b00100c2c101692a88820280406e0f0a0603170200c40b0300d46a04003444a80d20111a001e58481c8116603012100580d0101140c004000502c05c0810783c40003042800806000800c1800307403140403401640c0f14656410403650701103104000c12000b48100c00154112400442c00c200c4581c0742c43d516121410402403020703903a00150204056402c207041d640740342c002c0040103d480c1c8008040e40320b040031104c114006107032042c0000040c001c641500c00307881c0c00080e55415541ca01c22080c140340d2050315190b90100b86440c94000c00e82040191180c040490346e120724403080342541c080d25002d00a4031915060f4184000c140c803102400342c20303400112090032030032203d03110680 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 789590845 1250 789589595 789589597
    0x1030803130209010b0c061005010905131b11010e010b210f0d0c1a0f07080a0e0a0c150e0913140616171e070314100509010b0429 57
    0x8000d400c48920f40000034004d1031107000e011000d1000f02524030f540e907150704800002d0843d0203401d01007015840184800d08000120030303012070100c0b40c00500d62401c90025510400b2458400c00090712548505242c08000c0c01143d010400355002808010358020001341050000424000c007050380380003503030a54404201c080c01800701601903a0520801040042c150800600e051b16800d52020007040f115502c004003130304c5a04c1141c0d00301c1083c3c881c0c10044600d100098555540c0c0f40c0c0300c035904550020140203d4204620881008480034505801c01c00029040000f08080c01000000384006440e00710181d984007800c480d406868401c10720b402240805800070b04c3c42148031300c0e4200640c1c04042d024402c58211a80c5a0310215101e1800444660004503005640341040004607a580180052601c0d041a16400c02048602060308800c4803518116007010114480140c100703d80c1c2000307800c0034050840440001d14050803c00e200403441c4251003030400c000400c00f05c103080c21800340 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 789592095 1250 789590845 789590881
    0x1050609010627090516111209121608011811060c0102040b040f050f060c0c190b1305100c120c020d08070503360d0804031416060203030103030801030803 68
    0x16084285844d103494000c4010401100c1100d582480c1c003600682040c0034101910030300c40340f140240810708404501500c20740100f0800c60b001120400311441c1190305002d054070804414000002d907600d89007006080d9600c000c1078400400c50030140c14007180d0701000301d90407190165441943c82c032000b440540284201d50020784510302c0030a0220f60013012850550827a00126a40703c030b458a1141089000c4c80780e0f41f00403c89905c199140c1c0404c0c10040d035102c5015005550206945541301c090707a4190340424249640d140703c0da41c081c0700034540b1144c0019594000d14101c00348040994031596090352800010007880b0f02c4400304000c540c1d5000802e03080aa2000d80c042d10350807986400c80e50383d0410205a0202014001809d40c1d0000a10400040c050f0808e075640c03441d05d11206001e40d480b291103055603101410032011000c41d0005079000800480b00004005e1000c80c00c16100c3c0358070080d000282150002c0004101080d80310804c41c3c1541c1e0001d11640d41e0382ca031601a504c04000f00 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 789593345 1250 789592095 789592157
    0x804061a010c240507020d0e010302090603190906050901020a1709070e0c04050604060f020c0f03190201030b06120402132306190e1e090a140a0f0c0512010506090106 73
    0x3020170000300e1503022440140300c0348683c0360358403003045410041d0180c1c060303441c0c200d420440c14000501c2c1c407404510b8040701a000944c0020300b4010b26102c200660f401103d003030f201e9070340002e28a441142e0008001080d03604651080c0000e042c00307000c0320780715246480380c0ea21000c132020104518418643c2103800900004200940c0c443d0b8824003c0d1030301d901c11400c0360160054460340301d1903042800e203c1084000043c0940000019840c0c03c101d00046550241e04040e59216468000c4c3c42d03000007054009a80b000c15010381c5094030400026507510000e000103103044c00140b002140c40c16032040c00210112000f40c501e40d9810700801c48407200e844448400190b4480b000070700c1d4200a84907401000c65080c4031800d1180815601e0506005990302c241c00d600c9079000308007050040c01c041c0c03421141c0c0c000743d0f029000c42d921000d044080340d0b203080e580b0305103203401004a460500400c04040c6030210090046240c800000f411000c414490720741400304a01456500304100030700201c0c24801 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 789594595 1250 789593345 789593351
    0x306120304030309060f0f0c12170c091521151806040e01150b130f0f080c040e0d110304090e071403150408090f0603070804061a010c24 60
    0x982c2c203000b0529a041d12071000410f614510480704c6c00e206180d280c2c3d400065450388503181060b40d45244215101725002c00410524a51810070515a10381c2039002c1e020900f5107a0700c403d405d104014000090089070003600004002020941204101104110a2108a40c49540d560111900c0d0206040c0d4450f81d0112001d490f1601c02c11501c103105010310000d0f01c080218482c0082058221110071104000d448c030500030402114808030f005004010340c0d0309201003401d03030324107031061030f41c1103904042c5007843c0c6513a060110000400029241d0f42c0308950a201d451500c1040030380f00c02001e03412034200015a408908900d02c00c104560080203096400c01c03023080070565031501d80383c09009003d043d03811074508880364a03000515510b5040b161201c0c00060300c1d150340302c803001d40c000c1000e03035080413080080580302e0761031101946c4607a4141d1900380e000d1030185405030072601c0700b41c0310641c1403000c0000c00d8000d9902150b000d001940c84800500c4452880351111942840341d050151441c1c1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 789595845 1250 789594595 789594599
    0xa0207020d141e0304180222080a060b0922020d05070f080f010204080601060815042c0f0309040b06040306110c150114010c030c05012a0306050310020306120304 71
    0x10004801c00100c940d43c001000861883c030f00315803a445503101c2c2c061108420b6600b40d240846503401050032410019007040418003407090b4003050446a440034945070040300365401071101c01d02075002001d104a503001d0061601d071080051800141010210401c075607843c0d503086440300e19011020ba9049003c03502d40644e0749040c2c82440c1150700a216a030b0081c480c04541040781402680d05942070000545074580c244101201c800c40000d14490700794800b080511220385549c460498400405091100c611007042c18031280914480900d2455a20210204501c0000403003590070402048030045401d83c4c2420018880340129000035000d00c0c074062042900a00440003406101a2001030350a240a921a403400a880034891801039210714100c606466104a01410580307210303042a40d684da06d04e0310342c2400c6512032518200d14502e4004404075000242045000d010800e1806000580c184800300c1d4403608d46620035166076402001041e025034507800c00000c0289101c4c21262a55 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 789597095 1250 789595845 789595883
    0x2319030e09010902031e15010f02030706050408090a0b1305061b030d0c081e0c030a020f120a060503120714010902030d0e0109050913020909030906040f1a070b0a0207020d 75
    0x251042daa01e00811603404200d4101c3ca4807010410b10502201402d0305008007d44015280580940b1420381140000c00091000503402e11916014902070304280d07480d170742450184182d0340310b140c00260300010700344420f44a4881804140007a61801c3d2082622940f071481258104c3c2d6210122155034000801c04955810580d401510280c0040d40e8040355034840710b034034415050140c002c80c8004400040090b00b0051203800450300540c00c40e400502c0d044418000702103035082000c0d134141c2500d900043c82040301c100d000300000380404801511052072a0004518203206400d0002c0400b1842c101c1c071000100f082d44948170719034001c0c05a5000241b2820000c00f9410300c81c54140c00f180b1000c1012605040002042d80300301c144070300c0055040e00c40d0b020410701100080810406100400c058041502c40e44080c1000b006040c11105641e800c103040c1260640b00c0c40785200d4461400d01c491008582d001c3ca041d90001c0c00710000681d218200e0000c44c05115002030302919040104000007808 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 789598345 1250 789597095 789597097
    0x110c01090b070503060a03030c0f0c03031707050c03090112090b0712062304022206020d091d0712021905090f0d2001030b0a030b042319030e09010902 66
    0x224850700415040e03a45001080c1e441e03000a071038031508440c6500c001d02c0002d008945400006010b580d02d00c10180c200da0310035001e807400744c00440002d641000d048140f2080000c9040d0400030b103080440c24403101f81e042568038014440c0150411142c080c0718102c0754903990060748030640222500145161042c000b5040104403505031800390f10f000400181d2003c41d100c4401c0341550308e540104184203900800010f50800c104034261039410022061014400e6180d0700000d203181e401030945d840d0840000780c10000544e100180441814008642c5800f0351a030103503110225060808034029016840c1d0024011034200c4c0c2000180c005900d1f030456001005030144090072a120b0b08008000170a000e9480e50782d010042020066801e0035404158807122420030b0401890300207a010100c01c000b59031704205500594118030310409000c28001d52006200c02403c1c100c80c80b50a07880c104001507511812103503800e10310090010540c013014400c0044048820004000d4581540c4a00c565802 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 789599595 1250 789598345 789598361
    0x1a010905060901061d09190e06072705090403020a08041e120b0c090f15070210140a0302071a04050706020c0d0b0103020609030f0d03060302100809100b04110c01 71
    0x100780a042e0000510b0b0380f0078100f02281100b042440c00e0850360079030a00c640b616014041042d50000c100031410300c0d116a21900329044070a000810540c02d080c1ca000e800d02800304140c610a0a00d45106080d004c0c074402002c00b11141a50603103c59600c9050803410304600460003400e039200060700060410307098040e01c0c0741050b2002d410990513610451280d050b1a8204010001042800042e01c03180643d005405600805883d2040081882e0002018484038450300c10024401107201004d5082a00c0312450019290038419421108130520001034092170714142c0030540c00107101d0040001800f4100300032540d62020103007501b41440c06640310a858011a4014490920f82488910b014004800000d41082c5180002d0f401d5030280310307155100d064403a03014456080c0c15007099508000b017107082e128135900040d189003140304028000b46c50740514801c11422105205c2c061078080b48008010345600c200050b01c00b240710105000d01000301242125520114070404041019006820 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 789600845 1250 789599595 789599599
    0xc030a0213090c09090621170a1d0f0d0b04050a060e0606090907050d06020d0b060f0c0105010f060807030504050a0c2711071b18020904140405191a01090506 69
    0x460162202d6170001166a42e101d90380142801c084a104003c4070780722501c0009004104d01c8801c6030110341940c0b0319510402d28840007800e1002802c0031802c1c0c0300c1d015004c10b00216072048050000e1000541c44d0780781c80300003500e690701c001c0109003007000c00c0005406055104100380554120300c81d4464a0b404211203482c0145140740024151020109640c41910401041140364415640b00c11000790007103520410350503038a1070f600707200341da40f10040e00c050a4520109591407020580356400e49070103901030800441450018414560000000d65005141d0f00e4001183d5840703080041c5010890b400c05032626480b4480496020324031520b4800311108104154811003001000304100d40c4170f04030060344980d0a1000c2e8000480d02030f0b0061100304c3c441c142c01385103910f075032003082d184c201c00701100e03020b5500251030720090a03d8054002e83e40e49040402c03800380b502c0e444c1c0380e4450400c40100c0444901c0003000782d00b005030f0008811488072130f103e5640160341c3c48100a400401e400d6585034 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 789602095 1250 789600845 789600857
    0x3110907020106030b071407050f0105100608040f110321030a0608120a050a2c0a080d140319090f03030b0a0b120703060b070c1412060c030a0213090c 66
    0x10003440c014000d000882e80d110040442c50317a0303480c004941c2c2403200039110782d0103001040040c1c08070300100170030529240c14400002c2c0b64184807004071260200c81d44260b00303002903071041102081e054038240322615004001d400f02c0800b8500001e08103c8500200c4201c002c07500c4442c0c0308101c00c0c901540c07058542d81c60421520b51505142941e0300001401c50415603000c014007101e05120f80040c101d00c0f8964200240340040d0006c1d81d191a00c0301511020001c11600d4040a00780303411600d05c1d00078100503018000042c810100100286411101d4030340c1c0120003c042406111107280740b07a030000c00752408108000c2a86000031070301e182000d094002900700882060141740c4210007200311640c510255180010140c0091245000148061309050782c41e03900043c1000d05500404e241d904c951a230300c0d800390400000b0040c00710380518090240c1d078071006103001420009507850700980058051503c0e6600c220240b0080e00c50f0000104020110032030001c0c1c0d910144d0018000c1003800d032296 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 789603345 1250 789602095 789602101
    0x20f0604030f03110f070b0a29060d021213030f09081902060903300a0813030207030206040303030e06070801060504140303070212030403030320030402010c021305070207050f0301020c03071b0807031109 89
    0x8404031601c220041031340274060400490311441c1110080c400800841e00243c10303c0c100c0591040d480c041181e2419615050014080c101644006040f1a001c17071400e00144080c1040c20050703840e07203262411903034044076040d40025940d424041d11045100141250040b0044d8461001c40490301ca5040c2e401c0317a0403101170f41e5440c50450643d11500c44540d0740f03d80c03e595200e01c221074030505110580540c041c5090210160325084001c001031800394502040200388440124a0003800424100801004400612a0315448004c40742260840c1044520620861000030f09600c01c8800003544120300c5614030f0000b85010001d070040b28060b40b004c00131816404002000a80d21990200804a0400002c0c005601a5040d0b2400b01c1c00608000100381c640301d41c41044032019103089000d0781c040e600400c01454001c118007409a001e134000c3d8104010010790700d070b6078028460020440100c0301901e103100b01d044d40a40008004200403078803600d41c0ca0500700c00e07d0300110b641301e006460803800 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 789604595 1250 789603345 789603371
    0x411030103020d02210601030f02100305060a09020d0b10030e1002250302010e0607030b03010b1503010303140f04030318050414012d0e010501020f0604030f03110f070b0a 75
    0x2564120703034014046210000c4558204080030812007040d5440e203002e040607900c1d043e800c1180d076020f03610408413000d24601303a0040241c00d961540711401014100b0b01000003030b481c0c41a00d40221a040307140983c03140746c980e41c40300103020141125a08880304551102c034503940750b000801d81c1201241590f0204111000403070503480b81804a0700381100000ca140c45d80d600012828100714001c5c0300000305814040016070a04409a4200b40003035142d00700080945030070320403403404c41400c482480e00c002030341442c00294001440040e041c0140f01c02d0107681100c1e100c0880710070f01070826446a4032030712454041c1a01c0c5003001c1041d240c440340040460300e410f092103143d5440303228180018040e8079010801d803440048545140c40801d44000207404c0708102100000508403240c0a000300d0f40c1088002460100501000c04c00703076120303d040c400401d40000d5006050005450041410403c5400d901050300c5080f881c1c8403400b07400240309050060050442d03018060b050020b022114620380 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 789605845 1250 789604595 789604597
    0x7021206070315080303072604031d01170c130506030702030d18150c09051908100209180702160e0f07050a020c0402070c030203030406081b040e0708092a0411 70
    0x2e620784030345c030410101d240c642c0a0111540107a02c02050303221002c0b2185c1c1010621502510104d01280350911000c3c035220103c410235081c00d0082c42c1555003100681404580040d025280200c1c810300050358030704018a62481d00c01a20019154a80e24106031b08000d40e681d010250108071a032400f000b010842140c141c18442c02030b0008000c401140b403814000d0014041072501380300307100760310030b001810361030f14034241c0c0c3c075000c410035510345c02464004080c0c04c0c000d08400052000380704021940540c0d42e00107018184085019540102d40d6525101340d2514404c10301c00c0d0100151601c0005000900d5020f041c07142c0d2002c0c25040c000d8452000175111800baa0502d800983c0200c1e6100c3c4640c101503015101c100d01450701c1c440215540d402207801e40e8003d0f001900010118810400381542c40e00790f964110140c0350803e441c091805c10a0f410f00500980781d6402c101c09980490715a9070308101c01035030322030302080340b00703440d90f000756201841c0c0c19045065004505150f141c1c40c003590180 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 789607095 1250 789605845 789605849
    0x111206180a122706120e060c07120e0619020c0a030209070e0f0406030503040806100f03031d031c11010e03030a020a05071a060f0405090c011407021206070315 70
    0x9101a90250700403825610b10800300300c0d00c2c0180803c00c19150b00b020400220300010403058961900c0b240070610507805961a500c000d4400e54894001e01c02c1104070f010032681a0f40c1c0000d8201d200403680c62044409805d8400b03465030002d80415144200120841c41c48070300101074007201c080f05e00c0d40c01030044940d290b100207503000c100c03000010401c81c0540310300e0003a500c00402c206201910180054105ea40c0c0b0703007003034400307920202e8240003181d0300304400350304008904100c052482c41e1120b0203640401c0c9000082c100001401d88101c80ca0b413160008a500c00011309446220900980045140715456085c800007161256041000c801c103110b00011143d040010f18035655845141a01951103801900c003001020015440070420100f180e02d0580312020401e0242e00340340081010604007000300510980c079000c1403044091001400002e0750f2030a003007200b401c0c4c0050001602e54010408003a41102075522010340c080e4001c1500c5e1702c25002500e04000c11804640d02c1040c80201d4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 789608345 1250 789607095 789607103
    0xa0e06010e1002070807030549090b1603081b16020102070f1701051e130c081501150e0a060513172103070504030609111206180a 57
    0x740e440d07294582800c4036a00040001401225119542e52460360700c0c06541e0384c010346491308421030604032403041a80f00000c08840da80700d40d841e440f241440074051108400520201402a42c4108803507018213003080051010384a001d8503146031403014241010741c01012000200c1000c0007a854094003625402100842200c0724200005480c400d007005100702400d074190311501c0030000d0041110071031240500401d05543d54001c40320019a801d680010f84880c041c41c50540019044525001c981c9500014003804a0701d2401c940c00c10155001e65504440c442d4095400c0710110401241c1d000740c121303000b03132452542100031418110303a00a107802170a640010304540070001240b1500c0035100c0d001c08201070102541da603c0d81b00f4241c49410582e0041c03a00100364480ca0540c0b04400d1032000100c80d004cc618520741203c0c000c1152055000041c03c0d00d41d9031580c1001e0010b00740a1094407900600003005a10680d410305966580c12101c0d214520000322203221148000710b01d100103e980 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 789609595 1250 789608345 789608357
    0x190305010b091210050903041406070206071209030c060c0506060406030c030f061b17070c05191722150206012102090c09040c08060f040b0a03051204050a0e0601 71
    0x300c1c10009000075158140c24030303120f003a1981604c1c04240c0300c0e9900800e0350700700850380c03186002440300368031501d500c12602c03401c0140f00000150701c1e81c00844503a0380e4090083e8605c3d400d4183d041d00c0c004020b820180150211100214040b80c0024a807000c5502030802c4031195554142000240c9849000040242003803800801c0090806458012014816840410704840c0c4d0003008611950f404025000105080140c0d200c0499001d02d03941c20958600c0e10a11a0180e0348400e5512003041101180b43c1003000141c00c10b001c405080c2d10700c6540c2c1c06503c0c2e5984c02a03294500c9044041d803510205440301c20304005240e0392207080c403101d40d05c11034000e07103416840c100c054294515045268800d8081c590482c50040c0d0303400030094460f00100150a80711101e04080c0f00890340c2032020300090000d03410a118107540c40140001c2003000854011900140c20700c0810410055540014290b100e450181e002e40c0003004080c0003960030654529040740e40d41c0400c4900c83c9401d079415408112 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 789610845 1250 789609595 789609607
    0x201150b0f040608060a03080d06030b0a0e0703020909100504112b0308070e10080403030e0c032812020609191509110604140916080a05091504050102190305010b 71
    0x10240d84c4141d440700c0b00a020b20800c0760740307441d0300d0250791005043d05801035480c0401d00411180005031a042820008100048644108160759130f0200d404044c0c401d05a250002c0d0380ba400c104080340d20140180014046030a061a10544050321514454030034201034150021802140705000043c0c04881e46150444155450980321290060b0aa80801000106804040d01c80e038101c4003856056558549041c601800e00404a4803060107020941d0443c44141c081035500040d580c65102d024140013a8181c0d490b249501d080b040010300501c0c1ca0102648450b030b098000c5107051296860300251303800d000203011041406451401c0040c04480b10007484600820a540010fa03001d11510212000168603000508543c106074000d080089100807901d0703650420740c0019802c001441d5039003040c0d80c94201d02502c0e0703400c01086104000da036000000c80c410010045a040d00c00072500984142c01d00342400d034040d5000303d80744014160380a001c01c000511a00c1a50304a4110030360090400c4 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 789612095 1250 789610845 789610847
    0xd03020a08030709050616061a0604170a050105070f02060606030106050a0e03010b0909011e05040f02010513090507080703051021060b03100203060a1d06040b1206070201150b0f0406 80
    0xd00b01616040800454140100302911a00000d03d054500d00307845025a0100d0301d000720589405c402c280e20751000c03030452354007161030340002d0740e06846000da4407510104101d0016481d240700190041c10940c20001400311868002c0500b80c03404800d5402e40c1c81d02e564000900120784000e00c61000003803030420040020700e101d54802c0e41d90b0000200089003040901000402e429400e491a42282c2d6403045503265500d00020b8001d00e03545441d906104502e01034035211801c40000c00068144580040d41c414240f91091966000c1c0c480210100118109568000e21500f011500076011928040c00300b60700e84642200780d02208c1c03034011400f40c80c07031280d1021020a800c101e01211219150b40050f00181c0d018841142c000039480c8005859140440800044100c42e51100ca1010508190b0808007c24181a03e0b84200140c8012176000318040210710f8003284080c0300c0340580210300501c000c580d410341004400c0710040d0000f40200b034682c003049031a40b003001c1c01d03810b08540c200001c000c01 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 789613345 1250 789612095 789612097
    0x803070302071a0c070e01210807020f19060306090b010c0c05060d0f02040b0c0c0a0605030429040b06030c180a05100e0403020d0306300c091103060306060d03020a08 73
    0xf0403000d4500c40e0401014850b41c518202c260b4000d84400902940144013042c4001c03003403d4034407411000e0070f0860205840b40001ca00c10a0400303401211a9901040d2513214000004116415400e41d101e0056641000030010421030103200d10a80c103003044054030b5841140c0c1a206190050000e590480c0b9003810400b096000a0045000c2c544940d05150859400d01c0076000400d840300c03859990f02a03c0f9803840c100305544034400c1c40f440d5450028443c480d0300c08140c81e03001c1da00c00b001c01121240300d00c1d09075120925000040394084808200301c1002281801c1c240196400d404981030030001c40d08029200c800c0c2c04d50a50200f00c020009902001107400c00d81c4c0064542c0f03a031444040d11218031070181d00c1c0480301600560300001803541203507418843d10000b802031100707108900103070682021003402c0075a0400307803055640702d070780d01841003030102c0b07a00404ca054400c1181c004030601100090b01300315106840780c064000010098140302e80c5100036190305074046c000c029525034a1280d6 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 789614595 1250 789613345 789613379
    0x191208040203120c07080c0102030c10090219090917090625021809150c09010507020109050405070e030606030c0306060d0302120d1a0a0f06050c0a020a0906050a080307030207 77
    0x1c5440341003070203c400784564005148400e80c000180980600300b050152514042c1e1006504550041084001c1080c01150301000310703e5080001c16084040d000048190b116421000c05e0640c14003000180301140c3ea00103c0d5091048803200d0307601d820480c107100d80d0700408290303542180041001120241d107901c0b0000e84c01c800b1003804586841c3c550003007442c498a58540d80e0031400d0038400d22600140410038040002c0142d0070b110302e28a440c0105204a01038030140701e05001000c00c000086a005000480180c58051702c10000c4d0310305410300401c0d5045503040203010f4047e01003c20f415090100310203800c80300c051300402032030b12040305200000c00074020603411409044200e0090314440d500070104c4041485000c40c0c100401180074441150388609288907120051003003000e0400d0a013200222a01e07420442d4079194508180781c02c1601c0d44070025800000c00320085201c10310f5900c9501512000da600000c030b1030301d0780003540d6a4400d205026001d82c0c0454020095200c0c10044415 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 789615845 1250 789614595 789614599
    0x6130317010b040611120406052b0c110a021c152a0e06030c07140f030d0f0b01020c010503070e0307030f12050708030c090a050927030429190504081912080402 70
    0x850b602e0000c0ac003141b9003008000c1400c0d80e890b50861450305610180c440f220300405400340180000584c0091000c5a6088614460030384800c2d994050241d60750342000c042403841c4080c000d4800280d018504801c1078154215000030800c0380360001c91041101c01c01e002c03400ba00a034a142c90340741580580e83c00600086400341c0c124803820150540c2840102201c9054600450302c07111803a02d81d00586080443c2d80c80040c2c9840c0c11214960b900085001881c81c007030910503640e40320340800301d6024402c54202501440f40c11000020040702130b507040c0c0214001c43c2e0901c10004405821200c0d40300d01c60000d00781e241e0900214a0902082d0001c100c018401880404150385d03480c04909a400121003841003d94410703070228003045880780458200701e030034014500d054101801102a14184c0141400140540036640074508542c000c5505440d00000ba021806081d89001007003a8081d000302842406072014003007403090451070104002e64003240842e03041c0a0083d0484804000400030303a = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 789617095 1250 789615845 789615877
    0xc05040203100f030501090b130f0b040305210115030204051e0d1208060f01030c051b0f0f07080d030903090e09100f06240206130317010b04061112040605 68
    0x1000e1100e040100010743c421000481c021f041810081d01b075900044c00f6030b14030995075101703000282d1407a0050407202d6001001d844641c42d2030500711114010a1b104180100c3e201c0d81e040f0304200340c01613070b80c126810340100090b01ca821030011020b80c0200c0c82071a801044a011420b0011100c004003040d00d8809440205e440c9996240d10842411120851020030031401c24412141440050740c0444e410030b007400c0c8607a07002450000d180707100c0c0300f07920704641003840607000c41042d0600c0300036401c00341c02080b120120914801d550321201d407846098145c0c8960380400194501034000d0848454040e1506c4040500c0c1160560b00d0842c01400c03680035010b02c0405c441c1441e150f00c90704c0514030344064005101420210b200900c1c208045000b01024480d01820000319070028146501100e45189080600302c2c81c941601d44030b00f013560001c10002d2090000c60080b0000c4080c0c002c4a00550b240052a084c408243d51214503281c450038100104010078030003540500700900003500410511 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 789618345 1250 789617095 789617099
    0xe03120106120f11030604140405030319020c0f03090a0f0815041103100b03010b0103050609130302120d140711151b13090518070311040f0203040b0f0c04030c0504020310 75
    0x20012200007241d07150a418000c0180000c03407c29108444c0c01c0c3c1c0d2078801200440c1001d03200c09a03680401880909410312901241c191400d00e6010750700f00380704078422a05c015071194501501d130f4004403e658010a504000025800d5030f550000c3c0407a808075000d41101400200c1c102c0f803030032006109840d0114002922410381e1810000d180201e20380801c0015030003104002c1501351003120107150304141c203200921601d80e40300040e550f00311a404950510301300f01407a003a810000401d013042ca003000e008c6052640070300b10703404c401008250021850340e65501e1741801d55110040c440024a05e0b4040c84031290510b080d02c200e150441e90614880b111a10000c030511100d900c2116101481c00e0794201c2001060706501540740c1244a002e228003040082040f15030382c1304864071019001565001c81e5500545860340400380094a03400150366a01d80390074010003815098031803006039091500018404207000c0280c0c1e0a81e60f00201c0012090320341402c002c065040034013900ca204030b000d500 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 789619595 1250 789618345 789618371
    0x9040804150e0d0302150106020c0619090e0c0306150f09040b040605060409020d15150309081e0c15061008042306010f050f010507030513080f100e0312010612 70
    0x210307070300f5035103e0f0f402003031601440d0040d030000f4541a4064419580107040c41c591a80c0d442040d2001c1c12445100010b00c02c404070741c11502685164000955845038105000d00e4a00f420004d41c41000260b4030700c00b40c0034a001c110034007881200c1c1d10510400007032100302c105280c15003149000700c0b0700900118945d51160300280c010b90065102ca403a8541c0007907100174406142c040c03200155802210210514030303080c441c10031502c0c20090350080680d1001100c081000b9030042c1d4103005828a40c143c900a24209100c4040d8000f80603400c01f0f11505441c00004404145210311462014046400f800c85d0814252034400b0b01a00480e00285201c003100207a60544090140150a080050503194501803092901c1c0c8584d400c064050000c0c3d8102000b06d0360480d0480d0940d03a40361900c0c554a542e46c0c40703052a40502608111228003415440fa03003541c40019641665201845c0100040c0c40010300040d500e2051002d2000350b0100d0000410005025485240b41001c1020340400d02c2030a0108c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 789620845 1250 789619595 789619609
    0x801091d010509010e0106093c020a05181905040b030703140304061b0206030c0309010902040906020310120f14030d061e06021621050f0102040306050609040804150e 73
    0x1540d004280e544126144006009000703440c0207110000c0b00301310780c41580c5a030300111845941a5150276900622180301e4060958100b150007500200444d00c400c11076500a0150b4085005c465614440303c0250340c0e00c5c03524a000341c0b00c1c1210407401c1c0101d14500f01c1804082c0c40810a240d1380360042d8000000400c035074039284803445040c5130281d40e90304d080c007402810041c01c4013414170350308084041110040e107901c41100e1300301d1012849952640c0d11000e501d4007606142c10002e4001d8146108002082540c2d00594041c60480a00011160b2035029100103218900c50140c4035545011710400403613081080454044150010340380390071500c03002d43e000e40d811070348103a00451523001000c1210581114038006841144080c040100303560361000316508080c06070302c0a81c55541c0003204d0200e5802801c03003065501c2410795071918240410342c0e0003074201d48003e9680034100400914a0700c0c0141c2c181c0d204591041c4081e091074242040782e6018401c1801d10001d00c5000c820a171038a43d40c2003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 789622095 1250 789620845 789620851
    0xf1c0206040b1b06040f020d060e030c06092a0915190509010b12041202031606050f06010e1e040204090615030b0616030522060903060b01020d0801091d0105 69
    0x42c4401d652250200390306808020001c45050042d005070f414480040c00784040d018136550100c40b138100002c52418144014914007004202c507200003e58803000308408100303d441251414246c3d000f4000604107800300d01d10f0848080268041d0f00490001490f248102c941c200401c03d4617010501e045201241502d490520742d41c044021000003042903203803482180380509034404e256401d2100c0c550340001241c101400040c4801240f040c4220b01600c01c10544420305005140b0103020f80305800c0c00c81c0240826a4900c60043c05440080c0a41d401011004c2d60b0200180040d029401d0705c003080c400d41007941c0070b815030103602000300061000841c05040054030307030351140c2070345c0000c1c802018048030701105c40140150300c18404410302e525485803802006400d401d0450361094001000c010038980810038400d00c40d140c0328041801c9600c2456482681c1c49070500300034003d403030801a40d42d03011541410700001c1d510401804401c0f0940c0204503c10108031001725004100036030719003550811 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 789623345 1250 789622095 789622109
    0x301030f050d0507031b020d08130501020106330c051e061302060913180c0302120609280204061418041a220c180b0f1c020604 56
    0xa4030150306011050040564510490420510b00b52050380c0207441c007511203905406005600700b2a0301503440301c04001d1041a4080346081c0d58040c0c2b0702c90301000304924012140150700e40100490800d0300122040950030b041c84d404940f08a50100c81020081c5c03985680f000c1000c01482900080d2040182c503075641100101c804001c01500c0c1c2192038200003c0440c441190f0071501000980c07584002c441c030008064907000410221408204042d1104148000721011421814024401080b00744400d41e44211032100c01c0f4030560100d5950f0b44800d0303442a0450b0001b000c002034144002c180030144140d200324141c3e810790f280e00014101c403100d0f403103800b05043c8044115018074003001c10010758010031800c0ba40605058032010b850300b007011941140548040003084c1e06540c011410f0119609036441111007140c1c5160000f41c01e2000d10030503480440085000007000c40380c0c010040811806030a66100042c0d80f01002034620766032680160b036183c44210000540c8640004201078002 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 789624595 1250 789623345 789623363
    0x218040b04030e09070c0308091212151503280207111201020c0705040b0a240f052110150503012105030d110f04170d02010b0307050d0c0803030103 65
    0x428103000d41040d480c0a64613100b035a10100300191a41c0180481c0c048642600c0c0911099032803480845c0381a940490b2411030f082c000ca4650706805a440c0424032502c8414800300040074040b081c00607035224007918001240c4140009650344c00741505502d03000180080d0240c140007070038018000c99100d0036040d564807484c0400301d002803c25168811340361860800071807804040e42d800c1c0e501c403002801214461503c03110324520a655928880c405080c02505409051a64041c8241010008841c1d50f010a4212914054650040c4203a5070701804030512a484800407500d07032203407000000d10800800e1045034001c80ea10709086081490040c698850554039414003e19174141000000c4011459041100c000001940403065071900340186402241c01f0280d0b0b0140b110a00410b480646c1d801808034002600b00908130540d0b112400500581e402580300650403030030380700344003013094245e0b00c040310401040c10075044102c2c0e00b60103590240a03054490710413600f158001c2e402610903001d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 789625845 1250 789624595 789624601
    0x21030a0204090f0b0f0108072a021c050c01091d040311031b06010905250903080a1d040c05030117010b1207060807020327010e0301050705031009021e070218040b 71
    0x40034524030700d4151003401c1807c118945920000c03d444103e0411700ba0b2071030b84500d0561104101702503090031990042407501003e0090389035490070004280141c80384c1c03080740c0c1009101d500804141003078039829030021558008500c512a59104040d000b02c0c01c01c030034507040070300743c10b000e1000e40007000c1598407402607030809210440c90b110041e00f0280d25280350006209502c2081542860440d07218040340e20034812080d0b041c2c0b81d500403940003a000c0f450001e45604810741c090110318a03007c00c0d0340310207a00320081080c00102c8403007854080125504100501c032401e0440001d01600d100d0500228426801c000410b058124040a4044c00c0d88035200c00d0003402c1e001100103900c00c07500d2009605040d10915040840044035000030550411640a5050359106145a04000346d02500a106a080521009110b94000c8859400800c0d41e254045500102402126007c148681080030030f1000f83c10402a10760100c54103ea01a1a030300c1d201c482002c1444103248110f00a41c00210701d1720f = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 789627095 1250 789625845 789625849
    0x5120c1f1d0c1807050706050403030b130b15030c0d110901020f03030906070804060e1b101809050a140405010f06060807050a11070f0b040302040e21030a0204090f0b 73
    0x890100c40e10381590021440780d01d01d500c0740e24040d00803c240c46007520650b280c49609540d82d00c145580580130034200800c1006158040e0401c802d0590180c42e02103404c51200640d10841e070403002115440b0b0b04102c140c1c41622140c50181d5002801022150300e803140000383c0004564916042c030288950201c0c0018840d07806200001c55042020040c41c5185060080300b501c500b8010300740030522000e6008181880b0312503001e07030703030b404004000ca501d64029080c803840d654261050880c410101106810781c01407192041004400304984024102818203a029003d00b0f0300030f01e03012103541d5034ac7c02d5108031409110308500450081c1e00020700c0300c601d00310744001c0d104590480c1d000e01106505105846501004607000e0482c1840c000c0c40d041224100c280c00d0409a902900c07004800d10008100c20008100400450f44220ba0070803000b504488110b854105c40d6280729401b10301d000300c452001000340000c5510410086006140a8035400d0103811102c52011400000303030f68601c000024 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 789628345 1250 789627095 789627131
    0xb01020708011d01060e10031401110c010b1203041d0c0f0a052110140d1b090f11030105060f0d0504060209100e0306060402090f0a03030807140705120c1f 68
    0xa4440306d80b005465250107500400350243d14403008240000b4040452907441080d40800c880c245092000307983c3d4003502030381d80d01804850500520810800d07003c030b0309815000013201c00710340780c90140c200180039000207001c5514004181c103a200e0400c016610118080030300402c08034540791905601c4403885c410800c440001d449100081d00c101c40c041c8003a2250070380b011001c83e41501f144503507403071510010600c1c258190200500e2008a060000d940714226100700c1d099440701c03007040180c0e1407036502e0801552070300070501d10016410001404641405002032180300e09180c10b15103003616000c09441151400c40d01614160ba021444600c0c80c50040c5001204851a25190103060340c040d000945405000d0556480b440c1d00090356403554560a800a8125074010102600c1d43e50300e040150607400c00305c2c4d134000020b241030340800304900800140c0e0600341d0084c000b400401588888142164012100c3d8901c80c45000c0843e0102c00b0380d11919920001413171404200c00000900d4006c01e = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 789629595 1250 789628345 789628349
    0xc17070503031f0308190309020d0501051b180f030313080616030504050601140a0801140a0c09030f0b0a06091802040e071212031107060606300b01020708011d0106 72
    0x140f04480c2e0007000440c20b41c009403443c4400b103078100c4070360500c03204c03090b0010004c81000a41084d03040d100003040c803c4c1944a1840303200c41c0b2031591035000c16a00d240c5014891440502c1c40f803088002030580c141800088030702e40220140890749001d00042c00c4040c540e207107030304c50201540b05108110051850703d0840d0406102c50a0500040c01c041c1c0c1d82e1500c8810501a1341c03c1d0b000d4041030b0503460340d03500c0e98510007031800070020064486040020014070008450103280107003009003a0300c45030320900b521400c403034104200715280700427a07452440900c80600700318546911048045003420451040c5e40707070f0400b000a903030851046441840191503400640380c041d90000c110800081712004051450b041d40910759032441400c1000030b40c010856000046602ca13004103c80d400c02c50310b0303803001c01a50801c0d2211800e1100d025124244880d010b44038400750300b9000480380740c070fa202d42c1003540780703103014019103080580302c40798582190000001c00082c0012a105810311240a02c11400 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 789630845 1250 789629595 789629641
    0x5070504060b09010e0a0f03050a0209010e0906070309020f09010b09030601150c020f040f020a05030a1b0f0f020f10140c0301051f03022101080d021b010c1707050303 73
    0x304a10380b10070005107000c0c8500c0103040c4004102c1c1c204465852840e0307000070704655000c1500c02034490600c03980e0382102440072801a4070b010000304030314214076409449200b169000700340d1541c0f01441100a00000d981c02c0382c1101001d0902109682d41000081c080d103480040152a1a5084101860300106030b2112040800c11000a515141d004191061894060360910b14500000c00480c0c0200052030f1a10142803001c40d0402800e9070000046008030920310741400164000c1d20518041d0340d02103d00c40203cae144c8040f0042c03090146840040500090040da590744901c412528182001c107a209100150790300e1622240900450241e070f00040c0c3c0401c82c50644d070400340802d0350314000d124580c2c0070f103503801d888040c05403190701101d215881c035500940e4141c400c1c4001c01040d503030a004151490107820107201286c0d200054429010126045a0380f080900740c0041d1451103907803005a0700c2680e401604681c084d40380c8010800148203000840e41d034038202d804040341000801e0885 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 789632095 1250 789630845 789630851
    0xb03060a1506050702030a05010f05010305150105030a0b042108070216142b030207030c092d020405030114090f0a050307060c1b050c0306060a08030d1107140a05070504 74
    0x901d600203084010401c1e25124100155a100300d800001d140ca81c0c03100c4001c08540c00e1024190040145420850489119000b201d1000e003c0c90701e80988030009005080c0c055001100420200340010042c90b0042e005090b400000c021074420098aa8140b080100210301c0440078091815410800c0303d441401c50102d0060490500c7e503180e4400080c07032401d6211301d5900318450380c0020b0002d031544007a901d8040c0c08c1d00907141d5280207519074606e84002c0c2e508409800002640109900403400e01c043c61420004907800d52141242c0881c1c41640300180c2241d0a110120b071a48091040b10700c800900c11860355545000c140709440e0000c4004440850b41207040304c000001d0000040e90740c0f107603000e88007190071001c41c0011070300c400c0c103c8007204500d0045204202070020204142c0072005065090f1011946d80d4411b10541c80d0440c4580120f0f03500c208130382807204015030310071103c3c40003d800c028944000c0342c0707900c420410240900c200581098802da030410004216140003008152424 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 789633345 1250 789632095 789632111
    0x3020703020a090e120a020c090108060910050106083706030b010510021b031c120c030203070905010309020a0302040e0d1d0906040c0c06061401030f020408250b0403060b03060a 78
    0x42e9100c6a4059019010f408086006c2441c0e600074006588000800b41071001a5a5280c2c0134a07074500b42a960510300b40501c2c0f0503e500c107020341c00b64505a0b416a110030a82d0344520000000000c040d50b66043c010441040b01e507480d0b011000303046101c801032130011881a00b1400c0590600d00103070f20040c4580800896080301540220b40c04422400003103200001e20085400f086c101012082ea00c2c09a00421240420850b000780c0d0704610304030420304c10415210f001c00250100c0c0b00a903020004541c8c445001c0001c3d6109070040300b11184007401200d0010b549038086801d41f0501e00c1d01c40e60ba80c100c40c0c26001215401103000c5280007520b1300e84000461400702040d0300a90141c4030310301403034030740101803201402800900103e41c1e100b042000f070756640d404c1d4074840c104012442400282441e101c1405503640f0b000b074400350340c414000741055400c404c025030039000c0c1011144617500305040000540003034400107030000710301030000442c4103401c10003054108a40105a0880c5038502560 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 789634595 1250 789633345 789633371
    0x6020f0a020f060304050316061d010b0f101404060509011b0803040b150d0b01080717030d0222090f0c110604030e1503041208060a0614090105041203020703020a09 72
    0x501480360700b050b039065999440d14280607041d03100b00e100d00c4503010041200301c3d0400585034440c1110348180d2069090454004048a00765a181e02c10542d000c4148030154020f032810000d40103001080d1704040c03088000c1d010011045401c243c1c03024012620208403c101940c1111448a03000408482460040546d80e0340402500010b8005090307082ea0074000345010398030201201120600620385006000c42c0d140260403110f090284001c0c900500c8400508181d1709114a071540a50344007035421f00720240001c0c002900800c072000e06036130310000d0f00000c8131640d105a1000c0d080c4043c02080c01010b121440054410f441c1c2c2c41020002440b0710b034400c02802040d6103400c90740c14a44800402c6540c0d0002d4949540c0602029107000c00005000402071164164504400305031911103142d9105401c01000410a101d264003040002418070700220060000313000144050400354100364030ba4000600200101c0800c9015130302030f103018030941c50000c44c20350080186032414040c2d5005525 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 789635845 1250 789634595 789634609
    0xc190203280516060605030717031b010b060301030f0c0605070503090103110f040905011d070c060c181712040b0d1d011b0e0603010e0711070e0c0406020f0a02 70
    0x4010781405081040841014814001c450001003c1015400011240d0074804010030345032140a12a10614400051014024040320b541580c0c80307018508020070705911714000710600700c224900b550303200140c0e1403555554025502035401024541c03420b0443d49090051181240c101ca401d10000340a64400282c0c000203d5203801e50070310340032890064100c6c500115000700d50340101d49250104004c104460b032a44040c0c101d0781c0070001928140c3e40f4001081c0c4110081d50741400141c8100b0122000c00c1e40b43d000341c0e6000ca007134901000c0801c1e940b01e058503020501c0d00043c2c0a0501c004040075800030400920201050340c0e40b42503c0c1610344407410302907100380c540117483e00b9181e4003074664101d07081e03a14503110620240248025406503502071003030002014803501044030801410041d0604406480c1078529240d50b911807a10707846d00a65580c10410744441d002e104c5c64a000c80c80400100c1514001d424001e841506c5078145003000c2c4c00c0c40c0c0c990105000b81d07403254101c1c40160b0b54800e = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 789637095 1250 789635845 789635887
    0x506030105060a0905040f0c0e09041a04110303070309170c0325031a27060601030f021b06100801090506130507080a1506090504170901020a0b0c190203 67
    0x40b41c1c50b5603902400801d90f00c80b5226440f441d4417610342010b024902c025a0003c4000342c0f101d0b6240d6120728103210410042074030139100039050010140c85081d0004596a11542242c02070911131049242800060b1440d4004402200010308090040204080007044203048e00d130420060001d0b0700c2880d0109603245c90401011013250750000349054142c9540071504059500b002e10744400740c0c102244000f6501050324007240d00c0342410a082846110004164542001c02000d8801a11858011000742800400841c10b00e03a08000345401d191000069901134058400500300c0c600c1c1c403a068600c114403640c8901026418016407a0004101040d01980550943da50b0f40c0300c400d460901a02c0d081c12904400d80d60703c1000011070500030000c0b0311031076803050090103100a50f100e110721025902c068400415000000c0350b20800010030401400d62000d040c4100c504000c09910f40100d0003000b0b641141e0034a5001032100204a01e03442c0c1110310380f40b80d000079840c0001010702014980d40700 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 789638345 1250 789637095 789637099
    0x409020d06060f0e010819332408030f0315130c0905060903060115091a040e01060e030c100e130509010c08070c0305030603010f0203010603020904060e1006261303080601090506030105 81
    0x42c10952115803040c487c98083c42400d50310392607230100801004001c02e44000300c8640040d6002101d03d20740c24182201381a121914061170500e000c11100b03401da504046c3c6180c81c0c01000c12098412a141d5241c2440b00b441e502001140c0c0d0450f85c10017804220311a00b005001c1c9d02c040005a800703840000702c803411180440c0c1c61113071003040d020040320b0601c01a080581170101c174030104540a0407100c0500240c40a5040041d02641d8445060f41da1480240c002501900440c03080e040500d0300d402c1401c00d18046080000311480312400099001606000e0144c269503200c09100c9a0902482070300040c51407402d20078002d0030703c260058002c0814403002401c001000002421548003074208015044010b0030654495844500140194000710081f6014501d0b00230700003000e0b0445100c1900829201021800071070505408036203009001041080d80c03220000f00c08001480441c410744180c44036132860701c031400c04d441d0040241201808050401c40c80311018089030307550801b128119601 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 789639595 1250 789638345 789638363
    0x80c03150f060c12070c0e1311040e030a23031302060f1201092703050d020a020705030a030206041406040b06010309020414070206090f0610050409020d06060f0e010819 74
    0x1a0000200c0c2c903c540c4207602110b025a20021420035610005091410310540c4000b5900d0381310b003204001564201c6520074519110740010011851020716402c170100d0103840460080780d180798582c519840805c400000640c101e95440c040280d41210300d0b104203004c1c00d00f6103542800041584c032841c04002c0a40b0900c2c0008074115504e851a04071078400107510710742c1c2029a51003950390010b2900050544c504c25405214a411b400300641c00c41038640e1549840b41080c0da26017894000790024550281035210b41500410256010411400d04921030360090106252502e812035600d000030740c1013540c50740000140300000e1508110207510280170310300017600307500b00d00004000d444051081d0b5400300d1040705104000d603000c113080340f04d00002d030b04440d281000904076036665901107034400381c1c00d81c841070300744418600b0741c01c01140c4c030340001c280a00341d490035281c101c103c880c9a4480681014041d000304204025125110300510042000d8807000301e54004020340d0400c00a0010710130f1720 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 789640845 1250 789639595 789639619
    0x9061d1018030b090d030c0e0d120917070f06090b09040c0c0b240d0f02090c0c03040e01140618211504051507050712090e0403030c080c0315 62
    0x2425810701d0015a0000003040440c14401c0c50542c8424105100c9000a41800c0e50200c8040c0503019a0500d40b10161054140442c2a100e002418404101d00800c00107400400601c2000e0f92040340085180c40c0050968149404c604510610095100101380b01807100c007000101c144a040e034410300d00a03100441e0406007080101c80300585030744002d03d4200940140400c0c28808000b2000202c54908a000040700f501d003004000144d07404010005400b4104100040c20010701039500701d42c059444504041100c03600600356045504040c0c1982c3b03241c0300402142018511504001340161405450003180403d07201c1044204020140076050480781081410313001c5101540d10407400d415580c081d8510030510300400c0301514191003602c103078041c1e8000d0003541054a40942480c0e240d40e8a011420f50700c818591510390703c1c2d80c00348802030400040039030f000e1012512480c480e81c2c0014401c8a800d1001d0411030018240044104040c4200000b4008219403403250710011207a50368110 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 789642095 1250 789640845 789640877
    0x20105070b0c160813051504091d06010e0403080a06060f031e0f0c1404060804140115060905090703201305060d0905100504020d0605071b0309061d10 66
    0x3c40b81c2440481e414007a0003680f018840301c0c2d005400e0000080c035a058001d60744904005500c01030042c40c0d40f201c50100401c0000341c10950001b00c5100180d000300d0440185501c541d420300809a004d481c500c0e00c2c240800007010307402458075511424101c2c040120b24108400100155000c820b04014181e41d0759850503150403811b48402e4840c5a80f03800d016240894210b01c1c00342c00042c2d107000c003084d448000c0d446003162880c191800c0d9403080d52103003a1031b40e0b940c071200580081202c2955095680e03030f0018690304070511021020b040d00b9290488181d190009010003000d005080304101882c0414030650484030340c3c00d420760384c40580721084c2c69203102c42020500444983c0039944c003500c0050038802502c0700350020f0120500500036a00d610101d104c2183c1a14801c481c002d610039445c016580000305154840d40c1c001e26149002400d6003410055a00307880d110420580200342d004004215003603000300d1036a41c800501c40351000b2814038a01052010f00e0b02084101808010002c5040702c07 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 789643345 1250 789642095 789642097
    0xa0e010f0e1f0f020c03030a030914060a140a0b03062707080d02010b1005041e03080307110606040b01050706051b0a050406030c2c0102010b130b041503020105070b0c 73
    0xc01000b001c2c5100700d20301000d00070009084886090116508039001103d4600109900f2040000a006107107081c0350001e08400400014204461554038040841103030700040013440d2003181915000103500d50142c056241180e8014041052282007103a0301c2c1e02c9460104503c0d4006408210f2820070112251080102601c5144482d100748103400c000640750800040390143c07400d81c0c3e0020000c4401c100d05110821000d030401c3c0c170210f1410001000344034581c41003141011803a4000182c1641c0f00d940b40a0158400c2d11008002a080c0000c9000d1242c2032000c6500110121020400c0c900f4500003e440c81c02030140141125503940c0010710510784481d400c8160020203801c5a6a61041402c0a051a00701e80201d10000c1c1c900250560a00d00800d080008043c18088481c12505d890781c960340480300c100009811552142c1c401c0040d40c0b1a00807a280c4400c031010041409181e000a01044801c41c40800454440509003040580d0f0000c0c01c5032900ca4028030303113280030341e1220350035825 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 789644595 1250 789643345 789643367
    0xe13180b06011101150510090f060e1305090604030908010501061205040c09151a1c020d0f1806150308030c07170d02030f0f0c09040c020c06030c04030b07050a0e010f 73
    0x55400d0401c00704052441c9090582564000c6030300070113847c0b00b08011900e1041c1801010800c0c1407081003803281c1c40c00340000e05407104c0700030121400b15111000b414191141902d40b041181e200f00244020507030850300724405044e014008000d990724140340142400c480c4401d0004850352800401c0610511002040180015200074407507407a1045402c3c50300c20300d612616868031500c0c07191a1000d840d4004640a0340364119a01d030301d5403941c198410095101c01d400c055080d6841100c3ca0300340c459809259a000c0d0008071200360041203040a6040e06e822140c2c440750704054050130310025024400b669004068207098980301c41a52404440100e07162009140030304000c01d044c42c0d160720795001188078100e071412019113901c40304640e5490150656040000d64014000d00300700b41000d0b4828000d00c1c001d441180d07402c6100401140c01944140c4030100900741c002401d00034003e261541c05e0300041c0c0c5281c042e00c1c0c0051000010003202d10001c21a04002d600b80210360361920488044107 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 789645845 1250 789644595 789644627
    0xd12120b10050301230108160203070c060e0112060f03031b0c121a06031e1608011b02070b0306060a120e070311150301151b030e13180b0601 62
    0x2803071164014001d4001d4009200d005500076007544007004000d42103007504c0c060881a110100c0035111900c10003401d4501a500c642144400d010410218a0f613503200c900420f0036880d06031184660800052032452241c4101c59907504080f0108031140a1b104ca00d0100c075010b25007a504d104001400e07941e6980e4144000c0e119079045000800d045241402d0901114800c41100244404080c1400d41c110000c580b0181c1c03541100305000d1013141c00d80890261000c0350410b403014104a900e00344c2c00d499203a0800e8500341e54a41e0800c602c1e00256184100c051101e00041041e203161130302c050041d100c001c0003076005640125040504500814011a140c0b03954013041c802c503504503010690b1420140302c2a100550601d040d84482c7c1008080044032180707a14540d4996820940403e03402544150b00c40c0800000844015480006540c400666803095890010a0840400700100462605c5070f2815041c54018007038900c034841010081c4459108400145560f900f100603540c41890302d440e00 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 789647095 1250 789645845 789645859
    0x3060d0c03050f0318040605130903120e03031806060607060f1b031a0a051e0a21110105090f0108091f02070c15022a15180d12120b 58
    0x4103c0d107030048081c10140007280c1c01d00c0a1111200100016200c0901c030b040d0f000b54000f8034042c2601d84a400400790b50f8041e051030560b5804448602089480c410030000c031a400100c10321030302c0c0c12405000c407410b81c80d1034010901414042c0001d0000d00c6046001040d01e595400c400582d015150010718446960302e40c000d00003d2105005005048110107240071140c1802401700d0900c0c00f00e0901e020f50b103028140c001d241400b0181d5425040302c054100d0f50160050b2000158204010910701c041c4196560040d80e040e8540b50100405c2941e0400b10306000b800c0c400c45c215900e80b811031f0002d040d000d00e0490340540f500281e11b0304081208000241c40c141203003a4085881e000d40080c11400c2c825a2202001030751220b0710307420071410f180b04000581008905c2110306003404041c0025aa45411040d2904a0000007902001c05030b200c6040040000c1411000d00310340b0320100c6599203040d2505244080c3c00d82d51088089248030304441403018211f0b40018100c0b9a9000c2c6ca1079030005003181c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 789648345 1250 789647095 789647113
    0x90a0c060815010c0503040b0705031306020c010f030b092d07030b0a0506041802031b0304050a142b0e03160302040b06120a0b180a0b19060503060d0c0305 68
    0x1071021030115500c5004011014010440c0e51041680031304a0790031402071428079003001402c400c0c81d0700c00c0c44140c0381840f0a1004104186075000303244000c07c01d5400812500c04110f00140c0084050b544410030715107829040c00e4652601d400342b550000c2e48580f0320300702c031900d4030000807400101c2c00d10154900f00b48080046140c0c050b806407002d5a07007224a40d001c542d86904100203445031303004103a800c4950b60b440744206402030300a1500020701054030380501d1442084000c4641049506450590020f410342c1e041c015002102c40c4070555503005001c100102d603041844208403501010b00c41d04a2260080c43d807840f60f55141c4041c031004090300d44082071821094511034950005a20403403901400c4182454290110340c120980e424900c2d18603640c5c54480c8008245d88680a0b4004101132880070880e5025019113114001401002030507240b40340a00c00c00182c030011b6001540ea001c6004c0c0b0a99401105507a48501d0841c2c0c024160580d03440c00280c0c0280310780c0010881c1c440c000756 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 789649595 1250 789648345 789648347
    0x306090c09030506180a2607080403060b100c1b080f06010e0702030301120809061204050a170a0504030b1017030c010c020102090a0509071106072d090b03090a0c06 72
    0x241411240600111640d40d00c48506240340705c0e58802c603103842c0e9805102100c3c00501003207c01c200042054043c070001615400c0512003540c07051500b1110f8000000e409d1080100314803c0c07408100c0d040d0b418400b0440c0385030300940191044040580301070312094500b21149080c0e014200942040c400b5113071b03012800b030f80c0a55034600a00070b1310140d24107000010391051002042c0c90499451a000442c0c6a004d600e601d4003070b074044028150032050070803240c201e42c000041030902032417041e0000d20764680981060021201d0001e203c0c0e020110402c1143c000b65881400e0b0b07400d99030402e010821a842d84117031004d00200607884124946503007400c8030343c02003002c0054410601103070002d01c44200310403022800c0b0b120b4513050707503441116400d0901c100e040c80c1034460351000c0c545c02e100b2061358158610300d00d803000445411000031100d442a407040003403100c40105404070264990b071405050103024007a010302c1e00410003001c90120014107070344410844408003542116182124a4603548 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 789650845 1250 789649595 789649607
    0x50109060f091e0c0b07260417070b0d0b0a0504051812030c03150301020717090f0103110f1e040609060e180601030218180a0506030d020c0d02010306090c 68
    0x1002d80d00c1101c074082c0c0142540e85114a0380030554800c0100c130900c0d0900304405140d4202d88020307203076164864002c0840105084c4501600e4400b140c40b9a1104e14240321400d903951650b00f02c28543e088004204140d00f9810300350390f44010360400102d540c1d210000806d00000b8903a10490340b25003000144401d074082008031660b014000ea068032142c12400080b52800e00c4265130484580b0020000100c0d4899000550340841307000400161030103900b6159507a441c0241100c0580213240000e84841c2850003040c0c0315002c0c082802c0030b001030ba44e29210814680514102000c1c00030300080c0e410414036400da8139001400e01042c0098450361512001000c200440c0520310100f840404941d00d64076081600101c40d422940c4000100d640359401140030303401c0f552885d2500810364400365071541c0c134031402c00e0342d4114000d0007500078034100c000c0c0c105640020308500c3c000d401c80b1160b801c55582c040341c04820b0322000d450310f1014460f079100403030092101d5070000004a04d482c0d016044294002 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 789652095 1250 789650845 789650861
    0xf0f0d0509060906130f0f05060f01090c090302010c0b0717010e09060a2a02070f03050f19020a0b18130b010f0905010e13091407080d02030421050109060f 68
    0x241100c034643d0712400f0f41540c82e401030350400e500d150400340701000a01150714443c407507446030301c1c004060b043c103580745443c18500740e81d90800044803c005000d1641c4a110386d00619150b4907000c40224607580001c1c25180b00c4503005090180c03000c000070366507130007050310074100c41013030010624a683d298401904c5820660390200c0305d00174003000c11a260341c9401a074a0100c0c203115a60400c0c4411502d2002c81c4078070751034420542c05056030024100d8154441c0000a40c007460103480181b25207641c2c01d0508a00340310510500060710308900160319103d4010041c0c5060403003103503541000140203445d05100c40c000b01c3d80a0a6030716000c004400300e4000c070501f903100383c8591f050880719500c180e43d00d501d84c3c065a80001e031906000411460700140445541210090001e803030742890712440029000641040140d6101000c10010326908000c6030b44440044e10103541000d040c8501600000101c40d03801c40401140f440c3c40c1c05000d03082d4031640311164030080400c80f4991905040f00030704035070 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 789653345 1250 789652095 789652111
    0x22817100b032505130501140d0c02010e1606170709061422081501050616060e0703030807020717070b070212060907060e0607171309050103030c0b0a150504020f0f0d05 74
    0x45c150024143d402071901501c800b01100c3c4003820000030443c070100511300490054115902c64000310410074041c400d210200540300c0708060300a04011000c1c05082da010f054415138004101080209a801604401522030038600b42c04280c07000798910354980140c16500f964105641007d0b401a4000368000084034110360a036010850180c03818079003124240300e850b8212004218544c0c200c0051030f4480340d00d52140c2d00003d407492070312000625201440e0801c0f000b00380032406110409404001c90001848106603428000d804a0ba06640750b101d24411100b9070310010904100b15582c5030f0301b03442c1e5100b0880481e041842d201100c0d030742c1d61410f0320407c000316000c010065081d040c4181250b40882c2c010308002400068001030710000e0b88004460b995a1250803004a007188990054500071030007940c0300b01c030007111414100c50260000d07128454039803803c2c096020070340004c0510001c90780121401078076010161603541940c07003480f5003243c1c0a44c002a0000d854001075109a00803a44 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 789654595 1250 789653345 789653377
    0xc080a051b010b03150a060b071104050112050309010f0507080d14060607050604020904140a0b070323060909010e03040801020c010b01090501050d050a022817100b032505 75
    0x4900301c040c00c8858000110b60140c0017100c511540450301010380350402c0c010040010895500c1602201c80d80000100f118145100c3c00e21103070b240303014003030280581030500c1804036280155584540c1d034400c800c00107040c403038080d1218440c41c0c010b0341a52203282d0440c641c0e5603617000e0544a003001f4401c8040081d01c040801c2c5c08a00903060031000e81d142154000010100ca895607000c020521030010400c482a074801e80c6240c0ba5890709104c1e941d1294840c62590301c041c24282d0380642039404000030418148120400000801603605040d88c10003401c1e07410700000c0d00d45150300c1c4d000d010001c0c5602900d100c00680010520030540c001c0020840400007004921006c80044a5017014341c03003807900149052103034610b480083e42c4001d401c203004203001441c040021058281c075941c540f85240c01c622410742502c010300d030010461b50803050081c2c02281e5510b0041c62190381c0c44124000c41c4400c640c040001091040040c5601001b1146600302004d203200d01e440081071507200814042164003 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 789655845 1250 789654595 789654637
    0x3070512070203041d090f0106060906020601091104031103010b040c0e03070b2811070b09240315120106080a201c02010315061107050919020a0c080a05 67
    0x4030120903074045d03441c0b54100409280807444000306040000d0200100741c0a02941c44120000c240f107070000a00180e00d880501d42d01d071050280c03e00368146d0000c0441414002e4560110800c0800c44080d245c0c01042003008142030f101080c0141001c3c80d0305500a0324119400d00f020fa004011441d2540341101110440c68480c02003c0c13060003000d219075146070b01d10144171900e602400c064184203c00c1c0c9800e4102e20464400c0c54074203825640142042400001c03210382e00d040500a400389003400300201800d002e01021034070070900c4000c0c0556540c4001174401c4001d9992005011ba9140644000340700b001d80f0751100e96124840f10b58100e0340318a00400d002038041444000d84881d0500500b03554141414500d03440711803104040c201d0406941d401071146900c00186404094541640e8900c615281c41d4030240c50400c0380d410851040c49114100100c012078100c40d005801c1b0300c0d090250300d43d0b0182c0019a0049142d8030010080340000c141400b0440d0301802400d070b03012103004070b0307000d0306 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 789657095 1250 789655845 789655847
    0x203070b1f030b1b070c0909050f01050103060510050f1806060418020306180912031b03070c02011b11240c0d0f0c030507020919060609052b1b09020307051207 70
    0x44140768001b410255680b504002c03500803a0312800d5418090010740d0b10a200051409003110b00036041110141c0d95102800546142d811400001d480140c4110055451200c0007030300860b01c1c1141071402411500004200e612400159001051480302c3c0045248060180d1400394104a030054083c5006003016039107e214201c51900407a54040540210201d148040d20b481e4401044a61881442d8801404011006008500c6080503555810603912544001406000c5100407841c03100507015601e800304205d40c802510800b011101c405200400500c0244e14004403806d104089030040b4544c1d000f0280410009480344244d03840b003140300c0c208003040d5000c1d540c5410140c00100203000c04d40050400c14005500416844094140210302e9508002510000e802550004d01c803210104002c0c240903140e42140310f000303d6071074401c0049000040e660001d4800161800c00c3c0e14030303400d82e005100c84030400a04441e2005542e2850001005403003507001811088800042c1c0340040c00c91 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 789658345 1250 789657095 789657097
    0x60f10050d111c0804330c0602070b040b060f090c0d022a07032d110316080307150506030a1b090c1d031b0609030708030c0a05060702010204060203070b1f030b1b 71
    0x14003c003a40d000d074a50120301b0842d04810f065800301c800719420042c07500804d00f0041264461841095515120710b0f00400b4080ba01900d0701c42a409010202d00b0300c0100002078054500d00c100e9000c0041c0c03200c501c052289240145984d5012051527589540281c1c0900451818182c074003440044441d44130854510b01e01c034201c01d4100b1070104c002103d2a0004018514801c40e01c03c006049800081000c1e80b400549411740c1e124003015400014410108030728035040305404440600c1c10015460007001007038684c1e503200401040320814000320007400d0a03003000c1501600303070b10b1000c00c800034103010050265544c20045009400a80009c9001c07840c00040f08011040c03804950a0800c0c07684007480040d8112000d81507050181d060301140011041000e0490442c101c002815814440d003001d5080003401341500c402c59004000038003a1036000811110201c1e07002c120f43c045d565800c5080c0140c01c80b4090a0221000c204000200f4001707015052030050140c40ca1042c1202c041901d44846 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 789659595 1250 789658345 789658409
    0x30204080609070e1308090406090f0b0607050c10050c060c130905130201030e0a0501020c0a0b100602120d06090e0f10450302060f10050d111c0804 65
    0xc1402c600c0020304211032942481d041710f108920b8107090201d008001409c1e11819009940c280d80d8890188810741d480d80039407001c4a00640b00c0500d82030303140e2a40c5407941104640305001d0001c50a00300742d0a03116904855140700c4a0041c5c0e02c0b1800c0802d140191548480c56075040103841440118504410344a0390340264000c0074440450540c583c01500681040c00f041c03001030080c0c803000408164203000506542c4040d80c050b0030700801d40e00c0c10f42d00802c400b400d52032013100d200314181706840e00042c030b4011600f103915600e9290198007040d0b101030170554018611304c0741071410b14240c20304002001b100c03012a1205481840304c02940083c1100d20480200788540549908030703801b003000f03210a0203039480c0f02c40c501209000c01700b210300d00540c001c00110016480700d402c100e2038440c25003c0d203411800400030fa04a261608000030740f0b003606848003900000c5105003608166480410700405881d004445490461050604050540180c4581082c504808600401d40428100e205c40 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 789660845 1250 789659595 789659609
    0x3070f0906082a160f060e012d06150e010906030b011b051513060b0d02090c0c0109021906020f0304150507060204050406090905010c020f030307030e07050a0603020408060907 77
    0x203d040c221048914100808058155070401040840c0c0003204912201352a81c2c01076003101d602caa11803920b0710440c0e03a0421540d405900d01005034541c3c03a4000d20b5590114110400b810340324080030150401424554810b00e1500307012201c1d070b20f005410410300c81d140c80d000d898103502c0a9448138150140c0b840e148c8503c3c0094100c490004650b204008102c1005005804444280c0c81ba548040020745048d034000c1071404403a0b0360482003240314015410000d10581e01c0b0100d0f0b085540c00314040e4400a0041c00d0424004102e00304440c1095000c920342e00e4000b450b0360354010500d03080440b0561540138050041c006c07111001584030000080314111050310340d522082040c481d000711003e8001d02001c4a44580810000801c2d6407140541400340480d10400251010249021421180022999001c0d50003010000c0704000c0088140c0743c1c811031a0801160180c2c0a2070b002d802d140041d00314a82c80275101c1e80c08a405c551560140c01510030102c220f034040c1d01c40c0c40c44c1a56a150602c1241 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 789662095 1250 789660845 789660871
    0x30318040c0801210321020403121707050313061a0a090902030a02062109010209010905090f0c0d0b03240c0705031e07050f0f1006050915010509030303070f090608 72
    0x44d00c4040c0d150140c001140c064030300741e00c02d081c0f0003e42c2d5540e00d40400b401c1c1480780e00450144140010340e03070010402030742781c18120700c4940700301d07030211038503600411107801e204000c000141682030700201d5005450380401e08005001515100d041c00c1c0400003001402101e0740d850100345e01380c0074890019110380007401890001c503da400c2050b13607880803074542c5c0381d40e4903112810305007110540c3c2c135802400500000768840c901c2c80001030100c00c956100b103225240040a112920041203005a017100d1860700940d030311102d03544410050915425816010f11522142580301810307201c41020303565400400205035100c160443c0c03040d000e12080580310341c01c1040300d0046144a11543c50078a640c1031582030406599444040c140041d110594100c2e070841c40820042030428010382e8a4000b405c1c43c104465030a1002181003000024000d0b0709140e507107031052556a0060302a40e10028008040b00ea0b01e00d03210748002c00c0c0c42c1104020401084003000c0c0415040d02400180388201000c0e0121 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 789663345 1250 789662095 789662129
    0x151c03020105010f1a1e090d0b040201120204050d1b1a04051201020901080a23010e0403020d03150504050903040e250305060f091b19080a02070201020d0804030e030318040c0801 78
    0x40c6c486030784002100c0340c900c2c404010b0101151111004a4040d5020f451240750510f8540005040344100d00444003d107481088103005a54414401c544200c1d000310402d05800c02506010010f005203820502c40241400e0415030804a050000d005544040d10240462807000c6105030031707406405229400f1501910008a00008a0380f02400e0003802e0302840001c3c0b104000e481010a0081e048026840310305000c0000f45a010040714440154501e810401c095201d40e031503001d500503014140c0b05603195000b1400d403c50070003e0f03a005d025134401400307035414000c1140201e0800d0482c40318141e08080c4640d0211406441081d02ca000083d1003481510300c5d040810085010040600c031035030300c01c080942079082c2c20030003410841c540c1088003d04092001d00123001c0d0070000b0051034655004102e1140141d0b8007184801e128510340c00c1198450b00c4074502601c200b1804a03060350544004210401c000c00400400f003600d10050340d040014410720001101c2e04402401080740711110302d405 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 789664595 1250 789663345 789663367
    0x6090601050d090204090f0219050307090c05040b0309070501020f06100306090f1a010503160807140105041e0501090501080f070f0e0d0b010614030f151c03020105010f1a 75
    0x800d5100041e510010f82d00c201075000800700c070803020050f42c4aa20054201e021400c0c500d030480c01004400011405151030400065691005030241048094030791a6880c80c0600034015500a0303c0716030700064592406080099407840c05128142c010b2007603c2e403c8034011300104001f8010f500c0715100400d0300d03085441c0c03800130300400c1e08116242c904104085000c60714084280080c110000b07811841e9500d08000c02d403500c000b03804400e01c20030584800304450b10700000c054084500081c0914103403a8020700599050060341d210f520f00d80c15040f255411213040403003500c207503002600c1c1d408025450b10300440e9169030480f0041c01070901c085c089100e0714060350b0050041c041e18a45941c0c640501c001240d103840c103003281290340039116801400b0b0036070000240303924400480c81c450304510b4100c03404000e0140c0903102c40c0702e1040074009142c0585440c00202080c0034500a10f0101c0b026a103402030082001b48220403006440020101c0d0058180148109054400c02d0ba00e080103100b41c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 789665845 1250 789664595 789664597
    0x14160305070f0803070e0301050610270b0a0903030306092c01021605060402090a0b1311120103150c020c060414040902030601060804140a1a0601230d0b03060609060105 74
    0x4801c2da1540340050104000400c100021407140b81643c1d240303200309a40c80141800d4030030244c250ba1080c03210900089030958031040301f41900704280d414096040222901803107203003d54002008051000403044d02c4550803110110850b8421ba0302004800c0c1d444c03000c103045480119650503403509030802c50410061600c4180040c403405000149000c075000b0044007004e100f07980464058104a00308410340c90074030100755200c00b42d10750030300c02680d00000080c00d40c10b554106103807032951103075021513408240042c1c0e0403500c80340c41c400103035507100e00b809102040c0e2059840714190030314904c00e101c648080383c08894180c01038141340c1400d042440d5402c8038803480b42216001a5038043c440c002d81c0d410010706000b4205620380315040c1c1414200080e403074403124018412648100c0264001580c50220307400002e1710002103e2858442c40300481c0c4803202c1240d100c081002004071710204200840041103030304510300080002c00007040070b00d07464420460f100340c0c2c001003410000754654002d42c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 789667095 1250 789665845 789665857
    0xa230304030c03270f080d08060904030908010c0e03010e120f1e0d090b0c041511010f050103051f110301090e21030a06050904050606040e010b09010b0a14160305 71
    0x4101a40c3c101d0403040341c035101ca040380c0689070000003801405c014040511039504094a01072024044420386407502908010f0007811a034000c0210310300007002e0500c06d0000340042d101610085c401c1c040c0d8500c00510a2080045992203540390040f4404010350020b024405013404041c0300c0d05001100c001c480c51500128805c01c840c441c2160032640c1c0070440f400429800c6280e400c00154483c007030412541d0058010009030004004110038000c01480c4c46041c8500101c40c0340c85d8500f07214110981d4050103021613089060750910300003104008000c1541002070300580d82400110059004120a0751841c14052284c00c02c01c20040c002c1341c402e90010f0302852a0001103814004428030b0740b0a0b20342200c411241107880200a0011143c0385004040040c0b0303044443d841d41e410a51030b4aa00c84401502584c4929565000840000d8082d00410700c000b00c001c0c42d45c4050341e51203182242a0340a594000c0c0011184c07810b50401d070150b0000d40c0d072010450303104500c1c00c58841d90309a95940c861 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 789668345 1250 789667095 789667097
    0x10f091a0420030906040c06020613110a0b2803140a0504050312010e07030b010e0631032d03090b0c160605130509071b06020c03040b0a230304030c03 66
    0x1c0d080c0c54241a5030b200055000e100480000e2080d45000c3c20305c4902c03100305030064000c45d080b020502c149882183c07180700485401c00c00c4e0b0a80b10203d01d0010b80600c1030750f400f040300a040491000d04254180d14000e0302402c88000d400410a44170314202c04850401e021400d85800c504081412001240e0100c5da005214004a916005502c003910b10a4042640241c180e58814800c120305994103000312069241e0030f082a041d0342c0391150001c1ca060140c01c981050014070803038000001c203440308422000d000b20303121a01440e902c03400c2190b06004021030501c28034041a017405000b40307006c0344900215415640b222240e506290b0040101d81c010300b02203856218400c01c0003440b10208080c10018829510303565034840e5940e0500029202c0c1350b000600c144692010003a0103070b003100800c2d03e10070840041c2c0070900203915045009009280ba0403009210104011aa4480210003425074035002d403245518403103010880440e2100d0000c1c2c4080c07001c1d0510200c1c0c00640240041c054162007 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 789669595 1250 789668345 789668381
    0x6020109052814190c060f08040b04120216060e0a0b0403020303040e07030e010f0504050c1008130303060b130f0b0910031e050907060f0e030d050c10020a0305010f091a04 75
    0x10815003d483c03200140c000c0c0d6100017049030420509804c0f01c4030303030640c402074103000d0360918203a00c42d0080703640010005010b02902d0400c40f1003561003440b4101001b800c4010811b000c0c3e0b03d03401c00419110340c66000c640500340c2080007050754101041643c040701c2c0e00400841c0741c0f0342040041e91444101920310800c1c1900d03500d44003c1c0000c28001c5150000190f074000981c0e02c3d2506186250900307440e401c078010b8540000004006a0024140d40c3c0000c040800c01050f070481e2804034010503103540540780c400c801003a00c2d045038403140340c200111094100b0480000380c488900b40558416942070550201c103600b82c44940c0ca010fa041139030303400c1d582003207040101c0c140d05401d42510300c00c0310804440d40016405104080e00701c50b1020041d01c0a2520109010b00c10000c21b607540e41d144240018084085001e040180d02080002c0c041104050150b4581800c0c200180241c4000e00600c945c2c0542c04002260803800c500c1201e151418200100364030103042c070288070051074194466000141 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 789670845 1250 789669595 789669613
    0x203071406120a0c080f10030212100219110f07060c21020c01080a090f11060f04080c01090b0a080403180807060809070611070614040f06020109052814 67
    0x8501c2c0c5107038402e11400344086103800c80d11a005082c0c9000800c0348498907104014040c2070301c81c048841007600c0d030503120054030703034011158030380341601e0b2803200c1250900001c0c200b040d0f041680e010248500341502e0340289404180203143d00c48441102c0d05604e640000d1040004c28031075034645140d18041d841d103000c10040758008020056042c05110051782c030405880c0741c19680310003202d901105440040250380c105a44205004032082c8001d0004030342c7d801003800541c3c03030204655629100c0410503582c0d43d030ba2298151502d20700d80102c0d000c1a40c0300b82c0020b640b0a140101c920000e507070340ea0705150341d99503030b42500c1104480696108626810300089600001000000c0203010b0b41c0e02c03103606a2070121031300e078a08074650b0000d404000492144904414000491a017503525030b003440554110380705029025401103230300c84007010300e50304800070b105a01940890701c11401142590350800c407003036600205032011880301d80750010480741d0f8004144c10a02400341c0d642c842050301c0c4030340 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 789672095 1250 789670845 789670867
    0x60f15060203120106051309051e070c0c0501030501030b0f130602030c0409060504060b030c0f0c1b120c06030c0714100618050c1818042a030203071406 67
    0x9a1540000000da800001c03034032145441c01103002d0050085241c901d2918012940c56038880410b03118a80500391104003041c10303260b400300c00c600d200321545010703400c52614400007014030245440984410b440400003003a00e5201c1d0040701c1c143d07904403070768a5282d01c4075032440e20070800041c00c01c1e8100805000c031800084c1d4900085000c0c5c42e000c86c400351a00e051100c070714100e8580b5405944168604802004056856410350794413031401e0034401e0b103070381c98085684101d11403c1c00828850040800038851409007002c1d0500e0000300740d4a01c500c0e00031244805685000c903903411030740084140700240b80500300e000248030151103004030b030541c2c1c0c040013402803030a490369011446294440000b44020305400c20034009100d160b040510035400d103000d000c0950310420301280f4000010b0014403c140d00c5020842c05c0000300b8282d0183c40340392a062190803e00c0700412000c010850409032019a2240d10500c4c040e00c1e001406824901d2610249080384050301001e550070450a0107100d03060 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 789673345 1250 789672095 789672131
    0xf02010519020708160f0b16060c02060a0c0f1d010201140a0c170130020d150e0c010519030605100f2a0b0c0c010207210c050a060f 58
    0x40301c54004141d024100818141004520302c0340080d1011900020084003140e14400012510803410069035648200c1c40c4c0601c1d540c0d49180030380060b08040c1d41d20805580016168800c03440841e0070840245e07042400c5690b003441860704400100b40d29109030410708243e00208175581c0500001654500506542c4000d0f4401c40d000443c19944170421640c00d0380000361400c2c50600c0184003503185d0f05080250102034400b070780c00864910b6852640b400390325441c0c03507201d80c540c00410040c140350692a0002c0b0425400c149041014200f00301e40002c1c40c4001030a40e49000161030390341c10110740c200d0b00054030b445441c0600405841d40000601070300d80c00c1c4250710b001070030b039281044005030007006000e546048507030070041c00f281440400000c80c000750f00c2c01c0d001d6202c0300c0c0102c2c5850b0800da0b0ba00c84d00a00103051007a500c0024404d0402c000c060455091202c81c10040d030061050010665501c00b44c00300282043e00416080c40000350980d001c0c0045940341d00000030702503d691846050 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 789674595 1250 789673345 789673387
    0x311130b040c021501050a080d03091b14011d010e09220b012c13030c151d010902060909040f17040e0a0605010221120a05071106090a0f020105 63
    0x2d84c00521000b00c000804940742409451306441d07000b180380c50b2803061640c0b038042400f89400c041e52500100100401f10190000b00c080c680345406c5000c0e11500040921644640c50602049000340c40d01329581044030141c0303958505848411f6020082e0090002c1104c00a01c10034004400300303d212180a40c040c00549181d0180354051410740c10480c0d4034541c0c5292001d00c004980d0139802003404c032050030030354580c00f088592021101ca88149400d4400b00402507009000810032440600d00c0b5103594050009a000d030048803210014001000d400c0342d0b044031029412010811221005041a03104a078115215691515128203d900c0c0c0340e0149002c1d080d004400000040c00308502c801c00d80c1000d80007031000a00300901480c12002030350350314071002d03440c1500390550001d038045a4000103444240181c003004021901e8a00f503204d009000c1201c202c0d02107900220910304a20000400c4d6214140c1800244040411600d07540ca01c45414142241040003c103e004050f980340c1100b618 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 789675845 1250 789674595 789674597
    0x206030a05070f050702030a030e061b01050901060506161712130303050a050f010302040c0e03070b04030506070206070c060209040e1609060b07020102100c052502130203010311130b040c 82
    0x7825060803440100701551512032401048010300c09a405a1b5000c03c03c0d0007280ea02d030619101c0303d0303412008a001c1d40501071011b0095144204841c04208040d08118443c01c01d00000f08009602c4208001341e40c09a90100384c1c4084040d0000800a850984c20f49080200303044240d080544500005502d079404450ee0600500d50403849002c01d17401d070284940050100c135080c0210302e0801040001038105100103032140d5140c001504019004540070316408401800f903403a0a5210004000d9681c840c2c801244c04e8851140014a1a0710100d60f40c0d0154103075070360344817241d94641c8690010390004200c803540b140d540c04907500c11035010000b010441c0c21150703450705d460340740002c440102c45103584007a00c10750303003000a10010303a80800c4407041e229080c0c00000c5c0800080b01c04448030f000d0202c0d07994440d008490f000f40382e040b413491a030744602d100725000c0b222104a00800030903400b0a202c010f001c90b10b00c105061403850000300040c02d1500840000076210140c0000800361480816414 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 789677095 1250 789675845 789675851
    0xe03030907030b15010c030f05161a070509010807110709020319060e09120c010605030a0308090c060702010903022202041401020106090b03150408040902040b090f1f0507020109030206030a 83
    0x20010070300041c0d54040c07000f10411002410742000a064103113506c6004003008031041140c00c1c09401501940e41c0090003540781000900203241920984410648501c04441c2071000100030500c900119200713282d040e9104900c0f511504070968a1503900d04680c500b6005120000c0381010313441c40510b110b40300d00c24044001c00100385050b8200c9580d50010300b02c2010b00e4040010152000800222802d47c0f04842e03a982d04807546054010b007c03d4015036410302443012241d0515501c001040e000361407440030380b4500e00031101003002c80d03c01c824000340405c2e00e10008001500d4401700301c11034102410001e02d0795141d12a200c404aa00941100be2030807510f40c88081d555074240b080401605503418100828601800080e903a1480c0301c4407001122110f100003010080e410041ea001031449180554442c0d45601543c85a500141c040500952418000c10343c18500030410751010b03001a07a50300c4441c1e513030364030407101c81c0e10a800c04d0f410b000f07a130400040143c450754001c40c031a5402c0c013000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 789678345 1250 789677095 789677099
    0x90a1e060b030c011d0f1008040c0609080a060c110f0102300a0b01020708030a0302043006020c1905300301120f1401050405160317030a0e03030907 65
    0xe10112040300d51518080e60000141c02c05070b0343c200c00d07581042014810100843c00e9920f00154400c0391101c0c2e4030760000c04040d00b00e08019000013400d40110f119102003000681c070394104441c512503603c40c0d604503a0095480c000455480c2c8c1c065101c40010f071410543d441c141c070600c103160140b0313010b01c0413090f075000070046a150b400b4407031411101886c408080d488014039150601d16040070702002c40d05650b402507100360b40c2c000c01c91000102505410359488500c1e910002d0000d40180c072a2400c070320140d0f18080d600e04140d1101802c18000190140310302c135142c0e103d0800a410180c40305005103d000c0e50303011807034290703490f01c00c0307045c4600d0003810602840d1132584046c6480680f40c107121000b07109030036030000d03800040d40d05541c52007468075600c9445007080d000c100c3c0705000290002c901e820201e59040019004144034500036000c44400e2010450034400d4002c0d91310006d001490002860300c0c0340d078680002103030002800040442c103560340321446420755000b43c54401c440e074400401 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 789679595 1250 789678345 789678353
    0x14090d12030615020c190503060a090b0a020f030a09020a3b010605040e13170d0e032104080405100f02251e0312090302010e041b08090a1e 61
    0xa000251020f41110220f903880140065950180c1c80c40003485031020100e2003003a02d080b0000700c802408010104c0700e0714104040024003c1c6039100094170041d160b18009014070b1010b0089441002c0c072011824a560b80d07a884000c020706070104201c0e44146200c00000389210218040d01c082c008100e002180105035040a200301c1c0d126a55601038064a40010020150400140d400300c420b8000035903000c0e50744c200403c0000070703a240c1c000d0039002d6000c040500301c4a000c01030400070301c1c400340401c17040e00c98100955881c012480c0b40d299404c000340680c000c1c0074541070025001446a0021401d080e11503000500c0c494080c41c0141c0020400000055075560401a00d126419011450708100c00200040d500e0700d01103000c1c00940c1021500f00c2176020105c0d801d00710003582c02001126a1022503a0024188001444182e0020740c00c02c40b803030501d1402d4400c800c40d009a9480701c210380e1801480c01d03074017800000c082d0040c1e402852000000316151090140f00324103030f0140040e825500e4a0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 789680845 1250 789679595 789679601
    0x20c0f010614030303071110151508010f051c080705160e040c030605130507080c0a1a0304020d02031c030c1403040b0604020d150b0a110d090614090d1203 68
    0xc80340b103910358201d00c01c00203a200481141e0704681103243c0007800c0000b0500ba07616125132807020324500d174500200800459541001c00043d50f210796941101c1c80d402110444030b40744c0c280210303140904052420000742ca0907181620400c43c440c4181030100c551510b400d03000750041c00d015240ca81014450f9002501400800e0005d0500c40888a85030704054698200900d00c03070100038070103980d4801103080c6103140b80c6107042069020046a00c100e440324a6583c45e0202e03c50294010080804c003c01c40d408030030481058400c07541d00040c1544c0d101d400300003400504050a903094003e810000700c84005111650b50081c4c07c5440115000c05880307001006c90302000d682407121407051040c4800210580d155541101c02107602503152070380001c2d072070300408010919003214803c1c0b4000040050320f400c09491000f0007515035201440b51140025212020480070304006891840b05120743c50080c0c050b650160000e4071254103000b10040440c40c0300381642c00980f0111030b008404080e10354140 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 789682095 1250 789680845 789680849
    0x71b0b15040c051c050403090803130303020d020106031a070905090c041410020c01080c30010b040b030103170d020a05120703060f051c06140103060f05010f0303080415020c0f0106 79
    0x40303082450403135514400007601c41020340040c9550345450119051510450314040034055000a80341d50355000500c088410300244812005401903000002103030b8010b01c580300c1101e800494242007d00000030302d80404400601807001c0c460080c0c0041140d0301c0348010184580910610aa41d550600c46002c040041d5007200c1c80c8215481520710131340503404960302645250a0074045181d84482201159a01810241360982407171030401d080741d0141030740c91000c001c0107110003104a90301d80300901c62902c118000c0340c4c084402000100001841e509906a00301840c0d801c09041c207032010703028000d9a001c54081400564040340700505036007400c9404d50840741034201000018980050281c0040051140c1c1e44528248080200c1c082c00340c00c01c1c81e0101d6131211007000b03034a03810155510301910a0000313a619910380112500c5190051166a050b074801c4400a020b207440c1d03540c1150101c034001d00448004120403008145000a800a482ca01505102802254084001c4542114555 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 789683345 1250 789682095 789682097
    0x30c130e0a241e05270a02010305011703030f0a0902130c0807031b050d0e010501080105100b030c04140402070516051e0a03020609030304271b0206071b0b15040c 71
    0x903040c08808280054002000301400c0400c0705e44e130341012011072109000b0f14a100342d0002c40b450440030f001041010601d80f00762001c20060341c9400084804070500d0000140903442040402e0303500c012450825030194520a0119001034030b13601207003100c0c1c91280a5450a615445070540b00c1ea04a00450f52081d05840c3c200b1500300070130030015250701d121041d83c003400300009031505000360f950802600080c0c402d00900840d42d540000c14001d050071613445041003003c40740030505800110442e80181c20441c4600e05041c01c1c4064000200d541c82e2a10350702950810600001441c10f0200500e80551802e00018444ca4001071210000300a00d54000c52406000802d5540d07403240652820741c0d8042c2c0d100c0d40ca44d4922800310f8914401c9802a124140003c43c04020100042d60708210340103441c04240408d25100d58450b0080e0f1070719212401503000840002d030458415044e1140161040303000c4a640c9100c3d481d0010f000a05a650899240b0110030400c118209070160704032100007 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 789684595 1250 789683345 789683351
    0x305032a21090d1107091a040c1403040b0601110d0f12060602100c1809020c150105010e010806031c051e03040506042a060807031a030c130e0a24 64
    0x80d40710f49a001c0c0801040138130040c000300100091080180b500503100a581c100100801d43d0940748007412080e600b82d200d1810410341c00c0820741b14440045006949003195800e5840795910510104801042241040f0300d00881d26002c403010031440d0111441030300d6000c48036544e404000d044002c080007400b0282e040000030080700380d000480500b10800ba40c00040c41d03180d51203044480c050400511a40f108003504049442c10f02a40200030340b000580440f4008244070950000d1604248038050100d540e241c00502c8070750042d4641c540c840c0d0010203482a00c260700c4880c2c10f9400c1015002070020700e01103101c81c00e400a030b4010f002805c0d14010b006095291550b81c8070b076140030040004040c0341641032101d00c6c1c003554401d80d030003504031109603044207900ca50005001f00011034144000a003404905c1c106040c0213100643c6d003040217000b42004249650038003840551664045650995951010359030f55030134041c05d00c00da0b1040c1203801280701101c0300000c0f19400680303071000540c0703 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 789685845 1250 789684595 789684601
    0xa02120304140105010509090304030813031a090706170f062206080f1617010608100b091003112e110f060c0a03091401090b18060c03040305032a21 65
    0x23030004155000c80f03a102078901c0d40c840c0518101c4a4940980d40700030608d2124020b044003d60401e55054841d4035003404445540b55100401ca45a00710b01c074001d440050600040781c510a0440b4000d940304e080070f4501da200d1018400c41d400401c0803800844075896560100340a403900a0040c4480e251212000340b1a0741240c03e000f203110200e520440354600c01e60b1020a00e0141d007900031f040204148000e0b1910004c8030441d100250001042061003000250002046202e40c4040e0b001542e0704160309146406003c800e02120640402440c0d800c0300103d4100ca0000e011661401212211990394560003814050503c1c90815440702031203940e0429030800400d264001c081c1c81070b0103c540340104280520741061500641e402800000325420601e4850502940341204e90050b60740c0e2008089107000300131250b8561005455421421008002103008070340700c0c102860b00000740020715941185116042c001013000030060b1074002d50085124440c3c5841c41e0308040742c0c5055404044540d103 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 789687095 1250 789685845 789685861
    0x25080307030c0c020f09061207090c030b1008071b0f080702150a0e1027031101170c0708040f17070515030414010b0415090b01230a02120304140105010509 68
    0x11701c040d46240120001c00001d58160f6902d008051a0030045041d2004562603103c1400a45018201c14003c6030a1090000301401c103400202c506142655800880741c441c800102c91244a4021702d0103a150441c4280d0302160b5140b807000500c034460b00445a8501c0103105000645c51200000c0614007005e200320249c0725000a440f003040c8804031442807801e640040d0548610010200c0c1d4403030480c1c2d8000820802c00d0178044642034030f00038400c0c50904100710004490340081100d0301900882082c001c01e80010024003d404035034418078070300d8100b40c0c580f400c4d0b0140c034206038044903020203000804030140c0b0b400d01280025140a9500c040440108240c0503010f00c00604000d0001c1c030b5021ba008240502948089400c2000238000e000c05056000e04c526440c43e40d02454582d28640580f0450b00d40c02140541d0b04407c05c282f001040b86920280d850850b003142c2600020343c010036460210b1011090000c5224074488c10700c0e0301c4101c8640e985503003102d505820240c0121650340c10b2151103 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 789688345 1250 789687095 789687109
    0x12123201080a03081e04030c0b0f010b0d09020607061b11010902010c110a0801051501110606090c0c030706060303030621150914030703021e1b0625080307030c0c02 72
    0x82030f00b50502814070f8684d005500e900300c10b404442d01c0f01c000e8550900007003592100703003444a03a014946401c940d855041c0c96107800340081c494003840c2401001403541c030704c00c41e800031141030340020442c50038001c103601c0d2403050b548903a880071850200c03900180f03001c07034202c1d82499803414000002c1080780015400a44002034991010f0101c203040700105c0305541e203c024a10103850264000d00c19403d0015404040703c1c6003495044c003046403610708029800c400154a4071443c1c00905080c03c90300c070040302c2c1d01a540501160091800708100c1c010216a2500804000f180310f681d0000e110307440c0c100701181c1e09140403265031915611070199000700710201000301284a41c1c0f00c000441030b0003494a003141c14480001c03000369007c00704290081c142c01003489803d4400803500c0003480003000151503140c014138084440f103000e0015801d541424840003504820000320340e40090a905907100480c6020f0310fa80c11a40c0d62800400c0000c4d050b854010022100807500300000c1c0700c46603500103020 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 789689595 1250 789688345 789688363
    0x328031b0509210304090b0105031e072a0c0501110a03030b06040e0a0c0807081003030810080307050a03110706081504091403031e0609041212320108 66
    0x1045408124581d1682d11800181141040c1500341060303d10032500c0552260000c1c800c200c02140382c2a0904903030b501a800f03c1c0e02c20901031403102c510700c3da0902c0b000800d8102400903401c100c2c1e2122510416006011031070a080130054504c04010010300d03042c040003d681e00b000d0704100070303085510004400002d06603441c69042c2030108256460b5000314110740100d50048034004111010301035a41e6003644400500380c1141c4e80c16038aa614000c0c02d844840080c0c4a14403109240c98082010a101e045210781103603096103500c08099856001d9882d40d000740209413003a420800e0307120109030700701c45504044454880907110a62034800c015020483c010302c520404807070822800c1c0d2613540c0b94403041d940c91780088511829120104010360300d410446103101701e1101d0b01c0c01c4090300b003e62080d03030303200d00c0005080b40500e540395541d02e0010072603c24240305020100b0100d440558182c012000c4105440c802c5600ca02c2950340c01c46c070110316100010304511101d4005000b0b404002c18130200b = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 789690845 1250 789689595 789689597
    0x506030d110d2703062003060a030f1e080a091e120507050d081b07050d060902010c08030a0207150b06040b0a0c02091e0a0e0c1009080328031b 63
    0x1500012002084600c219100e450b0301c1c3c1d8001d10b4001008110003980410b121041408604909000700b01040d070b024442905d2156000024410410000d680c1c50b04084200744620360380c010054010f4403041c540e0080610450b0446400310704c0040290f40301200c04000d08205108145080d0f030349900b5040e4443e580a160340e02c5040d0b01c551030074003100704240001054054400300340030641d81032000c07190304001c501644000c42e85100d002003880001c0d20700c3c240c80c4000c110010b03101c401c1e5100c900911701c0441c2203040c0040f0550000100300c030100a103224200904e005640c9039618584081c04d020241d500c3d209103442c0286914150b25407006940070340b20844c144079682c0c65444c001fa9030903038200030020350240a140c1040046011079181019070951401034902c20f845000c4d510042d1000011036003003640c40081c40c02c000345803c00f400300011a403410441c031901e884030209400c41d441094800c1e850f51308440380c4141403611000e4840c00850a107010041c8800c000d0f84030000d6900ca02d4200 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 789692095 1250 789690845 789690857
    0x6090121030c050f1f020a08070509030a020a06050c010b01020105010b041a120112020a0909020d080a03060b1201060905010c150b010504091a0a061106010302060c031204060506030d110d 82
    0x1004050207150b05007441c0da080340441e9200000612002c0d5601108001c8014202041e040d00f000d104e954002d860315168241c07211062590750407411a06034118008040c0d061040005881c00340c3c69000048003e401d03180d030350a680307611001e122429682d04443e0b290444e850030004001d0314500d80b0944d800e5500c600300c240d01d0340020b808a00d41c0c0d802106480320452942784000a0400c0303107814a010b070144255a5a25069640c00308001194420800a904644c1641c841000955058010291424542000124036484404070b2095400000042c0110700c24100180007160f044440c2d071004003c2440c1c409140451543d82d5020650110340145810b0385818521010341c2c090420380d0081d15081d07400708189400075a00f0a24105c20540e6030740201c6503542c0c00b02c9d80520468504d60000311040040819910b141c0c2840b4103603002ca41c502e101400140410b800340710202036018003480c01100086270740d080180406081240510440e414030034201d03403142000c0004505401203000740d040c28 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 789693345 1250 789692095 789692159
    0x30f030f04050708060f0603060c030115030c030e03040f24020a030804062a11121c090609150b060930010f1a0d0506010e04080705030a0903050105060901 68
    0x49181443c240c0000ca218010300c800c0191451130564500d10900085044503090788403100c0c022143d10082c004c2e41c5400f945080044071050003900304000350b4100f071400054402c25403560790b00319005a00320034402209060100042c210740c47e03286001c1c041c0801d440150b0044640042d54400c00300a00400f482642000203003445001d0748a00b0b0080000700d42d541600d003c41140e1240e0707030019a884000320388030001d140304072031001a9240c0300c141c40ea401d1500d00785007250440f00008400300c15840c5281c440d21000c0000b00706009035031410b44900380c5000040c04010f000d000b80e82c0d8460820b800740d02c0031b11011600355070f001c0c0103446449201020342141000b00280c0002e041c00759000f01a150300304030b0100c1d20301110b076214070b0444081b407011030b002c1d207140d00401c00d100101c0100640b0355800000180070500c45211400e42052040e080a85004101c0e6074040c1560010b50300100852540302041061007003e01440e680004101c1e820751080d03040c42046514402c0100085803521495011 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 789694595 1250 789693345 789693353
    0xa0302120c030307030509090907140625080c0d050307080a050403030209040c02060109060e04080a0f18060f03060e0f04170c1903170906060d0609062408030f030f04 73
    0x4100781c0c1016003034a9490180b8280684607501444d141c5014090581c0010030902d00810406d080c2d8440c100c0c030b611060148820071416401980c2201030341c41c0d800015060414601108823901131042601c681c607082d00d03441c4581001c0c181c24940c428020704104100005511003100b0764481060140042d2688035420210001d0245140140d0401d1810001c281c00ca50000751050407102c4030001805031a44425038041e950300180d500510b070300c90030300040d03450380e000d40400130b00c03040103207449406c3d5051045030440740a00ca920203808035252405080c0200d07810f0180f04082e02c8020407100b640c0c00e20041d6480d80c640010009040020044445407028000104a45a840464040303946043c4801c840000d8402112400c40101c0c09980d00c801c17442034000d0400384218010f8015050b01d9640d0018007e10f080684801c6030003559946000b800100039220f2180300040010340740e0b80c0c81a4040c601c0110491a410a0540b0303401400400324401d943c50490340d0122445c0700d82030042e150303850 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 789695845 1250 789694595 789694603
    0x10080c060706021c140603010612060e160303120b10021905030405180f1308030a050c120f061201061a09130615020606010903111c05011e060b03060a030212 69
    0x802d200c0c130740c10702c501141600c3c1083d0440c801c01d5a13822800009911144105030803200030307100e1607403020310602c42c81020401d51342c40400d101c3d60041c103841800c001010120507240085e08210007103106008042864926072240d151148001c1c0c51034400c05101d03650107555042580d1041d0080c1b0744c80300b00d00082000c14000d4600238000640084000042211741101020b070440760340302e980500000007100418500001e41c003603900100c00d02d1958a4814248000d4a0000c140c4032200404010801000102c02c041521500d2811600300c140c0c2099810004a04402c440025840c0c0c1005414405c030024200859040100c44000381da9804101020900c442c011096000c50740d031414600148050361521508075002080d425210103a8900d0010b4454000d42d01010b45105122104142d15080030a8080c0b007070b0100110040c07000c0c1032940d0321405e450892203a4030400c01d1201d04448456401d0141e280542210014036040d4684107002c54207030507040c0300c0684035000d01480a04140030901c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 789697095 1250 789695845 789695857
    0x30b040203090d120606200c130212060102120a03020a0c0c060f12060b0d0207020f030f010b0f0d082b06032003030a09140613030b0702010510080c06070602 69
    0xa44255100d10b00104020384600401c103403070020440caa40c6010f80603240e48241ca054a0058031014032004541111b2245100c5800c01510300d8498130700140c00740c2d9222018800400314440c4056030755000107100603150b02015050505542c82001d88031071303005003034061318044000d82c40c0060b26006242421201140140c001074250403914801144599218042e030901c84c03001e45904203a800f80c45500303801c03074403548a051046101800b04410501c41c54000744401c0d400202448400c0340c1100010342007070212881e2210070380d5101841c0d00e00b8103001c92540000201150a404200d0403900c0b8410f84c0e104245c940740040c00200150020070413080d641c40740300c1c24407501c20000d950310392400002c52425804e9442c0058890301c0d441c0c01614001007116010981030390343c3e5055514148003003e407503943c4d146850f03210b50305100f4640c80008004044005502414040855060081c400313801c460014100b4083d0040c103070024840c0c110300180000410600b80c170210740e242480e0a04100a000b40 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 789698345 1250 789697095 789697099
    0x15060c0705060c01020d110a020307020405060d023109051e15090c01030506040b0f0f060c030c010203060f091b03070909061401110319051606051f06140712030b 71
    0x202d0101c186000545c05032000341504c0c6403c02c50043c242245c444180509110480168000c0001c80010305258000c50b400c14800383c4014050320a503400034800f4408410b90782c01c100c9001c40d800c0340005100c024118880c2d080c88082189200c941c5400f030301d03042008032681201c102a050055001c104001c42c00d04028110b240101030f08046448644560440280d240000d040201184107850a4841c3d00c0d034035100140a000d0002010051115090b00742d94000da000f90188000042c3c1002071000b0000c0400d44000146c0e2840c04004012541e840011028020189441000704403d5007403004d60030820300a0601d601da540d810001c60715150315812034a181c80c140600041c0300b0341c1810b190302d803c0304243c940b0210090400000ca951f03018103513251254040190482001c24018001012666810110078080c00200d07100c40054490590780c800094604010b401161040321858101900f814034100c0120340c030b02c004101b80c60089900140c000300d140440d1401c1c59010341e200c1030303000c1c1c80 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 789699595 1250 789698345 789698347
    0x90314030c16060905061306120b0a0b0904110702060304150e03040e1e040b0105100203090d0b070810180f15031101020111040b030406110c01151d15060c070506 71
    0x1030102c6071041240714420140031440360040031070145800f02c280d4448408200c3d80d03985240c03400700d080320100d0311000248955640d4903c82c00c9a5100c40408001402da411781059450301c0340300900040301c2c203480400d00609014410791006a44240489800540094014a580d01300440d048003c020360f08076495588000100052030070b40000c1138a2040c01800104821021150032a1086007421140209031b42c0c60f2000501c01c0d441c1c000040300d4100603074070459040600420100f0380070080a00e09a0301c8420480410130703d43c0e401004558003000340201c04800391329101c12140513561001c01e01d52034507125401100211000e610898585c4050000c076040f10f6900d05003c03c1c40540042039131b00550030440b0084200501601712000c43c0c0e00303541e50358503656031030316044003d0070440720306200c9030700400c80701610401c01d001d9244081c042d50440304140385442c041c8000b03601103844041a668007001000b0601600e580d1422907042d05031182c40c0c0d144408240c080c105030154000b141c0c8010 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 789700845 1250 789699595 789699613
    0x2a15040c0303030608060f0103170d050f0a060506040f050d060e0610030308130506010e09030c161d1311040605030a0302010e010608011e0903140f0a080a0c090314030c 74
    0x250415210040307034000d842c100421600c886807241c990b90704881388800d184100c0c0c010000103074402e4454041400503143c003810890342d10750b08000e5489c1600e91404148125040c08680d14140c400c080c018202214101c1c41e06261080c55004007103030b0f114a80c0f2a201f0000503000f4003080e600401c8410403e0020b44601e860318401004190a070b03400306400180e2000c002407240e140d07042e040c0000b503810000600c3d10f41e00e03000641182c288000c18418142c041400043c006120400500034450540c42e010482d090800c200760b403034044c040450850030702811041c010042502442d6000040e00407044020554920f404139001d4841d03984002d80500c6100285414180d0661110040240c0703100280b1081e13607540c2d902820703120703405202d103e108080c44030780f031150202d507000d49007807131080c00c04600c0342c550861495001c0d00052141135205500250305074550307a00014031580110240d004000706c3c0310b554070092440c100360000078845035100c4401400000104191031000c200b1000700c548100b = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 789702095 1250 789700845 789700853
    0x81e0703120c1e03080106030506130203040512072603010b0a080403110303090c090f0405030f130312050705010e010501060203092803030507170a050a080a1401061d01052a1504 78
    0x880f8041a00020002c03c000726810344a40161030090714002c0801000451441c03042c00290700c0980200c6140c030426614401c0d05180d100070300101030040da00d02249140d51802644244d1341c0f04003c00a0440801c014013440141d042a140e2040c0c081c03400344100d65462030290f13403c006040403c00350b444088204514541d00107425252030000741c8002202c2e40360403d00c0d4060328410343c1c2c0202641c00620000c0c55801c40207011300680252990002030280c0d030ba440c1e00406d061001c0c00100014000550002070003024003501c03508244840017040150315099009459015080310b1903c100102c5030b5007034100b946100c04054086403c01030b0726a0540c0d0785005041d0307034040401150900d02034080180b42c800314800f0f032052501c0e2629a14074100c00c0d003000301c681100c014109514540e480000c2235071402c2003003017913010b0b2066031607200c0076880c00b0382500008080c00107502d04008041104051600c038070b960340b021080c0f0190700104000c0351020f281c2d00384180070110010840500040200340 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 789703345 1250 789702095 789702143
    0x141504080319020913020901090e01080721030f1101093c0b0601051c09050c0a080a0c03141c0e0f01141209100e07081e0703120c 57
    0x1288862900c80100060b41242c0080c1d006040c042c580c46060102e42802d9140250010010f0301c2d07051504211054403040c060402a4080e00515501da021490901542000c5550412a03070140c02c80c0009035082d40d03400800d0018607285580400c94800e900c0030318a0800d4000c0c402042e803055080c010702c0405c17250401b04d50081c0080d600e00102c40015000070356480b5000601150b00039110b08400c0c1d8030540155280d0b0b2002c140c10b8100d4511a0104016880303a104142c182441440506400c5045604000a025503a04a5800c0d03403c6174407140002914000700030100c80e80100802c200c02d81caa62160300f0302100f019072084040d1194048059103601181e20022500125903007448a40e02e100110341c0d001c4401281250a44108207649000c18010070840e80114003104460781e68030101003c0041d40e28004640c0010750105009110703e010910480411080400380c00014000030501c01e0743d154002c0c84003400c025051103059140324855028442500d4000c8a01ca1100c40408031a2400d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 789704595 1250 789703345 789703351
    0xd061202031e03030a152106050c030c04050d0f1e03021b010914030a02040f061403010b030604150e030403230106050303042313060e0a09020d1415040803 68
    0x8203000301407a42c101041c2e41c41c1041800100e8000a41c00d5548039405031004000300d940301c411800e644400011140282c0940680040c001c9a03400107109840ca002030a544011341a800807c40c2801000f041c12410029241159401ca9200c0001c00944c1403014440d03d840a0182050000c13111580e0004404507604565030b10075400c5601c0b0220030440601d078400c2030134081d030000d000c84208000841140c2c4014030f41850050a580d030000080c0e0000302143d059034902c1642d152901c004100a26403003003c000c5a200690083c0319100c0d015001035101d0100074401000d100d120880824000802d07403200302d050300038000700e1f40e03100c0d00e9017001c118040c040c4a004860112034809664614018040c90049074405401981801c0c240300705442c0000d400c2e03900c040c603040c00000700e040703540e82d0442408202520010000d00d460600c1c0d4000c141d40802043c00c0c020310b042000c52801a182d04a1120038160020b04552854801f210340a0504078405040c0c640600c5100030b01091180400c01940 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 789705845 1250 789704595 789704599
    0x130308190c0b071101020d0e06010501021603020f06130e0109091211060c0307030b04050415050708040c0e0a060909050105090615010822050d030213050609130903050d061202 77
    0x5020340a84812228070303000c9400241081c401c8000f262115028001d18201841c41c2d10000d820031b000c940324001100c43c1c41c42aa0309650007a001005696018096081b9030301c00180c8600c01c2600b144c011821410b80011f03268003821001507000c0b41c452281c48420043c003404d040c1c1074059652005140d002e00340410064440e410040d80c40d000050080021001c4070b010100034003619650b8164000064000410090906488405040c41c03a030b114883c403403007180701d2024400c510740d503003100e041103d000030920703003d00190009003c00b0030b1254007100102c40c1e00c0585508290303202a090005003110750b0040ca210b90402811804000041d00094070070f000520807510942d0729009504a07141c10307200c1302808911900d02040942c8003558082c41c942c1c100c01001c01142d0b0075560f42e145881510502c803000a03a0205002c05001444d82c6124018101281c02606020040b00010240e240c12460500780c5550f45a00d001014040c00c243c66020f0525201002495518070300c100051014038003c0b8 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 789707095 1250 789705845 789705877
    0x313140610030309090902030c1306081f05070513090b0102031c020309010e07050f040e1509030309190c120c0302150a0806040e1c05120c090f040b0f01050d02130308 73
    0x302d05d690603403044191141e001802841d01014540c24001d01052880000c09082c0e00c5000100d0008030401601d012038007503030a504420395440000b0303411600064042000c2180801200c0c1140d240c00c040803080d140540e800083c460300c0940142d00d503200b01030310346c020150221808138a01d00550b010f107201c1d2084100170711000d20b030f1400003510740c400d03800340c1644407840c400c0e40e00040c02d1642c010546114071400302c440110000c00b0450f500c403412031302c0a5482c4c2c0b00008000e0345c1d041c14000380e002035020003046e104250090345d400300c2c0c61150340a45001c200c00030009100780b1a11120510045401501d010388601c0300c4109919107030b1000c1900c8021070700b06800315806041521030444048000c601815440522481a0144c25503030300c2a03104002c01840041c2d031030382084d80520b00078107215556568400080f01800f80710440744a10600c00d41c60610f41d03040c280c0715800d0880d4821002d20709542d94042c0380100d4402801441509021765820304008030402c9590001443d02080161a803 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 789708345 1250 789707095 789707099
    0x30621060c0e010530130c0e01030b0f0a18150c020313050d020d1e0308060306100306050603031605060109050f190c030e0f010b01080115050313140610030309 70
    0x580ba200c8195074840d001034020081c4034510b5019000e20030080f004d107410016007048401c151145000c041d0380c2410000e804008003000c00c284403006000070031840c86031900c0c23503141d5281c032110030000510a032424400d010001d0480b4800c1e901071000fa00c140120b500100041c0d0a00e00107080480141040f440d1a14044110042c0000b00741e0b100c5d00501d4400001c210f0401b028040c0810416001300c4e00301d0554010400000d10b8001c0107100071101e0b00b4440d10010560500804810008e03260600907007080080c03080c00d40034521980241ea82050000c26192100000b10f89940b16442c0c40c0b0031205200d00614041103404070300541240e00341c100500c5951101e000403c2100707000c0d11404c001d440000b589240035150b540224018012038140005d9000035880e02d00d003000b000d02c03210314030399541d144607600d03540e003010941e0b02508a100d9030506801a410024000e8800a00f010304105007040040f010820719004002c1500e400c1400e075030740ba04001641e540070301c5440c00102c012409190300 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 789709595 1250 789708345 789708347
    0x908100b091b070b0a0b031006080c01080612030a18081903120b060301091e050c1605030702062107020a0f0f020d0602041215021e0a030621060c 64
    0x1500c6800800400d1001d854640c06045858404112255440103400b4090b010100d410300942c18800e0f200080d0110780c10040404141c145522552041c030120301d0712100384071036140060404800c120030f08140d0b0007500c5200005181800005d481006480700142c00350078540d104241c465072004408201500e00c0e180e0740d480e5207941000e90701d0241c000110b01e0980210b072040030300301000c103840c0c4000074003420020003283d002d6109030031102c55940c6400140005400d82d0486603010b10308464100070904100c03442241ca4820702481c076503a424808903020504c1014001c4560f4598020130455803100c000e00d0315400803680b0301041414080c28030000f4030060000c1072258003150321600b503200c240d41d44c2c7e48446411841c410140d0300a540d0850b56800240d8074401000075000132034001004290318036000c00916407200c14800d4190050190840c0742c0c2142d03007041100c5011810319030311130350440d9044000300321540c0060200d14251840c0c0c4901c0501801040d010780c0101c20038000b401550380 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 789710845 1250 789709595 789709601
    0x14100e03090423070503150307090e060f0403140a03060519060f0206010503030f0c0309041d0c18070c03050d060e2514130518060a0e0c0a050306130c090810 69
    0x507041c0c4626032070f000010070781442000156486401c144040006101c0c50b40401d140040b60f800031003000760355164043e40480304003c80350784004140c40c81c0840d0319007546c004201020103801d0280030003001c20100040da001ea00b052000c0c02d00a00060301c034142080440401048a22500020410000451054510104000c0d0694602800070b43c9011490b910b2916a5440810f14141500090110b40c2e560703a42c034000c0401d0002a41000074007000d054640c0c40c182a8a08191480b401803482556866540210300c160720566600b0000c0c3d0f04201800c09803454440c10421094243c034010011810f0040e440d90f07140101c9204981a118044882e40f1306500c449120b141000f107119151488034041666000303080c51a018550342101e0b81d0b480001c511a11006104440900d0890041102500b000d0144100401068890148605103601545414400c105030202080000400500c4544500d0340895241041201c10409600c925170001d06d10301a070f006030440e13405580160500407001e40 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 789712095 1250 789710845 789710891
    0x50316020405060d0b0c031005061222111005040b070b010e070509012f0a0503030613110403110a0b0f030703050a0b0f011209050114040c2114100e030904 68
    0x5031021600d41b502c0e20b1100700354200408603819900c0404000c1132544031000070308020a020407480c02103042c2400c550602808581d40611902d103e25800340104049c001c290400c2c0b0826102c1d92440f903d2408100d40d070f44100d0f0007420540078005005001c001e51041614101d0b628001e040c841070302c030200100d4051195245507400a4540701c100c0075180804c9540d1501040c4944801110f030003020b1069003400e00c142c10542c0e86400102c0ac2000d1414507202c04a54403d0030341e820440b0651205c02484180954003001d0810b26805e43d01c4501c3d6110300c0e0b01003000d010072401c860b44500026103604066441190b660000a0614020a182c41034030701441e100d403440140340c0002c1c44160b000440c0d404510050b80003996441d640300c900071850a00c20000a60240c04060300c1c07602e0142000c0c0004021944610b083c04040508070105420045610360740b280e10604101d000100902514075144422001c1c42501d403802800303501241d4008000d00740703140c05480501a80400012504100300ca803 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 789713345 1250 789712095 789712103
    0x61107030c17071a0c0f03030106020d11010204410901090c030f0501080105090d0f020607080a241404050907030201050a021e031c02091f0c050316020405060d 70
    0x500700a1048034000041d10703859942d040c1c22259980c3ea10b2848440082c0901c00310301d89214000b842c1341c42e240341400344108044504000310301d55454880001c0d0f460200004010401100009030701d86041c003901160002c2842203a100c450205a101e8203503c09000c810f005001c140000000050300e22540c4008181ca88c01024240c890b0b1a012005002c0c10b00306015204155542d0b011040c61052031040c0380c0a410500000502882c21400c054500601c880c02041803080810300d4517403984c0c0c0002c229038004c0a03858024929210b402021000d0030701e040d501107420f0030060340c8003181803640c038480046400c4c191419581480c0da05c14002202e10680d8510000d41018006101550040009240058440c811194014403500e071000d0ba0b0034891444402980002452241c1c4001d0307641c60740d902d030200d140110314210101d40020790000c502c0900403081071541c043d920381640a604d01281040c0c000003a03d0303803504040c01000a10445040c00c074800c0f4079100203e0b2050404003081c481091348 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 789714595 1250 789713345 789713363
    0x2030d06090b0d06020901030b1f090501050f07030c0f0203060a14161b1a0a05040b0601030506010e2e020624030a0609050321100806070e0409111906110703 69
    0x3c00c1d02c0b030314007945c01580311506240d2211103885160319040c1d10181d1851460215100040002d400103002c1843c9070310940c10444188071144400c203044040300d0f00300303916081a03042246070745030030124440006030203075150180d1000c21002d480150444034100c450b09802e144560749242410714100090b0060304002491095142582c4090f51042ca210a0042c000154508861070f48900118000c84048030490746610501c400c0040511086403c08402d080a00040c0760000000305114440a641482172140e501140880c48210700700d0b030241440354103c90150307412020060341e00c0406580c00c0e071115101b000320791000d02143c403102c40e00e8440140a4054112561110b4000e031040c41f074142c455000400540f90344e00e2401445812030718591504066a240282c01c0611040743d6512082d101d0300810700b08402d040c0e0110880004440071940019100c004d070504200d14500b403500c2e15008050341c0d0f1620703000035000d03078000101c0d602c40d0346001c0c0000010801d42e455106a02c001401a60 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 789715845 1250 789714595 789714619
    0x42d1b0210060e070c1506240305010902030c0d090f0204020309010b010909060b090111150103150e0d050306010f1206030521120a0f0e060f10060203040e070804050a1202030d06090b 80
    0x48030341c4a50000c075103400042500d03a1504c8c0c0424400e0110401c00380020045004401340342c0d01406a10b0040000b440210300f149000d04980b41d01d84502001400d502e940c13005a0001c000170304214054590700604119100d180c03030700f40b40e40240400c0c40d42502149281c1800108948a8000c44064410322800b072420401c088005540c90305165917040c2d040c0c014004d50074000d0300b00241c40740c001d5000301c4150100d03180040b0b41008882201174059403036005041c140c4282c540020840780c11402c00e02e0b0030203035000c1680040f00d0200c5031000c0c1910840c1054000030070b000001621548006c6d445003803184200c4008071150b000d100c3c1360819615454008005108002c455001d80b58890b01800c0c0491510343c6c0302e54071400c1600840714141262241003c4c04096008145244054042d900045241a041c1105958900300046c400300030004c00307400181c2003081c20700000042d5503100420f003151045c5d00e000a03499030030070051000480d182000c0002c990200b8026000744078000b81844060329 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 789717095 1250 789715845 789715853
    0x70509160e03120712030c0c0506070e0604031a09010b030607020703020123030a060f150207181b02010912030b0105030a0e16031a06042d1b0210060e070c 68
    0x41c10003070150349030080c0c6804541c40f2003010014000680b0030103070080c2c8240384590240c1180c4403044ca81003040390008111002900010700590401c0c03a90074840c654000140000e9118800e9410042c040b8044034001e00c80b80c440101800e028104040c0213015160301342007415a0b54804503015001640600b00801c0554018046801755214811207070074119145114014942d0060794401d07403103030741c03042c1c2046202c690801580140413440e941d003a00300038030391000396980c1441c0117450110541064a050308000b42d4032001c0b411520441c20401001c152102a00030404845c00352140301a100d2026011072280c40750941084058481c07500303644803030701d0780b03001480c003d5803a000070311445440183c080401c1d444100190720840b04103a0204050141100c04400500750b80d000394182110720040c110440070300d1800300d015404100605046920040c0039081101c0c40c0c800c820314000784d64030303800d5000c9040c42c1c00b00c403031038428012680d48191130520f1400880b0710000007882c44060360005 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 789718345 1250 789717095 789717107
    0x309020603070e0d0b070e0307061d010e030c152101060804030305091e0d090806130f03020102210603060708011a07020f1c0c120c1413060807050307050916 69
    0x184005000b0301004c030b15913503414001c2402659414003140c54403101c030f9418602048004c1c0601110301c0c04002c03030b4820f86081c04c8240c140c80903e605110351915051855201004902482c0308020112503400e1054440200c165000017540e040900c2100345003840c1c1c540e401c98940c103c2e00c05a840744000d54890310124000c2c013000c6c01c200c0030740c000d01500d018000350882c8802048680ea401501c010180e40e0005040c001c40341d801428550051010001e010754040456024650842545d00b88000c480c034040f4024429000c0b4540a1560400c00c2803020340d00c088407600c80c1c4400e800f140c2141d21551030a8070084003d100c0c5594400018405c620f103036402c5800307420036a1000c0d05070030545650314009030b00c60440c1094139902c860b10740064401d004c46406d0075002820b401508406c140e00b03035214440d001c4600c0c0501300381c0c1076519a000c0885c0e00c81c01c40704800020242000c01140e03486d6480326882d0300342e40c402d680c401e1241407000304440c0341c80c010007801a144c1803281540c5020344501903800d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 789719595 1250 789718345 789718367
    0x5010e0a1803080c131518052110110d0b010507150b1207090207020109060c0b0a0218030102071407090204060e100c1712010e0f0a0e010b1206100501030902060307 72
    0x211a80c248940300c0950601d04070f0801921130321903090380720b11081c00300a07c42c00009071100021040c550081101d900c51143c0304612802c400164260003803050b543d03900c0d20081d040c00e01d40044c03400042800d0340000340060008031036514400d120060000004460a001e40440648180450200c8c1c80c0701031707400d0344180e2100c04090881042601003010310390400760594080400e80d03400080110440da0b0005416028010038200507014042540b01c100d00c500b001418044401d0307000803600c2c50740c4420303c44078060050080095550300364a181c18110541d082c20000030070712400d0745c046154450390081c0d80c00c1e103104d0380e41c81030103090f48010000d821313110010200c1800070490211002c00c000c100c07040d0b8030b003124100060f40d42c044101e4000c0c0c50801680301c010141400406e0010b040d08030010b65030000c0348032078080350300c00d07021900d60700500400c002554042c00c0e4036484260103101040704c0d44240c0d2442d01007024075556400640a40c1e05252009502a10400008044a0160004540e = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 789720845 1250 789719595 789719611
    0x10c030e091911030406050919200a03150c020102161112060f16050304084315020c03071b0b12013210050c01090605010e0a180308 58
    0x40ea990700d031210001190320152400e807400ba0001300300428001c00e0301030240c01801d08401070003c00750185090700340030300380b00009001644943c044405c481310362491b2010b06800801c1c003a8101d0303507131030441e42c400342003000824580c4c203259a0105090040c401c1e604100b152504940115815070707a0140c0800000020940c846400500e0121591040200760300c01c03c03c0000c00165811700b00c0c0403c01d02820b804180d000c000c000c20030800003400080c01c0d1248060044c3c200c171040c40d82c040f6002000c141d68400b041300640041800f41e00c0c41283e0480d5807000d8022440740300300801000215080c2d224006412016034410020140004d01050840c14082c1000910390b4001b1303294000030680b03511a00d1008141c0c01844014804ac081240c0c4d6980e4201c2c1a0342e43c0410900102c10310003078400040d020300e1090001c0e000c0710071968007840443e1488a0500020404c03009280703003c02c02031000303000b01c56820001784001016254948515000010248505441304030540d9080307a00c1d40300100a10 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 789722095 1250 789720845 789720871
    0xa0b0405060a03030207181e06061403010f06140702030d0e18010503060426030702070303030c080714030c360607051b0402040b0d060905060a0b0f0d2403050c010c030e09 75
    0x8d08680700c840c40607440e40d4102c070804602c0c1d03860418000d061034202000043c044004100401039012150380190468221b4200185c100f10402c2c051031440c010080d0180d01409600f0b0500c1030181e101100c1f40b40e03583e044558141020f20070b000440d10b00c41c02d01500d0703015071080340403030041105150306050051110380d103134585001036000a151a001039944001507400000c0500030181c142c007400e40c10748c89924000c965890b142c6002080015144024100040000082400c9580c0d07401218402242c1400320078102800300f108101004038030b842417520b9111155500b074145800021203e00540110003428605400d40d100034254051400c1d5542c480d81c200320020300e541458001c1c000c0840d10200c0046d04034136240685c015140c0007025644506404030003031054107421425110304001d005111522121400003580041183d181d085807010100d00105a885900750030a03010390723204900781c2d10400c074440b00551b803d070b10300980280843c0544142415a0904c0c2c203c040e03001d020b00d90a4 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 789723345 1250 789722095 789722111
    0x62d040f02160302071508060f010c020f0d0309090608121804090b09010e0601090608190204090209010b0307030b06070201090501110a0b0c0a080112170f0c060a0b0405060a0303020718 81
    0x300b58003041c600c800310b0258229440800415880c071000314500e0440c0d0400c0112454030b0000540b803040364054183c18010019070683c1036446924040c050700002034046051200c040c20040c101008910901500030308064000c16449070108050f40c10390314502c0158180341c900e07451ba0452000b03084950b900156202241408604214800350064180c10000200c10030110025814500160041e0200b5400e080b010000e0110015071000d050220100d43e0048c0041440018081c015801011b50701012032000403504104510041d80944c040e80c8040085007003034428480c543c0250760001e03012908882c8108107650203503415020000d203440595141c2401582e410003208816500700c82c242d03c0200d03003204035039040003009000d40742800715014161155562410008100e910360f6100722400b088085980440f034068807aa8844070003038414629011080d00c005141011202d480b40713007000c01141310b41c00d18040280950f81c1550252030200d042890155003540c040e03204048042d6a02c4c14 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 789724595 1250 789723345 789723367
    0x30f0201120b0a030818031506040c030f020c33040b040203100e06090d110303010312021006090c080a05060a060e03030d020417240f0c040e0a05062d040f02 69
    0xc40d50285200d51401d42c0c031103001c0708102c2000c10400f500d860003a8051070758030034154800c01030994018000c4a000c1042f8001c180120050001c0083c0c00c7d550600100342d144111001044070180c0600d0348018201d9800207032019201c10743c1c100c0003c210104640d02050100d6076030b00c0070030ba001313002034220740c04952441014402c540a82201c44407a401620600000da1405d0000c0703c0260a103160a04028040e0783c0c902e6100c0c8410300c80105a100041c084020310b0b8003d0005445841e495801040843d94819026016280542405001840c040000346107802d0070700c00e4600640015020350225400c0c0801903504280940e155a41480f003030001d550003101c1070009001810383c07882014910080240c9803403800d002d240742503480b140f803030704041a01c2a080c80c0300f560010400c00c7c5403138aa2604106c000291050360095220011640c04001030032405802040c0103030029a03000314043e01c494041042031082171030f10764621040f0944441340d440c0c55000700507603045108005240c03441c1142 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 789725845 1250 789724595 789724609
    0x5011b141c1a1804020406050f1e0409050708070f170a0f170c07050f030a0b070e0612010b0c0d03020c030a1206050901080d030b04150e1306020a091a04030f0201120b 73
    0x7103e040382e08034520402046003000e00030032004280c10f450204000c2030b405e00080c0c4070786401c200c80e84403101c4c04103400c02e2607503140c002440854000781601c0f002900d0360310a541314590780c040d426580c810302c00005680786900f250803143c4035000d00904805503555507850031800502c50213407185c0c0c10303a00c03010010740d202000400d030b04a2864001c02540b40b811080c02442c100c1828a244a60441c05407030022503c244802544440a40380c0b04182e01e9006e0001080780c0150b843c14041306a6135000421a228020024a44240032808070f45003d00d041c2011010307481452514007654005204461f102c030f000d40e4032141d2424180070301141c8152104003003483d400b400d074001c002590011507901c101a80503c9086540d0000380c4050110684d01030745112002e0061140000c0801144d00040f03015540035150000c0d180d0004003907581c0d2180010040aa400c1c601911441900403180c0103103a0030404100cdd802c40e0303030000b5946401e00b025001950030480207000d0b101c00540b11054041c0580d07400c4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 789727095 1250 789725845 789725869
    0xe37080106050306090d140309010609110d051003080f0a02010603060903050915030c04030206030402030a0c15090603061d04080f0d0c030b09090c090c0705011b141c1a 74
    0x48000246689404201403030500090300c24403154002403070550304981d1000160000c1040350a9155a0743c4404001900405503540244112031904007a0356000c0385900050000121800d820701560f00e5550718103880320250300c0300508c490000c02c5100e80c9410160054000652580000644683e0340e44525064581981c1d0450011700c0000c0c40790058601031203a140d480c07003401c3c1c44d11700f945400d07015250203100e140406407040c00c0100000e02103540403c880c003055584114403005840d0354520030003000d1400312101001c65111800800c2c4507100344214802c40f00815240b1682e0030a90a810211132000762007550030820401c0850300c10541e8000904010008400c0021100858200142140c40ac20071240c170400105060000140d0000740700e906404049907018420345504200c4003c2d807051001c010b0165080c1601070541e503885041c04e02a1000e2501c50620500d1711910118003441000703641d29a541511220000d0040a50b110202c003071032054880101070b01d040001003150030300f4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 789728345 1250 789727095 789727109
    0x306041406010b04150507150216051e0604140a02120706030f06031505060a08011404110402130e04020a0e090606120303090703020f15070308040606060e37 69
    0x440c424660202042040c64010301e028191582810304000546901900c0c00c100d401c100300000c2500018004035594510b0701d101440e030210341e035050121502c10803140e04d81c4166803a00030000e800101c103580c3c6820b0800c400032140580560360302e60340c9003d110380080c11402c00380d11500c102000140c0303c0008003c0901201c1d401006c290740362040090a5401d62a038884126003003410800001da042d030f900111a80c01c018003c115030f0740d044041a0188565405102d042d03017419580305805403500e031028003c50240420701c032103040e450b0500040c1e00ca07125800b590403400690030071800ba81240007a0b00544018405000e140d61040c19080610055417107042941152050010070b14003110356422441c0c824002d5411454412070b01a1514141d100c043d002e24032134480701c005a0394010001c0035920000001d03585604003810010001c04007294100c401c1d500c0d054011407194021440840000300003010600f140c800d4584a10321080800d40100680841e035040210780310011140c40013600302 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 789729595 1250 789728345 789728363
    0x30c070f0f060f031e24230d05150709080f0a150b0103060306020a08040b0916090c0e09010b131d0703020708160606030218151e030604 60
    0x141404030000c40441e0303009004014071200c007007220541010303407101da020440c100042d1080e40c40300200c0c00050245103404442d464900014204207400c0c502519051782c10800e00e800c85c0e1200c1014112404002030f50108814841101540349070508003141d65900c518162000740150314a2550000c105507403000106540c001d041c03003205070801240700d01ca4000001001e00e8116921404001007440514031007031510b985035088164045c1d00448015a80b0800441d40c40c6d803c010001c0041c80141c404641d0382c0e0508000c512002d03400561400b846e03442e45240c900d01440c180c91b0000034200c1590000612101d10b45650040c0c0d0b070400250f00a00c250019981e54440340540c49500e219281c01403140d08140280b07004240301c01d004034951141040c10010390b582206d052a070a1401044000b00e5241c040030070007410040c070b941110b8101c91096035030345040c4200d020f030344600110403100d082c400030f20f5811420340c40ca020a03880e4951002c60441c0e4060540c1500800c0c10042c04075010368110035 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 789730845 1250 789729595 789729599
    0x3070905061311030420010f030b22330b13050907091a0406171e09071d0618180d0305150d08070605040629010201061a040b1b030c07 59
    0xa011400e55500762041031064480410306c0040d002030b841c140e15008240e540c2002c415192290b402001c3e01020401e0560f00585102c0c220030060540c4007c011428011906140c030000b400002c3c0c010f0f00342010b514a062903003081102061034000b850301080d04030742141e0008141d1a01c000d01805a10a59203e041c464200030048a130b0641549104c546214200f1080250741e0344106a04034142140070044610340320901c16044054039100c601c00c50132001c01c103100c0d45003000502d0f041141c00c4035440c00248421888940c8600c4821030b01603410540390146c601c0e400c0510140715502151a00720600e40700b1000d50400e02c0c1101000b00580481e581d402070207002c0383c9490089406010840d84840494115075410721640a074510052000c0e84941c04503007003204941142e40b1503500520801003060648541c14141403500320001d01651070106d0100300f0460345e1000070200e0b401007000529042c5450190b81d05944052821410700f0469500749200840038401048140040001001014 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 789732095 1250 789730845 789730853
    0x4030f0b1506030919061104060801080c03010c1e0314011202010e031c08041109040803042a0b070813061e111218091017010b030709050613110304 65
    0x1440040d071a0384180c005008009903c04000b58103007404003200300501d00b400300ca180c090050007244010b0440140082004a00700d41d11200c00c81c101c07030780d0104940c41074042c0c100389030032545120007000004c0c240911001704c0c8610041a2400303601c003407500207040c14030060a500e98a5003030700b10007640000004010290b40c0c2c4102e101d009140118044c002025298130750f00030700c40c604c40b540d13814440001c001034184109a0601d151011010301051458a00742c580307950b450384212000c55003a0125103452809081035003c03540741881c005400300401d82811000015504600412911340300104044103c420005c0b00402c0180429120441d1410300d03800c1069110f140000a403040055408c56014801800100c03031001140c040490399581d0500320041e426940e0015525400c400458140325414819074041c004941d00e6800d80100070204011b00d5017038070030b0403016a80c1580030001c10300c01144117034009600058003e00d045c3d048000390300e041054902640c00c2c18150800801000240 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 789733345 1250 789732095 789732121
    0x6010e040507030c1101020c0c150d090305041502192a081c0f0813020409050d080702010506010f0503061005040e0c0d060e13060c20100605150403030e010504030f0b 73
    0x1300071154025820004a6070741d80f80d0790402c510044e0b10a03180381641403551004070302110440402c06c0c5033800080654200030740700c1d520610691f40000342d40d01d1980e1503030307102103a0603140264130320340c5040145c42901c5180b48c86481e0050140005c03500901d155080c0b0180c14004001c10482000d03042c402c010141606008041e8940f4505018548070004c0200d5032012a0a40c0b0825450021001041a0010800424800d5070082481c8130b5101c0740700f6525000901070b44903100d2503000f4401540d6440045901242c3d41044d00c020460503c04640d85140c10390134840400440e00e0004d040c00e03507a0324140320400c03041c1ca80c0c2002c403000180400001001d07000e04070180164070300002840c24802c14003400d0310010b100140005a489440c0d8003814032503906040c00740c1d0401c0510340b6036140141019101d0701454000e9280914140f0700182c80d040c0503080c80012035218810301c1c241031641d181610402c4940103441e0410000b0030010000484511030b214419000c1c0050111303a1925224051503 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 789734595 1250 789733345 789733367
    0x51c031b0201050c0a03021c053603040b1b010c050c21030103030309021203030c0d05010f03050c01110a0b2716050d0516120308130f0b06010e040507030c 68
    0xc5904020400c0360501398482101d0030310744c29140050380d07040e01004840000048054840c0c2c0241418180034500b4003501035945650444008a908692007102c2458110380c1505800b2041c0c10a01c0304110302100c42d006003035200903110304000c0700c1e19248091401c44201c002580081140812203c440300410090705000f502e0418041c800d480c0320140301c00c5580414800101090f80752259981151200a0703000c0c49903030003100f01c0e5102d052446002034150401c0000310280e62400c0c0c00040c5144c591000e410440c0d80220142180c40c07580c1004603012003110b105002d0900c01d1300440310000d04041034642c8101451214002c4c03030b5241c405038101820419a0130600d80c2c3c44001c81b0040c5419013010702c0c2c00c0741c20895215500c46868504076042c0384414100c6a490880510005149003a10b43d0742d03000240b02e03a40f01004d556681540c8114040c2c40c07280502001209603100e000a800c40d6a0642c20920505184008a03406400074017520001c4504000081e15180d00b04c4607241c000545500c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 789735845 1250 789734595 789734597
    0x60206070305011d2805070f03020306090a020f0412080d05061e1014070c03020103050601020607120207061404050a06202514060603070f150c051c031b 67
    0x10951602c1c80c0000c044e0480780314400b12000c0240485c007010741c0766001c50300c0408080011020f00a00e90080c0d0000c0c00c08039135038804100d40e0100c1600051282c03007260710882000b4a000b05076114120700c40700a41001090010050040001103450121641c50010203071242038515914134007030aa103401d944001d42898040e070800910240781d820707035400300040100c3c16501000c952041100c03c0300c0044c600c00226441410024102091011035a503200959000383c03000e012640750130b801285d65000440c0d80c80e000074018080c4071800303090b03a0000e02e01a4060407010401c9411105043c2481d04117071000c071000d070720004420307041068a000d10301050280009a0602000c20201c4170042c1c458800d5514483d44150031840d201088500100b110940040c1c0d03281d0390740035010b64a503552a054035014400d01c103140e8005420281245040d05690381001c440b00940b00202c4242c521000561045034240541240d02d01c00c0ca810701c0c421107001ca03081e074010414000100151206c41c4600c130301310b8 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 789737095 1250 789735845 789735851
    0x20f0109411f0c02150601051b0616050306150705031905070c0e0112060b03070b04030b0118060b07060905070b0f0406090e0f010e040f0f030e01180509010504020708040504060b040602060703 84
    0x6003019004102090b00c6800564440c17141d036100ba0041721544659418003032403001100101e014540000341031803084c605581c00100ca180064030641d118042103450641c42012803d151400c05440c00191425a106604480c01d0001c03110710110705401e50790080d00064000f0070b51354140100e0b513600000405005030707031f2070155040000c43c48804000c0700010304141e480d55130b0070026031000c110420003865a5080700c0d40315030f12450715462070381d421311990714000070070101d9016040035441250111800b21031160b117010040d543d102e01a2500000c20750f114005c240c40041c1583d0a00c001300300c1c00da4120300c6259140c0c14114040c26840ba69040280012405002c0100e00030750007030750b103040d542d12401c600c80070342c1c8500d4585c00c0000c0050f00240854507000c0a5410560007222424040900f62500d6140750b02c1c92440008100441c0304a590040340c7c440100000d05046d4001c2601d50b004483c1e141c42c2c00e03120310115040d520309901040058100060400c54994180909500010240740074 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 789738345 1250 789737095 789737111
    0x7020c0103060f090b0f040e0a020910050109181e0606091e090509120d1b020a020d0b0907030c080a0506010e090d05031e090607020f0109411f 63
    0x6a440f6040b0700400341d84503035030741c1000045c4d61040c421503c4000010018000010b02589242c2c441c080b158040f80100b080038003050003502c4084555007500d43c185c1d6050300e424944480c00b640c80e0750504000e10b03001e90343c100e404220a00358508112510780c0303440c0410260b180400c024848001544444150b11031800c002020700001e00704001110b500b480702044507180c8091143c00d01c00d2040a809110301c00180f00090141250000c5480b5034490741c8503c07000d0244001070781c6036807501d940254408840c041c55000562400591500280f0200450b10303026240e0b83c43d04c0302d1002c01d411040d020b81c0a01c420300d0170020304200d275a0140071040381111990038a403201d259603c25104501040c09804070024440380403d808410181c2c0c5c004400940d50b05042040346c2e20740f60140d81e0b0704010b0144840360004441e050050341c82c241c1d070180c2a1021021000110003507403860342c019921082c080e02c0950300101169071150041c2c900c040140100d602c86142520b1030100224000c02598100688 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 789739595 1250 789738345 789738359
    0xc130204081507110304050a140a1e030b15031009110303040303110105070513030605071403010b0a1e02031204080c01020f1201051f050702010c05061611061b0a05040b0f0307020c010306 82
    0x400c211007080d001540406a03a00029201180a801007400c80003866038000b900a2f0602d11203040300d02440c0313111015110881032800c00c0303501d0710215800da80400d0300c02e00c5101c81e0364443c0d41528010304011104002200c0002e00350f0780a0790042e40080c00c100f21100802000388103564005405040c410b19109040030240840301c0c40e8071000d415290384000181409016450400420210340501941ca6855151142040d0001212040001c680305602c010000103207046a1030400d083d0019810002981c1c0b682d0f02819000704100e805240502542d40f03601c00900140406d00b1100444640b40d210981990f002007505a010511604d202c1c1d281240d44c00035110a011030b13261900e031150f6030700c3e031900040e14245a000340c000e1892041c8000c10081d032907624030b1000983d0a43d40c0f595001d40406620b1952140d040d0346003040042c9200b00351221148000083c00c0d0707600380d8101503090036070f6501c00780c00382c0d0000c01c1c540004520001c10400c1903a0b050007807036032008003400c0070880b031410811 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 789740845 1250 789739595 789739609
    0x51509040b041a0a0905010b0a0509011e0e0c040519060f0f030b1e013506013506040e071502010e010e10060b07050c13020408150711030405 62
    0xc4054165a400000705007400b5001031890f2034548900b0302c4200a0400f9a420001812032120545281d480c1c01482c0c80795203092020102280c90041504080c1d074203112140c0c28169003d504926424a1080d00096140d025418036104545049080ba160303031500c03051201103408141d5131103401101e54410b0088580001646000b400b0303a1034460806d10358508160014070100c0c0c040d9910000300a804a04001c03440c451812020081ea69070790030501050041c10f00040c4a4040b4909a02c200c0c0e00c010307150410543c2c41d45c4084149000201543c02c001c4450907004645c0702c140c1c41000f5003841c11076801c4107500003504400b050b02c0800a440c00d130000d003901c1d03d06500444001a600c1c1c40400f448901c01d41001038041c09150080050666044a641e9140460681e040000e4249100000c88859413004e41d14200d130402e01420b4000c0023841001105058a1900c4542310750901012a5151082101c4040f00d07480142420042c14280c0000d0401c0b003034600900321a170710820062005482d654 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 789742095 1250 789740845 789740851
    0x50f03160f0609020d060507120213120c0f0807090b1509090c0915090a120506040809010c0b040f0201180f03020603090a050d1d01050307141e0307030c03051509 71
    0x1061451081d101490900c0c054643c2c00e002075030002a1800b200207201d07141c0d1002c6d0041030691a41c01200d1000c41400e0203a01685205280c3c44c4160a0100181004030401194240c030801c1d1038400c0544400196481e00300c9508606001da100000610158203d840f80c8114050211005011890145440041807040140030780c0540340a00104080354801c1d41590030324403009104c0c152031a8922100311075034005980e107034403c246a03e0001207c8581e01000c44c0340a42000180601e59141d031100b60b40b40d448400e2590400030f02c41556400300301e445a41078041d034841c0c41810400040303070000614440c9200d0008150455135002003054001108180301226416a4019125600c4c0640e8908240c0800005000b84c00303610081c0c152030390b05c00340c0001480c0f2036000e0040c02110140045465000441d00d50010800c45a1800160748180028000c412543c1404862a001e2107044040c541c00981e0a107012079141c6c03069090306a0180511341c1d10a4820700c00b078005c00d0001000408111010b = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 789743345 1250 789742095 789742103
    0xf0b070b090114180f190201081807060813050313030213060806150301090f0b1006050f09120f0d030203071101050c0a030506010521010302150a08180c031009050f0316 74
    0x303076103008180c00740080b04003140f200c01680c086e4680385c5900500e15603800c0c0224001040e00c00025414440d44100040c500541d01c010300030356081440a0f902e100c0040c09070b000c541004458080003503801c07c014802031501741103c1012500d0b600c14000400400354400d000503040440612030700c0f100040107940000f02a80700d080c11141c0c03101290041c43c2802c03000d0304288010fa201e00602a07040d0450340a8032004010848a543e00e17607049a141c01602030700e81602508001c54000ca141224110780040e41510903100000424020149403426154128002c280c004c410400a0340e00040e019403920031010007407010345408a0001840c3c4a9020100d09055580f004500c40364418001c0d5401004000c001a10084040149140742242440224800c031b40e40071122140c20101d40544a060009448a01d460b1715101c51550381c00c0207420011001d4881d07900300e50f00a641c10001030345190301d00300c400102c1100e142031180c1003d12041e004a01c03a88200000b1103e981ca1100d03841c01c04e508 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 789744595 1250 789743345 789743371
    0x903120909060b2b090f050610170c0f1816180302030c090a0e0a03050409180308060907180b0918040209070509030a0c0b090f04050712020c03040f0b070b090114 71
    0x1484040704c018000d5000c0034164031206590742040000019804e8080d4417012030440d90039503101492039440c044c160700841260080050320820342410000c440c05000001c202103246c101e80308502e95030580c11903044031414124410784110b2a00070801c44082035030340202c1440c15003180c0100b99a01c500c01c0d0340038016003901002900402c0658003d030168154941030340c0c2c5c60405800d000703000350002d002e0208098640062101c07807148050141742002da240c3c03104483ca5480c0310030007621480c01032110041c40b0718031492610320300d4000d0801000d89a2120290740b512100030910640400d034401d1035640511140600026948009519a01942a18000c3d40d2955610086401c2110f240340c02000f04095650100c0c0081c1807401070038130050140e5414a07200d09010400c4291542600d44030301040c106645507000140d51340013000da0715007034012a2314255481900c03d1030f401d5140e2182c100c50310080380801c10002a55140c40d0022031110081c8410b4455280302042050043c00a6008c400 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 789745845 1250 789744595 789744667
    0x30f0c020d020d1b020a03030f02060a0212070c0609120f08011703030c03041506030c05180f0106050c03042102130e07060f030e15060f040603080d0b010903120909060b 74
    0x1031300c01c00d92840680c082d1258004039941c4c81c0150281803240803403c09800b03076000250640c0c0340f600c20703030364034030412405800782d034407000c03002c2d20306103e2603805403415a1524032840c013103030307407540c0f0b00c0c4940d100caa5400c65440c54080b00241464410b0304401d050451110386003c0f284000011b40307401010750884203030340f03841c1c40c90100c52000103404098081c508101000050082041100c01103541c1559200103180c41d010881c40d060104407800c0d001e600f01c0c032005201d4070703100300c0103400c2400e02c0000b12071603e5140c108100150b0803000780940300b20104a403020850520b9120311480f000d00240610030000c0812080b61901c002d03005c2c0f04104000d8031045201503100b60440702c0c0c134600001c240c4400e80c115248000280760122170396409036505400188407410a807013014101d80c2c21041d014240750710545203030040c140703282c01c41d410800042c1e070200c041481c4101c600030b451300315180c008409240c4040c42d81900c2941e40b060321409410301c099078400742e01e400c80007100c2b01d0540d85829190 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 789747095 1250 789745845 789745877
    0x14090f060114040905100e1806071209080d0207050f2e021207020c01030c0e06040b0906070210180e0702100504060f0f0b040e030405130e01110703030f0c020d020d 72
    0x8003c56010343c3c0b61600303200c24012440310b908800c2007a600f000b0034040d0b139650b41480348011480001040c1007683d20140002d21464440c9034a00744d900d8081c04042070302c0040d030700c17000d4103030b04414680c00030306600198640821a04010990207080803102070034001010420344d0100324450514071242d294030b200200518030990341111682001038040921508000200a660300c03041e1149a020a2805409c200e0540c0510619079040000615540c50b0608080003540b89810480e001d5402c05024040300300141e9801d51240900fa0190ba11100c83c0300000711b020341c10340080da202a512540600605c5100b0790701040c1d040035a2103031200441c807a1120701d4241c006083e5407428449151400c1441030100500ea0410301d00d00310708850601202004014150b200d21443c0700c1ca60340700040301c004825043c06900001000342004000144c3c03042e0601880c103680c0d02000d02100003070f503034004491013000c8612079072100140c180b00500e07003010303540c1c4007965944c040ca07401c5007031107600e0390102014 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 789748201 1106 789747095 789747097
    0xc02040b280e160e03070905090d170609060d03110706020f010e0607020c0d0305041203030e0f1507051b0703030908060c0a0f050a02010f090c14090f060114 69
    0x142c0c0c100c02e01507a10120880013660540626540000d41d1603c030311071240705402100280124024030400282034401168110400903114000c1c810252540d403240f41d4015402d5410309c1300d128460074240e506103c90042d800700c030300c50020046803a5502060000a25901c44003e1003400343d501c01e020344801c000c5900c180160f00881300d0241d03d05c1d110040304a01c40c06030070840d1070a910340b01038507500ca0f8048020760109482e0340141c00421400c00c048000e2070b01365000351040c000120707104000c40802030500300401c40040380304054a00c02450450490b04500c08071460560f480c40c0243c4420301714490a012030103000d001407191102e0308201c034403480d035590310204556188002601c50360081c4241c070007199a10b110102140c4032510a148030a030040642441c09403800103040030b00000c40c038802d806054401c00b446400d1041e040b15540001c02400c1103114000181201401 = true := by decide +kernel

theorem cover : BRFrame.Cov 789568345 789748201 := by
  have h0 := BRFrame.cov_init 789568345
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789568345 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 789568345 ≤ n) (h2 : n < 789748201) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
