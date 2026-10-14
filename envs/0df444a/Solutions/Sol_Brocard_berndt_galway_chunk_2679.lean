-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2679
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:25:18.846151+00:00
-- url     : https://prove2.me/submissions/76ad442d-c848-454b-92a1-1282939e0e26

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 481654676 ≤ n < 481834532 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 481655926 1250 481654676 481654681
    0x1d07021c120e07030215130b07120e030a0605010801060602010b0f100e01090b07030306031101020d0903030e04110f0307110607090e0a020f16021c0201022d0f0a150203010e 76
    0x101904444050811807080f40c005580d643c0000b0000c40000c480301926000006030b071403221100c2031204001d0f200e00d011701c0d864001e43ea500c010311440b26146440030440d9805d40c1110f103036410b0041861683c4c0202c414021940c49084580c024025403080b04095803802c5080451410803000c00e0315603040042002070b4030000101e0503a00d0940e01c107a0207040110030040440c09100c0c0d0005400c0c054000c1d40e00054140c11071409951000444006074150b45c40368241d101d40c03507488112102529410b103420040446408046406441928403d2852450120700c0303115602042780994400d84080d41c8810b450741440740d50544510f0166222000920807880910201864040e01e1307400074456480145051035981e0740d0001d580001150701c4042d041009103006515200c54403485032140603291101c225200da001035504c0305580595074040d69000943c00b01141c80c0890003c071164420180e45041020024894031604c54003c21110307419071a40e200e40b000003034402d50b4140c40c071b00040c046854 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 481657176 1250 481655926 481655957
    0xc0e03120c01180c0501180e06130b1003050417031e0c0909270f0705040e0715080108010606030b1507141212090606010c12091d07021c 60
    0x1039020309003600e407664071003a08a00030218100c2948110380507509400d80d0341e080c040010f14040d951032907560750202118051013084d005e14030450308a00304441198821460021010180c0004010f041d80030307044c4da01406029030550011842940300300007080c076603120f00d03000215134002a14a9900900389000040c2c50100d5025a6604140c00062082c18a00028001101050200c0f040701d000c0304d050341c2444492068040002d10451448007610742210400e1015070394090074424030380f2582d01e03000d160720301001c10301c08180540482c0c00da4004614164a0280500c0c9083c031a101040d840c0140028646210f1300c00e204a0078401410310122005035400483c42e60071609060b200340c003402c4951100d41004010f8419120300d41e0030341030348500c20112445034030341d00203200083c1a0000c40400074540c4c1e00c881e44690469100d03a04080c1c000152404480d000e141380c001c401c03a5140c0e810404e59814000c1c2c0110311130411a8200ca140008180303c1610403c0055804004103c0c0c3c6001c001d41d8 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 481658426 1250 481657176 481657213
    0x901120b06091509190e0703020f0103110c010c081602010207050d050a02030c1605030d11060711100f020702040b010309030e060331020102070e070e0f12030703030608010c0e03 78
    0x120f10000d040c0301000840000380c004541680c0780c0d00301c03110034000506550882c0c012003449a20500140c02d14502e17540226400c180c03072181041c10156640e0785041410b400105550007150401c000708450900d1a41c0501290401c0d20a4400500360700380ca1441640b0500807103109650041c09080710038036141c1d059030a9080a84100298042400041140c0c00d04014220f0351b80140e2520044031403030311003814140341311a4200da04000745d05d003500e0700c441c1c00024115005582850b004a01c00d01040002d400c0a03246111241c00714200700c042421594107401030030480d4001c40c1c0c00c00512641400640898a150100030007044204500049520b08000a182c1c05a0440141c0c220340d03910410880b106500600d07a2800810201110002e5503070400109001e04280000c00d482420b10304c50103005030500b00b00b80c0c0d10503c520303040c14546880703a6901e00d502c00b440c00c00320307074864989180140141130203002d0480c0c02e602e0401312480c20707445403111039406030f0060f000c1d000480c00c120403c040f = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 481659676 1250 481658426 481658431
    0x2218060506070c09090f0b090d110f030913020f0f090414131704090c0215070314130204090213091401020a1b110d03080f010e01050a052416020901120b0609 69
    0x18806c80724428200451444800e061041c0001409003003180e07110700300507081d881d00c0e1014a45c0350340030810455a148000085407102c810403078901c501100d00d200704c07074044e1180d190394202170320f804165440450300d00c0001d0001c284044406220070300d1481c0381d0351407502003210880083d54608407620046022a5034440e410700f46280c256251613210204d2205807100c28040c00016800080b201401e114030410068018aa41c1307801c0c012008102000292801c0142c002e200b000d50071a122400c550b129440705403165400303040c0003001c1380b14440203401852a0b001c2913518000410b0800110141803080315248036907a2140800300010408004a1070b0000303104545008a211f41036400340d0b200e0700c8209025209560740e801500d003400c5400f2054406900000520992400504c01e03503440e129a40141c07070042daa0b502004054441b582c901c8008401d070b07800d0040c400120044071002000c05644c1160096680c041c450b6682c00d00203202440d400009004a500700004c80e09034500301c42c4054 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 481660926 1250 481659676 481659683
    0x170c01120914240c0301031a09010f06060509031c0219020a0b030c03060a1208190302130f0504231303121118010203120703022218060506070c0909 65
    0x1900c805000002c01d141c0859588034140c00794800b0480c01d140c1100d00d02c06039100e0720308240b00341154595503854850320340545a40c0d941c00208030024200345000d520203d80302c0e0b0852400d00440e41d03100400380a6a00081c8040d00a0107400b950803030941e410103208107a0002580144081c21618284080007004a4000c991000c40700400041c0c16110402550084041414196481c01c21004000e110302540e40044c0d030a09010485401040c3c01e01d040d22000e03c1e1101c031205c022082000c04600920880b220750b80302d4046c00310701044160b00400b08005449058904000b100042504401110041110070f0a15402c050004902902c503802e00400940700e802c1c6080c0d102500d20100d004e4031000c0400a503994404500104082900c1c4031800c00c0680a001071460071441100c654050701d0001e0981d010f051300010200c0c000751744551204404a02c400301e0b011100d880d01000c1d00c420350f00501080b2000d00700900801c1620b0158107c7c4c6400f6030000c142c0149a00d01b2400d600544204501076 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 481662176 1250 481660926 481660943
    0x2b120527040b27010e040f060f0b1002070f081908090301090203030f130509040f060b1c14120316120207020409080c211b030c010213170c011209 64
    0x1118540b10140c3c12150790002e82041d0f50000c0da0407000000b0868140c0c0600341c851410014400032510900ca05002a500044085032740d1440341c0c41a0080c003108a0142d03040301c0e40250404000f540410591300f540c40d440300140b0200c1e81c3e442c00e507540d4844108994071003121115040001041400140102a006000403888070100c1d0001307403e58024442e00c0201050018900a2440c41d034007044003e0081151400d00d41c3c10240c03510000c1c01c00600b4001d01941c1d9a03019003a0907034602c19048400101541c02000c1c415a0349400728102c0c45042100700305114102d80c001c62215210706492061118440d0761b42d0041101700119415540814100c00315503080142c3e40241c2c442e402540103040c002c810b49660340e410210a41d1070829882e4098105c44602c1d001440040c1c503e50440d0b0f607403e00c0301041004400300c034140a06500c80d0440780d41031584001614008400300380404011501104c83d01e02d00080c40102d4a038485118400c2180018411200860414980ea0040500380c0c00f130381e00d9 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 481663426 1250 481662176 481662191
    0xc030f190606090509031c02031501050d090c09090c21021003060b03130308100506030105130f0c0c140309010906030c1b03031b05070f030507022b12052704 69
    0x503408130394090b90896015000010380fa02d01c071088048640c00f070050a5011842c41c90401108541c481a404100313040000004841c40980003541040c00d1841e0400030718040390b595104400021b049241c012588401c82c22000100101c084800200750781c000c2c11401e001c010076508002e5805844264502450390721a00420060b1003900a14401c640e50414081c60808034140070301900c600030192103000710301d41c0b820f20450711a0307403c4d43d045607400d80d400c00000c03503031406541c0900401156507400901c1c01e4212003150f82c0c049d01c60028580241c0349e4080600078403440d180c9a10a80480c40d000c1039501904002e824801e61207100140d0192400d007102c01d00000f8103000556000c00c0542c000703900c0340c0c8031468880c0c0c0c40019812090590804070724010196455054001680c80c0140c01e01c5004600807040d903c8001c1a40c3e082c02c0030002109100003141c0304030141c903100e05820317150b0550740c00b159925140503008a8011440c42172481241030560880d88948001102040350019116080d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 481664676 1250 481663426 481663439
    0x806270c0f030a0c030b040c080616031d01020d05060f01110312040204180302060901050a180f0507050d08030708070e032d150603010c0323040f120804050c030f190606 74
    0x5048042d500c1200341c01e611f802c0c1401c03d1107400000d600505c0e00e54100b8030910100359003241c2402070741641402c000c6080400d440c004603107084c80d1040604107500004040101e45000e5008031b12501e8200c030080e1a01c81c08100440c3c40c3c032020340003070394103500400050000c00031110000781c1c80707071004002140c940300c4500600e01d8007140001c01c43c00340c0d1080d014025854028001e441d80880000c0701003268035005906400d500700c4144018000f44c404020220600506024810103450080c1c41c9104c00c80c0c1c20314028200e81e104550110004036140b0104080d940306090b102042c4400800400380300046c0140404076590503080d4085100300c40a00d1110380109002020f001c000010408010745840c1c0203040c01c0d40c1e6450001d104041c500b011841d18000c0703050388104002100542d80700203595524003540000c91480c2c0180017489115034512495a01601c00c42c8030300d220301d0580d4074800b841402d1650b00c140003c4965001e0308240c4d000c0c0820401ca101c01a000c6004003800324804c0d17551003 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 481665926 1250 481664676 481664693
    0x1309050c061902060601031505040509030d050702030d0b0a030317130b0903070201170c0307050a03060504020d02031501090b0d0209061204111f0e01030b06070b010806270c0f030a 79
    0x26282c0740c00400d034240511580600401e98001002e0805006d602d4071960b0a4207090540d00401d48034135034450110348024020410341d104120f42c80401c00050070005d07400f2355a40c20030b0729003440c00f41c2410150001810801441011a0b600d5164203000080040c1c08140140740104201c0ba205002503e10300400e080d040994094800100615a290b18500005003485000c0e15450b00c2000802d0500001d0540001100da00c04010305e00b4544800403101c2c22000703000306901c00daa0050001c281038038074200583c025402040c4c0c0e0720400840200741001500c032400340d40308a40c92140107001714022040590020030b4692001492503180820201101101c402e042e1415610f000071000309030090704056103641403880d038400802ea05101900b0000703000f800c2e2001c0d46810175464680f04001921550107644200d031340b04250070301d00d607160101e003651020121450300106401d50b9a60050710046a43d10021144030005401040c01c01c01c140101a40c400340015011b11803030005d240400c0b03d10 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 481667176 1250 481665926 481665937
    0xf0d090b0603010e030403050a0f0c0f15122f0d0f0c0305060d0b040f020d060c0201200405060301050904320105070318032709090213020304021309050c06 68
    0x100214419414008181400c542c0640404d1445520400c41440031a04c001100522250700034030b8080d800e083c514000b40c08400d680d101200080c2500340115000b0350241000c0c030440c12581d1000c0c500c0f15030701145800d4a80d40c150418500110b4000d91506000300048001c1c1e0000500fa26860400c800a101c802c45511703164113a04503507070f4260010a03a0313050013141e40103032040782c90807070f0500203446600b071008000d00300a08915820104d8000c5494617858846250b0b0003800400100c1061000a406010101100d08900d90700c4180b11001010400c252029104060250340c1183e0901061041d0140c001d8416103d160403065511801401c4244110b03001c4090310360101000c0a0a05290a4031304c040d00d40c1c818503080c8a0307003004100c0c2c4002c401000d0754162800038604400f00500b401524070340010001c1e44116510003044e1f90039541c10020300680b0949200c0305000755040c00703d08a000a450003540511072a442c800d517420160011504d560041080d54000441200020a07580c8031 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 481668426 1250 481667176 481667183
    0x10e0f01120f180c05100f0935030304030e100507140115030c0e0f01140913080a0e01120203041a090c06070b0402120105010303050d09080c0105041410020901090504020f0d09 77
    0x100b130741030006051020070381c8618042d0f42011414461131070b0000d07103048810302074860303e2400200103d1481442e0762030720480141155540c5941e03180803100540307e9104880a5001c100c09401200b030340e00380000910000b450682c2d505081244030f0380c8660b06030345c17800d400140039903c58011840721380001c8103290045103d00944c0c081c8600d4903200709200781e8020b00d40f01c100d0054200401c20030320030184030307000d60f042101c0380c07404c0341d41e448142545400703944000340070f440700802c444020719081070040d10340f01d109807500c0201b80210b80c41102607100455004081c0701800c2400011541686055500005040281c80c1040761640c0440e00f281c20165003613400c60325800501095041c10440c1d441c0719401d640003030140d5811902e0180c101d2040403581c102c0c040c0d0b00d02146c410702046009681c403888100009200034149800d1035092074281c141c441c2864010000c0c1d544a5100c80d208a94010324103071035818990f40740c2010403009400082200c0c00d00c020410204400082c03034031540740b03114403 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 481669676 1250 481668426 481668443
    0xb090f030609100b0109150c0b07031a0904030210111803011104050d08040b031f120f020f0f060301120209060901060801050f040906020a0309030e0105120c03040507050915010e0f01120f18 83
    0x146027030000c03801901a0585051600d008201625003003080c0d00340e410000e0a40e1a071030035440d6450201c0c03800e0180307400209918503003004220030140301e2004040140842002180d17040c0302c14101400c07140c5044035551032050400042005d03050000003049954020329081d410996181f1032a22103500880300000c0c0744081c461078542186c52041c0d81c0001d0110307810104110103041d03940918800a110703010b442441d12003041c4c2e50301c0c0c0d5074546014941d03501405040e00c80d60b607002d00c00040c0c4003000c8100d1280d011800002c42906040c0c201c20f04070b4246540d80105a442c000038400c000304a14089038201d500c80040001050640c0014070340350b1055640020340004030306004001d4403510300c0d8281001400c00448500540d110321644e00201c94094007039503503d6502e000e034a0003602e580a10b811100c99004c008140040030501070841c0c400fa2106c400300c0143c1020000c9a0301c010351041d0209030b6034524085902c4007580580c806558103c000124407041031a1aa012002c3c000119039201 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 481670926 1250 481669676 481669697
    0x4060c0e1c0201021923030d0e031804050c0307031a0604031209080106060f050903030910050d0f090206181206090703020406090b0d030c110a0b090f030609100b010915 74
    0x59041241d040c00d0070f08114004030120b040d650300c020b404d441100382c20145c1c01b10390600740014010310454031811100300003002a221942981034503608003c5440340c1c11080c603510042c690506000703d51090b404203000c00d15660301e1090907001070040039240b119044111040989640b212002000658002c0380b5004681b02d140100414214044d08006038030390400500700300845e0449045c0a070001c3d9401e1181c0c075100007501007840e500076030030b160354004003110fa2241d1094205009144d141243d040c10b103d0109164030700f2060320a80c0c0c80094101108015045615104143e401c50b107440080c0403030756000c0c44d544502e24000d016a80702126401c1801c042085140520441c002401004010300a4003c1803000503000800140c014092000340c485400400c0308499842d6088140144445030301611030000c038140ea001094018081c4104103040070f0f0381d16000550610600c0316074001c101c404d00540c051400742c00160521414480144404183e100c0c960342c91000d142c04561310f508804 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 481672176 1250 481670926 481670929
    0x7021e01140f100e1009060e271b030c101106070302070201020601050112020c1204230306011518090203040614060919060e0a0b091605040308070c080109110a0b1204060c0e1c02 78
    0xc00c1c03c24402e85040203509c80d008103424004c68200e091107001200d40508030f114402085c14458108081503100458910740d6880b00e800000c1c80300c22030b01080441c2d00e02d984e2007a00390304038450840082c2c00359101800410007580324004085595142074009402c107081c841482e07107804c1e400350f0b186407042404641408102d030802c0c0a40742d400c3c032194000c52000c1d000c0300400e44503c010300603031500612002040000038003a10180c0754001d00084401d0040350b950003810005d40064404507511410f110b144503501003000f000ca030203402e0041588426486120341400f02e00c0a9040407081c0d180c0302d00000504840500560740b15090003e4007140c81d80e002c4040128822008261480c0c240080d00a2850346901c5019a010f07a41e019100950b20a02d90406110b6840103600c411010760800b00d10380c1c1044010f1079042c410391025070300307081710703d031079441788109405008051a8001d01440005011400c10740000d1300c0064603041c03400b034a400f00750200e0007402c0043d0600441e40052094803085 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 481673426 1250 481672176 481672201
    0xd0b1f0e0f01031118010201110409090b0a020711130f0f060504140112080304061b02030a030c0e0f1314010f03050c0919020307021e01140f100e1009060e 68
    0x108078240f038204070400c1d964210100b2400b80c00d140b0b042200c0042d4211595074001d600c5420700203c025011a22141d0700e40b20100981540401214101d024001091000819009550f085640510000e00c1e060007182406170300581a055240403e80b01d02c007075040810184140314509600590100e42c141c1070406103c00d0760311140c0c3c0702c00444081001004916402e401040e51070b0303401813119950340c40c0c5081100280849818960701c49401c64886011980c0000c014a881c88160b242400988a5401c058032a40d04a43e4207a8000c0d4081d4440354061034501d041000011480c4000100140303200217820320702d5001d82011807400c008240038818440100498021b00c0d104556a05a915156001c0e00e450250181040402078000c804500e01c1d90081c810415500d000c0312142c9a40003041c0b0010307002c0c0039103044052442d0003010100e040d000b01b000301144102203c020740100c0501c0c102c4051501c4c0ca005014881a1114210100700041240036842c001d2401070782d00c1000d82000b080380030a = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 481674676 1250 481673426 481673449
    0x20c03070b1e13080d030b030f0601030b0c28020721080702010c080d09060c0318020a030206220602160b1c0f0e030c061602060103080d0b1f0e 63
    0x404241442000006030b0300e000c003080c0410002c1442da480350684003248064641581081000e03001d0311007100c40d40e651690000c0d08110084003103441d04400001076584a003020702015203051070140c0025640802035000f40581c0038012071240f5a4104045403001c420341c1c0ba40300d903006810007039041011902425004400340801d2544602401c1582c0e1081c00324841e4a800034140032005a402c01031000c120140c0c0c1ea0f00c428008144101020f40c50403200500e03861040b50007191602d25116070080901104d11802540546014404d90842c0c00300800342e0002404120041c002d600c1c645440030b03101d140b00004001c1c0c0d40040c1134042c4405070000fa540005c0c0c1100404030300501604103ea400d00b203d4400c0001035820010341c49015420020240039140d91000c000d100005410848030030001e02184201c1c81c0c0c3c0d0003072290a0509000300e88406003840042c280c00c100340030712002136107280d00c0365020180060170001010100c070480108100c04102d02c03404641d0494030804c0c9800d10314000c00 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 481675926 1250 481674676 481674689
    0xe01060504080601090b010504080109111e0a090506030c0a0f0501080a1823010c050c070509040203030a18050d050105040c090e030a0c0f0b191b0f0c020a15020c0307 73
    0x50800d8240034042e42d6030041441110320007521040c4002469000e48104c5000e0b200e0f5a00034041492242009001c0740b4000c030781e1500523020a1004089100d110203020b00440c402017140b2202d80c50000310b680684030281013282d06004861200e8901e6a0b01002c01d00200064407103400b9291405001510802c0010051100c103410846407210320a1135000180046030701c0141c1606071840c4007101450000c0e00b150403559903103001c51010205801801802400094000b104c05172a01d810034458413030001c0d13400a4044d8400e100c904a85400f80c0f80356030058002440540005507100c00051122100c80c1059959964403010300c428096030013000700181c28002401d002500034006e0f016a01e01c14021064100610090400c007040000490070302c2054000300c64201c103017800c1e06c59040c840440c03017141000b14500707111400081090004040c1d129425103035500380803204401510241c45121040783d001c5106100403984030500b480c0e105101211754001c200c0d1003c900d091500e000e01542005 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 481677176 1250 481675926 481675937
    0x1b0402040f051903050f07090f060b070f0618061a0909030a12020c12041d190506010e0409080c07051c081c020c03092b0b070c0602040306060e0106 65
    0x144035040c070414440048880c1540c81c41144048041c8080d001039681d0070040c024012202c85100d17110300083c260f4142c6201600030003001400d41302e8074040380e1041c840c4050a00d0240442000718030003100020800e07000708008925101d5009a804142030b40f00300450790203a488880341002800365010300d200d50801d940c05160b500b40401c0241e540c1c02094014410010986a400027140154042d03a840300112022241c10200881e5181203030b4200317005a280240003156804490098641c07030340c0c054007040404041c81594110304502070070f001001a0f061003040c100443c0c060320f4034443e2000e03140c0030b0407450703403500e1402d407102d0b0826140d6440a8481e580c1203049001000c1c650396503144465000c00401d54901d201034400c00280310701d00e20f00d000d80744003069440d82c0350000300c000c24100c1000c840e00e00000c41100d0042c680103441040042e1075900e408a01d000041e84904e0068100603541441c0e441c900082d41c1e000300f640c0c403603003040314011303150501080000a9602454003418650815 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 481678426 1250 481677176 481677179
    0x50117030a02061f0f0b122410050c16050a0b0405060306120c09040f060c03020316080604110d1508010e061b040905360a0f021c051b040204 62
    0x290f40e58000340c960002c102c0c0403010516140d00d01001c03840140b0540e038000800942c0c628040c6083d40040540b64a4109101c0c005003800e0b0903442c00c803d80c003000400e4007140300022030500c0a00040100c0030b07810302c032042083c0c01000c101044088024401c001808022b14100402d012003000c00c1d600010726410140300500480d030303801054a51255003039a100100080da030421510301120505400e0f00040103000340410302c9001758140b4900c50141c84240590501c0391002c804900c4100c0b1a2041402c403d281c6c0082c044c4100a040e070446801000890459280710a10249034803a40d1906802a56880203840c42402803212100901244000300103034444400c000740c42d45c0c4d00070401c010001c400040f50612031040000c4d1006020350400070003440c03400400c00c1c0e4140038608032000030b0750f0018160740342e95000c00c5a480c4010032410040d01038055659502e20b0300c0d4031501400c030781c0140746102510070051503100030219140150014080301444e9045420020b03541d000c91802503004020 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 481679676 1250 481678426 481678447
    0x303030c0a030902130216030e0d0c090c020c130c020105130305070807080f030c0c060907060f03020c0a140105011e03051906090209090f0d05041406090a03060f05011703 75
    0x75125a40d03454103010805648038800a861108403494040171188041890b4648a00700c0441c0c0741c0c030900c03944600059602003400c2020748203c800d001042a54805418440b076401070700318249c0d00145e401140d18901800c3c0006141188403020540c0c0c051307071803031280b140f1607090240c2038025240d02e1001c844502640c6000b040d40c807400341c000d0071b010400104003081203001012682d41c400c034140c0e550f40360b050180040c44146e0000c90241218411070f80441c41900020814208685403520f4030100742c1031034803050300690813403d4000c0f450700409100b1408903458900d80140344404200000c2c00390705019203004408440190603000854080050001407400200740e00c240c0c2618001030300c0c8240b02d1805c000030b0318100300d00039088840d10040c011007000010342c9450400c44281520204072400d0310841c0c05000d9403003000a401c040b0446406641441ea0040c5a915030280c4440080b98580e110401a68003a5014410450f5210010889021403004007508002e401c0050752400362a00c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 481680926 1250 481679676 481679701
    0x100e0601060f050f03130b07170402010e0301060302090a0912051c0506210f0705010507050a021002031e03010603051003110f04020d0e03031b03010e1504090816030e030303 76
    0x92107003440b0100c241d000b0400d026505444140c002c401901e80e407440e00c0701a01080c14a40f440c2100c00c0c0003a5004071342080c3c092410f24520310343c0c0c3ea40449403503279903070011122004c80362401c80d0107560b591004000f40e1994024180b007071400c3c203004182880c8501d840c1d04407143e01071000c420000280002d1500300c8442041210080c5100008074440e202c5000207160710798840b550303185a405240c1c2000e006a0302207605008500f483c030990345102e907644015103461240103002400c136002600510300603e0441d02c402440083c610403242800500c0d0081c1103030450b07030f039800e180c80d58002c40104035495050240584c00b03000008240d070703483c0c13550b610b0a04040c40d07032007590b11031300101e03071106001e4030395a05803041070245031014800c42c5000f19400d5105d0b44107551240c036940d612500540000b0580089030b04844007030b0020482c40c1e0760030fa030308007008040300b1050764019160301100e408a03402e24064440c09944110112440010b03140141281d070000c112a4020b030070501c208103541c1f0705c25 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 481682176 1250 481680926 481680929
    0x30705010c0309060815060414010f0203030c040b0c0106030f0305070b0c130b030613180618081204060f0528050c0a0509060405060d020921030a2007080f100e0601 72
    0x45c04c2100541d1a54918002c0040064086641003a004540068003072941021108090020b8a0305590a106c40904a0320b9110480d078804240710704110070070800001d82c00409004d1529400001d00d20b86a9591200080c40544240e00050012840909000e842400c0d01e8014102130699460048070300810101c243c01032013040280e20000c000900d045d206c402c64980c8006024500700109100c036100b060140c0e24001083d13405616000100c00e028800490501445800141403030400c1c4014445003040e20000f030040796030701d4882c05400c40004560180a004402d5180780c0c01c010080025449110081c18034000da0140c03c00c01031051400700a021254001040d2900b40e64844420010840c54400e5520954102400040c1c49009100541c05417550000c12281982d010340c51403010031440c146003014402c2c40d002044807252490003504d4106254044070540d1510301404e9845030304040c0c02e580081e049810143c3c1c1d40000c00028051544641c241060400c412510501200c2d40d03440705 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 481683426 1250 481682176 481682189
    0x130f060f030c110d020106080708060c0d021c0204030b0601030e0102031519030209181911010503040f02040504050105091c0e0f04141320060304060b040e010c0509030705010c0309 79
    0x100c40b4421205481007820000b54040d49040b01d128030f0388004024000c01580c80707110b24a004018011442c4000840e0450044030243c42c810304104602820700e000b0b51000300040201c410001c920b4110040e0350000e44001c600130813040d981848c140340054183d80c0745090b03007230f8241d20410401c1005d0020803c0303075941406c15140d6403500a00040f0594901101c0d4001035408103411040014802036258401c4001520405903811401c80f02e031103000d4110052002029014981803610031548030704042e581c0607000380b0780001c0034000d84d0003140441e50203440940c1d01d88d4652007040314040c01046458600581b0b2400400f0036014404014400d0843c23150961240d08540c0c0800941d80e100d402c400c40140c1c1e6015010b0302030410203c0070405641556084402168003200041c0801148044a13041203028110a29558035070b5120801030504040e07055105036034802d4044c01e5142481503020081041d150184d407140850201441c22500342c3c030007410808441d15241c006a03000003d9011901d1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 481684676 1250 481683426 481683431
    0x60f0819110903120301030501060519030605060f12030c06010501050c03040b0318030406170601020d170601020a0c06020d140306030a30050919060915120908130f060f03 75
    0x100c060300c45164402d68219603454441c00e00540c0080310a071000714101d9108034000c00209585d4805e205c2524000f0380d0743c00e40400203881c200003107010703500010343c440401440b4041060240c0001111103020440c982c1c40b50744046101020340c1020410f03d40502400d00b4114142a001700301d0940e01c0c841d6014107900d40c0d0012001c61200843c1c403c65002440041c01607030384407900c1c5d080082c40910001300b8415020641e078041140d0354008141c011010a00d41d4071403142c0c1261024440103110301505503811031042d5000600820540036041002c0d00309275001d0000c03641700507001000c0c3c07200c85004030f540510130401e0100716503002940054156001240b00d0318040303404105002c44003103407456040d1401040c404a07110b6070243c0185805030040390b22254207034640f260844c03560b0b100d0052a0204040340d00a1043c500c4001071883d10209504c1d1103401d82c1072b04020a0161903100f40c080707414403004161840d541182003480005400c000206021b502c0c9014401015104036940f520249035 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 481685926 1250 481684676 481684691
    0x1a04051f06050d080309150603030406030504030c05010f05010501020d1403060f1503010311010f18050f150408010209041107080f030a0608010207050d110a1a070306051504060f0819 80
    0x46590400d1000b0040140101071030100b50800c034000c4d6000715603600e507038000c10f150000320708050704516000d0280a401182054244141a8010440a00306030103008020400c0c100143c024084d980d0703420001c1d44c0100d959450203001900d050340001000c42800805501110550381600a07294404002c868002c1004000d00114a40201c02c0b12444903403427001002005004079817134a0905600b080e80c1d900b0038000450300484100300002c640281020240408100307600d0804025803107940c008200c03610300c240b04c6942d000e40d50b0055102d00256500800c02c111146400c0c03145820710051810f0072881c2c00c0700c6a0f00d0b0b0f196442840e4040c000e50401001003182c241e400d030700c00c41c0640a140e0003150b445059091107903a40c130140c0d002c180011004010400c000c0e4000c500450440e1f84000404a010707244c8c0c0030440260b070014480744c101691420b00050a54031755400c0400d00380d211030b8066945042000040c20304003000840b506015035041800301071000a1a401c1d05140360b200c0016412 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 481687176 1250 481685926 481685983
    0x60f1e040204080709090203062514220e0915010b0a020106050a030620160209190c05210705030604150306060906090506150306012d03091a0405 64
    0x380295040602d4a105880020405c90581c3d4402844076000b14126620340d500c0141400c000c00703001032010700b14402c05d0145c0701001d01511034040c400d4258100141810024180c00448907401051505c3c84402684100101411400707410b801c007511700080c1c940050400103c0c000d0500c180b16101d0070001c0058641b00f014800e41c0b2400c0034010060084071038568a0520201510003c9031403520345000d1480c50f81070280030b5013100c5542c030f80728600030411103294081140210380240780c1d10030100e0b01082e1248003100e902c19010b60000645440ea220700b0300543d030980c4402050500000b11840c00f051006064010040c2c03079000e4011134001c0350150303c40800c1d00d0080440c0d0300090615091541c00710340c003802c942000303041d81d2600d0b00420450f5514020003220140d00d44c48110151010004030304030f94032840e42c40c01c111031304030620544071040780d20050504c0b00702c2d0b00d03038800696510205020001540001d011340d5208035840307280b5040a45555460380442c60340501510362015404540 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 481688426 1250 481687176 481687181
    0x303040f0c09022b090203060c0f1324030606080402090402030a150606030f021606021e0a0309120f140318070306061d07050301091a1e010305060f1e04 67
    0xa00045501551204c5510f0700c40b626102004103003881c900b2242c03802602482252040d41d14241e0010000c0c140780c0c0366a0250030700c0358010794030005095070821001840c06d4203500341c44001c0c21176143e141907034004810b40c1c42401c02d144181303030304240c01d004080103165404120076410540440b11000c168443d0b1001a01d40320040070000c04000d1a401c3c90310f420745a80e407100c8116012501e0a100c8036042c505848102d116404804a50ac1c5680704101c0105640754064030104142d150302c03680c212242235104089401c02000c0b240065182c500e0b060410484035035040c800d10003810681c1314407042030f0018254080c0c440307034142d0100011002810500ca035803401d4070004903074401c5c1e801d6207460303040c00c00180c2103d0042c03202c0c01e6010650070070386450055084e807141909035601c90950f4241040c0c10064600e12500c1c6404080907041c08259680341d40030076907054040b404104140c403070500050305a95006100602c43d4841454821991316003c0c11107100001c072112500641d546a07000800 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 481689676 1250 481688426 481688429
    0x405190b070b06011707030c20060c090f061303060609060312181706010806090f030406050a020c130b03010b01021b040f110703260411091005091302040f0c020303040f0c 75
    0x10500040c0c05004450b60560700c80054200c642e0b88076a0782794004200c100380084404aa14582d610010000713084800b0b070707800b81405410040246a82d0845000050b1580e080a1008070000d08030840070410400c040c40b0b1440142400300041c0400f515584484000201c02e1080c5014000d102e00381088040e102001361003d4400c0c0e80b40170004007178035941541c2d03a0000b4041c2407001d2141c6404240c141b980001c000d45a040b01314021440c282c1801821582c5401000344001544120342500909070340d101121241c10401040025000d008c0a04050070340b00c5201d001419900700081c0d90780248100b00c00f8200c4008259004500c01c030507418004001c2112090804203c3c00124610341010740c0990b60592680420008801c90b95281d0412901c119068600411406032014810b50a0529104440e4014100b040707180c00280d5420218018203812503480300c0c4604014503810442c40c09200c2c80a0003000d40307200f0801c08503513250281d43ca22001c0c0c009071480100f07591503010081100301060 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 481690926 1250 481689676 481689707
    0x10f1b1704141f050a11011406041b0f1b021005120a0606050304030809030c0a0501020406020106080102250f050a200121020d06050607080405190b070b0601 69
    0xa001088a14824190458007905201c14102e0800564078034000c0316030480c0b0250143e40c01d46594004809561681c45040740f0f60900030703001c01c070000f010028400c2e5100c100d5113074003403c410f01c3d00000304821580d0300440300800d01c045104010701c0990010060031000b41c0c0d800c21070070562002c0300c000e0940140080003540050061030b2104c03590384c414098600140b540f01225055201e885100065a031240039200c000f507400d2000a0200b80b15808aa0304a83c2d01c40660b484c00004403081814146210030980d0642c0d00040e0410009909204a4000702031000003107040800d070440e01062428603215200c0131200d464070b08005d004441e8100100c0c10340c803104603031410f541440d020a060b0001000c15004290000c030480480d4020720140d03240a604100100601588101110094111054580a5aa8807100802e09803100e10082c42d40a00501105890354a0182041071030342e5540410b44c1180104d11041200400080540f100280d1020035440150f48200048a031804800f0b00070 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 481692176 1250 481690926 481690943
    0x60126120307050408010519110408060a0c0908340f050d02040b180405640b01080304081c03020d110d0f02030c180a050a0e071d010f1b 60
    0x803c4210300c0034034081c1c09142030a014818030030381c409c2d200850b0140e840341032000d40000f00003451140e010b92040f00d410071682054400c460719801d0b400c3c603204998440c5000140f107148403455112030b00444c1100315100b1b2808a41c05410b040d4410443c641c42d110303041c058101c14040e82c00f19901c0d900321003400e02c006011284011542d89207104a88000e030b030240e905d4040c403c0758010110119001030340a65840340002c0031007004803001001c2c2e0828011250661540c45419421861141100b4018885003c06441003080e02d080011803b1810f922000e141c0d03200308000c110308840401d0f410285000054180c640d1540e18006402074800c1c4429a1610b500d0407204000c0260000041c1c031401081c500d080100000c00d001034001ca100640c0c0c1c03180301c10b00500100000c04502000c580c100a800740803d600740e680c1c1e00c0810042c80150b00091494000c0304104580303245e005a800c00b80070311030808604545130682c0040c050b040a41e00c00000c02c010020140d000160255401036043d5100186 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 481693426 1250 481692176 481692181
    0xa060f081b1c0f020f03041103070305031615151e1203030929060609211e0303011a09010e0a03030807030c080606031303110f0601261203070504080105 67
    0x20b215801c0e91894280b0b8602d18111800c8290001d510a440700c81101400841c42c648890320f6000d540710300f81076050351500c0341300008400a04148082c2150600340039480c004d6110034a0000308140d00350030840f00c00d0345884040b9100c421122800d00c121240c040360b80403441d0300805404280038168101c4403001581f001d001e8201a815445201c159004103100e8200700d1407082540c1d90500d620300d0903030314810f1400101c1c000f881d00c000241a03420006146080c1c01d000c612200d41e040343c0745510b0b40706980100014100c080240440c070000308580002840c0f13158100008600040a502c611100441c03010441510710f174080c01290000c403c00030654a0401c1c0d591400400c0f071182102e01ca00020b080c5a0420f0400e800b45103000d00070380e0010b2070181143c0e030311407800880f200307003080035010440044501002900280420486c08110b400074243e658140b40003103040200d019200314511240c1d00d51502018070210f20302d05043c440d18117640d56603e0b03100e400c9a4a0050f0b40201680d94600001e = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 481694676 1250 481693426 481693447
    0x5070f0c0e04121b02040b0a03020d140607050a02030a08040c0803070c03031803050a0b040204090b0411180601080f0411030d050d32040f060501080c09060a060f081b 73
    0xe441d11031445444210910030803c0c8045038098403a0302140c611000002c2d2a0006141039000022090800740045010555980006145452050040d03514920366a50045002014002190720009504050340b0300302003020001d660344030f20b1625104105900010404000c1426a414010700c1840300301c0b5100c5080c1d05110200041a01c022008242840c0d003481c400f81903610400101c980000203402000400d803100241c840c3c00410407688240e0704e89100b00051518681039005901900700c41140080070014092601030064000b0484103070b00042166a82c1d016022940c0803c0c0d01c00030040c6c5443e603180c01048001c01352503140e4140900310005d2003142e4000d02070a9040820300701800301814103510703e906e101d0403264040c0400d00003820303401da491b13207016402d812911804100003184c00c1d54941c5021203800f83c005001903008814242d01518104500d9a00900200c072096100352078000d000d440d140c500c1c00361500740581400001c5488a011180003e41c1005c070150390395442d503001 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 481695926 1250 481694676 481694699
    0x5040c050306031006180e01060e0c0a0f05040e0a1505030102030903091503010303050304030f050405031c030c0e0a12060b120a15020304050303010504110d09050706090504020906030705070f0c 85
    0x210414064071902901c14524006070044000321518034501b6155401c080c1001005403c81d80d0111143d5901c0d000005020500080c0441c420240038181a4480d0102040206401265918107080000030700051212042c03001000d900b00d60340e100c0000d88107040f200d80409034051603111076455440841001100e10012008101c1800225520b0611482d021440a1940420300024000800034000500041d0044400c1450400681480e504090340c810010789025076072006200f00c0084064221400c42c2c2501480904560508104c4000740409001c15040c01291041c0d100d103020204004013841050741c0305201010010301010b14031031010400503554000107504441240e8409141c580500183c0700381e030b0160742d000020310700e1a40fa010401018142ca00c042082040007001101da400300750380300f10740d61f140c4254050103040b4070b4048040c0c58100d150307100900441c01040072100503030394a001c80343c0c40b285078105180c8800d05814401c100207410b20b030050002c5149107001c5600d48100 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 481697176 1250 481695926 481695931
    0x8070503161b210305150f0a0e09010903030b030c0d060221010801051e0f06040506060405040f1a0118181b050415050705060f191109030708030a020303150a05040c0503 74
    0x3c841c50300440000000403001c07103c2c115420400006500d8003010603161980ca9007a1b01704000340710185044e00ca06001c1c0004406540c1c132840f503903441c01c0391300400d034050140701c4c41c01800303c014254440880c4080340e80005514801810140d00003222049440c0030202d0045290108864079195070312000704a008143c01d40e0708070f00e03a40030140c000603400500c4002c0c0c2e104000a140900302030700c514060002915018199540c0100700344404115512244102e41d0304148000004c246554407819900c86601c0e680012410003040c034241003405607a0f443c24100711024111821500c43ea030000b640014560407a103d80005e00c60b4805090b016031100182054451a4004048a400707445042d0b0b1240300315080101950400000070b022418504c07000d1758007100301101c004641c040301601e01c0445a514418642041020900c90040d0400300520001703080520f004614016945034003035900d000c014001400c1e61005022000b86440c2e0404480060a01820611807034410000c050070b2a00708 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 481698426 1250 481697176 481697213
    0x70c060e0a03030e0601080c15031506070f020406050102030c03180301020d02040b1e0403020a051011060106030905070b0414060c120d1d0606090c0d02090d0b1608070503161b 77
    0x70364001144000c1c0214040503c0c0ba0010117503407401c09040750189d8990802050085103051248191483d5102d8030020300802d440748824900380800c1c5c0c410002241c1c410380180c2c0c110340c014051900c26810000c200c9005203152100760f0201d800700e07000a406407054206940d9a1400032400251601800340500006001100241103d45101c2030042a40c000c03848065480b0300584404c01007800c00c414015540748192405010805281101518107202039000d0f00000740d462061100703021060007000007900041e180e181c80c5c640b6003406401d9070054034442e94800c80001580100d01c040400140d00c0800001040c540c6030101d5040d20402001852a01c0015524030080855103034030220303459104131001040020395480301d1500402c10382250600413107041c0d0030030510240d9a280c07040910b00510880007042c0620f00400302e42d05076500d0003810740a103e508828400e5440c1c1041c281c0350b01c092444132012401007038810803142080c141070a1807000c03a4418102041c40600da800c400300030407 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 481699676 1250 481698426 481698433
    0x50312040c0e06010903061a0d08040611060412030e0709060f0501091401140901050904020c010917032203030207082701020d020705090414061501080f0609070c060e0a03030e 77
    0x1501e0030010840c040440c1c010f400200245c3c4144009040707584030009036145040c10840045c1503501003491400c90f400207890000340810304000d000c0e4080e00130303803900019030050a6203080907900c01c08030400c01e00c452014592605100440d0316010850721004140129050101c0c079a18007907001082107501420380081c00600011900c10700c0f03103d08040f41d050682d944041100301006d10f240c0741c0c100a696a04000c0208035401203a170715400540741100b51a0000204160b051502c43c503050301151900340071f040c0038000c00002811032071445401d07440c20304484114404a203400c900030b10400741c004040180120b0045100307051203940d0200003100513020170a0214076001039030340b0007100500d58016844641c090100741407000c1e0075501305201d0340710840c503120903400943c2030100032605441c40c02842c42094099603446807040b5003103108074242d14068200040840d10180c0000e250390184000d06c141d02c030800030310381d00090700304180b4400d81d2a0007409103401405002c01c6c0c1c004480f40d22 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 481700926 1250 481699676 481699679
    0x5040b06042637030f03050c040909030302030a0b01170f041b0602010e070f0b0d150801090f031206030b2701050c0d0501090501080c12010f020d020904050a09120e0d050312040c 78
    0x40f203c0e035001c480940c258079042d48061000301c0440180000511018000380700b8003000803501c0150248109003803003510003507100c0c03a02506450807121607108880c100101800010300d00c0b00044400d43c2c011070600742c4210305607943d04122031107041c1202122400b4010081c0000da90382e0640c81071007038030024410b891015035a55284681702c035090051060b007c0040110040c000ea00d64003801080181e06070301d0719003030755a14545084802181060b9011295801c02004050740300401208112008008002140c1175031500751402c18000d10124140782c0c88079064440d2040590b6a82489040740021311191400141c03a03c429007089140a15203803c0100100d0503104d0350140b103041e103d481e0000e24104d29181d0421282c000202e140000c00d55840045400c1c0060900007080b030000044005a035a19699080c03000b00c0710014101c40d91a454512404005180148080e60901d01d0b80f4110784c1c00f511040009001d1102a4002001440300280000c07500000e0b207061485140a00d0301a8040c5 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 481702176 1250 481700926 481701013
    0x141617060a050f0d02030601083a030c05120403120e0102031303051c0c0807090920090301020d06030f0b011d01061d060319050105040b060426 63
    0x10096440c0ea41c045980381d014002410810746200c8500801000040d0300d102e5034010900349079003070300f0090803600940070007000d8407140c80354022000c00018188201145020075480d505041f16081400c15031905000800c00d4811416110300610b10045101542041d107405030a654280c0a101c80007070a0015401140c0d0040c400d0302e00c500d81e04403540600360541d94044400341e004e00c901403002030ba940c02c00110b03c203180c898455a000a900c510131507060822024000080a1b402882128101145080c0c60411000c07032440141d44101540e44070a0001c0009019005151103050b443e840c140f00042071107911f4480030003c0303004021090480c2d0b02c0d921201001101d4400c2003403050b00c004010010607100346064132003031140070500301c00100c40f100050201e50090380c02215071440160203880e01d207854441c15004100440f0200000b5840002140050049104844801310030310941c0e0b08400d040300000030640c0c1c00030180d46d00c40300142d20f23074449514889803c0a50100030f040c1160503 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 481703426 1250 481702176 481702217
    0x60601090b04080a080901030e07060e090a020711040b0f1507020415030503030705030405033106031e0213030b0c03041203200c15131401050c07020909011416 70
    0x55890002c041c000e200520781781c0c40796a9211500050400d907440403020144201070100501601066035400030030b8642e0002c00042610180004007640c0c0704200410004a940945901074042900c012a45104050008150034a1529080e0700400d41d07849000d08c1c0c1c540c0780300600100d40b08a80400500d5414664025000e0441c080203141d40c3c010408200d500380030b4806180d000d4410001c6900c0c1c06c03194034500c0740d44c8100524403030140c984030444111010500917003034064081c40c5800c2100c2c030921010080350350b4110740407100c0158001801308807100d20120781c0d800703581c21000b45185400c0c007601100d000c0d40304940c00d480405003244065412440782c0900007032440440180a0010000310380140f6550001c80200100c0c4181c0c03152440c07422100b840584100f01e039032060102104a401d08424482039200103640756450041040344030f901c198241c1e0b6420b501a501502c095548002c03290040191411002002546408104210101d203c24082580f01540d8070f01d104010342c541c5101 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 481704676 1250 481703426 481703429
    0x3030915010f0501090b070f0602040b1b01200a0207090c0206011d0603030306060f070c06050a090f030b0a0e16080313051008010902030903070f14120a0903031d030f060601090b04 79
    0x100501d001b0000c0034040006041641e02a11940c043c1001a56580007281d000e81d00c4010341c4403000c246d03810b4915000c856056040d155000034040c0501d4110044210754000181c14413411003c5002c28185208020b00c1000d0701e142d11082103401141d200295641c0001d2065100081a1240b0601d5148880340c4c103d0003444094000c604603161541040101d1704480c0241e40c0d900014040c0d00c021915024006001b0000303601c405541761071512004000c96000e400141c1c0d15003000070200000344084450701c3d4009907031000040c035040c5404045080c41900c07204200b843e07590280200d222103001c40100381d04c042e0741142c070000301e031380b00b05103d000f000004000021038040c0b401001081000e400455105000c41d065034989441070b9a07102040d60034001c1682e00c0380440c0441095004100000890001640c0b030342070521220000080684282d40001401c003c84000300e101c800c0c50030f10300010480c41c001e081d60704013040c02c0d115564928040347c10b01e000804c60b45000a006440208440 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 481705926 1250 481704676 481704679
    0x6080c2106180c030129030703030906031815050a06080c0a0302041104080f10050f01050306130203010204050a090b040b30010902061b0c0418020420130305120909010e06030a0503030915010f05 85
    0xbc50500c1c0c124190010046010580034142642543d41c002800356a001000d800404038001480e08110800b00c045540310b4012800542c4004110001541e41e442c07654102d0340e048801084200b074040141082d0300a0358003c40e502e1240310f2010076900c07404500020303a000d00940c00c10442d50348000041001c0028400c141c0c268011801265a003100b0017914483c1c640040c00140c41c0075500c0e40400c8280101d039001c00d42c590765900408095181070f000c0d441001504841700a200291810b80c0320b03c0b5401c1c60005552011140301d2080010070a4100c001c3c03141c0c0080546841d0076203202d52840c0300001c8151080d243c0506101c80140e03203418400c004901188842d0b1ba40d0300c0b001a4244002803038102c10b084583c0446417044490700f10418003c0240c059085440d1014901e185080da2034601c038805c0c403140c6104144403a20154680b10107a43c1110500080c00c125500d6100100b810040c0540020b0a01d010000800907100c00c00104d20003445904242c14800c0d86c3c0c2c0d442c02440c019001e019a5 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 481707176 1250 481705926 481705937
    0x60103060507031802010f111204050406090207030918181103100c09050d0303020d0614010207080a080d0504080903060c04300803060a0906080c2106180c03012903070303 75
    0x304c0255201c0c0c01d010300188084e007041d25554120341742e114035004001f1480340205000180a1249081601505c00180031000b000e40c18194195005041c490b000e02034400220441202100b880c9400d4100809200780d000b8001196001030030180e1041c40e020024034000d00c00c14160148a00451091050b0000b03036589103215903013001c00b004a004150b40040d41016000d1004210302d021510a1000400c224400c01550b00c01c89400607040c4030700c075071140c1c490790007510320113002c1081c0ea801c03035801003c98240096160754914080001d40111580c42d80c041c801c1720b0030000c098019400034001d0780c0301c00c052440a101c403403291b000c0603480e5044240798842c10044590000743c012004d560803c8004140e099030740d07103d40c05007040b01c1281e40050240e51240d03441e648a400c100c5c041e1040301e05002b090040411140000700d40d1000040c1040000070005200740c640c10409220000030f050780140244044a510f41c5185da030b10711080c000004440354004d14070054580010340e41d08403507254940 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 481708426 1250 481707176 481707221
    0x6051806010f03020c0c0916180609050f010302161109281814071809030f0809030f18040e030a2003070f060c080a1104050d17040806010306050703 65
    0x210003942140014007051301c54404500240d68403031010724802c1034500c800011280c0d45000081c00110311012271504610800c03400c3c00016400400c10b4140c1c0d0060780c5040415084400413002403140350b07520481e060320b03034004c0c1c010090441064104041c04a802d0700203a103034060041c8a40310011114a420928090300b0702021030070b070308038503a40d8407200e9103d90032400544607040e15501d1300465440d02c0e04022400d22410020b030141d00610321250a040103a03100396600942181e8101155206100c90140003039000c0c482003003283e0000b98049140c5841e100c000b0382c0c044004110083c042e1150341400462202000c001003990342c030448554440c407141500050291862060345c1c0000b0030389c0001c2143d00042810411072b1842c062040c02c0005171252600c000403d1100054180c400d503e007445954420860000d0584081d40c03c100c2e0002c60014861421010101c0e680070502204100442d001502c220041001030407640280024040303076640040480840700710020714003200b0b403c901c2 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 481709676 1250 481708426 481708457
    0x7090602120a0311040f0b030f13020d14070510020c01020708060f04080c01060b070804080c0909030409020c03090a030308011811030f130b010f060e0108160c021807030605180601 79
    0x483c00c141c12042440e1519885a0300d9024500301c64001281c240c400000384555045005141d5a1124003007003542b11900c009c0c1d00113107280b0002039001d4010480c544d083e5403002c00c02e2000c0001270800400101192031a1103020b51034829180c01140540a03002002031107440100e4100c0c810714840d005401140e8841d51a04100e4002c9001e07440c080d9655500401d030034411200070000e0500404840e5203a03450958101e1170444c40c4004603001c0c20000f418011212800030507a000e45510703880160700d5800c40707004945180203040c0403a912441640c400002d050700100d01c54162a15508603c502c0340b41d40d080c003c203403030301a042c50201660030400140c00a129800f0507801604502040901c034801d900c841d640001c081e003045400803090b01040204d00d8008504a001c0b407801c1c24600300900c2c0250280142d440c00e01070840c01e1001800c0741c07a08564407a440812801c10409500f4503e040074600140103003403d00515024880205100950000c1501c00900c900016511000500710045 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 481710926 1250 481709676 481709681
    0x231f061809090c0305060c0d0c210c0318140609030403030507030f121b0906110c1e030a0302030a02120909061e0a060503060906010801051018030b010e07090602120a03 74
    0x820550f1545104400400003610a21619000d010322121044c1c03501c4a507500035045034807150102c000d00000502c078808000c80d12001c0b80203409182c0000a940e8401e2500b40c0c06010103140305a400b07a40003840d00c04100705020714016444403001201d40c0d40ea94500250307500e11890002030080303902400b07400000b03441050000c48160a034989074068040341060241502d420007002c070180c10031080e0b420788965000c0008001031019107490042c50808400d103688a0342e074070305114016120146150410200904105c1d604e800103000c5400100710750034025101e411540140d0018022050010300005000c2c00792440741d13400920201c101d417030750000c10954404841c10381b030b0b078604a580d00701a2659400710742001081759403241a5240f41000400c112020010034042c14811460014855a15103140b4420740c00c0003420507000394091400404caa0070801d82c4010000c012070340022a0b03000b8001c44844c02a01da80e281c0c12a010744488007642c8034080c2d84c1109280007000e1004282d442d01c240c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 481712176 1250 481710926 481710941
    0xc04120501110c100c02030301260c210105060d020108191e02073804050c0d0c0602100507020c012102040605030103020a090c09030303231f061809 65
    0x14400064500d0340b25040011a4026600705489a00324a2810485451078080d41c0340315402d600c00345146604004082083c068504d4074041011007110121154040400402c0d034500310041481404441004001444420759a03610101d54202400f10b0020705240c2a0229000d0707058503215107a030789081142d188d11403020f58841c0b0b9603480d03061808100030f059030300741054515071102607030702d000130300300048200079011541c201c104095034081c41c405200004040007280c01c08070113046448505001e4600000c202c905944000900d10074010002c2202e070400854119400b44c0f5040b140c0310008008803003040319040056001041942e01c3c56200d02400190400c0790b8580c0031450b1242c00b0707100c0403604260800000320704000014025483d00c40b203010014240d149050040000c2034030300a0844580d4400107040c5a16821043e4100100c44107407035034036001000c101980d00d00f071030413452101004e0141034805002400c001c258640b00d5400510010544020381d01c4c4d061400710208020b00f5070 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 481713426 1250 481712176 481712183
    0x30d110d0c062003010906050307140d081b01050f0609040201120c17040605090c030a0f02010e060c06090a140f15040503040e010f180203090606091026150c0412 71
    0x10364036801030005a0f0f0714620f100c45201ca402c0b40d200d41c10f01511404450654100b18480d070311440040100d602c4240c09000b0303c48068400b00046021b51070042a02e008072186854011000c06200810b4441540050312a00001c83c02211a89681c824042030f0102950040e00003204d104103113280c5032040d000070341c061415240070101c6203e0051007018032071081d01d04413803041c1c41d03e0034051403a4040200c0b03079940707008402030085040c15650f4007203c00e0541c90000d060081c0c11444003a00d46d902c8041e40c003181d00080c1615103920b003400030310340c8410f04034000f11107560f16030403034400350100001d03103048600182c40107000c200480f07883c00b50610402041142c1c948400c120200349038105c2001716008040c021005c80c0c0d51400c1c0b0b40038540401d101110025090b105000b0082c840b0700002d0080e80200056607043c045031100706284000c0601500407001e160a6941e1000f00000d0000c0509100c00c20340c8269505d03840d05a0341240242c405403281030102a040c0414031440c50b840e603800d01200e10 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 481714676 1250 481713426 481713431
    0x7050f060318100905030c06070215012d0e0618090a020d0f0204020a11240106080411060301150e040903083c01180e030a0f0c0c0e0105030d110d0c06 66
    0x1880410f000584400610071981034001050a4410440c10040140c01c0880c03400504200c51440c1c1e02c4003010501403049558255500c0c4503c00105c0440070208030744402650502101b640301c01061071940c400f50744041c014000041400906a030242c5001d0082e0018409008044116020003c50340b002d80002e071035801c0344844400c01a41c492009064002c05038031401c800c1540103250301e0900b0442010040c0310003010311205107403010b003100300e4155a45410240540d0303c1d1400c007000520410103ca070f4012000000226180380342c940e0038644a46241d0310315491503440c1c0c040c407040c2c40c05103100402003200c5c0c0c00802d40450031a000b0000704041d0f43c1f01c4046c0b60182106184120900c5001240415a440b00510443c1303908010b045030707041d80e03020501c50a403208180342d40c1c1e4401d00420500b000301d4a50004121481141c12001c0355400c0b01a000049807070303000340900c000c000e1003928824070802c0d10b0700c00c44038080c4c0c400840b000c101c0c030080c00e110301c505101651081440b1804880f52503 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 481715926 1250 481714676 481714693
    0x915031a190f0e0105010f020c030d36170705030703120c05070b070b090d27170309030d0c080409050411030607120f06030c0306091a0c07030207050f060318 69
    0x41894005402400f018030b040b14a549002c0024040c0060110750000b150465034440e060380c0c41c00600507000207402d15111322060948940325400c510350310405140c5642d05079070002c0b0401380c0301209060f41c0109409001505548070419a43c104911646415410105040010078100000324001c400035040c02c4464504996130641002100c0d0406e409088011a0981c207111901c54039551201c10f240080000d051820805807038000d03103203510032141400704c1c404402c20041c9604c4c1c0000300301124201c400407203410340700340c0c90360400b1709014000c1c81003e807000b0b5818815039205407407640010b0741918003424242400b01a0030011700c00d03545580d180c11403008070740b02003141c035114428554403402d40341c4000001c401503039401c4010018203400c1442c00d00100b030403500381c08203d0b54401d0000450a40ca031400c0304e8040304c12100c1c03070304030a042020001205001d00050004a00c06d80c00c3d15a01d948413000c02002c0301103a40425000941403000845d0016409501142c3c089400101d54003903 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 481717176 1250 481715926 481715939
    0xb0c01020403020a1e0509190c0323011a0406050a03090501060e0a0f0518030901081005090705041505040b07030c02010201060b0a0504030218010b07032007060915031a19 75
    0x30490b43c403021065039900309481c4240003008a805c003406003287e80070181c0c00c00b0456002c02251211001a10a40d0b8070350b81041c140c060340c0700240c840410301d034205a4084246100c41300c418244030b2880d501c4241c0340d03a144810300100841c0d081d01c0081d01c441d810110301013022401445e20a00072074580d17580303410114440310440c80207442540400c10100745052034176000d50a543c1c025241c21904207140c4d00f0884544d2010080c0c460342002071034a11040d50302e118400c500c010060340550f401c40ba038141030101e013640c060014402e454241c1084443d014100404542c0d520039803081c602c0c0c3d032006000d401d00091040c003111000d82d00510020415544039100c04500e984616088004164002002c204504140d41c40f28002c0c10b0001c2100580d4ac54810100722500c501c0d0070003820050314038a5020f00d18612901e5426104171581107032407040c0c031040c018140f412640110880240b447d480300e61114407078010140c80b440c0c002d01342ca901211103028050403a6100c081c208428840010100d8803 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 481718426 1250 481717176 481717189
    0xb04050307081b1608030306011404031407030210181701090b0c090f0d02030c09090a050709140a0b0d0818030105130c0602062802040306020d09050f03130b0c0102040302 75
    0x800c5541540f56101d149203001c041c60000301d03a8001c01c03c40040e46003004442804400d481d80300b002820002400320340d404c00c070100d038400c5400c000c0940606001661000c40001403100039030b84266102100c03052444005c0c0c1d041700d0b103007100500080c1500c80c140302c513140550340c80700d501d0041400807c10301041c2d0f44006d00590103c9801c44000c1000c6150f240b50b180ca041d00911000d0240c40100d8040b2240d00401d4035003110401e030038040d000000c08902280e900f0062140740341d4000040d00c1e07040380c80d01051409400000581c244086a00c030101301c00d40018800d505038518000d104069103030550713aa881460700304118a0a038074507000030226590300c083c09610300c0759200483c0158101800d280c2070300c0c0452036800542c119800359013081606100e20044420611800c0c920301184408040150040c4c840d41c3c00c001c082da400803c0702090f4010580000311064410001c0d601202140500580c3d6800740400b0361044900300c01081098040610050030b0300b00d00000058641500c1e078001c10340 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 481719676 1250 481718426 481718437
    0x207080a08040c0603020f1b03070f0f0204050105300106050a0e0612060f011a07060c051e09010f2319080603070b040b03060109180905101103040b0405030708 70
    0x11a80150401041040140d9520044c03c02418118284080990305090900400d002d9400010032501001c40380902002174528281c0c1c44050500e40e03140c0b42c54500700c20400303040124015030400300080f860b0b14140c03210401d8080070462218185064040c99000d5015015a40c0300e039558441e07010070291540145000603207400c0d00d941d086410703c1020310a8175018000e8094480d000002844940c01c10b00152a0465141c0000170103482d6210340c40740b04521600c0001440b580c0b40c180c441003030940203000b4201580f0010020444080300c0c0003000104d20501d918540020800d00194120398000c2484090403c06880e060043e48899a40c01c5000c1d030050f505001c54502c4e01e080304030044d9100c0d6070a9400034054028240d9145000e01c88103490085000fa4429080084002078060344a200e400700100302c150186014413810445c0d0380028040035030140d8007409107031626801a80307030f4091182c042c011030410038036542d1780d5140c03018120000340c0101c509000401844010681440c00390030b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 481720926 1250 481719676 481719697
    0x60a0e0106020a05120a0806010c0512040f03110f010807030e010b0d0f0210020f030a050a27081504151d011401140f181902070c08010c0512150103020708 68
    0xb11a6003000780c176112072004114110360b000c100301c80e6402d07400121a03811210a0903c1c0800040740d2801d00d01788040c030000d65a400c000030400240441c900c00d1540100d0f805040b0b80c2c943d0104000a1000b40030110900a0202d011540400d4000c4e200e5400420504841000011520048800100744061118041e00c80d18003180c410001e602c2c1c80800155501c2d200d0006100301c00c0444141500d134091403101c0e000b071001c049018115507010703200c807201115070815410302d030810044d00140f145190740103c034098402c440012040c48840c4031610f02442d040f03030100c040d42c0c5600c500c0c40060402072002c0e03c5000d60703011240303646400074061900902c10307083d5901c3c2c0d19810508140241c2158a490602c1400714451020711610381340d03908056503d05900c807601d0303030f0358103100c49040c0c0c100015030018407440020480d0601500540303010035112020f00a111910200200700c031f841c051990340340010654074011481441500b1510550900181009820b2850302e0b11105a650000694103 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 481722176 1250 481720926 481720933
    0x501080a020108100617040602090414010f080c0a0302060d020f04030305090306060a050d110321030a050a0902150a020109150b030715020a020108180109140105010803040b0909060a0e010602 84
    0x304641e002410b9a0b0300140140020311685c3c90164000e084045101c400f0700c86c10300340c001040601110360101d94120360003600a1001141c221000968413800b40b0640a150f01031070804120100003051300c02040c1130082c1142c2c485421074003001482c2c0d1002000e4241a542089001d2041500d00d0140c002180662100c81d100c165040516082043c001c0c46140f2407124100c0500c03403a50f81145550300f582d00070744c0000b840400030001c6440c1008075488c0c0c0107000c1806861a07400c0043c00005c51142140c440d007486142c07a020f04000c01d448030b50304e000b03501010301d07011807100131041005062400845d10001c14041120344600000c40d5200002c80035035a207801c01054182400c01410004101400d03280480041c07820009407950012600281046a03e10100341e101e1030400c0401d20000d0f0700d83c020050030100b450404205111030340514925400d2030b00001d84980040155412a1010000340b071401d450340c0c04008003190000e181680c450752144000c03c00f5505010298041d060782d4008 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 481723426 1250 481722176 481722193
    0x31b032a04030b240f0a03140f030d09051c0c0f150c090303021605150901050f0309071e031203050711010903020105070201060e19050c0f120403090501030e1b030a0204050108 77
    0x5001c04c440c1c00e07115541c09074803074101c0c405841d1100c07280c3c1011241c0114010b0074441320300c0315050401191720303000907452101240b81c10b80c13440143d01140c1c10600c50310440340202c1c0220f1280e40e0024040c0300700c00101c0e100c0590403010484500c0d0f0500744c607201c0e50b80320011079084455403013202c0050b0360800000340741c11424020140c04028460320080c000301c04515092420340025901400609140e07074540004c101c00a560b4010b000365440c2031268003c03180c07a8544401ba181e540c9180d481000c1c0c0c01120801c01e450454060803a04003a250403505030745c40c2007a01d5200b42c0192201420446c00c001c03020910748191902841001101d501c01c0d400418241002c031002825a07d0a4010340001c980e030701c0034030400340000c50000210070041da00104560f587c1d000e9402507801454610300c101d050003c0c5001e0580300c08a065442284203840e20341566032608011400c0742c0e01d522060099901400801c403900503a8003040b50b000000404403501c0084940c0070a0075910207911400e2140c0c4580003 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 481724676 1250 481723426 481723471
    0x130f03090306140f2215060e1f0b040602190309080a0f110406061d01230d0501090b01120b03030f04081b01050702180604090b0705031b032a04030b 65
    0x1a5076030441800c03820b44600101c810003800d170350301c80d00200400803a1000f6074141001d0450300040010220213a48420070306d406182c458034483c51040a201d40400c1913000700f0040ba200c0261000c0d03414950080c022442650103260711810380c103100342c0030300c1003208000030660000c21134880c8081c821212175182013030901c0c0102c4010a070710b140a1145041210a00c503940d84140300700007806514079182d00e9000da031401a50000842041c441148056503542c0365071030410001050b154401c2d841c10000c84e0382c0e07418078000b211030140025000070311703204440102642d40d420084880381c000341513a01d010140000594070303510581c0300a6550304111590500c118a0b212050341c59042802c0003440c044d4290b0000c0d0180c0504c0405d8440307a06071401003012a240c03903104d900099440602e03002c0504185501420b950000c0312424203403103520180d641141c2030305096030f00410300d110903141c40d446503148190080e8012002100030b07034010701c80003022440000d00700d80603084100e05844224041c82 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 481725926 1250 481724676 481724701
    0x3090809130b0f010915050f160c030506090303060d020607060605040213050a05180f100909030e0f010c110d0203010f06031419080f0c0a02040f0b1305130f0309030614 74
    0xb509541803043c81d04081084030b10030306e1001080b102d0742ca4016612a44200c018030540039014a034603e07c10300d070311480200032000060005590080c82250100d80e279504000ba500d201c1103c006401c542c624032410014100500540700c5180304510101d101a141c801150407600440c14070708100580b010208281d050034003210014210503a000c1e044917030554032001814074040c0a4072018240d0f8000a040703a00c0b04181640607180620381884083c00f00c1c00d00400d000072743c2010b03600c982d2400254071010340c05401c1034000799900c0552208103050000c01c0086000e242241030313030155210520303184440c40d540305103000303944120300028880c8650301e81c452404072000618285803084440410200e0125415101c4489a40d40c0715230756204da42955034141080c01c1c2000b5081810711006001104041c0c102c0c200d2003100792022460804100c40c035100356101070b902c6240c000403c4412401048401190030f124501a0404d150301e10365039568001111007007920325040810040a2011850849 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 481727176 1250 481725926 481725949
    0x6050a0b010201200304020d080a0c030f050c0a08250609030e19090b01050c1509060903070317070e0d05070311090601211b0216050306010b04030303090809130b 71
    0x3032008101070748413818440704500d401c8104050900000c030015046684140700d00d000154042d42191b10b46d0003130303d800b5140c80c0801300300300c0104413050b81c250b000b20304ca2002d6440c040050340041c0700d440780640750450154440040303041100714590b40070703403590003220b4500c10040c454400001d994401d424020320204899912034411010f40d01c07075a169000401d4600b0946082a40000c0d00030900c1005071880c1c41102d544c000103000e074144513190001d001e811f861088159505031640c503030754042d006480b8841c4c100d00501044000d0701c6082450503104100d07500c0b4205d410100c815441000001d54500c1d295482200e403079111407001d01c2080340040303c030784012809490b864032034100440060a04c01108610480c07810744005501e1500c1c0151f08003031031034150b90345840c41041050000070b44803d509a2811114006c20000040c00c1c1070003d001412107506141e450b0a080c2559805c40160044080603100030100b0b00502400c3d0f541c1d0307003440c89802100c40e4000703101d0801c4401c1c800d000022 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 481728426 1250 481727176 481727179
    0x50f07140a140d11010215160f0503100324240e10090f2c0606120d080403032301030b09010e030a050715050c120f06010507020d051906050a0b 63
    0x340c841c04015a242c580302c140c089544240c40004c11030103140104c0c580651101411120303010b040034004c40c1100c07070410030003442e0b01ea9552014141e0b081d8056982c1d100950781083c03000c00030f00040000c9480d00440b11096102c044040700804400940300080d200c0074150309403140840c40884810301ca01c0b24080c070045c10301d103420401e640b4140502e00a421210304c580c0c0c1d40d0540320341000b0583c0b05694802d40502100d000426a110071003102c1301003101c141c1042079550702c652030124000d407501d844000d40e11390000c030043c02c81001001d401c444140300903000f01c06258841203040f0710341c0c0c80c0c1410365070070241c44482c4030316035072440c18160604000175100c081241d03d40102c11804400c0401101e40d11111410255a523521601c1c08902d01c001c0081c0d4540710500d032000703001010700d00c01d0003803090092001c2042c40a0301d41e2001c900c048a000d41e80c050214504005007001410426030212000e4018000d0301c41c0301441c9403407084108803100e4100c0342c480d40c903401c0000314496403080c156884030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 481729676 1250 481728426 481728449
    0xb01030506071716120902040e0c01030c02010e030d09050703060c020309090604020712180e1503010516020705010f09080f0106080d09030b0f0c04051c050d0e011b050f07140a 77
    0x51500e1050038000c4c90140305810030580f40381c2e07042071686942000d44d0f000da014004012140140314803e03100c1c12204600c43c0021b05010030070102c648140a2140c00d03100d8074010754548400c500002c030040c850700408507014000d044c0300001141c2184030700840c0c80c04c99000346544441004c2042403941c00108014072592060181760040f40e000710400c443c04800d4148902da00b0403c92030040f040080d40c2c0012810b01180c0100502c0e4114103d411603030520590090003a9100c10070f241c3c940c80d00744141c0390010b921001040055620800e1012454082e03401c2401d01980c482c840107040007580c8440c102a03a45400c0300f00300300041080f40f141604958504800150f0850741d03029031409001d080360768400d00d42c1c00403c1c5142003000484005180040840d00c07d55070075000e131803034440e80100c01d03039082c000c405604040d680103240307605018005a513a03410307240308039500e12008031039010250b9461160041002d0190001c00204025002003c0c6940010240030100800603034580c01601c4100c4c03 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 481730926 1250 481729676 481729681
    0x305120703080f07020c04090c1e0e1302041401060c02030d02061605030a060b040f060e0312120a0e070b0903010501080f0705100302130b120601090e0a0f090b010305060717 76
    0xc0d84082225004040f1003006a40f036141d40d88200e00c1d1000d50b07803081358003a1800da5441e0410541804200450f5640428603805003d039001c4800070428030b1103565070011604000940400f4900000060148010b10006560312080e011602c1c1030700903040800861480d054043c254034003000381011150982c8000d0440c3c3c94102800003074805002c40c06800d2060100100d0350f0440b07103822841c040c10350071401e540c4513566400c0b08165101180300350404980c8a40920380c19040120300b00e0740500d800c1450914001e0f0b040480095024000d1481f403c06070307034441d0020140e605115600051070490807140d142c0045000300f5084440680c0200b0980d80918074540200c0000301d201c200b1110212403407400070917480e4041d03000c0c0c440e188030304443c2031409002203000e0042b0800380441d110b000309440342960740c04005403002c403414000d400c151800200040c0081140743c1000002d084000700c04941c1e900640e840c2d04441000b030b003080b41c1c590040820041c9169004044480e0b0311604416040c150 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 481732176 1250 481730926 481730933
    0x10906051801291210050c0316021504150b10020c0f0102010e0a021c0c06030606030c0201090203070b0f0403050a2a060c0f0317240312030606090111030d020403051207 74
    0x40c4407401e00600a01d880743c2d50295100041c8101c00c17001c00307140001e000f146803101a5407482d500c01c89519a80301011040c43c8449840050404010000d2190102d01a2100d8441c00202140e807802c034624152200c01c00ca405807519141007078884007540007044140382c60b00400c01040d03903030300089046a240c8001002d2500c000501c68804503015500d00c3ca030040541a000c00710f4410100c0039280c1003035070b04006407140c0e01d80c0c03003101107541030f5500300f245074200d201c100e0a0310201c0303001a41c1940b010005121200c6408024680c82c01c03450309551610303030303640d40320303414115251002e98180c00030240c11007042c0f404503100c5448001980d00c9481050800c030b00038004586000e0003074442140c1c40340103410513005954003031504020806d41c0426150903440481da10316a00041400038a45468011903414000b40c850080040407040600310740d105400c1c4003007900441c11440c10401f00d015081c000240c2440142548a0705240c0517079568110300305075107001c2400c0744c20f4010050400070714020 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 481733426 1250 481732176 481732241
    0x1509090614090f130812060a0f1409060109090c020102070c150903030509011812150203010b0901030902130c110105010b04050105070305030703090b010b0c160f1502010906051801 79
    0xe000c03c500308154564103450100318070340301d10041980300c0000382c00e48030000120f4510b10411040703424440f11901c40400d40c1560030340348035007160000b109010349014036001c1e00b1607500050600d44001401d5858000000307480f820b0f441c01002d41d60005a10007030189150510380504445061069842c18544c00280010003600c006000c0204c04544203403140e2259000b00d02943d0610081e21400c0d881c2c6003d4101034145610441e03d02e02d03a200c559452803514004c0c0da040b0b489030302c815428290024015400b9101c00c42080760320401007807559021030458401e00301405101d645005a00400307071215801c5441c107802884043c001800201301c0c0b681e12100702d40809030b040c9081c5440b91103032030065000c0d01035079500501c0407090728004034503009000050807408007070388200c070f01401848034103241c0c2071058042c50b5002080034506010442c00c0076070243d130440241c4000150f03440c1644511046541c01d90341c06881e0390b41c40c1048558043c09018400e03a6484014003004407220384080c641c0d0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 481734676 1250 481733426 481733431
    0xa0e0d0c090606140c030910031e051501020c0a1802041e081908030a11090d29010e070c080f03040303060e0a15051005070227010b040b0703050310150909061409 71
    0x21032a03070001e0000c07066119800400543c69440102c2b51120b00a007828005010212025103a10441c680f001035598400030740445c1600c1c01400b10341d00e0a00785079158202100c02d40b0300358016602080001161804409003842140900b4980d10b240350412204030305203100c1103101da9103428049070480c045014001241e4002100590000c0e60085100c498403580c0140d0000301c0c0c0c003481d0b00701c150003800501c0303411402c42030703c07040d100b041045880c1005070600401e00132602289100780c0010380c0540514072025445020b0301515007403030440f000741041c950080740d08400007919a40104100a04e80d81a25041404848140045000444940c80c1c1440d01d1013228416030000c000c15203420300810466029039009410041c1c107010305081c003040280404240c02007843d042c0b000080c1c040e00017080d5426035000b0700ea11454088035850460303560b080901001e0040414640015000051829115160150392a0500140c0c506000c1c4011034245506c61244242c2c0c00c03800c1800c903a1f80c2c60030960b = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 481735926 1250 481734676 481734679
    0x2091b0f16020301020c060a05010b040e010b090a030b1006081501020d0e0f030304090506031603031e360b0c0718060504060e010905010b07080a0e0d0c090606140c0309 74
    0x9807905590500c250702045142000b942551000428202001c1c02241e442d114841e0f114060044d41da031b668040d1000c1c400c0c0d1086884034108003006212003080c0c100148843d00004014041082c3c80307889000c1540f0068030701c004500264801001003640002159500040e9141542c020000103030010303403280642c042c0e00c0e0400000015000313590f82c490300c00d202c500328098122034403541c4a0a140000700001c0d210700c0e00c00d03c103140c190f0070141801b11140003503d9256a5107041400e8044c00c283c501e04040d0070700401e0204198001c0c900c0300702501c040e0602c1c0300c000c0e003210b00840600900300308110f298000c00b500550401000a80100028100c0b0031285d00d004078a071b03690359a6822500520154203d158003038240400007401fa100c54040c14183e8444036000c100d04d90348c4e50000402d03480b82c0d2030014001d070707028040700d07940c00e02945015425001c06811030003248600e0b50343c0082c0d40e54980043d0941d580d501014040607074848091940060b00c2243e55103840000404280c0c1c7c6d02504103d103 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 481737176 1250 481735926 481735957
    0x30304060f1808010c0309020f09061008181009030809060103020f0d0302071208040602060c130e040f05010912021506060409151a370e0303121302091b 67
    0x80360605090b002440040c00c241e00204442d00ca0f804d002005031081280992280a992491502d2031a100c800b0303900407100100600c901c80440c00301501c070100000c024070b4a2404115044120001c2440a02c181151914000036001a585800340851202602413502c40d4003d500600060315030709440b50400d03004594a00800b0711a01d402c918111840c1c00680900c01c1e124030356401c00480340007400988089400b518060394440d9002484c50184200d1090560071b81d41007002003d105480c40c580240c0078001c0b44100a000ba2111400c2d40d00c281070480c0c8581c0900820640558103019103600841c1d0850114018200040060914000c0f0301448010310b6544071640b28541c11400c085004114610706854401c0c07034001e40d0740060300300f0019040180c2c0b00381d940482c040c0c02d68199105001c040b0303030960103005810390101c41c104d00c00e500a075010f100400002c40d0151401c080302c3d101d0081c003040740c0030403a07251062041020014000e580030690540c5000c680c03c00e01c006940600110b888075 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 481738426 1250 481737176 481737197
    0xd1b14090d031101090c0f0509090f0c0609040902060a0903061d030d0515101e0306030503070f2d0215030c070b0405070506030106170129031306020406050a030506030304060f 77
    0x24107005001d109802002003040d0b00c5e0000c0c0d0b0010024140c1c088900442d004011a41e550008a82f1407101c0e003460f07801c0342c0062440c0c03da50301d0408090300111034050000100d840c190390202c1c441c1d82c403030000840810b0701031100b041005800e0040d070761111048003036101c0c0000d40c106107507038034001c2e040c01000568496001861030300c05070340b64417010380004001326003001c81d943c000b4007210041108015020640b481503903d480c01390003000100ca500c00c1c0254504101500c07112b01c0301900a00440d030111f40b11201c6400e201c0a140765a85800031800c941d440c0701c00e103204016410345540c080b01c06840050003001882c0c40c1c800c040d00d0b6140d400c000e100c0255590761403c641003e09030f41159520640100001c03507415030010980007240c410003041e21140e40c84040148505e0110541e66200042140714011014403210281d40c01c401c00b04182c05440e0000d94560003030380c000b03402000c009800862001c1500f0f506010b02900107c00381d01840c83c1500b050300c014041c070803226031481401000c1c4c0a = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 481739676 1250 481738426 481738457
    0x60a06031509050a0f02030c0304111f031d030408031c0501030309030f05031e0a03140402030304150309081909061403040618020901030b0610090e0105090c0d1b14090d03 75
    0x46060300b0b0b40c04540441d541c3ca42303000c1c820825001503600b42e4440303001100b6016103080c40b20300340074003011905d22810748056050003203014200d008440301c55001d140104901c8500100f000e000506184005541c039941070221011103000c0b20140b459110342084010404a50007414400c1076035041000c03414409090b0030302c0352440c0302e4465800400b40300804000603401184003c0c3c59166401c2d40c0034000c0d550549a10000b492059a002e581a0820007042207449400703048203850300040e0134040740d5201161100c411580064803046010070908101740440ea5204c40043d0280c00c0a0800385121142c0280c408281d01004000030a082c1e515105071568040829204030030390303801010780081d5a103030315202494071800d641d498040c1ca55007102d01324480c0110f41e20401e079416400741c83d032268685410001e500e0300141c14502002c0c420080c2d01d0605550f030007003686810700c40a89001103c6012401049591524485a200c1c0c5090101841596514210901907605481c201e03440e21002c02 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 481740926 1250 481739676 481739681
    0x60831020103110f030f04020f0102011a1216080102032e03020411070f05070501120c0507021c0206070c050108070c0803130201050c010e070503011a03150405030d0e06060a06031509050a 82
    0x350418584c00340403003003044d4901c81112807849603200751441c5ca644400000160b090f501500600d0b2001030807081500d1460804412161403201070104507a080f90300b81c041d2a1120045400010541c0d40000401050258409400040c034503840300400103140085420340903003d41e8000248900c3e182c0364914003a078082c00544081c13581000440c10340030071920b40540d96002a102f00b601180b03026601c0044c180e21881035150011654461a01e00030703181c0d00b0400354040c6c850202d500222a4940003015845190203000d1882c802c10340c1c100303902d09010000d02003440080540c410031000840503000240c1410540b508a01c081d8420040104180f00585150050003480e0b80658602400c0880803800040c00d07000300c4409400070051b40c2000c10700314a11b00c8014204a070540c0c86030001505603081a03c00b40e51090040050328140300d04100c2d018240e82d54208200d069501031070501585207080c8118500400e86030a00304243c4120302d00d04042121144036048000742d40b18000b0794a001c654 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 481742176 1250 481740926 481740937
    0x1090911120114010809012306040212191817131701060614030f1612051503060f0108060703090501090b09030715060b030414010e060106083102010311 67
    0x12081c14615a180e81e03a03000d401814220a03400141c904010512110041c4589200e15410404c43c01010b02c001980b030b962a1000342880c1d0b0480d5003001803c0441c0d503600b000500030181e0081160342c40f00464842c00c15628581c032034044802007650500c001420286850110408500c0e0140e02ca042e08202c0482251595010503020081d40b6040f140070801075214806451542d02e41410161a440c4408518041100c181d81082100d00100e882e1030741c01d290342e0012080c18075007811091a0122803005551040e10f00103000102c2c071a0034056440c0074040550301092010100720190b160200e1559102000ba100f20103155980e11002d00340a0290407920303200ea00720020080e141020904a60359078020070096590f18a041d40710300700104907008000894840115003403d42d180c549807043e50340007007401c1c41100d41d0303149192030124100303206a41c0241b0303071600c542c0c1c1d080c5440e02c0454100c120503000b80d282000ca070070184019101e0700400c0c111294080ca0001410020045845ca0b6031240 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 481743426 1250 481742176 481742197
    0xc0d0e01020613020f1305100f080705060c120f030717040c1a090301060b090301050723031306050f0a0e0d09120f050f060601030b0d030518060904090b09071401090911 74
    0xb486e21401d042907482d000580551210441c0c0302e01c641d130713a0300c0a072030181080c012000d807500315803010843d45c5041800703031042060344400d8036a2400f075030000c00c3c4581e2200028140e100e0300407080004280d04151040c00583c42c0006401007450076a59541c1c1151841c090300000011508120201023241c0095036070b603080150081003da51501c0194900350008d402d01c034840e41c206000103414600c21101d4907240914818042e04000786c080820082e50002448601c180c5146418480402e8203070140e140074154945440501d800c00d949040140d80d007601c41c00c0d00c0c5500280d441ca0120f980300b02c02000701c504035598010300101c2854203140045c03040301701400c50b20800410003420000810085e0280700c09890402c07600d6080c2c001d0082030f800d40c10004e4007195042c0300c00c020b00d000c4800f0010004000812081c42c11500000140403169403c0c4c00340d410500130402c116540364101b00c444060107000b190500140c00c0180001c00041c07541c095107051644481c2402d10000000080d43c051105 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 481744676 1250 481743426 481743439
    0xa05131d030a0c140309090c030601020c0406060e0102070b16081809040c0630020a03090b130b06060327010f0911010f17071b06050406020c0d0e01020613020f 70
    0x1490540104090b03c0c0307101c195110710000441000380c00d030000440f0040d1502500201035550b80d030700c0c0110241c10040115065021b482800b5089a460b8401d20028001949404480d039180034002442c15210381c03c10440318804106662a4040c401070244c40079130301024642d5500c09108851100c024581c00343c9400024a100740300802150107600026100307a903a0f0303028000b0360b003500b8880c0c07003021400c040c2c11100380820303042030070800741c000740712640040c1404540d000c1e16903101207132540c00f200c407424840210703091402049401e005a54100e40c00300e4805003141814000c41c03200000807030b410400440c2000f20000c04403402c0d00140c0040b07044e01005c10007083c85003806d0b81d008141c00c90760b5001a810b0828003150078001d440501451001d140ca0011655a02200380c5440d107003000380c032030340241c4013a0000000c0c806004403440741e80b24003009038480c02440a510300e0038950380240030520a60404514450745c0c00a10b0581c03003510101d1150804403940042a0001d80320000d041c0c20a2 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 481745926 1250 481744676 481744687
    0x31c0b060c0307120c02060d05090c1503010503010c05040311210f07030618050c0111150c07030315030b220503071a090106080307060509031c06140a05131d03 70
    0x201d000c07019054140c0201d070030609115680e48201d07080210a800294003500c02d1001c0c00c01c440b6180c0c400340c0d20401400840e40d03403107410070010749452178030030741030300f42d41070000050106d42800c1c0100380c2031140c507041850a05045030b541d0341e03441900503a001c0c01000000c030802580081c032000c200c8920040019210100e003114680303501c88005010550340d4604210340c654001490300904000c2da07401c2009031903503080b61130046400107450012040c05102e0700c00d50180c10380444011a01891410a078655100034a2030098141c0c0d0500360b041001c401c0000e0100089500180326a40c4161103403030007040c20301504040403003c543c03100050300d9840080340d070704104404414550041c02c18013088041c0e0f0360b14100041d080e14487d004100054000740000340003d951900b00745e406c01d0307005040c0e13818442c4580a04001d004110200760100e92100c4c4c042191440c65a590050400142e40000d030160504010900d40c443c0c9031121384146a9400c0065400f5081c400040001441d00e03055941d1074 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 481747176 1250 481745926 481745947
    0x180613080102041505030f06150904021303170c030f0309070f080c0a08120a080606040806070c1709060f07171b060c030417030a180f1112031c0b06 65
    0x1d4003d4002c40d01488030741a01070007560b0183c000c0d2031203803003540c1c070803032243e5150014080078402d00c0488040708007061107000180e079070714009070146044502d00300c04021f185003060241d91554600030300c0d500b90104040c8074945004001c07584120404900070796a502c401c0d40140c50500b83d50300984505110000c0030814660100c1c0701622810104e9100c03009540316800c03192a40032004e00c181c4481d1081055042090051962951000d40180381909144d610350382241014801c9070700c807000888244000c0104045000d0000002070600f04160400c1c540802181b0188954a0b2440304128046864003c100c81c00c84c0100d0060007544140b0b40b0b0f80d03101450310b2820f01124203151680d000d04400240038140300c0055030b10840d000300d44242c581c54016020f404607440a403e600c4d5450b221010b15603d0040c42d01c414400034850120a00701002d00d00f061200750b4484c90826101304150403080000640000c20343c1d583ca1040320313880c4000040030114000a1002c094004e070841d80206401e03652 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 481748426 1250 481747176 481747181
    0x1e090c040b0703200d080a0c09030813030201081e04020607021311091e031e10021227060a0c0e130c09051012091104141015051806130801 61
    0x10800b04010b007040c1c2003030340180948070b14114107410700055443c000030300c0304071f030a4020141d10507407401e0a21015450ba210401e036a44540c180460403d4076a10800031943e1250351158008008442c54590f042c140101c80e20081000d00068422400410064155600e440403290302020b002c5e0104503004001c11041500e80000007583d20507055000000c884090805514020420040c00340c81c10780c08041c000c1c20701380024a0b03050024803c1d03440460754a10944000c01e08000d00c103903c9040703450003840c40340c8000e070300c5086102c0580d2820a03d2442c4000011941c2e0000f15104000c109802204811a290102d152450b40e128000216040d075039002c170340c041001e881c00d40d61030300c122039181c00901c4a0004104580d000041c80f61001c00a04101d551102100c170b44240019a403040504000030300b902c0b12038251a010003c4d12040c4001a10000841c000034481c881900c1551084500d0241040c00b459007400d040070b0081102402075030f200c0c0100c4441d0000306400150340d5031150401d500 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 481749676 1250 481748426 481748447
    0x50706110a110c0a0b0409090606170a0c05040c0e130f09261608180603010b03100504060b0f0c120c0f0c030102131e0b0c0a030e1e090c040b0703 64
    0x54000d424041c840b0f402d0040601c0c045e50300071480e5514262409003d040240598081680c04a81d500300100b8481400040382181101140042003080b070142080002c0c1149030b0300c0316106514108034851826000b90411030107040c103c072041e50030580f005420f030140a500030b40707003851450005040104074016041950001807a25110002d2200304000d11041c4540f04d584405106030600c01d0700051017200061401c8108440c1d045083d442c0080071030440d400a80042c01c03607400101c01c100944501e41c03c0b200007010102c030240a0383d49000304000e81c1e441805803800c140d01001841d0050580704001100410b0a1034280c240d031074200144403501e0710846010b89050b0f02820681516070314050080d20006101d00100502c0700d413030041c914004401185031003443e0603401d0000200081c1040241840b43ca00c0c0000c0c04201c1101c3c5401846594000001c07441480702070400d4410803030f02081032804140954080725a500d6a0050500500407036204654050000500c0760826074851200607 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 481750926 1250 481749676 481749707
    0x602010e06090c1005070501050f01061d0603070309020d0b010608061306050a0501030f0f0f0204080c0d0c0506090a08010903031401150f141c1517030703050706110a 73
    0x81400d044400d51034075425100741d000e541c46503002504918103904010418295801c02503d410030a607902401c1d150102e680304180301d0502d0041250580100da1001e01c1030031400e06903111024800005c0d16400058404010541d89070b1400e0300315100e0140041c03001d604100c000ca102c0d80d440c0d10017803c0100896080e4060b071043d415820b050401070040d4010b4500080c510a946403d02c40118000e0000b44403014010f9120108606920014400d0000d28108254003680d84d030f08101c240c030300c2c120100400c14020049111881c01081c0c2d600c1c1841c007624012102a81d0381c860032000240e0341074042d003100f5499444c0c06440f10406406920049000135820780b80e070156a81c40f45a501036203855112180401d0881c032022050300d1040800410200340442e141d800d005612205c03202040120081e901c81b15510346207405600c0e10540b8078401005d100c03002d5405503c010402039120302409100034140180854000b00b00011500f050b41d440701d4660f00c0c43d0f1241d400420043c181240304940b407 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 481752176 1250 481750926 481750931
    0x918060e0f27070306020702010c060e1005100503060a0213051003051e040506060f030f030a180801050115050f0d0f0c03050906062125080c0414070807030902120106060201 76
    0x6901d80400501c50080b50041030040d0008914640320345010b9488514101d0401407121845000603483e8418030f200c10707285e41c008080d90400c641541c070440d680030300301c5002405d07401020402ca030b0300020043c0c5d1200da07040d005619500000f80700d550008103a080103034130214883d00c0c00001e80d410380c06140714100c2841449451041c110080b82405400d6401030042c0e08140001001030801901d149046e440c081c0c21107811a030204c02e41c41c1150403100340c02c000240c60610380254012501940405000398100800c0b0035450003c2100d140443c01c0c00420a00c0004205000c1010b42001a211140c05680b424000004140d41c1c2500410b030700c02203400820300d0200443e074044800511107201d48400380001a6010035002d0070200715070345100c10b811610405201e200030311000402c2c00c66071203d14a107498501c1c185442c080c105014100d0550156103044401051030700125420381e00300301d89081403402d030344800320110040c0800c290301035001101161a413191084c158000303802c41d04a0f9008 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 481753426 1250 481752176 481752211
    0x31214070522050105180f10120e06070801050919110403060c08150646080c1903090606080714010503010b0315010c0b01080d0906030203070918060e0f 67
    0x1c4085480e43c055640003c0091007004443c00b2500c0e068508508002c00314214441344400040d0194142c120080c0007829040801052080e2402100024190800540781a18140c1401040b18205105840c0300b03500300c00104900105440300b08a1659010f08103000884c030b80d4200040d41e9000e403004a820300d140c1041445e6051058204034000c107094003418001c4e002c4402000441d4000f40d0b480301c1c5c0c144401c1030000781c19030700031480307c45082d01c06880024810541c0f0258005d842d00541c800a10407200c0c00c0003501c1c50103800b111039004c0c9150100c4441080315204600034940c1070001011545041d101081c103680001d524002c0f01c00503024031650400007401142e240c0021301c40c14002030018001b28024140f10000341d2503480044c5080441c148250701d0b030f01c00010013070744401031a400002016031000d500c04002006405a4241980740d8248000014403034005032142d4031000075103400b42040b50342c1c07940214000701141ea0007981a41015400144442000c3e607040a480c96400d25 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 481754676 1250 481753426 481753477
    0xe03030714190509030c030a1b12080708160209090a110105040f030803060312030c0d2003060103270515010504200a050f030108031c0e0a0312140705 66
    0x45a82c07050550106104a89051030b05a6543c2c1015030005c0d490b0084000241c05034404110042010b4004c000907890401c00941d071101086a6400074148801401140008287c0c41412990b02c19480321699548800320a8411200700b2200c1c0003d6100000000340003c0e41c41c0042e40c92043d6028071400c5c105681907000540c2c3d80d100e248a104c01d40003510300d08201003161030f00035507030018002d0151b0302e0101e084100720125a10450f88000e215002084541800c100e511612465418501c1c2180700a6240c482034040c03400000e11803410151501c040914107510190450100b841e04000701010862500c0c28548920752409c402034403403114000003406103428020480e000c0c583c02c0e4507090498402c100408070340c1c02007041c0024000b0400c031030a07048024900540c02004c210001e10344503004140c500c140c2103c0304415990b445d0900f03806071011311000c10296600d0b541414600c4401c2d0141003600041c00081c0c50b0041c0c08041c440070010616000030040c0140e040000400800c0c101920 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 481755926 1250 481754676 481754717
    0x1502030a0e19030b0a020405120f06010602010203040f0f020307050402031512160b0a020a051c02210318100f060e130302030906070204020c0a081314031c0c05010e030307 75
    0x40700b000c0042c1021400c0020807844403606403c00100000540f4154540011401e01035504400c02015031080201400400050201c00d014080501c029495400c0a84840c0000b91307001d100545151541c98040c030455074100443c100601c00508259100d02c1c1050030740001c9850300408501501d14002c6490b0a50808100c0b001e1b2203d502115a0f041400c0c0f008488050300b04202600640c072880e14514042182000005084100c11003801940141200000e0800e4501e410400c0a440b0211054412048480c00e40344e20042c8055100036007080b84804615099080c010140c15514140e0308a254041c0e0383c0207082516000d103240c8000b500d40303a0841078144000d4002034016001400103207414501030f4000e00c5000e0004101500340030342c5041050411a00c3d40046610b07a2001580004604480d003030040108000680300e03c24114510100740c071001a845150000100d405440d0b600c1ca01070100c0d000b0280c0c006008004000408448640e20361003540e00c54080766607128200304008801 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 481757176 1250 481755926 481755949
    0x10b0114030408091909060f060804020307030803190629070804350105010618030503030f040c031208090c06031303081b12040219210c1502030a0e 65
    0x100c1401d00d1542d554a520010340c01c2481c0455105c00900010f0302c030b405c030030384208002d00311582000420603c1e2501050748803442e40d10410520000d442044056a40032580720304032600484003e940e50303100e1141c92030751003000d43c100040d0740c0340c04404103405003e00c602d401c03050a000c001c64110648420450341c40e0044040c002c2c1150801c2200788001c4003e1140103548448001c00081c800a004900801c04c04080e400f00407070781c2d520401006400d61080601c800242031501c0b0301486401c54a64941307d00c0002d0600c410020028040f0301000080c641d0003000359000003400200282c0c4403030080c05e40a0694410159115034540c0c0034442c500320007200d014602040a250b05512182e0f41920110001450701d910107021011030980850803400034145088000514410361a00e841013000e025010024403001e5800520280b004c4600308000041181c2184400140a1010320301405140c040d1f030050000701c0c1d551400d00c0f80b00340e00000909144041521180d01039400c4005212880140 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 481758426 1250 481757176 481757207
    0x5031207090e0a020a0509060c030915090a210206040810060501090b0a0e01020c0a080c091015120b1c020f1207140612010b030f09151803070209040c0503010b01 71
    0x141400f040581d00f20b40c1c014540c44005040440c00d150800c4001103182d00032070b4040903143c1000a080790545846216040103110300c0d047e40e820300d5049408240a5001d6001d011003064000b02180118518001c122143e0f45d0b0040005a480361203e003155240d04002c0d114070211030420401064070b601503545a803d44402c105001e06011182000b110814403840d1030a0540c02003e80200e066201e148020002d84196001402030600c0813040c0301912034020080e07900326140c0c8109101c0d1020180465000c0349503403401d40303600000411840d004041480060780d0201204401ca082d0000001e03991006d68000c0b82c0d0740700760002103820302503c41d00c0f543c90a480c0b03411101060044a03184000c680210304c1c045c0585041104250007244681403c0c0c1003440d40708404810042003c000d0b0b2103980d8400d801e90050246851512008100710501808151002e410b5608a41d0025400c2069920b140d40080051a450600d4141400003003020b010702c602950a0440004541d40a8559844204e46 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 481759676 1250 481758426 481758449
    0x130c1d04110c0115061d0409080d0617071a0403060504030225061407170a05120103080d050c0a0c0308060402192a0203060f04050703080d0e0c0409030f1103090d0503120709 76
    0xc0e013104020051031b6a0000f01c8030060305101001c800e00090bc52400030300808500c1010300360411400c94907169071a40b009094800d17041c403080702e2001c10310660342101e5005501190300d490710724081e41041c00e0040038519502214222041a444d005086411101e507500c0358840e00301e00107a0305415200c1c030080900b2040c42440c4460080b0312040050140740524a0614280f40e0340300303a800e80e109820b900580d0f4500c0081940c2801039084e1240d544c020303100b850454904504500085c280c402582c4026044c041e41000280454980360115000e41c44440b14440380c031940d402000d405046080800b10351000f85050600d82c01c1051000c80d200141c006000304402d0356040e14907212500005d208844034055098004001164440a071104500403c00440d40c14a003403080c0d0701d0b1403511404144a00c2c10050440003180d00200a0f0030014900c1c501030700003424a403c010702d188900c1d0025600040b5241d181024403901101900d820322140f41082441e8490031000c868601140c02003020a20 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 481760926 1250 481759676 481759727
    0x40b060901051e0f0406060819050603100b0d020406060f0807090b0906070203190302062505090603041406070903020a09060b0307120905070b09130c1d04110c011506 73
    0x2182882c03d8410540001e191a83c07141181c0007040648650313611120200c0c0160040c01040001e01c3c00280c208d0362134050070015840c1000000743d4542403006642410b50b5a0001c0070f00d203483d9040b1064000380c002d00305000c043d54456000300540d0303175100058000345803a004102c0052060b00d82800701e5452208044c1052040c00800c40d441e8412030040368144031341400101c07a170014400405031303640650098205841d10440807040341c4813049081f85e542c1d4108540750501c50f0041d003652044d03070090f030f0131300c0d102c0d40e452408110f4030103e081492039a108000030008240d61000704501a244251081d1181035a9200800305541c1a4041c140e4400f03814000a0700c410b206200d02d07004224000c002140050a5846444c00c0407a136400401081070001100000790a0510840038a4440008100114491900020b107200310156200d1131202a40c01020029542c0f5049403140c0101c0003503150f600c0e10724a001c1402401100b000d0038455198640000f5010f02030340e540c4003d075444910b48605034 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 481762176 1250 481760926 481760959
    0x412020606030c030309010e190b090a060207050a06030c170a02091c0c051014043c0e09030702090108030a0314130803041515050112111c02040e0f040b06090105 71
    0x201c40d6a00782d19044900b0041e02270310401e548695400070314018640b00d5607941c01c0018415040480c1c0c1090003550b0240700100300d1510f444a902084854a203030001c2d000e840750008680c020405000c540d42c00010005001c0c050180d940100b005a101303d500042c1034803054410a40116080030250101845c0403041010b4101017070030382c18546407450308040001500142c40002d4002c0d4000e1201210b00220310aa07500440000403121006100d21810007010410f0444401c0168007440080005250119480326010001c0d180038580c000d00e194400c1d07845141c143e941e0340103002841e000034200b5015814803503446150502803550920010000388068555038029400640200e59243d100900b0015041d514482c4402c0380001c151140c50040c40e200006045800c020079174540b29107000070140c268565002100d103060044641e040c0900707035894000c00240121b0f400040d200c0100001c22070700c00701d00e45a142c4610310805210000c1c4c0c80d09000e1140144090203032a401a02242408002 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 481763426 1250 481762176 481762187
    0x50106030b030a060c0c0b040f300c02030f0706080411060705190206071a0f01080712140c03030f1b0c13020d06080d0c0c080604030c0f030203040306050412020606030c03030901 78
    0x170300303010f080102000b802030f655880030000854060703030800000e25400381009409030084000340d82041079608100089803543c80501310002c08102800001601001191030600004045000359010707034000a69030b11010b040500c04030b408a6030041c2100c008822854040251101190400c0051903a465280041c0d50235000500c02aa4803030707030078001c120004a00300c07105243c0d1190080074031001c0c103002e41046403035401a0088845500012018000f51440c000040303544c0d50812084040070501c424800d0074103001c66076054160100240e01c07269a49034000030030307903206d07800d2007400b811034a000a00c0d01ca015041c012035210b1f5800b445241e04458507000740200020420000070602e40e0780210303614120034214594041409071003404240306410319241c004100c800090041860135540040c40301011a40052403e1040000701c3c060510820544014643c010003c02ca5810b1a040c06512002481550b038018410030001030358a06020591268880000d0011402c201c40c03c00152403 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 481764676 1250 481763426 481763441
    0x310021e0d0603051c0f020d0807200d02240708010506030603010b040c0e1c080f1312230a0b010513090501020f1b070812031503150604050106030b030a06 68
    0x20200d40340c20b0b0100101d0401e010f03022644811080091180c80c01c5080030781008404c20040c000c1d501721000c1a145650484400c5602c01c102e8981150300380010320003829810703107180b441d000c00c3c422998a249200d40014031000400c02d0380c1c1003070840d903000c2104404148021071b1407400140302d402c01004170f400d21801464110074004e002103003007035000c800f0404568449000740d002079107040e0a0310341e9081802076410175042800c003481c0b00360055114230384981b02e02c00c0140710600d40060110b2001a1040c0c400c4c000d4511041c1142c00c600740c0342020300244030082c03e020124a60203044020381400080d1064140c0d60040355400c06a11340020040341124100c08208031a0325400d450000070000e02c01040c003810310003112600c070900c0d040c84040302d40d00b40d114110260300c1528107000c0c601001a414241e1982c11420950341c1c1d5900144880261000c41c189805126503084018085e00700c54030030b440703020141c030100074907030781e0307242c21425990b4a9090302e4054218441c0c03500800c0b10b9410408 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 481765926 1250 481764676 481764697
    0x9010c06020c0a060c03051303140703050c0a050715080123040f020f0408060f070c060c030b0a0611060709061b0f02220b03010c0906032013050310021e 67
    0x5080c50030078003440d410703d080a0030450b41640d4075080d9844094041c840c160300400c881c0301e503071941226903401829051640c144810302440100b000f0081504c50002c8880311040c1c0300541d440383c07405e860318030381e80c0c04075029082103000801314550ba0b80e84114041c0781200c90740c000a241c40001c409081c01d4543c1e48103102a001a1209100104121640014080000001c0145580d24506400c190608601401c0d94902c521400203120030f440d400403000201941008000801103441d5405400500c030380160350784c002011003c00142140c11603144d2804516400590300c1030398400b9801c9a030891103006003c045007034041404001040c081801085038400c1d82d2100408406400080c51085c10300718a51072400341403503c0781d07200080d01a4044106096000344804021004098002211030050908050b683d43e00800b5034100645614042c0104a0341c0c00c1ea01c010886c030790500341140b401100d000e403040031183d0340b50162500c2110207801800700d03600d45c0c2881104d010b240c1580009501c0c0c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 481767176 1250 481765926 481765931
    0x14060a09051017100906081902130207061b0813080a260903190216300b07090b03040c03030810090c030209010e1206010e280b03070506070809010c06 66
    0x441010042c0d41284d00074940c3d401c648a2a9240030454000d546c2e0320b400c05600758201d9181c0084500b40a40420b0815a044820706031a940d2001c0c410002c1c06a440082c1c00b4a0034040818404001042e1030f0701c07001001c1d0341d020020764411500d07807100004007200500786541005066411403043c0910f104921603075071003000c80700490300c028084010540704031089820000300d00c0d03100306807101c0500026990380054529100746008104d200441407040b2004050303d05640c00307014040010f5140b5038038060b2440400e500742418100b4481101300c82c400049400d80c58040b03061001d640950b0320403584000b1680803603003595000c65941e00c01500c408500440c91a002c2100c0f401402000000026130344d0045c2c89151b80c00005003c051010307407140c010484000c55650144021501c40e05403612012004119141e60985264030f40350724004001c10f4881282501340801070b43c01181d00e4440403800c071449151507904014591203000f1004100801c20810f10211b94010340000000314000c0100 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 481768426 1250 481767176 481767197
    0x306010b090a0e180723060a17070305090d0914041503050f030309100603050c12030912061603020903070e040c0b0703030e16120611070602070b0114060a090510 71
    0x169620403d003503a4a001008421010807500401046140700902c44443ca0280c2035051001e04086a01044005400758600180102c0c007540900d98402c0217005000b841100c5140400307000b40103000580300d0078800d01801020118092203540500d095403113404051100d000840e0800c00280a5201e0110b10050f10060000100304140006c42400307030100080c60307480c540450384a0509070340080518026151440030310210b0000141c0a040e000701b86d8191309068103aa0f40940303940510040250b010101502103914044007213403090041884030031403101d10060341e1040e01a401104182c5070960b2114801f080030010407484c0580081c0101c2c60410800d48034602200f031940103c00640c0400c1d1140500b900843e020858514914046600d4840860410028812828070184060561919a0f0b80500040c0c854401c890646502010855031400103161240000f242441032486034503000c40012a1401e008049903985403041d40c4440003141450204a6149030311507140c010070502011 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 481769676 1250 481768426 481768439
    0xc150522080d020607020609061501030e010b0603011d06030712121b0c0e060d051b04020c010f150902030112031b151a0105040b0306040908071a01230306010b090a 72
    0x11403002d4600c240d010b0640c0c1c1c0361004001c0d203808005810038040358000d00420040c0402980c0040c1958401d00c1c0c086a410b244121040c051314051029550100000000042155602000c031242c006002000461581c60204054450b41103220f03800203c20a00b501c0d1000508d0000080780715800c03828444200b2203001e2240400c1860007204840c401d14218043c8900c1c0414a0341c9544440225412481d250a9a42d0192560a00402882c441c02270040300342c0681c1c0c0d9a0140c1c0d80e001440300007008811142c10319107001e840322070080c000d03440c910b8a011400c45050300850741614484c06401d50b0302c140785d0b502141c1e21154001080d07820b81014000100041000200c030211039186003012850026000010401d4000c0d900b299050044c10030081221058680079207038007900071100081e0810007801c18904900c43d0140c0204268941c1804404072402600031074160b0700c106600903881500482500b80c2c205180000315410360068004000e10f141500040903a83e03005818400d1044e515103 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 481770926 1250 481769676 481769683
    0x2030f0a0b0a1e031509031215082b021209100323071101091e0302070503030d140109021c1505030d0306170a02100806010309120c0c15052208 63
    0x3e0022414a0760000410520000c002920700100c42c80c4030030000358020f540d002e003418036040300094034030740c030f0b40401070440d002196010000c009038001d99840d0300e0560b42400514000a00b954485850487c070301100f203100190540f0b1807000d6000c0b05150500b04420810440b400d454403408050b00d0f00400d201c601d0003401f4a40110100007000d00705403c0c0700102a02c002c01ca0101601c01e41c0c50910400c020900b020400040400c001849031100721a5042c120b04250303450300302ea5050b200004240c0b20f109420740c04506800d1501c50007000d0f41c0d072a15601016031040c02c041b071001c0b405078035107403100c161183c3c0400150303500421a560b1072030b599008241441307055a40103012913522441000308014207030859264201c5603011b005107142590000d2042000c900740c4508002c462000280c5c641d011764082c56071290080400744010000080040000c0324600003142d24661a1900080742800003506000146240e12054182030f4a51b810861600d0f1218118064103501a0700140d60074050 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 481772176 1250 481770926 481770959
    0x1060516051c0e040b060f09040b04110a08090607020a20030a0c0803040e1503120d230411090412030b010207032a0b070503180f10020c0a0902030f0a0b0a 68
    0x83d262810420f502c40200303c00c8880b00702450b40034000400c140004600c00a04072094001d045600103905400079010500824100340c003c0720000d80018004201900041d007144144641b40c00c5800c19030703c01c0022600c030034024400030300d40c007075035040c0d10300d859400304810340e07040c1001d0100c4000d00384544800b1244420b544c040f200c0d54200250500103600ca000345142d00544000ca03084c000b600700004642d4400356480e00b441031003008140c09600b00303416003000d0700d10760b100c2d0a91036940e00c00c030014011081c0f06032001c603500c021003601c41895062250308248116041080088600721030b041c254017810075480c400d1f0440c0070300100440000d10300f0040d00740296140524070b07d41c00d100e270304243d08403140c3e40100010880c103000c41000183e0010072984042c0c0c40d600c805c1102182000461043c6c2136190010794402102909110210360010b4041103d5408403062010684d44005000484c801642d5140c0590700e60800285038011036040342e500240081d200030707078a80d5039450600f41004003 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 481773426 1250 481772176 481772233
    0x8090f03060a0c0e0123030402032b0306052d030c0603191d070b1e030906040219030c0b0903030c03040f06030b1f080903040f030501020705010f050106051605 70
    0x1681d1080d145180d0102680442e000c4c20300740400041d40ea030030010749000041005441210f00040001c086450900990070220740c071749040c1003c1250901120895a8021184400a45840400242460706150701d8000403039103450035000e902d440800e250b03c59100d030202ca4241c419000c0182e0f4a40711300c40190700c144000115940000121100c84003551038020002243c003070051603844035020003040078001ca498448101d55204980c0d0340d20050410718000c0400310344004400c10205003004903041d88160700c00c585607602c0804d50080c5454010481c000035210150300704040c82555445001003d01e028020304890a120f00018200d1855000f50010640030410903001c01c07074250103014101310550204c0f4000c400340061448101000961007109040000a8000c9001418180200c03070180c00110381250003d9101e0600c0741c00303540040301c2203d0b60340c40d0040c91507080c0c41c0c03841058143c4940c0e07a9814903000410f007002c909054070b0402581d19009000c5c6945210b09450f6500c00503008 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 481774676 1250 481773426 481773431
    0xd03200105041b05031b0a050406030f030e09150105031e010303180602011a0d2f010e040c0c030f260412140d0e070e040f050607031808090f03060a 65
    0x70300c0d252002d81c81103d02940300c0f6030810990244020f80d804030326940b04243c40e07683d400610150034001629030005034015a0804d103001d0001c01800541c0300380680300750280d180d2880028038081400800c403412681c8440810070902c590040d584100011600309140428240240c80c0240e0312000a10088e40110007080d0480c441448020310f00a480d40248001d00081202106e1122900001001c201d1610320070644440c4280c10003400c06e000151020b2407410815940200f810800514015540001c0c0440c081040104e1585440c0c010750111114540c0c07009950030b429582510f1803406258901c00b1300581d100c141c1d0000c42c2c000f40c4480320120041c0904d03543e0406041c42110f0f8407900001000304a102c14035140c80a51050484802d404581000a030500845613101d040100341e0304030340703401c00021081c44244422240c0600802d8025025101030341c9030f0050540c100e80000c400b100c403c014030b1240c0303008501003c02800459101505540c5030302c0c40900000e003882400c842d03c05c121a17 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 481775926 1250 481774676 481774681
    0x40f0305150c16080d060f08010b0a031a13170702010807030c17101809020f0a080d050706110313050106050d050a061a060703111002040506090d03200105 68
    0xc4100071000c600712104560110030304108528034682e00c1807248038611803001c42986820800d0050444004240040b0204122a151451801107016a2241107185d41c2400c00300d10040c40c0c52041c510480e0b0f4404000b1090201d80ea441080c2c0900041c007040001041800400c04555508051301d141c4100140d1980e86022510016100040203405035040600d04080000c0b15074206c0800d00c0d110100b003c00300322680d64284031784280c070fa554102401c2407400ca00d1182d00640e0319013100380721034422100400c0203030212043c01080390b440d2007280c0e00ca40c0b0030f44100900e1401030740140103a03406000080364a1105010030509544150b8080c4200401c0e41c60a40901100f8414000603000844882e000600541c071a01c0da200000a03018102c1caa451010b051404108023200c545440e02403d0592203000c5803d000c1c00d180100845400c550082411454082c1210701c00c480039100000c0080d4101024001032280e0203101c54411818403e92034820041d030328800e4030410b04210340ca4008207031031 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 481777176 1250 481775926 481775933
    0x603030f09080d08180d0306050310110f1e12061206060604170c15070c0f0f0b0a0212041404232208030c07030305151005090d08040f03 60
    0xc100096110080110008082c810b200b0042912110041c0d20328103030026888840e0b414032603046400b4100080d1013018214807078140c044d00110b040320340c21001e6a5031940420206000e40c1c05003848021018400c005111351a580c1c000517142c420201c003801c12010381443c0c0c840303501b680700807a00d0348100464000c0180700c0c0342440c0c0100c205401607016089904010300400c9550060b405440028200b480600d03407540c104100c0f02095940081c400307140d441e1107514441441e4020401540c4039448007030301107403a100e802c0314882118010001450102c2c03a2030318864094000805100442c0030b000c801d03000d0364103c407001e0b01c007a20080120001c1c0740d1060041000300c0d061004440c240f12307000300090038401007450381198840c040d8a034900d0743c0c806003500f140c01e0044c004802460131401000340030f29012100d02901401e8825202040345440c2c1c14051105522030300a5542c1c0010b044010000310f40c0b00c0c90203018400d001405003210403e40c4c0da240d8040c1c2e045504014034001c0b003001c0170010b1 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 481778426 1250 481777176 481777187
    0xf05012315010503160c0501020301030803040311030915071506080c030106080109020a0611150103030206190b090c0c010209090c210c03060f0d02060a020601090608150a0506010203160303060303 86
    0x22003000104030307002481e880c0000e446400300624042400d001e84a07043d4a09000381c44205050307a2100c0215525a10f1346002c1c035007a0010f44041d800100d502c00b034140340c85000800c4428004008000203407410a00005803d07a92010780211102120380464602481181c007421024000800190070b950041406043c2141d19a920481c4141e0612402d80f000d0380364141020280c5117285440b102001903940001d03c0c141c0c1401c0c154200b40c0302c00313000005143e400714010b0700910300d00311202c1300601c0320414001521007030303982c4079405a0041d020030081403001c40206440c12070350300003604040b000e90004001020483d82d840303007800002210010700010a900b1021031403180d00031040c48c180221484018000181031a00a074400040001250742d174403490800568001c040f0340c1d8030000644c00944031002031060340d0040341481e4012840300404102e014001014062840c40c503503401c0c43c0c00d000707420058031040c10360108000540d03041c0018140842da03507000c0e031000324a40c1e1451070700901 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 481779676 1250 481778426 481778431
    0xc010506030c1e12030f0d0605040510081905191103060c040e04032d1e030c02030d0b0414010e0106020714060702040c17130b0610020d0c0f050123 65
    0x115042d40d490f5100901c4800e0007050700c080c0d0948481c032415111007451880c62040000700d525030003000c181801c0040c82c5802550540c0e00c1a84c1c24400da84403030b0020340303140141e4010018990040711450305500e8076030803210700c0c031400790341101c0340c80744c018040002c2580c20032000d4810640c40b41c0200040d0604210300c0e03800081c0c2c0c0c10003d24040c0351100341461800040d000908004d42140c9001ca040c2254a03021680b01c45103068000c00445030801404104141000d080c0c1da54074540e0030300715107010340318841100040785c000c1c43c41c14003c062410010401602c50b40d9101d0707a110380c00720b041c006231f55203a0b0203003003042c0d0409010350500e100641307000342c40d40c0f00c030f00c40360005200d40341991100015248090f50603900491500381218040d1801d41e84610102210200003080000000200240210180c080e0408032901d071070304d009000200140c09804005030b401082203000b50744c0700395550040c4034040c0100c3c4182c854a60390b01425220880c2c0801c0b20440c4a40d000c00e00340141950340d03074 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 481780926 1250 481779676 481779679
    0x7020106140a0501020d0f09080d03051e091e07080604030314010f08030a0c03030b131b2321150418030c03030c02193c02040b060c030c010506030c 65
    0x2d124503080c0000e65501c20401200704011000d04442407880c059505078001e400d502c41958444602d420300280248012103415601c000c140c0745010603024880c155070b01a100c020040c00d1020b40d1101d520340311101c1707040c400005101d032002c001243e600521089004034807a0b58041581c1031f440c200c5820f20801032b0000032440c42c040d1002c0200f1030000084840d02038540c145407825100c6070030250010304400366142d03080381c001001d07490f0448141e4400800740701c4000b03198081244000c03007107900c9048181499a088024100c800d04428150054040d1200707506800c0007451b1080b580c0d002000c81500d1440301024041f806d8245860300e0f00440c090204503501640c00c1241a031070007000c06402c02e001070305260352541c41064641c403d201c0e10b491200d10043ca070f40018998980900507400f62845900480c07006c1c86a2040d0a0300e601c02c806c4495004501811b818045408000090080c20382d19540b1400800035a9202d074000d0025025040049000060030714180003454100b00c6040b8485 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 481782176 1250 481780926 481780939
    0x6090c140a0b030105090c0702120f060702010e1e0a02100509041107050a060507030b0a0807080c0102010b03030a05030a0204050a0b0307020c01030507170c070f050615030703030801180605090702010614 89
    0x1401150b0311a0305803411144100c0c0c00c079030a81c44a000303180680c803640c440a90040e45401070310a10b0703000010300c00050850002100c1c2e007030f0348000b0100d00721111002000e0841c0c0007052042075203c103031007011105980c09800d44140d55001d500055400c81d0039107041011400101e00d80c40340e441c1520a2401545410070403074900003c69581c1c1da01c84010000c0102190340d20008542c4030b620950184882e40e4010300b41e081459114220702d0384e140d60303c2c466141140300c6e40650000952060245450001c0060021030070090f83e8030013034410b81c00040c90924015424400090282e43e40500a4000c187d1925a240c0d20304203c48001c0c140302c0702d0346400b41494101018013001c6a401442c80c40c500801d1682281a5180c0f60f00980441c800c551018004000031104113040c480e010500c1c0f4064040c01c40383c04071400c0d02000b4035845410600c07003d8003181d00d160040000160340340c804d44d8552114500020283d4592000900750542904d40c0b10060b991340a041c03081005582010302c034980211070307c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 481783426 1250 481782176 481782179
    0x31524150219080304050c041d0f010b09040f050102090a03110f0102061009090c0503010f020301170c01051b10060906081e0c04110d090b0f0a05160f0c06090c140a 72
    0x80344150340300000800c140000400a81400407d0240c018032190092090000e0303211101102808600e40e54203403000d014091028850000505c50782560a4018154207981da84685403c180f01d4100131041e96a95001c0150424546e030b0040140d000c0d6100301c2050505400c1038081c040381801401207903040d075000a040c000510050b000040813141004001305400f000c1d4070746107290b2440b980c011601503084c02d100000103506030300a10305039102200c00c06000168400c83c1503030380c0b0101d09014041002084012421800c22201c0c0f03010040c82000c58a2156142c5100811500340d0ba0001c01d4181d96500144800a000e01c0400039200904e20400b50048a5034000c5490310003c5403800d204603034070102e03071022007d298103441040c61034850402000c42c440c04d2050300c192045540d000281c80e450f0016107446c141d48a001d019000c070382200400816403500c00d46159011322914400d010695150f13800051090094000040c42003812400040c6841c1030b4108107004c8a0078944500c880820 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 481784676 1250 481783426 481783453
    0x715080c0306130e010e0114040605090601030b06010e0d02131508011a04090f02060c030703080604020a1d15071b050d030225050d2a06090315241502 66
    0x143c8a2103000b80b0480018031030001d164480c0145280c4403018030550802040f036089868001c0602d114038052803003440a6541c0d46960340e2510400d0000034452001d41000c24081e5100d680000c0e40d0a030064149401c242c16900094180c54980d40d01882d410b49944200f005145001d11190003440c5040082c000d05a18805140b00c6d00c0da900522070146507524a4002400712001c521822250050304481c2d69904810045840703511540301034000c200740c140070614508161003240c42252040c1d5588452600360382000b200c0f41403501803194090740d0481c0300c1d070790401c8410040540a110710031464041c03031120301500000c2038070360000d07204110318030500c03001c65008620a2950184540765601d90300c0d201908011940ca181c018582007400c51181074100700c10703003000c503031880740c0c1426504240c0700000722605001080c1c00f802002807001901000003441a0a80c0d440088015034046443c00114400c201030f003443c4400300c10a601901f00c06c0101407810301c510f0304500000d01c054006504500d1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 481785926 1250 481784676 481784689
    0x60501020a02090a0f050408220e040f0c031203020405013f060902040902180a1a070f140a1406040c0e07110604050303060a050a180c09080715080c0306 67
    0x101a01944000d0f000405443c89644040d45481c0408402c0140e0b00301070030305d40340d02d800070310035407900580c101081c0703400e078292a40740e00446007210010422a40c0b80d5031600d01c13140c5c0c4004d0482c0c03a0200c3c40d00200000349444044658001107503401629140b8200006082e400c1407541e80711280700022030b40c00c140340c16248003082902c07043d0702c5058801203413001c40c0c000e04072540441440c504c049004101001144c0003803402c0184a8a40306101822001300101402d440c80f4104441c03d4080301000e071b01e00002d024014150041211815003030554a5407004048049641141d940009400d40100030030741122910400b002e80003002a407070141c1d900003e0f130805008016908240c0400180600d100d017031140050b81c06402541c11a00f014603040f40c1e07940007603889510850820701701058a081900e00c4c00e0480b921035013102089100c141c185030040c02071071194030401c00e444c0c2005c100d04404003d442c005054480a01d003006600c944024000200500300e29000081041804125680c14 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 481787176 1250 481785926 481785943
    0x4020903120702030f150a05010e070e040b18090115081501060305060a05031e011d0601120c0312020f01050f01050f151308071701060303080705031e04081c06050102 73
    0x1d5a015565201600000e4074002018600400ca4414142500c0c80c1249035140d0794003c00012005002998940302c00b8452158100c44000008052035280340c864507042d0443c07119800d000e82601c0c80300e082400864050181100e409445a4480d1941c55251480360a010b0040c000c02c0060201840c070103911815250041c801c0108041e1904081840c40c4e45400c2c0b150001c1c007000301152842c844451414207031402001c1082c41c154078001c50029a0880716141100740c0341d46d0320241500ba801c1c0407507a01d60a800400039540d010240350301100041d04010744644403013950f001800952600c1c1d44041c2558801030460310081c48006c01007090ba124441c000c00701e440102c5107010a160785924031b8900303029900000000f00381150380010b180d40042001016550a6036501c8640d42412030094243c807418440180000c01c141c001401d028887c2020f183c01101c44400109004c0d2960407000c0080030965007070310b12040001d540c481a00c0c44070030880003513144080c2442444d18040020b510360f402d9 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 481788426 1250 481787176 481787203
    0x803040b0405010b0616021f0f030e0a02120601210b28020a0f02070b042103110d12050f09122206082d0412050d060b031504020903 58
    0x40071900700202074100403084800a04460b40b42c1d40103980c220300300320203814160300071500500f012107440000420080460a5521003c01548280d0811001001b20000b00701c00340c01407692942c016901c1c21040d0504018180c0208203c1d414115826040c0c46444144503200c40a404040c0001d2101d43c00c090b4404208040352510440d80c0062800400300d0001440840e88000b9031440481c1d00212900c2c40b1544560848000726194411680c00c0e1141703004001110106100c40240240c414020b00c00c02d45c403038a012881d02e408441c0003883c080f1050790000200c3c1900d000e0404d09a000d104180e80204189078100e05801e08510301903e40c03040030b03c00c4c000d10000023011420710140bc00c0954a25401d03000218000d036a594004101d5402503461450703194038844a08814151901380d10076a0130040c4140c6ca44e500d859440040d0780c1c06400081051000c1403140802001c010702c0f03001e004061000c5207982da03280c800e42e08040d040010064501c90751050040309550740b000101041d10200c0b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 481789676 1250 481788426 481788443
    0x204030f080f0721120524060409020d050a290f041d1c0f09060f1202120a0c05310e07030b03012003061009120305070b0112080304 58
    0x14071601002007440365030760150800269a04c00b804452018501c42c64501c1655998030852401582480c2030350400d403401d60b512000d80c41543d03091a211540340300d1046004083c40d2500b9074400804003643c10544c41622280d5854040044120180c05459485162416020004542c1e80c4510b00c6200100308070500618401000c400381d030f102c6030b1010380409100020300b50310380307034155a007070f6550039226400030414044003a101c01c1a001d810504803400071600d52901d0141069001c4a9002802d02001c041100429a0104d4224144005c220108070350170144501e1500800311400e640d0308001c103008014041110b003011440525061300203401d00e000c3c418075103070740006c40c1c403c1000c142c000c0b228003120700c0140450140c05502c000c0540708107400a2240c030f080812489580420a000c82c40d8416082001030801d00e00000c00c080c00b0710980c10140b20064460408022907031084c4000c17404601e000441c4000c2c045003408550050103032148605800070780355250720613408041d0004080c1e50 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 481790926 1250 481789676 481789687
    0x3060a0c0509060d0605100c0f1502090603012306190c0f020307080a03090b031603020a0c1704030302060f0709050d0f021009090b010804081b160f0303080a0204030f08 74
    0x24454021150314102c0140000d0701d400300144403030018100c82c45424030540c9000200c1d4600750280c000072441d20340045649604106a0701d40c5480b945800100030780c0c6680c00c100d03000c55995103070007842c00391907011901c1040c40a051320440d0003000740001d5130306c158010702c00a03480c070030044124410300c00702c1c1c94a04440c01c000d2030000704180304c0342d400a505001c0c8081c0800d13951130004905001e1070207941c44200d0569124103e0200c1d02c01507404081c03407a08921200c10943c00703a0010540a4280d11705403541420544407104080020070300d0b1002d000c00000d003082495030404c602c680080d40080140713601d041c400405005c00d0300d94807804e4007400d290400031050014202d0b2409410f600a01650802c44074110010300440e141e002e03008050b0f00d8521310441d44d51148000d139104507400304580f89400308004600c0031031008078003146014401d00b440900e9205400c0c004100400030116080f108504514002d040d401000b440c91050038810301c0300300041807220601c2600d050704003454a680c0c5 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 481792176 1250 481790926 481790951
    0x90e0c060d1e050702031c0b010203030f04080d06030803071107050915010504090f1b080601080415020d020f070c060810060f090e041109061507171b0105070906080603060a 76
    0x1202186210b0800c03510300310400441640100c01005900b54a0904405c030744582c8140c40101d8101c050a140164403e0002400740c0843c6820f498215010b000d804d400c06044440c03034400c0d90400e07001220900d01c0030003406007081d00140540361b410070400c0640000c500705004207003115001006446403501409034400c180c1d01590885016011489003813040e00740112030345010740160101c0c0c00c03454544074017000000d032081c07003001d025aa05940d900a0b43c0ca0719246d10714000d450407460781100745c4c00c2208482140d510720040c81c88610900780c80c2d880d0003203414004400c8032290b2000d014481e80f001000840b0039404621415075156050460340011204c404640c0b51115410072200d8658004c03e101c14030084140c0001800c600321211856641e80800f40050000340e410780041e90a03081c0310b000c000602c6a10110981005011400d091007401d803800c03c149803500f508041d5903503495060014555100098a010b4081c5090914071030604101080d42c2c2d03c002440f65041f035036110b0460039071 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 481793426 1250 481792176 481792211
    0x110a060f051537060e19081005060411071a1303050412150e030304022d0f0312030f010e09120a08040203010908041716080a0b070306050613090e0c060d 67
    0x4000300c0308081c3d03100c203840c0d0788050112000d02c080d4a01c183d0044a036032060303003541d0030383c00c00b56070a03000034104003107a138074030b150185c080580780c96402905c4500703401e40e02100070040d08a4a016100070b21000b240421280c004140142050104950040100c80802e40001c125000c440050b88084100034880c20914125a0521020100f1130b050007241c0107123036400005907014600171910006820304640700100d015841100303044074000e0324001f613a4580350140b050f151805003e0305403201039118010b10445540103c0d0701d0141c1c640c6030001405242c0c2072402d490780c41007550008004070b01c2c19402c4200c1c1401034111403810014a01e00003011500c0c20b4201035095944232840d16103660f1203840002a101001e40302403030310711403101078091100b5082c5000c01101e4590016101041080e180c40000000081100d001d26841c0c410025403600d41400500340b001c0403000c80d143e4035060480c510203440c1c1e0703044098000e0703100e400010003c1d6685400c0f1820702d607d50f5800142440442840c0340c4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 481794676 1250 481793426 481793509
    0xa0807030918050402040c03090302060c07150c0807090b0913050405030d110315031506061e0307020106050109090c0e040b01031d070302010e0306090304090c110a060f0515 76
    0x41070038009880e02c00c50015070801401144215414010206c00401c11030850340d010b000900164000d03004210400c442800419105002e040085004440103c4110a80384400c40c080000f1340381c601000300f4a40e01c80b82040140420b820b90302d02e040c0020700000c0181c10b000b0200d40c2e0803640c41c0c001c541008420001c907000d151010000f40a1001007050111302c0d0780080781e0043d103013030b54981601e40310300e004240c0d02100e1950b03052006c40c5441c4c1c0c0c0c041c07010f03903080761502d072030b0448201c102007010301401800355100b8102a40081105800c040004000c91019444a20321506000803034000c103070020415920f6240039180050702403c3c510048002c1c014502124500f02a00c1884513660a008038441003540c1c002c4e2038040310100414141651180202d82102680e001880180680c11054000f007201041915180c154204c1203581c080c20b04118060460f0402e5913405014101c034194043c02d0390158184130590f05801c581808104204071510160000c02100b000d6042041300303407002c190303 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 481795926 1250 481794676 481794689
    0x10804030822140a03030b0301020903060c0309030c0a08031014130f0605041e05011d15030a020604061106060f011d0324040b0a15091d011e05010b0405030a08070309 73
    0x1914141c400d443e0b0701c03a0b420390019400207007402400c060700e050500072034549810280042040c1d540e1003422f8036050f0006410045280010003a11480c036100308040e00d12103026002103592802d0607000300c140352619900024400d41c01d4001d2403ca03544d441c2ca24000780305001e40203e0814040c100200080c09540c2203a64028a40391003035001e00c08001c075240c0103e03101101003110303988a04840c403c2c0341e4280b80c2c8c451352070b5201d00029000815140110200f550181c1183c0c9041c066500003851500a90000c400003510030940401e0b807201008069009001a5400d20300d2040740300c00200043c1c1110681c1c3e01040c8201e880031a2502c04102c086580c984c2c3e04444510281902341c040700b030810980d400d6411504c17060210304501038a10440d0b003480104141c0c56041460100410081c0002c2a00c40c5042c281d800c180f903007101c8080c002e030f079403003e50031032200c0c185080340e882ca500304d9906800600d52000e080c00181b08685000a640c00704a80049006403200c0ca946000c0b01c01105540001 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 481797176 1250 481795926 481795943
    0x8190f080a18091d011406060d060f0e0a15032a170703021003060e0a090302030d15091a03070b0c0708030706020a030f23180f0a02030c010804030822 66
    0x29207056903803001510130f00345100800408441c0c12064281c2e400501103041174005c1c0030108880303140c0780d030003440f01201001c00415429030750f040761a950390159000c0292902c0260030400d150f030092244108844980f11000070441c21034413401e008130f40d0105540f00d02030084250300071020340840040c004107401c81c1c032600e0034181e8040c11307611041180310072405000ca58031280030a074000e00501c42551030402e0011180e07620070f8040806407a00c00390560540c082000342004000d03242c0503070f41900318904c42140c03c0c9840c2c0600c8000b11850b8005a001c2c00450080009442e60086611001c82e0a03104050b602d0f00d0440d0056030812030580d0100701d05200c001040e00401040360040c040580203038800301724520401903d2020750702101d40c41c900c08581400400114003400110941002d000c0300c0010303844000c0c00f1003070324140d1030200140d06944404241c0c0708500d0100825410a082864401c0c0070341096600a0066640541540c511034409a000307541002d0620030031b13103400d401c080071 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 481798426 1250 481797176 481797179
    0x7050904050c09030114071e030e0604230f2a0604030f0c0b0702030c040c120207061401080a02011e05070f0308060102070f0f03031404080d02030408190f080a18 71
    0x110030881d0f0120a42030302039420304190700107400c1d1a01215116a9860300c0f0205019105038004184c139040382105c2040c55520900780034080402c00146119503c91004080016541a456155a18410910095035000c406019110140401c2d402a0640c1c0c030000b2001a514100c2020b0304054181406500520045000001c0c005d0720502080074501030b20b403504016403240e00b0118144104a0080d405038840320400c1c2860816510623903807990549881e1a49440d6411040140d81c030411080c0d8070b80303403a030a01308880840c0c1110300e4014010300d00200844000caa00103030900750380510031a40100c4007165140103174094012691250740c410510100c030400740ca0080d0800406030780d01360041c81101c0700420300300032901d180e40960b00c0850103030b42c0302c0e8690b540c2103400980048400303d0a207010304c030001d0142010000d0030294074458014540b5242400100c2c2d14004151200c002072040c2c50410002180e02c81006001e810340042c0f0190307440080500940d03198820204942815005880 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 481799676 1250 481798426 481798441
    0x12150d03080f010806012114011b09080304031a1b0304140105130308190f1a011b020a05100309230706020303011409280c0305091b04050705090405 65
    0x1015445010340c0403250b81d0a980b80c03050070703545402c24040c00700034848810200c05a080c040b114952410f1040240011840c0070510103401d4558059640c1c1401ca01c241d03a807481c3c960080100e10160501000441c200380c91a20381d80904146a41c04002c07a00300100490301c501d10000400310210191400300e941d900385890281c448980310000c90f481546410041003950b0000c50f0074000c0c05406039510000f41e1510221040044a503041092200ba40c03200c00c050725400c0b034005c1b00c00302c0042010051544515000240c00c01c607a0800f00f541005116004800581e40c481c100010707140d040d10207035000444400c003a0000c1c1400e090140c400d02c3d10183c921810602a0349990700c9031402c0c070955800c16aa05010b1303940740021b002d00075084103491111102e07410106c2e505640210801c0c1c45038a80e03014512550185069103c0700b0072010744a0410151090b0540519070b04003400d0801800c05c0c0202d001039180c1da20910f601244115102c4011a15061254055503448103006104210900f003e41 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 481800926 1250 481799676 481799687
    0x10b131d0103060e0604030c06051f0f090b090403090909170313060c0c08191b061506090b0d09061d010519020301030302070e090a140c12010c020312150d03 69
    0xb00442c0e001e4241203846543d4940414014059645030320352071900b82c03884d41c0d0349014050061203065030082090080d52400c11840c4050b00405442c1d0458402c141010480e0b4161220300b000d65000344000c000303000000b60b10900c454116501d00500090980c00303442d0511340782d0100303100081c3d610b44c00700a01031003035040141c0252151003286e040024100c3d4000c196001c903105100503061400a026040ca00600c4064040d032544040c6081880c60a044104080c0340c548000160341c456941c0813030401c0d10b0f1200200d440640518100a070700940340022800d4070303210741c200e03a242450711040f09000304801500300710100c0c2004103208411324421005180200002c071180b4ae010b0323503a892031a05c085424800c482c162900340c1d0241507000e040402c0494800800b1b407400f100c1d841518800c0e4089030303140080e6401d555200000d021214045030800c00d29084549010565916209080310659000411108007200d605118407843d555050814854106a041c05030450030040e01e010401d80d02a = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 481802176 1250 481800926 481800929
    0x12020c0c13110409090c03050a1a0f0c0a11120a0c02041109030a0b22060912080c04170c0306010b030402011d0d02060904021b0f101103010b131d01 65
    0xa807000507195900d440e0010a598002501c41c801c048100800d1100e00300607080500308a015400707840c2c82e16940e50b6514a00300010a09a4542d070400148a00c0840c00c1e4613a0350304034440c030307500c0c2459040c00c010785000e6101e00000341c3c09000c2102c0b42603a8840c802d1040d9101c00c16414222904c034040031101030541c03180194124801d41c54060380d405501240420307a509410081c0081070829442c3c0e50300e2410410190810100e0420f00b12070701620b50341c108498440510508005c1049481c0d0324094540004801101041c006407104204540e10700c0f9068030219210300351011003156143c0001818105001c6040b5058040c6c0d6002188d801c40383c00c0154041c074400ea0300c003044180d0381a00040d05540203803042d41d00030403007400840940b422201400301c0c210028401450700b0031405905019a0012010002c00c1c1c204820b002e510400c2800060a481001309040c030240640084d00c0d5243d04c414042d210000b40d021036400c40c031204480c0144041c00b0016040ca000f2240301804e00c2c0200402d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 481803426 1250 481802176 481802179
    0x1101090b042910031410020c1b0d02010815120f06070f110c01031109091008010c0e03060c2d03010f0b0a1b05010b0a060507060b0d030c030f12020c0c 66
    0xb200055148900649034040c850115540c0d0084803d04581d2040b105203d1051159403e22884910491140d030718802031004002d03103001007490782003101c10f5500760034050f108544240d02d401c00c1400940d8101018643c800000754240302c0411200002843d1101c2410002001703109411224400210006580340100c20700c1c0c90702428851202402c44007510100c51001ca20740101141803590350090308001030501c070f00304825003000403020128204400440355a0160245080b00300002402845040020f20a501d400250940100c1c0803943d5a02e000e0a4020b00140006000044091440700c903030490003809151092038911031401c0034590070a009418002131012400940801104229002e4400d1521454450030000075124041c81205100341c0d800d540313503c3c030382400c1c1d40d41c1b40c86400540320944505480d0380c241c0c00e03d8170490304c0b1869030074041e104c00301020000c282c205808000540d8035140101c6400110301e0300310360403460ba46040e101c441c00410400d10444010419001c01e400 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 481804676 1250 481803426 481803473
    0x30b090603190303020322030206040b07050c0a020f0f0a03120e0a14010503090a080c03130f0501080105150c0109030e0909070f050607030219060b09100e071101090b04 74
    0x5506040648803202080b440c86038542c40858540080c0c0260091580720305209000ca5980e0040b482001c0e01d8200c542c0304400603041201040b0822100281302e58210716a4034090f41481326040c001c41c0d5a04480101911800068240d91001d80e03850004015680c0c01500081d06c05070740c1c0c034261901c018080340280220313404a100078128140048204111001126400c5d42500310380015036042c0e0019215074218001c040304000443c034444010141803025000840e641c0358a10075140c242c03400c07900209500d103880c0c1800c0003144c0c3d00511190540d00116180707104401034100881882c4070700c5a00310740c954200040383c0281034111060310300d45031003615075179040c1d92050011901c07147c0c10700480a65083d040d03400c3c040350420001034504a4031900490344c65007440c0b140d400e5601030760682112080d44400c81d409846c02d00c1149a900003217580c211280c0c103402c000341010640c0b40146031008100302c1480416521009401c50340300d0342c2e0048607400b080d04240c1006c030390750310114600014444 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 481805926 1250 481804676 481804681
    0x30d020c011d010e070e04290106140f090402030c04080d030902040f230601050f1201080d08041a0c040e18070611070527090106032d15020f0a030b09 66
    0xc1040c003c004450300410045d240850400c402c00c000c0c03440240c010f0b500d14220313600b482c417403942c200c100c00000c0c145d40301c48581c558589100186900f10540031201a240180080007540c00b02c1e809843c0348407400ca03009601c950f10442020311302d0080303038000c0240384140a800c070415500740c1e004080c038a00030b5030f0500164808141480c01e0ba00302042c426610764039406007503d5800c45140c019084a01458240e10b0300d444000c1d140c0c07080e0030019441c11260030304401044a282c0800c5032004445490800401a00e01a00d0721a40600e1a130191310002c003002000030565aa0101240c0243c048040c241d082410400b403e4400b90203501000c48181c49645008241140a1400c0392403009000c0e0040111a0070401842400000c4040038216000303000c0d150400c0700d14050311b0a1040b038659000003000c034039600300320341d0110307904107a408404404c5d10400e20090740848a60407141e000302c050180c2c6c1007030304050002071003541921034140e90081601c0121a606070801d800b1a40304440140254 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 481807176 1250 481805926 481805981
    0x230705010f0b0607020d05010e0106030c080709140f040204090f030305072304050f2103031b0a080a0e0c0406120c150509190302030709020307080a09080406050c030d020c01 76
    0xe65403900301d00d500900900c1040c4c014a8054120541e581c8110004642442900285400c6d070340141c104450707401c100d00701880a2031003080004002e000d0b500061106640603040308001401c00380c0300340590380c9641c00040c190745880c0c0140828a5005401d8101d000c49818014010502039070b901c0c000a40310305071141911380c503903c1e055600d540020140e00c0c00d4981010080c4030a1040324254016110901004105000000148091000c5001b0f0340c0e481c038150303c0d00380714809624444020704400707206c04400c03943d0010340141d110140313808c00220401d11003500e40c82e101ca01900b6690150400b5804078440c036000c403070045028442c0c0e14804003d41c23108901d850001c09000024002201845540514503242a0302614042c0000303040d002d8a48a03004079060060702e030080e0020f603030000248590143d214903140c0d8801d41480e420070041100360f86284c240e00c618800e50041250109240e520f5010920495030f4007d040076003199070714050417031107020317099000d500045441e40f2110920307003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 481808426 1250 481807176 481807181
    0xe0c0a02012306040911090103030c1a13080c1e0706030b0603040f0303111209030304020907020a2609041a010305010b070f0b0c0705390105071101230705010f 70
    0x8544030002c0d00d05941d4460510005108040e000d0722600541c0405101d00d444800765580a14040e5580c00c140031403509112101c3e07005025500007211904003004040c4031244000982d0982c400f882655030b840707168a45151201500014103c0c120401000c0040c0d40c00003402021103105072001d1008114001c00c00c0030302d01003160054081061602d110000074403a40c0314000b40c0901061450404048001100d00814100d6418815074800010700c402d61401804c86c6909c841d0610040c020320100c0e40d40d200900c07104100c1400a500500d481b04d00b0000e40380c00740c5410950141c01008030725501d1043c0070b0301c03c0e5600f00d00c5003ca4a4140041120442032044400c680d811107803d41072091240c1c0c65965000d0b0042c1a00300e00a02400700c83d000403418040c595a00c02c0b895844281e001083c0c0182c0c150003010007006055020070450741e142641c11030f00380e0b0035143e000401c00c4111031010005a40120401010209184280a6103a40c00c1c10500c007525060340608001c11a179a9400b244408 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 481809676 1250 481808426 481808471
    0x6142a101410061407031806020d140702030a030c0302071d0109060f050603150102010209220c020d0f080604060b2a0a1a060a09020315040b0f1f090e0c0a0201 70
    0x207401141303c0850826400003000c10601c24541003102aa4050714424950126000000103820204842d002558404802440c1042440005207802c00660020380ea507617944a00070107202d03056902c1c10605000340600b00007003590440311040301c0d032441508214a4024024007603180d1501601042d50b0301c0d42140001600c03809081d0510b151a00000c003040b43e1000f20719a41159020022011252210644031500c0900360920444080d2100320810070303201650900ca00b107600210000c42c105510542ea02d410124908114015464840203d4054060b6800242d0710140c0007a004600038205420b09032150401c400c0c029104604542c0d881c1c803840003502c0503015400700c9904000000014006c1034020300c00906c02c01e08660355404000503030f00100c0381070105089940074400d840c1024055080c408500306ca4403242c9a1a1f900000c5d040c4441d20600c880c001d83c1007442c41c8070700380030380c0c041d10140060040002c030903c5d240d42c00c070390251700900700c01e4019400c1100000030800c0322203001c80e = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 481810926 1250 481809676 481809689
    0x6010f0b0405331306120c090302010c06020415050301180b1c05100219021c052b06060e041104050901030f0201110105101a030f07080c2208010606142a101410 70
    0x40c04274910380046500e55042007041d200c10780e0800c8001903034024454075080076405522403070740b42d6242c498502c5c00e000c81c8004a1805c1804e04501050a03071328800301c00d000c1c4191031240c00c1c8451050800b5407500c1c6a000c10086102c0c4002044c0c6050041100c0340c0d1103840031642100d048240d05504c2c00d8005041d0101362020035800c2c00b030820110700803802818814801c650707004145032030500074019180a94400c40c0407c41809a0f0345850604c1d0062180c0c441154141600c0d05181c00e022600f5074105110107003035031404502c40c0045a1055030008994200301e00281f00c1820f2000001a0300702e1188a00301d10400c00c981c102043e41d8452041c0c0c0d1040c1d2140d0030031415551034a200b9195210001c081041103141004104002c080f1120b4413000b4082d01c40314004218104041c3c0c0342100c074203800c40381c180152100c1c030081204080781160245180f48204104c5860740301d21203085032243c110240704502038003030740a0440030b031a800545600d03495410490305858034144210070214a00941d0f = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 481812176 1250 481810926 481810937
    0x3030c0703030822110102120a020601031514010e09010b0405010b09040504240204260a06020903101a130e0712050a0f0506010f0b0405331306120c 65
    0x704040790007520700d20341c0450b20214008840007041e00c12649114690421501c0040d40c0500008650f070401032854080c0c03c0280311882c0584414020b0340e2541c05120081030f600b034407403006030388200076000b00300d02061036003c1050650319040c204550602c1106d5144440d8682418842c0c1840e2501900b030486968100c854030b030000d4901800080c100040081d103005005401c11000c0810f9005100da200303c00c1540182c1f03503802c1510004c1050444a81c00d601d035082d60300c0c1c891404101081500c040f0390320240c01a541d078028408207091098030211918024a0000c80c1d0380c00070404206d815005d0412941c8003640c0080d201c481088845c1040d2440196100b4401484080c461807419044140a0412078021140554406485403604201218587c201300010071030403500d12524409010303002c4201d070030075003003030082036000762220030404810402068032405003450620f284000b2000400107540c61088056682c25000d040c86800c0011320507041600200180e845020b101240540c4d90 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 481813426 1250 481812176 481812179
    0xd110712020402090406030503030903130801050609070c05160b070308060a062712140d0509060d24090e120903063601060f06170604150b1204020f03030c07 69
    0x1e1000075004104c250390410790303545001c4049203003040238605c10704103034000316a543c40d003c0d0000940710382c0b40d212500340d03070404080c40b03801d0f034580d814140e0011a902d4200008603041c20311a141c8a099500002c0021201d040415a5040703d030040018901a40300c1040c00c2d106c03501403110082d103600c41d50001401f131031a000c0f180e003200012403403040f01700c100078400306448007a4a0150a1101e000f1160b00c09280c1c0c8018a0704c2c014007400d50034180f64280315041c00d020303001140c00d5110380b10600c43c005030380d140341e642151842182150728507215040640482e440d07498010050140381c203241040c0c49484254800d207443c400c1242c03d00300e00a0043d0049444170100c541049401940c0340040300102c0444000107149101d075010281890000814414a8072003000e0281e440768005c1001c01c810308401101c0c80c1101400c040c0c22030005e0314001014106404240b0f80384905422020850f040020340700c04640d4805140c0b40200d00840740324020180b40340c1050340da48034510aa91003a002100f0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 481814676 1250 481813426 481813429
    0xf071a1b310305071e12050d0804030908060708041b050616060b06030c0a080c070b1512012a020309012c0603070f0e010908070e1806090d11071202 65
    0xc290051141d2448201c00d01d480c0d035a818248415074100260160700814039076540c0342240114801012110381550709185180c44480c0c0b1103092400d200180042200450100b43c4660181e00081030100c0648002d801c2820700208500d0054400395900004514032468030240c0e01d1041089400003442c8038a095941c020f224040381500b40c041c0d0700c881d42c502903101d8640b20304004500c43d0a09008159403044103100151041c000504000c0520030b0070301401e00050030007103210b0b821a0940c00c0c0c61110b0b4505c1d03030001c0d25180074203054850360b508100c0c1408400d548064426002041d003c548100c0045184040b6aa409040011030004044e4500b000344045040e80095a031078108a03102c140c0940c400104400f54001e480303842c005103880b211941c18540c408041c000f81202440c01c1c0d0640c621f0b1403801c555419440c081c40c254004010b0200c0e5841c041e001c54842019200c0d402d86a1030714002d00d000ba114203070304000502059030414400c14a4102081c0c885c1540d0602054010b569150b40 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 481815926 1250 481814676 481814737
    0x105061504030f140a1a07020106060903140c03030a0e0102060f10170102090616020112110f0a050c0712150903050a030218041e0f0b030d050f071a1b 66
    0x9415901d44d80060f4030080c07541820301a4020313450241c10610490744d030f0112142280c1000416900459152110921400c0e80c418442c0080702e030031800800c03482c07d03031214446c10149000f41c02c582c1840001000d0155503004502c00a03654000d8003a14150380d9080c0d0303c400151f80480701010501d01d0640240245223400000c80701c1c113900f00c00010b0403d0300c01c50120360380340e1003203643c41003400482995104640e0b1010300420180100310041c014007426801c2c2d00d00c207014400115180720703c04610000700ae403040060720120721085007200c0400f5916107002801615005055030000541596012083c2d00c50090081040c1d055403500d00d01410240110003e41100303d2050700c0c454050300054460343caa000314402d108240508105181109503418221114002c420b00348500b070050074081954046000d070381d0f1408500348590380d4441d11880200030305c100c0c1d01c002e02c0d0100008402260b4049189a43e1061758162100c01c02c1340d01000040c6498050103180e2020100407441070500506200b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 481817176 1250 481815926 481815953
    0x50d061e050a0b0d050d03091e0c1401020d1e020313090605090c07210e031006060e0a05010c11010903080c0a03081312140c0d05090f04020a05030f0919110102010506150403 76
    0x1501c04054203100c25050540003c040401652022b010300310a00504200314543d80c45403100740010400c2c1260104050308501d8040e03127940501140001500c00d0034004d0040b908410050741d18450019103484800f00200428054640640c8140c0e0000e43c0384141c51045500d55030f0407030a403544032111010070110000203804101d0402c8449124582c0c0e070b4030104800c04041100041c082071160600d00000c12a208101c43d051288000c001c080100c4d0b40c000468115a0380c0202000c1000c580c01d0f001600c540c2400e500c001c0c0900c500142d5424004400f04e01c00d0401440380c3c0c0c440c0515210044409000750302000c01030850b140038008003c410340507010103800b12f400600e2581c2001411504141008400e08540d40456400100c014003440c01d000c404c0c0320b00008903000c5041c050720003c010920b002c002c2400010608060119040010802c0b0806441d842044c00c204d0301540d92800c041644070200b00d09001d03600703180106000c2d2502c2840812168444a4194141071075512001c0d0b403111907 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 481818426 1250 481817176 481817183
    0x1819020d0f090b070f050403080c01150b0c07122d0204060807080709141306020f0a032406082d01030b06090a05060604050d061e050a0b0d050d0309 65
    0xc000091440080340144a032a5484400c00140342c0154280211404001003161007085400e102068503d50000150340c00c0c3c079000300e0016190300c030715400300780100454411a1046200100f000a105002800a242201d560000d445c0d849a40701603517600011504801000034a007000032040a815403407000c0e60320040e540c41100002015000300702181c02c142c000d82d429802c501001c2c400f06000300034040007408103020130030036112801c000f801800d1016028500ea0100a080360b81032021540599000f050f80842c2070340e0741d60380303190058001c001d541004e0030300202081130092000d4202c2106400c8483c82d442d0f189103581d95003526250780070a900062882901107010b284149002d0b9180c5000c0c502c1100b8050041c02c2c030004000e0380b030000500345410301d03003007208022541c0c503200241e6044403010b4550802a48044c0f42c140007902c103103200329440504507081c00040e401c1d039400a038029080d40404203c0030b00f50700180711040251905c05800c0d0390009a01c0c6e0003040c80303a8050140c1600 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 481819676 1250 481818426 481818431
    0x901050403060b010c0c03060e0f19020409020d1b0e180a032001092a06140d022101092435030c06010609120204050903040f0803070b061819 62
    0x2007907500d9001c0a1b045800a48401d507a403d4241c0f0040310410100c064030050000500110300c1010030085840c982c1c400080c0141d03168200030b011910360381c58210b507076540240003110940b4000d5817604c010b01a8895640b1601041d40481e41a04912154502543e80c20703024248d031003101e8071709a420804030034516400103100d420b00010b9403000c1c0b00b010001c1b8414000000f6401882c0703112241c44400072050b040703000201d0410001d40d6000f800001e00d00903641161502e51200d003c40c90001c0c014071b101c40c900906a90390b00b008480c4140320090588089840800c40f6042d2016089030703017103034454140e980e240c0d400e00a00c0700c2c1e0290484d414002140d1014a0284016a2643c015141d800113080747d11340c0c4003140001002c8400c0c441c09002d402c1ca490040300130b034641380d0888501ca11410020340115500c00101d0b41ca00c100341f04031005422000610b568840ea14182c85980f030b03001140580d8040c0751030780461403e14200303000d0400c00089002654198490310006018107400e040c48000321603 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 481820926 1250 481819676 481819697
    0x801030b1b040510050c012418020d0501080609120c0d050d02040902071a06060702010c0320011b12060605030612010605100c050c01110613170304080c0706050901050403060b01 78
    0x1900c0c583c804d141070300a50350310380c2c0b42d00340319925500b51407c5103400d40b12004066003400ca0308605010003030072505040409800c01b03803036076003820081c80b8600490070703420700300800802e440100003511800303800000100c825140411110300181c0c05005443c3c0500e410411407013142d03902c1000540b0800c00020001860326598950100c2240d0040d0b500f11003404074445040107a85040d02e030190f02c802c05a4001d0300c0c2507607c0c0d0000f4940c1d207140000a09000300800e0309020350000110030300000c40071030000c00803030340c001f00644071404a44000d040020301d21402d18440c1c07401400f400c821100c0680300c2c80d0454440b4402c1020040141041c0a0a90b686800004660780d0758603000b100025140c840000209807414a00c1c1801c5101081030b05000068544004400300019103035446014a04941e404015626100440c01200d035699014418040240002d001d40c08004080d4112100210b94641da52060240e682d80a10b816085c00301c1c00c14001000400c40c1e60f04417101240051403c01d04a0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 481822176 1250 481820926 481820929
    0xb0303040e0a05090609070303020c04050a14010303050c010e03130e07050705010f0504140604020114181512012702130803210106092105010b0d060c030c0801030b1b0405 75
    0x40c0080b51007107412602d03034050210104d810f00c030b00707504003040901808403142561800780d941e0310780d01d151a00075503540c070001e5a40f884039401100c46543c0b00942100d59692410000c4c01c903005021966060b510b42811303001c0e240300c000203c0e44c180b51204080d101040c500610024840c00040a4200b804403c0010b400051028031913020f0080841e840029a4101810030084081500d000c2032065800344080c800980c3c1c1040200080c2d640c2d02810541d500220000c424a001084c2e05490300b00d84010201121204400094501400c0d00c0041c04001e03aa26038800c14140c040075180c0400e4150003c0c45d0140c01c1598008006028443d2a54190159030307000302032540d4000b0100c03040f080284400d00680001e5034000ba401403100d442d0002c086800d22100444400b40b140c041d00d00242c40c0c0344a1803c105013908142d008034801400754010071030509005000d402554102e800191500100c0b51001d8041c42d6024140e903000215001e03a80c1c3c403500400c4041b21440020100381c1030601001549 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 481823426 1250 481822176 481822199
    0x90f0b0a2105160303090e010608150a05190e09060601050712090f03030c03080705031902071b0303051209060f0402010804030309020307081b06070206160c1212110d0f030b030304 79
    0x184981c0c0b03c480881c092031400c000700712039155003180302e0600030341c4010041d4aa201c66442c2e0040030340c0c8041c01280c0c01c0340c00003600e00b0009510a54000b040b003e1100c0703035440c000705514112200c01c440d4001a6417000d2105850310800c40e44203000c100c0501040022904512965912000c5402e12100164495030340b2021072105030b00490003e0261362840040603440f000064000c0e00a0805508504050303d0180900d0a00d0803180340b001e9002c80c01034280f051515244418800302c0102030b01c00f60304c81c00c0041c51a0300009031000500d407260042070300000e00041c003078841d200091804c612500c556004481400c03015105404040d15440e031400035030b605002e034500400e00c04004020141c02240c134820003500645583c0d11800050180b280075855200c108d420b803a80c4501c0c0d580c01c005e028030300103070414000c0c3c00c2041c007001c540300303410700704100600110055101d544840c1040c4a4000c50540d4a005821400300000c07102d10110345410300076080220040c0c002010b49040c103440b014070400 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 481824676 1250 481823426 481823443
    0x30b0405130212010c090b0702040204090509060919030905060c0a0506090c0a0503060f06060307171518071d01050d05100303030605030d0c1e02060d06090f0b0a2105 73
    0x1000c50710300101c90214602080038048201c1c0d210000c0c0a0743d40590009050913500d441407002c80c06c0c000400c402196116070441d009031402b40c1c0100128101543c0280d0350700300841d40c0284503c02c084841d1fa8010746164024452941031b560384140906241c03d100d115004150f643c0f040b4420303c001e2400040060180e1489003079254004c21322550f0031020821811125803000c0c0c02a0090010700024121904000b80e0080e42541c13129a01e407501501103801121601140c1d21404441d0f0500017420555418045410011200c0780304000601c0c0195242075019150303000032030140742c50350120490031100d4240010050406900700004000c030082a90011510041181c80e40780c07061080603010b203e008060001600185030b1f4514003580a84482c0b07402002170b007403070000c90030300ba1001104e00300c20501560240541303454910341c16080700640000d0040725036040c1000e1111503401d0031445410744070100184642c01031450003c0580b21070b0f0803054076a041d500700600c8171002c06c004006045 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 481825926 1250 481824676 481824691
    0xa1419030b130e0604120e09010807050118060c030c0618060516110a0605060a0f0b07050c0306090c04051009060b030a060e240d060e070f080703030c080307030b0405 73
    0x501001d8200c20024441c88812491542c10300d0500c1e030a2103644000788082e88603a111104036403460600000780d422108a030f4820b0703445036000d000419400808584030342111000c0c0c0b20100341001c4600c0c1024440558028000021170080710000441d1060489108041c0030702400500c002d85841501144030041901340c40d80c030b468800780000041a004035241d007007003a1820240c2245000c10740c030345541041c500902007940707540114189964400d5824014140c01d071f03d91406a540785070060054000e080150f075140580c0045020500f0041040c80c03040d100400a00306802e00314007003200a0102400c00d514612400c003012480805a00c210300103000b0451800361245041d8080c901610100d030000c0d00401c140e0740511840e090341c04060728030320007010148103221a14402041003a01c0d4441e000d40524105a80703280000c3d408107110040c0c403ca03004200d405a110024266541c41c28403000300084c030324129100c003280c05000030b950005103518000c602903e181001505a540c2991103c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 481827176 1250 481825926 481825931
    0x1205092b0b09070609050a08030307050d0204050913050c03011b0c030509060c01060e220b040f0f08091005040305030f0a0504090903030c08151503090102070818090c030c0a141903 79
    0x103101381a00080300341e00034401100c51000c0b41307080038040c5889000140000d0180240072542d00810140364065901404002e054503046140552480e030492141030002d651501070b00340d0212144c01d06000b00b05071022030141c0c0c01d4540311742110455202c40800d0068040200c00c1c03020030136a0b40c402d402000360040703210011980c40e0400110009980300a440c1d0030715144050300c5042642420042507003000e410580700d85c3d043c0e940382800300442800704001858621803101001c03c001806000e0147c042090b6084e0b400c0c14510f2a060f2001c1c0300303500001d4980d03403007407083e80700b9a0326000081001480c1d070701d0b0950919035a01d540b203041c0c3d4843c4008401181d21107905441495101c240c0507480500744140d940041c001c5000701d41240b0820320b900f00c01030380010004064103400d404030749001c3d50000c10a695456040100109231840d1801c80d03120b40c605502098a088004042c0c0703000740c0c00314004038540708100505556540240e4010400c41c1010700c4448000701c85521060702c40304054801 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 481828426 1250 481827176 481827179
    0xc0305070e101208090111251a0f070f120207090f27061104030b0402040b0603091903020c04091101120614010c1407060c1205092b0b0907 61
    0x14011901008092140880707407103504101030446072089643c0c4a0700105001d035641c0140004841c0c9940104140520f842101400a52610750b440e48030040c00c242c10350403403183d4071668684881c18181400e100181010310030720810090240c020003805204072500820b41b09942e84182c0725854280e44a0096000f03040104484041405803a03801401e00008003d070b4501c1c61425410340001d6844036803c0301c46191404108051076000d0100d4440f034001c1140c03615a49e03d092148844100c070304034021420031b008400b141c00c100382942c0c002e4030010090019041c13001a80031101e02d8484082d4118403440c07510350000c2e1151702c50f501c88540034140300f403000703401140058501300014084a001a181030020031460705900d41414158209103010307560303149103091090300c0d000d14500302d82c603e000d40380000415980202e00da04201c1c1c820004410b1028001c4010744850140e240b050b9040390b401ca445051041103840f58500030f041c4458145003400203a11070030041c400031a0000141ea004050 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 481829676 1250 481828426 481828439
    0x2070609121106100308070501060b181203130e0907051e031e0d0e0a09020c0102040e0109020403050c01120212150a12210c05030711091608010e06030a0c030507 71
    0x50100e00014648000c3c4a07a0400e1401880350188070703c0080c01c1000c0206141c010043c0070742000c4010800e156a1645540c40c4140281007507070f0b03440d0814070440d04581c2e9a0f641e00380c0801a90003950f04180c011102c0d900c2c10031030510100c0010003e0b0790302d015041000c100d0b60b6813203142603404030005850503030050421023418030f04800d41054180c42494041c032012030444c00074419509045501e45144110005400310b03180002c2c540003520020300220f40c43c0710008056000d802103482210303402c01c40e0b0340d035a180e030f40c100c0c802e601004c3e0494015001040140d40607202c81c509444200c1030052400c188154000000e480c15a402d02c050910440398882c2813415003400d2000d82000c0f801c080c44c12100f9901c40307102c241c441c240d185140c81d100f84110300c2c07907000d00c5600e503042c2c0c1c11030300381d940d01c428610b072040204001401c1103116060300804038075406040d201c05d4130060f05c641c48813862070342040350b000c844250040040b5410702c2288042800900c85070b4104000303510941c01070024506150307 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 481830926 1250 481829676 481829687
    0xc080a060e0f04020f01260a050f130f020109031e021003110301140117010602010e01050a0c0f12020c191203020a09141311131e090509010207060912 66
    0x5014120030200311042c070814061460440d90041d40c11a08298880c0c051001079843c07001400a10703002210801034503100740c1042d036100b48290300c610170030489036540d040a0325260000b0340b011418190054842070004c2c182c100354800282c01410103e03041d42d5650780700c1000f5440e5000c2d551907545203ca4123011414001c052040100207818184405000c10408000c41d010501c2a65010101c0c00d10902c0103900440010042d00405150f0700002d41c0c444101038041e08450340405901e6182800298444201c1d00c00e07282144034980d83d41132010240c88084440d02a0314285417202075080016000288042010b000748599140e071281c1c07401c52a052400c03000300170304400d4061500420000d02c5903907000042d82c1c1510b44604c0300309035260484021826070b20b8960039518600d0700d04840301905261084c00352420451003010f5194068507000302c0c0d4440c040c54400346c480d040c0c40302030900c080303d80c1da0095a44414084001402c0035221380718902620001102540c6400d4003500403910700c1da104 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 481832176 1250 481830926 481830929
    0x519020c1f060501050d270b07091208040e1906060f02070504061202150f0d050105194703041502072001020a05070311042004090903120c080a06 64
    0x510104280343c0b404001078400e108144462040325170b10250b44083c82e45a6007112803000c000030312011ba100b924a41504101010b079440c82c003080540e000000c02c1c0d40f40340170700c05c01a0f50290529081c00d1821814450440024092b41b2484441c50105080040c103881803400030b140e103560700b04800700d0140f006410004103801c080d01650801d5000e020107042841200802d950544180d080d420301500e00f03a0103070140901528420310300107038903081380c0e00d07942190b8180d80b000c45041c88038007040d800603440c00115128031060900340d0065501070100d48881021480ca0411540f0070a108001400d800c5008400082e421888081b040c4011301c0070310182800e0b580c0c1060070462401d42c00e0b4403002408030720b000200501500000c0c07507184a0344240300a0f14140d0307002c01264080c9450780b900c01c4004a5040009000fa882c000c15540000c1d9502c034490074581c4c10380c403564645401c0c00d480f0800f5241040003502402040a03e0400395a500c1c4200c034004c04956441c0407990802003c0f1a0994106 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 481833426 1250 481832176 481832233
    0x3050d0b061905090d14010f0e010c081b0f0417070803120621010e100b010306120b0603030f0301060908010b040c0203030f09070f060c1a04030c060519020c 69
    0x10b10202c41031504405112480c60414200b4070784809242e000140340c40c1d11081c0041c03c840c00e02c0d4020000c1d0005410403103510b100c10307d0901041402c0003800d0300700c03210002010300281000001c0384000c1072059913165041e502040741c5261000680200f5001d500a03808030b008601c01e80c0454200f01070910856010300388000c00b071460218180c0e0b00f640743c030502600d06071294817031440382105050548103501d4841608070081c000c0220302040a9102c02040ba091541182004031405666109100f9103050f110344101070054030400e03890321a91010001c1005400d8441040f40d80c00809074003001d50300800e03c81d580d000c845404c218026081d112141c40c80d50096040c01d800c0300d030072600842503a0380004014402100f60752424021894440954403050703d004044d000800d481d41d0046030f40351070300d015030150080783d40710420700320007000b003200d0180000340007202c18000900160040350304a0a0300300724440383d0040e900a40f0407070307120a0000e04194000100a24807491035500c88114854 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 481834532 1106 481833426 481833439
    0x9020c011d0109060f06230f042f03010e010b1c0609141501020304031e021c03021c0f0f21021209010c0c03030c170403050d0b 56
    0x19080d03c01c1d1121410078840c00d8040b441400b0b418200d551550304200f080301c80060280683c0c0c0882c005540c000545060f00c003c641d21030098614580c0054505200b001c5ea240c0d070104501c4114500e0540d110707080c80100000c11034030b00158111180705110a940f0300c030107480402c5444505080c0180d851078800d000c074044009903c807400b40c0d15120303000c1c4603a845506401d9441102c08142a005a02c00c110620015007580e2800241c0c0d29600c64440104195500241004840d2201210700c039104100300e100b456810011251000c0441e013003050b42c403121082c01026507070083c0d422030600121141c0d40b034545104601c440310803001c3c040062044003c03c1500c5000c1d5121113134038620801c1880c00701e00c071300c541886000350300c00450b1220702004605a078150060700202c00312005002500d04034059202e544900d41d03102c1c601ca61f030744030f0751124013102c0142110284c2010314010030 = true := by decide +kernel

theorem cover : BRFrame.Cov 481654676 481834532 := by
  have h0 := BRFrame.cov_init 481654676
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481654676 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 481654676 ≤ n) (h2 : n < 481834532) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
