-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2301
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:17:47.115718+00:00
-- url     : https://prove2.me/submissions/2f66e593-b732-4ac2-b93f-30692aebae8d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 413669064 ≤ n < 413848920 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 413670314 1250 413669064 413669077
    0x7021c0e010315030209040c05100c0506041118090d03110309060106180e01030501050601030b041a040203190213090e1b09040309030828230f091c021005070206 71
    0x4141d150224001e00b00000d80c0c3c10300003542d02402d1240e4506052801c0004540d41c0c3c01b030240100f000303803989280a4411080d003c4920340220141266489070f84520407000880960341c1d400c05c92201e80914241000144148501a1340b4044e001e800c00500c0c0080a9555400244c1c1e2141d80c14020720131b52490105005044a100d820000c1c49800c0440c40c0900940f101e41c8207014042150f00004140305040d0040c41c0b040c0c500341c1e0200207081142e8104401c42e1020341006c1130340d400d10600003016080030788c011a004441c181a1138070326410640c8070810303644081040000d881411008104001c0c0d40e0040204203528140075040201d04403040c5a02100d80300d2210f8843d0b040e160100cad00707160007405000080c507009400d0710340d40c803d4840800c10b50040702c403240b045886c1c2c0103000642c3c10701ca40005a40c240c2c034640500b03440e0f0940380403c2c0203a0401501e02084c1c1008100c3d18910780c3d650502c03580d19000003010800c0c0d00715640100100c0e5078038200c0207c1032100801c24030006955803021145c5 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 413671564 1250 413670314 413670317
    0x17071e060608190c050f04060e09150f1e06040e07060917190f0807060c0c0c09050c0a030b18040c06020c0409120c061d070e01080109020a170a080a0807021c0e01 71
    0x180d000c0d4140068088d088075880700881c0d05840050140b55000032075582010351411a014869132a0740c90400c0010408a800002c1060b511002002044104803040c1c1c0044d4010004103900c000400c155060103503592241002c00d0500e14200440401000c80200109078000170308a01c101c0007800503180340414000410f04192244500208104042075951040d0000810884001d10070b1b070140c032203d400002a41d804480d804001a0a041806101d2003044501e1074541007a00c1c6034003e40c0034102e070101c0941e00407a403035440e003540800d044000e4460f5000306086941c151a0400c041c1c00c06034a0600b6600447c10b201141e8007181c4400070303034841c5403542d10f051a21181d0b00e09148009022400501740700f192841c89095000e20300260a000b6503004401c014501d076070b10701829088a171003c20080d04511402410040110360006007003006002c00309507009408582d441c0071455101d500d030940031030300c414240b11103140e0420601401500c0d58030030a00c44400e5880c0503051011002e5000d0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 413672814 1250 413671564 413671579
    0x6060f0513030b0a06051206040c090f09020301381c0302031b030a090806040f0803070504090f0c0e031f0f06051201060302180417071e060608190c05 66
    0x60780034100034018001036410100041c864204046a0740c0545601d204040c4940b0304880c1c2990440404222980500d500005243d20185401c40f40c02c050030a80c0b414411041d6506043c0016840038060400400d900b0b41d08100815512501c59112a61038034449020050201c2881c000e500d42100a10070b8006011580b0844401d52604074610300c83d4100c440300620490103800400c04000001d010043c0c2c998940c83c2041c0d4448103038580c1e6040c11100501074a0750704c40031001003102c040085412851701d14009140540b52024527003034440c0080c0c489905950b03000c4c0c0181c1503900030300e81fa0b51008114003603c11886008403800030340d030398080250980e954440e4000d200d1540c56009000a1401512421542c02c190410340e001b05004d1000b079020342d06054100d81172070401180148100c5d48000b0050b009182410340c061250092101201c0302c2c0c000c80740d00207000c4903942101d400c00d88100c90104005041003080d6081a0019448880d1640620300140c0060f00f01e101c42426143c00341c4004 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 413674064 1250 413672814 413672827
    0x20a03081b0d05030121060c020703021e0102060114060c0304060c0b01150c1b080706080a0e01050601020a080c0a0f0b04201c1a04030f02070b0a0e010f1202030c0403110406060f05 79
    0x1951b1010040010202450542d00145d02d80d004210301d42102c0c003c40d013003403014450680008210210110071030060f044000140510700141d00300b0913500c540940120304002501c160340346954825084030001c0b540e030090030b6041024024100e40500030040b00200d100d07050400260110180c0c00e0010007002040d000481d20b20401c2c0c580100420f1400200ca404a5a8004c0030b0222901981c40451542c100050b800a803181401110302407801a401440f188185071210b1215400c03040c03200750640200e1000701c0110782485494507026000b012548420308003480c00c80c0c05101100e001c4800c202c80c4c094070700f0b0f45580e0652012200500c2ea60f080c2e050048625003014aa810400303048401200c0b9418403042c154450102071003622503408480b080380d11000d206001d40144071070346d00054003c0d8610710780c65100380c0700300400c4030003405c01c5000207800707201880590304110340b450042030000c24101305106129a600c4861401179808014403420940000e01d10000840c0d41000d010001400 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 413675314 1250 413674064 413674109
    0x40b010801060c06090204020d020705011b2f0307140d091a210901051e010e0c0a031b0503070e060301030f170c0106060306050f03011e0b040207020a03081b0d050301 73
    0x45c0303010a5004008645c1d48410f40c54890080d004580c040d50345610b4400d1001c006104c1d51125070840c4079949500c1100d183c090716140201c0060700610b94a03001003071903041120b2041000c2c6c08c20303620a1001c8904c0760100d40341c092400741780c04940c83c10000101c3c0c0400002d06800289880c1d174142030100383e41e82c0300040c0800380c01c0c1083c0f08400e03501916030f42001034080b41076100900032212801940f5203a02c0049031021035a60a0040c0c2203001e2485012034408000c1e40d00400d500703011810301184e00d6810303224610200d56900d045802064000003007100b039950100c09915200411503509007076506580310700220841401c0000c0c0104000e004400b1030b40211415a55008810340080c03082c140c0346d1070001d020300784500c20640181800c111096440c50103003e0354404921503070145001038503e81885000e0502d220903075170450f60800860f400b42e218000710f48065802800001c0d641c00e988400342450110241d250f660a400500c0d1040b40c170781d40501200d04403a1849032444440007910038 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 413676564 1250 413675314 413675321
    0x190e01020f0f0909090303091c09050d050a0309081204030f0c031e110405161805060f03010509130c031b05120a0209061c030503130c0e04050c040b010801060c06 71
    0x100907414030001c2007400c1100380e440700070840b400c01662807a0704e0b500c070044040d42c0c900060305d43c85000e420404c0a200c10040418408800c20340d1450705480e15503440e404500c001d284000281d1b45500002e046006040d0040d84040052004000a107000d1240e240c81c00024060f6000041984104551070b0b0706010702c0c10701e41070203182c02a62b40284001203103e0b9035180c17104540111002c5401640c1c2100c3d40c6494801c0c240305504081e201952a14503410803034080c40c80b210030b544510401d550100345511007602a00740c0300d855103c91640c1e541800c04016403410700a00422841c16080d040c00d002a040c01003103011aa03011007280c2c010b1000e10145031761502d03590422070700111100c1c6101040c1400040000100c1d000362003c40d61612444113010300d00c040c4e00008107c160b609050000024402ca00566000501c14800c20f0401c101d5582c1d640c801510750312210f105607562051005005080c0040002c0c10001c940c01c100c01d901c0000003030310348001481181c050149000041050003460380 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 413677814 1250 413676564 413676577
    0x11010b0603010f0614120c09180a02040f0f0b04030b0a090215030402100903081e09040e0f06010f14010c060b0409060507120504020d2a08100e06190e0102 68
    0x4164540320343e140c203a4412149003611400f070000c3c03841005c0c1010311410700c040b254028205205140a80e80d070020200242d40841d07034440d0000c10f180c10800545c099035200da030090f80c0b55500903035240e00d840000c41000d9419040403504131038240c01000082c5034030007102c040317990101111003107130394603440b4400138504c0d008080d4000140071400e034403031079005009500c51032007250b0305a012205205c04481c0310100c0d00009001620400c400500c0402011f85440000ca1203c6851301e0100c003d00030400f0f6590001d800022035116402d10040710800703205650140051481140105d460b015103819100000300c240c9051080300d28090041c01101e42020714250341c045d00038051030266141c400010071040301c1c000e0018032400b181c812540024011036000e0b54004007688544142e0f40c88400c1008140b0020a0780b9440310360804440000c000c009000400440c0040c02c0102988140d244c01c1c2c90000794101c46030742061301000b040c1000c03441e500303a10552020002036080c0d10400f0356030082c0b0852 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 413679064 1250 413677814 413677819
    0x30a08040906030309140d0809030c0402070b04062009010825020d0807170406111c0e0111030f1f0b1204120f02060a020708090a0303020d081503030a11010b 69
    0x540425290495048102103901c85c0e9142c0c0d01d801d549031034668000e0002c52015910610000e011030200380744102034080d00d20010700341d804110554001800320307404840704580031450b03c2d0410042c001030b0310441810031051001002c0400003a00000381511440400c90f0511221b4008502051405000009070060414151042c003014080295981184964000019108500003003010744200d048200c0c9441032088004544c03910340e0b03990086d0003103141d01d14001c0e006200300c3c92030200c00c1104c0d4000c0341011800003000400089403900f0342d000e1101103402080f042081c82808003031500060303480050095003d5001c0c1009441001841c140d0380991700e140b03004180c40181266070004103005510600c035112841021010598400910382d0050000d40c00090001c1ca914120390002c10b54a4414030b00c1c1c030320703195503840000d0700c1c070f00315400c107a006a00040d0905106600406a940c1180007095540911010080040c1e520712071040700c1030403c1194803c2d4074501400b500f0001018500 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 413680314 1250 413679064 413679067
    0x180106091a120a051503160911070204020406050c070906031e0213050a150e0411060f070501020310030b060906130c02190f1505010e0105011b0c091a010e030d0e030a08 74
    0x80c01c002c0c400f44c0019681c210400c441905090344510340000c540600c001040680c2e041c840c90075424030001c00d0b580d0390701d1441c1c1c1020003c1d9030045e6202d01c014000780c203082d1a101d1f252840641010300d001c1c482c0d0090f008051500c7d10620214010380224512805070000d0040181e00d9480804e890040500c0319919140c1441c052041030009900003040b40c80140300c000031920399455080e900c454056030050b01000618004461070f041c030b4801490744402e00814a0724140e520b980301822030344200d0344c66084103920b4809100704203070000b1031038004004484455075801d000b0005041c00c0308411100c0012740c0e4560801914500034005280c00d0082507040c0c070310403002d41c01c214a46500b041e01c01c4908025000010464000301c0c8200341c1030b10519010308045030309007001507030407010000f0b90341180130810350010f00080700300e1480c8003c1c00080b480800c5240064240d0003000881c41c0c2c030141400301c00354080c40d440e140011040108802480e01c1295000b0300008039040c0741441c04040c00d202b10 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 413681564 1250 413680314 413680321
    0xb030c07020d1211120301060e03031b0d0927050709030501060b03060f01080114060a051b1609060515180303040305010c0f0f171b0a0e180106091a12 66
    0x2000d0024183c1412500c0f04403a103601030070f6140c2c4580c0b60302140d822801060005205541c42040c10031760210010701164640f05403040100480076030f900c80010150b0086ca605c4035400d5100e07032850020180030040b01000455a900000358418080011280581c0c0d200003880c41880380c1760b10382c025900034000304201d9403102a404069841110454010503034181c0407041540b042c0d12260490303030004455103500c860b1404102c8240d100d20080d008210041c0645010f01c0700d003560000c816034030200140f501c80c00e6011104030b90310386540401c50b07007032074071030704229a40b504521a007481c4088002c95076546a41c1d54143e100c041202c10158040c840802e01208001055020032400c03c2140c48090209404000440d1010007414110000810300c0340003010001c0c01908003508100844a05101d5159414485206421500c510310001d400c3c00104185414038561000702409441c0c540e144941c10f2050250817a52140704842c00011071007108040c0c81821001d880194080800c5000c1504 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 413682814 1250 413681564 413681573
    0x5100e04061e030605070302071a090f0d0203040e0a0603051f0b030c0d0206070c09051314030c1c050f030c0306030c0a03020f06070302070f0308030f1f0b030c07020d 73
    0x14081004540114606400400d240d0700890b0700140c0c4842c8180c00c0b603191030442d0785400281802816200502d9024003007140092081e0211809514200d40c0321a101e18200012510740b034000c00d0440040c0d00400c0c006509294044110790030350b9180100e00113103889040c0003000511913940050058020410030344004c02c030703012150524540520081c403006030018100b40c0c407070348525441d0741d10031251030b0380d14014105440646500c50141c04026009565088090241c9000300e460b00300341c0d82101c0003141000711842c801c0c8030441c0c203000110b00b80103101400369551000708540480012007040d10240451192088440070035246507140c1d01e90804030380740455030300103850546c4a80190003102c08582001681c100440c2c2e002042c1d00c40d104a101c1c2403010540c000041a8110b004242c0b005c59400700c0c2600c0c13a001180710300d006650740c0c40d14140c80248500050000d042c606183c100c00351100d40d40c600e030481501c154401c56a41c940b11180104043e01c24250000d400c000030605203801e01 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 413684064 1250 413682814 413682827
    0x10507110c1909020409021c0c02100f09020a08030405040c0c050601050d1b0b0310050409050a0303231302091303021c030212270a0c0e040201051b03030a0b1c12090510 74
    0x100400b2003001d0b07508c1c501c014550140d8070801841030040c0c3c4910700f0720144140c50341004001c105d0825000501580c02e40109120540a030410115540b0020701048241424441d05614083c81d1816504601c5160b44007526000c061103480d200d0541107480d4000e22103034a50400b48000d01010403090a0ba44045d0140160400c59005000382c0c0f0040740000c4038141805013039005980803001c2c0001d4032007030b901900140030894038050341146519031880840764802209000310359000b0324130400440b86c41004080c035801000840e203800301d800c8850000750005119443c1911040d903100b01c04120040450017030141544854142d00200c007448004d040c1031a008021103110034060300c00703005000e07aa0345d980004481c010b01c9091000400c020218034a004580c101c0c0c4145442445d0003641000031401501a0f1148610f5800000c05e0100072030140c81000c0c0c000f0070685800181030215a0700b400401c80d044c0001d031403155950702c8001c07460310444061000d0100102028400c0c400c074040204003 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 413685314 1250 413684064 413684077
    0x180605040b07050a050904150f06030207110409172212020307140f0f06040f030318060201050f0a05060d0c0f0924030212120d020a02010507110c190902040902 70
    0x206461000801c01840c483e1080341c100c0c0c82c00d605e44500d041030300b00900005100e010391070700b09183c0503030f03001c01e00c0354015a07107600620f060340d005030301c802460400014120000209500c00c51402040c000041c08000d40791400a0b030000c486c2e5140e00c0540c0d18541c048200184501080382981004541541e011f1140c00e40c047c02a4107c8030100d40720120b69000c22810f0074410350080b014a1a03400a00d8030100a200800000e445c560178a5611400080c0075040e40e0005c0700442e00c440c02c40704180910340724460041249100071310081c01c008103d40c07048040a04043c080c0c035101c000080301a160034240c3d0340d00aa02101078920a1340d60394481c504415940103054549041080e004ac3d40c003480740c01c01500320522504a0302c0c0b40d140d80d082140d11581c0341140e040c54055020f02d039810304541d00c042c1c0008040c01c180560340d07641d000802800c490f40200309805020110748281c000d00303400900240c900c000ad0b1514800b0040f8401100140721065201c0141d503800020042100f14858019281 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 413686564 1250 413685314 413685323
    0x40f05160e060d0203120a031508010209011706130f0209130507090501020c060d0e0708060109090b06040915150b03040609050c09070206040b18010c0801030c090204030b041518060504 81
    0x4079500c40004009020302542e40c069410b502c041c0d658440004c104000b050398840b64280020031201c0071a40ca005a030640e48a03c400b45d40c086001c41a650700711000b20a603a80c40301e40d40300107140c104005100d10321a0651807440d1561051420658010380e03044881d00302008210101034501c55540402400c0d00311280c0300000c05c42c410004d1036500002e890f14141100030314950500301412280401801c8510210080d071007403040020318503e0601c0302c1800307010703007035004a000d0361242051641c222000d0005c1d03014514241c4801c2c0407512401411000c0c0da8000c8c0041180c1c401054012044061500705108202c80001804104407a941c04460040e1144054500b0303042c03c2c908019685904072207200161700b0440000700011030a802481e480701c2c4850702d488040d440074503400c1c03c440c688914800404c07000001030061100d61411030008081c81c0340198581400e540d182c08220b18040d0000b045a90704166a00b40c40d0003603004652201c80320341c0c0401c285542c40c201180a4401581c2c00c1d034 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 413687814 1250 413686564 413686589
    0xa03020304080f1201180204030b2d0106050702100f270504060609210510090524150604060c060f060317070c0b030609011707050402341a040f0516 65
    0xe0b00901a80261030849e038100d00304c1541030760760b0007640401558040e41c07071600c000c014065010024004036101d011b400c03244d0314103444026510500032400700c00344000341800b000b4030b40a0310a950121001d8900b0494038115140034503420328086415440b504995031040c10031001084450307208511030102c40e41440201c1c0707005800e0801d0340e1210140500a0507640048101c0d000c0982540c00c0300080d6807248044900401c0c9030510b0819019640c50080071446100c000c4c0161031400b00210324010000b00c1c0e090345070505d0140090002644040005c20082c4c135101c4c00c42460715142d00003001150080c1940034a103030141c424038042d40c80000100c51503902031001041018400b0f007624032503a000f51600b0340590805009400d01030703012403064a944070340030f07011500e501c460000d0904854138284412001d5201c4442c0c0c60860030900daa0080c0030f0800a4060100d880d46400c481c4d070b0500310301140880d4455041802c800c50400340d015006110b007135501c0c4000c121006407241190140d44510 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 413689064 1250 413687814 413687849
    0x100c02101a060f131505030f0a0c231201090b1f09090e0307150f0605180406050702121612030e0c0f01170a0608210a03020304080f1201 60
    0x4004426079207000d903001081070203404000351005008240707140b00081c01e10301817559510301108a02d03030a40340c600003540100a11622801c281004c0d03030850039045080c00f080106101c000e0102075040901d8522035906491000c55000060480d80c1a580030805d0104035a101c14414002c0c0c860940c840303000f4143c41801c18101440780d03130011440440742d0f541094092034401500c02030b02d10001100c14070b020801000c0300040030808001c6400c00b40d5000450000a403501400071207916a101901031402110b140c0011905403017140d43c4158060b10008260721420002c0b45440042d45041404540c0000c61900b5040003100395100c0620070460007d8807050f900382202034a0703480d0020300342940512a0341005141c1540c08406001040c074000d8022420341e50003041500041e540c0302180c66540d5000d001c580000e00903e030f403d444038040b044002c0d00c1d0502415080c403950010b00d040640c048040380400100070704032009010721000441d250021014485c80c1c2d580c082c404c96281c0c01030907142 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 413690314 1250 413689064 413689091
    0x106050a020a031d040f090b01080118081806030415060b0c0d1d06071110110304030b060a05040c0806040507030605030709020904020f030112060c090f05060c100c0210 74
    0x1110140d8816078068807061005a406035000070341d11002d020040d60f42ca0314500305441d14440e0843e480340441000c03078407400c2420000070714403040c0c004c0202a4140329102004140c04810385da00700350b0180d0300035951401c505400450303890103000720794420300000a200c2442804c07800c0d92801514120100440340c1d641e2440302c018426903445811a80210b031840b0707c1130703000705d5028055813102d810440c0d00c044002c00045e030136800710b00d04854520404062509030300f800c03865500807400600709000308103800c0d40550307502e000307903c00105170080b0400041c0d01600c41c26284001000080e1040c8565241c40002420f050320468003140183d01e0714000400302442070040c0e40c216500030b00609612800c10340c45c44080e41c48600c0b000e8016400304021003034006140011402040440c02c01001c8207280d20b4905c00380d8041180f080204042914140300c007030128030246003201e90032170302595941c5203107050078244030b400384107a440240344c16000426aa004652940101c1051504102d403040c900807 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 413691564 1250 413690314 413690317
    0x6010f0c060e0c0303040609061202040e0c0a02010902040f1a0108040206031609031401060317033102030d020610050603190c09090203101d040f11040e01060815010605 74
    0x86010024014060250114407554804191803941d902990091003140300401d02d5580554003c10001d000c6010800025a03c2805414020322020003903182510303000910303819072400f50044002e80800074182c81654001d41c0050b09156000c0d006200301402e110300f810061103040700c0320380404002c4d1401845584a40d030018404d0354010710003403c58680b281400e04c0000000c00b51402d00c42c0d020400b00100e00508503d202405144001040c144d0a40c035000201c103c640c050104054000d0061200701603140b440030001c0560015018001c103460950110020203054010750540205030305101c1c00d0743d000c140a44111000641626000da85805028003803104071030402d62200156110800f030042c44c2c00c040d01c04011846d02c9107031aa15080800308a92094441407629040d114003088089028001004c50140a01008107075140c15280c2035420002104000c04584205881c12100c0c1e44584c80f40c4c800c0c0c21000000c00910348c94100c5203664400c0b41c0d80c4210841044800021314611410 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 413692814 1250 413691564 413691587
    0x2100206090d110a02120307050f0601060905011d13060302040513030c0b040c030c060e130e0309041517070503100e1b060f0d1506020601060c0b15180406050601 71
    0x149032607541c955048800c3c540071111490103001d80300040c805aa03400c12101404056039000c5c40e0303105900c0c03501c0ca00c1e000e0b506040c00550341080d07004010b01c5401515201c225074013828840302100c01c844041c41c0d0008010552507100030034400f440010503e5910107400c8c5d902c259420040360b21120081c000110507020300800058111079a140001d400c1c40c20070b90400e1041960a62241d186d0340c0d0303002040c07102c0d041080083d1088103007024a183c407410800c05e00029580c208070140101c81010f45034030131a00d51501680d11340b4a8030b040300d1640514100240040d01101f01f410b00c01c401010344811642c031490340b082c4508101060b1140c15031281c0042d40350428002c0070f170580c28441d40c00c26022701e26402c5511032024014200384000c60002041c038208003440002c2da103008281d0ba42072000a642294085510440041c0a0765801c0b00613400600e0300009601705070b540300246078011200e84400c030707134100007011300b1850345140c440707541400340b4401c1c54140140e43d224401100c4941045 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 413694064 1250 413692814 413692831
    0x110a1106131b0504111312030503160228030914060412060f06060306051212040605070f02030a0b040c09020708030105060901020316123b060c0604080702100206 71
    0x849804000031128001840b014248107001859655201c00103802c542100303403e20b24000000039842084007488141101038102c00c0b076022071401042c1c40041050200400c08007400032015032080e245170007000040c3e809000c00180200700102d881d6900000341000388100c0110320610404103001d142081000b0410b100a0906404c2a2402e007180c07a07011503600c4145d5180e070340e900c03050103480c00038040c4502900300c0382c80101d40c0364600810300550f807032015450480b9070407841c0c55800c1c400061040b00c0440d000361501c01e440316070600300a03000002000c0025490310a1500c40c50070030402c0c08140c1c2c4202c1c05440300c0d0340001e540c2d4030030b84d081e8401e03000c00504100d0204014009442c05038080c0400c1401807049034104101c041941002c584404410307103a1f04181d241c1208107907800000c00840e450084e41c0804500f80701060f285180b02d0350011401c1041e08110082907945800c0d054800c2d48121a084a6040c11f003400e000f00941c0c4800c4080c1e000351003542d03a286a0a00000c1e031680141fa44 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 413695314 1250 413694064 413694091
    0xd0e030c04050c0d050406090c1203020c010e1206040606090e070e0c03070c05011d0606010c02091603020c0d0c050712151505030102070b0a0c02010b0d170904110a1106 74
    0x10881004010b000c02000f20300328803c10301c206015180d2510840e03124501c220300004124490b4180b82601d64215408000040890b14185001a03404600046c0400c000e0800c140c0c1d00f920392001a007404204212601c01d8450321003000248a500c4d00044115801c40341d00308002c100c054102500c41003a40180050441d07080042107c100e4110002c640c800254508120740c0c080998646007581c0e040303010b08111800b07081e4920000b41c0709022007038000d8800d007042408800c0c6680850018400240030700c180c81002c4003400003940c0250101c42100307500500703070385440d90307a2076000d4802c1000c071405499900ca80f42001c02d00d000007103a903030b2055400a00380600a03401800b1800a07210214000c6025400c0705030000d01c0392000d0001c0c140b030074410001306808d071a00260040440c0c110b103914004580c10900566003984078102080b03103094001a06904400640c4410221442068485a0058580840540c03040301c4070010f48800f440c25650405030b4851070200c0703640c551064800341e101e000c2 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 413696564 1250 413695314 413695333
    0x6050405100e060d02040305030307030b010516150b03030c0f0609070b03010e07020c040e150f040b06012706110105180303130c1505040503120a050708032502010e0d0e03 75
    0x2982c0c4040103040024421407500300d510040000341d03009940215070342c0c0d10100a0013031444d05805005111748007880c0580c104400c0201c0315211054440f0058100401a000d29203140f009402000c4020000380450366a81d00c1c00710030a96603003d613904c8542901a01c4042880d065021548604507899150f54505507420404012400003000c0d0a4406510075040c960302d60f52235601610452240b0030000d0709000c510500e180280241c018000c0d904980c2da60304100015003100c0c08103812440a207400101403003804c00b800a4102501e00002e905843c40c2c1e0001005035001c0f00c4a80c01819040003840642c41c2c04031200c03d5206100c500290582040c40003441c050050000300b54218019010410f1081d550300e02801c241d40300c04c808030002000050f082c88141000c21400800d101d401174032514142d02001c005101d4083c00300020521003002000c2038005c844d18451f000716220b0a4440b035101a112034002e802040c004025002d02d00516001d154864001d401001d1152000b5014010500 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 413697814 1250 413696564 413696567
    0x3020d1d0405040503040f050103110d09020127240207030209060a090f0203010816083307030b030d090501080103062007110f10170c1c060f0605040510 67
    0x221040c00500c065026020316564450180900480c06100510707070341d0303042c01c0d503a90101c00150051410716082c10001c10350000401c3c02c503141b0b07041c00c450020b0f0000c018401200c402d00680d84085202503502031040040e42821442d508581d92a091010b1078451340e45060b044884c0e00100001680102c2801c0025007450805180e0282c0001d02243c0f240342c844941d80111030442e409a056070751702200500a0b41c401304107842407551079440c0d90f0703991440c00030a641d603012401352101d0704d03e504070408039005556041304056000c100d4505a0039260501005000b05600c94805104e48524240714050380c0c02640020240c5006031364007112a030840c0c4845d8050000300e0056008080610035183e0482e02c2c82001d00480340c45440040358011070b200820145010706094648600c1d100a000081c10360884404060f0041c94100c9500580e101c54034850715000d614000400c1070704450104c24501ea15600c000251640c9801d0030041035214003003115980280d001d005d422511142d550351046 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 413699064 1250 413697814 413697827
    0x8071407020f01030e010204060201051905090d110a02060307020c18090304090b030a0f0305030703060b160212120d0b040509011a0d0c050d140c03010e070b0705070b030408040303140703020d 84
    0x1094181004202d540e007018005d07089a00a910003c0141d5452040c46903181015803180720002c2030341030520190400102603503c96035002d0180080c841c000d45280c00e641e03028050400007a400038403040d241c0c40e041e50080e4403108550b290320302c6441ca0a505002c590f5420b8015401000305030021401c05080c10050300091012501099261050059480c00a00104404c0b00c07154840d65a1b01e489040a03c406016035072981c100c00b2403c6002d02a100304a9800c614001700c3c00c3d0110303050444000c200c000309003460301419001d13080160004e6109126181600907141c00303101540d0800265490713001650895102c02c58403400c001c00104034401c2454000c0c220700741d8902500e200217a15a5a0000070741030340040f4000c03581204034184140402c0028030006905c02d4081c2e009016401c1c000c504a9141c9019000c0c5a00c0d01e40003150440a0010401414010344204019603581341002d0410500b240c00c10b11085000411050301400c24400400a0b940c0b003036803640050a440769143c10681d0384 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 413700314 1250 413699064 413699089
    0x60414070c060209100c14010e19030512010602010e0c030f100522030309030323011a0d020705030d0c14070206031302100305090c0609180a090c0305030a0807140702 73
    0x1101e4080c000442107175070b0455001c000a1050310340a00b03865640c40e00d005888a415110300c40b83c2d15000110a02400104622201c61210b00070b451000410b46000c0d181c1c2d0240b04a01030707203941c40e071002042d11501540030050000959080340d0428404000309513503058203c4010103140c002c1c41c8000d04404079a0881034004007070031003060015103034400e00410100c99507800d40c00a030700c0d10141c2080c10b8251007500030051a64680d042508000d01c1c07412003080c010b03c140c403001c0d00c000e110401c01c0b1039080c1c04da8080b00c20000b410740d03030340040b41800343d629000f04200094030ba01d041614910701e401021003d00541c2c0c130449890500f10b480d02004400c2c2c00050441011202c41200d6000582d00c1d051601c480c0d44440d103000880781042941d142c9070006d0004580d0040364200800c624035035910b5030981042d02c151b92035a8007583c840c2e640748050000e0140041013100c1c1c5140100130010007001a01240c0d020b6070740c46800313903030714541207800c08040981c540c90702c0303001c204040140c144154840803 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 413701564 1250 413700314 413700323
    0x5071a160618050a020a0b03091905010b0a03080301090c020f06070f09090f09050105010504022a010b030d05030702120702060405120a08030c09010933020c0901030b010e060414070c 80
    0x200d0300c510290a40840b4610b034000c40d81e581007200950b04503d007020704100640f12190b030301c03400c0d40b800d81c20720f99842c80c00021030078051910001d103404001003500028504d83c409009445500c3d56490108000e820a00507040110b04000c2c1c14900148000780f4011600e09030b0700100f5241d140c0070010b66402e03501d4034600080000410004c51100c400f400f8800000f8104a400600620316041440c02c4a00681000f4400c500400c0f4211640d1104a0003540b04502a0b5459600c8241207411300d00408400c160b80390507001d20660303c1c40482d00880510b202c3d40f095002d545914603645c003400024883d000c402503004501780000d00c1941844611000028854000c56050111903100c1c40c80325001180e40480c003400c0003074010015644601a1002400c00c4486036040303c0c0c24004a031005000141c505806026042ca21480c26100b00280b070041d102c0078040c0310711940c60303042002c5286024003a40300c4910300704001c200241864480c805280ee43c11001481c0c035100c206044038410b80c403600545 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 413702814 1250 413701564 413701571
    0x41d15072a1b0602101a040b060409050403080403080a05060d2307080c0a061701050405040c1a0d0507080402012a0804080f01110403050606040903031e05010305071a1606 75
    0x1000030b00500c0b54458070540402145055450254001d240c4003201180001407070405541102c1040381411020303000d44121070101300300d07a144c004201140141d5120142c400d043c4400e002c24140c02800c128051030107641c80045940c0c0304a404001d84c2c2e0191800c0b41c000e8400c8409502145501160800200c4030382c005201c40341044040c1c40c40c01d10503811401140d0811080c2c00c219241c00200740d4010044e078201304400f49107014254011400503ca05c5000e04e03120b100280400c24030755a00300250200c007002548003a400c0c82d07600744a81002e003040d5141c614002c003040300e0074021071800e807045038140d4413800140c55004104d030803070304a01113902842e00740c801d0450000d4646005800600b9503080104261071003e0b540509407103410a0380c2603005400c01c801d01c046600407640642c0014103440200c0d0340b060500c3c00720010b1a05a218510308030f005030a6805140080e040300341246d00403021558215114014465000d5810441c98070039482041040e1a94200e0303103c11032020700411001 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 413704064 1250 413702814 413702897
    0x3080d0219111c1d010302040b03180d05030c180301061701020c07060c02010f23040e06090a0c0c0b0c09030319020d05070c03110d02041d1507 63
    0x18011080c1c0311a5030020400515003261081010410210000f03098160100c10540c02d440281903000054812400700e1001004542181d029404440080000701ca116640345404c07001c021300da0041c0c0000030303440d0040d21400d00c1c042d40321394140c0340100c102c0d005451824a0200541c00000d500101c0303581c15548400000070000c0d900e20345030103000440d82c005a50b5404036594203007051010b03008542440303107250100c80941d0f48400907040205042c200305c841e0903241e803009250141081c01c5211440300002e00810560120404039004c1c000640301035a09454064074101034400a1502500003842c0104800105a04909690700581010304c418a012284c5002c01e0440e0321009105190610a41d1070311001c41d410003c0e503035000b41900e4443e040034490f030b40e5140c4040540c80301602070886810407203c1c90b650a0340494510703500a05c2003003c2c00103820021860212610f12100c20b028480f20450b5160223492040e100761069070701c1c0e03022030082c000b2890003510030b000d04d010010041283c8 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 413705314 1250 413704064 413704087
    0x4030803060609131a010e0a0602070e3114060705090f0a09020d24030b010b090316060306090c030204030b041707080706050609011e0b2b0609050c1303080d02 70
    0x103c036161900f805d00e40303201c01718050004d031994041490706402210004000c03c174050780460482c00344c1c1c5400d1106902902c920780d41c4000707502e030f820400002d00010805038040c03407901c800241005214101c8a011600130030111781d207900781102d001d00491010030000800c2d180040c85c3c03100c804002010015080c0d2514241d0080781c010404290016540314103003ea06042e09003070076048003000c92081c42981c01c503031340c80d845110184070311b010302000841d100c01c165030103101414840c1800010811003e0b42c0c0d10004028040b20302c1081c03881480c0c1034110200d40e200f4000c88003681c0e00046050300d00c1c0c456586445881c00d5014520103001420303c16200000e104000134414940682000b18043c02c100c02040f46408060f0720001d000c144c5504107114240c0d428458070210f84080c07082e40d48030010042109220303140d0403441c007550b107451450408121050307800181960320302e00041080d80d071020225859880795040724440c0390f412110400016074803c0c020207440344400320144c00c18520618 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 413706564 1250 413705314 413705321
    0x210c15140a09030b130b0f0106270510090608010801180206030903130b04180506031903020c1315051005072004020f030603010c08070c03051b19060609020403080306060913 76
    0x20084000c50490112a0520450045558000b0008020901d80b54500070003e03140b1072900d02b008900c40f82440c3e100d04150071241d080380043c08080c20348030074405114001080800d06e40503000110301c8403800480c840360305104203c0310051014035884800380c0794003080724581006041900601c02040751340024101e81e100c0c0002420100c96580d00c440c2880344010f01a041080c0e528030813817904041041542d000951680165480e10b0441040c050904040f82403c01e806032070768008038000804515100c141d0f00070301c002244101c1e11084d42d6280e1040000e800017143d851700000300103010200204002281c0b070350701c140200c810310b03041c0403e440101e81603801c10140c0460281020040180f203050a000301c81c0201118644045145008030b00907090400c647d001804000e00403a0801c403031a6010002c0041c1d010206c110782c0702024502201902c03200030035003211513a04000000501e4034843c000c0d1010f8079403082489045030f407510203010481d0001d030005035000a5806041c1e04c400d00c03511 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 413707814 1250 413706564 413706571
    0xc09120f050115120c050415030b090a021e030f0a03090b0a03090606090e0c0909030a0f0e030a0f0311030705060a020c1011031506090d0318210c15140a09030b 70
    0x1012184e002498204000002c02c0d40d4002c1e802241842c980700c024202043e1101c080d207034008039000c4261205602d480c83d004c2c0b400c2d0700940000400c0200300f524440c000c036080803280c0c1101116505000030300c0164071402d20003401408500d0948040c080444000007510900b181b92130005001c0d20261100019a1159480010b45030b503210b003400184070041c4144c1901000c2500c103280f030b90601c111210350343d100d1400032074100f206400d401d0b840d003441100d00c4400807030003e08030341110049041c40c0a01041202040b4007092400707078080350483c004001d41c1c220680207806000680e4480d0703c41e1010b540810a0130a0a0091104940c1210051b01c107121006004a440a489140c810080740308501e86000c03591180c1014825080b040d61940000c1002e640d1600d012011807243c902402003c10180c1c0190303810664001c00ca14200c0316450302940d0305070090b0986641a80d0710101e070810001084440c2000902c2c2d4030710743e040d102a4000600c00040c9500d041c0c045507641ea1182a1144001d9 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 413709064 1250 413707814 413707829
    0xc0c0d14100507110610030209060406030c080c1815011815020705040c032d020c07080c040c03090327080304080106170705030a06091703070201020309010c09120f050115 75
    0x400078808500e52140d45070168601300e400811040c00c01d1440040c3d10242131000901c1032288000065941c0c5843d0044401141e100000c45905500d030b000c2651a644040702c842e029228200304010302e6054010010b000e400c1c2000e50740c1c5104c0f08900110b0700e03910b40814075490540c5505000510401c600c0c551150231641c0d501130218141880c0800c02601d8820403050f007014200106a40e01800e46150030f0b5000006802e010b003d0307201e204021001c0d0041e03003d8036003e80103a0000203062000400c1010140c1000c94080100c05c009400a4044801440010700003440c0480c1448110612120807000800f040700407244060355211802d02e56407068001000c2079445200402076070b403040c40012195405613020b8040d050421300420750303600800070050050f42c2ca0f80002424012650501d01650109000803996450043d001034040c1d40192240e540070340ca402ea0f110105072158590303005070b03161103003c003080418035140e02d0700c45a005201034440f5503030b401c14030303c0d440244a2090000c08a4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 413710314 1250 413709064 413709071
    0x4050d0506070f0809100209120106030b0a0506010513030609020d08040f03020f040908190516031709010b03100f020d060e01030b07031e0e0309031002031602030c0c0d1410 76
    0x1020014510700031070070f001d02840010001c0c003134100c6001c02c2c1c121604100780f40040c1c88500950024140c403000b010604019403030002c0c0802403040504170540314080c10741c010b00031a202c010046a0620a4100044000302011000e000003641900701c0e4030340d04e000074400d070161380f85600d524860780d120354060152820380b000100114105544005070178001124108504029910741240c2c0740705100c030f0581ca104259410308102d40c014419940103004984002d02c98801707074900584900141c51f44854035a0403000024044c1c041401140200b06c0e010b1b0250440c880109803010141c00d581205224a580034041401c4001d254400c100080c1440a010541545035080a0601c500091309200406040c4080e10420252410007419045108400000c0050780c10340d0032402d41c000d0000e243e62601500050501100d0315402660284007000b8000ca000c90220800307a076207224208543d0300c5500b2166800d0ba0501c0c0031700702502d00d18020f1020003079100141b0001818801c0c0f007045407001a40e07 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 413711564 1250 413710314 413710321
    0x7270503010c050f07020f0a0b0c010c030b120d0302090f030a0f060c0f02070b1b25050a060905060309011103070215010f0503060f041e0323210c04050d0506 69
    0x40900455114240a08100d0b00d0099804c2042080b403155800282c002c2c070103040565425100c803180e1b28020841300c00c544d920782c280350710303014040c060020b40314000030f007003134440c14903441d1080e1150803000b00d201c010310016682100680c040d41220000f40d030b01c001c154940c800180c4060240550070340c4507090050441c2e40c20f00d810000c07120401181c07010403007600381c50040580c0016074981a146d200c404103456006c2c440d1081d1319410301801d01a0140900a0b5841d01d00c0002c1c800700002c01403a0024880107620303142070084e07660003441164002002c198040146043c800b0065810481d85800450b20312001c170208100c60740155410070040c1d0240908046408130403132454090500e1031149010f440c50203001a0703071410050100f416401510000c1800c100001c402910280303480341640b59100990705000c0e02c21030981c242d07151000050015002412180401c0b0f55560052041031344680403da5499181010011f00c41200080f04000101d186d0b610044584c10003881500100118078 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 413712814 1250 413711564 413711569
    0xf10080f07051c0209150f040207050a0b01150e1c080406120b04050103020f100e030d050a020f010203010e1b090301020418200904090201020c101107060804050d08072705 75
    0x110350300c00b0310b01e414162940400060380e4042505402880080da0000306c00342541c00200000540a00c1b950f106200042283c01c1010201345c00803030600031035503990540e03030b5200c2a500594410b400d80000030220301d40185c00d440e03d00341844200b101c01ea00006640295501d080003035000380c01400101c0c20900c0804032880e5240901958054281c038107002d03d503d542e004c0340f00e0a0405040c2845404000246100755104d64080c040b80d580080480f040c01c95010009043c6901000c0031900600034116444102d050500859040700d10343c0a00100655440e04400c8100c040b04015200042c0100305400041e54240042c01c00b900b00c0d851004001c40524160b00304035400302c4d04545006403203002c8404190030510986040c07503000d480c0419152610310040f400c10402221a5038401d0080c82d40c6150254012400c5008000400441c0c1c19139899207429522350108580c01031859216150741482c2e5840b82010304e8110800c0c1c24400c2429414550000c003000941041910700f812400003040b0301d1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 413714064 1250 413712814 413712829
    0xc0203070c09140c070b0f0403050d110d0e07030b010b07021923100212030c07140105040201030c020a05120a1202031f05040b15130302090a0e1507080f10080f0705 72
    0x940300f04c007000e15081e03090780d41c00300d1000c0c010f01a040c2c0d540440e001400745405601241d20044400178100b040118070310b00300d038a03034010700da800c00c845107401448041070800080d5242502e0300b1280720b094580c81c00e40c0390806ca901c2503a040381c00c540c0b030b80c000e03d85102c0c5010480000c0e1004000c90070b84c0c80c68051071100c1a9440005961007075150318182c9495a8000c20311028441034401c6040d03a07a960040859524441c80d50002c1014003500380841031510107501c0540907610036603040c8180079a40784100c0c0c0e41c2100000207401600020688901c19511200030b111001c501d0425034092000c002825003241c0007181d02169a001c200d140381c5028135210560070103028101e40800c9204c0c1032402040d12890400c0c1e4481e000700c1c00140182d00318900c1c400200085900402c10a201c3c54400329640162200e00d02d22402d031f204487e083e00340d204503400c24610951141d03880041e10f60381d002000c951079201415489200154890220f098003051100c44140b000d01e60040510720325040500011 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 413715314 1250 413714064 413714071
    0x20d05151320030a15140705120a09030306050d081e190c1509050d02010e06010b070f050f06180c0105030606091c05030f070506010506030106090302100e0a090b010f0c0c0501030c0203070c0914 85
    0x3005403c0080c0220400002724058000501c040c002489034154581a001030040c0d8100c980d11000d0005800d080040c0d60b0002c0000c0d480c0380f40d000510080113995a0014098001c8899480442413082071545200c2d0f085024401d004518284050351002070000807510711140076130b826000800703260780b03158090040c4800c400180d00281007c0d072411009010310300400100410180f2106032103002d002d003c0041080400c0c90005844c1c10f8140107048240c6000721050800d00d500404190504540c001e000756032007818060b0040b49420801c00400a8003804250800340d4210904c0380c650104008101910080340350401c129982c03110f80c1412440d049050740300781c0c418681000140300b99907000607080201d03a410b40d803020050032075904c151400c54203c04a1600090360710300c0040e40311540c1d0480700302c6000030707218807481315104d40088034140000c941c007805210809000f00009d5120b544200d44207403035441901e00708070013a40c0d2201503981c00d0b0301c081c0c0360030b80b600d250079484c1d8803c44580780c1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 413716564 1250 413715314 413715317
    0x4080408150103110f0111030301060e0a1a0304020d05010e070b090102010e06011d0c0c010c0c020a09090b06121207081b03160b13020d05151320030a151407 69
    0x800d580345580c0c01584291300c4a02a0068221203128070701c03640203550382e030745a440980c16a6242c1da1140f80044c401c507100c00c43c16100d0908050005102c0300d240c05501c58004150a0343da10f1a43d8603000d001114405400c102ca0725940e4000f151a0020b0912440e00600001c8105a41e603001140009003500c0741c0401b4018603030803850042054200e40800450340300301c5888500ca043d990b500000040f0b000380702000903507500b001e412040700c90307210001c2d1a03241e10841d2502d0405460301c007200c00300cae650385500908121150000c03d005103800e05010441845030000c0f00c40036075803454550416003085804481806000c41ea0740c22b0086d03041c2c480540009645d0017141001549480d6114003200080d01030290301c030610110300014808a1a50380315500540f442c400303501545010b55580c40020310031201d01c207042011600f2a0790101211070142d8100c02c19014110488004292850041c10155031502c05c8403002c10001e840c03554490742010b818000042c0480d4a01078049403000028200c90 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 413717814 1250 413716564 413716603
    0x4060b040f050409050313060806031005070507060b1212040801050a11030f04030c02090f0f0603030c030405040b060706290d023601090b0a080f060105090c0d0504080408 75
    0x104688030440c580c02c07544115404941d1140e6810407904610a1000300c0d508a030200b8000319006402c603525a01441c0e0903021180c081c002c0c010000100c60303068030a02d001410410007240440c105400400e80e11000410301020f85508800e02c5282099150045202c00e40200307003007001002c01e2041660040c024001840070071061003a8881a120007002c0c9a022400c81c2d012506243c45009508100d0317038003a082c0c2c3c00303509050308003800d5544100c0c0d40052514103000011142d040c00f00c1500d048480d00c0c402182864201810040a89429090a60032074024091180441c41c03901420342c42040d401d2030b09024880344850b0840c10b19600602501840103d80c0550058444000303004c1d840002e0105d50115218400010341113886070801c0e03d01c0e01d00c131040003080c3c0d501c1c070381e1107001e1804048903103400b2075a440c00401c2d15845400090642d0f41c01504c0104010700b0500251580b1516000d4401d00e010500b0b0469801c8403020794081e0f91000380450b09108080c0200017648842001c1c1001c034 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 413719064 1250 413717814 413717819
    0x18090e1b030706050403080c01020c060c07110103060b0a121b0c05060a050f151305100807080c03030d05070c080706050f060603100303110c040906050f060121020901091d040204060b04 81
    0x4c3c082e07110394840102650070010700b01100c0340d0300f981036418a000100507a1000d040c0710700c040840707400801d000d032110400000500079940c0a4881c10040340c40d82c04119007044100d41c0140ca10501140c3d200c0200b9454000d80c450b00e08420613155001d213040e41303540344109802d0030060301e072190080201805d20b2508052182d082c1541480543c01600c0720081c1d100b0f495440003043d60403100072210310405041c40c00307203e01089010b002c8401e07201014100e401550341d80f424555076400315603500c0e4068000b04100c410b090301c0380d081340380c4c028803e0801406a810303a98a02c415030340b1598007510301c1c9039100240b0401c1030b088040c40381c00c8242280d8690440c104805000e1b1a082e4504c40102485480780da44441340d2000d00030a03040301c070000c1040000b0509410988003030f04003103803503198200203880003401c258011740c42002c8021440810861764142d20703050034000c1d4801e02e803050501445071340024034164060ba820021a441c01c516040701d0a040c81844262145908926200102030005 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 413720314 1250 413719064 413719067
    0x60615081008062a120109110708071b03050f070608011202011d032a030c030d05041e0302040606030b0f0102010c140d0b09070906110a0f0318090e1b030706 69
    0x60980141a02189220003013180e20121442d0494400e02d4a02c4040890202c0c3c00b40401210607048a03841c03102403000480c2d440807000c0b248604200180812009d01c40a004aa4858400b144c03201c55025207410321a104d80b1050701e00048030b1944003090703011000600a0700c1d0301c000c0c1d0b5401014035403001c29140c2c4641c0c3c006805000440710515501c40d03a100b02c045a50390800502001c50303a52800c00c0c0102c0c40c01c510b40c0b40c08150548070709004e1703c61b819003542a42000503000484014a6644c1400c003070600403118400c00a04c100801c0859181001001681d210f02c104401841d0302d84000a907469050240000060340040d01415a40b5144900c1c1903180c01c8402c0c00c5010f14007540d0344d9900c180d4941104010700300b0001c402d030400d0345c090030031110035042058481601c803e0745905020584000d0320640e500042c80300100040c01101c60b540000340201c104d0044a10015040c40601d80c803491008200c8408400206517a03100143c12030702d0f100241220071031002e058000d49115400c00c0b00 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 413721564 1250 413720314 413720323
    0x32160c08070210090b03010602010c0201050906010f03020d0302100f050f10180f020c070e1b070f030c110d050106060f0212220f0f0e01150207060f020109060615081008 74
    0x70340160904003079443c295204411403009810f01103120354980d40c5561009008088803069000558030700710204550a0340050110304031038040c01c0f1380d403c0300e0030740c4d0910003003015408084040d8440c8800c02c1d400d0180074000c980343d0175070143c0000b0380380c541210700301d06030039002e0120032500c800380700d051216429688183c1034a91100c04c2c003040d95988900d60704001e2058081c076100a024041d1301180382c89011625500820b07070410441681000261200300510860f40000e10b5100c46004400000c0d018010808070350f4000d0484202d84200c050204d58020101c10040360b241c5d550f80800c4c000e09030070880c2a021452070344024001c204110040d582148520301c00f030340d440031003000030204522001d80700700b0107880c0407501180315030f036121100b02342003010b030290310f120040170000070171aa865040d000000381c4103540100141890544140c07002c0d02406140d00c1195200c00c11640480c8050181100820301000c401003041c480c581c00401c0c0d004040c281099101d001c1000b004202c1d00002c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 413722814 1250 413721564 413721577
    0xf0b1f090b010f111906091713060c02151902011a0102101107140102031b0c1c12060f0e10060206010608063708010c0f0332160c08 58
    0x1003603004070131980e900c0b034940003200e4041a5802c2000d02c0e5801040060f4000151040c0b103400c2000c105584085078071424060016110826010801c08010261080e0340f85030340140058800c9030050705d640f00b49080d5500481d80c0b00001c098140795003860319424411070f084a5540c110700f0003a1694400001c2d211101d0440b50300d07105031285a4241c5420100c401c40e5100c035400080e5890a42481c054213010390011600802000580301848510080c1001112142e40c0400050314040d45411615840346103502020390401001d10741d00d01c80303000c071480f0f5030380541130380010030745040c7c64403034001d0462800030007000d00f443c402042001503a1f000502141075464604081440b65030b28004540e204c42d0001c02586220081403c5c010380c803c1d442c40052141c00c20301d003411440d81e1a015101c1c240c03030005818500149400580301c0c0054402e030300580e0780d500244482c1121980148040a60105500003280380c0c15621041c0f001c031070940b41290461503128204088992480c0c1c44d4a03d1031302419 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 413724064 1250 413722814 413722817
    0x60b032109090c0c06070914010f0f110703020a090609060b04030c030b0403030f0c170708090c0f0d0c03240b03030403061107050a030801170601050306010506070f0b1f090b010f 78
    0x800120b03407404980b10940b031100b00d644c011035246103040e400c0106044450b1003003148014201d01500015442440f60380ca07140b840d51102000c10302210720865400c04e440032142903c2c000d030500800160b45101080c8020210302e00003242c81c50810760744808452469000c1013103150100010400500320726002c200722900504211030566a42c2000e90243c11002e40788031803a45060183d2440a400c680d4103542c0fa01c4d0787c500300c1200d5031400c0e0f09035201d40c0141c2da10b440f0f55201520301c0900703190161984608170405440c00340c1901d0903680311000e40c0d42940085504450b901c0e0f2501041003600008041c10300c1049003402240d2a80000c07d4403886036010241c4290384070000308900c40c8840c0b044541c0700d944101120b80100b0b00781802440c005082c000d1316580030b0098031881d2a4580001c005050741e20082c042c2c8640e0f481c007020844940e000c2d803412150407003081c100381e0125241c0d98034184900440509041c042441000d1000d082071242c01107602c00303180ca044030314241d030b1000020442c0c4070f85 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 413725314 1250 413724064 413724079
    0x31608030402030a0807150c02010b030705040e0c030a050d14070b0103020d0f02130504140d0813170c01200f2b0e0c0f0103060513050a0204050904060b032109 70
    0x118004642451002ea801810505d400034200081000c4901d104920f0003504004110000394140e0485c00c1c0c50700440540c1c0d0542c80307d44248524501644204040c04281084508000301140400e086c01e180a6090318160000121000040d8000021440c1001481c00706882e107052591041540003040c00083e000f01c110001702070802400f14100c035112a001018540126100d000b1b0002402c01282d040b1046500380d0380711015080d0009540c05110f590b42c403100d403540d607103661b01d49807841144011780314030b0088030000c402141007200074540b40d6001c2c4000f0030144402c5002440300f0414029a14403440b0810680c2e00c0c0c000e200064640c5000d5168200040d915407070b0305c2c0300019020118098a20f4a4010712440760240011941400e00c03003540c04100400c001c0300194202c0381da034498a60072010300300410300c4103001c42c1e100300d500070403003400141042c0d00c0385c6c0407030441181100d040720040d1392100804060301c1e041080d20545018035050164401c402c0c0c25201c1940030b8084030354090040e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 413726564 1250 413725314 413725321
    0x60501080906010905101a03041a011206020306030102070804030b180601140609010309081303110a0b03130302030d05100303030e011b0f0225030b011d1501110a030801090e03160803 80
    0x46c441803440081ca12205900005001c9158a501e2640140d0301251101e0b40101c403105402080a103c82c100d40a103902554405e6454580c0800b82d0b0000b4286981558200483c80c0014058005000070750301a8020780902d15104144807600d48103a208420750744c3c80b500041080e040e19100305080c0440035240140c6495980f0b00503409010384500090203410040388001c0d140302d0950801c0d048a01a000070915602d41b042800118400c41c0101484084200001010452a10068001c1500c0ba204492405044404c1e07d0111201560000000c00c88000d003001410780c540104811001004000c200740c5200da06d0a0190200500404062041401c1a003058034000c0c841216041c0403840c5201c0320720307184415450701230450301044500003e02c00012401800c46046c814009103c905406d0140c1c0326103884501c00c1402180e01810841104c030030b00380c003100501030f1205a5100c0d40f10b00320694144000740013502c041c0c1156050540c410b000000080494240d00f031035131030304030280c550340e031700e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 413727814 1250 413726564 413726581
    0x608091203070311120f060f040204030f12050f030106030617010513020f13060905061005070b04030c020d14010f1d0613140d180f052d10080a060501080906010905 72
    0x141005010521040c1c5c040104114a114078240309038011181580f4404041c405c1208078050740c000900a042414400c1c8001900c1d485294205c242e9410400d050028003011a140c40d40b00341c01880000391942010440701801140407d00140500001e114070300d409245000c62508260010b48076010841c2d0080740391303ca480c078002001c2c40e02042400001d840306505005440c06446041c0194001000c000f1100e10034010360b520035611241816280c0c681d0f8808440d08c00c20404140d034070910805054002400b8440302c0b40052012000200b5000214a8040115502d81003c0505c84074400380c0900c11107030220781154030020fa0241840c85000c2e070300300317610300300028580c4003a0752142101c55054650401007a141101c09482d40c04200380d1112040c8004d00740c0c1c3d110304d5402030f01007406100e4400c0f00451181000000c0465030001d580101d00241d9a04160402d00300495210024007507000101d0241c840078000a0030f21507010700304070b618250b030798005100e4890050740e5540841c2800 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 413729064 1250 413727814 413727817
    0xd0c060b1c11040c0518060d050106080f0a060602030d0222030813150806040902030a050d1205010801050115050a0c080f1804092f090c03010608091203070311 70
    0xc8025008201d188540c072054100e91100e4001035550104003250780720549041d019400140c1c00355580c5604001074903010701c0388100d0740010f40e80e0001083c04245910107051040500030320b0a503075007a410b81002c0300c0c07180c060b2001030b041b24085401c0050900040c2e80000c1290000d0441d0000141d8039520f21441100a01380c0c1804000700302e2030f844002040c003405002900485031040e8002c0b40700d95542e032a0f002d90b180400d80c01800301c6c0b41100080c3e1145003591109298500150a0b00e51592043d42c078117091814480304030b0089040701c1200d00c00444984502405401001c000304013550412844402e0729080c030401d80200a80003d600d4007140c40f815030308480c560301590981c2c4401c0610a01507a5802c40c92106a0b2803840e21642c40d00c07840c06001d10041c0c50b0300003000712503203800381a030541d01000c8003030320180918203900da403001510b0300240c045c4948822142c1a03103c2d410036100600c0a60040c1040d05d1940c0002c4040040100300c0e0120b135081142414009102151031034542d005 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 413730314 1250 413729064 413729081
    0x20a0b0d0908040602010e0f0c03060106080c07170c0708150408030903070c1409090604020d060c03020c031309060503031314181003020312070f060e01021b010c031d0d0c06 76
    0xe40030080703400181130390150041c040401e90202a00c203080d850b00d8606a5981a500e1416419403007040100203060291200640041c0090b0f22107103018074a803144900707950320b01c19501c00e043c4005840007107400c09101d0600034001e400058520072940c0446c070400c03500c015001500390312001020541d440810000c4407183e80c0e0029003207000c16030b40c07a04440c1c0000c80400f0700e40260090bc00081415030045205440345500410034131002d41c058591000070301e070143c041c400f4140c1c01c001010012000b040a080341054210f0840d451500703001d02e08042e9000c0e544814040e1f4818440030b44c9500811140c08265122000d00d0f96440c14003200164400c066214520740344070388182031081c01e0103012403a8061300e00a60441e908141e110140e4202481140e4000d80900030209101c00002d2050b0041c0f50000d0b2020005824600100622901030791811341c40e0280e03a56541c0002c000076050b02400840c04a0302d4050fa200800242c0b840340c65031980710b219000c20009008001c2001810b50005e0781 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 413731564 1250 413730314 413730323
    0x1050f060408070e04110a18050a0227120f03220b030708041a01050102030f07060b0616051c0509060a03110f0a0201060b07080909090708010c1205060409020a0b0d09 73
    0x10280da0303601002e400542607070301ba101403031000c0606c451400e0107801a000ca880d5401107840d00320903840c0035001044050140c0503002e40803c101292034031072507040c00f00c00c079614550074480c2c02c07290104400755440500041032501b203001e013801006c1000c0b0540311860721400d82c100b5440c14481c0b01c40c0022950790041c01148101000b841140c690000982d44034510441026101505560a070000d22800341f00709801a403081143c02c82144004014110392071080324007180c40c4d6021000542c4903000008403400e4025403030303041c0c0c00b480400c001640b031100f811189198030900058005120740704032914603004840009202246a2181c0d10400d085150000d15a40310102500c0051007a800345c88000019802c000002c28400c240c00c0444200d241e1044c00e80b40f9121040c4188081002c0c02420000c0c08d0081c440c001a09140a00405500c0d203000d03592100e0300f41403002c2403c01c5690180c8043c2c022403a0051160068440d02c80303e20640700c00010880e12804104d03560000b070107031040001c0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 413732814 1250 413731564 413731573
    0x2070602040b0a02210a050d0605060a0c03080f091c1b150c090f05090c040815010603060e0402031203131401020d18150f090f03020a0b06060c0601050f060408 70
    0x2c1040002d0081c02c071120310756080d40c003070300001815590307041e14107904a000e0038003c001c0904624024401005a56065180855080d56440000302d898002d07004103c08076071300411480c00c0640c821101a480305103240c0c041c1190400049440e03580c02c0c01c1003030301d800c41407c400c2c41e5490340c040e08189070920180100e0603d400c407145884504001e030114082501d6081a116038281d50003111400c0542e8280642a89000c0c0b500c0101300e06c00c08060304200d001b400810020612000500400f4450307486001e00b0b03a0030354944400102298026444503c219200c0000d00005175000f20f02c03900ca41030b018072926201d803a071041c22407101c001100002c05c0c20103007209072401ca0342c040d00941414280000c040000c001a80c5400350414600740303008001207494514010042e889501c01c5492002140e00010b24a20713560301c1d407611060301d2000b500507907c40c0c601c0404210f0b804003059172101003525214109111030003951350b02c1c00180141840340301444109141515440c0681c1d00034041802101c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 413734064 1250 413732814 413732819
    0x6090f03120507090810021303080304030819110a181e030c06050a1707140d15081614060d021909080d0509040c030f0f0b0f04060e190207060204 64
    0x2804071455503482080d000d0800c00001c03e05401000c0140849000e000034010f185c03803012901c0000c0d030011117801c1c0e10035400100800031603010f03005944102d210707445208003400d00f0b00c952245801040c0711080481d0a005040351111191800c0c2d4081344503a0074034400460000076011150015500200054121000706252541140c0301450803240150f04000540d5111507044509109042c034140c08a02540c041d0014144070724482640841c5074540444491300d440c1950315254003411039050440e49400d02601c000344040c0d90f080042141c08002c1c07601040d50387c0714480d082041d02c111440c03036a12101c1d8148075101c81040b564950072900d42190b55085081c07240d01c1c0d01c2d040c1e0805900091507000c000c00c0391100002c800d4525401074450a00b0007003202c1c10030001e05429030074241090b4484046103411240340c00741c2c280310085c00a0100307000d041c40c824429500066144a8410340c2402c504200b441040720089810982c451594041c58449a90f140e019209001c0c2c0240ba081c03000400 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 413735314 1250 413734064 413734067
    0xb19020c0c0103050a110f03040c1e15090f090b0d08030a09030906050a200a051506010f081302010c030c08030717060405090c060307030e0f030904140112020d06090f03 74
    0x100c40c0d00c1d08240c90030882516202550421564584400c5142c2c0308104540c18000c8002030141d64000d114007d2545842e407222541010040f0041d40c0c4a00c42c0b41084040c044003081d0790300450028814500510306a14102c0c600c408440e503846501c1000341d0386c1c0400080d9031580741c1404c01c0359070841109943c0b802d04040c0d1000034050028241c001420010000c681030b8420400c1303030300c0d0a209680e0028500280c1001090b10100e20801c80106c0c801c1441c0d110001da000d018607400310303400030140101c500d010400905582c0c4440542c1d010820032070b04200b0100e58441159540b26020705c0d105156003214a81507405041000300602030203000300800c40700700c0c1c1c4040b104054131050094205907444040600c400e4580540b081c01d413913040b003000e15a041c00c09001445e40200c030351401240c11200404018100400104003079016000006c80d0115800c050041c644490102d842c840c407a5803400700c1c0402c0c40b0940c810002d20071042502c0389001d210264001450f83c981103046001c421006280 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 413736564 1250 413735314 413735323
    0x1104151e110307020913020901080307050a030806010c2f010302131509030b093306010c03180e01051c0206072901060201020a02251703070c080a1401020301030f0b19020c 75
    0x501f280b00fa110000085904180403055610707041d4060010508201c1940d400d544280000f0042c60401c1f080503004000b1a10090001101c0c08000441c0303c11031128540ca41502c0d00007040560615004000031003401095000034021210800d0100407500300300c03c411102000194009020700c40da66080c89103680022070200040b1124041980580040342041d050b020604c049a042403d41c40001030b2642d4011403021032001c1c4a8a0b00780c3c04581586404c000f5425150441e4415034850300046c001c3c0d040c00c01d0b4010b07601c16011b900d1200741e0410f50001e0103074800d030745004022140d0b84100001c032008048481914480c001c2445141e5a11008000d000f504080d94400040c4141c0c1c03442d40c07100c202d1042040c100480181d0030784400c6d04080300c0d10207042d2004424001032208000b41c6000c5000003071901d01400c0d802c0054452565641003100d25440f80b58450941a407042004100103442e900e040320304103500018400c6507641e403103a4071007225040385400312002e00004100c0130016000c034 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 413737814 1250 413736564 413736601
    0x14070f0b0c07080109020d021e0907020a0203060603030304080715020712030509191707080c010e0c011101021207080a090204051501090f0e180a061104151e1103070209 74
    0x41102c00c69540d6005981c20395200010194102c03c40c40403d80160030032800b4058800000c1d22011031007c400c3e00400e03540350701102d0b05001a001003080004514040c082180c105400b10b00640c25800d058840702118800c1da88010050004c1c85001c00b55100d01e42c041e941c14607008465036590181100c0c0c00340260004640e008424083c103000f48034160101c0590400d1207070004807051845040101141c076030341c1f01e1501510707403400c01c0c0000710008601f400364002c9031340c510020700845004140050458203600038a041d099005021148044080e03500203a805840b910307122180b0385940031080000d000341e01019401c5030629040180b071070542c41090108102c00e903105131000d6640c088400d54006103000b07250f0803403001d801060462403184c4194404080c0d500544410100a5031008201c400c032545400d0a05800b04040003940b0041602070107180107030038484000e184d40c0e003006000007944503002e014020591020300c01d0760030030001d0f05c11030340e03000c0d040d42c1860a10f100072807003058030700 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 413739064 1250 413737814 413737837
    0x912060907090605191403010b120307050d0518040903090e160e01110c0d081b060105031002040303020a0b10080f01050115170a020903100908090307050a05030a14070f0b 75
    0x200001034141803c4840c5c034181c9a45036821140141090303041c110307040150f401d040d40341d900c0d40e400c40503075901d044410b2031000c149001517a50744450714002e800e00c40c0c080c00080074880309122080113210342901c1442072903000c071000510ba180380d02d070035914158150802440884070740208900c5c403035960182d00b02c1031300385c0e2946128550000d00448000307050b00c51041250b040304040020508144a5810b0010b2246020500f0001c0400400c0507400311b42424501030703400720004205504051100510b140480741c42540740c5030842d140a0366500c1c0d002c1000701003011a00016031603921424160000c0c04840c0309903800c2085a0740d540d40a03100078041c02100f50007402000079201e000b400540241c42581004610554409080400035000458966014010711800703019602441c4101d500c00c9210300300c09612907050b2803c0c140340007010381141b40140c2c0900810b011550300014040035941e80085810145041c0048550070007449500c650164507407094041341e070708205d60180070700001c0c1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 413740314 1250 413739064 413739071
    0x30708030906071826070b1912060f0b0306010315080f070e09120c030f0a0c06291203070203060c090306070201050c040b0904020909150312091302091206090709 71
    0x100e080000410107038032030f80401903140c414141c00350500041c03c001600c21041070303414187d134503038803401c803075201030303c440e0a078030070115004007054001c1e107803d10040000c00d040206a080c10740080c100403090040891205006c80000c140360701c241c0044080c02c1711a900c02180ca90340301451039035a501408020705038041c800300824141d5900c0c0806104001c0e481c000c140c1459030040180d907580c0712154004490004020f07549218405c00000c003035150341a541c024801001d820b001045610410308120f081d02e6103c560039161008005041c444202200d5240e056812980c2c01842c620802400030f4142c0102020030040c3e00c140d00281c40620741c00c0d01600c0c210740d14504100d0072120300300c07461321045200380b0060260115a0002d407541d0032029000510f00f1318601e000035400306048030490b0402ca4135540c1090107040910020031004041c03048641085d02020000c1c1c4505800381d03650182d00d9000c160041c0130743d6500b8031036801c041c0c010281d40140c24200c90140d00ca400e2400341c0440c2e03904 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 413741564 1250 413740314 413740337
    0x80d110405041833060608101d060f040b0d06020a030b030a0515060406030506280b01080a05151509011b050a021e270105040216060902010203070803090607 69
    0x80b08a01c01100c103611001d54090103205002a58003907644c150301e08418203104c855207030141c01911515020300300359241c0f5a214a010b40082c50100d0264102d00c0c110703855031182c003410009181c000d642005007145d015900352800b5001c10300900c86d0b69080e0303030300ca004d5880640a1100340c0d0300a0200b46050b035810310184610303030141a81c419100c80010300320307406401ca0070b24001c041c0c80c6490708036500420120380c1a80c0d94481c00c3c50302d002a281c0d41540b564290b126044202d20006803140500f00410032300115404000180031404010407061202e074035207000600b207441d410003100040400600109824a00ea00d0880c40358200300019404200310b0f6201c2481c103c0116201c0c10510342c07100040030912070550034400910030502403682038145141c0345241c25500c603450800c0c0490400308000490002c042c00500504042c0d0025024a1041000e0391030400d084001035a1240c200c000401d16104a01c0100d20354032030300c800a0310601001c81070094950012503500d010303110550f03c030040b640 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 413742814 1250 413741564 413741591
    0x21815030f01120611070308090c0a060e010c020a0332010603080d0c0210111c0203070207050d0821060f040b03061611070303030501030b15010504050d080d11040504 73
    0x441a1080c8845102260040028140e00100108600d200c0d110108072200d0f180c0c5c50024503008500100e000c9500c1c0400c002803100100a5200c003030b50201c5040c409507240041c081c110922800e045410424520040c0c803d54942c92a600c0c011517000544101103054003c4045c18000b81881c101c840000f100010b6801d140140115000c2d40d0b00002c00c0d601c1d08170b00e00481002015508902c0301580221f40340c41c014a800c4c0e10480070300e561200c02c503070760781c1c84540d2124040c450f18410a040c100d1040c400d01015590000e44e074800c1c1d40c1c0c02c1c1c0342107800d6652814107030541d00402404500301082001404000d040b540081805080241d600c440100340c12020001500c0c400d03a141c2c4d816501c00340000d009201207100b0060400c080e4142011071150300f903c0503081051681050b00413a4542d4010401c000c007182501c3d600c908030001040c0100e0800380020000d1040c0e20410b8441c103d20703800d100501080c90211010218401070410111000c002c2e20500368000c5e216452240b03103030411030268034 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 413744064 1250 413742814 413742817
    0x21030b132307050301150305040506070825120f0516050f1608120f010f030b180604060b010f02010b01050304021507081c0b0f01020a0b0a0b04021815 66
    0x94000e1140020034110000c200003814100c1280d0507a581034402101d002092500480c024503099840316600d41c10b1150743c0104180d030700c0030380003010314200030000402d00214403950402030300d1800c1c0700b031602c5160203800054800c150b40e00201c050549054040c0740c00c042c030207408045450081c001801025600310403540101d420131001364013210802003051240004240c2e14541100260505001c000e50940311945090203e44100000519181184582c042d040e40800254032031413240d810301249100160309440020b002250141c08a480361038480d95040344e204207441103c00c4c514090400c1406000c01020740340c040345001c03840b101c942d803040c042c400318001c068640034919240c950a111003200e030041d071004100401c0c041e0f200040d0440e8000d00d614519035440d00540c3c0104c203070650495002040651098141110719510799802040070710055804c10f004000340e595201c1d40c84003030041c1c0c03520103030301600c00144010614542200e20740e10f04015140071413942c07030300310b8890401e = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 413745314 1250 413744064 413744081
    0x100507050a030507020f0102040306050103020a140114070f1a06040c0504120f05010608030417060f01050d080d090c0801090c0e0c0912010b0a0f030b0a0c050d180f2103 74
    0x204100410301d00a4040c0e0841c13070b00b100c00c1d48102c030300c44003400310080d0072600301e90021900d280c1c4a0004005610b0700d08501c0d8050101040c00425601824001030117100305020300305000e04002c54135005000020303594041c15500600741500400d09401c000050500484072144200e02d032070b500740da866100f413094070142c1e010b103108455154025210482c0c005401001101c0c150340b52000420f2a98040c40600001c010300d00c0c0090002100445203405d0690041c20003d4011150004103c00d80c0d402c802030f00309907007207100250707506400100100604807000c40079000010504e0001401503055100b03d203d1030050880e4050107840310703901e90040c03006645007409031400b800307035028a20300908011001401a030000980401d11408184214259401000c1140c1d108104005100b0603a90541c0c2c0280d40d46410803510040e244045e010b40185401c000c00d032590340002007402100d0380510f0142c0c64120001181c0ca03440c0c2d01e40405c0c40000030000036940c1c8131031052840554003d0055181 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 413746564 1250 413745314 413745317
    0x10c212a03020d120e030c0604200904060218183403050903042c07021906020a09080a060515030303040b071d040f1415061c0908030117100507 63
    0x20364681c030683c1100c02034600c90074110039503a10444071166540c104010007061007200060462031900e4208410010b2007181255840c0d0039403950011665201103c456120341d01080068959040c0321003142101c5150707044680101c0d40c0e19107e402901440d103064031030070000208000260011004010703a000302d150031040c030000b012003100b06038081d400c0103a006070450110380c01d29980782081e25544103c0c5031607590801c0c10303a100d031034080900001c09a008025000501500c2908040c1084800e900314016089940c0800d00301d0f0294414000f450040c003410b81150500b20040c184480103100544000d440344000c41881c640c141008016244520340152019115035115401501d040c0c43c0e400b03800d040c00540c0c1180070090798075440b41d505107241c003034400542128140404000307090094108480c00204803004402ca50b00d60302201c00c1806080000c405c01c0c296445400c010b4401c00f81c0092030420b0100c00415100080c502e60200045444d0484030f04603252001d01040f14415600c030f90 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 413747814 1250 413746564 413746573
    0xe12010c0203030c0c0a020a18050a1109121006060504080f0a052512061a030118020607050a02090420190e040c0b0a030c0e030c010e010c212a0302 65
    0x103c1000c00013014000100a4000f550f00182c101d41c005a40424150070800400d48642000c1c070200040c1d10405d540310090b482e00f08040340d2a01e041d0b21075130141d0428503125560501d80c2c4a0b011000b0310000c5120902250244595a2500d074041c206030454040c102e801e200b816440812841c001501d80395044c4c2007409031000a42860701c940c40141c810a40402d10103541030002845482120054000c40c0039100001c1c000c45a2400e0040714028030074034034446e038180381e9201e8245a0500301145181d5049407007950311041491f28500340589180003950120394181003005001b41d51072080f0500e08060320b8a003010610808022201015403111400c070100c0640078010b0040800350b9a0f0018016001c0342c410650703c058410140c0c1c040390020000035180e1003000001500300407a600d1000045003d040c4907040e010008060b100f101c1c0080b4100046001071800344108404180b60622811041c40c81e11098404080e0a2880310a0310b224003441100180c1c004151000f05451555030507805003 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 413749064 1250 413747814 413747821
    0xb040b01091a1303030e1804080901120b0405010303090503060a0903050702060c0114070f090f082e020f031e09060610050c0a06050612030f16030c060203070e12010c020303 76
    0x203440022056006000449003009070b680c50084aa035100f0045101e80d032910350218144082c00111124001060036600c0708a0904c800102e0603000d580104000b0310b81100c4136460b494110010b0182d02c201e29801518100012041c0750380701c0091801e07200c040c1c04840d05521580706410469002c0c00e4060005602440f041005107045402040b4124640c0e001055a59100401e55905041610312038042800654108005608149044024511041d142d0101c603d04440e0740e0302c0b071a02c14110300005001506030b1511248a00d400340310002118400c5403244240c0a8041c000c0d0b0017520002003100c10640091014241c5403000d80c8a00380160180a960311950240964100056120014098103010040d900c0004114450f2801e001d04404246424810f040c00005010340d00c0c88506600204807160b41c10300e00300d048400340e000501903849010094102180c12030381a41340101001e00001c20301802a40c0f001d20800c09850866080b1200c0981d20322042c00c0352109502c00025030000d0000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 413750314 1250 413749064 413749079
    0x606050315150d1e060605040819020301061d010303020c060304200f0d050102031801270503040b0c100b010513030f15090b0a0f090b06120a0b01180b040b0109 70
    0x142d201030882c410716801c0241481000742543e114580c110352414202c80804003200003802040300412460030024a014144015182c9501c41c0c3c170145207801d62520510011501c09511580c01070100c1d100d511a011440f45520341080c40a210030341c0148110031880f025481d005007180d0155030f0288000800344914062015544101891264081c02c02181c0141545504801d2152544541d000690300c0ca0813002c0081242c21085040c074951703140a121460407000400c4030300032101c62078109030501c2c495240c12851480f4540004003c2c0101040398404000c001500b01c54003075002809010500d120401100e060280c4610b201920300c841c1010404100481d9107925113500a0140503480452400c89600f51114880304031a0382c81c9210810403003051502c01d00c4041c0e0803810041c040c00070aa00c3d000b1007150702034455442815500455a10500d04000e90382145612002e040000d681d504100c40c40a0a000002010305090880d2400c151415208508422605071104101281001c0700b = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 413751564 1250 413750314 413750329
    0x30915070e010809010b040509030403021e0607140f0312040605090f0d0e010203040504060611150609040201030507030b180702120301150302070201020a0b091b1228140a03030606050315 82
    0x30341030255030b25880c46d007440e19940245480b54850900075aa40c40c60b5206000d045010b80c510350480f002c104414028903591501190607090300b0000225000300c0450340035041482e503201c142050301c800130303079495142070000c0443c1c803403401410704200507501c0c641e40030b4803a9814444c110322500080c5030090044d00645040199101c10310459046c46e8032a00400d04481440c1c103d44081190303400132502440082103640300c500301c40300040c841410f00e02c1c04180710910180c0000c2c141070321a40080e6129200b680301003540880102200c50010310707a05400e400c1c55043d1010401401600712003580c211580c03044904850034110041c90781c10038041c0c218025006030304101c0c11402896040c0f004076010000d100d016040180161181502d241c180155040c00c0c0544240600710914204000440108050080d05074098105030401c9840d121100e4a034074080c0700804e424240f58450b0b0420000241051825210362401c00c1400c2d00c4280a45003800101d1342a500c0204c5511000301c0c0d82040c00b03 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 413752814 1250 413751564 413751571
    0x1205130210030f0b0a030c0e011e0603330302030601060f1d120604060f0f0b060a030c0e060a0201020409140f04080921101a010c17040b0708030915070e0108 69
    0x10004000004c04d00042c1c0d810000c0d4411341d41100410800e20441c6684d00d105401040000b00c800e18600d10b00012050b80d06440c8070701c4080c075945041c40c400d0000306002c40003e40e000750700d04609100313081d440d07800100183d0205a00904c918000410114015041450644019110030760408000c00103007010507016140507400c07010b598041c40964504003c071034000c13407090b400800c89099001c28402180c640ba0301e00a4850308044020340c0c0350b142c031001c5454488951801140e03000b09140e06a805070702c01010384d07802079000039141a00c3c40d81336010b402921071195091120300c1292800520054040e03d04410841001001c14002603041d402030008000190817840805400341c070984540b080800c0d510345541140703441400c1c802d924403940c0f050096141036140800b040e100000e15140225400914440b80e8041c01401410004152401400940c1882c1d5071100326150510700c58106985c543e50a02c40d140c80b11a05000261440d80703c1d29003a078034082c804a246004454525028 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 413754064 1250 413752814 413752841
    0x50a17010207081c050601020c01050a030c140d0e1b150a02010b0613050906031c0c02010e0d050a0c0830130b0406020d02030c0309060a1e120513021003 67
    0x700328040c000f80d20400501214180150700c48040d108001c8040183c440041c4035034115001120201407607a00207041c0c440364004c038580003a4001c00c119003a142913940149030100d009021461b024900314a0300070001360507032201a81c0c0b40010784140000d10511481d0842e40c440c1052500414401c11000a400541460701c0046400850180414960b074031000441d807000301400d400f0700c0107007081d04885800c204250000e0000e030303044980070400d840c0e00442c5d40d02000109440c020940e803141002c400070010040030f6100c0c440c12880c01c1d60742c1310480030085440e10f40421002401c003030b02040c0a405982c011808007440030f218080d02841441000804850720414030913001ea1821f41048070001c1c0c1060001140e4441c01c00401a160180f04410b6804550041119184010001c0140e8960840540b01c46890300c16014007599040359110120f00d5450000301d186840b50f511801d410380d00140c00308104940d403114104e15050140c8502e010b5004103440045114541c0319520495128100 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 413755314 1250 413754064 413754067
    0x9020a0504150b04080105252003130806090d020715120609050405070302210a12090b030a020d0b010c0b0402090604020c0312060f01030b150703120c05120702010204050a170102 78
    0x102c0900743e80769049500540c240d82c0d506c1041219000c614880307954401d10120031001200d100c1031f00144000280207d04542c00c10281032030803081c00c10000d803811622003000034803190361288210356035408112820700051081c080b01c00c50a43c00411400f0948a0017944120b40c95012072090702d5454015000b480e11039604d040c001b404000354400c5a0199100d0009400032a1650040001416440307a00900100040ea510f054030040081c1c0e06020300d40c410070701001382c1d40002d0282e409181a40c04055489800020080760402c07039802821003500701c0c0c100f00056614580111955101c104c0f00174809820300d404140980340c0141c0007940188020300c003520384140d01200710300716000510340740b64501010050103c1d5180c0030015955101080c80c04100415032000020103400303e100609070240030001d6020140740c0b00b5081d240000300d65000501003001c80c148000c002c0c1d0300603070200b003264031424081041540706008903021500d0003415482002d040c82c80d2414640d0038040c020007503650 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 413756564 1250 413755314 413755319
    0x103030804080919060509030d050c15090102090603040302070f1a0405060d0608070602010614120307020d060605180f100608070315090903080906070201140f06010e0904141009020a050415 83
    0x414a1100091700707a658a080e02c80e0751000501d03240442083c6088140401031100c4184080002004090074060401e200341a0712880e400c20300900c105401550405400010001856000610b0608480051661090300d41d07940510400c8000030032103040310b032601004100300a24004000c0c103e0b418140784002740300c5503034100003858003041d0380c80000940d458800421220b102c040500800e14400d507050581c0c00805286142c580c1f04005000b8414100c0181c1401403290036408000544000741c40710100044052030401c029008882d60142804c1080026603035019a002c1c1c0d07012150300d82c9900c403450301c0d0b80341e054000d041b0890961408031290031001030040030b2406410382040c0207446402e000d003000c042d22814108010444415a07041040c0303440010019503519074071009001081780c00d900c0e00d100494015410702c40c40c0783c0c040d81c0c440902c818094101c0060401c052188103c42440e154584600706550311140080c0d4086007800d010442814550040f40c0100803901c450344410341c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 413757814 1250 413756564 413756599
    0x40f0f08090a14130204050a2c011202130b0d0305030714040b25030c060902040f0e0105180f1c030b0d030f030b0603060607110102010209040f02030610050301030308040809 76
    0x3102035103d100a8142c403c02d01e5410704000402048020b401c010075840d150800c80840d41506044c0300703001c2d081450003845503203020900c2160a03140c454071a0344a942d42d6450b0104006804400240d1241500240703600c515400c503c0341d10070688000e0103011800c1c5450320281d0305a00000c1950017030001c40c0582c200c000d02da180c014000340c01c2c0003030300780e8039040e001441000d49904558a41d100000c00a280700c046600100c0083d03040e51300141c0031071100c98502c00b0801802d0344004950107603081030300301d28042206406c4a84a5030081000f4044035032115030031540c40305500403a1080d03030481540482280680c0a6501e00c2004a0401207906104040410a41400c6002c15800200740c0c030f03510f01296030726000700d00c01c412040740e001e415801c0c00d10000f142c5100c0c0403001070201c44a101307540c01d603900079019101c0307002e8020400c0041030150851440a544126220352003a150001d00d080014025010742e410780e0b030155036503c0c41e580d6980c2c07004a20b82c1f00b2000254060000e17480314a849 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 413759064 1250 413757814 413757829
    0x402030c01270e090c091b0906040b04060c140309100c260406030606090b0a0e01030e0111041701052502070f09021206010903050c010c030504030213060617040f0f0809 74
    0x2400255002c20f0705140440c085420444045401ea200e1180c80c17060000150340c550000c00410b03420030000d581d5620700c00002c0c62034400c5610210b80118003050000f002500000d520490ba030040c0b01c00070502d0414420140c5a00c52501720b154420031f500c0f11a084944901002000644500303034102c0b00440c08028031444e00c000c11383c50540300e01b0005042c00060750500440b001081c0c1da0034001c04650402414400d98001c0101801c20003000d60300529040e03202e50080100780c2c03511402009100d0165409508560060140c84d00400c08450100a942c030144655403040b202d000c5a4414000d14070488a0f0390f80000c2e400c81f007184555100400e00540350601c00380140071035400184e075158401c52416001c10000c104034180155288100082000480c7c11303a5030400900c5c2060303d45019203401e072440d00880d00083d41285075420f00d42c980100d95071240d0191101034803618018401d00c1c0703040b682000200d80007462140e0f800c8060001801582200c240944030343c5070310382044001004908074 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 413760314 1250 413759064 413759069
    0x70608070c110d06050402130212130807120306080d020c030c09060312040b03040b090c0f10140c07080c030a03051210030506090a0b1f1818290402030c0127 69
    0x3130365072041400210310b020740c08160712400e07441e402e41c20500158054141064014038180e10100642c0905e4200300c1d02208842c00e00354001754030404001a080010010402030103001458071555003c440382c140006020040c80710010b004100303d4038000c0c2030000d004c902900041c6c0501c02c812441c0400e00d084d2000c0e1020701918031407182c4910f03040c00d017210bc02070080d2a40809401100f04c0e0701054841051035454090107413030965501e402d40600311b980380200c2e1a24000500045500c0c906d0f0072001c13845034120b812140450300701078800010507454003c03240d80200498410403418880410b420f22003540094841103c00d20307680c0d03035103580307051003002c85880c078aa8102d02184c42c10003080c0a87d194004010a01c2d00070640307681d8561600b9156507008403203113624200413483c1c0c128566000103030300c079000044200c00640103107071603150402c20096600040b0008030703042032006400807845201d0b6070002c5c01409100c488100540e5140180c0158a040718404252280c040c42d920070500d00 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 413761564 1250 413760314 413760323
    0x450303020310091406010e0111070303110d0203041217210f0c180405091c0f0f0e06120403090b18120a02090105011b05010903050a020609070608070c110d 68
    0x80d81c2c074224400300c51840c6242c2101c6000391601c1c0c10a01090f02000003564448000e0030304600326012000162041d00d00c0e108103072418414010003208056008008245150141007226a0b02032403610990b00c1317019038001c0102040b003d103060004145443d0104801e00360002d02545841c0c004041d021420302200303691061114030000b4000b001c199140081d90041c1c03140314031070811100c001000c03003a142d4214030a110b9602c0d14040740c50000140440548480c40031b94034000c0d646007043c06807440703a1101103000810200c0748107409a0340204008041000014038aa01d84000c24400c901c404202500503401c0106414020440d2040308000381140700342104c41d0141d84203103c00300004110b000104003401d41111100c10b006846203e4210705450090a042103580a016480740380e40c0404003014006609020340b000502d908100149481910765082e07400b10790344c0c00705866484c0980e00c01c00c0c002908000001d2143c03841461644105407003105002d50f0724034800700150b0000325442c6e00f40c8 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 413762814 1250 413761564 413761567
    0x106030203250206010611010b04020d29030705060a1b0804090f3b15010e09030a08040308180a110103061205030a0c02010c081201061245030302 64
    0x1030002041400b03400030340c410b05802d150000d4020004d44604040c46241e09010320021070103a80c81d02900140c000e030001800864407032030b50061200140507645088213507119441490360324444084048c1c40d220074082d0043c0081c078a07080c20300c0440c0d40300c00304401c204903081500410078034410b81d44441e0700b03000340b14458581d03003400030b480d0840388021844002d0520701911302500610f00303809034001640007004908040901151301c1c28000081e00c10040038082e00903141e1418446008881c1a989a1850420180c1d103681410340c1c2d034860701045401080d1820006000a4400d146030380d07201c00c01803408200700d00110380151a00482c90021107070f15010018034070044d641442240020b10b20f0704900d107101e99041d140c2c60340781d20454048008100c2d1081c0d030a4107590060b24112003266109042c25990b0383d604500182c4200280070301400500a0034030785540c1d0b802c90007000e514842d403208070300003030100002107100b2445481d01e40c5090201c1c91040c84a21001030300700d8142034040e4a000d0f = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 413764064 1250 413762814 413762821
    0xe06070906140421020102070b0f03040c0905010605091216030807050115150507050106050904060203060f060c340f0816060e04020304060905030412050610080d0503040f0b0106030203 81
    0x250401003076800706542d604083c4020019115016220300013490480b000301c1c1e451119000403030a052054100c80d8040c40001080fa521401c420000d610850240d10503824880c0c581040805480080c403900000900030301403008a0720380107100e051420700d244200c801c2c540d100764912071224103540c400d40f4140000725042e81130110a004511461007100e040d028800e041c0240d800070f00c00010725040030000003242010410809500020142900a011841c645041e18151002e0341c41100d00c20301034540304140d121903013010800c1d50801c0c211440604a00c80440720300c10340d03007544c4180b4201150081441d40108030220f07a0f243d0080e258058140e0380700303403c042900b46800c181c012150301503280107400300a480e90003070110408840880b030140e52500d035820008050000810080c00601002400144580001c0381910000c0d00c500281c43d440d94400001008003004c7e80720350619a0400d990003110103100744000e5502500c24104d40540703ca03642c07120403400c40c09802400120b0f6000052 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 413765314 1250 413764064 413764067
    0x80d02011401030c1a041a091c0206041502011b0e0312030708040803060609030f072102090601084f050d0806010e090c03010303030501080d140d0e06070906 69
    0x80c06403080c0c03001d1544100c0d51465403007010703d1002e445044c5a50410098540d480076400049600030480c00707440782040322084900b41e400e60301541500c1d105030f003203001501500407030601003000190000c1c101400c0078030744000100c1408644811030119541d481c5080300814005d104050f20340c0c0c2540d82c018444500805241c507001241060b411000810720400040c55800340721158401c0d8070949594894a40c078002c00c01d14050f07480e0040e4140518038007140c5050380003d9072400c882008a21403494a002e4003660110008982c0c00b9400c80000400660030f07500a680c4142c100c940c55401044058020a0b6400070352110b10075054030b42c005800707190000c20741c0e0743c184540c140300040c00302c2038a8090341c5880d40c40489080103000d0200c80b400107a6140c2c003d910300c50800c840549840c4041ca8119480c03a034a6000340803c81c0440c2c500740c0041001000002e60710680341d81c54655085084c0782581080c6c0c20b4200c05c100c8d008480d2070b40c480c9911003509029150141003e9100e0840031410b1540 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 413766564 1250 413765314 413765321
    0x80901020c030a060f141302040c17040b07120b010203040b2a030c010501151b260c0d051c090f0602040b0904050f06010c1128061103030f01090209040b040501080d0201 74
    0x407106e44034113107501803000d00b03c02d940c1c190364284d504540000f080b041120381924290098240c83c40440d00300f07400c00042c840031004680c4280700940d07855000744110b280120455071080f2580780103034014030043c0700782ca03800002882440c3c62032007807071421018001e000c3e89142c44440600c845803c0808c5865655509004903401362059201c0c600a000011400408100f03c038140d101007000240c548000344030044c0b240344aa080c4c5208061505a0380d0011400d5961015050031076030302c100003420f9079040c882c42c1601d0001d4503130f12070719100e001c4140c1894081c1151a00c140e5201141050100009019200078001803100c5070045403107034201c00802c421140014a003110501405c2c003000038030380c1d1003200780d040d0030b0388a045445030342c03802c4010071100480c06000401a4801030840780303d104c1248124000c464041e6207400e070b03103418414896107a0205641620040a2131001030012107000c1c3c0180284101c060800220740c00440009010ba9030281c2c0000003e81014000d003240550a01 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 413767814 1250 413766564 413766581
    0x301020a0f022404060203060d0b070e2b121b0b06040b04090507170a0f0b010302190803120901090204090b070e030c0603070f02191b080c010c080901020c030a060f 72
    0x103c1c99551030405040b403440e901c00060000f0421607000000501590b10203e14a4040e6008400f55017107280c4002c0180020080d03120320342c031076a020300049405202201d00c0485d150343e031500d1811a0001341c0d4400e6685043c500080044c008a008441c1542c0c1c5140340c90404035005800e080c0c1d880c02c2182c18802181c40520103107008500304060f0074081341c0c00052000840e2034028000c0c1284241c0200309084c04000c0d08018035081c40d01c082d02050000c181001410789000300d40104000340e140c8511441c4000340e01c1408800d81082c80242202d0a40900c00c0307a002d0781d18400802c980d2260340c00181215608201243c2031244c1c03000f03214086520400d42e640e010429002000c1c070a00c040e0000b115400010040300030040443c0740290f80520a0103807220394104102100c480c0c40c3c031032600c0d003110001034214100c9800401400a086000024072407a45041a191061038041c00e40341d1414662003441c00d0b60640c42940111150f41d1400c00c0303002c41190113400c001a400060144080640d280c59 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 413769064 1250 413767814 413767843
    0x503060111104a07030b0f0f09030a0c02010e270f070e0d0605040206070f03020309010311090d2a090501170d0f030f090b071106360c0301020a0f02 65
    0x408000036034007483c201540798102041d03060082e082c410700c2042c0c5000e055400040c585258141445210900800300714082c02d04200040000c2e9102000d40d50340e401207565210009010500000c05035024100351641100054a40c08002b0700b155080740400100c03040c5004058207002c100880d41c440c4080154008801c1d281c1030071a10510000901070301250704015041031381d0b40d80031400f15a10a402c0381c1d030300c40d448460340c6480182402d01940740c1e0800084103001c00d00340484c0c1c0d88040c1c4c0c3c50007144c221000062901501d1155926030340c0343c000181c3c0c2d008182203021000302001c0d03403d154001008241091011400358142800d601d8403401200041e0000c0d0700a24007c4001e03030b0400f24000aa610620300000d04034860200d20010b0400c40c04040c1c58140341d2400e001f00c0d03e51008040811240e280200c80b0551a203002200c8000d21101c1d4004d130b4041c246820220002542c80c41c00203810310170302241d01c0500440d000a003240e008414072004114003c08441980c0e03014003e072110704032503 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 413770314 1250 413769064 413769131
    0xc0501020c03100e0106050409050610050d0b07030b15130612023c0d0c0320030c130e090304031203050c03132906031005010510050306011110 63
    0x118070101e0381c1e07440300b40660f841d01c2d03441395442003804209500c650001c180080c002d00440041d401d100da10307000c1c1036400a1413400050404503075800d010f14520803071903100910660300e54035010704900419440c3da0841c0d2144004030100c400a6905018001c002d1188400101c018074152004c3c8c81c1503802c8507040c2084e030051010b060101511f0300c0101d44580140825160850120380e20610303204c2031241d420080380701042058004240d41d20104c0c80209030303102085400c4210007228000c1600000c0000d020380708000241f10480c207800500002030302e0450500106c1e45070100c09440d82c1085600b03000a03480800c04205208400040c9024150b103420200400d040c00034154a0030320000f000f41000e11a0403450904000f070001c24250030b00200506400b04611040350309c100038100f603801c18424810a080302d440d51f19540305007812602c008050683c220107002003078920307800003001f082c14000c20b4284691a00014840321048144124001600c01c0e03448030103440c03100c1e0401d5900c066404 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 413771564 1250 413770314 413770333
    0x607150f0e0f0d0e0a12060204090507020a0c26011d060f0709030828020a0c0b0a0806190503070303020604050d0f0c060f1b0306030c05060f0414030a0f030203070c050102 75
    0x340403915480d0b036452882d001e28180c0510000c00e9a0545c40e920254003000c10903d0f800c14403009134041e1003507032080d2401b441241c55400d0100e0303480b50001c03800f0301700780e9001c481000890054503250312540ca0014103600c1e0318810005c094215440440350702c8400c1c0d42c0c9400341c80c0340b100a1000a501c035000c3c0c2182c0209042201008010a0b4140030007001f5a10005076841c926241468941c200340505070820f00201034020000d48801503c0d10441701040034003404218a240030054030409a038990300c01546680751410490320308001240c1c051105542c0b072010a01780c50500c0214040c500030780062400b4242403400e1032800804600c4101000307ea8074800290540c085900c64006402c210086010820081500c0013816000a1043c42406200b1001c1d10070360140c200504803030082d010201000da41c5d0050000c14032401d00260313a07212040005000c641000200120400d4018084401c110b42d0b44d680c00c0c3c4051500201540540e001003501c00c01c02100e5031045014000a05c098814100c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 413772814 1250 413771564 413771593
    0x9030c01051c0207050312040609030807090803090d1109010609030c080303010308030402090405010f1a091005031218090a1407020c061914030717010e0c090105090607150f0e 77
    0x2d07035401c504001c0b0380008054007408020810781702039101c02001303815141807038913040780108000780c012400b003a40c210000d04c595001d100c1e0f000c1100d0b00407002d10700e0200c04004100c076000700ca0404445400d41c0c2c03285145c941c1c0f9280e016a01038810ba45540072a6030a41c2050b646081700c83e400b200003503004100610018619405880d045a415994440d15456a20f40140540320009803620795034581403c5060002c2c4083c0007518001007a91004440d071111100c1301851055400b0b0a6050352200b4035001c01900781300003e1205a02c00d2815406038118000001c40248055807541d40c500c2e191500d480f1a246484417058015600e8001086280c0078000414002d0151100000520840d1500349940b10b001701c1700e0441000420340781d1541c03490700c1d110103031000749201000d6604081010000c104040c1c02c008442c042c41181d4041418600da800c0116260340c407080203a504910f080c1328030000141c08880916642e2455080820a00c90f0000d204e0100e500e54804910141d00605030001c840c0d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 413774064 1250 413772814 413772847
    0x10f05010f0f0c0f110f04050603060c1309150315020c0a030e030708070801050907060c0302150403300c020304030b041b03021305060301061203081602010b0a0b09030c0105 76
    0x280c241428410420401003d5506054035400548040d00030704940013040744045007000e01110403154010005071200c1408220b5038220744003500343d844034010401c46401071018044401440402c00780380c40d102c00340c142c2030f1040407034819414101800140100090781d40d0411583c1c4208100310700f002c42e000b601a94408070210060280b040021080205131808d0040c00c02400c090412280d01917540c0556600810b01110b00c0503a038015000c011520521810400b040c19406a0080807281e0000d89401004e8402410031000d0095105800c1d80c0d84811a4140803050340b0391401300080c411070340c11841940d10451038642150002c0101f40001404580d0302d80e0030a410001141020b840c514880441d5125500007a6001c4600214000503014070b401c0140300d038200b03400a200b80d680e00c2c005001c0345024414000c001c60058000642c119000400072800c07400d05100103c0c0707104e07414000c0f0748444c0103a04090843c5000103100a4181020000c000b203101c000c0c07822038a010b04901440420 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 413775314 1250 413774064 413774087
    0x3040302100507090b120a0e0d0504090203060103020d05090f0d1107090e10110d1a01050a2d02010e011d0a0210021005010e0702010c080f2208040b12010f0501 70
    0x101c1c1d541e4400700e001c061089500802515000c0e07031081da104603480c0501d031000401c403072081180d07051903900240201c0101c0c0029060030035444d00c5080034101403880d40a50401401c040c10141c0c20b20500264103094000c0a018494000c00341c504220821103440c2403c03138504584c000c0c40a0445030b1341c0300c8000081c1d108101c034003448c0300041900c1c818540d2810025441940300c0f00d2400c01c0884010107000c9001090656841078042000c200c1900c154404040764252301801b040341480281c055501072452001130441c5480d0030100e01e18205078040c0c6c05075001e038040005030341da1895003116202c24404c8a00d945200106840045128003c099854210fa14000c0c020080f4124203840349008200034940b0440e0850705001e290b0316107883e05110801180d00000540c207000c00c5040f502c0c0141c070300500629003a44c0003074003661341207402d1030000007403500070082c00d0030ba2006201003021a4050805060300d22a40d640e41c900a040301280a801a0002c02155403d920100040c0e80c100303004016 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 413776564 1250 413775314 413775343
    0x7060507122013090516110106120204090221010209040e0106030b040f17031317070b01030209060f06120109050106080f070e040b1002010902150c070b0c0f0304120c050603040302 79
    0x1a224041c100310500300f90613601400b03501c0c0c28401804024845c01c0469030b882c00040d91541c1714a0703600d44442d0b00760781841c0300388903440c001e00c00e2840c054106600b0001040c0c0c0060300320142459070f00d610b80d4550f40c11280752030490354003040407480703864030f4000c4856107034080b03000303012542c00e58860001e441d10142c80200303445803070501401004007032680b012244100100050722864a0380c0321017090398016208442080e079000c4001070721a462416148160b400c4203003813800d03070308690030b00014000241916601c1041c0310100e0710542e40b0380703004007402590007003072100e1545002c68810543c0c0041e0042014401c1440070021085c450062007988041c42e86031600b48090448041001803007116034442d00540d007040c0c0044050f40541002c1711051090b510f910b202c2a0071180041580030716402c0c00e02503000450700f0070002c812507002e02041c9110400b551054801840414595845603210344540320000520034180030200196800a15060710301c9460b52600341d400940b04d0300b06141155 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 413777814 1250 413776564 413776567
    0x308040b0c070e0103050d030f060e06011416060905071a0a0c0204180b0f0f090309060705010605040608060106110307020a050d050703170c1b0d1511070605071220 72
    0x1c2401c404000610042610b180348000300c2d45c41c0d04100fa25182e0f66419800442d04003000c0a2903d0b80c07502c2010203c55010111548581340c0d600110380482c40007004a400c200c05200042c1080d1f41000c100c1041c030300c01e00700081c1c42c84151030a58101410307503020103440d0501c1c0204203400c08009043b42e1548040d0324003281c06000520009000f001c408041207a107440040b228001c1003040c0400c1070044001108021181d03403460b600b40c403894021a2444400c0e001406042c400342400006891241d01c40c1c000810030540390170100c0c080b100964000f0707006a00400042291982008c02c1052071507001010398500125038010410711034a81c850a40a2036115041c0c1c001d0200521046c1c010315400101020164a00180012a500300203150301042c06941c0f00000e1a152601d9004684c44016017811079070320007901ea10400f902c000c590300140d15100c29900c06030810110080500d180b14000004441c00e004c18010880c100100820040b40d140080301c44c43c04030f06004840d400e560607113805 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 413779064 1250 413777814 413777827
    0x90503011505150f040806040605090c030c060f070c080a111e30120919030203070902030c07050a030c061118040507050903070906051f090e1e07030f0e070308040b 72
    0x40300c01e84246e6011520718040c81c0c06100030801c40760070281c014280b0400b1105003100c00420151039015004a00d60311150800040c1c103124103400190012900941c1040c01c84d0390b40f03440480c00c0c030020b4602101e16414010481140b813500d601034403214000440c402e2802500070020404060340c0000d504209100100f81d0243c229107800700c030008200000036030b9440080f10000981c140c0100603802d100c1c05511402082d1040181200012650014000c2140030f20b000d811900030b6001800040741c00c0d100300a0b000105004100d4161128440d42e128114201e1a081400440d0680d40303108504100400000c0b101c0300340d0f1440f032401e6410840c0c00081d2611100b07420786032880380781c0c04e1981601400301d00007034504e00f035800f20085276800da402480d000b00800c240051210602c2583d0041844144180200302141f450144c0c00201480c0103408218040b4030124000800c950710400a40c0f90101418103040078000d084040481c1c3c03001301401404e50340d5440c143d00030fa00406412203130201c2e40 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 413780314 1250 413779064 413779087
    0x903030903250516050f04020a200109020a0e070f0c210e1504030c140d12140c010c0f03180b0624120c041215060801020a09050301150515 61
    0x989541c2c90388002200c5000310100442c0e40301040c02e11496101d0120071b05a600750742001c1c021030300f034200103660324542d03044101e44990004003190941c0407699643c030104801a00c3d0005100042c00d40c4075074518040c07030503c03001030481070040c030440100b1200900c904002540e0320280d49004160841c0c803188040e074110111250714a4850340b0ba4098140043c030207081445000030130980e4000c00120322525100c0c0c07443c0c1c509200f8900340c9a007005d0350310066004601102d109a10080061a103052070110a10b202c0005412070001d0b4a00c0b40d556403d8030100d10341007804081c40b1007460509000c59580781c0e8050300280d41f58040907200070080e800096003a42c612041c03a6600c1c005800b00e1144180d82c1c540054190844240b440c0600445400315451301d9258054800300c840d008000c5000c10380300d80d1001421801001d109034083c0e103401c4007240054003030014003010a5203941d100c504070300c0c00e01098207640f081c8180c002c41c0700c5400002e002c544c440c1120550189480401325a503401c11246 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 413781564 1250 413780314 413780377
    0x503070e0a0228050d0b0301050601090509040c150e03062a090301020c031303150e0303060114070213150b040f09051b0705210307081906030507031203050903030903 73
    0x1142d6481a603090f0b40001c200c0e00312010b400144071207032040040107036400c00d06080720000e4605a0203da83c81104000324a170174441c007980148141740740c0400580c1c403a6031414484010b146400401c244071269100c070300b41084010b44c001440d10b0380c20041e04605c8125000702460303804007450130000040d25469510250104c40900441c1002c50b50390308690200c1c49044441390002b21800f1010101d0480c0c100540d0042c010580b0045e005185140c54840c010345021040c5141c00e400e03140280f11880150717582d03200009071750441c071502281101401340084080d070305c1038000f0307034445109010501110114400d00b100f501d10f00f09000070b0035200e10010b03c600024411181d1280c9100244040c00c020b80414252945090120300b02c01782180d598000c03a450208560800000304080001032851503520200c101019114500103842c0d030f06c0351901800d00788650006c1c1c80107480c8034140c452403545803040320b40c00031024003e1821803c10540b102d0700c0340f080300e00450340410202c0409030742080c10007 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 413782814 1250 413781564 413781607
    0x601030608070b19080910020d2405040501050d08180a0305120409050a020f0d0504030e04060b0c0d0507030906080a0212130c0b04050d0b0405070b220503070e0a02 72
    0x20441d80c246940d001d0b220050380c0000042c1094101400303084c86514081e0840c0f0f030148080c10040c20255080c6864031009401c4030034820392160b11040321a0b030b030303240341d00b080303e80146805003000101e070401003844141c07441a880340707000e0744084040c50701040300340c02658907881c403401c5503120b43d4000c400001c210300d00c5900080c0c0a80200e403010780c0c1c4840c0c0000100100d4218040a100c81d941d5140008100d0040a00c800141301c02046942c809000c2640308592041c800e051648120406002142c2100d200c5c1c1c028500b0b02d24002040903901c2010450780e140b05010785003c5242441590340140740e111544101400e000d100d0022501800740758041d1104041d50b02c1c480501803408181e66100d050300608140c0350300740820400701c2c1c01d0020394200c13801d07600040e0102d01c0300542a502d0343d13524980100152118024182c0c042403182c00c806c01400300e08007402400001207106003030862032102030381c400b0788a580090380401281030106c410b2940121030110060715900c1c0944024216040c15 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 413784064 1250 413782814 413782829
    0x1b04030b090c1203030a0e0a170a030e100204180e0c0d0602070803070905090f16050a050f210906041101030b01030e0610090c0207081c050409090b1506030411060306010306 76
    0x3e01851480d03043c0000070311305c1030b209036401f803214007030201c4c2c000e44814140708003a09140790350940e040343c10303038040c014000020640b0f00040c813402451017640c02c0080e25025040c41c180c0004041004501c41e9115100001204208110a010254509030381d0050700c50000d01407440b42e0f2540041c00480d078159070788903402000007550f03840c1031a4020305901702805403600c03075004000400c1c4034800c4803c806105035404241d466100c540442c090705e2940098500d2402c0010410900040f1145540034017600d1003240c011504060381c2182ca02c20000c40201103088a611039020032001c0703500e194000c8007643c400c1c2030001c0c40d414103a004030050001501c00c078185d84585018041844544c000860440310008030810000000d414203d0325140302d481a54226131289504c600d00301d041407801c801e08210303030506074a050b58400c1c1c650309a8906030404d4607650020010084a04104000c803074030900c2c201c031071918515195580d41046181e9010b401d010724804000a12281d02a030702c0913000d456031 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 413785314 1250 413784064 413784079
    0xd110d08040602250306050c3705191808010f05070212070b06010c0821041205070f02101107091e062306040803040b0c070f0e0103030f050f030903121b04030b090c 72
    0x50019212694945070b602c0a4841e44c400c0c060f00050b4480c1c010f40307412602c1c481003190007a001e003008480ca0f440c1c2c004003341003c1c102c0b90001c0d071240244102803040240c2c02c1c011070700386401e00002e030400c005484210b81001c0304006901c005240c4a5010340c0c08002428004450002410084031600030a41010b411b0284206181082c1c207025100e144510300c9140440810b60300401d00301c5040c01054401020301c1845040c01005240002d80d500500c1424640b4001c45c000182c051864103603150b00c0781c104a580d0350380d602d10005200090080c2c03807100120a003c440e21344000720f2554000701c4141c48a0141074042452503554000860b8001d0a28400b184d846940703402c0d0003906580107001c0350034948115000003800701c2d00c0206840884007100b00b120483da20f1900d003580c1c4071196107000010030400304041ca5901a07030201841c0205540b07801151241408814055030400281c000407203002c000c0c410b000c800c01460110360642354401e61280158840c0210149020b00303844c90a40d00450 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 413786564 1250 413785314 413785357
    0xf0e07030b0414060a0603020924070605010f080c060a05041202030c030d0201060e0a150e090c0d03050316020c03120f0d02070311070f06020c0d110d08040602250306050c 75
    0x39054514001c0300c045031708103681c90740c40ea004d408922809014a8000c42c4510102c01d00050f1406240d04100011078000d181000f01d82e210703411900241c002e051070408822b000c1c000b1240401a00f000450123459240c0703003082c1c112010700030340030360701c500c00c1c80c01070b80c000321011900c0500000f02040c00180841e80c46445405010303019002c079020f01d419846500e03001401619280c000c14111004001405201da8246034080103a0b42c030052590f446407180119041040c0c88d8158035110701030203035940c0c030740340d003409001c1c10302001400b034444003190b202c01c1300b07040b2540c0d0225114000c0002552400e0782c0d103121002203030780740c001c07e59400b038150301c08203100040c103801816007018494004141d0b07a45585500a004500c2c02600503400140d02c590304c595042d091286040c07102a024108108014401400060070440036042c2114021008941000030300d4040100180c41000d03032040402d0222130600940581010b4070002d0032040d192004550000121411600b6030903a09a07a0031880c038 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 413787814 1250 413786564 413786591
    0x905030d14061207050d030c021903032105040302070e0712060b070203010c020303010b0d0213030210020a060c020a05060a02030406020405120a0b07050a051801020309121e070f0e07030b04 83
    0x62044603218007500c6018440400c03080d000c200e684c02d6410041094105440702c0c2ca0403900300c1120b10080741c12858880b04021841600d080d130600540c8295200d100d54030740500301202c0a001c0b8420001c659007000301f0b000003c2e40214100094a40c10008151550703603049082f070341107011003242c950451038103d0200e00103001d08020505e45000350000e10203000f4101040361307a844240710b4600c903d00148511007166207550000c142410b084074500308c405d500ea800003444140e0846010300568450130002c020400203018250740d0312002d0000e445644c181e910740c0c9440380340040010300396560000000301045001d41c1654080d12001d0200040030024800c1aa45d48242c054282c800d0f190b4040000e1741240720700c2c101c4845001030380d1054102218103240aa080c5c2d03840480b10705501090240003190b07220001c01940c601100f134001c00400c0351000d01a255079800c25035940007500000001d002c1044800c42c0c50342190711a5251040998500030120020004003000d00d41c8203042844000c007a2 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 413789064 1250 413787814 413787851
    0x3030d021605190309180f0e030d062c25020a0308090c060702040f11180a14030a03110f03030408030f060136051512010e0c0306040905030d 62
    0x5215204691080c11410542010f000c84000000d0005001035000d210b510044a0186038507005940b003c1003040341c01c504801a58500c0b0440052035001061101c0052401d01419000707015108a452200310301c0d85a4840c006841c4803149140d107490404a6010108480c2c201100c00207059200901003940300c0c001d4403401040c1040e8000703404800480d001e45070204135100d0007000201b2444c0b038600a0781c01c0c44050181440a90800d5544200700c030b286208020042046a00c40841d280076803e0310810890980c007540c000c0400d6010689070f80845460000b0700780105500741c10240c6c0118001c0034068a4070140725a242d0300b5010200500c402c200404025502409034901c00321059a1110011105c2400c4c0b1041e504402a100381d170907602c9460754000030081207a07084500c21094585008c00c0140c10f07403406601e140b0341c00207101018045036010381c0707000d41510755117500c0905041112030000d00004d010580308039500d500c00020040100301712a03200e07039540400c3c404486054021003d1 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 413790314 1250 413789064 413789107
    0x5160803010608010e151825030f1a030c0108040c030f1101080106020105060a03030503091207050a020307051909020d0612060906050112150b040b0604030807030f080f070c0203030d02 81
    0x804600c0800f06c1c110310752110140840c601d014129999900132828050702046014000e50010240c08803603400baa4040031000041459644012a1681400240500b1100c8079641c490b5141008441d4141301d035008100c010110fa400d18102d503440d243c90a09501d8018250300041142003101120020090103c840c1410200b090700c81254580e0391340003c0e801d881e0103d032010382c4041030381c10910000380034002a5410950b80005c440344800e0540c040415544210b2040e1083e03808100500e045242c10850354014100a489804c2c11003500715203140325007580d0003102115600459441a100c94540c81a0000c1c607d070740340c00300c0401203810f0000c000c007800002902c03810305100011402c1303140c03046103008413039104151003030401014029800600c0c070356080b00d500c00e851300900300f10343c2d80c0c603405800a180501c40711540c0d44514a0701502c007140c01d00c952000e214694040141783c0c00c003800000c2d80408c0c0c500300000d40147c58400203007180b09400c2201681403000c42c4001740800007400d032040 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 413791564 1250 413790314 413790329
    0x4180f0204050a2c07051e1207060f05161509060c020c030a080315030f0304090c0e1305041b0f05031005090303041b0e0a02090103150501020d0516080301060801 71
    0x80e64030788900c0201500d641e03002c92411050b500c2c4e10100d107032540b081812034003086003041d1290a0784550000b084540007803440034a0940c605464800762404c42690754490351218001c0038002e18018016140020f91180c0500f448030103e0000041000903140d4243c140d40300d561264840d240ca50700d02c000340a502c105680c2c2500e00b240c15492240001a0360045d000010002c00120200359035521a980c401042c4601a051a5083c1c0760991000c20400c43d00b50b2502000d1030712039091100b07001c02c4681100c4008100704d069041849030351900c4050501960020802295075621b03420569a410f15030347e00445015007580001640c25201404403054481c1107040d18400f0301c0d0f4403551003e4070400c1c0d4070780715590400c10104000030642c0303101d02c400c0c0c4003039000c81c00d40315541c51400c0c3c03210300103e45040019030005045107aa682c144100a402e0a996040e006801d08120000b50360312103081c00c03c414000c1c0056550f600c1103038513075a00449039000a40980c3c9684864000305946020701c02e110 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 413792814 1250 413791564 413791571
    0xb07030e0108010e010513090507030b0414150105010305040618050c1201060b0d18050109081803030304050d03021303170a02190f030e060c030a030506030613110d0204180f0204 78
    0x300390362084000c0c41c1200e07a400d6100c21181d0808003000444c16443c040d10040b0f903038800791100046e10034481000150b00843d20180985071500f00b285905035000001034040d04220139003180f42c41d42c20704484c1907036003c3c6000181a40d843c9090002080c03408804c20b40400400030000410400007611500d844058402e0030050100b00c0081d405d880c50783c02500402d0302c080c020100c0300425648001c0020f11400e5030404018000d444031821201012010b413540c5c03000054003140e0306001083c1e501c0d00003040d00258070314031b01034030750603243d4010403440000c05400003000c0d03140c1c0e203182501c01c0103076400c4082c5c5c010300703000007a810040f903212614813030141c0661400e101c09400230421144039990411100614044c40d95401c039401614441e2981e0300a00900c0b000d2042c0c030040008e04404032494900040c1e03070504000301490700e08000c0480825550284451001554050042d40704c40341c15200311999001c2031000402402c00414002c985060070b0f1742400a004800801d032050381e00994040 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 413794064 1250 413792814 413792837
    0x301090b1014011d0301021909091503080d1a030d021609020702030706120f0e0a0203070e0c0d092a0e07020a1101050310050918100207030e12160b0703 67
    0x801581555400341ca0101e02e00d42c4c181e50820409030305001d51140000e000520b0311208107030311020f42d02c0d0010310400040722540180088080c1e40708010013031040c040541d217510300d550fa402c07809218038030804600a4130b400422416036100004140d4040d4018183c0307075103482036235000356180c6407100c0048000055460000340c030040c910842c0c01740b40c1c000e0003500003203042c07a0040d00d41c40c0a040183c107081e984c0c1d0070700010b514068400c202e46920308030003600080005004041c900709a40c1c01c605841809601844a100703128402c230f83d00580e0011003c200700d0741508085243c420440c0415042e02c111202c0e400e9200c3c8990225005d4a450100203103064a8040c2c3c01c0366140980380c4024103454800740a08150344c043c2d030107150703c440020b40d03000300e01d9281e0011400f00380061707070641d103043c507003043c0c40c1011035091000714100c18201c80118200500380e2401410200c001d1910340c0607200090a104d281d940c03e11810355919403020260b80c045584c1c4040342215800944160300048201400 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 413795314 1250 413794064 413794079
    0x1050d1e090c0e04020d03110f0a030c0b06010815040c11030a0302030916062a0c081c05030c030604050601140316093602160807023303070c020301090b10 68
    0x384d008540180001034202c00a95054030405100c4620a0f00b51140162541003010204041e0b00003d12a40d58400d03414481d180145403814090691070620001100304132030039401510907084035504940100c0c1c0c070340600200390f54294003c01c0320001e81c000000c25000e0700e43c158008502402d104400c841000340000480881030000e03018040008601e4407409405003070b01415400d4542c000790340340805040c15614120b00e8100c551284140343c01a000001084103845aa40710030440c1d0b0605501d0340c070300054800c84074400145840e200d40d0340c80b0041040350344100f00081b0300325212403442c0e03540d04101c3c0440a42d10003032101c110010380d0044d004207240f2400a40c80c0001181c00300b010b801072050702c1840004410103483c01d0041c8bd400d100801007001c000000c80181400740d10159a80c00703141c0117000862040d814440e5810002c51040d03800c00b02c51490010481c410a00000d03241e0319103042c102c40c0001102e1010358151b003808004030a01c1420701d0810b000d9000c4610038540d0350b545400 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 413796564 1250 413795314 413795339
    0x30103080c120a0c080d11070302010e0d2d020a02090f0103060f0b010816020f120409112502130f0c030506010305010819020625060c05160201050d1e090c 68
    0x20309800154501c0050310008801d174000d40100722001d140481d465180f007040d0015500000e80680050307444128216603402d013400180340301c101918111582ea0048581144a10101100309498003042d4801a107103910074417021030079980c010324030b4041b41000440c00c58090000e00007625414a001ca40e04002d480e43e02c10b034003c142c41a1542203080e07070b802d07814110b0040c075810b404056002d00d19102c00d51074018070a0760030800d0414076164589007030140c03080071900544560806240104241c40e0740e01d5203c051150300020312110b10004401a01c04141d440200010120295080040110708840d65030048240b110855508000c1a9100401102511004e215001258002175081c01c0306081c2040b4241a450028210710320349500a02c40c595991104920a8600000890100f08003c024000c15000d01010318041d030034040c118514010b52000881c00906016002984e6500c64809130807d00c400d0f4121425138003040c0f100f02d0940042d0190010071a41e0341140c090104180c0040d04 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 413797814 1250 413796564 413796577
    0xa031107090b011b1502030c0a0318020916050c010c0306180b060a0f1b0f02030618060109020c0a060f0213090e03030a050c121302130203060904110411030103080c12 73
    0x1d483d803075941c1d03001d40b0035400c254a10400340d0709171408450361310b9014000e0006501487c3e0b4592810340e07408112000034103c89602c1d48840211000341c07082d80c050b9560400c0c95070000c082c1c0c2c401e440005210002607034184900d20070407a40d9400c0ca500000c400c0d415901c0201141d200381019010720121545a0048a00b911400c03030f03000c0400d101d001c5076184282c505c0c400b02c80a0781821103000307000c51590990034502c3d1004681d28031050080c1011801d0900c21560441c0d004442a4458140c804c241c9840701d00c14000c441c8400c1c0c0c0411003083c08502040440c4160340c010104102007403008441c0c1d8007070760010b201d480e40c4082800000442c100a441411a8100307010302850554440c1c0c400200502809001701d945122f003030003200d40e00c50a58805030f001300c24000d110076407405540b05002c0e1003003200741d491750818070502c04c03c09261120048140d00a521050942d0100c0302c042c0014002e14540c010350010030b5000c0004401c00c500200101a1540f07010b040b20000c03540380300880508e20680 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 413799064 1250 413797814 413797817
    0x501140613030b090111030c0406020705100e04180f05060123030c0f15030703051902040302030a23121e0c0a0609290703060603060f180605030a031107090b01 70
    0x49070410114624141554001e90300c000086141030308054603280c1900309481800e03050300001410040940c0401104c40103107401d0742c06840a400301e60b8040c0140034410b918600690710b610b16958504041500d0702e039540d6104040e0902146c0d80d0400640d02c02090044089400c0321541c4c10007170160082e00000365000080040c80742d0082d030740a21400880c4425910742040150416034484100d040c00340d403060b902030b0b60004141c540420681c0c146800700107a0b21107030307104000c18000360b2804100c0900e2030b600294500a03294801070040d00b2900c1114584800b801003036040355090b050035004143e2a00d0000c0503040b05040c1900c80e403040d2080103000300c3c0326406402403500040b0980c110007050380c01094101c01c0b030080c00f051501e010300b80031981c1142c002c0c140c04000b80d454040c0300340c070094006031504000d03160a00c0e41d180d1a4440c01e0103481c0d220700681090300e070461102c0c1c0184000d490b001d4140c440040240c0303805480c0c10044101c00f0040c0c003aa02000c68200558070480c000a0b105 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 413800314 1250 413799064 413799097
    0x90c130b01081b0d18051c080a15030807050c0901090902010e0303030f0106080a0f1803080f040b06010e040b10050408060916170309150306040f06031505060a15020105011406 77
    0x11000c4d000d00500281c00400402c085442d00100403444c203005540d04906020026902c0d4540c125000344055401404540e44e82d02d4900c0c100d54000d03c0049480035258809041680d804072030a01718a0303d19100711940e8408130602c00030500400d03540140c200300d4070070307211207000f00344440400d40c0300c0c002101c42c034a4000d1804010000c04d0302c600d01131a0408070700440000c614480a085005039014540a414040840c80c070352410141d00c541c074680e1180030140d00c8003042c24603076034a003c480d20281c0024100807940c28200f078143d07a6030380700e101c180c1030040500b407001c65424809000d80d00240704035080390003800b00042580c01e011569548002d0b0383c4c0c010f006801c3c2489400c14440c0c0c0f6042240c002c521081c070000150348c0354082240c2411719203403c61901c0389480002c0200341d410341c0f0307403241f9802d041c0740d000c00c001880702101d1085010700d941c0110300c0d0f035504d1000c280e040383c441d40402d084003c0c4041c40d00b4442c1e0107600c0035042e1444890180350800c40101802401c1c400c50b501041036185 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 413801564 1250 413800314 413800327
    0xb0618010f05040b0a080f01080102070f03050901110102131e1401050f041d01030501061a0d050903090907030b03010c0903110d1103071409011d040605090c130b01081b 74
    0x10844507860000a98100b5030705090700c03600c1c040d80c40d812204100000c500f071101409040289001154018040080207501c4e11a40c0c3d60780004c1d44482c100001d007802008074003204540c1c0030700090020400184000c64640702609080c0b1110f050303030310507488100b40001c030a6103829011b0001c1d800340c850419071220828110401100c1e583d0009030b41502450f802d101c08100e1490102046001c11140b1501101550444c2880c908403000769010320b12510f244034034520200c02c4c8400b81d40c0e1105417148001205d82d1502d0f2041d040d4032030b1a1a03154000004020403104a03095030200d402c84409800030442880d007024103840c1003040303000c050043c04025558107041d15100c00c04600e07051007500c107080d641411038040b9282000942054444500c1c82c0410306450400c40c816500401c80c03811100c2d6481c8030700d8424800341a0240c0003404803510348001840c00d14040001d2402c4080192410001c1e814100c6c20030018103c40c00d98900290031600840d188914203170300781e1419164100e40d10325000 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 413802814 1250 413801564 413801567
    0x120c030c1b100501061e03020406021f060902070803040b06041514012a0501230606070602160c090c08090c060c0106033302070503040e0411040f0e010b061801 70
    0x1003026240650500c6107002c0840c1d160030360700a00d8000d00032500d40c0310100034021211003094003280c55050801d07205100401c48240c0c00a5800c071203810501003040886810071950000d0452a00920700c02800041e49104018251004510a50248150100f19294082000b0545103800c42125055048550610440c0c280030044494150141813a20400e007490b060700c1610320b4620140e801d0114501500b00c203100c000c0c05042c1015503004600d03014211032002402124201801d401e00a440c082014001c12540d60704880d00c0d19000082100c001515141c602c840d401507002d4104454100503e1584060041c0201030140ca005c0c0d014100c0548103506010322030308044412010b541d00c83c0000004110f0040000303405202105411426030380e40400501d2122981150403042c0d44100220030100e4408020758094078007038220440315480d1814041d0892500041e02a0320070319054a10781d038000c07594088500d04002c0320080c440780303040c0b4003003017001d0054a03040b03900082c06038a420a43d6 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 413804064 1250 413802814 413802847
    0x3060a050703020c06011712120f1f0b03011706130813120f110a0e060918010f1a0307050a05060307020321070e0d0f140316030302120c030c 62
    0x1c1e040c90010304181c3c103681e00c5843c01c6000c2e442051038145260342c2c5415980f041c0700410303c40303540441d468640b902a02d40b103495184000c20440380306505201043c0b0603540c80502c1000481403025400d00151256681d00c6954004e10400c0001d019841424241c04c0c0b011130040e10170492810711008250040d282c406181e84483c404141090030301302d004c60b00e090340c10069001c041c06401c54020240039464a003540c41580960f80713109880c0c0900400254041c0054298004029a00c03692961200a0050f18210300b03015955110b50a00c40180f882420980c42114810340d04040c0241c00c41e030380d4050544444890040c1d903080140302c00c06000904140c8000e540115241c811a45030900c0419040e00035218041c1c50b410342c500c00c81c14803281561016003541744610480300000302601031341d9050007101c41c04000402000c01ca0010b084044024000d0b24034022032141584014046407600034000d40c0700640b00203a030380004000c01d1a44402d2020360384a0201d80409902d49401c02080c001e0300f = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 413805314 1250 413804064 413804071
    0x120c0307080c0310111206060c070605091201020f0a0c0519050d020106060302091507020604080703230c09040204090c0e010602012901021510031709030d020a050303150607120f1103040503060a05 86
    0x1100b0f042180489c102c404108400003881340340d0720b90b46c8440300d6004000b5402e60454134450303aa801440740c0d940003c4036404852100e0214107001150141500d01507081a0440314002c0b40311440022150600c503011550ba403c1100300d50003000702c940c07108011f408074003640b00520b4100418030618070340c0044080060000318001410241043d42d68480c00b89000b040f41c08c102d8103d0170001c0481f1107680c0c4414484524a944000b174001203c106006c90210040148003a00c02c903250b82d40d01040c0000c510811000d40407640c2c560486603100c1c20080d01070f00c40c002452141006203c02049004003600462251382d030141e01410800760503040741c9101c1c0b8400703080001c448101220000006400a03c0341c819440300405003512603c0780003c0500700030304061020b040d504081c0d070362000148080101c5c3d0348007400405003801c25072100e01082c0780b409501c00040182c09440b203400481900300460000400f0313181e507450400464003010301d48a0066100e41a010350104010482640a5801c880c0c1d2 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 413806564 1250 413805314 413805319
    0x3090c030b2508130213150501120203010302010c0303020d0f0e030307120e120f13080c0901140904020603070201091709030105100303080408090f060d0b0a1e05120c0307080c0310111206 82
    0xca40c0661000c5a044600701c20003c1f032040c00d40a010801ba5070082c20308442103010b98000c42c01c2d0361541c0c00180441540700e8005081650025040d2000041070b40035041c7c800e0b400804000f8002d01042d141d54a500a0b030f04400452446124099040c4241c0141440500c1000140c5281c10304180000455004082c25004520f820300a204541d140703081104010702c2514000d2481d4080b6406000044206801072044010541c04c814240d844a1005c0c94001c2d0781541d06079600e90380c03d403080313005180201004040041012607540588241c0d400381503001d104900030081a2501703c00c11016110502c001400701e5021400140070400940c0902400c0502078000540520300900089142e0700c89458504060382c0c8490380003107418034500703d00c00f420302d28403072900886406100032000b180368070815209070b0382e0301c0910303000342404e01910301c1e10200601180c14480c0c4070707044251600f40d0304c02114003a01c03403444031f2029440540941441c054600454515010011003104405240103102a8 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 413807814 1250 413806564 413806579
    0x102030415260601020303042a060801211a100302060a11060a15050909032b05090c010c03200f0f01060803091c0303090c030b25081302 60
    0x7228486458000e4030300314950354070640c802c0000780d024424042d0190b407946207401101000040d90700041101d4000d03030030140616020381d076000b80c541900c44541070300310540300b61000050044e410100c018107803849024203003200084a1808810100c6851018001001b410035180300c1501c21200260051400412800400c3c0c80f50085100390b8000e030b1019002034200d0121400b12207090210b6500428608400d200b8100508002d0180403450300445209240004c00314001a60400407035150010714030102c12416103102d1a40d0304071503450031800340941030000241e5800c80101e488e443c0d00d1016158000c00c003210361003c07200c90060550485203603001d520450124102041750400c480c6240e0f000701030f540d61440b42a42507901603071007102c2d641d000340702112140e582c4040f905401c091102c0541803015181c01c044014000b08040600010340c207070700c04420b120364940704034841d8900c0401c80e00d1041c141045043d0302085050700d0000160640003044007801030102c10130101d0300050614 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 413809064 1250 413807814 413807819
    0xc1002070803040506060d08041a0c0a1209080114180307050105040821040f08090d08040902071a0f01180b19060813080a1214040b0114030c03100203040201020304 72
    0x1042264000d240980360024040b0400c402c200b802c00041d5030001d410f0313822203c0d003000d907500d03032819026501403109a0f003c26885c425440c880031060310b80100004040f940815902d040c0840c580c0c4100612100180c145000841c50306414015224074031444107142000e036403900e0b080c1001d035658503940c0c0c00c80d0108000040210301d0900449014030f005090940d528048081a0a0320980844001d811910030301c0402000c9000c3c1d104000c4125001550340d5664403030000081c10300381d4152401031141c01d0201c1d01058a528550181c800c1900c525050002041d00710803003810b00350304449104010700f0500040c040c60600044903140ca8081c040d000c1002d441c40d0002540e203e001341c0b501d001e01021034808101303c5600007216500141c0901205409401940720300102d40f1a030210202403003000c070b0900c000c20030141c1c011b0500c001100507094080c20145403684056a0038861500c2d02100129684424500852410300c3d004004000303002948076046414065080100164151300090100 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 413810314 1250 413809064 413809093
    0x4020d150c11010b030a050318011e27050d02011101020d020706090605010b0903030a14040308070605060316050a090b060f03040b1909030c03120905010c050a031406030c060c 77
    0x41d1440c69106440c0c0e4412590a540d0301402c560040000911941c800d60f68200400c002004076614441200d889092410240c7c0046e80c6405580581d600a0f481c0241880e004d590300c03e40805c801002951080841c40c12003d407440d8126190060540c01100340c2100c02c011340c05a02c002020414110000d070428450b004080304070f03000101e080c2c070761036201c0e00a001080001c4c82524050a400080c0504115070b0801182d81c3e4010207044509200d4001e00342020f4003018401e0f00c008540c0000401d039285120b00d0880c000d0041a544d160280c4664009110325415010f80d10040c0d51010302490b0346a4900244803014000c50814290010701c10440130705080381d010300852003540621303403c801030708099120040f4964840d619440321840e00d0409800207071b002d000c005041c0d403d4600480f40ca141c00c0640c100402503064002c02940ca02440c1154141c2c0040161114524070b0324104035a0507000c4a6002d0168200c1303000e5455007054403082e845142c408094022079012504890000040811 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 413811564 1250 413810314 413810321
    0x140f130615030614060322080403060507030912080106050d1a0307120b0f0c03060904030e03010f0c0e01050309120a110609010609060519061d03150108071d04020d15 73
    0x9903040000e40f146020301c810282d0380010301d004030b41681c5942c90b500d4043c003100b40390944450f10300c0d1588440a411010b004031607040d10061034202e40104001d00308614098010a00c040c0700b2185060841024584540204c48050480c1c045858492500012511150080c050740d10103400c5040e10f1042c3e00a540c808205920280030081e4500c00c40041d1820602c108110080c40109010054002c0103908078851054a410080640d085c9105407918078064440301c05c07815005416628216052540c200550003240e011750701500e0700001400082c0044800d48002c55107000c1c0d6510415003031030000b45c200010944849240b03070404031000504086800c089080e5240300c06a0b441d0003081c00421468400c01004200490394000c60401c0c0046040b6904583e21500051011594a1400040b05584010f0300c03e00000c00703031515021490001d4101840c05c0c0a4440c0c4c5100e80700010a10f1500ca071a08140d140c2072040d155000d9455a01300315039055401c404480c01401c80041010782e181900 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 413812814 1250 413811564 413811599
    0x10e0405091f0507080f1e0406090209090c010f02190f1103101b050910030f020c0313031e031b06061809060c02011a0112060506120907140f1306 64
    0x11004140707803e00981c000c003d1750b400740c2892015402d900500c0041204074113404a00c20080a0320180c41c2d80d5814020024202d40c00040d400040d2034041100f10351012404960490b0b0136202c90348007180c0c105c0100c1c3d07550b440a0503420740c0040510610007182ca1611012072061050eea00215001d180000c00d040049035003600b9029902c1d5072409440090f4415414100941c500e0041e040900f403e000803145130844900d1014199640441c0b48040002d030121909035851408481d510107250200000500c00392000b9100d002880b26207034035000d00300214161301034141d0341d01ca001c494401607609038140008002c403502951003c3c00039144e594030f000c0300e0005c0c1030200001002d0030790341842000d442800c12081e0840e45800c04909130350b526240c0007a080b030802c3c601781042140d00e0341074200420254000540c000d1020500303582c130a120914542c8200021016195825940e02c207410006a801040c1c1f603004094500e40182e03420f0039580d0200d9a0342c1c41d2030100e00c40e81d403000740c01c0c4450500c5 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 413814064 1250 413812814 413812873
    0x203010e06010906120b16020c03010222240f05070203060403030903020f07080709020f0d060f060912030801090b0d1202030a0906210b03030c1605040605010c02010e040509 76
    0x703500400500d151849424020b280340800c0320342e420000c1d0b807404030030304006000540c420b0030328048200301c51080254446004025008550b60710f2080316500c022074011928034010341e4420404543c484031170000e034110b4049020303100d14804070404140c44001e000f040c06010000140705080150740c0400056000740d002c1d880000303101000d410001c2c280075095004c1042940000c808108003880000c1190460344607040042e2119100840e008180c4946030034401d000e401c041d4040b40002002c401803080303984545443c00318583c1d918041c1c1c25015190b0015021034250b82c0104600328542c0c1003002c0100740209150103d15a990318001000f14020060005a10110b0030404241d08402940043d224605020400800d61204860740c004141f00b0300c0840b80d103a240080c4c0c103842c02c00035540d550443e602a129101170b80c0e02c80741c4d07800040d4407425200d5030800b03000203855402021000f200b260180c2d5000c0c00048082c090101901000c0c14856251080000c07203055002141f4840c0301c00001e0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 413815314 1250 413814064 413814073
    0x150f120201142515090309051c06090b07270b0306010903060c0903050f0c030a0f14031b0d050322020307080d0305090709060506040e0705040f03050a060606081306180203010e 77
    0x50741032113010400c680300780d40d840614045903080400e420145c0e450807501d0484182c42e6403141510792280c1e458886000031f10340c904111a0004004542d2516407003805a540d45011a407d5a102114540740f040401c6d105070320710410034041140c890307000790350104e4107040000c90f16680f5541d0000310b80d000f081c5000041d40c0c800b418410080d0511042c03a5025414004082041d80c1200003a00e81141d0580184114030050461007004101070903600740800303000c00d41307495080c17100240b03148441c0c00004481d2800b440302200421400359056074000c6580405148088049442e08207280b0213010381640c0c18480c40d000024660400c0101c0c4909041d44c6c0d40200305130400912281c5402d92a40008003403d080060a2000d42c85a030300742c801b100d041001e204003a4580c150191050711580c0c200ca502c00340780100200500c0000100800e18620660082095582e22142203079224801e0b106203030003907040040380c00840d4036500b06070100c01d81082400360701ea0995002900315040401d005180f41c11 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 413816564 1250 413815314 413815387
    0x15060206062d12010f0912020706020d050301260102031f080105090a0b07030212010b0306100e03030d020d060801140f01080c030d031a0d06150f12020114 68
    0x60500e004100c070110b2851828038002044119104080d404100764002c604020010320704100941113142009a0424208440d020130b0400c0b643c000810022000503204628000508a100103500c140203640c13559824150b0f401c1c16000d40c5113011740e42e20144038071064010084543e0707080c401140505a651002c6942c03040d0381c0d030501034548140c0d018000d141d16100402071a144040340c02c095180e4425003035010b999511300240c0c001e005030310700c031000305c9201e2001048201d64040110b0240300c08807072030000d0001d200c2d4100c0c0c48480c94091280c141e042031200d450b81c0d230348a07000342400845101e40132a565485107142401c6641c4d2b030328140041c24260b0300b0310507408903902055014025840241ca100c5600c9804659113074035041d400010960b4400481010b0020508502800b950040a1b40e9140000e800d00001502c0119810703074901b140c00c08006a400141840b00b001c03500031900e01281c8982c01d40065441c81807808600c0b0300b15400300401422510a41407103145001520741c640480300 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 413817814 1250 413816564 413816569
    0x70c0c2303010c080703060803071e0206070507060c0b0c1305060c01020424140a1b020d0b0a0903031b02070333021806210613110711151c1506020606 66
    0x13081f6074040c00064104001c2a00459490604600712051404c10000700c40e40d0381c030218115103e0040c000d043c5000d41500807601c10303402888526030034050004149603071903080d4100c0b403a00c20342080c1d1851880100301003150703007010800f80803501342420006041035520816000150700e501c285102241c071002042203840c0d0016030341541d6440c800c0e012428640d42da08041c0600b00c52550505040302190008021941c1c0c00c401104140d500244110690400c044d07030030064000180118040303801c000c41d00f41c80042c200d84040021500380e00918101d469a2034003030a2003545001c420700c0c00c102d600724404003080e21080c003c030034100c0100160703210210441294843c04c0b85101e14820407080004040551007a4640b0810b1701464076000d00c00e4680318005101c0110a10320100d49c5800d00413002100c030714210103880014000e000d11b0881c8141d00f01040200700503c2c10242130070b501400412018041d4805028588d43d01c0ca20000325030300310004212101007907500c0100164084c07020098a030 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 413819064 1250 413817814 413817821
    0x60501051207081e0703080d0504110603130308040c05090c04030c060201140c13180603150b0904082118011b021e0c06070b0f070c0c2303010c080703 66
    0x61003402510b40d45041071190303600c9507142c01e040c40755030100a6901c0040071050000ca00110b83c8402503503551070b010618600900030440d010703030300c41d02d103c88403010ba8100071086911801544000303110041680c0d400344c900010151081d294040d99100219554440d01e030407900600e80090b060352110302e58540806066403640010b021a41044a5019444842c0300c429400424001c1403d840d52800d015410680003030ba4805010380c0c5100700217202680c400c0d030000007502e0007151800b0340e81c014800d040059440384007607243c11104007400100405c0148024021030a607960b643c95106000c10300c0020100c9041e9420304050000f0f20200c0034440c0c091040340c2d01c00010786800b01031400a10300c083c0d03d990b041d0091400c0f4814003104841044000d100172082c4602c0206925100d0b007007800c0581400c10b0480d018020b5942204c00720f131006028601400318607a00001900e03c940c01e00a04400c2c81020041c1c142e100d0740d90b0800d0f20f03000c0c0d40c2030041081034002a519503500386001803006068 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 413820314 1250 413819064 413819089
    0x18050f1c030606170a02071a01140d020603011712040602100509010506090402100306080601080a290a0906020d05090a0210320c0d0504080615130e030904060306050105 74
    0x141460800200f1140350001c01c2d200640007903500a16140c0d40307401c035800283c81540801440d6603851040c0c0701b25000c2880d03c5074160780c403204062410071a4002070bc04204450300d8065400501440100f014610070103d49039440300300c2060743e1a4000f18624003945400c03a4000c2000358001d10380d004020f822510519900141c410000d004038140400070605501c40500040c1c000c00b034041400709124002d811407002800201c0449100d5070303440380c2042d1914010304003110080844070440718540b040d004003080810803440018116121105000001e140b111f00445460340c09008001c211005446000e00c990b010313130090036400d0b8041c4100142000342d02014414007400000c00786071254604084103599601c03210f071401c10072040e84080c00c10f010b00f800d0034500d072113502d0110715000d40c40700207001111044001c882e400d40302c0e500b90240d803418000030300d070300103009925000110640740c11519034400d0040070740c2d1910801da00450151410351304103907411078540c0c004000030308040f07491810 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 413821564 1250 413820314 413820317
    0x3150310090615030f030e0609030a050601050315100623030403030b04050c0f1b0a0c0803070b01080106060f0807170c0c0609030a0507200607110f0406051318050f1c 73
    0x50281190303200c03400080d5940016040047c221a50720240e1512003c0342d41500d802022614507900c0342c6071040c0d803200240601e40c0a07005480e0465010801c030b03c54075000340402200100f51134201101101c10074455840354400c680041004000901703c1c000a5000314065034010410313101110074803040d51409005950751000400c548890320016509540002040005210070140c2000c50a4544003803480042c0041c25a000006050f44000004005445c819400c5030050381c2d070f07419a18200d0300345106404c0031800d23408078a11603511584099070302c40e500e401d041d80f071409602500d01d00c8000c211080954014001409032401000300985a884190360004619041100e4401409400b5815000308a07250341051440c9211203668028060200500644d84403801030605a41c0b1903c2d84e85420701882c5401e03203404e540c0c2010300400c000ea41002c0c01005068440081c0714004107101c02c1540d10384000c8003240d10000c1c03400d01c40d84c403c030303410310008082e0594210400021510540c0c0c0080 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 413822814 1250 413821564 413821601
    0x5090f0a111306110708031e0408070e0601180f030303020a170709140a0f140a0b0a090e060102062404060302130c0818060a0504060e0a0b0711030703090b031503100906 74
    0x5c03d0806c004200d407601c0200d010f80307224120a40d0320504d06030040750408102c40c00303028408514100030b800b20741d200f004240d031541404103040d1030102308120140036192356800126010b04c0820700a40052003d80c40d94941140d02d01c44000c0312040801c03060380c185001400c145070802c500081c80840c80300b812400c88024203403a19180004469075040c0c0b24821108100b49542c000c5569440d5072000101108034289a03125100240285180518050b04840e084c850001c80c03c00d520000e1410701c40c050600e107000f010f0700c11850301e40f180b810400015a00c0340d180c0321f0200060311004560500c201c01c4d03040100740c21b41c2503800500000320043c144d65040828600c0c02da4400700010b0b10907000013150380c0010f49522203003010b00c0946105c0c40090258468101150700704458040d000303108841598030020740c040e2004d0715988030711403c1c1000d00025039422051005003c040011a0440c01044503251501c880e200881d0030200200b0304049030603507800d450401d01010380034081642a0305080503 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 413824064 1250 413822814 413822819
    0x9041407031a090415230f07080402030a030c171b0709051b03060a0506031504060603152106090302030c1b0612060a050909010605011805090f0a1113061107 69
    0xd1507030f440003040034007090004c0c5069000d9008540c480e480015041094078804e502c0c049556050300d6060b24041e03801070748400024105071284100f00d01a41e03000b40640007122494404951104800c90240c83e41c102d050250807104400600134046d62002c1441780c1c044011603034025041c03a0a81d445180c0391070611040001c0640840c00011020900780c6900d0385a44900d404079001ea4075542202d40c02c48400024040c4000304c0000003407802204030750a100d06a15003900300c0642e400082c3c00a00c82c0903000c42805681c681c0c01a021200c000a000d05800d0b6440361181c001f5541d0070756064001d07802c000784000341400244080071100030103040c625442c3c4c0d4040086a010b2003680b600003042e100c00000705543e5076a0490902c010000103010b80c51a05140e2080ba008080e01d11036140407035039032060350500125440030b003412030b00020181c4000740d4075400c0c0101c20b9540100000031550313035070103d1074141d200c0a014004400e28000400c9a071070602e5000703400000070490030900c0d40d01000c000c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 413825314 1250 413824064 413824069
    0x816050d0b04291017010603030e0d02121608070b0a020d080702100606020c0109140906150f13031406040c0b1803190201080609040c0302011409041407031a 69
    0x3410340040c0e025115850b01d00380f05040e44584001210140e6002d4102414802070801c0c0c901c01c0381c16150a180008041003182c40114202ea8840c800200468625807013141d913490710080440c410b90000c0c140d8079840741080344031420b000f80910070070444000c02005206d0901308000310009810001c0005180c2000003002950310140012201f04010740140001c01c10b5109000d4041c11105511084c03124a446100103507c401030348440754000740007004005450050820324017200c11000e40b81c692140c441070103224811340d555183e4640c0302c0080040020020060005040100081c0c0441c1c40c91411403502003aa94180809405135500039000d00020551410101c2c0440707482856071540c515071450403003a1070142410300b60741401001000701d16110301030b071140301c04d41c0300340d9401d0031545e103034000c000b8201c0341690b005c1c04084001c0c106000550080345809040030807191004c0c1840359480014007070b10109024140e109000c40b092000e019014001d00114039900c0020740d103080f494001 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 413826564 1250 413825314 413825333
    0x115020714040c0c080a09030b0c1e0c0102160f0c0501030b032d100f06090c0207030303091716030f0801080d2106060233010b0c010b06040816050d 65
    0x201c4a00c81c55991502c0d030300b0180603501070340c880c9602620958485c00214005059004984000d41e0800f0140c1c000403130102140e01116951203c410310f40c44052081c841410054000c1c00c401c44156500708050303801c541d1400100104107100d001c00791404000c40c90008121690780d0b01c1981890304250010b055550f02041d03e8180714541e010300000f4107e40d90303050104545541600c0c0300360096150024100ca5690808901c15150182c20302c025035551103080d0494880c000c00b40b006810900041c4002407190b004203001d035001e0f0701e0443c140b800c45500003156501840c2c25041d10b40700d0b15140010503800c2440510610b4060820001d9985440100c43d01c0e5081c220b00003040198904100701d070040b00800200c040c280d194002c000c07803601c44030081c0d640c0c200e04030345900782e490b034012007a00ca001300d0605090240a1801c0c07007140f13910f00172a0300e5140c0c00441168040303549542070b0561075182c94001e0801001000014070107103004041d00303d00b007003503a042140600c1d8844a0036021691404 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 413827814 1250 413826564 413826599
    0xf1c03020418020702150c0a0302010b241c140601080a060f060507031413050310020408030d020a3e070509180a1a0f0906060310020901030902090c0301150207 70
    0x1030b0050b80e9668144006040015a0310200900074004543c101203840c001030b504a600707110382c00822901c100319081110b8400d06031022102c4a5051680055059a400c090505000a249419804100c484003c0250f6444020f10081c0d09035603c1044070940c2d01c803681581250385903008100041c2004034100300b8a0a40c0610700c10f2200c0020f100040520403005c403544811060340003a2a4248080c0030411801948180b5101e44514090f5401d510316030301c00c40c0c04480d80a80150301d0551960349000180d000f9090742e409014503d130400754440c0300c1c2c020381d2407900b01100c403c840914050414080a40100801030b106d580088000d0003951100c00701643c004256080440c148004052820710305115407000509140c0e80305140307807001c04801c1506000d06081504100260340380344a10381e851400300c80041d45517108040b180440e0030981e00030072040c003040c034010888a1081e008900c0c031942c01d4071090314a000000c010012016503415031b0070041d42c0c502c00341102914100e003d825050004 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 413829064 1250 413827814 413827859
    0x180a0b0606040308030138040e070e03060708070201050a09080d021b030a0504080d050c0c0d0516120203010b0d0b0f0c1c140f010f060c11030f1c030204 67
    0x280451856910907058070000c591008140d580e035078460b504920703200f8808644d583c0091401a50f10380c2d541840701c44121003031074400c45d60708084c40c02d1240b05580700050721800900c000d003110181503440c01e200403441210b1a8446800c41d0400d448003d0840d400104806069441d0000d0580015506811500c204c00c03080c00240c0c0358541c150042c0391700c500e40c1c06191035a1000040d2001c406422070041e0048a510206840c2445207040007a54144641070107000b03a908900c1c0c200405180c40a03101100601a00440700d042609401c00580c81e0400d0708044100700000c80710804600e000d01a00d82107a00c06c5c1d43c02414509940d84615501d200603001740c01c0f81580f8400644031441600c240e4203440c1d00c43c0542e0801000d8684100b00a003030040241e4001124a80050858428002c155048030800040e01150919010044408102881e012a00c0e80ca20741c00c00709407641c0421655498851090180071451801e0000101c400c2e5a902c4007400c2c540144000c03c504007141600e0304042012 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 413830314 1250 413829064 413829083
    0xe0a0b0306120d080412090f09050a0e071d1e370501170106080d03180506010b031014011e0509031b120318010315030b07030f05180a 59
    0x40c080091110300d82e0004102d05880382089440503658402d4400e80100e0081080800c516952041164801d805000e1b900c1081c4440c0700810240c94207510096110014a000043c9549440ba5050408010b5846444038043c011000c0464240b100002c60304203109a912a414040c03041041c04000c100a05a02400130501d00340325500e40000014020024681140611550302e50071010047c0420b029842c10300240245004c0480014800e04060311040c0005005404004204401400003002a0400011500d2003480081d82c204803c502030000310b00001d442c1d2400301c00081440340d00343c3c8039803c100d990460381900c503600024620400e07600380507020420b9030f04882c00c0d0380910400c14001c0d0188a000f01c3d5800003c409606898800011582030442c1075030030090691300d000303010034106d000e0300e1000081c5456010b07501c620f03c800300d500c221140c004d65a444010516a040b40c00c8800301e900c038038030740790003e80c3c9110725a880602c1c2e84400c40800d01c0c0c4450996510030340d51005048410 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 413831564 1250 413830314 413830321
    0x51b03030702151306180c06030c140c060402060d06030b0406050108190321090b0f04110103060b091306030f06051509011d0403050c011a040e0c0108040f03030f0504050d0806010e0a0b03 82
    0x100316901c040e05070003007100a0508d60b0b07040d0080040200c42081400103202246900d0042004421034441000702c1006002586668080241c01d621803924a41d606680301000000241c0b0398000512890003134400080ca503144c5481c26003816952825154003c1c543c80403407000a80028500c83c544024410000030844828050802070000719805001412130300104041c0440c50f00b0072520840c071440f06441d03c0030100e001502a20b1113402030903c000d5060200c6211360510701c903680d05c200883c080c00308030f440d40c030348800d4403541c44100c017035900355240c40c10004546840e141507002000140e440318655071401c1c0d500119943c07204240d40750f5441e19030224060501c035000356165007a0090013000364070b2070303104041c20b121300d10240140560300b402418450104080340080010784183c4402030540c1d940c0d510340703400070f0002c103040341419565154590041100e10629120324450001480803000758031000d03219000040c002410040070361020402d948580b070041c82114101a0260344984 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 413832814 1250 413831564 413831591
    0x2040f060803040e27011d0d0f080a1d0d17060d111f0c032319030e03030103080d0e210a030e030c0102040f091812051b03030702151306 60
    0x84e0b079031600800502c0c01440d014066001c034140301c0d1f402501c51003d1001411403070b15000b000d0901008202503807901070003240181030a5510011041c00040e14040d96003046260b070001d41070300c242961240c2440c814054120350403000701c00507101640002d14041c000a000340a090034000c3c10000d40c40240940b0342ca8445070650a55050070042c111480e1071403008244640421003900001d083c031480c0c00c61031311000708642c0d0340c120b00e4507140e2900d0200c1c108060b0000d04240c8850406030756202c035850820f400d20207140030b548034001032a61440d0030720a600541e0310401040800350071020341169600084100100c5100000100315114120604141c00902c40c0c0c0e020303000e4074040004c403103000c00c2065000b40305844131811450301d03658907100071008407034140040343c410401c05401c91010644039082c5986881c940d19046282040c606184121500e103540c1d4614158400f2050140c5950140f2011140546064460340d481c0b43c1510600511a4101c00140080795075408000908 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 413834064 1250 413832814 413832841
    0x80c07060336060e0c1003021e07020105070501050106080a0b03010c0206071805060309030c1c1b1713060807051e070215030705031b0910080c041206060302040f060803040e 76
    0x41c0e0043e50801c105849480c100d030310350340700c01213480c031400d08a1440c80c0c005000f4400c0d20301d0042d03010558860001120f1000302507038030482040c3e0610405008020005400740201c2d40030b415160b1741d10901d42004008001a45e0300070040705d03c264103120040d10100e074006070103a031008041c5003800c0301c80816a000034414082d1f800ca40e41001b000000c01161240001c01809401004000c803150b48a4041c0310303080541c0c00d100710500049140304910400303800a070003100b40030700a01d010300d25090b0084601c60780c0c2d402428826201401e4030f0003040201c2e0004201d0368018100d0400e2031030403c81110310804032000078007088128801080c40b1065441d480b0700f030b07106034040c901c10940e20304200744050f01e1038004848003440400d482000c003d820070244140c078224100984001100c0c00350f2103041e10070b01802000041483d10511001900068881040040d18090080014442d0550060006844007185c09620032404d04030304001c481800421603046443c4089100299141d07241c800f1800c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 413835314 1250 413834064 413834171
    0xc030b0124080a2012010503010203010602070603150e040b061201020408030403141006030c08061b09010806030a050d2c01090b0c010b2e0e01020601210f080c070603 73
    0x70f41408450340241044400041030224402c1103170b000982c3c1e80d0410103090384824041c80c0c00580044501304803540c0241c10448203102c1d18036212600381d444080d02c0000b002f0032107050340d00d550310909000d55410400342840040d64184025494a82098059030b904d03c12440000c15504002d0b020350b002010920461218003807800d0207005582d504d007403d003045500c6005201075030080902045040980b2501403041c840d40100e0741d81004045d500544504070010410758250203030300c1403040068000d02410b0031501141d214108440c075aa0090700380c908c01c41c00c42d0340344840146450500c0b82c0c2c0000e00c040484685134081e507955000c08030b075503026041c2d0058658105c0074111682d92003031720031809a201004811607040c0318400c01d44040300c007400c1c000601707030142c0c020000510614502c014042a550144012000c100b41d0f1a5208025000107003415240400085220180c0103401d00468000b400c440c40d0038050740103480b40150700018075030035241d010303031003e04a1804031000080304c00c80c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 413836564 1250 413835314 413835341
    0x90c120302101103060310020301050a060509220f0b03010b0a032607050106050f030307020904080f040302060708030f0106090b0a030f0605130b01180e18190c030b0124080a 76
    0x2c3c404824044091504203450319486401040140b0300c0c8017a83d4801d4904840000b0072074080075291007026112540030381000e907080092180100007104141ca40c003030186e0390408000900348a140401400c0712300050a00340710b641000c441c00d456540d40401c1900f80c0343c0001c06410900c1e0491122500c100a5100303086021030082034072428172006501150840e0b500b030390222044940541099103071321079940000d5000c4650000301d00801c204001030640c40010014461600c0d89a0300080c3c4030340c200d4042141c1d120000000c015100c510490010300500060a104011508120342c2581d44e0240941c154101940c41403001d403c1510364000ca401441d01a00c05044c441322103d60101030004102d203103010401d0008600019803001d00040200e0300744580154083e207500e0f140c080c562105e1030f1084440d108012007040d135490b49070707100800da40c462412014000d2640c03800014168050f0b0180054403444100c0014040c50701001400036009480c05106580d540303007025004191100c5c00e0302c1d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 413837814 1250 413836564 413836571
    0x20606120106050a1410052505121606140402060f090a1805040c05010f140319050906040302060f06090601030c0215090c010e0a06140d09022e03090c12030210 70
    0x1170411502030814228001a900058140e00e0000103172072901c2000180300103020901303107505c0226104e11400800c02d1103041600c00c80b6005c16030880ca960052080030300b20010300c07030068040080d24030401c05100e034400011162850560006141c2d070186070300725810b05000140310391603541c5580c0da03e0080c04030102c5583c188001006d00c2002040100c0b0104c8051252410200d101c0d801000e02d54000445a030301c1b9421111595055040c50300054040e580c02c203008550013116071614051148036110b000d00400c5240390908001303151a901404400401f9a080d06000c415222404a0b03603002c1805c0c00c000c1817107010038608a103824445a446c181c6078030f201c0300f80a4541404240000d610b00e09a80d02c1043e2100d4030200052202da5104942c0400d0103e01e0840c6030180c8280070741840d24950000040c00d90054003c03800f4001c00b800104c0040007542c0c180034403c2c5442c0310708046a030140c80c6c10484040c183d51050072100c0d141c02052040f000407010320007003500c02c00049070b411641c0c41051 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 413839064 1250 413837814 413837819
    0xb0d090f060c1704020a0501050d0f09030302190c0807020603090a0b0a051501110d0318140303040b0a0209030c040f0e0307050705030c101d04020c0109050c13020a020606120106050a 80
    0x1100400c0342c1d059810029618074000b4826545005a650081c1c2d00100703111005440d103001550349078084d0360822150740e1102000d221031040c81c130440401034000d44000d07996040d0f488406d4409a2503070091028025044440c60100351100d040d243e1003039050717079070f10f50b0707501d81c0c1031030a141246e40040204803a518100b0800c621a49412450040d0720740c2001c044071000c40801513400340c1c3e142c07142c5a802d50041510900c80d40c801d410803141244001001d001d40420f40e1100095130086204400035079000105020400c4000070b003059000b0880c0b00c00310f04003003008002035182c4000d400421b104584a010304c07107a19010364040b000450740301040f2950341c885032500310703140c0441d03104980c4039010b4842e1500603820541e41020040c0415541d03489400356141d0040000e00014502e190007560034403000650300d500b44100c04038540500000d004000e001801c1090000403c200c211b1406d00512680010940018010350440c0007140c5910400204001e402d00618595008952050081100 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 413840314 1250 413839064 413839073
    0xe011a2b0f0e0606030109112403160801171507090f12020f0609031c021203090c092424040e040510021608031e01080c1807090b0d090f 60
    0x981082c610b103505541140d5682400c150032100129400380000c640c00016540311303c1c10b41403029000780c0308120b030074800c1c1480c52101515001140c6e210044500c10f0307000c0340301a4200e01054010304401c0c450740d02001c18141680d07259403840d030340c010b50752054401141045024507606805001a81048640b03940d403248606110038030150309a00981c1e00103100e0b1800d0070408100c3d40003940c050003d1045086030569011180260180d22045005109a80d2009a0070314011030040810100400c90404824104210500050a030500d8841005066600002e02d82d0303032f80c8034040c0c00b101c140e5142d4a401d0002204c504051a560400600000e800315000031103607540c81c060b500441c11100231a1314501244202e00c19044024a0f91849441e0080056000d4000395440414060030000d01d00503506112034960302030300700c00b010f80c11170038101405040c00841d40c44019898001448541043d00300074000286078096800440c400190414286131720b138118051003984803040903447e00282c00c1 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 413841564 1250 413840314 413840321
    0x20a0201090c050a0b070f0503090d0c080d170c090a0b2b06051c030c0501050a051b040b03010603022802030d060b070314180301090c0e011a2b0f 64
    0x100c40020110380c0114803800c20071310082c03d80d660490924a44162526090303c02200110200c8203444200f080e1a15134507418020700c000c071f10a03a80300c504241000149070a00b03034442c0f807280801661128040da05824040a690803038482c0200c250784020301c0010a14218041d041280039200002da10211920310f0000004205160f01315201042c00c40c3e00c1d0802500d050384a5280d107c0d1800d020a440920704000202c00c4c0e5219007009910000b00d95141401e46030f0445a0000840c0d0341d500300118007003841c0c003d41034086500d040c84c2c81e0030b0a000300c2d824180030600480003050b90128043d0300242002c425681d520b0054800c190600341d540a0007580c950040b5007180c07105045c5070000401440510690382034075072548442d142c2030708007840c1910320380001420343d018401d406501d4440e81c8080c030509045a00a00032518910300348000711092400682c050551145c00c1780c0280004406641680c1c0d055403a4220a0815015076460010321240000c1010003245002d5010b5074080140d0b0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 413842814 1250 413841564 413841581
    0x30f07120507082a04140907051212070b06010c02030a140d1b1b090608151005150c03071a1006020f070306020d140c0703020708070302102001020a0201 67
    0x742110704090301c4948241c2c8504454101c0b080210442d0314200111101090311400d02c0d10242c400603003500c6e582d401d440860000d0700c1c0c1d921290040d4005200c6170408111040300c0502010051400403003200914800f03204040703010f06003008010124803243e1041544c650070a4005003101c41c40001d034100034a5001c5650382c4000240309041d4100a400d0081d040c06050301c5c148094040180d4440e104c000400801c41002144445041c0c40456440b00500c1240060301e2610010710001c2c00d036110b0b0100c051f038007800700d584424081100308010358070382408a001103804000d20b0b4440d07203000d10661842c010f40d01c000305513001c03514050b60b80341509d04800f44940088032258a106a64190030383c0c40d0320407007901d8007550304081418404102039400400b00000c0d80780b0005000c094021102c40c0c000c0b01981c210007840c0002038900b040c1541000f00310054056040034200c0185164002102044402030072002e101056030700801d084413500d552a00401514000d540c0c0340f12210009009140d4a0b = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 413844064 1250 413842814 413842823
    0x16080601181502070f0f08010b06030402100f03090b07081f03111005122806080303040b07020a051608010c020f1b06190804020f0102010c0e040b030f0712 68
    0x64403984100c03030094030050181c400319030050030042540740380c502510415055210b8000d0000f0b80d801140c5801000381250b1558100540c2801000e9080d40c0d0100400384c480d29003401403001603a5180b515002c0c901c1039060007401d1540c0c0703000070383c041d051f848000b401c0c0c10007007020420300b40d80002095122718111003048015208007180340c2c20148450201070b102c4000743c207400d1081d00b44900e035243c0400b0385052490401080145001211800319001034001c44041c02c00c0b40580d0b50341000000da0b500002013030040605103119561f032800300070b001a00040201010403003030b030300074060000c000380c010307081d101c1841c2d007640039000c0c440e0b0500c180e140562034411403440907403011940c01d10f00101a00a000c140580600b0300880215074a14543c1c4201d04001d044820008403000031000d0010b92540c40e520b03c0d01c0d004101d0a0400d51659a0540e41000c2d40c2c02130003a030142001d205071004480000700b40c600c0c0c00c0828a005020403601d140346c4035110010905184010f1440c2119224 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 413845314 1250 413844064 413844077
    0x9130e060612150a0507110109050f1c02120a03061206051611120702010207080f010504030f0305040f0b0c040803040902070c05100f052101062028080c01020316 71
    0x200220540d80790700710030103c080070301801c002c00c819500580042e608845149044024100602421800c40380d21355011256940a40d60404020344244008002503901600722030b039500040c00c0294684200e61580e0140480004045960f14044d501c02005130100d01c00d03003880780100740f13454030040c072003a1801c242031895800300c03034401442400504000212240508280e080300390208580c3d80141804905501501d175022450120401c01b000d00082d41c1c20000c02c2c2c4d810107080c0501106010794424040500b4041044080381185083c042e026038040c0f0151010b41e02c14410385110300503078100d418280400036000070024403030340140c007940740a9034060f0001c0390f0320410000725074002c491940204a079041c418403c640220301606d000c20040010f061601446d64815406401c03d8010380082a140954110900348aa0350840e003540401d00512070f0944044034031100001360b1142c1d05280d4162104541041000b03c02c2ea995050404004d544a080100c0313040801d11600e589030b0b002078407 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 413846564 1250 413845314 413845339
    0x70b040213020c071215050906041101090f060c15060f1e03030c0209070203091f030c030c020606060903030408150f0a0605090a09050a1209140409021509130e0606 72
    0x10340b0b208585a400320343d0000e06002d4500004e64500b00c140b56010780d4002901c0c0501540c503109030103202d100c2d0030706202911051401e0324201d040100c00003c3c00b81003000c081c1040c06420310001440707003503d010713051072102c24103a4948898090900703403034a2034060174a0000142c01e5800c208440944200701c900c0c0400c0d0075600c2e01030704070031030900c03000d0005481407000c200581044580540c1188092065a00c0e005401d404100350003418020300303280a695441524450798140b0600040100301d01d03051280d05a2094002d55414000d03161030f118403000982d4501c0c1d9603080048a00030300d000020f81c0c00307400d120f5480011080c011203810450480d90800500c91030502d1041c10203441c00204100c1f0b90351111320001c0010100c040045406208280300792000c40e14059049104d960540c0c0c901981b030703092420300589400f0102d11315025900388040ea4006949904c46410421040c400b095220b0b0b01080000301046014617900740c12519081c81141c0000d0301060440c82204240c40d108c4a280 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 413847814 1250 413846564 413846599
    0x110912071502031602060304020d0507080d030c032928080f030f07150b030307060b03010b030c0310020c120318011104060c1b08100f0b011809050a11070b0402 70
    0x41550600d04032003a00c01d84d80070052411101958100e4009000301890007441da0b685032038034025800204e42540032580030b40b58158180580c00f80c0c00e642d80703401c2c051402580105101c4e4164040c2c05500001440194142c84c6c07190300c030070412a10300a001c0601030545030803600210100c0c1c02409035501554440400d42c220001c2140c2c41c000b40301c0d481c985000c070306d6101c8985018114107400760b815280c5111080c00e55080000d0091030703000d86000a0142803680805003160860003069010b500100305980003a0790200300c416281c844040d015a99120f044001414400300207001c04144102105116840fa40d103c40012846070b104001c02c206415841c0c00b003000c0c0203070300c00d0000140085001000144217184d032140c4800301400c0088a05842c1c646c0c06090015480180c02070075a80c949007001c425144c0110b000402d000c0c00c10321a03643c0781d00e48815100d0480d0042c9220306803180b000c5603004641e64000783c03040094143c2c440d1222180d01c4d110301c000302c1c240c6003070340710303102070782d0303442002d6 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 413848920 1106 413847814 413847817
    0x60307030f1a1b0a08060f09010305100f060b030103020f22020c060a0b01080601050c0a0b011502060718090b01050f030406051803030906010911091207150203 70
    0x5142c040040c2c60164003c0800b0b01c3c109108521400c0031007420101c0e004101c451800c001d8955038074011500100c111400c00360030011650000050100110302c050107401d081d80d080c0000c3c01514200e105441c01070040401c2418100010001403509070904010383c0c80203800044101c580718056068076011800007078280d0340024420450140c240607550b8800250a42040f040c840c6400081528000608140c14010001400031381000100242040c0a80c0181d01110541e114107003482441c1c44a024140981709070008500032038000c1c8000150242c23001e03140c40e1418a0001ca417009000342003040e906105c01048004c445445d620029071050307028040200d1301e81443c8400d11850f55030703022004d445800500a2000d40c0002082e0703076045810391003003c0b41480c040700154410b0701c5460711160f806034034103400040805011642e13208032140706540c0d120b0010030000a036101d = true := by decide +kernel

theorem cover : BRFrame.Cov 413669064 413848920 := by
  have h0 := BRFrame.cov_init 413669064
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413669064 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 413669064 ≤ n) (h2 : n < 413848920) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
