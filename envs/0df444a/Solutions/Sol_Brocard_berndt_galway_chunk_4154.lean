-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4154
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:43:43.034672+00:00
-- url     : https://prove2.me/submissions/c988726d-015e-49e6-a0db-97eb29ac5028

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 746942446 ≤ n < 747122302 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 746943696 1250 746942446 746942453
    0x10506010f0e01030906050c070b01090e031204030c0b0f2502061f090204030503041a0c12030612100b01030e0a05030a051608030109051e091c0207080f2107 69
    0x41c004107021a050081c03000442200780d209501819850390007620903c80e60400c4990780d140c6502000c0305860344c03051a000130944044601030700500030340704e200452070000180a142664400680102d081060540c5020b012402d0403400b10300491842c180c0941a0030326141c0c848c4190480036140c2d0601c03654100d0301c0030f10380e0042800b682c42940340c0000c082402071000204641030164000c2e00c000380c40810f001c8207001002010340309a52007001001c030210720181114200e0300070030b49001150b6020340b0300e0090400650010310b1b0070260140a12092006800e0a21309203440e0f81d100b000225910310360b08050f983e040c000c84984070506005855103803980d40b50709482e8426610103d05100340000c00d40c91507000c220400f030f07110b600442c1c0d050301d1756142d003440d20191a007910095100d1036030540640c42802c80c0c4918600440e9080010121070840142d0403607881104c03407141d419401405000641490b040c0070008078079002d11301400540d0305180c0d440ca00420340c800f901401d081c0601502000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 746944946 1250 746943696 746943707
    0x4020d0321020318151909080c01020405030114090a11010e090f2a12090304030b04060b040b0f060711120703030c05060a0b011202160c0e0a05010b03070f05030a0b03030a020f010c0201050601 84
    0x210540044a41c3c109a01105646c050030400034010a0b0780ca00041d010f1111074198090030568004600138440e80740105600840010140c40c44441504994064800036000d50350750142010103040c00c1d003680c01403400240ca40b4500325a80b440a080540420843c1d02c0e00c02d081000d0000c1d007400501c241c40c91040100c0942c0a200b81010b9480c2420001c0b610058041007503900456008030300000ca49420324140000c0d00c10390004600903418030780c400070329160658502c0010400644050700344a0140c44042d82502040020751304080b400e280303108503400a01100380598041c2e203a004c0070901e1403034510303d403035001000050810b140013640e00340740e039100b07010105c8101212805600c0302400c40b07002e101560001c0b00180f500b0281d502c0010314090a240940c0f0859078040c04001d580c0c0c0e2843d140d2035901c0103d80000000d40c1c84030141c9082d40c0214050b41d01b0080740c0d040051001c0344c22012900e140d1041d001030300540d001e0b4208080d004000d00030a0b480d5011440240590b04040001a24 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 746946196 1250 746944946 746944951
    0x21e0c0d1b022205010f0b090103020304060e0d020d020c0603101a040e100512010509030a050c010f0203070509130903020c0d03020102190306050f0f0904020d032102031815 76
    0x100086031100390710600440030030390031081e0024248000c824121008140100110a180c40301906100000030b0302c1d003da01081c011103032152100b51a0506020044000350300040c0101d50703040d0380301e408241210b000c000d5120b0400d0035800411000b0042d0340041d02d4401c9103403480b8031501c02041040f4515191508810440e5100d030000303220041d40340342e6010640101d4000702c8100540b5020007481481c800300e8103086490955400c5664241440c1d00742c2030307030390840c2c1840641e8801c00c130340210b5906c12401400e107090501c00024070000c076a12a0026a40141c0b2290300088000c1407006007442c00201010b58084003010412519549580113900e500c495840248038543c030210820a150003901141c0c00c0d5100800c0d2028a410f030324801600400003402014010f5007042094900c606004070460b011103c010144000c40e5900d9003000854800808210104400c08000c4c103a048803407200400b0f0302c0c0700c00c40f000d43c80780b424200031040350413200d03c640720781e602840c0c04002c1c4a000b000003d4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 746947446 1250 746946196 746946223
    0x1e0b150c0a290f010f080d080118060b0d020307030b030607140d060e10060201150501121d0a080301051c120f020c0303040803070c1215020702010c0c09021e0c 70
    0x40d140b411080810a014405040026000c020b90080040a50504803254140c0b018010f0303014009807a280456521003032030b410700021842c0c54006002d10319a9686040001400302d50201b05140c40e80340740c1010760007204612941640110a0040640d01170158100780c0c00c05400609003841c1c4418014035800308a11040c103070000000d074920041e030280e000440a004c6c000000380d07150505400141e06a901407240d80d0065203028048000360550f508005e0803a00141d44e8a020911030b075482000616a580055802c07109031261410102401d0200760403181c080c0c0e04040e1290b14000522851000c40c0403104400d034020207114000800601d071715100225289008000c8244481069207482e50a40403da854400071800080e0800d0000050604500c41d46500003155941d14072050b1910380000c00502c41e004080c000ea000d112107601070110b070b82c01403500121004464450403258000e42e00000307181a00000c2c90050700b8180000004440c4450307554600e884422034a4940b10b19a200210 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 746948696 1250 746947446 746947463
    0xa0b070c06150b030a0f2009060403121805040c1d130e0a02031c051e04050d03030603060b0f010905120102191806140304060506041e0b150c0a 63
    0x10340c140040c903440440c541600da44508501c90300c411121000307400c221140d0780c989051552880c031140c0c2c0c9019254940d41c0c00c8444448461825140d041c00307401018149410400c1804000045107000200c0c490b0410a0384030320407940100d00640307501040c950030450245d82032160b00c0c500d65502c4034032011505001a01d103404401003a0010303d010700f010740340d030740b0035070030300b80c802205032004915003001c0c40c070890484055014801c5608550301246e184080401c40511150501141c10800140b80c8000c0e0321a69192507160000500403c0e02040d0560000e96240c0c028401c0050601c1802e04440c006c41e6002040c210443c0000d0008000e0300526002d030180582214141c1003d4056a2140350101e416070943d040406005051150588000303a0341080d56800081d0507000740344011200480300d845520315940c03525240050040600f14030f4100c1c0e82e4004514600c001c6080d00d243e00c0c1042ea50114440c001e000402500c03c603200071036071404a082211950549001440100403644003003031 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 746949946 1250 746948696 746948717
    0x50405060906120106081f0f170a05060c04051e0d080c07080304091401060503010e0403032003070206040b06100e13061206020703021905250515030108010e0a0b07 72
    0x20501d40e00901000383d160748404800865080e81081c032544c490b01aa05c0e040600c03561040c0407151500e441d126603690480e0b101010702c501e8200714019049a8203e104135140f1911a0340c40625140c0c0c122034051450101090030301c5103141c0f00c0400411034075845450301c003030bd41400c001a4200f000721001021601c00003084141410144100801071079101c080d01c0e202c076964844000501050001d4850002d1a600081011801801580d044c1c5050040c0240a81e1700c65606074000d11105504400c3c1c100e00381281581c80490710021071191416138060b09141c146864408103914000c0c00c4d841c0320f25005208122601c0d400203041640703d804540da243e503240f24444010081816821000240c03001c14083c8091080c40d80040c036500d44203500300c800341840c0c0c458000d640c5960100003007070f642129401c11200c010131041c020f4004c148940d0000201c1d9200000717a00c0992800c0380781e207455800700c0108110030f400c1c810b549000c60164094150700215075241040c24500070010303800e01440c2c014 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 746951196 1250 746949946 746949949
    0x30b061804030e0f281d190207050a0b0411090702010b010c030810050d0f0302061608130311100609061203141c092d11130e010501120308070504060504050609 70
    0x1041090403079242e40340ca40301c94100300ca01d2103d00c0c9070140c101c245820702802146c0d00101c0c00e802d40f1035411142100d0782103030b02c04081e1000c2d500c80c5006462a205800c821000300390741d0402d09000c1d5100300c00c0700f04188000810b00071921030040c010f10035a49000400c94459800c211a24001075040c60042041c1e518121980c6d852841e542103035400c81d486c0050a000c00c5061615105194004d808942c0981e441803000301101001200e8080080c41d40f001007034a9100c1700b052031840e54481d042c01201180c00103111854110100565400381e52100d90400000c4401d00c507901c00383c80320591081c1080c50544000d424941c1c40c02914041560000c0c501000d60a04400742180f510588002d100311910b906010090365180f404c201c120b0101040c0740010000203408a4184990213590303c9904120b400030050040102568116084e0f228402c41840c80d20a11416000e441107548080802e809403d00815003d4010000d40502004001c04d00100c2e400c441a03c049a1080359065981c0403010b0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 746952446 1250 746951196 746951209
    0x50903040501200d02030423010e040f0f050a061404060e070c0314070f06051312050a1b0804060f021b2b03030506030c040207170d090804030b061804030e0f 69
    0x80c004102d020700c41100c40f40320360100081c0304440322111200c2c090230562900401801103009510b02088042131654054201604540200c1102030b000284a101918401080e076108841c0104d4499079558140710000c0184111107c1c7d00e0151420861107040c101a00f00c6a54064070708070a00c100200310500301031141008151009100341d446403503041d28502070020b8002c08a08031842800c01c00020381d008003d01c07248460b607800c004881b45082041d1010b481650044180408100c0c0c0c1203440da44001c585407410b8042441241d02c1503550f45000001482d01c1112303140082150094080400c084101090648240030110b4008000301e910030084000c1204400c40d6280c6c0e000031040a0b028160160b0086110300000c1c2d00381d4070545d040b402048224418403400410120300880480d44090302035007e0924405144800034220529072a0180c00fa0010761007101e08114030001c200d07550420103001403202c50070100016403400c2c03d030740240083c1d00c10398201d4041c01c1198660801a69801d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 746953696 1250 746952446 746952497
    0x60c0b15030304030f0210080601021905030904150f05090f010e0603030912150c03010f030305031302030f101a0d0b06180114120d140c100501060306030312050903040501 75
    0xa00b101e0f0f69954034900380c85072220548040e0312a0016070024854036001e80320741072043c24142c1c0540500c0e8018402075603051b40e291402c0c0d809105c10b01c040c0543e6101d602c1481544685010070201c0f442c5880a50700341030a07039800845c0184942000c0c00400395200d0410f5064460499420403030303903604004a07240d802004001548001240540c441540c00401c400210f138070610000401c56460401049885c8820302c02d039403807014186800c0021a1081e40515004100452013201c41e070803a4002a240c00105d41c03608059800c20f002c10040e1909a1041503800c0f81c030454100c41030301c60b02000603100100c3c20307405440c030310007000051710039507644440d14282d40441000b201d0742c1d42c640102c1c000b44002401d074940104800700b020800c40a0001e0b90f01c0c4403115541d12184610030236007465960707410260760341c5100d00c66020243d6195416028082c080c14041d50001a80d230f2071030030010301d892011807000720346074a4602440380c60300c0080121000d4800a08046612540f400158014030864 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 746954946 1250 746953696 746953699
    0x14010818030c0601090506090612100c09120506220c15032d0e06090304052707170711060a020a0e060d09060e0d021906230601090b04060c0b15 63
    0x422001140c1c03005c0780c2c0d01290007031100f070394020030a980302c00c28841c01e00c201424441e17580e4056202e142c410402d54100c17540d60300760f80c503000e00320750303518420b544540b411410200d038207070410b404100c1c4419850500d40071400b803441d907075640080f650300c1e51302c040205070080003481c0e101c0800c0001458042d8100000f004070300020f508109140b1840c04c5038034000f81c6c140980c0c280c141a0ba9844070030000401502450000002e10715240c540803c0200da00d503580c010043e084101c0c02150500d0030506540c51081c15151115404281220803107089040d004042c0070501030041d24504800c04001541c96202d00c0c40307c0c00603542c41030400b0588102c280d001070140c1c041030004590049550682021010500ca140d0a002c0e8404460b0001c4c0c07221030102d420030040e0f200c0c0c1140340107113280c503042801a60084000141080c8081464016042180e001e081101c220034180191568031001240050a40e44070a6007824100300c40100350f0f0605120150100c90b248000c2034000401070451310b800c100 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 746956196 1250 746954946 746954953
    0x10813020411040b1902011a0f0603041103060406060914160e040b0402070c1e0e0411011b03080f2d100f0e070809060601080105060304111504050a14010818030c 71
    0x16170885a282c0760b01d0500100d4011b50901c0743d0211441d50140105000c100b00912400c02c600480c0244130302900010300942e209036410304061440d48042c0400d60169004000129401e400c000320803050b141e9101d40010381c840700004014282400341800d40d910441460145080351240c000a03001d481c0c5415881e5002e84005003d408021000405400301e0f40d00030850100c107038034283d5414001115110708582e81b40c480c4005000141d40c0403002c11103d0b0141800c2107014a031000d030440b18144c902e8102d0106607a9428001010086090154010b00c40130201122030422201d130641545031580ca5110030307400c078000c1140b104070411040d0240524924000200303a680d081c80031005401c1d9a9800462402408038551b002c020405621442d0103840e03160143c2d291406000302584010403d4566030310050301a5107550701d0070405c081d56844c1c03c0d000750b101c0b801d142c104281040d880c5c0c00b0140c2d41001c2281e0711000c1c1d80129882e07501501c5000440403446501c044a03043d442616130201c45800b = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 746957446 1250 746956196 746956207
    0x109021c0c09090201021c0c0b1303170c09042a0206180312070c06020c060c0318010603110909030d020a020106030c050603070c1707081602030606010813020411040b 73
    0x6124444002441c0601031041516588912440031510f441001a005810a44022054241d101c1c8a030150400314034100c4c050340c0550302c1d501c001e15002d8401c0314499640c044040c090585c02000d040e640c07c03242540448504040354411030310b208100380e90340110344a409600030007400d113841c81d00e8209540f25a0042c1c20318040300a4484c0320454103000d0400c9030080c01c1c00a25000002c0d00c8083e03101401c164001c1d101c01c101a640190260340c1143e0751a02000042007941e03007480098002d49000c0105500c030305004540c18810424603412400a078944802000443c08940000748640030079101c40500e901c0390307025a4210b03c20344a021490b076000003440c1c00c645a0551040048a000b5618401d0040d1190104903e500c002c3d02c070b040015002c0c0c081000450b404c1005844c6941128404c82d1a181841d5600102600084100e010403140c0360138040541c2400d020a40c0d2069091038802103d04d0300010704d0000505c90b49010b802142d071281039403154162141142d0241864504994951 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 746958696 1250 746957446 746957479
    0x151a12130c0b0c03030a200a1805010c1509080c06070809160608070305061c05031b0102040806010b09040b090c030a06060503071407110d030c140703170c010902 71
    0x12842104101c541d0032814400140301c100c98002e50b100b503a0448061491905c94640c850060540d51003150f80d0601d06030410b01d903035a01c00005002c00401521240f45201c843c0000d03031a102215800a814045c07900107200006070440e402806d030401007807000400c13a80c07074103003035849015601048404e4842d07841400f10298015482d5441007840d041160460b902c04000c1c1c0c90000c04031702c07610008c9030b0a100840c00c0c0500942000e50b003e400070304050741d454003804000c0c001c04610041038810350400281e24241082c840b0144201e03102200c0203515084c60140400d684441c144600e40d40200089040342030380c0e0f555040800384035001494040181000000640c0b46d0380241c0e59500314500c0e044002030181e005d0002c0d64805c241503100c030700c1090403a045c031300e00ea0f901c180700888205020b061004810350f40c060074140880c0c001c1c2d840840564161420340c1448848040b0041203610030b1100300002607401c0e0950f1040161302c1c40b410f45845280303482c07030b0140c840500d000b548240b0300d421f03441c0381 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 746959946 1250 746958696 746958721
    0x6231620070e130b2a09131d01110a2a02012001052d0610050a051b0717150a0f0e120c0c0a0f1e0f06030906050a151a12 53
    0x160092400c510010003d165008042c0c6c8201540360350082c1140000b5480e2040c2580003180e86e080300d0341c5962409070f6242c2c4031421500241ca294086c9080810541c9400d0340c00081d0109503201c2c5140c924001c01a5250b00d50100401c00c0005c4c1007084580c01004000010180034801d088004028461f03410014450300141084040c0310043c40e05032031080340b050100000140c0140c1c40a450b800c400d040300c14040f10540d12428845050040030044031207010503013408480803011000180ca00300d13080c2401440e4607911090b42000c99031161491541810031058800e4100e080044001071303014203002440b01506549142c920300f4090503000c801b00c50441c10003001182e4100d03050301c030614800c90410400b21480e002e103c0e51626041001e20042d0024112003491401e1200e100010507a0b81c9000c00b8610030355000a400a0340f101c85ca4820003805010f610b4125814074014401c2202d010002d504440a604c10f80ca035280c43c1d0201e05d1800c0107544c045449030b1142d0100c0050f103103404264040d1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 746961196 1250 746959946 746959981
    0x3240d0f0308011401030b1516021908121806071103010e0601062615010525031403070806210118020901060309050a06231620070e130b 60
    0x4c40c5001107450b14590703c244103007001d01c40e0060061030806d200c6890040e090700421800800e00d9561840780700540c1ea10081011a807610180e00d02e072080c2400c40301400c08040d402c444403040001c4c088109208000d1140d245030040c2610090b0320342641e4100002e40304010100300e501946801007a0511070000b180550682e000d64454612000d11200451304100380c852244681100b400d010400c1c8072001c4100a0755400145042401e020190410b02d0207108014444c3e00800d50a00000c41055000020591a03180c0c9515980c11440d0008001d13003582c174004d0015100b44080101401c900a841400d8001030345400c00030403025410045d071381060304078048242e2280690400004005100740140780f1000e6005028050f42c0e102c2c1c1d514240500350b44010914000c448180042072072404d05070080c440c01103000c1c80c0061042d40c40014142c504da1501040905280c0c40112206800000700304040300d1611172241219560402d200c844032884c10703001484c413041c5506010144442c50305020 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 746962446 1250 746961196 746961209
    0x20309090a05070816090b130e10060f0207051f030e01021303050c120d0804060f0f0b1003090b0115020c0a0b130b070b04020607020418060c0207060503240d0f030801 73
    0x41d55150200070b091041a01144240086c0d030309070301480b800040c4d6004d015640801303000b4140359915401c4c44000031074101d454007481e10b0031540402c04c0d50740c0110040e503942e88500151881d03500300004030b1151140300f4002e003481c40c542d203440c52a46106c0da2018044240c240001c5403591030001078072443c041184000d854500c0b035105450014600b81504a0403103c141008000703801408505540301c900042040d55a40c1c0c1d00c421304484c0900c1030003043d614904501c80090505060000c005100801c001c030f10b810589004004400a030307043c1c00b040c0c15a564040c3c0b084d07000044400491074015040c9150350009045c0c0c1d0001810000e24000d8055800f1080e8048281619031070b894070f150140074000741c40f004606000c5009810701100414001d40090300200704001e080c0c541032400490b08004642c0650345026800800303506000b00005080075140051450414007000f544034041500c000c00d00420141101595507900041f0402d81680b0540040c481c03d0035040161540409110710b4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 746963696 1250 746962446 746962457
    0x402250302010b0310020f0301060c03140d090b0a020c07050906131104050306010b0c0c100306121505061c0803130f08120a02070f120203130306060f09020c061303020309090a0507 79
    0x6803c05414029a5000c3c00b10f400c0c40b81c03c5a03c0d0201c00c2f03031040080c0360141c0500014135031060200004d0402080d2011f6690408210341c0440d00c0c2c0449244001415103407134a1060009400354a03010515904a420407134058400e9215030000901130b0401c0d51020f2102840c0090701f1007002020800b601c1110422415100c2d5170303a891203800802d1264100d54085600846a040a546413448441442c0b180354178001440d1a01e50b1018440c460030b4820503149155040100180c0300c1c418060180c0c4414250303031382250003a1a441064249241000052441002000095150410440e0805059004101820f401581d401e017601c59500c074030204491180c0d0380c0000749070144240200c400503a07000e03242218800c030382d841d0700051f031781c41e0002101140002c101c1c1040007010300b0a40805503003e00d40000b1320501d09203490403600c4643e48400440350050080e09600c2d05d0100360161f000182583c54140d100003460101e041d4070031640074580c010304410600032507040a5001038414402e0fa110b1 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 746964946 1250 746963696 746963713
    0xa110d0f1503050715050d0e030c100c050a05030c0f1c0b0405010303051b0705091009060e010b1c0e06070801030b060f031b040f020d200f090402250302010b03 70
    0x22441071015500002d400e96100c0b41d0200000042c0d01100d001c841002d00e030203400e2101c82856802980c0c000f0041d00400e500110f2480301c0c001c400c0c80307048038420440d041006207540c2114064018001d00e445903040c064048002509201c080301103800c44801e4005030f40e80c1da070f0540200b003407030340ba203030040c65000e4a00780c800403e40c101445950b050720303016140c2e1303400e244181915480200d8241e844007402d0050f00000501e588584007403500540700c4804180c990350a00c1d00c41c0007140c809900038845c4030b0204004014034003122044848200c02500581c40520700042c0030b4018103806c140481c0c0904c00c00c020041460384c480d8009050302c1c821847c00101d51505010428400420301095506030004408540030f03500d11140340110400c05800427912211000d54841203812100c2040b201e142c80d552851000c2090344181c1e0403103000b958440d0304200e078014603541ca50180d600b80c039004945c0012380d450461841b41d1881381890401031b40d1040e24000b0b2400034041c06000c8601d038041e00c542c81c0d6 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 746966196 1250 746964946 746964971
    0x60c0201020a18061d1305040c080d02070e0a11040e040803160e150c0f070306020c160807030f06020708070f051902030606040506011e17070c05150a110d0f 69
    0x340e4811103180c3d58405d0282d10301c180356012201200341d03c80d50311602c03010126890706020b028161041d8080c00020314076916100c0b0240c03d00c0c0b01e0b111110219005a44103100081c03644102e681c00c5609140006503011440c440d1000300c0c402c0fa080944410580020001000424001144120b103404848602000448815284081088900c1d50701c918080c10360000c144800c4003500142025400700e40070508030380c807043d04140c4103810a07150641c0002d03c120152000f007040f64440c1003100c0e0030340c00c1039203000c10b4a40c44540740d0200504e00c40d0201009020701c140c6406035920b1a40241e00f03a562640d451a00000d50382c2c03010700c119514041d0700c041d054900811400b910041d90003030b02410440d95000d040000601c402800a4107014400b03065013000511000405000c51407900d0320311510074400d824034484003009040508214078480d18100255000c24507440041800250130354a49030b0303403548805000b02d103654a0030103802248005210060390080c408105a4040070040c1010220 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 746967446 1250 746966196 746966237
    0x5040317040206180613170c0f0607080a0e060d0b120606010903060506060403061113050d021806031c050a080f042f03010212040308060d03080a0f09060c0201020a 72
    0x1500a90f010a0502c45180d0b100059049403600601c01441d05180411074900c0c4c4440700925000304000201105000400c06000c000b0b040781107508507500720441d007500c1c00051242c4141e40e00140700401c04500ea1403190302079855208116801018551110354080005000305031800b103680c072500c100c0d44071000c88440482d000e4080c03081a9184801c41d8115100c44000c1c020240045401100822001000c0b0340700307104d008070f0041c4100850703540f079003011004440281d0f160400c80c0300d11800c208000c01030b650070300020301044055141c145556103020003e806c10740e90040e0040b555899804101483c0d90180081040c0700154840105944510415081c80b19041b9401415940303652940181340e02e002c02e0204a402c80740620b071440c0c04841e004207003a03801080c2610206494101400209500030607802e51141d01900c601b912041140c800074400b0130080c11110030660b50b6803c1d43c120f124550007240803103401400a12042800c01c100074000e51101003031500080843c40050061034541c0b = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 746968696 1250 746967446 746967451
    0x901050f0615090a031203021b010c021902040e0a0c0801060905012d09150608071b030e0f0306010b030106030c0c0c05060a0c050609060a110901170402031f05040317 73
    0x15046060b40700002006042c19031000101c540d210610440000c00107142c0d14a807100200c0946d00980c0361110880c5100c10414034030742c44240d40c0d0400600030726580e40010703284002043c00200c09240c1c265800454000d0000420100203802124400780030b11400000c030500f1143c0c0000200300c0165134030112000c440007800b03141150140311901e503102c010b50310321160054a051002d102615580d0a001d81100c10907810007030580345d5154100303c0c071504404140d5101c40581045070030b122a284018010b2203207500300400713000c0e044a6264064850202070501080c1c003030200ca0366940c5844503c01150030902c1480000390801c201100f42c50702c581062020703240d00103034440e182410102003001035004a010761b41004401c40c89000414803c00802e405144801d01601d100c1c18000c0c010020340c1d004101e040d00820042101d10b5050b40d0020750106d0041c50030302018055121807002a06048080761075640a02c9003e084010310100ca81c801405a1b03c03030f4440c40440109040003c901c0f1504 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 746969946 1250 746968696 746968699
    0x1608071b080d05160809100e0319030c060c2a0b0912040315090c060507020901051c060e0f01091211011413050c0303030a15091103010314010e01050f0901050f06 71
    0x510441c1040180080301c0240c8600c550717041c0303082000210100d820086050301c0c000004070b41d0001c0b030982e42010b020394000d5203103020701d4021f4030002c0e0320050014070b040500104516680d0010032089803203199024550f0702e0030004040a00078a82050300c42392010041038410980d4400403410341c21000500c0800011151403150a00f4507644659086071602e40520788041d884e9104c2038000f500c0350402e00090504c544031662102e06600602c03901e0101600080e0040c1400c0c41a1200d0003020b06068070f47d0b0f83d00c46070200391585043c2c412828849050380300c1d0029824200003204009945a030021f001c0313401d9a44003052a4005511801d0f1140301d00782c1044010210040341c8580340724450862024014021101200c0710000440c3c55030348211548030081f41d4484000640c5080400a034004007602032047c4101d8802c03c102030710f80e01c8103200003000d181040001074640002034001d00381c00f0840744000c00c02c601e440f0007079412581040303c0c080415440c01c0d0025404590190420f07029240 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 746971196 1250 746969946 746969957
    0x2107050c0a081c02010b13050108060f090c0f0303130f03051b0108040f03021516030f02190f12060f15050c15100801050118151203051608071b080d 65
    0x43c80c02c0240c111048079568030007195212981200f0f00d1322000c940c0641d40e058618006080d41c0340000840c01d04c680a070180481a1105040c000502800640c038440f402048074070b80d140300318078000607255200e9103c0020f911118400c0c001448140c07130031684100c0e406001511449134020445804030005002c104d80410010804940807800d4070b0f1440c0c80d804d1013801100d0a00c402c144150a01c0ca030704507060b01ea03030b600c80400b2080f090f605000c0c50840700d0446205604111044490300a01804080c0c0740c0c0c01c2015100302c110078203210b0340e40c05e90460003c500c100019519850902c440320840d0245840f819902500c845001d0301c54001c0310301000804014050b80050f030000e01c11041030141100980350440707400070440440a204050007800e04050100c1062140c0184c0070540b03000c5030402240c40c0c0104000c001c0700c040c14103440d048a070300d0700e0701079518040800e28008007051210050214400881d84c10304000903040400707043c001640c07010f402c940d5240a0305030707107400100c00d4000140 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 746972446 1250 746971196 746971213
    0x10f060c08030414100f0c0207081b01030b130b19050603040b070e18101212210501080c0a2102120c0411070c090c0e10022107050c0a08 60
    0x12151809140c00511400c01e401d00f1010580c145407810349007017040c3d650302c0d0741c81c2d180701e4441c4124424810744214070b00241001501d400040398440752500c95039000340403000710010a40e0710a42c488400100300800401d1601400d42080000304605603066000e07025820254880342c1a0040c001c0890b440200344a24559455031b48034080036000d010f0500380081d412a0920130b035100d0008811041003108604454940744404c0c001c0840315a00601100d41c2801c0040c01040c09000301490b1400741d8104203c8107000c516900d003039608900141c0e44e80a2900c00081440c4401044121103080115003007580140c0301d2002084036041a80c4280c008541408150010708100f500e90440346200c205a80510400f0000f042c151552864040c03480c0d20000b400c001004080709042c4003401c5001020415143c0008000c1c00a0b80444000c074443e09d02104a000f517a40b00f000740b40741da2041c42851b480c22407407010001106030003030b6000715842c1c010403141c1d99003400c01581d02000c03110300100030011803 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 746973696 1250 746972446 746972453
    0x50c0306131806110a090e150d0f05010f0b030d020115141206270a020a0e13200a0902091302090a090509150a1a011404050a120506010f060c 62
    0x2002d010981c03140308000c0390303409004a41d003445109024038005070459074407611110001c003680e00700d82009004440070402c0c080300d0300203030b0011201f0070b200b640e2581c445103047c20000310980b00203000a10303e6080c509800301e004403680180e4640c0e4801e03411100c011441d034500b60301383da80b80c8231199060500c0701810080d40b510318648a00b0040c02610142c165060703501580d082500c22034a141100250b0f60f6080d5100e140b1030b9022000996140c042e008010003580002d800d520a4800e820b420140790000c59030204114035030300101d590201c4620302070100160762001c00740f402e0000320b03c03070a000709000070790340c42a0003214a0081d00501c42c0d04401580c1496100a4026068458004580c00da020850300310b241704150080303001d10000c02031003080d5900e405080d4030041582e40d01c82e041100302c041c25061801c00d000000d4003420842c0411030720b900a45924051648100e0b4440e034031030b2002400d138500000c0720800300c0c054015940682c0c2c032002d0384030380802548210800140140c0c80800803 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 746974946 1250 746973696 746973701
    0x327031b01030603230d09030b16050c01020d1a03010608030d0c0908030c03070b0c1606090615030311120a02070605090a0f170606010207050105090d0c0522050c030613 74
    0x105040c000744444d107948990425031070b207001e221240c4040f080f1a2103030301402c004000c0700d049039103403941c0c40034110755441c96001f0000e4100b0300316032076402001c0300103401030050307840da40c2481f00215160640c040c28803000c0c007088150200702486d80c1e20a0445030406000c0c070f1054070303071a000075444c0c18000300300c800003007100700c0721101005a0888081100613081c80240300d10307040c11008548450b81400c01c0c4400355009454001b00050800445220141943c03221503966040400050302d9105402c101010386660080b40d118a540080c0200030160010b59080c091404030040310200003030108500998840ea00c2d1102c0540d004003010012188198001c0c428030780003404001c40c590b075a502110900045801900680d050030a001e030001b90100030540d40a002440140301c41c503c0e2034000382040c0b24105002d0b018400c026101410301c0303083ca45150050030702500c1c003984029501040000800c0c1061700c0d070340b03a60400380403034522407008050720f02520004000708114000c42855000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 746976196 1250 746974946 746974993
    0x15050a110f07081b0604031a07170a0e010e03040e0f070908030a0305070f08070e0f0a0b0309010504030f0806090a02071505040c061404030b06040e0a060e032703 71
    0x2244205848040c1d60300091082c80000d01c5107100810b00310101915840c102c07000c00361302d42d020706014481000800c403d4a02c500700c07501c444c848a10749440b211001c40d15012841311104500c3c18035014481149101c2d03201880385152a002004481680000c09449101e64800c1c40420320710b11012070101d01c1d03005001504211142040130201b543e0708031039070454015280002c0840c1c0e44004200f0281d82003010410b00c900c0300d1902e0181d61030b20120151212021018140c020480c20000c40c0072074482583c000090f000822095499240030b2072080c1c080c2000310350450000341c04440c8444c005004985280c080c85004007018600d03076403041218003e400102e01034a40032203011070a11101d405104060107180a50098804103040a8026000760201c4403140c0a501d0204001c0020480300c1c40f415401690894002c0383d1203410303541c07007803401011240c0500118900b080b9000818030000040419aa6100c0101404184410043c02c079000000d203843d019003180c2c40000b80780303000303070403180 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 746977446 1250 746976196 746976227
    0x302040509100501060c020f12060f1801060909170a0f052a0705030708030f070809120d0e040f0612110a0f060917010608120a03060306090503070c15050a 68
    0x760802e142e42044025964213070310050128841940402c2942410f1405c19403558040e0b40b5090030b000d01001c440d551f150028115507a0410303000100d000c0a0031208020845402c41d8020300c02c1540391500b403401010075140403200700c4d00100014421015004c01c2d00c0d0340701c1c0a81c035003490081248009603107940c00413580444519803885401b0340340c414100c41021a110368402400b0103403d01041c14070781001d80d00000d0040c2d01c2441440c0340c4190340e4084a84060348076003120b0b11200310781c010030358001191881c1c001d68080c05030b801140650211103020360900c226000e00132107032605900c60883d0321038028011f801c215045401f001c115184006110701401030b0402221554070455102c02c41b000c2e4211400140304a2410044070140245002c01d035071100c0000c100051808002d03640d10059941042801c14012400e520a42e020340d01c04401144c11500c1400403082030310300f41d40c1700d0384580d00445007400c003c0400306030110783d941c01c1950310765140c0320030b40b501801d0203094850404075034490 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 746978696 1250 746977446 746977453
    0x1e020306060f180118080a03140d050903070c0e04020105030103021e0411220b0a0f030e0303010b0a02010c14160606470301090b270610090f0302040509 67
    0xb50304810b00e01c00180345a10301c603050703a941014400001842c0141003483e03101401d50804007845010000702e0703100e40b4a0f6140c100031207000c500904014003802204510f03018107282004100301e0f070301c001c0020701d003032407080740a02132041d1900c4014425076001d44019001440500040c401410849190300384a8107a04911040b44010800031b8143c070794051400940c40f001284080b02c21000c0221010504040e9102e07001080c00c0c40941d401501030038503160b040062088a506086000398041110203401c00e080d2a40c81d80c4604c1031502c01d030f01003080c0000640c80c041c200010300d032017200200c010603100c003000352070000c1d10381e000302500300072603400c0d0752041c3d40d40d4002890009200c0c41101403c03011200300220720040744410034858958403040c0001c0c40b51181001c0000011040300c0c1550708c05880042d41c00c0d8248042850703445042810349003410580c44104200b104040041c0c86524204e800140705c92684d5401c8440b01001e00c9400000751070003006000515250708103070740c8140341c1c5048 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 746979946 1250 746978696 746978707
    0x150a0b041503080406090e090d05250b0402182403010f050a0506032103071209050303040515012102060a143601080a0c110706050c010c031e02030606 66
    0x180340a81d1800d5000b1100c84100080401545421240750b40040100c00e550300e1081c03070f0003d0070b15100e10349404804d040080005403188444404e02c6c000c4070502080081d10821112450001c000d101c050300c0903072162442490090b103440c900c0c0302c81403003200400c80400441c500709a041c0c030070940c4a1903665242d5213030005a05401081d02c01d041c80f50b015800c0108030b0303040c400f09041c1010441d0450080ca105000b5140c100c003010352003143d03000070140c5040000c1202e0364001c0c00041c52000f200402c1c50000006100a00c100060981c0000c440c0303540820150f40c0e9002007002d0040d60002000300d5041761800e10015160660150010b00d031513043c59a400b824982c8203c10b50760012607906007808074075041d858000c0c1c02c40c0c07c0c20a034883c56070082400038035860019000c214014442041d0316210000e20a06038441c071183c12510f600002140d400d151201809030481d04803820000c955803800410100c40e82c0300e40600c07003010031100c40c0c901c1281900121800a035000505064106908211 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 746981196 1250 746979946 746979971
    0x20f010f0209100e0102070314010b06030103060903030501050909121e03070504060905040b0f040207061d03090f19151803030302120f0606040b1c020a03050612150a0b04 75
    0x1461003103624894016900e1050500700030205400300c41150821071240d14542540e6000104407066a0f000139a5506180008440074050446a20701c5504400d010000004100c400d4010407401c5219480500c4140e88580030720a407618100d903201050fa105150014500004400902102c000c0600d0705045105448080c85964070903105140080c20005040000c0d0354082c440101622040703405000001815001407040e40410320030520482d0300003001403c0180550100210402c800c1c001c0190801c501101a02c980001c03500500482080c40c5040319894200d01c1d20229100d17034694040d5650401c00d4030740340562030840b03140501801200d440301105e94a0b18a0740150710a41e0050398400e004c50310941c0103d0050074040b8800d001c4c40a01000f60fa40c2c1080c6c1d8180c841c007074202034842e451800081c141c0c0400800c80c2528500c0000c80503c802d40c9904030714400c1e40700340c50012125500d20301250b0b480c2c80c0300e42d60111070450600415160032240d08602c00c5468024004a550b000444 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 746982446 1250 746981196 746981201
    0x3020d050a03141e0f0601020a1106090310050a0f09150c170903030106030e16210b0411090912070209040f060213180e100504080f03160206060609011b03020f01 71
    0x16030306444e02c4000c110b0b58110344c0e01004642d03803014203900400018105080040c2d13031403087e00c90080c1502855030560f10b00380c807810141c0c5d07030b4841c000301121101e105010104c001044c068403099402410091586544c00107801281281580564904095140020401d009103498506034003000038044a094110301e2130000710380104070400207555294900038025048034040c050700307011a0010b881c40010466001003c40441d0320202d914803100900e030f00001003d1109403c0181109403084c213201c11301101c0381c20b0404c809400da840300202d484243c0f03a5550741541c1c0c0500c40e135400c0c0802c00f0300c00505065600c680c00910510303603144c603c10740b0b5450b142607030005103008480d83c124800800400701d6003110311020108207581004140415080603440c1c0e10011648448a500c801c0403c080001c100c2c12980802000d2100c0c80c0ca9081c403090500c41c00b80302c41600320040c0308000c0461010b260030001c6641075141615540c0049038240000040c89610b01d409230154013880b0f07500145000f01b030 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 746983696 1250 746982446 746982451
    0x180406050a0305010e1b0f040e0708030d0213050f090c0d02270301110a0504031e14060a0f0b0904020d0230060a05090723130903031803020d050a0314 66
    0x14800805e1402110340b0203481d00134580703000d00c9641546006188103445099541d20040d000390b8000c102c03101040d80142c5401d040380d01c500c00e903100c000f170002c50a034490742c050704800005411540d00f40b5034034004c00c42d840d2915401a50312160318800715010100c0d00c0010071042e00070381c10243c14560140004940450400b00c00f40340d64030030700c0d4500300900c5c0c288922542c0c0701d043e88a082c200802403500030103034022400001c045030f0081620740b101c1c500f801010000198002007010a4150003160503441d540c2c00e4415100352800c18800742007181c114060b034030400d00003528040c565590f030340801040c0b008540d01603030418821200703901d01008000c1c1e0038000585036918588008020001c052a001b40205010910f603d000e0a00c030b0307951008034001007119620301c01c40303c8440304460104000c1001d1111a54040e0250120708060402ca40000d00024041d860400c0008164404003804400020005005801c51428034480c00c1c0281c0c064080d020340c518001030740f0481050500c820744001e = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 746984946 1250 746983696 746983703
    0x9020a090501030b0a050c0306040c020a0803101e0501020c0108040204141611060f0402150d090b15100c06020d020405300d0e010e060d05070804121103180406050a03 73
    0x1e03400140240100c2c0380240303030804032901e420400351070210654074050201400d514815500e5556441485100304010315055030007000e010b07601d05058035181e81560a03031003900340d929141d8501c460070048488203401201c1c8180c014181030f081c0c01e0011a030801c002002268000d07910401d400344c036042c030300c1c41c648034032122031b800c032421008100c000d0070400549145a09075800f00f003c002400690a40f066002030f4140d501c08940501d244041495018a0510703440c07162906580c02c0600c1908400d00b4020000721908450507542503003407040201c1801030390804074403550841400101540c0c010310b90780c000c2081c01800c1503140c400083d0940703d8a0725407440c4030984004d4a00200b200c2c02c0d141c0400c01200010103110401c4c0c0c5001d420703001c1002030030b41800503200c1110348a0300c1d29003c5845602d0b40c01410001440e201e20041e000341c409803000e942000f8014408035620b405020703403000c100c100c0401142041c0402e41101700320a035150201e5006a00d5000000700d6071a40340303400001e10710 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 746986196 1250 746984946 746984951
    0x318030c020a1202010e0d080c03120a0c05070201020d0809100f0b0a0902030f0106030209030c0a330e1302070501151802091e010309170d11030f0705070609020a09 72
    0x501d004010500b900340d0010040b070140180070400503a080400301242110036a52181a0016800e25101600404002002c40c0c0800030b00c01c841c03003032080390483c825100074101b0042d2142c0410101e6140c020880001d025911400041d04031a020350102640109402c04440d211300d0030b02055400d0302d60381640c135078003603032520303902403403031429682180107410502001c60561609200007400f94130b061140038241034ac00506400a901c4c140700028040102170304812101d03548805041c2142c0071a01e04000d00603100f60f00c2c0281c4074806110a0400003240e548280604480080040d10009040702c1c58000d90708000160000c0c1c0203004a1a19a1921180310142c1e40381030124082540813413000906d092041100d001c0380d40d00c6403c00c40c560040c00560300d40f02e80d49800103074020584a20090941e4102000500c4401000002440c0c0290b00c000c0c2880122100204d449040c003003a907020a0300000807000a14251040c40607010a50188401080742180c83e004100905819000440781c00d4 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 746987446 1250 746986196 746986217
    0x29121302030d0f17060a0e0a111602031b06090f03100f0203180d0206070305061201060b0408120309071202030709020f041d07090b0d0605030718050f04031e031803 72
    0x250031941100480800d10f0348400145481d8000030703100c4145007d0810051450004101a00c803968002e110002041400755500d14072658517800c01900c40350220312030301c500c40c5071307107901c0b80c1c0004407008030740f1702400940c1000411800c104048000e01c601303581502c80c103018281000d0443c091a1a040c0281d0401030b030720300389880c2c44814240e60101d032a10340c2d4001c582940341c2c55030004005900c00b55500d000521901d40d080001d0301c1ca02040c450348001d60800c80e000c6140d00440303000300b089800c000122056118a4810901c150200f2141c00c82c3c2c1c0c0c3c000c1c1c9001c2110840c62030800c140244000c0650b1421a1200d10040407078110818503001d800e0042030500580500c503424a0b0250b005800750006441c2503900181809040d00400200342c0c0007145a00204200b030304803201500008081c0d88403d80c4610180da14941c0030f40b03102136110f0030680491203000742201d4031400f40e5010354546100c01000d00d4032a06d0242c240061408040da00c039091000d050505900d900090b111380d4841c2141e5 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 746988696 1250 746987446 746987477
    0x70509040516080106080f0408031302181017070b0304020d150b03121c0c090522150e220b090607033c02040f0b0429121302030d 57
    0x28401600071106124002d01132082a241c0302c1f80c0654010380c04442c450340c0fa0f4824455201c03064081400079007003104100400070781102c0c1009644a0302441c040c40060b29a10400e15250569011880215801c4500240421100c080041d64400d0001e01f44103503100f4107643d50070b080304617903a181c003529a862142c41d416180a201001c0c916410107411418440005507520070080354015a10729030350785a0300c0700b10752400b0700410002000b0052100740015848440d0070307801218000c080114504e000d80d9001c0d40090700f8000c5041d19840807580c40c003a51034103030031503446001d0000b20220000140c1250b00180700349405900c03e0342114050700f0181800400038082e1000c140d041401d500070759030030441600d400720301c0300e41e1105000980c8000b2409900c00c00300a200b6500202221880e00f400800e412202c0e00c018001c48151016004207007118241a020308003945102c040d200c00c0407c5544d00b90840301c641d1a421580340c9210015800071070b030000e49804090b91030100865080b01d8140c001 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 746989946 1250 746988696 746988707
    0x8030d0605030a020901090506120106060e0a080a0305250c12110d1205070f1e21020706030b060c010528060308090d140a0f140313090203070509040516 67
    0x10241036006041e00c0700703c1e03400104241c01c1401107030364842e540d00000f82c00346d0344c2d00010b400074210180200308054440d00028280001540c402d0701810ba402070004001c0c00c00035248402c290142d4505050014607105010015007030103840549511a80e14013011520000000c402080d40780740f807030800d410030314203c410703603035050092840f071504056204003003054941c45040a01c0076103040c40d526003283c5821440860414002f0706007210f4501040104007040b03040d2019036024407481c6440100a0301d0120280321098050001600701c51700400045000e80c1001c1100c440050400d4104002c04001e22300710f440858030048140800804502d0110031024040d98044208800740803030381c01c64807486840c0c45601d0000d03000340c100342e0800003030100c04600304400c0d14042043d500f03d24182d0501c1d6000e40808030041c1c83e99055203a12815004002003100c4030900c2c0035031140c460a2401c05d01b20300941000301900103206042103440020b944d144a0075103e84160703500240380325a2440000c08 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 746991196 1250 746989946 746989949
    0xc12020f04150e061c1a060303031603200a080f060d020904122f06010f060e0d05011b080f060d021c0c0b0f120c090105040e0405011508030d06 63
    0x8510b00400342140301c100480000030b44190900d180c8440c1c40d40c102060a0540072400e00c11a101000d424508210300043e86010901407404980210b4540c0020181c40344415503201d003403074003c841407480082c041c1d000100f110340c040c01420740d01c8402110200716a40400441c1000426010410040c401d030001b0701500640d00350760300c0401600c00c1e400f040c10700703801400c040c02c2c01100d080611800e503c01c04514a120000b0480f10301c40c0c1050209100c40b0f01c000074251105401603400200d091340700503c0000c01c1311701960300c0781c036003a42400501c0081458000e068a0720b5403200c0a04160300980307001890001d10380e964444980c6030500c090f607080c500180a40e03101c0c1000c0340c04400560741e9a001d0700203c4840322048080441d0a1600b0f5031055016071184010300804100c0100448610015114140c03001c0d0107100355a503401d42e07140c404d00c18120b840e0301046007072205000c01d80c1d501c0003072076009100d0b10000a01c8501c600020310115183d03481403031254000601d04050384850301a1a0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 746992446 1250 746991196 746991199
    0x13110c0f070b040308030a090602131805100308034b2e0f0312181503020d110313031403060a0306020726040914040f0b0c070c12020f 59
    0x7001c2c10900d5801a074426480054206800440072850000c0aa4405403030164011000c40d912507408102640700d121611420808500b0340c148031815071864010940300d50709a59042c0c0c0b503d4115640c0030000d0304040c00858084141941c4071070300300d4041c898040e650b0020320141000130201c00700c907003040c0030f48001008203008190070b00540303e44400713a030841c071411320000c0c0c400b81c070408040c1d241c0300220740c1c030079030680400400001c1030252a030302c00040340c170f9a55102100c0d12461341e005480b1706040d02c038441c100e4035540c0620701000e12130ba02602281400b01e00110f00b143c007000c4e106810703800c11b403030011003010000e039007000f09600502c419161036080320383d0600314908a80041c0f5121503911019004540006001c0100584800e00d148025605050310114203495664090a90030174003030000e1740d42c81c01c407404001e08007407110a88101da00112400d0703164940d1f550215a0301d0080c4c0248668841446410005540c2003609000341601489902d8a07030014010000b0090001c1e0210703 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 746993696 1250 746992446 746992453
    0x10806160c0c0b0304051002210f04030e0402031009060b0a020d02070807051005090d0b040c06020f0c0d03022407080a090f020d080d0212090601080c060d0b13110c0f 73
    0x1000001c02d424140012255040c094588982d103904116003014080c20903008075500c0020b00a40c0888801191000251344010302403180d038a03c80203140542050302c014000c00c511081111051900e81c00442e4007a41d511449811155a0003441d01942d200f600a034003001d0f000b00d00598699810071035048150100e10003030044034904a422511046180039550040705406148545540203d0448182c0c12010f400b000c03006483d070410710f070041c000343c2d02154885a1518000f4000b8070014907040c996004030060031008805800b0003181d81d290314412020760054034414604070100546510100c06140c1d150203da10704280014000c032401000c035510380b480e059210380414410f50450310626030554008000e1821030400000c28040e040c100d1060500009480d0419529040c1c1c403805105000300301c0301e00780d03261700c1c0050701e030700c54007007040c0e000350341400845000c0d9100c2e009a21040b078081d01c2225502c8204000d0002d0381c600d01e40e01469508002100c3c3d07441041040004c4039000042e015 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 746994946 1250 746993696 746993717
    0x3080405040513170f07120e031e1b0a080715020c0405131410150e09120319020c1605011d09011403010b03100501050316052b0b01080616 61
    0x140c08040707a01c03c5908040004c0840c078141012207103c00c652007181c000800300c00745501c007807000f4126100824414007038052148040700030000b1020394401488800043c01100c4501d00314000940300c011140b95100200340c40024200c01c003485403030041c2c050070720300340310b104055507001e46001c0d40140c51600071464401004944880c080340c00070629809401c0c450fa4074606800c1d54500f40ca117100101c411490400400461262048401c08541c0c18082071401a607420043c1500c0e040401e65803d9065000c100250420041e80120740030300b204045d0040c20690300c1c104d540c0c50000009180340d941e0f056a0400d004540e0090300b500100301c803c0041c86c03403002c804400b00f041442c0601c641d0354005800c2105006035074081d000500f42c164041c0469184564480214010f81401c0c13003403e0090103850710441c1d03c940e14051141c20f9900103807600e00182c0300020285c0e512810201c0035143d4100c4044400e00242100e010903009100760401000d00f810540144285044041c0d41e000611945208 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 746996196 1250 746994946 746994953
    0x618060e090a0515190c020c1201060806040201140403060207080409050c091305060a08060a06030c23090721090b0703020720010504150504080d0e0d060b130603080405040513 77
    0x58481888260807132004240c1c469a10420044000a0328500c9060074843c040a04613400120104256000c5409042401000f100b482c01c880403801103880f1600040c0000780554001c6140c4075106440d1506540340c95500d880f03890072604100b004550900000404012003241802031680002240c0503c502c0c0c00e100030001030009201c09100d0000f42d1b100d80c00200c841e13a4045031140280301600030303541c00c3d02d4040c007610010006400201c6815400c080c0118509400188058402650500562075426030b0000c104000078010150810440001040c500c1c20603a2000c01e0307012141d80902103015021031910f080c0001b0000c26100070144148014004202126440c0380c030703a0448245525003261110049890740315581040d02040140d4990000d219840b100170021501c02105907400b4006081045848103805900c4940c08000f0443c0d1101007181a407094403e03001c020702440d141c171040780d10042910b259600c240e460000108040001e41441e0080b103a000040300b4811603010795996 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 746997446 1250 746996196 746996203
    0x80d020307120e030a15020412082203050d2a050102070b06010320031012031e050304080f0307120c0f021b031906090204061226040b0901030618060e090a05 69
    0x403010740080c55550310300e8403040d2264100c8000d44800c200356214800306042c0100150700100c1038141002020741c1d900c07412f0010b91040015030741d06c0310180012980404040300c002c0c4030001e2000c20f40d00b9420f48a11400c0300070b8100d02c0c0303181c032078030002d80c0b160351605010b58080001030106044c5802e00c0201045210030f03c3d03c0520300481c4018039501c4c0d031107680308810008400c0d003112044400c410314040c145a00030000440c034244c030700d201401024900f801102d681c002030f40c00400e140c100384400c82c1000c000401850b4801c0c0c0b923191000c40f5405541d0b203481510001840d0030082282c1c629941441c40e414801d0001490301f00c403c6101c4040210042551410700b004000b078880c0c2841a007000300819034000390849a0010824070055480d02d00d10100c40c118484100c0d250700405160031091540a80080080c0009250740c41c10189009440c1100341d100052550415030f88040110310440d0b251040000e074158100001600b0782040e100d0110810050042d143e25840f1800c8000041d0002 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 746998696 1250 746997446 746997463
    0x10c0215130302030d09030c05100603080702040e0c1503070f03050903070305090d0c142701031b0f151b0804060f0c0b1503060a180f0507080d020307120e03 69
    0x94110448000382e0500303d041d4000c0c0d03007006800a04040840d0b051541c0700c0d00303454601d4080c005584440032018400822030f00c0390310004041007801c0c0246000351400e80d005201504904d400d50b5141d600762400250f4500c0c2592890340d0882005c0144460300340d110170180d800c4016400d0401c05070a00c81c0c000d42d6a03005100c4020204080010140404e840c1e0203910204254420b044d854481c0d01c48101d0b0341031211070300f200e41c05034889402c1d401c80005a0005120202e08800c400b062507407d42d2030b1400b1905010221103a582006800080c00803208001000102021203042010b4010414024425014111000705444d918602107021410013001c030740464070319041c00090000c00342e034284c2e1064603018016180d6402c1030108500190070408070012072508906451190b580c2e101c4a601715032200c0d0310703814807415041580c4001a038607002c40011078041c4040b20809503903040e006180030303004080f0100580002c9008000c00411f5582c040c81036030705091a401880404010990b00c0014 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 746999946 1250 746998696 746998711
    0x30301050d050111040b0703021603110904080f0f0409060803040b0a0806040b0409050d0e01210209030f0d02161a120402131b09090c0c080307020313120203010c0215 73
    0x7188604001c210b030940c008014882c03c507411584490743c942c405402a080144142c0140c018000b5a803003d8088903105010350307900104142007240c440d8184144030744010021141c0e0f0348100406480c0c400c0b610043c0803021206440159210705011030748080c2c3c0c0c4075a204100c180c0c0144828060382e4400c4040e02d20342d010324640024150340b444000b801034448402d240782c00074030740719045050000103d1004105140e540380c0d6054080500011260054817002c40304c10300340307402904e012150b407a800911140a004080740d41d03501484041b2410061a5406440503034440c0403140241205c81c04078000a1008003000c04c064101d040080030188248c41141d9404501e520002e821540c03810705010b60411040c0c81008044064110840c01d010120324800c00305140140c0010400200c2c0076040007408a659071910000e1946d4807018141c101800040035400184805600003070303542108001030100c0c0e140d11510041d580180360848624800c00d1007103400003104281c074030741400d0080780c201c5403 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 747001196 1250 746999946 746999959
    0x105030303240a09060905060901050a0603020c011e0501061704080304021c0b0906070e03010605031b060714060a0b0d051f0f181b03050c0f060408060a09060b040e03030105 76
    0x202d034040c0c01d00b4403685030840e900c440703020404100c0e02607643c010700a5400c0130724200300c1c41d100c400c20450403080910400d0341c031084500301406900d10a0f0040c0070320250075800131400c03401d0700103a4a900040c9030f41c900c0380140d440d03004000599201050b40d02c048003181240b40c860520b1745034124184002040079008140d040703c140f11004400303405031079451304081c800b82030f42020110251998410ba54003800904160305100940c5018440e5400311070000780105030f03908492100790403171004012196880300007400410003145103540400184410280070380318074030b070002205086801c070f42186030042d4000e01116001583c0001e40158280026083c8000b0b608081400b030040d01040c031000f01c54908080c1d001000c1048044034070480c51080313526060380b41e03409200c0086241e036488060300b0b0340d00c000c0410780c0038200404801840350014107424a02629010329a10709101510703012101907851141c3c00501103d4403401505075812141841003119842899999002c10300406110f40c5 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 747002446 1250 747001196 747001231
    0x6011e0f030f0627050c10020d0815040b06070503070b0c0702060a0e0613081e01020a0801140102282105040512070909050a12020d080a02160501020d06031104050105030303 76
    0xa0560413850b480c0902d01d82126100c440a25149495202880241c2d0050303940d0b0103500c1d400c50011450003240c0000c2d40c0d46030103507581e6500721145044617400d0300da006665800b4400b102d8590400030322066015800a6640b0445480d0900046c00c008100703d0744110184800070041c0d982d43c048a0100b0401d1a1500001d010400010300500c00c40e005140400405074002500340d43c081800c05690001c41d001c110307910b41e0540154280d100e54580f03240000d03d401c0c0107218030f1640300314911388140d042c4125442c8a0b07184007001d0790020b10140600050303050101200070428004100030103907500841798240401543d00140980c00b032802044d11070390144030311a00741e880803c140f100402c0d00c594180070b07000032400c009480b42a5014151005581007041881140c00050380c0c58078101c0a588003070b4030384c0d10881400000e400035001e200c401406000040e0106809001504801e820f00301c0000c3c0c04e86c510300c2c012051205440d643c0380141d0270080108025a0003105403a445000441e01b80e4215 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 747003696 1250 747002446 747002471
    0x50a0e0108151e06042304020a0c02190302041e05150f01121b0804031103070f141e0d0e180703020304020a031a0402040501170d11070806011e0f030f06 67
    0xf0038030300ca07000350803503808103001800703103002090700100040c60b07100c140702d400200e810720060b403143d0320002000c250a0308408005081604000110039011008031020307030703120350003d07064404000c82d0443c0c04c0c41c09080442c081010b44155a0005807500e140c1c81e803c1d9040b03010490807989290458188010000041b5095160390021030700c1e02e01d0303a00d0300780c000400000043d1803090150b809034005000607080c5035a051001003268807a641011030034485e00d00c0c40d6034034001440d00e840a60402e00a010350480c0111a6028484088018a020304a0511070300303001000180c034802c2c0765201d0b4205540c1400c1c3d0807602281c068014400e450090780c6c036911800800c0d2241241e9200410400c203017046843c850b24883c0895004a108850a100e1a41e84000b0400020308400f201080d541044c02d0b801d44040c02000f103104500c540c00180d0708c016603110f4800d0f0401400741d102c2c0040d5500d426041c400190100384081c042c0c02242c0034a1002400c2d521288502842010014840740c0c2d580040341d0341 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 747004946 1250 747003696 747003739
    0x20f1011070f050a050d111b040f0203250914060904060302120d1209050d0806011803080306240403060f0b0a1403010c0201021819080a03050a0e010815 67
    0x15500900380b0501e4405620b0300980c1c9422151017603d01e4050b5450741d0901c2ea00c1000d045d28603c3c0300728020a0342c40d580b03840190620001c042c007075900a80c1c46490a8044180b800039612560103020700100244454019802540c019070185c01088901e24090105040b464070020390b64800303803600e540350f0407510041801808260000382d444500b10192940f0070a00090124103604660789031030659000e05090020740d09004d0000b4041e4018006c605500c0d40b2a40c051070307002c131051400c0c0740c07902c1114413000110b0010b500142c503041c400000f0010345003810604100d0117506a0044500c00d40c3c100a460002c1c01940001002d10381c03640d1082d00c034425290000c101104000b0b005064a60750750070181d003040011880b0380e00079420310b010422283d00600c00d44d807100103020700102000702d1101c20040040c0d881480c01503035a1002c0c07004a100300781004030071040c91080d100c0c5941c80c0040364000e002e1000d074800d0030341000f02600410232a80402000c50800a90a40d00000d060202501c1c100d403 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 747006196 1250 747004946 747004957
    0x604060b01082a0c06010f08011503020d030804060b150c0c0a030b0106080403030f060e0402040f05060906131b030b0a1205100515030a030207140607020901120f0f0b0703050106020f1011 82
    0x1c040c45405c1c0080390881b107800b4010121071045000300090344c1c00c500440c901000500c03010354000d48081d242c1d40468026101a5407240c4100d8000130401c11100008002c2c241342078001c03241070800b04904490302007c005a4228910445011511070320303551310000d03400c1c81401390070200300780180480c00305802608445440c0320f0701c40080c05907030b40f81e03a03141c5042c000407203080c6e11803814490f02c00465011880b4142c043d00c0060003c03282651950180145118003140114030955140d080d4400180c0c05036281000052680c1c0c00b0604880300c0c003c00113514095000101d501400c0387d980000110700082d20300d114000c90501003119035882d240c8142e0a942d510031b04e03406002e0541d0400070154040340d800305a1360410301d0795400c043c01205003c1c11340a04107000350004409001400030740701200f40300740268403c0300044494000d55844d03804800040c0c03021100d0840c0364003400740b00c0f50580905805000e00d40b004000300e00750301d4402a03440352004090001145d0740c1840084078481c0d00115031 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 747007446 1250 747006196 747006217
    0x414060414160f02120a020c0907050c0d050307111f060b0a020601031e022e050c0601141507080c07090b0d0311120a0908010e07060504090b0109170604060b01082a 72
    0x5886d951410030203529014415a114801c07480500080e2440d03001c4d5060311810404070008103140e0724001400e0b9040c0d030001d0844018041000c800780082c081c00c10110144084000d0849e04541141c41480140c94451304803482c00541800103601050f8002803850441740c00040d41c25071742107041d14011000a100502039085030551200b0a400010340441c0c0030018007880ca403c152050115044400340680e081c01c0300b0740c0d04050010015500d2281e440801100001e05600101d007000c40008546e078811301c401c603106c3d280030401c0043c0e002d050049400a02030700a05001781c10030100007c800005841006080c0034584650800180081180d40000414040344607074802072007802400907010740c80b454180350300306001480301960100e00c103070441d0203644601f17040505000807913000c4c0444001503130401001500008020201408412036526028090015030500381400c2094030050740b5220f045c00100d90074004c2c00da0344803802030080000b0074440944440c46a0882a06209072032580 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 747008696 1250 747007446 747007483
    0x7031b0b010803071b1203050c0111030f04051005010605040b0c1c03240308090907020c220509070f0b07060b030609011515020307150b0414060414160f02 68
    0x2c20b40a03000002003040314050b04d02c0c80309201466001400c848980e0094200c00b00c5c91b61282000607005201400004075940c002040041a140c0340c045940c204482c000c482040d807905100c280300080c4174500800410b01d409101030b41c10008003a10b40e00c128890854819030005050010784010320050710030255061814501c074410310070080281031070307100045000500c448800d201000b000c42001c01c40e9803240e032441c14500810100210318000a0980095000740c0b10010007596424940e040d4003544403280d04144901107a4080417110001d20038003450703100c00000d21821300900d00401c2100d0030941c0c1d103981d40519180c1039014002980311306406109000500500d0306044d04241c00c41410b80e08114525a62204140e03401c154013101240980c004106c28000300fa4400341048002c000d82e1001300341d488258020030210f52407030b10180201042071050000510f018012110003c1903200032901c0d5081c4505100c2c0e22500c080440000e0018640640480a0007070041c1d28002d80201540c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 747009946 1250 747008696 747008699
    0x80f15060c070312120e070b0c070305070b13060806011d040209060f0414011e050d0e0f01150519050907021609020d060e0c0d151502070905090c0607031b0b01 70
    0x300790310411307640c5100b000c036900389078102056605d80710304881003d46400410721280340c000c00c80780581c092504658640980d81010000c9841005220001c01e202c080c0c040e41d60403242d0b036212050f0a5078201c0001c1290700801c0c04140c1e039110602c0c0d41150100312408a18050110001c0c00a11800ea40c054001c0c1c000b26500024150b864054011620804000d04150229000441c0c1220f1001d41c0c0c5001d11200c0341e5010604d510a6015000c1c540802e0030008400c2c4107024243d1415050341c0714002d1981d11909042d900022a01036900280703070a94908500449450120105101c00d0040d18020504840021070091081245180e0700c070b4003105003040691600c180001940c0003442c448402030a003840082e03a440b100d0031140c07294103002c00c1141450320800101d03000d4054014022010f0103c8000400d9a01441001140c0c1c61920f4000b00b40303080c03800002e1016a41e008100a10f02e4110700709001e04c640b104011500507590620342540c407010b40900c102d815828080c0054510b4008000 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 747011196 1250 747009946 747009953
    0x10f020c1909111c0605090c0d110f130801230415090c06300902030c0603160206060a0e1f120b15090c2704020703020c010807080f15060c0703 63
    0x5103401d6200c000718450103000540d0000a035002403090a40103521040000c03442200c00015007520044038001060324a0403540028003904a5800500e01ea200040d14cd041c0072485080341c001800b20714020b100096003500d0640701c514505411800031094400090104907031518013038003002c80c1c20001c014040d0b10b8184844100390714050400031401030305000d182034403081c4243d03840c01503038003580b040d80c400154540098a00c080040380c02d84501007100c0c03056a60203000c0c6201c0d60b03031581580410b40c20350000030300e0404090076a6000c1c1c409900103028000c0c4100c403190b071000b41100200030000d0b0013043c240c20303109503034490f040450703000c032458080201d900803a034080c203c9007091004100c002000c100c0318000645009424071420004170610130b03012888081c00d001e16041070341100b10a40c020805a91004c0c5085005070040d001306c200f15a0000350094000b51545014401791803c44494994941c0c00386c540c0c0714030001001e22100f00d40d125021112000480300c1515913556030fa19 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 747012446 1250 747011196 747011231
    0xc050301050312162010110c010912030503060102070b0c011b1b1506030c0e040b010b070b071803020409150e2103061f020307060b010f020c1909 64
    0x40c4074031901403070900c42e248128400a41d000a042c002d220080e07202240c1d10030b008007070a40507941c42d582c0200d04448440d0382d00e18104004281d19190b15a040c079110045505008e54481e0702c03414003d203058103201c00f0b140407580e43c2915070f160920954030f450f040e0043c1c1c50501d0540c00851007410003c0d50741e445410641225000c3d8441c4484075041c0001c0365416101200745596070041c100c0c3d140c0007c408108140540001c0444444000038455140c0d1038120806510360080e403e035098100504c801c20203010f01ea40c0c010a11464030302c0c1010890b98642d200c0000c003404001c1002203030a40e0020000a2130102401950300034820010104a49080000d510f80c1c09a0420524505101400c1520780850b80b8030f1400c840f00107201d0000042240381300d81da04007510300d9411202e0206048045001a4188040c0d035415130019a1500c03000d107440000e4403c9607480c0d9040240c50201c00c640642c0016886446000865540fa042d0107190340c0e104007401d46030701c969900b900f4032a40e001c00c169200c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 747013696 1250 747012446 747012449
    0xe0c07020901051008040b0c0c030d0b0901060314040f1703180607110a061d01090807060b010507020f061602210f0102070b280c0314060d0b07030b03100c050301 71
    0x98448603000ea03a10f60801503070701182400300c40825110000900051907203402c15510000713505859003001006801c061854024180038400c0b0340d83d41541016030b20b0018003403401041e0503e0144020f4882800b100343c4860003130001030100344c680c442c801c10031015002400c0d56079000b419003034482c680711030510684d440510b2801d980c1d01903a00407070703c041c0c840e80c004280c51440d500140001c030025038a48005103c0c450090208660884504c0240038081c055030804c41e0158142e0307074030f40d1380c181800002c071a20b8500ca60b0500008000c8400143c40e103003030714810f1910444001e40c60b42040e00c4501510016110300075403101c80b02c0e04481c0c4c941d15455202100c15401d50480f00c800c130088149501700c0c801c00801070003203051040081c400640d0344840742c907841454610015032580100b07210341a80d00c658012030109482d031218070030700d007920038a1a174020811121045049910745030f030180642d001d001d1104050300c90300d9000054a00b049403420740312031088108800c841030703d8000d015070000e = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 747014946 1250 747013696 747013699
    0x1b010906022104031d0114070b01080714012003070c081e060906060f060f1306080601020a0f02040c2105070314010e060d034d0309190e0c0702 63
    0x1001c40700007a2018030b000c1d280308075450384a91201c2201c01d0030704040320746a03106441c10418124041845c5c81c6809020f000581d00c00e80313240e43c240d410100c1c01030800901ea0480d4a2611282d0343d1031025a034030481205008014542100c20060308803001801e500c669080036200d085031100008070300400140154103e40c0750050080d950005034455500c50b4819070724901a98400c1011070107915000c480348601d103800070320103443c0c100e245414035035a8101080306210108442810404c0c5a0040e040703e500003c00d00c0136100d100301540d07401400021611020380201da42e92082002030380a840b1030290f0881584040c1c6c420f410b000801400341808884540000e41089013540d401402c074800c040c1a90307400301900542d540d8002c144a56018442001e50811081100f42059940c403070301411904140c80911a080048514440b4200a072004c40d40d4013400d04a403410a40034004001d03500742c2c040c2195001005200d071001090811980c1c0c204a100200310010710654085c00b40042103010320 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 747016196 1250 747014946 747014977
    0x2a09040e0a050f120d05071e020d03050c0304030f03110d1107170c0703121e0e2d04020318150a180b01170703050f07050103060b0f0702061b01090602 66
    0xb1684585440c1d034544d603403c604c0340d8410312281c0440c1c0304a8000c260f02c074a1034607004070480c40407001d050840a12000d1840980c1001110400712641401384641c000c0380300820524605241d9001031118854194040801d40e503120024601503001040318504110010b045c01540c000101c0d944040d44a00012180d0000c5c81028080100254060f42d0766403500d20060007160345982c9541d14a00c480c6030541007000368481a200703441a0045841002c2c0403169102c4105e648900309100100590400700003c00c1d030b059904c00c140e08644074090100000c15600542c494481a0000e008250410300d44003107030041c0c00340303030482401d21150a403160280d44802e101190261074070340b000b4112010040c205c80c00714001030014402e400d8840200300144011201550341e6038840c24203000222321005031a81000c00308000ba507134140a150050203801307442c10b01c0c044448411400303510402d20000e001e4070010030268240300b440c40041420ba800c900083c80b1660052410000035800200345500004 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 747017446 1250 747016196 747016213
    0x30c030b030d090617060d0807050c13060e060312041202190e060a1a0a200a06020301140102030412140f03030901150602210c03070f05010b0a0e2a09040e0a05 70
    0x59503400c140074940c054004c400080c01d80e203d008d01d0354001003080d501441800c40c0d40c1c074161981d443c4d41c1138040402e000010302e1404c1103c1070700d1110020301110320940c400041d110b40400c28004482c202c51540c2c4582010001c1403010424004070452500e0040d4031900001628400c140441792050760129441d41d140c945030034848041082ca0b503c0d80a148038140720b000211070207180124540001c401400280c82c0c08100c6851404501d244103c85142e00400100441c8149240d8408192800d0020b10b083c641018107588850202e120040c0c071a2400000c01510054180f10300052120b03400700381c0e6500e140040d0403034040c0c05e414203821000791a003100000c5180c400328401d600c0b000c082d012801201056050170b092500116490542130000304001c400180b0802c0515030030030720820012810315100c0040000120440d4060110301c012003041205071110031640104229210703981070a050742001c842803c502a49054a801500d4101c1908043c880021100300b824400d0341100c140c1c1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 747018696 1250 747017446 747017477
    0x180601151e090503010f09030e06070503190e0904031805060703080f0c0412050a06141e0a020403022e020106050f010e040f051314031801030c030b030d0906 69
    0x505a0394041000441c07905481c04006521400e03000c15440a14100c02190f0316280000d00b11501603405184450f0f1798550082010b811a40045c411401224010300f06001a00c0310303504c91007145451459007051000d4440e08602801c100d030300a070005444c0c50a00d01d010701e001781801301a4402d851168042c010006641c1c90281e08941405905550f0819181c0313681000d05140301002d40b064002503801e10020507140c14050090101c01e010300c1c000d0411f2007080c2020303400c80300002e416049c0a010082008003d00301d035050100070701081002c0b6400d969032001250020701a40d040258040c91604000b030000e01580c02120f00841740046880602c917000206908940d014450b40e900220400600f2070558004d40e10340200e00c0e409040814041c0d0000c0c21401141e500301d6488500d80520f00c04401401094040d29a103402450015485d1001d802c0000e1031001c20303040b07140c0c1015240c0c040b141d0318501c42c0d00b0800c1070348000b030304132034203801509406419000705000c2c18001981100006518 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 747019946 1250 747018696 747018719
    0x1407020d030c05070812040f050d08030403050f0705061302130506030615040f0f020403030f09050f06030603010f0921020a08040504050c19020115090519020901030e010203180601 79
    0x516600502003100d000295506403000b481c0a0701c00d6419004a49001544c0001840301c5440321049144542d0303030b1420b00d08942014a0720340c00c424007615900d80e401001403a408101e079000340d058203080b44c0360284018084d22500c190300b0010000e005250511507442d401d43c8004540d180f080b18a291480c2181d4091000c60390100d4040340d00d0350040010611450400e4046401014080c0002c1a00055549644140c45171422890038583d80050100281175000d56080d03100c0700070b4940b1150309840d020005450113008102203110b10700c0000400d8035690254000c24602c08411000d020340e510a0800e41c4282d0506140b003c010000440104015440841c0000300c0e0ba600c401c1e03490400f0305143c1800f005001c0203000c0350405070300b005109110002e50101860b400219400030419502a10f211102c05050394003224503d4100400e005001a400285181c00d840c03610005803111400c80040303020b02103c0c024003020b07520000a02c145201c40e8a464015060454225502030b41c0c1c420300180e1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 747021196 1250 747019946 747019957
    0x11e0207110913020415050907080f010e10030b2415190e0a0e040302010c0e030c011107050a060302030a0c0206040302030f0a0207170102031b0307021b0423010614 72
    0x249585590701c2049501d0040c506075000308824041c0c0c041c220356a40440c0844000244402141550241c2008540307400344c6c200e5804003462402040c1c5040a0829515030756041c002c001380007501030001001010910740c010700440c1c01c4160035109043c01ea060080040c505c1a40701500202c0c1c1e21320800c242000000c040300031101035030700ea01d844849104103109000910803102080500e44040c3e1850380e485034410064560716407200745600309460040d0031030b001100c14a0600590b0340c000d00c165507000c146070315054401e090050901c084541c40c00e09151154000c01c0c1d200c0c40c614804122190b1603405188900c254950400c101028110243d9a480c0100c90060050780704001d01c0c400140c000700501070421050041310301031b51702c90450701c24840e00c69598441d541c0d400310810170384001200d24040d01076440300d034071469410300050094448141c10080f501e403000000d4120420340702d03039200301100d88220542c10700385c0b110240c030441820002e1050b000010300149030000e4202c85401142e0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 747022446 1250 747021196 747021203
    0x23060708280509060906090303031819030e061608030c07021203090a230303030408070201030f0606080109091109011d0a050c070f080904090602130b030105100302090a0b0a02011e0207 81
    0x7410040583c0130014503901002070690000c80a1080018540f0700b00083e50042d0032211001d040c120021020b2480c10400300c0344c41520704100060311001c2a000450300701c0488040c7c2d800c0340c0d07980c9a0003100080b03034048000140100d00003c01c2011802604016007041403084a19032418450f20310640d43e24042c070070031345034004201c19080201d2a07040500c00202010f442c019805611074000290071074004650540d502c02c130010702c0404645e13243c0700c2c4624105c90240104112070400034001d0412405011f6880c08070341d40c0148400303010f0300c003004020240c3d005050010660f15a0035046032040030305000c0c0e0b02c240b08500841c1e0843c859002d0503214118921015007454115110441c3e41c404c00c0d081900c64403410041c000107a100c0d4059010001d0040a0241c2c1d06d10302c11080031403249855110154440042c00144078039550450003011014007840d0142e07d9041000014010032810703440303510443d200040075284182c06410004610705060321078489100c0e8845250242d216049004 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 747023696 1250 747022446 747022457
    0x30c0207051e101103030106030609060503011a060c0708011b0206010f080c0607030522080d030606080609100b0408060f06100e090a020d060f051002010c092306070828 74
    0x400c1418181c154107404140da250500c02400c422007440d0441c6e000fa0007040010352100000d004690b414014500200302c00d4000300041885107141800b521805e911881c814000000d0421402d03000300f16400c09044080c0007045030164070500b0b006e036030f0303100108400075002d500700000c1c851b00c10310b100740111048070000e032259824480801c100303070340641000c03000e12009012180c00c031a028112420380e82c01d0000344016036070500c003400b8a0712038240041410035080c5807041c001c142d4440a900d811840681d0450544c0d1990b60031450140002d400450301501d0104d40012100c0c00001c0c0b450194004c0742c41001652200d00074056569003031204400456143c0039080214203000140e03d6004041071001818442c9a010080544440c0d41c081c0b00c0c03511810805000e0341c5040040540c0405460000300f240e0212840064880c00141c440c40900c0c8090302071007142d41c00c0300030f403c1c03041c005c0c0100040d980e140c3c10302d4410020341048441c4181d806084400c801a400781c02c541e84c08285482d2151f = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 747024946 1250 747023696 747023749
    0xd02120a05060109030f052b14090609150d0c02250311062b0606030f02041208070804180501031202060c040b0a050708120105131e020325030c020705 66
    0x3c2005030601910300b2185e920600060f032180488c00d0241449240c5002d01014003401c01e58801442d03d0030301c140168680204200031180c1d40d454004461040e4400c1e5012075000c2c1400100581a009000c40301e00e1f22810200304010300c584c01f1070b030250714000b01c000f119000030416003100356111a40c000240012559030b89010940340540240010b0200d01c6003401550781d80410101d80c0e85030600c01180341c251503080c280403858050091303040d04031804504504003468501503800c0038a24960103000b805000407844140000c0208580c0540120382c10080b01d40c0c0019a24030081009202c2a1130003802441110051440800d0740ca02031071032504c1c403a04140c100660303005103a103e100c20344103001c0108115000254404041c051020702211110706544c907007418445040c002000a4031014946900040250800b00a003110f40105c0c80005031203035684e07d072b007400401c41e0745203686030403480030f03c492191a40348d004405e201015900b038810855403241444201c0842d80016038003881080c42 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 747026196 1250 747024946 747024953
    0x50703020103090f170301081209030c0402071b0b13060512060112060302130504053a1b050d0906170f09151e01120f030e01050d020d02120a0506010903 67
    0x8210f0425000b40c00c0c1c4071a080341d40d030f15024025100d03140030920041c00300c01007151401c00d2010b500c0c00b003600c4480034500960f032000651a66688003d841c8115030100b13013241408511288a007156510482e401c805079100c42004c0302607081402e103032242601c000300c085100c51007141941e2402100c400003144d40d4070ad00780155040700b0039403c0e00022566a460010240e503480c02c4400c8003d028840c000340a041c14100b41b81442d980b000390021940d81d007007014000c2106a81212180480360400c11400c0b82800821215905007500300a02d4014029404060003000b0410300104c07841c2c0e460369001d0a640322000e40d000178580d000310b05000d500c50300044c80d1003414102240e00884d40010b840345000c4403108207019010640d881c0c6402c0c8148040c0f1804041a889010301406203801209008902c3d43c3d60314489035002c105c0103081000d8102d0a98040e4040d10558041c8980c071901591904c0301a0500c50094106c1d2400074452403407100880e00c0e40c1050710030303503025090680d03c070b00d034407030441c1c4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 747027446 1250 747026196 747026201
    0xd0605152a010c030e0d170a0e01020d061502010b0415031b09090308100609030b070f02280312094b0b180c12010608010207121b050703020103 63
    0x10103203000d1081c81004400e9100c00b80300d000030400d6513440c00225180b4500313511389405016020082400650404001e030078905d41e40660780400704090100300135003c054404d0190151664116003141400e00102d1210f01102d450703118500a070303000700b007141d4110f020881a6070a400c401c50a44508a00c1840402d074428580d01443d9408440071040300c1d0345409040407511050700c00d60010700348105210512030030340b00500c003d010601e0600300e11411902c0340c0010940c0584a44103000b00c809401d05468002e2100341500c4851101c0c4101414400204080c1c05030101d5007280068400d224040c1400c0d645d11961240d00d800005030340c2c5140c1042c88083d14960080916000024040f81c2c800c0049172107610f607405100090b0b41182c2d02c840e2842e10000b500130103020b415030101403150351084202c00080c180c81ca00000c4540d800b00c3c040541c01c003030040c400c0e40c2013604a9400010b82c1000d000303007510f41a41d1984980c2e942c6500300800e605c40b40003142c48803801001500008803c1000d58402e4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 747028696 1250 747027446 747027487
    0x60f0703030e1504020a140102030a051612080a0c0203071e030504030b0a0b1203180f0114040f05100519050a0e190806071b0b0903040b0307050d060515 67
    0x281400106010a0b4030250715252951061240400d00d420401003141080c0d00101c0080c400903050042d44150f060003c0e48030f000d040d400c48104000803c4d003215450303290344002c440c41c0c3c12500072502d800301c00e0001020308034219045440035007041e80d4403a5880c400403c50304101d0300002c9041e015455034040680910501c403083d420484203120100c0800c0032f418460740038008482001612444c074105001e18190244403000258205006810343e01ea030011441e5203021040b51002100415240141e50540343c08686031103009010501180900040e82c0752000d0740c10448104410050852044406103e0144140c0300d5100540500d00340e03e0144000c1d0010080900701400401240000b251542131340103007440c00301e26101c50030880071009000081c0c00074030380d02e801140c00b89102030050004025400042505100c60002030b1104401d0050320054000d500d249540c83c20441c40c002e1442d0440012015818542040024649080b5807001c3c810b44044a20746e0600a140911401c03c071301c0c1 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 747029946 1250 747028696 747028703
    0x6050301090c11030f070507050a0303120506130e01091109100303080606210610050c03040e0405010f02030108160501090f2309010f03060b120304050913021c050d0905060f07 77
    0x3c0205601003091010b86801c0807520301454a4040b107040240c0b50031082d40c05207004481942c02400429440103048081c02e600e000049450303100c507000b14a82d01100030003582100e143c502c0e203600042042d003100e88034a0103002d040c4607201600c420060240029541e04001c03c00300c100070000a801800e040754842001030800e420300300076540450806503804000d102c00d65505003001003a00c2d011440442c1d6201d2407070400c0c00d002c0000045a030300d100328060314103060543c1d4002410400f00350010b84858000c3c0c83c06548070b5030741e4800e5903a03420b8640168941c2141440c4045103e52007030101c201290070074041d4078426460403000b84400c101800e20b40c140810881ca01d0a69a10380c45800c50003009040c407040021803940c2007103c1140e20903220580b043c1003401e00300d14031540c001f068400b6180100c0360740300980c039003001107081e1015041d4000d420201000d00003d59542c1c160700d91501c940118107480903c1c800000032605030020740102a840041400b4001e405d000b01009410164030 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 747031196 1250 747029946 747029957
    0x11031c110c1516290910050108031c0b040e061b03041a070e04050c04140418080a090906080106051f0c171209030712020307151503020409050616020706050301090c 72
    0x89001c0042c0c415414050140c01c008a030307a003170004049003040300c585410103a40d01042654105042140c807840b610182641010b1a90503c040301c440d0341d4012840c24800070810080c254001c071855072a000101e6074000035074240031440c66450a00400c0324441c0b0341c82140884a003600c01c140a00b243c4018040004118070003000349541e8039544517042c0984041d40040d0340340d031701d0a089842802d20003c511070045003480c0740c0707101040003100c0c00046d0590020540792074007003041c012500e45850340c2c45045407074101240000c21107810b5000405940d010707540902103d1140d030714690380030f040301034a6000400340a074542c040f4024540d403007903d140f0300c607070700c1c1c038105842661007072481c015214000c1d00d40000420900300400e008240b00090f0042c000355040c2000c07a214013200e000f12280540344181c40e40400c80c0c0401010b003420001e5503004108200c882c501c0e040441e525501181c5003060100d4148080b404103000145810445040e952500d1840c3e083c09201e1010300b0005d401e4109014 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 747032446 1250 747031196 747031223
    0x1e040f09030e0901030816030e181503070e1614071515141e040e0f0c12030412030918020711030606060a05070203010f0c050705070e07050711031c110c1516 69
    0xcad28402c22840c4030070746110203410f60038800341100340c80908400c80e5129a0102c03078200000011a10f2065100416900407803801030f484005032030043c007041c05448080c44c002100360070064141c42d02a0754408040b010002040c285e00503030010300b0369004600703500d01c0c6000c503a003882c03030048820540f00e00464403840c00e007605900030409071201d4400c0b200d803d802c8804071007034401d400c1103003621613401255544210301808103c19241c0c0700740d000d01542d015a804c2d42005043c001c108103801040041c91150745007004200e94002034003c41402c44100c000110f40d06550714001800c4c0d4010400107055500d00b02a0304c00540d0380394003d075400c903055500c803540603000710064401c42c89501000c0c1c442c1559003001c5d2500900b400721a03000884120b11290601c01016800340544080342c0d40f01200050106205000a2030701945403110700c40300620150420080b42d11040c298cc0740718601040307400c2d1000740e000704550847c0c400304001e0035040030300c0312415814006c102c00d20200d0117141c0710048103 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 747033696 1250 747032446 747032449
    0xb01090b09060924120901020a1707020715110613050c130b0d05030405090a090b0103020d060219090f0806011409040c030510050f0a090b0103021e040f09030e0901030816030e 77
    0x2054070b00c004021110105d07580ea07000d41c1c0d0491455005444900852801440302000703860401000341c0005980e400b800050b80550081101102a003020501c00402101c68007004040074110301d01d120700c0740542c1c00815031711060007202508442d40100a41050300b5070300305002c01b0f00c54550000c84c1c4145c0303840000e0f0503074481c5031120042d180114003031942d6504040600012a40141040070301c02d2070280c1103008a50000c200314156a4102c40e1002c0d0354505060000c040c0c012400b42c8006904e00454141c21190446445401c031410706001002d469512a42d503a2200300034030032400e4000d0b40d04410101f520301b60100540c8513101ea03801044650f22030721102e1500801000b2203042940c0d603024004000302c654699580b1041088052203800c1d5560390705010322a040c80001c0c050001c0094100300b8001c44088185108000f500400006110240ca8400361618900540208821725a10f6149042401d61141039035009403d40d854501c18030003051490300e84002c01c0e402c000105038100d207503 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 747034946 1250 747033696 747033739
    0x1030b0613060f2a030e0306070c030f0207030503040b0c0f03030906010509011401200f0d170c0909130f080d050f0a0501150503060d050616030b01090b090609 70
    0x321144003584641600b00300c1c0c040d0014804540740010300103552000c00c144192004c401c041083c1601504c4a885003a01e4207031095684070ba400f0b03615004100070055074544c0074409141c107034082e0fa241340c5088041c080990301c92815000c00307040ea400404c170501100381c4130b0000303000c400c41c000100c0d11030f1078400000c0d50641c0c006440c201200e400c01c1004101c6841c0104080b800340994030000c03c6040c16000010b450160311b4a00123a550000c4040040420000d02603081d809004c1c800b41d510211826400420350036400c05002c104c0c03022007003c41e80d07010991094a20140d40942805102d481c1d00b840300e0710360707a90000700704c45600780f003042030000589000c00b0b411035511007a030105881c2000d00340201441c07002040d03516160701d80300040205848816034282054218104503989450740e101003850105c0a040103031982c414082480b40e4000d01c0c00c1e1007284120b10384d80c2044055119401102c4c500414414800c0350082807041645070b250442c02004007540003000e014281c015403600044 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 747036196 1250 747034946 747034957
    0x150408010c02061005010518041a03010612150207050c1306082d060f010626070f11160510032408011406090408072607110306070c060b01030b06 64
    0x43c1c00900c18440500c400074001c07000350209003451f5043c0200c900700b441942000b401d54074415900c5408801c2d0300160600c003604d0320380f40500280702c2103440781440c1c140f0070000384044441390150b822041d00c0745aa4800d903001170b0790020260424031041000c0000300360091a00807045079480d40700240401041150450141310015884101000d559045003090101600325080f42c01801c104002c2e03044160801c1d040d01c81c0303400d00802523041d43c0c410044d1000c1645413852800700c2c100074440c0c0c050b000180a6441e2000343d40b8120403142d5511010340300c2d06448450308020041c102c040c00a4901070100412140c07681c40c0008000013051160300c244400c02010388203022401c001400066428024075440c20f02044003a503085c03c0410216a8a2000410107090903101040400420010060081040401d0350300410036180d80002c0045a178030010044400c0c5002001d80030070340c107001c03800c180701c3c2095442c0d40101d240c107038803001c018110b10005241019640c847d100540c3c0e072410050407 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 747037446 1250 747036196 747036221
    0x110d020105060f0607031202030a020720040b0303040f030303050a14040b010608160c080a02010603020d03030b0a120206090906011404080601090c0201110703050703030623031002031515040801 85
    0x38003810300d0010300c42980345090b40700d800b48104000b0170000c81d0304015107120980c0064001a03072951038950a80090107240c000414480c0821641c0c5281c44c12161450041802282d08008080c503040805a89208031700c10041400b116110800100f8040d80c856075100700b6000780030850914010481b0f440b0341c0100e40880320000d02c40014000680d01c83c42c41540100d82150030701500300b19000c00b9194201143d402020f21900050010503203100b0742040c1c0082da070262420360841c2052402070068909080403a00941c1c40020004110060211a0384503d401902040c0781281c003200780a400c8500800c0705040c03281a41e0803001d9100000018001030204001400b01da5050040320016124400084c03411603051090122250f00140b003203820302c03603040c141a9950641490107902400c000c2d842a400c248ac02100060410f03420540e8003480700e403c40a0320010450110f80408078002910b0715401c600344030000030740a041803101d19003030b900c81c5003006091a507a481083e0a45a1905196 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 747038696 1250 747037446 747037451
    0x310050a0f0c0c050606030f071703040f26031206010e2e1d010e09041103060118050907180b010c0813030b01080a08030a0b060d0e0f10150509040201110d0201 70
    0xb0f000b4401c0a0102540121302200500640e514205078250b039903c0900541d80840140080c001e50114100200c03401004c0c00e0155008003903641940c400308a001c8400c0408141c5908044a00107001004613442d0b90500d031000882a180c01d070045588a0000392015048910718240c40d0a00b0b09644042c1c0c0e80d400c03072001c0b0400c62003d007440100700b04600858009403144000b01c000c0e86a810600c0b00181200907a810005a0341da42000d55411742000c0e0125054002c0c08008680c8228070320804081c003030102000d00064840748542941d803072052140159941440340800b45e000d003039400502c0b0703900c01498034801244194983c3e1485a110541c2a0f1007155455410000c005c503002100e03004040d0315000c1d0090815a482d200400d100080a07148800c2d1303a2001102143d0751082510302c401c0042c0d10810000b000401e5150b5101c20221902c4910b00c9081c51040c0ca0001501408103c0006440d240b01e03a249404184200f101010300304a042c00341202c2141030303051041103101e5005400340e001 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 747039946 1250 747038696 747038717
    0xd05180d0510141e0403090f080a0309080c01020706030c0507020915032b120e0a0b041104020c19020409140a031b0b13022101050a0c030b0310050a0f0c 67
    0x4410441c1c10001410008182d15801c00c5002c1d5085090b64400340103007910044140c0d590301d41100c1f0050644c000030740003401a40003040728030000480070320311f0348a901c4484500f61509201e0f5600c1c00c40c0d40125006901045041c89018801e401448204007542816424070200b1350000d0800ca9003215140d0740120750184c4101c040c07078100690001c0c010306000c001c040402c0c2e00507195140840500366410320030070381d10001807612107034482c1070b1421911059070326841c041d15040c02e01d840c003034600380d4040202c0746103081d0741c2c0341620032103800c00c2d114030040c010b5182210b110070001d181d00005a80c45a03480c50060003103101145120300c000300d00d0340900020030030b074a0041c1003180c4150b80e02811038880796060340010f0307440180c1c1d90801484500380c40100424400203051064050300445404046401e0010007181508424080c11607000309000f100c85591080741250903000c2c0165160740300800511507081154096608803610a00101d81d04201244581c141e480001d995030018400c54003 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 747041196 1250 747039946 747039973
    0x5012303030c100e0c061303060905150705070308090c1809030f0f1c060518190e030403030801051818071e180509061803090a0305010b1c03020d05180d05 68
    0x107901c0c5038401b260428140000c1441d850a26145400001c10f11903455044205000303042110000009002c19058103d00d002e140041c01600304100460214455a0114849280109483c0c008082c050f145030100303900341d50021602c103805000c1e90602c1c0001c01c0500301040e0b04000900000c25080740c2740303503a83d601c4008007202c81001e280344c020182c41c0c00e1003480503aa4407010502d40138a0b031811010035231590001c0001f23182030301e01c102a130030f49004030081c003008001c0060301c00c0720b01a8494200e10303a89d41050001170094003d58011141c1c0b4000001d411b03840101010160050120880c0d070019198064408904200c8007054481541d01c00c003000107a000681404001e030100b4428042e0f8140140d1160340c1314000b40807140d4404504242000c290400c10a85280b02030041c84141a1940c03402c0490003000510a42c1c0c3c055054201c0000d59010702d030504d008d0b5030782d140d80102401c203c0e0075000c840d1504545510703964900c46440003036030760f941c003a201c0c14801e00500242480185895 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 747042446 1250 747041196 747041203
    0x8010602070906050307030210050c0a060b0a051f0c030903080a031512020a0b0f0d0603060605030c063a051e070c030903080d0207080a08150405012303030c100e 71
    0x50020b800181444000c0c00180c801042210480b54180d400050810400600f03440500401001c5c000521981100009201640e0400404900c0940380f001d00240c407041070143c0c010508440302c10310403504062003d00c0307101d00d442082d030600034500200603944175550241144d004003c0640040d80b40c3c840c000341543c0c0412130f01c0c004c0c524070756080d81d00302556000c0f03280740455110f60a21406d0109000d145e40145104a5080800000c0308105064403464108010465405010300a202d00c01030300143c0c0c10f1400446100c2100c505001c121401d004440480d004200901149005e1002c1c183c0809a40107000c0c06000e100e49640c207587c2140700e80b402c40ca9040b0024200350410484101200200360031000200c10342c0d410810039907480704843c0000d0084c1c07240f45d030010241040000d444444507444007143d40036a02c0c4103840c40240743c21500b0442910405e0049060503403500310301c0c0c0034035a090a11410419006400d0702d0401e69241c0c1c1250900c5040180024416142e0b032840100c43c40c140b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 747043696 1250 747042446 747042449
    0x12040312051608040b09070f18240909020a3b010f06081b070803090607090e060d0203010905011a0a0b1213060e06070309060e0609030a0e18070801060207 68
    0x1104142140319200300101485000780c00580340404c034030080760000324240900b00162a200a0804a82c1d0395400309c506d00002c11010701c1c406620b011240d10f2085c2c0c0d4084c6240041201c00f405000b034900381184803008007600034040360701281070305000400c01136242c10382a1006440e2004074011000d0070019551422403071064001041e0140184583d01c500a9544150350b079605d00b081c0d56071b40f6900c004617001009260406100300105004c030401c0207820055104903210010b5a00a45540800351030380d10040c0145d0b140f911001001800e182082c540030180756000400121310304d04240c0b01c103030071108600401201519201083d0b07100b4140002460020040d26945600d0485103180c009081000504101c051042004040051105d15041801d81444010175100282844400a0002e041d2600c0480d401c3d4203204803a207900380042942485000340c540910b19103012801c00315010b0840d01045076018038101452031001c104004490711480040d11071346015414103002038070b03040e0300703 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 747044946 1250 747043696 747043711
    0xb0a0e01060b16050c062b1b030203042a050102010e0a051902130c021006081c0503070c080301081b09040c0506130806330d0b04081204031205 63
    0x41c00002c00c40c000c440c00468840b418a240b40d9064405640b5040341060200c0c90500d0340041c0100c2e140300c9032500c403090110b880c0741580c0042180c00c4038022107402d403640c07170015614904180b655103000500030380080d60f01c98410150200c40c41443c2a10450070360120703801c0c1200482182d810b200725602445200035101c2098010f0034500b8040e62000d41e0307080000c0c800c00d04442c540400c4021520381c1c006064441866580c10301508076192400ad55070080440000e03030140c00e100d000a88a500440d022403086060907004d801c4015520717040c0d8156201030100c3c400c000b203400501011407014000745010300800d5005c3d1480c05003071589416402d03004503006c0c3c800d103c440c0511000035050384e02d040c01c07110261881c1d602c031040584007140e034400540c00b151050007164200b124000c9100008110b01c8100380e62190b14202c04010343c010141c1080541c0e4000b00c00c6c803440380200f4010305100b030388503201d483c40c1071074041d800c0703c04684480107950480200f50348641326050b039181802000d500058 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 747046196 1250 747044946 747044951
    0x60a0c051213060608011802040f0b15090103060e010302090a05190f02040806011410030e011e1b1d04020f160309030b0a0209060d15050a06110f0303060d12050d06030b0a0e01 77
    0x88206c00d800d8500c0003040c000303102706e903107085c091441c1110340c0010441040c024650003084004d8446200c0684c0220542030000740f9181002c5240c111981c80941030f030380c015180703456540d2000d151100a16002d006515041210050025241034078040c0c1e000d080500100582c8403460010003d00d0640180c000b044000c1c0c0d0000d6201c4140c503031444107801d8102b0380c80d022560910b401e2441c0d004241c1c0c460b04d00203001c08103101c4540d14007a0340001e1030b02111000f01100e0410500e41c11940b40c014540c0e20740440e0b581413008103041ca069000307010b146d00522901840c2450700c95003030401a500860840210302962820010711001440040e84121500410343c0b4040d044400500a84590120880d80d141c0d40c03500480705003a03154032280030302006040450300585410014007050151110b00f44c00f03104e1030482d0300c030143d03001c002d4034050f01025004242048050303489070f040d441020740c008200581803000550103092170098400650181c8820721142c141101c840c0305454807034154091603070 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 747047446 1250 747046196 747046211
    0x304030c0e01050d031803020d0c081e07051216031a010906060903060f02070f030201050a0c020a0b0708040807060614040f02030f0708090a0204020d1d0a05060a0c05121306060801 79
    0x1213840308041c50f130a07414130303000c0000502a80413100c0d48905800c0650460f07118a401c0b030401015210000c00d4070026821140a036803010f54900d16075285140708001c5402425041015090000d5811050032200b020b030f88480d44003d402050640c0182e1050716805000840300914542c00304405000d440d400c4014440503003070a2000d05898050300c801016a035030780098420501d40f0303034103543c1d0a82c4d102c50301c03200441301414002e001e850140d82e00a407161600d08a0142c3c1da000181c040009603000c08104c0c681d03070752203900ba660b002c0014401d4905141c01c01043d030001b00c0c00e01c110030180c243c408440140300c00c1c0100740022111b02140e81e000c440d2040042c400303034110aa62690303011109140c0201140d890010060030035901000003900103001040b421034641f140d81010720b007a8654941d411440c0001c400050340d403c00f04001030728030340040012400c0e88000d600001100700c0a82800782c5070040705c101d50140e5910413a82c000443c10683c015030700f0403d4038040e620061040e80005d20250703 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 747048696 1250 747047446 747047449
    0x30703050a030806010c140d030f0b09060909011b02061f060203180a08070306020702040b0303163e120c03100b132c072102041d0304030c0e0105 64
    0x240007a100207010311141c903000590680c4528822101d483e03100f43c803410b440c4099408140d032440740700d480d00b01090800100d18a400800d21820303000e88001001c0102d140c4410f014800001d5011300400015501c8070720080f40e030700441000e01c007034402583c010070b400d1800c84007103d00d00c414403202c0540c4070070701135041050b9580017003074035029031440b10080c51010132240042c2c0d07800641e80c002d14060098040000a000c0c195000d004011300a403420710004042c20101038481c0714100c1200c40002403a9a01400b185041c4c0703260500d006200e02c12015103080040202e085000d154a484400e0481181d8640c43e08210111002c44040540200503110100c80000c1d1030f50040101005040d50f1105480501e6554a46410780c641c50481c040152801170301e01c0b082c3d11101d400c40800da0304941c00000f8540040001c00030222003030213001d8004003081c103502003030f034070310a1000b0b90b030140d08c5244601050400000300c03051b81962600450383e9924502e00401c04c46265403083c66000c3d144801046070303 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 747049946 1250 747048696 747048703
    0xc070809010f20010e0c0a0303050301061b0203190201030f060f33020307051b010c060209030f0708010b010314150d15051306060b09010c0206030a140a140603070305 73
    0x422800d0801c2000c164491000301d0f00c0001040e507200c945803240325101c820541c10f50042d9040c1000d00291609a2400c0c018042040210f00c00140081c0040004015281c8244040c4102010001000d44008504e4000030b01d03041d11407103d00d12a20100d0080e40c1103603010310480508500e140001d000107850901854800c2e80a80315402d4001ca110301090545010321190049250194499501000200c1d0000307690750817140c8111518400e4a004039003e05260101c0340900c4030580d24070121607140c0c0d41d41c00281d0880e145441c3c052040a00504200b01d05200300d030302a02c170401c00000c1d40d1503160001010b49003441d294150801c1400240f00e61001d0340d4a0214401805580c600300c040b140b890700c81d8603001c400d01600d8500745020305115051140d22007080c8064050103050140326201c0c990400c2900c02c402d81180400c2c40c0c400328100601700b4802540d40800600350020b20842c001d00603074542c4a085480e155500c0c0c1d601d0907042d008110018150700400c0503001003440504640e6400d64 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 747051196 1250 747049946 747049957
    0x51302060307053f191e0c0807140406090b07030e0d0807060f0c05030a1509020d06080f03040b1c151205010605010206090316060b04020f03040b0c0708 67
    0x2403800040010325003801003080300c4e15003a036003101800c01401ca1180f0400441d5039003140070920b0b0071040c4162904c225407201d134050416203090300c52051050340e03110014002c5100b40c07174011858100342075052180f4418111481102c0c0c0b501c00032450100340080c600c0a2080c01000501c00510060181950000e03040c0c0544100003c1c140d6030b80441e040650302100180c0310682e005071003003258410407007000080c3c24580c0c400c2605111105001c0b41ca142540c0c0c5614599000a000744000303908150b160b0800c840000006c014207501c02d407130b030342e00000303913808405103100c519114403007000401c408100785980c118200001d9030900f4200b60400d001881046040301600888050310702d103074a050ba01840c9448011603807244a99070720700e0a140365141a1700300b40c070716510344800003916500100300c052240e030145011307618001400003016144400031405440c40c80d56032090b14030300d49441c8001d01519004e00c81c0181c4a26242c070b040c44285600628200c2082c005002c0200061a01c0080c0e50 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 747052446 1250 747051196 747051199
    0x1030501060f0f1d04051806071e0e0111010c050903070b07020f2407240504170f0909010b070b090a02010c080c190606050a0816090b0d050d02031c051302 68
    0x78100000700b0380003240f41a02c0340115a11920341b070148007807541d042c2e00400d034680a1600340c0710180e40350a000c2d07610714118020b071100e50301c00c95400300f0954410301140e00c281005042030004e0840303580607103003100d01181e080e4010035000035040170245003c01c10b400040c8011031490307103800d0031540803d03180a003c4a1450144a01d020480840d61700304644e03581004000c584262950b0380e504081403130810105c41006800310059040340862a9405078511894115103090464410309070501110390114440d44403184c1d0921514040b65240d002c00c0380205130641c400f544030b0f011818804501400501948440d85c403582c10040149d07084110310b02060740190000d0f0b00e42042401d240d040c16a00442c0c141d10b050034503101000c20a496200d00305a403c140c030350902603611008856940c0c40040c049490f85035218400708400d0040781c0200010041c007508880892010365a01880d0110010000c40581c10114060001c2c0c181c00c0515186aa0880d03424011407c0c00c806400072101e1000d0301a = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 747053696 1250 747052446 747052457
    0x60b09040e030c0f010f0f0c2001090b16022802190504090303090b15060304200306010308180103060620031c050103050c033f041401030501060f0f 65
    0x7125031001401a29010154003055540300c1c861806400c0c002c0251511103d190f074a820400b11001c4414483d4074803040300d03034079002720040c1000b00b81811115002d000445030364031580c00100140c030400040c1c0c001d5018202a504d1007850100c00303424080b0700d42d50306511040e62040c0e4600070015041c80c00d030b12a01075030740e020400355059154491480f9600300c03c0d001070401101d182095130603071048a409000700800402503c41c60300c0c2418400144480d5a4407490500108012030810310044100200c00d10b2050b61100319800482c0c04c0841c243d0007507580310000b06404554803c0911101042c2000346000c000f00d03400c00f03102a1481d180c60f01076841203d42c1ca007800c000e54104100b203c44000b01800c08248440f1428004006400240001c90b418025048010400d0034002448183c506007003c0d14002030030700514146c84039420b092541c4070143c4440c0300c001e4440204004002030002d001c0100d00842d54900003400f6130f681a407142040012040c142e0300525480f6101240850ee2441c10 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 747054946 1250 747053696 747053711
    0xe0a140a021e190608090f010506010921120c0506010e04082209020c0c1810120501061a0a020607020c010909110c0304080303040c06140f0307020f06042301060b0904 73
    0x45443d240001d4a202c62030124520301190310340c1c00c03a03d0280b003215114211102042510b48150070b0343c1054510354080381d02240140002031003c103900c80200490800914000c8094490400707c89110b030303144000c00c100501e52002e02c9802e000684c090035002000312280e041682c0c17604070501c502ba440d100081c640750755060240c918090000300909113010295210319011041ca0385130203940a1944c40790004010400d000700314030942e1446050b00c4414000014984100c0c080951000803048031155a60140850700686090b40c0858443c01c02c00c40030346501000e41c019150900c054112010b643c82500080d0740c0c4e03a03118445100f030301c16004010481403a070150040709070044400b454500d01011070007048460000015500ca0b90103080c07680b844559401d410703900070615440405042c60300304024184003140200541c0c00c007006204550390b9105000320326090a02c180d03000c6505922000c0f2046410004e80400c0303031a10f01c018001c01036945071107400c5200c3d108401460780141c2c0c480d000c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 747056196 1250 747054946 747054949
    0xa030b04170712122004050328470702060402030c040f380a03030903081e070507060210020c1b010e090403020708060a06030b07210e0a140a021e 64
    0x1440381300e0392040084222807100317640702c81d06821501a4900038810540100a02d840c40003025004802e03002c403403203130b06100362101c100c107541c0303003040b03000f000341d1400d001c00640d00131061411039041c00100d0220070f690340b201c00c00c0c0142000c4e1035801194032001c117103c00350303402055503651490216000039003001d035110704002500032402e20029aa03049440508081104c00800d40703401030b00080c00c2c0b1900383c20b0042120300d407414000540010084407007440090340c1c580041400902080c2c1c010b1486440f02e40501c003540c0b01200444250301b12110820425404215088602e002c2c61360660401e003000d4841c640e244940300d041ca100d1202803445555a034014a080d080c40d20014050341c0e15450070741000b80d80c0d40a0761088100a115043c00585244140c0c440d2a040d294400c0d0310301903980741d0860841d198440070140494000200500130455804c0e841080803081c0840b01800c0143c01c1410002c0010b104d420b40d8007484d40003040c5c3c010041c0d0742d0a1114041841c01c0840c060942110740 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 747057446 1250 747056196 747056201
    0x80a0605061602030c0a18020304080f0d0903030f110723030f03010609060203041d0a111b07050a120308091606031a0a21060b0a030b0417071212 64
    0x40c451a00311400207281c102ca40c040b5a8501c030107500940440b100e00e00d0380000d11011090901c02c010001c403081090895849140d00250f030001e00074031429003001321180c800c1d4050b034443c203952091940d403030b081c0c0010580c050240c80d0400c164884104400d03007407181540034600c2510002010901c41c0c0d204c210004640c5021010014a200d00f12a1540508400c840b07296100307016003408900a50800200c6901c00403c560554140c4070440301001070072410460418400340c1034106035a11401c41030804001c89015002210407011155071180b0b4250202e0700b014155003002c3d00074440c68030705010005a90b440a0a0660305107044581644c80821540c00c10302048200e04150300800c000041c0e00354990000080b00000006a5200040020801245201d240303d0380140140c040f100c1c021002101000c50760150144030b000c00c41c0741103c0006200318403039410031221606040c042c07000b80001e0149180d80e00081120785441c02503107848070941160999100f90421034000c41c00070701c1d80700d07a8 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 747058696 1250 747057446 747057449
    0x2061f03080703030b09090a230f06040803011d15120322030c050f1e060d110301080d0f09230d060c0f0c110d0303061703030a0b1f080a06 61
    0x40701611142e591a005000e4105544802d12810303d5002051014a002c214041c0451b401002039500c0405c2c9100c0240d880760b4103400c148140214041c7d40700f441d50512101c0d228a1007556025a070b58100307402c0450229980e041484440f19460070803200f00b410440030710001404407030701a08003504d00b8800d8a140311340035500da02119100103100041c1d12114100c01900c0c8513000f201c60180c1c4503018460701c0340d00e1415056018802080c1200e818140c4168000c3c0d81c0405000c0c18a00142380c03440300d040d240401d003e04102000040100a0200d0601419503045000c0c0741c0314125024400c4000c0106001e0b005e40210001c003900ca1038228a03603c04c64003080e00000d40140d0002c182e03410000010a216901c00300810b5541d104004818424007001840344d6102c0400d4007606804418000203007a081011024190303502c8001c100b81017207020100c0720600110080d90743c4e1038682c01e100c003514218501513003c1c0003184c1c200c001c40d60060061588425141c681b45545a880000c81c10150409 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 747059946 1250 747058696 747058703
    0x10e070e100f181a0607060507020111070305030f060901080703110103060f0e06010215090a080c01110c0a0c15080a0b0a03120903020108010509090a0b19060b030610030c02061f03 79
    0x702c201c0020022006401c200b02051941d50030840340c1081034818802085180003d0b40c0144e007000305c0b10010f940c6912254100c00c29100015526007042a400040c2d0b1101c171082d030103c1e0000c8208100003180c02d200560001d010b561000c0c0a52400041035a607500e903004c010400056074000e000240d1103580309100402801031000700c142d9335042e03003142000d010340c1c0c030314018003d20341c5500d81c544100c0c6895029820391801401485116200c0c8003050700320f045409999501e0301040c440c0c030f0303070f04001601c86040201c01601d01d50300a842c000c0a41e1100b83d00c691000d004101c10750480a412144403a4024092040410400200740020b0b10302419034000134942e002034007440403281d92014003070301a00c3c400c0c0c9580c8140e90703c0f0420448103020840b20450a42e004841c0100040d2500c10031507007100d4030720200030340c0d001c0e049445000c0d285240c110182c88800030081040c94030300940740388511f20341d03400c00300010704241000a407250401080803220012404201d110040c5494207000150382 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 747061196 1250 747059946 747059969
    0x60d170a05220b04050103180803041208011410110a020901090b01030f021c02160512030f070e180705040314060403021212012304020304060b0a08010e070e10 70
    0x2480342000d00190000d64002a001407400149442e5070580b01c407000079608151001030030586000011000707070804552203042d40c0e40c440040b000061001000c0d500443c401c0b502e0030a242e000140003011020164041c018000404440601c20f848511281758620040d180058104d007032401c100f460031141d040c0080d0071040c80303000004c03c0815503100c9040400241d03024401d412000000000b07a0140902600d982075046600079030700003007507008251240d200700303525505110f40e488103420130448554100f012039000003040008a508001550300446074102940e43e0040d80e008901d2180151600401d003039085000710b03043c01d004400f540e00840d400034841101e9240644550344443e015101100036220710300355840407240080540342500c03400d80e491400c42c0e203804904c40d01d40084410740001150700c04207072a42511103000035881280184004103010141030240715248410b80e0100c14164500140004218404207444044a04480e400740c820f80b118410200d1480d01a40070782040305 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 747062446 1250 747061196 747061207
    0x12090f0b0702070306380a05100905030105180607080c0f0a180603050c160305120a0b0a0f050114130f06020d1d0105160c08030a2f0303060d17 63
    0x50340007a0080551340300309418000c200000707428140700b54006d146103115540b99216080c0019010b880285a032400400c0640e01c0740e82c07000462110100710030fa12002400c0c040081c403460400340541c54220710400fa12010202261102c02e0300c4080c05000704041200140c080765000c64400141c5072000e101c050015651082d603400a00540d0358034000b925690605100025403d010b441058030455010884034034060101088141d1100185411420301100784106c4140c60300070001144a00d40c1030000282c920841d804001640341d00303511442d004c20b48044240700c0e69034029003840d4070680d40343c4130710f0302e41c112610080380c1101d41b5003110030f101c101c0f1100003600e1030340001c014140707184545401a01c1c01c8176100d0000040c9044204c00d021440400c400c40c00424003010111010b03009c1e10201500ca501c2e070410b1800c56210340f48000001d0400103410801300720042c03002e41e6007110403410703100310f660611010780c40b40030080c0078038170903207503450031106000300400d0604912032903100303099982 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 747063696 1250 747062446 747062461
    0x6150a2f03040f05031912090e04032c1c030e06030a0c12051e06120106060f1b0b0f0402060f0f0a1e0c1407050310200a12090f0b 57
    0x7500300340f240306001c8003004400142402c1c04030b02034042c10b0102d01c40c81290300e45600d5061411510b480f2100c1041031070040000c0041111218a006521907601c07980180b0030f05030b580400e400303020842d08062554480d5111686c2d52070f22040c101443c1c1c0102d41d100c0000904007581e01d0700c1c03440700c215001040082044041180d070380c000d100d410072035182c50102c9140120305204a90003250704124a1075040303100300f981ca00003040503038040070050401c0b2a1f0110211501d0954100d5030090b0041030032580d03807880c0c154010900c90040b00100c5031009542500d5103070300c002034101418245c119100c42d4007080a540f1484125103c40300240d041d0380c0c1c2c1d1154650b0480c407603032003845076000113510a282411040032018032421402029a5007407071600d600e4403424024084040c2c000c01d80d119041d800526a1014407880c84610000500001c80c1c008191031038119441c000c1007140010401c008400b04150004041070b030705202c0910010744103c0d14a0000e6407581064406043d103020001040340d813 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 747064946 1250 747063696 747063703
    0x9060813051c030c090308030c0d090206180312121323030301031a011401030507020115180606110601031106070b010e1602030306131a2706150a2f 65
    0x900b081d41e404200e4442c61610494680e0701c00c2c04028201c4d201080420381c0300f0001005404c45a039851000140030a042d400641240d0000c2400304804104004482540c13600340601c4ca284010141c80724501403400240d801724910040414030b04451002002050044041070f060708007d0b0305111b140c1004407000f03516035a8000740720840d151b1880d030920010740091045024120342407070580040031500c2c0030054000d0b0400411460031507680e0440d01c0c03880602c0300e480c0e0008140001035513852006246c1030700c00b65622904290244003122041501c499070000b00103044940141c03ca485842000700051010302c01d041001e40500e6211001290312503801030b038140124000880084110304000e4160788030f000440d040c95014640c000003606c11503440d00940c8481c0d40c01141d06501c8459140002c8580b00700c0c1d0311498bd40202ea40050f2143d0840c04801a0030400494100103000e000140c142610300c5000098010030204080da0707583c04500d44c512103000640c14041041484a66080c1d542c0c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 747066196 1250 747064946 747064993
    0xf06161b03140606150304120e040606030b130e1207060609020316030c0201290a21140a170a03020904051f0f050604050d020d08071208070509010906081305 69
    0xd0b5402400c0102c2c1039464a4218801c01403203c80980381941c1d6261500c28005404818180601070303800520b994983d20340c070450003d4900307514001180c59050081c4405a50005c1b02000c0d09440d01110030591140015503210040745041d074681d9480c035a1400304003511990b880404a64004014032103655408140f01421494541d000c00205040d40e83c101d00760b403c55601d91011902c00c8040c041c0b46640150704050000015007071020841e0b0382c0d041e0390302e881c842c04e400400328081411003008104200903000004903c0354010501d00003961610702550007441007049290000240d1003180e0f0f8041e030156003080d00c00600411180ca014060900c240300d07031151580801800c12008039070007003e6814501620800f030303d02414a41441e050240034141483c003668004152038085000822160040c07410a2040c6107032603040300201406401c901d0054690000c0c001c05020460160b607100c09544112030710752a024038180c0710241500c0343c501d40800c1c007400c140074002c103800c0601e00310208000c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 747067446 1250 747066196 747066233
    0x2070b060f040218011d060706020a14040605190c050d02060901110a0203092404060e0a0b09031906150e0f070801050109030303020306030c0a0305010504060b0f06161b03 75
    0x11071031501c41c42000124840c48142140408081300303001d03600c1d441481040c0507800941d400c0801d614034500001c005030018901200c905400090441c2080e510000d202c2d0b0070a01001064282401c05501070014020172142403000e048501c00b0210962286030001c0c660b54014058610820390404000c0d00c581088840528039820400401500345814003205d02850242e4099400e1081c0e81c4c04100040c22441d840034040601c0096051903035420800600003015181c42e10450f0b185401d00b4803a06011580c04040e02010034818000b29848c042840341303403600c070454000d03242c1c181071408500404003501d445030340144a460120301380e040c00c0c00c3c20340610303614001c100c0700c4c1d914098102e902270f80034004d1500003040d0000400029001c0d8002c0d541102000301a07544a0060101049008400798000c1d1496910394040c8014001548a00e110102c0103441e05885500000007040790343c4605806200da40400042c1041801031040c007807598a0070b407490309600180d880c18900c02240ca00c68200 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 747068696 1250 747067446 747067459
    0x5010507080f09070509180607050304060f060b090d020d0b0c0a02150106090509090124091a0619090305060f0402180106020601060e010c050706021011070b04060c1202070b06 77
    0xa500c403030031030381507a203d040c42c4401044100d003040240210380101030000054078104030009102c1103000e2004c180320304c2c9207641d11a12480c0034100802600e50300d050381101c41d4504081400000c0c02c49049030044001541c00c070000d11420310104400b40390980014080204a001340000324240c3c90041c00c080000745d08950150004540200504c142031140d58041800c180007003100c1e04081a80360390000c1c03c07200000c0c802d00e1580440300c00c043c560600301848020500c0c14060761410348112484581d480c18004010340d030041c0804c0d00341c46610300c12403031010184c142d145020f01c9550030300041c40c0d0150a80e08a41040e4111100d40b0384251001c078440c010450742010001d45034480b40d4107c0d0b01540c010940f59103000c0e41510a2a482c203075050410010b40003c40200303c082018000808075039008003565446107040310304070344140c0910051094104003000100340700410039504283c003c8800a0b400402d04030944910310700036021602d250010030b01320301f0b0002c0c0d40c10940c415841036400 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 747069946 1250 747068696 747068701
    0x60f120522061d0106050d0b040c080f0a0201080c1305040e0c0a032003060f07080a18050604032c040222090606173907050303060f0109030203071e120501050708 71
    0x1041c2030b90302d103000c0d10350807208411f801c3e408079407502200d913000740c05600c0341180f254540341d040342030130700030b01a144c10303a403286409108550f8030480641d4400c44a41c0040c1c01d014681100e194100d40b00d21510f4450381e01c81c4142840220180540d40c50943c004124400070b1346d803032034070f0342440d2111400e2000f800500d070804230660030301282c50381c8134030400d00e40b8103480c0d502d00d20203854010001d804411070039038805417071780340d1710045040b501444e0040780100620715092800402001d10201e0402c14080411403c4441c1c0c3c40000441886e41001c41e03001d6143d00844070001092080c1a501501204120a0000d40d4600f9170340306070103555840d038540315104d2410790000101310080d00c0c491400340710710010203880d00d400c2c0718041841074101400c80c00d0202c0107943c6485500f0000d016142c580001040c00210f00d051501480350043c2802d040d041c035465900080c2c1c94082038030441e2004480c0441c00140041403005034005040072703100e61030491665040c414001c040864070000803a920901 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 747071196 1250 747069946 747070001
    0x204141806190b3007051b07091a040c0926010e010603140606012f0a080a0f110607020703030f0210060b03040308060a03020a150e03030301091401060f12052206 71
    0x130003500c5030703c254503854034000f42c0031200e00c2501548603805005000360140030034901c00a000700c2035550b8000410700c080c85244810001100c200040d06414048009407c01040d0004a05000081840e841030000c1c0d440048000c0d01500c0d4038807071b041c00e5504c0c226011080015440300bd115840442c130840f909540c5103c01901d004901148101940108660038500081101940c4158810010689016060355550701585800c8504110080341242d003002c0c0303c684c0e104400c41c455103150300050175241020400039464080ba4007001d004c11291070500d4a200e8000c00c40f03085803400801042119a554441d90281d6030416282140000c1250300810b529140c00d01c410401d80b80c0040c02c85100768a0706400c100f80c010700350307a0a0180040589161040d41d410300240d4001c040014010407042c905580d1700c0c40e9094140c002d42d007804030310340078102d01c0c41d8032820144a042d00c00500061a45401c3c4001c4000504024400c501d812411044800c0064030381201c241d07248082c0b03d40c061641c041d907 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 747072446 1250 747071196 747071287
    0xa0b031009140406020a0c06090c090c0203120c0903071508040b010b0315102604111005040504050c1b0f120a141e0304060204141806190b 61
    0x8074800d48214070740b01141c00700302642c0c0104000318050034500c2c445c01d2259a800191400045c050750007036511801000040300314003456502100902c051840c11104c01d18400380c40790050050b406692021131804182d46080151102a000d40c0c0801242c0043c0b026004048a6003100c0c1107a090651400003c0c00c48000c9040d2070140308001c58064600f07140400b407141d00b0800140720020003160f010140907002e556098007081c01d000d407440b41030b00d28007410005890f000701c500160198001c0c215085600c2c0e480410781d0191001118041002c0c3c407411075103c0c59010f01d84608414205504500f039401c0c50004200d450ba520344000d450800c100b60f842095140940007600d000711316849a00c00380c00c03494100a2850000c2c11101c948040340504100d00b00c5c3e042114111042a0b000034280412201c03e81c803020100d80071500398100c6002401c1c141e07200180645800c0c0a81c06010ba03910032444a0a260310103410000c16158849aa01500c4070020180010000c01d1031018901c403090300c0601c4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 747073696 1250 747072446 747072461
    0x4060207021c051f021e0d0e06040f0605060103091509120807021002030c040f062102090a14152209060f0b0a110d030c120b0f010509040b0a0b031009 66
    0x21014004028503040c441c0c405003d0000e0034130720141e0800085000d0400c00301c02101c45410f0042d15600c92030101d440c5000c40d9545881805150f00c0b0404000016429602110300d00da44588003040d5521010b006074007400c5003440040c20403116016601142500e40c2c80a03850340d00405082141c6404150251607602d070540c1c4290060300070b454160400b0380d00b500195003001a215210345010303581d0110102c502040e40041e0001407515240d1540074800380440245455070341c00c214984400c45001407100304941c07240c0ea580d140004412005659018000c1981c4880b040340d903955000e03102403d441c25080e68030081080401c140c80401e481c00c00d8407600080c2c54900e02c0c0140c4940c03c112004640e50010b908810801c0381181c1d0a420b004001c2c007401e000216a44c501103100c0d01c141002410402e0815030a50049107043d100d16400d03a82c0942810001c0e1003070804c140c0d1209008045000390550280c2c00341c010421160000b04111402c0045129075a01882100d09940300c40700d003000c2d02d956 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 747074946 1250 747073696 747073703
    0x141809060619030c092315010305040201020307150b03120309060103030c0507090c02011e0b010f032018030c030a0f1704081603030201060b0903071a0f0304060207021c 74
    0x14002401a0805418840d501e461540764041216543d68038031444d144d29811030903400e62a8041c40188650081c603500010300390741c04038a500d1800c440302c0100d240681060904058807600840c040d0390017482140c14042d00242040b240805900e440300203840d0b905c2e04c07140203100d00b0b6200320030740c6030b1030040ea8042c0d40600068440c90b4a5030710300711f500c0e01e0100400d488a0203110070001e14417065110342c0c000b04541d50004a0404480d4108540e10120280d4281101d420070b01c8580460380d00c0203181c65030a26070305000031510002401400444060f81c4015408140000c07007400c40703e03400710000714441c0220115600c80c11040185500c600103402c5c01400300047e620304400240c540111f8017100d4101c6540303642000d030359425051a010031420b11440000014809000341039082c0106006006918007543c50180c1d050302107940d030303c21842030450380681240300000c1c0344240e004403080c002206a00780c0d160b0801d402e0a000960120703000700d01c5003020840b0707903144d10401c6051049643c1c1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 747076196 1250 747074946 747074953
    0x501060e0108011802090603030c1b0f060703050a08150d2604150e040b06071b0605180d0206090301110a180b0a0f0e030d0903062307120204080106141809 68
    0x100d60034006d03160001b41c4902d40c980410302040b09203160030003030a940800c0d140070380100b00d07000c4403d01068500341c2a89a025a10401c140c0b00401d4010049a007c00114904010103540741d031001c90342c8038043e000b29030f0300c615054890400d03c1103001c079040381e000401d81c540300603001082480f44148158410b08840f440c910186c41c41c1709008040708003000c03801400224a20f840480020503a6010881c200c405030300b4100d81c40e00000c140d010302c0025010900304140b401c10080404103959144900d81840340000300041402c5403204c07401e480e110309015001b4400c0c100a80740c22240d603004a803400d000540e845148555907500021040100d0b08400e180510b0a440e240c4100d606c500012a4101441003003d400c0b00340340c90810008042032032a41d18003d00d00d0035860b100003950766048580e640c5a0440f010071a4000c0b480c080c0d01d03080001c1d420318507158810802d0180c06409150300c0040036519102002400280c42c7d418551100c3c002c8450301040540113003e4100380c0419940c0040701e50 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 747077446 1250 747076196 747076241
    0x705030714010c031403040f110909061308190225030209010909020409140303070f081021150f0b01021606050d0f0e0f1c08310501060e010801 63
    0x14020f82460448a010f86845441d64110b80c11143c000d600981e000c90f00c09031641103c1301417100400038100301a408943c010581d084c100407080d85c034040988200c98400c4942c44400800500b201203a030300c849040328421910125100103501c50240121503100000d401c2c0e00c400040300d20501c20702c00c1c0c030360040c041646c590900038040010035190100726001a41c2c0c1d0b00d8a008030300801054800c014520707004565074030300364070010f2000a5400d0b100b8240034410f018801440a000031040c141c89400f407506d400f507440445903100e0124409405040403450505401c0000113503040311000480c444814884010582e0049940d01500581401d00a08412080c480207106000030543d04411003804564010300355600802c6840318540300f4100c1d8070404500c0f82c1c40c2c4081c40031f214081e00c1c61106c68024000920080d180b400300408103210701401c040504070b1b1540003014030b9410010030401200d40c1d405854954000c0c80b9a0140b06641d195500000400c0c0e101406001e5040c01041080300400 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 747078696 1250 747077446 747077449
    0x1050c0309100b0d02060712140408060103060209030a08120f0c0403080901140918060a05061c0209010c06060303050706051b07060213031a010905151c0c03050706030e0705030714 79
    0x8010301d02481e6032040300e0000404c050399070304014100090003001c00101c5240b62543c047c04500c0070344800d03140508240030400400c000890708504683e009100540e860390440006070070b01c0b00c4a400102004c00102d000411840f1994480c5c1c070604056048100a031102c00b20305802d0300a62000800c411010000020300f03500c40c094810080361544540c5090001c0d01d000589100030640f041815114a001040303c1458510314a20040c18150707146072810500e0700ca485281d044107d600e246103a0001480c01c11644a5403007040615044401081480c2c1ca80c60000c0045c2c0c419142656130350706150100b0444000c0c000031841e1007001000d45d0b8030b01022550383d040a90440c21014031031903003520000010403040c2c0714144015000260101380d640c1080c42001c21680b003c2c205102c06a02c0c04a203410989035030300748003405004040300103180c03100c0e4580302c59200303503c0d0002800c0d8000e8160000d0b903a0b800d9002100b20001090a450f4200d40744c4003410b41e00c0311103208800e00c0040300864810745 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 747079946 1250 747078696 747078701
    0x2010911040b011103180102060a0b150708090d030914010e0a140103090503190f08060307050d05010f1a010e091b070305040e07120609050609010504020a0201060302031b0301050c030910 82
    0x100c1c2c0060416074259881c0c101c6203411a040481039045050a2600c00400c540c2d040c056075078083c158403070412001403848013003482e2482c508041c0d0b810303060024074402884080d03c142c40780c00700010040c04400200b0320b00240407140501c10302014800403c03403044998081c040c0d0240400700900850b02580c6042c0b01070800843c04a0680e05160782e81503440045030341030004000c12808051004503a201060005041d40303030218030a82008040018403140307540124841c400c03600222103241d5038071054105a40102040c68074404006d240c07800d007410280c15100000c0c4102806d80b90394600c085500300303008500304101c94405554640c113090071a468000405044854002d1034107508140d1649a0842c6a590654207400403904586450001750441d001e0100900151070060240c1c0c1403840200d0100001800f584d03200301c1e0081581038440b132003540990015500142118110007017800010000003030105100c0c029400c120000703030104003000440e8000c0a003c801840c031903030000180c400 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 747081196 1250 747079946 747079961
    0x3061305060d06020417070b0315090403110f0a0201030513030801030b04081209060105043c0e150103050601050307030b072703060e06090105070215040501090219080106060201091104 81
    0x9110b030001d0700350400314240e44054806405d940704183e82d607003000003802e0b15251b007507030000401c1f00041040010310002280314128460055505407203a445a14054a4074400d070000c1d50700601c906218264100f0001540c8840316000381c07400c00c09e94035804076000000d956a800540440c070404010000985480207850344603004003000b6085c5040e43d100542c800350152400780d002c0c5d000c2001849545490b108100b002003003685504200c0b80700c03136000040c8031030720b6001c0d41d2840b10451a00cac0920301107401c4000402c2c041c00a5070a00901c0381248969402c081c001034405200c0e030342c004120b900b00040d501003030304d0f006410100c0c1640c034950b0840d0203840e0303845035242e0014601040c1c8c490300164400d5030080c510649010031020f80001c4820b15100c00180740303000d140c2c100750602030020703004542c0c2c801c04503507025414410340e25818828003601e8030340e40094026080030400d0315401d00284111042d0b460480003405515030b0349100302d090358807090026040c001007071031001d69490030341d00c40300 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 747082446 1250 747081196 747081199
    0x1806040812071a090703110307060f050a270314060609190209060d0e010e0607121116140f03070b0a0b040e0a0501150f0f0b0318030424050306130506 66
    0x1089141c1d070150f49000d00c5025103030202c2e07961203110203108015106200c0e81000105a00400703d89141140051030104c2203175102d42030000c00140c0070001442021055010707202085000117241c141d04030060620841d1106581d1584040d0040000c10804a480c60044a008240c1101c0e0349541d104406a07445215880c03044c164200602c044649455000d0200e82041e424000390031681840b595094039199803203004a83c11120410000940182d00c4a100501c083c000003130444010000c0071862160040603a0303621705600340310041246801303403490700d143c07140f0582d074011844c000c002c1d90301d0003042ca008001c096520009010404554422080d00d440180301294800f07014041508241d420071064030350b130751078401449111f103400c9842030040c450a01c140140d00d00e8200710f0701f25400c0714003480942d10000400b05000c0000519a00e0f205000c0e8001d60740ea80f030780e400e00078110758602c90400e03180a081c03003481c0d60746a001b001034a104810241c2150f04001000c544500280001021107 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 747083696 1250 747082446 747082463
    0x50c04210c090c09120b010303050c1501030506040c0f06050a0c0f23061003020f09060a030b160219050c0f01180306020310140a2711180604081207 65
    0x340490040800c0c54000e080c031050000d4000e56070b4a0090810046070028903000c1800980302d00080e5131154020704694251800070b40312240101c10a0805078140040c54041c800b460001c418040e010581d6030080344941c40c4100300b6962040b0850035a0310b40e10990021840034010584031501a01c03600d00100d20802c05811410300700d50b07500c210091078801c1507101c1070460741040c2d4180d10821400e60020080304d4014504d0f89164000354049800d4451140a200000041041a11230b160321001540d403000d0403504516013480000102c0e80300076450701c014803070305039002c031200800b5804000786a08040a840c41c504403d0a0204042c4038440160401841400080c940ca10600100f0043c40c0320707507005a9079040441c41302c03500b00d0345a000b2108011180b01c2341d500a44d03071051100116007802000080d620043e01008900014010000c82683d040059000f540140070000780303c40d03005048040301b18107001e018407030301d40101e000d41140c56200c0304161a100254030083e2041c24440d0111 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 747084946 1250 747083696 747083759
    0x8091501090b01090603150519080601060807120b060d0507090b0a39200904060b18011a091908010506090705160201111903020f0c04050c04 62
    0x100414600241d1098032000c0e600c0c159540c1c2580c0c444100300050400d454140b02102001a04810400b26842064440c504604000d0606044032002c04000d203201020368a5560f940c0b14003500b00e560468204001039541105000e0104103403240c07052901300a4251801c100500300500e00500e006407041091102060700050740d40032441c020092107a042d580d541c400d90901d9a102400301c0d0040060042520401001d17000000312540762200e1604400b082410311510040f6001c480403692100c0d41010b40101000240701151300405281c910688d030015021044440c0d40420110038000c9540c1d0085207041500e684071102c0144c01c003100018040e000f803e001d0252940b054041d644024800d94481081081502d0142192a40150340b400c116141c541203095070011906c00c00e070024103102401101510724142000941c138070115148079030ba0f80140504010350f0300c03411310246094610440c42d43c800c2c941054001d0300e0003901d07442d60080c10030307007000341000d80054410b030541c0154002900 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 747086196 1250 747084946 747084973
    0x207050a111c03051908090309060f0c03070b040b0117150601020f2b020706120c0504051206101d0103020909030c100e0601050d1a0402040b12100f1b0809 68
    0xb0b101140314881e031906551188403a0f061030740030800750120802e11019a08002004101000b00c4500402c1100c1c415900c45040c04015101d0280c088240310503c000b003080000c00c10018030041c0103170700410610109aa0f91102c8003c012509480705200750081c80c2503203d00f080c600e00d013940001d0140103654002171a48003951401010316554030915412190440601250322440109001d00b0b2025007100c03070a000018180350000b800b03285c102c0e50355000d40607019203d14107943c042c05000b0507a0280c0101030500c182c0c2c4480030346a5100300541e14000082c1160203600b4014030702260304544c44684e12315001c01041100040c01030103180400c00244810341c000384070203c0f2090300705100061141c40b402116161810580045000302c0320038600e2804130f21407145260225000c513100c16010b51b00d6202080240038401020758000000d41807116100001003048105040a0403040024960401070f00c002d460310a2008500c174240c5048003180e083c4551080e0f98840b00381012621030650740e11 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 747087446 1250 747086196 747086239
    0xb0309152206020d0c02010b1008190e0120091302091309050d08060901030201091701060b0d1e090c0512010b0901090e190b07052101140901090207050a11 68
    0x280210340d0240c0c005100c035501d129178030030790f00050003a1008100400012002c07890403250007030800180704218000900c1e80002c00010071180e0f80749103052100715203004e105030180480c0984903c016103003442e00c29890815400b0b640900e90000c0c482401c0312451446e5500075405545040c2e0010a040018065012140507914107a03120700b0091940382034180c00204a041d002c5e26444c402c89140d0b0040001d80c0c0d00c9110542a1441c0810280810710418126801044141d0140041040104095140c1c02c0c01d030b4451304030700d100c000c0f4000503150264140422079480b10401080b0410b4203105209a06200501c003510090000000880340400360000c0c00c5100240e00c801406a100c3d0082000b1103414044c00c01c8081c520354000c1610105642c9520204000518460030000c002c1001c0e0303094890540c01c4d0540c040a201c07080169615038010200448801204500920071840001070a0b000c0307100f1124482d0301f190103440351413019550f50418000e610308a03a41300c840b0b131980701580900e44 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 747088696 1250 747087446 747087511
    0x703050408060c0c0607260703060906170d050a050d02030406050402010e1c1113050a0e0c3307051b01020c040b0a030206070804080304120302070b030915 68
    0x26112151224a009500d80c40c0c03000050240c58034900c00d001d003901c59507001542e985c00002e0b5040c41c4030760100884480d40400310000b03004020500e04800d000e1015010362108041e0b45078050b09118194030b03440040c480d554114041a0b0903440b000300c801e2260310401c0901003440162900341e1600b00100f10050903a0000e90b0306940c5035542c0c070284400c540c4c11029850700028103880d00700500c012003210156810300c0034400341c44203900700b442041030307502c2e0029840003103003555017041542044445440180b02e0020401e04510070201030610a1038280941608081031074000350490441003c2030480e03a643d40008202c0c1b078400d0140700c0028009224103240c81c4154614580d003060040002450181c2042d6010300480c0381110140640e110481c4650681e90141c40c0b0664820042c901340c013140c81035500c1418940070125007c2185180c00300000081c90007a800c540c000c4e80c40741113800c0d1900c001d481d2005103520142180140c40d211404aa602c849001d083d01c60402841140442c1004036 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 747089946 1250 747088696 747088703
    0x108011815091e05010b0d1a03030c0f0106050d1511130b030703060b090607020906150c070e0105092e0902220b07032003190801050111011e2007 64
    0x1200e09454101c900c00c214100700d00700c43d580c148030035491300981c4c42642c40303204000314182d5295001c80855807120585020399034005800c0726520300071070b910f8903101c0f41148800056542442c134002000e14004001040f850b4101480d001007202148a4000604000b229150b003540f003800308420036a50380b40e041000700945000c0ba5941d242c0120b0042c100c400035000f509500e1000e100b000020348482e07096600e00c95041c3d502c15030980301c07080041c01986e000d09649a55070000520741114a80200e801c03000c032a1b56038a07290290b607c0d201003003000e540032155207403ca0428002c80300e100d070450020310308101494140001040e2900100001d0b40d01c200c10045020542070388030203460844019903002054209056030402c581d607a03000b841c13000d504608404240d1303042030082c14010103004035144400b01d10130a4890550028005e496900700b44602c1d030214104002d09543c4070810b00600413038424400142c82c1c80484540018020450081803480ca121040d20a0621510550081013400e01 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 747091196 1250 747089946 747089951
    0x280204030b0a06180c0504030c0b041706040f0605192901021504020108071b0308060f01110d1803051e1e060103081b1b10030b010801181509 62
    0x46040c0420101d00140000741c0103460003208112040300c02140c03400c0181900000300303141070883c104450383d010b5600003a1106050800c000b40103a140d400038422502c0042d5076500314801844c80230385a0f013088902a002d400034034204400590a41e10840e80060800b4450309400f50308103800e011548400200001c4810340c01c60b080387c004041d81c0038481c2c0c00091004001e40e0308a85101180000c02810082c18071040c8400701da80d8038056403440c0340c980b20001c140c0c803000c60385050041500030180d0b02240034401e50196009a548284210707039122000318000e100d0301e58680001c4603160704006c40280307403e0f91400c0110000308240500440501079803104d000da0905004031a050000e1490981c0400303140c9010071400c80000310700b039411642c0000389291241c2403600c1201c001a200040343c0d40c0c9000d06104024865161080140349580c2030b6008501814001401c0e0100d80341b58025601042c8103c004024070204210180081c2d0121000880c96a048600b80200e01806070000c03560140c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 747092446 1250 747091196 747091199
    0x2010309080c010f0608210c0703021203070209060a08031c2918041208070203040b070b0f0a110f090609030d08160203160204020703030b060d060503011506080708280204 75
    0x80481c00340c45d0141000d00d0281902c4603080c5110745003084ea914400034112404a2255a040c2d4148001401035030060400350307184052821aa480e41d0140310124480d03000c9074041440d070300744010850156410b4100443c42c2c00c6000c9070b000b80c005640c42044900c9070302c4038090081808241d5441001c080104c9110501c03080150401501420a45c8110403200100c02007001058015002c07130920811414101815100d5540880c103510854005070421000003c141c01080030321b14a4034411011100341402c0d46e115151504290740001c12101c200382024001500d5107515000181340c400c0c80141424500b104010110b41840d060365680030100e0080c004004d12801034040300420704049202451400b0f035884400c010000c2d0080c03002c3d0003141e01180400805009521240000c103009048585846000c40440043c2c4100e004044c040d5013003403041340384206003509010580710162140c01e1590b4880400b25503840c0010707e0005030b0f4203424904414404940883c1c1c002d40c00d0118056a80da = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 747093696 1250 747092446 747092471
    0x8010e0106080f0303060d03090f061e020a0804090b01110f0a1506060f0804062a020c090105030a0209060312031f1521020c06010b190203040f090902010309080c01 72
    0x6a1a6070b0241655400908844400a41c0132044a901000442c1c0303003041000c10381802c40d00c010b00c50f0010f115446054001003a0f143d08284042c1d90071410b40e42580c00e9a0b4940c0040b41c4803e0f001c40001c1c00312105000600108a0503044807442c0c41c0e041c034041410280b15a41245001c40ca000455025041145003005004210300400310005030350700c05200305403900f40010000140345640c2410803500c000407608018940e00801403440c40c14440806865951038000e100421144004000d441072411107585420b180c2c0742c10381281c03002405061885216024002c0d40c0c600200b10607414010420041c0130444007070040c501829500b2000c01c003081c26a8103423030f02c050458100e502094205c1c040c04007140d07071203800c0152810b1504003030a0f007003020a8821019000d110321086203801110000b05a900c14440903046004900c49142e40c200712003a8241e8480c441c6000d60f0301486102c0d44180304000c1550455a2800e20614000580007071980700d1400b0fa8000307140c2089940d44805030714100 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 747094946 1250 747093696 747093701
    0xb09040e0a0c0e1e0109091104540c030f03030906140123031c170109020901080408090117070c0209011401022808030c1c0b0a060302090d0c08010e01 66
    0x301640c442a51081310750b501130128004c0c1441100b1445881e000590b00b0440600700400d96014050024003819a4100100e0429400030000e0b060010010088500c180806891007210300c00110a04550016000c2407909204080c1401c0c0d0700e803007285600000203003e0500c0c0c414542d0183d43e0010b00c1400c1032a144041d01c94080f02d0b8084801010018040440782030682c41c00b0340e00c1c05101c40d921301d0503030010038140b004080c140c1400c141000e092000349600901c004241aa04540600c034680e22121030408074000c50031160700181480d800240050b200c03100414000b40c050502c0001c440030383d0075131021848201d42c00000503008140f41000c5042c0180142d01600b410700d80700300d0398841c0ca0f0000303507030f0711100000228031085178404004403030710740c0d0321006180d421291a40d07981c9058a00441d490340442d4040c3c071401d0182860003500c0b02c41d8414500100c00040042215500e0700408402030342100071402c1d40038050006500012309600803940c01004250300206a00161611843c05c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 747096196 1250 747094946 747094951
    0xb0d260c07181116060b030d030902040b0409052d0316030f0f020318040204030c0801290a05090a02090904030e1926071a04090c180b09040e0a0c0e 65
    0x7400c2d410155a003403103c00c8a000c0e40d09813660110441e00070301441c00e105000c1d281201d03006e901800349a54004546616820140350b00c0e000780c80a00450311114180021102106009002c0780c00000440d4880d00482c0320110303140007050500d200d0500417824003811a4401c485603684600d000300d15004050704800e01d11030105840c14002c00c08050f03040041e4882c42100b01001004030200510300050780d644d4169400342da000b200300703d68661500d14581c02070007031005150540510103105211141c4501d4031101912026140010711480d10090003209000500b40030121030f001e0143c024151207404281c0e1083c2c0c041d50741c0d1540003000205109070001c0c16200d80c1209100755209100c3d4407115003000c0b08450402d80100c0401840c1c0362001c0c140307040c5070030400005c00c0c0c5001d10f447d9007510001034000c0d00d07041d00c4c0401c40340300c1c0028140c1d4020080b41c01d6802582c41114100100000720015000724000a80003003039442c040218141880240181203686040f410802d0110300055079440b81d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 747097446 1250 747096196 747096239
    0x51903150617012106020304060c0908030f0a0503040c081b0109061409100c0f030c0c09020711010c03020c0a270915050903090603160809010b0d260c07 67
    0x54141e040d4120a01c400c00140181900300c48803083d520400c01004625134040c5800c07a01c00c5440e400c00c0d00c1d0140140811030000c0c00012504480070a000310003004440098441d40010361501d80031981c241c0d81604014810b54180109850000d135828040c000700c491580e031b80c05841010f49548001400c0b080140d0422420405844415511181030340300b100c1905404a4080c0380c403126190044800c4009198001c0c902c85032800403800f0542c020034200c0030030b8403900f01005115180d4004000701d0080c0c410140281d160350004420a5009002900159009106444440ca40c00010440002180e88101c07100c04d55014640320500c44105e40050302880176805024807000c0703403a00c2c108500400c6511001d10303580c80100b1000d01c004c20031900e0082010307000c00e4580c41d040c00032035481da00650710314000c181c864001444000042c0300320040300320010611700442125481d000417498101d942582110000e25a01d4214822400500500c0442d00c004000b82030034080c4c03503480c40507050b0608 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 747098696 1250 747097446 747097457
    0xb1003020d0e0f070b160602130f09150303081003021509130c0e15120a0b090609061c06061d0106020706020f0703080a0c060f06060f09050604060c030519031506 71
    0x10084900c0440c002045580b030f502c0840d1207445035146480c04403901c40707001f032099100082e0400f004003019002411038060203c4011000d0b030394040344007560242c81481480304800502072000a0141210507009042c10f034980108580340d40c0841c44268840d000c0d080005004580c0b42010700d0030744441d0030308505110341030140481000d8050442009001d0b43d0344030b0060080304500394103d540644d8603d41090300ca961403800c1c405c1ca10b40003060241c0505001e03d0069002a0041c06c0c0094054014200a440b800030400b001c0015050740465038022200c454581100103903c2ca0840e0802c201d108503a049603485500d0840c010749000c546500100070b40d0090f44480e908428085100b000700c0e80c010000d00d5a55080c40c0341100c0c0d80d500c540c4020300c01403910402d00d88085459002d00181d80c00c545a4902e90b240b00c0780240c0e10816130348613460344240304000c10300c0401d102da894400310521a040c4036007040f00c3c0c0c64070170b00c241d02a0714251000940c0e50301b0010240c40d498090000405241c20007 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 747099946 1250 747098696 747098713
    0x8010603080711030f1504120f0f0e12011410060801120b0601140c0d030c051303150b1f090506160b040305040906030c0801110a0c0b06040b1003020d0e 67
    0x44503034502503002c0c007400d05182a01044081d460600030b503807050305035009907000c400d60010700500746c0c80f044c2d40c151248140d500c41460900e0081056009100840d00c50000024085a013241d007008548525908030340044081c8444090034011022a100c0e40c080d060704625040c880c803081044250701420400c0304000040104140400c43d014119401115040141d660140142c4294020864018541c0400200640305240105100140408030fa9081c0314445c81c01c1c10031512402808400c0c149c0b81d2641400b00002100f0525111403985030341c4020401e03800f40340000708810030001290703040b24030101080c41c400c0d82c08502d81c1d014000458402d401c00260943e6090302c49002440105500103100100c1c0070300d40103509840040081e20400e00205807a46011305080c0c0311803080c04515800d18040d40750341d0f1507000944800c01c000350f80304151031701a1b0310303200c1050102400303068100e40d4589000e0116180d00c3d1414600c54004d4401694400c0380b080050222501d40103c0e01e91038204622 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 747101196 1250 747099946 747099953
    0x4080615030a0c0b090609120c0915011b06150807060305010e07090302240c01200705030f030c0d1407020c0a03151e02030709050316032f030f0601050a08010603 71
    0x8010040c0c2d603030020010b0300d821026000c0350f41c501c9400c00c1f003030f0310400c660007448915a001400d104601429100410903407540c0c05418010b160383c0346068081100d054081d41d40941110089441c540142008030310070443c2c0c126462070030055004ac2003650040c1c07005000c0d098060080c240102109503042c5a6840d0441004007c0c5500e0300009201d40c1e0030303505018800a0a403015050700c0702150342c180d6548242d0a10600808034060000e9440403160881d0601c49500c00a076125150410050341c581800e07420303a545590b1008204504180c001c0c4010980d994252085100d01038074408031540714100003202900c1d04442d1b400303140c42012040420710005580189642c1c02d07079801c1d640410020304042244140d42000340c2200b0f8500d102100f00081a944031607403000302c81c419001d0343c107000c1c000300180101004502010304440e001d5842980003070340c082042508a2001e00048d1a01410340e00040d06220038413035400038590040d80180400d10b0031042d120b00a0005200800002c1e1460340d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 747102446 1250 747101196 747101213
    0x11091801080a061d01050106050309012a270605120a020306010e090a110c060f0108060f011e0302090f0a0b030a0302100f0207170a030b04090b150102010e0304080615030a 75
    0x2c80040a058981c001d200c0e20290f00024020001c010308001e008030740c0c40f21030041c21900111040701840d801c103049081d601d01c6400308144200c100c880000f07405180441c095841c10100300700840304044010000e0380d0f1017920a00f01014000ca669801c1c0e076410901c001c0c803801c0300d0107451503000510400600005030f820442c010b00d24002642d403441541c0c2c0c0c0c0c0301d85100078100308032840d0000800080d0301d00c01d0100410003520900400e0054196662600d644958515044401c841c42058200c014800034150400c1c22141d103000752518009a034495001c204c0c000b00980d41c00042d6030341c1a040c4640d00344540202c085041d01a00202030359011918004d507648032a200c0041d2240e4ac40b14142207170b81958040b5084290800154001a0580c0e04403078002d91010800000003490900d2030303500f600d0280a4280d845811410000382e58a600a40c83c4e05029050361540c1076650b41e4070071103428070052000e040100002d8015200c285405000c40d0004800741d10f0300d80c402c0e04008800d0b000035000c075 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 747103696 1250 747102446 747102463
    0x9191a0d02010311040f090f0612080412020301021e1e03060d150e03190801050418030e04090c23060f031803090310050a2306060702060405041109180108 68
    0x240380210301d1000700011410b40784165007103084081d00a880107d4020a55040290500c1c00d6180c2004116500d400102c145420b0500040940760100300400c502401c034111001483c1c001000145819403190550820700030007202d0400160000c20152021924850b20b4002c4150320500540f4514184000504182e56840c0c01006c3c5440b000b80c40c0052060340d4001d1300c01c42c4000084a0f44d0f0201e50507108019020360481c41b00085c00100041040e0926009030708500940300b42e611704000590b5402e40701c02c80100716458210f681c0c0d1159034086030402180c04002e04511b0b40f04058481840c404100418640f030b0914003408007002440041d42000045a40c004108032104082c00c120380d4049055200798000070343e02d44195006a400c1d0341195114a005e024007001c00c00c2f07030301c600124144091003885044840b090100001540e2030400700003c1078000d100415041c5000d84880c00101110540808100c2a0b85e0110b00c8505a040a00c0844046100481f2043e8250b00d004031640d40d50014 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 747104946 1250 747103696 747103699
    0x17130314100c020c1018080a0b01060e0f040c0309171c150302040902030f0706030c11010e0c1306030b010305030306011701030b13080f030a0e071215020f040509191a0d02 75
    0x14008020519101b204800c103a0b5000707401500405a984528558a000d6032009451003104031000044c1d0b0740c081d91025400210280170014a2448030b41000001c10174036800800340b5858144e020006400e440000790704042484400d0f843e02c880303845007420031142c3d54150340761314030f807858401ca925101e03810002242e41c120b50208044945d480401c2c10102200b000c48100c0c4a1060007080c9150540c128001003041d41d038410580001001c421030a07210415424078141e00445c00051030f0381022a2031003110f285001000ca10503589030384168113810300740e01c1a00e1582010040c03107442d6074003d00a0700f00c01c441000151055040d80c480b120030300c901801d410314030f0101c1003401e010010340d5004d07036032803e81c0140310984030300c0e003c0103440c00390541040c80350300d81c0a18840440c0a00c1d00744003900c290364210456002c000c030180003880c000e45c030000d01c082c0c1c844024040047c060ba5034884051103845048502d103403140c41e20003000c0640324072403552159107180e28040c00307860301c991060444c400e40 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 747106196 1250 747104946 747104959
    0x11010f0b0109090c0320030411090c0a030f150e0a060b0403051b0301180506180102041d0606160f0b060414060d110a15080903030106050717130314100c020c 69
    0x141c0744e020b40040403580c0d140d015817500301350b4910b901080c001c055481240109003d8684107100c00400031345803412030b019078040f2024884400128800e40c014110700403011000154840103e0704000b000076141c2c000d0f1740d82945201040503c030b08074000d030001000e12051046c1405d0550b903070151a5002c83d0025070a2292401d210300341541d09400010800303907544104031107a4001e040150301c42ea411204e50071004030821013801e40b0b100500c22202110385130761148102c03454030320900d00080d00140099a100034280030790810042403440564032a40710722500300d03c000d01c81c0b410f034071520070040c400c0e8410b80c0340c8152047c007a00d10307a002c2640a032040781d034072207052a189000d55031180c00c401034a42011800c4800700c0d00100460503075803810301580f907041c8603036a010329082c4e81c1d20090064000086042c07001900061707061100791544581100c42908040d4520409501c611040e0301c1514504008080a56907181c00d2204c4034a03014001c00074004040364090107552907440455190143c2c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 747107446 1250 747106196 747106211
    0x5061303060911010201200a030c0c0b0a0b150a020c061c0e030d0b09010f03141015090c0503060307140f03070b0904141e100b0a11010f0b010909 64
    0x14410050006541d0024080210412500700400c00c5009111500e01540c07801303802040c40c4580c0c955103c0501e0311030700c0807890816890011000707440640d440500744880c10070301c20002184c0c910003a2140300710b15030001d030150390702041081100c0d09050102d100d050801c100450715a01041140c003030309060f00c1c0150354a10b02e0114052000320b0421815440d0f2400b000c3c02c903094004001840110501801403029007a120208400c0e078400380300b1070702c0e0000c40c1da40410002e0880001d4454400b42c0394117444000640d0040d04080d100b0110b2511399007070755036209004422a5200742c0c1440c0380c2c01d01d8414214603209011999807090f80c0105494500c4130301021000c0d990b10b101c1d010402c0c0010302510540c3e65180740020307070340e00403000780b500c154140200303041101e004140151050121086409600d04c00d00340c0c0100c1140041e10440d0040ca12410203e40003844030028841c82002d6900c0c0c50030f00000c110f07014211001144001500750403c049000b6584e400020f0354140c402100d000100103 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 747108696 1250 747107446 747107467
    0xa0303230c13051c0203070b0f19021608061009140a050916030305250f0f05010605090403020c09250e0f0d15051b0304060b0a031523060105040506 65
    0x2e5075142d00c101d501241c8441e403034032207541094100081502c00d03400c071200c0356112440c0200c0740c0900224441228000e011401e080402c120100071a04100d0040d660080d4140d20902c15110740c45d0002c040a43c068003d111109414280307103802800303840b400f00004500c101c1c803c0c0503084050504100c0700c0d12080440c242400511221540d182d0072186011016074a140291194010441c0c0380c0224054400744d40240402210482203107034000d00c00180d0501c9942d80004402003903009662542d65800007049075190101c03050301a9019030014222642403c0801c0301407140109082d41c2d0307284c0c81103054441147ca48444400300c4041c104501400341440c0480c201c8410300306600c0d4072440040810381403244100389040004590842444030f41d40d08a031151000800100590006204000080204e80d140c0c0c006092050010310340b041c115a02e4035003000c0b2101142064080940d28038a0803016645011490300305695610f04111034a89100080c0045c00b9038401c09004500c002010b5015 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 747109946 1250 747108696 747108727
    0x23030f0a1805060d1d01110304020d030306050303041d10050a0605070203100c0807020d082a0702030706050a1d06030105220606030207110103021c0b03100504050a0303230c 76
    0x90003000d0120f9850304584150307103001c0c0c030344482c4080d13001141420070821400c042c0100c070b2495824200042c0b031509e442d403c0c862955940c00d415010180c0e94880415a5901440204000c040c030030f40e80d144500c007400500300c240001074140c0c0000f04059a0400c019100c2035502803c4940741e0502a03100c1b4528000f1a0804c21400b240c01d0f07840d071820707442c2c2c405180c00c05106801004140e0844a40c11480b08055400c02010f0307808281c2004140e40c49200103101804c0d070900c150064440384c0c100310040c4e011a28041840d00544086035012810001859001a10584800c0341c000c52044e0000010302041d11844103001e210700402410718060003000b2040d607a4000c808122100300300035655002c000340250442c0310102d814680c0d031a0544130542c420300076200084604c22229001d50802d02c00f41d00202105444540c0501403250300c140300d80710b00d102d05846503001d8405420766000d80d180c014101c0700b5905005447c103441280c800c00701034110300301c0c07580b00b904502016a100000e10750b000e80c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 747111196 1250 747109946 747109949
    0x3081b0307050609070e01141005042103030b0d02010e0409060e340602060601030f0f0f0e0601060302040b03241c03020105010b090d151823030f0a18 66
    0x162480000345150800c0800501c4074403401c0303c40d060b10034440d252124194001001e10801800742208105816a45049401490340c15110b04080e0300d000e540750018901c0080c03410009852000700740c40d002c103143e014024445040812280304014624503800130b0b260501d2412820300440d941c1d1015002c002803a4030440d01c289180088420521104461288048448202da8442488240c010309410002c1442c2d100703844043c1c0261905d9650680110000c14130000c101c08140d48903030003c17180200034401d503417042800c051301050304c8015911840c034081041e8801c40c00c0610400c42000281100c500b0f883d041540c002048200090400441e40118400341106510801101e6140c030403052030000501c54505c03070380080c0302683c0e9548c80001135000c0c1d07a40803604080410000400202242c0c91025891504400018010214401c03c080e200d000d200c1200c021216410312521580c40003041c81400c1181b4008514010011152080f1405801c11600034410442d40c17800c00d10f03840f07018110 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 747112446 1250 747111196 747111247
    0xb0103181b0515030702010c03061211220902011103190809011e0b030f07050f01120f15031505010f051002030c0d02010501170703121b06090f0c1e0308 67
    0x141011440f1082050b802035410002562806201001050290242008584441150904c181d049458021245203d039614950210581c6819800308411151345a510001501c000070000721610001d410003000313142d4000319610030301c400102d0201d10142c041c04003045161600d1580c860885160140504108985851110006032400903000f60b000e2544c1c450210100c0d018065440e2179a61604e0050041c1500606140a070007030650007501e005038000e808840004901610108500884100000c40307008050321003420000d0000410702d484010700d030003000304540c0d40341896000a0300070380e202d940d0084955280710700c5424000d100b0b8400e2451214181c03050072140442c001c0c0209401d016607808030f1401010703039014610002e00203080d08da01080644d07030740707000e0002030360003a402c01000102d5252a200b000700180709030044810043c80f8801c150210202490000003101c0c581d0401e4100490b8155883e07150903100c04e00c0b40484c0c0d04600d00c0c3d59541020100c00511007580c12008 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 747113696 1250 747112446 747112459
    0x3060d05070b030c09040f14180a051e06071404090c090801090b010806010609030f020613170706031404030e010e0411040326070309060f050910020c01030b0103181b05 74
    0x1200408a100802213017804450030000c0041c0410008200d8111440c5130340303404103038000613181c85030801501c110f045420307044034000f014654440d4038040401100e07440d90032500c5240035540c0401c201103600003034141005204400966003001144c0038510402220684462207a007805002e80c0c40103010704200340007806040c0403030030280103d110a108408881c4200313400042c5292080c3c400034150f0f5849846950000031a030200302082d080003944410307003007141303100140d802001000f0304480a00040503054043c90f00101400300c2d40c5021a18000307800710303400c1000181c0c2c000004030f07c081013420181c414150001c089002840300540c5a14000380c009804028020f084070100c400c0c1448811701e2590388a8240c804410303006400b8010041014a2020b0142c14051202d80103500818079007941070500d000000360f40c840c1d1014010026070001c600b10309076540e05018101206a0a00b410b0252068000000f242d0b9070a03000080c01209000c40c0c00c180c03c0f0130016900e001803200a004 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 747114946 1250 747113696 747113701
    0x1e040b0402042a020d0306140f0a0f0303080711010b2107150c0203100b06161a0c0406230a030b0619050c060a27061b1e050403050303060d05070b03 65
    0x258000c1401d801111009885007174000500c443c4a40924415642c941d041c0c1540c140002d0b00b8403400e040e004a40c1940000c1d00e102c041280c210700d11107a0000c0d40a0350303800540e401c00343c0c00038100501c2c03541c8d28007051341014100051929240310310040700c4c1d4403040388810300000000307e60600d04980c0102c1101c4126981e43e030318132588118283c220a008605481e0f80b01006040c400c00c481e011000c007904003006003c00c1c01110401c3c0020742c5140c2c062400d00a40b54249210441201802c503150810080041400d1008035881141c3c0044424002400ca581e41c540d0040c01115000c1c9004501c201038681800c030000362141030542e24014084040041c20780464440940030742c00c098215215841400e000900800007809115182a481580c0c003000e80a24119100703440031a44c0140c891a848014041143c402c410094a48260540d502c40b208200c04890500c200200030320081003000510003400499004000c170b0760800000c40740042c01e030300c60b8948541800c0c0d1030b0740002d2402c03101008 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 747116196 1250 747114946 747115001
    0xb06040b100504050a0918110d0506040804170a030c080c0a150501170a0c0626180c013b0303040609080c01030e030304020103052206020c061e040b040204 68
    0xb500a81d0802c032030314180c17640caa41000c0308440d402c60100d03038040400150000800d05001440b000c0f2030002c2c00f40010603600e900c07142d2402c6001d81c0c00f1a861701001a0400035210400c00c0350001d107040c00003600381c054071a200200740181e4184042d222035400500300300c4882c020004820090381c0900140f0141e200d03504140000e0009208040760309120201842000801203140607859600c5040f60060341c1c1002011a030400d00c5001c4041032490543c070300e0a2480130405003d01c5090540d03510704103c03680303488160a2a40e018080c2d411710011039a181841c01c018000c841d47d4061100d1005032505030900914180c01350307020030981500000030003250340c80c3c2c0f060144041d00d0440c4121341941026200441c1140e0142201c680c0343d400a00c01304005601c2900019001044807040440c100161004582140300d47c08003110146e60000e1004030860050003490b5000105040c01301188840c40c401d00052000103000800d42981707034000030115038403640038980056002c3c14a50f442c540040 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 747117446 1250 747116196 747116207
    0x10914210a050f0f0a080f0a140403051b010201020f1804091e03080f33030709020901080c0708040303050c01150306090b0609090d050a051b06100e0708040b06040b10 73
    0x103c2041d40c0541c94503020b070040000741c03040105500c035018610305042050aaa5140c1081c46d24030700300500e01e01100903203030100c40504051406080a00f204540021480101c00703001c409290659006000341c500b00e030900019100700c24948041c04212002c80c0000400070207003c0802401074100c40101d83c100e00d54900c81c00c101034425103c07038140c1c0c2c81e41540341142007022036140a68807801480c407241003000c000c0801c0705889083e100307504100f010b0b0002e0b0401d580b03900b01000c160360100d1841c00e50740e40300482c0c5401103c034589051400c1202d8590303003d242309134040501400000203c039403059809500c07180b07481c00c541485002301a1245480700c050319100d0002d82e4400e205001049280c60300c480f100b401108604000e203030780c644850003a900c42d0000c1b51030009101050002103204045000c0644084260b0300242640740303030220400c52035801a801943c0401c445000704a40c0c1e5401010458000760021142010b47e278661000501400e12690542c2d040b42c1c26640d503194058020 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 747118696 1250 747117446 747117463
    0x52407080f180c03010213051302070209190b03070e100506070c09050709030614061e0907200f0706110d050706090c081f05090c010e0f1908061005010914210a05 71
    0x403658120b8824055027207070141c0c0182c01d0080d521201d0940814008184000d590805c08488070700440c00c101b45500003401e042003544a40c107600f4001040018820108903220040c0104842690503c1c025448116080245d8028403102940d5070011581c081e010350504002590f0012040c800c21102e40503105d40c1000540d0020702803a810800801880359055180038202c4010745607000c1581c4001d42104c005008a11140ca01c401488445200484c1800300c0c08400314110006c00c0a40d1608400404040303640400c91441d8001c0d440d91407103680c0c401c0032288403a41102c13011481508504280c41803048a42c08207403144540e4012a0a0503481d403040600450108810006e03035030742030800c0781c40c0d9100f403842c2800104115605501490310440c41d541e003002c0500031010419180c038013004d0f44034150b00464101c0d41701c01c04208031035402c0d440240c007500082c60404a441d2074101c1091210401c0f0f1111f612a80032194000f000c10440060440d1600c0c4449c00c0310f400740f8041c1040394948444 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 747119946 1250 747118696 747118699
    0xc0f080304210314060406060e0415080d0e030f060108120a0912050a2604090f02091c0c08030414130f0213060801090509061602010603052407080f180c0301021305 72
    0x84c2c0c0c000482c1880e0900c28030080f201180c4429a4103044181048002d01c0484110a400d090710710300814403100403c010303500c416040e00c17407082010700718041500e40402902e10758039a81c404801440071040c086000b401e508400e8000796201d0020140039504141e858016211000f440140c1501348140042c0c03400b45280101e40e020115410503c0703225205800344c5403a08004d2041104101c8240c0c290310416800320380500c0142404c11900003c1e03038400c03000c132980107000c50b00080c05042c00501051400106030030002035242a103059803100f5221060500039200b04808860440c0305030073707604181e40904064804640d60b4400e125040c4104110340101800141410004102c2e06c40c02d00c1a2809412a00020042503903144090070156400d1400d5404654132050004001a41081041c07181c0c24480d9056990440c074001540c00400f00a00c42401c0240007030034030000f02c00440c0426085075842c1d01c0e15041d8014488a40d28015824260640643c0b0005180807400030000d000c2c001d4800 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 747121196 1250 747119946 747119981
    0xd090803131b0302030d0e0a0302090a020703080f090d03110c01060b0a090f0f120c0b04030f02040b090f15010201021216020118080904090213090302010c08070c0f0803042103 77
    0x100448000c1c040b90103010080d019484805c0e80c00d012401044c02210300350f8010609207901c0d4480e40881c4d08408151004400740780c010800804242e0001000703a405018500303002034514059545030b030384941c860461414180e58412400603110500225464031380d85400030301440d507840750401955400503000c0e00c00551a1500842c060707107045040700845032078a401c940b009080c10358591540750007080803110202070030400501c03450010b000c3c0008600a8440302e4984e400c40c0184801d9403244c05510740300d5151901042595040103401031703040220070322240c1c41a02d0640041c1c0c0240b0480000c07020304801e07071082025892017001a0102075102c1d41c001d000d80188080c2504c1103040c410b400820800301480949400e040603840011050300080652030f50001c605262403c071504848190b0050b5196031103064442e401010641d00030040d0701d40806510b0407504d40842078419072030010018040080404c0074803018413806200856031007400d4003c59100c14001d002425030164400c12181c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 747122302 1106 747121196 747121223
    0xc140f070b0307020709060509040f1401140610030c021903121a040e030301060207120f020a0803030703050c040b030c070501060e1e0604090f080d09080313 69
    0x103100707601940e607810082002814120540c01c202d9106091500c204825194644142c0d403041d0042c5d00200035002502d040000c0454450400e0003960070000200b80303682240c25424010358048030960300b165500081981a02d60781c01c20940503800500c2d110050b8a030502403490501e12910380040c05440f800314520460f024095080401c04000c500c003142820700e44142980600b0f500d00039800d545c035041c00207644684501480c540b102c450581401048103c00c007012403542d00500d200d0160f5110031049680e40c00c1140c0880020781000080f50301120404119015a00140786035455661903180d2035442c0e030300840044070550342e10000003542c0404c00d03c0190045004100c080c505c00c41b504c00c0d10940d500c001d410306201b0352908e103002002501040403101340c0c80d405180c0b82d85030360682c0c0c0080010900d250018201510000822101695050400c078001c1d104420080c12138 = true := by decide +kernel

theorem cover : BRFrame.Cov 746942446 747122302 := by
  have h0 := BRFrame.cov_init 746942446
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746942446 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 746942446 ≤ n) (h2 : n < 747122302) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
