-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0925
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:59:32.723414+00:00
-- url     : https://prove2.me/submissions/927ed088-1d34-459e-8fd7-9dafb5992a44

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 166187050 ≤ n < 166366906 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 166188300 1250 166187050 166187057
    0xa06030b091b04090204091a100509220312020c03130603020c072c0109470604050d0614070509010c02060f040e0106050c0d0f02060f09120c030c060106 67
    0x2080803106000d0b80c4054801c04007510f001c1070703e8410b400090010114143d01a00401a1a400c002001400f505251081e200700001c44040751300e80b4140511240112844d040f039060024004a020984044d200c101d18440d14082d088080e1800400e400e03600700e1007021030194008078599440d2542c42c0c0030320001d845c0d545821030900f003403d4111a603a81c0c2e148128011003821108179004003140382900780360702c10300c176400744020759440d005503008154210369224509401c80758221540c1c000742311654003022607200ea5a4070048044810070080507018403e0340042d0800c000509621a582c04401032806103800007030b071031107160740741044034401851841040381c03c0006c58240da030085e80310b440b0340d501a80c103d034403480e07001c5c0c04c01c0440c40741e900b003680480ca00e0f0700002541c1794400014140380d80314038285d400c940383c090001d403501c0f84c0c00c90402015810031800584400a99185183d200d00544211800c9038910451160270b03500c2206180103c1d040068514807100007001194010405884c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 166189550 1250 166188300 166188313
    0xf1403040b04090506010c3314091c0917031908090c0402090d03080912070c030c06020d080f1510170c0a05030103080706060515090108090601051018080102030a06030b09 75
    0x1c1d901c02c85408144003d503900381503104084c414040b04034690301c8036250480108210052180e00d80342e514011500c0f03201c588204000c1c001d0710bc51003440300541203c151541240c4e603080044071a09040f00702200c000510007444000700c00c1f5101d003042d002000031902e41f041f49040c00490607051003d01d4580750301480c01007011040171780715001489442605441c0480c40d945891a4803818140a00080f45540801060071010b000c2e04030080001c6a12a0300d0807840309603200301c260303260f50741a00c411021591076070000303204044050312660710204100b082ca10483c10400014001904404402c00144c044254262154401081d094003c11050f03503103410400311070340003000b500c0705000052201002003404401c00c04650048406004010200390b4100030807482d5290903044240314038006402000419030024002c1013442c1601d0010700182a8803580601c151ba11005d110040c0c0052000008005000c071028030285005140010002c01c0c0c0d0761460a0041d511480903200250540004 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 166190800 1250 166189550 166189553
    0x61101050709090b0a03020a091b1b120c0b07080a06060509030316030c05120306010305060d0506150a0b0301170c180f150612060a14010c0f1403040b04090506010c 72
    0x1c0e442c401c4601d40e43e0081292030450380492000c03006a40300941100150101040c0440035400c86a103003010340c424202034680e041c10854600608405603c0e00f4100301c08c160000c40c25000071040700004030700f41002c03960401d569a420041c42120180c3c0000c0b101d4050090072949805090000c1c107a0740741c01c6040c00000c0001a440c0d01c40c0c001d08200300c04071206071004040c0103020030214245c12406403031426400110340e4085501c1140c0340f500083c64a0005955803504505112880c2c0e00100203142cad0340c0da0442ca003039001d14108141a1b01c8288450300141d60854440190b010301480c000502c10025001c0c0c5039840d111203d040203100340c089800c030041b108105001c0300e5120041c0200c141c2e0a895448402900300c20200361543c201d44d0004501841b46127030303c4454090070f4141d6180080310340e54204928022515241e03d4000f5000070551000320f07440c40b01021003140100007080342a20000301c0a4a517a10541c40041c0011001c80c040040d100640f040503070100003030a08404105c0036 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 166192050 1250 166190800 166190807
    0x1030b09071d1518012307020f0d05100506010539030301030b0a020304030e0406080d0905030f100218090405060106030e0c0a0b1c020f0409050114010c0209130b100611010507 77
    0x40b10644031448013204040005a072007583d03145a02d6000c4a500315142c222441561015800303840180d0240c101c124151201c1e00746120721003030550f00400078010201d1800d092402500000d40010b04100082c001300c11400b01064445080d890304416143c0821440001440c4413002c1412021046c3c1050004002098a5545013030340b00c0820000182d49584604d0b003592004194910744ac0c00503d080350108100c040011500b0100220307440c0c9080d959660400c060391054000c0e00c80740142c20420103481d08071210740140c910b61000600954502031808041240d0b8001194103a400d0740c8180010030146415200da082580e55030310140410741e00c032901042e405480f81c45a00044c020005210311044103000c00032410003030303204042d07650b4a59004210a55040f60050a15003032600c03000160500004500c0e07a4072a0042e1564284024a90204070340f403078004007505d2002c14004001000101c2d0505282d1142e088610f801c2005810000d00604182286515a01d568508014081c00b00c2c0c2 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 166193300 1250 166192050 166192057
    0x30913020f07171e1210030309180e010f092001021c03020c01050a0204050a080c28030804031505010801050910020307031103090703020f1c02040b01030b09071d15 72
    0x403c01e01c43c90781d001c000303a0031030007510403890640c1c41a14a441c080310040c91840080c0b040303040444880c0020346130903030405040c1009200090104248841c200720280c034008513a196210900e1f00001c20300c400d0201035003500c22411981800c0781e41c514014040040343c0b0f0074000003008070070001d0100e01007500084d43e5070040b28030710b4000c205400721280c0460303c07030b404940a410802d40240328508200342814007030b40060081c1d40c4a41c61502020a049600246103040d065004110380c0c02d421200380801031000829800c2c160348080b6860100201d030401c0700810045104480024085e10b141920740101d40041e00001d586074148024011075100014080d4040103043c0c0b00143c2d40d881c0d01200740c0c014401c00030003120160000c001c01914200200d00c06088a009071201e000c46101982004203800e1050410798031500050310080c01341c20f041e03004010b54901030400246501e02000051241241100c0500014840a4041c20b04103804410800a4502a07550101c0c00c1450010301e0340500 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 166194550 1250 166193300 166193303
    0xa110405040f14010617191b0f090501030e030d1104080a0b06040510080c0f1903051501060f050313030903060906020712052b090b040c090b032407170108030913020f07 74
    0x41d1019003141f0304040f5502c107806001443e200c0000304950910b0103001c5010b40103280c004510501e5002891354041e0240c00388041e900d101940c60030000c004104014241c4d141c0d0040401802d10004c20840800c2001c204104d0240802d0010391410804000684000500c01500f40000420821800744006600000b00f84210b41c0d08040c5c600c40b001185a5a40c0c1c1d80f4031502070848140000300f48200421040341080b100c58060005a803281400e070360f101002e1860302c00050080001a09203014080c203103220b41e120f881c164030708035070300d44482e81070712080f13101070780c00d00d40c00100b000c20004e0f604410b200c1852541025810f060120016801803504654140d00b80e4144441110403907a481d0b00a40b610340d801600c00109007000e04180c0420141800740141c1c15207000d240a005240000307014280c0111005009001494148800022040070700510f081c000c015100d0400d135031104503a28080c1c41d40b8001035407248440c4080010183d08540e000c010103104000001c0820102812108003e = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 166195800 1250 166194550 166194571
    0x70807230d1d0d060204090902040f0204080a022707080106030b0909071202030a08031305160f0506072103020c0c01030908030a0902010c12090614120a110405040f14010617 76
    0x604158000c60740c1c0543ca00c10080c085840020040741403c050761200381040d009940400112101c844042d00700c2c419801001c400c0c0d0300c0000c0403401032810b400802c140e4485107d4a01e0100300c03400c2b41946206090359400c0c0401c0b95540140880c56241c401c100c5141e42c2140d90b10301e1414085561070b1120308a0090920740c0d44d2a800160564608006501c10b8561040381c595682c50111000d031514000c10b00226601d0068806c4100014210780d1102d068501401e410042145087c041008550042c601200d200074a1000c500011582510484032081591405a83c40b00c42000e0b035410300c0084064281031500e0614090042522035082d41d5000e451800009101720840c001a25620040304008003d892819041120103602041440849241d0b8079501c0424440c04040c82060040348402c2607452601e00000310301540603000b442d5804022102d440c500780d101c00215081e500641206840e00303440350000f040d8015000051801001c0c54908601d032008503620302030b904440070f130039161031 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 166197050 1250 166195800 166195847
    0x61b03150e130f0c0f05090c03060d020f12060103140304080703020607050106030c1205010609020702030307020108070e03030a031e0608030a030905010b0a03060903030c050f040e0c070807230d 85
    0x2495900440c12020b03005250002c84007050302e41325140b10b410740103101d41d00d03841c0d5500107600e0405140341e80c01200c1c11910641955a65018001c00d1100b1107401d0741d0000d44010300041c10303142d4000d00c40d4008170a10107000c0c3c560641c1002da41000341852010704a902c01c10081000c9030020424409407641168000e58458042c20f00a0142c501900081d00695415200050107811045080500c0b44650028008160b5941043c01217000700c86010b5016041082104019071040482c41d5008070182850580108100302003855038220083c840042a07540310b880da0300c031514400241199550070745c1030101c1803c143c0c1650312070080c0182d81c414592140c07440000c00c5820341150a0f40540601302186280c0d0b00e00b4010302030f013600801500443d10b41078020604511a908a400c154503d0b034000d85018034140002d91282401454a541c800c0240480070000311403600500000e070240400d0540c0061029a4281000d10806201e6541c5e000c01c0520078000c0d040344d1184130591000300c84841 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 166198300 1250 166197050 166197061
    0x120815011706030709020c030408010605041103060111011104080109020f090709030201081b0708040315091e030c021e030d110706050306120a260f040e0402120a061b03150e 76
    0x98513082d07070840c159050000c02e046444441c00009002100d44540003800895915000d2208861040c2da40d03403444502003000a15070f502401740382d84940454400020300a0781c101302d001c0241c000743c21486070b59459039003001c10f52403e19940c2d619601c2c2103640da0054180700001604035009031200070305002c046070000c1d088070340d00d08942c44403810710750f40d10350740b00e155150503685a80140406ca030703440c81c00b410018685a840c1315180b00c05901c442040f183d010000350f401c0050440300c2084040003c01c18080300140c42d80d0b140030b8070303061800c0c021991854020007091b041c07c1c4910f20500c100302500490b03103001034002562204481081c1802ca070381e40c56800108802040800e544d174103503c10403d0000401c41d00d040c1ca80a041c0d40d0300141c002d41d00042000c4c651600c51250858181e003424441031240111116440e0b81061005090001c440f0080111900344007207a10251003480c1c0e0341c4444c1c440c2002000150310b40150380c0c81d00b00030b9100c03806040c8240256a000340400103258600284 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 166199550 1250 166198300 166198303
    0x1a03030d0510080a03020607030e030c0d0e03030d06090204080721020108070e030a0c0602011104061d18090c0f090c03041412120105030d05071a0403180312081501170603 75
    0x1c020b01484416244201380301d04001c0e59544054130f064001924210080d010f03150003000365541140c0314005020071480f421811103d1440958000da89408200401c0c10001412303c10903009041c403100168030707a442d1100c15824104554454918418480207250713402c4040d449030b103080755090030300c0b0310581c440c000d04039440030b002d10a06030144030700340307426041c412400440005c59409900178802410114141300e0b442c015489100c0100c0c040c507040b4000542c07030400c00c0c030701403801800f2400481010780b9021480741003580c558445800080c043c1d5a14144800c00141001c030584000415040110315440380e4800184050580a001100039400c4402444401594046049083d807100403800b40e24a401d07400323100d0103209115074001111403038003c00545010a4202d02d119100108003060b8803100c501c000c008404101d1210740441d52542d00004000183d401350116041014150b10041c084150250061011076540d08294140ea0782c00a014040341c40f111003001020f803204008607 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 166200800 1250 166199550 166199581
    0xb0403150b12101a0105041205030c07121208040b041e050f10060e06030604140111280306032301020c06070201050f01170c060a0e030f101a03030d05 66
    0x7140d000303420b00ea10609085000400345440c0e010240d041142c00c180e01d40000b00c1c0781c02040c0e1940424014801002011546550112028021b5058030720303101110076440d0070a0f007250400303d60001000b401a081c400001c40710703070f03100030b007370030078001c10709280d1110720207450004c0004040c13540038110300402c40d4a801d25201155401411a00802c207456446510f65800c03205d0381401c0f61403c3d500080341e01003070700801e016490160150049440c1c9803200e5401101c501c4030b624944d900ca2040c2c440881900c80140032202002c9071041c08030481502401660f40c205042c003040500b4800103001254903000e105641c420301180c52030f100f91710b110b20140079014030f60443c6194016001001003240c0c064205520500502001d407846a0b2518014070045150303d50070811035001c0021141c0d50b0a050b4014005140f0350f06050000d00001300009107040f44a44030f09545411010b040c241c3c80c2071500401c0c1c1c0070821101e00e00c43c11340106021a40d240111a1070a040310307141d0dc04241c08807480701c900c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 166202050 1250 166200800 166200821
    0x6180209010e03100b030f060f041e0b0a090308280519020f03161103040501180302031b041802010c021009030807030203042c040b0402041e09060e070b040315 70
    0x2c1d50300d0482880a9800102121000700f402406800c40c047c6060b9008500b9a00c60700c080b99841041e51200c1d01c610404950030099407a8501c0200b03a501c0115806008640c440c020390040441c03180240e103402019010090f201009074600c440918100c84211210386c4164500c0900002c2c040c1d564014200d0f811801050701c1e040e241c400240d01c000010b5071030045100f030580200b084c852005038031044990303222580310a52250401e02c400d00c000d41c8580c007060800004114614009510394000a00742400d082d040160001050760003903403810039004100310700c00c3d030500c0c4190102682e00080c065540c4031000921840841032403004003070113030044e03202654104450544494003850065078941c0a40a0a041d1040c0d010030061a6000040e0492802d2942d10010038251141d5a54250307480010380200d0303110351241c001c900640001c16404804960300103010440030840d043c40000c5a801c2c00c46220035400030785040c0251064102111308403a07100ca03040c0000a80742d0408001000c0c0b0390503 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 166203300 1250 166202050 166202053
    0x703020415121406010c0f030e10020c0a0b091012020705030406090303020c06030c0f0304060b040e0c0a0f031101080712090605040b1509010b09011e200106180209010e03 75
    0x2602070700e6552010070750500700b486200c03c21840702c0c82c265040c3c4a04080b1040c070f0000c0d00d0741e014400090010380d800c00d00c103840f034101440c4056043c0000f5164140242041006a214249100f95407601240f00c5000f400000e0401d0b181c80b005101003104c0b0820000311b4400d11000308040c880111350750b0f04482c0307810b4000c2c5c250303074440c3d4890500820034105440250700621600a2400e841d01c2c1036001c49000f201a01c418510700440401319141a8000030f10070780d040b40e42d90308075210b2925a40100d44220300400094071004a0765004c204803900d041d0402d00c0d91508640d0f0600000d40754050f52040c0950900742264a40d4855004548004070000c000011310b0800d40030310100701e42d64102c81c3c000c0b4417554090745956500c00040005004908081340c2c40102c55004200400a00004020f1481c040c50300f00008103a07189041a00c0190040d083c0c0000c08007514100c40751811001b00b007801c0b4540000340801441c1c452402900c02d500c0049a07d10b6038000b480c109140c1c0180e150708500c15002d0b0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 166204550 1250 166203300 166203329
    0xa11030d0203040b07020601120f0f0b010b0c070909050c1210020406090e130b0c090d02030102160b0601091419030501050a050a0f0207081210050303030a150f05061207030204 77
    0x4140001c1e41058404031003118402000c42c000a0001c5081e9060b107101d4921078074244c07100c0c3c40d00840341080c1e000594209800c1001d0340c0100701080c2040d4060f000e020b00d070b1a0b880180001e800e03e031140039480b004900c1d16040361500080c45c04034181c4504042151100c1c8060114100c00e0308205149940d100300d40d2001a00141040e04040064211408114010381e15615a680080141030350a8003d000c9812100051030302807880014200180d0090700706450380209030b003c00d00720392100c9917480d8050320081013a0100b0102c0050f1030b622900a29201001c98a0400301403840b01c41c1408030b91248003081c001001280700231040600550b0410300910040c21300c5d002c0c40004040540300400a1030803c600054240d18038021039004a612510707403403030414100e140707004c0d250006d00980103030102d204001403d554200084c502800702c0740b00014844601c040820802c080b10b074800302c0c424820010402003a501c0c1400d0f03413011414200b01504030b590b40c1c801140284260b42100103407a407503e = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 166205800 1250 166204550 166204567
    0x181b0206040210050412030809030c0f070519080619020d09030807090801110d05090307050102120f0f06060708031008010e0a170301260a02030d27030201140a1103 72
    0x500980518000e80e408003043c00e01d54012282407095000704604500e0003100a000070784900d000507031080c0da02c3d050300e0609540540060a010001c00b003140c05611400c402e02c56890301c1154072020070300400604401c07a285c046d005440d00b000402d41c035540446941c160803403101c550121105e4000f901400c015001c842d24024005080550b0440000303241e038800400c26a805114101d003035120511018100095203500c840034010050a03c0c15601082c444000010000d00190030701c0d501c1096200340c14a0040c00d00042124001c02e01200903c84006000b01601c9040407900401c2d0080b1855641e9900da81c00d00000900e503070b100711003561030101402162600802e440c0d4009100703402951107841c40640204450100380030700c001c1c50180384641c0500f1204444442c2200001a0546002c40400c0c0c001034241212000d500f008620140800c043c0b400380d43c1109501000180001c030b20450642d000286003400400c06000b10400005e100e600160242d585c12204000d4541281d54a1500 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 166207050 1250 166205800 166205803
    0x2010f05070c02010c0501090b0a091a060a092a090612140a050c0c100608120304020901050d021f0c060b01050a091412070b092106070c030509060d0e06010b0f04181b02 74
    0xb02c00003918cd0500c2040300514007040851a1402810020100c10f911424030400000a1444000342d651501355040700400142110000790144002515400c0001c2d181410151007124620814054545829000d00c40c0701d559054036030b0020301c0f60100240c08d03610100c0b04011171081c50003608041c0b10314003407c80c00002a42041c0305507004001518030900d9603506100c054007060f00c00a5002c1d85c050014461400e001d50600505400200681c402880c048500000c5c0d0b0451041030740016034688201c4180201d80c01042c22000083c60100d1800c01003039001825a40c8900941c1594561642e2160603a502c0d04040c01130001c0c071400b5101c581e41e843e04920340740e40c000e410080c01080302c20f0346880c1645131030800d004003d075804050f000c166500764044072040c1045000f2070520606004e03080260301c90f000940925121002d00142c2401b503800e0f03852405405a20603a4400b06c02c01101000054a1091360304403001c568625000c0c014520401000d08400406109580100c0c480130390301550 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 166208300 1250 166207050 166207061
    0x50a02071a060a09060806040b0a0902090703050405071d150a09020d09020f030d050d0e0304030b040f0311070501050a030f020409021201170a030c0f1103060a0204030302010f05070c02010c0501090b0a 88
    0x204031401d0f11103607590407200c4180c5031a442504031b9500301e440094082116400070541c0300341c03542c400203120111640040d081403000c4d01e8a00000703659004020401c641080000d0140c2404881a20350341032101696500d001e0050094250210000c1d4104058a40702070000240441000954881c601b0380182e400810b03800005078403c6040c03000000c000c0c180490403005210240c1c0d01d5074600b00045c9070250207010300b810b051905100811000010403040b07103806000c2e0341300b4003020f8846003085c1801881701c0300c010203c08468100070390800c0700e0303a000320807128a810035080c003158222191302078000078062548040c15040c00025000048c6a203500780c58142c840010301c40c5911020b6076001c6680d40510322004010034001061040803e10007058900350f40c1c441c20814104444d030001090400005842a02c2c0356900413505008258080c003400d000702014003010051440c05800c01089006880030203414042c550102c80c0500034290000705059800c004045400d04203120202c00500 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 166209550 1250 166208300 166208311
    0xf02060c0d031109010503010653010f060f1709010b01020d090f0501030207020f0d05010b0a080c0603011a2215031404060203070c150905060c030903030a050a02071a 73
    0x74548103d00ba4500b107202c050f1001a08180c0da02e07401c40c2e00f086800c0e1203580e51000504c054901d0491404c10b00c01441200444241307460302d4008a0700ba20301d210116550b10880c44264203280f280c01400754102c0b440a80086552601c0d20602c8805854001d882561003642d010032200110f40400c40302c40c00540080b00c01c48001c2e8201c890500c0e484a080b180030005d8042e1900e01c1c1c088403001c10480d171013a006441154002807140c04080c8a0311b000800c0301c282070208940d1039441d0008820107107081d4030114014003500c0082e001b0158031a0018a00d072105004026506072003446084003900c10f03034181c0702d03452012aa8a1031440c400d031101d03a40c07049240314051040039419590f141c400d200e402a01d8020410b0000981903071100c0c0e4440005e50002040e8600300001004480301181032104000d0212901d00c20000b000d00203030910b603090031030003000d860b8171820420501c001e401000017200c2d803054000c1c4001a5171388132221110b0203803182c0b180150a904821399111032604a001045000342c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 166210800 1250 166209550 166209557
    0xa0c0c0e040506060a0320040e0a030201050709050a03170d0902030706110d0906020607200d180503030306060304030509030c06041725030204110d18050f1f090f02060c0d 75
    0x1c4c2c2d0b81c04c0401020500390b0000900e0380c124039214010009200e07242e255003000041c008181045a420070307a00d007840096083d00140c0d111418081080d4120203400040e01c400d60309203010380d04684501c145000c0e034100007140c09800080e9850705810550280d008260b005040d94a41595034100801995544251140a01a9503180850980104007010480351340d034000d08000e0740c0d4034170251788000e01100255481901c2404c115491003040c800c00829000c40d80340c1d1503105695403540030856889402c0301d40268020000d0000603910442500e912503490b14103280d540060f040031034200707461100c440c0c5d0401c1c0c1c003080c0800e20044010102c20025683c20480b0465000b1605980d480720310007015894690245d20180003601309600808010016051a54605041814150104c1e001c4036400c06481e60b900c3e207407800300207040c0000452000c0120081c543c0d030490f1811403001e000e8008000c10358503070380e10304e040c00c01030300082d220101a00100308607114162940c3d0306440312000040c0c038000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 166212050 1250 166210800 166210813
    0x3011802031302100201061a040f090e0a150f020307030f0b0307062309030f07170a0309170a020306040b0601030c0809120a02070b0705010209010801090905060a020a0c0c0e0405 78
    0x11029842030360700c55400d01c000c40110310156002d106100c04002e920000315503c613540403444240307030741e90911070300c0d03600d900740d65101d25100f11300c84414140d0300100d01c00e9080c40c60500005074009a5051280c3e0040200f850040316451118020416141c40680d00f50010040141141c2c15038131417444604001c400b8030400789003404040c0c80340d03c3c074007558001c21040790254290311859580d00d010000f00031007003490041d00d840084c2c42e11500407000030050340405c0052003070398075000c1c00d03856001c0948010032441e6030310350b005001006c0174000c005101c241c2c0c0b60b170303599040741c108800081d01d500039081d1a003904040c2410b40081d80100c40f0310b07010a04082b042403040d480740c008070b44681200409000d9503a0070f880d0b8404140d110400c3c00b021846501404250b01ca640c100030600d04e441040016130301c0300150000f400290050348013091151070400b0f040c02250011540c00d501ca04007800050395100b0400064541100c6a48060f00700100c45001041c0703e03494201c014011f03805002220740 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 166213300 1250 166212050 166212089
    0xd260106021501150c081b060c090a0806100504021e0a0c0507050102030406050322050d02060103030f05090f12190b040c050d0515060d08310501020a02011809020304080301 76
    0x4e20304030381c148400012602c00a08020600c0800944941000750807451a511202403840389030510503a688440e90a0000310b0340c00a2510b04001001401220082e0041d49800d0365018a00d06103803044602460f00010f070a10585480003d034030007080e81c00161611486088001441c41c860030300b0480b000d10540710040355941c000010303101120080d94500b807450352207244800c906044208641e2208485004100004a041c050001691650390080600e0361560400601c41c40418203039505001080020103c036031603002c0c3c50540404e003503898501480d9203407000303854000c41c00100d200d013091f003802990401c51540b0003d401103011b5031007031900310b4036170b01081140b6142420040969004c0865920780040f24210130398807150042c5120032181c03d585031211654031200c102d1401c1d906903a00172151525040255003d0303010b00f07640480540c1064000707583e0703d480a0f00079050015480c41d28444080c00003102c806890080002d540300e0410340340c403030450b4000b8003038503000c0302c4403010508 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 166214550 1250 166213300 166213319
    0xf19090b090f0402071103070b030a050604060506030103030f020c03031801080919020d080408010908070605330406030c030b16030b060304020d031205160e040204080d260106021501 80
    0x12001c920040200d040404240d0410000754040d030f034100c1e140304a00c6146542039070300340450002404100b180302d607240350548024080310802464148203901e0080d0074450b40c1c4070201528196681400c0480003508100d200381d00c3c01090524280e490302c4000b4082044070f404000c0060301420070f0300d030380d640f6480b604000e94692180e826140d0b040c1840d849540098545a0080300101d8041c2c102e451805444004035400d6078200c0e202a240b030040083d000080000502c28940e20481c800f4001c0040c00d0311042092140b4829822210008035045a421684c0e80b598400d400440d400f19403003c0050b030300d01d0404565982214600d030100b01052502031014000e018001151310001c103c18650360b0b03903908000b04500315a40035800c000440e8103205085070b641c032031180920600054601c1d0603032001001465075410460b101c2c05140107100800042d1340c00903040701341e11014104008401c2c2500301801480007169883c4220642d95000003484e50b40100b0b00204000e603001030031055a0705c07000b040 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 166215800 1250 166214550 166214557
    0xc270307080705030d031e05010f1a0a08070807020f03040e07090f14100c0f060f06061b020f0d020303030f070f03060825120503041701050603120f0f19090b 69
    0x1250540c021491501c0170510a5101c2401c126032086201c25002100c00b101040320004d8125000310103400d1030038401401e81201d804007903101c070128203250214628000700407850240208050010000100341c200780203000c00c82c1c8211640b400c0f00d0319607503950110504404140d40007004038004c140c004c510381016400d950709403048243c80c005810790401c14041c40482544d82801007190448410300014040481811a98020380c00490840540c4060380d0884800b50301c00c006000e1070f034000c4146448412104100260125400c946181201d004101140c0b6030105c000d40c5070000204111840b000e03141c03e02d0080416a0710000c46641c0c11206074100e9119000e40e0310360380e00040c070500d0500890212210301642000054400715a22071500c10f41c0940440c0880e0241c00202c0d0520034412550030744107101c4000f01c005c1c442401c20b280071a4584001c20102c072105040011201d44c4445442d0803640c01101c030103102581da82a1820040340100040c4c90000000d9024000050004040c0c098 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 166217050 1250 166215800 166215809
    0xf010f020a1b09060311040615200a020d08070c0e0c030a02030a15060521010b03161806080103021206010b03070309020f0619180b030105090c2703070807 68
    0x14841c00e801c5440c1c50000c1c2544102605039105000c00100e890341c014000c0c9001507100795010041e442003a0108019200759402280101c43c0315181d9603085036000b2030158030ad02868003120140880710041e1410310048a102a4022028411403004c1004100040081c00d0007500350008154440b00280414002541c656041080510100301034400c4c5500860b0483c40e2500300244070303403001400d6203102900c1d41c002c00203c1c00103e0003040c0c1d120741290003544070080030504100c660504d0018a02808050072080300741003074170340581c04140500403407100c4170706007050024600d03a1000d0003000c4082c01d010403801105130215201c083c075000140141a07482841601c2d0465441603021402031005240590384050310424003102e940b42d01000b01418110020415251960b03500701410b005001182c1c82050050624200301d030900b4001a241500c204443c5808182c4601c00c100503a40610200300d01c40c1489140b111318004c125607030039650b900301a02620756240ea20b400d16519001c2510a = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 166218300 1250 166217050 166217053
    0x6080403080601170103060f060f080a060b03101e0e0c030c090705040b030a0203090f0a05030403150212090c01020d0f2001021b0f100506010c0b04050c0402070305090f010f02 77
    0x12900090154040603440704061514051502592400c40321030142a0b000340c40540c0c1c1c500102d4800320780c7e8000c07400542003c0800701061480c090031280d40b10709620000d4025551449505403c0d541400000c48a51000109004015801d240c03a0320710fa1a04036620a04c41c80c0500c0c3c401c0e074880210700c0d0301c102c5000601030030981c0603c9040c8080e01400408903810400104808120108098040c40c01154140001602c900d03040b00b0745441e251001e281017000d5030003050b0690024a0000441d42500d07840a5880c0e1002000381245000c0d001da0381e18044000d9001040007200c1d0b000107036030443e8030801d81c00c68420b0411344105954107a458918000007074610b012401402d0f41030f45d862283c8040942c001881c1100645004c405120b030359a0005180d08100400c92400a040090903015440000c00300080d04203000041c105400003000149881211030004091000c14000141600030107482550380c3e200516000f04940c4c00355840c544201c0c2c41640710075143d48a44030f1000314840640 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 166219550 1250 166218300 166218317
    0x90317045906150a0507050705030a0818040b0d0302060a06050105041805090c06031006080c041508062103120c0c0304051504080d2c0a0506160209070806090109050106 74
    0x2640c0d22416400100503c1d08400016460409900c0c0d90004258507501665101e448560030324210b402c00c02981e2100744268403a082c08000b0070606012500203025141c551f0464080290104016110005130b05030300644d2341000806158000c5006880f505c552003007000702584070001035986002d40e010700d0350845901d2100c140d00c0680780c2c1c011500718031a20301311400c184110000130ba240d801120043c0303c8000d114030421100350402c014030b42001002c00a2410f040c00c2c2154101c0c51f5407210f031b038082045001c0d400f1039525125000d0000e050340154460102d84e2803214400d0f556030380040c4400701d81d0840c100024001143e1081640c000c42c0d8590095440c051178030341040604c1c58030340445150218200800665110300300440c210300e01b000d4039111411862220205a003000200110900480c0c1642c0c00c0c0442d52540e003110207841b400c80d4003035100c1d8620b0390b0308a14403100c540000d420011241c20700c8281500100d06621803441100c1040050f03803a46002c009a410a10a0102140c000c1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 166220800 1250 166219550 166219709
    0x1052404090303110f0715020702060901030504140a0b06012c01030b12060702070504051302010c02011110020f03180a030203040302090c160f02030d0f09031704 71
    0x30303080080801d02901d00483c030114203800b1060301d917010b00c4200b0780003130001420303004001820410f41c50f0321310000001c5085c07134005d40100c0c3c0310f40300740c1001c1d41c101a41c440020341080b164411501400114204440d103e545a281c082080141031320600c0c0881e584204c4a07c0c410101404a08042c8074268408902d080140040d4050059012074581c01103880d40c1071684040204200fa1040860f6401060950b04c0c0c04144411524081d11f0203415908118103000982d030040c100c0001c0541c2031034405070007070070012240d08200e2112062020f0a000240c02c440707803200d040c0a54041c0b41540404c44101301803e02450307445100301001400360700107000800140c5407601720030764040b2825110380d1401c00d2540300d2982c1141130700811a1101ca0810021096003003c001e81e0306034200b5802c215044170440000503001c05020f00c4003c0c45012414046c1c406c2d15010006d0714010104452188000100341c841c1c68000900c82000d0070390034466142c42c01050391051704400039000030074144c0b0001c0745003 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 166222050 1250 166220800 166220809
    0x30905120f04150509220501050114190e03030c0c1305040506070507020607021210060504060807120f1a1b090609010302070501060312090f0b03060108070503150d060c02010524 78
    0xe440d001404e21400b072003050f8490b1120b6028800b0b1200c8042201040a001d10852044a106803c06810400b03110880c403c103201800480724001100e48180f101c205481d4011075004052452803905801301140c00302c0c0c0395000003038803641c0d04e400700c0302d07000c4807a540301203141164130803076020306140d000102044030b0307501401c000d1944a0002d0002e070f1a0100540105d07051500c0310f141001560701042d0114020075480c46450085c090444081c08101e2801c01920b07aa89441d008200300009126000c40070014a120304024096215902c0082c28600c0005461805070440318071250305a0380a09150702c19440e001c0707c0403804001d140ca41004d80900045000750051001124150340e5440048003003429848800382c201c4a030b0340c40154090030b20013a124020030303691000c03141034800d1052040981c0c01108040c2c0c0480395283c496129514000740f5007020020200050b000b03d40a0a50020301c50b140d000a0459400c0d43c00a00c00e9444501d00030242c407002e82406a20981d024000c141c56290 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 166223300 1250 166222050 166222079
    0x140903071a04080d140118110f0901090801090305190e0102280501060807080714030a080c0307060606080a050106020d0806090a06050402190315030308040803071e030905120f04 78
    0x1e07440f43e81004145064642101e00a1404c80b031580b041c1d03401040040c85d1207030303502c21020000c0da05000c543d00c40501d116480c010842d82075203205000c42c40e2001c41c1d10501903600102042002070190341114140940158000c1030032208103001e605410140c0d030b0003000e840c03441200613801450007440141a850076070b070703e903083d1f4600318202000802c0403a10901441001e09446c0010f420b08510f08401117141c0700d2503902c0110750034081124000c1035500031883c030007625000000c44e5550748440401c00d06501c14550001c00d860b107030960108446a00c10100740c8240010b541c20449a42c82e40010b90f52081c032148410300145201c0c0014150782003201c00107402c410200804500c081c0c9682c0002c060b0303044100703000752915200c0100207000e80c0c14020140e10440400d40510440d003903840007000c843e8018000303080000000b020403406031280c00031141c19110b94411515440302c1c002e0040151041c00c0c020b41e0b5521030112890310190042c0c0c11581c4000001e05103a190510306203840c0890103 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 166224550 1250 166223300 166223303
    0x120106030903050f070302062d0604020304030e060d0c080f090307021201150b0909010f1a160206040b07050c030316020909010902030d0801030516140613030c09140903071a04 77
    0x3c05100070020408160302604409210b81c01410300e61501c0c40300000503090004154000c009014500119890395005241d00b008081d903004d0303036903030381e6080568062504a154a8005600140d107800b020403c4d40a01c01a4100795558191511050f03140701607041c094920040a03002041701400500c0c02080c100d112010100000c15034007801c1c012500108102e9010f2002d8003000200b601071442e0036002c4174054400700c4030a4070054100071203902240826000c19864210000f0f403081c4000003100b88294490380186142e07030303070b9131525600807140d0031009003250144903030a01865180303000310607660030381e81c0358503080c0c400700c650740070440e0396000503044e56119566000320b1009600e0070301444007a6803d0303450706403241d451890001d00d054847d0613190185628500d041c00340c1c40c1c689100140d8001c08640c0700352685114000064074922941c401460410b04160008148130150004000c2c2d00b800401d6501a0380c0700100300e500c0348152240200541c00300c0102a011652a500403174006 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 166225800 1250 166224550 166224557
    0x201030b0402030702030403050f07030341090f0a180b0402090306040b040209090706050915090909010c091202061e0d02030a09060b0d020a06030c120221060105120106030903 77
    0x345500c00810200d900655920300142c10000c2e041c401d21204126a061007441500200302031495038030003c00b00c01d1074100e002d4503401c002035018880200f40007030700c1d014040b0001c450081c0c16183c0080a60368080c8020ba406070912a00740c104900c0c000415204a40055440d4044a031801000f8002080c000303006a0303100343d0901c02c07518162010405103200c0e03445141417050703608280c01040381800e4010660105a0b001803001c0c483d01e540002507512070441035580e00941041102c0c140c0003030180d410f943c1d8100d00441e081103001001500840503461083e21040240c0761640c1c1502000420b448020b5009541000340040030700b1a8900c840703c01001925850822003a0540d4000f40c3c0e1054440c1410741e038171140c070311003804000d10401101c081d04580d119045092a8041101a803651180d5414141c3d0f07030f41500320b114021080300304100005c03402190754800d0f04103000385801da09118010002103200c000344995008404842000c8400131088070981e103003610850203004140c0089081 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 166227050 1250 166225800 166225811
    0x20d0f11100906050601140309070b0d060306050906010513020a050f0a0c150b030c010c020d0303090516170106060302091e030709020d020c06091207020f190b12010503030901090b07020103 83
    0x84140510655102da0b01c00e02c400f141d507051110004000491b000c1d19550030300300c20418000d021000095681c229000c1ca4002c0c1d0f103805034513864800402c101d6201614060610b03080005111001c2405410307120122010380d0070107003a05a0200b280aa5480324012600c2040701c0d84000d03030380c00050410b6190626111400c10007a0380e8510865011401c10108262580f18542c0c052134103100e45561040c0c01c0c40c1814400c0030580001d40d816194010203010305a991011100b409001c3c04444041212084041c2c411783c1d45040e8101c10050001d0189060351a000c00420801c1c42402150001c0400030702507054802d482c4490954143c810445592511901000045d801c06d1400500004002c0520050700c44180303d8640741007007001007a41a680c1c01c4005c16010011680c01a0390140d034055030149011480c80010514481324917805c0114005c40541c0003404080740e80050140340098004085545d80e00d0090540c4e80c00b80c6091a4086101143d0a000c00307101c2c44041c021603801454003160 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 166228300 1250 166227050 166227073
    0x506070e03210708040f080d020d050a0c0c03021e01081b07030f03020c1002120619090b0103060518011a0c070311220204081b090601031d16060906020d0f11 69
    0x910343d10644c4901c2d00c00381c608400300300e040824045108c0c4042a80054200c81102e51801441c91250807911020701070100162803d0040503840d9002865010300410400c01c070182681620b0900800801e000541c0c00c03000480c01041c00701c060f0358101c0155803c40c1490020764060781c001000c4403900742011b909210b01120034904101918800c07003e00717001641e5120306000c0b00b507111801845107000b0b0030f544e0305000c11131000b40700c0a000c44025500c00551840d901004030054080c03580140e9000d4052511110f07405c0811500a04a5030300300c036403480b621007140b1540c000d801009240c13031040c0c20020b810000714440d07501d03180205900401814804034182038028400b8402005102160b40c04981803000c40b400b00100e203001a0300204c181418011070000825194000301114105a1202d51101107094103100d8102e07210050340980c2d071058100307103070491501c1152051038001034410ba0000391150010500300d200c2c035041e95840442d040bc001c0150380d92414a500f180340381c410712582c0320 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 166229550 1250 166228300 166228313
    0x9120503060d050105040803040c08030a08011a120109050a0c020a030503070c0f140a0b01050102010b030c040902240d060b0a0c062c060a0b030106151b140a0506070e032107 76
    0x24846c0c0c1c40342590301e0704c0303041505049100c62801e4010782907944c03003000b0380801e213904200c09030304503507800d00c0f4112506100020b600d00c60241412114004107032000101c1e00700000d42041c2d2254641e01c50801c00a1841d440c00c03a0750300150100500820350400204c0c1c4030034456010a0030352b41c081e4244001d040c102d5a0b4019031320205001c0584190001c1c0743c40342c1041405c0c020f00b030050600344000d000352000c200005c1c0d12003440302c1015100d559a02166800c41d21405402409110340d442540b00c00e1800510041c4142c0c00308541c000340c20720741080801d403084030405880c40145107030f0300e0020481569503004e005110701c01002e0300300e44424017107440c01c406100c0d00082c240c210300040d1045003850100a02540c080c40c80e1140b1a1341028000d100c103010018446000800a00d06100c885076508440380c20407980b484040d082070303402c44400715180320008100c00300c184034104032141a40c55040803200e910a03500016031681007044480c1d11504960020403200240c415003610b403075943d82d20407 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 166230800 1250 166229550 166229561
    0x209070c080412050f011401082508010e0312070c0b01050409020f060a0f02060112120f18060f08060a0302060901030b060d0509150705120106030903030f05010308031909120503060d0501 82
    0x444c1c80d84c0c002c0007034900320a828013500c2008030b1f241200c90000d50500000b41c0c0c03603408a100c1c01c1d864500e41001c00e224004c00c120010700400446008220351520001403540300d900000c03954103010a03a5001c9a40e80d4425003409003603613000540c940240e400c0400b00800f400c00204140d0f07004c0d104902050040e6203000080082c00190b84410304081480c410290428105a00c1800741047d40d10721400841c03514134444003500e006140040c1e05400c05403080d00c0d078032040c03136aa000c40720100402141054200340601c0140c81641c580c015107a84640420007000d00c5400000d4009400380045106940227070841c080d031010050619040c0003400150300d04450341283c141400754020003001c02c1d244510000310b03030441d26070f140c940e00e0858400d41d0280910b1040c414041017580d960040e0041c94802c0e8404e03601d014041e0000c2c04696505e00700034001e5081034900c1042402d001e0900e022054041c822036003056400802140c0d41024900282c0d200d0b00001c10854200c40100600c1002850a105070b = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 166232050 1250 166230800 166230803
    0x9060222090e0303010b12220507090f1b14120a0902010314070203032418070806010203130b13080303010e070e0108010806060f0102010e010c02280209070c080412 72
    0x42551a1486010940307042c0881e114030758004100502144071840200d0391314508050481450341c440c90381c015039801d9003126442d0050819101201000400b25147c4c04841c0304100501c54002c0740d0095104032414400000c92002d480074078140c45900800c0b2000116032042d00b0755040c298103407590030006000b00c442c2c01c00b495035079019200310740c0c1520855280704c4c0121101445031410040c040e6991001030038080c00c9038118003540c1c0c03402160950901102101510898a00318030013024002004280c584001041d1b200d80029055480041650b010641d0705400030203a0f490007000614076440200c3e4540d007024800c0001c0b0b056201040154000d02c4036035030201c0316140c62180104455624501c0c1410086031100400985000140c0150000c1e006c645041c030580c5442d0050340141021201e140c203e50030f002c0c1309402c40e50045221203c4240020300d01a40508240d0703030b595915801700d0001c0d8400120f4000c00c01e91485801301c0300d150342c07091310b4031407406880740d89006002201d45070 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 166233300 1250 166232050 166232107
    0xa0510051e090f040b040809030c13050402010206060114040b0d0b150406020d0c021003180b1e090703051203043e0a050609010507021f05190206010602030d090602 72
    0x90220306824030b96001a8031a1080c40c00b8040360610303a4940a07180d002410241c40c002c004100140b10703540501c6903c0c81070a004040109440510054501400045400383c4c0540106000510507500688403241c84206100525141a040c549511400d4000e0348401e1109680c03007024203520384406100c032080e5112122816141e625261009250030000c590340c0040054280040b0016241c80507141492202410040303a1521000f1a01c0c0642c40756080c013078a0809148203100044075200c8480718800e40d001c082205d6a0b03034550601e130392504588001480303907004401c5d0002d0048a035000c0c0d50840d2017000701030140001203440301000100ba40c2d801c15460001282c4c186002a04180ca8124050549500d40f01034940f800040c4c40b4022075182c14184000000c212003155036110710303160b440100700309502d2207e5291100a0154200780a00b21081912102142c042400081c885049844540c004e502d0502003c40b2070000d400128022030b0180d40a11140070403241706545030049941c45074 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 166234550 1250 166233300 166233349
    0xb0a080f0f010204060915050706060311010909091505060d0b070306061b0b0402041a0a0e0103050f1504080912010c0e1009080a0f02030c060705010f0b180a051005 72
    0xc6100741441041468035565a204000c03c020598100070121b04482c0c090251a400d16006a010754452103142c1000701881d04d030070008030400181c0324a1040410080e13a0f012031140e1112150001c6444560380503040e403c43c0c0b4040554140213403c01c0b603100c9401780209480c0c0c9820f50350a4021401615403402181c0c580c5000c0c00019400583d41c0c0302c00b0350007504504406120780300c8041c0032901a0019000f940c0710794049800300590b00f0001c400c42400f0b414214600d595100170450796100713000032109400383d040074680254001400384c1942107010305c00728413a00c0303640d9503609941c0400301e9aa0000b4581c090280b10960070f01c60503442e0b500c0764948401464174041004103a002d80301e928400d00c0b2800d201405580000a42c08550551100030248121420b000192a1441e03880d40c065015a00207103a00800806400ca0001c401c210071003480303142241010000580042c1c80c481c030200707480500044e07034284560001504a015243d030b83c038059031640007140501480b000305580b42d01126 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 166235800 1250 166234550 166234573
    0x31101051c051b040b1b010b0303070b040204110903100207020310060603090506010509090d0e04060b07030f0905041b080411040c050c1506030a08070305040f030b0105030c090103030e040f0b0a08 86
    0xb0410210f078401c0ca05668a810f0810704581c1c0580203000285180001201c50501c50341c1d801d40c030012690348000c044a84803555031400d07d071918800c5608a004508044040c8100c200303d2094440c0004c005003e00b4850781c0001c4020300035009803030160703030611441140f512000628861a0701510580c1ea01040e0110311b82072080c5040810f80c4414040d044000420101c6107004c584d005032803c40b031a01926612404c0005009099140c00001043c600041c915003015081145034502c3c600a80f81c10000b42c5d41e03001044203c500b02c0ca2460b28031035009540e005001d1140c800e4540c80f52007400c1051514503000c0100d002c0781e0702c3c1c0c44401d000c1a000500d008000c02c00b041125030308106244250745924101c00803c1d11100107c3d0700030001800411400c0415020314207507070241820f084482c580a641b0304103440f00840a2244c0c500030300880d0051101c5082c01e64107581600d415454146404403428140002000e580003070b40d003080d603503205004090751110303104001400020b005250b1010034 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 166237050 1250 166235800 166235821
    0x903060f040302030d1503080f041802070302190303090501090b0601030f0603050c0d03050705030c0d031404240902040e060907121203020d0f2f07030801031101051c05 74
    0x58a84804414100c0c20000000da00008566280e148003401081c00c421141c4294009916170300010000c0c540444c00b8520007801f0400f030030445040d145074860024035514508124030a203080900103801c0403131006821101c0c0881e0203401ea1103460b00003000107041c0c40c7d40d401c4540f208004c5540302c0c245001e0104560b49801150152007000d50100061403541da50b459450200300c400601506c1d00c0800e031000c1c0f41c01101500c941e00e030403000ba2640c85660b6071805440300e90b04032800c00800d00d0100c2c0c00688000440c02503128641c0212040e203000c107940d150411403a0318004800d1007586800380340005072035502034002211080070080000b401d05600e043c0c18181c903a00100c0703e107003488000d03d001c98050124003040c40c04a00f001640e0b03d008000000217040300901000c503240c00e02804400030142d070300c5071680903a0500201961180042c82600304d07445907080140000702200d0050020440e85a2450502001418403e1909000404814075101c0051039142070a81c0c640030031020050 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 166238300 1250 166237050 166237063
    0x114070f030807090e040b07020f0d0201050609010905013510020706110703020a0b060d1a07030e06060a140d0c0b03010905070201060b0d02090a0f17100605010f050307020102120c0903 81
    0x20030b410801300040c03c3c03480c48985840c0040000d003640349003d010035903c40c028810100722001d98070654001402400029001e09419200303d07018030801000060103008605c90799041c1d03a003800c2104e1103120324100c80070a0071520100440041206030b21125060b41c200b000800300307000404056110390007401c202e011102c003000c00c1c080d5800200240030000b94003113000c510580d40050301c104140c8a03400842d0b00480c80010040800e031085103031340c18441c01052000c0c441c0c0301585d028040e0300044d905154640f0130541e00c43d600802c02120611890944c8011030128040140803c04031070181e444d80000e00c0c00ea07521401070070f20000014803100181d80943c941c032030404d000900c00d2130318180880c8401d1244490b01000183e0200c3d40c290642d0300c203c5400020003900d02c0e00c240181e11340c180311100742600b82510819128240e14440c4030f5080b401150221030b0141c480000c03000c02a4810748450b40001d10820841d5401c0220b1454401140d451134090304450300050344804841003410726218 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 166239550 1250 166238300 166238311
    0xf060108060f12070816170d020601150c020303030a0f051806070c05011b030902031605030304030f1a0c181f030c09170c010905030109200604050d08090f0603011802090114070f0308 80
    0x130412365000040c02c0c1c00207540340c1110030540c070014450318108030031079400e000000001d5040c0000400d210b10b10007039800c4a003550280324010000754540300c0d80c0c03030183d085201d06403000b90010700c005403806000d0110700030380303038011000840c0780280700440d80b107461079508050300403a5580101e541907003403c00001e1511940001c101c00e1690821000035504e0159100041c14821004404030400019200100030145c0350b010394492420020800300081d080000b28111401080842c401140f0384070055200115034499800002003900343c04a01501400c410a02032281803d800502d0100703d00b0016101c130340b40d1000d03102c05506e0000040c80100f06030b06c09803090381880c9160000c60203480115a82c0781d040c0c2140450f034904540420303820f00581e070016a2220300700d4050b1301401100001006072902c11a80465090341e00410416140002c0c010004184458034002c0e460307842541c01040c29000505108001030b00303203010111107070310440d02202d071050f00005170000c0680000c80940c204 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 166240800 1250 166239550 166239553
    0x5070806040308060409020f09130215040b0301090c03090b010f05010906050414010c0201032309010507020f030d0b040b090106050a090503030a02150c04030206070b0f060108060f1207081617 84
    0x504068030002c1c243c0c9400781615205070740e00c0724030004566403070b5800169100054015203c628000e4031030407105001d1070341607000d28100c0c25000b0385103950100320340075280b190045a0550342400320f100e0003064010001c42c00c1c0355072003242c1c00100c2c1310b220481d0b0003000b9078203c0400403800c0c90001030981c40154040803d00c5001c0c071040c08400b40340010301141400c01c0c07038270078041106800100d025180d8001c0d4900d010503203e4640d400c15403468802c03032003460103200270322503a01d441d40100d9803514410703a142c8441d0000d0001c0040c0070529001b50001c400d0003440442c020b03403074000059031000c0a91103480450030015944001c1c0c5d800080880080004401440c103002402c1c00c040c0d00e5020340c00c0c00980910120001800300c1e03c3d500c0130740d0043c64001c0c002e682ca4851a14000402c200d003a280030300700c900002c00007060fa40c8540342d21841810040c2008600201c200140000002404211f650314041c004021401c00303001c100b0403160b011007084048181c0c1c5030200500c41c11000700365400d420b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 166242050 1250 166240800 166240813
    0xa0e030f03040c08030f0a120b0a06121b02030403020307050d0c0308070807080d020304030315030305030105010309051e01020903190c090e0c03010c0f0e0312030f130c03050d1d0306040204020d0f18050708 90
    0x80b2b580741c3d0b064400b201c5032400c0c040e04c00b04514844d24003c1031586169040c6400c801041440258000042c00550307100b03a00b03c5a01c0c0d51100f081001c031414103038005003010a661010300001c0d80c40b01c058503245104000490500d08a41c1c2c5440164001c1041c15480d20350110402c42496450301962446c00d89210203c070b6118216203004055200501809040c1504c50400c0d1040000821100008020850640200c100c40c409200d0203584210151486441019042e110070015607400380c100303517800011404000d2502951401034030f6116020328090180c11000240c1e61820300621031031410690718010704a401840c00b50030084180c5103a0301961241c83d02c01d18210191080f00c0d001010350a005420307541e5a034407c03101b20748844c1c0003041aa055039000080090001e407413100c0c24240e48503502a40740c140036100c6d000c444514119410f0744940042030143c203059008240ca8003c0140104206a01e5003108050360384207210380030144d40e0324402500307000381800880301501411014000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 166243300 1250 166242050 166242071
    0xf0c08032106030c0603060109080601030b0126030412140d1e0527241c0902180705130b041a0309060f0603150a0b01080a0e030f03040c08030f0a12 65
    0x6951001140c1103001710700004c081041d581c0114519001840b00e042203a01c0b40d0b03100d1600f03480310703c02071013204801d00d011004000c1c0d03520b110340e098080c103100784011810540b611100840003030f440c120a9415080c90b001081903194203100f00c50348a085074890700e01900c001403000c200c42240801d400c0c00c00c88140103066501132600401a0300364001905041c5042180000915500240d01c3c8079520400b80d030050068080740301c01802d00c03a220448480304c1c40c1c02191004080e507019031002581b03d85000da800c003010740440c1c80d040e001001441e009040485500001c52a0034103030300704d052207640214040081005051095848401714444182181883c4840781c1e51048041c0c41e07a8041911040040d1140d201080f12010301c40421030900c0711030600b8031100008122000d588d5002a2080e00000e60f620701c1780c0203186071003110400075072034650b0681010342d4a03000038204980c5250030940c001180354041006e040c0c41124001c9041c0d07104500900a000340010300c091b00403540c1000c0310b880 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 166244550 1250 166243300 166243303
    0x190c020703020402030c0c190c0501140301030f0c080d02010b090a1a09071b0803010510090305030a050d15030501270804181d0c12070305030301120f0c0803210603 72
    0x201282d505a4025840340c43c1c1407900c010038081d401500c0c0041c4102014030504100d20011128081d000340c18000c1025107500c01183c0303560b040110303885d03544810001000001c6440c04040301403401003000c145100e0300d4090031414085083c10034070050391103881c954001d1a10b4080c15411101c030140030054044403804006040100441c240c0c0301d585a04001140180280044110f02800c0b140b038059012281c81c060b51540c0085c000c803405400804c2c0360059960241810f5410f5980020045040001d904012142c8c0e034018150404416141d03e920059a003040305404007562050b000815100c000014030356840b074074405000080340c1415099404103581c00c04590966405005940301b21803440c00d000080c042804100c07510b4540380c240159400c3c800725410030680e40c01c40d421045600381c00c0070390781c1d2280c0c0ca00000c2c145410400040103d5441c014640c0c0703181d07100f442584607083c0c0e50b84818400600d26480403540b40c20001e2902140140020b480d1a101d03a0100d9140c4941400000319 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 166245800 1250 166244550 166244563
    0x30705010e0a180609060801020304020d0209090f0601090509010c05130b0a0302070b16080c090604050427060b030601090216110609030106080109120c0201020d0806061306020303190c02 82
    0x60600c081d44010036490340b035154620015102480541182929101d500c0c0018140f07440303081496440c140c004595840c040c000c07030303014507001001043d0f8a5900c2d0200300c1c040340003400b0310845100d6010b40d0200600705100d00382c0241450840002c0070728000608900b520400c4280c401080020000306059111000e01a81a5122142c16a072120140101a0f000b403250752030150280d02c0d68000c000642001054501050103656100e01258071008400d019501a000300103500c1402800700340001d04042d0b020030000d140b5813114480e4680d600c800103e96905001003a500e0a40300c0300000705a0038104542030045c10131031021031403c194050502204510600010030b0400c1c6005010090383c3d6503025201c546c0030090003006003e9590720783c02d00030045d2a10444203030005e4401e030425a030080da00035010a0b010b0300640040140050b04690040004000300d0780480103102554100480c02490400380200c0d4000759964105411309407010105c030329640003039a060020a160840d40451034 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 166247050 1250 166245800 166245809
    0x9040b13090b04110307262a030d0f0c11040204091103010905010509010302060f090f0a0602030a030b1c1e1208060f040e030f07030e03060a060e0a020408070b09010e0907020c030f06060307 83
    0xc550700010744a81424041d46690400e48407003030000c40c12602d0099001084030b000d04608482c0038ac001020280c5072441ca0407207107004100e4048058000c00c401d00d0b11440c41c2ca41c0144014502900c03020123008681d502a080340450802000600c0024004d05c9011301514046411360600d40c5503130b001803200d03c1034500d0800c1e620b0001c0384502e23880c7c551105c0f80450f81302c020002140e00e522824001d680707800c00c502010009003000c0302c6c0000b60500074104845907002850140021038540c94104640e0009403010060298824980007c100200c0c0403400750080b5a0b82c1c11131a0030001c0422172120102200350303101da8a09992042042400811640300c0160003a035191074280b1400c058503450103406066415004117030401500c0451544031405a0388682c4400c009070b164404058200d0096005040d01075110301da050003200c80351005405558014913011300e031128682c01040308410b054070280d000d6403118080c801c40e888d007404000307400340401c00200b41f68506400083e6135140c0700e204 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 166248300 1250 166247050 166247099
    0xf04051e06191d01050702160b070201111204030506101d0f0603030d020403060b031e0a02010311090d0506070f0314010b0a03060f15030b060304050309040b13090b04110307 76
    0x242c0c5642998541120440c101e03000b6a0321400301c110b0983c00d02801c401c4442c08014000d13034000c240a0752000b0000820380c3d1541000324200b0b400e640c01950300000c5814405181d01c00d60740001c4a000201c1c000744082d5200d00081d00c0b1a003040303242c1000c00c0d0383d10b42080c10001c8211141050b804030a00f4016400b0882c84202c500300c0c0c44a101007070440c407884d1666507115000050101c02e0012940262194240c19411550803416061003c01e1844010154001c2c40e01b0807000d000143d84a908043e46e08148030140c546000c90750746c0010180e104a51044175260024020031032202c2d0001400c11000c22030341800d021f00443c001c150303405502c0501540820400104040c4101c600c2075201002601100048072102038a130542056494011380e02c050000341400500b10440c1844c0094a01840d80807000718188100d003001c010150002103900f036004030814440b030000c2e140302d000c0c008825000d420180c60b6420b0506255000100002c03289019a004003030030424500316942004280781d0001 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 166249550 1250 166248300 166248331
    0x40501080a150815040203070501170c0d1b111002090f06070510090309080706050703120209030a0c06090501080a020304030e1509100807030e0601060203040b210f04051e06 76
    0x1002e0480012981210b90b1900c130f180240c0c1203009103518a030b80507500840031115410740d50001150001442416200c8213850030300410088010745000d00900014101d001c84c3e1b910301482088188405000c0040c00035600f402e83c00c0a464051101c6a040c180e007010540c500b1034400302041c200642c2c0008140191000642001404030500a8240000c6640024041c6002030f04000f00403503107600a0141c140120310000880e14041c0d0200c032245039060310ba10750700b44c400001001c003e407c50103102d40c1500031140000000340a0003901000342040f5155202c0d814144030005140720401400b041c1058810030621020075042a1440b20591080300e80080a60659105680e5400340041e41600905449d0150802c0e82d040a113032481110b65a07130420807440c600350b03129a14042031080b00050b8108110a00260380e6590040000d40d028143c1c00502d0003810900300e541c5281192064210700da1182440200001032004400601010841c1c03030b034108011035910349501d006040c4c102d41c0807944 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 166250800 1250 166249550 166249571
    0x20a0b070c031b051b1503040f050708030711040e0a0210050a020d2c13140609060103200f07141e06072f060a0c03180c05130b030f0a031202040501080a 67
    0x4550702005252116111f40c8900b004c0c03030441f0340c8484492080b10345020706100818111800800e03500d80030703000184981c650840c20180b0000384881c10b94006180949c840d4900542c03205580b401c3d00c2ca159588031585c4604000c4028103221540e0490001c1010003820a104180624400030b000003172440a5481400300303c00281500c40c1800000d40150304002100054210b40c91106100e03041c03c1c1c420248540d50003004508031004024811030803c00f000f5500300500c0904060b240b403108000d0600c2c035001ea552500b82c2e10b0210032456544a61010314010144001510700d496508121001854603041078040034106440b5180407105c0090224800140c00d142007a91408955060041d01c599080079400e14014001a510510100307040c100003d0740038100c8040688441c0d080170704d10f104142400d0421400003181c0103021111510707554901859a4140216030a03041c072500180b0380081c6624000d04444400d80b000500366105210030032950340c1140d080d5520902456000070440c442 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 166252050 1250 166250800 166250809
    0x1206010917030903010c0915080c0d240909080a03050703090c031118060307030201050d020d05100f1d0604020c0f01110904060e0705090907020a0b070c031b051b 71
    0x6900c6804189003015400d60301c040040002e20000d0b0f002d500a1050f584016802d81d01c00d0350302d03c0b03540c5040c03000d14003074080c19104021041c0c0124074498124a0072500000310300c1501d120107071014070301009200c0200f40c0324414020348020802458148001c0060f91911041801030148250074144c8407800078820310b01c20303448109440e44c003260440c502903c900780242010700d6403441c540126040116400307021a070000c4203115920040040c0002030565004440d036800c44507061000e25001e01c403d5010000c1070041070300c0391000a0074114000e00c0c0c08003100c045030b41684491991180814030807541294044400d501840c19140503980c0d05a002d401c91500d020041410b1155107040d14480760160603030000c000080007200c0500c509904d811500254080541d45100421750400800350981441100b269000c0804c0c016075002000b030351902272028608486520000351100c41e91420540c021101d0f01c8004440b08004030244070b15611180d440c442024240300e40c3c0f5107010600c149644 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 166253300 1250 166252050 166252067
    0x50a020301050406020912120f070204020906121b1305060c0a1502040807050105040f030b091204090207030318050607110309030709150506030c070209060f030d0f0207050312120601 80
    0x502400030825403405061a030000d40003002030740e00c0355400c0e203441c0c0d100303900000391114a42c0a1290127407416400f511051a80d031310a007002ca80043d0284000c0d0b00030380d1460080c0900b40d8220050300103e140444078074000407030071040c44004910500a00700700b041600110010b48034180c030b016907107140c2c1010062411000c14401060348107040f000c0c030045445034002d0000c4464803411250482c0d03c0b2001034480b4090ba0060749111b0b48120340c03c0002c03c12000762150040044d405844448071075042c419802d0340a03801000107503400094036001c065041c0704a011840c8004601041d40c200e60f43c7d04c54440740094240c034100324140e010544445010310803a501e400c1c00038104c944903a62401314074044d18020803084911001007200003541c3c2850000c0f2172180d0a0b000d6400e00e009015402c10100000140115410108102031140075481c00c1101c0040d0540c0c2c0d44500301c0707080d104500245050729541049020380c1015510000c1c0328890801d50300c0042d080c44c0807508a50b03890004035800300 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 166254550 1250 166253300 166253303
    0xb040f0b1b01022b06080606040209011403010603020405010e0405090d031e090c03140105071209031b08030a05090102090f13110412050d08040804090c120f0608060a0e0303070c050a 80
    0x5100250280320a080c4102c3c000d0341800205107040030480c104d8800c42103032110700c1060103640220700011074615141c2d004203c0300300141080752043d042d4800203600d503002604041d010a074002801d020542c1c00804400b1404170440d818091494400740c5130f51246404200030f402d041c0c440d4008117944001104240113800b0419080000b07800c035062030140d503142440141d031620355810400c04d9240040c05080c0c031a64031511414407411300442c04038020005c125041e4100b0505c000e1101d03011804140c00341d600c0303003d00280e68981c100fa00c0f800c0111b801c003804860190b0f104001e16540ca40303e54081c91a2501c0c1210030031201d11982d40084058a40072000940c8072070000340204403461581000700c016405a0211061003d1b8108140c5030b9090554028001c080140020401000c994000e80c482e20554600343c00c10b146003440b0b41042e1491050044001c07600c6d01c900748008503080051540c00340030f0b01003d1040002c00b8803525181d110240c241c03400c1010f90034200c01400410881162000d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 166255800 1250 166254550 166254553
    0x121707060905030c1f05040507051203190c021207060f1416030305180a02010519110f0d1d090402120a051504020f010c030807050a0c1410060b040f0b1b 67
    0x180c03002040c0544800345c0c0228045044c41d40c94804866615603c241481a90b010008009140c100380410128800300505420144810000c000249640740e20521a03242c450311840c152030864410026070044e0107074400807640c03141ca010812907501003400040721b00385041c01840c503407400751218054880d240c0004040190619070034100f540c10b50107540f2840d42c043c1a00c4096501a00031501e40c10b0200c00a40054400d0140d13568054061042e607103041910300302044145a211076481c100b0724650707503048180e0080004035821070f80104809602c0f80302d070b89441e010700c2440303000104903110140010f03000da0f40368860789205581c00c10201c3e80943c0c03c4012580c80f03052107100d0594609080702c7c124000c91882c80105c8055029403240d040c8039034191034100d215030314070100b1030b590f80100c07000303004000a0035420000305452040103101102d0010140040786000380031a030030b681e00c50f4040054801e04000400203c10400004e10940c1c22410b0055500c202a1074680b442e28504402c0d02031a = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 166257050 1250 166255800 166255807
    0x909050307230c090c0405030d09050301060602030406020303160c1a3c040501061503020304060b1c030e030115171b011b0f0f0305030f0112170706090503 68
    0x14054000080d00129124110901420840e15040c01034094403038903041c0e295220525883c0316140407a0b19980c0030201e5081e003414640c0c0d620000745032000511018010412201040c4202d003000e015040240049000030b529062030000000d541c1c1c40001d105941c1649100d0600b403005114215101900e9008140606000c000c80c01c1703020105415206a2030351003540d05800b1506a01ca13034039014003500c410400702003282c4140c5d942d80c141001401103400e55030347d20010807071040c619440329140310166001a12450140340000850790000140b511a10800b88060401202007840c4403040f039040c81c00d5042641610b000c17a000d4504080760070090100c0c03a001065034a03405500d0128407441c50103d88840700d182e518418505803c00505000809060aa1503040048d04101425a20030343c10000038918680300c101284610a0049000031000014006c180054584481c09050aa1401c113006a851b1761a0b4846881203110080075410100d800d105000e41c95020411254111058030364 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 166258300 1250 166257050 166257053
    0xf1e0a06080d120609050f070c0c0e01140102010f090206040b0f0903060c0c010c030902010801260102070f120806090f0903070f1515050603180a1208041101050307081504060909 78
    0x20b4400c04401c082880f0345855000107188140b030091501410b0038255800b81c0340c550040c1142c029142e6601500c0d04400c0d4003000a80c803049072a99070083c02c003203003200011101540024203640b40b44041c100031360f05025161015030340350402c480441d0059502c055903544044a02c0b200c502a01080650602a43c0c0c10008030f0051b0400070842c6008040003000218604d440035402c0710503884d4007034000b071040e000601c40c0060010006444480b404c0c40040c90080c5140807070300ba030b13020020807641551210b10b081c0c1040041c9012024684040c01d100c080d40c50040080341048400801d6000b000b1204400b161409409104591180d50030810405101030181000034880c030302c0c0b2580e001c40d207180a1050005448141d0301c0c038251980180090310396220500c80058004461101c040107000d00160300700052070f80c101524001210744c9648441385001d00f869618055a002c1e0a41407040c1001002800c0d40c2c401e6140380e01103441103010010b006600003090042569810034450540392912800 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 166259550 1250 166258300 166258307
    0x3090f0a051e15010311030106090204030c0305010506090112030f0c0506070206041104020a1409030705190305011a030a0b0c0c01020a0e0f030109081804090f080c01050f1e0a06080d 80
    0x210440019003080010b4203250100369650001a4500c84151211006000080368001726100702c0e9001000401c8081d1030303070191000ca82c07103588121030000704d00d01c2c01c204200c000c2c080c00d0b074001000c0350503081039031521040360880d902c860307002001c1181c00c80c580e0100d42e009200c06e028958128013100c0042c6006034010350307119001d4400b43ca00c0b40c000031070148a80341c03c0c02184e00e240d405980700f403114900c0700c80c005095001034110700e40c180103481c03001c02d07181c440e40b40350b9610404450b0496091b9141d424410700b150301403030085071102c09405401303229072000100308040a600030044042681d81040b02c40c1c1a00540d0124003c5500002d00440c6003a80482c1c64104040704441900510a645040600304e641c07220f00240301b14418491010602c007027442280040402602c041317014041551031030700045c0360701c4017155494400704060000c08003d01c2a260701219090020761a800c01002101055019064940c040c078444400581440700c40d0300100f0084c0030040441d0326500700c018014 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 166260800 1250 166259550 166259563
    0xc02030d0b090603030901120b09100603060602190b04030201060b0d0b0108011d070f020c0a09090b07140d020a030b06160b24212505090405100203090f0a05 69
    0x90a1401c1c024191201c1c40c00c000018054180100103610703000c005001075546200c0c480c03e00c0340e02d0741c0c2c402c407881c00c5032186020703d0722401190281c50802810700340d002d8100c40c3c0a070405001c56210703034050f20074240d84d000c0c0c030030b03160342c001710b080040795201e04d0200d0160810340c0082c1860000481c650740141d450760460440c44d40241ca07549001d1b030303d5000303001d0074500c40724103c80e405039503901080e0114010384034845a00d50f00c0c81030ba0240405e07070b00880e018542c1640316161480c1d0740d807400428812850021500651549044041c1c80301201c1c40050601440f407042c0c60a940c009420000c0e45d00039030012010030009411303943c5a40103003c0340e07d5201d042c5201035400c500d4807000100303c25107604540c4000e4500d2151704501d40c01250502400c28551303c01034010b00900340c2c3c8400502c504104205440c1008500070020185035916020041d0141e403249010704041d00034840000c401240800704150003100c01600d84c6d0300c40718420700c1c0aa01d1443c50010b8050320102400b0700c840403454 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 166262050 1250 166260800 166260817
    0xf020105090a080c031909090b0d0203030906070302150702030d060602010b010903110d06050c1201080f030d0c050720010906031e1503020d03020f0114010311011112130311010813030c0203010f0c0203 88
    0x20027183c11801c003400314403024480000e5241d00104605403c17881c281001d014031a0003441202c00310b4400c8188840e00c01c03010380300500564030108103034902c1940f0380a50b00c090030481c40240b21903103966001030b11005003804001c1c162860201c0ea00c04c00d0706d500c4040102035070081c3c0184014246062000038541c440400041c0001100b0f002054082c00002e1505000000a004601e0300d00005003540c014010605d103030342004070810080740820300c0140c42819000003031143c0d260b43d02110b0009030144881c0e9024100b45414480941c20324244171440c100c00c0340c504400801c030b028801410b80704017205070b04000d40c402034069040050542c0010710440c03c4103410001c01401c44041c40131095000c3c07d01c00104031585a90340810607500c210404401036003844211041c22602c0c1b120315640b900030800f500e689203010601003003480751301049044940c00070302b404106400c1c00140440c2c026003418014082c030584c0b03c4c0030821500e09621000b40c22014030030400120071892002502c0f90310480c003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 166263300 1250 166262050 166262069
    0xd020a090e07050a0c0803070302090915030f070501050d02031005030d0c0501110313061d06011d1807050603040507030f03081f050918010e0118030f020105090a080c031909 76
    0xb01d0b680c3c081c02c100c0f208250b5a444000801549a91b07168880d803000b0b107103d081507000d1107440043e032101400203001d000a001c401c0b00941110081c54649541c0592120081d8028842000280d801c201114040114a200960b980d541d091940161b03540c15070040350980310340442c01c0c0090b40e10a11212413140b15000a00c81c20618034400784450005644035882d086030310080301c00180003580b14225001ca1085e001e0301046507a0340041c1440f909034800f0801c1110744040c000e2032003d10103a1540104004c081c040c0c0011803071240340d500d1806009190040000001180c14003e080004000a40e03011850040400007881c000700100c509542e4004c40c840e848508012903014840140155000074024003072641c1e80345102e00c0081180d00421245558a4400c1c8400510a001d14030300a003881c684400c02c80f2440c40e0040020130303480b020000310391500d07003400301012000c503e10f03014a8021807020340300e580c0c180703810b801c0d842250a0301d010500c00c6050380d80c070746170042071817002c45642d0b44 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 166264550 1250 166263300 166263329
    0x3060c0f020703030509060a0e1201050106031805030d0506150d020426060c090d060e1b0907080f3d05010c0201020327060703030f052203080702030d020a09 69
    0x39040e0380da4041030100502003031050007800543d00304003019040602c11f13490040d14455803040820006a50f1010006490351030b00c0043c04071075090b004070341840310320000400b071200054451030345900134017810300f281d0342c0c44602042c1c40d1b64840150071549085180555642c03042c4540010083d8032602c68402d40c00700a094140d204c1035540513480d0302030418400750000740d5a651030880241c0c80001007503882041e240341c05000c1045442018000c580040040001601a9904500b00b440351184a44030708152410014065800270ba0385400c411401e800c0e13911625400580302c0c01c90030501c00c0007200c0c2107541d50034610088032801a0f101083c8081d5119405844500444140300200006070142c3d0003001000303406081038840403d006040c0c148080506001c400040329540701070400d500280d10f9131158560344484d4819150489252408507401d001032180041031024001030203000c0c440c1000004810500034412682c900c03280c0c0070308550302c68081d45d0142820303c50b030251543c6c2d8034189 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 166265800 1250 166264550 166264577
    0x604120e0102030a0806040f020c01050108010f05061503070201110d0b150a050405010518030601030302030d06120b060418060606180b0301080601051509060403030c060506040b13090201110703060c 87
    0x80100d51100101039010310301e0071a1400c0181e510600240105801c950360302c0b15a0943e0040348050142207295100104180d49000011170a440a00141092981c54141070107069512071040351144c41070b502030a40c90b66560f07841a401001c880c00760b10000b540001d0103c4000705180c1c04446101400c942000c42c641401c42481c12074010381820b040840c100308003d10956000702c0141600e40c0440381413444401c0311201090a08100380d0040300583d002154002e81401c3d01d00030000500020500359019004079190300c0703500080135011a01541c0d1710744001d07214180c0fa00594032200c0e08800709203c0c04e5985d0714020a42400c1107507030048001c2c41c2c080400c4485d0741104490488400100a03c02a401e000803c040c0300d20f010419030800604001035081500d64802401c01140241c68880c1d528030141071107802e440005107001d02c01ea1414101250720b5a500e40c00604403009818006640c007071903c0140c4a07004880800c104600c500d580000400482d50043c15111019a6420b05400b545 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 166267050 1250 166265800 166265807
    0xb07020102011a1309050705030f0d090b130513090b01030818030303010e16210b0109060309050703110319121119060218064302270702060412 63
    0x2c12001d40e0f01c01080a041c0d581c8100c0d5400000c1740d140034005a9207982e0f0b403000000c0c41d2070b00c040d09920803500408440c1e9002d83d0844010b01c020444800003a01e000750740400e00c0402c0244d805400d1003004001002003a4850a80c4010000c5910014054907540c40b4104002160046000096102e4100b103007070202c0d00b4048240d034103d034941c0b020204e4603290350003411000d0707814a00440c10031650001c55016440143e07180c041d138490410f00001c10203003440004180ca80b00d0b400100c18542801c1c25000081c0b4009042d02c1140d0b0040403030014154001c00007800c10004248842010070341421840c10b201c403000f0020130355415900d4100403903c0752302c2c046445140d441c000b07200e00d015483c01c000114119400820403114100e045858500a02000038402c0d081400c07e02203429045651010202c41a480b2036074411504031146c1d410f218400010421520500c8001d001d2141d02e04031460b02d00030072504800b24450414024410320384054000d540c3c10044809482503561650740d40c082c18003 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 166268300 1250 166267050 166267091
    0x2070302030c01050423030309030712030f2d03060f08012408071a0d140f0702030f0406140903010524040c120209030703050601060201060f140d2a0b0702010201 71
    0x440001640d40350f50b400c6c11000340f0628134080c4d60313018041040408119901400041c0c0a00168003103030a41d40b078541001400c400000d40740b0030034408c8101c0c0032402504120300f5080488509105400c0343c080c8550210050082e0768814045181d0700d0001242e18a4103400a451369171000340e5083c0c01d01c074520700300780c4c8a02c15445058042e401800003400700340c1c241d081243e00c40d19040d140da860004005124001c40721551941d40c1070360000010f000344036440c4100260400c5c850b10040d800c2c94001b403140f41c0365104d2841600103001c0204060103140c01c002e003d0341d004040c014001c020b079182c00341c00c007191044004c0c4610003074018080301504030300d86489003103e00c0119603281c5200b40321403207003040254055203001d0b606109401001000842c00c0200324064080f41c2d0012070141e00e0001c412480c0d18180c6c00c044841480300d01990076603220b2080045066422081c0784d0144011100ea0068010540b20800034a5180003808140e070500003006080c0309100ba4020040c58800110050013040c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 166269550 1250 166268300 166268309
    0x80f0a0b011505040803030112050d03062106090b09161d04080c01020909010602010c20061f0b07030c11090f0105040f0f0203191b02031909031202070302030c010504 73
    0x444080040c052001082c102c00060b60580c10014a820f84a0440d5171454100360302131f82a46503402c42d18000c201c0d0521a0000e040720b6401c040c8015410550404000f8078107190b0050540211044a030600503142c00c9043c0c442d80240824066003880c01070b440c1c40d4560805000c080f11164900050070301242c6203c8030b070b030740d00c01c2482d603280d922181c0e29540150310091035000d10799028403da02843e82c803d90414000c2c005038000080307071140120003401007802d01c443c0c0c050314094441d070b014070402c0200741d46a10a8200307440f101181aa602c8644440a65402522198101003943c404041d00140310195041c02206ca01d0a00c4110b50100203410740107c90204c1441880401008142029042064080f41c407040200344403a032040c04c20101c3e0011101d0700a400c2211a4820041500340b0405803080c01841b43e4101e403e05461010b507a9119440f843c00b100b415800100d046684a0840b403006182d20016041d80c10041860007552060303180426846406140c810b00100d41c05001264203c4 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 166270800 1250 166269550 166269563
    0x2010e01050a08060609012601090509070302060712032003250c030f050c01090b152407050a0819020124090b0612010e010e0a0209010c0219030b010f080f0a 69
    0x681c0d0b01e805008413030b04011b8905041c80f46038010355402901003000c04031144900c17140400e056140000300001e503100581409403030f810a1405201607200d4004a8050940000c0c100d101e0304100d410440080600c11410700c055180c0c6203401003180300c080e0045006078482ca40184505082185000c0280071100c0010082010170540400080c020100d8850741c4105081403400c01c080001c0580c01d5420003042124442400300402083c0d10900e95a468100707029144094501041c0b251350120003582485c5201507900032440c801000003c0003d0540703564855007141e2a866840e200820403904203000001650800140a0260410b40080c0e52161403403a4110405032400f0b814400522024140580114080088804d6441c40411036402808c00c0301c2c9540581d0302d06006520006000780c41241414010007030340a250381c1c865103800c0c1071901100c001c03501c03111000e010100e420090340014040c81da02000007031000101d0079060f04944000d019103407041e607581d100c5501c4a40116004040 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 166272050 1250 166270800 166270817
    0x30313171b0d0c091d10020703270909080306040e0d05041503060e090f16120b0618040506090c01050705030406030e03040f09060302010906030b031209151602010e01050a 75
    0x20302e0012500c14180f0f02403500248038503100c00020040d1407018046400107024a22541208031003000344502d0420103584c1103043c17000700d40c1c0c001e11a920b1000d03440100031402c0d64000c00d80c00b034140c454000742030a01c0c0070003d070790151501c3d070391a4000300c40c6e0034810761030b140854203460004140301c6000d420a40d1401d03d440e0800c030170312010424040440c003c16640d1304010840682c03001002e80560400002446200604910140f80c040b004008500c03120303005a0400c00903890614000b00b0aa002411035002d03901c040116031504113908280c080304c2840801d00c000d116000c50064090f40d040c0d010740e07600b040c89200650341c620400038024010350041004000c141d102c1d52020709042201001d603840c1c1580c90641e258079100319017110021507030b9141c0800456812020720002800181000e0240944007800131752940c0d00001c1c0321089200c0080d4807515507580b8840d2700304002807928141d441d40803d5210891031041d00c20224003140c40b15221007401c1d0300030401d85d0402d448540e9220071 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 166273300 1250 166272050 166272103
    0x60f010806011b14030c12040608010303050a0c0b040b01080f0a0f060b1203030a140f160e06131d0a0219180e0103030e01080705041d041103031317 65
    0xb540e50301690943c00860f40321080000041c419003898a0100c0a00c00444c1c4501c405500c07507080032201180340c1c044110803c01000314607080b4520301c0c1103941500f0710548039458035000756002801e080004087c0040141007000300114612228162075007003085078a640780c00360712540d0701c05800d01c01074034049001d00d00400080064000040c994005000c1c66280d440480e1482d00d150001c0e81d0034001c00d510750302c405911400741c01c4095801004028030b00c42d2030420703007038807405c1d40800460b08003000130b85107034950140c484000f00c1e050414544120750601c0d41d135650300c60800c01964a002050500240817580c1e80495001361341c41280c0d4082c41901403001350505a0f10318650046554a801c0c0021000400700050f06407903000310300a480f50030041c11504001860b18000624a500380b001c2444140001030b08403103240321109450001c1c903113a488a080c000d98140b80c040d00158103100025641c508841d03c404050f048585000c0c07a80320304811910303600e8460b5000c0c84c4c0a0340d00f40d00040500d6 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 166274550 1250 166273300 166273307
    0x21031d010c060e01110c0d0f020c010f050307030b090c07030201050a0507050f03091c0509010e03071503020903030f0d0e070b0f0a08040807020a03060b0a0b0c06070507020a0f0e040605060f01080601 87
    0xc100140d1070000204046500820130413500f04000303108a503040724040d50801c5400c5a4140d000d08d15a1018149007004880068005400403903c41c0404c20040005982c1a00170f501010122100510250302490304916202643e440300204800550030a004190a03d04e00c0c05618081c6800d500e43d54180100c600d0310100750340004054591506c94082000f0080040e085402050340181d500c0d40d680f00ca4030740c005841c1c0c3e200840c2032130082d80802c1d400c0120442c80500164070010354035015a9908600d000030346503002d000c41558109100103501d018101c3c540d48564884c030984816201c9071503441c0141852406418511040c0c0720007000341011852090016a502c107100b918030904014860300840c040d10001e4100b2140c169444240c2070588ca0448141c1c00241265142285000c1201c404c031900c0782e80c06884481800004540390086544500c240b1025080800020248940e1820400040d0030140e80645d4100d143c1804680581441c8040c541e03440d40607110640144c5500c401103 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 166275800 1250 166274550 166274561
    0x3050f1002180f0a03060f021305030a0210030203090a02061306021c0e040902040603060e0a0b091b10020c03030d0f2712111005010513180b0403030621031d010c06 72
    0x7a54007121014000c00055028490340747c0c001a9510b0040c4c95505060740032108a00c281c2103c0d210740d021a030450016507440140e1903d212140c41d01517201e446034940c080c41d12201a40095011001207000e40078400b01c0e280c130314120b034603e80c00c0758140210303205050000394448104400003180d01e00002403504158101084403417000e0300000f121940d03501c6e000e0440c1d104090280054100c081c3c070905000007034401c41d401405c107001400344d03140003d092682a030003130802c180c000c00950460425050017030003d0000d00c10060246c03075590741c0a80702c1c030b001080d604510342e00b050b02e400e0414080700e44403640d01118800c0c400ca508104229a01c905146002c8043d0060400a000c52192401c034410b014254000184105c04180c950400b400c105410300030a1441c4c84c071926000c40e05002c8400f02c00303400e80d841c0e042031034510703d40c580c2d0604a0281485070801000340c160030300c0400549090300c48640c4514003da0718408150408642d2002214000880b9400074000c02d0845000c51001d40c0700 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 166277050 1250 166275800 166275829
    0x803040510110a0e0108010f05040506180723040e01030618060606050405010813080406050304030302070506040b0f10030503040605180306090c18060108040807061503050f100218 79
    0x115000c449801e00e03010306542005010039000701002c02c200005580140c80c1002e859006d080c4080190b04100c03181102403402c2c03080714480c645440104807a6110209215280c0340000c01d40750140c0707003445c40503040000b48a0300c1920882f840c9aa00000144001034806646082d410740d02c1326461500c41d403016100c451010051918a03424200c002815841070200400c225102e054a0700d01e031400242080d00014841401410850304140000e0740080460b27080c0d07005800c0694a030345450030300320001e020380c03030307008045100301d00901c001d0041181205105240140f200990f584c0c4281e000c1d41d090b8494400284030303500500062241d213000390090310b5003100481d9254a04010b400002c0d25100c0d09036401c19441d04880c003120110b051401000701c1c2610814189009820010002010000020400741c2001400700e900c00130805540c01c2a51100118000c0035645900c1e42051910b8004038a100314061240500702d04191004e0300940d1700040886600e031107541d0141040c0010007203503000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 166278300 1250 166277050 166277053
    0x6090102011410080d020f0d111203041104060b0909010501031d0a0b010503071502191509030305010e0709050117060402210a0b0607150f020c12030f0109051308030405 74
    0x5540e1001541481d0180c0708a00f40c84004181c54075041c0007500341076800214904540040035000c5140d000012040da04682500d00034040b80d25100049051904540e0741e0001c21100005000600010b01c0071810703c0003040f03804000842e60b58400f00034612400f290550050078841c01008950f01980c446240300c4036041c402495410a0012035040014041003165042d00d044010b000d5030808014150103400354000c00c030188000045e02035500c0854901100030711030480607007002c00000b0580a00103044910301400085224030780030b40980800d0003031203540140003002840070b5228042400403100180c603030800800340d400d03000303003008001001c8941240d0200502d92441c24140c5803003a1740030802c4c450081c035080284844050307030403050401d4801c1409015020110303e0b1040074401c254020740c0c00113020201a003400001e400340d0307064000d0031b001c0c10440100b500744943c0194840d9448440c11100c503a01c41401a0494400f0346044109480090240d000255020002c64000c0c8c000c10 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 166279550 1250 166278300 166278311
    0x7111e1e0f060c010905010b0102060601081b040510110c010e0a05010c17070308090d03050f18070503060c1206060304050a03050c01060e01060507060c0807050915040504092301090b060609010201 86
    0x2070125007103600007108003105a554001e054140302c002e1096400d0950244007803c56070a05200013006184042e00041f5511000702604000c06400d508440042102510002d20007004d20700152801d000341080c910640102c0b88416450f600c02d0340c00740206e240003040a0030b206d042c6801103d030301500613411102003c44000c03803103c1440c8030001e441a0b51081d0b84060035450204076403410050417900000070701d82030400f8001d1011f0311004c9141e014148100188035500e03694a00792400031298401601805203005000300e09085d44020070307c52144009510050720754005100c0d55200498000d002500100c201c000028800c1e401800c0907541c0000200720f040e00c6000300070981e007080e072100e000308800050482c2040f9040c010103860341d8103810081d21501e41404050708501c160011f0782c0c80b4120300c0082240703120219089d200689400781c0300f0420240340e0325014000860f4400c070302d1410b01c045075400e81d0010707050091943c0d059004440c14055128a41803002913004070903640d056540f2035 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 166280800 1250 166279550 166279579
    0x20303041e050a080d05090d1506090609180c030f1a0702010207060b032e0213121a0c0d0b0a030b090109110406030305031f0b07111e1e 60
    0x905070540c20403080322000d1a110b1921040250922440c2d0001c0000d8203d084480840d90300f10313041c0c0e0441c03170058030300d500003103001d01d0a6040b2084080301c0088252500c540400c4030318040e400071090b55082a001c0104064101c40140001e4810000400d40104000144000f031188141054864031506604240b4260584007900d9554201c400000503903002c6a054188001401083c860740e80130340240a019140c22100e07000151a0001504040c5a0010409580c07003264100c418100c2e40d5402040220348421030b000008800c1003051342c0c1811400a2072005030302d0f485080c0d0188200785c45e40e0780b45c07049860061000e41200b4480359800300703030b0090000200e500c9081d0640304100c4400006880012031406c40202c10b00050218003031460900f05000180e04582129001010b440c42415441c0c40352400b0181211355030441d00c0100c00c04154102007045140c2c0110342d13902d08640742d83c42c442604034041400314041c0000e40e0301000584440d940111b2169003410008009071200e110310078030 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 166282050 1250 166280800 166280819
    0x3061104050d030e090a09050c011d0616050c04140115030228031d0705120307050106170f010b060f090a0509010605070b0903122202030601061d04090309090902030304 74
    0xb642d003540444d0300b00402c44820b144c00400e81da885250b01c8010042415283c884903500c000e010740381414007045000c00846800d80c5440c2c2c0248103001004070317607a07685903070b031400000f401c0600c110750038450120191602c3c6024010042c41d89646001244030341c1ca05492500a008010298010700d03508001203048c84607007209030105915001904c445140d420700004044070014920b16070b411b001c0d105443d0b0000404140d40c2c0488004031581714880c0200c000ca01d06510548a004000d980780c8000064407441c9042d1301d514140d501c9054421915040c0c42d11420786141c1d4070001d91004042014010b00240000075140701170f0064018002a519140840c45007102070b0456004104085400002c0044038000981c3c4003515801850410300074800b43e400c020300180503010400034003c403918100801074061148541c0080c121051569104805880e8461003401c00c801a524001040f1035800d1500611000039415510200c004fc9001018070042007440c00c2241c1c103020410000415110 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 166283300 1250 166282050 166282069
    0x91503150f07090b03060d060b04060303030c1107062f0f030414060403020901050d080c030403320604141e030a030b0a060c0206070213050a050403090b04050a0306110405 75
    0x100d03004001078180301c024003080c014001c162904018260006204885801c41640d4008400351900400a01c0318646100a052000402a0002e2401d0400424542e2540021029840c651102003140f90024452a11007c1500980c008141403003400c8240c0f0b48901020308140201c0000c103884c4072003886405040034140750514030950700c0410140070804c0c4030060040c00000403610985054950b60110b240060144255131003190918070740c02c1440912011604d50264500c1941d40d02e6803607241c418120201c144a1a21000ba0a5419582c00c1c082411108070500c100340100142c1d540c65650400300e540030500310150f0f019101120080300c012a80c1809502804006140c62340d80c80c640050896148614840c0b05d00981d031170402c01e480c4c100242c1082d090f01075544e0b513928481da0000c9030001806400d1600780c2440d000400000c602580d02c40ba000c1c03031281d52800401c590321b0100c040980542e000311603204088010400000b109940500c4d200c0815441c07040c20242c1d81c02c0090048030 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 166284550 1250 166283300 166283323
    0x6010c06050406270b1303090302061201030314040e06090928210c1707081c0b060a0212090d0b01080a1208010b040e060d080301080a1703040f02091503 67
    0x90700c13008103242080103e143d1a00410b000402c0004507101612900b403101c8000e0b159190050b80c2100c0402454850032040740a99006450641d9603421800c1784003019000344416000264212a0710340c0e212058001c403012030704050a441480d03107544013001003e62000d000b08103280302d031103001c4120304101e070790705a903140b000c07030316a03000c808203042c0b8641c13044030201500d4504400381400040d071074000d064028529040ba0309505c40341302c2d441d2212102d00c110700018055480c04600306003071a144040514100050700700030300010861805200d807500410f031442000d80c2181d00d0228011071400040c0c891004028905010310078107440d9020083d4003a0045034840e00510014400e2024079a0558880030491030b24000c15850311001d20400d01441c001c80b26042d0380034022514564a48041b499580c1d0402400c965a5a407900c51035a1f0742010700d42110f4000464042007007410700700c001c0c1d0f4403482d08080d1003180c040f07081d82041080b4800400100b6440001d1030070302c1c001d07202002a8041c00 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 166285800 1250 166284550 166284563
    0x111010e1e030a020a0f0303020d150314070e0106030e03040f08032a030f0703051b010e010c0201020304171c0c0903020108130302120f0c0f01020403030f1b02010806010c060504 78
    0xa6501c0c098210070040d01102200d0242d108004207028a503000807440d43d81a003008a41035400e8071883e00b00c0180c810003100440c0c0505100150345800c90800001c0c3c00c5070702c0790b4811520780035004000c40d01d890445c45400d001001c11801041458042d0300560b14080002c803d49180c99182c0700710a443c498640c1090b20b0907840071038105200010001c0030300c410a40c2800d003155031550004000e44d81d1045c054051116040418010308060084081d90495140500100207020201c0c000038003d043d03451030000c2e00d60030203c440d0700341c500600c2101d000b40d42000c081d02c1c007520011070011141d40410068608035101055005420b03ea41c80781d6400400d8560b600c100e0145140001403c03000003070046414a003041c1c0c130000000b5000509140301d00800350a00742c5440b004c3c80b0708000d42c01404003542d980e0060040c000d8002074190700820659200c4e4403005030301501e44030221140c0c840b0464000701c28581e80c103810003660080d620254082014900444020429522581a6041518200c03080b = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 166287050 1250 166285800 166285813
    0xb16021f050709030b1f1e03020f0a2607091116050f0706081b030c070b04020118090f14040c0b0c0c06182103070f02030a0209092104030b07030b0111010e 68
    0x86d0705108405900820b03031221041214102c60b0103650000c080d600c80248200e186103200c40030750321886440c038003c0851004100b011412400c01d0150002071450703103003080c003d000c0c021425150320700c2100052042c602085040c4100da00c48028050321021054806216084407000c0d009420042040500740950311210181018801c0088040811040143d1403809204024820f40524143c0d5040c580205c00341032107841d1400165101c0136044042c45081111000c081034811464210400310b0980c02c00400203042c090100d40ca20103020303500200701154901040000d4100b03240074048003400d00080c0da00a900034800600d89520081d0050024100c03585000c5052628a100701d040f098000440d9a6241413034220507264032070603c00510000c0880910025501e040003125034280d805422a41c00f0305112100d955120420071034104402518003a90701c04000072000ea03004c0781d5001d125031445882d0241c0682c050580130300e5142c10042c070b120100b485e0840c05d002c0c01c210740c0002006000c1 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 166288300 1250 166287050 166287091
    0xd06140c0a03140f060103021e03130b060901031208040602091003060501030c02210a020307050d020105040209090309030a03081302040f1a0a0b0406110f07030b16021f050709030b 79
    0x545101400f0b0010724001c0508210201c03a1052840780d01c40d10918005946501c6401501c0b40500544144104002c0100410548184070440c44002900610101c0c4a036540c03042045000e407402d0100800d07611001c01c940c03000d6401407c45540061082001604050801c0f000c1404446030303070340c4400005d40350b15080100e56054440c8a01e0910705101030710300084c20342621000315030b0490f400c00084000148000ca818802d000307a40c0e1060b40501901e6010307218220080c0030f0b00b02a80c007640b260380480302158480d0400000c507980e202000d00034000740c40d029202501c0100c401406150181c203c1c100490041c3c0c0c5034821030711000700c00ca01c000303132011b92034150f00c3c108428200706a018140405061004807004000c0c0c41c11a83c0f05c1c07402d07054880354034a03180e003400c0f041a000f200620074140044104030222000501c01d655011080301002c0c94040c040765542d0300913400000110640000d00c03050052500500c1e44a1100d08000804603aa40d1b075602e8a84c2b02200c0100c000ea5225038184d1 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 166289550 1250 166288300 166288307
    0x12032f090a03050f070329010b0a0302040305031c051003050d03051e041208100f050d08070b0412020606100c0f0c050d05070509011401020303070305130605011401030b0102010204060e0d06140c0a 86
    0x100800954a20340712003c007000c1c1c068008036818010340d81c01c01c00100d2b40508891190b01101e000e5588a000c1d240c5942020528051150040c00f440c00c40d28140400100101d0814000c601107940140040104004a40b000e4009010103410b0009104444209005040414110038000c03441004452090b04140400070120768020701940302a41036064200400e100c03244848055600c00c03100d000d4a58254502030f5400e02c20346500620b41541d110030082804024402e460001c622a02a0b078110344d41c110802c0b080503040407010011641050302c0102180418801240e0544107507000080e03036490700001155011504002c5917298010042030002e4140b0000090040c0010741030840302c9807091002030b4aa0100400500800da030701c60000b41c20a18a103004404a81c02c2902040956144c8044154440100040070b0209042404180c4594070501c220303030445145944150040092100300500b0800301c00059a00b5a1508040781d200d441c54051b150241182c0042103503180403264015 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 166290800 1250 166289550 166289573
    0x504051b010806310501060513060c23210d060803030907061d0d03050316110616050702060c010b0a120b0106050d0f05010312032f090a03050f0703 65
    0x1e0411000c00144666500c07000b074400392890b2444a001c400c0410b402000246000d402c2070901035030f08040000a03c01e400200800d603030405c0c0d010b00b401058466505480d40139002e4002458012009603840007508040682400b42c0006815a0f44040c1207591503000c9a051001404245000207003420380200f461142e0402040800c0180d8214174040c01c003e5102c000303a11a0710b082c8081d1043ca4460642c0a041541c140348005060340800c00c12802d00405d41c0d04101c03454803140900894541101e40a10040c940c0080341c8001498960b541c0200901e022080348500410310205001d0800143d9a80001e03050406100d0000600f031159503080003a030300340e1035000001203d2521182d01c0824036028129054130b20300c2c101155150740030034101c070061400b401103c84241c0ba2034004810451130684032007031074400303507810b01c00f05100301400408042c00c0152441f0b40d281c030503182c0b90710b40c0388040036107081c160041856603eaa682d803140703410620804a00e013040d4204a500b4005c200c0b060f0b404 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 166292050 1250 166290800 166290853
    0x30c01061e0e04110603042102060106080609091c030209040203010305010506032b030c090302030d09060324030609021908030c010513020321042105010b0402090102060f060a09050405 81
    0x20086142415184c1880381e400903003286000b1000000005c0501c186c0910001048a884466880e01900194005c2d1514000e00481001540364408039920340380c030b1035106d070180d185103000c0d18103000f502040f0300025100590000170309d030b0244003c000981e10703880914021400f03080081810301c0d0034810541403400042c00380c036890386500d0307501a000780c035004241a02c8045003800070740700e0350780101502d00c42c11b9075200a50501c6102141100254448525011207040e600c060104401280049910800107562403146c0f07800b0040401c04103120380c010b400050f0024165440c0440d90101c0304008803080d8200180d20340c00001e103100034842c01d10034203030f02152000416801c00300b40e9001035250f00c0000c01c9001030944910403400e0031040700003120000d280802c484040b84030030310300e40030b41100901d0042c0d44039481d100c400c41c10b070b00b040e00880c1d41c0c0c5201607000d0400c507610140d05050540002c0d05458215500c0d01011540d0801d500c980c03406240a480280400c101d407914004402118000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 166293300 1250 166292050 166292069
    0x414010201090317040201090509130c0e060112020d0608030c0601060e040203060a0509091e1f02040b04330c02040e1c03020a0c05151b0f030103020d0203030c01061e 73
    0x1007000b2aa1191300c03038290101001403200740e51514001207032024040d4100a41c0003906106010080e42100c994071804e601c0b81c1900440c1940d14034034607241010454005001c00c401ca0410b044040159008200707101c0720b58000504c0640320000b0310300d990056402100785d0340c40f000041c0700f656040713041056130382e004072415031440c81c00d407000c0b50305400a44039141c0100142c2000c102c50400034807c00080f4002c941a8800360510803400f2540c034500f8180d6420308190103a0900700c5c0b418240202c070700350f50b80c0c010458030b05480c041c000440203a5881015034039101d1a605851641c840d90402e922142d41962200006103880c010031040796003001292009601c82e01002d82214107804100000480d10f060058440c15041c1040d01c400c808004024028055103001242c0013200c101d000d405000101e204406070f00b40034078005100d00c22401c0302403084400340010001450305080112000c0e1002d4140c80c2040d0311000700f142511100d80005a2600d00c801402f8001035401f00359000034500e0b00c0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 166294550 1250 166293300 166293311
    0xb160204180b0106081303051206010c060f050115030b030a02010e0a09091a130201020a0b15040e1005130c03240218010201110901050405040908040803030403020c01090f1809050f01060b0414010201 87
    0x90f1f018001d4400c82c60300e0842004103800203002603004081545036907412003010701c50440e201c0c401d02c0c02801c09009554283c0442d41d800105030b4441d05c1040c0200c031019000300400c03001600156141c045001a41e54080c40381c0788046004002c0c0d01560b43c24074401ca40d60001300d55400c1130494010782c02090050000c3c0190701c08030142c1c0e80040d0501060b03800044180031038540c800034284991900c202c4540007410890040040e0340c1c0003c3c240030104800314100501d4803115000e03001002e400303c1c09031030071311102c0081c40420303444c1c080c0c11021412010140b2800044203a01020381c2c1000c00c034a20a4000c10351100c03819602806510700b000b1000c10801d15049403c00040c00d0b500560040901407680e1340d540c5001c020541040310042d040705002c03030b074607403a240c81c00030b544bd4a460242400200028000144411246480010748400ca204801c605150707001c00c400800d58100c043e10944601080034041281c284218405081c0c0c109001e40d40380d042400d10f14288100b00c0803a811603140c02c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 166295800 1250 166294550 166294553
    0x105010905060111210f0708131a04150519031b0206011d15030f071403070b030a02090310110702271611060c03010810060b160204180b01060813 64
    0x850b140d40138484201041000750b60340718a0340351078002d458141803600c100254890610401da07000d0400708404000303c189d200d858031484101c034400c4400400a4800034442400112a20a11103000404a10b40207003481c421200314040c0040b4070040034003003691102d003441034000c00c0d200c1d240410024001000e031549400e03200841d481c200380d01d400d040040725004c20840314002181216050009080b540c5040c4158031407034442da201d02c240081180d15200350320041c1004111b417400c13078028038982400c50f80c5071074400300a94420520365616001e15042c142c00d485592203042075045000c2161a00d89445105011060b03074080c60300c10100040d03801030b03c2490480c13800350354010020020201d501d0320490080e03036a99128044943c0501444042203131220410300514101d407414801c0f0303078003401500d6510342194414050b8940402e01048810441600c40c48130101c441e1003e040046d1307101003c1201700c1d1040c80388901310f44111101c0c0c010400b04d0b50062000b1307004000310000340c4000c200c0303 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 166297050 1250 166295800 166295803
    0x6061e150c0b2d220305071a0f070c05060604050613150501140304020d021212030a092a0603051e04050105060307050102070f26010c030b03010c090614070501060510020105010905060111 82
    0x500d00800d9110020762404044c1b00d081501c9031550300c8114030faa070345003040002d884090200c440346074800c00300c00022030305031140c50542c510302d03080009004c1d940c5420043c04007034080100910b80250b40101115242000d03442040307a43c8080000100c2d22506000004181c00000f1034000c14000c0b00f4018040075961b542c2603c031500394103c0b4910101251100d03210704010078512a1031100c00c01004020200c10580c004201c801c0c4210b480e81021182d0b0100c1c42d40001c5040185590346060500602c0201d00980c0039503049a40c82c1190b05680ca50114800700c076102c211030489250b51550140625801d0403c002405040d0074005081d80c0760800460f0340020f0400c1c0301d860f0014000302400e002a080c01c103c140601d94508000f4001b081003c0c101070302910680013103900a61a203903000c0c1d0386510840154041e03402541c0c500c03410b1000b14083e012207800494050f600c035540d4040004240d0341c0c80c031018402d204107400101d01585004045811120b0003051581404061407000030341000 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 166298300 1250 166297050 166297081
    0xb060c15041713050f01050403051c110d0203070c080f0316080409060b0309060f10050103090215031e0f04020d0308040f05061306061e150c0b2d 64
    0x62548080c0c440e950780d401d00014224540b400300e00140000102c072107103101402c024000303441e01640c80703c11244269004584600c11480090729a0304800e00b00004058524803108007105d0b81e00d048c20100c3d00000402c2e0401001c8190b40b0090703480000c4c07000800c8001c14201000b022940054103100c489080d0140d1240718a00614810101c1c0c3c181010800681005a4002d020030110810055444481d07a80c61036109480d0180c2c644200800268610074007503c55200c0c039225001e04610514100054002c5e00d08858100d07840404112206001c00100014505c180c2500c200c005e4040c4054807802181c0c00c000c0c041444800b01034080102503200c2a011251250b8546004e4409aa890800440710303021000000c019000c0c1d101417241c07010b09801c0c0202d80a009110402000b0303541c0c11960700c3e001c05482e0300f0078032245501d03080044000c01212a8981c1d03001d400d0540803038415583d2002050011a8491840e82c0c00045414440e0201c8026824444103254441c006081c10340e28500142ca = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 166299550 1250 166298300 166298323
    0x11104050d0b070504080a0b01090f0905120a0212030a090c060801030f0b18010501090e0c01080f1617040c060e19090209040612080c06070f050403080306061603030605040b060c 78
    0x60000d400300f0350252040040383d000341303c2a000c1d500180031500c1c00e01c140e04420300c50342500609010003600b400465121300840d15910030000d1044030031102400410740c00803440ca409601825034503950742402c00c0c00a500c101200000003613401c2c01423508000700c81007504004100149500148001081d00861070203072070708000200c030166110501032140074441c01d0740d80e15950901c80001600700c519042102c440041c081a00c80702005e180045404590031900d56800095130000b09141109110500500301c000f460003250007038000654140e13540b410b07107040302c420f207014400300007440e8861266291000110750301d0720743c078510b04040800081d04c0d010b91001598001048000743c3d41701c4d407000004029500641000c40c480d0306050545411524544210f030041c01d000560380c0384900c19030504030700b4540340e00b8227090031030315010b5071a08020701003900030504001031804901019803540040f88251f9010507114284014402510000e224070340c011071041c0f2005844410200720142c194 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 166300800 1250 166299550 166299563
    0x1d0c03040c050301020a0e040b040b0109210210080a140c0304120302090d0c050406050f0603041e08040b03090d020601120b1506031305010c14190e0918011104050d 72
    0xa0300e80e8140078049501d182e021a5040d8400a003c40b8403a400464540310840100d5040010101803800d03c41503c206c030b5626800a030451f0018894042d40c101c2c404403034107968040d18025011980858160290811407070b0100e81d030340b400c010407400c503401140307007202081c880c2111504095203604682c1c00003400080402890000301c400d8507120360b050b9907802d400109001c0030201107040109102c0c4050103618061400c181d00400e541c10010221243e0040180c80a032039030351913444039642c01c031100c04906056021280c036200403811950180018260581c802581d03400c03e10f03403182c41c03c01c440911605540110004105612007100d982d4a000d4010700074070410b5559035143c082c58915444041c0d4040f5011042c4585c44850585400d001885100208003411403143c1c2940ca80c1c034940c02040c508042048120035140c00304001c014414a01e0400807a45001040054a2070720122040c0d58421017003a0102d4078582c09005000d42032101981c214a003a0402c00820601d180049014280 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 166302050 1250 166300800 166300807
    0x70b07050f2122171507080601050f16081804090c270606020d0807020a02060301090b0f0d20060c060106081312080a050c0306100f170915011d0c 64
    0x1264a400440c001008640107580340d0903031244c0301d02c07840700600801000315202e90114540000400c001c818002c0406403070b082015500c03c001110607038070071260700945000a21034903500c60088164007920911900d00c45484d28541080030350400c5011901078440c501340348220020500a1000300161142c086032141c003c4000c042011900680c00da01a001c0b84c5001e2001800b59404201e68003483c58590b1400c455445d8168201d0b0307200f05280010b0741c011410030040104819903032000c1011080540385c0003441e1158030000b40309445940c000d1301d00300c80c803a45603c00c0e481036920070208220304075140c6080c00300340c17005c0c0c940c1c44005019200a10404801260704c03d0b9441c16074449856100c60321412950304000c006140da0304c00c1c0c581c0821542098081111210303000d059900c218800b412040042d01f80690403101c0c0013400300707050144040504c55881011a4000d054030401c09140100300e149504105000907074070503806121040c0402c103034112108404107e86d500301c01000079250700c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 166303300 1250 166302050 166302067
    0x60904240603050f0a05010e030a051606090f060506040c0f021914061e0a05060105120a06120503040302120c092a07060506030709230a02040305070b07050f21 70
    0x40c003503904068200d114404c290f1800d604000f5418400c0c03842200280460384020082c1c5a40e03000b07175940b1002149080c8985c3e052075003000817101c1d42ca8040d042c00b00390100942c6400c0340078003603444c0507590f09071220100440c03410a80101d000441051414240140041d00000d4a0b40742200d0030b5100090140c0700d200174002c400301c140c410b113403d03501510114142200c0c500c1f602d41055400004014130000012000801481403600c1240c068580c079141001e0408a1889030b50000c044038601079444101044c0c080c00d514006e4400c9200d07000171555035046004010031281d030302c140680d031540a4014000b264850900b001c0e00f02c200040c2c440f11284811808416240c0204008041c640e004110041440240d41001c0d004203000d0b01600e40c4541c499400006981d2262201202c6404404900c07000c0302d040840c0b1030303001c0712442005040603103c2c2c1d510b5041003029400700c0c2942d00301240d81000c0c85400e200302d00743c46030803000420400390744509040100005a952007100000440c00c141d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 166304550 1250 166303300 166303373
    0x106020d12200a0f030504020a030b0a150609180207020616080403320a030f050d0f0207080301031a01080c1203120117070b1804230708040308060904 66
    0xc50004102035440c0c1d8104024a42d00d05075040307075200c00e00081000307000351203850080c03080c40c4c0144c0d0080c1c031000e45942151101401d0381006040740710002d9440e1040c103081c410000984020302869907a600425240607000c00380e4070302d1058021030301c5104002000c0142d4820040314103464000c800c0421600c0a81030403611801039501c060094084145898256a9902682d0203a14407085810300c0c8020035032240c6982e036018841c01004240c46246144e2aa40208003503e02e488070020080345d103140c8202884140d800c001801c0300e40e02030110051081048001c985000c40000d501841c41e02d6140c0001103175070b0400f02c6081070140c25918103003607840c60b041c81124118400c0d9402c82d461540d50fa4040101d005007042600418042c030030f4045020749581d811a80c001241d03011920f500c3e069002000010720491070501e800c441003014140350807030300e290514400d02094403848500d142909010704664801008175100380702d00e004000000b00d42c001e01039010507040b280322000007140340d0b00b01d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 166305800 1250 166304550 166304561
    0x40f03050409060303080402090a18030503060d0203070e1608040c03030507020f0607230a03080f0601090812120105012a06060503070b030411010c03020d110304090608030901090e0106020d12 84
    0x108140c100f01002c02416080070701c1c1d0380114401e445020240c0d69184601c01111100070401802d00a40c08000f00401e10440c003030b5030030031782c01042e81c030300420b096000034500040c03540301c0e0300e03802080300810441004901245007206d505040840c01407500d9038802d203a6008034080141401030100d00c1001f91344621401c2400c04d98043d00c510364a5a29040600c1c04410404010b42040c1240c2072078481e840c80480e9981100d0344c15194210562615208400c00120090120741088256400064007440401101d08c1e24840d5100d0103030381c2c02e10007648020302001600700c80d0501010642d6020441034400049040360304114141e01da840312807411002621b9030307900599061042c80c40100d03115013114011401144a01d030a0a00c65600b04d0041d40c5000d030808020700560800c107640c1c1c0b5a180501030705005109000c09907883c2648488141d0200c0b0810741101030941d00100d822180c03542c021b0040c1d0b0240016448903800c941c5405002940c1da86078001140400c8a843c006545200e490b4200 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 166307050 1250 166305800 166305809
    0x60907032907020a020f0406180b040f0507091a03060a030803101509060306050405090613060b0a0608061306080c010509030309150306191503020a020f010608030301050307080312040f030504 84
    0xa19499040601c002590780f0000baa045c5d219a606103034081755442c0c00e11841c41100c6d155182102445c107031185c204000c01200da01035400c50344032189031189003054820304c1e2140c451034503000d080a090030b04000101c56603e4003543d03040c01c108107000f000e50b1100221001c80380e01c99000b1b0303a80d654012844001017580da010b014080c01010011040b035802841341d90965100703030740c10013000d565030081106030b41c010703629054242c0101c004500800c40601d02943c1c0340d80910700c0450600618000b00301c00d050b90741d0062000a00c1003040c03011074500b0361072a0186030b034000c030144241410404840d480f00d20404405042c480c000401c11040d440c10310a540702018010004402d65108440c1050254012500c0d0f80c4101c0029405c0f0781e00710400800c100584403100c41c400c40c42e51002c80140d0081d40b10a10010170b51158122424040c4030034000c0c6400380000f040030b1070704d95140505061030045150041d080035041440701c1e040611100030300c50303400b41d04103400c4540b0700c0590505403000d203d940c11 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 166308300 1250 166307050 166307123
    0x506030a06180212032203110f0d14061005010807021005060a0b030406020c07050d17070305040b03070e030115050d021309051006060f03060819020604080f01150806090703 76
    0x20140310003072010001d880300c203201c0244848045000c90480b009100d1b01d000c000d0100d0240d019404980c00c0160b10b0510518000e8081800c01c0160b40b42c080c520803800103191015841902004000d407050000213000340b40a00f0184034904107008003a4848002c0304c001502d040c0e49200041507a900d001c0454000d011140c10300741e80c0d0615003803200c0a540140985c210500c1003600008070342c100003521500903070300104c10703083d2803030000604816a0300c200025801c2010138080443c80f0580d52009501a001a807100b2085102103810b05007555078541c183e00500e6044481005180c0300c01100524982c4d04580444070410f943e844807000704015240a00180310351070001c0041885e40d400441038072169203c00d99900c0ca20042101030b180c05015000b0303d60040304100c0d00848401101e0220284011710039810592110419490314001300e08841e030076034446080f00894107802d203202002d80101c80140c441c0e4038088407103541d102207a10000b000c01800b0030403000c0841040340d131440b507a0301d41e0b02c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 166309550 1250 166308300 166308319
    0x806042c01090b0108060402060f03060103060b041502010c031e05180706020a0b0c130e060301060302060a030c110c090711030403050703080403230c120c150712030506030a061802 79
    0x340c01034000c15207484202c5000b1040ca00100d81424001502d510403075000303001c0d0b454510504c10b81807071381d000030b003105040c03540300c540c04902060700e80d020708090941c0d180c480c4454444520000e080d02c6064900a003414500040011840340040a14580c000c00740c401240d00d0b01c0d10001c100700e4483c801700903555405800000304002d90b01049143c030150050035003040a48030559181c80500c50440c0070500706213003250400100c110251841d070301400003030000850715500c0c1c0100f240395002c0181100000c0d9503640c680c0d055078110b0f44030144681904005c0460300610ba010503a0030102030701060522102a102d000c01b0101082240c010350340c880c0903648a142c1da85003210194102c2d00003200c2d45902145103a40160340400d400515292001c020702194040c42c044c0b01207038010a0340740381207014148140003a52650603ca100407080c860700395075a00c01600340051401300c0042c0501c100350600c0c080c862150380010340313583d031550002c03000a00b100002800b0101c004100c00b000390000b5918 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 166310800 1250 166309550 166309631
    0x30405061c111207140a0c02120f07090e0109080403021903080c030a11030307020d1101230612030304151a3729040f03050d02011b080604 61
    0x4000c0e00c0307141c0010b02030345031079150701c641545c40b0700580c200c0101c61003050114103109817007514080880e130300190001410700a40c4d0003c070f0420000d1100c54009902c0b0786420811029548280038103601020001c10500bc140e5807200040d00c02ca00c4007a00c1240000005060140340c144c1450043d6400030307525584104240145459822680d403070004114450340350000d010001c41180d2094510360b014081803034040c40281c41000407101000c0e41596241c010710994014520507400420000100351820715141e41045143e41e004186104982c2007841400b00084520a40c05a04030a02c1804503007814040f584000c014500f00705190321100c8010580c80e0700d03c0d55541e07800e54000d4840301c07881903001c0680100c0c542c62140f00e0808004811280c55084002d0000704c032a000f8404981c00c0d103800c0c2e5842903c10014a6604141d98a030023200501c0c2c0c1c0a502441800d403907000000115480d041c01040140c51220000c15841c0129110910030321003a5031240f000605e80c0c1c500e0501441c0c074414 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 166312050 1250 166310800 166310831
    0xf0f0601030b0703060302130906020d020d0e06010b07051207060b0603040f0c09020c0307020616060528060509011e09050c04170606060906070f020d151a0102030405061c 75
    0x70320094465040c604081942d9070711901414080c0c07074021703155500c2c004074070714408020242d050090310800d500340000d10461030300e030000b440d000415110100e41c603410301c00620306000d41a40540e0080600300944800540c01141103000c107281407040d580c80789090305000c009000c4001000b0f922502c004208010014506102d0729442c0c040c000d501c0007262100e449004910a401c40c10100d0350050182000500c1c0000c000e01d100301100d8042002c00480e5925030b410359405403052041c2c01d4031080c1d011422106000c8907480b03845a18420b002003481d180204a601106000b5a4201e04203503030980c480b003000b425600001d08245a04002e54541070b0291000f6401ca401088680c42a200c02031624403c00100340b40910700041c540380c54205400200802d643c0300f0b02049402c180500c0301240984e03100f007030044405009000c01f4501c580c94940385030440d000086805000760014002545590b40001500d0555900f62542581c1c0d28418400e035203a0100403298100d00c1e810410f0004440c0c0c507 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 166313300 1250 166312050 166312063
    0xc0405010b04170a030806040908091503061305040209040b041b0f060905010801030b130f0b04030c1202010c020a15140108010f060f03081c090f0606060e0109030b0c0c0f0f 76
    0x8400d5111090b03042801030301500c134248000058005421071000c242280350592000741e0151042035903a1500366010f01107070180f4000080040c41900100c1000f490b801e04500c80c1c2c0307000342e007240c0410091a1540c0050f065a002601c05005c03056541c00140402018072204030b0741c0481030f2280c0000a98580030405001120701a081c00034104520000343c0e54011002d21b4162507118100c03c0e07840d50f9408103407240c03020900341a10010a500c0c48007010420403448180990700070b9940590700101c80c1000c100b130104a8400d04116071518105181c0241d0205002e20b490b5801580342d1804c0305205101009808582d2000000d6104d03600002240384055000010b036098500c02401110340c2c46d01510100201c9200280040f40c0800109020360201d008541c217040c00c50700700080031078203501e41400c0402d072450b040310340790b0f40c1d410148030654001e10b1200542e0300901e03224032482d0455030b4800c11050b010300380c0f40d04100085404040c1c450305002d0b411550725800122620f11211102031075031041d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 166314550 1250 166313300 166313309
    0x10203160f0302070b0a0b060403140d08060d1a041115030402100e1302071a0403110609010c0c03031508060708070806010309021807030f0f020405040e0303090a140c0405010b04 78
    0x244070000202406000c0e000b5595400d8004800d4400f55580d0081c0b04c0c0501021260b0982c040401c01020000032903484400041c40620002000d403802c4a4002505003200076100300d1255a5090a40c03001902120f140ca15070a80f221a80140ea101ea18081c074188140e501443e51082d00012902e290200070000b5500c22802242d20b010345101c00c44040d174403a03006585040c1c01052401002034525611b070010b0403003d10a460408504258140381660074400383c5040b0009261003a46580120080001680000d40300c1d000b00700f00e007000b450103080d00040c0c040040c01e250300c0e0310b40d203808141e07440008401071115500b540c5851a002c0300040400c07400311210004254000d0214131154030900c100900294042c00d5100303400c07800741c48045000302c02007040f0105a21440b01841a82d80c0b4024020302e90000c08025846a080804100503250071400c03603080c40e40240100501440002034503882103800078002024a8844003440d420001d100c0c0743d094000d4180700c0005066074412004004a8 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 166315800 1250 166314550 166314557
    0x1202011209030905010807122a031a1e060a08180d0e0927031b19061d0f030301050a0501020d0f03020a0306170703020102070f030b0403080703020c01020316 69
    0x1880950a100110780d400e900140000e002e02d08144085c0d4081d5120540000f0b090030b1902c201c4024000c00c80584446207100ca081400031047c450034070800200751072028146060910100c0ca11084850548480d1800c0b20300c590032000500e00d00d807000c500d4410600e03202500550303603004006809007800e442a92408110110210090030000010402c001c0c00710b2070303559003950000e802c0c08202101c000609425407403800034646c64448001d114224030440d881c0c00203103494400c07180e600f00302c5052800710b18411750445c40c400001ea0200c1c0d034844000c0740e801440000c0751507050f14030040d03032070720032403040c403d07110310035018140b0000000554100c507811a000500c054945c0012a03d0700380b502c1c8031202054a060022a0240c0690003400040d1040c0c0380020328a595032202c114011070b424405600d607000b1701018015541e050041d1001342ca4400c1000c10100e145940740030032100b0051024040005500105400394481d404440c80103841b45d00964980c1030a00011502c401e0608644012 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 166317050 1250 166315800 166315817
    0xc120a2606090c040605040e040201200a0525031e08030109090b010504060b0909060418030c0605010605190305071704060c032016080f03100e070e0d060c03060e01120201 75
    0xc3d209080340c1c10b0301c0141e5549030510349845c83c03007881c480300504101e05100c03001e0107416411008044802c102c040c2c0d0002801da02031141400303800c00c3c80d0b020545800080c0c21207200c010403040c0010104a07035011407200250260350700201d0b030b54911a1001050300d040000005003030340c920340040448500036001400d203660380307108000403103000d071250119103c800d0004d07440300c0c904105442d170f00c64800351011618000052184a82c85e10b100c00032800f0410307151100b8140629071080c540544035505101e4a80086552640100320b1000030600030592103400203036030740e441119070310318411010410348482e00b000d291000141014400210020349007103103501d4041740c08180d4005071a000600585040e10441d400d41289102c52030a1f00c841c1d0b4204000c4001140482c01184128040c20006411504140d0904006103014103124100040c810100c06a90b907806114412541c0c009400030740401c0088040d07015096503400042c101c41e01000001700b40c840d010035080b006200b40d884800c03 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 166318300 1250 166317050 166317061
    0x2114030309150f0402010809010b03032a010603030206010b22060f0e040b010e0f010504051203030105090c070c06031a0d030908010c0503100b03090a08040f14060c120a260609 77
    0x1000c002140c0a00304403000c0c2c3d000c14050b50160040a4100c0d08400001c0342c144501004070303140d03030b0003100200207001c2c91990341e84801d000500118841c80c810b030000d1003001c2c51618000d60b2801c041c0200d1280c20380c00100800303201c40c480d03410511420704c526000480b654409015083d04014180038011170103541c4c259200380b400303100b0f4100007107050b19094036152a202c10311401001c0a90503606000c003c01c00412941d40750410048120480e400469496040c401170040008000e010400850014404100040d05c500d00e00720a44040707107130002e00c514441070312007420403001c01482d81128100a4007000d05600c002d40c3c1e4290340e00b000c001e200280348410121110b1208503241c21305250b503001d081c0026400f90303006503004030f00b0714200c42d840d01990301c2c1d54059900c81c0d40b100a03242d002a03010802c902803403e5241c1c0501084640ea4103250001c01c00585400f003007401142900c0c0001403204010f40034100c03d180e0a80404e024607484841da000408005000780c07103462040800b00001030 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 166319550 1250 166318300 166318333
    0xb091002010b01020a06020912072d140603100e040606031b080709020702061308030a0207090c050a082a030907050d030215060d0f03022103060a2114030309 69
    0x202c03082d0103030f008104414170780d1140d9000750882c282081d88659151402d02c5005420850000608204526852005106001d0304840894003d0310030219403100b208000003541c04030107607500b26050381c017540d0701d40d26000303070020b00205a04080d2240034104140420300c16658800c2003500d1140d19080301850940c00d00d80c0c5070003080d12079050f040c0c0c40740303c2c144144642e80e0064081d69202502c0c80f414402800d81c420b0321601c035130300320f50215807010541d03401650b81002144010302110504201c100c1c8041c85c0141140b00e8062000305204604012610782c1e041490703000c81c020700c52628410514249030341c400c03659005580c541e038148110b41001c150740c605090101030f626419001010040395181c40e240c46245c0007040d49920542c050718030030204103402000d40400c0d21981c0076000040381c1b01e111040306000f0000c00c01cac000c0010b00400c00b07035441d03510f4142d0564010312110125000b100030640b80f0b01000c014018001c41404071202e03401c440020155024481c0c042c207030b820906040c4001c1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 166320800 1250 166319550 166319561
    0x2090117250501031e09080712080c12090f010c0306030b060a0e071d03030a030c08102102030307060c0806100f021507020c09190b06040e06061606060b09100201 71
    0x844100c50900080001d907004e903224684001d0031046800c5d01c0040713002c03010100d4000f244103860303600d0000307801d400700200b580c0c03c1c00312490390341404a154180041510305034000c201306a04c07012207000c04229505000c110742998a4210f40080c07064200d000c1c0700501074102803100b1142c005140005c680346203410340700e44d42640e00c0040c20303140c01e40d0780b4103081707801440c101c00d500f0070050104a000034a8078244000e04000703620780c41c0802c404414280062101100030070f030030074004089030240b2404401c103c001088410100c03958601882c1c1d400080d085105048004081c01d15003203e80c4c1d01c040d0405900c5206010031507940e8040310030300c601a10b9210280901d02c0040c0c1008a4580c1c0500741240c0d4160084064030454085030740d44000710b880713803e050b241c1500003030000084588100f6a4080c1d025140c0c41903840604092500c600700d10001006008a40724600110307401503c1142c4032241080355801c61320612920f0383d03030850100c80354443c40e8880d000d0b2041407141040c00e801400b81 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 166322050 1250 166320800 166320853
    0x102030405090a02221d01050f10030e0c061201030c1502060a0c09031506080610030317060409050a0c050418020306060108040221030919151b02090117 67
    0x401403559103440c4050004c1d80441c521900c98401d20070304807030140e80d003035001000d041c1a41200708181b0540c5801810100705078403991007440d98406c28010b544400c40307000d181002e41c0c200462800540e1602c60f003840b040f10003071a001200401d00300143c1e480e05d0303617903412a4014844504503a0300d034018809051800d42588015034810030205e8580e01c11f03584405040440c1c0c2c80c1c442c1815844c1d90f50342c0c81c002c0300743d469407040f151280400d02c9a07510a0040980140d00101c80b18411469903402800e103443c1040943c0d04540303064005440741e11550880ba80c0303243c0c02400d4519044003407514010203241c5000d45070040b468200d00e0b504103100855098501d070340040c010300203681c0702401100c500100402c200d81001e6402c881ea04a08049001c1005008500340a9604c502d0030400380040e41c00500c40400704440c031024100600c881010039600700605510f401c0c0034413002c1301d40c0d107045030920560080d0000401000059151814221401c136407240d1402c5c0c4e00c2d140b07555440e042d03440609082 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 166323300 1250 166322050 166322059
    0x2102040b06090d0f020a050405090a03030e0d0f050903030f070302031908011202060a210b091308040b031f060f1205060609130f2f0a02101109040603080c0c0102030405 74
    0x9804180341c01e800713030320340c610051142540c2601d841c040303410382da01a41c0447c12580101c42c00010181c06020b0b4010303440c020700003441600095000141103015007a4071030240700001810420f81c0c1c41c02e004480071540035130280355030b42c0c00926000b90380340d01031080f03d40c0846411490702d0850303114413a50b88c12075000e2100001c0c4100d0720303000c000c034a901580802c800d000e070194072100d156807800c40324012101c200100040540e2801d05110580c60001c1842ca10207000c400031000081510f0107482c243c800132540c05880360b40c2d00e4100542e400c40b20221040e1500440d40020f42c2d95409080150b211a40d41e0b1400b00d8044050000302c20303124241c400d95440f1100703001c5a0303034504100e0352011a490a4010204074406030101c4c3c0c0c4112104109910f405100c0c1070128000000b5080c0d440484011200c01c8619100310584004e4442829219001c10300d5207491042c41c803800e584003071300d00301880180708201c80d964a02d4254203650202500020354090b68804045643c004000e440407918041c0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 166324550 1250 166323300 166323319
    0x20609010203013b1518130b04030c080403060b0f01020316060c09091b2006040209040201120507090303030f0c0801030b091609021201050405090312102102040b0609 73
    0x110a00f4000f48004407071040c540740d500e030b10f454550316654240c0c09880036038180080c83c9030b03174000e000a000c0c4550f00110400f40c10b0080c001c25010010700050035940104404580751500e2030211480c03103c08401400c0c2c0d40002c20040700b80103107a4070000e95100c0898544c101000400c005a80f45c0c01000d04440400c1a50000360001c1081078201100b250200d1904500181c0c4411a801c2225180071000307070000004000365034195003100e134090702d00052214070303c10001e1000343d4a594090050000303008644070400700d07003164000e141014151808580038080b40c030307060100034000c03025403205400003404c00a00446106051140c0381c038124207682c8103190350307003151580d40031303810040d041422900c200c0790282095042c41c441940a02042c200250761a00d1804030085a100c060308a036100d545800c09105480780f0000464202014078008141d01e960381c410a01e4911144d907002516000f00f520300306a801d0312103a0300858052003280d0401012845905000c250300481c5c4c0c0b016082400003 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 166325800 1250 166324550 166324589
    0x2010507060f0b04020f1903020309060c0a1206060f020709050c0f03061305010305060106140a08070e010207081e0609030301050f130603020d080301180b130b030c120a0302060901020301 82
    0x141c1200c102890181004524443c0d1207000c103040740d0080b059452910b00102d820000040740110b1000000800d160950950920345041910741c0700140041d044c11100154605005000d0850484489620b101c10440180c1d9080054009292020460010b01403404081030700001486a64041d0700b0200d191030804881440505803544082c3c00c0a6116010000280d1250040d01486020f144110301802a070f514080000e4040d14610110110105080c0905040f040d448507a4a42c442180e180c81c0425401f42e50041c0e05000d015004500e5600600c038040c1c82c442189005d21100c030f43e040f01140c10340d80d079200e005a242d00007800307030560202e58141703c80d0807860302c00c0d10b04020003410000050704070b82c0c03640014030145406808841049021004001c00f0042d107800f02201c11b01e0359000d10a0305407420003d011103112034a035001d89641d4100d4001d55072020030103816181d90140207500600d803a51000345e5107920844c000c030010304c01c40d00000c18120041c02500d0480758080c0c58400d07264000e = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 166327050 1250 166325800 166325813
    0x70f0503130203070302042a030b030a03030b0f090a020307021009050604080901050f13030218041a090a0f0b060301052421010207060f0e07120f0f1406061c02010507 73
    0x9603481a80d040c4134100c004001350340c2d02e210301d0407000c0c41c42c0310006050b40e80d240740e088480c54010700ca6081c9441d0240c4c101080d1004654640c0040c2c2c10301d00018400001c1000482d49214001e100360051001c0c020006450219401513009600710b4086035100c0c0c5080000c030b07081d107492641c000d0060300480017280015140300d01800b030900d014103101e401c000c0e440c03200c804240c02c10649103100355900041041542860481a038100f900240c4600c8145419200c0110882d1102d5083e02e211407010000742c1001d070f0500480034815071100442007480b00c10b0828114040d425203000c1e02c03e52a001c0450080d00c601e614034150307103503d11040c40010403c081045507440400b0960014810b004c1164407410f075007031006042e900e200c2c540000303184a0701d52a0508481c40e041900b001130380400001c9c40303110b04081ca441000b40d4402e40e0b00301041e10070319200c54044e42802c3d0040c50085141c48100140e0701c0440e403d4401d4009454007104c00101591100080101c203070042d011034010003011000c03961 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 166328300 1250 166327050 166327081
    0x3020c0901050f0f2b050a03080606190c0203070f06020619051b07020f0a120b0106050f09190807030b16050315091503190302100b0a050d050a0c0e0f070f0503 70
    0x3281746003440c00559016248500610b071500441d0b0a4022800c0d80d01059086040503421040a1752000c1c205550107044c0703000d241d03d040464003484038000b0031201711758041240e08044c0c001e203032509482554a00001c1d660f2030040d41c3e500c1d003d05021a500b20720400c240300e00e03031040405000307021310210000001c2100d54000603003a80c110668a00403101d584407480a03c0080c140d211405400e0350322800c0c80b0b2502d000681104003000700130464035014036038200a417280c400040341d5180f030000c0c00c54076330a0340c3d00c541e5004541602400e0400028001d0400c45a88601a91010101c00400051086485100440c0c0410300d0500744a045403407828420031f00c07a40079003030f85d00001421040d5000241750100c964071040451800500c000101030f0305210074009081d482d030081c0b0000180e01c0016581002e00c4c0501030050464a0100c814440c0c20005002955040103900c0702c070316200c515141d008401110400040040304020a09480c8210800c01440c03c16039101030640e01c6900b0303582144131 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 166329550 1250 166328300 166328329
    0x9080c010912031b1406090c0901050f06040f0b031902040605040b03090c18160c020904020103090c0f0909020f031902130225030314040510050a1803020c0901050f0f 73
    0x15600920038800011450107240d207004420001c201701c100c0d1511403902e440104200303000d03007010100743e00c030351941c1b500141503a0045500c1d100814401c4085810380c02990320040300014001d00c0041c00c403000e50010b5000311441402d000f503460380080e900060380300e02c0c440c042c009101008200b0002c0c911001079a00103400200783d801ca00c1003000011042c5507c40011070390108400c051101482c1c030a00c0c3d0342011402400c000707056803240d80020b590443c000b8000390615841c2d911400c20005420350560185c14440c00301074065840798502e134000d0100303880881c0115088e8a4002551034002807590801d01c1c04850b988119072143d00b400f48000220030b212003115002d00c030b6040c50340001c051290341c18007042d80b400815921350400174191001b524079100311605c40d0341800b0200d80003043c560141081c01001007075039120701403c02d000f86091410445241c002d1019407040607404611101d1a420480e45c120281c2d032039104200c02e1040c1c0107992580980e0750b00351500c4c10b0420032900b040ca00c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 166330800 1250 166329550 166329557
    0x1303030b0409051501050a080a0f030c0f0c030201020d1106041b090204030305090906011b060b01090b03010b030f06040608070303080415090f06060e040c0303201c09080c01091203 79
    0x201003000401c0c1511000031040b00c10342c004440c460540201d110040b4014a030841c0c0c1d0031030491a002845446040b01080a884c4540700440c0c0001d0500034444c213a0306a90040d8551501d80e110300303040d0340d00701d070358003049005005400c40b44403828443e94441c24080700c0341028041c9030b01e40e41da81e190b03450010b40e031f158034002d45071070001481c2c001c0f40702900c000c1d4001e0b00c07550754800480c020400d0912005003110306009003001d081d201079045c1e080c13800b1640e60050f00050744074050801030b24410f545500403101c030040000042001c1003514061409407100003400103460310340b00200020743d00c25005140d120341c088001080801d10070301e0455000742c040e15242403680c45c0c20300d5080940b4494002030340c2c906e042601c03d00070006148600b500525200d1001501801c15035904d803c805202d1002800f000a41300003e10245101c941d411411120b003021100036103a440d50750740392006101100400305002d0000041e03400c02c08110032030703180c1050755101c0c546030810200303440740181c0c1c0c0000c2e001c0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 166332050 1250 166330800 166330811
    0xe2b03060305030a0917070e060d051c030b10020d080c0a1b06090b090307080d020a170703050723040b030c210115050c06010506090f03030d06050f18130303 69
    0x1040b4244001c240074030b426503604401c81d040010031803019040d204140303200c0d80100d40410013020719000058200004807000a120701c1c0d1070070700e40d1510100714031001c0c00204103102800c0b0755426506c815520002a80c1e0941c1e4042e100205a807180c12540e07015003c90060b034002110058140020800c20302c0c142040048010020f92003680013101e124103d0700d0307998900c900707014020203203c285e0780441c1100040d440d003400d039500d0396114043c426601c0700d425008101e900083d4085e003035404240300c81a640c00203070b06d403407a001406030034190307583c00c0400c61012204403885107074106007007224525844185024642000d8020550005048070410f00701888541111601e950700c4800c05030800b2006c0e4415418030b64110300100800100e0414400100071200c00e96101250150449030210707240c6444480700404190303211005400c0c0b07076041c0400a0fa1412140140e413000c13081d00d9082e40c8402c00c0544000034454648010402c0c09620003046002030005440108540032080c802d1030302058 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 166333300 1250 166332050 166332053
    0xa09050a120507061103060321180439030603170a0e03070303030204030c0e0115030510052713050a0609050a0602072001020d050921030a080a0e2b030603 68
    0x1245c0800c014079480e15800820f1084500d000c00040d5506451440055000e80e40340040d0000340c03140c0035107404100380c444a10302280d0f489074060500700d60f0b02e41c61500c1c00000c45c0740c446030000d0606082c411166480021701b00851080c4508000ea03a07200f0820480041c10292581c01500000910000c104414114025680b800d01403800190b1207510050388403421464054a170304413a4000142c19140500104128410050340c588402224103002a203a11115646600920160001d541080f611610b070014024000801742600701e50300c11142c225214100c02e02d00345490444080d00c2039000056200200d10a50b00c182c401c41d22920482d010302c02a0780d19041079030000c45040c1c80d07400f4020034a001700c03451800001d40103002417004d04ac03000c0c0c1e00200981280140c1722214043c1892081003008a80345480c03040801038150216501d64005160013011401c084503814210b5041107030710601041d000490300124250503100042c20a14101034070140c91843c40307000105511400c0000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 166334550 1250 166333300 166333313
    0xe0301020f07080307110105040b04060f0b060f0c011104030b0c0a0504050306040f0506070c080a0311040b070807031805030604080c10060303030b120f060a0c09030606060203030105090a09050a120507 88
    0x1284512480e442d030386a1400c000040c081c6c0740140d01c020350704e03414041000700041040540c00c4c0d02651241c0c0004045102c01d0130000102940c01c03225030000c000103002c610284100000d4000715a01d14001e0001d0009411903643e0b50045110017030820a821001c503000c80981406001141404c0ca845410a41c0e900c000a2030a0010750f0181c603000c1c03d214125050003421300500b41e200001d420301c204010029074501c109840355445030700c200f6944210b644001c11140080340d000b8107147c0708007902c6070714500306228150300410044011542c00229080014000810941100d400134003034100c0d0783e260344482481d5030203008041a079000700091a00624680d01c036032720107580643d07400940e2b070859030107100140c0305a2081841c40d510845a60301040800103440b50300c02c1d4007220206910124003400d07540892039030001400d440c14410042450360b4000095412548100d540c50589c1c2c5440440000702c5040d100068120b801400141d4040341400f440c240c01e0381407900e085850b01140f44c81d1071 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 166335800 1250 166334550 166334557
    0x70f0506191a031c2303180627070315021305150406080601031d010c030f020f0409110712080a0515010806010e06040506070803190507020a150f0e0606030106060f09060e0301020f 79
    0x117103080080180240f081c40c054010411710088001001c1c1418448001d910080300300f801c8915200d20342450407292542449884020740e8402011140c884002106030f000e50420311500f1490b021840001a0619103400b441101c00c000c0c003111490141046001c4031002c07402031200d8149610344a44400208030f070704010346281c0ca030000004a4007030040004007560405242d90040030f0040c00344140f96000d14041300d0844540c0000054040b0326058080790601600c00042d02c1004410803481d007258019a00c0d500c03d0300104010881a03071001d1000c5d808130f0820100e6400a8101c00015200e075000d9007510b4600c540042560741042e5640c0300240307865203d404100c3d00c00801209000122000074003884c1c0304440d0a000313111078036001c50003d541300020320025002c0716003a03a989901ca4900d0707200120895461409011481200500568030f400503513019000390320307082000408a104580ca80310480c3c4a50b0381d4a0000d03e402001c43d5002c1c1c50a00e52a4107560801603100450840c0004 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 166337050 1250 166335800 166335857
    0x9143307210905010b060315040203040c1d0f071b03080916120606051203030f040305070c0f0303170408030601030e010b0a03030f1209020f0105070f0506191a031c 72
    0xb182c0d0002d80d14115007595540c82c0d00701e0260000f0320500204948804407030341005415035006072280d50f1420003242c6880107030b0218410342e044055003200031840240061198072500c021000d1a01d60050860f400326000480c540c545500c020144002485040b400340c0000904085800044007418800100d03002c9038011b4401450800c44201001010700500006010031103500030300c01110741d2540d03100d02c03004100c648165a02c0300000d0415001c1c40995402e0f13900100da1040881c1c441e0500e09202141c2e000a401080100d80c06100001001942c203104070b034405150b5007141c417003030015006001144071400c40c035503d83d44500419100c2c86251001103000703039280d1250082c0600302030950340d0300b6602d0f055810305001640000d84c40d44002c00255080a180050f0b885059091a04143e41d20700b00041182c0111000d0001d10442503800300100c05102c0810004034001d174600c044101c0f0881e5030f064064000c07209024540031040c1c048a450409420032007140e81d40d02c50107003440e024680c44c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 166338300 1250 166337050 166337117
    0x1407111005030907081609051306060b0301091803090312050903100c08010b0a0c0f02060c0f0a0201121a06030c040b160303060902070201170603010e0109143307 71
    0x20092400800c000c2c6400401741403001d40414401c0c0d0541206d840040d01071240c0042d1540c01080c1d50b000d2000c0d1000304950019400c00c2115145d204c0c0031030700e90080c450320540c2c4e802d0800440b000303c0c10511800078150326445213281c2034a15540c000150300301c0040e0105002041c003084185842c28404100010161030700016100540c00d0098000b58040c4c10000b01c2c1c003428010000e4a03a00220200c41560b048060143d100d00030b40300041c0144a50050011a0301844400492913000000e0401980b40300341c0703665840da1800c417a20001c54160110402e4017400d850010700716406d000d00150f4003c2e10342c4203850300d419110031542d409a440380d4405848400c80c0c11001c0203259240c401d40c005480081c60540c90121541c0009042c9c0740c4444034a10810b244001003407207981c0c01d500992030041424020b001c103000c0b50a2038103a0b1410080e800d1080d003d10039120101c00c031010300c0a102d000203c003e803076019203035002c3c402c0ea80d14020320703c809010010007800c3d2100400342e102c003400c08e401d10 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 166339550 1250 166338300 166338307
    0x40501110c0c10020c0307090b030106090c02011b1404060e0312070506040317010f0501030f0605040c0306050103061d040803040c030f0b010501020d030b010927020a180806010302011407111005 85
    0x3083c0002e28915088070401c541045210f1001d99602042240498030501170100d60030124400180c018020340d401152244d06c5d0000300f00e400d80c1c0642003280a40c60101c0c031110311401440003034590328404600c2c5082818200400e202aa0181240403007a81001d000c4070205a919010035200b603208110076150b60b44544100700c10141c1c0304441e40410101a100b040a5500d05540c2c00074050160059078141741e00d99050b481007054603030010780145001001403210103a50074000d0b00500540c012180064100900802c011503641202c009444184402d0229617503151070380150f68001034402c0360729180d001c00020108403c1202403c1c10783c0580c40d0f060f0f5030b51410002a01d030508202c0840149414100c01200d00d80e00419543c00700c5101105486c0d20620f088542e40b910101c50f0307101e5000c240f005c80d0758142d150740100690101c5504030f82c0c1c000000c2d140c0340100d94640c0c0900c0300900280141c0c1c40400c18801c400003074a0344c80c0c450400e15290000000c0001c21800f00144003000041010 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 166340800 1250 166339550 166339573
    0xf0103180614251d03030c1608070b090307060c0f0507322211190314090c0402210a0c020715050909071403070c0303110f0909040501110c 61
    0x75070b01801c00088002c0b6448031001004004d0458101008814030140c503142902c50303a5107040c000c84290000030400e0722601c0207400300340103850300c81e030140e501301b031003030000109003a00880b045810700c0134014014941d8503e000c40482ea41c00e4003000840300e41c607100f00c03108002642044103101610b10341c4410096411040c00140c10800d0310016181076195044161741141c8801001421608042c0b50110102c04052005005011629500b00401500180700400400d0500e8064030651440e0345c180080f820f1b02031211084402910700e00a45c1d00540d00c4940c00c0e02d01a40181a01c100e0014010324011040402c0f14000900321040400941c03101d0004403102d03814800e001c09804440034040422480e2080101035008448001340900380400104000c41d0090070042e244c0c507100c2d1011079072847c10314402050410514800c03008a03050a200711364030001501540c14102c031103540141081400303803c110220b030380540141c44039503980a000d001c0d400c01c1700023410081582c80c000c142002ca017 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 166342050 1250 166340800 166340821
    0xb0301061205060607110111030703030603020a0503030c060109270605040b0a020f07020108040c05041b030507050418180203060a060e06030703050c0105031e160e010306050f0103180614 82
    0x220359401045142500308403d5990f40c0040e0313804540c01007001d18076407841d1001031741c581003410300c1d0003020303c80400c0c0c0e00109549030b0401020303a40309172130100480713941d04c041c10f1366070046d042030f403080e40c10803801803100da02c06606c10000b130140380904481001d914044100306240481007610b200d500c400800081c461102e8400d504107903017200031403811035100e18411550064840c000d0404c41407038041000c0c07001c1e2122090183c44000c0040102da000246406c509031300c040c2240c07022a041800142d80c240c010b0b0b060710100d55440d18083c0755003d21018800042078450808148003944804280c00758030200716491180c0c4d2840c1d000541a4149040f000842c407000305414420b038044103080c000a08c0104031101e01d0303102070901c4c540700d484042c4900c0e031200340654021001d10481041160503040403221403e0703800b0740d8482d004201400b44c0110256152401010303005018180700100a500c0703640051600607400d82490a071001c6c0d40d60700c600f070745c2c3c000c261220381d008584180101c00c2c01 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 166343300 1250 166342050 166342067
    0x423040c09090531030c0501050c190c0b0c09011205071d06090f010c020a0902030903030403090e1501051b03040b09040b010f080f060109181d0d0801140a0f0b030106 73
    0x50446142a280da80c0070b49018510440e41d002c0d42ca10b13010451035003010b02803000c100304a0741c0003009004070b00e490f1440d0315103a04010101c403002c0d0a800c0f26550014043c400c0c102c1007942120b2000038a9690030310f40996640032424260420002081000301c807842c03442100d0090003141e071020f0b0103031801c0c0d0ba540c2d0841c0592106c10710444c1d081041d180305070343c1e400c905034070100e086c2001082e581c07040c00020f0f0414100d80c17241c10290300000810915450200055220318030988801444540b59185c1d000418000c6549541c103482c221200e100e607600902c082e2034412031000c1c0010b14035600d6510582960400c1c0d200c100c2903080410381084903d8240108500003d083c07034180300b40b0a260500901c40c04014009009010b0b220022030700907407188041038040c0c82c590b40d00711500030212032028001c01d03d4207414146240c11a41c0000360309004078000b01c0843e40c60b40d030010142d08241485425458404601e54884079094002a020704074041c004018110b04441940300e61608402030010742 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 166344550 1250 166343300 166343311
    0x227040c06110706020715050c0f01050105090f0103050c040f2310090213060507050120130608131e020a030f0308160512040204090804090e0c040c050423040c090905 73
    0x10403201044c040180d000911408844010a201d8030100c0031000a075841d00c500d80901c4440e02a101d10001c0c074200541000d4102d490554040100390303030355610002c400b40c007804028400e1b080745000200510b0160400145000c0e44c8600041501c001062002d0141c010b079082841100198100180300c4201c22000004110280d400c0d4030700301c03520900c8103107101c1d207009280c144140450104d0512109603c00b01080d01600344c2416078110345000c4664580140d01902051030b03031072101040c2180710b400c8850203400002d0300c200548099550700203540c1420f90342c1c42c0240500b00a030f40090782e80d20034900029806001c02801d842981e0030010034008006007002d02010045903150b1000c2d9000d0212000c401005003e00d0f103d4846200140240180c0440a045404003250200d11000e40750302c0035101d10090811100594805818032042c0c07001980d0b80d001156042c041000307200d0204d0340c0ca0030100c5200c040c0702c0c0b51075650400142201c0849244070f0014217698400e106400e910b120300b43c0c001 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 166345800 1250 166344550 166344553
    0x30b030f0307030e121c0908011a01020d030f020c0a080a0207140904020105030403030b0409050c0310060e010510050c0d0210180b0a020a05040f030503031e0f040227040c0611 77
    0x803141d46000c1e200302045004240641d01d0303101d021740803880c1448440c1c0e403113004074162260030b200114002c11007401405556200d5203032109401480c644001500b4000c0c4060300034010084400005500074807001400105030345c4c00f00300b00e540380e02080c0900c03503000c2d11a01c105500c4030b0f404c1000900c0c0000c140c010030020a01050040403541d60000d05542c419424601296680e0322894103e020b0241c8204158015003400403510800002207841c0c040ea0714103604840040710f145409074243d07030551044812000c2140010300050800007c5050a034a00d03083c11803030040d0381d4201d9450050059056401031704402a42100c401d458017134245580703100c02c155104c48099031202103400c81c0140880004c03c0e8000b5418081034060f4090740e005101d9021038030303101503590411076260b86c4102c46400440e5802038002c401c807445290024000c00c10148040810b5445030b0034845080c5003031032119440e66400030080b40d850342243c1c00c6403250b03100d15000711496107020700c0600801014200c2d0402e5 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 166347050 1250 166345800 166345807
    0xf0317040605030f0a0221190605090c1b030304080702090601050c0319091d041101030c09030f0302010906091101020c09090a0b060d0605100f0803040b0a030b01090510030b030f03 79
    0x5503900030b0903607400c2a4a140c10701c55035110030740c0c0040248a00c44410b518510726504520410301e01e200100d12400c2071007101c0b400d00a01d11a8042110740c00c1c00b400da408000940415540c1c1040c10140c441d42070900e203601000c1401c07400e66440c51b081285c08030740e030000025030842181040c1441a400c400282412030070314070443d00443c0c40b0b0160300081040d18040a4100384c0d00792040c0ca06100500c030700280e49021402e85000c0c0219032100300e07400c0d0380f0a5449000c502a6511a102d83c80040c842c0c3da440c0c81150342950381d06107201070600030a0b002c640d2100304040c00704a60344114202e443c4a400e0642502489070000390506143c044803d11406003c010020402c0001ca4020302e03003640705945814a030303180030006944084a00d00500501c2c0b4110030031040045540c00d0030161440c2c108196409035954054a540b807045000c1c50303001c07840500030728440c24001ccd00521005101410b01455081d110408901da03115100014800a6150a402d90041c1414402403c0300481440074519 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 166348300 1250 166347050 166347059
    0xe010209060f030a09080a110105060a0510051e1b06070201050c09060c07031b05150a020a03051b0a0308010519050315061309030c140d1713020a0f031704 68
    0x710300407440102509800040015560340ca240c0c41018000e5001c0c0c840c0e6203801501100801303a180c0c004540590750700e014041140d6141c800c00d22011100000c001c031400ca2403040b01141c403a0000d04443c0482e4552114505180007404098010102c02251403030034405402c050070300c3c0c550080c05260545e4903110038803040c50300700001c0721303c0d00b2015500d0b196504000349489181c10802c0e4005003c40260013420b0340422007801c1860112002103d1801e9051901075100600d482200c600ca000340c0e10126134040080d002e10050302d009410b40c0f51505807400381c44881820844000000c4001540c0400180034503e00008041c0440340780240f90000c0c507041c400840d64803007240d80300407000c6030200c0000d041076646015130288510303581030500101c1c01500d0040c3c02c0100b4100c0440b09820000c15482c1d44060000d61140a0456540c3e88080c0318400403120850441c042c2482600410028070240542c82d0010040000e04130340340d00001e118694103100030390820280c94005c040d5010081040b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 166349550 1250 166348300 166348309
    0x131a0a1d07030b0a0b030411090702030a020a060c090503061f0803070201090902070204230906010e04020d1212060e0f0a090c0902030c0706060b09040c09350712060e010209 76
    0x194050500d0400043c2d00300510001010510b06510090301800004104000c01040301c541e07004921041e83da00b1495112140c060b40c690140300b03050001a40001c1e400b101255841d00600070840403810b040101548071710100782000000c40e048402010192501d640d40300090800d0b400510010b006542040f0059000900d564128803c0041d010740100d281c0c402d6548036848003456124501c00a448400700c3c400000b07441100711511902c900581000054030024014114404e40e40180068108890360351035003c4042c02d8030724202084082254032410748c0c003d105503000750100c190121800e181c46030820000e0940141003980690400d10b484000071188040102981e09d41d40c0050307103950b40c48411070560700034003070040c0c040741c106500020590080c0d00140324038901501e05001d003414024058a4904040c8100703d15010341e002040c2805014602041c420f0f00c216444040c5000c0c218201d6181c06031075005080103841c00d540110030480e00e885545a6082003030300a50800d04010f000a = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 166350800 1250 166349550 166349609
    0x906030606140315100c05010606090e06040e0a0b091011070f0b0a020c07090b010e09010e01050607140303100f06020f150702030714010c09120507030809131a0a 71
    0xd181050010012031000004425003e0314088081d00d40108103140705e000401c2401ea0070416902e40d4607044010840302d11648081054802054959200d529a0403d00c0020480c0c2400703000240a004003d80000d00900203440c001c2c1e850030020144201b84c18024421a000c00300d5220810004000c9500010700c403895080c0d140d9000590442d09594002101d0701074071030b10b10400c0160251210200386001c83e80d01508907134101381e8551011a501d04144030b440c802c02e009544501d1850340040040c2d1402c0c000030050148140a40711541e0402e100e400d10315001039807820800c01515a007400a254100d0640005101c64402088072003000d040154841900394051030745008a0000240781c0c6000700201d5034010384c481032141c40c1d40c10901080e0700900300b00c43d030040055802e49000940c2e0412a50740070388190040050300c03100e4a16a65040c007a0300c110000d9400400a428024203081e407407180340498010b410768030003024038030403c04c904e070704440c8c11404004002000d050002c400c4107040 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 166352050 1250 166350800 166350827
    0x60f051c0f1401081005071e050304110306060d0b0901140a0c0e032a0109080607030e061f05040b0f1c12030507020613030201110c010e0d080912090409021f0906030606 74
    0xa1b49840b0240101d0710b4290884002c00794280416a44520707542c054002c51140e4010300c0360b108181c502030101a03e0b800e0598069038000124140c1d10042043e0b040c43c1034100e034020000148001480312005100f1208445e407540c1507580d5010041881d80100382141d10060071400762401d0b225110900c043c21100d040c03c0900400091188017103030b4000c1d00c0c124003801d806822506075140c600c2d0014090a200304040542e801020003003201c107075640d200c1000b03003c4c00c1040500aa400c001c1804001c00107000820b034462411540d4080d0b54540100081009a003d0802200c100850920b1950030b45840c600d00d003014501390030000095408140c0b1034000c03541e0060310001010f83d090403405444184d5204855850005445404000c1548114802c008850a80722503000c144e00956204400316402c0ca60354002d440503e600c000300b01e004090fa003d00400014074091550003044001c05220b0302200c0088165074900c00e0943c0180340301000702020b1a00b40032140c1480c03401032841088052 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 166353300 1250 166352050 166352083
    0x1c0206130602130e0c0904061e061407020a0608040501180c050103020c100204060c05120327011104120624060309080c0a0503070b011e060f051c0f140108 68
    0x3030043d200c2d0907450241c40108108040007490742040f1a00d040607074400b103035207071060b0b20740400051804c540340200514400030400b180b49042c80d0036020b540103060b060362500902d400b000b08800503615460724a020f40030300d0383c81d1f8056241c0384c5006421900000e58007001c80c0400c14803403000032000da2004055541c207180258580d038550b044a442c04901e5000040003600115021841c1607101c800200801c0c019170440e40c60100d407085541e940d1000b924501184d4010b03c05080391480ca41d003080c0341c00b40380c040001560b40c00c8581002142d03040b54100c00c5448000204010a1100a000700e030b07158042c1c010000e802c1c400343c600300c03004a40c1300e1040505043c0c489014400f48146442500c0002601d20305480e4251501d1a20366100d500c0300d00e0837560f0361105000820800c0c42031206000c204040c109202045040600542e051044002c1e2041001010000716104001250780c24404052606011620b1160448600c00352898821010844044003004004618001481c00c084c14180310 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 166354550 1250 166353300 166353307
    0x9030a050903011515030b0402090f090709080a080a111606080c0f03160206070504030f08031819031101140a0e12040b03090105070807050d0f020415021c0206130602 73
    0x1c01080c09080f000280c0b0f41220b40f40000081c840c0c8030b03c3d1903c0c112a4459508004000402041200701d0140b100c07900e4100d2111510300080381403031054603030042260304115449580d00d03003580303240003d1481e08464511012405100003a00003000364410306804000d4020211103090b14400303250036110b042c040041d908045884034079103500721200004882c500c540d803132900d0610700500b4a10b8210060043c03040c6000219054480c1c4162020341c0c3c0d2141c1c1c2072078464001c0d206c1d0212504060003880c9151540010291010750030003820f5241c9211011b510b003055060304024241501c95484807045906025041d0244024280417940c4403030b80e1140050b01d28080d0f41030915140501d684200b1002c1e00180202d1042041c001861045ca0001c0007403140e903503901d008032401d0300e00f45c4c0d5520210340107000c04005041d860b0421211004005801400c0581da40c07001c4d00c140180c404c0401c0036030000d4403203c124a40081204100c4810f5000800317031410700554003454981d0312040540105d0f400b1 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 166355800 1250 166354550 166354567
    0x6050a0e0402090a060207080c06030c0412021309050f0d05130603020f0706090c03170a080609060315011509081617030f03010e01081e060601120902030f030415030509030a05 77
    0x164151025443d002c1c0104031240c0d1290740107540c1300003500944015102e401c64000c82842c110040ba446030400303e84032414030b0b140520081c15101d400344220381c80b0a00044802410000344529621140214000d12501101d180305606226100180c0010010308101488540ca42601501e048400780c1c6070042e42e03100500d070181c800d405440c20083c5030500b0004a201031000130031850061340d000c4c01e00307014003108920556002d8402c0d40c030a40003240001002810030300d0102d10306a8800c1d80901958544003140390001c0c60024240c01040300d040d4591314188540313274008040c50160210000524400c510041d10f5049031580e4820140281c501c1e1a8071034003c4001e2081d20004d0f40625550350322940c540380d0f40a0014024090081c003442a001c40e805040380300f11030842d0302e404440c00751001c0d482e618011100651207807802e64126842d25810001620f04100b04034002003d00061a1144d00341615540200c40a50a60040504007010b01c03a00311408000c0b03039280940703400e0480c0c1c1e60405 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 166357050 1250 166355800 166355809
    0xc0809150c0f0303070f030213031e1401021b030903060f040c0807081b04090b060114130b0304021207212301060305010e03071703060103141005040b0a06050a0e 71
    0x1440d580d19040d0046090040300c107070780040914041c0d0126142e00001c1e03446c2d50f404804038090314404000100070010204045484030640c1150602c200c204407503200e40b26250ba00350030380c40f64050200e03603500003117200c1c03040c0d9015401741c0642c445034055482d045403a00040c1c0e0704c2c440030307000211031640080414200020004614000c11404003610061669201e0007078840307038000080d801d06a1104580d020510342841005a4280c1c030003408412a19440d004403044260004034000a841c101301e141500b08030003003043c00070304000300200d07a80d14291040c424481024108180b00d42e215140520280d5448441501c00c140308501d02d60001c0c03814100320301c600c40121103550041e803403020b103007000807010342050050f81e004031300034040d01801940c400e560f441003410140c4280714880da04000506040c000b160441014580480d612070594181d0328001d0050728602560940040304104505040c015003440c814211501c490b543d1030224050301900c12501d8400402c079404000d102142d0f41d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 166358300 1250 166357050 166357057
    0x3031c09050d090e0f09151f0b1c05071b0201050412081b0616180806011d010603020f030703021b030c030a08090105010303050f0703020102040b0f07120c080915 71
    0x1c10000300d8609070095800580751200502401d401c424018002400d001c01c4040e0070790180c00140d006040441c2e41e482224480e440207002d100044e050248204404280998188040d107250701446648a40902224515400550b000704c88a0309200402c075000e50405004a00007001031103e40307214940e8030040b40d4511035504000003a070003103203d400c280441c50000d0070307200300000526100043c0381400d070307030341d0b0501280e035901c0c4440c2000540c441c080c86010541061806481c00e500710030345594031182020000d030002030070345040e0040105aa2150300b596801000c040c01c04501d0020f80600c3c00c030803440020b1800302890340020700952800126906244010740c108260b94540301d000500c151641d00c52050440020354000104074002e80611074030b0704aa03850384456151490a000c2c6841c541c10401007075003075540c20f01c000142c0c010003200030148a04140e02c2c285d550000c070318040030b008084140c04010804030a0f107110024002a04654084504840c0c00f10700307170402104100b4034407 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 166359550 1250 166358300 166358303
    0x212010306020702040b03070f060e010207030c121b081b030307050607050c010c080108060721091101030c02010c08150d0f06050601080612120a050706180c0501090503031c09 77
    0x1100000000d00510381e000c0c1c054503108803011b0000031407500402d5074a020364003840c810080710700b10400115016403458480c420060050300c2c41c1d81d030f40761100055061036034000c001c200740005510040264420303480c100d00b903ca80b941c00f80c0a0030710030304a0351000c074020203020140c10365503039405564003001541c10603584203046604034030381824001d01700e80054400340700660038002c06c2080c0c180a0849607050712081c4000b826981d444050071a01c0042c82c01808694090f6900c1100001550b070190003102401100d50141120f10030000500715814044004210b9141085041005030b1000005070000906505422602e92100010300d0708107a19a0040c00c8034100e025860801c151034101c03601c0703414240c0710902c3c41d5a804091144c0e10120f00c2d500a03507608640040540d04100101070401c0340c2d500c1c9003203130070882c0b0703075a0307040480303401f251010a0601e160f00b002c000c0150b00402800500800e03e800c215061501c00802d5407406048040040e4100c0f04000005582513a40720b01540ba = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 166360800 1250 166359550 166359577
    0x1050d0603140a0b0c0a05030f0606190203091905130b03100609060e010504020406081f03150f061e09050603031201150332070e040203150108060d051f02 68
    0x4100305440e8030340d510740300d6101315003880c40040041d4410303001c4025900e4455154446611b540daa110780c8802207400101a241d008506000c56010541c0c5084400e901c100305800550780c4d00350410401c040f0084507a103658400c003000f2014801600c0396114040405000c103804600016640000790a2030840307500303c45000c0c9449400610790036160408001c4801015a140c810790301c5405001c146d10030341c040c01001c1000b04000c18031640d00041170b1010119032580704002e561f165910000603200c0c41d143e51010a86070201c0c070034015014490300004114000c440c2c420562074211544140c800c51041c0440103981c2c50000700c280d00c05000700c0f050800380301840d8005685418024100350324019201740000c0c501150a0b09450b80c4040f40301e4240003042c146902005002104c03051100c0040c0f41d5420041c030108415840c1d101d03800a1405400e03450002c0790a5560b445c001400900001c0c0900d00c5940f400905001003080070802840112a190b42149040031203d0200d0191190385a001c2c4507 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 166362050 1250 166360800 166360823
    0x50a0b070321020403110414040b1506040303050901020f0105010503071518030303140c070b01270504030905190b0d150b041d1812030718031a010b041401050d0603 72
    0x94181590044c03098912070030100001e40040b4040c4070480e036507900003001030350113400810301080c520b1959640c800c040c095144000740c031071000f048451300304c3d601c00c40204034040b840314640c0d0780500c14010400080c0f002004190b00d810000b03a651b500074030600c0706c005241d01000c06030a00c41c241c180001c0d28052100e90042d0fa691500600a1040468032450307040c0c520040303030700c60303c49104864220303400c20070800640e400c20b441d0761040f02489030303c590704800c1c44071800d140404500620707210303e000780c5030740d10650f140000340000130303071220003c1007a103981d400306202003032154040e00ea041126940018811200120030040440740380c0000036010b4001c180000d0710481c0349849070202c0300801920001d5107800d08a00c140c04d01003514070f074a40d000900100c1d071600300c1e00301859010000d07251800d0304400005c002860102c481d0400c2d00c0e000c0006000040940d01040e4050061460a0082c1c0c941803400c203040300c5a443c26035220f8100309000808140e05142a0400005140c000e2000d000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 166363300 1250 166362050 166362107
    0x1410050904022203140f0c040b010c060c12060b0708030c0a090305030c0319050307052b180203010c0c200d080307050306010306170a11060f04030c1806050a0b0703 72
    0x3c0403000d9110440b030b80302c800003198908260200b80a40a81c00c81c0c002002030710304280401c8080d100201c0d05504104807500c411002c90401d0142405100c0d0340e0f00d50b000d166141c3c05080341503034441d4001d14902c0030b003000064001884801125070100c00c2e0038486469030300a1100300c0d240601540050078622020411491494001c0007d05403100d003540b844041d084404420b40b103602045a0100100740305101005555004001d03100038100c0c1c2489a10044650032500000ca1318003800a80c03102d200c01c5030321001c5040034401c44032040c80728104042c1c9400550345000d01c003d400c041c40c100c0c03140240003050300703905e91045041c140d52f80b10401320b81721719041ea002007581c0c20480d8080c9c0028200031001030075036041a0301e203240c2c40c28140079010200007910740d10760488081040c0c58101c41c1c00c2103524004201080540003940c070800c444055246442040340048102030810200e1910f4100d04011603555624260200e52041d005651108803606040d20310b05600381400c51456128142c0d040e = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 166364550 1250 166363300 166363357
    0x10e0607052e0f06050a05121c03150f12120e06160302010b0d0203030a05090f03010e01150906150309050c090403020601060f02121b03040b04090506040501141005090402 75
    0x10744101a030000308488103d1207050030950b401845950341114074404148901c5c1418041040380060120480702e113103040d5105880c6e1701d200c9402000c0007030356904901611007404600c05000b4484054806d40390341c2802c1c9003e44c51020300f24028031401c20b8000a0703812a020b00d240c0d8035400030040001341c803800c810100100e50981c182c0101d00651801101000909d00704002841c6a50042c0003541820a4014251001d900c40c2465580c40445082144070381e81c2d00f40140d0040340d15000005c00e00640400001508070b801d0740103001c5050602c401441062490944da071024082403034046200d8a45040441c01d01480e45402a0804e51b504200300a05070005403a40c104c6215079200c0c0e586c05000c2d036040f0b0b00c0d41e03c600405a840f020402008101c03a26000c0c2d030070010701005003901d1420740d0701c1030f00301000e911a034403003284a9103a1041216914152003081e00400d590550288030b0600b001c0090744a0122032220024440041b0354440d49071265810340f045421008140d4111000807946103 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 166365800 1250 166364550 166364623
    0x15070305180105040f03030b03011e091109040305160807140105071101150311120604050c0307050409080313141518030a2a06110304020112050105010e060705 70
    0x82004451001c150822814401ca5120300c0d00a00c14070210412590202c019000c9094030aa05649600d00d0b421080211039a00c0308a9501d403500080c0d140c0c6a19114601c605a0030b1090312407207200c003c000100380c000c1c0031584410109504d29201400b145003001c501d004000c40501490040d015a45640b04154402401558161280c103100505a0b05490036600e01000356442d5240c1c02c0c10800014655400d0f4548105d402001000b0324180d144043d0f18240c401c0380c007940d69a101c01c0106c0e10a080902480340070b0101a41d06011032095034a882d0035078070000e40301341c1400e071615030b441050200c107544040c12400c01100b90703038020400e19079101040400355105900d220003041c1c2d05098000000c1104c0c08081c80340c84031f800c0005180e0014608c0c8026410078080c5d841002030359800a0340d14410b804041c0351541c0f6035034907030078a8000144000b00343c1002d4040e0514110040c800740c1c4e045004241030304801c59803103a45d4001c9180403401c150000844408046a0456010100e60100004c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 166366906 1106 166365800 166365811
    0x910030b101502030304030e03070608070e01140a0210050604150e0705130617100803030606070201050d0606050307141606020304210f181505090315070305 69
    0x72403881403034544442d00160000400c020030075400403008450210164001c16007242847c0b0003900945d00540210288100e10010303426582c820086041c0d001c14070000b80d0b0b124011010b0107591000b80150482c5054146800a0054285482540765100340b0080c803403107441c85c050701d251007200064003440400a08011541c0150329880c2500700801807075490880140800340c00c0d1000d1040500306051500c0214820400c1c00c400200340d9410440495220fa562103003440161050310801440500c0c8038140b5100052107500300c0091403040865498400070700881c0c00d07202c00f46204410700081400e01d000d0740300000c6000c0b0b81c051540a0b100e0240ca55030710390208444c00317084d0300941103880000d000c514401d00447d8469030005541120509814103030f400c01030506a09580343d200c20007040300c081442002964100800541580304103403d10b560305202000501500c4115031 = true := by decide +kernel

theorem cover : BRFrame.Cov 166187050 166366906 := by
  have h0 := BRFrame.cov_init 166187050
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166187050 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 166187050 ≤ n) (h2 : n < 166366906) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
