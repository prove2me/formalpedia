-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2959
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:15:13.224638+00:00
-- url     : https://prove2.me/submissions/3ddae1be-de6e-48b6-a021-58eaab1d8149

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 532014388 ≤ n < 532194244 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 532015638 1250 532014388 532014391
    0x1c0c060201021812120310080105010f0602010c080106020c0d06112212080412080f0304110f0409081b0309040c09081c02120a050702061c05012114030c01021b0d08 72
    0x1c004c1d4001d601400041e2148901854005c144103200346001c80d2103401c960b003100e4090f840841c03504480c0e5000c2100503028031511804a0092030180308540c182140603582d41490101c01d801020441000740921400703074040c10903100000740580da5000504078403c090b00380300e14042111900905c00150350b40c81341d40030044155103d1200d500b032a141a111003225035980d00c00740c4540804103c90000713865403d00540c0300d14468001c90320103400640511090306413a408090045241c4108200410100001d8402001c0c40b000846a080e440c0c1500906600587c02c0594002c0e041000c40710406801004030700650345044221804c1c00d010041e80b1850b1119030000e0000761300100c0c0081e10001c10700000700001121428014a0f0640580c04600b4542c0f110700c000c1300003881c84d840380241026600450380100741e41c0080c88000b8690108448070f40301d805400400d25186400210b0603c50b040c002daa00303050f00341c0e008540310408444001000c215818201d0443e002c2e800c10300c081d0030300403040c05 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 532016888 1250 532015638 532015669
    0x1801060212030a15270b0a1707032f06040b0a08040507080a03080411030115060309020414010f151e0e120a0305040611010b06091c0c0602010218 64
    0x41c40014030301d1a4a1026901c007a1858400c15150310390038036200750f41d00303807513009180c01c1c1421081c0f890400b00c0443c00300c554066260700c07181428600e0100d0b503502e07441c84058921000d4207003000c0e42c500041e58a40103480c1e200410020406106200d4126001c141807006150840310184c0c00d1100400c01181c3d116502504480c0202840114855842428102c0e17000c0d02c2482240c405c80e850304040c500e0b11622520450009520600b080200040b858400c102b18000358028003034000030481c801119102e03405a0400c0654403070340801950b459400c2042c9140c0c0d8010007408558413190074040c0301e403180c001c1c1100703840840e001e402010720910f203802021206c101c004140c8200c1240842e90598841d4100f50702000e441c6000c920f0b00310500c05011098460380320303107945500d0b04002801484404c82c29100c10f0345401001c40c03043e103541c800c4135068030041728150708110919030120002c0203904805050034070b9806000c240903030154020001949603801c440c06c0b040302001004140d91620200 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 532018138 1250 532016888 532016893
    0x3010e010311030a08280f09032409050d03111303060903030207121106150315100803040608010501081305030d0e030c03130f0603150b0304080d0906090218010602 72
    0x4001054842c49002880c0d10000c05480d103c03059615035040741c2d0407096405501254089800c0149030540000403555906424440e101565004002e086919548406000165956012054002d41003540c1e554004a11000c10010f031807400d010b42e50702c0080404602203464001c3c0300c0c014031020800c4e540c40700107042058120504546d0b4a4001d42501d000032814141c0074003940c80020703508c441d14400c40b01c09959000012024000b21890b0220143c0100e0394981c1e801c5031600039480204000703003100c6808069000d552241640d4403c00212540000114000490701240e40380d8800d000c90304a031003d81c0c80d0005926844507129140594280082030341c0c1c020803883e1889840c0e1f40108a805e41c8000035a0300f06601c078080740307055921503e017410065038101e0051090032003010f00750003d8021490200702c1c144801701070100403d40c2d80284450004080001004c101b803400440b82500c2e0185018041000e00340350507030240c502443c0880c4070380e0038010121055800b99117402e040b0350041d0b00 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 532019388 1250 532018138 532018141
    0x30f06130303020708040b0d0b04060b1608071407030b100e1509070c0204230f0705072003030406050415020c090c130911030105210a0206030612060916050603010e 72
    0x60030b600a5008460840b43c81c00103010020b00740500101421468511030f0f40810349108070b6041000329160b54100c1c40c80da0105105140c90045203121126800758480e0f5280c9d5031740d900e41442070080201109503000ba2080100110030401c00c0b00300345000700c0880c500d420140383c64042049050740110380001030f004140300c54101c0c600d0445101034000511713007480708105080340c0100301502c51503a1440e2903051200080186030070015211948128551000542c504100d40c00074194460444050b1560010840c4e510403000c001c0303001c8103211002002c80e07542d1a66800050001e0300306124202144001d10b040b0460b290002c600d0b511400701c010401c070120703503071810f001e2140c3c1c02c0600542c1c40b00815110125170300305140315446010107180c217000e4aa6140c02c080280e50105155a60010b2800c0383d120302c030050340080c82c1c641c3d42d94116441c6899540b00c0300400c104410b112032041b400d100d58800d000e40b0f07400114a40011111261104104c25218020b201403444284a040101c804410 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 532020638 1250 532019388 532019393
    0x2312010e120a1b030f0f020318040e0312090c1806090c030c04080109141e0a020405130213050412020a24020403150501061d03060402040f0e0706020c030f0613 70
    0x300106800d55207800c003030400fa00200e03108a854085500218040b6040da094945003d800c015643da01c0103040c030081d03180c441108a50448096100000d90165407a0302071604465403e0003580c00c0b802c82c0b43d91099070b910b828140c6580d01c020b40ba42a40c0143e910006001a6060b1441618400c1101a010b216941c4031101ca9a00d503500050221000300300a00c4081510002030080d8003641d402003e006c1040d480e403050b01828840600c8501783c101da403815001701c07288000309090a060ba0100c40001d110340d00c400354041e112145c1100213501c0020603072000040f0b9030365403125000794080e408040396100100026680c4464401c005480314100c69502c071000303c0701c4410b10310310650403003001d424155030380d40d0f0802490100c4501089240c5881c0148006907000500c89007584c6090b15001080707000b02e01013070b1180d0b000790020b80070b107454240070241142c890300008040d0141c0000c952a081d586c1c80c0c02910f402e8607802040c8a4066402d03a03400b9407000040e203d02551031000c40b0304030122030341e = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 532021888 1250 532020638 532020673
    0x3402090601140c070f0902040503100e0304030b1305010e010c0c1e06090305030f0a061503091103100c030b04020903060705030a0608160501030f0504050d030e072312010e 75
    0x103140d2410812500101e11950328040060300050041c100182142810030760110000f113160b070068500c4910520080045030b41c000703010180b450700281d000442440703904d5020305502c070310740014201400d44801c0c8540d10100c0180c007a0003a004100800642c511050b0160036510310040d4900001e038144080e4011030625482c0d04d82065200140008100d6a0303501e50781030320764145003500072907008003c008008031400156a4010a1000c1c1041074500b0140303541d106105001e2800101580c0d02440c0c400c100c1c421074150302c251001011142c0b541e01d8004104058800082e09000086c10111640300380d04083c02600d0b17074084014042d200c260f4a0340c10440703542e0401000415041e48440d0000780503541880040c115082010f0780c668010304240014007079a610000002415150404000101c0c801250480c8000b9091a000c540070f42030260491411580303411121001d900303c0d800e65040e07040445400315400301554401c1c101d07428004030074200c0b2000300c80742c003413500b24414440810400 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 532023138 1250 532021888 532021891
    0x824010b0a0314040303090210090617071b061b1706010c0314030f0708010b070c05011803060e0d1e02030702090402040e060f040516060509042708340209 68
    0x40c0b4001801c0c14295a105582e2582030740d054010956812441d02541030084044a000f00c80741003d4400170f01e400d200500c030001c0080d6802ea121600b5001c145181d00c5020035907000741c2c1c0c4580000d000901030030408014400500c00030040c5100c40d801d200003034080c1000c10200301084680e0300060741e8020041d030f050110701d101103040000a8500039050340c9204082c44c012034105c3d40381d01e014540510050300f04d080680000c17955160070b000e000700203510248640e051702c4c003e103458001800700411040f048090358100620880c100859400c04000000301c90a0135441f56599149010802c03805402415100509400503081042802d0140c1064019640c0051000d040080c01982444100c1d0031f080050f5032040012200605010a00404200100c0320a900351024000c046c03070701e400501580305800429001340e407925022440d400d01d080c9551a00341107140d0341032001410b031410340744950043c40011600802129021407034484030802c840c0c00103001c0c0c00744290842c0360b002c2003c0b1200 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 532024388 1250 532023138 532023157
    0xc0209040203120d020306090a050408161e06020903061005030d080403170103030c0215190c0f080417010f05040b070e0a050a06030b01030f090519080d020703090824010b 75
    0x1060400c4290842e140000c4c41d01d9400c1100050b260700304007007003002d07884020f0080c103e00340c01d00b81484042202082100e0144030700a00501c806032840c1f601a641c941809148072108004505203000d0004940050082c040210142e580d03d42da43c4c0345099850080d401000d8044e030110f554401a14068810550881c1c041c0c10100d132014500116582000c400360003c60008952100b40300c1142800d01c07410300c0c0d4072400039000703040002611580840b00c0c50740111070100301001200c0c405100e121480d50340c0300c40d0860300d1103507200d8035602c0103e2401400004018076600c2d2013031100075014140710700743c0106c0d40070303546203595203900c0b2080b92280c2903030312595840441c401700000c5aa8038a00000020001e40d10003042100242001400710b03801880450f14180c108070301ca10001c0c00c0403800c0b02e0034044038400035900140601703200805008004030f0144032840011264103040d089201801103c14420454050b4003151070038050003c0440c0014084005000050040002c44006811100d8 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 532025638 1250 532024388 532024393
    0x11416080c04050307030f02090604051b0f0f070f14060f15040e15010f080f0607032c0a060c021b01120e0a06020d0b061908070c141501090c0c0209040203 68
    0x1500c07040003d0074500e171030707200701c903074107076800c0c6000843c18560691940044100d42c10031152405440301007200c03a001d21140c101410006030300d18840d4441054072500020a007105072103042d540742584034107408150070307104024081400c1031184000134103544513508007800c0c00c8880d19007450f2500056a001c0da05580710b510b0b14604051503804110020204200c03000f0080175524141962800740010342081106070406500c00540a8000904a401002d10b18001035040d6009000400c038481800044205144182211590074030000341402082c0c0543d4003000366400b40481640c0c1c902041d0f508108451201ca4203010070340c09441038228050408070081844070078404818140030b2481c20444a850340440da20404200c2d0340300302250f411050768210719200000880005080700400040c00b0002c1500c002201c1d284215100104141c1c040c040301c200e030003104120741d116100540400c6511101d0720001490340c1c0e5900405c1030b01050ba4686a406150366002c1c0302403c46c0081090340c01d403 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 532026888 1250 532025638 532025647
    0x2100506150a0e0f0105181005070f030305071b050a12030608010c0528090b18040903030e2a06030907120807060b030c01050f1c020c0f011416080c 65
    0x182010001407400341c41c103640f141c100c0d0007000108501200d02c0400541005010710054159500e0200400f003d0380302260b031815070490300d013811951882a000d00408010411601104254040d0400b6000e15120b03190081e01120036030b903604080b050440081c1041e0f00c14881311010401d85610f440081c4014500454040e464504040c203481a001080d80040d01c0005c11403180c81c2c0d41c40d08000034484d40d1240c490a41040ba070024140301190240042d050780000e551842407100c11480c00d08514080c005205040503402c0140c003d0071407241002660103640e21811007a00c0310341c0004418421204c4401c0d400f030b180001d000c0e09400050602c2524801c194000c580f100c2c0405503000a44e00c50519266200349034980202500d4907410342d06c1c065030201811250907030700038041c1d4451300108a80c0342d840f490190340c001c0010415540d070b50110b510024402481c5e1402251203d10308540c003000703010328440c9030404a00c407802220003e40c0141003e000e404224402c210380c0b5000741d0642080b5040 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 532028138 1250 532026888 532026919
    0xd0b18070e090c03040507051002160303030506011206050105041206060509010312181406070303140a1a0306190504021906090608010602030a0f0e0d0c0803040306110a02100506 78
    0x1140549048020941c1858004181e19100d00b050b41d1011142c070307000f811420070307982d46550303011280038852060182200c401c00d51031080104580d03000301c070541c0d0004241d0f00d06010f0002e010640d1494002042c500f865520320445026a4080708c1041c1d5030180703401d1600c401000243c0764178104507001615a280040da03582d03100c0499000e90702810081c02054850000508400b800c1390746034446020000b01081500000010b0650740d003030680700c41380c1e14502850120010201c41800c0240d4a507564107010b41625079500c548000b011034402918821a08420150745050031640100003411035112540034421641280381c00c68400340492a00d0f08003900c40d4205042c25420040000b1550401001a02d602c00da07928010071050001d03501c1d06902c424020b080441000313030882486000300c000c0285895804e0409200c81c2c100389600303240368607900c0383d03600ea40c400d1005503041c5040000c240d04a401d001c0c00c554075503900d07400500b136008006000e50041d03c4000c04013584081540300da03c16 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 532029388 1250 532028138 532028179
    0x60209060705060c03091c080610050c060f060a300f020a0b070b010e0103050c010c110406081516050d0e011805100e0705060d0b0a0503010c05041503110d0b 69
    0x590210074541317449141400742c0c07520b8000882c1007400b25030682030324021000e8011901581001069400c44000e02141d01e0559851198004240041c4500d004206103201181c0406014002c11164104075594542c0b1440c0c00300917001c203c2600600d003042d84000503050b09541c00032103104108031680d0a1054001070702a62150784070b98403040d80042d00d4020800e060301143e0140048004404c8039504503251740c1da9624900e0721481c1070004a0840600b4070024012070b106040c402081446407540750702089480d12107510641c82202d40c1c00c004143d0992107043c003504400c4465403041c0c1404003400d0200080d001c4419041c0c000e541e2489048800c1d00000c482d01c01090090004044690700c2c502d20030105d41742c6040040040d08140d10600c00c6944140813134080000051001c900000f0310400504002881d070710080c2d00d51f1074100920302154000c3c024000b142d917206003070115410214001d80c151801c0c0b90010b03444504c2000070310a02c0301290b000b543e507040003500c603001c0b00a41d04036112 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 532030638 1250 532029388 532029391
    0x103090f052a06030c07030c060621020109090e0a08160b0411130c0503070e040e2b0302030112120c1407090f09050601031103120307031506020109050a06020906070506 74
    0x28640c02e400004100d0b000c09640b6040c1c00c0030780b19280b0714503200d02810464020740c0801420864030f03440d0031040c8012900680c01400c3d4080c0200013580b102c00c200c0c3c5c5240c11454049001c50754035100014010302c18400e646545030b20402810700c05185560f180c40c5030b44600640b060701e0b0b0344407640d940070422030f4003500d11a40c07050b10400e41942c0040200180b180400d040c3c0d288603420f0451040006d9441003e4075000815800c01341c10380920200000e0180c21840c0754401c280c8508180b0000d1043c00c4400792030b84190103500400401500c490481c00d0744024001c41124010030080540000d4444941018000080c41e1410741c1d400d2513601c010070191012490143d55210341010302094010b03201e8940c880c010088200080f6600795100c4d510b4a40500c00030b40b51204c03144c4245102e85061207400300c99108101c882eaa00d180c8017a011b8014034106e0024107200c82e1500780072400e60f005100b80210a60844000c0c40c0f011203994443d8046c0d80251021a00300105000880000c0c40802c07809 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 532031888 1250 532030638 532030663
    0x50d0201111e03130806090706080c070209150a060206041a0a0b03061503010e0d230405060c0a030806311b0c0b0a050c07060b041b020604140304060e0103090f05 71
    0x4544d10480c0c0002c080200855411402281e08800103100038801c1c0010b90b1011900282801d1040c1d80d901801040f003400b0300c50000e5003040614042020080c40c500300d4141408007203641c0a40141c40c0d002c126a2450304580090440c502c4e04403484003a004101e0300c507405801890045074091000c1e0100703040c18801c0e902140e1075222100e0f421030384d04e07080c010350960150000080c210840e160600038828003444142191031500c05043d00034007017544049034007070040505410764541c840000c2c01e94a030200759040d8000740c0a00d000c07850b9442c0003198100511002440a0300e007a2010010864120912a0401400b9030300c0151120b016106040d1260081964643c05031025442c02c0540410000401028903030b0703d40340401410440c0c0710160f510260b040003002801c4684000420010403008408100e14086088403200f010b80c00107403144214403800e11030407220383c00c0600aa480c001d5002e07142c082071640032032951a505c0382d07204030b5116029148141c000c41d41d6490317450800685000380c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 532033138 1250 532031888 532031893
    0x4080606120a1e1b1d0916050d02040f0203131403090108070f0201061a0a020f011b0f18030f12080408090d0312050106110706020309010507170717040915050d0201111e 74
    0x517110805240001c50f4054049400380100b00c0400e1104610310000b401214424020801d0321010741d19254440c414200242c0f10855607414040807884203001504c0d01180c800c0160301201c60410b401000b0380c0c0703003a14182c55034800c90315034a401350750500c140c02d5400b046668039040081c05c0e0350382c0300642505601100d845940e43c041d44500a050021944240f03a00340e0500109540680f01900801100c0f855031911101104046808441c2c642c01c10450460121003850040240f10350814860350840c070400800c10300d00c2210405440320a0115409031007c03009200601a5090001050050b288240303000200500c0701500c00e8115002030b00302000140c40ca4501210f201001c20114000c1e02c07040c00118184064400020007900c43c42c1c600600d1079602080d403000254103c403c0d5105180c0c002000a90780200307901d40c02d40303a045031160803a500d04043d204104880101e491303a007917882c040c101107041c5000313070019a210305500b04610042e200d9203030082c01424021103040003009a1401 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 532034388 1250 532033138 532033169
    0x50304020f03031306031b020f0322120c14100806060f07080f0703030501050a0b04090c0c080c01050f060f0d021203070b04061401050103111206030f0304080606120a1e1b 75
    0x41100c40018800180b1f015544110080803041d00000103940741030408841c010a4403003004104404145258001000e0141e040304d4203041204040340c40d0705440c02c1c414041c0031b0003c42c3d000c008140941e08a07070404100e641010400030700b00b0710024040103c1c060011494840e442e99880308aa006c90408044d9581c003260000070107a042c0162401000200d03604015030b42000d500039428420351086996240d59100f000340801d014085100c1905e4003c4009900c40030f0300070740030b4044e180407240008115407030000104986406004c2401124000d088405840c5069081c0491003071404405443d40c801400000d000800e020185845a0b2141c24041074407001e584502c256141d06800103814182801c2e0600e810a581209884586c0d1407200030001c1a200c40011030b09040504184079154040010040340707000c000a8528000d42d01507071050140301c42141c405841d1603914100610705280f400800010b1100029204c550900501c0780303191142e8803030360b0548030400070f0f844134060441d420b9 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 532035638 1250 532034388 532034411
    0xe1b0a0309110d0b010e06040905100506040b0907050c10110d0504050a0c0f090f050c090925180909050307022707030c1704170708070b010e0417040501050304020f0303130603 77
    0x18071181d0881020f0700e0270300c81070032103589107500c2d90030031910b00d901a6a54070004801740e883c0c2d080f81d41542c4002d01300c654a0f092503040204564003070312130441103109d00c5550180d034083c64443c421201e00400141c600700b00441e03003c0c41c054400a00305035050711540443e100494425065500149a43e007140031b80545815850001c0c3c0740b80700d9600310954581002c010075002c198003140e48001081743e040380f040d61109000e09202601a620000a4008000c002c2c4800e8002500c0d08202c1b00020f12081120b954000c51000c1e2062210000d01d80e070018480d2500500300031014000c2e0701c200c01055a41003801903894005081c0488461000946668444000980010944070516005040001245003c0c1c45080c00542503250411180c040010401e050000f003009272440e03580d220018150725690f41460107030000f41076800351480344400e803d0600d450881000c803400c07544d068682d181941d0340c036020011003400342000340741c050104100c0404c2000f000d8000d13101800305510300044903c03104 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 532036888 1250 532035638 532035659
    0xf0d02060709030804051c0624050d2105041a0304020a120b01170115150905010206220f05060901240b041802071b0e1b0a0309110d0b01 60
    0x140852060102c070358810f0010481c588201e41c140c031419100c400070784103050060b003841c00aa03840a0711705407a103910b013881e4155040804001c04008030f21002820388901c2006800c444003a0014000c13844a91f8000c2d03007031490504500400b0282c1401030070701d43e94420304c250030200c145401000000010030041189810700f080c0000d40390b0460306140c0e90701d10b039407891044281070080d049450003070300c4000d076100800d401612500c0381541503000f1050380d5100141400d109145aa404200d1000c40451294400104140b2604003100b0003c01404440c94405200c501c80c0802e0791041502d4105401148040000c540505204000041d0050022108034400000c0780669101d0b01d030900c0c01001364601890540f0160f528224818510100305007000d0024450098001c124054034984081880c082001c090100e1380340d02080c00b001e50300c40042c144d199020b9410450600c40900a005480e0720950110300840d129500d0300c1c10720030740c0b0f4002440400d003480c01111421140c10040c010044070 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 532038138 1250 532036888 532036891
    0x3140403020f011a0f01030b03160f080d03020c0303040b0c04050a03050c0102060c041a090402040f030807050607050403171b030d0204060e150912070b0a2d1e110f0d0206 75
    0x1400301d0740e840c1400880008010f05c003c440c80c1810151180209034041c0d50900c40841403101c0030102c4407045a440d4907800e255081813081060f503000303140100c0b0794603000c0e0081322142071851001e1071442d612540c48030a0a500a00b1035030310701d00f0510010800391035030450701c806540540010807188404030002850304000170040888800180000c00c00d100d080300c0c0c0f10b00340441d01200c40b41c44150076070200c0e0003402140d03c10b02c0c15206012000050000f400000c181c3c03680154151411507989040542d01c0b1700c5603100091550040000a0f0314825280c005880140b41004d2801c02488502d10603604d5078100003011120143d00090420030b10b50000381c0741d5a002c0040c0d07075079076041c403900191441a0103000d1500707018003000c5145006404040c071020b070103048011012501c1d00c401840c024600c8034031040c00242c080c814988400d019a0441a00721009641e0b5121404580b00340c1c1820b100e83d50060200d01400b0003084c0c0d01412250900818194001c0b07007005000f5214a03407402881d0070310 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 532039388 1250 532038138 532038161
    0x30913050114150307030b13110304020a0b12070507030309151b0216090c05040b030106020a03080c0c06010b090604030203070b07121e0c0312050f180c1e0103140403020f01 76
    0x30315600750301620450710f003600d5220f0401d090009400d02039101240c2d42e0600503a240f19164504040c98074400c00080182d80035500944003144080d884014044162003848041425424030400080d0858480d40050513214464a03002c5040d500690324920700b901104041410545c58540184400c145c00d960b00c4601d281c1072000b0441402503904001160400380500384205807280d0f280e190302809842124010014644a16170b00d40c0c0d904d80c000e44079021000200d000943e107001203501400d5020a590300a4449400f500541c0d1810300341000b540d20003040c450300000709000020240e81c0602000c40100300814605903907000c10f00d0400c10b010b0181d41f0440030700c040d001440c05803a408066040e01401e10f401d190481c0c1c0341a0600784da00503080405400003908042c10043c5110014011a024500f007041c0c2d1880400c0c40000306407200150000c1a0308a8201d000548402c51010507124440c0d00c107040004102d9003141041c807100b04c0c01c44083d00541e001c4440381d13030705072800d22501c6401c15 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 532040638 1250 532039388 532039399
    0x10e0105070507030504050904050703050601080f160b12060a0810050916060206010b0f25120302090112050c0d0203042d0312020a1107121103070b1605030913050114 73
    0x3002981c4c040d0283c01140103150003044150001420458100102c2001d503070880708076441581e44003c5156201e032111000a041d0090012005c44010040e0070700c030680e82c80440d01410100445040d00c140c40d802440980d0120007407200285061061100400076200610b000c506441e0010041e403400b51440c505042c1c0500d001c404008180d408141d6505581c4405040d0355280080349c00c0310100c0c05841d0030413010490141c5241c042c1d403100c241010081d4840d010201714450b00c0d003016001c9000b07200da9540890300c501d892a041c800c0c50780c40198003802483e081824030720114440c10403600200c1d030032a24480702d544032114103c07040f0340d103840201e0b80f0740070f807400501d95942c0106900c0a0070000307102542c020a03182c0b885400360482e000c1d8038002d2401c40c0c0c00140c4c0c3c0c0907000c229034003030700c825104a645245551614100483c203901500c04a50010340380c42c0050400281001d03942c0420f550701e000a0000404640c0c6144a00040c0c181d4402d004c02d8ad941004072544180400035080ca2064 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 532041888 1250 532040638 532040647
    0x5011b171311130e0d09330c0c0608070810030314131e051906090902031e0f18061302190905010e040b01050d0203062e0305030415081302040903050912010e01050705 73
    0x202007e030101d401e9800801500030304444480c806680003501c0b000002c281498424020802541c84036485115103800ea96526880d10b803103c0d615542c005600010340007070f5003881442c4aa8100000804d00340341490441d10045686680c07010b8800e100000003054100381a004121a28000341e04942203584400c1e0a07131461316140002e060800301e031007100050b60b000710000750408019020205410107032101580c40780303020a83c111003800e048030038001d81c0740090201c4400c42d00000d01c1170b200e12140300c2c1611050303000f6020418003121411007446030140c2804042a90031542c0100390083c1074114035200d0300d04091400540301181600900c1c05250940c02e0f500142c0d070001840794001140703d006079005440340082d84000c40011071140280b82c181d40c1c0010030400004001d000b200d10300c409030112140b50250454100f04156075500040141400780c10151a040d48008849403282c00d0403443d01d082e01012420a42c0790200d44501a55140c1c00c845010b1002e000b09903000d6614505189030 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 532043138 1250 532041888 532041929
    0x90203072003090d0c051903050d05041d0603070b0c0c03010c050c06070815030111070b150310020c011d160618120f05011b171311130e0d09 62
    0x203d024101180384101c031016540301c140300170692980e0203894050141c40c250503146241040d51245440110348620540c0001c0d00580c0c070070002c1d6420b403072408003803402c0b420324000703000c0307500c4c001800b40d5505020300d1100152000700c2c40f000700948010500940104100107007050700b190103160103501802030400c40c1d100340720300100306164090b0b000d003014021602c070039544501454021b182075404d0b62070303d940803480d80d4038203015103030b9180326482140641d0b0326100403200ca2601c0032101909075004640c03141d13881c0e03082e4024001120320780c0e00000d1180307010200b51000255007840310303556801c00c40f4504000700116420300054051400c20a080010380c1805501550092061590b00030340c214100302080455142030040b650044020300011a441c0b0a52011004511002c070225003c80418105411030728a5540b140300c410000312f00c03180003034840c001410701d0002d41641c00603402402d409100d80520580403102240c0000f4035510003d904080c020302c201d500203850042c48211a42c50 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 532044388 1250 532043138 532043143
    0x5010b03010e070e03010507031a060a050313050a3003050603031902211209010513061a12070815090d0f143007020606150706060902030720 62
    0x11210036591030240b81e40c90b21000c031140b0061918241c0d041d402d00041c0104942d15400940c2a6070003450b002c01e18541d4002000b01901c00c0c01c0810002c1042840020f828a000b01400d54901b03004038156a040085c0c0d03a121000541400c104550344113020200002035039240c1e070012041d00031800c08004508280c0006996401000c212891241d03222007441c001d03610a0210803040041c40340c0c4481d441e0310819850219070841040d0141400040c800241804014040d180c05000b0020212001509d180c80b03a00140103030b0070401280000e0b80981320420340380c031905100548410000ba041c1d1a05000e951030904000c200e045620151a0f002d01c1034141c00454044800281402c0010321310091003810f44400f128000f290000301004a032401d1158940d50121250f40c4800700d08001d10340c182c4640100b1140c054404c03000590061000580d5030500040228064501002107402e110640e13032403000355034450300841805500401801102c1c0e4006d00f69521180c4c207000c6241095000011f0207a = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 532045638 1250 532044388 532044391
    0x1a010e0a0b01020c3307020436020d05100c0e0406050108011502010b0a0f09061211040b0619020a02041a180a0f021b0c01030605360906090c010305010b03 68
    0xe12603601c04c220220291300c1105da1a03050107102c12045902071101500c5141d40d00b240405a00a1781003060030b05410380c01d40c81080d2030061a490b14811048000c3c1400361650030090700301d802001d070703c4030040810000c000300441c14061000100e1003000b5500e0013814502040e524070300541c1091001c1c8906c1c5c1e000342100307041d14014240c0319109034100b00124050300b2001c82c6181c02c202503040220b0003511048520080c0e445044041c405035950300c64212051403825401b0b003006450050000f2213140c56040340d80b070321500401c100d0400e01008006140d1417228100700c0d02582c00a0317941802c41c20203008206a8100b52139940281d10f06000200b40c40c40c12414200c0c0e1941d18400c00290345550983c0102000d52241d80215100c030380c00e4544910001c50f0301d80d00400d41c410300000306002d40c46802403105989014040c404010b034117041c0d004c0f06041904020f20030542c81001c0c108001c194049941c80381452000828560401c0d004043c242002544028109800c240c0144410780c0c1c500200d9 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 532046888 1250 532045638 532045663
    0x1505070206032221051e07020301060503010204120512070503120702070e0403050a1106012403060b0f0a2706080403020a0b01060f03180c0e040f1a010e0a0b0102 71
    0x140d070740c0da00c2c00c602c40c401403640c48076101401800283c902c14414402e507071a42100d0307840002c480c03201d10140283c43e139000d109014683e000d075034075019051002104c082c100e0a031000d000826465101d600180c26600301d40c1203010221506494903041c05410880c5c0a610f060540c0380500d002401c2c2c40300743e120311444000c030031030440c800c1c046034141e44204050401030480c280c06040f1400c0c1444c0041c4294411001600010500207410300b03501008151207040f00c20000d1000c00d42c60741c00382010340140442030f13444141131750707903000240d403007a0500105001032001074081d40c1d4103014000600b03241c198241610403c18100f9030130380c07071b1113440c440c00007501c4640c1003556031075032203180491501030019002000d00890000000e509500420304d06018495500c050090080303e000e071100240e43c0d40c4001c1d1034107000400804c4420f000d4a05a90014060031030078100d002c9a03280c0c0300c1000350b4011105115007191004200440d40c0c100d002e900560550402e101581140000035500d50407120007 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 532048138 1250 532046888 532046899
    0xe01090b0a0e0901290901090e0102090a03110a0f0e0606030406060b0a08070207060c0228081c02060a0e061519060207080f0307051c091a07060615050702 68
    0x6022190741c681820500a0141c4030b0360410324902410316034044c0030b880c0382c1c010740345100e00c074218000e08900342c4070046070070003500384060380e0b103001950406002e154143c041c40d0356082050000c40e0302c2e4042910091130040c101b000741000c04100307106884400380e00c900751540800005001110f580f040700e80c3c111004450700c607120348850904a0050000c0d40c8510301c0044000307140201e25400142c2940708003043e800f500ca40c1581c032403080c2e4010349003110095001c03016807003030181c2e81c80d02c80c800c5250104106c51801c1c002d45411205280c2504130130711010240308010070980240c0d040203510341c0085540b100744108540e00c000c2658440d0b001e0208111a80940021f4840e501c5800001d5045403d56030000c81581c0e0320027000e07449088a024100d840d004071181480d00300c10010440d81950303030201c0200f440865a200c1ca0920b020301c00722120412043d1100010f803000c860116603e0382d160764010343d0b540c89007403174100c0803070f58154844030000e020048821030580d00f00c41610140b5406484 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 532049388 1250 532048138 532048151
    0xe06040602071716061109010f1d10050403063602130629070308041212020f09040c0309120e01170a0209030613020a0303110a0c0e060f01090e0109 65
    0x20f044a20300c140050110000c0c002052100c5030200f401c041c1000e2500500c010410182c0c0304003180e000d07200301030303042d404a44c0d132481c0411303d144140c200b0405e64444564496640500c0000661415643d40c0d803040040c40206040c030a21210f4440c00507040701075585070000c04518080c10f000041e0030780240045d0f40b14020444259241c5050040c02400703a1403040050a4035500c000c0101ca200aa5800c07000750341c2c0b08417003028946070f0201c1d03101769016100c0403119561036980c80c251a2003000044100004a10117002c03580d160300203442c0440301d03d401252030b02042014042200e01016a0000f0981050700c0d6001050100c1c2450f4400e65191400c00ca00c000307100c0c01602c03070701d461180c00c400d000300031030070410308011950103081e4029080341503c015890b0002c08426400d042e07400658001621081040003e002c0c24003e0498180442a83c1220388151509080301510341d01c654a403041c079008104061900808400d10b0350004d091980d220b504150040c10b1000d01406504409942c800 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 532050638 1250 532049388 532049393
    0xf1a060f010305070e0a0602031b06010b090402031902030408090111030306010c030e0a08030c0f010612080409050601110307030206010302010f02150609040501020913020a031a0904030e0105090a03030801030b0108010e0604060207 101
    0x94901c83d00000500401b0300395907505c0c0300030340c1c03075000c1c400c0324400c0481b091b00d452200d580410748074104c03030f80c1741e1086080051003010407009500c0078144c400040182e00900084400303500281d03100700e000310815902e40418030009402a002e0203c031442c6900104204130135a0380010020003055010318011441150800114800340c003160041c410a100100d4200c0c2c0340039000900c0d00740d07860b201d00284142a61038044113110207803a40b0092030074100b0b0000317001c0b05069074481603114005241820802109001031425540b20180c241c1c0180c101500600641d40c000c0001710650909100815214031350056034003090101518041c0704045c003401050500c40250140e40e0070200013032010020000420702c0800a500021103136021901b0400106a0a80c0840e0002c000c0c2901070004403c0d9138890f6022a01800200d503014140601440892070a031941ca00f440c019601c01c2d00d409050f541035007010b01901c2c01c140c2c403100c1943e042407074135048c9130b00204519801540c4110007580742c288a1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 532051888 1250 532050638 532050647
    0x209031917040e0a0c0905061c02040b030a0207030e1917070b130e10060f0e0409080a090810020316120f050a0504020f030c030c130f02070f1a060f01030507 69
    0x45050801e40a004100807800b160000c200902624030040d081006a661510035030b0180c059214841e0704c00d50030710440c00c046581d4800c1080503100e50b800180341c25207900c1c21698641064483c150019404143c0d1020190002c059545200013140c60f03041041e5013060022a1030700e00d0003000e1840c4030804104d1a0080c0401c00d030405040e048501c0ca4545114074121002da58161140b5109030341c0036000705e05158050880740003076070010f540c0d92120182100098840010024519410a50319081d402c0410454030141c03480303404655500074280d141030700451801c880001080b4610b81304009100300441d80d4030303000c0004803503410900184072034068090b00804240c0349540b5402c2c105010080e4803a9070342c0c03000340f055208403882010b0254039402d2595515401c159540c15900100614076140340c81c1c80d0030b10318110307005000b2a41c90043c07880301c02aa00702c0d00e81141d0300100041c5071402c0104540100004104010340c2c0002407800c00006200e01500e9848103050681c0c83d404500c44603c01e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 532053138 1250 532051888 532051913
    0xa141306140a09051c0c11120106030305030601021204051804140f1e030c06010e060d02150307090b07030504030204090618120f092607051309120302090319 69
    0x2460441c0031030300c1d040218001030825080125018001d0701e030494240307285081d00b50302040c0650750303502c1c0720760340d50b40c9100c144070340491701c20380c0507207040c00b42c4211070400d01501c80030f184650b8134a501c9041400000e41b800012004000c514034082c0014020754072aa003400124000481ca88140d6803260b08001b400418129820b9000340204402c02e01c0f81c200020310700c0c0019003070210040c00d0002d84038800303840340100342d007840c1540c00c040010040001e184000c207811483c0101000c80b401c400d0340c006030014807403844101c60058080100302030385070060001c6006004200c1c0306071802c01169001131103440391f03000091280b9602d06400082c0079496000c40100c1c140c03000e4490f15030b51079040058034030190510400028441e031419411042c482c4c140c000407582a5400380b4035280c0603c05018007844000b400c0041031240c0900022a5500ca40e6580e00b03051180c800050750407401d0601e6420700202d04103c2013414010041c40001d5100010520080d031441c1e090340808180d5850601540f121 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 532054388 1250 532053138 532053161
    0x2160f080403030e0103020307050a0f0905100e0a050a030339050303061005130512030f0a080a140609010509040c092d06030b0c03040503040e0a09030201050a141306 73
    0xaa0190202004000001072054074000c0e1070304d2400318104030045040c3d20013140c0c200d00040301402945505801400303072221485540c05d10b045180d03180c0010a108020201401c40003820b0010140c1003420311441c840054002680c41902440c25918040c00504889540c5038001c041d4400e102140d03601200c1500c008049072561442c4a9080d0a243ea600d41003550000e00c00c4080c110340c925103a0082c0121900618402c0f8449111403402c0c0c208500359224080100c007502040080c0c6e14080310340320081c80c082c0c589440300407480c1800c00858044580907144100c6102290080c000140d41d041c44550441d4030488640c0d09a03a0707149044e610b98522544a1100e150070304134942142d4a9200890300a8040441700b03461201c10f030f05075041650090720001d810030314030401040140d04410004c5901501541c21a85010ba4807021b11850303140849080c48141d5841416108141d428001c2540150b40100c0501200d680e1086020a01c0405009007600d074100c80812001c011480d080302160030b0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 532055638 1250 532054388 532054403
    0x170a081315031b08090d0e0d0c06031407030e10240e071701030b0f0403020f0703081905030907060e040e01020429070308071b0b04030f0807020f0a060216 68
    0xc000401c05005000d24a01d0b080800c482c140310300c81801d103d408035030700c5140c00400402440c0a0200c06507200d9902c41417183d00010301c0040040811034003001c0b40e00404450b82c0009203000d02e481c1d5002e075205e001d403030b110030113007041d1741301400c00d07400120b05075240105000002d4005038506205402000f00864450744d12000800080350003414007010f204850a41312038a141d00441c031b5281e48030f1000d020041c2a80c2a56020900d00708100d80d181c1e40c094031a0045542c00040c2070611880d0424652085a03000c4001607209807418076000d180b025803481342881821418200e060540300c41841c0103000400c1540114102d06035166000101c6890940c2d00865840707840c2c03417800c101004100d510416070204101010501128002192061500355640d00b0040c0c503000e01c1220903504141c00c00100000c044013210100d136400514a009503c01c1d260323241c1c040041c0c0e002412000008241e407080d0342050714035100c0030b00d0104402208543c047c8005945140c03400c43d00c4206001d042c0c001e03280c107 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 532056888 1250 532055638 532055669
    0xd1805040b210d0305010b0c030706020f04051c060c05070203060f0601020102040f09050406060b0a050717120112020102070e060d26030103050d1407240f0e0d0306170a0813 76
    0x1042c041581d003080000c664040c80142e0f2200d541e24002c0c42050040e0701944c1c41088560007152203903000d8a500160a54000c0c40c140e0780d1381c001040380001100801104986e092980100030061180000721269410b01030304041c441e0300000d0b220784c030040082c00341134900740000f94660300c00c2d81102c0251032002c40754084183c80320010740090a04070f030121070361441c050000c10190384100998400c0349003681d0315031134420141c0c1e4100e0305000701c13407001e01d49420038004400719840c02c02c03885010f030011080049100c0780364000280b80101c268040d11001c00c0d0031080c040c0d0b540f142d54082500e10f82000c81420103c18001d4544495600e00e02d04541a11003c0000f00070010041205120314000341d40314900c681244401e02038611507498002c0ca0717005040b00d0005480700860b0602d9000c582484009040a0442c3c4da50301070f031b1542102002c6540081062a0b509c82c0c00d03100340000f42c074200e00040e500400d11403134280d880c00140005840000d0200e4a0000702e020040010068516030150781030701c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 532058138 1250 532056888 532056949
    0x50127090203010c0c020906092505070b010b090f1e0d0503090a03081c05070806130207020d06060f0e0105130e070b130611030c071a0405040e030304050d1805040b 72
    0x520010700e41c100e1180d07030b111020506524001000c0c0c1e016a0802042b1000c402040001042d0744440807440414860284001004203504012480c0201302c5084202c0d40c0e44509400c000000c5c2c850042c140c400e0054859108c2040090311310715a5003a400d81d561000325449080c0b4070f203140211040e242d4802003811002c0700700401d0304094903003038141c1d1300341c1440c03058000420360640398102d074800c0000d0424400203142d0b00e007880c070000544028003030051074800203401050103541d240f0403c0d01c96503154a802c000e1800c6046424000300300e285480309942d41068000780074088109c01009603903071903041001c43c0000c20701904000f482100740136603a8010b00b001081d2542e1251060390302140e03e1300d41121240e070000c01100d07580351501026100a41c02c040400466515840d400c4442200c1800082120b4035079200710040e003c21b480041da01c03887e20340b410a1070042c143d40d0100800c030454000801d5043c540407403805466089501080600080c0d000c1850300090f034140804841d201000c0303604c0c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 532059388 1250 532058138 532058147
    0x10c06020f040e090601080c060f04180614010311070b0406230901061202130f06170c03100c080103080306032d0d050310030602030a1b08070f03050127090203010c 72
    0xc940c404002e002c400e59032240d0b1325841c3c030400d1140300d034640c020030700f10101c030703e40304009040485e43e108601c2c1c2840d0300d49032000000c1c0741880382c201106036903a8060000c200f501440c408806401d1a051140c201d510403426202e004100e00240001041c401240c00c004041e001080d00400003204807a56110400100c3c42c818805d5138401d105510300b1401003254035480c045000789a401600a0340c450b0a10200c400c0106407a07150080019660080410000e01d04100d00307100d90b0b86500200b558202d200308140c18804600040349005180001c074461554110b40c5050440c2d8020074503d840f82c2d1982d01003418490004805108100d504040f81a051040b205c0d05109601080031500a0050108140c0d031178072094071070900311030408500304001070140d001540d01595100012a0220b04182c1141c0d0b1448001d0301400406c0440b0104102d20360300c041000700300c00d010714050042e545032070b2004c40400340c89800515510008504120000010f8005140e074a501800070410b8880c07a080081 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 532060638 1250 532059388 532059397
    0x4020904021909050a03020a12030903020a120b0a15060c060e15091b06030a091b0f150203090f010804030509180105040e0a0c261506121c0509010c06020f 68
    0x1e000c03c50708040850344d810300344020303402c1e2030b030140c480101ca905101005850100100c1b044040080e250008001a160003695200030514131040f0000b40c40d6924018600c00c400400b8003810500c0c02c3c1d000795442d45100305c3c2c0d4044031040d09085541c410f4500749071020700703080280700d0913038402c00d1640c0740c540207502c00c1188660040415030307012640c0c600c030703083d15400030401c1940d1010f414800709191145961003401828440d00350061444c45048802071000102d52055801200703106082014403200c00100c6041d0a1500c003070740ca4600d00300300161001c5441d038139003070403c50320300005010540100122078043ca4001c09080c10f0780d0484807056442c9070709004450080d42401c03031001c3c1c0f02000180380790800380e0041d1714103034072818500580c00751001d15918042d40050103001c1d5078040c1d01441075090403250302d80301e40020f15018090190040d4400d900451951102501283c1c441902c28017000d609440d18000750381d01d440c6001240c2c020740d0300802600342032000030010035020158000f003 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 532061888 1250 532060638 532060687
    0x15140910210512091c20040b0a0803030604050601023d02071401110403150513120c030e060702030604061d0102040b030a0c1821080a02010507140a0219020402090402 73
    0x7694003005858a1804000810310006c0c0740250920300d003c2036401c0c00c0c0014141550191000031170010a00c0042e00841c0c45502000451300300005201190030a8094154070140a00080c40140d841400c060b1503a03200e0302d0041501d808128080b154903258070608620308031041c5c01075403228020b08084003440c200c00c3c45051a5860b056044c0010500c02c1c8c1640d003203c0d00020203003c08000589001c0150000800342c0c442042e10690000011b08001340000042c10180d1300c500d4a240d0b00e2030040d00035518002418030030754060103810010f96002801c95402a481040401c4031255008141002070010b0200d5003254000f0501140c010100070103540b103544001414081c507035250324261641d99605d2840c00c400208280305008011041289142110b1640c104100c5d40c0a26182e141c000c2d0420301c1d0000040c2d46907020700401d0340e84402c400c03e140c07448003203d40c60110302d03001c0030b507a0f400000c40342c52035034004c1b05140055503900d6041da900204040d105640d00c001e450303907000314a51218900e = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 532063138 1250 532061888 532061899
    0x15091c1103011b0c021207050a0b03010305010524040b0f2112070503040b031005060f0403031e050a0e01020a120302090109170703020906131514091021051209 70
    0x1080741003441d00e142241040550341350310800b14510b40038080c0321141441e480312148030307c060001e100e07112000c0038401800d00301c0d2480e86950451611909649010f8035180800c40b0030205a0546d40c60100741c1c84070a44211000919500302d200440c1e00c0150070300c40d095000580b12000890f041b000d058400802d4000b42c142c175466200101085124011010080d1282d0300c03e007c02d101030151000216082028001c02c900265a900d002642039409114038000d00c801c04502002055040302c01c00c400b502204c4404100078401c90002429401888108410011451504400c0e80d00902501d100d0f20307084a0606c2d41003011002c090080d601100b492800240c10f030388000b80d18000003a01d40342c00d410f088041c06d00c0030303c0c0d0340811110a1b00500070581c080b41c200740340300592415118000074030640c100c440702190b20b00200708420040d9445c01d180903900103000c001116441b0701066080d14215603080b40c0e640c412050415414000c10002800b500c20941e02c400318500c2e10025000381882201ca = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 532064388 1250 532063138 532063151
    0x3060503010513140312040302010902100507111c020916020609150a050a291e030c0402160c030308040b0a0603080d050403030b10030b0a050f15091c110301 69
    0x1403508803541203581d0b901d0b0001c80b1006800140d0310101280107800910200d0b03040003040a5220100641030381e085015170344d074080c81d604504101c1c482c01c010a0302c2d401d00c0c908104041e1200162007500c80c501c07d125400c458110720342c20411141024640350050084d05240c0f4080501d09145000140c581c005803154200052840c02c0004000025100d0f50800c03404546851545901402002d005000002c0d25190700c80c1c0d002ca910070344103800b2403e4214405034244620700b800b100800459101d5030a050b0081c1d1140980c4002880b52210b04040d00c1c016905c0d030a46464840c900c0c007120009000400c4402d00000341984500901e010b10b00860381c00455440d41c80d00309040301c44522000b08034001c241f100705900e403807a62009500c280a0f00300031410440305e100040e03230140c05c81d00c5030303010a076125240030941c01c224030b0b81000340c0b00503904d02142c2c0d02d1010028480003500400080044000a100b079002d8603001e581c0d03004003a0540d020f00c000803030b80c60000820801c0b8200d45000350710b0b250 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 532065638 1250 532064388 532064399
    0xb150a03060906050a0321170403031b02070f030305180a0e0420010806040c170c0d0e010209060f03130b070503090f010b100c0311030d050103020a06020c0109050418050106080d0306 80
    0x4400100702c1e98411440030741000d400c500080700c048200f45030801c0c441c48c610103044c64641204000c0c40f4920030748e000035845c0b8000c81100c003800f40310b40f24078046500803101444034800c031043c0c02c0152500b60600f00d450380c40780a4402444103e407450a904003007140700001d2030342021a40b0501892040d00500c0c207100405811440440091706064009180c190101c1c0440c01c207944813002c218030614101400420b040900c511010081d200891080d900088140d0420420302c40c081400005e100207502d00302820340098041d01484807600c004040000c0407403d118100040015103550003d501000b5103400c96000c0c042d90000ca51498507400f6003000c001c0070b00700600c29040310361401002601d44042405003144c982c02a0f50080301804450084144001c004001410a49240300c0c0301280544c1140f0500c500c840459104ca0103560241c60000c00580c0c00c0410013064840a8030b000030000c5036001103112401945601034590f52a1590204520202043d071a80910158406200f503c2d9640b = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 532066888 1250 532065638 532065649
    0xa0603140f1315090203010c02070611070b0307181d01090c17010e06221a0a0e0c071104020a02060703110705060606361908030d0b150a0306090605 65
    0xc440301c5640e4442d000302080022640105115210074a0310700103100d24403640400d003140d80500f0204090b900c0810101f03d1303580d1021092040c400310780050102030b0b10b068006042d50001410ba0418000185040368204511030760050060501285440b881a094240703450301720000e020310192103003010b201d080e606001d0300300c42420f085054200c050030307031134900044021080645655444990040589071248030144410001d0004400000d48100610800048615640d40c1c41d805116081c0003002140c241500360756100c000940d9140e69410745240105180115645469206201003111141300380e0005905100e030100d91400c0140d40030b001c1c00303543c41e4002d4000040003a07001000042c1c4500b03007030002d0242c500b10f0480b020031344d905a02d851500271f0700000340a040d1702c2030104214a50f15081ca040170f260805ca0400d00c21090401040344e40300e01c100507840c0b42c0326032280d01c0b41c01c060300c5641540300458000d0084584500001000030054a540d00c26844100d0500c0740216061402 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 532068138 1250 532066888 532066891
    0xd02180f040b1005010e0f031f0e01060e060d060e03090402270103110a18030503161a0f01030b100f090b04060515030415060f030b040b16020c1e0a0603140f 69
    0x51b10f074510070040c41c008100421a4160001d074150140c00e0320500030401c07101d4092203151a107040071501c1400c20080901f1a8910362010071030308001d50500c68103442c2c5460390300e030b5960000c101103200034602c080546540319091046810610000c0c003030190b0103c08141c0b0002c0114001c802d0811140800110186c90b40480c811000010801c19034004900071080035100c42c081045a00100b503503030f01c0340350540d0046188000041100104801040100f44d000410722000000c85403460078496140d8811000c1400002d000c0707091200400c00c50042d0181c50002080c03a9280300036165110540c040180c400701c40303118021070500c80e01081307078a004101c181007601101d05850441d95161141c0c88540034000d19044030ba41ea4640104407a9112b00410003e14014080501242041e2604c000030002c0148403904000e10058074401480d4041251141c40104403210511400c06401906894500c20055648004141400505282c140d00b02c0e0100c0d40404c1c00201c03c45d40d40940c0c1d0510181d0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 532069388 1250 532068138 532068149
    0x606090403050315130603030e131401060509030c0d0c0501020d0c1e02120102070f03091211090604020903060412090b040602250e0411030118030503060d02180f040b10 74
    0x40074400113228482c2c00b54000c00d803440003403030070b550522000b0388081103072800e40094002030076510b60316059040200302c50041c42035032401000700840b054180301c00b001060207003030200940010041ca260b0b84c1006074942e161401810459041e81c645030181440b100c1d841124050b0060b5545072103281c0c01303040c03142d0115070081e080e0300c01044610442d038401c01e1080d60403a4800c1c4600f11507840d0f02424400307000190703c20900e02c3c058000b203081c0900f1402541c0d2140c1c3c2c20184820200000501000c007442400c2c2094400e0712154135a180050064041d045403960944200c004020074007e8880d420070103904103840310034101e500e501b000003072882a8001c1001582c869a00036114000a04034000604518180361000700c2d107410b0300c014031610540e0309850404111000e480903160178425a945023025840d15840003d4903900070f01280001040c4501c03403080207a1100c10f5484072881d10810b00c0004204204602c0d181c00381c03185191090b1010340d1100d42d040b000514a485001c4248182d07034 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 532070638 1250 532069388 532069397
    0x10f021f050907080a0302031e0c1c0e030a0c090b090615130b0a0203130509010f12050a050d0c15060b0405040e07090c0f08101d07020f10020a020606090403 69
    0x4500c1003032000507240c003030300c00764451298000c0050040000d000d24800e0705c2c82903008d565074440c0d80f000404a0781c00551000f00b0444208514400c6a4001410b583c812408101d406052200100240e95a012407240e69406029200006003084901c6401d0300659a0000c810005580400b061281c134801c1101d0941c0c03c000e00c04000201d00a58030054109070b00d104c2140b0304065211000e040307032500302d8104030000d82d06c0814400c48001000d4041000b03440269541e00e225854822592408040c5118000c001103007400c9032001c3c40300034044424100e401c441210690000e50000511000b941e203001e80b10800c000300c060305114014002ea400326052034210500300750401040100500142500007418402c2403400117164006003c3c1c141420807030b03119880707900240d040141c10900c000b404000244540708043c4806021344481e64001060300d0441c2040c0d958070401a80360000a040c0c0000c00c1c42040d16112240781d03503400070079080350542d0a581c43c50f04c0b11000d0200080b42918001d0204 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 532071888 1250 532070638 532070683
    0x1b0206070201120f1503030e12030307050d0908030f10381e0a090603110a0507020a0306050c090a05180c0306011404080105161404030b100e1302010f02 67
    0x158410b040d80c8540f0300000b28005410440389000384200d41d050b860104c4120207580c070820515412568205c2483d00a642c1c288034200f0441201d6100d120041040382488004034102050559680c40120121341c0000d165076a03007000401c102c80030004a0b00c1c00c00c5520881d402007004180110260228038040344500b100c1e400980c11012158400072090403694021311004110b07a03029041c4541c21080c81c0c2109a441c0c405040043c0394000e00d4005209160404055000030307254281145c020b01080d141003030b11000c40d4800a984803200d540050f0050341048e042c0070b420064080104500981103d004d0004c0381d851051061170043d80b903510140d03080e00c900080c1c102c50180300840d1b2010051401e0422440160700102c3c064000b6000f01019039501c400304245807404550100c1c0300e00003420a80990381013400d10240c941306034080103029002c0180480d030000d00229100f0058190142442c00c80c0c0741440c03100b0980b061b07002050b40000c2042002c001c8441c0007240013001080c850b03a608082 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 532073138 1250 532071888 532071893
    0x40201030c050d051005120a03080f061225090c0c030e22020903010e0a0209131a04030329060f0315040507110706140406030f0e0313061b020607 64
    0x1c244516041050040070007041800a9842c8102440380c0034041ea54202d80382840180f00001c14904042c20303882c1d2212980402003a0850a2264081e402d044031b05403e641b44004036040303022183c05920700780b00f50300102e61030342c02c0c00c040e040e4040194514041915601d100040656950346210804940d801661102192240884003030100300648024079802030b03c86161803002c4805002303c0141e41c003080c0341040345000e01030358415403603003001080c410030343c1c0d00003900c040000ba1580019840109d41c0b00c08001e50b452241d044000c1c1102190001d14007400c002d006042015280040400d41c7c2901d803908036120b04596450040240030203003440046540c441c146e40c009031070014503c1c0c40f40812401990741e4095584111440c1c2d940003402e00c44140c3e81307440c180d400e400400c1801602504c0403c604402c0c0c0c00d450072071b80d01d450b003c1007540341c0a84010041203515451001d41c0000101a0302e12642d9400340c404481c0305540b40c850440114007822403210080304000d6004030100f1004c0302 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 532074388 1250 532073138 532073141
    0x70e160905010f0309082a010c14030702072310092612041e09020703050d022b1b0903050c0405061c2d0b0a05130206030108010621080304020103 64
    0xa0840e0f40c140040d042219803600111a00200008184026410842549480b0301c41b002842986500001d00010100c01c10181c00b10403680c5108500090110001c2c140300e01c200840307001400c041201d1001443c21102410861440322680360046103240c00303041c200c0c1c1c818501c1c45c081f00c1252400008001c03541020782e20500082505079160f100e196103000b008042000104001e103403002c0c142040c0d024210020403010950390200f01e1452040c0310120100c0e8010f13040750302c52440c003c0700698803801210304d030a1184079688000800c04200b0505070031402280d120f0480d00442c04810201141d019108030380801140c00000c145800884e002580741c1802d402441d00030400600c00d403254100c1c0c03210710343c0c80441004240c0e680104d501030101c24410480950051190301200b0200c2c0c400c1c0c0d9110100180c001038400d011090340e03400000c8441040d00c0b21070b41c40580c02400d2a9495a641e01403502801241c021030101e1b1008500c0c10410304d1600b1050501c003a44a90704509664030743c0c00540 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 532075638 1250 532074388 532074407
    0x10020607050d02070b010e010918080a0311070b090d0e220e07170706030f06120f03090b07030908070b07170a050706090f0501110913050c1902070e16090501 69
    0x40180b6000d010390f600003a405c02889001e442c640e0290209507141c11382c180c1c1a103401aa01c0ca00301c003140e01c250303000b02d403078002102c080100c141404500b116209004201900c030300103014111300284414002d0071000410810054006076540c4d024001c41c1d0350070802c14909240c00320b182c0c40c039001000106010313590028642064508150f5000c1540c6405031015080f00000c0d4080b09e030001c10003804600d8240c41600c1692110101c00c1100c50f0030f210f000007449800b054040c1251001500c0b002c07c0511444007500a804400d103901d495003080d2801078050921030144c4e140c203010390030000c50700c00c803002c059846281e000f0240c440701c092030304411034940d03000c0e1001408114040103044040340c1180150500a446040074007184a407504004d421a410320019500307600c410001500280e8505483d83c6400c0c0c851800090309403140702c2011005e214a4800d03004075400d8001e4610540c5c8c004c204c287c01c0301e03407060001c001d654070a00001c10b503a002454980115400110a000c903521031400c50 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 532076888 1250 532075638 532075657
    0x70f02060405040903170108030406081810020f090a1d0c0307090e012d030213020903010216050606010801121a091f0c11011103060d02060f0304060603020f1002060705 74
    0x114a42510b03038012400780e901e00b8400343c010503903920410714981d000701046401030204030051410035040031001440d5020145ca0361403207030888031210202c40030a0221a5041845410445d524107082e0303d071080c950001940113108001d80f41e000150400700c00715039850410b0912102c0d80998401809940541014000030100b01d848800480c0110307512110314042c00702500d0360602d84190b004045545241e2981c40000110030f072a0070001600c505103104007199a81c9001750b200c00d0280c000c42e00a0203005c0c1e0340462920703c1c0140780140b050100701c1c180120340c01e0341e0314000d03683c81d4111654100c070340d29001840e2000031000c184054484802454018804005903207400000c00040115509100010394a650340c2e00e402d400d28941000a00d090380420300020301041c000d0600c81c95880c04003d05640c0100c0d2594024011543c0d2801160000341e0000e601c90b80303071f091909141d00200a81c1c0012030142000f403488103224903160303442d0b80500034964010b041079030b00c0050840b015000302d1280f = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 532078138 1250 532076888 532076899
    0xc1203090703051005040c050d050c0120011803080106020610030b0c0f0c060a060f030c15021f02030603060105040b0616110a030627031b0206040f0605030604050f0705070f02 77
    0x8800950140311300038403000d4514001c02d03141000e0815031034290050344898030454400301c2030700010b4008030300c00b074540d8002d0821b0f100d1080d60f042c058000150340c036408400c4c0d5281c4141c43c040007001d10b030201011170081da6868410703070301c030f11041c0d907585001d4400310220320101404200080384001650341c8410000c18050401000b43c2030314507650000078052400e80c1160f41041043c0c000e500c10703500140030f89104120b0b03641c03458a4070010b1590368000c3e05e040c45008441c0c4003013030707000700100c09000201b0042c9200c17540c120250740000b5082510030a20a0040c04000100d600e050f01540710540b400506003854003848031280b055012484404840405800c03185150350394800202c80000e502400380456001010061400001851411500c00b204040c04210110390f12817200c007001c030b8009040e41e444412900004403507008a074007036094440d51140105685602a01441c00b0358401c0e10148003d80396021112103189041b00c0c0900010028003034400413030a1100c040c24103a00203000c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 532079388 1250 532078138 532078153
    0x1090c03060f0e090f1b04150b03160833030111030a09020a0519060f17070917070305061306060801150608090a0c06080403170108010e0c060c120309 66
    0x140c0702d0b4a4410307603120076000d074503d00401012140c180070820307880c80c1c980301a080310354281e40c500c003075420007080040c06243da642d05600c20140e503000380001342403043d80b40ba131a4900003003114000d813514940716001442560108400e00c2c82150240d07540245452420b40c2d0200300c8009468510020900035415901c0d03015a41519422200850040d007101c0070118542d50640140903441481e036100e1401080000c0c2e807258103d254070b0b508019135160389406806180c00d1102181e10050000c0040b05500b00f94040c0141641c020411004076058012115002c01952007442d84441d001d00c0041e209412810000e12106140300c0f00075400c42c030440d0001030b855203915040382150700358070a000910054417400e1054941060000340d000500400510a504482c0d603401d031240b4003480f80c542404004408901058003a4a85a49100d07011601c280a983d6503400d003406842c045608481c20b0050070440403540c14100c003180c0032255081c0081c01c03101c488488080c4140d1004040510901501c1e4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 532080638 1250 532079388 532079399
    0x1b0603071b06020c0f07050f09130b0702010912050a0c030f030e030c01090203070f0803090d080c0a110f0402040b12040512040303050a03050a020c0a0210111e010c05030f01090c0306 80
    0x10101e14500c0c0903020041e00c4110304030010f850302a5003400d061700c0d94890341081289540d840c00442e807148c01a1069101034480128549901d050500014840301c500f00802c032600750f0550040300701e5401200b00d1020a0703d042002c0d1214440c0f041c1842c0010400602c0d1400b19000d14504c4620b036a151800140000c08102c1203425074200304141a906d94441d0788900542c80c0c10803a4001030800b450b6034811951502c0c51081e5203210b42c52516004407209503199040c00789140a0310a000c44c1001a100c1c010403a2401450681e075041c00c40b4812103500314038100d170341000d20948045d0340301c2d4a0b1291030060a910310f6034507040020310031100d500c2000213913183c08001078090801140302e5210113850b1000c1380c03c0542602d000501c45a0381e507105114150542200150700c1e40401d4060383e10305004655464103c0e03410322162054000741c0700b160101420580c0546051120680301002000b2010610004849601c010b171002414024140010301c400b003415440f50351000b01c1c9007000a8034135070f0b8a = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 532081888 1250 532080638 532080677
    0x6041103071e090c031e09061d0610061e110a05010903050d0b01030209100302090f030f071e030506010315201b010507120b2419021b060307 62
    0xc02512160504040100031440d03140c01002c10304c02c22420b0a0140241c8000d400308020440542800c6003900c5088000c180840c1d0b5100d40e100d41c401800c41c50a4001120020f42c1d40c80040c0c440c401f40d4030301707803100086032071295624141103074040d510031010070115032003151100581c0001007000d0052000410004209124400b58184291500e130f49511486031400111010b408080d41410300400070100c0a65402c0e4949040400364100145c4640d204e101003140604040783c403d80600c01e0b8504824800e074005080b41c120340000050154030380440e80005000949840001c3c242c0e8000710040c000900d210401d502c003206008000240c8014400804180d5100c0d500c0090343d8080c0025800c80340a00040581c0d4040000c00c001d0013079003014032000341800000000c0300003260740c8030b2a064075030340c40800344c2480d1815028803a81c59850010ba24a942d40000402500044240b1482d40704c10f002241a0001100401e90301220315441010b00c012580000c2c42401003042c103145211500d02030 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 532083138 1250 532081888 532081919
    0x11e080c0d06052806050309060c160c0902040f0501050c070b0f19081501050a0e010f0201020f0c03032e05060d0e0f0a03090918020d0303090b0406051b0c0604110307 73
    0x2440c00144c0707809040100c55444419040f40c410814104100030200d0000555603810a280c0d208642d92000700028a0141c1030300c1080c000c00c0d550400c800011290381903000361003665203c0794034041d601d645000641c6e0b00d2180351621441a04401070412044400c10090300301d4030900900507241400d21194410f0301241d00143e200421003000502c0021000d0180f004034190003800e085140240d8060081d0101c0720711000103041225110400144902c00c1d01030b64980f04071481e10540b1a05500304035500c1c0e400803500100b007096000f80807170801b002942e40340051032058a0101d10300e0300b860248030080d03100d0401c0ca445a0303110f80b8416590102008070001094081002d05088041c43c40d000f032038142c10703034003c801c22411320440c1400b4030381d51100c5803121907044400c40c0e1040e040d4501503000e09010310001e046001e6605c100b005102e40c2c0d4003c01d2095141c001c82f490700313a40003035941009001384404d1260030307840341d00080c0000300102d40c0d480501d140207003120b689035903504401006449 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 532084388 1250 532083138 532083169
    0xe101701020a02070501051204060902010509030d030218040b1309110d030c0203100c0e091e100303180e0f04060608030f07050606090603030f0d0e010204090b011e080c0d0605 77
    0x500081008a0b0b5a050050402900b024078010b45450000c1080d03000a0b8800b600180407595900300150131603001d502181c2e20b041d0080d060310811504104090000c0d000562026000e040c01010340403d880c10703100308031103041d004000c0203d00b440c40314264014400f65000b12141512007855040d0b0303a4848080070000c5101c2e6480030f503203c2180c810f1505190070044000d84807420302a0001503203402c136000700c01c40c8502741d800c2801d55031240225400a005c45040c40228107164023413040c54155404d500c401c5e2400f9844009021041000d803129440c0075101c0c3c251004458000300c0c02040d2a402c0941d0401d000301d00c0031900c00c0c1c641050a007140c1c4010341100068000065843c01c0140c180314650f8420710448101016151540100c2c1c0c9074803490b1503620300720344002484001100c13694000e540322084c000085444548888020000b89501c0c4140381c041041715911204101437071400302c00c020010703034480e80203803117083e1042c50503000341101c0300005840340c80210b441d40321044401070156 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 532085638 1250 532084388 532084391
    0x2304110903010c170109090201030f0906060f06020715030b010c0203060a050726070f02031e0409110c0c010f0e03011a09100e0c031e0a090308060406030c0e101701 72
    0x220800c01c15003119605080c02c001e020420010f1150440b0040b01d480c1142c0700d040d00800e5050303503480100c009011401001c8040e0b80f514a6120074000c0d558002000c0d14948924000c480d602c41800b40c0e038072082441141000034000e0761100c061880f903044801c0c0c2c0c28040c1070801d407142c4a603001a05000d81152480191655030f42040402030f0b05c01802e050708961505007820038030383c10a25105030798000f0841403d204281a4040e4014420400c40320001400b18402e80c8c6800c4141201c50560307c507101700d01c1c8103818100c1020040d642c040403500c0c2000c0c84401030000b003400c640150f0b446220481d0703610910951a52030b1105407400c0c01640e007408462042880c110641d43c04101900d0009080344a010302c00031001d0000f0701040d01455049000114010b482c0c0d51000c0302c2c4288120822107801c5400014000c0c841841c0a58100281c207521030b803900000e071b688610a10044405912000e0001205420200300071f04c400d92000750040103503410060b0741a2030741c101c11014070150001d40c030a603 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 532086888 1250 532085638 532085647
    0x21e1210061203021203100b0d0e0d030203060d0b0406020d020c1c020a030813060f060b1902010b06070807150e1612020d020f03071e030b06030a050601230411 70
    0x9010074422030002d0090711090400580140d01d00a50711440c00000a40c54003000010848000300049100c004000d049000707a0b030780312400b007c0c1c4003610b10652144403e204450031000405d009000707685c4105805007803003003a80ca058542d141020005801074032019400c0010707805002150004040d01580c100c01001a1140904403030040c8851446080071900884260800203500003c0d0f44d40010801000c9400c420003802c1c203030014184440000c680318a050381c0000c203c0e0024010b4500c0310f141c50491104894000c000780c0c00c0c2c40222841981c0154200154000161010080c12608d030191847c02000002c068110045812221920380e02d54010322414134012b6103980510003030f0413074400c00035680010340d000c45c0d107100b40140000d02c18103600081d00d0485d02d0412441c1c0c0103040c1340d56100c20102402e948224800d038a030000b035842d1501c40000907954100020400103459100000384684c1c0e2a080b611130501c2800300c0c14014490004803a6050799440c1c1c0190300c9000402c0001540d074 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 532088138 1250 532086888 532086913
    0x11103210901050411120f070306090204150303050405040c051603170702030c06180c0d060501080c010201021908060111120322030c02040213030204150812030c0403021e12 76
    0x6820010107680e07803603040070100b100007802d40034900f81650b410b4a0184060224042990420341c0a071980b150612820500100707001242d0090000c07980240c900300484607001ca00c03940e03600c0c1c2c01c0c040503010844c1000700b08041c0c01c040e404800c5072074251500c10704180c000540c142c40c800030b06805070300003012030b03070300d040415178482c86642c0100c5240001c2d40307003003143c11086884000c02800001c0b0240000000c400e2010244411510742c4001081100c501c206440d290000700420300950495205030a2100001d50051088602d030094601d01054035215010003250744d16001400d00c0c1c1004510300d0726040344c50007000903507010381032002c816840c0d180140d00250111404880c8442e001414102c460101f0f070001400f91086806a4026035681c0320080b804803034a016600c000c0d042460550380040d800d44e8025000e040d84c0005c82511004252011030350f00c0380c001510300010b0000c0030001000181761221164600803020072905209200d80000121082884041d000190b0040002400c0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 532089388 1250 532088138 532088197
    0x412050d0f020613030909020c060a0b04020c120702060f04271e05040618060e150c03011e18050402010f020d05040605030a021308150f0f04030302030402011103 71
    0x40d8140e031800410100008200a5507420b02a01c0307025008490000407043c903204251010107010040f00a560720080f200d030059444504484011172580713884000390881c50607000700c41c01030900b00010020241114401601644009012a8452400c010041d1880da0040c0500020034014851841e0740c590002c49844070440000c4240b401480c206003205103800072a8a90f5900500500025030b075580d601e040001000031809200c02c0304075102414007048031a0300034041e001040400d449441d0001410084201f9017596200d03e10202880148400078541005501d00030081c01442902540d5406240111030b4207403681c4000ba45503800c12003907581115980c8860b5109100070716805003600c50040290140c3d02400c01044000000702d01244080d806036100c50982051201545039a5010155250071850708422041b40c024000741c03105e40c546103094810b940314642d042950356559000c600950000300102d060210103031a42402010400c05000b0b90b0004008403034078080000282c0381d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 532090638 1250 532089388 532089403
    0x10603031d0411030106030c090801050c041e05010509190302040c27050319060902030d02010c02150105060421060509030a1715040509120712080a0c0e0f010c08041205 74
    0x90041d420241c6039045980d502e004c580c11036009140004550100d094207c490400552003000c5541c01c0c00240426101400003c108031200a040e03603440c1e02910018800900092140c1c602140041c03120b4210360404a80349d200040029000d40c28098032940041e08a8081c80d104500207070702c00c1040c400d4120780c0d41541050382c1c0c601c200341d01043e141000090f80c079483d44098080c04984c1500106c10881a40c103c180302650080a542400c9038040000380201814100d10b001442213541d404583c004054109050321805003900340341c18205054200c0010585c0555040d12540c03403454008a0500d01c1100d0040308400c0286548050b0f41c2c0005200a108083d59404c81906405120744c0c4c00d4885018014480709890104540c0e9034181c00c5030a042d0392400c5040200d000040c40c0080200005000100403030715250000355403502d1741030008031107480d146040401e4800b0b030303110350a103807024102c0517a0b0350514182001c45402e0341c0d0400c498010f03900043c820100640b052080000502c0442e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 532091888 1250 532090638 532090697
    0x3090f0a050703031112220618290d02030a0501120c0608072c0415180911090a0905010510030f03140d020f07060b04110a120213170c01090f06030b1201060303 70
    0x20b182d2044081000c081c11803030780c824030ad00036101da085009803490348411501505003203420b49480350402c2104d0350281d4411604031000c0e514082c000f065003298200310b90015600308034440815401c0180a8030207140250154003445090f800d2211016242c102102d00000000101e038803c060000074801514420400c1403142094a6030a1000c5406807042c0c2c0380408210784040360707645e41405c1c507003109000800c0240d0444d80803003c00088002d650000011584120020001c90780c0d40c0e880010a400300d40401809503200203586070200388501d180c20122800c20080e0b0380fa0480603c0174008a03440030382100400440401e5640c144802403081c2c070000b081c1680c0601c4248101640b0799801e1061020325030a021800145940c080500e41c192540c0311841e803144080c5548907070030300c07a400180144101c00c0d8821001c0d0b1030401c0d40b003010700b6012541c0c0c8030801c42185003071003002c0d000b038400300b404a6005001c0c0b40342c00c2c505240034001d0b031000b18003d484204000c164140e00820404108120 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 532093138 1250 532091888 532091897
    0x1608010b0301060f2001292706040b0303210901020403080405011b0209180c01030c080a11120a050609070507020a050127090203090f0a0507030311122206 68
    0x4001c07030368006521307002501c103902c0e011000744420002c3c00c1900c07260421410b0303590710f000c2c4d420400c00f800740070b00c804504420b41c20940034040c0e10200030000d8200c11902c1d44e00301400042c51581c007101804241c02c2000100302003a62185800801e165403c02c032005034a0f413048030203004101d107001c0c1d10b1507080000340e0300941c542800c645910781d007440740b80b25103810840c954500c0d2144401822950b084d0542c0144085854100768084100c07610322011341c0d242901411040b4030080d8024450307040e442000361076400043d941d00c0746500041500c68000c0740d81142c02c1080411500c0b00c0c00b081032050641703000000785400d000c406c2c04506503000744941e003800420080310026994100810741240c500b4a480b0047c071002d10a1101100003040000203e0603808030042a034050a03006148222998803ca23000004244001513840310300d05005070240e0040803092011074842d82d103d01d803c1301998100ca0641c60701580c60411548034200c0d230300030902c105514040203280340c00c2120091107113181 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 532094388 1250 532093138 532093141
    0x3030515011e0c140f0c0a05100e090603010605090406020a03050f010f0b0a0c050d02060702011a0607120507020303070b010f06081e042f04050105060712080402030309091608010b03 80
    0x2032042610303601e001400b040c80082c2e076181040084100c0485030502042c010b0b12a111415000140c3c3c44602c194802c3c4901c0b1490404502424907007113121035414981c0d2800c0d403042d0301303c00b4000111405002642c05540359540460940c0350114528041d51181200680d25a06101d0003811224080d003080380c0031a154004000c0030030381d500104184d03140041140c0d501c100c10002511481100e400060560040c01070342a005074002c641c4034880d04d0950001d001c0010354516038900c2d12040b60015600500622504011441c6914104805051420b0081c688140b0782c000a02d1500088000c4420b40d00001c010f01c41160f03240b03058401071595060a5040b410400b0300c82504400e8518051240e034665000601448049501561b0410100c002108225281c40310348807aa214081e90034003c1c2d040100001b4a410f0040c112000c154011450761701ca0140d80104882d40030b00508280e80c58481030108181d141d40d9801a1400b8085102d04610000b814260103030854005a0054000c00c60500 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 532095638 1250 532094388 532094417
    0x10806060f0a170f0f090708070b07020609060c061009182a15020601120b010e04030c050d1205060f0a0b160c090e1905030d020906160303051501 64
    0x1400d0321106030428088948415480600b100c440c030800c1140f80804014100744202004840d200c02d004221541c03240c2031070b90342c41c1c401c195031700a10b200768643e86d40b290604220800884028001c203510040a041c0b03005094000668a6080680c58901d00d8110005104018000c2458400100b400000500000c0510f110710440d0000000340901081070610b88081ea902040700c0e80bc40100f20486140c3d2059261200075021403c0350090b140544184000810034200b90298203da0720342c04841c451680c0e0030f140c080b46104a02900441c140b000035454500096818880400700c1c00700d40d80c0c1d42d00005d401d00c8103a0113403a000b070000f034060a81c0c3d8002140c0c94840c110114180e035540036043c2c0c0d44102c101450f26080c140128042c1c92441590701c0800e4aa20f1a0442178602440030101c0ea403c106980651103458038010b0001d00c2580200311600c0b800702c80b40c01400d043da00007001c41d0f051140503100c00c4640458000e084001079a2030f02041103c0010b1a8140082402803030040480320004 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 532096888 1250 532095638 532095649
    0x10f030b131a0904050c011b0b2206020c031c15050111031c0b01020f1f0c03060506070c030c08030901091e03020a030c050109060503060d020411090d150b010806 71
    0x169469041c540390404442000100d400c0c4200464000d0a0b2018514090400c0c1d500c640c4086500c60016100301042429411543c00d01044140c020382c10700b441e5203800156400d0040150752480751003412074858008615144007a02c006d91008010b940d80d21017288009a02610b2040b100313001034600f1402e40200e0f100311140300183c450038201540c000740391862072403942c0038451102e0303a41c07007102c0810b4607228110f802c0358031100c000307800329244042e18100306501c41074103016490601e030320814241c03512800c1d5004004104500d06000072070300d88413400308801340e001e90004e071803481015104004000804100358000c0121001560901000c00c0000780400310520814101001400c07100607502d01030b4003030343c00030b680c01005041c1040d074910705071840314008d104a07400708070302140004505004400b2280308400c02400c04890003019401c0100034025003520300059001400416032076200c0c80c5803003200701d0103a0b480e65046a122030704141074425a0034070030b0400c0309480500103552580c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 532098138 1250 532096888 532096909
    0x106181a0a0e13020f0403020306221b030c0618171002030a0e01020408061b03070c020108090a0501051801110408070b030c070203030d1a0405040b0a090c080f0c010f030b 75
    0x202c0c80c05103481e9a00c0400074005140c400030000e90700e0b00c002491640c08400710004d008481c4290203071801c0c2e6036070744244950140013560b248508040c00c28040c00241c654400c10007141c1c030030448000c506840b5140c8040c44030058100c01c01140705100d02901500c204015003005042d1a282c02403090300c040c284c1c580300c0020080e80f1030580d40100100381c0c0038155030030070002400302da4021515641e0b80d000c042c1e81c40405a5042c0320307d0f19003900101c00c464030f00c02200e20480f40da40300c021081000e13500449040c400100600a03902071015010300045c028000c80b80030f54441c00e0300711000c2c50700e460582e08442280d84500f080842c00c2004200d0b034800800d25204503081b16010a8aaa440e40d500500034411044000d51601001844001100e050703804034080c0c0004003c00c0b031350100c0500c10720003151815a80a4900d18101c400905d280c4480d41210310101d2040401d0b074081c0781d48021483c42e000c180e82a4400316001007824a1495a2102c403c0c60001a00d16092041c440124046481c9000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 532099388 1250 532098138 532098157
    0xf22091a030d111c03051e280b0d0506070e060403050607050f070b04060f18020f1309020a030b01051212030103030f0e03100f0c050c061504060e0106181a 68
    0x400203ca24500f001c1405031208600303021540402d04084002d0050042000f1100d65080034912400c811089a42c0c4491602c1096004c9900c0400c000703d8226011941100e40007114042d128981b2680d5611401c101c114224841c80c0203240c5401c00500150510083c8540d45000d07010a00081010603000541580c01c03036214101250348a24845080708107104140d030140803240e0b071401344410480d02c1d5015500d00d88841c8010084070070b01c2450075000d414030b07030b40180d4031a4228040c81040d2500060350344a10100d00340c0002c0300816640400c1d4003e0080d030066555034102d100400c82c81c1083d03400c11660301e2110028140741c501540c1002070501060001400f000000000d000b21140900903c500c02180102191001c1da81460180c000e88000020070780098100540960703118040e006840e035049403c4003a02c105c0c0e4421180d441d190503110001070b48903450f0040001c848105103030b180d02902282e40c9510000081841f540c1003040c50354006501882d0001c1c00004045414081c1c640590 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 532100638 1250 532099388 532099397
    0x6070f060f15151103071203050105490602070618020a0b0903031c1b0908070911071415070c0f060c022a0406080102130b0f22091a030d 60
    0x43c9412581e0309442c1c2c203540524440050074078140841804121801c1c4429501440301e0703030701d50007071240049072917418080345a142c00700c681f03030012504005180301c00d021a000100308401c0243c1c030742ca06503140c41503d05c681d0000d20442032080c10b001321381c0717040820501d0346007419203680452444c5a04e4403c0d1070210001042c0321005503800d008072180d050145400001030308220940000500c15021400d89148000d80203040d03603401014100221810040546841c615082e0004050211440410140744007002041c000810080c031000c41d0100c420000e01d06103105000005a121000c1d000e00309020501e000a00040c40220328680e0281e80600085400c4515034410380c41c2082d85404050b0000c0001c0103480c0d034480b071090b411003440c4216024070020fa980c080107401c038404e13190104420900b080701804910807134001052034842d00c1009610f00440052021200e02c0c90b01103070011201390203070402100d429402002d05131110341081d558030540000c0002c0d5201041d100f91021320 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 532101888 1250 532100638 532100669
    0xb060a030c1a0d0914061008060c0c0102040305010905010213120c0b07020105090915040f1514030307120306050a0806131223030901051b0d0504020a030206070f060f15 74
    0x41c80c05058030901c45074681c0c02d000c1c4802c5858164800305e01c00131480514070070b8000007810300d42240c024000f00c41500020305120748650904044540c880301003200c44d903400300000000541300344142c100143c05200010780381d45c02d10546500b038100c01d40c0b052001801c0c94a900021600c1e5410b000c0c00c5456500546641d002e0310710040c1c1d81c4d80a080f0459070703c80068400c000110044040c098084001203800300301404251f80c40b607007210124082807504c036003ca1400c1c0300031180f20400d00040040181101e08058060ba104061501d101c0c0c0610300003911403008004a0911031008400b505110000d010145003a4078121800e243d0a40040c0c000042303040583c070400c0c0580200064940e07104410014400401d0f4031040b10381c030560b0308420315881d040000380015000e0f40c0091a401010000500d00017083d84158080c04005e00140d900c8007101000000590702c80c0c0c020315115100f907141d0b11500340702e820008100c8031280140d179406400c004400c2545800c0745a4101942d11a800c601c0c4c01 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 532103138 1250 532101888 532101929
    0x90c12150c34140118120908060a02040302030705060c1005061f021e06010e04060207030e2d0a0f03060905070801150f05060406140306010221070b060a030c 69
    0x148140300501c000b48840c111101016104070401c5000040d01655101090b2007052007868204d5442c401100800c801800c3d1100015640c0642e82098030100d10b80b0701007130b648510015061400568041ca003240d80010104114141444a0002000b0440c0c0190804c001c0038425901d880c0100c4114154581ea02c0028000b541c800c00048601c18050610000100b100c0c0c501959800003002040c0080110340742d2526a0080051810f041c0d0720003481d10052510f4650350070020703401020084041c043c40b00091180340e12803010400841500e2008000c48001051140d810b1328090741c201801100c030503000344070700080c2d24039000c101c950100c00040c400d181800d0941c1094541d0f04901c07400c4d4240035065005000c02030355041501c0b626060501070b107a5480402459214510601010030b6040004049900301c01c400b07140d101e00107005448288000b590b696100700b0740d108442c0d6944501140341c105000c8500182640a10252400d5043e1401c603254010b000c501ca1144007082401d210249070b6 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 532104388 1250 532103138 532103167
    0xa0e2e09230a0906060b0307050412050c1f320c0a0c09060302090c070209180f0d08160504030c052403090703060b0f0a0302040c17090c12150c 63
    0x301c075100d00d054078181000001440680034801e4243d55080c20240013103034011205088a0090010b61a810b00d02481d10b0385d008640c04402e00c0c1910107006040320392956459a002c02240d1040010038150001d0940700b001d858149154010035510151001c2c0c020300d0707600060000004015a0310341c5841e82c0114401070b203071801840009107a0b412030040000c140015403c04810303a0f108403a890120398460741406400d000ea03a8029500c1050341c004921055000a40c00c89503c0061068942080e641e01142d45002c0210220b040003d42e40d208201c001e42407500b520500440703910f0841d15091458540701d50f070609500409115180b9194002140b400f000440c0110f40007007180786803241340502d4202d8079901c092000b950703c2401c200c0e00c1c8803036150444009001c004002c2401002c05e0854003440028104560030b0b0040c0280741c3d0040038011018240d141c4a8900c04006081c5d00b1410424010b0b13510344461300e45203a03800000c0c0c041c01c502107984180e5103c00c44207a941d4035120754205000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 532105638 1250 532104388 532104431
    0xf0507080f0903130b030601030b0d030f030f09210807020f060c0c1501080c03160e04060e011e09121404090c05040f060320091509040b0a0e2e09 64
    0x81c42c407441d0700c009020113501d40031b1842100c0903201005202e10745824804140c00c0300100900181c010b000010300e203402a07001154240700340c140050041a160f58882e096801c450008091584220510381c402d07500c0300850f940103c2074406003100e152203a0603195038040182c0039541c85400814a00a025010007031084501202840c074030855954048898540b800b2641d01402809140000c2c3c14403191072081234200d0710907105455240d516605c1c3c0b940202200051010595214003a014220100c45071038407000c0148240003a0940b403610300a41c1d5614400001003e00282159031011080d8490a0f40c00f110200c481c04148142c00040841e60b6101d0b940168002081220700071511542c5684440180880d0180800c8400c84004040d040c501512404540c03081c2a00f81c035104144000d4003400340c00102900c00328440c002d1500040392000250007411060703289104006071100e9070312807090196030070407840058980d10018800098128051044015250034504241d010102d6044 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 532106888 1250 532105638 532105657
    0x1c150905010c050408060703020915090a0e011404140c1210030f0807110a052d040207060e0d0f020606090402030c030a0c29090d0f0c03030905040f0507080f0903 71
    0x2c0088100c50035001d042500113004284c8a4402c001c001a03109000e03100700c84840d8070040c160303800d484a20001d10704c640c0c010750040d5003041c003110002510345c0030480c0b024080d100120552034034402c0c8c0340502c803c640d81105000090b060340d4045c401980c49104c1101c607174bd4a40c00c0030702940d44d00c1c4035907204100d4240d07100410710701c2804141da06014503007010b88049441840030054080d2031400304401c8058900402e40d0118031400403a00601c090116a03200c100000c62040d82500c844002a00b01c2c2c006a006075455a141da00500300c680007446000300e0554541030200140701859070003551400014400c60003481030101003820340d6000c00140c1030185d4014222403100450b440d01d840d502d141d070701c10300d0070201e01e8910030030200d03041e4009a880e185101035150305240502040261030b4440c12404d41d102c58040e0301d40e40210780c03030454101c00b4602a40310980018a400d060004558100b06484415486c1905200046030b0045141e0b4201046080c1001903840d00180b850940c42200760a = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 532108138 1250 532106888 532106891
    0x7110d050a0c0308120a0b0307091d16030210020d080a27051c09060221070f0803010e0a0203060306060d0809031501140409081c060b0a050909061c15090501 69
    0x8100e5040000d042c0c518034080b0b0350002c0e843d800352080c141c61f42e1030302042c1e0542000300280000c0d8081e9200b00c401c80418566411007003400e03007005082c0710400d444a150307103940c100140b0560901b00090354445040d403009001942d1951001800740318080d2640060540361000c1454190800118503001214a200b0000800e40c40c50240e5a42d044001e14220f19210341050601c050700819100017241c0c0c4c0b0b6000351904ea041e03440002929903d4540c8071002482c18841d142c0413991140d42044000e12900c01d10787e0b02d5042000985502d44002e10241d0340c1801001048003540b00807501c2600f0101c1a80c900f81e41c4007451408030014080c41d1000c81d0544100d0746c018110240e1400c1c441d048450000c0c81c81680801d10b070500043d601009800b40c6149002c1112503c4540c0742d0700e0070f606945200c1c600144203900c95410305a90303800f003441a00091800320b1019410701d0224442500090200d444600004644410000c59100480040c200100c191a00100d4403440e07046200f075254480c00 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 532109388 1250 532108138 532108163
    0xa09020a0c1e02040605061e09190f060e090402010c021905060c0307060e010b060a1b0807030504061220070809040e0a05100903080c0f0c010c02010b1507110d050a 72
    0x309000b84030b000c48240d110758148100000c007414100d00300e132211100900d104103811404d03210400c299120001c615007110b0701009440030115002070a0018040942c010000c1520b4000020040c45000041920aa40e1702c01440010b030381040c102009217030706464903202e0151091002030542c0c656441a500400c0004000003042804001040d0592051008014408603a02454205e5030701200440e0480820004040414010700c1c0381d002c4141010402c0030404559502e40c599500000800c40c01318001040c14040c0340d82006040440244c030420030005030011203005008100180c6924808100010b0f0001c00e1210010860f20000c501030000c0c824500c85500030f42c1d540798492800da81f1409441560b851828541c01030700c1070315400d503980d0100741d1103114080086034006480e4a000520401c004500c584085c010402920b103580c000280c841a03130020b0144a8000d5070203200302090030000003000842e00b801802102d0703800d41d04903c1c103110b6490100c2c94100c0c0e1b2000078011240208 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 532110638 1250 532109388 532109423
    0x20d05090d140304200307090c02070e0903030f1501050c03040312260f13020306070306050a0f03030207090b0301270c0b1602040b01051b03090406080c0a09020a0c 72
    0x108200310706032555907191603498510604080703010549008040c0c20b9500450701c03600d130040700d10504143c0d0003001c0d01d010640e01d2090718100ca410f804000096000007030204445030710340e108158048104070296280d8071b03044a0400700c03414010018800700a070040c102c1c840381d02c508192800800f040c0101ca58540d107038102005a0900c01e0310704400122440002c110b40b4401c030908001040c032085501d141e68883e01e030b40314188000204584414100d090648016035010804e031401945143c40000b000da080c10b040c40000b210940240d4860007017042d08100195001910104030b940509000500c0310030f502c0021302601898072044540000000503803690582c01e151980c1642c41034042c80101c694541040b030040c028400034130800c0217004910700141c01e194200300050300c814580145410a040d44031400c1246060210065910104945085041610503000500381a60040c15101404030020b031101511340240d401440d0041030039001c0300e01841c84807548951003220f2203022080704 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 532111888 1250 532110638 532110643
    0xd0f0b060408032203050d080601120501030b160e01020c150702210106050406050a2102030105070504090506030106151101021c0506010e0a060914060c06071809151701020d0509 78
    0x400e072900101c40c0350310140324141c0081c100300413a81d011002d01131500700c7d0001a1001400104071078180407070301c4c4001c58280390511503240614800e0301c0490b075908103015400d20040381c0107161018003c050005403001c0ea00003441e03c0c0811021908440070400c86092080980143c940c000d4210340011070040d5289d002010001e00700a00038002c01c00d4541e10300801040e68079521501da00040141c10034480801e0780c0c0110391030144e03100d22500348414280d01280c03c40d07100f04c58480c009a00402e003400795014a01030075800510071402030040701e04008611000744100740d9000d050003026403048070009800e405545003118103501e00200440d090079580d001c2e21088490700c0c0007400e00c0d126040d2031714014045805445d00c90340c1d0250300c00c0c10b020060001280c040340440e80700b807082c80032001508040058500c100d00581d6044022420702201c101000c0160f00009031030340c10500c2d4900409102d4121004803907a002180701048007002f1101e00920500c10107000160a0a003048480d8500 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 532113138 1250 532111888 532111897
    0xb1c0308040218100902250b0601030b04020c07050d020d0c03030309120c030206071202040b070507030b0c07031d0d051507020f010c1b0507050a0e01081506060d0f0b06040803 77
    0x3e40300d600801441c610007403501001200c0e240c1c24000700d03107001d110100701980684a01070440c603240641c0c084001c011fa130000188182203d40340c1d030000c10440156414003034028444001c0c0c5041d03051150031004244c4404050194501452960b1907078001e5540b110860f510094102594074403d5441e800c0c014081c21095100341d5040c114101ca10140c00d100d0442c01c40e482e90143c1c05048203888103041103500460050700c002c01c4580910000c940c449540000b0408144030318024503007149185000e6080d142d0080100000742e4080c0080700c04240c01443c05403901d42907010b40d1218845a500048550120700c00141003403040501d00c0103441004c0703050758010305440d02103d01c050081c5404509032540380010070300181c00c00005540000c200e41d00000354a00c604244c607003090300c55001c19131810156214030b45010000b0010010b0042c140b1182070304c000c0c51040c25075a4603144000ca1a1071040310510f102503540d40441028600c8141d02030f114003c1d0003442039503160b07618903e850740d9420 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 532114388 1250 532113138 532113143
    0x10914010903020616051605100f0f0b03030c100504060603080304082206090605130b0c1e0102070201050909040606030c0b09010e0a32040f06090b031f0b1c030804 72
    0x134400410320006408000709041802642c8051800d5241c49003048440e0024500721024400c044000e999581c3e00d0042c010800c42100340040c0600e90210200c0564004a00c001e0094104101c40f01c160034020640c40031205684c500828140c0781c900c1c00500805030380e03101500f518804000c0c80104a2940010184c0ec00030884030180788001c000f1080010b00e26118080c00710745810005c202c041d0203180540307e0001f6a801c80d0340540d0b40c51815021580c81a98040345030780010a054500441400318020000c1c0e05a00850501c000c84e80060710620481c2d200743c0c418524030700042d00f0000c0719089207014583c094100d00105940c0c051400094100c03066940c0130070f80d240021041e600349540420108c034294501450440001c00714a400e4000301d103c2120500e5203000f11030302e01d46881c0030b40c1c9490b0f2400c540011700c0910b4205185d04170752080d002c0c1c0c1d1003a001032000419940204ca2084002c00074032000065034403505000442003d03000300c47d80d800104142e145400e060700050719a200f20b0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 532115638 1250 532114388 532114393
    0x210f09110f0307060c05161409010806011a07021f0f170f13031209080409241802040302090c0301050306010e0c0a0509010c02180a0b0301020a02030d0e01091401090302 74
    0x403a03036010018100004140d0030380541c0310355800c000c070f80e208070b18510076240a042507400740007800b1000b450b505036a4200c02d1050302c46111803a92030800750b910500400f90403018003115410540c11240c10049403109610a020104242c800d45d65001c40480a0700071000010403d428408006005185896078039800300d00c0880e80340f000340b520040d0380343c410181643c1100305507503001640c21a101d6081d0058040000701030407a034011000344619200c00d801480750a031502d103802019803c0d920300c0740c6002d03508000d681011003220414081001550210b0310000050907070445081c0081c0201d62019500c000c6031028442c070b042912000394140d41d03054041d280140c1c0c0314101d04550207010381d1504089074017040b00f582c3c000e208e600039010b0260140f60141400044ea0006000001c0d0814190305d1000c0e44030a11845050500c90400446c10681c0254107000c41520060340b640034903800010455100e106501841900398084000079901442100032401c1e20300b185402401207500440151 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 532116888 1250 532115638 532115663
    0x30e07080a0b010306020a110304030809090c09330d050126030406110c100305070210110a080a060509070908060108032b06030b0702030c0c091006210f09 68
    0x203040030900c111881e402c40001c0c2c21607403a44d43c40320001e600802c040d504210075801400305c1c0da00240b0080000b10b009010061711003e14808200022001403d0030440c40000c100540e580c0c1c56041c031040420b640d6020f9501606e1034446018025003d181d140f00c007080c00060001900c81441d400a8180e0b0702100c0c09a40d40440800f03455540869800f40c003041e035000b80400c00c1072622401039002c2604045059440308000301010943c0901c1040303035400481d840d10100221540d0401150000521030301301400b00400031104045580f00b0034586800304a000c2e1300040e1012116004900102405865821140350103140207003409454003980a21b800b8000c0002a84a8000182d9000554240c201c034950a0440301000220303460f1460040c24603111440000480e01c52120380b80b099450360041e640e00d61116120368140000481460311801c62a0180280c80c0c4468652b48240c500c1c0d82403c56010a90142b00e001c14501c03040e004507082c2c10040304101c0c9452640008805502c03a01001140c0d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 532118138 1250 532116888 532116899
    0x10e0112181104020c06190f050c030a0f0b10032c07030516050f06160f080d0c08090a0602032806090c031b140f03010311030613050d031e0c030e07 65
    0x10792090041c1e86005034460030100e408004e481094150401147c20b00064080301c50744144255202202c075203131015004000c2000d032234075138040c0c1422a040c14408000074442d200c0040c401703c1c218039003082050758880500c07800d5121800d0740c25008020b0080fa0004400c030049241c1c0ea10a507010031502030107075450300040004076214003400d90704018104c845800b0950305214a54009440301039110b40464442c90209070500c0741c810704a40a4001d19544203071701448801a55100101c840401c1240e03410844040c0010031246401c0341e1098000d6583c0c0c9801c0c0318400c2c41e0801259000c25a82041ca14030a40662688002c00300c0d003814006202550701130000764115406400940c01856803945401500e600c01d2100241d04c000015a542c14210246c01480040d04240c000f240c0040b0104001e0386d061804004290b405140d80d5080f0300e9140781503565a48452110b04044141516082086003140c0440180e200d2118100d42c104038413034a200c1c00070042e14240c106240c10780103510000c102c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 532119388 1250 532118138 532118141
    0x301031211190b0403050f0d09050c1509091b0a05030613091a1909030201140604060506040306051012060504060c0e031f09021804110901050f010e0112181104 70
    0x2103402c080c1d58070030103010340b9292002c55a100400c200c0410004024111142004030081e180d06113100d035000071f07a507400d4540300b0f00d0028000e1020f8805c6607107811095803012648201d40400c0007d80360104a9203610350b0103615103040d5030600c05078800208014103219401030181d445403008440e10141060820700c074404823002111b000d4480c043e9141e203200324001d003070629074024411465003013001009030b8074501140d40c0408110f0042c0d44510582115209404d40c1d144c100804480410095140900003030284c03050340b100034011170302c94000030320414500310850000c00c1c0c4d00b007009010100519028000b0700c002c0700c0480d0fa007807030310100c40310052050944294480f0041c00030920441d91002240c5503401c40200b0303002198031070190b0b40050302ea58100d0f143c8801101880c074154142460b0001036481d41044480c02201d4035401000195a43c40030740c01042e00a003003080d21243c6860040b5082001070b1104a111400e00084084214a88003803130740c1d483c0100f18130b07407592041008000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 532120638 1250 532119388 532119403
    0x1505070f0f0210050915100e1306090227090c100c060605030703060203190203130f1509111002010207020f010806180405010b091f1e0b0301031211 65
    0xc520248801415014100c9040c800c589401111000b100724000041651801c03104a2000e8000031504002d4134401c9060075000114001090311490504010645014004000881d5201816000d10070302800c0c0d4081c0c1021030700508140c0c5a542c6951490075515003410906901840341d400080848002103141401d076203005100036100e1070070301011198807800b0b84c0c081d642030f6658080098641c4d410041d03000194405e00000d80c0300c1c03802c0741c0e003001e544181c1e40c102d04000d07004204000003c0302c155014914076601500758030300d03181e15084c000020302001c50b00007405450400d000e014040048082001c12a040310301d81c0d20f6a00c0d00f04202e09070700404800a40090308803007540099030248003040e034003281c0602640300c00301c0c00ea445480e448005440030f6031640d666801d01e80c100d00b0180030303042c0c2c010f4003003c224840580405c40038502d00e645204035140c01618503010340d0302c4100c00021000800e50286010340b40d58480c1000301c2e8150214500f8404640d2080b40203407520408140326 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 532121888 1250 532120638 532120651
    0x30c0509070c03051b030309061e010321030f230108031303060b180f04060c0503040b041209150201150e010b07030e03011104080c030624150f161505 66
    0xb0100c8000c150f40035110f0743c215408802d0201c0c0004440504514100003175482a280b9400511490030300c1385d106991002108012030100003844018808241e210031500e501412000380c500c80031418140031401407807610b00084055007410034101c07a035030040d0f44202200030340080901991341e0380d0807041e0b601d04c20307080482c0b1500c0c90f02d241040400d845902c0380040610103403070f04045c0095000c080007507010844015850070754060903c1700f4448103200e0140880344c12300b000e80c91401cac940c9400c2c00806d401400103094112a90380042654410694000140b1090a14010f51642c40300d010f80079110701e408144521030a80c0001444d10a08c08900f03049a90b6800d600d403500b6066101180c60980c2103851941541d2a400401c9030f80d955100100010810390001d0301070380c1c201c5c1c4201800e25002901042c0a8004035402c01c0700d264009100007011305040341da2211005945150800c80d024500300c01ca02d11030085038074625100c1c0881c8c0d4900c660720418121a10380c25031102c0408031001a5140f = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 532123138 1250 532121888 532121897
    0x10f0306260307080a050705060708042003010e060a2003070c0314091306060206240f01120e030c0610060c02130b04051501111c0c0c0b0310030c050907 67
    0x803108028003103803029081a034240c054a18044030f603102c0882ea90b02080f844000200001803e0003803200038803006420104502c0c2c4280075040684400324414922000b410100f580214107032207a60f425402100744403440025141f0300c3c51301604003801003061300c2c0101c102c400d010820300c0e04072600b40300310b03032181c685916030518905268030211110500104800356014040041d048981e5400050103442035002c3d501040c00d9040c0b0f8002414a4070141160580082c01148640300f0300108505524410040d41c0120b207881301c00c40101c1d90312044c0c04520710884e240c15504c417510b61001c001802c000c6d05020840d04243c40f503010841d5410b815200760400544144800801031920440c400c0075501252804a04ca0201c400028203c07803040e1450701e070780488a1824005560842d824003000036040016100d04c1d89003121040748180c3c0b090102c0100442c40c031a680c1040450950040640000c0390303455124989001004a1200c480c0416110719502402c00107a5181250200b0301c030b14a030741d89 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 532124388 1250 532123138 532123169
    0x210c02090c1c06180b1914030102040b0f0a14070302070e0a0b040c0906020111071a0702030c0f150112081209030c0d031406060708030c03190e0c010f0306 68
    0x4410780c01d03007041121000ba038070940b0076601501e00900484000d00340c08406448880701ca9500303c1d0465414002860040c1608005440c442011011768012220b40402c1e555060050800080c0203200d00c2d0003068858001141540c20494940c0290a0900c443c1e00c1c1e440d0b2012a002601e4034600400320001d00590120700140714404207903c04c40d4200d94004000b103881050310f00054292910080940700040d010b40040100c81d03824020075501c00101c0c13054030302d480b0729522480709121000307141089900c0c0170004119030500c03c20480ea4400100c1c0180c0c0c1840d43d601c0c42482c0c0380e0b00700441014038410300000115000034120484441036512502d21032034041d8101681040c004000c10b4008540024010206da110341403051280d0120b4503600041c2042001e1660085010040d15140c0a9282802070a0000d180103085030b03080301c0040d0b0380766125690f0218004a80804d411402c000e2030034584403030745110700000c400381c40c007809803108400c5410070a805c0b0b0480700b00c1d10030461095642c0c4c0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 532125638 1250 532124388 532124401
    0x50705030606060d090c1203050c01110307020a110a03061e0c0e010c030c03020709050c0c060c04380a0809011d0705010e0d1e02130b0d0303050919210c0209 69
    0x103001c440c85910422010076669554031f800c4003414000786083d0041200080e01d00d210755028420182c80c91003042466040d424450f000035920034513400300505240c0c102c80e200141d07030b0f100e00f000c00085038807040501c9104c0c00218000601030200340042c00c01c900b403a42c55081e16001d0007803080500701c185d40b0b01843d6000c0f0789017180c400703920038019010343c040e8650101e0a080030713020300ea200b550200c59003642c580800c51000d10b06000141810100c40c0180030030312006441d2260385043e1640c940f40203009288040140c440300c203050035443c0e0034410005610134801d0300320500f10f00c0742503906c008010542180300310b01c418200310480c00c0d80a421020742885250300843e03940c040d1500c0030313060300c6000781e982da6000d26458008110080305031220210008510700211903030007042002d80700380b10510003140410303a030000305039000302407680f1038002414551007006003100f48001e200b525440741d03440e42001902500c0c0340c8002001800100700c140c210714011401c3d010741da5800b0f0841d018694815 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 532126888 1250 532125638 532125641
    0x1005010b03221704051018062001020d06050f190e0a0209060304050a0c0f0e01051509040219090801020c0604020f011715040507090605030a0b04110a0c050705030606060d 75
    0x200c0344491a0b0302c2103014540440e0000c0d000d07000409501c500d85a8540c2010200241810600640b82c10004410460007440800d0383c01c6004030341c110f04011000044070358103c0301d039004828034032800303600c0412401c0900401ea045039045030002e0b88d10f41200744000042c800c0c68070425040120a080902c01000044041007480d0381c00341c030140b8010300302800345002504c0c48e0b20540703058801d0f41c080001602801511600000100391110200e5203a40c94a01c3d11180418140700b039511075003c0c0d000005007050300f141107580500d002441159690020080801701c00c600e0300e0042c00060200c400460310f41014400c03034510840c2c1000403c1c080d6510f03403c1110004c0c00d60100ca0412545c1d8401c400c1d289096a105801414100d444428101d890800c2c0705c2140d500030300407020010104070800c03145070040100c94101030f420b0004104046040c003c94040d1104240d410481c0c103000402c1e14030558801041c0e01220f1082c1c041ea00b210350b0b01c0c0700b050355400b0103079600d03507000768100210210440b81c1e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 532128138 1250 532126888 532126921
    0x60612060207060b1f180f031b05010c051e030405101809020c0a0b1f0312030507020a0b0402060304030201090c08030702010e0312030f130203030f070b160203030727080304081005010b03 82
    0x2c044030000c49030702c1d40c7d40689104050750044941c2031480d918210f900d440501150301502081c6448442c4201070f440d09a075864030005810a10742c1140b1805610361070a00484001c0d0002a001e0403044415510050000c4984851030a803c050920086881c4030300d402100c8890000d600104120490354441d4110340078050208072501c091448070320a494000800030300154010564403030b00d58203241000c0c0559600824130400c40d0052042030002500406000341c100d034054078500d4803942c4034030301a0f005200d0350f10083c054001300380e400100550004018604240f00b03aa0380070f00c00a104c4249961000b90400794907052100340700041d01107850b0001158064100001003d400b402900800d045500004400e0810500083c01f0030074480c0c0000d4154010507206009403203440300d402c0080d00c82c000a45008100080c1d00340801081940170340e52200d02820803805030b007290707a070001d15907a9402407040c3c4001d80142c1950180a48040c803c0e18101c402e4505080d00e5582d40f034081003411401c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 532129388 1250 532128138 532128167
    0xc100908030f090c0312130f090e0d030203010b0a0f051303050d12051b22030825051c030b04060b0304031403010803030415180609020f030127060612060207060b1f 72
    0x140c1f6140040c9408210710150018034001c600041c41980c07421846050010a0081005040c010801044108a04001c980e0210b11038a031002044008410031031740ca1154104503e040009604003100307208020a002c2e907a50601e0300c5d0204001d03080c240d0b01e81030380e0381100d1501496401008031012290107000905d480c1010180044078021410b5070b002404254ae0400d03a50118007044007005058411401070f50005080940d080c0108913680c1c150783d9000d4030480d4641140409030205030240241c00000044000400c1881000c0d160218200503400490382075000811038041042d0b460300001c122416541c030300c0301651542c0e40e43d032200307000c540504075032203480c65507825603490b00350205800c2c4815a2003070901058452060040040400740c4182040c442e91401005080142d6615149010001d030300d01549a880c1450801c0001404c56a01c00158030704203142a81c10402d00c4d5000340345852043c02c0400c01d458441c41403141d50311081264a10004508210701c2503903020304042c03003000d00f = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 532130638 1250 532129388 532129417
    0x110c07090522060b060405130c030b150a0309081b2a010903080c0307080a02010b0a080607020a110a03020312030405010501120807060f1d0304181503080c100908030f090c0312 77
    0x5941f0310125080c144a82d014000c01a5605058044154580107c032a110411a1513010b081811071001d20346105031078154007410398912602d01040307070050640da88418401d00c1d5030b041a214901c440d03262203a505500607500c10400701400c440001455502811406a45284043d415681d5030785541d8080032070b285440c0b0042c0300c0c80c4009a500c10041110450b03560000c103540c07440c00c0900c4840d10854000400300d401481c20080030650000314440101d801c50320400e801801080420802c139081d40000c0c3d018011075000c41902801c141c0114001e9115030004c01c21a079035446045003680d1041c500038081c0c1c0c01040284080341980c0c20007144180b20041c0060300c0800f900c03491a41c4040b1050095003500089410480c40607113401c1d640c100c400b610014441c4c8100301404100c2480749000c0109000f40c042502c0b003118004001805007419464810022160641042080c0383c03c111400c0403811b038407400044030048042101000f6000240080c4030312008000b03200001c1c1c105811281e502c6 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 532131888 1250 532130638 532130647
    0x2070f0201051b010c0e030c0306010b190c05100b0108010e0606030f040614010e09010f0203010f060302070305120c0301150e010e0f0d08030103080c0f0d140d110c07090522060b06 79
    0x3603100317228a8600200603214100400100c0e800d26061050340e12402d031094112000411410f8100421140002c01e410201c40313500b401d010040d50651181500900070b48a90004200c03110602d41c003030300c522403090300d9480e00380c0e03a00c8003ca00b0030442111129004902440850740104071a01c2c00e030381040c4140380c041502c600d030090709441000264004100040400d0911039502c400380300721032041100b003c094bc690f60504040750a5140c2074894041096800039040040c140b044054602d6003008400d02e01d5039041c1443c00c081c0c150000e010711a400c8400914442500d40200c04005481e041a101c0040000300c0300c0c1000b661600c8050403c0d00103010180b01800507144000540c0030b980b14085a0361119504420146800c7d5418006c0707a080c2d00641c066045150401007000041c40300c261125901c90280b10980f01804040d0131341c0f6081c8401040b034448a00d00070540750305844800d60200003684e03d40611400c200b075140900c1d54850000303100d0300c0c0481c0e6a03070000d502850004c0c0c084d40c5032 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 532133138 1250 532131888 532131937
    0x6080a030f0c020d060c200a02030c0f1f020109120816031a0a120501140c071b0f0b0a030b04150504020c01270303140126100c03020a080a02070f020105 67
    0x186e54100f00c03034000041c400304026400c010780c9070250b0700740c144840c000c040b040d0041d80429a1083c40305012440f0780200161001d40342c4e0f4550541045a0128103000c15000b14044060b0113040003030b20844400940f116900f2407035104940d2948640c004000d481d040740d00e401000d070b00610a90320f105594034041c4400702219210b41111800920010f13690440304400c60410a00715038008960321604030410040c07100070329000c8152000c0e150004008143c903654603185640d250007a600008410042410000d002e91684020f080c92600a4038140310095030001007200b01d0b005515216805070f038101007481a03040650103040c2624449000191890047e503071070308031507182021789039020380c115048403c2540c1402040441440710302100c0d01d55051640720403002601d80200078201070780500c0010f1101c002c019010320500140c204003c0c1903003600b0018040d45c404400200812005008075078590400d00c2103480032508900980c0840c0300c1980111200e82c00900650a1508100c002039103 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 532134388 1250 532133138 532133141
    0x6090204020a121b140307090521010f0c05030a0902030a021e1f020a080307032019090b16020604171c05030411090709090501030b090106080a030f0c020d06 69
    0x10852110b80700d4031054008003142d401038624613400d9050340070f0321915650031039800002000350080139a80c110340320307524040f00303c03040050356010725440648101035022100010503110781e42c0070280f0080c01060009000e45051b150303c0041d040004a0400c0040d48515003075020b01c04c1144020241c134503251303a5030009021007900d60880030f824a00c0038080c804501d000c24480d80000c11440c00c0d103603e50301c03e8501a441d8404258050501000040002c80c811710075400039150f192070810515408000750075201c50343d003010180c1e543d03500401c90101402c1e0700400c9108210b911a0060620781090354001c00b41c4070b4100c03181241c0103a41407102040b4015000040240003003600005c011000d038807007d4059603159000c407041885020010f01003c5005031115907016001501c100109895480089610403042d61180460038a004008000c1003584d00880340038801c0a8002c2c0407054980e06000d4440001c03200060104070440c005043c4280900d14540b100e40c0010564601c58a882d240c580 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 532135638 1250 532134388 532134397
    0x201110a05030c0c0a050909100f090b1305070f05130908040b0c0c090109050403050712021207081207080c0427020705010b030d0e130f02162003011e090609020402 72
    0x4081c1d085a00c51030528100344032158000c06d8111251030540c100350079503980398800c0301212986543c460007408102903c03038011800c2154007000140b850b1400c114101044d081c043c80440d00ba00911400150718060001090b06546005000542031200c024944005110200d02196501c809200028640894801801ea40d0003a000500310b101c88240802c40c05000503005840c0c074a18140038000480d920905541c000c0f603000452034918069a5416440c00c1203a143c0092442c600040b05030070401010b0140c0075140c020b44ca900303115250000203031140c4404840039030b220340c8203002c1044543c44230608403400c0340400c1c0403110b5150007104844240e074071180341641e00d46e44440c0b07441200c0c1020007030a0300030450b61a254600411100010344460b044406035184a0307141d003000d04802c20a94111103900000c0c40d581d6a1441c0c052600014800e911260010011120420000c55040c180aa00003229440003110740c03840c2e100380e2090082501c01d40984905a0722040c050040e1190b10013031 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 532136888 1250 532135638 532135657
    0x301060512060f1f0303051309020406030209040509030403020319030c02060f0406021e0d0f050d09050a0c06260712050c041509120f0f0503040f03030f030e0a0201110a0503 76
    0xc0c4031603d0520b6080030780d9a009003103051210b900d292141c6000100e0000c81c1c054176410300d8007603911b101085180b003c5042c02d810801da003510000340092116050390090a04040c195070030b01140d61382550f400e4481c0120310000c0c0d00f42d000200d400807000c9541d0f03400c82c4914801c1c1051a070b0307030700c068002c58800c0e0006280c140311044000f40500507103404020440c413145090f007129280d04050f040c250703103030f0790322045c1e440c14030401340340305c4084501502c180c4204018889081041c010103040003540c3d8944508155a812680c11000c200148128081c41554089443c40005245070407501500c03e10000c1c411010014860030991105125010b12030042142c00006601c86040c440c00034400c04581040c00c00740300c03110008000a9240e986540c0100d500b18110041018460808140b1605400c1004005000014000c151002c0190312030301603034000e42d40c03600d44042603007040d0111098012002c1d0642d00c005801c80041d80b268490701150306400090b070f59140c10036aa81859038000802d070 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 532138138 1250 532136888 532136893
    0x408071a0601110c0a1509081204030c0b16110117040c09050709030f060e01020f0c060f010501050c06060f0118091407020a080a050708070b04110901050901230301060512 75
    0x107101c569030340040250801c080d1a0003820f0f510340300700001070785005148902c00f011007100540c500c1c200d008002071030003015920b041c2c9a40171040030900c650b0303a03c07a01048550441c0400d0100e6a083c2038403d4800ca9040c040b10307019000704030f07100c40c2c2c5005810301d4030604005200360340540442c2d0341e100e03140c050742c8901103092005060080381d40a507070b0010000303002c00812400c2000801d100700540d060882d000100010b4440da5001ca06000e03101c1d003103690402180000f0f210859060001d1201e01c1070821503030486950740c031807004444da4851051540c0311a801140482c02c60703e0480048550b440c01410481c00e13004480c00f01c1801194190301000c11550746980074a181750350b000340e03036500910a1001d080e40c5007a55890300308501a4805503010403001061100800407004122040f054209200b0b003914030301441c1001e02d801302d4031900c0b07010715444000011036090403000310381642d00c501080805800c030000c0b52014a40340090305603041d0340303d4000003480d0321a0020401c113118003801 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 532139388 1250 532138138 532138141
    0xa0e10180b18190b031b030a080c0601091512080a020a0b150111010e150408090d0b15100509060906040302100309050d0203090d030f031b080a0b0603040c030602030408071a 76
    0x203044125040400d245201c03900300f8210384c030190b80108012811549084406020003402c6020a02d0001d800d600100082000a500d4100110000d1003170704032201d0310018000052241500d0001c0c0c1c051744602d421120491a4071070009030a10081d00008659204030343c1c40070545d072164541c0801c191032a9801c9648481c00104559103c0508016089880024000700d101018140d944205500c0c9801c0e03042c0f01c902c04507040210b41811541c607503100804500011056007040c6003289419107040b1241c42c02010040c0c1d850030541a44d5446000c2e81c3c8640d03042444610038440c46500c55282e9640c03180b41040040016518103100c0c001683d20303a600000e1121031380ca0800d18184048400c0303030a40d4401e006c1c1d0750321641d42c40c2d0200c2e500d0b541440e046140510320345040e4003a0100841e5440420401d281c07880c1c0043d030000805104d1180007405101451030301007401881d22060350054008402c000c014408544280c00460308188181e04030780c039086098031001c01e480050000b042d0030444420 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 532140638 1250 532139388 532139401
    0x303030b040f020906040302062a070e0106020a0b010605090102011503080306030c1806041d0303070309020a0605210c0f0406020d090e010b070b0901150b07020a0e10180b18 76
    0x1c940b8003403000b070b91400c51030030b6840c50000c4c01d10b00451000a108041c001104c444140b4001d1104080489064040c0648011941400d440b480c85018190f994a560710000812503c0015030325551500072960130156401d22008440d1940311107000da040d907490b2408460921340303900c44034000314054650140c49041c54000c140c2008803840e61944108008030120464000520842d500300804560010720006c0c896482c942641c0d50b01e000c000c49000c08002c00c2207054045e0030000b84180300311891110580c81e40c50540300703401514102c9401003600910503c030350140d41650398106100d50803080c01c0ca201c404002d20744e603009800c0800140c00155030501200c1c0c0004281002e082080780c103910560600395032480501960700040e000491400104455010a5008161010142204884440c2c858241d04070303a610031107080340030700c0c0b0302080001c2c1c401605c041c1c03e004400b200e4200280516285061000c468010316915101d5594085440c0d60381e107000e0400e001e8450802c544082d840d103039 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 532141888 1250 532140638 532140641
    0x11b02150c0a0b060a060f0f180b03090601050603310c0b0a02010b030a11011b02040c0c0201020c040504020108010303050309100513061b050a050d021908040b01060c020a060807030b03070303030b04 87
    0x29010034041e1400d038174288481604185004c07520b09051a0058900010344800c03174001040c4031414020003e0890040703288499a401580700b080d00c41c045440720390381c0700c080c402c45100c00c58031034800d5032045c0207090108140600d52001c640d001410700e405c1e40f085803a00d600d41407043d400801388480c000750b545c52040e0280910b00c1600801c074090a098401600c4036009441d00400060400000c0300f2002010040210394002d11600603008012090a041c0064002c60f500300007a805442081c2a004661a03d802401c1c451903040c2e44c2c04030b10364a96642038a181d0406040c0516a00541e80901c3c543c910a20800e442009a4140419140010300f4030b00300311046684168410303a0aa035121100c6070b009400c0ba00344104c1d03441d1240d918800a003a0782e00078040c08008100a13034580c04004901da0b0b018844a00035402140503088c070303036615130080c2c603095444d80c0c00075040302080d2400c211003401042c840303601c91081d003008107840103058000b9042c44500d400880c0400d907903402103400340c10305 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 532143138 1250 532141888 532141891
    0x14010608040201051905071a070e1f0818010e0c100c0c0b031305010501150e09131709101815021207050111030112150b011b02150c0a0b 60
    0x40d0400003154102500028040c0c400d40280c100d04000c484038440080344070310101c0da055a0031607080d548418540380b801d8038201e82a540c010020300d41544051030b44c6840300c144401d100900c000c01c48000002c0d0b900b6640c840d4001c01040346e0582c00d6080010b540820302401080412010151800018220803c2450450500d50304200140d01000c040000e04040881c400d45008104087e2a9030750951440e6021031000801170941d42000c0c0001180e20011688050b140301a80741c000c141424034041c404504802c8030300b4515520040030b6203002c540902014030200c050f001b8064a801062004151f059112055800c00207102802c413000721441010700300090f04080301c10b008440800c00009646a154402d41c1003c0310b13002070b03141d041110175400342040041c8992841d0f100d6a55001d03944842c103a81d50b054a013085819104980c1c3c44842c402c09181d09016110703008807100b5090348030040c070301c241e200f20382080f100840034500c0824627020388542800791004001317411f840d14200254038070 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 532144388 1250 532143138 532143149
    0xf060506130902031b033306060909130204020d0203090f0607031a0f0d05070b071208061e12030d02070615050306060607030216140f010e060d0903030b131401 70
    0x684005440160380200c0d017009404403900058660241c60300c000790610705100c0e00454001071048900711810440040b240610684030030902207950b4070401c2c000c4074415440f0140e40a2084400654650f01500c144000e1a001502c010708044042030b406c0101d90081d545880766500c0610000065071080007425800b0303e41c2e103001d000f0384500101c110519402d9100144c400e0b8400f201030f4003942c03203c0803120203c0d60080c007140e928a0f9100e03509885070307000440a0b02c040c01444002e6a420307001e031011a01440010b440550344080021b8000d10428441140b160701c544000d00c200e01c66a402c0001d42001c0341e0411006039901c0041c6010822034040b07480e9600852480d241c100499640400d42560242041d582296552454a4106e00b851050451911102140003001c1038a0759580103030781d08144183e41c000789100300c0c20019544003000004196010104103c00c605041d501e4200203140fa203e4103020170141c9100000030001900d80c03200501c25507441180344000b4131300c100300f50700501 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 532145638 1250 532144388 532144391
    0x11119031116140307110109080d02100e15101d16030506031905100e0312060645010503040506071b1e03110f070e0907030f06050613 59
    0x42041d030401c916801204500c20004400c1600d030414003000080365920b00f5028010303a681e450003403500d003080c0b04000344502e00207140791001080030400003c40b40c8444880b03400a01a0082d4280080c010701410201440c0c40c1c081d510b0503d03c000300c0011171a0241400405000704a403c0030148503540c5440e560140410b0014014404c08106411440c4c05070312061502203850340d00c078004285048021207040d10040e0302c4041260a114001c6050199061130903000d000c0800f6003041903540c0e00440075000c068400d650041051882c040c0c1c0148204980e1041c68141c005c50000d18030340483c148224142c3ca42c2c180c030b8003000348400303061010300030344424280141103050076103540f55100310080203003083c000e10088050011103500424a2540d0344041600d010740c940e05258803004400d443c049010408035030058024210104e4200d00c0d0200d0f2500400500d031900764889020500980340c0d0030345008000d400701c04140103103460303005140100350200d01c03420001c003402881c042c0c9284410256 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 532146888 1250 532145638 532145651
    0x304150b240706020405060409050a0b0d030f11071805041a01060206130c050d03050c0705011b02090c0c071509060e060f070303110a0306051c08070308090f01111903 73
    0x1c10800710000d04290004040e291510b495240c403400a11594100c154444030114000407400041d4104034455464502d05000f40c51482c0d090000040b02848020b0108540c50b8581c2556485040c60088800341c081c100c94026507910300d04410040c44840c800600b503151001c21081c0a2031402c25519032800300c54031107140d858400002c0d2500c1000e442404400706c0c00c0152401d1017552a102806090002e24114010000d46805001070b481a121000030340a040b1001a940d07028503040501824004e85240b200030460b03082000840300101143d401040c240206a0302600801802e00940314424008070306c0e041c121000f40ca1003403d940071000708500e03002c1c0b108960325400103590648066240441d1107451511301a0040c0c18000c203416210140420007141582e4940c1001c012074106450100080d0030324094070740f1140c3d0215014010003020085500003d1040c044254270015400a6030340c06071580101500796090f49078550f000305004201c4880142548941e404036141c54102004403 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 532148138 1250 532146888 532146919
    0x915130b0f070c0602030115120b01020303060f03100509240c090f030c030607050d0c2a0c0b03010b12060603101a09041104081c0512041104020304150b 67
    0xc0c0e50003001401c21428600108a403607004041d1412115400700095440f5a11a00062604402080c8940000301191a001c440c40030a116200d507800d0180c2c01b641ca55a5254140304280603a803020681502c1003881d107078003c2c0400c3c8100343c00fc42c80301c00607040221020504e00500e400c15070b10720780e99289401c14001c05c00031010403500740c564240c034040c01340d541c0c0c400020f081c011546500d03038050054200b080b0526034090000d04809040c06410484c00e2000c80f0b04075890307a49030142000050006035001d120303020100003c56400e01c524143c0012070f8076602d1380707a0039400a900050030a0004103800b0307418592202420780c030200036035441e4110720f04641d038107901c04070601c900040c80518907204514410b000085507041d120142c0141b049035060040b40c030090707203d4801e060307a5024203602c111920781d188000b44010384681d034800e401c2001500720101d00010103001102d0400080b03452203180e40795400554403a5000b1440c0307000102400038120141c60825200b81c4c4a880411410f050 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 532149388 1250 532148138 532148153
    0x50a180b120a030f050706180201090801110d02090a150206041a07020d2a03050c10020a05030c0306060d090503030402310b0a030f0f051014071101090605091513 71
    0x80d00c076007515101c40c8640b43d0080a81e824402e4000290487d400c081201d085131503000d903006080342c400c0e603400c10f0590352400203908907000c1459641c140e403010407001005485035005000b0058004020300421940c0d20a40340302c0070107400508025800c00000c100c103120580030700e11a0354003c0e4483e19418134203200001d498840c030246000c240801c141d096a10404480c01c914802030040201e42170f4014203090207005500400c8190405129241c8070a035080c03034500030345800700d10302c4c0c6401d0b04640382c60030700002a400041100380c00c210184072401c81c40b10640503000a0502510203156a0304007030040c4001d0000c51003010b0925164004440007a403070109100c460f403c043da20000c0c451813180c0015091070503540c8080c00048072010a0800c0c000b50241c2c02804a20401c11940401540d803810429144060314045413499050001031429000d044400403214100b0f0000440b0f1a5036620302c8126102603072628415400507212030301f100070308549507400030441010104044240e584210 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 532150638 1250 532149388 532149403
    0xb030a080f03100510020703060f0b151c231e0a02180901260705010906030c021036080d180b0103050309040c0f0225050a180b12 57
    0x20390781e94000006011407143c002244043c0a0040c8086400d01911034004c0da920382030300042e5421407620045800000c90340c400c070381a0500103031081141d04841e030080c00b210303080ba452000f1070715008201032600440e28490340001107007500041c0c01040c107202e41805e000300300400078050449100907130145601064680c5038404c10342d590259a0780081d00312600d618445410035178101d40d03481e00114404013400750941c8140403070040765810340204120a40c0d1050715200c0d02e8003013032040c0c4042c0030a0344260442410181a4011109100d00384c5070100c048481000c1051340072080c451a040c2810040071001c80d25009042241c0880401516001c07103d1188000d03503401d0703541d07030325030303140c031010850501e201158100c50b44004a40c2c3d80c2c14429107075406806503071705c030707602c1c00c01d400c00442d000d1103111b01003406a40c010152003200d540c8054001e01c06184007000a041c0c00c0001480c1d03603800512101030480030f0801c204440300c0724014001d03a240c035a40369204444075000111110310004405 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 532151888 1250 532150638 532150657
    0xc0b0c1b0102030f18160909050f15043c0b15010909020a02010b030604210908060a0e120c070816080a0f0f0f060b0102070602010203010f0b070204021210090b030a08 73
    0x40c0082d05c2e420b200c21320705000c01449685c041071180000510b201640c0c410320205004109641030101d01140c1d40b5202c030141c000e400044e800e0f84010501140d146840301d11399048400400404020028040040000249e45010000d60902d80741c0c0401000000382a04461840040c2c1100f025420001c2c010078640d0003280011360340070682c8640140700f5003021804100203401e03141907040130b007000502a401c1c03101c203480c4190840d000d00e0781141310b0203004044419400240c50542c48403c2610050085078a2983e070502c941d00c03407000d02509a400511498403000018034844c0d2400d00031a09181d10016401e2000120407420440c0c15808500500500d0f804001c00b804041c1c10300c2d0002d129030160b0f101400807104405d540040090a80c070555107444240c00711035240d951141c04900b030344401d019441102455200400c003000c080c0c000f07000c3c4144001c101508254951070340c048036403021102200c1300c080c0f801040142c0701c0030784202d90714200141c0151074000b0380750b06c2c0c0018034419140d12 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 532153138 1250 532151888 532151911
    0x2040e1612021303080705030f1c0b0f0f060d0b10170a090c060807091d0601020f0d0f0c020d02120717150705031f080d1106010e0103020904030c0b0c1b0102030f 71
    0x45d2400c0060508c03c0b200d480207141e000d1a10740c0307003084c20441c0700266004406146841c2a4404d2454500500f0316004145c0080c4289c0d2041c0302d1009000700d030707001001540c0c1346a44a0082680036520120f04c5001d420051b0f07500b14800d213500034001511030f030141200c07264928101003100880c3d550700d00441900c00609040da410780b1048400c98190255500411400d40350b40e0040220802d900c42c000d010f104240d0848807010180c80110386c840115100c8003002c151450031507a8030724002c1490705006800240301c0c92490800c0e4001c9001c90f0451100c59601c4c0d0041c06041c89407000e0145c081500641c04001440400350000100300d000d030002d0b01d046d042c4500400015440001e4100031903c151900705101d925559070401d207903a852420710520b01142c4051541841094001043d6040b40d03210345459a0991171a001d002c185103018109804021040c24070b00302003440201024043c1d2004251070390349642c00e0714a9030590901c0b8a015213540d004206024104500019176034104900044 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 532154388 1250 532153138 532153147
    0x1914060d080f0708040626010512011418010e060f07050d110705070603060b0f09131407090e060d11150405030d0e090c0702090703020d02040e161202130308 69
    0x5240d2818060824400d6000b580010907408016088000d04215035494032009400d1443e4041444400c000c0d0300e06020894010004011510b8482c1c01c81040c99440c03400044d0281c05030303903442c4015904640c0164020142ea011915140d0240308040400031420090042406c00358540701c0c040b40041c0000003040300205d100000c1c2c0f000c99100016030035900740c030a42d60b0541407800c6910303241184200d00129140100009645541604032003100b000385100c1850904c092003001810009040c4014000e60b4940603031800380440041140101031503224100d89038030302a1140c403c100000c103514010031000c0866800900442c07101800c11b8400c6030100380442500782c181250b4060b961200381e06120b0011070503186500043c3c2140040c90075142100555221911003844c0e00c21003500a4001c0c0c55000086c030494030913030142c9582e01c2c1e920360151910b035640102d28542c19040d10304c1c094081d681c1d071200d40c00e680c100500803000c4295550075070402040f00140f001240072031101604099000a = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 532155638 1250 532154388 532154393
    0x708150a0506011701090c0305060f0f0d062c010f180b070c05030427060b09190f03030302040819051207060915060510080402060f0c010905010e01051914060d 70
    0x1565184090b281419015542c6d54a41e5500903150108000c404a4038240114205e1b0070850058200e0a0b00581015002e4150342c085c84a045858601683d002d90340d80085100d409c0000d5001c40c1700002c81402d0015880c0400c06203085440c100081e440c02481c010980301e0554640d0310303000704203030055115149660781c28826220b000e00380c0c0006101d40800507011a07541c041d40c101e07140200049144038134401c600038110044401c18080d2203003c00003804409158074000303c0c5220700542135200c40e4581c80e03441c001c8003c28070643e04103c020a4000c50140400070b001c04c2070302c00c1f50344040105000345c00c10385ca90580326013030154204980040000c0c24802c0c0413040d0082445e080e800b0505121740070605035464010920b6000e418460b80c2c2d45074980622078444c0e8481401030350001c0c030304d51403c40081c501801c2a80224820303000c0e0354a900d65240070500c01c1c072920b62103070400000842e603440c0c01e500720b0001003091004200040d20b807140d0020000b10041201c1d5000c04280da0707200c041e0000c5d0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 532156888 1250 532155638 532155647
    0x11090c0414131407050a0306050f0604150c080a03050f1e040605070201092003060115020c04050a0b040e060a0513031b02030c0a06050a080f060603150604080109060204080708150a050601 82
    0x1140c40080f00c0c2030b040c03060791540700004004803084e596040000c02d80321401c110203515855407143d40104148010b1001910384082c8d400c0080c3c45042000460750181e40c1c42c0d0417a008801d0034404682c5e0750080221940044203401d5004507200c50724070712140d00b40c8134000f0000300a000581511f81c0c0e50005040319001350b21421005411a29040c0a4030300d18500c1621a041100f0460103800340800000d07403043e2001c88044910340da41c01a203c00885a8103002c010a401025492040d841d130014982c55241e03803046461140c01100a008149001c1c084442948c4c03000e0b00000302c08a4501c124408250312540f94400303488250319648800e0f0a9000081c9001e1740701125a83c0034550000000304143c01a00801d24914181c441840c5581e807101d448004000480c0c42942240d002c10005c0d6942d0351015401c5050039000300035070308158030b410015084982071a011200719500150a00c50742c401004a10f000b071000d04024040c5000540c00c0140a201c0034013032030301c020303140d4001c2030031a07025 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 532158138 1250 532156888 532156901
    0xa0e030c0d11040c02060c12040f02040f1b050a050d09141f0b04060302300318120109021c0503120a020a030e010621050705090411090c041413 63
    0x40c100000c140d110b05141e241e0102e0100e505100380d1910000c2d42400d4008036000c0c0c40707001c0d0310707030311504118810f070b4110008007000300103c40d50003c902154005070f40c1c0344500080c80148250008a210400d95000009050380c060003051103070a0005828507a4000d04807042011011300116002c006490301c40700c00c00000c8001c0c040c6005590031400140c40c42c021030201030b03000050900540c1c1c685030a0200321100c0e4000a504444400000d100705483e80710049410181c525804030300b01c0c045c0801c60304607004280c0b404050307080c59100c00c0d11071901c0b0715200910850718000304940c1c01d1941c00a603282072089034860860314a0070409040c0b100a00a8518541003520803030345506d4211130990080d8000450240882d01e0131000b1820500705100344419070f101c41c0c0c2078000345014000310b1104104070050071a500d1040c800007281e1501d5916045001b01e00c14902400f03010410010000c5c0800e0081c100138014400340020060324004030140e501650060781e40d1b5101c00318030510f00016040 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 532159388 1250 532158138 532158163
    0x302090f06060f1b0a11090109110904091a0a2c10050603160303020c013f060801180b1609091515090509180309060a03090c06020f06010e0702030a0e03 67
    0xa62a200310030701103c40d41c09002050201c442e1f101c1c03603881e002c2500444400d07107202206244248031004550038185e01062507980503d00700301c0c00310402014078800c03100807164080700584900d4540885c10032041c081c580141210302d08018100310004c07491350b4504080000c2c07001901e03480071414a0300e00b4030100c00702464803400016140d440c2c0c2001b80d0b8605510511074000303104a19000c0340c00141d244142c0c1c113044920048184007400626004007060701f2a18000d40c59a110030025224409200714048000362215092511701542001c0e024810014050580145502d10ba1102540d102d0984030a40e50421000210500700810030000b01d2002d0f0006c004448080d5040d1220903007241c2144111f580495240c0c213113558017442d2a5040316030703082e50602503200f884003c40341d103800c4003e00401d405030b250008501c0c0c1139454400d0090350550001d000740e0059002c030100240d0500c03815002d0296050350342050300f07002000a42c0ca01c01c0326149010068440d1030008031359010301c4050090035 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 532160638 1250 532159388 532159393
    0x602120904270507050102070b070f02040506281404021201150c0b0702010e0d020c0607030806041808180301051e1801060b040501022401120f1b0302090f06060f1b 72
    0x5420b40341c80b40d6184032078045c0c140036106105001510001c04c00413904003aa011000048006055090002a080142c410ba51060801922411018840201a03511342c0300a44032004289810800c00f0400c42248a003401a4010810310144140c4006640e0440b900c00318401c2d003030400d86004640542c02c0720170042c5040180020b1116290341504490107180b6a40c040d00c0c40d00e10282016a501c1e04062011604032800b4450f11000c40d00508070ba03503020740c004e040440e007003402440e04002d00c4500482243c2c02c1e040410007501082410440c0c8a55480c00d600070491420106488010042e8071032100018044000c0000c0405504000d001c0c00b0940c1c1000030310206444105500319a0014050140148168683e00152405455400f581e8411080341c1d0222a400c00c100150181d8551070180c0300308014400309070008100700008440000507942c41d8040174290304c100211008060038860b0104120340a1108a07501c65040362001c800304c0d88032907699001201d00145200303815a0101160 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 532161888 1250 532160638 532160711
    0x6154308032e081507020607211b0809030a0507080904020c07030c0501020f1606030903090e070e0906010302071524031a2401030213051c0c0602120904 67
    0x244202160841503402d01003d51303003842c1409030301c94901d490444050f001603101e000400c0c01d8900814642e6140440c1c852060502010b80c2e00e05c07020b40341c14054920000b80c0080c1e51540440d07000c50107540121044002d14504101618018000d0141c00700c0901604070003d6149a640c1d0b0fa50304a8032801c02e05800e42d04201da4905014245070414407034140540140c0d07201c2e2180c0c02011954900101e07084510704540c0d4207000c4120000d1910400440600c05e40140c040307281111103480500c80c154541d138504600e826031060064280c07021381140d0601d8014040b080014044400400c440030303440200140303220a000350342010f0a80a0500240300f031031050044288240d4291080210070343c51141c5500e9100c003003d81e0074402c02c061003001200e0070852100b00c1984240c00821041d00f040740e0b407503401070319030001036281120039443c450b003200c0300c0c83c5810410000c0b07562080100030038009050320300a4004400854071801c032032203209070b80d903007151041c0032595100c0300c00d610b00510a0a001 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 532163138 1250 532161888 532161961
    0x8060d050105181b010c1b1a0a0314010308090d0503090d03030b03010b010804050706120f0e0c09060a060c06020906040b0f0a09210305030615430803 66
    0xf962450410140ba8000e0305081c0d1440d1071104040d080c5070030306944000d41c0c80303820384958101114000300c50300c074513030b243d07900041c1e880c44050b0100012501d458a0340d910b184000c0054203d41c014107071401d04000d01c0004001055080007a1148858151401e203082502072910900358450b02c0d2101e0352046002d0400d000345507040c0e01400103024154000c01c04503003058015140e1000490b00100396a0051a060010920600140d04c00c1e031800980800c0000d0700b0441c030300c156060710075034560300c3e030008000f040c035407500c4c0704030580000e4240c61b81e041e002d0a0480c001c00529175401e026143c550000743c1031485840304004c0300d0040030003020b0162210b0710021208403551141c0900d80c0040c0c84040085140f200754404103c81242c0344aa1600200701e5550075101c682005250340d40c0480c100307000c2c805080840b00180340d5031081c1820f2101c00203003404248074042d524110782441d584075520f484880f0328030a0f084074225420036541510313640c81300c100034013090509400d040442c0359003254016 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 532164388 1250 532163138 532163161
    0x103200a05030f160503030922182103110a0f09080a060207140c01080406050402210d03060b0c101107080d050118020c070e071403090d030b03070e0708060d050105 72
    0x1143e00d0000c40440c049079445c02016528092000d03007580c050003041c20183c0420100e0064200072004c5d06011800e4440d40f0f2900b181c040361410203440017200c15403c5009070255000c0c030246041c403810300704061400380c07100115900030350700c075032003809901e0741049611801042900010060a02250044a50b88c40c01001940040f00201e5003004003440000040c04d01090403080c0c6c040694884c181396495480d41d0b4003602e00a08240d81002000200c54450f15020200f0250f40c542c807170091511f4041d4010040c100c0354a5406050b065400307002801c41e484001c60002c40d01d08156602203442c0c04442c25144c8144121003008000300000114404800c41070b412240c12502c0040708094014030001d00102644501c40030404035411621046c0421006814841e81084840c17070000d040707021080e01c40c68994025110700c00c06a100100450031990305000d088102030058025000c86480d02d4044004080082c10142c180510b0100041e015150250701d00341d80e80e0410300a000b542000c0c0a481c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 532165638 1250 532164388 532164403
    0x201080603280c060804150f0902041a090907060804080c010b03030d0c0807030c05070b07090503030f0304020f060f030a0c1b031805010e1c0f02032b03050103200a05030f 75
    0x40f43c1800c40c0710b0000d4041d000c2c4800e0b074400c50300724040481c5221803201c420010304030b0200032040c40d981c0d9811200581c0766449001034880040c00024007100511042000181008120f540715520541d0180400b6601000c0c0c5500503a00000703158850a04404c82c501401075100e201d81c05100c0413540123a4003c150b00002d64a01440e00c46407230343c0e241c1c08000c800362209501440081041001090009144040700a078015a00e142c04900340f500c91000904543c00b6542400d86804040140801d52a015105048042c000c0314171911700502c52034014400d02004110f248110340d5009003020643c0101c1808900005040018243c2c0f209407401030042211040d61610040d910000480d407540540c040c421619402000b040e440b02d01c80000e2980da407941c160032620421030b00d03414001a01c00300000c4410706052103480d81007036110b402002c60f01210402840c10141040010804540011900c8031100070595100d10050203040c040f46008009600140d054481c0f00c0b5826840b480124072403 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 532166888 1250 532165638 532165643
    0x9010c060f14011d070f0f030e030d020d0e03090f1002070b0406120c0f0e060702030c04050405030c06090a030801060809210408010608010e030a050912011803080f13020108060328 79
    0x100070b50801ea5004d82500011a002d60225865138910260031b40189980d000c4d40c4070b28540481e9211365070100e142960000c4d5500b4948580100d41804900085d00030f030450441c1d0007000310304000d0b4403000030300308030201c60245009510221a40c9817481c405e12806002c0e181c0074038420fa4039030b03407132034001c00b000219034010b40d9851403d604c101e004c1d031290a64042181c111390716007000c45125010800039038030480742240d0512822940b4021921240145803003240980d01860311218040103460420a00401c0340f03c0a400803141000000d821008181c1540d83c0317450110b039241e60f100219482d0652110242da80c101d800a10800724010080c0100161800100248411036a80b29902c3c240c89802c29005010b1b001440980b950521400141c8000c01009041651b04100090210b0869103020034035896003003014440f00038180c0125030650407003000301600303400d450300b001d01c44184200070304002e040102903408a55141c0d4104800e10700702c61a07982c0e401c40542801c2c803890031184843d80c05c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 532168138 1250 532166888 532166909
    0x30b27190506010c080a051e040608060919180212010617070815060103090c06050d0605010e1f0e060d140a0203090607051c021219050c09010c060f1401 67
    0x40c001011890003818020740301a1580c0b000c1c4040c3d50350704030054210114003010048180308a0080b003421502c0c03000141d490900203642c1e81c0c14828010400900100064043c02c904002d005a0110440c055103030300c91800c00000302e032490807241260118409801a6000ca000c484600034940d06501c200215005039034000d066000104074240c803440f41d88581e00c6150400700c0c1c82c0680c800c07171040d1607901000514000450700100d56401401e42c0700e6400600002d0004030f801c01d109045840b401c006030009080101d030441a200001e400440d44502018412b00446032404605004848450781c0000080049455642c807080c040d0060001d6200d051100040e0030104000401a00c04c580c0102c480001805c050358449c581503406500c24514a005244203011100b1801d07040d04c081c04420030f64110b010700c80d0400c900c0203200c0808840d00f800c110752508060150310719101c4122401e50100382040d50100d0041e04040e001000300581104005091004c4a003001d940144554141c4400021 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 532169388 1250 532168138 532168171
    0xb0a1b060e0c012303090c0a29040317210901020a0206010b070210231209010509011a10050d05070807120902030c061c06080d0e150a030b27 62
    0x4490403651300062503101c5200d9010034485001c1320340115880b1003064100c8801185c00d001203610100c0990000f0381c0d910750280348413130320341c2d4403e8900908208101c9550070282103441d072044402e6400b051a20303074400020075540011404240341928281c414842d5001d283c820202c2e4080c0d4001020034005000d60070000c034025200005036060b558001c3c1005120012610003503680f5881da5400b58125101c005c44421160f550000601c1071a0b01d46c0360010581c2441c00006080d100050305a002e1641000c19190201500032441d02514000722524080c221003020242e034644540241c03d01d202e03040604102e40d0540181205001c0e040d66900e80101c0903480000000b01c42d080c0c040294907070465081140c03546000009003864031800400c04020143c030400180480701640d0101805401101c003d103042c03034204c0b0908060321825141c0e4031003250140340200e100c2c400e0864020030706030f83e07800306820784e111362484803040403080c0a1403580e4403050515410301c0c002104e06001d02c001040 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 532170638 1250 532169388 532169413
    0x90605100320030709590604090606030614061801180b1903140f03092709060f060402070b13050115030c05030607020c0a0b0a1b060e 59
    0x2c9034594202244030000c202e603088106440c0143d2000e8100401c10900c8200469030b003c2c0c802d00500040248400020301c10000f401c14400380400c10703a2801440340d90400700d800c2d0f85882c00200d42610b5848282101503a85030001001030400e500041c01d214030703209000c410421142c1c031a03c03800b144860815030640d503c80030410400a041c0ba00720503074100b01c1c01003001c174603000c0030f42c500d111802c6004108044801c01046803107161911359401e411000401300184400c1c11410f02180c0062009080c0044100a0040c0d8034881c1700c5a20340540c400000a800d0b449d43c20000340c45500030201004170501b0039081465807180e0a541808a50002e0b5001c03c101d403525201300c0c2c41065025041ca0150b65895034955625003030101d099400f952510107000740d16180614280103144900111036220781004241450000000c10410075540400da00c101e15560381020003003150207180450381d8411054100311088248001080300d160110241c4d0404c20184d43c000a1156244000b200e40881444 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 532171888 1250 532170638 532170641
    0x1020301081e0102121e070f0e0d02061201081606090e04030c1a10060206090606030c090a090516050f0307210204060e092805030a05220906051003 65
    0x28880c900c0e03254000c40101d48185140d09269000a644074001424034520010404529108846d2841410445280d07100d2150038950311030f41200c00f81c42c2908004c00b12441c0584003020081600d80303c0c0710480c000340c2c01c540d16070040766a0006011514000b5580d550049a45d50f181a1f03000240050820401300300248a0780300c03541190030522400c0d12540b180c0d1401d0b1050303c81a001034920284040e441c040c5d24480c2c400990040300c055030026201171602e04020306000024040109a4020340c0620a29540020300b150b1a00303802c580d09007035512895810340c014a001034000303043e4001e020190154512450380c406c01c0300c2007a1054030b8005003110416444031a240503420380c1420311070007540541070108101c2c1c0c01c503201810000b8840d49030155026271020031940d00c6980da0000c0e1143d65280702c4007040b2001c00d52003840d50000c50341c031591080e44038014114050100300c00441c8001d428a01804c0c82440c9088000e06c5a0010303880d406840c0c081c05072401003900079860034014505080c4030303 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 532173138 1250 532171888 532171891
    0x40c0e0319050d08060111010603050d0909090503040510050c0105070801051f021c030204031a0a2412022106040605010602031201051302090a170106050402071e21020609060108010203 81
    0xb00001c0c102c55181200c0aa8410001400250402c0b04c0c0d010782e4040f049007482070b03502850242c001044150721444006002d901550007050001742848250700c00210008190307016508112803452200c461900e080b2102d018098000c525503080c481030002507038121042605030380083d594100b4120305034441c0c2c030071400d0b02148040181e010785514540c00d0202c40511955500c24a070240c60907903a40c98410300900d002d481404201900e505026031004184900e0401003020030300c00e6180d5001901322415a5840d101d030b4410758003000b14050031541c5800c0401c0a18911a601c94542c4030080d0a080c1d88240465081f02d10514200020504600000682d41d207810080c034242c40683c28042480640450802000041c9409200317216117541d0b5800000b01908030781c0d41c0c1d84048051840114250380e80b0364003290144d0b104102d00c0010852912242c0c1c5030802e055407d80300304030149002031000112803d42605611000d100200c105e0b40850740c035004150401c1202c8869072902c2030343c0c0c200d100 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 532174388 1250 532173138 532173143
    0x170402090a05091f06080601080703021f1b0308150307150e0d0501021603021603030509010809101a0a0915030b04050c0a03031205100303210209040c0e0319 69
    0x104800640030705102c2c0c204540c041d0004098a816111240710400702e5480099800492926090184002c0004005050042c0609401408503604d541c02190105a0500301e029484001400948074107001d00c0350348101c41810601e818140d840360500600201c015071f0001a155922600f002c550328001a0704d10035110318401c1c081109044200c25215240480c19513600022444c5520340451020320103440e002c1c8020544441c0001c90f4a030080c01c004507e40c0c14202070301424411700129a014003a1030004c1001c0c00c20000648030700e240740b0300e007a103080c02d6500040c0c140010b464803400e144285141e2001d00795500c80c051910390328000c0545420310039080e0b0000c8401003c00c00b00f500f06c203080d03030403038060425108400205400700d0b1018659810580c04105101c031b1607130030700400d4440c0c02c1e88801508460b00c0194155903009040c1c9840011035041141d0f00601542c024031694110b581502005000304004911407402405e0b0036462240f451180c0241c000440d0214102210903004c5a0b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 532175638 1250 532174388 532174399
    0xd0219030209030d03090b190b042408030705060f09010209091005040e03040302150918091501090e06041b05092e03050c09040c0803210709050d080903010b060409050403170402 78
    0x5480c180e154002c01c81ca40042380c0c0381c640b500d000300d00d07945451141a0381515940350b848140424002aa07150b00243d43c0140e519a0007042100041800072407903603001030741c6603803071a11503e07902d4181c1d001e400f0312040c09610000c0141404580300c60001c50408840c000d4406110b40c490b080b24054485c0200d120181d04882d0200d1420b05a04409006042021000f0b002c250504444c1c0c0021190700302c1211488104c0d841250041f005130140d0480e14014080103000b41703c2c600400d405203881d40e201030710080100034032800a0800540c0620070034003402d8040c01103090740c9800c05c00c072042c403401060f202c0c1524514901303081c14040070b1030055098a0300070307000b1301c0c1040c1c0c50340920000e104d004005071090000450b020500da141400180084541412a0300340341d910f40e10b00c18100407029161a05100340e16070100020f4603420030001c152171300580ba040d100c01602c0d020074090540c204e0002e51089001a0100c2c1c82046988064002d50080d5595000b07100c0d00d44100c0549002074401940c081e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 532176888 1250 532175638 532175641
    0x70e0d1b090b0f011223040302030304150207030c030e01030e011103010f060c05060708040609020a09090b060f100315090606050c010501060804020d02061c0f0911100507080d0219030209030d03090b 87
    0x40c2c403903040200e00500c0501b05006a031000684003405c100c0c00c0e00d045006800020602040c0015500c0d40500e020301701e0350451a04005035400b41035048032003401000d00ca203481520190341c2c007951282190020000091000c04805c000080c41d9a2007400303001c03984060600c000c29002c1c440c4c402a07142c02e61107030040071903445c2e08505503503240009104454064440c0110401130302d5070b02844d001440d0552001c0360a000f24a404200304000038403050050a6001c00d0b01010b507141a81c2e403442da0388500300045c4c41502d1641000e00300d4004d800c011030403800c1a000044543c0c0c060018042520410002c0040380d0700c50074125518501a00d0180d80000c107008040007501d410f078014a0724515803562076117600d448030013280c01c0d0781e00035040300300140d51401403806010075102e00c010010f03411113200c01c01c1c05400300003034958000c4c9107000d419074001045040406000307504907000500d280d5181001e1050180008000e580160030407070290003140c00b4103851074002d004201039203134080410b503050b = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 532178138 1250 532176888 532176917
    0x30c03030c0d020705030d0b01030b12280f11090a0b0f01030e01150b192607111006090f0b010f1409190807080307030206070e0d1b090b0f01 62
    0x66080b840d25010140d50811079031000a1041006221079890b502000c10414031245c00942198071041c100d40c003c0909a11010441d5008145601d101d9000301d41100201150482d185848441c48030007444c040a8040078421f10514084082e000e00c401c0b21800a103954882d078180648a03845140764011904400444031507000313400047c2400f07403040001400c00b000e4110316440e4001c40c0e20034800240001088500310040c0e5407241c0c040d0903942450389140c10712800d240d001c010503048224006c1c1003c0701065070036101c1d41d80e40d00a227490f041100c1c03403407141c4518400142002e08c103030015a894200c04a894440b140142180400140c445040000400e40305413280c0075682c84001d0391700300411081c0b006669600042c004145080000f803003083c00c140100749050b580350014005a4000e028070784c006580019400d80c05042c6240c039894170051640414042c880e003660080c5000c40b941d220031b85c1b0300313001002c001c200c4041e0785081c40501240030030700000e4507038161034034000b9020720145001d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 532179388 1250 532178138 532178161
    0x100225170d0e03030f01060905031506060d11040e0a0b040e100911040908070c060318141e0a0c050906060a03051b0a0c0b15061b1c0309050f030c0303 66
    0xa01030410307008a0421201d048a81c03d40d801100c201480e5401c0710010300082c1d61040c0000060f05040d0001c00681401d401000c088501c02020740e446100002011490422140c11881032000c200f10450344460b115601141c60a004a03413a0013038500d03102e500301c1c4a2400d40501032105941c40c014101100103c0010405009680b1043c0c400c00c0710f8400c8001c954035188107841401d4000e44920b61036041d54a483d02c0c1411440e480070003058200008204500c40c4001100c5040e41c0c0304a148100a824034860360034299907050b2403860094040f011000380780049288c1e030580b40301d039000141c4107071120100502315100399001c5802c00b00500444c24032601941c0016040007103248044807400005000304880d0f400301d054100020311140b40b50342003103841249a03400807200180c84e821005c00101181080c0150541c41c102c000b180c0c400451585c50900119000c040481908000011282c201074082c10b16800100c56038800e46c44084801000030068a4084c40001f000e1851600c2c0e0100818 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 532180638 1250 532179388 532179397
    0x30f23030105011d031207060f0209060306060c0c041515020a030e2b0302010c08010602070b0a0318061d100902030309010804051006060f031d0d1d0310022517 70
    0x10544c0080402004180c0d02000204440c240d4500c40654401c190328010701a0b600320032000b8102401840312001e503503030710000d5a91220b400da5206440e00303061840e0620f40740300a032005400503c1c3c001512000c04004240c00d041d107800852100303901e407a14500320390700c140049019001982b080c0b2017040511f0404204900e4041702c00500000c40700f1984d014040d07074180c0b541140075030b5440c42c20244e41a081b45903e4014041c900107064210718088444c03040c2e1280300d18a208159507400c001b0202c203840004108016000a020003070804c0c403400500581c2810707802d901031840340100d00900e8119a0040e002c0140c7e0150185040050b43c400550700484007070800c8070540a9105106030300e0030244182001004540c0c0d418820014100c2c0107002c40301503041946c080a910b408401f00383d4000910101c49046030314007a20f8241d11800d400d543e820030040c03950380c035001d4944400c880c1e1201d81c014180e03440c2c8400f0000b4441c14800030040302e0003e821001000d1445040d00c1407101c0501c0310151 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 532181888 1250 532180638 532180667
    0x6100e0a0b03011a0a05090708011505311215020703020a051005150603040f170f0f03060405070503090a08071a01090c09050907090b07021c030f2303010501 69
    0x1c80c92070301c1c1d50002030075502c02681860820180b4410880586840320310100101001d40c2c0510060501410051007400705000710609001b00b0600c02d00f01c0d81c0700f2002c407070f60581280400700c0d010520882e0002e4a490303800c1075429040702448040340000c3d41241d01b404d240d034400740180c0d003540c0c840e20750070294128aa0540075402035085041c0860300a2001d00184440040c0000e01850700c8410b0940c990b100b4603200e40100c0b01403003084001001d40011510064010401c0403408a100807509194810000100c0e015640451200309144003580070314007504c4120b40502150b41c40d43c00c03c480c2ea01048034120820380c0054070307900214903048002c0c09564020240c03291130060200c4105000c820a0384044441d035960302c4c0b0300b07009030b910580c0c020107040d044800304642d003000c1000070011091401051004c2d0000980b44085503145461000e6500b80142c00781c48000890401400104419101318080f410b0035814502c030045003102000202e075000b041d41e046900741401102c5050124000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 532183138 1250 532181888 532181891
    0x50c09060a0c020a03060507120c0903080306060d060308040801090606080102031b0307090b030c030a0b0108160e061209011409010204030201020327041e15210201050403060c050d0e06100e0a 84
    0x1c070106d802e03401520310414660701c6980460a00c50b10420881d0b02010a48042102e20282030000582c030a040b22740002d000c481494560500507501c9004213000e0b40020903009000a00103103008041d084400c00d140607200800c449076440e0300c818241d00c0103c03000011001910701c8007910341840f801542c1c000720b0b503140900c0b00e180c844500001c1503100740c4101c03080c40c4000c810043c1c04082c5001c2c181680e003080c41c0c101e0541c10207000445252081110017002c1c4482c80c443d8140c0c98860000390f132a0180c0c2e2103516103c13801c01004050003040c0420401401d90701c80c400191381c00005000312800c40782e0690055140c501e544043c0780900f2500302c5040043e4000c8044100039590b5030003041200100c0e00340041005807660194022108083d440800581036a0420051002000603010140c0c554262054000d88180f004940314030503508000c0810346080014002c65038080050240010f0212040000d00700d5440c1066070349800702e604490a2210b2802030183c0e900c48100b0360b03000008540c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 532184388 1250 532183138 532183159
    0x1e0501050c071827031202032a0d0c020a0308041e021011060a1401030b130b010f0806131e030e060c0a021e130c09050a060806010201050c09060a0c02 66
    0xb450400e00c8005241d03465140d40380c2d59040003904139952806060b50500c4100205030400d0360700905020184d60003130f4411580800000c103841c1c0e001c62414143c0019104031000c40003082c49419042d040044d80074505441c109000f035420780005400c1040a4058032261a1a0781c0e07940c1d44c1601c591302c04144001050f0040380d00b00162154070320192070901c181c40d82e0300755010040c1c01c18500340300180f20140030340c100301014401510108030941502d400c144e5400c060b070b0329042440801010342c01e0007000c40c94130400002c0d5191401e42c0721000d440205068403400d458203000da81809000a901404800180c0c81d40031040450030300e650000ca1107810b041109100344400a10760fa00407107000b2100f0381003514180118a4420441110043c100c00102007450b240720118545100c10088a000c41d40e80d82405489507002c3d0440710000d010040103001142e44a01c4020520081030390000d02641c00d201c08604d91204181c00d840c0c2d00031028210b10300700340d541f03c0b0440380c145882400340c6c1c0200702d130b00 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 532185638 1250 532184388 532184399
    0x150b030c0319060506040e0604091b0e090312070e0307050a090e2b0c0305160f031803050d0e06120c040303270513180303151e0501050c07 61
    0x502440c4120060310009890b8600229401c40364074001c0040d5111520b4800140260303600d8501792001d030785c80d400a281143c4e654002140040084107009006941d0200c0305900080f90540a50142d941190301a040c948411105035500c2c09503469081255540800141a803840b4290356a400c040081c03c030ac01d21036a84010410001c1d00e80c07c107010094a0b0f84400781c0c2c035103040200610302040100d041c040001108085460b80092200510030403840c00e001d5000c2c18412015101882c144040080da20185890321540a043e520300450100c4d0303030200d4482080d1442c4510350116038000c009042c1150400d10f0481d51042101c146d254005424045800d50110621826100d40d0300056100da881d0704504029005c19802d200b10302d041009040c9680121200c026064104c50040e0740e038096244581c50400040d1160300f81c00160100202078170310606616411948691700507207d4a0020354541c008000108141040040702610806c800c00855216200400d4218004400e403001c627a1100c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 532186888 1250 532185638 532185659
    0xc0307020409060203090d020a05060408090a090e0102090f01081905130b01030c03110a0303050405060a1b0f06050108030414190806191d0a1128030c050103050906040615 75
    0x21a000d0b81d0a0394048208106c0040c10010f40c252019540000d100e1291039a4545c1c1ea159030003000202401340120f601f202030385690000034080c18039160f09000c0d0454010029000707400848005102d403203883e800d41e245501515225024070900703c3e40412481003201c1c0e5002400002d44401540c20a00c05010081603103c0d014034040c42c41104000c4880c1d1945c18801c103030fa40d210b194648500008082000000c4d000b40854044502c1030310210f448004c9010305580c090810150f15086c0b58840d4800000c010101d420020001d109400401c41e80e40c80780801540c034091401140700710310344102c4a62140c0303003810200300c0d01d100780d5049070045034079144018100002900c0c03412811554400044410100b0300a00840c22800c4150202004803100d440c0e5540700155006401414400b440500e9510381504080d0f140e1101c1942c8811003c20a6242c805550f951000781e8162042c482c0c0400c240d8428020036010b50350b90002010103441f00c1d2911802005682400c1212601c1c0003000505d0b64802c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 532188138 1250 532186888 532186901
    0xf0b2209030513080c090906130f0809040e0105060a080d020309010e1309080c1203101701090b10060e04060503061b1e07030f140d02070311010501140a061407080c03070204 76
    0x482c80a016031a8021050000140007c3c0c1855490b800803401c0100044aa4484074140c5030040900003104400c3c0c24100c1071485a600d9054006c1d044c10310134043d154054020900a06081c2c0e03402442c0d40d0b50f07600030360300d40309540b090782c0044e041008610342c198030680040a4059006001c55813000c0355081c40006c440046108031007811011485d800740369000d101e1040d8145180007040d1940c5800398030451801810300031144c0180b1000d03c041043e880940c8400719290384582107001d1400c0100104502d08107130301c9001c00089001540110340d00b03040c001c040898078090010500c58840c0b440017a0b41c200c0c0c641015000e0a810711032000708411084d0700c45080340e25608400d56941072030030000e005034001c00e2418140b0020b001a514208041d2007128060524442c0058031070803a0b02d012105002240c0503550360b50300b0403001099034a07020541c100c500d00c0c00c031011280140ea6080545042303000c0c0004200c10903083c8880d00100d04a00c004014806185040d2031400b0030645c0000c003115023 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 532189388 1250 532188138 532188149
    0x3010209030d0f14032203021f050105030d1e1b1203060f0504151814090c09010e16050a030b040c03091209230102010e0708010f0b2209030513 63
    0x1401c101d010070482e040100320202100c1081302070301c2c52900080c0b04a442009041b41820071085410010501d4400c1c02030580b405251110442860390140f00b110241c9403e02030b4512030300a101d442e05015006400440000c0c21103184d01109014044081d036941d1407030713590101465400f584540000b062610f2007140341069403070005101e41805482d00390204503400186c0500e14009120421440320b42c40708046820a035000a2810382219070080940508400000d20f244044103202003c14049002c0403409001e5841d40166aa1040c003200e00c0b641c1036580c410351903080d0002d1011188144000c0c0102a164203000c550a40844003003403c0702c001d840c541c00060f603501f0241c002c20081400702090f41040d8a080e0001c42d0a041c0c00071a0b200170070280c09078a400042ca1103180364000e4004400720484903090f02c8045545501d0140a0000c11400b0042e640c642900b4600524280b942000b0040f148842c0006032610a546200100540d050580500c041070202e1107a480c1c091000700040e04 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 532190638 1250 532189388 532189397
    0x5040e06041b0f0f240518010e0301020d0f05070206162f100606050301061710080a0302030a0e0103051005040c020c0301020f0d060f05091f091a09130b0c0903010209030d 75
    0x52809008175170b203080c0000c101c841d0400e543c101250081e80300040e1150742c0c80700740144842403000c600603201f4510b0908555055400410fa21040340401c0e480034035001c064403400d01c1a5500c042c022a141c400c1115101c00e105444103107021120720907013240b404d10000e00c81c11480400b407180c80c90100909802c5401d01903105079110901c02da80c901030000203080500703000c0e09550411a0103842c0510482c1d0010480714008005402c00b08440d0301000204040c400307480d00c840050400075100c3c2e00c0300101e440800ea00040029443d4840d1141c40d1040714445043c110007410901040054503d80e121401140700303410329814a607800b07100910310001c08103891940c176412498040243d4001e64020709025400100030880394a400c91860342c842d401d60350307488880c1e007000800d6100b83c1c03e5400145207140b4150b0310103204038650130100ca03085002ca6410100d41d0301c4171001007210811910050080502c0d030301240181c01000b0240c90282c41c0200094203062a0001203841d00310980310500004 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 532191888 1250 532190638 532190669
    0xf090307030b04050f15131703010305070501080108070609060c020303070c08031306050408030a030c02031e0915030415020c0a1506030605090d170703091a070905040e06041b0f 78
    0x80800c0054510341104000580742d2440d8a1b400d8464907a4000c08101ca005150b011070010009064416240d804100100030749030350310303401d0440e5595502e001d201e003c26188000032a2000d070004004d021911240d48104171941031400480c2c0703003031b19960101d82611040c010035000940e171502420162070140000e680b1041901a0150075807030a5000c80c0a1040401040c001c082c004012587c20041c4c50901140c121341c130010880ca188034003800d0710078481d1802c400b0281e40071004001d0070305180444203050741101c41c001c0d03120140b10036034008000202151140000c5d003881d8003d44040f005140c00e99410584549607900c04a9002040c2484140e94241c14410010756202d41d0742c1000d00e2200801042e08405c00141850850001c07001841c030300d100018501c0b074400e410030041715501c03000b10081480d4aa000f1241814195034400115000c07ca0210b1681028840c0208141000c03008000640355138941c1e4050000c10100007940303612201010802101d00c04242004001e621200d000c013 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 532193138 1250 532191888 532191893
    0x61b0d09120f03020408060c090604030804080303040507050a05030d0e0307150203120906040b0a0218100c0203101503140304030b090a11031507050a11240c0301030c0b0f090307030b04 81
    0x600c0c4010b8420070901d031050005004055000901e1a03001c9000300006a60b030725000d0015501d40142e5000070254000020085103034076020001c1e601591040d0201c50649460307004114804800c0d0003001d4040e4080381aa40a00b0b2003130440c864020ba0180c2615a540d0b10f0f0320200480c0e080c42ca11103000359000180309010b1480d034000c025404000c00b800340000e0b080560701c40ca10040f015002e04c0150381c0100c1c81292925400c60038920341d08000b080f4548040b01284090428000984242c2c031030f0044220041003003d960203000500042d00307413a01001810b41c0d8985040070300002071a800d41c84188000b00025400180c8940a120020010a0028481d1500d042c5000010300218025000605076841000050001513044a40c50810350340740e240010085486602e1441713108954800c0c00c0c80c0c40d000c998220124000140c414449000f103903640c1d510500c0074030080c807004000007400841041164450f402402e080c28905601900e8500b12078006403900c4076580041d2094400201407008 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 532194244 1106 532193138 532193147
    0xc020a20030c060a12150815071b080c03030f063d0e09240405060d081303061a040c1106063003091c05061b0d0912 51
    0x1146c0c20825501700d000d0040d10600e040f9010342d0b80701c40b0b80321484040c0644502800e40b00d05005001c2040049100d0101081c02e4801c007206102c80b406010f0240b00560280316030003400d45882c10104100130840c035501008400c0c01d0049182c04007444101b0181000e01558070404040030122741c0d20686822030385028140c0d006001e08200700c03680b00101201c695201070000181a103e10280905c0b08a030001d035011a4800301000036013000030b01c440020042840614205a04a1380c0c0790b4407641924a52401140994601c0c840e108803400d2500c6401001840b0b0b20701091100341800c0d0107915024058211401652200d401041d00384e00d8070f03031215401c0c0030b8690910340714200c801c0c500c0d1250080940c0502c0b0740da0000d2103082d0021140944940c40d904807020b4486030b1110404044e024803948500c0880c204140010078100882e403281d0031426001d11070007021003280540007007 = true := by decide +kernel

theorem cover : BRFrame.Cov 532014388 532194244 := by
  have h0 := BRFrame.cov_init 532014388
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532014388 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 532014388 ≤ n) (h2 : n < 532194244) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
