-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1388
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:43:40.721105+00:00
-- url     : https://prove2.me/submissions/e73ebdea-4801-4164-ad60-060059227b81

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 249460431 ≤ n < 249640287 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 249461681 1250 249460431 249460439
    0x406031a0f07141c060e041b03020d060e0c13020c010b0d0c050609130908030709090c0207051c0c031b05060703140306060c060f060328020d1b060e010e010306 70
    0x1140c083d100d4201e4040301c140e540c425849050342c01c4181c0c1992801050b0400c4000600f0f1000220094800c500030504900c0070000c4104494502100b804000d52004903d400d02d404a4201d0f0b008220028024044801400003440080c1d0300d80100281c41c113119400240001104800f8040c1c448899000d5850403429070300f030f42c1d42364811103040c06500e001e051f01040e544119614070f21041003d28403d10100050841818001016071040310008041440301c04001016801481071840c04100d07a80503101030303804c1c035003049140c0c0403801000048542d01c01003070340803948112104004501c50807094405030a4074101e072100038035941c40980b0400d4140f10341408240c01843c600c010740e501842e150703039035507542d00003a480340035103c001718031441900c0421884408200c1c240e8041c0100300c007100c0d60100000741d200c40c2042e20610ce1140e060b203d215510040c00c08183c0840c10510030340024420b410340750040741050071658040070018483d03801d07030390007544c20000c43c2042c03640a00c0c0030b000391414 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 249462931 1250 249461681 249461687
    0x1a041a0303030402040f060f0f0f0e0105130507090803180301200403031812060203071d0a0314031204030801031101172202060a0527011b0f020406031a0f07 69
    0x103002030300460316006e85191030f400c03035030240f4080c100310010070311169101d03100c0c5084010303070b80900c6040c0b035400b00c80429a00320b5210742e94100e071070090004807030304442c2602e1800390001610410600c5211100401c070740c41c044c4050060700c4002c400070000c1c942c14408140c03e583c4050440050710140044d402821103810003100c090300d400d41468a11410103048030380650115510851982504815610400c482d0340c005501641c816901c8004040c421807080342100251111140c0c042600c46040000840c101e80214100030000156420026024604201c40d5070448045002400103401801009032980301d1030017640c820318001446078040c1308481e00d840070181400003041c204c020300d02c14600c10020b140c900c056019051513147c2d44002409022a0060b040103542e044074a800704200408044103035548100595a03031584903510200940800d40c0d41200340c460405100c444005070b01c030350161200441c82450300b4054081207000d2501000c10140401e001d1111500c02d00001740c1e8 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 249464181 1250 249462931 249462937
    0xd0e1c08041e080a051804050c04050d0602040b030103050303270d1d10021b2403040317090309100c0323040306050c18030d12050c0d1a041a0303 64
    0x90300c01c0c840810301c1d80191440b5410052040010a241030015910001307551150240c010b4000050000301c0204003031080200b0f81c0c6084420485003001400100702d10b04d8104e0600000790f0185100601c0e2a441d43d041c186907910980066546520000500032031441444500409543c01c8080700f050900d190543c1d40c841090344d0450040100d00121851720300e200030306001c081800140307103144d5035442000207521008480604c480385100070300c141a95040545c2100d00700c0d1450102c24002c910112031101407500040c0055003003003000d500c54000e101d0000c464a001d00581c000440e100c07200c031403c10180032a48110300003040784003d951300019403c29003450300c0c0d005421543c000d0321440d502c01e62181c00380d50f001500c210705180901154405141c02046407085905090111195400605545054243c0e1500000d5240d1001383c502807401d9000701e401020006c009450004420004020350721984d500840300914840d000e031075031801c1c0c411070b21000079a82031161201120b900282e1240 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 249465431 1250 249464181 249464183
    0xc031203150a1503090506060118030813050a080303160311030414012304020916051206010201140108010c08160512040204020405090106050705060f150103090507030204020d0e1c0804 81
    0x1004105012440c1d0750701030702c2c14040c0441c04007002107034003d4140200a0320403c5000e6031340d0300500010501c1544124110900d400581d1a0a10014510f039150007840d84035240600c01c3c2620600c0100d01a0b903510300c0580204501c00003180c0768144954010040b80508401205051800305050604540381c02500d50290704131503506107500714070b40c2e0113024003004102d6603c854410030103130030191003c40403140698000d507204001c60f81c41420001800c0c8400380c051011540070f100d18150458141c82140d48070b4410303c00800e00100a44020300300c0c140c00c1e0450060f80e5154500402c4072944804030b01d41c4000303158101c001c00c019144c800340291044280c140d0400d6800340009041d51110b4044400a10300030303042000560391810020010340045008566501a4402040204900c0c003940390043c5502d5958042d502c0c01080198002c081c035050071101801059000400b5035101c1c4041c3c0154031920700007180083c07202c0d00450400c6580c0c081f00141d500051241d04506601c06030599100b = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 249466681 1250 249465431 249465451
    0xd1e050a0e120a061b0e060c03070b07020f0109060209030c0a0605040b07140d0206040b090f1f09120305060111012003060307090204090b01110a020d121b050f0c031203 74
    0x4031a15100ba10704010702d086018041300d0030101c1c20700e0030903401c0740c070241c1d100b4a41c2e4421030b404407068100819072040900d1042d450703000b80900d2000c16800e0b500290061114011100c08a81c000909429560751207029901e0503808200d0920302e040901c450322340c41c01300301c2d055203980f400d229010300381d400345004600050f00b02003504000c120302e60600702d0741d0700f10400c00c031000d1070380000c4000d5403210304075011100e0300c036102e01041c001c03540001d0001c1c520002c00080c00054122500029051141340041e442c4c4580b50408100881d44503641a0f481e098650f60201b43d0b40703454000500f620300181c10f081402d82c07500c050b001d0b42e08903000c401100c182c02c3c9030340681e03680c0760000040e240c030300650000940244001030000d03080c2000d034400c000110080e200e5440e026000c4120586440c1495030282d00800401070000001d104407d54400c60050790a200e04400110111070040001c000c0d4110b81552141500d861007030400c000042c1144030480091503510016050b1495a00001d8140824 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 249467931 1250 249466681 249466699
    0x3090905090102041d01050312070b0c0304020409151b020d02060a0504030e1507030e09040812040524040507090204061418180f180c011107080d1e050a0e 68
    0x10720801c0d011a401804980010b00202048003058070001e0003c1c46031602c00d102d10350031aa4080c80c3c150503100500d8022761145002d584030103850f10f0a510045c000c076803096555030034000007a91500c40110701d6510303403400203200200c0711030007403020880042c000030355100d442c080c40a02d90015200c3da00801c0e00d9004149a282e5280954400015444107540803078203c80305610311550390090641d041c02a50f8040c408150308041c41140796055402420100c000c0158000700c001d40140c03280c0091141c0e04440349a0301d042c4c1076004903c21581c1490fa0f80c4414020303c0244a400c11503403002c0c1240d01da04618040c58184080e1100b40c001014101446c000b003540ea107207803101b1050b1502a0b0300608140020390b090040780101030000c940180320b03584208042400c00c2c2e28845900464034402006000c560100700064920b0005408102202d01c9001404030708503e0900810103c101185c8501d501051500150340012518001d21004c006051142542d0180c1c01490501c141d002500d003446 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 249469181 1250 249467931 249467941
    0x61707061b05030a0f020613030c02010f0c02031905010e0304080d1b05010612120e06041a07020d030206040506010603140a0221012c01140411120906010302041803090905 75
    0xd031600c1c5600c0042c0c510301010035104d6916800c6180040910819420341d0a10360b00c41c4c8a1020012991070007038000b4081044810041d405104e026011900a0902c1c1094855a40c0004d02d440014a8080c40c854649e4110904001090062990940320361001e5418182030010466844590903e40320400207a0105200f403481141010401c29401c14020b0100c0b51b00c2d503001c0102c04803c8442112000f0001c107419095503c943d880d0004c0101c010416881c2502e012241401030010308001c3c0102c1c40100446070043e030311b4403903100311144690060f040e146898180941041c905a0216051508007181c626003060002e0065601c250419001a201d00e0071020b80f02c2c00810034615074080d201028004100b04115000141020180f07040c000035051070b041401400031000e00c907030180c018140d00d0311002c9160035081034200e1440000c0c030500f00002e1081c14000c50000351418501904404010b000358217040c059400c0300c00344075078031440000050340c1c01080e480903481020003155450000c15 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 249470431 1250 249469181 249469217
    0x9011d0d0210122306041a040506060d0207052d070e1003060e0f0d0203040f09091a01060c0204060509250207180f0e060108030f0f1605010207050106170706 69
    0x3c02c4482c40228100300c40702032204000340703c005a03c0e202d04541900800295245040c2c002c1d1f030150001c0c10311036030402c0c03064401d10024250140941c0c2e4401402c0c095190718240b18405414654065001000d80544940000d5480c1070103d415011030f02e00251100075060300058000101c43c2c0140c001191641d8900c2d540c1c01c007080b642c0000306140d0900c00e440001a900040121143d80d1020550350381105010090b0b80c1d81c800d501c01c041c040282054100040507496015031559402922410120305048070406641403090b04682c2c0401c440c90701c90425801c00d0311902014080541d50001305040000007001d50600c4804c0002020001030101c682c0c06109000c450010006200711f896800c0d5100003020223004030762410f1f000e19107400603a82440500107074060480d02c01c0710246107848002d9141c18450381c091021101980010092100311904d41c1c1d10000419002c6c1000580750303107880c502942036562903403298912003001d2658401c0c030f10700412074a04540407401d0040031150200910 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 249471681 1250 249470431 249470447
    0x703030f020c0a060f05061e04090b070206100815060906040b060301120b060312040e0a141626241203031803120c0d021b0309011d0d0210 61
    0x4600384a0020454a40100340000c0c0e2002c000c2c0700714010b00031a40c83c010200300f20b0340110307001c640c4030f04503100f141c840c003d4044400e1000c0c4030180c0041140d4087e0b440c2c840d01e111041d148400140d0296003001a080780f0181008083d01d6103101400c00140d040c4080c00000034080c003854483c01d00c500114105071303680e501452100307101420700c1c0d8072036954009583c003e080000c03042c4c07104682030000840e9850040b91006c8030080031400103051506202c01c01c18840c000603c40c4500a60b1101c03c4004540a011064401c40c0e040d881000420704a000082600c56100d8403c01722215500c0100440c10000381031036808420f055440c800305d2501402c0c454106040419950048491000040701c018080025841000e042c81000340d000310001100d5540c0c421902c00702d503940500008102d10701c000c240101100c0c1c03e0710101604200d440b03103101e03142c01001c1118407250f80c0300040d00f070602e50300080c5103280000c0740e10400803203070080d80200e041140060002845081c1382d1840d003403890701641d90 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 249472931 1250 249471681 249471701
    0xc06022509110c1605042d0915051303121802060a120204140a0e0106050708210709080d03020c030409090807080c060103030e0d020d0303110f071109150a0605070303 73
    0x8444140c1a1308028080c4e900150141d180658101354000702a00000c940400d05046440c0d000b03407400034a400004020094608102c81100003c1e500182c11b81240c000e03a80241c00030a1000300c02100d0f80750240c40322002d00e03030240c10035040001d0201d4810814400e4000d154050764a5540c3e0401100c1c01c4130306a0664020100c581e10105000c205e0701c03107000101c40018030a44440c030702c80d5200e01034200b20303040901c56100000c1d0100190000140480301400306003062000701030f1740301c0c4151080c507003408040380e105000480c90603081000300000c000c0b03036280c42140d00f1b0031490301c28042c0c2c66580301d2049010f4501c845844040d10b500f082010402c540541d60860b11413a105c1205020085d140c960070b01c003d40c0042c4842c881c2075403a240500c0c0310080554010004000511165415805021030034403225001d1000d00090440c0716030b960040485074031070010b159800d5608010040e9090380542540354810000361600100e0b2541c0119a00b601d1003424000d03124080e520701107014160080c1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 249474181 1250 249472931 249472933
    0x2010f02010e0312012c1f0302040204081605100c0b100806040f0606060513031b050306090a060608070b030c18180114010c111003090206070c06022509110c 69
    0x14211980d01c2074112140d069514000b8000424940e440641000d001d55503e40c150704031b407601c08202c41d84d58040d0300454040f006050119003aa403a00014101d0300282d10202240c0c001b03000c1021005550090304d001741004071440070785000c0701e803c0207110041c00180245010f9892001c1359452041c4d42d000c400404403441100e1a6141c1481c05004c4a11400000c0321807500701903002c10568080d006488641d122039502c4c6000324510b885d0b1503105da5600e94405003a81942d200031502d0340b002d000c1d842c8660f101c100144800a0103151aa0455000c0e5024100980142c0010f00c602c2c03494030200c0c7c1c2c01c4441184420717210052031100406001c0e5843c8402e0307010079008103c100c0a00503c460328102e03910b50340350030ba41e81c1c0350354010340b04205606002410040e0700d03489501c036460090418a4810298074001600e65441d034040b96483e403140713005482ca171314060010816540d040001d80901c0c807148903008a00b08104003060a403210314018900300d986c41c0d40004001c01c2c603103015a000032080c00 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 249475431 1250 249474181 249474187
    0x18060903050703080a1a1507060510080c010503061f020f030d05160201021305060a02010b040204030506040b01060c03020c1e0301050a05090c04060b09090a1803050414010804020d02010f02010e03 86
    0x200e8060200c0c1d000300c00c21400b0940390b1000030610301d900c1c490349400705c03c031400d42d54207892650200a840c00c20b20006203103008043c031500011840c280701e62031040c42d45280881d0652308080800786010b034412444d50401c801082080907503180e1030200b44100c1c140c7e103024401346070881010b138102080148102c029200200c0c1032382d051015a0082401040700d0b038581c06201c00c035080102d00717074130414090740e9480344070070400c12190030311070000c2c0b007940060310002407004100350008042c1c2e4400d500586a0750f2100b028003040c404007168203070061042d414141c207c204185c1c0d01a49840b01d0014035441490b0603034154241c95403500e00e100e4103010040c000c0003203150181d00100101030a83d4540904e00c50300702ca803207081c2004c0c4240000e60303564210f9941800c40d440100b0103040d000424000c15543c8688156a40c14124650950941d1007a140c068a03541030444131000c100d002900b150411040005001c093385440300340006081e0203192122080151a43c181c1c05400e07541082c8059202c00 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 249476681 1250 249475431 249475433
    0x207120e010e010311070f150c030207110307180504051009060f05010509070914041d0a030e0a12030507050a050d030605030f01050c160c0b03010f06180303080604180609 75
    0x48501100026001d0b203980180c440c011004400b22030090b000021241c44c104030900c0032520380d800d000855480703501c1c036529510441c1c00d00c009461000e241d80000c241c011401c6410810044c0d0304591401050f00107189052074031100d40700802100800341a401c1c1c0c2d81c8042803d105d001d005a403925008050700b800300c0001441c10400502c4030350480c03010640340c1400441c0600c3e00c056a1801186c19989000c0a241010b040401c2d84112181e282d034050f98800e40c0075003040001030040b444243e404003414100e03c035410098801c521801c003081c0b11700041d900c1881551003094920203003a406141c1642c80e000c01c1d2411518100d0100d00203005c0340f07d100204100039a15400660946a040e0142d07048a0310a01145081e0b46054405c481e5806061202e00124044403200104090141800741c0380107942d1440000325520a812141c500350f4003070424804560045d90008003d070030350070f207501820302c2d42d280107060044c0901603602ca981c48030041e001c0c507081d50f43e0301d460352034000401f04002126 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 249477931 1250 249476681 249476687
    0xc0f03070b06031b150a090e0c03100f030804030f030203070b0123040b0a1e0b030f0114030a02030d030f020706020310030314040f140a0b0d0903030e010c09090e01020712 75
    0x821280b0500c2031040c2210102d56081c0480c0441044030041c5c2082d02c100d0181c44240100e41008049400b04020034500150b81034075869064003071500002d803036503281000c011500d540c4025804c820021f02d40d0007010400500300c10111411650410b022007070681032860128154450746801418030003106001140c00f00e800720303070700d2291f4075425242d00c0381c6c0703000b10140001e503138604000c103500400c60501041280c180000c1e036405110480c5030280015101c011254a0360001c0e2021998100f00400501000402c1050260301c0c507803c81c000c0c2081192640000d98840480310308408058031804083c0300c02c0c019805990f0117030b9010500755180d240481001444040d1031000b54000358458100f00a040f4991045405545101303001421740360a10341041c801c2c1c030002d601240c00401141c1d00152200c00400501003a021070440420034a400b0f09008040c1c5160f1504041e86915115000c15265000001c490858054040200d0003100040380c140c024011120040d202d800380094a20314558 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 249479181 1250 249477931 249477953
    0x6050627072a14010c180302090705040b031e0f131103071a030a14010b0a050306010c0b1f0e0106090e04050a0501110a081f0308070c1a07060e0f030f0c0f0307 70
    0x440200200310005d01d0b020111500e15403140ea001c100130980c60144003504203010007a0740a00141001e0b0b2519655280b45a6030740d0080300d001410840807031241071386242c0183c0c0160044010010081e07242090110300ca012044104d005001040d0000c0c004065202400710308024000c41c00000784110020380340c3c52441d482200d01040441c0381c4101c180c07588403981da1150503100c40100071401c0080c0210161010390000e0440c50610802d642c0ca8000039200b0380d00c0d18480c4104001d826002c08006004403d010744c00e40224414028400043c0301141d403000809040702d05207968008603403500d00b44941400c12041d0040c2841d401c290074541400c00e80700062031860b11580e40c03560a40c0d0b03020707690603559080c01064820700c00d07180c50070808502408046c140c40c03130007030400c46000383e070710b080329a60882891607484500c000400c8590078020781380f003401c001c500c40ca0040c00208070720300c07142ca440e88100b8039800c61b144401716121342c11038020008040d410030010112940c880c0b5034100022920 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 249480431 1250 249479181 249479213
    0x302031f1e05121203090a0b01090f0e0d1b03120903020601060f1809020a05090d050601080111040e0c030702070801020c061009140c220306050627072a 67
    0x71401d00001414146420320a142103060f80c0900008080803401402550000d000c0c0001c2e8440c40b14004045001c50711441c3c0203010001340007400200300e0046900f6921001d034140002d40081200055130358003d80d000340e00c50210f102003e80031141e490f0a9a000d504064000340e030710318000020342003540004034a81030310a2a1100001d0f98071049089504104480c610300c68144440001c01004446401410400c00d01c4d040540c1411010700108403441c0940b0340507941580702a0040008c04801c2c0b0407a45404401203815190504007020401190006050101c0e444800000580620300c203008000240030404029540c4004454016030789100c16903410207100c4500c2400100d01031144941c640020700308450080d01d69425a00c1d0005401c81e2601c0840b03189074001705a0b07207140c04400d01015611030880020181030101c11b10820540e44400d803024141000e07201001805c2881312554400f051b4a844d0070900d03480000c0c0b50807686280002c00701000f2000141d0704201c20001c00d0240702c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 249481681 1250 249480431 249480479
    0xf12160620070608180a030c0b010f1a0703050913201206040b0a050a0e101d0a05090736020414010302090613170c04020306060a0302031f 61
    0x1180d0300040410400c00741044111075940040e208211040c003410300c46910114008900301904070b0700404508148800c002240000ca407819200300b04600c6030126809061031f000003035007031410080f0762569001141c20312003d490003c41d80c001014803401c21107829001c0500400101c1207886041c0020b061454151100c0c0d81540702c007000d0f00c001d0a81a542d17411000401482941c45050501c0020000300034095009000c1880c041000d0301c641c07da1100521116030445500c0c60182d031890040c08207038028082c1502c00c1030010b401c503001c8109458000d40c8103203001a042d220a040346160181e00e034058034a00c013150789044d1b00d81d200790000b0203001c881c8851030043d004500c00904d080344210701840414800e96555a0040c3d4420390140c038088501800c05860a80390b00d044100d40e00c2c0310341c409000440c5501c04800c0d4110144030950760414240c40a600b90b0a102002918501552404004042c3e01200080d5500c0d101e045850512030803030115200356483e41d000b82207000c1e0311903c105032 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 249482931 1250 249481681 249481697
    0xa030f020115060c051507020313050d080301050910080d09050f0108010f0b090a03060e03070c060305010b04181503080a021b0303040e040323090a05031b0f121606 72
    0x8040c010300400c074118003849020202a41000350959200c4000e04043e00c00348200184500746920351380701030303000300004c0d002140c403294400c031014025052604180c0c02090a03403030000000e003140f0103036810f50f03c04403225021a61100b00c003540740d40c00d0b03034020344442c821203600074143c170307000110310b02030341c00a85143c5000580d490040d150382c00b00780710f0315151080020381000084420000742500800080c050146161350b619540160b5600c1c900c3e10702c880d04002581810089030201d95401000d09060920180d0f14000013140c0a005031310400980c0d04402c1e04c1034054084a500800e024640d244e01d16078110345a040c650400c0c3c1200c41c0c3c01001d0f00c01d4000700d00441c100070700c01c0402020024010342c6064104100ca076203014000e0822420300035607200c3c607840d070000c0000452032500700c500d4840d01c4240300c00809c0194038059000c2c3e07019400a41c48100c5825000c41910343d10030003500c0e0481c0003080c10300465610504004105580d0050410002450b01c10038249070449500355a0140 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 249484181 1250 249482931 249482957
    0x21801120506091803070c0807210804060305180d0c060f0204030c090e010b1804020102010c080105010206070f050f12010801060e0c1c110403030c050105010915030b060607140a03 79
    0x401c8500c240c4045500010010000d0f800210181c040c1010304500d00560303060405031340c0c035600e0382c03403840c2c00a20181d0407000d02400401d82c2014104110b03038200510341d0f090315143d110b00342c03207101d039000f80c03c05c15460b01e0001c0c0b05080b03028003030341c00400c82070112800c0c411144402486100d110300120b56103400e00300e0000c08101e150094605998100c040096100c2c0303440c500e5401440c200800904c15500c4a10003503a694600441d9000303007010b1a03003860300b482c040c4002802c4811a0500b0818172400320b00501490743d0000300142d0244130750900c1e814001d540a001d032040e001e210701700c0c41000b00c0010700e243d00c11003d01419040342c0e5404002c0c0051509d0b544071841150003114bc0180c1201c089c4403c00d014440d1244224040d02034540005000c051140032560560240d0015004228404001800c119091290740c0c0104210715082100101c0d80000d030000c54260f01c4058500003090700030400d95a00c500c00c032a07280e68000801d2481d010784580c0107454200b040710a6021036801c9440b40c0c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 249485431 1250 249484181 249484217
    0x70305010b090109050609040e0708060417071a071101020a0525030c0b0c0f0d020315030109050316060212090f07080601030209130519030504150e060307080c0706021801 75
    0x5800b4120503110f4400f86400d00d024810035400c045640f50344a0384899640380401414850940030b0444280545040e20309410150040018006c9900b18183d0030041072000c01c022980700d080e03110203103a121005860743c4a080f59444003200312040d8079480056941c042540000c001d1a0304001520004040c6200e420b001c2810320042d00041d01003000c131801d00002801407000c0300d6200c180c401c01a41429078070343c40c0c1682a00440040c8010540c0001403000e059480d00340c52420322000c4000344000c80407079560986a00481a10340700c0240d20195550801000f5015500d42c9020101604102e107403000307a5503034400035241c500860b8000c4c420049903030180401d180b81030b07940160100301207864014008101c91100d2000b550b0901a00c9105030360001d02d0740d80720003194040c2e03561546850a242c040d01e02e1026002244017401401d00085500740c403440281d039444025828076440d1607640d075018000381d114006000b170006100041f200403107071112110030340c03504007030741ea00340c00b120360a040c2 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 249486681 1250 249485431 249485437
    0x30e2b05180405070215040501050103061a10031e0e03030406060f0803041814130507060201090f0b07030b030313090522122f060a050708160c1a070305010b 69
    0x50000740c01425440155828180c20094220b1158070403203411904000311844c2001c01600e0845859450380010000c0c0113950090018106004140b4601340001c0c00004500199095545e014141c82d0003003d04d2003401040400c1d4810300305d00c000c4c01350f035201141581d1290701c200c0b01124000d02d00303100418490304604010b4107480c081002146442c7c2400e0041050109010954000b5910381080041426500c0d0041e400340364001d60b5007078071000900d401c1c0e003440101d030414400c40e0f14007039481000c1003101001034401500401c03501c00c986c659010072400307020b0b00749606405210001c4da20000746680346e050382c100c414001040207540c480c04c160946086095401c64103600b20030780700301c0104008640004018100d030030030020a0020104210400402066482c3c94602007a50185003150500c0165404580c580040001d40b0300036202405440b0080c108c410704030004031180c0c45260041e04888c0d00f10340c1003607100340650300c0014000c0015904072501c0c0e0010342403000015810400707000f9 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 249487931 1250 249486681 249486697
    0x9150807031b0b0f18010201150b0702030a02060a02151b0904020309250905310501020d1103011409040201020706050a03091b050306100b0d0903030e2b05 68
    0x9000314901c0d41e1503140003450000e1a048101c8040c2000140d41103140d0700516514003440740311a110040c0000888011448003846419039051400c20724282920340c102d0381c280c1c0c0c500e940c5a0744515135800401c0c941941c2c0500250000000a0404241500002d1442108504002c07010556032452078000032542c0401025035224002d10042d05945426000fa507072001000c03007250400d15a80d0400c90003401e2030303003c2d230280b030340b0300d040611011005001d0b16600001e642c0d940034448100302d4010704442c1505d08403003005404d01d0208410040290102c885081802d0418031070b440340e503018218240e0003845040d0200d0340201035401c40d0b0a2032601c0b14480e0350140c003e1b1071260b192000030b850030787c8072010940401d9a40d01c0490300062000c030040c8031140c06a08030300012070501c0f092501c0c1a902030310b0440212810101008501c100004440304a081298040382c00107180ca4203a0240102e00000081ca000c0c0c5414003906010403481e2090411341e1620b01c20400c141e1a2003a21640b04082c0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 249489181 1250 249487931 249487933
    0x1802090907050a030b031e070602031c0b0105040807230117061e090c030f06091504090312020309010902100311160807080310080105062e030e011104091508 69
    0x41e80369001d540a44038810040c1000300c3d09819401c002410124613078055410015940c0301801c00c1482008440c1c054022800150326201d440140d224003844031103075000645803a44003a2800740d00c54810b0f54000c041c0c031000c80c1e03c103a480e100101b509030f05401820300d500341850b40e40c020a40c445d0780c84008490000c00308a4850301d030038051000010310004a83d600f039030148110750007510744020462203030000308140c54407810071420307000b4401d5010344900d110700fa40409004103681500c003501c100340c6045a002465020500c0c0503130390704500004c0050085d10120400200c40720640000527100d00c03c1303c2c600066801c10f03506600f100d907000d0b107400e1607090a025181c07240603030b5519407400e01d004d601207a003408407690798010183d00490b0400c03c505842e88003001100b1090281c1034008100316008184201085551008400c1c0b2806c03424403030a034030103011452400b03076000303c203803c41c800003c4c0034014000c0204080350380184614404540f80003002061022480020026200640c0c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 249490431 1250 249489181 249489199
    0x150a1e060e040f021f02010b031507020d03230c0c0d020313030222110406020c060403150f111b061e0c0f210405100501080709021b0d09180209 63
    0x240700d060010300b5640f0201e800c80401c0b442200340c000c1c10340521031002c00c990b001140000035070303051600306080700648091003180341c400d1148468000c2660310152406180000380311040b80040000000e5003c4c07181900380321034040c0482201c1c010011705130107401000710380441c40204412aa24401c41c00d001c07017035811910040c401031500407034801849100c074031106100000920503008845541030402a0b0030000141081500d4040c0449000f0000449400342091f107142c4591404a64000c1450b46140c1d0fa03411307081115009070300401c610f4507010003890300c500000c1d07100b409034020702c0d41e003071030622441001a120084e00404d41607541701907601000c03285c990740c80300a081c0d00310708100c030048907040c000714a084044810001c1d51030006096001039081605140d82403114140d0b0081e03201d810400103002c6108002a120205c502c3c040300140c0d40c407074481d03500f8090304000c0d000650342d000700302640d9400b41c0d000c2854415075410301e0105903509580e00d41e0604030f108206001383c10200603 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 249491681 1250 249490431 249490433
    0x70f17010c021501060315090c050c0f150402010e0d0c0b0a030b0a1a0307090b0c01150b03090a02120709060e010e06220f0b0306130303231503150a1e060e04 69
    0xb075000388410340a0321947e00789040c0c59040d41300690f1010340c40403000407404581c10010003410404040d00091900251030500c0403543c01d03407a0304070010006810300008040c0030880f41c807100d210001203a0403220000040740c59403441c0050b50300c5042c2040c0000c1c2071952090341d0345030003554481120081480d010540d00b502869000581005080f08107200c1c1c0d000c800179401c01b250004007100440c0000020b07860741214110130303075215a034002e0000c2c02001e0040103600c100c000b079903d5202d83c048130041681210b40480501c1d04c00130740c2140d0001c0781005400a00c056880a2141c141c45128520411540e070311018000c1e130050101842c1703014140011802035809032a400681101c05280b40403a10040300d2001c00c5ca00740742958810800428410700106050b414800d8481080340c9100e400c585401c000401034940310040d20352200c80a920045100a40d001c0001c80f581c0290303103c21050600d4030b101d0480003028941c80c0c001c4087c0c0c15042865044000748142c3c4191008040010704d25191 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 249492931 1250 249491681 249491687
    0x3150e07031e020d06060f20010e010f0212060d0206120606070602040b0910180e0c070b011203020607020307080d0b010e0319061514060705070f17010c02150106 71
    0x90010400d2550b14981c03042c0c1495200c0d0a00600c0184080140e55035203094200011aa9680d001c4803c100540c20900c54041c0c1c8201a61410341d500040d42540a0300c0c030340742a00501ca2402e6141d0a076107085a01c0d0324002d116006400800010740e01d002c0b655590782c003800000290700f840254400340c200220588090303850001034200401a20181c18402e05946613007ca0303200d07070030407200381a020070305290f2307868403101c0710f90383c070901d07140015000328040c0c04082c20b802640501e0349015019800070b04864440016980460b402505807180da59642604c82010000032034290018010300300000ca400e800001141d410541c8207170603910f40224030562000030814607414a040007101c0849866642c3c0410200f50f84810720f400c01e03102d811103481c0c004201c4668690780498168442410042415502002c101e0150190b41d11542d480e11880c1580c00c205484d00020741c0d200c0c04040106036103a0580c000980408003070020000c54600a00c01c1e80da40c289901d0350038181406500500210784 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 249494181 1250 249492931 249492959
    0x12030405011b0809010b0a0302060f0c0c1306051018030f020613090204060e01090b041e030f0605150301090203060402060a1809150e130807110402070516060315 71
    0x80a1000002c20108507582d45140c108010110000a005202071101400085c850044524012a0360103692031460340441d05038000e10704070742d0103c040428202c6004809220b0300403450401408586c2031050704221000134101d60003914000c0005015900c0464081e031041c00941d0000c0305420312651456440a04807611150100d80011041c440442003402c404420000740409540141e212418120020141042e0f05181810000000b80c00c10103260340780f08a038207031402043d0082c1c8600340e401031201c0c042210342c4000c00b1001020f0031803051003803e40c4428080c04102074500c106e9102d46080509840310110003030340c0342e046540806c00502e0584010b08203200e0a050051941d03e1510502e051240c0c594805602142c552103074500c900c02500c00300002e0014400c8034041e030700f040080c0509212243c40e0060450000140c1d100c184490006085400440103100703556441241c03901640742c0e4840ca0340c9241a010700c40c0007150242c00f81c00b490b000507821301c03480780b14245001c2016807005 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 249495431 1250 249494181 249494183
    0x80609220f06020d05041412040e070e06210a0911091503030c01060e0601050406090608090c09070309060501080303090307080d02041d04170315040c0207050310060e0c040503120304 80
    0x180c5501d10200049250000d000712039085040002d4918007420440c080e000003c0780800d40f50041056a008480c0baa03042c0c40541d0410209091039959460050b0f50395130749868840c2d4001c00c040b1380c0c80d00459481c403d890011003200004000c0b82c407480384003410741b800c0340710003080440074000b010102e003040c504055100001541d84082031541c0d2010904640c41001007180607510765400b40803a80e803c46801d500a4004e10340145014a00800100890464042c1c1c00412440101003004020100000c02506c10020b221a0030340c24241c002a008001204040300e8080c00c00c800010040d0340031055900c9810103a001e980b85ca82c0540e00c190f500d51029440800441d1f0902c000f01d0300240411040b00c0c01440c44010380000c0c24542000030310b90820749143c126030b000170410002c40d668054600c052141050303c0119440c421300c001070782030085941181d90103100310f00101044141e03030b802000032528202042103641c0c5440fa401c0d1881c1c07185005a0b501070303000841c0c0054701d18180000759405 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 249496681 1250 249495431 249495443
    0xc031f0906060e1302041109010c021014030c030619080303070516060204030809091005011e050c10050117030f0307111903021e010902030c09070201022808060922 72
    0xb040d12150000310510050b10020b100c0c1c524903e120045060a00c030310150302d01c415012501306030010000815170710840100074010000325400d280101e0082c1b4203650080d46c0880e0140c2c8a1900544451198000300c450b1440740e07504604800302d10001c844000c0a41c0c0c0b2450145166580760074003511154171080d1008255484640302001086640c80a0005140300b031440315959a810020003040400c0a001c1c10441969108100002e030b030015203c4902c0f2240104c000c1d82e020300b400741940e0500820940712b036680030b55040186418081c2c0d2045041c1c1d00300401034000d0002c06000d1958900400a000704006402c10100d03089a008100c3c0e020350725002400c480700c0c001103404141c80310018901c01c5000d40d10500c0103100010080341d0390088040b1900003088607034016000240d81c5c202c500c0d203440c002c490503804a5001e603c00e40484212102114075441518010002900c90034881c1007210300007250400440c0f014940298024002d44600070200141c80300e034134401d80b0002ca0214207c0311 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 249497931 1250 249496681 249496691
    0x307032d0c02030c0106030602030a0c09080604031202090612100b040e130c051002010902090c0a0c060b030c030706050306030609010509030a2111070209150d230303010807080c031f0906 82
    0x10031400d00518021f1032083c0c4002d616402d10340b420600380d5005440601c240320f0061000d00c40000d0014255a100f070f01454520b440020740b0300d1a000a2203481000e540240000030040880003100900c1e40c058030501c07036074540301079032602145078070302903406007559600100c00404c1c14910f10440c4104071a0007004240700940d41e40c0f00290cc008402264034002d40d45940c2c040d4150320b802140d00ba03024007814040361618140e008006c02e408600140113210039512001c0030076070389082040b6103840d44064100d0300740c03546405010340141c004030740b03282c480d105d041c3c0021048401030042c24000c1000d100114100709070701e50151080032281440303003001d1000c0c100d201c040c4152805050400040911215944c040b03070700504c800c43c10000c0207a801040b1400c540c0b54251552882c030600507400c10700c00500c50514140d40b44208000c42c8414840c0d00c4040004514840c0100d00c02080760001e074225110348008a040c10340301d2041942112940306e0a5620b41442c44180d080544294031032140020 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 249499181 1250 249497931 249497947
    0x60a0b0307450f050d170d1512060509071202090702150a09050d020c060307180b030702010b13061212020c031006080706030902060403060905070902030c0307032d0c0203 75
    0x980d10020307569502002c0015541040143d03a002c141d07401420096801802200050703c414500c00c01c01034400103030807000142c400040c010365100c0810b080301c004044801a81e5613845c102181600701080d1041850314021071006940001c3c00000c942041e419903800d0703400c3da020018020002002c0209501400301c080050140c1c8106a611507802c01c1c100140c42e4a80d810f05501e0401509e10920a640c090409103a4642e1010242c0380d01c804a450b0955245018806040340080b5950004500403400708c2400105a01034201d04c88440055456100c000001d00e04074043e505284a468202d0380200c000d10301255005602507000161030046603900070015001c20301e0706a2001420b01102e13607611091114003401d01c001c03001410300e1314062101c00d00702c0d00069528407952000825091795a80c503501000414801c01d4001e0103680b4003151246000d490a0406a0044480c140060301c0c1c800e415109142c1421419030700040d05800346ca4010b1b80d141100c1c0200211b609002c00c0d444140f140b26 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 249500431 1250 249499181 249499277
    0x6050a1203031d0d031b2c04090602030a06140d0305030105010c0f0506100906060f0203160f050703030804050c011d210708010f060501020c011202070804030803010e060a0b0307 78
    0x3044e00e04560b0300003809035941d960070305050104060b94010001e5804400c0e01852180c0248903068806401d6003061030f4000c80001c00810281d5401014540044108218023125a02440c100c8002003400d80c4103040f400204800c0d4540800003e001c10410300041c400c039407041c0c52010b041803103018502070025481e21424a00742044540c0c8482d40c3c01c41d0303400e20407810507010701c0000f0100743c144605008070115019440e40a403802200724440084a2102402200e005401c801034002040c0c0d103c0c25140d090040610b00100c0701622284035410a240035544074480045008038103060781240312445504000d0328002542c0e031010002c00d04410503c20070018009680117080c2d40000041d658240384481059402e81d41c440d41c1590045000110140d0f00b202400380000502e80f030040c0c0d00c00481c44c2008103400341d5000586890f1f00800042010b01c2003000150182000322843d621036640c80d42d0402061208544480001f08a4017008145400300000d40c0008a0742d80d00103081c00090b800c0c29 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 249501681 1250 249500431 249500443
    0x1a04090203010e06040c03020405030a0b190203010e010801060f1202010302090f090106030b0102010e0d0c0209100807171504110f0310090f03180605040b091903050607020106050a1203031d 83
    0x14400f8903500d48180074841c5801e06c61500f0000c00d07401c003941014540fa00003030301c6040720b10003d0000480040004c0074040c2c01100030b180401910b50841d1696141d080003074804009002e900c915620300880852800340b1203000c80100d4508020403c101c0c445070340110003a400400180ea0800004425100c2903070322580214068185a5000988000020002425a8615404c0c0c80c001e400c0304a11100c0c40d54001c1002d9009901076403120810384030484210072004507a44451110302910a0100750f00c024200d0030a6010311070403c4480e201d409200e03201e0190025107000340500080c007025111401c1c00010740101d8040103041c1d03851904280352210580300080c0d811500700c1e42e0740030030070304254100007554a8610300304101d64640d818410b001d04548202d00408840d07400c00b20301082c00d41c0e0b60515402000245500c60901d032590780c50282d80c0c0d0101591401c0c059402c000020800c2d00f0300340c042000722007406089040c0452551020350082c00042e02e0300390103400c8a030107018402020401 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 249502931 1250 249501681 249501689
    0x90d1d100e03010603200a12080310030b09030301061706090403120603081201090e0d02060403030f0b190f0b07050c040209040207080c03130b0901051e0417061009151a0409020301 79
    0x31180c685118046c0d05c0c01610f00e946800c03413103190429018002c5003445c1c05020f180c0b95014400e165252034120386a02d0010b80369100900341108030040203c62000400618101d40b580c0c0c44952181000300c201081d00501103071038503003050f200c40014000c603100d4030210711035020039040010080e4580c0c441281940c8092008586002d40790010805004540b08401441c202507004e80410050000001e403100d8002d0009810103464401c0040083c9544d8481c0c17005510090011201d03459204856003104940c0c03041d1450030003403603070008100e802e8a04854020343e000340a0520401c1f070100304170003500032007140351700142d09000c203000103044000208507002c0d90341c00031238880445c0201100801c0340c039000700c44c500000340140b54442c0d03041415507078107102d20044c1c11010031642c04110340c3c6004640c0805d0080d1020b00c0ca0240c0118081442c0b0b0080303c0580d4004080c607101d40042c8140c07590400d864100c141d040d88100240c020a240d290085400c040d02640340581d100700c0c040c141d8100703801c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 249504181 1250 249502931 249502943
    0x80613020d0207050f011e0b180f040308150a0e0405010209061c0605040b060706020307030b0910080f0c0d03050a02010603060c08090d03063218090d1d100e03010603 73
    0x60383d00600c0360400c00c100c2c9288141000744000c081244598000c42c410701010b03c5900e4990303d000c0d50790303603e50f1074105100c10a04294451880e20100720714807060300361020303008039442e000481d82d0044d8203510b4011118015008801003440c0c800a4443c0070030060040d6942d5509100285132903039004001c010301070f1411151251000180503100440c0c420307a0045104500e03060b501030140d00c9007015901626000314005031a42e480302e8055015010b0720245d1031344807900d00108070038210040420307c25140844210f8000641c1305034102d90b0342c04002c0401d9070000010b4012000a0b10400044c00d458400e8070002c07130070640d2566100255002e000d810320224280204000f0701500422a031507020303210f407a00b40145441d104041d42c40180d001501d6102c000d442c0710320102c1c0c2c0c01c0e44804140442010b0242d2005135242d80c4104000b250540b0b009442d805003d035113550380752113280c12581c000d0103561980704658211040141d0904040c0511007800f0350103c180825542c284249002140910 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 249505431 1250 249504181 249504187
    0x71a06090f0907051e1503100b071104091406040f120c0312020307170c0a0905100f081015030c080c040605040e15030a030309120903020907080613020d02 68
    0x10820014103030080c8041c0d488060710007000742c04680090660115581910350180419100703c01c003080510303460489030041c181c4807062440c1c4040c04011031041c2088100081080c2c0c507241c40c082d680c8201c0741d01410481c40c03656040c1c10b919007039200c2104bc606c101c030707014002d006c072402890800204403819240010103013041000d204410311540b0140041e8a0440640d9600d03540c003a00b02e01c181240120016804400609418002e030b81d40018210b01044c030801310700e050015810300b548040101c1c400201e11500010309410200000340c1e0141050f2604101001c6c0340e40101d0318220000c2400c4c40a031400c0c00c000800703007000307012248440201c4e074010a40820040d0003614000c406840102020000c00040200540c003070251420f1b40c80307414442c41591500c0d1000707500740d03403528402030385070080041120400d034140e40103540091007424402800b4848410650702c021140c4000394104544100040e007291040100c1c03580958001c1c52181e0101111104030100d03000703038600070b030032680c00 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 249506681 1250 249505431 249505441
    0xc07120201020a030b0919050c0f04030f050d08070c0605132001201e070b161101090b0301050d0f050d030e070b0712050a11010c0309032601060e06071a 67
    0x142c00b5107101080140c0e4808007d0810040040544034400b02c210120ba580d500400d68032041401160391215401166a40341c0d5100c2c140301c42116488002198140b00341426101003034000c06941d031040026841e4050711030f1554460b40c000c3c0000501136118000300045180004113082c0003d0310103254034542c1c40e0070302d180e08005800820f01034050341c0c01c2101e2060031805891b0003e1051015042140141009004510304528190046c1c2010840d210041010802502c0c013650415029015030030740011684031200640f410f560500071141c02410410060000741071070340d041200d8912036840c0309403010003030b1501801c1141c003202d40b900207900c500052030003980410031380020b0151000a03030b1070411140da44a0440c0c203500d40460070b00c440802d80c60346e494060f0101d464000141c800038080f10b540342e00018000c1400c0c1d0002c901203207140c6035840815040c00414003080b1610050700e41c9990800c1c1003940d004040f1b01d14154001010003941000400070007a901e1141a84500c1000c14205 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 249507931 1250 249506681 249506687
    0x103121124070305060f0111011503030c032304033e010f020f0c0f010917030306090106030c020c060d0207050708010b0301180c031b1508090c030703020105030105090c07120201020a 80
    0x361002c070400d0304042c1884000d40e00e14003559540322003402e15100041b07454089a0250000700e03082c04100112080010600d5002010503c83c588640d64048110b4070248202840c44401e90926003024010300007400000c4000060a00314500414040001f08a240c4264090940888001440b04065652a8003540c01c40b100001d403030414005004540005e910940d84d40c901407804a1003209000705946250b405444083d02522944411203070700c02c24001c00e10f0343c0b58010b035000c40c00b4190420001409034420b100d004464400742d4050842071085201300521908980784560000740c0c00c11507500014010000c4e0350003883d49000114030448080209400c440010705003a801104041020b800100c0b00032501c0306481c4d1040d00410394400744600c03440341c01845c2c0c00141d617a0340411340080325240c0101010b44186150401c45681e80354540c10301d900c03400c0900c002800b148080c8018809445e02c2c0c0043c1b6404090000450b04180303440c1c5481c5103d034180c1c0ba02c100540d500090180764294 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 249509181 1250 249507931 249508003
    0x9110909070501022112060409080c0106030309060c03021c12060306060e0a0902060f071a01030f05060105060a0917030d060b13050603040b0f060a1a041d090601031211 74
    0x20000c2c6203007120f200303508145c00c40c441d00003506416907114001403656900c6034400356005800c018981e484413034890070980242410301003a404908405400030f10701d480f89042d85c1d003042c0d01d40e02600080101000c4507407030b40d5002c4032032024044072500c0c42d240700d0010700c1030300b0085001c0c200229800746000d041c6039440902030000c1442c241080c11020150319800100c552099110440a0ba60b041505200b484090351071104212031100c01d00000a01a42c80c10340b0040c9406141540e401c0c0c5d0741d9104100c414440e8a1095002c107007600002c001c0c0300da04480c0c9220440c01c070010b4078079295900308500200c51850b040036000d140301103801820106060303805800f07800305840e420314506054490160b44c41c0d008008011100d0032000280c419107921036a24014410460400710342110540c81c0c040e01e400a02900e071182d40d01021004140a00c107120600a01030140589041e9080d0703150a41e07501c0000c4206c60521030300700075060082604010300c0003280b50200b00702041003084035031245000 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 249510431 1250 249509181 249509203
    0x190509130c090b010527040207141b09011505040905010305070e0a021602210a050105070f0201020301152303160906020d27080303090102030a2702040911090907050102 74
    0xb4600f00c80300036103076003082c00c80e243e00704400e103d090240044102c030004503003440d42143c0c0140c00415000200101d40b406240c0244001c4169044002d155514096207210402400c1d4007028042c01005070707051500b403421507036845d49005854248c5406084040c0c42080c3d000326400d502c20701040102e0f015180100703420020501e41036240429516464180f4038840b00003910420580d0080315411320b084a50498003c0000e0642d4107620f01130811500a00d01181c2d080f01046400450703008551040c4201c90681d40603d41440f400c44503000115050780300c4032500358402c1d40302c64074009252101006148651034240e1181d882e40742c1020018030100a82d4881c00c2558041030a0300a07098120203480400c000d0141350401c04480c04480080d848211350102c0004d01000040c801d50315010340080d40304014007603051001440000201c2120007002281c2c18105031019698001460150002c248641c0144070f124002c0b645000043c3d84802c00307844a200550203414100000c1d40c0501480103c8 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 249511681 1250 249510431 249510449
    0x6010506031306022802010c1b1e0f0c171c02060f0703060b04061716090b031510020f0d0305060f040906020708040e010f0e0402010509190509130c 65
    0x141003100c440204914480b2006101903001325070400440741a43c8110100072921103079955415050740d0103402841d0301c0d0f0303119001031500c01001c4402d080c0c2d94030694020754403540e0192813034082c0640050307481481608035041ca02c46c3e0590000b241e01d2004e0a009841503507000381032401e44045252802ca00c06d1911030000071400120f141403a0041003080c0d004580c960803040c107a5a0400840080c100c54020084001010a000c0365031507010000d0b0b2086924100c1a0301d250711600d1400040c414941405000151701d00c406200410089016680100882c0002640e01c1c20120008680c0c050002c03c0c10010307888103c600035003001c00c04c40e0f0140080c690504215030305292001ca0111541d010425000701d8407544074104000712941120b01d86500010340b1900c0310f4503200b2500440500703100d0742c4108444158042001e010065180340166416120301c0d142c20170f0700b42032000070000e4041c4954003c0d45000c00003010349416031124440d036403012078034a036100545020840843c41c0e80200c461 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 249512931 1250 249511681 249511687
    0x801050901110702240c030a0e0a300b040605070318031d01120f151707060809010e07060201021b150103020103200a05040f0e070e041104050d0b0103030206010506 72
    0x71001038100c411068040e268140f4420306200c0003401022032080d40e40a60b00001480c6d200f400012003e0450610070307540b11045000d100c400c03c000c070109801240d510440c031200c55030a44008100114106604008081003078449882d140f20500b8100e5040e120780740c0744c41c00c04c00c0407a03040c441d112242d01015407500c1503001ca602c0007040b02c94402075013101d10350241d0800c90035a00481070410380141d103880070300c01500f034104a8409018011050b003048000405e003c80c03060a1400c039540c5c07050082700148000d524019045070392034800380c00740307015542c0c1d80e00c0241010424000c00014003402d030000341e6a26002e00c6646441d9080001000705604082d598104491000403c2411a50240780119501804518181c100d00c003c0b2000100501c001640030a01e0350480003401c221030302d42c2010307400300741d0f10609039582080480e281c00004603030522071003070341c0303843e42c400c0c00341c2c0042500190502c2c1e12280404c80e010807103075082d15004280c8004000701a41086414003600040d262681 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 249514181 1250 249512931 249512951
    0xe040b01060806031e0c0909070b090603130219060e0f03060604020307020102280201050106030501060f0f1b06050a110721140d1a060a0e041107080f040801050901 72
    0x4144901801401c0c108120500454242c2e40c080003403a9a42000da5004407096504229031a07031140d9914403240a40c040100040c00a013010441c7c00c2120400c01c0c11910340001c41c010402160710007000410754056508158001d6100c0408140c41a016030200d8038a0500f449406098440030040c82403107110740d03294406481d2404543c3c1a00301d6001c0e5001740c2c4035110300348240d0190059096440c003660503000303501f6100085400c1024500620340003080540d80364501142a1582405094040703928541d080340401d100f4a80d590a020003403134802d2441d400b810703200c01d583e800c64906694058a400074400000e04030310840c01c500301410103003032400303015960b000c0c01c100d81c030300d42c5040c030031500c0c43e4200313005002c0c0165880380f8103002a0140d80702c0148240100070256043c10544d54040303200804401e050810071110a030300640c841030001c9200408200c050104108902e05c842014003100d400180d051028000440c8103462598803203041003401401c49800806100d200e83c10302d03480a0b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 249515431 1250 249514181 249514193
    0xa060503010c0e1509040e03120c070c030209090a06060609050f040501060212031e040b04060f060302010210020f04090501030309081506011b020102031219060506030c04170f031c060e04 82
    0x90142441a2110b07034910044c5038080c81a8040c229100e074000e41024404048240040010400700b1103200305440c0d07940f124158031b440c5000d080001804201c08110a2002d4074110500310351100030740d070407651054015a240e10603103495a0140d00400c69140c014010303071402500c00030608100751000c004130361501c0c1000f90f070350b07008440000d80318000001107a403d0078660b081c00315009804880703000b01e06103441c010760154002c07101601c500e0716040203000d81040d84c1c0102c40c102d0707805900400c1e0110b400083c0e0780003903200c3d040003420120100300000b484c000c58040c0070b008500a0b03d40060480c40d20348d2280c10300340307450f008640360a510b10800036207a8102d81000024803c1c14403000c8680d4241c80140c1c0b1711301c02c00c11038072841100b920070851300c0c0888a81001c482d070000d5030140019035403101407080700e00054414a4035408140000d1140c007201a14904860000b0b00c101c48000c04071100c0c0d07030b0a640c0711110340f000034100c503401144203c000780075143c000d010101d100c038403034949605d42d0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 249516681 1250 249515431 249515447
    0x9050303060d0804031a040c0902120402040c2a0308010807060906120e0303240f01120b031606050a1e0c0b0a230a050c07021c02130c080a060503010c 66
    0xc40c0c40b0300340340314001091228100941c1c000d1130707002c00c401840f649030301c0c5210361044080340c0440d082c10f401e04000c200b000c41030003565200d00380f034580c1180c1c2c0c2c1c0340c035400c103c0540b4020001008200002820103403030b01c8083c038031410003070102d01002c626030300b103040c020304454050304102044c1e4040f12081041607403142140d030480d69503103000c00482210000d5100034011000300110b84d84004000d000d003005c80030328100d41140c1d1b84e01c4080164184c420901207110410000103002c5003100c03560201000c101e40241002e048000c0c1500d00d000c401c64454175a10159400520000300042075a80d021600000030a1810800300000220080c6c40b1074000d18007002d40400502d07024100001c100351840c80c0d04030800d038a041c20f02c0425582128602e074500c1010864020f9074103070404000c5000c00c9541000c0751381050700a080443c0107464542c0c186404031401c00202d03000303c40342d41d829400401a01c00c00328031640c19a204215407d240b4040c0302522201c1d00700a03c80e92400015098564000c428 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 249517931 1250 249516681 249516691
    0x20a080915010e1303050706020a0f02100e0a08070c0b0313030e09130f0309150210061d0610023a0e0102061501091e051e060703110a05010615110109050303 69
    0xb411304090302030700d41243c0074010840c0045c801130000c1085504560400c0490320099299400c469001460701c034480240c9610214111594109040840101c1c00358001455050302076004041019658000700070b1030f5004a6400c03000c0c1e41500004020164001d80c002c00c140d40c11030b01f8030400d00305644c04c1000014007450080010f03035503207a46410540202c4c8070800420300e0f00302030050308034504d0300a0f490320302e120645150189002e001003400348080024402c01425441c08481e01e50b02e5000307009440458803a490b0561041c80d0034800c1003600001903188003080c1c60001d6400b48a0b080d02c01030f110410211000078840d02502191715030346d0004400e07074000201a1044a00008030707005840d0751000740c005007401c0c00450884550ba001241c440801c440c4152088400d00025000010003440100c82c05980190108100e1010911423820b5201c03906020060312032600300d6690b158211000b87e400701e40013a445152661300d45400c6040b1b8294101c12030002d001c1900c081c6ea4254480c0700c0241 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 249519181 1250 249517931 249517951
    0x20d0c02010c0501153809030304120309030209070f0f0e010e1305010303110a0809060f09130507021c08040212071203020c0f041107020904080d020a080915010e 71
    0x18546055a100d032008042c030641040081207800710001c0203103203d22450040010715008800701481c2c40440c0b600044028090303500450910589410020700b40c0d0002d00f400b0f6042c4400e10011613051480440810380d14400d4481002562540c811702550103c01045403040c00314540c1d06440240e0400440d031040035281c64040c6509041c00300580309070400b04072490700a02c80c0081a10b21418035400141640d020362605105460742c1da501c00e64407202e00758000c091480074803117041303542005405041294548001c40e403d01c034104008c2101c4170240c01c08508003545607024815000c3d0140a414125441c005401c0584014403201511448010700002d02500c552100101da0303030000e0183c40058190f00c04a0f8500300d07078a08001b5550320740ca803042c51044400d01903445880c90130f480b640003804c5190711003a007441600d40800010020007003040d200795800300511441c000403071004041d1490701c0d4964007151b0401280d140d251400040f035510611075040010705c13840480e0010190302c17040c042 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 249520431 1250 249519181 249519197
    0x191403040f0602040801020a180503060402030703030804080f0715060e10030b06040b060f070b070810031b0521010f0207050307020d1401021204051618020d060513090b0108030a020d 80
    0x490860b00034881d681c0320400c1341d403000c40e450720b4041d84000242c100d052600880e255607921b038810152903070000d903002581071713105500c00c100090094220691150103180114240b0710040c0c0345405070361101a04640c0840e0009d0410300d540054440c08000d400300725103140480c600b800d4945080c08150001412340c014050014505a50f1500404400c040107450180c50b92100076680201c7d0300020000c5641d119004c0018940920403502588a00451000700380250300e162541140042c184504c03100c0d12150b0036000c0b84c2a26100e0050f6008203840d0f030752141940420002ca42152003001d8050060b90042010401007880041581c0c0074503011103000d440c07a040c41c6801e160b9540f081307100b0f04165002066a80c07036400110600c81c41980101c0c01c3d200079400701044100602c80501450b9041c6401040300318803000275030301034805154440000541d141d00d80d0000b4440d003010740700b0b0b810107036205c0f0948001c20004001d900e004021a100543c1841e01d08007020391685802d031100c00c2044007034 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 249521681 1250 249520431 249520433
    0x6090c0a060311070507030f05240a052505041a03061e13050c07110402090306151804050c0a062303070c02180f0903270307030c0803191403040f 64
    0x4104582e0003a62105c210b5032950b950b46016240342806a07000d9403140944010300c0c50612140380507220000c00b2840540c695607682c0303071030402004081c10f044e03c800001d40030300303140787c0c030540d00300c10320407480d807504c41e16140342c61064580c0e0024408240c24081050051000607145e1069600311600e0140303441000ca110040400c200e0410721807000d400c1414101440000c4a1620003040e5050003030040041606a0100344003da204800358190141d0090340007078909030741085900c1071510000c01110403a8174510070b241ca005002e50b41a03031240c01c4000f04030024600305521b50010310f407070b05095510450641c004107004006480710040f840d00000002c042e0751242040138006036009252800190a054000c11465400c076040c4580c100d000c408100c21940010980d41907104112102e498100c2d003100c940e402445030101c0075018401e03104003100140e103080d00c00b0043c1244000640d00e5600d04084858040354080c1c4000900800020380d003440b07419030040b01d03070140c0c01543c000115245 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 249522931 1250 249521681 249521711
    0x70302060d0203091207140607080121030201110a17010509070c200414042a03020d1103010e0d180605090d020a03080a0905010306090b0a0e0703181406090c0a0603 72
    0x8034034959100d40b172002400c82d081199451b003220b80d8181003011110395603034110069812032828010000c58404102110800d6608041d04860301c0d0301c02d01c000300301d2401340904942980c100801c4840840c4440d03003c03000350455110b11900500d01124140303c02d05040f039025211014945001d03180d42c9002c60f60485400035040f814480303020140040040c0034510102c20b01c04141075408882903080c500410104e0f08410038200c00b481241441c0902c458070359030030001040c1d20590200c401400f88440750010b40d5080c441c050340442c03660003034a40b80c00319141c0100011013980c0c5421144074000c90610070329500100751601c44d0780a481d0702c1e01070001800000d410304415030000380540000140070642c1d650007800320341128402c1e02c0501c10261039060040a450009129a4201944000c01c1103400e0351002c901e50006070350f040015550217190110040c50b19420b00070703500c5108003140c0400403038040021550000502002d00702500386040040d40403091441507070201629240202e0320165 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 249524181 1250 249522931 249522943
    0x414010b030303040c0e0f0105060d1808030c0a090602060c03070f05090907020c0f0607021e0a0305190b06040c08040b0a1103090a050f060c07082104110a08070302060d020309 77
    0xd00600700c940341d1600d480c0148000080b4000c1082080407200410700d2044000351240c181c5030018a2141410107407641030006240e0080241407040380c84241c9004110040c00450107000c9c28850203030341c1d036a4504003401e035400d65800300c2c0842d0b0000c420040e00d11814416030b0b40003e514907140341c0c4c043c3d8a40302229075014620495030700484c11700030300c040a5000589440320342010f461070400303c0c542504000240c0a2414042d40112800035110303240c1c40c0b003140f22060501d000788a0030410740c8035151645003001c00100c01468070501054141405580c40c1815802035007100c00f80101c1c00c00d0f50380209001f0029000800c08444a000710703424504a0708003a01c00f1028000340c940300d01d0801c10b4190342e9088400241c45a0050000c0043c25441c0850b48612074880410f10916040c40d03070303990071469442a000c1b204441502075009543c00900c40382d0f640902c1c0074042c00c01e00a1001030411044540641c000503140e03000010400043c0c4030802500c01d1200740c50401a260340c0c1d2101303c1800e1007 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 249525431 1250 249524181 249524201
    0x17130803090106050a12211b0c08071703120705391c050306190909150c0e1302070c06050a030c020c090a020a020f0304061d040204060503041401 64
    0x2500110401090410560058007201e0f812140388905030340c2c40001101e4035070440400707040c2040501c06000511180c101c080d180e10040d00c0c1c0070111b222104803c08400d80145001c9800c001150010011144d0800205014001810400c02d100c21448545562403044000c0701051035103c0b4001140a40613009440304a402d0700210341c48124960007000088907540c4210422816241a0205a20b00003c241c1c1c600c42403903c509a1035101c031b07001a103d0780c1000707080c01e03800400e082c0403402491100d85084010074594901054544071490104408024200e074154514a0140c40700d2407140c1c02490840000c2d001e64143e2946810300c030b1048007900c01d41c0c1011f4030b0a04401c000003142d41d40b01c0001c02d0498059030302041240f8500c08101e03140c03c03400311100d0703002038900041015052203600030844100170340121032104c08401605821904260311400c00328000204103c10901c1e1007810f4940210104c030114a85800c000b0040d29901018101070310354014042070815007242540809019 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 249526681 1250 249525431 249525443
    0x504020f091602060f060105221e06110d090b0d2405010206150a0e09012004051507050a0f1e051c1110020d0204180b0405090d1713 58
    0x1407800035030311540c29440780302c01401886a00000307500c032060034038454001c1005030769403403400b19109003841c035121800c4151721207100001030010304100d40171101092203800e069409155454010302400000f0031505012a58211210824031540c1c400942429200145800d680381c0034980303001d00003455012140c0d40250b041e1004c0c503003480c6500d03030b02e1422a0001d900315841c1e40d840e41c03044882c40c030001a515410038040388090195442e80201e00d0b9002c0302d0760000244817a44113602000c00c0240d41103261001d0300024081c006030411b40d000c01a0091499540c51812925913641c956500701e820001d0548400c6a0360841007148202180554420310600c03840032180b141403a589039103032411820340d0b500000806102080c056109013540c0300b01c4201415200c00e10101001c06548154031000d9190340c02c10012401c14031051075450741d1105071900003642c0300c0782c40038481203400240000e040ca0744210031400d0f11641c0080800b506d1803801096400c282c40d4071004805021070b0810041034 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 249527931 1250 249526681 249526699
    0x7081911040f0f080604060903030e161412100902010201060305030a020d03180203031e1b03070506010e09030a1202090a030323030105010203220302030a030f0e030d0903060504020f 80
    0xa2030303000050000d9820964212240a07501d1642545a03a140c1c41030040c942c02000c00a4003291140d449101418000c2c00c2c041681c0c3c80442c8080d00b0122048404e002111011000f401181c1469034074108880e8240c510f10310760743d28000034035a6401c0c2d83c0302d1201d6058503805400c0459100703400c100001d60f84001100e440d00c0f045a00a502c4182c2c0c1c0d002d4200181c5001007040344104000d10201c032980c1c020340518504501070046640d9150305044901003410108003803418035891207080750414044901460b124050740c03425501b01034060307005841e0011004148040507001000718ac4110040e410007003420200c410500c0060b024181403507500141002c000801e05811030080b5261810260003c00f10b81c22f030920a07440c0740003c2c081c05006038002d000d00d401d080c0c0c142464400003020080302c500d40300c0d900d500191030a80c40354000c6000131042c0402c0e44020fa0841681908100202c0141240c240d00d02c0c001040d1042300d100181029840d10007040540d01c48442050240b400a006450 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 249529181 1250 249527931 249527951
    0x60f030903030a0c0203070206030c03100b04060e011106010303091206060306060e090c01031512020a0e0411100c0b06010c060f0509010c02070e0f04060b150a02010603170c06070819 80
    0x207101d400440e00408003500f0309044024841c404000c89404503801003509007991200411000103400003808103502590381c04002c0b0301c803a840b001500051100307585078204210314100040009000b00405143e50317101e0001400000d800100080940383ea07111010003012070382c14200f01601c5030380c0c8003421803071410001080500040d0955032062840c102141c20070001c140044044461268410100a5850b001800800c030025022508180002c3c1440c3d58076880e0f811716040b213481550106e0301c10204003000985c0c0c1c148040d8070300b010706141c140b0198201c030301d445220903481c0091440e030400034004002d4080100e103a0140c20a103602243c200640d140c106841402007048440c610050311680c00005842140e00d41038920543d4071a040380520380b615a00c00028000c0050748962101e601c42264a41c40c03003080140c100d008140d030000c5a078600d941459016880c040880382c2e940324042209c2e0000c40c0001505079040441c07880e250095030391b03144409280d41c0503005100241424115060 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 249530431 1250 249529181 249529183
    0x1404030f0305070b010f14030607020607050d0e061003021507030516020406080d08010503120a0207090b0402210118050610120b10050705100213170a060501080d08060f06040302040b060f0309 84
    0x882901c0c1e0034107c141c100503a59007050350b2480d044481d00010b030303c1440044c0c2a1481240a00354a6642c520081200180002441d04001c011034062201200d82e8000f04158540000220f058140d5079540c64680300080e10010940d01c18011510752030844401288110f4589521440003070105400303803801d24008400003000700324288289446031042e040c2d600c01d4603554004491500500b50024540b592400ca16007003c0d00301c150490350300136401c1c0691302c1c44c4410f0101c0303a10401c5007403d0045096042411020002d0b0518503c0306105160208200d0385403030b001d1401c8125120342c2001d40210b01400641d0b230240849a000d50f41016803031080c01c0d03d00750000003034092a0300c0741d01540e03580b100c0e42d000310080340180c0310782c03141444048104010a00c5181031801c05001e0b01e00590321010b1443e15500e00351503003a4000c207a10b6000020088500307500241d0b03d0340001080301c0018190203201d00041290199000c007070b00c0380e90703103007101c19407641c0b41e800b19485030620340c0e43d40ba01c0c0d1405009171 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 249531681 1250 249530431 249530459
    0x170115020c06090a061107080105070807031407080f0424090201110604080712111f0b0102070506040510050408010c0e120703020307030809040b120f010b011404030f0305070b01 78
    0x4080980300310520540e00e442c0079400da40c0f043c80b0240114191500c0e01c001181c4800e401075000405001d015404102814207000319840b44201c0d48070100c050512040007412944a46501e850002444080c002c2e00c5611000e003942000c890341c0c43c090941c03100c0c140070340d0440001c5070001c000010341d03140000c541c00c07035049102c4d81e5000362200c0091400c403403d81c549900003100e006202e58003c21640300060240e20207000040c0d801d2070401445214103c41d245050100718150b0901d000070410403041c0700790380c081c0c68845082031001c1c08266241c003020501601407809014840c0100350a103004043c4180207450080c40140028400007054580240202c520307114024019031101c0441c21000b10000754840440e940600140707041407035030b1554000c40d00315041150303025445012007030a668034031070303035034a05502d0902170700019401d05000c90840358005d0b0b40c1c80c14003145c079481c10b00070480c8000741ca0440f504030400c040307100420f180846070b911602a008010703002e801d00114074107607034800e1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 249532931 1250 249531681 249531719
    0xc120f1c0f1406030703060e10060803120a0e061602150c1809070804110a1205010608061302030a080c0a02060d0b010206010605090906220603030e0a14150a1701 71
    0x10401c0a2544040c03450510700003103420f03e4041e803020504200203512548851074142e03a05040e9901c100c88401c500c0240d0700c45038402d1410380d00100f0000a0100d400405a80040c200c1d04104424a8040501c1d916100010b1600f034a041a0302003a0400368021f02c40c00302072002d169807004084c0751012503000036400c4141209004800c0040191180c00c21868150180110b9224284141d407156900c1446840d55104141c02841d1400c001480070300139200d5000d80351103a000482c040d0709140520b481c040004140d030405007980752541015803004101202d403030740c210796502da4960b07800328020f24041009000035004840040c00d02c182c9211a4070000b00400240d00740d68160340d840c1e804035558090440129032180c1c441001c0b030700070302c3d0120801040200d0320b07200100d1a00002c0c50300c000c0320b001c2d500c150003003440d420010016180c555450b4000c2c0490700c0007c89154503c40201d5000c00d0302c94140001a180001c04c1003072035004030020a0b00070b0020051801540e10b446040c41c080c069031032 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 249534181 1250 249532931 249532961
    0x20f04090f05090303041e08070b0f06090c120405120f04090f06032102070b16050105010e07091a090411040303030b0405190b04020c010c020606010906050c120f1c 72
    0x40d4003a403916081c002e950095a440d03004505580b02c0da00c450400082d00710940e0030f000c65043c040300004482401400e00b46003d865840303904d152105000c196680300070700e00c8e80300d100800200050b030b1949405456040b40d034602080c00780c0d55186080b6103040e0803058a001c0c0044041017100351a0f2000c0300600556408d03900600054039550240426100d2b50b020082003260116042c20b44400c2d080c03a1100f000c0700d103204403120150f807101c41582030707840f0000c401400c0d0010201003050120034001c6a00402e4120743c1c5c00000d180c001001031500004e4065081d05c0c5c42003450203c0711f0920b01080e170f00700c2078008004000b2407044813582d00c055402848110003003410002609054031313052040600c540114014181e80000404001000b041c8030704d107140d4802da090020845110382442411200b49942d0000d00d5182041c0c400034101040d42e41c00001080000c2128581701040401e40780300581035440107644880401c401c3c0007190003403042e00728000261868100d1340b480943c2000e1004c2c9104c3c0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 249535431 1250 249534181 249534191
    0x50c0415112b020d081506120703060f0b0708090105070311060c13060206090a0201032310060806030a0305041401090527070507020f0f01090e0c0405130b0f010819020f0409 76
    0x49003603807600c1e0340708404000714142d240001e86421b0040070031601024010075562610ba0001201d0310a544143d6000c2d00180d030b031302001d1001c0074104142c41c002d06101c41ca500e042402c9903071200e41034460b5042d001d040103c0400c5076410503008036426150014510240c61003440c0c00b440c1081d013904010150039043e0004540010041e0010a58900440188010386009006500150b000e003c4110b0a000032400301070449240d2210358a10318010050040d800d5021445c00303100030302412000d88050301c81e030006c1c00c40e440066041401c983c00c407103070140c0004501c0c80441c0103035002d1b511580600d80200d00e11103079030010007000000c08416601010f000c02c1d0741c0c60b10002103600e0b000e80b00000303402540200401e5a03d10740307414101450341c01403400c04000303902c42805128944080c0c039609240030f404a018030440c5003032604400d20122440c0d0030820910940c001400901a5031130550500002c4004121042407020030f1000c6032405c0035081d99104010204401720368043d220b1120094501 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 249536681 1250 249535431 249535513
    0x50d0b0601020709060e061207080f03071511070b04020a030204020a0f02070b1e22030317060103110304020f18011d01050a060f0f05040509070909050a050c041511 72
    0x40c03103400d0540d21b9440c09400c5c1c5942d0b0380c003031060065001d01003001903c20300c1000641060304000080700f061491000e0341c2c071828186080c02059000c20b40b01c0b000b950408940108110f43c1d141580c104641020003010544c6039800840e000402503000031750403e0000603600c4103107820000c50202c10042d03600315201303250b68001a030035900407142004004408018205101140d40d005801c010340c014510640b80c02e4580302c04c00d40c5d98410f070320442c00f08400145041030030b81800820b550252080c01c4c10701a00701106012a41d48c400200002d205600010b050829a10341911823402e0b201600007031060307035849814644200ca000006c519400182e00004540c90910b0000c0100b11a2141c540030031007041c2409c15654146a82d21880402000340b100143c82d9481c41c0100f4001c212503181c15007450305009009041d41d400914484c2e081e410401441020121101140c049407281100301d000e0030b481e6003040342d000c1d000b54600100d030b00c030300c100c1e154406021821020741c050807507906e46001292 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 249537931 1250 249536681 249536699
    0x50f0402191a0702010e0324070f0207031205072003070506070803010e0c0c25050402090d17040902030108030408011b0807200105070c1401091709030304050d0b06010207 75
    0x503901078038882c0003031614401107030310320007016188040c414108603030007403103d001080c42e0040800806248003841c030178100061a081100e184c1115881c41d02110481e01c000300a503a801e450703c030040c8440d2090076000f10b12482071054030005584084104002c001484619001c19a02c01c0407a101380901c180001c2e0518262086404007a4001807181c2140e03e00000070044400040512518000800580d40711a8043c0081905400010b445041140408000116944007600440e010b070b40f0412001d10550b840090714100c0581c080c4541c0600c110141c0a0503180c0541d602c5901c901d0b0020001047c8a10080003810950b02d154000b04100746204502c4560ba81407000345a011684060104030540e1080f04c221113400d0003d64a203c0c150740c040c0c20745007165012149440000c4d107500b030141c10011540024102014294005c0c0840d00c03042d12060b5040900102ea49a0001c00045d0039450762003c0c01a5001054006c1c4101080c91260800b41d0019008548140c014000d06c1c01c003261030742c8 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 249539181 1250 249537931 249537979
    0xd1a0a0f09050d0908010c17040606080321010b0403032c06070c0801150e0a18140a030f0f02030f0c010b030102030118060b0406091203030f0e210c03070201120204030501050f0402 79
    0x300b1582d440204001d040c0303888c010910301a0059840a403038480109000408000800321035070070301c408034101804c04560200e10074041e00040c05c40f100400081010980c000380c2c08000452701c440500110b400440c2c96440b101001400b00d42003400400d0400030700c45002a288111145000203000081d845290301440780b0550151035003002c003003000301d00849001c1d4001d04003250a4040345120700501e403071380110580d012140c907035240d0000501c034041592255540603200703041d04001c04410714440d40a034807801100c5180381e03d410049446100010250014001c00740083c00842d0ba07940c42d11a078101d4600d0405601041c98144100003a02501203000c880880e2065030b2520381c0141845680035152490840c01d804142d10b680003c0c0b030460785032060701c20b0094801c5c02800880385440440383c001c00e04024030908a2014001000940d03c003008660b12141d091034a03850248011503003030004d02451b00040d00f1586080200b0000d1071070a84024000c9000b125944031400750b183c51010408 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 249540431 1250 249539181 249539201
    0x10207080a1110060e04030e09040b061c0b01030c06021b0105030622050702060a0b03070f1715010e0106091e0501030b0609150d0b0d1a0a0f09050d090801 68
    0x60030800070302000511031061014079400700c1d002d56980a02560000c4251102ca40068182a0540d4244410180c005490080c3c00c41e0030b0391280c10318640f544031907114690080c00d55008a21002c282a40d0029004140440f1580840c3c00040765840382014040c01d0540c3c051b900140c8115551800382d640349001011150005a58492440c0e80307620500501040425031420076907100ca0a6058021071400341a2140300c40e64000c0c02949003800c4100140e0b42004440d500a40041d80c0a001ea80c15208003d015034041005050300c94006501d46031501c9001740181443d0148000089a603030762030150300d41203894580d82c880c0140e0315401c00220107044030f142285c800d2801082084030754000d03001103d032101d0086c08241040c04500c0030981d202d0040b100003609500c00076101c20450301c0c9208011004000b030305d980031040b859036240582409502003102c002e4603090300140100d0710319080b481c120071031050144241445490401da4a607000c0039018045a9000c1c400308103804140b1500b00d5003 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 249541681 1250 249540431 249540443
    0x2d0901080714010504030807060c03050703150b091203040303020705150324030f0a050601090e0105060102060708061c03170c03060d02010302070804050402030408130824071e0201020a020f010207 86
    0x640b40524400000e01040c000506001042c40700101203001c0310064000f0b940100408505190750746802402c031003000741440c09145ca090132903080c45181d40b02c0e203010b5480312169242d58400c179000250480760000300314072031448006004020150701050b4942220410303210718103000e5030b012603800c903400221521a2001c08500160020501c6e0034100c0c0501000035060300c10080700d40c003000d0b06162500720191030540c4208010080c11810384112940d81306035100030003080c18080300003074540001030308007001c000c0c010000c036811381d580e1086400022695503886040c801c25103005064403492541d80492021a0f000240c4030303091134006c0780d1240a00130440d02650a45034010750080d008002c0c00d4445050074400422142c656100644c0038902403115603840d422181d079041400440d6401a11494110484040320080b2002e040d140c1d1080c0e0308035545c1c081c1c3d41c402c0c1c1110070210050900401d100d0000c1c0300364205806500400500440380d00751008030b41004140c600307038800d4080007440 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 249542931 1250 249541681 249541693
    0x4061715070503061e0f0301020c01060509150a0308180904030f08060a050a1206110c0c19060905040905011808030709050405040803060d03020709050108070e06010219060f0b2d090108 81
    0x81d9612800d040f0140e600401d078940c006c062002007822030704a1440040c00340c1d5076220034007140c50804413130756000025404900b040d6400e034010800941c2c05200c0203018000c0031a009a802c00130080c084001980601403070494945418010302095030403050002142000010a0040c204005100302b13440f4091f1a00050510700041d080301d9130f007148401e450503540d61022140780700d007000043c101c40c801400105018200c1c1002c0025000d9071214559011052000402010360444012021103204550019601740c1d1801c0c001c0c05024031095070758201c0d842002d100100036014014502441c002c0e99a40619038607081031004542065601802c004401d00020342149045a2121031640c030034030594955598410040341510403e800c602c0c902c3e040b5100074004000220f00300340d4050710901c0245200300c00b8800c1032584205103080034100c00e40f0f803044103030120340d00d0300b10380e815103c0030300510f010015841d0420564026403403800b40c0046400010030700c5140203140941a08d2941020f002c07 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 249544181 1250 249542931 249542959
    0x10626060f13020a120201020c0604030b01060c06020d0c03050a0501050a08030d02030403110a05030702040c030212040609330b010e01021c02010908040b18010305070509010e0406171507050306 85
    0xc481c910040400b01e00c0040310440300016150702d0021001444850b01442c2202c50314400a030a044040810a025000901c000c10201e1000360981b41110614148540c500b40581808001792160030b46038440c0904081410814544c1607001c188200151841000141d0300d40b0100b020f908064401d0070003980c820b2081c80c6941c4443e50007150401d120b414a48000386002c4038070b03400e05000d60302c1034a9a8002003078000a5007014042d9105014403440d08500e880c04a00b81c03030a0f1000c0217000600010369400051007001040c0d41d05084800c034150075200002c00c480e01094880140114000c00a800e001d0040015401910403c50001c8160080c0c00d00710485070040d601c804900c9001c10466480f1341c0780c840807078840d1004001420301d003034910359100110b1824100c1190b048066074101460a01000101075000c005c1d1400d0000c00d01c0c1084108035418001b070058200ea40003402002c0602e51000760400c00040c148140e449440f44500d0503070b98000d000d44545c002220902c3d00805c55a440d12 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 249545431 1250 249544181 249544201
    0x3070501021015050901180b0405100618170a03140910081003020603071106090601080607030c171810140c07030c05060723040506071716030201062606 67
    0x3946000f0107038142820303190340b903000038500c0000303070f010b0651400c01903a4031400350028003d01d002d20740281c90501c44d90402206020440c541446980c00708205580800310301c3e00d001021b00f0007060000c2107038036065103002d812526016184003c40119015002049203140c1d0f00d815100041d0005182040c039009208055600c0180200003071510010240c020006a0b02c0300c02440c0140306035038480d030540c0504500d00d8680b00c0b01624000542d40018010042410009841c6902505a24000c980d04150391810f032441c00c9000320105410101508010b51100b900100c0300c5d0b40320100045842c40c1241440390002c440031a198004240342000008503044004c400426420744240703440800010300e41c460a04201d01a02c0d00400203403c040790300012511288051150600075450510f02441c02000944a01c94404000c1c0540340f032040a141480c4280241c1d00c100c1d0301c44081a031104814980240240311307134094903421080708503841004424071201058000c080300000d05c01c41d01c45024030 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 249546681 1250 249545431 249545441
    0xb010f081005010e060f0f04030c1e0312030b0d2117040219030b040303090501051008030702090a0905070e01090c0f120e031e09090a020c0a031b0f12030605030705010210 75
    0x86801130006c20051048035030300f00c0241710b04074844c031156840d282945804000c0010691000f030320342c07002c4a043c020810f030303200302c0394103c83c1e002d07900780d1800a041100340e000e09604400140c0c0329103842441401d1105203003040b401040c0c81205507590301c10a44080d00c3c0d00c100131407500680f60804000400505284841288052401907101000395036951a030100e1101110102c00198a6120174810080c003401541d4009582e9280445401c3c20b20200a50701d008000001c0e208500820108480100d40d61000c90b01d641c024091318031440c4c4404400303198600c284a89148146048010b201551050910882d1008a903542440e42105020080041c0c000c060060300c1e41d001c00c01181d802e004140007079564a05c880ca4101d500d445030b0900300000c0240080840c01c040d0300401500340b09042c041b034400410742d07040c1400c0114a031002120691844207420060034008580390103024840540456080946580d80520020340c840c024180c58142600c03605000da0300c002c800c0131441190b0303046 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 249547931 1250 249546681 249546707
    0xb070309030c03230f18120a02042a0f0e03070b040302040507031b0215010504050c0717190507050d0207030c18020f120f0106031104060809011e0b010f08100501 71
    0x40410501361800d03030b902c1ca07a004003503410400034001004400c96001080d40e850b03501084445c65110042e400d400d54444030011402440b995807032541c50052074030142c003500c03414100c403500e01000c995404090100701090000d00045a00d136540c0c0902c6203000030704581990503c066041c141441c642c02e101c0900006803031901030540f207104500324600c0120000d94902d07240c2e401444000d104005d800800441070304814003440c281010098213552035000c4a40340e6601c0004a03404c040c103001c0a070140c1c01070b6050b104001c5188880d5200860307026004d002d245002d00d040e140c00480d00ba2080c0da40342501d11000300790a400c034504016114800a58170b4419902d0380002d40b600340480f2070010180d129850b82040d0300703104001c0c41640001d451140d0302500f6603080810142c03401d00581c800c43e0099200d404200311080d00014184c48081d08040c4816910000114071a0358440503000605208185180060641c000120300720b4461803480d4003490224400282d11400d0800456101d100900 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 249549181 1250 249547931 249547967
    0xc02031209211c0e0715140a0e1909020304061d0a020f040605090a020d0506010207210606091e0e01020a200f030706060e01090209010e0112060b070c030b070309030c03 74
    0x20080c240e0f5410340c014800d021031204d0140c41540d0070102000e00300c1da603580c0785c0000c121a070200400106c1000d0200e8407240c3d07550a01c2004400020b0009010705c0480b011070809440141c000142c82d6a640c01450050740b19040502c2441d00d10100000c01c003400601d0403a01ea031040c01c05030094102a0020410084050804a03a164039500401e10402d025541219060740c0028103002e000281d01c202130f003112091024020481c5402d00a1402003c1000f0141011074002344050401200c1d038003000c009d10f4910b80c28004c0d2140c1003071425800e1803880c03102030413030304000104136101c1040c030071202c54031140c1c0c440e9002580d001300300c02a95a601e0201100358494140b489850004c20006006103600c02e02003c80c3c0503040c480c01c20b014400607888450030354014484859240e8000d00c00c00e0740c4890038640084040090109000a048a80c1c005030120100045510510440003030040c242c90080e15890115240c546048045a864080107000984041960070002e84644c03619250422145 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 249550431 1250 249549181 249549217
    0x606012102040e090d08060603041202010b0405040515010e0112060b0d050307080c072909030c040c030c021e06040f110301060611100e030f0703050c010c0203120921 73
    0x10940c001c07a446900510078420740c1000b0030a2200007041519500c103410b2500101c00d0a0a501080140c0000740005208a20099015031024402d5018045001c8010800d01c80b509003400c1140c2c82e5201c601000d881244000004240c400e80c05035014101c80c040070f04034403801c803a92501c8006100c001d0000341c1c4400c180b1180004940d0400103001031602924460395610144e01c1000e28080042e0b10072818549055480c90308260408881d00341d003a80f5016440d41c58091500290403c4051405540d10505d4041c04101c2c203a40356008600e80707c026021210250180c9005d0b0030380d030074241c9441809920020000740003440f00c450b4000440d200d509003a42501030500040e080d42c0b087d400400000d042440400b020042c20407400951480c101800c1107841403800e01107849200325652001220300000f05041014450303c122081d10031824000c02101c0800d0b10002d440e1742c44030f6003c84114515a000c01e1300d903c3d006c10002e4000340c0441904481c0c0800303520b070300b0a40e0040d03452a10101880 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 249551681 1250 249550431 249550487
    0x30c030e0606131118240d020304060e120a0912021e21330f070908030d020d060b1303030f0c020d0c061206030308010314031309051b090102060601 65
    0x203c00790800c102c42c0740054031a21001024801030b420083c0618101400c0e0f0f040c4510841500c000315080b5900c00d5070092703580d81e241d00f080d60203008400040c00c1079105028031400007225080c0907004103681c6954007240306075194101044139000d60b0300607600010030100e900300045031074008407054402404d15050314101c180c0d01410300800200183c00d84e0844000d10340041e0540710080d80c10b02d110100c064010800314440074070014001d0210440d00058030201e00c4082c0644140b40050480030220b964999200014202a401c010340303c00d0b2107818040040780940034001a256500706040d43c194549155841c11110b04400e10010300c28406401504009601c48040c07503139010303000b010843c040c0d07480c10b0720042020790424140c0039007a1500d0814030001c6e5001c2d000c64116600322158110402c1c141170410304500c21400301d600c804604000c00920000590403445c840d0b80004821086800c128aa80400c3d2198658442c01031304803000103482e942c080e60707620000e940b540204514040d01d07 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 249552931 1250 249551681 249551711
    0x50306040f1509440405090a1107061109040f090c08150a0b19060c03020610050f0103091106030f0106020c1f080907081006030605180304180b0315010501030c030e060613 75
    0x81c600c1d0030301301e80c203000405006070300700110444d8220744c03451420000c50310001c10401d01c5004108000344040e454901c03007040c14803041c060b10180d03a40100200208071410202000610342400c3c22500c2940314400066505808030301c1d84404810740302c5020b400d503903605030b402c001c140600805074880f501d0b40100300240541c0030540d01805440e140d10f0300c05811070402910b040c5009090104603c6020001d0046464034148054071801c01e0a0106001e95249402c080400402c00e040707800039408010404c85d1000029050304070340258003a280c404a000b8280000803400c2e908180c201e81c08003561000c000d115107031091f407003090001500c5000b0303162102d03039040c00515407801d4200c0e40c0720b00c01071080c44114859903070170001b0b40e5103844070801e0300c0081c6600da0259100381c840303060068040943c8031808ea0003d1440c00c000074160340c0744980c405001c02600c0000e02800d8000b070714144c1c214030000d00a11034420b2001a04009240d175070313605400c0100d01e500003d0303500701171900c5121014800403 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 249554181 1250 249552931 249553043
    0x6070c0b0a0c05192102031e04030c060804110f010c05070b18010c02090a150e07050406110a050a11010c0b130614040308190204050306040f1509 64
    0x2140d075240b9440300b107a81405841d05007181101c03400c002e0070b10300030000203074411250f1101044411040030403807010001070303041d0b010305450841703151140c02c80003900a003240010010b07280300e0b4514402c2d0b81d440c1c2078100c601050032603004206100b050048482890300340180c40e40a401490300c2908034007180d40f018102659a403240c101c600c00882c10008940c80c181182c0440c0c0c1003803031325101340455a00080d8000310083d0400c050150b80e800c1100c0122450100c03040901009030b80d40d0001d003001d50340180b05604c07034415000015442e601c00c25024030013103012108650010014880042d40303849001c03015028240b090305000030709480390001200c0d032100d00d200d903542c00c0d07030b54aa0609500f40030302035070210204428160340000c10000004e4001c40c00c02e0b0040fa00c010030008462250041c2c6000388200e40103254140724482c20402040028180300c0c100c0741c4100406884074108803014001e6030560b02006000e0014640000c8000e019482c2c00c0c558580c655624442c031000000d17480e05949 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 249555431 1250 249554181 249554197
    0x5131203090201021c050d021608210c04290c07030501053405030a020f07050c041b05160503070606150305010e0705041e030b010b09040b03030906070206070c0b 71
    0x103070300e070707a182000c2d982c050181000480622a501044000c000c8008041e8480c41e00f070001255800315105590000c0a1015808150300601c1c0c2d556555040380d142402540b045040c00d004051600000c00c085803030000d0b1022a040e075401a40200c01044543c80310f54141ca81c4a503a1407000d012102601008202000095010308000242c42c141480e802c0070031044503a641102d408403201424800801300d003200e40c2d00b11245049500c136116401510083e110310705e070b400355000c8041a0481445004248501c901d2800c032810800881000c5400700305940c82034480021075406d11100e00d4988045010044c0c0c2840356040d645001019528807040b0346603900051810300c00d2200010316503800d4410340f40903002241d030781012440e0a4200501a1086028200a2035501d403290000b0544451151011b15404201c0c02510368541404402e903070803080c2036030320441c1040c0f415645401c5c00300c2250381d401000703407036240742000e190240281a40b19201c119501608508002040358295020340801 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 249556681 1250 249555431 249555437
    0xb0a030b060315040b0301091101080405070312080a0c0e13180501021201180501050d02060c03120a0c0f090803070b0c250b010918061a09010f0807060918051312 71
    0x300f42503014130040303803101c0302c0a500030b17031520300104c0100c0c0780c9186c04041071400340b1304045c09503035924040d03040200a91004114081598841ca88a90014500751150900c0c0324104102d00d0380002c00c9403504120300001e42c22000b41c861600c10790700d40703800000d005035a040070640e003500d143d581c03d400c80c0e0009a50b0b80850300580018403865086410708213011800150134440c550401d0001000f180205070700a00c41d002c00200c13018002c038240181da40f43c0e0000c42001e4081e1820043c4880501849024180020131207000448103074041d50303001c02502d0500c2c004604100050703461201544000d00034046000d4240300382c0200e41c0401ca00d000c0c26580068110318440300d1807404954003101a0840c2030034500b80310890f0019110b0421f090101a0015008a03640000501860520f003540341c4242d0001c462000215400c001c01c01080b04444040003120700050365881f00302c440c04140d0160301d02ca50591540e090a0074000d4026582201003000c8940d1288500e40e521000c09140e6000d48000c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 249557931 1250 249556681 249556711
    0x305070b0307080f0114040b0409020d0507080601170606040f021c1a0901031203090201050d0c0206041b050109170316030e030d030b0105070f1103030c160902040f0b0a030b0603 78
    0x115a9120200e16080800c10104c01d10550429112a59902002e850540600d40c0c48500000b0345c2d41b079400ca09001c1c1e0b005424513403252094203219803201580d00803500c181c800e01000003074569480a20748070134000b540203000c7c20340303401040101615041e990322415940a21103a02c0c02e21115034039030842080e2078000200050080c03503090400d1301918405101781c400200400118400c07a1a5405204c00f626000644820a100507101d5000e11801000702e140b4140665140513000079007580201d019031b000c400340c80c2d44020140703d6401d16005036030018540c0e140400c00c201984405a01c081c03408005e403410142c680104031302d42c0300d2403807098000864a43c031400761307400e003405416601c0c010b41c075041c0111444540060b0561003080d200500380c078400500750080c403462510b02801000018150707030351091206003c50395071304291880e0f1480c01103940c1c0001c0c03580c0c40340b007110112080d1400d0180101e1528807540850f0300300e1900c60b0203141e29030420702c4655642500540c03185548001e903a80d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 249559181 1250 249557931 249557941
    0x70f21110d0c0207140102030a0801030f02150c0a0203060f070c0201051e0a20060c041205010b1807020d02060108060402010f021f1a030606150714010c050706050717010e100305070b03 81
    0xb00d00c5c1354040d807810354000700078500c002940103900310306403900220b40c452070066a01c0407407c41280e1083e031400140d4081602d2820810100b59600000e00803801c5070625110440c15107205034044d60240081440c0c0004980154002ca000c1c0000c410320220a01c15100308481410841d480100c1001c0040e0610640e001214112410102d25034035540c01840c0030314202d903500c040c500c558050356400c0701540460504002d0250000d00da462009488041e28805241d0460b541c00c0090f644500540200b580d034140b40c51000a50034100d0361041d00401071615290010345008500030b007014214010640414101d0001003607001220b055114000b80c00d804000e11960f4000b80500002c1c426040740c1e06010242d51514000c120011080d4845076441c902443e2200c8074400000e03100e01c0c59400c00c80520065504000a026568050201803100d0781c4d8100003182c00004110100c5c0c81008a040107218030080e8118060740400104130b0190001e44a40700d8500d880b0035a44491494140001000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 249560431 1250 249559181 249559199
    0xf06090b0c13090b040b060c030a0908031804090c170a060510081b0303070203060408071502040b0d0c03061e0807060302040b16060605090f070f21110d0c0207 70
    0x1941c89900d41240c1c07030500901c41c2441c003100c0d1203031003143c1034a5114024080c02e0783d00c1d54070115200e0401007840c3c1c1c1d5041c2d403107511134480c3c00650903000400e00c80100003502020220031603004c0020205000044101002000020305207424140d41c4c5501c4108c010640d1113612502da00c0341000ca1008008400d150724101041d110000c160326920110460b08002c2c5101c0068030840c0380344407080f5106802410404640342d402408001380d814402d0400380004c3c030100d10300502070305000d600c0c0440030749060311003003040c4c2c031803441407034403d40c800c000b0001c03002c0303a03a842403420300031510b00410102c2d41c41e5004245040c410207109172444e02c1210410003c2c1c01081400c0061031141400d60400d4074014139403200703004002c51003407140000c982da13404100c526403210300079100082181c1c19074180707c08414260755084924102042203280b002d8441801031034402018000526a4101217030380d11a030001030102c101721100c1000d001d0240024071140741c0940c0d4224011b650040084c1441d0039186 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 249561681 1250 249560431 249560453
    0x10506100c110315010f0603150b07061a130c0201051501050901180803040605040311090c0405130e0604031e050703020304030b091f020d110408030301060804030c0f0609 75
    0x540d20a0505241400312280c01008803212182c020070208040d482e454082410800d40000700032000b0850000070950318640b0011006842e00d9603020040c041c0400b00300141a086406941c074140300a200e1140020f0139a041681c50a41c22988910141c09110104406031a00489210350a884a0100c048664240704071a40100d5854101040c03041d074000207049403080c40d03a1603041115000780c148002943c01002d400070006001200e40c1d45540d184000e055800c2030000f203d0341200450005820714000121901031303101c000c0c480c0c0c50140b40074104035045011800c1801c00c06d850313841c4030210040030b0040038815800307501c41b90121560280c0600c42c140c41d114500c001d10501b4800240800c1d8000b0a8900340c1e0b0340a00d0820203a10340d075440902e00014507081d51061910844005103621250b00070f01a51107120806006014024003282140d00a500403404203500610042000d0340c4075014540c0c02c1400380c103000e4088030540e01c5882d500000400d00b500c0c02900c40100204020010b031340 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 249562931 1250 249561681 249561691
    0xc1b0703080406030e0f0a030c120206070815040b1903050c030f101503081c0e01020408030d020a1403130506010605120a1e0204031401050108030702010801090216021e030105 77
    0x25000003415503903628180c0c0581c2c0107080030581d0300c01a140054800300302c90440042003d081715568103c0785001000c1d10707120744046401c1d004445842148500000384035000e02c84a07114035034581d4a90801d071401d12901700035140c0c0300d611b401018a040d01d950500784400036040166421881c21400c00034904801c1e11006400b941c000e00915080b48804104814a60500e0b078020400c2004010003a032142c4080e0005802090300264000700207101c0f4a00d400d8401807480c0600c05c540085003480e08031b005610410585800800c003032804a850347c1e006180b410b24900b40400c140320142c02c0450703513410448070707088034458170f8481c04284130f0f00700101801002c0920b031141c94141450014100820050034075039038213480780740c40c00302c01500020910010924070011509c0d02e5030317400c00800b405400800d486155213400000b02e200300c40032049a00440d0180c507000a182d1900c3c56a4000754024a003050660b01c40c3c0c500180166600700c8030381c0040c000c40103010300c100d980008060840b90f0147c4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 249564181 1250 249562931 249562933
    0x4020d0c2703050a031101090605070c020406060f0c021512011e0b0403230106030b0c09120c03061f0f1202040b09091e030f0307030c0f0503040812060609090c1b 71
    0x41d0820000da80002d03052162689460141140d0a401c86d659014140260008241c682002c0c200042c981d44440c40c40c0140b8021035003402811361751002a9450346507424110000b80070300ca000e2001d030401141c080d160403010000705140110f90030201e00700160a8005620001e50008840d850005109050002d04a050a524036007842e6640c2c0c04c0034008101e601e205a408000c00200300244294081e41c006c54006582c4112031400581c08a0b4a90000d192144202460f0360241d0301d146000980a0030078902078000e1896882d034020100310702d2506e070f02001100060900215a2121442c88000144180c0d40c559208000c0c520401c000d442c40413030705501801c500f5007000210000003600c007518506a0000b0f407494400740710564198419411141c5d0044400030500070503070351507800b4012419182c0d8520f807890030544070803100380c0300c144e4018058010034031068651448400101382c10030700091540e0720f01812400403c1c40d108086480a441107004600c4a942110a155401510380608 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 249565431 1250 249564181 249564257
    0x50c030d0f1d100f050d0c0819050c2208070e01180b0315060402121008010e150406050711010e0105011403070605040909020a120501050901140402010e0f04020d0c 72
    0x100114030018103c0f0f200e0030401c5900e43c2c1c00408180201c08407045d18014000510500300c0d20b203400303044030906440034070040901c081c40152030b145500c16903004100c0000228906040c140848281d040f44105107009100300103070000d038050003001104018516880d5035001989489a91056103180450103080942412420401236401140d94034441301c0c00c500b84d14007600e502001c500240107800807500b00c8003c0800f8440001803440d046002c1701d0035503009228035041c5845190b00d80030780003601d030584001400480c00042080c0c114070351095880c44e104159008210b1001d0a56a101c5070303a5801e80d640340c0c018032500304200d041c1002400290700800456103001402402d600ca903104503401c286e925404e010440d581c41a01c2d00c010500f0041803c42c0c0782503801c0c80350090200381c840b01c0140d8608500080c4800c04c5043c51841241c050311080001c2580d0014400180c202901c0b00f0b80c416401c10003c1c0000540303200d820140b064036030355000000003400c514803c81d81c81a002c031000394010 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 249566681 1250 249565431 249565487
    0x6120b0406080f15280c02030c031c2d0b010c1509061a0a03031b050a120f0305040209010b07030311040f06090902032e050a03030e04050609010806070507050c030d0f 73
    0xc1d00b0700c000b0301c5c0a01c0704000303140310102004a046004580c0c455196010010304942d510590100c1200d80c0c0da80284108001b400700c8401851260816180d100300840182400300b481c009a0301c40100c2d5603040c14503a010304810f42e9145880c0880324101c5000a42e1001030405211481c4507004100c0290220700e443d05d1500c00c00030b00c0e00d03455444000c0c10000780340c1c148100715095182014801e07a001081712480402854011101d045048692000503500c15051074032a11a0045a004a8001e440d40304264202a81140300c3e9102c403d0503824103444044204103245040001c00082150010584200d41000c00080c10407010b9131210340d1306801441840405039000e1b1a03aa4001101c500f88080500c1c01401041040c0442e03211316402502e0700310000515400c100c80e41e80060040314100140e0f6681c3c410403004042c2800f9000081d400840083d006600500040031507038020380c11100d10304501d0300002e00c3d0900c103a44660000382d459100413038241d04848800d0415054061103014100e00e = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 249567931 1250 249566681 249566731
    0x105130b0f041e02030f06011d0a0507050412051501030501020c0714091303090906080c01030c0f14030c1b0304030210090311060a09032a080706120b0406080f15 71
    0x1420b00420300c00203500f40001156401c00c0743c2070b0701c0010329080d50025a91015002000b010004000123100341040c000388203a0300910034640301d041c040e10340f070b4100b40c209654038029040003801100e0a100d59401083d030440440100c90086115038000b59881f5043c842040c20718641d50b12050038206101e4032542070359a20b031500343c1d0140d000c4c0302c2c3c02c1520403103003000c031403203400c66100e207404034500f16002c28520004204200811400c0c1c8051100c40c0c42034074216a00b17010100c014000422502c078600b032802c084001507400080d0603001e541040003105610510b1981c8482c0b0783c8c5281d20003d410000c50504040e000d083e1034160800700308051440c1c4642c03100740d03040d42e132030b07885084009040c40706940200700e48406140c00c00d58100014440c40010001030708031207060b811001d03c10300c0000da02701c0d0002e4500180c50059030341c03c003c0c904e10005c2c80e024010030030050f41c0c0180c5880010a482d413003044001c01c40a5030f400105560300e030003501030211620161480d0502d0aa14582c1d00410b00 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 249569181 1250 249567931 249567953
    0x151204020f0418080c01141e0a0b10030b0405012909061c1a1909020d18030513080c060301050f030a1e230a02061b0105130b0f04 57
    0x9016503000580c6488440001c005003400400069030403007004054040c8005800135080805c0a08020440100050841070b050903045816025101740b040b1801400421200c2154100001c1c03a40458a462401c0000703006a00c0528200002540c0d00d40006481c9403600440d030050400030400c900701030030710092000c0c503189003c075a25960f200184420281d15954100c8041d040d0044a0703500381d00d1001c504030050301c0e000d00410041c4405c985212010b01e081030603040003c040b4580c007501a850041044c020350000e860b10040e07181d0310304580e41c1f110b0101d84010900c0d4400d544075030351440c010b214084200c44541100b19240d01210040c407a07038031004c044038103664040b5101c40620400b040000e01e00110407030000c1c21107240007000384035032003041c40182ea9070744a60702c4400b03c0902c4100b00301000b83c0c200c06003200d90340050040000b60030140e005101d4406003403154030380c0c8a44c22250350f007501c109681c0c0c01a8480e0b412003000510506042841c3c11940c0210800013a040c6a101c40d03269071 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 249570431 1250 249569181 249569183
    0x70804060f09050405180c09070503060d020d060f05091b0a050405130c080d030c020f060112030903050706180618030201140706091104060806040c030605040c0909050c151204 77
    0x1c408261000d4240110200001000c005005122500d0710b00103125500501701c0300c00c400da1150200c00c04103480c005906038403c1855549003801c43e510318042100b40203025406030b82000d08045130401045043c012145030000d8507102292904285030060720b04881801e001222085400c080c03141035507003820300da04a48046030042010307100d503401c061048614a5005200c8881d20300c1c0000c4211020941000514094600708225881c1020076a120300300141b440200750414070050116884413401402c016009203031840c080e40c0c43e550b5191514445421640100c1c50004071800141d1030070700711070003500d0240b400c2250711521a800705907203401c40c0002030603c5260400004412290019180000d80104060107500f10f5400d0546141c2d00c40f000301d6000d03030b08007180400d4541000444c0781c002c42d0701c090401004ea145031900030061902a000f150100310302c4c0000101009207000c1c20306c2c014021005820307141000c800f0040302101081c2d004044070814401e508035510806e0a085c4c0c02 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 249571681 1250 249570431 249570437
    0x1506051f0210050c04180615090503060103060e030f03010f151e0e130618270b0402011814041a0f01050c01020708070c150305190207020a030c0902070c050607080406 73
    0xc4d0326010f03018140d9010700c0e00500499844002001c050032506d4020001702c500145944c0e0028460f0201202c454926000307540d0180d200c8001000000c01950003000c64842c410150307410030b000d0603000320341030303100303074000302040d12825000c4c006030f0f41c44603442d6985080d40c00c1400c880011412080c2c01840e074440c43e001804404200d81702c40c0d44641c0e210b010708048452082100c10340f1500c110a08441d682002d040304da103001c2001c1540928036078000d41301031441a00719080001c5a5515161200050040381048403082a008000c210505414003801c0c1100c0d40250182208050004a032401080721400701c0c410440001562200001c9800c012402c1c0380c140e581e104501022406840303180c100074424000081d0440500211040d1181900c0e6000b00310b070144002100c0c100c0964005032040c1c0c160200324a4001310311080d582c024442e042c400b800c212b0f0401d580751610000c4100950003d11070540000380d0a0801601038098006448100c407801c0c24000a611800b8180c003441c0240414 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 249572931 1250 249571681 249571691
    0x1e0a090317041b090c09080313050618030703060203091b0f060901021c0305072709020c0c0301090308150a03051905030f04030302030d0b2e0c1506051f0210 69
    0xe000c601d4651003070f51900304103110f540315a2401000c009040b1042c4071800101c4000c00070a40d8100801254280183c200f1607036452418441000b0031584880070303c0d441c82490700740c020303247e840a010005c01140940c90050322840c0403104a8104101031013070b5040f06806400108050303032440c4040440210550703c85858250442c0140d1508075203a01440340510000c00082d202035040e08403d01c074071050b035550b82003803039150001025000701000320500b03882801420f0022442c1540606100b10340c240840701c40c0041e450100303003110740754201500003c0e00e20b02005031031307043c0303c1030000000000e40d480300e117983ca9a1184e948884103e059400014a4803940105003e01001640e1003c02405c00b00350340d990f92490080d40d0ba5004541310010141022148074032441c110104400c840c412040c80d01c12040c1d55041c0500502c0d00d40b00041c02d0040d8110b0310070205019061284407030300d50700c1d000680c075800c00c01040944511070741100ca0340b2100020608180f0780c041400865107a0007000414 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 249574181 1250 249572931 249572933
    0x9130b030a030f0c0b090a031b030f030c050f130306061a0306040f091a06040c0918090c09020703030209040b060a0c060c0912050607170705040501180b031e0a09031704 74
    0xf1040664132014004920303803800c3c82035681010072688800c510a40799410422899031844241c249400c001038089020304030941c1c10140203070803200b04040c00c2d20345145003440200c00481d41d90404c90354480d00744801031003841080203034401c03680500200134040040d845a250008028030008010902494442801c002c1905094014018050780000d018900c00800f40300c1c01c05407442108c81e00d00c22414000c10301402ca0048049409440603110807420b14000220f0b04005001100022980c880e0380960000d41424248050a4801c0c400e80c2d0140c0e030748518000300829a84511095031094404200d0080038035008241c0580844e404000410b0820f0702620a07100240301c3d83c4001d21000c0c01c0410307501001404201d5912511712a201d030400402207080d10210108110f403001d0200e0310400c400e004070760080b008010203407500d0f8240d011083d2140d40d6500d550300180e07401141c0720400c10ba030095041d51140540d078050b250000810680507180c500400e0102cbc0000020030b03400b600c0300420 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 249575431 1250 249574181 249574187
    0x60f150e1203031e060a1511070308030702010e070504140103140c04060e0a0c020f0705010518060a030e0d1b060203360c010203070506010e100f03030509130b030a030f 74
    0xa44072150800307480e143c0c42e080c24202d01e100e903003c515a0248454400250b003a16090903104103541c411948031569445c00343c0f09442d1b00c00380554041581c4035069000001402400003503205103516170021030304180301311200703242c00299041503102c1c0d810041c00145400300c010401c0d04683c1c0003111804515184944181010350818200d6040360401401052280038410940d024942c0c00100300300e11819140b00303d03201c81846040901c160401c00c8100319561148020b0403400d0180b9440100750b0208400003003c40c0d22030580400403980720104a81c441000380109039111240e03040826003010031441e1007100081070742c2c00401c7c90303601002290300b02e04071240005002c19200e0100190300700c8540072142200145803180101d1280341000d2440307502c0031007660482c540c03040013000c09034208440702400290050158030200b80384000041d003202e4005406000314007070740700d05d0b5a40d144201440800d80644000c070a00c00d0402b200b1885a490000701d0701041901440c1c203201c0c0c0c0080040407 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 249576681 1250 249575431 249575449
    0xf030203241201090f11060a090501050306031005010e060909060f130602070210031409150411031207080a18060507060902010e191d070512150a0603050901060f150e 73
    0x2542d00c3e40c030380713561401005100080801c400303000f00742002008070381000f041182c0c071550a0f03240024040d420b0030095940210b010710b030060070003410b582d0b8228007140c00740d048038000d0f07204910001800d018000740c2e040c000c0760190481c6082c4050302ca1481c1c20040381440200103049005040c007170080300c0040c07160a606440f99164020701c1841d0002511200030040c207214441074a182c101580441d51003c1c0000350982d4880d264104000c0030b9490b62101c000d03082d00044502d415025071002d0002d0621050014105588904440c54488141080007880202d40c40820110000d4a030001c0c8116908a001d44101507801000810540407070710049038103030492080190840f010415465517550303445100d5069500c000c14010498540c140c000c410f403c8241d07400c4002c220308006036440e0f00901e0314115485900076840001d00c03140c00780400c503094031070f91012000036034034405d003c14604207000b80030003440e1101c0365080729030a1020300f001c4500e85e400d581c818490340c1410000b03076840308942 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 249577931 1250 249576681 249576709
    0x8011505040f080a0c0f080a0b06030106080a0812060118090911030304060c030e0f06120907031a010905090601080615041107060204050a0b0f161103070f060f03020324 74
    0x42568000d5a4100d83c90756000707422030071181d82100807000301c2c2c24401c007040366088440020061029203000c0c0c65008407205d01800c03144c0c26540740d80d0085286507007040b81320003007032140c1050740d52800c4002c1211407848001c4c0c4541d0402480e04400c454100c00300c1c2203481910b03007212000603c400d241c03a210031003481c2070005039054000860300107243c50704003034a44000c500135201c20f103d03071181348200000fa51100400c2944480c0a0141c0e10740d0540c00e2202d03070b61000041d4121052540c4035140d460030040740611060103801d40100511030416113002e0b0341d40022410300200302035414981d6082e1038600080403100340c8451181054500d55450f00901c00101e000d0403001c3d501e5140341403400295001d030044902a0381c003980300203040004c102c00c6400c800c5029000c0307806c2200b0001866000100c0c840103131a40300d04a0b41a0b05076580601066005119103418000c00a141240103010320300603604500030b140c4140100f00e01c400171408540110040f41c8861107510410000240441029030a = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 249579181 1250 249577931 249577949
    0x5090307021e1314150d0b27060601020c04020a0c1b03120804080d0c0e060c100507020a050a0f1a1602010b100c121b08190503070801150504 62
    0x104030020300704250030410003807401d403800b100000c0f8030b00e00340007681c01c568200b00d0300d400340600141200540b900300458100b402030060440302140d8032a40d83c2c001e0b0959a6107000b8612840c8031005804000c030040f1201c1220b005009586440310010352940003103011240505e800080000c22503100b010f151b484260721844608080030540c503038000012440c08125190060509000303003040c05440c1140c4601d40c0915502c2c502580d10420002500700c1c89805c5c400c1c0910a040e04040e40e54200c094000920010000d08500c446045801c0581700042d00800c01d6400801728400480e0340410840500c0340c100702c5d11158809940742c6400d031148441c5c401c04c0d20029201c244114100b051315005106503c039030003403200701003070000c11820b8600d2440c9031012804581c0c820300003818003480d0001c14030503418043c008030214032480c0b10740ca480c0c50307040340c2d40440010300c080c400b440b48a10410264461074010f08614050001074680c09040c00b5050000e0320308107051500750302c550110b4002c4d0451070 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 249580431 1250 249579181 249579199
    0xa110f07090902040501050d0804031502040504180201090b03010b04050909190f0507050102060112110114180103060b0313020d1704120311160515091005031906180509030702 77
    0x241000700620120328124070650400c00000352038035100106803c0b80d42c001116614051450783c0d0350952055603818400f18a40078003000070075039610712034400c0340ca5441e00c1d050707180c624602c0010440c050a40000070420014401408000015016101516001c0e2001c0b650b580307c9001941ca030104049440e0705040d0f203103000e1010000074042501e042d03072080d01241d040c80e40703900059803201e1003402001407842491800d071020070011840007500349410b0400301c500000d4030b00c00307505581c803441d520030031403e04070031404080d41c2c14462140104055402141541410b40d00c070406008048400b070b00c65a007450038201408221408a000301c407c802d403a654681c1e0b1382000001002c4c002d002940414400e4004041c5510046000404d03100a600e030720340c006081c50204810400c02c041c4c421810501440854003a4071000c0f14000581801c1c0c0781c0c07949910b407801100c4141324000a8601200342024030810048103007050648142004140c04680c0740d41301a46249507010794503020798440080 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 249581681 1250 249580431 249580439
    0x150204030602254e120e100b1c05010b1827030909090f0d020d05040302010c020d06020307030912050909011511100204050f12030a110f07 61
    0x159004041c24071006200500d410728002081c3c0ba03483c0c06040241c0105081c0303440040385202403040e068030352a48205202c00d086010001321040b40030f14500d079440b00c9074003119443c0300c0e007007001e036a90190844000d10609400f180800d44074019021202461030701c5403071842240e92203503810303081c01101302030a440152032030410601901c14005c00c81c3c01220800000c254001c4003113800c0d44110195001c210600988103503406010a00c00c007144201c0c08244112405542c800e09c3e901e0280c04003500038141d0841d107881341070074003400c1840f1505541c407840300b262089803c80f0582d41105d40900b403011400b0310500116541000d44600206041d1001040002ca030350140c0c0950300031400740f081403101900310a01902d042c4101068240c3c071280c894010026541024528144100035107030291a41d140d44d02d04c28941400c2d40403e42d1020f4000c10705002d1400e00c00090103085608440042001d100108240d80302d120f141c0c640810000781442072820b20808120301c089008a003812200040d6035 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 249582931 1250 249581681 249581693
    0x9060317030c1b0a0204180827190e070203070b0106050901091703130501230304050c0301060609080c0108070e011d090702100f020a02150702010f0c081905090601090915020403 78
    0x5405000c1b8880c03890141c0b4140742030421040030296503401500c807440c00c80100300294500e4506494059652048030341030f205503e4814410710421078000d565120141441980c03008000d0040400c2c04540c0140280800701c1c071111100380c11036440d810542c0d541c451050041f2407048540d08241e014814002030700d000f83c403001004007245030161101481c11902c69004503483d0480b203070100840003241015040b10403600b002140c10611400489043c011080c0c0800e0a40d102c41d8015400f18240d4030b010030108070140600c003805203013464034444904d045070010f05900907190b400340c100310909004a02c151910301426024043c010050351141c90000e90003583d4003542c40e51a206582011140d402c440e043e4025100d102005402404ea501c61100384100074400041c9850704564851090805102c0e1900c43c1442010180d5600e82c0246070036001c2e0601101c0f00c0f000300c0c1c1c0661130309003013141c000804549181501d02e48a004140080c89044c841c0c0461082d000f81c06810344006000410019 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 249584181 1250 249582931 249582943
    0x70903050607110615031002090406031b050102100905030a0309050c040603260702030c15120109050115170106050f07140604060e060408033105010902010909060317030c1b 76
    0x55100e0440d501a81e401242c1720451406240050f0190701c0244138010701281900a8a4a00f1014100080140e43d03902d8812190145003496030b05222900000d03c0b980d68107000c07494128150304014444541590b550030356074840d03491440101940c80344010200101441a400f45040041050011030346905042d0700403040080040300c021840111403410f40c0028003a6a1400d40080147c050702190200b480001014002001b000c1c48040203041c8164040c12a0f1902824481c0c0d000100c0e50306011000164180070204601404032264905182d03414250004c0e0548880d89407070781d219611484207452502131f8441c001c000c17450002d0118483c80c40050f0180c4501e01440040c400c07804030275030341c82d10307030b1b40545014200030410400220039200c41e1021248c03003880e12151890707000f0401214440512019003c5885945558980e825903074403000c10b030054080c00c1da00300490352541ea60780c0200209811650b001c00408000184012120015129203140c9502140003040c4598000c9807142 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 249585431 1250 249584181 249584207
    0xb120a05090c090c030601090807150909021813180f02090609040528142a0f01120209040501080d1103090a090911030d0c1118070503070903050607 65
    0x94a400d0000d0740e114000180046038040240c150585074807808151a403c0c0e000a00c6141071084542001070020b4040001c00010000d62000c01c49840118a0043ca03841b0117900c0f05480c5401442007411540810304050200e40301114a01c844a02d00c198403405042002983c0c2c0f1504650219181070110719018150610710071541c9107a1640c40b4400c1080551003940c0c0944240c0c04103912160502c62001d81d0210004400300c1850040d001d07585000104001c14081c00c415000300020400490020b0150304000a030030407008601a40308002c03c100c0010041140d04200182c1d186000c01c102c0e56048881c4110040d100340003039038468200d643c2e961910072629001030905000500c0700100071007510003520004111b04031451420041c0d90282900304c000351900070740c1c0401241607a408120303078840d200d42c9844541150107a0700b064400e02c0d4a4031070150180e10701001c49484140c0075010309a101821341421a00c07078071130704003c50743e454071500020842d110f00014070070a90382001350a6501 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 249586681 1250 249585431 249585451
    0x40204180b04050702030307110a0b0408180a030201140d0b0d0803010512010b010903030e011e030507120501031502220311100318140f010f06061b17030703060b12 72
    0x600780c5030600040b074074111034881c0141c0080c000301e448288554180b01c040340c114021241c120f88140c49480c90b40354261030840302c0680002c0c0d051500e80c3c40600e08030a03243e04480c01c4661600c0d40e000a488002c008141c1d0080890004038503100302d60551100303000000180184000118a1401c40341a600a001300351141841d1001e00c02c19081c1400344801007041a5600c0501501e10313541a205121a000c040c0d060001c1e6070090000140074503081048164142d50220391410032080c06007500c544820980c05141c104070045c8040384400782441900240ea44006070340d1801442c01308500c411304103011044500c410f130000144140040138412a4400f2120500454a1032409404940041c5c83c0f09818140303001111303000c51503490440740030482030780a03070704804001825a0f084030702406020624580d900803e000c8664002400325441100c4883c03e8041d00b0316803241501d00103411414218400004002000b040c0309070403080042001d0540141c075441c03045400306220408994003450 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 249587931 1250 249586681 249586691
    0x9060f2003012102010509101808030a080c0a0509030304060201060609050607110f03070503011401090c09050607080903011503030e2b020d020d020d03090e011202100f0e04020418 79
    0x200e00c004084904951000211401d0b000c0c400c40c442d1006404900f09034140502400859803640303030080e4421800d0300aa0b140c081004030305000130710311034940e04110101d5106120202d01907401ca031800e90018900482c2d43c0c0c80b010620300c100c8440c412100d6a41d0035001c082070000f402501504a02c042d50312503124411119262030900c9482c1c0a402c40240c104181d40f038070000c65091014400007000000b40c1911605a22000032900f554150b84552600c1d081c0c40c00100101000c0e0303c28241a045189010760751949001c001501602482d603000c0e100b070a0009004c445a40e0941c411152503426a490700c01440c0d59042c003419946481c54964003840118041054441c07036110000b404043c1c0146200041c2d04035020b01901030f9070640300300d03000703c20107015a0142e907a000b1244040b9110759960025582441c0d10f8803520340d010b0703020741c600d100c29141d40c0006950b503085807028540e40b40380c410f81080172954101d8000d036203c00c8803600244000340110351041c04499644032034041140601c8 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 249589181 1250 249587931 249587981
    0x305092a030a08121e28060803090f180408300403020d020601030b0a0f14040f02031e060f0c0d0e0c1503010509011203051e1206030303060d060b030109060f 69
    0xa00050301024882d0240d10324000a292440340d1b0103a426000ca207072804085180d404840c0000b2034290350840403c550000c40d214200346403001c42c42061003c2036800f007108800040410340801d03001b034802072a907400861408108000c400f00780c80c0c2c820b019422482e04138100c4204100780320003a0350607001801020b2802d0500c03070000030010b049a601c00c2403040c0998900100704028074000b45400e06d05902c1c1d29141013400a0002c0140c020742c01241c0740c085203081031042500d44006441020103030b100b01380000004002c081030040d0f11030603032910713022150360751242c1c850b1078400c06040c42c01c11842e11444a01c900c000044401c40e9140c1558103100e20b41112410500302e000c240b060a5000c1c0302c1d80014003c0342909401000b00620034103150742840000c280c020550212009422411040491451a901d105502d1590007c400f58003840c17860400c80082150444207060160030180c4440182101e41c400350b001690303054002004000e01450030941c000500300ba501100029038903800489 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 249590431 1250 249589181 249589201
    0x6180c0510080610020a050312100e0f0a0510081b0103150e041e0c0605030402030606010905030a11150f12070306060906140702090c0c010c0305092a030a0812 70
    0x101e80038125260005a641e03203008110090b040c10710050218020615600e0019900700003804031503444618016640c54081c1401051410030750048000b000a10240300044825900300c40d00180340038404640755a4860707013400002c40b15481944684141e40c04c4c2d0341d800d1680400040c40c1d40742681e0174460b20741d149021034030031400d600032002d08009240204000420485182d8031010010340003c1c991001070300c8900000306c2540c864408194000b0401c011407405001c0c01e0362080003428802c2d441d03410a0086990794241c83da000300200d0650103071304442d0343c840703d101140d401d121445c5540c070b4903002c03840b419540002854001c0411094041081c40e80a402100f0940d41e1701c0d6554040c01d45032190440f041c0d802000c0b080c40c00c0c64100901005611850140c91003803541c40d0080365162080c4d007055003140d02a80300e039000c2601e004103201060303802044140702050220180e202c0c0003002d2065120652182c4001e56040c810380c0c442004110103540034101940c841c0d1b40c00340d21136480005e11 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 249591681 1250 249590431 249590449
    0x20a12110909070501231612020109080a0503040609320708031608040506190816050301141c2105030601210f0c020705040b0f032806180c05 62
    0x2c510140c22248050041e544075503c03200500484124005d80310307900f400f0090199000689843c1140d80781030082003405040b40a052207400035200820041020f615009168024100d14604021002002c07605200c0c4a410941c0c4003070300403c00074000421402541c407418020b0019030f110009110a1483d501404a4940c04451040001d03600e080078086001c0d250340c0380082d00b120100c030203110200e502c0c1c444c480a0000180c02103c3e0000c904020170000c4d150a500501598019074042a07406120b0f6202d4182c074115070001080606644c400c2d00012541e4516440c41c1002100100c02c45090220550040b100d940e00c4064043d81a400c0140c12030f81844104d030b09a022402030740160070640191400086035103a100d03400500402e40103590401d80c4e8901c0d100000503404010240403c2c03616104524845a01702e0344a8000110000401c2e00d03040d0115030141d001c8585206440c402501c4001ca01c035040e8058030800c40d49190b212aa408601412001c0c1e0380802c2046006c0343c1814001e001d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 249592931 1250 249591681 249591691
    0x9020705030301090c11060702031b010209030d2001020d05040606151d180403021e010605011707090b0f030709060c03050d1d0106030819140403030309020d020a121109 74
    0x2641c0b860382040701d030001404001000c04104619002d008084070824000e090013149613074080c0d075a68a0708010382c03011211641c504034859104100f152641e503400039845c01c200d00c150a04241c00740080402003091120182544c40315400064a000714511a9101c10300c40c912a4030100b211549039145180c0380202e19112502054154041d0701c1030b50140369000c42800c8005040c04e402c4c01c2c80e100d1020740008151030407409648911440744022040c400c00c4000441040000c02c07045260800080030b0191040700304060300c50550110f4600c500c50311851001d80032510341e50b0758502c10502c00301e00c954401c484020000d80010804a03502d40f02c1c01c050f481e81909555401d04000140c080c100040c5801c06403070140d081e20390261912002c00303024200040d8058a02d107030300c0e88401e24240b10704400c0f5040030b038108a00e030461002200c02900c151000d0780e03050301e000100001c16101140641c04044000307076000080d52030014000c010708541c8079541e880b840c0750125050f0780c1e400b8808074020507a8 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 249594181 1250 249592931 249592933
    0x3010f030807021f0e03011b1202030c04090908040305120f070809030c03100e06060306040201020736060623031602120403050c0306090607020304120204201309020705 74
    0x24104040384504002e4109070340000c1c1101001815110401c0400d21082600c40c00b140c034400101d040780c82d00703106902a40074805003100841450000041008400002202109602002151800080c84103841c0a840c294004201c00d103c0345c18505080d400c0f5220443d210b114014846c4603008801781520318204038101c1072350178a00c003603031000301ca90421543c0b42d030140301c0c480303004000c1e0ba820011404a0000010005205040b840d000b904184005000c1c50180e4000014880182d900148030421114200c80c142c0c81560003400c0b0103441044a00c41b40c409548160035409100c2080e403003a01160360f540c9410b2504600c0d1096080c07104401d451011410b841840068000c59a0384840c5620028901c1036503844801124040340b40c5d08560001c0d501c5511039000241d55003010018590082c40000040a180c0f80646000b9a284114010381c01281d0b00c148100e01103451742c0c1c200c035a401d080f2902d80c002c2d0501d89900400240c22a07030034035a003c6d0f200d040024001019200b1150f881d60450 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 249595431 1250 249594181 249594209
    0x16111e12120301030f030203120c180d050a0b09071205060712150302100201090c08030903120309070303032703021f0e06010b0915040f0305010b062502150d0204080f030301 76
    0x20302d42d0b074080e170081c403416429070004108100a0145030440c8903c201c4035110443d445201212000c0b51121002203003070b004007610011203006c107000252071242c41d41e01c0a0400b00550341e50040c0ca00b001255400b140d8407400c0340c82440c1c100000031036054400d80d19a0f58103640c04001c00410410f03201d03c40314141d0040d0f030215040c009400d000c8001006200b00c2d00020a5044e1156076a13140b00e403660780403041c60341020890304003614040c0304140c0034480107c116800d500301120301503194507080c1b0008040c16030301c4061440314061a1840c007404040300074209006552810007940713070914400d40701d0300e60007000802500d0001500c2141c0d0345050010040801b41e00740004815070750301c1038000da5401141309913124080704c1344400a002505040003440c5501d80b46260141c2074072050070b032a9208140a104040c1078602000901c408524215500c1091404c1d5001040c8104201450001901c600040041c1c0714441c80d001007080340c1c00e80c41256a00d0380604900d5449001c02e01400c08450340b40 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 249596681 1250 249595431 249595433
    0x3070f030605220e12070b06010903201309080309061b0a050d110c030a020606040203010308030a020304110907020a030917031b0c040203040c05010e100516111e1212030103 76
    0x8414070000c402406074001421800812039540380c01c039a1041041a40c5000400c01b00b000600035a9540081d002c2c202090000d00315501c0345080582c0071580c0c26500025071941070160345060603048030074498502042140d8007820215116401115a442d85100d0400401d980711036000001c00c5003041c500d80e080c1040042503007103035680e1108480c10b400035184c00c1d041c074040c0c200100900c00c2205980041d43e80d407001040c064180b0f07000038000ba100303034814030041022410000840358403880c51400145c1d00d075580d180203142d01480742202078003e07003590100402c01d40c0000f41208064040d84440700f10940d640d4496804409101c0d084a00340c0092010f50340141c43c6046401c0c2200a50040d600c1001240c80420100d0304201c8050702c61003a030840c03c00c080d50b00400380c0d4480b6041551804903011101201414034843e00140c038001c081803240010901006c8803e050341140b008164048920b41c0780d41d80608804080742c11803241d08010ba000c190302e03a00040090928807a250700074116803035 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 249597931 1250 249596681 249596719
    0x30b151003091b0608091b030a0210031e0b0406140a0303030c210b09070f0206011a04050301060e010e160f05070606090c0c0c05040c0806040b0a0b04030803070f030605 74
    0x72030046a1400740f00c14076107000c2c206040128050003684d0366045480c0307071620210346003001070b58441080d281d0390150408640c07408111800c036140c050b10b102007129100141240200394400310213540d07103c5510000d00e040f0403034000940340c40040b10140300440d1501c034202000c10303a14580d1a03202066401c00c00c00030b4000d4000b844544010304060020030359031444000080aa1022035002a50790303006c601d6545090f07425950810018504001d400c1d1205002968540043c0035211414101709a01c402c0101484102e4015200240082c0301c0555074808046c81d984080c0601e1000c0b500e050300048121464a5443c104004035990f60000340401c8041a10395901240055803040e8403060003148481031030040d0320080c100340d52145942000c40c200704000b00540d804c0148694202035500a109511184150f0020011100055a05d185100161042c4e04079804504850b40105000041c000d6210245100d141c50303444569500d50304001c218100c400b2401410360082c0c08200070a00d80d55 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 249599181 1250 249597931 249597941
    0xd210605061b070b0706060521031b030f0a02010e010b01080412140d0c0804050d090b180402070b09100605060909040809030a0b01180e0111091002010906090804030b151003 76
    0x50b81200751103a240d15a08511451745c0500c505450807911200304010724101601d22002101100101c2003035081034041050700c03481000c0c81e0038246041e84400001c0e120051007203406540120403901d60b5002080d1010780a8201049460123551030710106218550043e44002e1140b0751120f00c060200800740c4042e11411031b11f80082035189001d2007004150f80481c071824201c0201511045940c0c80c29141c181d2400200c01045030411002130070402c08901082d0695401c0070107480d03003c10b0b4a49284c0820000c0c083d0b084040e03c042401c4090090301b4401050201c240708122200703204c003588840901c56503104090326550032010301c5000030013185075a00540f5174100004c0c1035502c150032079102d180390100e003a003007c42d000080703411580050000d1300c141482c00040320020300c0300c101a070260480c0ca00036440c0d000e004030240301082501c14402c0d03111000f01940003e04028001d618103201ca280c1d00280807c0b02c6030780d0800041040107100c41c0e9030341000a4020075515048042d1401200540 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 249600431 1250 249599181 249599227
    0xe060108011a3a050c0d0803070e1201060608060901090207050a02010c060f050103032604020a150c0501020a0f0e01031829180705091b07080c0d21060506 68
    0x240f4209284000c610000250010f0720f15a1200038803c1d0540e007091820034045600c00ba216581c69001800014144404d81c2d9000c3c1c01d81c10040c0d0500360f01d2000c5503014000d1001030b40c080d4608240401c2c250b070481709850081009403400c40086c0e8a0b41700b010704910544e0400340080c1d2205500c100190b00c04c151890143c1d00c26000840d008800f4580f1409840c400c0c0c00403004039801456040800c0254038021180345603102500c60981040e0b004a40442024044e01c6140c00c080315a20300f00c50b0049214101c0305038000000c40d52070700380e41d1004200098482d07088000070710030401305605601c00d00540c20780d4400e02c014800211090b6a8441517400040b00d031110b503071000c0e90181d59480c100030405100e42e50100c02c0788030044a110700d43e030a200c81600440d00c50a0240c040c0b01001c80d90f10f2100c0716450308000303d180e071500181003450040c041c40000029130700ca02055101c840e6407240010b45566402d2254140628030a0390003020303120240202c41e0000c105000c01108202040c25101d246 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 249601681 1250 249600431 249600469
    0x30403050d0b011b0b010e1023060c070603090302070b03160806010e15210c04091e0603030f0311031605090d02031203090f0607050901051e0408010e060108011a 71
    0x2409002e0701101d8840500c19082d54155103500040003001401680f20350720244180904042c2424401c03041b42642d2800f51240241c01c09c000c10a080d51201d008452151411070b04982a079a81e40340300501070050650304800500401c0400107960340c0300c0003524011204005902c6141815500842d4003031070003000e544c1000b00141c5422450344558070060704150440341490342c2c0740d000003415410142545584010441403c0c00c00800d04005001e540c26520031480204035500d070300f41113005000c81280c00103071075840c158000003015000f07814694090107949050002c40600307005034002e8001210003041800c07030302580e8040d00b4441c0d401004046d070004c10030f400d0010543c020a00c0c154020f05030000c2003000000707100d103101c0700300040712440c0500c000032305907403501c1c0c6001445401a86c1c4a941405004156008000c07103a04401d00b403480b420f10801d0b220390f030328450140a4400086c03c01d400b07004601c004a4069410b015030002051008440d03585882018144000c000001031580d0003 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 249602931 1250 249601681 249601697
    0x20a1e1d13050a12020c040e03070201020c060a0509032e090c0605070507030512041707031a0924181902010c05071707030605010e0f16030e06042105030403050d0b01 73
    0x65000c1c0008004c101d21170f802028810071007030034801107403003800340260741d079100f8084500140c0c0e0005e101004224282c44054132440e8810381070300c45000d449002c95145c0a918940c2a1004628880805500032149540030500089c03414000325107107207102034442080d82c1800c1c89403c0c00707000144202c52082c0d088920300d035135075200c95080100d1803d20424603140018108030b810040d000c4002c031084080c0181101034a16a00c1e0303401034405146030303584182064000ac022480522803004941c0d9038906001d50700008a44100e101c000c125002084002c00b54070000304d603503002458250b44c00b4640301e101503e0300a0340065404120000040b54544030f21706002c680c07080c200c0c80c11681040e410004000c0349040d4600750083d0b500507000b42040002c004204100c20b1070120200d5000300c141510022900303a5844110301910500550f20141c3c0f03d444140000c02c035211f420199000008901ea02c109040c050003210913100503540600054818000c44e600c1000710750114040e40340504090754 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 249604181 1250 249602931 249602933
    0x607171c05090606010f05040608010603050c0f0a0c02120d09031e140606130b060a0311090a2601020906120a090b0a050a050702010509100513020a1e1d13050a 70
    0x5035082150200e0b590b80001c1e007485000c0d40c2101c480d401911380c03030074410f060a05141c40101126030512500c410140c4039000302c3c0d5140c0c05a0200c0c0c0e8510340c6242c426a40c0e0086a01c040c0801e031a10b042240980307540e840c0744a6031b0002040041440e1856951280201c0c070310784921868540e41e52101c40440110100d040016030140004001e0198540141019107008010418001d1081d80394150844c1090005c52013a6520401c80380300015a04000440388450030300010103000c0e240003681c10420b10003022a1003803211829000040b03a00c45203000c10740031411b400b8242e000310520f45400050a120078a004800200398540c00100820001002d107038641b60701700d09101c15280d0720441d41c0d0ba6070500c02c0c04266070150980c40601d5000030702103824500c8030165501b81c0203200d1640c460750341000c6203405032410044683c0980050940c58416201ca000352000d022190551807010000b03400010009281d91000ca40f400400d00a000389540301d804010003180780d0307101180e03035000c0c8500c104 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 249605431 1250 249604181 249604237
    0x20c040e1506040b090f04120e0108010b160b100f0f030507170f010501140405090a030905040f0b04020406030c021b1c11030a08030a0b010c0503030115050c0a031706060717 76
    0x1403246c40d010000c0000c80c102818081d00b8103422602100422080e4501828181d81010083d41141c882d581c40070390720990345035000381108504200806007440702c801d001c1951641400c000603584016004078440707607076203580400b551342440000d010745c00990041010303010581030030582c2e2080c001950310131410200c14030f08503007098000a440c400d4100b0080c2040c1018802c6960080040d0001c02c020441034401820a14a074860144190b441d0400e0814040d1550010a4a004003070802d5440d40d44501014000d40b08003100d50f0700500c0f94020781002503007114902c10407060098528044060825102e40c08a0b81080c000d803409040c00c91070000b00d880800100300001d00079581030780c0764148060b2070001da8021070f45d40c07030400015003100c10108002008890460f4030305840e03400400c40038141610366000e000e591884a02030410010300f85034000e1118141c003d90014022640c2d51101c00304851400b42520103018003e2401c400c450902e51480103201b000f058500c849243e26185083c1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 249606681 1250 249605431 249605449
    0x200f0402042921011404090c0b0a0e0a15031103150103020d0204122303090306060d062304060f06030f0b0a240f06021f0506011b0302010c020c040e1506040b 69
    0x11544030043c81c010404000d144c00f0040b0754510441c0c0a00400a517502e4060030b016442c040c507032240c480040c00c02c6040d401041c84440500c00a483e51000507514141400c00c4000e807840e500c0801d04008048070200d090b141120b02c9444088a6034080030b9a107c011402500130681e500665a400c01000c00c000a00c110110b0b0789a1081c030782510007215030036184503181000c2e80800f400e0741c0140191246a600403030496841034041e200340d03d0340042400e04802809084a480300d20804418074020500210340c0001c2c4268050803041c0101c20103500100d08540c003510001c4e245031074642d0800700013103855000f80c0d0041804400814a2020f00741c40a5000145402101c119400c0071000c200d100c503841c8a2a009240a002816001c0b4860800c0c3d0440c02c00c0fa0210042c0e15500c0300020a280c1c01016402c246010301c2404065220340751038064004d244130140000548a04080030307903a49030602850007100210801341c091410340000300b4a0000d0050300090780241c40e4600010700f503c80b50b0807 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 249607931 1250 249606681 249606727
    0xc0f08030c0c0301020301050a030308060310240f05010e0402030a0e160602150f06120304180608060f06061803010b100305010f0617071209200f04020429 68
    0x10395614503074066070320b203000c541049950081c0d00503c010441991071840c503004880d01810040320303a81d82d41001074100380240c1006c2c2822458100140c8080b4540304012000548002d1004071aa4651603014800e203904d100751400540c100040031220700b4250082e43d000700c0307859808103020142d40c160500b4144659010369000031b80c214104402c590401c040c000b101c8240d444541c642c24114049500004000c183c03d0041d20072a804061b41c1c0c0c0100304440040c0901e0162080795003603040ca00f8050000c91003138030031502c03600010601c0e0b8402c042a142c00342500802c40d031303c1d0096445011981d500c0702e22450b03625540c0c800042d00c058440d0031081500b401c1581d0300003095814041041a0301ca500d4201004015050314003a21241c00c46502d40e400559a0422000351000602694090b1003182c0e8014241b000c151100c0e68010442d540704481083d04490103888442004248012406144210030315079101c1c500d07000e0080c00c4126400c894100340c0381402e15242403c060706210301e0070803003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 249609181 1250 249607931 249607933
    0x203120702030c010609022a030c03030703200c1c0306030807150501060903030c020d02060d0905010f05060d03090e0c19020303060a121a0709120506010806100f060c0c0f08 76
    0x55112141102071040e01701501001d002141042c2014495240b0500a03800d10f4041b0310801400b111410b6040050382c0d0380880a2003140d86c1d038031740f180004010380041c404c0840e0b07649030046001d80706451201660501c40400b40145440c2508081c035500c4505000303d2082410758510700400401c0e1008014021280642d4400010705c0d50b43c1012000c45405038000010070000100a20009500103031f0b070b0800750340480d1400d9407401e042c00010310038800c44580e03500c1680307880c4046042080c103410617031001c0b0030340d0004c001a0303540b0070030f0181450042c50300a00050505909201c00000c9a042c140c000170744030051414500d41040c2c070114240c00e2550030f0056880801000360318a800445003003d0443c001b03081c2540c0c0440c2d82d0340c203928800400004084003e8400240354948034001140050281c41008200c2c15090308106464840138014100c00f405004000b5130650b00c0101d04104551900901c00c0c0803038a811003c8580f04604d4004071402070f03026800240c03131801c120420020b062060 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 249610431 1250 249609181 249609187
    0x7030305030f01060813060c1205090c0f0a06050904020c190b0420131e061206050a06050901030210030b0a060807080f10090e0109021003020306090906041e0201020312070203 77
    0x5102480c082d0059000c5420000c013201001401c1380a40b240c00125a4090404a9406140401920500301d24101000e4940c0303014100b000340140000e603070501d44002c1c0d88020303200a41400b802202020750080d080841c804004101140c14590300612a100d040300603680b0405402e6820305004034004415030340512450705100c02d000002800e42088200c1000d800e8896881c00301007040009070300003d028031035480109845580c140c40c003802d0300003014841000110b488013081416240380c00c13016924ac41c0b901000900901d880e00c0b4030002d85038003c1208146030320315070800102244a4080008142d00e40301d80039100d03110307044100c1c041c1c40181c640c0c4000b0318103802c00410000d001000206110040c0080c8861701c1060b50720710b01036842000c0041503544a0030f84203405490f0700400250407a500c0410813071925850b074055400b17181304846038892a1106040a50303205001d0350b014115641c0b000d0035003100c403034000190055901c1801641d0a085c04000010307500e000445910340136070000 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 249611681 1250 249610431 249610441
    0x30d020301031505150405090a0506040b180714092d040b09011a150f04090608060601091401080402040f0507021b0d031e020102040e0a0b011701080a0f140703030503 73
    0x100a030f11907a0810010401041c0f6003290401101d10703200340c045001d9652100421000e800174050101a55082800c0328680d05180ca0300038007250085034914140d03807060990129084002c1a100101c40c924020420070100001c00c00c4482c40000d01140040400c0440c0d101d80a43c042030020400d200030702241c0300601d0142030141d80c00d4002032500c3c4241c2d140280221540c8440c2c03a03150760341541511805c4050488400794100c4d88070f00d110380807d60f0000f03e80010a010a80c0007001030300d01010585030191034101c0103643c02985c601030a00c01c2d41c1e1407070090040c0e510079007002e54024001400401d201d13194450305012140c0507940780c0c00680100710242031000d20b4845004000300182c5421440100d00d4800521903050b030450681990b03000504840d2180c800d4041d01c0180c06011030342011414001c3d21800144120900507000c90340c0200a0701c10740008510345812a01d01801138010f006840e60303500450f001004085840c200600e200382103221080100300041c610035220f0503236034148 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 249612931 1250 249611681 249611693
    0x403060621060b130e03090414060306010605030c1b0c031218040f09020307170d090609050d060f061409161b1e1101080907060905010e0111030d02030103 68
    0x415000740d2907a0503075024041e4608000c980740c0ca10550010800644442c40700c000030300d54102100e0000034103003055100030103182c1c080010081050704540401022403948180300724902c040340d510303a05800c40c1004020441c0520011907004921602e480e26040446080f40c81c407001030095072440340d204290002d0142420030113100302501c100f070900d042118200c41c40b481c070b002071002103000c0c41d01d0780413a2803600c18580104810070750007020766503078a84541c1d002c1024103180484000c1da00c195005084c1c60b03030140b1030900a98600c0d58078ac146160814050021010b181001101c0080d07a40e10780402c01e0050f03124071005445200c14062444200604004424101500041801815a0b05003e020390401c086d00c4600500804101b001a26401d03c05c500c0794000345e018418500c401000f008001c2c0d51240403160000989420311951183e603d07c941d19800d9016002c0450301c10071051005600844d01004d0349041458120151030a4650607030a6410407034071071a07450740110050040101c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 249614181 1250 249612931 249612941
    0x201060f0905190501051f2102120c070b0a110c0a050d02120f0d1104090218040e1507080a020f0f0703030605010c0803040813080f0607020613030806150909040602040306 75
    0xd0f8405003c19410440010201500c01140b00d00248030b418820510034064540681190501e074103201d482e985e2860030101950040103000340303151400002601000650090b659201e800c5000041c0341e41d100100d80d8010020707504141d06103001841014022402004410178080c89034014200c0b03603d00301000b034174100b4000d001c445484000d001031700d6580348080550b80c04074540702c2d02040b03080b01032040386064403554101c0720215000280d2a500b0f20f1a0040c0d0f901c6c1c540054070100582c0e11001c0c843c075120141c4035401c0d110303050070070007144190f48108611030b04004198401441e040440f004545290321060108404540200b100390a05070584a1038004000c00c3c28105001c1145a480300074603c0024001448402d02040812400c00c00f0320a4802a00c00344048981d03140b40250101d0f5241070131100c0000520820000400c10381b00c404d00f42e40c0c40e41d0300d622002d203651940b104000e03482004101d4031900110070700c66540c140c1d48107106c01380260b0080b8070050f0f6450031030602e4400d40d6 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 249615431 1250 249614181 249614221
    0x9060a020c15091e01050705030d02070c0e04080304020d1b0f140315130c030602040b031918060f09120c14070e0105121507091410020a0807030201060f0905 69
    0xe40700740807401c0e142e01c940e000c203000d40f003500d99070311130039455500140d500740105c040c040e120f0300c0041650600b038a02c1f035009114090090401c0300c0e0305542c608600703660781c1c0105c034003c14600041c8081001410110345c0704003654800d0203403544034400c16404185e025000e80c41140340400d000d4040200c50b40941044000003030550152211080500383e2119140025002440010042c02c20005003d8400382c0c02e000b07160311800c29135440d80c3d039085145040d0410303642c54600c5920300c02021407501d00c61240300d0142030f00141400c0d0782c46454403600010116440500e2103d61104028000109804070703c0700c0650041e242e682c034074106400c1200e00f4131000d20100078240e122880c01d11984c04070821070f6044813000c854070000c0c04031680d0305500700403071160070780c50300c00200050185898000800c0e505568980b6045409011a60100102002c044040c513000d6008189403101085140e401040c04500a000105078281d130740741d8528201350140d01c0101000e513608280034400c003810729812440 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 249616681 1250 249615431 249615469
    0xa0f110c0307020d0809031b01020105100315020d0e0105040f150b09010b09012606030d0c020f010509030715030902010906030b0120010e100218010206070c0602030a0209060a020c 79
    0x268205100540c0c910036044040d03c84c0c0c090041040401100c041214074051014042d16017242c0b41c0c1d00d203ca4104c1d11506010f000d03508120005805003004c07081f910442e9003255003002c000d02030280d007000070750140074020304a80e296050b005410800f405464080c520440700e10002c01c426040032040c900b000d01140310003600744a02d10310301d0799071001c0a07411f580c05091b120b0b548122010060722103c43c904001100600046210321900401280091080d00c0c203400f52001c00c1d4010b5400c503500103a01c28001d601001c940854034041d485480500b0000c04040c040302ca00301d48a18003030b0f0f41e6070303068550440041d444004003401c65902042080041140c0d0800380b00340f0003090006040100741100051544e071b002c03c141e103112102500700c10191030070380c4281e400c1c0c21080c100c000301940c4105800321804095035a0b4040700d510010f24030b0702c20340380c1d5660791119103000d5480001a52010344504001c940a1101e8141651400018504140d0300e40081030011080018050b12030305002580b031031 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 249617931 1250 249616681 249616687
    0x190905100f0501050a05070605090c100c1a0402010c1505070e10080609041b030b0108011109030d050a02150112111002100914120307110a120309031202030a0f11 71
    0x26a071481d07240303059500034248680c5070340c0c1c0c03454110b84901030034a000d0070f128100001e100c00017401243c01d045824068881e4500194500c80580d000742800e000103000c4501005240d1954038600703001a08148140b40640d0242241d4503411580c0f20104102c500c99559603090214064200e20100510321041d03a6006803000500070140c2041001040f0a001c1d0790a00005020070400f00031285220b0340c040e082d5110680c890800c4040003100b4000c0034410f40c41c0c58106801400041d040c3c5d5000b5071300400400a245004d0002c0f2140e0704003600081c15803068100b025091014099170502a112809242e080d800b140e0500e03075029500d1880c0760303000f150b600458107034055001c40c03110307280070811078086640345803482d00b6410380d504013078028034038000c1c00e480b100c0d444000b50086004020340d5a42c020f41d0180724030402c1d101c5026030300003021400015074040700345000b81c0024003218040d0421400541c0d260000e1410f03a4411100007214581c0c85141d409261038510a0b24691000c4000c0641 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 249619181 1250 249617931 249617939
    0xc06160c02040506010c0b01090603171303121806050d0f05190b0d1203090b09190209090115060915180b2503020d1e02120901030b19090510 62
    0x81490035898000e0300840c3c0710800180580d000c0c4414036501030b03001c00c110509681d40c2e81080014031042c0401c403081104081c481c008004141e040d5090350400400780680c0c4c034a580c1c0c84002d000c5141a4a8040c4044910f860002c0803124000c98004c00b07a40d12403554401c400c24413142124401a05232000d10b24107010710160309941c5210b400c4560040a000075400d2210000440e0708207030f00c40041c02c1d4031300410110341c0e06515420940d00345115a000c1c854a440b242c1c0001e48032400440440000c00d2a9031030b040151804001c8650010898000003a107916140414100807050b50403080100302d50741d00811040c03000200300c501c28481860320302c0e440040303200e403010000480d03c1140d4400c9004100204196001c0500450b100500c0e05400800e003900e15000c0c0d140d00010002802013881e10050703c1a50f00158201301001d072482c1d01400d95842d502d01c642c0c0310b42e0881c0360940e042541d82d82946180b03407511000141001c0c842c1101d54a040d19000d443c0068030b1303000f80030140d00d05600701c0802c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 249620431 1250 249619181 249619187
    0x306060e070c031e0309150c09050901060804063201080d050412020f0a05090406060e0c090d030c052e0506010509060a03020a0c0206040308070b091b1905060406050c0616 75
    0x2404d01360001006007400c041c000700841c0540b003141c8002e032545d00000102d2070f03522001e5200a502d4031664a9181d101c0340d880d400c01c84407070340900c100c00102d01e504000800180c441d500540b48044011044543d0009541d450802d90725003c10b912030f82c24850005000c1014100000c9603848100c0c54054038103418401da0803d40011540024021144109541e0341e0350345800707484000d484054590342c6a49131901380503000d0040c500c11400f00c26000c001281d80c1c00a000200c40d440c04002d4504615181c05a4003140c68456189017602c0c24024151210000c00c3c0c0d0b05401e6441340000010034000785031180c819401c5400241244d8103000c0108100001900d491059441210342818016200c222a40050b80c048651a50003580b0a0000401108005120014246142c02040c000c80d0341d586000c18655250124208007230150b50304211940782e0318020100d09910390500b0603200c0c1d1b13140d40d11702140003500030340c2103940802d00c0030a81802c252401c04c1415404020340d4030301641348010303071000703 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 249621681 1250 249620431 249620447
    0x73002120906150a0531021c060e07080c09030f0102030c09040e010c0212070c05040603140c240a051b030301051507120503131a1617060609011403010306060e070c03 73
    0x1d850414010584031031b0440c0381c80384500c49810850640d0380d0302d503804881c00c04818000c0b5890595241c020701103000c041c10524248219000c0e100c022440d00c0d1070828440542140c210b0030750510416070107801c29002070014501076485030103401d484010b8002080207448098400303405680c58003900d180c07480d50000300c09644040d601d100554174851403d01c0b41d40ca02503604100c2d005801c00300d001080041901c90005110840001c0d02c1e8298891810008507049291039005028174401000c5c00b801031b458010b044040035070401c036107840b80f40032455110041700f1045682c541c1020004000509040c242481100c1d203500c00185425a035039240040341e080e04025100f04880800042c40c0300c294807080020260b00f01d14031a90542d40b0340141d10200303e00301c426600044070b1404800307056008030303203459010800c50141071a03643d0310340501c1000d400403c61035040101c1c211102424a0246e00118040c40c003690000c80c185080000f5982810300141c502c1c4100021f6a4140021a60040070 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 249622931 1250 249621681 249621709
    0x804050904020111010c120c05090f04020c0a0c03140606030303190506010c0f050607090602123004050c1806062d0d05010e073002120906150a05 64
    0x402551601c0d94001220a81c042c904008040e41c40c058210070102c0c0c100400110560420409014003103801004941364007400501507004805826402114030b49a005880640e080310111040000c0540300d0100e80b00c0c6a90060b11006181030009227400001e01c0401d502c12030582c019448e5003007000d0000d8a4400c1540d090721600d07038070004542c4a030310640c0410f50590300034030141003050040c100680c54600559000003c100541341c0000c48500110304103028010b1440360504000d500c4a803134054034a11b441030441c022000100d8545503800d2199207001d00d004c1c030020610031609105118852115665010361184081c04024082e60345d9001c03101001050b01c112040e60f0000f528500780302d2000c003100c410881021034108005207007544000e040b540060740805050b1035231002a1880030740000c40ba12413001d010500c40c00980d1404003c403100c480d61900500d00765032001c0103440c00005940030341c846c1c0c02c00320034441c4408003184500848a01260f807100000c0c40c12001496161064031 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 249624181 1250 249622931 249622939
    0x141203070c15020d051501020106080304031b08010213080d0219060914011a010806090f160504051005040806100807060c03020102071218080a0305030c0306030307330207080405 78
    0x8075404010140c4900b40050008900c195120054200d40360050302086031044a40401e0221444042d0b205018401c2210f1070b8101451a040c2952240c007210340342035840030110b000841c1c000500900900c0201480140c44803294800c07810810030317500b405020044842103621200c1d41c5d41c0c1e403150741c40e20401c00c9903020400142e4200145801403103040603030607801e455407074003081107a26a0304e5102c4184404090b6113041c0195140350411030004000e442001400056400041c00030700f034000b40c441e1641c10f0b03003407281c109556080041c4950311029607400009401050800071250704002c03994204c9204041204140c2c100700c0e880d0b0340d56801c0d2050008100c10050440203241c002c1d4111b0b8a00c4d5000814800c0140e02e091001e03140b41d08440403d06401404200007c03d1440440c10300140f0754195600c604c0e5071149000701000d50805807000fa4540400c0080ca40020b98191244034070303c14114400c00d003041440d803d02000000c08002e108118010071402001400305000c80d816550219 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 249625431 1250 249624181 249624197
    0x61e01090527040305031806010b0d0b010c0b010308040f0509070e041a04140601140a080114150304060e060901060518151905040c0c02100f11011814120307 69
    0x14121800d041e420038000102c0d082e104240014954003038011481b408201142402c00c9417914a6150390b040c01b48140303c507000050024144c042c000740c01c14941c0c01c0051400c20406115502c1d00c0d03810701000c0c1e00c125000213000508005036030b1000c000070001c000131140400035190002c4041d202c1c0307082c680742c58851980c0304110101c4049142140c2c004a00182c020400c0c0d852041e010030f5141c03000d40780076000c42d4001544049100310442102c0c07031065640d0b201c00e4164640808070300445c414021080d0b002d0340001c040506801c901d001f4510840c040c410110750b2101030a4841d080c40c101034040050359050540a21003515507000c08101c2c030301c00c1038400003260380e035031004104407904510303482e881892881c40300400e41000505a080c0d4030300320b4080219010680301560505401d000080d0041c500850a48580380901e03000400d0356464140361f03074503005846c925401c440e02d102403e800700080300c0310107050180103034410740084000e00042c40201002203880b881408001c0c14401002012 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 249626681 1250 249625431 249625459
    0x20a02040f0612030306090b030703080f0702040f020a03020a03060e0112030e030102070203010608060103050709060e010b0702033d090b0c0f041505040504050a0b09060f0307150503061e010905 85
    0x164441d0008246454a51007010244d24008003d041c4910901b441c0301d0070120109410302c1d01240d0502201e07400180189070507595294031800b07070002c900585c1e0050307661081c00d221342d10318001000b4400482d54010303a0f640c52104013a080340e0554102100e01c0c2c40340001030280c00c031304455507580c20340c244c05d040005504100009004e44113701009405508164002401e9500002c242e07042e607101d0015664699115200c4404035000c13031051840ca05004001000865808002040114000341c01d03980c1500805142807060147c00001c425810755213030705480002000a01e8038100c0480103003e20148005072211100014064146440c1c418001074110403401180c0840b001002c031114902c082060b50030029150390000d04c138440c003490030400021542650792044001102c0001c01c06051600c500c010301c03034130710055105c25405124217980820040300d0001500400d219030344c0c0b00daa480c90120184004400c200090311601910704031043d01907a04026040180c4400b0b4443c1800c01c103103 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 249627931 1250 249626681 249626711
    0x209061c02060703020304240203090906030102093609033c040905180601060f140f03041b080c090604060905070e03070b040e011802041502060421020a0204 69
    0xd806802548030304000b41041c209a0040041e10031520f10b0002c91100c0c615003900126026106000c2100603017041060b46810b2800c0d06140380c000328050b00040c189160b8002240003002881c1e040c41c00c5105264400e07080d040003400d00806142c02c0c014101c0d0a051080e2465a6030054085240b40e01b80506019640d039103514020400780c0c1940c007506d82100016105c4200c160b4010f0090710384a40c00c0800052450003543c0490084009000041c901c0d6881c0000403a18240565410000c001c41c1c11020001c0346016409046448252032030b445c1e4900707291422400380311403900c104480310440035003003041c060007080c1d10000e50410340b040005540c8410000e0000e020503000700e0b11451a1174280443c00d5400026800c6600e81a4121140ba40d1a50181c48a50055101780701c00300d141746005104481d40300d04124014504403a000d81056103c680c0c09000602c0f059a5078016840355042009101611156401d098002a41d03190b418006004c02900e5250103100070b03000c0d07a01c9805145211351 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 249629181 1250 249627931 249627979
    0x70803040609110915040b0d05100f0e010906050105030d03140a1107020904030305060306010b040f090207020d17032a03160c02030105010b070624050d0f020301020703080105030f0a020906 83
    0x800421401346441e03c00304c080e80c041c10b4409024003641c0f44c03030056007050820b5207000b8001500140100380b568040a1403402502c4100c00b440c5a064880b01e15070074a400c240035209055206d250301054075070400c0145450310407813028000415007407144001030302c1101c1400d240c2003e100040841d00b4241c4048003805c2e03205064009401440320000c010a0581c503501c464096a4100c0c15141785990f182c1c5020058065030091186c2d03480c06020070001019158002c2c00c10354400ba241c0002e5640c40d0319406010640540c0d580d100c940000200142c4095010040c000d90101c5441c102c81035444a203040403d00009200416507200841c0c89d40005002e80d0341000b110754010028441980c40f0040118260048041150201d082c000d680c01c6800c000505072100b000c481d580151658600b4040140810050380700f614044000021580583c1303003030008146050103502d0b40b200ca5458901418603100c1c04081802b8140c002c0c07811500145d8840f03da8641000c002c8640c09a04068000c2c0700075050 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 249630431 1250 249629181 249629213
    0x71203050f040e01030c170c010929030406150b1903050601031404030f02120304050615010c080406081504090b06060d020904020d1505030a0c0509040c1e0305010f02070803040609 79
    0x3ca8120f000008001c900d40c003000a588440343d4980c4130907400d4200315943c4011000f428003183d4100001d00c03020b413823080c201c5180890202800944400e2200c1c0302a26403085d58240c40c456120306107102c0710b40c04000040020100f2800c018580b19440000943c11566001c081003059200c2000c0b500716071290f0000c00360203541030f42d01d10315810305160150908800c1c1ca8858090b006144001926840a01c03d0743d21507600720740909003070341d1074018a1031401a0048120b060010f221964000f04140d080034002415054860080e60b0502c40b00c442103100000940d40e00c41d46c01d00b0342030000251026040ea0f0004026141c0c00e49400418013074501900800b102e49030000d20102d14a84407590301e4004118000c00041ca442586459105140d21a8480c0303601030302d5010401380410150a0240e819940580107150300c40c4003685034034002d00e0908414045400411251109009206081c8240544030564507001c52804400d0741e141101400001c001420803903a80050310284840d176101c41d1890 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 249631681 1250 249630431 249630449
    0xa050a020f0a02060604060506040807090f0e1501082a0415050301150f0e0405060408070303020d0e16061806140702061309060501020c2805030f011a03071203050f04 73
    0x10b03210410025070300c41e0200d030b040303101e9810101e0014090926804840039a070500014050007414a00d621002e0911403440301000d940da013200010502040c8810705141461509107181c80d45044e414510b84250007502641c3c0812100d090310b404012203000c00c403000800d070707008140b5150505022520a00c1907201d1038155081c85000d2002d400b080200906540e000e40005803440d4031080c01c003818210071607004205074010404500442d0020000d80100c0e882450090325041500403201d0035540b0290210b8040e6101400b6400c2d4508805074000c050000707403130001c01883ca11640d000b4400c1c494441d038014081408440c5203250620811104516006444940d81d240903006240603203149100c1c410810f8580750700414698400b10b011b080c2100c0050008041c0f11540e28082c61050340003188500200032141e0001d040d841c24001d18028070f151900000d600900740d250350f06407025000b911840f94010a07028040c40d00c0324803084040581514115403113400c0c0d01c0d480780662081d0741000c001 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 249632931 1250 249631681 249631687
    0x9150501090e1207051216081303020418031e140c0307050d020a03050405010e040e0607270506040e100b0f091f08010b03060406091a1503070203030a050a020f 70
    0x1019031a42202c000d4051803021504001a00180392006028020008100b07412a09601c4e01130000c807009000c060036640d540072455801a0340d000c403a039101c2ca03000e200c04d202c0c080d070410070740c41e00b40715105c1144105a24030714200c6007030f03400070003030702c0c000042c00512243c81088004603032141c10706400201d0054100303913840ba01d005005507250481c007030844241c4901600046a68400301e0440480d075416211141407505090046d9a180c080c4c500d200e40043c0c0e81c1d44100034000e001c00400e4040c43c000e80355600c10030240082d5810b4415001995504440440c1c03080040e03440f0300741281d0071612101c0f038414098031000c44100c840d01c150340c0700b0760525001003000c2d02c00c0031301710780100ba680c54200e50b0f840c404900103054440320b07803082d01410049a22480104044d902d12401968030080040c0005001d0791641c803002d0407100c440c21684186801e4100c0f00110342004001d00480c09a480407050540c90500c200a503030744001007400012940b5800828043c4860760140d0302d580c4074245030740e51 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 249634181 1250 249632931 249632939
    0x304050705100f02030a0804060b03060703060609051e0402030907030f080913050606160c050303041d01050d241b050705010501090615080903040902040f06141201030609150501 78
    0x10303a828680c050288601c10402c1ca42e41c00d07501520010f0050080754000e103052415403281511502c90090094600359102d440701c594641d014065503229801c29203001075003d08021000300080c5035500f200e806100d9058442180c8019020300b403901c840100c0d000b5030780c0c1d9101d01c1e807503081ca810790388000c085140e81c0c2040f01c20822808080e22a5403010395403521030300c01c0c040c2c07176000703039030b4207440c001d03088601009090695850702194452450180c6059036400b5a6180842c3c6541e00a52200c00382d94450140c0621800000c0c803a14010a02100e8500d200c5c0c4441c0c650148280702440e00030000900243c008180b181550032800c035100346000c0000041d8202840500b003030b441003100715155442e0100201d5040b03440c0c030400c001e6034060750114151407500f40c2c0685501d08007803d81001d5110a010000d48083c0c1800240090408440340004291070488042c006202080c0010703404402880b071203142c002a0311b05241141d030003442c0802c40705041c2c2042050144e800c6941440c3c03508104c001b00b = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 249635431 1250 249634181 249634183
    0x2a25030f050a1406060d020907090b040603020904150303020d1805150d0506031222080313150e1f1106070816110a060c111501260c0402030901020708030405 69
    0x1104040c00b9843d00b00c114011420300c6a19188201c607072651205001d0402c0c000360034680c0045a0101442c10b2124a05456441c013a03a20303041030780402d001030b800040c0c204507420306003d490508004860316880340c0b42596400380d03e82c600e1036000c104200212070f5010700c1d09260315211004103405000000710703000940050700e075a408110f103c0403032820500442c0c1607060024a050900b8143c02d0818200020307529203060707003400ca40c070750b82012001c0100420f28260070b1006115141c908003410409502d0000050003c000c01200c440508c240c0501c48030182d00c4010380802900c3c162849002090580501541c03009102c030f120400e203114043c10800c9080d000703e0042c3c00b8560b0701510440c44010341000311042070301000c1c0c0e075485822008940002803000e8019a140c44814149410f50300311042c000ea02d44140b8007080910140c0c081300400401c04412843c14004112140004005540510040d0780c1c421042086014950002c002103651a003941959001c1c0c0d400131005d9540c0c20316050203 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 249636681 1250 249635431 249635443
    0x4030201110303040b06010f05090306010e0103020306100f060c0602120f090c040606051902010e060c180d110d08220306050106030203090607081513022a25030f05 72
    0x89000c180d00e22165441a007001081c1d902c03a503030150520480340c0e5620011035800c40b00310391910500c0001c2c0210342c02a03905000305400392229049030304a5601d0b500405291510241001721900710b81c0e0f90601962161880c124292005410040d041000c40e06e800350003071084a4200ea0f190210b102070210640340010366501030b82d03186049840f1406100f041208541e1140300d2100400c004001c03461214000014044200c000c60000046241d40750b4551802c16104888801c0c940000050040f1114900000910785d620190f810f413041c402c4668505400d0300c003031100c0d144610303a4203000c00e003040402c201f100c922003140501c04030b218040e5602601c1c400d46900085401600f0301001051062013403091f00d128483c01c0c0000c2010b40c031191426286c14002904ac1c480c0c0d0041d500b01180c2c5502c607086c20b151a098200c0d030050f912003410510200354001581c0051804e880c01e4003401c43d214000030095544141010041b0501c5039042464416208613400181800c080c00840c0301070100110300 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 249637931 1250 249636681 249636683
    0x3040302101b030e01060305010204031a070e151e0c070e0c0702011713061e0506030a03050d111e0705060f04051b0103021215030708151f18020403 65
    0x803626084625103050059030041680715490080340c80080b2181c0344250010f507058800c18000150183d12500c1f903509980c46504140e84031004034141c03480d48602104004d500504910380000307040300302000501c1681e642d828071100c0000200c0c01c1c00700415411041c003484482d402c5501d81c6c3c0e0900d50003c545403102c601c69070f140441d4030000104014a40002c56016690503941c030800340c44d041c00d42c0001c500c0064001c2040310941c030901d400060003449498802d40346198006220403520740d00f14283c1c1e800402d514081e8001c01500d00000b03410000344c5030034907030200020610225885c0740703103c01c0c001c0301c2a06103800b4190303510440000360040100f41d101d00500c1030728225550080600281901564002c2ca175074444c0b00302c0c03e14141c1c04080000c030742d00b0524026242c080b81300711340500d6500641c0c00b4525038006800e4520039240030409900109444000b900c40c0e0940c00d503844140000c01800c20b1600b285c107101464484503405200d03000340c8072041c10342d56040100c0d0100030084d045400 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 249639181 1250 249637931 249637933
    0x1a0f070201060905010e06121501181d0c09060d02030601030609120203040b0906030a020706090b090105070c0206030f040c0509010b0414060f09010e0105091c050d0306050a0303080415050a0203040302 88
    0x140814181c070f0074014181070380c501020081c01502c0350802d000c0100e03110042e094060048a4113100c00080642c40745000346800138091f03000c0f030003001031642140c020f82190018820070706a41407150780c1c0407402d2400d4400c01c40c0c44080a07a543c101142c42c01200c0c2000a500d4003441d0008002c11810360f0182d05000d009080c0d004064640c200d083c1d949200701d01070a502d010080c08150040c0c9440c0d402964081020003000d400c085043c0d940c107050f1240e01c0821100011031804121460409207d45503102e003580c40e00d01145a40c03500424000c1c030014003044c5140c260080018180701240344210014607028000a80c06d41c1e640b560002c081e003040c001c0ea40c15614007910304040d480d00e1402c0d94420042c2c5502c5d01d140c0000c203030040d80e1013198440140d05200c824810140c0035a1525070310300b0214004001340c402001c0a140007814040000c035001c2c1407514181c030070701080d11a40800e20980b0790500b841c111907107803802c0000200c0b0307908141014090418040040b43c50040e0060b500441c400c3e0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 249640287 1106 249639181 249639191
    0x2180f0114131503140f01120b061206091c091a0c1e0f010b04140f070512010306090b062b0f02090708061504031208041a0f070201 58
    0x10700300502213540d6182400940c3c1c200c001186c0e008038034583c0e114403903041ca01040b44c0035201c0d20001d000868904005281070b10361401d000d501045c180200d68942c51f1006903a903894218028594048030030316884020b032400f50400c8402d4812400700e00040311307121070f0882500c2d0001003c030402445250641120101107000e4038050304034500c0900030344402c100c2040d0a60355010003c5000c6c0c0e2030710680308201b41d224000140c000070800040c54550715452002c542c28000e40c285401181d0b4200300000800003a03500814107030303202e07421200b11581c0340d104005402c2500000d51030300801144019061103c081598043c00e840b41c40000c00301c1c001600840d40f101803c91f04070300810010030501c00d0303a1914a8410710000a10051140380906555900c421400110140e805005440d00410200800d900c4203a1004605000c0c540c01840c00306005200e480301a501800554602 = true := by decide +kernel

theorem cover : BRFrame.Cov 249460431 249640287 := by
  have h0 := BRFrame.cov_init 249460431
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249460431 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 249460431 ≤ n) (h2 : n < 249640287) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
