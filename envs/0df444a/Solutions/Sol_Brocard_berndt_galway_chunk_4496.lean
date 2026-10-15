-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4496
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:48:47.065754+00:00
-- url     : https://prove2.me/submissions/90881bb5-b1f5-4096-9116-c393a827dd81

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 808453237 ≤ n < 808633093 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 808454487 1250 808453237 808453253
    0x1a060405100501020307112701290412030c060e07030b01080106151206050402040e0609090a080f160512030103032a02010f020a02093907030503100b0f040f15120203060d 75
    0x118023100f1511001c00100010721520144044c441d429152044c0744510400c030781d1296018a100f591a40d00c0c4d64a00801407500070448118090b803c00c4040c000c0c0c540011186648500b00d203c01c90303081401000014011106110340d000fa211208180605404281000c03500b446412300070030101682d4201c0011183d031184002c00080c5440300041d2844d103403c1041220540b001801b14590780c100b011100006848401296044568082c40d030740c540d846444004040082c0e240014241d104d0049424a149140302c0954101d074401c8d92100f190250304100d0001030b40340011b00307182c1194170341e013030100640c040c0800351203801d580d00c1201c251407520740010f14003030f00030350f03921082e280030b010500d440c040540c00078425440e06458204214115070b071860114400c588010307081090102c0440e40c1c1d9202e10301c4039001440300360b0209460762401c103014482984203108000c000340000b440002c0000b00d49080d0703030418aa5444540e03080d41200c18200c00b0390b00051080e40d0280c009003a11b0009408c41c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 808455737 1250 808454487 808454539
    0x40911122401050a0c031b0c0e2d010612110307030c0e010f170406180b15010e03100504110604030c090e150103080c01091a06040510050102030711 65
    0x10a54400c0c4803166010410003003590100300d207040210800140700140d410485e0f0484595051a101001e464010000a114140814010440181190b0005018000c041e00034050300100402614024090121681d0b03407800020f0702d00d040031500d004000040c0140122030300c2140d1240c0203d00310009104500c407561088820340003107a6034112000a0340d901c410641c502d08402e083c05544a00c4582000d046c0c1c080f0b4825403444405650300090070403086402043c0405001443c40f07203406c920f8a007150001d001195034802008400301d540f1036562180b44115030303ca0340500941622281c084e0044081d0000408c1603407090a0610804069100c00c8002d200450281c01020022070501070300c0000c4d18a401c079054255030042c0680c1c03d8a007104040141104d44c0049029562007516003201e014041100010b03107600b03449541c00320b601c0c125081a5200d15412241040b071a80d402c071100b07a4074107150145900690050002500103002490050600e22005000c1d4040b00383d041580800c10540d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 808456987 1250 808455737 808455751
    0x150901051306110c04053607032315071107050a0f030309141c050c09070305040b090f0619090512040305060a0204030215030406180b010f0605070804091112 69
    0x40b0701d440403e91105019409a24600322130074011800c1c4560b030322540990305004000200078407458109254070300c80c1d010041c5403841e0300b59510f0982d242030492843c407450312010088003031011450b00a010200e991400d500351154850815129190205e801c1c0050084100320fa10480d00045180c0e61417008500c02001d041c2103000c00305041d880d0040c1503220960001d01c4100ca00e04501c6010b603070b81c10429040c010b00c007081c0001580355007001e9142c034001e203010580119544091107a540e03030540200e440345000d142442e005071918001c05aa6010203581c40324103400820105440d1401d0b500c0e03061409102c5840072421698648845003800306c80743e01c00510b030380c00150030410040d09208003940400410011070070685103401055561b404001a9404140c00000040030400e0303584c015242d043c1079038004000a565842c01c41d8600d103003070003065501940740000140e824490710485913a1603100c1041d42c10305103044d0214003e00843c200b0066007038002d001304541c445105070602d04c0703001 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 808458237 1250 808456987 808456997
    0x403050d1b38100b2206080a0b010203030405120f040504051f05091501080a0f0504390506090a15030f06060503160e03250f0e010302150901051306 65
    0x100103560048812011079410b007880380804014108001d51071601c00c503903001c00d00965030000c1c1c0111040459030900030b80300321a0110320110300c15a01450962144a46207420000100b0400040e0f90341c1c0030490b0014000c1c2d02c0945010740c20700399003019080c500000310149041030b071141c4c00101550700c100c510079262105203101e25210031000898000400043c4c0388442982450704c1a00204d03401c0d2003035907044c442200d0106151503440d41c807040b96a2001e080401160030249050b42c01c0071038003040c1c0c106040400c00181038580c446240781080ca1560102140664175080a200072600aa4840703036100d960403400242c40303803201c404500c9100709a0740000706441090004411544039410200401000f4010448000000072010150341c50394100122846d094000103444c0c00c42882c0321103442c016112080021040e401c8285058441002070041d80c680c0f210644c4090b80d80922020394004032500d413120400311076100030800e2900614005180455010609484c00d107564001d1000070 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 808459487 1250 808458237 808458293
    0x260d0c0504120807110d05030406030b030a1e0614070c020d080d050103081c0b011403090120071104180f03020705060f121b0a1d1201150602030403050d1b 68
    0x254105002007000340c02ca071b00161902a9444960f9a8083c50041406155503086d850402d0f80d010490644040d07030103441581c0d0040a0141180d5116010100300c8115041c420b02c0c0403030211082c1c00c0ca110f110180e48030500080c80c0c4d0208001040d00080a9618100411180c1c040780c18601806e0301860090b008543c1e1000c5403074840c0d500003120842182070500d000d401402c1c503170b030003030603820000c0d82005004d0b00c0b0f4441c0011a40140b0540307165981c0c1140070b60700b1601a1045038040d103680c07401190800071400f024800e21051341c0d001e00120400c1c12000c017980000840000c0038119140c001d00c1181e24481c0c842c00841c003d136101840320b010b00c4401050031403440d2580c06403982d005954020240000900f11401d00683c00303144440010700420108100c0c4241072940f4503601200700900403690902406042c60082c04040d040711619400e0040c04036089000004030380449030310000500031050000001c0741c0d480488400006440c001041d41008580100c030100e039040d07084030100c070b807075 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 808460737 1250 808459487 808459493
    0x1020a080709060e0901090b310608060c070305070c0810090b01050102010b150d0209090a1b020316060510091401080d11100507020c0306040f260d0c0504120807 71
    0x1a091030b030f01c91400c0020f4100c04003295100c0428480c1120b04c0f5420204201ea003c0000031070404250404100004142d01c14000300c5203052040c07003070710700440c0c1c08220094484082c10386402084843c03125516040103140000307885030f4000c100300e600070300c005001a0b441d22110382c2000003070700d51400b140d0381300ca94400502042d14451070041100340000c2208690030700100b1811952030410200c0070344040340b186c0008206070112511a10020400041072a2580d03000005080c051010f00c4000380c03610000b03415038000011540d80318910032049010390329036503548003e0400140411040212080d0000f5007a0250150021400004101140944c1002000c81c9002207010f504400c10000c00c400601100c0042005500149066030100e003558840001781d06d00f000344880c40307401d840340c401003005010121070340580481c8182e0b0400c00382403001840340c80d0711075801c60550880c0810440400070b4034860384007401d52601170600b01d0500c2d5984a00200c00d10200d501a0b90354400002c8590030 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 808461987 1250 808460737 808460747
    0xf01270317091c0f1d0f010c021302040303180812031303140309030a1403010f051c020d0c03050d0c0213050601120e0c09010503010204060905100c0215040e090a02011b06090501020a0807 82
    0x104940c4002c5c03100e807142c0000001d44030070084441241072200000042003592200040313001041c0c0c2440d0259521540da1500502503500c030b52054200109100c0c02107912075000c00d8603010400720540d010300319129816030aa062040c02c80c1142441108035899000c0c010001c051441403080380c0155859907544030000d132400040040341014540b0030001840910f151100300301c150360054981c45000c00300c4200c4011003117486074001e0740c000d941052140400c140c1c080d902054906c02c07030a4803826182e111003584c81d4a062400258400940c2c8521007008040f0342c0141d03408441450007082c00c400c2c0383d080c0000c480054250a145800c0780d00710908a0400c0c4c50301d14018003003038000b10310f0146040c800030200074150081511a4502a86905510344034040c03005005070010a024140409a00800074690044c4070780c03181d0103c450300045521201041c03034113002c0e406860b00300e050030806a0030200c1c1030000d00202c40207981c0e001200f010480c24801380c400206582c480c8642424540000341c1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 808463237 1250 808461987 808462007
    0x412030b03010507081305010f1803111f2307020d020d020703080301030303200d06090524040b04020d0f0b0a1502070b0f040302030f01270317091c0f 66
    0x70080c1c0c18281441031003036004502545c44007022458070007a007280e02d0164003501c1c40c2e05140056600b00131641540f102c80c0c0403481070031840b82c6c90f850000c443d0706890300e882da103001110861914900d4100d00f1203040c160040312142c0203003050481c2d01c40e401c003403032020306d001170381c5034001640b040d52001c10058041204d403030030b005240000d1003141c1c40d6607180240c80c44140002010541c84140c801c82000c0706207684002068010a142c0e02ca84000343d00c41c000303208900c190001a07042c00042425403102c118030381030000300c088603507200440180c1404003070081e080308941c0143d800c009a030071100c00c9118003000489116800302e102d824020070401500f94980020203480000074400050303070f03000118081114104507945071101261005101c1a00943d03002a4240c05a110015251041903100c6180c0c4043c24030704440d0b0900341c00074503800401501005000c0742d0f108140c03080da0900340e004c0c5a40f0080030000c450402510001045c03020f600c00c400b40011500b4034030034049540e049104c40d4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 808464487 1250 808463237 808463239
    0x60b0105221a04080a020d02040b0306130506011a120411130e010606030c02060115090f090b0103050a020a0e060d022b0506040525140406021b0607020a061d03060412030b 75
    0x140c00d1504240301e49803a8603061400912841c404540c1f00c003151181d4001e1010b4130402404e680003441c00081c0080d504282c0201121036000300d8001040c0c8030a000c10b02600300610642c16824003816212211108030007501c01d4039a80c019160300340d02903035100180640d41011040114142403126200c5094419640020061508119180e030300c01c0d81c0060320a0445601981c424221300c19001e040c1c80002ca16000071881400381d040110b00e0364982c0c0c100403d003450a076410480380c0d541c041d420080f40100001140020140c40403240f59207068006010400c00316900146464529441120002c5070420300902040d00802908940c41c2517110b12303944401c2c140c5007440740b441c01400c440100080c003119101030305542c43d200921325210314103001144601c0c0500c6507546032164006581d0b442010880c0b00260a04542c0040c241003000c29500801e901400b015030044c14400207943d034444450030351080080c11340700c111299808100c001c1c0254050480a0000002080d0007010398082c05021 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 808465737 1250 808464487 808464539
    0x130810020c1c0c020603040c05090a0e1c082a191805060d0c12060f08070503160b0c0a050d050301050906030c0d080f0c120d27060b010522 61
    0x1000c80c003500288000c0f031403541204c1041c0e0b0380d921864003400040860b00400d8201a140082000c070000d1340d406442c100100c801125080f207001c0c02c03415108490380200c00c00117540d01d004a04011084d01100c5420008040010140d081c611440d041e80d42107803c0d005841c0001804c038101140d00100c810450b20704251403404032604000100320a4803410403001900c47d9540c2c0200305070f40c41401012500d84888400b4400c00c3d545488000c00e0403540d006888141c000c42200140b503290001e80650620b0500301c81000540c41e1250107101c0c3e03044004004080d002e05124800024014000c03400c07030000a844a83c0c895040c80c051211040004141d14021703031018070030202c03940d22400d03940d1405a200381e00d85d986485d074212005090052050b880010f12425032007103402500704011b840341104800c1c08000701d2004d125071850714200c40e080d501600d408100500007150302d0750022414510113040041c80d00030b020850000e0500e8403401014010080d0b18141700c0946803480d1955018048645 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 808466987 1250 808465737 808465783
    0x2003031903270b0c071401050109053105120f0a03060914040f111002060414010207380702060a2d150306020c06150406140402130810020c 61
    0x21184282d0301a14000e02100300840010b040440c000c8100c625090f8800e41c0d0000707208480740054040c2c6800e0154000450a0200051034a00341c440400014401b100f16000c0b9224003440c0b450500d03400a83c143c80c5402001c0f10490ba8181c04e100910000000c5100260341c3c144c400d070010201d915541010101c1410041ea501242024500d665001500028801d4400200b440c15401051807550056000ba628030321030081c0039004900c3c9849240117140d9840c282c903008013401d00300d100b003140040119042c41c0103140c604409a46550148131719941010800680e1921010390b4142200c0b8500164032400c10400b4036081030140441c5110301d02c2c0e44103e41100485d8903e0b00c0c0d4035241d20300c80c030030350307145a0458500301d0691040002d58100070701b150b03281c442804458464008071020820740f0100701481c042070500d845144125400d100c1030a00b03000b80c03e000c00c80698000c8074540e100034091180490b4201040c4007510085000c09070060b41d580030300044a0511986180a10039880f62100c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 808468237 1250 808466987 808467041
    0x1620030607050316031e29101d03062503150504020901020705130c080c120109090813170f0c0306060103110403050105040609200d2003031903 63
    0x1a250010b0000362540782c1c0113840e800403002801004103404c10424100c40c45155802554441450813402c0303042494208480903d540c0c040c0001030b14942c1040701701d00c0012801c0c0c411224908140c0050a080f41400c4548001a18001c010340b004e01d100032041040c860480d41c9282049008511401c0c00e110301851030240d00c0b4950a6803207540d0090360001901002a842401140f0250400400c5d80c01c204000c00744140050180c84030301d00104107100040707500d92400340e064440b038240c88050200030fa03007412103c5010304180d00d400c5032420390900402d4440c0c0d6840b00140040d01100e10182d059174444111b851400074196003035501c50304a141d003a072540e200411020740c00b030000c0c03c0210b0005031076002544d0a1007640d1018149520f030401780000c015a90700701c003400a0044480c1c100101c560300c0e47d1200c000320020840e078810107a80c000030008a082c05610101d0b03110801920360840b95a001ca4110381c000d26100d076012a030100010b4001760140301e40c0710340103999100408000b102078 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 808469487 1250 808468237 808468247
    0x90e030a1119060b030f0a0b0f010611060705090105122806050d020904020111101a040612020409020f0a094a0309040903120b03210706021620030607 66
    0xb06000d08142d0b03e030010912a41c8041110b624500c060f00d04480c0812003506002c4c504410980c1d0a00c01c20000c04000503031107209d44100c0c2803003c11000549480d403112817094030b055102490b0030b03040c0002400065054084414031a210305c807001c0d524005c0e003980484122006c5500d66203514418035010060003142c9848801405103a8152140d035110f40f00e90005031440c0700510031502007480b901810345e0b41c402c1035030441d04ca01d58102d1040420540d40c1801c10050b00c0f03d80c0900646d605080d0040c2001d80b0341600881d52550000d04000344040346d65011602032001d58101d500b95a494800e8803244404203504008840c2c0c00090b035010b141c282da24034144811000c2000000010162407490005505004aa092100091040103e080a032802501c64150507900b1030810b49048511311250a0100d441d805941e05100602024203480140c40c0b865048034a0648041c2da0a01080c0a83ca02c5503100c030300e200e40200c4030343c01c2c40c1c080c08544c20558000300c403215010390040310600010b07036005 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 808470737 1250 808469487 808469533
    0x901080c2e090e011d06010309020d140d09090912120204050d03090503010509160621050112021516080313020d1209050d020604150207090e030a11 65
    0x80390700740007408007891a40302054454440110010842801c4520903410a070040200c45880d080c5651aa0340c0e052981031002c1e007150400403100b1a400040e2441d0b02c60350114042034802052844488156210b020242141943e504105c1e0300c40c048040205801008180041c1302d8000103010340c2d0420358461105928003d160820b02c01001540800030125406403005000040c008281d514900e0400134500d9409120b10f902130f529281c003103016058041000d500d051401100114054544441201e0121f8902e448800300c6d56045500d264440180c025540200b10780e40c1000e4068015004002d22800d6111401d0303414002004400c0055030388140300345a084e009a03c450326659000804140070400c0301d0025441200000b15904110500c1e0301c0702900981640c85c28091500d0b0010b005050700740540103548002c09000401c8003094903c03018039486090301c1901c40c184c0d40c8460500c00e540c40c4c00340c914203035040850030310700440d88146601c5203404904010050084080f0b030642801c03190b = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 808471987 1250 808470737 808470739
    0xc0a031512020105160b09011d0c0a06120915091415010303081b030406090308010f290f030c0c01150506030411030319030f0506010c050304061b020a1e050901080c 72
    0x1010509020791300e845c1e9010031002c0d420032401003062622001c00c500900e0141c90724190b444c4107482084903001c000510810900303015054540c4075040c00e8040e221159086001e0326120b071034144030400035240c9030200c0300342981700c0400304184e5141d1808280c01c0d60142400030f83e6602c020107aa0081507080311480c1104c2d014203203400d00382c03110f103240c505205c14240484554003002040c081041425404029654043c1e600c650385a600c90f0100c24915245206000030386451041800e003100c0319901c1d041e05490f0856000c1c2c80d103101c0c82c41d24250f03a001140e000989200c01306820070300490a00135801c0283c080c0e075905611360b0400c400200140400b40025087e070203500841d02c800d440030012129031040a01180c01d520702c010400501400f0f0100e070441d58541440082020355004a59000c18554401c020b503041c981041000ca4400c101049948001c1d4070360700b80d00f03002d0385900b05410301a1000711031070301003000c203400c049041c007203c1d41c080da00440424004010300c800201d55040c0c1580 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 808473237 1250 808471987 808471997
    0xf0d03080106030f020d090b060a0905012904050a1706010f060c030c1502340b0c071b06110f06070207120201031409070312141e0d050c0a0315120201 66
    0x38034144001c00902582c200b000c0d076281f40a4251051122141c1e4592007a00c084606501468464107004107413082846800360a5101c0d44802c2045072200780a1840807a50391209402c044d0355100040c2d448189920034144510342015440318220f00f0b000c4a40985002c03030141c440c0900d03180b0000c0c43d4085100c0060108504a144041004200032804107604030301c030000c5d511402295100858081400f19218013004084200a015141ca0342d400013503a40043e041e141981d6030f8590707151a54000c0b0821550101504640c14141070f50100b8100a401c007613407034424050f00707514050300d04122400c3c0f4110503801340c1d0400200907030016506090320109411320321b00010520040e4054184802d1140d8007880b51000c1010b40b400c00210030040742d000d21071580c00c1010000d000d0f00e801040005484c0d002d4400c11449521030440e0000eaa0401002c14803145030042c609404011600b06841602c03040074002000e400084d4103000703040313150071a088960800740c41c1c402c003080e03040343d0110000c0c1881 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 808474487 1250 808473237 808473251
    0x13060e180a17130902030a0e1612052a040513050c040f11040909260409020901050c031603080105180103121b081e030105031f1b0206060f0d0308010603 67
    0x71442c2c5080c3d602415461201d0301c05980c580b00307000003942007214608441482c0c421200000c1c80c001400c8001c080000d10250002030400400407100300305820161054071401c0100f013402d0b004401035110b14210301490078207600c0c000c02040300381c80018142809810005d0b002d00701162012544e480440c000310b40000f41820f14440c408094010703420b402c066801c0c0410006020121508880b010700c0c807502283c440119440350a46481140381c4031145004170038003040c498101c16a0050901e03c038141041070500c884688100e140d40d11655049090301c09000009003090b4004a442c1e0140030308a520106904200f002c0c5504e20070140f20141c00042c501d00000c0c1ca06008051602080150748414544048181054200c0d540600528269031401076441c801c0c0180c04410f03a4141c41d03004000c1d082c1c0c3ca119480b004c040c0030040710581c8003d0346d50445203810040d2941404c0e01d51410341c0241110313203090300820101c8809030120f54001c0140c00c94600000313504c4020309054854a043c005054 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 808475737 1250 808474487 808474523
    0x204110a051c150e090d080c030a15030c0b090a090c02120702300606030c060a0f120f090311060c1e07081b0d020705090a1a13060e180a 60
    0x5012101e510065410b003d080c0403540b030780003640a500c00c50b43c42c1d00304e0b6109654090202c0e144641112490070400051010075519072058100324200b00009044e01412622500c4907180d060341944400010b1340c00003100c0c03045040000c41e6034000c0042c80010040c01002210103916648143d62030111074a0000c0c2d05421075685108103120004030354903812018000780c10241192000070000394082c0320340d2000030030302c0c6000500c55410480c0a0000c5040c081211410354886c07a041c0707581028042c030800a200315000d18800c140041182c9480031525201c60309002e0146031020082d01c48031741015003044140c8951800b241c58840040e03190345505c001c0415900f406020b542c3e401440c846001540e03403c0c001e04201c2d5027a00b28603207000d454641c6040101a81e45000034031805400400002c00501d04038031581c0403e180115140c00304130359401c0d100008003414440e40040240705da6624051000c1d1801004403a4040072090280c0100d0460201c066552210f59000905002d514441e64481c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 808476987 1250 808475737 808475741
    0x40504020904110f0a121a09180a0804063203060a08030f0d05010b0c12090f46050d0201030f090302010902090901020403031b03030902060403050303040204110a051c 73
    0xf415500003246458003400340189400d54065002000000c41e443d5000035441030610904065950010958a2030f2425030244605044020880b510007540a8841c00b00050b05000107003002c4d00c28403640c3d9465080980181a102c0d1109100080c0004540c0440264200a1080215180c0818125240e542d000000b8024040c0343c3c0015800340404a100e0118800090140440030304800c400d120381d81c0c80c0c400c1303c0c1c0359001c0e6a402131008d900c14009402c49504500052850820203881070a503442858007003a00c00c520701144000c0c189030802d011801c80021b200c401d44244003410342d540b4808010100030300c03c86080c0100303407047ca00c06040204680c022f0344020204840440184080030b1b06081c003900805071802d060b8010000c0e40d00040c192801171086805590381512083c0c80442101c00e5106540c4250070218103040d503443d043c0001d40d03101000f170001544104015a41e82c034191040c401030790a10300c03510b8a00300307045c004a01084d0700a000d8501040d034404c1c0407070208224144042c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 808478237 1250 808476987 808477001
    0x2d081612050102360609010509040f062c090304050112020d02120f04050f0303070c03080903090a0b0d0f020f03040b0a0f0f0b0114030106020706140d1d0d0305060105040504020904 79
    0x1500c0b134402c0b12902c00350342900d40076181003c5900480c0d50440c1410300c1814400d003442c00d400210100039561152034075a0100707040302c80b070300d10000d0380c59101d131082010082010a494440740000c00290800000211003a40c0804800b018504141c602800603003550140108004896008140389000c2c60301d83e8151044811189842c2d040f50408050078000c80f0380545040c0d502d8010004c94040b0038034000212030140c0040e50340c000c001c80894404550307919002d0b1804d00d5a0004200e1421940d0b50f00a41002915142540d40d0355500084441411952051514114540140205041d003020380040d00e0340280c114202000355503980718090000d000ca00b071074512a500d800c2c400c03440204103a0001241c02c0d801e8a80343c60702c0e07603010b03100c54a5003c04d109020040e444180180103072403180340c1000d0700d050400100b81c1068012420340c0709940c02c440c55040421072125001050000c10040d42c642c0c40c2d25824204803d08250700020118803560250502035138000600b080300d0384270350780070300 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 808479487 1250 808478237 808478257
    0x50c040e1605030c1f050904060b0c0c0306060108010b0d110a020309031b010f081305011103010f05180a09050f030a0c031202031509130b0910060e0f06010e0103062d081612050102 79
    0x1004c0c032b07115403100500d508015191201c0d4458082c0701580c03400e0004600f80101030507124190346a10345041404c040c0d0000300f180c0c4d511074846140503042098540a0b20440c030b1190061501d820140f001d040c44d12030803075000c040010080c41c03440c6023643c210700b01c05001055403078600001e69070304c5180042c1407010714009000d5840c241b120101301c0c2c3c24102450580f9003070888001c0040d5108100541a00c0005882031050303142c40100303180340307400d600c140046d51280007501c0b010041a00e180741550004801e0802060000911500f090b90102d10240c030101119400c6045041203d0180e00c0e4400b10500240030b200040c010810034001564010000356001a454040e8076003a0041a100c1c25003404061400d4280480441c601c0200c0510034460140320782c1398407044c0d480a00444845030342994050502d0760f94030000c0340284200d60038103d0760110f801116a05030801c070883e81c04c40e40b140d2044401e5000b07500c005450481014644003210b00c4c0321120349440d111424140d0080c81006600 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 808480737 1250 808479487 808479491
    0x30f02040203281a0d020102030d090f0f0b25022d030708040807060e03100c140703030209090c040807030b06040617071a190507050c040e1605030c1f050904 69
    0x3c3c2c4031260058209911094005040d4544420440c05200c90554102c0c0000e01613001400164032a5889611420486005103000b98002107039465070340b00e10584040075120300100c0c00810451084c8030351511500000c1c4802c040514503001c00094441200508440703460f160b445400100007204480c403650308000c2000d03299039810ba85880342003903016200d0214503004003e00055050301030071620321010006806032520122042c5070100508100c11751400340700059005c41c1c210550384010304101442030700c0059898040c24100801d07000010aa000eaa4908002c01c0c81042800b184940c101c07a0b100c14411029180e100005000d481c1c1c90704505020101c10358110804400064014112404130040b02d0411950702c0d414807442c89030504042d1700e40a49005924810f12030300c01400107030700a400781c60746904942c1c0010183c2da64601524480e40c032000b034100f41420b45043c210700404045004100c1038070700001103181011003443d900758860b04088a101110f0242c2c040b200305a50007001 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 808481987 1250 808480737 808480801
    0x80a0207080102131e0b22150c061802060f0a0210141e071b060b040e160b09210307141501080d0c080c0a050a06060e10030f02040203 59
    0x300d245030a07894400c41c0005510412100e1344030800b11700080a07145500c4140d0715040205a0f50b61610f408992a10213254280500050f00904590b40708031102c2e5a60311103465030101c2c00d001041d102d40b920241804030071941d8820042c2d03110340495a5001040781c09a84500d00900e003a41042d8071000003110040c10300c0000a81d241400c2c810911981d150b40b8010790078480200f50012030f40046400a01081a800840884010120214141921a40d000b20b079100c00c40000c030b026144030050020807640312400b51505010700d50300070130103070011002003030800340f401c80040c01445894420f840c01550745a02c0d810000705c180101c92855412040f00154000d0001c10103980d1001c1e0009900c0070283c0a0020541510208004000a145680e00c01d18035003c0e8484144039400340003005001e1003003411500000e107080c0000e21109005043c00103602d81703000078072088132200402007070032411070f02014000a00c0f2000340e070b1840ca13010f980042e00c03a41c40640650f118401071807200248030048030 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 808483237 1250 808481987 808482007
    0x30804090b030d0219060b0607051f06120803010902030c04050a030305090918210d0f1a010c021c0204150b0d1407020c12120a051201060813080a0207080102 69
    0x411015000d0540860307195200041c0300301c0c5c0700c10700c1002c60703918840d40b4211000032401a40160015445c0104624500b400c50b503581c0e0711388030490ba4400703a032191038010b42c2c0c0d6403801ea03c201c0700100300c14001560380304916a510121031205000743e00d10030340c0c04808211801c030345c001a100039000c0a0007944003c0e48a090151154001d056501d106094032800100050001421404021300030001131502d042c0d0034074450810b10f04000d01119500c0f080c270030b89001c5100b500800325110124200001c1001841944441810001c03800b181031050000c28080140c6034400d10044856016100000032811840024060308024400b01d50030b90306080049011001c0c10010b210b0301c011008100041a249150603003000d80c11140070007d608200f04500440c03c000141c0c40c88021004207403100300c00000c104588a401c0713200d03080e00042001c50354900356400b03468020301400720703814614070910f018170066246481c4c10703030007c04004001c581c0c035603940d00801c048000307085840002c2d03450b050800 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 808484487 1250 808483237 808483241
    0x16062a0c0821131211091303020c0d0b0f15060a080f1b0306191e0305160506092107030813050603040807080703020a08030a23090703020f0a03080409 66
    0x24096200d103030215039108070701c04811048610000c070b0455195072644c5001079004844500300c00a0381c00d0341d000d4141890300d642e4518000d02c150a010703001902c000c803d060082c40c040d082c0c26101d00038220310544002259034004650385c800c81c0d37002807440d69500e041d104aa20002542c03a940c200401141445c0c130702d90088691849039007c4004180590f580e000b007c0b100100d0100c0d4208041001c0003c92064188021500446003151628040c101d5550b5081c200081c441400c60806c2640c3c0c0d0424420040b00380800144109584203208425040c130000a250f48510758aa5110311190b0800d2160b1041c0104506101c82c00703030054485240e6039082c281e07125400034500d12800e9070720082c0450b031032600b42e0a40380565000740c10b141c10f0490701d81d50060356a001c000181d06502c96001c9580005060701c00461003408051400716404081842d40c040704508040b44084024a440421004802c001004070480342c040365140424044140030401040310303a0805000f00300c00180110300381202d6 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 808485737 1250 808484487 808484503
    0x7050a030306150e09010603020a0507020a03050a020f4f050a18051b030a0f12080709050616030302040503010c1112030106080c0304050316060902010216062a0c08 72
    0x400f000c5010041401c1280e100c0c0440c1c61156000465400510002d81300b94080c2c003508070b240c1011440d0010a4000a900e0041980116041d07440260b5280860911142079604e5101c16034103044800f80c00b0802c0000442e05429040e842000655036810748205585085000c1c3e140c0c008001c4070031180341411002e0b2a048a4081800d800c05240075030b002062141040d41035000801742c0810421041e41c00e011400e00c51078540d15208114000740800c0c0a08050002148640310300100001c4402d40600000d0b0000e00c9607080c030500010421158403200101c90095a540c040ba541c0900c5900d8260001d0140747c000300d4142d841e2036051044039030040c0c182d0200b01c20410488007440001241c54000740b009004000000d21110081110700034030002841e00503128900f642d007003000200407001c9110441d002a695942c4480c010420340d40c05110ba1000007400143c01400300f810100d0140410356a11100c5041c1010305601c0742d00d15160107003c100c600d07808a40c40352030755aa020b005a8444003 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 808486987 1250 808485737 808485749
    0xa08040305210310050d05010b060412030305100308040306090627230c060d0612030e09070f02060c0d060503030304061e020406120e150108060702010b0f1f020307050a030306 77
    0x12070a14002c0c1d40404034283c82c070885074000c3c2002c0c01070078801031203c96141c10108450f10364903494982c049645210151000d04102a400c00030440d6909004044d00d40141640d403480044480a00c0481c04d02d0003100c0c2500c1e0080e0b03001ca01c022441c07405100a040c185108415059000071016252030300f10300b03488905000d03840c0b842c000300c2d0819500c488883d008146001c5544a24200380150615002038582c0d451030040014100e0b1342c8204440c0400c500400c03c07400958001c0c10b4100780d1500c41f1100d5040081c034903182c1060741c080e031006552010302800c1114161000300301000d1110240d00880c01902d0054292926400d10307181c0b00015001c00702d1070014081041c000704019400500c2500d0444140e0380d5070030050070b61407800b0402850310170b0301c130246c90061a000c2c2e1400030a040d40f982c02021046d005101a18048000074211603051341c10903c20f0a40f624418016030ba01501c510102e4800c4098140868509009a180d4418540c00031721301c1c014840300500b0f16030540d01030405c80d83e0b = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 808488237 1250 808486987 808487023
    0x60f01051c0507031103060a0303140423131a010e0307080a1401051f06050310090e0a05010606050a05070b070203041806060216030b0f0903090d0c05030c180f0403020a08040305 78
    0xe170841d03c6007214001280c1c0c0b96000305040000700086031180da56000e908003401c48640c9843c0c1c42c0c4940c90f100c0f80c55401050000141ca00286507103040c0449109001005007108101d0810b00303090315000b0120071035010b4100101c02c107070303c501c564091000b0b4000313000020444080d60440c1c035114075081e40c038284036985546000c0000d211081c40f03041c14502c4190003e0381044040c10030406641503040036208071030912040c00c020800078803502c80e030002c030041c0340d000f0b042500403840c000d400d42d58181c100804108051201008154100c003e485d411a846034003460151350f150000ca1450107540e10180810144119040e0103405a03405001a1200c907070a0701c404c4050315000c44c0595002c2d00c0010402080756000900040600d20700c40d400c41320710020340e0300d410a14000075024590900c0141c0340c080361039004100301c2c0b40801061800882c1a42c6842d640078404040c0108000c00805001a02c03010342d0003d0b007050b04c00c0c400031041c5903120b8041c03500c842c1c43e8200160358800d50b5540b804085 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 808489487 1250 808488237 808488251
    0x140109060b090105070f110904030c0611090f010c080c120705011406010c0605063f0d2102040e0103060203060306151e01090815220209060f01051c050703 68
    0x104021048414004044e124285049155680e000240580b414103a68506455400440380d50391203440c5402503009907900801100c9504102e4121050200e070580310400070402400d403500c4104d40040c0700340f424202103100081c14100301d50a4815080c120703002d80200c5100001c05080c01000d40f440b140031b04020894000b200f2109414032070241c0d2040e0206624060070b400041081e007005501c51006410340c03001c0c42000c000c0c1030046045002c20684640c80c5c2024518582c0d0b150241400214110000c100007214440f0240110640c0300c0d80c00488901307000c0101c8240c45540480d0010500121100019070303480c1000802504140e80c2e5510a0103500041a08a1800240a0040000205682e21403228501c1c83c608991950b884981130001035100010307500e030140050850710f400703801e1141240c5044c03a415100b1164251050000b0504030056001684032110344135841403080d90b20320b4292419000503a4140074594180d254850140b07019140141c4907040540107983c80e0301e00f0720000e = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 808490737 1250 808489487 808489499
    0x27070903150501030206030105060d0f1d0d090e07321c050f0f13082701020307030210021303080c0d020d03020708071707020604030606060f080c0d0f060914010906 72
    0x30394000e03c000396019101f44010f0029240c44001464103020342c0304000b5116018184030416116002014012400681c0035480192814092500410306900e440c6d10300b01e090a4000c09034610282014042281802c00b1100f00482c4c01c85a03204001d4a041d40c400344510f0444000701036004d6231110004040b00b10301010002e031280122805510f403002c565100d135803249200d070144c1c40c005040c0721310f442c0c403468640c003c903400394001c00588604030004244198195140290007584024084c11507100301312841c04650702003115031910081c00c0015a4800c10305034a402c4011607600080c184060009441405c541c0c00204124445159000c0d2802400b071031506408900803590060226031040215000180380f07400700d420350044041840b07003440303d5500070a5903904503400842d03a196480a09100d002c1e0803013003180c014099840c00701000d2601030032002090156408da02074144c1c0b200071501c0395003903075009031002d001c2c180360030805200580c1c00d00041080078404c170001985840c3d004518 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 808491987 1250 808490737 808490741
    0x6250204141501030b010e0a090f0e032104050106150201050414160e0c130b041404051303030e0a0b090c1306030b3d051201050907052707090315 64
    0x407492400120b4440741202d140150f02918014900c24100607a410b03924036159520040343d400780c050540300040301303180464120115410003d802c1c5165000380b240070701200d4120300c00000101c44041c0880355880714a0b000c0e014118940001d14005440c02c04607208943c1540f04510907401403005811a1065402d0b15442c0ca41604815614405044040c404645010a01c94000c12076981c5140380c0740380440710f0412041e150300407031a0060005410414108010580c0b641c140d4100c80c01c00440c100452403c1300459280c80080505032240c4010141103070502141c05c40d1074111070701d0440361038403522054030b401202c0f40881c811556400148940e0983d0301c41c1000b600d5001c4c6425149440b400b100841220b540440d4856940801c0c405808030080c20700c0450781000358071422030800d42014100240c6e01d90701c03024405684c4c5031204000000c100041c40008442c0240e540c00c41c6100b221015029040030040104007180f6400c0910149551000d0364a08990140400d0801380a18102142c2 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 808493237 1250 808491987 808491991
    0x1b0120120f2703040f0f1703040506180f030109050303010f0807030b010605160602070317010504020306030a0b1f0e09060f07050406030b01211a06070c0e04020625020414 75
    0x3961190191091032001c00b041002100381d00303200c1200d060071759402001d0307101d40440d04081d003021010402080044501f02c21124407a0307200c0f02441c1807a08000200b90b2600034184d0710307245400c001c0c00c0904151244444888043e802800901c0b640aa509000340c0d030398002c0c1326045205000c100b00050790032021403031609495118007100e0107079290000854142d04680e003150001e01c911190180002c2031480104241c0348a07860303402403800c0d4120751040b903007016804640280e00400c2000700681d808030b13041560320307440980c2083c00c2e221042a00c11603107010036900002c110707411001c10143ca42000310761103082810219105542c1d40900e081c3c0d200c400b0703a900300c00704800b404103120490094105103840c1e0300615003081c00c4048151030303210402c051f915010000355180c05a0244540180f0419010442562030b1440e015180da24031060032824403c241455020502007000c5507211800c941e0840d20114101ea00e0000d2040b1611708a00c8280040b84070b54a4800098198003020742158 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 808494487 1250 808493237 808493251
    0x18100c020108130c15020106300210021603080405090a0b01090e060339030d0207090b0f030a0b070e01021b3307020102010b0f061b0120120f 62
    0x80c0c11512100200c1da103101c24443c0486900403103003000f0903000680300d0f40c039500442070340c00410441d1034400d030003100b01c0640e803e003e0516519800005070165103100c2d00d4a8550640d22035140341c14694003241800c501d607099840c0c13400c030300340000140150303480504140c0740304407240e4845464800e840d0017200d0b0100503550104052107404c1006020b0b280c1210751108026007030b00c0d500411204031607046c144941c00d074242c01c58010080039036039400111a90b50300000750300510700c1c2243c2c114082d42c0d51885109012460783c813804d04002c1600c80701c0841d5640c140190448444400926002e90204000c40300c0307000050700c205031103031298400500d040e003000c03d05522505440b4843d00344403124205107000c0140d04d020346800c000340102810240c00b210709469045440700c03005d02c002801d43c0c500d01d15440c482c0000380c012443c1c80d9100e4007116108403040020700b904805840e186805014500f80322200d0519080940303015031071420003809094540c00404240b9962603a6a0081c00001e4801c2 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 808495737 1250 808494487 808494497
    0xa0b011e1e03021803061902090301090507060809060c09060405060904021b1c08010806060f01020a0506040c0302010305090105070f080919140706091a130b18100c0201 74
    0x494003444825510041081492601d1035210000c12862082030031807003039110019070f00184e0352220402203110350700b220804401500507410944040c40001540d00f07083c2440319400103040502e135509522500c40366900134166501c80755980c201516002040740e025115004480010788814001821210820f500034640dd040c24140010301030701e90000c20384036801036070801c410032608030340302c013020542110040182440c22042106a40700c0116021040c1403080703c41c0140244c00c0081040c07544000c040c1c440110440540d40105e01c0c203c12310401400e640140800d01c003c2c0041c1c002e410003624000c1e2810f2046031669464a4200c643c1103841e28000390402052074841c40c42401c501d900624290100ea0b8003103501c0328620058601c0030000c40f941e89442c444824464020b000d98070040c0214184a510f152400910301c1c245d151049406040c1a4000307641034002c502401c0c038201801981181c19111100741100300c0380c1401400c030142c823409108043d030811a03c114440d480013641a034607 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 808496987 1250 808495737 808495757
    0x3050c151210090905100c031a10020a0b07090905061f03050c040b2a2107050313080c0301110a0504060c021c0506100608071b1119050102060a0b01 65
    0x5030080c8003010340310714801c0c0d0703511034000343c254880c1c0215008a4000da01800c890510103050108441006001d80c1c141810003141c44600509024840d00413407007039a02130b503200e440702c10403400c0029042000b00709280b1501800700ca40c0c1e1050030b5005490005004102c00c1d1134070020000c000300090090700382d00d0381c10500c492125220b90002d82e0081510303800e45007000e03122104113007036420910180c4c00c840b15000f04000c0700401038110758503080a06005d040203031a19403034070b540714900d10340111880d00005103000400c0f504100b158204000c8110942d003030307500c8580036605c40c0d0b80e10742814469800c040014031000c01d048215400f6500325101d151a0910300601070f906499103803010707a4000c1e00038502e1001d1030f2218440e009643d20a2018080525201103000320b58640b0790040070411285004101016401180c0040e46450000c03803445a10b070103140c0169490043d8924503081440c0440b000810004428a00280e070713002d03029a5059550b000c030301ca08070f82082d0b612500058007a20 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 808498237 1250 808496987 808497007
    0x40e04030e01020a1202010e0601090605181905072609030d0e0c090c0a09150503040305091f080603070e10030f0c03060c0905041b0e04020318120403050c15 69
    0x22074802201070042c0e800b50441a02c80751010b01400b0608405030351a4040210a2041400329038050034004608000c19810000403d503c00c2c9240440511b03117241c0360110f0224481c80500100007490b1020034071161401c41002860301030382c070b0340083c02240d80d1200351803c0e07002104400e1150362008010350425901ca11b4800240c00745074840c41080c081c03800c40d40029107034400c41601c10703480d03000f202e5921a140c290003482c0c00340d203501094003592020500001c2c41d5120040304e403c9030305880d010b0348a0b0b0100c070010b0058416038200d400c24071410b41d8040c20050304240d10070303c0b0356421030594810700e9803040441140c01c000c6074000805079240320b0074000a071001d04803a040d240503140d140783c10380d144e40d241421501030107603000c00701d805440c042000380340034001c8882c0c000b0300d0280304011403c6140042c02c80c101010030070344629000700000d02d40211950820010199641c21500c2283c0c0c0c0c44e089004a0f40703d40429a4140500040d001c52814040b100000e442c402e400620f00d00300042d0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 808499487 1250 808498237 808498247
    0xb0a0804061806090b07090602030a0e0103090c05041a101b02120f0601060203070c0f031e052d010606080c22050907032405010507061a0603070203041505040e0403 72
    0xd00b581010040c03030803490208000d07104941c081c6108180c84003107400c2098014140c000203a200c8021980100301e4041002d40c4081c4a61a1130710a08021031804030320b140000b80011280c0001b90458503000703186003528104906a103014000780c843c8049442012401c84440d6040914807581e002d078170446c4801410710882c0e18403000e2400041e260004500e9100034203242003a401000180d0012400c1c1080c041c00c4000d44000302001d40131a0343c460300c5c65548004010b0558141e00d980004030b100702c01030090900a078200e02c12465880e070300040f4509035080b00d501207110380a450b07628200002c60b2160040c004036002d0021451960305081480070410030003021903444010030440030b08001a2074807000111800b4140070744002c0307605450041c030007400c03a9641009101c88000c0120411950360840220745001c1d401060115004175407280c50b440590a0f4040135030040000000c12541950200217041070390402598454131002d2808101d5880c0594060f00d034001c03401c4000708000034060 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 808500737 1250 808499487 808499501
    0x6100501030501080d4505011e03150302060c0d0905030309010e060a020309180703050a1a0103090602040305030a09031709030d0f030e060a0c0e0a08030d05040219090b04060b0a080406 81
    0xa149070150201075000180c149010000d0b01660203110701b8050044020044c003040140401b0703c0c14907050521180720800190030032210006060703490a000c51b6002d507080c1c03480302554001d047c0b1903445054a80a070b503a0324620481400044400e0b0000c10240381c04030483da403415050351b40c21800041d40c4200a0030790312401d06481584000c2042000b81e484440c1348001c400400da40c001001d140130702000c0c041e2180200f080340f590b8503103d030395071000302024541e40c00180c0c286000981041c6900d801c20092007140c0010f8554400421400030940e400011030301601e1003841900803420001d0780e42c8420303008506650380e05821030088212070511511003140e0a0382e407494041403010110417010b040c00000d494141c0c44a4840d0003d840481e0807250170302903500160780d4421190300c4d0900c415107070f01075909881011078441c0041070540d580c071201080c01c01c02e20440e55001d1035131001d440d8020040700d81150f000d02d003450030024034035a4040c260f4202c201151900d00ba982d0b59540d40740000c11361 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 808501987 1250 808500737 808500767
    0x15080c0402221d0717010b210f010329150a15080a0b0a12060f0e060a0c030f180f05071a0714160306110405060a0206100501030501080d 60
    0x2c8815910400c0000c2c00038000300506202c2d111104480c10010040c0c40c40205130909220015000e074500c40807418840341112a034071000c40d21100b80341c025409110812403140c0c514039400c010b000d0f4448418003810304803840b613601e07581044129000786418180703211003040c3d4004554000f404020004011841b000c0e0000d160b0078040d91580380e0050844254009280002c0549040040107080c070311648600303a000701c4442c80400c0c6030040c032280e65284030300014600b649843c000c0e01c0303c4040d41c22849a5041381002c0d5007403480c007140c00340024000711200d840046c0c01c1403000080c0c031003503100e49099801510b01c40c01d406086034036040c0510402c2e01c03088400c0e110301280041c010b0424100c3c024010200c040c1d0540d03528041c10020b83c5200d20710050340b01a0408441d803c0400d401100d10710880c1e80c01107000c0f0703008803e008614400d0103103600440e0003c1c800a02142501d0740445e03014032030292038204090540d10b9170011022540c00740140b52031035000e940d40c0d1881d913001c0c40c440c26034040 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 808503237 1250 808501987 808502017
    0x150f05151e07120c1104050606090d050307050105011203093005151306060b04210303090c06030501090f1a0d0804030218190c09351015080c0402 64
    0x1c07940c540e815543c074283d01000148001000708200b180c0d00880b00c1c4a10381c211424040c508000d00001c0c00f40c4a4026036a10881030212070100300310090007907440158200d0001c021540c1c0d182c5907003080e014400402c42c0040c1b042e0501103004521a00c5082c5c03400d1040d82003154103603444104400c8201c5580094800e4440c1ca24640d141fa01070380780c0700d4482c0c4580700040310350140501d040c0e0282d401507006001034420034441480340d5100c421340c00c01801c2c10201203242c0d03110070f41000d0700145224400070380200340003c070200789140c00d508024100c80a4803c1007145240011640d400c5a01c1c0848007200c03480102c80305452842d040c03c018014900425419140135604e6000036084018240e03440364401441d030400442d091401402c140310703e03144009001d41c10500d030006044511500601e0b86440c981200c034a480c4c0484d070070b480480b9286030021004234a09258890742c4030202106c040e14941489040650f040a03100c628044843c1075004041000d2107508000181d0410680800814 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 808504487 1250 808503237 808503247
    0x3010e0c0f130609050f1212132c0a0504320a060c081315091401140109050c0405010827190b1e040b0c0d150f05151e 52
    0x801d907a000b240140b009886000ca03807032030542848031203655803203124030034107008a18280089011031200d410a00c40f800d980d6070340002090006803046c2c140c02c400204140c0b24070340e290030000d1b01c501d04140c4a103184240302c542d4824090800365070084074000d0140003089504c0c408030f6070191103091141d9507202603100046240e004ea901c5c15181481c26210b85440303400891103c1e400460305504202a01650318038030005071104003602d45030450070044250303117981c1c040030b02c205025215031114151000740700340c003401101c1c81105c001c03e000388800c09142401103044a44504202c40c00c503041030310b44201603a602060540b50b241c0d15506641203803034140302c800203900144100c0218860aa074039000c00001c5092120035030030000c10401a0792001950841503583c5956110b90082d8400c0c0e0780f20b190350b1450010307a031034014220b00d03402e4181840002200200d40030101000d640e100c104811400d0b030383e00104101001d22040c1c4a40100c020400c03070020b6141c40781001c200251480a5520300307 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 808505737 1250 808504487 808504507
    0x220b12010c0c140c01021e01090605180d0509130f0e0610030308070e0127090e0a02030c040c0e10050708040e010501030e011b1d030106030609021503010e0c0f 70
    0x1d214503184100c0010000300c608010000d020700200d441c0ca10000c01800c54010001c0080d42c0e03400c507141018200e040d20007048180400c00d40140700015030041d810711260074803692140d0440948000b403803040c0207104403404001d00c62415100207104c011f08840705054a2000300c4014540c1e0201c0e601590b0b151281d1100490702000b0700d500541d40300085816440ca5400c00410000c0e000e0700500130020b416903007191983c0d014040307500d854600c02850341e20910000c1083c6e045005503002d05c8543d418514203018003100030800e00b41c001e00a5082c1c0301070320000003c0004803901d440d03040001c038541901420709030405010f034241c15001410045d01d001c555440d882c80640150744011640b002c1c05005016550341409240031480b142c000034040709a909640304080c140d088010f40400098483c08041c811440340034480003072000e402080169141c1c01d22501810802100780d0003074007400f5011000001410441e81219402c00103210240c54814008e0120b9000084200c034804042c005c031140 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 808506987 1250 808505737 808505741
    0xc0901050f1825090612050901020909010303021606051c0e070e0a0504060c02062413020f041e0e06152109070b0f0409050c0c07120b06220b1201 64
    0x42d040180a0007090041a4603d8286104061000c000c0044820040041d5500318401000002d00003c1c045003640c0c071854058020300030030030b45590000e041c03c000424103401203201c02307001201080111040c3d0b01c94609039802d114040d2a4603149a0303c0403406001c441c103074410284900c2040c01ea0320265503900c0728031055001170b100c05daa0682c5c1d9609000420a8a104582007001c20740068429460591214505070850302c070041186607144100442d15551407580750100e0700a10011919848400c040c0c144581081c002c070284011a1480c4070300990200381500102c0c0c02040644050b55100320034044d0380500b5080c1c0e04a500f00174040c1041544180382160501c549800100800d40b82a00c0900d18000e259409064807a40c00c01c0a210051403c80072602030714a2294007003140e840d0300d8000580c510600b00013050902482a0120b50038801038283d1010600803000e4042035154041003100d14003030030101c1d411f1420302811605103a0305641041d841c05c0030085c0b8040c0e5201c40740c4e46240c2 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 808508237 1250 808506987 808506991
    0x70b03010608091005091b1c0b04060c050c071e030819021e030d090206130b1c0204060c03120603232b0c0507081009020f01020c0901050f18 62
    0x400e40d410b081002006040000c0c078482510340c03206004a00705a4000b80d22505424804011040020581074a68030b0f1440700d56186000705c01d050004410a041c00c600c2101c1c2a14116416410011071100b0240704000b61482d4404150260040c6841e01c40f40d1803003103948d141140c3f11000240000030100e007190700584a2a105100c80c05d100190800d40281800750790b90482d00c40810004100f402c880d00001030b01d1407003098001c00200b00e0940e000207841c0780074a00300255000d0454a0104002c85074501400e90904841ca1143e241c041300074500c070903400307540100790015010046800c0480e10641441d000711510b99000544151280c89090400107810070407403d10380c91b88a0742442200c10030100b0800101403000044001004600d44900c10401c0c0c00302d010089a5045d4170113210b41401014010004407003207801200b0300150071b20151414601c164461072030032540841c0b41d400400c0c145c1500d60010a1402c644c0e00785020000580d00b4105c40c50380240c0c5c50500c3d41d68180708400d000d4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 808509487 1250 808508237 808508249
    0x1c0c061e0204060f03110910200f1908120604090f0b06030d050f072402070507060e090f010905090c1503010e01050d0c0603091523090c1f02070b0301 66
    0x5030ba210304001024024020300e080000802d0700c0d04200d4140c80103d007099902c05207044404200200416204440300c40800c118001e95541104402c001800c0005103c03d03c0c050160580340d06082d0144620031040d0ba51310090b0a00104011020450003480700043e4001c07002480007408010035100c0180416841c1070403542c1d241404288031280ca400c00c2036000500700b6140c401d250055a20080801c1d0107009001030100c90310811114227045021060410824480400c5440c4c99150030301e07580d1500d0324800d400100d1690f6080441d107050544003070340b003130350180350340c01d51641313811249001004010312510490003032100d180c1d030695840e0b14641030040700a51180d01c0b541800c0e4085a0b4002c180c3c041482000750250440c00140c00c1306a0008480050030000f5403080d050400c44182000c903403d25402516144000c1156951042420415200c000d051202540c0d8a04080d0380c80c640044c41784d60200300049920346090b0541411500d80c1500e106417045181d580c44ca29070560000c2e0022 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 808510737 1250 808509487 808509491
    0x80d05010806100803180312030901021305010f1d030c060c1006090c08041101030b060708070b060a080c0f12010501060909110a090b03060d120309060506031c0c061e 73
    0x1048101401c122054005544400700c00810f440d01340640d43c2d912032001c259460b1807601c228405140d80500450440c03400f14042030740d0703a18203a28100c5c002c0d4000127854485510100020440d544038605640180c54507803522456800c440700c00d00840407100200e40c0c0c3c144545c1824a0b0300d40c4608000c0c20451900000800c030b007010914495050718119086120b1080c41c0c100c40704041e47d4800045504580c01294a007200100c5800480141c100c1500d010f80051000840104110f000001801818020b80c0c00038026184d10082102000b503e10a01c4003a030700c070702c02411141c0780c0000c0c180c2c0303140c80003844040891000c903621801e441c02640f01d20302042641500300920445402003001c0030030703116409481c01d41ca000000e000900d4034040c5000b98980403000407003680784d421001c1902500845008a03a9003064001805030403400c1003101c85904050204540e420f000401c980380c9401060b030890780b140a424119408540c00d04107071402601c0358080050061241d9202c0300030f658140c00 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 808511987 1250 808510737 808510739
    0x902061c1d1509030a080424140702060604060e16050c0604030e0102160e010b2d03010f080a02060d0905031308031e090d02150904020f030f24100c080d0501 69
    0x21660b1400a0814000b500104018540136901107001c076801580482c2010741d202c9152900404046000c0c41e20b103045141c18140745c0c007810046020740c4241590b908882e5541c4c2c8950a000540e621849144180110580403900d00c040d94404111500050715201e4281807003041501d16221040c1d6094020130080f94480156590510205460340404c0060307011507490413010014107441441016101100484c0d407071102c1903410032682c9805141208100071007010030102503103070300a1150a00985052030000303103212000c9540004a60010680e41c1000310f110744603c064100e075041101e4a000c00c000c8003010340726108501015103100401036450f03086a080904205000f90341c10b003c409018403034001160b44c0d2001c1da00405605852010000300c294910030024050003800d1a0301c1400841c100a00344115009103204081c410f01c0c0345d00c0354035200002c1c80ba004054070841c2c0d44003a000001121414451110081081d540c034110210f10520f884494450300800c03100080c151f25100 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 808513237 1250 808511987 808512013
    0xa030305130813060311070f031803121d010201090302070519080706110c010c331122080604030315030605040f0309090b060403030311040b0a05070c06030902061c1d 73
    0x4a46c4600d041e2844884c0d11303040f0a41c40c1c40f080000032541c02020808103003841c140d1445d0ba203800c0801164005811501c404c039588010f44400c00703044400c08020303180403507a1025071050240c80d070226010b4005d0b0120b541408284034407801220000c400c4212076020010342d942d01017002c600244000e03951007403c01910300d4a541000a07041d4018104400c03c2d920300c020175103000c1000085e0300c42002070140d40001440d80c1215002078005080e00c1480c0c1b0a40410316015035000f0410310034407000e00d00301c041c001e41c6880e450b280300d406000d48990003140002c001a02079402010800c240400c0d41a0155580d65190192541100d044a0302c03c1c0c00500e4004141c0c001840d0400303805001d4091103401030400124070b40c4d0042d403001604040c0c440d00780c1e0035280e048804840c064027051039840d42d100f0007614082c01070350241e601150580f0080c07100040c020b1082c484c4401455000b02071a00d41644000d1116040c44a985105c660030741d00d07403001e58420b80c03981e10f00c5803040c0500040c10baa030002d00 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 808514487 1250 808513237 808513241
    0xb0d0e0c032b0e0906040c031d01060608090a12050a02101a090604290a121112010209091b13090f0c0c021507030215190c110a0303051308130603 64
    0x802c0e4200380180ba60910f142640c03240c42840c1d00c00e006941c0042e0029452508502400000d050540909508500d00c9211441904102c0c10b4035000d0f1500b080c642c8a0b620305070794803e40100d0142ca00803c96000019240c031690041016085510444020006041d481c48c12107600441d031304440306039882151203505004541c2540400c003150100022041d0750200444400e20702c000360104200c58990825680d02d110405c1d014254540707100c07002140e0341c980340742646d660703080c1c4a00c0b4400444040c181030364140226082c10320068585a45170700c8030301350b402d050081c84122442d40d41040c046141740b032010607950b000916081d200400c40c0c408903414102100c2d0750407403940c1008407412110015803140300c0d100004030f003411001c1c0d642e00300504040f4140400c140f404408002004140000300b410401c4508040e14400d0080240c1e5070341a20944e2040e41d0b5000c0901150050407100020a003c0d0340b000c2e5028104080d81ba003818070b25a0345850030350150025008042d6140d6007442030725418 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 808515737 1250 808514487 808514563
    0x30c030f15031b0d060f02091207031e020414070e0a050109120b0c0405030601080a05010605010801080c09070201181b050a0e0c1317030712090b0d0e0c03 68
    0x9550070440d1140d000c03030340f54074500254800d07000c0416040f00071502e541a1011010342c0200080140c00328001122000c1c1d4130150130584280c42902e6588012440801c800c404c507503100c20200d02040d2981076810400220309001eaa100780c2d03d0010b403103040101c5107550710900742640c603041000002020080c0c5012107070442410490700721024050540f646029480c010742151488100e592032401c0c2c4941031146400c416010700600d00006005200003030300ca00060b00c07901c02030141c0e0340c4403001103402203c00d104070003240d48140e400703114034200391011a0700045180700100d200b4000700d021101810349050104e44203001e803070f004c14039098105048000b0b0700080b102d42c0c0d415440c000300a01c2076040a00700441c9800001a2203c44000905c0418006e00c500c4005210185203035019940340e800400003916401c2081010100d80c0d4881c4e52443e003a20010300340305003030480c0102100c0c01055090b40314140c52040c41e518502680e0700b0444c04141e50400212104290500100080030b8560 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 808516987 1250 808515737 808515751
    0x115030b100b040f0b16020607150522030c0203010b0a14211e0a0203070f140d0201020316050111071b09020c0a0308060120030406020f0a110d030504030602030c030f 73
    0x9100138030000198400000844200e901a15141c448001c4500031040b09510029840071001030408100022011007000c0c1140d03040c000c02043d901d850004014140c10101101c40c1c0d401c5818807400207005000100782540041c00004586c0c15040120720380c000c8a40101c286480e00c4610450140b501198400103c00c0c41c08802002c18219402e59642c0c10006000c070950b20301c0100e80030300c200f10800180e0101d07900201101e0340c1139a6007040e1300740c0000c1401600b802991030a501e4515041c050703d242c43d40360b41a40194941042907030000c80050384400c007142e00703540701ca041d0041481300c200074042040c09059494501a0b03012180b0b413075080389130b010784a4140140007051110340c0104050031890340505218503107a50b4180102e802ca031008000f103aa041094034500c9650703500002520940d01a60201c400484c0c61062042d65498041802007071070360304111540d901d003400107080060318468288203081544030398483c41a0f80040310f074032581020200404c4154440c00d0441070308105e03 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 808518237 1250 808516987 808517009
    0x60a0b01090e04110111190606050913030e0307030213050a0e07030503030604091103010f15060525060902030a06051e0f07030b0a09090b040521070609050115030b10 73
    0x1282c55014550356a00410240c0003000000c080e844a900844024520802c0501503480080d04580300c8040701400c42d0054070760074039280000c42c1d181401c52005008410784035000582c0e0300079a400b100c1c5255011941a01070085d41000401078850020a081400151350701040c1440c1c03c080000440340100b01d5400c0b1b44c3e1000d0b030200003091020040701d412682c05c2c0c80201d0f40c6446410042003c4405c040c1c03494040d0310f084010f04d154230702a44290010306070303801c60041f4590b0756001101e40f400741c1000250107603908000c40201c000c4003245420f80511601012420404075000242070070803540060714038a403600c040203619146c02014003204d100d5040402d02604001555607001c0c4001000d040501d81d44640c2c2c2d007450390f40d085184008212003c4180708104280c03510240c006c0043d41e0840e820f104018540c000c121070044043d5100c00040101801c0981030340783e04c0041e01420390260742d10355075903885114075221608800d010710b019001840c042d05007500030a00c3c4c14455809010351074 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 808519487 1250 808518237 808518239
    0x112060902030f0f1b0c1e15070503090d0e12030301061806021c1d101731030c0f060507120b0a060c030e100206070801060f050f03040602070b010305060a0b0109 71
    0x4081c032403e11813030194100c5d442c0c5c03152000c000082c5001d03c0301c0d50004d0b0414508205100440000402e00d09030500380f0010752182d1a100010346080c0402c3d22a2a0603410a041e00101c1078810b0b00e40000980700100020310842d9480c54040c00c40e4400c1c5c01c079800086080c1120561583e60351602c100619140c030041c10006405810540c550700d0400300300c0100312960407010411a0801780500303000e0002412141c28182030200604120300b00030181d43c0d0f64401d1800580c290030744070804855500c41d400140744a000610401c0207458011400318144a900c40c0038102003540404004d000d18803a4400146500f042c110190000404c035072261060b0781092811101e90b140c00d50804200c1c4c207542040e22000f0a140740607a41080f11422664001100454070003a083c1c0c00940140140601c3d00c0b012001e0f40c8691040381c44c6140fa09161340800d4080203942c0340440d81c0c00c01150f009010700700041c00c1251035620350001102c01c3c0c0c030031b0b40c40390b00ca10280002145039100d400d490040901f0064402 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 808520737 1250 808519487 808519501
    0x26060112080418151e030f05030c01060b0c0f0a170c030f0f0901120b280914040b06240901110f100c0306080712080f04090c1e0215060112060902030f0f 67
    0x410406e001c010500160680040c0030000c00704251400762500c90001d0165945609203080c0750b40103007005403403e1089a010020130030011480d19825070301301c000b88140d02c50300c071f901031000c0d40b00c1c280d03400c094441007000c003400300f01d0a406400b40800b0510b6080da1058250001800c2d1002e000c6003041c1e4034a40320b14108a50354541c0180c0302460030400001d0110b80c854400031550351254443d4001c1d90611802d40d90010202002d6441648161b4680311252161400e0004244040c0ea5241000044661003202003d20b0400b400d81c3c8a0145002d107403001e65600c3c5039080c007030040d0850704603501c001501040e455450144803281900b81c81d0800209282500165440c2401c0c4642001c1c0c804408005003404004812a1544080710702031942e03c65a41040000034840202c0304400207603200304800500203896540d08000d865503009007152a0040300744181807002a0145045c40040822440b580360103000d144020058034200682307a103012501d500144000900f0700340d0815400e0204805 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 808521987 1250 808520737 808520789
    0x90915080c010e0a0b1c0f0513030e0d0c080f0c09070f0c050a17070512030c040501081503010e010e16060203040e04080f030f012606011208041815 65
    0x11080c400d103018661501c460001c650000c22035000b803000c429000034960385a04406602410f001b00b446c00030403007101c00d444101c0403103a060356540800310842da801e2010a118512080540c040140708160500c41c650720390103a40c80d540e1181c50150448484c1c440c1c451010301c016054210b09072501da41c10f2030002c1c4000c200340a403400700c0c1c06002080b92014180881000107510203a409503110110403c44002d243c0d8a81104100301c4d460700c21030804001d03011119041e2805001008070382e604040c2004015260440014121110081d04416122266501340a9100d6a501e0b040001501c492049104c40c1007100101400700001880401000107075030010449044800c9080100c1041c4c581d440c080102c0d00c580c1c040440c2250700030041c01000c80010306510f04a40140116508885203680b03107402c01c0141c103080e0340140d00244010002e03915454001007100b40321304100c81c80c1c2a25581031950401c00107246014042c0d496003510007040368114410094820501c00c06800443c0c0c09003180 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 808523237 1250 808521987 808522003
    0x2250b130803181608010902030609070303050319090b0f100509011505030702070312080a050a090b010b1e032401080c09060706020d020705010b01121103010510090305070609091508 80
    0xe0305481c8200000c0d02c004082c0a14001d41844c6148080701e10b640d00d1410340a0b0251910680c8a40034031780101c0c21602000500008581d49600c5140c11580c6d4030101403880004080c03ca850561901603010008900146162080303603821040ea0150815200390864001640c016078015000c150050244680034421041e000b0400c0c580b150790303070781d540f00c040b41800c0071903000421040d2049810086c0d0740c0c100c4881807041c840d40100b0025680c481c4040c800761401114050701902c249401030107600c1c0c1d804028030310707201502803640b500042c210b00d451065008888815007808008040d101070a0740011019101200746001c851500709910010b6052103191041f034428200040c4540800c509a01581d01c0040d5106007152103000350300b4098081c05000b40c2083c00900341c00405010420071317201e1200c0c0f82100e5200d11703081d40e00b0322050104a030071740407101c010301609800000000f842004402e018200a9890600c1f6910702007000e001e5880f02e18510040078050481800800d02c005180e00e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 808524487 1250 808523237 808523251
    0xa1a03030a08010f062d110709020705010b06040b22120b09062d0613020d1e0216030309080d110712020a0b1501090905013308061302250b130803 64
    0x121100c3c8541006603a0811440d147c5038150049a00003d0b1400083d0701508000d80200d009012154091040100900c05e9000301500c0207400c0c010290b20301070341c80c0c04494809000f0140c440c4251117005642d0280c00ca084101c2c0c00f10403900c20000068018807600d60410302e80c0e072a03000680d02e401c540e0386504d2101000c014001a0420000d0003565900d41d00b142501c22a44046523211190801c10000d001490340c2c4088103c45840340f110a05214801c54510f014944041c6045080c0d950f000c8000d4401e4440aa03551001403002c480c00010621540b01d82c500c480340300781d0703403110640f510396408246c001e04441503411018000c0f0100d400d00f598164814040c0c0d01144d500c464503030050300e003220190410307140c0700d1030000040307040c00218030007844000d4148180284010f6114030324001c10424803002c000030300c0308404602c1505014402401c0860fa1a4015007000c0032040982825018a0004000c640105441d041801914810300750070081172481c04d01d0680d116211b440191002130120 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 808525737 1250 808524487 808524557
    0x3060a0b0a0203040905070c051903051b03091e01090f150c140105090609070909050c010f260103031d0a0b0c1e2407080a1a03030a08010f06 62
    0x41c020481c42402200d003d000c2c0ca01c0b04010508103079800030000252010211010300c50030124042105032a40c221200b664196607541c98641c6c201400038480d14014000001480280103801c1c80c0c1d950f01e1900a0b41021140144050040800006002c0d002991040e2002c10340c00e602031100e40c2a20030fa590040000d0b0030000c004030002d01e480740b0380520240b105081c5500e8041070010058010902c1c0d030003510303140c0448072100c2d1983c4a15080341c1c140c1c040200507901c003030080c600d2035019401e402400700090421600d81e40c0d85410020f05540e5580602410140d0840107204041d04038200720703504c45032040c5000c110700c4008081001d80c6014012010307005400b10390310400d030000f08641c15600c101021800c0c0c4545c066142184c0d1608441280309800040704038885007500f0007a10306d84070741c905980740b00c2d071600c49400d000001e1002d01140582e845000200b60220385082000b03104d94a081c1d070320341e28953326103d481203503807059030841c0c030070800089103140c03090b103c541d80080400fa441c030304 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 808526987 1250 808525737 808525747
    0x3080915120f010e07030b06120c0705070b090a0603090510051819050c0117040b0615121009021e09030f0708061e010b1c1103090109060f0203060a0b 66
    0x200314602038401e240301001e440808000d55142ca00071410704a851080d000b9215464180094003a41c4009451640214003400700001260540709960780007030400c5103091502449444050800c6034681014905a400242c205028101601c40800512a91404005181c0103640300c50325070009100c29121140ca6034040781d00750a070100542c4815000c8c030211494641449400c9500000c1d01c481a1001e000d4418100307245e5004d8000d000c0b11440750f00304240107555550314640038000182c159500038440c8035059400607030680081100a0402c3d44004c400d00c1c03c280141001000ea8000040090060100e0080c088400f41d02004a80c0000031013501c4001c07000100c4e01e41250b00b01044102c0c07007407407800a40584080340131405084511280d07001031521000405174458280303d44074059104008102c1d80002040880c0e020b4114007901107940407a0340c0c035001d102e4009031120781150f5034610b01c0c4c5042102510802c5114a0b076200700754190300e08180028406041031290003941000080c0c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 808528237 1250 808526987 808527019
    0x90601050316111f061712070303020d06091413080415021f0b0901120510020903030c1c0908070b04050d030207030c0e01150305040b0408090f0a1815030809 69
    0xd10140d00c0001c1040715002010204240000c002690194131010310301400400c800ca0509443c02d1050180c2d0001c0440100c108250034183e40581401c1d400c15500b805041c03454513803401800020080e28102041d6011424100121084003070046004401d5038507800001804200540e01100c60020f171300400c0e100c0812003030307040c00d01c9103514905842c8020416043d4402650041024040c00c0c2c40c03140c010380c0c17600880694003035410070241040d449540502d0300f1a55a4008143c10039015003902c0c101030040c00c54518010100b425001300e503500811583c42507900200101c010070718440200b00162508442028510030342c000e050040100301480420300d070003001000c000f140c0c8131890200f060350764078000721200400e0183d503c045161320481e62010b4440d010741809190440c81c0300ca425100d075503491602c2e5100e414495000702038000348000d0b81c2e0724107913071000511025003600010000f0305050001c03113442d501800751486104c002880801d42c8101aa000300700301741c45d0f03030b011000516 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 808529487 1250 808528237 808528247
    0x2151506130b03010911181e0d05060106120605090408030a150828350d02130602062a0d0221010501022a0f10170105090601050316 58
    0x101410303225105030700c001481c0000a0040d8121100320030100001c0c004403001480078420b45051180c282542c440c16540c0d4a0700c803103030f14081c51100300032008100c0a41d0200d82c1c41540d0400a40b410340000004001c510b401080209005400389810008103051900040305404080d101601d42140400024080d02441e40000700c44851421401005a5500c91656682128a1843d402201005107a0328620017555071542e2895114141031305490500309040d0042e05040c40c0b50700c4150024110320204101c140040c200401003031350141e5140007240b0031040039152a800581158005001c00050303000c05030041078480003a0612540f1711490503d1504203000d66418070031081e10002d0700d0074803000c80c140320720030344000929400807a0b0303610001a80c454083d079a02c8012804c00840902c1c0400c04105041308040303000303040b9500c582001001c00c0390750344070344074400c040b4904880030030341c601103026014010a82140c1e000c0c84d0345080d400081050101a0014009072114581ba0810900030 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 808530737 1250 808529487 808529497
    0x304230a0f1e05060405161404020715020301090623030d11030403060c0905010807030e030901050a0306030803040f2102030d1a0d030206011a070c170712080304060c02151506 77
    0x200300344080c0c290107410702079103134101940e049542d44100b9113074802040304403c003001160200c030780302c0e00212203000c2800041d50154104031544070040303100d19141031b07091002d1030113040c4c2010300180e07090134116140001c09004c1036000c1040c038006100c503080e0358001440f40038001549850701a04068500541c510f004a400040c691743c103140740c0050700c50b8000d161100305d8100366146040c0d6181c01c41c0603001c4030201825032119420401452000e540110010203400c50140740007d18240d90343c980756040d0700240c03000c41e201941400740c1300a00c404141482a080401000760741440f0610901a603680b03da060076030b1800e43c41e94404902100042801c12007003001a04840448145141c0251910300074014401510707003440c0c0502e20f01030000d040e510707125031107842c180d035242c140100012201c0c0c02d542c09030014450480040307180390680d681c410003a40305000a640307a0502d46010300944003820032100440d80034440c0a40c03c00700c041c01c010b400241d0401203c921200e00d0000c030300c0d14824 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 808531987 1250 808530737 808530773
    0xa1109060d091e050a02011e02070608060a0b0d0b012c090a020903060a05061021110412060606081501080a05061f02030909060906011e05130303050304230a0f 70
    0x1940d42107400384000410b030201709a200f40e0b40c00351114002c031350711403940340d05c1c4c030103200103074040c0c0c0081c0003050180c1500d40d0400e40082010008550f10300074905280e10401d1044109612458507031031a5801440d800600c101e078070301e8100c1e10030002c107030482d4110228030102d07c14480c6002099407036030709504450754138a014050f40d80900d4080d0b007080113008280d0305640036481424100c1c001c184501400009030703615510b0030151200910420025015811540c0c00c2c404040000095100c68541c0941e503180c03168a01040d5946040b20282c140d410040c030130700a62160241c1680075030703880380a5661140c1325a10018464441e800452240204689900c054000c1c590780081156000000b410032104c0884890120b644d0707100602180c200c00b6207102d408600001401d0b104c1080c00400340000d520f041c5001c504041442c2a81c840294160740164080b50000080c0700c02d012401c207960074100c0c0360144c1450280c03031001d00240c2d0303101560310180204185080b080b0070091500640030f003441c8 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 808533237 1250 808531987 808532033
    0x11031f03020d11010e190b03100807081e060f061905041a0301050606040303021e010902190603051501020d03020c1002190210090804031211060406050a1109060d09 72
    0x11915280010003ca000a1804120340b0800224a4a809481060090f40d0346606c80e0b038540c074101070f0b4913040d040a40146034074683c0f9113001c42c00b25010001c101c0103013103240040020440c0f000400c0f10100b02c200760011182c1080c1c00b00310400001c0c9143c290040307010340d2410f99010a0100301130884086e03812140e406800c03c1003504d050300094400c0705107680c04034001c0240780c41d852b04020082c4240c0c03000a0168021142d2204801c1c0c4030519800b0b10b510600c008580c0c0d0407250b00142c03024030a401c1209151710344007410310080d907040c0f086640c019505c01c1d1001052240b80000707507440d45641c0c0360303208140d00001c1d20300c4c50210600c018903201c400104255190701c0c04108187c2d180f80c3d20415800140704d01c07140a05404290f0040c5040c1540011120f8542070850721598104030700c40c00c004080c0810750703200e00000481081140d21440c000e100000c0c03207050103410b410581d0f80603c00810703c11400e00c07401099a45d44401c8400c3d1417150840000c800410703241c03032480d0070b0760740c2c082d502c2c170030 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 808534487 1250 808533237 808533259
    0x120515120307150e0c09040b0a0509030d09060203070807020607020a02090a061206090b060d080f03180f0105010e070906211112220b060d060b1018060311031f0302 72
    0xc6500181c4c3c1008412081c1c1780b8100a82d01030089040007102c010782100d40510203d0211800c541c466500f2440d8030059074500128801028140e4814000c2104c0e043e40c00004c01860642c007005042d00140544058440b6042c01c01000356507181514000e44036100f2800407400c00c0f12983e10900041c21103010001441d141420b0020040c00411801d440040506001038520728080c0040b4180b6940901168100b603030a040b00b500d503070401407003816012100c240b10480c811003001266802d02418001285940c106081d905180c0c101400400610103c81d0040c0320301600030078120740c00e000d50004014000e01a108050150085200a0003000b9001500c031201d5099002017620480d5400b9400e100602c103260390040c1c41a416a014211391200760100702c0300c0c584000e10307403c140d0284102003141e44000c00000c03406d03590b162030140410f4488030042020038842e41d511005240f41e00742040243d15220b00700905100003400c442d0804010031002d1620b00b2040f030000051034000e41400201 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 808535737 1250 808534487 808534523
    0x70908120d05070315060e0f15091201050c070f05071706011401020a15050a060915052407020d0812010f2103091a19030b01120515120307 61
    0x50341c04000280d80351814100002d890398000d0103052040700d402941504090724041088846030600c5030120f600075281e080310559030b6120600e1602603aa5908042e0f528084d400810411031103400384041030764105410482c8945c03065041d41c0440d40c02450039403074403a4624203e0300308040d0350003400b00a110b94205040b480307800280305068440341e220b000c4240c03079120016a55015400e900030605800d2100c4001e070702619820064120700c481d01c000c0f490f20746842d82d610035105d1719080d842c0040240b0710100054a0032258100d40107040313915421003904400c007070805030720841d10041e02400d41007401100700800e030b1080380c001ca042c1d102950b480356101c1c4038181c08029944180c001401d681d032030351000c0d405c01c40b2000f5134255050720303003009151805c0ca40490500071118554400340e024081100000d03024418008648410380c1c0c0041d4000d074600c0050b0034440780803c220b562624120420051440c011a400790341c031011076101c03001c06500c0c556545184107003100101074201e903508031941 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 808536987 1250 808535737 808535773
    0xa0306051503070f0317073215060a030807030c0803190b010e01121a04020f0c160e1b09130b0906060a02251703041802071109070908 59
    0x1d9000314251642e032940c0d81010139012515002c060841c0b43c4100030761000d43d071120001c081c2c0178031400c0c8180360914580f41c0c12250f41d4541d10006510004080c400f07126180501c40404001c1c0c42d82034006690034200c1c003080d0301d440240070052260800003801e406043c05084601c40c05507000c256540d50b8507043d428000020b1007041c0c0380c50340600305440c1c3d0040e9070050321008240c3c2da06965030300c1410025004800500181100d01902c1d030b00303900301d0031880d8a03140018010030043d44242c0340e50303000c00703801e0314504401c8410910008010603810300c1918a8000e1043c0c03c243c02051210803c0301a13400884a442038495060340030f5000b1316052102c00035904054800710703003214100702e20b42d030701424000e0303034400c074406c810041e00001c000c1c8941c1340c00440041c1c0040341d807640f540142900c42004045005442403118207d0b40049000c1000300c1d20050309101c0c0740080c0106500302507e6a444000241104640501c075002440014800a101e1000b400040240c40100ea5080010340c0c951a1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 808538237 1250 808536987 808537021
    0x19080f040b120a1802011d060406020114130302030f1c1404050d0201052208070b07080a0c020705010e0436051501051f020a05030307031a01081b090a030605 69
    0x104412901d0002d4120303000740c8070b03210f03000e155002c613003102640301c0e0700440b0141102114500d401a01e188200d480303440d102d02810107410717540c00010f002481d400303003a840f42500806200e40c94030798000844c0081d501105484003a4440703000c0e01e032103010100200d40081d03482d036441151107142c0500400c80e21641030101d4000c5009800b42c52260060301c0c400c034241c4104549550241e4080840f28403904041c800991000340907811042c1402c1050750baa40c00c2250a480f4000019040014020008010302c6064090451400107140c050314050018007041c141610180c85150349a840c01510641e0403550010340c4101078424070680e000310f1302c0e900522202c100035921442030400e61449035400703507450341c16514010710803050f0800380c0303441d090080f803504a20802c600400000800040d42000511302415031900c000c13540903000940000c9500104001c98100460074090000d03c41c0c61000340d02c040c51b4030101c09030752168100d020031044c400c80c3e0b000030501458103080220845402041c05 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 808539487 1250 808538237 808538257
    0x70f030b0d020a12060b1801080d05070b010314030714030d0c031e050c0f0a080403110a0c06051818070315080c090421080403020f0d0219080f040b 65
    0x101000040040c03204000241c14020b400c160441c0043c00142034040301110703040e12404010481c1c1580d0804501c101854043c29425070f0108001804002c0080c441081440c9080c40c01e00d09228035602c03031001480303040c8006000c1c80421a20800e05240600444c0c005640200074401074644924a80e65203610040d41c008200f890f0400e800c4030140300740140c070300e050306840c4440d440020f41250480103040c0584540c5030380b0400c0202c214400103a001a00600320a900c89e48198541810701401d090381f04003c0b8080f41e0065400140000c06440d0103c0c1aa00907141c101c0d1170f603065070075240c60180c5240c1c0c1c16500101344c1c4043d080ba1003c030341416200320050354042c8900c0d1000040111039400034000c0103034a420030b10642071181406007441c1d5215028603005000c4c400b03440080743c0f12850400307001d40041c044070204424142c040140d6600348a900700201141140342c90002d44424082120f00c00c50800213680b04148880001036510240c0024040c5035650b544114012460380800005 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 808540737 1250 808539487 808539491
    0x40e030c060108011b0e1e0d06140a051e06010e0a0806090f030702011d1c060b151e1c05010b0406090902030c0328020f07060f0c0e060c01060509070f03 67
    0x8800c820070545c2c8400c03008425101c0d9103c90400a04125915440320310000c0d00040102d49003001e9914441c990b4840390180c003000814440f0038209043c8881d00408011940f41050280f28400000404042008200101c10451522404012a81100141c4503540c2c025034841000c00c4446010030703418019513102040350748000c855030200d9128000c101700079010603c210844508090030300c007000805480204264440d1044400b0010000d404000650b80107a503000311007132a060041c6100b0021400b101c60508101d0908450204104544103101c0d0780e0b030007c079941641c91340c4502d00d001c00c1c5000000c140015038440d40720210581091140d01f0003d0082000000e03083c4062084a014071a40c1080501d0f541c0c804120b2100c030040306a81300c05c0f0103880010700c06940018405402d5220891030307015a59582c604080302070b1901d1200d04840d80d4500131541420039040b90414017200425282c40c1d44032041d032140b080c01070074075600103a00007401c0c40170091180d9200740c030b801e0b10001944003 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 808541987 1250 808540737 808540751
    0x5130608061f05031603080d02070213050603061005100c0302030c0102071b0e0103050d0806060d0c021b04140a090c03060c09090c05090a0501051e0f07021206040308060f040e030c06010801 83
    0x305580c0b4020720322041904041e5179814008210310800908206014039005450544aa404242020381d100b40e82452540c0d103209101e81440c050045c0d942001181450795119802c110004026011100a0070240251145104201402070064900380b40c114002103465034074030708210f0300c3d070102d09880c9064071031101000300782000300d0960a4140c980100040040b1200ca01c010307282c804018024644c420420701c800c05266849000f801e0a425195014090014410114400208103070b814503201d98208102104500721343c294595001049040100c2c4080d010f0034084100c1d9016000680480d0400c2c2040c0c0300c154000c40a801124220042002003002c40c080450f0f06005108035503600020000d0100240d6100c1c50242a80041e400e03840f0030000c40151205040b61b200750310403e10b6500c041030040c00d41c5042503403211038200202c0580f000e4a400c1d50000e0450034010407071071040c200300c5d041d611184c03101d902031400c061141d0100c90b0303110038201809960703078000d02c5a01029801c1c01031b = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 808543237 1250 808541987 808541989
    0x1030b0c03070203030402010c020d140d080c040302130903031d031909080604020d05030c0313030c0506030f0705030a0207020a060305040b07140a05030406320108010603080405130608061f05 84
    0x2224482c403600d50245046032625030044074010502142a6440036a0f1420340380829060242503000c10301010040c80301103080c140240c84240300500d1411008400e00041015071a110600300d800f0034640c8000508100e1854103600070114244031400203c140b5100c1c4211410020090109054803c51505e40d0081c00004170350245450003040c070726400c220040b4006090070340040c641d16115a003502e0600540304c01891039030f08108061840203880720f070204284642201c0706005032000341c1d165481e47c50f003002c50380341020000e048441002400800224000d115074142e80105a00038504e9000542d6108001c2c003400b400d450035110550008081881180256501350810b84900b42c0e15040080140041e909500014010f4416988840003c8040c80300b10054030485000c680488121030070510500c0c0e49840142c01407615030303162200a1001c01e80742c030151011202c1c111584c40c000880d10044402402855000300c4051148a00340007416a0640c40d0140205100d0400b45005039650 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 808544487 1250 808543237 808543261
    0x2131404090f1103120310031104201b0a0809010818190c030215130905090604080a0302070b0f0a0c03140604180b04120909020306150307141201030b 66
    0x1d00020281c0721000032840c000340781c41d9440070b90014000d082d50580e0314040b008148039401114244a007a01c000414400c00c0365507100718185850035102000b08480c10300d018000d040764141700c0600d40e000072420300303607920a00c07100b90f0000840d1000c1d605424003c0c503165600350000b42c0f40728042070107180042d0f03180c444480444102d0342904010500041c0022100209140d07040041e200d18613001e2002c405602c0e200348145080140c208625610005000210270300140c5821902c000346c10700040c443c2610001440c03030740203034004441c3d40c6c3d20319030440141c0003841022401492051a80104a45a100c0212243c869903075000c4c28040c15803090011030460355004503404501c002c40c0e0102e026400c050b840146a201c102d24000214a440d0300c407000c0c0e0645c1150104c4a6040c2d1401900c2c1c0b990f4007011136001090044000d40c00d604101d000240c0c071000c030703200c800d107510008400101d0030740c821400a2010003442640c1d5603207003082d0001c61951182400213503a80307402035000c200c05110b10 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 808545737 1250 808544487 808544501
    0x4090c0816020309130507090b0c0f1603030816050706151a0f070b101a0304050d080f070305190903020c04050915010b0708091005130f0510050f07050102131404 71
    0x7070158680401070300c03517030006041c0513003000704108141d00f0115020507454020f0820690302402011020b424802807840e04000305d00c0103045501600080000a0300b000149401c1705c243d000d00302e8041c40c00e42045441d07026200003d030005040000109207110000500c0d0152040d0b03400c8070f0311081207103c3e050340030f00c988440031041d05000c0041601186030840101e0f08662a810301d06105603842d882c520441e211501c8543c0298030001c140400c20804000c0307100c8110040c20300040614041501c44c0600310001c01080030f040e00d031800111020042000c00038004480502002440c050b41002036a0303400c40c07203c06015a26050228011786000207090f001c0c28120080b000b1582e00f40310065249400c4024115640c0c03006102d020010740d43e00c2c1607944c04807465038034180c983e0110780610360380d4503c0c1d9001034a9489200d5040c8200c2d220308152030b958000b1820101c2d501c1e880b21120700450311500c84054203951010558509411802200c4800c42c0c58018481191115140c200300480c0c043c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 808546987 1250 808545737 808545739
    0x1b0501031b030902060d0608070e0a0c0f0c320f060114010c050a0512030a0c03060e0604020a090308040914090601082a090f01050307081b011404090c0816020309 71
    0x7103501c07140e8894802c0d0081c40b00303107101400f003030300f0080504d044006503011130f0440300ca2600f04031428441c0c00266404030780d212100810601c10b03210303500801740c440c681d854400c000704103c0b500c94038184903a11000000f800d60051312220000056140e08a24405001200d00350340100c3c81e0f042280c0b04000ba0960585000d4141150b001041100560795030340c0d0440100c84070300803144d5600114109000c0100c4612076240c01f165649460100141103800a8a124041c549801e00602209a0601034981e0040c010760300140e072406c1d00c0d501581c4e15140c1e80d0000349503110006001c01c034003469420845507011b10030b282c040b141d21001a070f107031200024014107400390300450720003900300301207520008443c4c06101303001440f0216102041c04400226404840444c3c12401000182810403044004020203800340c60780302d1044c118100704107000310f150780c10800c0c11103c0a0708038040b0411500100130f075403010810080d1403e0041c00280c030880b070030801d9a0600800c95882030021040702ca46140c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 808548237 1250 808546987 808547021
    0x90e0c0402091e1f0201061401080f0408090a0e0c090405011a030402040903050c0f010c0207090603020f09040302010b13092105030406051503010204031b120506130503161b050103 79
    0x140070701c40c140418607031120103520070044035080c000d426180462a10310b500715400071489038103152390071403460300c0c0e174032203504001b03901c1c0402c40d03ca0003594040c2e8105520485855072554043c3c002030b800c95294001010500d800d105000181604400400c140c00c4240e506014680e0b1300c03001805010501c034802c61107404100000750041ca81340d400908568400d003030040c140b413850001e4a2416a15504040d090b039540c401c50300c04290108925001001140310501a0a05650204240f03c490882041c0560000d201080030107000f90001c980f80f0101400d4004d00640c6241c40a014040002c01511080f0780b5040b030b1402556810504511400103481303891854440d5a1403000901e4003d294040340e034800f00c1000110b43c0c0a00040000f140501da01d240d4908460b9920450001158480e401c00c3c5012a00000040c0001c1601c5031b2200345180c20081d140351a003070980c1580304455420f441403040130004002c00a18a60700c00240700b50350498aa081d8451005500b03d40316807400404801d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 808549487 1250 808548237 808548259
    0x32d040618240c050102040e040b0402120c0303041e0503060403051806030403170417030c04030b1f030f060609060e010e340504050301050a0b0310020901080c0919090e0c040209 78
    0x103000303c900500d540c0c07013200010b281070340ea0204600f10a1041c3c03001c031900440b2109000652403c02881d0045404c984040c0030300300c08003000a583c2e0320a500c180d00c022603841112004d015605e0107000010000a4190b5015250515000f88668820f028101e05c22130304103001019401e04105880c45694951544d02c00040d840300040b5007500c000380102c40c0065100410707917450081501071341c06090f018240d151100c0c250714100a42c018000d100044500c84004816100092225080205d80e080580e50008102900b09840900615002075100c04d003008400074080b41c0700c6031003a0403a48544011441c0707442e00c10f00250303c48020b403040014181204001f401d20642c040440d8100d034030509102c4e1400d81e4403000701e800c1d607a086442c82c0900356104154022802c05201010540d0200601186000c9400c80044c0290102030000c0b4060f83c00801c034075180b611351080c42ca01040d8060444078030385607180340200c040e0a0f040c10036001c40c0640c0b000e40d4042d06040c000d44194010003800d40c5052 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 808550737 1250 808549487 808549559
    0x5010507050a02151b010b0609090403110303091614090a020c0705041407080f1018110d0621051c02010b0604080d0e01090602032d040618 61
    0x15400514094405018590b00c050050b525811464030501e2000c625980300c408400c010b1100422203895036005905005000d205561201e045a0600e4411038400da2143c0704d90808859a520b192000100c40c40004140500100300003000c0c4100f81843e08003112203a15144108030b51701000c041242c00c50500c001040312901a90060105030b00c030390b8101c50030307155640c0015003550903da4680405041c0c20b0701f8450000d5100d10701070340c421081c4940d00b503607040c94940c00c82c03504410b22907000c0c10689400c80980c2c4182c2c0380c001c10301a0110116041d10b82043c00040c600500140c03080c9008001852151810140454131452000313420402410039242da500c0c6548203116010041030440d562002c2d26080b80d131320400944081c00c100d0008102c3c0344117440b4060442101d014825040c09050b29041168550000480c1d0402002e000b520403a10115100190400355049900b01040e00c0881c000c2402540101107841d024255280c00d80d1196036601800c1c0e046000b1907190100000d440206011 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 808551987 1250 808550737 808550747
    0xb030d0309021c0803012306031504090c350c010e0d0f050312010e0c16030e0306010b1c020a02030426060705090906030c09132103051609030305040501 67
    0x101c2c00505104003d0b10400f0b020882c00c0e0f0082d50840d00188084018400c82c050301c1507105054605515003900481c04d01d00181c1c0380e0000403c504080244414280501d48807034205044059100d140400d8280e141d10b41c0103622140901300c0f80d45484a0205078103031082c070090b00000c0c0308199024106405c4038400441d40c00c030f804060076030420f41c480c01100c0016a052071500010b4000c60241da00d40406c04916410362030181d001c0041403d03010140003c0c80300d9081128142c903015145420050700514040d2450b007101031207654180901c40001501c074558030020503160040403030b0500030720f040140031801ca00943c50f2100040c4c2c0309020501020070944070074810b125401c2100c1119010021180303244c414222800300c0040e00202d1031151600300340c107170325030080c104401600010300e900c0e01085801300003c000c2c400020006900340240f100104241102801224020340642c0f800c01c0c024016260070f8901049011000c0500440c0c6442142080c1c00e40e030389903030340a19203850076004540c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 808553237 1250 808551987 808552001
    0xc0901120327050315042003010906050709090e0f0331081b06120406021b060f1503031207080c0d020c0606090109090503070f1a07050c0d030b030d03 66
    0x1885000400003001c554a42560020407004442e594001414403040c50b0401000c0070342640c079115080103000c005500212180d440c0c210308240b1603400000000020302408071501e010300514501000d20000c50360242e211300540c0c810100070b106c844c6035221442e5591076210f880410303c1c1c01c10302040c410411601c5140d03110383d1150024500c25004100704210b00070742c0d40d224408981c480351300302100035800c0f02c040c10340806c200e03400785c01e1440c10880880e2041e80200000c08c990b5000844a81610a6000880080c000c2c00700304c4c0c426241c24201c030318031a8070903110070124000001150517035250000450342c40c0b0724011515070307041c1c89048040e00d4400020b00a00c0060105002c01616060b203440903040240d00d260051015007028030a2042418042e00b005001074141307008800424000401c65480c29803021411002c000d06042a1003010441040740c00410220b01c03e0029255006c0058018880110103072281c20300c10042c1541110ba4484005402d500503500d0086018001c3d03000d24 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 808554487 1250 808553237 808553243
    0x60a052b05070b04081005010303021906110708070b0901020703050a0804030e040921030204050a03170f04080f0105070305100e04061e09030e1215040501090206030411040e0c090112 80
    0x281503506075030300d550901ea65500009449100410300300290b0404020480d02c05a400300304010550544e20003c0d2286802c000083d021a020300ca21400c000159024000d000c5d8010000c40d1905440d19100102d98007400060f0b583c1010311001c25464401031089a2400c0e03816103866190007116201651100001041034040c0b06090100359001d88941c0070b400300143c450341000c0100a51009485043d140303080c4440e00301881030006005588030140b80c10141c5c1c2e003158500000c0164100e84482c01e1082c9190113407031040204002851800003e032040b24412140024030895441d031508604440088034110810000082d0800c2450307042d00040b41c000b40030300310102c1c9041105005d4600100d054036003650050f9501503413018103a0005c18401840740031101c2a0f04140402d0322079540f1a134591141d1402080303d8007180c2004070940c0050006075014151030744900e0181810a121081d007550300c3c0c05507003458030300075075050046580d5249074002082010075908140d91203485203c0c0c00d07021 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 808555737 1250 808554487 808554559
    0x10507170405031e0405031e1e030d0e0f101109131b110f060103151d010606020c15031303080601020a0b091c0807270b21060a05 57
    0x1007000301d0500140c80648221543d0301690b6145001d00b131502d82111034450742081090f200040c0230210002c5041002454030041c804a00c03d48050014254840d030600b600045282c080c180404a8010510b031240000300010790324243d1340365800c2015240d40078403210b8ac07190200a1020280f500c0000034034058003003040003410200441c0006102166204414003044145043c842009d1080002c1d09481c0f00c01d41c09005507501d96034494901444001200c60300c0d80c0c541041001800031311644040305c1f84640002d20003150383e008043d450f0030502c20064080d0109024140c02004010216030248031b941141450000240d201205d81002c040c00003411030040b503000c0d0000c182d100c02400e0155864601900000c00b00d50028445045005c41d00e006218004042151203604284882002c2960710400402d030400300d03292000107000f9410030550550081080e0344030550218518a50656400c4801d0071511204104000d68245216a60340300c881c80c248001441c10468135400c1103070000c000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 808556987 1250 808555737 808555747
    0xe0a03080f1c05041b05060f031b09060a03050114040e0a0615120804050f09132402030c180319020609030f030a02060a05150607020103020a142a01050717040503 71
    0x210001e56406403819604a0b0b41c1038046107941502e07444001c01001b084900034a00000403004407401c0c0002032690410342ca0321110840c0b03400710354049a80e403400003000241c2d00c00361401c014008010a00851030b04400300f004015640c1854400c0e00c070410014001460300003040c0c2c0d1802c0c050108010340f4016800402c0000403009008074516200314450440c540e1100c0c20003061003075100c10406124443c10304181031200c2c80b00c140600070480341e00031650016081c21303040919009650726106c03000e00c51001042100d1a106517000c4e0040d488010b801071414034851003010755484442d8400080611344509100041c9044001000f5010010b0166210708207800100b605580210755500c2c0581c01c082d04000810085200d126488021406401d9403005440c0204106004110009040c541d000074a104164040d0524410b82400c4044441d540d0030300300313170a4074030801c0c0340c0b0781140c15501c1c100d0540c50640f040c01041d1103049980d44c0e0840d0103243e0340c101c1d1003549001e082501c20b4002080 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 808558237 1250 808556987 808557037
    0x51005150a0207270b270c1215030c0d0c0915152001060e04080901030b040e03190813120507080f03010f060f3f09030e0a03080f 57
    0x800c1311200003180305504d01410342ca62030500340c0d840840e8592203403010402e41501400c0f40b80302c1c01c20110303440602c40d0113540d8900c0804103134490704518010001e1044d041000444c00c420365014130b550180c09850b00e040240c2c041c4031200300907040062180c10450418080d0145503030115403102481c030100d60001d9a2006001c8547c080c1206200014916420881416040046044907483c06a00800150385014003a40c1d091401400c0248080720000c1e5101442e80300b5005104000e600030f10800c881050008900d64039404101141051a215003810304054041c80d1410303c240710600d040400c1c031015940d031b460a207543d201c07030005100c0309100300804116414007030050300103042e40c020380e2541400052244030846034080380030130110b0034140c075860ba40084003019400c081c84039806010742552820320346d14a524140c2e081000d41c800c075000b0111070350b04010640d60094684851b5090100240664480580009403040c64100103458000300900000c010605d504c28903089981c074100 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 808559487 1250 808558237 808558259
    0x1703091e03161401111912090504150302210601031106040308030a09110d030c02090a020c030f072306010b030408120114030709021c020d0605030f06070201051005150a0207 76
    0x1411110318519491481d00300e40d6000a10900520070040c0104006c00150343c1820903000000c0d40280b142101e1600c0700c000500445240001d0080284140503071032a5100b050405081e92100343d01c0f855000703641025150300b074030100c2c601d981c0e002c029103216030030b50701d80c03802c0e96031002c01083e00708604000000c0030440394800b8501800601d2400701340444c06050100000603801d40c1a403140d0380c0c400c42c02000a40250341460619416551440302d50b0703a0080060080c001c18400442c1070100180b4610390030034200081c070171203200d0400d02c85558540403846080114001c0340031724950285005120b280040805036902c1840303041101d107003892462042507002001c2c1e1010704800480d0498115501c1c0501500d400344c07081e03200450038000b00c1c5489280d5680d039180d03090746042c0c0c0040c4404500c840c0d030704041c01a05000c0d0440c5d000410034401280d442c213003125100010351a01000c02d19020090010714200d5800424911013010f500540c0712175944070880785020340c45202400107540d06d0b45 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 808560737 1250 808559487 808559489
    0x10518090a212c09060f15130b191d18060111011a0d060e03030103080712020303060105070201050307111e0f0303060d06020a020a0f0605011703091e0316 68
    0x1456000b80c0c205145038000d00603880034442c0e02c8030207140c02280000100058052004030004480b8922151240300c00304500e040c0540b070302ca8001240040c1c018004070810002c0c4081c4618a0309040101d90311612206039000314604010000000070b16418903a108040a00d041c000c003c00c107007031b400484000280e0365103142c0030300000e600074170080121030368120043c000602c4001d0000d00c103100181c40c2c1110305d8201410440d1080c500c02801c0d500340300c06940b01041c05e14111045990342c0d41c50b03041801007500b101404503075411940101c2c504803403010080d2801020107865090900b62164010f440a40005181000304490a004007103900303410040650702002000c100f003ca210155411814a5002880707044e40382d100700309000e0151030b03001c0c40541064000b174005803104400750049040c04191a0041d01c0c540440702a18117000080d40003034120750b140d0220380703084100b28580035100c0c06016040c2ea03010800300d03250b03e580640030340d09a13568200201a01d03d05031285507a40704000c02 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 808561987 1250 808560737 808560773
    0x30e0c0d2a0b07030306180b0f01051b100905160b1c090f140c030d140d0b060705031801030b0f040b04060b0c0a2919110a050705070608010518090a 65
    0x1a031b0310810000015a0b061401040f460b00c1c1800074100100c0424211200041d50743d04000002915130020000e040c00000e031f00000c1c10668a000d030843d18440003420b0300c00c0c1c054506014201500c55624441d00040003121100044541013038120b01000047d80b0f03010740050a10780d195452000054027010313026280ca407040d0564020840c4020601d49401c0032000c1d218002c0e031044109401c8982c000c8100100041d100c80c1040e940c001409452001e070101d2114503401c03170400314012003000b0004c4041c042d44008030b40711404c850070381c1c0b00440070740d0340c41001144c011160440e1004141071907049606000e00c0a080440c115581c0d02010a080d0710049842c801074102148104c200142c0300b51710340d400d4151040e180c13070460019001c2100c007500075200b00c07880d02110815100c00400c40d00a040030b89440c8030701c0d9403104083d45000d406030380603100864090051010128080380034002d6070b4140d800180105181d510010004c00e458040502024801d2151801400004e4826090044240c01c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 808563237 1250 808561987 808561991
    0x50c0406120b1f0b0309010e0a1a0c03010b09040c182607051809160b03090d110705040e032701080a05162a03030e0c0d2a0b070303 58
    0x14242001c8078510406048010325000c0e0303c03c10811880d0f49a1000155041d011301c483d80c03500e803508010700611244003001400e0249040038001e215103801c48c00079080044007112541c0d51143c403115900d1100340a510205801401410301504050348401101c0c0c0c2e1908000e60302900c500f43d4070310001410383c00340c0315078580004402121401104e0700c400c03904403080203104c15400e20001855928181d080500030028200c0011200d03c4204048101c000403441000c0a5a4a40d032003c4200d40c001c030707003030702c40b52180d0024104403d03c40d62290146141c1074000c1c0a01e00d003480104400382503a00e080304d109202c1440342c40342003070618580501c29100c0b8000780a004040d00005001c5038001404036686a01d003000b005502c005640700901040403038a003901c52070100b0000301200e8040b0b4902500c200840d51103150030150141c0c8846c0c0d076a6000c2c411941032089010403c200c0304110728004041d01c4201c1e0141c000e03802080e0880260141d989024a6901c3d03e03902120242d030010141a00000e03 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 808564487 1250 808563237 808563269
    0x213050a050703421a030711060f0711010b030f0102070203070519090c030212040b06011b0c0e060a120f020103060906050609090405030d0905010b03150f13050c0406 73
    0x20b6018400c482d184100f0740d01c2003605204440c1c80e0444064140c0880d88080e00001300d00441c454040c0ea000080d000c15180d60001040520486074143c008441c408003080d0307440d10b045050080000c4651080c841c0c0c00c0311684070703910000200e81100c2d40e4441a0340c80d6494030440a61683c0922003111100c0300720000580f02c00c840c0c01010f2a0401c20341c0114000e599196007400c01020b02031070201502c00c10300c0e02040315060508114000d110b40303045581c01140d030074107000c10420301c00f00d00390140000366584004510703040007030a0205040c410050003001d900301d0422803c21101e0915a01140040c0400032031680e0f1340000720302c60510f40040303807881409180142103603014800c4002a0003480001c1128a00b4035010450034481d4031071480c03081607480000380821404004554034120752aa0174401d829543c5800c90180c90380c807440c5840390241d0b00c000c80d05520100c501510550030f9174034130f0103242c48441c200200041c080d07005072000e010350306015040d0f031154020740009080c3c42c24944034403 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 808565737 1250 808564487 808564501
    0x61d070e09060c09030a03050922020d0510080a0f05010b060a02060a200d020726070302070e0405060f040302032a06070c08190e03011407081e130213050a05 69
    0x80002010000f401c0c8080c84500b08a49000410403070141c3e050828590f162415000541107960004d04100300c0c2000c1c1040c0a00505e054015000003110420140029200d41e848032960841c3e07805203440c543d00070a0400c0c04076000c06030040300700b8091000000e0285c002008245a58441d8140c071016074018802e0211030b0b8110b124050404403101101d04964119102483c514842c0000c810803441c0c0214043c010320400070400860040310301900001260140c40185180c1c0009074240d001d40104040040c1c5e20500119a500c030300d40c000080c0c10107545190514114441c064015001c5210034000107200e0126030b890300c1c9406408061171561060100011443c00c90300070200010400d0900c030620000310fa84050303a007201030301d10305644000b05001c41201c013028a030f06402d90540c2482c0703100c8010200c40c3d407928040ca03080d540700c0c043d80e82e030f11032400040342c0b900c0b07100400108004001401f00031080548041c5900c0104200024141c071041e180954600360740e9a064165aa4140846 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 808566987 1250 808565737 808565743
    0x30718080c0102060403031a03010501090f1103010b0316050f070809041812030507050c0114040506060913110f0d24090503040e18070e100e0105030a061d070e09 71
    0x4091040003442407941c00d1000035120800a00002e06164445040c801010400c62030303402c040d000174008003c650394603107010f03010f0000c0d130300645403041c41c0004001d80301104800312810f139598001010714544540e5409000304864603c0f581c00c02809101c131036006601c1200a10145001c0e031881c5868866000800c811595410a0010003400d4405800c0004d04e82c16811260b050241c1400603860707980398000d50b1548101018003003a5480c2c0300d034101c000000540110b0040c0d004a08840743c40e55481c5c1401000c40b0b040c1c41c6003003a0b0040c81800c100145600c6080442000007074012000311240b0804205a0851000708a400d4102c040035100c0c01400b044919900d40d40c424003e00c00d1042ea80c8036030391030b4071943c060718820f0826a000100282554115411410100422125416034036003480c41c40100940d42501c1d0611080000640020002d00700c034140c8200602030088040c07903581c1d104c01070410020480d06c00a00d85d0000c00d90300801c1c043d100c000c0c0100400341920340342c10400300e42 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 808568237 1250 808566987 808566989
    0x71a01050910050306070c0212070f0f0503011e090807020d05030702120c10030b12060103051006080d050a05130f080a020411030f0103030f0302040312110d080405031c020c0102030718 81
    0x108801d0202e4040115644c0081d9098100056040c5040c100000d400880c400ca03826070a6846c2c9403003400d80c002860039074144c0d0b160407222280d80d94500d05031100100b50a8070074042e060b5610321204a60103080c0e460b80da02940d0302c0e6110350491032400d1034640c041125181c0404094405800104000c019402d00c0b00340703444030380210005840380381480740000e1301c1182e1044190007010340c0c0e01f940e0201c90710b070368003501c0e003c00448049400c95a9203281840c2d440035000145000d00b42019000117103a40d0005855425500c640c0700c07203003080e20740c407401c96150f04050000628034144500c000b9072202075103001c00207051b0340c07005085046060b0043c0000d031100c503039a0f0361545108004101c138940f030701c106050542e40e251609441c182035405086010740100e1704040d0581002146100d1107940000c00d0f40c00c00600e10084e10140e001c902e8068690020840707001d04030303030000c00000d0350b0880e803129800c003002001400181008119050182280c108a40b54804240c042d103c000c07000316072800000c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 808569487 1250 808568237 808568251
    0x2101d06090606090c070809120c0a0609080d030c02010b0d1101090b0702030c010c02012a02011b030819021c020307141804110c010c0806130b011e0203071a010509 72
    0x202c2141840b202048090600820382042c0e40030110300740041200c0d4004176120000002c1a84414440c2c140d1015180c008814141d80f042e41b81d19000902e2502404181044540b01d2000e0140d0b240110790075405820188090400c5560340c0c0c0b4200d07191b9460a055407280c0e4003586102c00805820000076006600c1d58000b00301c0c8403018440580184d0303000444407400d48080c80c00390b8050500d031006135010310186003200c0c10302d071800002e941104255080981701c40d000b6030b2126008100c04444c03804c2240d505d1070183c000f40640000848480940400020400ca0500014581488088500101521403a000e8945074002090050315a8440750340101c2d03070b03c81c0c80200c2c46c00d030071501003840c80181921418051501ca1a0000f5980a60700035901c480e4810802440032400d50030005003504001c45466120741450b141442e409030640c4510810b001d0706864151800c05141403c4005105020f101c608501c0104440000610b075032014000504035400204080d5044c1420001d840c00028110 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 808570737 1250 808569487 808569493
    0x15040b011202330d050f010b07050d030c05220e060a1d100b070b0612061e060307030c0f090b15070b0a0609050702300f0a02101d0609 59
    0x2520142c0d640101c1510f04010f98031115003500781c070202c510610442001c2000400c140070840036040c5a042c3c11543c4141541d80c940d0b4180d0307803152840c01240c05104000790050384403045c0f81812501a90202c038142d110303070501c40d003000e2060703050031a881c440c9084022104010542013158212191025401c5101100c001c03440780d007080441da841401c2d1826018003c0103410116140507800000d100107007000c0d05595a0303940c450f080400401d902a14014012011603022045907030010070750394001c5074108100030040072031045000103030034081c3c80c042d454040d9000001c002265140284c0003010241020074034946032200a030200c0b00c10103c3d20307000d482d442006180c20448202100c0c0c1352607000b101040305459030300616004002d55003100544900d00000c4c0000250000f4000020180040942c44940f4103085030408080d10a050400c000d4024820401c01c0e001c80030183c000510380d48101d8141c00c101e0342d291300540e8000b00000756030410f5010000341103602031000b01d910000c65402 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 808571987 1250 808570737 808570769
    0x11061b031303031407260706020d0c080a0e100209010e0a1203110a0c050d261803071202060304050a0519142a0d02030601170601061b0b1815040b01 65
    0x4401001841003400d80c08102090006c0e4105411101542c00703541d0031000454a448110711081e00038a501c205400200e110320000239449a828003d031420101c416001d040c2c003001000c21100079401480d1036a0501a5940003000e494644100c80e40080c4075007503d8a2640c80c85050107407008001c68a60000d54200704820004034804042c02d108a070720544400c220100d013400c114681c1c0c0e2020314580d488a20350341d50500240311300350150896613001d00100703040034400d00400d5595000d62152461400e510400c200242c50414051a4080d0040055804100700b07507580c3e9052458144020040d098200c001001380104182840d41e07400e4040d0080094103441011584c82c0d1000c00e116161410320354001c0301e89500c0c1c002207907280e103501400726031855864000d103001c10611402580c2c51072052100009100384070f09288007090700903000301640b4282c0d944400240b48402021b10403a100c4500f2100e03404c81c420064201c140381c0a90402c8260304051038424030740541039112042c01c07160009 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 808573237 1250 808571987 808571993
    0xe040809211b130f140610170703090807031205060105030402090f040c0b042402010c0912050a0209070809070f0b04090515060c030c071211061b031303031407 70
    0x1010700ca100c004100c4542501c02e07400026901ea101d403101c20b01e01c2e0303043c228988084400d540110031445140740e4070484590391042403007181e81c0003d8170400050300c2e0643c00300880c420342c8000b40e0030454900d00480d01020a8450592544c814681140040c0140078004c1c810034881c4500c2d9040002460f1247c65401d241d00022000e95015280d1040112000007107020000c01156100c000e14152800315211540ca868400048549038000107031401e800c00f060f08000c0c418401c0c00040d4205440d81c07982141041c0c0c08000d0381d04514022186481803201c2040541c0c0c4241e40d0b28070071840c0d5031f18500240390113040c00d4140b91040d403190034000341c441400d00250350054141c5080c0c543c1d901000515940c2c2c0e440c807e844908490703c0036000440040c0d9030f9003403171b008001407201e42400c00842d92000d83daa03081903020142c288010300a00d441808140862506d400144a02c13081090b00203821000c003082d09003942d0201caa030b4184043c00040070820541c210b40100d5660200685844c01c008090b1 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 808574487 1250 808573237 808573243
    0xb0f0f01030b010309020a0f0302180108031903110301120212060f060f0d0609050304030203150c0d0c020f150603190f0201050c0f0a030306032a030b0a02040e04080921 74
    0x611800c0c14540c4580c0c440302036034481ea100e0070320181c00903c0701c4901c9543c3c0301c0400d40405a4081a8000c00c26800040300080302c07450414100c6500500840c80d100c0c4039242c941c000301e04000f1030400c0540381d4212001002c200800355010380031080505000ca4241d01c100841d0080c511a507680340e801260802c5000c109000020750f0061040d1000320800211a0000c0c41070031901c6001009503182400e132405000d4004003030f0095a00c25000c5442413146050803008045049030191181c4804100175840c42c141c0f40c02111203050039004031030b103c03c0d41d480c04504000b0401064000c4988020030840103217010094080c1d000146000d000900000d5103c1c1c0080e1003040401034180600000c040300040420070049203c04044404d50b08844074602e40100035015610054a54041a40408030011a00214401c9203420010b10452082c0755540302e48a241004060842850303003482b002803c500c1080d0700313a10440c40b4230210b640e00c02055081200c10100d024080e40c60043e021240b4074808000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 808575737 1250 808574487 808574509
    0x1c0c0504020d09050106030507080613050c0f12010e1b011407080c070e010b03040b0109050108100e070b1b150c071502071707060b010203090312030a0219020a05010b0f 74
    0xd03200941d0302e000c0c548903031001c2c16100d20010b01c0c1d07610f031075400001c5c4480400c2c0102a07900721421340c0c66684991070301d0308000c0c500341000b414a81114010700e00074038110400105058000d8011030804d40c020078a1802c4406140c0c0c06d885e01c2c2c00516800a404402d00d0820401240c2402c2901c04004408000c0d03c3d2801440001000304000164410700c103041004001c004022001c1c031040c840d83c40302e02d455100c0d00181c0c6e0071610003e290002060f00059401128180c41e000002014140e00501a02004d0f120007501d0aa06020701c500119144040030014000508284008802c0d5814a000c5038941000e0103403421404002d4000d0082c0d45900ba0101d420f526005232504c82480702c50707540100207115044008201044564200e18a00c000f030000d002183d000c1c1800304102c03d5108016131b1248154810103a05801c2203501365502c1400b030010f0760b044a02806e00606045200c0340e11300703c07400030301403e50140e400324011008201090103540d00e00e50060711440350340720402010401610701 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 808576987 1250 808575737 808575739
    0x30c150e06060103020c030a030e16081b0d0305190908010606090501110d0804121202030103111c080a05180d080417070b07030f030b090103121704020d020f011b060204051c0c05 78
    0x80e030410410ac800b041255040600c0c011100000341070380e498503680d550480118020002120144960452503c2100244000d030540c507018684502020000801b1007038203451001d02c0841c88001c00c0c51902481202c001c3c103865190742d61060304040004d444208226403440c1a503010074120040b20340e000350312681065000c4060104101031800c281d920904610003048824030100002062101c40100c1c0d002c03c1c20166018980603445407210b070380c2c6044041000e0300b611400c102141d100391003032004142c02d240b141c4402c1c1100401c400090510030f0801003e8400c8600400c040c050310000303c0e005500c54a07880000c080c00d501e0b007002d58070103008a600103000d02480001e861001c074001d400c400c2d50084020645c40013507840f40b41030260342e40031140e0700c170014203c501b070024494040c000c054096074004144440c025465401c001d070070382e5001e640b9810081020880216102040005080c20b486805c0241e00c0f1401c03c0705102c1d01410500034160354080d02c40c2f030384002c240362440140903164 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 808578237 1250 808576987 808576991
    0x70902370c0305040b03090d12050708060112020715021908090705100e0301021306140702011205070e100203070506100b18150409240803030a0504030c150e06060103020c030a03 78
    0x151410155854044c2d90300c520b0060800000301720610381c0104824000702e815480b100d580c0c400b032480c1641295030483e07000300400c18a00200c0c00c90340c01058003441e0a60551030161a000c00c1e40d03070390965a000c01e08010030958000c6006010009050b44144a9821a00d0f01708424540b6090380740d59500581b01d111b0140e03210384910710300144911880144160094000e556602540105010302545072061200284081d60b02c003680160203000c07105602d4050352940c0482c40c505d9103140007084090408001e001c070120a008841c0c440c4a1324480881c25034020b552100002d00788942850300090039074020704602041400140c1c0614161030054801d620055504e03000800420cc0307280e01542000da12100c040780c00140c4c10a290080d000b030460349000200803240c00229495013900c90b01035214950018000150155001c0d8481e540c018000e04c2c0084078003030140c03560b00050782d46d440aa50640d8448075481c07858103003044200c1e0032107400e103400c40c6070850780800c02c2d07128082d941c13622007016 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 808579487 1250 808578237 808578257
    0x132910090c09091509050403020604030306060302031612090f0c14030304120816170a140903030a0c050a0204050a1a1203041a1c020405120c0a050103180507090237 72
    0x401c420340d4003004d4170241c8000c22190405007400707540c2e803108580480c0020300307028012620364400c0c02030300d0281c521080808001e0f00e0060056441030172610b1500a06a030720010f00e40401e031810300341d01e10103024050f80d0f550581091400b9091451003a1080c4c041e81c402c10003004048032485c41c1000c4c40b0b81200e1407a480e5000c4003011013211071442e0300038011280745405000c0c182e82800c02020003207180d80b544129007456200587e4940900c010440c2c1c19082480f855801c02d008040c202c2000344603109840400e076480d070009040b9442034880702c100760b03541d60065100094482c00424552403c8507030b1040b20030850340c50ba0b90b9100e180101002e0341400011522605030100c02d5850050090b8424480c50030f00744032900017504588103041c421070511040300710300c08010444e20b2203508040e0584901600380310040d005080c4080540a004d0400514403020a00038844e900c094103a0704005a900c00c00d0358a00600001540ca081940b0b4a03106c41225042000d18103080300420a4240b13582c42e0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 808580737 1250 808579487 808579511
    0x280f030c090e0916080c1002070807050d0c090207030c11030c0a14120318091006050403060b132a0e092208030405070e0708040506132910090c0909 65
    0x11040140080c4c003030140f13008180c02d0000b290000c1c0030941130703846407100c4800e02e8040344d68110070710840407103401c448070510040c1003007410702c156107002d02d000c10400c036500c02c031300e00492384503c1060780061082c080070420006401c14062403000110003c262603058040000c902c3d103858424420708015074000802175446031150484404004419240c4941b41103822225aa01d40301daa54814100c00000807001108030081c203060310980da48040c2414110703a190310043c5001442d4607440070f001e48820141480c103000c0c0e41d00c08a804180c00060881c410441c5000c013642800c00300c1808015000d0008075100e261019922119064210003410722801f00d8006141c407107000503050441c00010030003805800210802140c035445d23400603550b40e500204070344581d810f440080042c1c01c10408540070070804441103a000340103006117025080c40300703d90450b400c440846045905451000c10403014415035504000380000348080c08080c4d60564010700000050040c1b00806944078201050 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 808581987 1250 808580737 808580743
    0xf0601110111071103120c120c0118140c0103020a0509010311070f1209120317060a08010c030e01110a08161b030c060524060702010302280f030c090e09 67
    0x40030980d614940c3c85070f00341000f0340309510695529010348034003840e810281d101c030400c684100b0b17491000381c07210300c40c00c0d0102916039000842d5a041503480d62066802d080001c041415601c0c42a0842c040d81600e08071014100035450000034141032060100d011019005002c441c0c3c280400d00e80060701c00c9203c415400503004411000d4130300003414034007004010910170030711100501c98070785002055aa800308100030f140100011300103008045404007041070903440d15003100700100742c00b0010b91688455821a1076042c07042002070b44031042c08505440170320490080400740c1110914050901c0c40107429440042e2210b0250310002c403841c0c05081c4140c8805507200240704680035401a503003401040c032254400191000e40c94040410050f4013041545415980061440d100c5010142c0411946030080701090741415001c122181700501c0628a40d6201c0c0c030307a107640c01d00c81140d038400100300309010700513581810b150440c010002900980c00d02c0440304001e82c04d1081e0b989003104542 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 808583237 1250 808581987 808582001
    0xc0f0f20010c0201090b0f0601120513060524010503250c06150f05040b0d06020f090d0b0f0903070b0c45031504020405091c0801030203010507080f06011101 69
    0x203065182648059040d41e040d000380301c9950080124403526103070340803948041e400a44002d408100d40144440c21484c55401072079200c125181ca8400380d0703103162141c405031a81260240c0c42008100e0b0f02c05485030011210004c004020f280c41401d5103404503002003100e184030124032032034880400030001d0b02e22810a80c18116800740041c007031041840c040c108903004034014510301400d40d002c0820207081c130703200d04070b5040070003010320100c0c0e46151131303540007940007084075819203d0420560718507807900d1602181c1c00d445602c0c403400900e0584c0c00742001c031340c025080001d83e400c204108c2c80410010307005140c0141050325420741da00c8403054035150b035901e00603800b108400642c03010b00144e5440400b411030381140c03100c030000d2405107408040d1120310003002e903c2d43d41807040226000d4105540216800b000c01c50440b00d0b01051a1038071307541034281c884100000b07040c003001402107060a01411341c210200e4184020309040c01c41f50381e003803030900400c240e04003c2c950b103050b5020902500508 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 808584487 1250 808583237 808583297
    0x7110d05010b0a09150608090316030509180a110a0906030b030c040c030213140d08090d08030c0c0d0e0114030601090e090102220312080a020c0d0e01030c0f0f 70
    0xa000780740d80e203100c40c2c0501060781000117042c00c40440041c0c0180200c41192060b4160307805035180c90301050140e40c800901941c207904004040c001d000c042d45440c0c1c4401c589044010441c0c081d80b825600e007805581e07a542c21039070291801e201050f0481e4120301814140c540e02d040108603260b8481c003003071506107074410140e8014184241c11503880d070554010000044200750f0f010074640c6448624031021007c1e0304c0903420401012043c3c0c007080215010700465240103190003001e034000d4990a50540040c0d60903010400c0005401c840c5400800000c000d81115003402c0b0f58012200c030018100e612054000d4a08c85400000144160310a10710b620141c101c0424800f01c0c0e060040c4958002e401982105002c41075841180c00400c8200080350304407548118026070803140076134201c5000384090200c15000d50240503103032080c1c00070b00942c21940702641d180f0700d1810303001000409030380359107804605128548100091060b8482c0000344c02d2585070819091814400000c60400d1010801c1d41d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 808585737 1250 808584487 808584499
    0x20d090b060609010509120a080a031d0a0b180307080408030a0215060d060c020c1f0e060c03040b0c12030406051b030702100b060c06040b0f071b1509060903090f090207110d05010b 79
    0x2b2180c150b030204400c00c40400502d5196034500d203400707660381c1101502900000040c0006503480f0b80c400405a610480402039a00f0300e4969a10f1008a80094000c05000d4001055020b441d0790304100a0742e209142c5d00c00c400e001e040000102e4018000c0083c00f604c41a114180e110805008110b40c8113940f401801d103090300520b03081e20302d5811552011410004c7da0002115609142c2482a6044229424040d5240500c0c04882000a40c0440ca0380310450284000f885504207070100550320903401048042840d00d000d00004603441d544407404090603900b801406402917000440454011004000081441100d000140203006681c45045c00e442503030100310801c0380e6450014050768800c2d03405002e6071607580c0e064139004103e40d05000c80c0100381900d0004207014110401a485030300e0030000d5480915124070080d51412901030300841c100c11030400089050307008a800508013201d0450510100f50755a24004000701c0c0c0051007000301030040d03c00d00000394000c0c80000001031a03 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 808586987 1250 808585737 808585747
    0x60d0b0411010f020d020601050904110315150d240e0304030818030c1f140307020a1a0112060f1409060f010e0103030e22020d090b060609010509120a08 67
    0x142000301d049101c81e40c00a403541e2101a84240006001040304882c2e80240c40f50b6030a06050102c08803000380190384108056405196649052007070401c0c000401a01c00640d20f480381800d50041301e91601140074450940445010542030351408011a401c0f0740d41d80300700b42d4250b510b0806020444825403681c0000900001007154500050401040f0810302c50034101c3c109081640381c80740c941001e1340090707820300420300210401c2c18442c40200b00e800c1405520302d5000120000350000c036444009030b40881e880c1024402ea004404500b29282017140d0155030411044c4100f101d040e01c1c0c0145560f850f0900e903070104019400040c0f0314020074010700b46900e041401c140c0c0d545001e4501c120419a4a000401e05104501004d03040e69015142d00843c202602e050041c224600c10400d01112148050341e11480300c9c500013405404c00c1ca060200d0b0300d07215805d00805540d00501b041d8480d81c0d041103c11000c0e41c01c030081c0d60165070100c4078000c40d00f200708007440c181300200c48010700900001030 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 808588237 1250 808586987 808586993
    0x6090f090203070e04061d0a06030c0308070611070605190e0d0f05040306050901020702130b01080714120c0a030e15010501030c09150c0c0e04021e01020f120705120f070605060d0b04 80
    0x11f06818404041d800d00d41301070312010004802c55145001c05000141d0002050010480d280014000c1034410100045d030311042240b088100d81000100b10f0b480b40e101c2c1c0602000741008c58410b501211008800c104080a0740c02071569030749100c401c50180940c85204180481c005c000b0380d402183c025200380180d00d80355440c14000d40c0b00010483c80b8580400400740014514032908583c43d0701a140c0b40400d45908500351011014481000740012040282580000405407031902030104c40484075100c101031a806030594100b1159421258403212a400300d05215104080c1110803e00b070000b00c1e5030345407004403554003031a00f00040400b04c00045da01a183c4c40b5000c8451301d030203410085503031605c890007104201002d44010390301c40280d8840020700078030130f88140804201401103a1041018200d654100400d0140c3c00c020003101166001c00e214061200054042c1608044d4ac505451509058080d008014003e051590b455000480f141c03100c44150000c0f44d0080c0542c01249480e103 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 808589487 1250 808588237 808588259
    0xc030111030a06080715200f07060e060c0c1c050607090302010207141810170a111522091d010b01030203010501140915030709030c06090f090203070e0406 68
    0x42ca030410303000e1811100281220340403640006451540b0703565420110780c1c01080f62540056030003442142445440d40c04255004c001e0170b601004070002400183d0710700031020f0026242202c00f01d001b84404c105000901c03d02048100e540c2100700d40750b0b0118139035001500c9102c4c0c2c81c50f100400702e03ca110244180355070408c40d02802c0b00c0c800da0882c0c110766103071901c001800c402c8443d4940c10480004414015034642003440e43d001c05809503500f40e00b56212407840d03100700402c80c148040e40000b4280c1050280082c03650505940035151001c04000c200700c20000d078455405060010300044504c580c0710720400e0480c0005001040c0140700c000c030300100003065104884900483d80d86019140c45955000c8d0080e40e04840d416181c8900f01c244100310144164000102298003034a410000c122140c0141c0c06035020b900c49544106241b4114075003445040c2658210b5020303c1180101000751026400711601510015240580c0b40d4072044000c1d100405040d40407540203043c10310204018140c0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 808590737 1250 808589487 808589491
    0x3080a091208100b04031110030905070f0f140d1202010605032d01050105060906070c1a070c0e040b2e080303090118020d020603071709010b04050f0702070501110c03011103 76
    0x6020b0f22007a502c09942c2002d200d43d2100411080400400402501d802191005400540e06021441060554529040403840d820844450514900c180040c0c0d409481000c09080e12914041e504810107000441d000065400142001800c40f20990914400e400c000001e0801404507810b400e5500c3c0a0060380c00e00700c480f030210904803103200d101c0b8a0140500d034122a409041d6a00d01602002031010952144205584000b1400c000051405a115062180080501c266034440380076140c4150710136110390043c10482418002d102c0400c0d60341040729088560762402c100c1c03503040b10540003040c040201040400034106007000070038490100c0114030036aa60f030020013821717241c101c42a22440c3e2400e8042d411440f2120504c0050901400850b0042c3c04c44c20b152220755a0344410b100d07448001c856903d044e9458024428060400e03000d65508004140e00d00401d07450322080c029520792480c85480c0c10041c8070410518806e506100c0303004c208001600a11118440300300301d07051a0b01c1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 808591987 1250 808590737 808590751
    0x3030c09120a120f11030c010c1b11010e0f03151501030c020c04020315032a0d150b040b04020a02010203040209010503030405150903100e0f0c1c03080a091208 70
    0x455501da2034a000124044951036804412280400004002118120040d00e298014005040011700d0b01c81020009403200000c484000315411076070240041600d0b4040c40003205440060708200005500111020044007080ca000c90007400b404000410b10012580380a425001d10b05000001c000d40041c210700c00c141203810394040f410100d004404603041f04903038800580000240d009030f441c05030021508080800318018086040f0320001e03050109801c0105500c50280c414052008510b02e60400701010495000b0a52401c54550303030201500d0030800320001c2c0e981d0304075900707035500d03513001200304074020700115200c00d0942d101a0003035009030f4080c2c0c0310f6580000002114900003007110141c40010701030b1280c041405d41541d02a400401d01d060707250140c040710300700c5d0024070711510039a50f10002c02025541c114003449070402c085009020b005902002c040e501580c11b640c070400302940c0c0741c44c01c80e03096a074803c05d080c005c00024500800004002d03904105081c1c0c442c1000b400b500c8 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 808593237 1250 808591987 808591999
    0x4020414010f090905010f0c090e07050405010f0e01030912090302090c0408030f0a0e060a030218030f07060c0804050901030b01050120101805010f0606020f01061802070305040803030c09 82
    0xa034401005030241000d1081c10007a854102080c004100c0d40d070420100203100310004901032410082e05015a000d454900c80003a003440001c2012049104686070481124140315180038104000240107a0000303503088244414030410b140d0f80e0340f00340d100c1c003000d0b0740143c0341c50300b41061108004c1c00014103100c00d0740b0401810001c22140030050080300c0c2114100c5005600d4034000a949803450b4110480402c24841d030725140200e1a00d4030740c010041d81002d582c0040e0b070303040071410041000d615180494000d602401841d00c0003280080e101c0305598403070800d01301040c2e00e0724040c0d00c3c91069411481d041680c21000000b00444c00200e03506860090700d404211040042e22810300d030140e1002c4800552104440d0411540f80390b0101c080600e0508800d0603440b81902c0d11829602d050a000c6580d558818041000d5941031107840c1e14649100020f0044170310f4545003001100990f800414900d80c001904020140910f080710003c096030819251a0f00d003588030381c2450f400c007882d2240500 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 808594487 1250 808593237 808593251
    0x1908060109090e0c19090612120309030e13181a07050708042102040e0c03011505010504090209011b03080615070206030a050a02090a0e090d0206162312040204 70
    0xc015030240403c0140c85800508083e10791404225401c1915184045100319000300484c0003281405454040c10304038503100c0e0601c90f50320303166907501c3d41c2403450301c1010f00d0000d400703000a0b0301032618002401c040b1250f009003d040140b00c0010700001c000001c01034070842e80b4404100310305a6080100303c1000703502207155524101503402d84203040e40108994010801404407114803280300041c078900d01c80303044144d13606902140499a4a64200c015076004c40001036192609002e0805010030310303400791308004d1504001a014cc0030b81e0090101440d000f0078007035440d034810b18000c01c0006041400301c01118107420042d0159000307a4245020714100c2c1c0d02c06015000701d0341140c2d1400d80c09403100d850741d62440340b2070008101c058000d01020360200080f0440750750300c1c013600000c2c083c80d0300901c078903040591155203842640d00c0010150340100040244c0368540b00c10100881c40c1d64204910410300101e45401c210315500d042d10368a0101203010f18400c412a822648a18425201040a8 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 808595737 1250 808594487 808594499
    0xb0f0c0a0207120501140109020d05060a081002071e141903090504092f09090a030f0c1a10060810050307092a02010b27040b0c1908060109 61
    0xc0c820903403a6005030b4451039040080c0035100c060750308414043d000018103055040032031070402000b0f92218080e2038001c142e00104195612a0903004402140c844051030300d00408181c031500c011300890f64403a4003054840c14000301151510b00085031141c080c0c5200c003d450101c080704011044601244a4484105441c1965606c11166140c05450f0860654981800c000240030000e200f16221103a21071400d4080c002e1440030b6100b800040c2418125016007814004200370080203c03019074130480e01d500100c1e8000f5130208558266150200144000b4100711940101144012842c844c081c420402e441301b040e45804107031992941d50700c50b90303241c034484082c0700c07515030041d1a41030300040070070030000210b036002c00320712003000a44040d4465040740d0703103100b14998400500540d45901002c105407405011b002145c407604401040301211044810178020002000201500c49c2000851198900b200903100b646401c88221a0300d840b400c40c00a00841d404c6d90903e0100310101ca0220b07403 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 808596987 1250 808595737 808595761
    0x30f080a0801170604020d0303151512180204020c1219030c0503280e150708060105040b0a030902060d1b020606041e022208010c140702010815060904090b0f 69
    0xc00181e200402545e2500d4003006402281800110103156556440001e021121002e0780024003a903420408260304c40304001d0300031850441c0c107d404a00d440100748031107030360034000b90119406580060321040700032001c44c9800c0c040d0040122040000c10a013800b8a1202c106030140036490394180000c44d51600151258001a1184401d03036008409101e160b009080820003000d19100012071000c0c40c2013001030a0a071450035110540500ea401c004250307130400c0249400040030f19146260900e049a00080c41c025421240101034407000c4007015035903005c06807607540321303005d004114030381d80e40f20044a00e94044006102502401c00001c0d40703490a48200041c0c1d22002004075546810616010000d5200c510092080e461451203000390700800e0f05030401030308100c3c000040705545101c4c080d0003071204070302041003194100107140050341c0c440c40359608603600810141e0742c0110b1600103941c500800303045030382051410b202c84050080c1c1c481200d0050014049000d4507455000407004 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 808598237 1250 808596987 808597019
    0x611031302130c170901061703130608040f03050d0b0901090f110a0903060b15041d1f0e0601120203240d0203070b03130507090203092a19030f080a0801 67
    0xc00c000c0e800020030500c0c800b41817940800c22100010303030310381c0340e2000940b0030b0849500c58a0b2540701040d50b201c1e0007081400c48014000b0350509054900d099922030500c0c1060310702c02010080c001ca9080740e4210395401010b0514002040420150f844140644c0148290103907404031500b000d080010900300501103498041d07103652040d030f4480c1141c07504000350150350b152580060800e6180b02c0281a5480540702038407150151104050b02448030300701402001d040038032920074440f8450403058400c158002124041003189006985580040c0d039075403800401c0610540c000000c00c5400c0f00240c80032355250040220200321170381c50100b40008010070348002501640060780510601031508007450b801143c020700c45411031115034030941000260b601403030410360044144118040184010703248029521a0800e20100c1901480412117540b0405401420032042c00c0d0204201c0c0c46801c00550707000403c1d1046030005280414956004040e980d000400080000c40c00c02c0581c49200 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 808599487 1250 808598237 808598261
    0x60a0903080a0b0a0503010f05090708060105060403060c1e020303010f141e030a0f0f1e03121a06071a09060702060f10050904260f0412061103130213 66
    0x290755980d401c2a400400c0e201a1140c1d010203455400100c1d40d409000380038820400940200e55814291880345c80c040c4141c01032001c0f030308000c0062001d80c440710280c13011280c0180001c0f0360240c1041003550b032400603480d440e0f007010403480220107094002000310304a540c0038040e1010b466503940740b008203902c07040c0b40c564003007210124011070505c510500d0105240084c19620b031120303150b0b50310540054081d01192440fa440401c7e906000360800ca495020403070581440c0340804507039004105400300102d00d15080d5490400d02d40a112000d080711110300050310300ba80e240c0440c1880c80201c00740440f90354401101c0f03400100d6150b800301c3d403d4014070294001b00f0b100c2e02c4003902042c40700c070020310700004503d11100000e0250b6901c0c4038a802640200c607150f8044586040034a441100b803103111800240400010840100c40c508890850b141402e00e1202e0b5845850694064410140358840501000c800d01c0840e450800c0d07110310b15882180c9103107510040b01d902005885681b01c444c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 808600737 1250 808599487 808599497
    0x1f02071a070213151e05010f0305070e0d171305091515091909020d1406030a150f0e1b010c150b0d020901080d120b0607030c03021501031103060a0903 66
    0x10340030003090f049103d915400c0d040b040c5007991030750f0245c0020ba05004603800558003280040110303507000000391468202134581840341e460944000b0304542200786001d402004041103041c00c1c000407094107040c49264841c56a603541404142c18503c80319401900e01c0780c803262011a40725401d041c6c683d016214007509100c04140400310715030702030300b041000c2c0c0e4204912401c05400c41b2100001c00d00034242c0111b0050704c5114400c60308045881a00700e15035203a1b98402885202d542c000340e030180341907210400300c00440306503001201130001426001b6200c1d050225331048548007081c2c40c080250961803059095a08000442d492044880301905120b002d00c10301c1d18280c202e4005030f88080018104c10700300405903000c034030f40e50350984c0300354859040002c80e03801083c1c1c4000c40d080038100d480c20502082c86a1000204a4421518020300740004401c0f00c0d41010b0081c0700c0d514607030421080c2c0700003d681d603080c206d01c52000c80f0303034852190280c0400038507080d402c0c0c440c0d00b07400d070307015550 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 808601987 1250 808600737 808600759
    0x3030e0a030f123206040603050705060d0f02030901140901060e15041e060f1202061902150709170f07032d0812010e04030c08091f02071a0702 63
    0x380c400ca90703c800008803d0381c40d11501c1c001007500300c00401c265138001d900305800300c0b070328104041e0661020303280e43e100b60b051140c200045580001d00f402542c1003244d0342507032202d030455101e00801000039082c46082c00442007000e41d40e07044d0f00c0f158480a8100c44400f05944e40d80d400c46c200d170010302481070b440302d10780049000728400840c1841000e0000d440058604c3c0c00c4030308072100708510428500c503162510024030044c410344185400800c1c81d000c1400b102c0d121a0b00082050140c018030415101c07107850120411403080050861081156940718500c0c206114003e101c8107040c000da1030460550400b000b12079500062480c412071540014090850842e640c00c14a038020205054008409405000d4080d10344250800400d21a45199644844603084061500c205038000400c1e0030302d003010080429041810000c603968001c076031603613660b62800060000000e20b2a03914449104155050410750006184403e480c0c81003008010b000301080c1d140308920551000075040a00014 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 808603237 1250 808601987 808602017
    0xe0a0c0305072111041d070e01030903020601031104090f08040302100507030f0c0302030d0e07030204180b01030f050115060f2c120120041701140c0901090e1303030e0a03 75
    0x1c000f07401c13011503000c00c81c0340c9035880c1a03051649203050400104900c0c03110511509a401004030424001e0a090a026008680c0ca01940b2480d05200140020311030b0005d4002c25512980024600b65101401e038801c2081c030b04080b81550410300089001758210401501194007c005464003140d16a98451511048100840769198a000201c042d4401880714800410960040000e00c4070b0660042550503c0e600410007074031002c181416000300c3c0c40b500780d8040780c1914403280c1980e070410007883c3e00e41d15a2910600400c80020480321001d09203402042a6910950b1007040101c3c1c3e80d5805000300b89000303504908001c01c004903081c0d80021a105442e0b0404c1003500314405090702c000903213141920740c2510f0301b82d1030694200681000003014880b500e007031010358012a1085001f08415202180c4100b545170f000350141c1103240000c01c41c00011382c0b0400f038140203051680c02d2142c003030800414a10f010580307002c084001c0f0741410b82d40814030a002401d031400a0305942d400c000010154 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 808604487 1250 808603237 808603241
    0x40e0f070c1e110603070c1502040803031b0d0504150b150307111e06011d0f0a11070606060908011404120c0c03050f06010e0a0b03120f040e0a0c03050721 68
    0x20b08992075000703e144848a641e644001d1031150502d42c841c806074640a10744102016540c001040c1224814041440078070302c00000d131f960184450741a90000b0300401030604d0b081c000c68044000132420181000100f21541c00400303801040d0010034000450b00d803040103c0d81c15802c50512050000f030000840c4644a1130540d41c0000828094480b00b10840061010010b90400074040c280c0c000030040100180c8018003003548840840c8100b03a90400c45403007540307294050000308002d070b101d0070014019400c1da03080303544080c0e2101701003102c903540300400b402008141c400d516965180c00440300300061341d50110b0748515030240400c0e000062042c3c9c140ca007a80625825259070403e440c2c0800041c03400c0000110084449000b480c0a41c1f50070851402104002c1c084045a0704001f00588940c8000039200080001048000e0301c0740e24079007084d207080c0580d610981c0c50411600601c140c00010380e000c100f10705003070703507040c0038aa6521405480c81c8030040300c1445403149000910440304501e07 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 808605737 1250 808604487 808604543
    0x2040203070c050712120206011d060a0b030a06090c170a020f040b0c010515010f0c060509010b03010f02180a03031202070302070b03090d0305090c18060301060506040e0f070c 77
    0x50400320b0381d0740c0140d01c559103080181e4011110800c00b4440d44001e111401c0a4070343c0d580000d200600c0d5540c10101d001010448016114a8401240021648990f19003401e0006010b092020755240c0c905448451b018003c60b01c90321407004e01e081a0240510702c968480d0a40b130002c9154240c00e134481c441d001000794001e04000244890501c000704500008000a0104110550002c900703070520078446600c02982180c13003414002d14a10420030b15400861040400b038002600140d203503a0301080602403c0c174840d03915459480c0800300c2000c84403941c09480580300340c140c032907840b00c010380030b20807119140d000140110725072380404500f0302a1500200400c40c401c0c8141d41019990b4198000250800d84210080741c00091082c2030b1160b141c0302d00ba0340004108010602a01d4070b50129a602080c411041e003110512400a051074409404c070000911010f0500b81d601c0e5502d1052600e6884195002496500f035180816941d9120b025440020ba4004822044800354801e401c00c0200e14 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 808606987 1250 808605737 808605751
    0x30102211003021f080a020310030f061d101116020d03050408030a110114062805091e07020c181905010801050a140c040e091024060c050a02040203 65
    0x140c03550100058580e1134420140d900e2402402c4071481d1140005011071000410020701d072481403081205842c80141c0032021030390440326220406903541401006000841d0a0b0b01082c0a0543c0140307807540c000611160000c0c0c55a01003000d09025040890f43e88a00c081c0c0d0100680320005000141c540030034840c08036886800d10b2494a90b0728510f1302e00b1a001191503d0101e480100b090080b1082802501941d02e00d00f1030344105032410100080c0d0a296051400c4100045040807414078951910f15502030203000b00010510b140c001e20803100d081c04141c82180303d15846011039031440c000900e20710b2200c07008000d01d600c0300c1200041f07800560000c2c80380f03103100490346080c480b0300715030701c551741c080c1c01e0301c00000c41d007460074500031010b9841414003110510042d038104481c0078188000d4400b5201c0c483c80d451450745030f0054562400110301c41d000c80346480d229001102005840320b50140d0702c00580041d020f240c0d20101554030803c8408050f000d0340182c0204c60040c0b80590007180c2c4669 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 808608237 1250 808606987 808607011
    0x6130b0a061b0c140114120406020906090402030a09020a08061e0403121503060e2805010e12040504060f150e01050d1107050606270a0b040c0c02090603010221 70
    0x198a44a04a41c01580580c0d04111010b21503805540e0191504050050802e1b400b45007452210142c0902003005101400d040c0c0c2c0846c610002c2c0e44e801c0101e0f480b5580082c015034490400442100040030b98107000c0744184038051001030b000c48046111441241c0f810381110001a04809028407070400500443c10049a041d620b40901194824907024904a82d9042a95800c61925030100d50140307109808580c0600d51a0260828a4804014004000348508510011803501c1800340508100c01c1505009444281c400801281c01410445804031010b2280b01d03585e1503c80c510030540d01030524802e044000a8000501a10072500b0412041c03401c1450850a40e580f041201c0381e003000180740000c0029601d00740003080060030303000041100e5504088800000301608024519070041c0d03800c41d0783f40000c1c2901015401300403174040140041c4451030300c9060060004100400407880340c049000441c0d81406c05200b40e80c1d07480700345142c1c80c1100b407a1013546808040d0043c40f15503500 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 808609487 1250 808608237 808608287
    0x60f01050301090f1506052d0714030409050f0412080c0d1503080a2106120b07230307020f0c0906041d030c010605030715090b0a0507061406130b0a06 66
    0x485d5050b180d0080c56565030b01a11883c40861559003080400400d54002c040e410302051090032020031502c0c1250b101d20080a642d00d800d601e1400e50145034003e140051510302009031109246542c148124441c400d2044443d4048a05942101c410b5440042c510030904c00390140e18015884000800703000c00311194600d5590361981d08550141a020f00050b00f03400301d0803080803280581c01280311490360140070f120b0400341c0d04c0c00009001d040c003504088040001c034075081e0081408190340f00700c41d000076024540c6138050944036030090300c034100144a142c01240c00800085900c040b402d000404075501074850303008010184c560040414880d20000c01040000d0800b007005000f0010001e0010590524200415003800038039801200788070340b070003050140154004840c03010f4a00d40101a500d40d0b203901000c903028001d00740014141450400d4020b00480d240449510031501110100d0300a40101c4840701a560b100c00788a030400e07803942007804098050f074450840290b655134081206 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 808610737 1250 808609487 808609511
    0x303020c0d02210c0103060806060f0114041505040f1d15030111030a060f120803072d11010c2f0c0603150a0f060e10030e070806010905060f01050301090f 68
    0x389007030f0200c056580240c0c013411042d40c1601441006000e9800600344500d002c0f0042018880200e082034100100811008680b03100d01d07090310041c0183d0310750480480d049200c040c2007a07102e4040c0181e4800303031540014100940c494114502da85008006800761109000342144100c110407090f455521600c14107240b01000010f0342c0306022a80001c94441e2030201100010881030308035400040d00c00c10100080782e0300008503070304840c142c0b824200c2d0112910320603801000288070541030701078249201300040d6010b0130007905502404000c00180e00d0710881541c1d00030603100105007807004196480e054220300350001008174100d5042d01c071111000800194145c1c000c80d40d10a80c04041c603400d0032281440110742c000380c0000200302d40502e05100002e420006504032681c070030081d16810543c0a8400d4202d018068a803404841080c0c1e2038100e11612504240105080305181c2800600079142400503415280c006031545840c60b400e14031981d01825000d2804003259440350207980b12 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 808611987 1250 808610737 808610779
    0x10090503010c18061b030f1407050604030f1d1c06051008070506090604271a01023007032a1509030e011808030a0c1203060303020c0d02 60
    0x500b046503a403a6002c0040f280380b0090729802c1e800c40f60410004201403400d032150b084c00120440d0301818040110101d4030000c542e200080e0090810180300411120100000011018000d070b00c280c0310007041c4112408100c0d40c1000c05540590a8050501103101c0e6080c00c2d4120741c4150300b0340184030501007c2e920340e0003c0d52400d0311041c0c088900e202c820000d065060081c200036010407290146803a4444000424901990040340222031001c2084001a07904241d54413007034003032200a002200e2a491485210394016591601600412104016102e038003a010b000d8040c401030456180f030f00d00710008810740c016420480500902414040091908038011101e0f041c40c50305003500c20f0064070b490304d041011890035004141c284419000040d8000c10356148401081c030300000300c0c030218a090a800c8001e40c3c440882404002089a011035000480c10592401424050000284a20200c0454949101c060700603041485d108034140780c81d10390521560b000902034952a1004080051 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 808613237 1250 808611987 808612001
    0x90613020c010509250608041e140c040c0903080304110a03050f0601051008040c03080f0f0c0d08010f06020601150302070b0a0507080a0b0604030605071806050d0f1107021009050301 80
    0x4240d0f804141c0c500340440340740800903144c4c00f94010203070303505261546c0600f81c4440508014483c095200c6018007000ea441240e0610a821a460381c12840701e1004031912440c003800b02c070f40140d0905085846003402501c6103400c0b41e0744409810b20750794580d111480348104520055901c40e0740282e000020840401295080001c41d00c00f401c10343d407400e8100f0250b204101010001e0240b60300400010582140440c000c5940014002d41d507082c0c003c40340d41c41b502ca6103429000380800840c0420010000080c03100004038140c0300c1901d20f9880c2c2c00c40d00b8100809205400040c0d11013401402044450031940e1140c05150601504010990381c07000340c20081110000c4100d55035004100a0036480f4502d00d4200c00d000804200021141d004250288103038040580300603103540110b400f07548900e24140c5030409540c0039101564648070000c20560014000803242c41c20001c0b1905000b5041c420f01684c51500030200c1d26114550b401c0c05814504003c456007400115000042c40751802e000d419 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 808614487 1250 808613237 808613251
    0x70f03030e160e060409020f01030b0f2205010512100b0612040501020c070b040807060806060c0601080a12052802010f0c2c010c200a2c0402090613020c0105 69
    0x110748207080c40c41890500703000404c40d80c4030f14108041e00c800341e2030383e0107001c80d020028a004540200410b0209208010341c140d15034210707403081e600200210810351018007030342050304140141d990720780130462469500c00703544040d0341241c0790100344403816070301a000704030703011b400030341840d90740e88044c00100c03411982a03895940014581c9043c803014800100907020800c1014240741c207080c0f210383d848a860240e001401300c0c0c40f000c01c003a5900e0f04c00b03468184038003900322401c45da15040c0c100d44583c030448044031310721440010b05078501d004100359071b5401041619110f13085000203200d20589081c0880c0025550703110a4843e000105020346c1c0010300aa44600a07540d8180413051074498600c1141ca0342803040380313400d44503a07034440301d50060640c104202a0241d810000702031400b00318641400d03801440f22100007162264031300e034a9254054000c09080140515101440d94402220300940c01170160f4002140c41c540f0403501d59415207150001410b0914181d001421507000f42c4400d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 808615737 1250 808614487 808614523
    0x70e2e0302070b10030b1803070206070c0635070309060c020c1002031314190807060e100917071a0910021f0c0e060d2906070f03030e 59
    0x241841110460f050300120800c10414440b895030300c649038a410050810601284800a824a40300b810400c0c0c0f81602d4005182650f600500e1400c8200e240c030a1040c000403909009400b0703520f808001c46921a01d0713010a00c0620145c50110741c0e050709c0802440c0c1801e042d541c48461010412510030301240e00c882da0000e042181084042042c807184d094074400c1154401c0003403182582c80c2d00c414104079029151f501050a402400080b0040c5c0d010078500364000900350b0000e00c860340040c4c010102c940680b1510300300c14095050019060740e9590b004c001c1120f20034100300003a044100d40720718040307107426a507507946c41c2c403a546a2450184c0c2000c09481e0040f509442d1840e100704543c8090f0323072b240020b0070a409030141c508840c0011004006034240d80d4090130004ca800b941303000402800061810b03030360700e80690040e0700070051640110308511158044a0188030800340c41c075084e050080c10301c1d00b403018640d20340d282040c1400d001ca0405445500d1702164000800c8000c0d0b02c0d401c44150 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 808616987 1250 808615737 808615747
    0x90e1305060117075604210606120b09010509030301030308070507030203130b1908070504030f0c0308030115030f0c21060b040b070308010905070e2e0302 68
    0x4801d2030300c1c0040e04080552030864504042c400b100080000444c0d8503842243c551001910724441c814108444441e0328070b0030018102d02e25445801c505515080c403159041c820000f155210718180114018907900b0a003030460046082d01601c44290614800c4002084160707e503c42d00f040d100c04030a00315200600307103050111000c000e010f19540a80e810b0000c6095600d0754a004200c4c0601404000500900040d0641414800d1044901c43c01c0040c0b6500003060fa40c981c102c6c0326038000c40314452407110805d900000d1a22402001d4018081b9036180ca04007030568490a1079070140f08001c41e0071481c51100000091208405140203009a00380600d410021560240075075a40008e100c0d1000d1500070303002405a0404a00101340c100c48141004030a88400240004d02c00c5400070029000040340001da0390b001c01b401444403e02c00c1e522241d8030303682d60b4050400d40704152081c0001c900390014043c540d007010207802c0313100300004250b090407900001134401c44640942c0c2290003c2d8000170 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 808618237 1250 808616987 808616993
    0xa06050301150e150d171201260703050607110102070b0405160e010b040636080d020127050a290105180c03060a0b04090f0b010503010602030f0901090e13 68
    0x2414684c008030711114000c0680480f07000032074220004c60000e20b613244101d12624211840c0040d5682c030040c41407900c116584a401035214155003411388402915040704900c1e1610340840c21038103d0b54000003c01c882c2d15100c2054580301030b1100c1003001507500788045000b00703183c251098021030003040581104078028809444a1565400c0444082c1001e00100940c8118008580883c0c4040c64598014610912004098075214081e00060f10041d0400701c407030300036070114101303d0314005d08488215007810416030907a4032100003850380a95490040301169288200c5140c09485901603a20102c81603603001c50b071018155561040080d17803045200c4d551001c11070540508800c032a40708581035940c11500c540c0c1d2004002c002824800b1004c501a5200c002a48000d132070f541000700d03100c075101c049040081003020182a4050b041642d000120350190040360b041c1e4406038060340c4ac0c5069405c11800c55480b4052490400c11110340c00180c1d5112004e00c6400384000c084020890b2a00d41 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 808619487 1250 808618237 808618259
    0xf0b0a090c090b0d0b07121a0f0d120305130203010c0206090105060f150f0705030f130e131103120c01021c0608062d090a020f10090e0c0f0a0f0f0503060d0b0a0605030115 75
    0x149e85d030040b000c0c2206003011030a5200c2c141c1110065141c0030400b40d4415050b007020000108000f5010b600f040a03807220690003050076440b981d02d1000800c00340d83d40780c0400840800950748240c01102c0c0940d000070518101c00140007400d80c141c4000c1c60214140c0d00d003403031f503446006000c001141c00309107403503101010703051b11000f0103003529828600c0c1440c00701d402286460041c000c6c82419011352580b019141840b551149541042c006901e03901d8400466000c0d5001c0e860200316403074000840341141a145c4220400e581c08080101340c9a9070700182c12102c807600070700850303203c0d440b604103e40c1002c1c480e584601c0748580034017510b03407040e491050056442a034a4801d114815119440d0030942d0305c07480d00811142c41c3e0800214075203035a900f201c260700c64404522403003400012440030840d0040c50b260003115072542c0341c005420708102c08407428002aa4429444900c090481c1e0100303204400d516003042d44900002034855031000001d00f12920741d42480c0e8030b060b142604102c0403a00b4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 808620737 1250 808619487 808619509
    0x1b031603090801020a0e0409051e0705042403120215010b0703030e0601061407020609100314090f03070305071a01150e030f10090f0b0a090c090b0d0b07121a 69
    0x2d0025400d14040040c09000f01d0303281040346010350703590007440082c440c0801c0140829008886131008070840b01420644500355070045501582c01d140c00d0b201d505c1180801030a0030700c1c04541c1122981d08503503a9084c1403000400207401c41c419a812034400c810503c40c0203000380352100f422644c41501c0d10b03001e41642c0e000a00c2001580007000100f104035008001c0b0501035140c1070440d5a10091031000441c03034040e10704103a401005011503d00595055445650304400320f402c0442035640c3d40418941d54415800145c045810a03c15200000d0082d00a0309503503204075803241550350019842c028404099200605e07040b042ca4002c801c803600103103d00c080c03510a4002c0d04000c4103001c3c426507654001150410031542d5940c83d1018000308454650070503520108900c4c2c1800d14880c00360180071800003c0d200e1002e01000041c00701a01c0c8218004070070060708d5580c0784403607600d400140000092492007400101000e0f646016058490712a6500307400400c0101d060b245000d2089021075 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 808621987 1250 808620737 808620749
    0x60c060b06120705090a0b040e01030606050603090304031b0e07030906050a0c020303040b0a06170703031427040608030a050c0f070501050708090d020d1103150c0406051b03160309 79
    0x4208240441c480410b0b040070b5000c1001c0c10103d80d030340a500701080809142d54482101c140c008240030038805101c0720514102c03405043c1c00d000c840e490f0802c00c58148401d8510100c40e5000b0031040000030590a031411050020a45040c82c580d91428800b940007011a400c60000783d80c2c0d1688020007072248100c50b0403600d2024100015468900b01070365074840900050000b0322420f0005640c204560070039806041580010407400c0101001141d0f2003920f0701040b40881c4031100e042e003036550000c00380d803640b0903501550213401307044111781d41d00461114406504113844030b00c045100d441c1040140b24084403547c9807590f5404440c0804c1c00c21641484040954203c03400820040c3e0344442030b00c0c41943c01481d110f50758210400028100860420025000b40c6a0304400052140480b03004003900350a505131910807000c01017003000c074030088a00700059101031201303100240c8654050610508005c3d03102181f1309201180d9403454000e509a5900700e03490f00c2c012010135034850300e824002c01c8 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 808623237 1250 808621987 808621999
    0xb071107050109140301020d1401030507140607030507050f0303070c0c05040b0102030901110a12050a0f09081207170705030304030f03021303020d1515090c110c062101060c060b 78
    0x1c1031000080c2102c1240c0f00e0a10307544210031901455940030b50446004895000d010003002d141c0e4a01264254400d200031380c0c0c603018509000400000c090f00012403080001c0c58a460a0095502618180c201c84001d0381e03a0f200c0c800f00d4030500c000400080d401550280c0350150f500b0b40c249014500381c001900518025410040108039698000080e01c80781402403c0c003040543c04424141d15180d804000a001e181c4006000340440d60880001c0c54224003543d250003502c8200c14064420400611461101764040e011a11102c00440058601c041c4598401466002d00280c07031001c13500086815203243e00008140700805401c2204c05550080c6400e055041055151840103520302500c4040c1c010382801c01d6013010402c644c580c158010380003135003c014243c14290f179008010851b001340c101040ca404481500140560007c140b844c40b4140100241076503103081c00b815030040c5500c0e620f22070810070190725001d2a0081180a00307141d586040321512a400c0900944012a0403240158 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 808624487 1250 808623237 808623239
    0x130302241603021c021e040e10080a0f030315051201021201150806150f0d0903030b03161406040536010308030f0601020f0f071503110322020406030b071107 69
    0x40b0140070091256100c00c0c0162a07032007206c07443d101d55084600b1000744503800100030541d1040c0d1443c290244401840001c41ca0340c46807a42681c1e00c0101001600920504445a00180c402d030015217440403001d40600380c1035619400702e242e07210100c4000c14980d4002c640c0800d00712071000c1071401403140706041d2030b181c82480e9001e080500068822405480c940b00344003013001e8040c08903902c20380d402d032442d42d41c3d070540e54110000300a1600201c0c0000d0419040300c01502d00000c1022000800c0707018040700c940f0301100c0700300b00d0b000004840e030400c10500c400038241e0380703800500825036100c05100c5000301c924101540b11b0b6020b0690020319800764001800443c28034402d6941c04003030b178200400c258841200503440c168021000303e01c0c510031803010038122100030800340100c8541c2402201160902c41d0150b0030750f40c1801c00b4002998040c00001d48040d080c86640c5256448040c3c04100d09150350007050507124036400585621a4501c04d00020550041c110703500c074040240900011 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 808625737 1250 808624487 808624507
    0x270a0804150509130f023a0b01050f0d18080706050907120f050a080f1b030c0312040f060504060e0c121002090a080102190f0503090613030224160302 66
    0x100d0290b101e04042240d6402d01c0b03201c452681c0c0d0465201410750740700d05515541e20640070500194034a0302030b040280b481391403c0454208d0180d0885280c05071201402d0180705c450f0103401d42c00c50840600c882c0c0c0c41c2c40e07030b40c0c0c00e812038400703029a19402540403d070746214a040030001e40f04050007107510b40c0e001c95420070401c0d0100504041c880d900c50b44096000090f8184546028a00c107000352007448001549400d0f00701d02d10042c811249000500d02035030700c0303801c0456128003408102101c0b41d00200002c1d03846501e00041c942d8003030320404032200c403190303a0348a00782120000c54084845075600e56030a21000c030b082000c842c1c5100c003200e00190300780c0803034006503c510aa14810091075004104408139035916422900030701b02401c021900c4049203001c0c500b56044441102d40072800300311810541e00d20420072240700b000000c1c010452612002106415100c0104040c0c046001e681550040404103940450080350882070704040c0782002003c0c1304105620003140c03c20b0500c10050103480b = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 808626987 1250 808625737 808625749
    0x1515031b0102060628170106060302070206030105100527010e0f10051e07060902100908030901050f0d1a0a0807060212091908060703060b0301030308270a0804150509 73
    0x8411810355031919091008428200724400f4000d105007030b580c0c2c0131700109140c0040b5031a08040702d07080c4024007074140c0e2901c0c103800703d11074404042c0d0050402c100611150070320f001300e5002403c003840d041e80790007018200c1c2c110155521950b5511031400d400000e4a41d80d010860008196003143c3c0303200707108034000021b0503003105a08100280213011030000907505a4022a8001c0e44446d1680c0c1c4d07585442d07150160013004a490200e11400740c011060400921440e44071080d609188011807404443d03500554668000a5031008003500811041010480c14011540484070546002140020403400c200c06214503811003010707540002c400700003042d0b00082202c103c1e80120369a695a00b601d03c00f080901c0c204000c065900302d0741c09000540d00c6000140a845140d00da81d08000c0184c560403ca60b8030300c0b0038400500001e80b400b001c40c1c2405c1300e05c012031401c8031101c0e01d401c409040c102c41c07042c20640c0524080da1040d40c0445c0c10010031b001c07043d00c0340e1002840d24015203032051400019030 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 808628237 1250 808626987 808626991
    0x10c06050403110a032a05030414030106240e01020c0109091a0306010f06030e07050d030509010e1c0b09011416020708070909030e01080c18031515031b010206 70
    0x125120800305040c1806070100b81031100c5000255844010f030f90070040c100080f040000c2214031404640902c801b091181240055076000b405185028606850b910300b080701002c1c070940c1b6540c3d50304001204001c45070140c0f4082c41040350100310a4120802174050600c60301c50a044d90005031203000242e80c0b18a0180035200303084000118010300110389400c3c150305807074694252240800108840402007152801ca82c0d2540e4203001311011441c40a03214580d030301c00c26804c940400c01000000340510040c200710078040c5404e00c01d0000b1140042c2c1c02d09011404858107620388a5498140034029420950055281000380000e0922220203481800010300001500000c0208541c0b0548240321400040000304101c0e079807562210941401092406412408103600300090f504950148440a00c50004036800e60f0801d440d0202c040e214010303c60045606008500384406000801301c0c0881c0201d51191444601c03046110900d440d060841c059170b030400780c0044904400baa07001886907 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 808629487 1250 808628237 808628243
    0x1406010f0918060801050f180304060927110406021014160c082106180703020c030f0f0426030d0b0402070f03020c10032702061306050c060106030b010c 67
    0x11402d07000c111032000007041560040384165080c81c01703005140310115103941c000d02c0040210002006480d01080d40e074032407845000c0114211407410481454000c07103440010744844400d2204190b07040d802000c8070740e02032000d0358082c0041018480903030f0403c0005095480c0c2ca1040215601c0c1c0c1d0070a500c9104020000c80e540d030010060200714912407600c0200c0c290344080d01c15151040c0c1d008843d00000c11300080204000c3da00000ba00c41d152904405c078002c042e100f9104e10301c0d1a1808114041d510019000e0f16504c010402d030a61806010018120082400c41a5485c1c1c0d050103000c00c0c40745142a40300600000610006026150220071220040905903001600020301d001040217401440c0b00034241c3c60502d4201c038145500441e25492001c421150304817000e02001d0306030304566500495544103619a195001032901e95100e520065000030034040c24142c800f10585a80c1100d0f4020100140b0041144031030325008000e2030b8007420442c1014006d180025000070081200c0c01d5002e = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 808630737 1250 808629487 808629509
    0x1060f060e0d03180306020306040c031a01180b0d0209031002040f2108030106021c02010c0e01050304080d0513060c0804110d210e030615010915120606031406010f09 73
    0x200070036002d8000c440704d03c903d07034404191895031782c2801e900a40003121001c1c090781c04c000c050003504d482403154519107191000d100008c0314030a8011648004000e070804803d50f04510f000c11443c0451001d4819125441805691603000d030050508111846503541040d40c0181b1080c04400700d4402c580d0140c880c00d42d0900d0080342d038190700480c10540540050800000000040345940d4080780c001c050074038001070800d1440030445d04a0032a9000500080002c2c03100f21869510361082c0011500a401480701e2420640400b81c1002103590035955000301c0c1103000542002c0041c42c1c040d05c02062504c0c1000c5000345410780b90289003050307404d64140300b40710040f007a2080120003125000340760309803030201c101820a900b01602034800b22400c00e200307100d0140001e00c03814102800034084181a544c00e512285002c001c0c400380900d10346102d01380f02c0d4803180755400d034011b8030a060007062255000f01e4000d080b004544180d110150010f410003480842210b80d10340c01005c1c1c80100c410000c85 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 808631987 1250 808630737 808630759
    0x30405211207080a022103010911091207030308070f02030409020f21070306080a050304060503180a1a0f0f040311030c01090605060f031b0603041e0507030501060f060e 74
    0x1240741441200950303401000400305040d41031003c42d002a03c0ca0548540885124175810300311034100450b0213425031008081000180544030041c1c0280e080121b2100740ca608140042001840c9009100f0030006280c0c0417207010820306038409003080c0c0068260a1169104068210094983c452800703500070403500012500c0d10f147c5240c04407507001035040038030580380685034461025070b01c003a05c140c0c002a0500002007403401020034003a00c00c40c1d02400541c985803030514141c4e2550002001d2810b0000e40050382d50302d201c03040c07002901d524800c0c0e44580d441c84e505800142e034a440640200c00240280f010480040c1c00040c2107500035825081048010248400c014514461405120303060750900c0124804c00c501c9803c454020b0030b00f142c0260386081503005141d038444400f5440358840c5c000c010034030302c076040840083d900140901e0042c1c13540460941e901d5808901c0380d40459082e4084070041061280c00c1c410200582043c20711030340c800b0700c1c001c0300400e46415903036954496450208 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 808633093 1106 808631987 808632049
    0xa05040f0e0d110304121a0901093804170408032d030f04020a03080408030316020601120222061206050916031101020a15020c010e030405 61
    0x4000e42c241741c5040441a179851144030305845d2800c004005600101e075210b00903104660880001c184260540f400c1182852540e80b4415240f241040c1c42d0624040c0300b12441501250003030030105d03034139542802c00b1010303103c1100d031100c00b01c0003600148020010014008140380c0c12070341010214203004211000c40f03042c000110724807007000000e07208504905065000341c00640840f49050b2a60794403030300c940c0326400600c00390f8804004c002e80f0700e07401c40000b541c0400c0351004d04807551401c08200302e10441054028030806120041551480c1d01002d014900c50356a030091101940d6442c3c59100030191040580381c0604110014480d103038005410411f41d11404819002e10b807071515000441c2c440d0076201070460203081e80c001c020412020303490720348041c10040103a41c0c00c0c04806150848064444e8070302182c1040c002004160340b044401c400c50020300100921a41a00c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 808453237 808633093 := by
  have h0 := BRFrame.cov_init 808453237
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808453237 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 808453237 ≤ n) (h2 : n < 808633093) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
