-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1127
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:21:17.673051+00:00
-- url     : https://prove2.me/submissions/67de4a1d-9d24-4127-8685-700b41525988

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 202517985 ≤ n < 202697841 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 202519235 1250 202517985 202517989
    0xf14030a05071b12030e0307050d02031c11030304141005090309040b0402130b03060405071e0c030c02090108010e010506030309131a040e39130e12071403070302032205 74
    0x801c40521711a0b00d42e81e1152441c1c00406080c000c041c7c10540c02920180f00c944003503074000034028461620b801d02031609100c0628100c80c0450081c510109a11001052104104161a00149000140c0107454821f031450303004506440c4203039101e5465501c107111020151809a002c08425040144018a803a4006104000251240c0d103d07036140540841048510705090054551020f0b56103850b45440743d4994030b03c10003180580ca02000c020f01018010704060107810809034060b0014041d014660b034901b200b42c0a07085182a1103880d508160104400e41030000564038050070050980a4000000744c5070401000004200403101203d8403200e0141d0310385202d00714800e00d89101519a85040c46502a4a50070b54040c060380352801c04155183d60500c60320020300800c00f11142c1c410002d009141c14003908111501b80000e008612858800c0c035040ba0040c01540e11800405080c07540407041c0f55281c0c0140307074001d00585c00c20010101540c0c809544bc010070040c42c0c60440300d031511440 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 202520485 1250 202519235 202519259
    0xc0207080d050406141608030705040506031303030b0909060a0b0f130203100b090a1202040e01060e01050a1a030c250614060907020a030809190f14030a05071b 70
    0x400c002280000405000c0c542c0d0000e07441d2021003c5c90070032882c00003010692144291140c80241002d4000301c0425204d40c0f0610495006010042803d5100e091403031540f01400e02d4102e0803804203141c0705c1810034908040e40341c07a00c01d111082c041c00070b60356078a4000300039118035224554040290a44020700d655014042c00043c2e114030b40050b1070b80362070100f01c0c0401c141da8018070441e40007808499201d641f09614a42603c4030481611403005851021a0182c101d124810b003003075084c40300c04107290000740740740c2d41210340840d2060300c00d40e518050081584018850b04100360780800c00180c400313510000074455000b503084190b008030103c4d5080c034280b6400c5081150704948466041c100c1085d40840650864400ca60720401810000000707541c6081c01400102400024070000d00070560601c00b419858104080e2018680000d10740b0f030a50001c0d0030001c560300d983c0b188280300205000004d4072400034003521003504c0c0c08100d0312003001d6590034a168040080041740003080e0031036080 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 202521735 1250 202520485 202520503
    0x6040513050f0601061815030f090b0a050601200606100203040b0a09060e040b0108040f021c05030403140105010f03030c0503040b041212030b010207060e04062c0906070509040c020708 81
    0x60203442c0da541007000c001c01d4142d1b020707941c1d0542007544400340441c40c0007034860b08801d0810b003000111784a44000746809004d00403009081c0c145101e00b005541440346d04201c0c800c80003661016007400d041b1550351020f25041012000c0d80d84558001403003820130179460b90b5000001c0c011207080c03c0d50b807100340c841644944146400228481d50800c03000f41c0000030014900c8081710f05007d641080d000081404000030005440c85415007407134000c0d5100c000040440c0c201c24180c0030721080460a0107541c2e54000e10013102c1070421020050300117501031141a041e100c880100340c001c2459910210303184800c442d002e1700c4501081000043e1401d19400030001003410255506c440803e83c2803c0a504000165010905041c000500da030b981e400300301d07007041e1350107814100c0300c1786003000c003040003061590080c0300d40d81084121040034401900d9000120350b030a0490310515980d515401d034440131b05032100004264140b100342c200d0b01c0d198024101030301007031044411096660081524102d401 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 202522985 1250 202521735 202521763
    0xe04050d09060e2206091b02190503040303080c0903071403101509090c120b0615040e0c180306071e02010204231302030a021902010902090604051305 66
    0xd00c0030144032504590250018040703410054550901d8001086850042400300940d002d000d80d458000e180a9078404409040314400400910071740080c9029031165001c082d0016100b104003000100044200c60515154414040c600b0a0b1956500390f40040e000341c00100344000c14008070000f03031070422282004291142200172506003510a05007404c601003000202d160400c0f417003011031201049200200c03494108002119116030078000c0b07600859410452051510300d68803020b126840a000d4001c42d41140c0c80e1046038811011401284601e124100c080700906001400d0740c40e0b001b010b07044000c40352403118081e0300103000180c140740c000c481c1c8030081680d410075940d00122140c45e4505040460000f1403405040011351640c200da11120754841d049038122038010354a40ba103c0f05100401c142c019500ea05210b9100c0c070194028a5000d2824809690824062441405400015500580f40380f1040c3c0b540b000707020107800000c200704105849400c1c0440028003c000c0101c00c6142 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 202524235 1250 202522985 202522993
    0x1b150c06062701170a0b040605010501030b0d050a03030c2601081902030c090705281404050108060906031f0f0b040608030d09051603060b0301050c0f220e0405 70
    0x1040c20000c041d1003200c90411402c1d07031800b800e8002c0410321202c41c103551550b504a00a40c40002c0500c2c030b01107041c20010020580c400c10310040298030781056040e1002600c040c06191984070a0092071548407202030031980c40081c100011070301a82c031807002c41403580343c4001c00e00079258a1500d5142407035029035110741031074010410500140044075000b0140344040440300500d03000203955503030101c100f5100b403100d84e010818842c0a03d0462f081540c503c0c5194000d541c40515101c410b4109181030300201d2a6001502180d0850f0030407a13050b0342050311802c0c02a1035050912850441c020103140e0180300303a5946c001840d40a6030345035542641d5000200e8041104070001050f01c5400658600450426900707001d04107010040e81c51505800c107001807501814149649080d0305403820080074500c100c0b02006014080e0025901a40b00703600a1190703841d2104070201b20f1040e0201e880c000201400f0ba5001002c8450302c0d5003814042c0321000720002e031075404144440c242501d0856103584 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 202525485 1250 202524235 202524241
    0x2060f09010315081f09021c120c081204051f0b040e0706140a23040e070e031c0e1306030b0901050112120c1209060201060509091b150c06 61
    0x2034036014124550f002030301c1d01d1043e00d01e4142c4255039003da000740654075040e50f804005100c01c050780301030350050300100f4840b0681e00c20450026006100d500585003148089a0304261601030802541e40360703800044c240c0b5181180c156180a81c20190080320f02d030141003603c4d081ca9032450190195460860000524581424104000c845400358400459000001c04210042e008a414008902040c44244daa04030341c0d070040780c1c00d100920b07000c0c03540a0003122401d550607080c0007a005403000500444d0407038480c3e02c4103840a0000100e00795143d1b010000d049055a078100d1100d02c00c00b014100030b0240707001c00d0b00180c00d00c4110240040060303941c2000700148a580424903801c080003200030070607941010700d00c44007005c81d514040c01e0403003000500d0950520840e6600d4216401400440200200c58070007019211544500c1c001582410408a011320703080342a01d01074481c9000405049800e0503003901800100d06c0d905d41d1051511250105032810607005100603407280c001f03884603103 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 202526735 1250 202525485 202525487
    0x9030d080a0c09030803010306020f0f0d05040b06041b0f0203040807090506030d0801060905040527161d0a0908090303030405030903070f0302010c11031e01091406060d0605070c02060f0901 83
    0xe00074030109003c01c0380100d070800100f01244200c07070540e41c105201503034600e18180001083d00c1005400155010005001c140216195000d2030185110300c0340f40c4d14507182d000400c0241c0396004180c90394070a2a01c02c0d82030312801a40001807008080c01a241010765444416080c44580c0d4004d00381240c854041160519041c03001820103005410710301d0995040c4000289445d07881c0c050a03010b9a0780710b02044006000242c100098414aa020200b000d012010b094442d4858015050546d1842c0ca0105020b04541908813101e1440140300d205552500d4150014007043c0005603100e01c400c10070480e041d28244001c2d0303c500e000c0c8006558584840c0181458100180d1061181c82010101400140e03403003c00400c6541e081898a41c10741c1c106000a4145a04018401010f40d6044444100240103400009055004109070100f80300c074102469102c00086030381c0e96120703a50703680500c00a4845d0f4041034000d800380c54001089021540814015440080c0741f142c5000041620301c055 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 202527985 1250 202526735 202526741
    0x30e030c010605240a0509040207120e0a14010210050a0b0a0b03090709050114010c060b10090503060105030f0a14120403060e010e0d12020708091503060117100501080c09030d080a 79
    0x201da01c4c200030641e02501c846211154050f5015582c104280001c01521540c0c498041d200d16a81040340f080d544204624050a089800d00c81103000d00c09800b400106030400e030032041219281a000b80c10702100c4000904014080106801c045603a80d510510440c0c0f0307210b004502500c2408010395a9060600105107405610307800707202000d04050050004202c000403450550000f0300b0000700f0080640381c5030029088101c011030708036a000a1140c0c4c0940c4c40303400d19044032000c0e400e549403645c0398414503031106400408480b540d0b0196100340e00181c00d4101c0325000c0001c00701500c2552100060400c1103030b010782e106580040d02e0756020203000c10288184c856000810000700b08140c1c3e901c001601d8900683c884a0049901103210020301c000c01d012100c4200300241000d03c41650714031207141c240c206803295400507000750340180480124100c418040ca60280d80b404055180000444070400e0080c0b411040003000c0c0441c0449440070441484548080e4440c8505443c1c0002d1203022 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 202529235 1250 202527985 202528009
    0x50304030215150f060d050705030712020c060c070503070b070c0c05010c1101050f040905011d10060909090201050d0e010501031b06080115021903020a1104061d040201030e030c010605 81
    0x60b4510220070f00003080804032003886046000e803411440483e000c03000804600800004841c9141000100141c080e84400250300c2400305440703a92080300e4030f56680c1c040f8000c282d08048190b02150204440500c504046e01002e8800c004807880c3c03600c190f40b09414400305465180103d403a2180c0c0204011510b203040c40130b0602868082d00c5c90013103894000d0034001003447c4a0500200143c19281c6480b1602210b01a00302c21405004e156074039402c0c00310542c4900100c01d8460300080100751180d4a00611508445040e9a00c0e03411a05240311400100a40103040f41031000812030b55400c0c6a203400b505d2400d0303402c0d4000040d550702d9800e103c50048001c045201040c540a0020310117207800c030340780c141034541032001402e582e1005041645000020010043c41c032807010001c0c02015030002d40407042600c00c0d61050410b41c82101404113a404034046d02c01d034510710200c802031000400304000c0c0e0090052402240b003000351482c00e400c550008410604036511594141300604105203c200 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 202530485 1250 202529235 202529263
    0x5150a030609020c0303161101060b09040f0b06071b0332010c12020903070e1311030106050f0d020103090602180a051206010509100f17011802030616120c0503040302 73
    0x813801219406864881c84020107604141e540070b004084038038400d0b0065450122554000c004180d10b60110058580041001e1072007142081c2c030000c9280c0d814000c280f0121805012141040229900e41d42d0348409038001c4241d40083c2c4000102040014400c1d500d8110360000c1c4603800101610419003642544100c5a0706a040c860b4003612030707501002da68142d00c8140390050721041008006801c4c01401c3d4003450a1521000521008001107001c0014403172042c800701c1c04d00300c0d050b02414261000c4e44907481d80003074450a00c141c10b040c4203c80c1c1d1407440c4149400110843c403580d0f120201d8004003070950b0280c0712002c0040e0b403400c1c00c0c048040507003400c543c2d860149001c500c070150b84030014014180218a5500030640c56002040400c0140c0389160a0321241034660006078942d0002c00d08081c055802c140102003a00300b0315000d0001950043c0150030b1698400c9280804504039821440800c00b0a0700c1a0716519058410300711140c2180c0d9a80d40d03603061a080092500b020054295 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 202531735 1250 202530485 202530487
    0xf0105060303091203070210180e16050c1912022103040f080c01020a05030f01150f1103040503030c0703030327060507030e010c020d1101150e040c05150a03060902 72
    0x1045a07503001095400100c400c070342c514014070310b0030111429405001e03030080d00240300c41e03241c500c000d4004403001d4541000c46000b80c6116640d81800e01c50b00003d481c241d1044a02c0c00c4000001ca10500080641e038200d2070451341500150030b218031984003108425240e04501d0b03180d854200c3c0d030621860000c0140c1122620007000c0707a040384e148a10010b400100030550005c3c0b030508002c2920151112040040001c5403a4000900054075039403048802c030450f0001540041107240e9150030141300e690803030307564000101c40030342d0917117140b0404000280301d0301c8240800500d07a1303001c000a24903000e522018100e01840c619002c2d041c1e88400c44071044503081c01500050304e1001d00303103002041d5008540840c03107454101c000c0e40245060800c4210075400d0640d6041020340000e01d01c0c0d1080801c0d5a4982c00032918000d02d401c9603900c141c01030407540f14074820844111190001a005806074440032520343e902d4002488051140b032031403000d5900170030490392454151103640300900c0f942d8419 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 202532985 1250 202531735 202531741
    0x250b0601090f0f050d030309080706050a0506040204061715060d0603060b090603100c030902040603080307080c0f0d0e0f0a052506080402040f0b03160801050a0902210f150106020f0105 81
    0x1048180c943c9016943c011011150848285407080d001941c800e87c002c006141d5482081c10704201621084601c00412400d00e0085512802c081c0700b01c1e0102d51f026070728a1042401d41800041600d006400d800ca2007801ca5044100d40d95414000c00f01d24071030f20400074105245190104c162690240114807450300e1508000c0c0c00d440104000014000a100020700f60309880803e5000708120880a034005107400004020481c00600840c017980e40c036114860a03641e103a0616005100d030203800055564140300400b220515904a01581c3c2c200320113440141244e0301c4030600d4200321074410350392a413102000c807000106107a44045d080400c0f00305110340030306180c8085c114031005400240100c0c1d442980401100c001d07881803d000c4e80050556401c80c031141219040341c1418026a9065480d040108100d40058030803100303580c1d0301900240c0b000800c95009010000440550f1002d0702482541e40d112003001c1c002c00c21124600044031210394144800245001e03600c106a10b0075030b24240034 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 202534235 1250 202532985 202532999
    0x203060f0c0406050a0504150306240905040b0f0d060212130f0308190c0306050a060c12030c050f0c1506090f06060d0e120301030b0f0f0408250b0601090f 68
    0x11207054901d04d0600c15690407480808680e544540d81c088000040c2d0920b445242940c941c00000c01c652482c000e0038100da4080c581040034501d401a20000319001c0c850420043c1003a070011244444000d1624480c24060408902d1b00b001415003201d00f17550008406078582c0400741016044801c0150212108403195545041c10b1814900a000d0041c1c0d8800200c1c214080c019460076111100340900201e014031130f0150142c8143d004942c42000013440200d1540e106003011506a40c000c0061002c112074a0b82c00e50040030903507014002c0150030000300400024000060411100c084010a40c55000805041c608034014201c50301c101041c00600c610303d045581110b400c644125196a600c0aa51900b50010018600d0184a40c021303803544580c0c2514500145040700d01070580071a1580d0307031401c0d11095545c2107801040e000d072014041008a00030710b001e44580c06042c040c001d07401c0002d00ca441441e801ca0b4804a40b0620381004201c00f41d41e0060512008085494814407000d0511003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 202535485 1250 202534235 202534237
    0x2041d0117151306180f0b0106020f0a1403072001080105040c080a1d0d09091a0108041704050d06020c010e0706091e0b03090a05010e03340c080a0203060f0c 69
    0x100342120300001030340c0e180500403242e1240011441c030001043c03c485062426a03541003001b081a60314031010000003034000c1c00402c00d00764910701040078200b968429620080b15030000e041802d0644030501c150000102c0d41080301425203540c2035440c003501c0a9800041c9617080c1600440c3c0104e0400c42606229504142403c1c2c1007015604080350011224501402541080203611103d21079491070030a555040351000e020399582c540b09000040703803c00c1c00c40102c010030b000c080c0010000c00c00240031607506d5032502840034800b00c0315441e296965000035482500c205040e1380c243c1d80000c2001c4800d60034030a80404804500241540b180b408402821407503062084400c1c0c0000711101c5903a98103158158405041e1404040d074880c100b00361610b03504c001d0100704882c15840c10748000800d441c00020fa0b00b8030b221080c100a00001e00c0c40b140344480000d000f06403800481030b203440b4000344401907060050032400c002444185514010903150020243c810300d12260034605010450764504 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 202536735 1250 202535485 202535491
    0xc080c06071502031e15011d0a03031209020d0803091e1209040207020406080c01020f0609060a09030c120f03060f030b0606030702030c150609070f0206041502041d011715 75
    0x1d000584a588103031135405c0c4114125217134000e003810030041149990316804503809140c2c0c03c2ea9010342d1307058011101001c0c2c5121102059202c150040104006482441c0300f008007420380c800418982416800300e4074604003d181111034a03001300800c016044200807964040e2540021605034a800036101915581c24183d01c0d40b00a50000b9501950f1b07c443c2c044500056016100700040396a46c544d064882030300400c2c0034018001e140e540300fa201800903030300f400f0b0b04409000e401540c4682662500804402d00100c0030301441ca645100420f0054685024030000d0341c51300b07050f02e051440001c080b10503541000c1501e41e00300e0000e1000c103d41d0f45080b6841380b029245540d0360b469001c1d080e4518020b560145035a4410751051001c0c8802d500d2403d402298180d81c0315086071074000c000ea81f02010703103480c540103a20001c00140070650b00b494012000603080d02c014034040c2c40b041c5082820229000e400032125803034004102920480e48000700700b2603048058640a1802c11031802c006c0006 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 202537985 1250 202536735 202536773
    0x30c03171908060f1509010912110405150d0b0609060414011203091205070816030228090608010b10090308072402030906250e01080c0c030301030c080c0607 69
    0xb501c00140180c643e07004c503600c0001c00401c041210840b80c206a0402d81c02090203500007180c9000000351101d07007621a0408917408400103021006030014440140b07002040300c200d5882044401c9550313112910fa0011441c001c42c841d503c0d610300b10040c000d0800010300b500d0700903407030050015100f00301c011747d071415107010380d041e044c19501d1424200c0d030f903118540003075024034080c0884008015001035114111802c15050320352141440400c1071302c10342c103880042d4109900741d00000d032800ca20446652306803d45070308030803102c0d110303c088022201c0320380010050341e5441019400342e1402c50b400d0344c5008140d291481e41c10341156a9041d0901070010700403c10718030405003500202c24000d0703511510080e00d0045440f0b141903042d1030707079541c1c05540b5501c00c5c03000c1500781400e40b02048141c003401021307516000368100c00c210044075510f80041c92174000715018045c0e06c100c010140010b500940c0a8000136561030b040c58000d508140704440b5403449001d08000712400280c0c0603844811000301c0d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 202539235 1250 202537985 202537997
    0x5060f030304060210020f070206130f09050610030c110f01140f090d12020706050a090b0f09060c0f0412050d080106020d1209081e180603190506030f0304030c031719 73
    0x70081f0208114010751000a41c0308001181d2202001e0740c60500b007085905441c1c14004240d13a80c2da4200440700c003076078090303008200816805445030080c1c101170816480340c0307007540009103002001070400d00490b4489a06946036611a54850111001a80c000000c00450411343c1081610503540781c0c5507441800510030025228400d5607859270541d100590824014030651504122400c01030181c1081164503909502c08181418000d410300c5204503000801444941c4910f101c08000e600403852103401031604010101d552078940590207082c1344200010050f500101001600da010140c012504552000c00341005056110401120303003220254000307100d800340e00388100d0b2482003d0348040481d04042003840610150340040400680c6c82180c5880c154008c0700308035641c031080d42c0b03a001b641e0241200082c003284680c040b13604890028111405e695010001a04580041d802030f691815100c004009000031340340030120001010700524039000101c500d00c01d2000202c00320904100d0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 202540485 1250 202539235 202539247
    0xa030e03070f03021515010f030510170601060f081302061e0a120b040606021f0e06041103070e0c031b0d02040807050f1819060302040203040605060f03030406021002 73
    0x10080c0121510300e504850040540102c5003006540c1c1d0681403000b400041c070301c2c4001199030040000030b01900300140d40e0f4150301c140f500c03822009003102401d00070300c5005e50000003c041d0210582c10a0940c01c08014020642c90020044c1022000f0302000302400198800c019054a0654031865001e604403074554845907020080c51034950341e62680c100c40324000403012101da41101c10703501200303400c810502410718140244001e5503064401e003805a406030302a0042c030251000381d400c0c0b540628800080807411007009610b048015070341550304249848131605281024030400c00941a5016421510300b0940200c0303003507100090048087e00c0300d010300484400b021100300c1d08840b402d90000d54a6076129041151181c1a600c500b500c20b00c050030b00742d1618244003451010f0b070508075850000a82c1c0350003e586281d084076203142d14441d41c60710040b0050361248080d600450203040001594a0070005000304103c84034101e600c640e20501041184590020343c40c1c60502002d4005611030f1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 202541735 1250 202540485 202540511
    0x1080a150f02041d07020f0709050a0e070b0703090506040315091506152a1410110d1808160c030c060507150b0607020405060d0609051e010509030a03 66
    0x10040a141c19aa240000b60005821401d550310258103808400380c84980d40ba404806d91365181100122180e075008200108480c0b2010ba000a51000704548040b44100818a05078209541600311b1300390510089024401d250b4401210400782c5029a40c41c3c0c82c181c103503101c44a02006560004000346d03214007040e400c03c68042541c0c10001c0079071600b4480716450b42c0350600084600c0513101c0c00101c545007544460000307100f02c81100d401002002d0f921032810303107a92903070700c220705c00403049031181c50007481400a03148100000c003003443c0300d01030300c0d0b41044540c1026200c908115600381150000c5000100302d51504581c0011b00501c42c10030414068a4211510780c050340c40684801c0740658005580c03078004006141c41442031545104c07900e2091802e8003201d8003003074084d070443c0c014400c0380014146548019042140245817a402d081030750f80c0ca41c00c0d5880c0c204115400d80002c046203c0c4110400d03a1100840185c40082c005480d11415440d50303405000c01c050101920b03100103840740 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 202542985 1250 202541735 202541741
    0x204031e030e040f0209120a0b070c020a08070902030403090902070507051c02150307090503070e0f070516060b0102010c09062708060a0e070b0313150b03010617070e01080a15 77
    0x1248040d0042c071134041d210200d03038000d402800e00580074103025076100c0703005000860b0b02c041e00b590140c4074079001d0b25600011202807105900898014112060201c0e174503008002c0c80c2d004146c1c950340981c0d645042e1030000c01215540d80300c500f1840c0140300f40030000d080842d821094070782c1039501201d121066100c01402c8401190040e4002c0c1c00c0186490300514050011841000f281e294111038503642c0c03080c076980e038885100e800c464543d01c034040b0b00314504030010140c0000d03503441d185e81000210042525100c1e1308000031150540d80c0c40480c081c0356028059142c06000c0380c10a010769502e859000f40c080c400f00407035044014216105400300900451004c00905901c00031501b1a2511100400041c2603a151141040c4501c1900103244070211040744c0c8110260b0048650034070403a500c035284c204010201115a80e1250000e401c1c5803402d108500040030305c0b08844010400c5e110342c460030260150041c00101081c0c00061001ca400041e210342560703400351410640c5e50a0b42c15250003 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 202544235 1250 202542985 202543007
    0x3050732040213030b010f0f05061902071706061306060f0c0503070602130905090a0f0245010b07031e030209061305120f1e0703051203010f08010204031e03 69
    0x110030207250020091158485c0024140e840d07901201d80491b46901881d04224030038440d5541c484010080c94614044030851802d082006004803074069407940381009410890510300c80c0c1a900c2a030400c034851030246250382c00440c902c0000c10046007084001400c0ea024143d4020910080541003000c1180c20412a101241c011104640304d00d0000309401c0700d10b945118121080341010080740b504000414906c0ca16030b4050350300314500ba8564241710346100012031101d070b445a10303039103201b011100c20a9600e420584030740082584101622802c12a001a0042d941000c403d10818001035041b050790081c00c00302c400d4900c0381c044800d074201c01034840c1c40c10454202d800410b50f01045044c444601050701c404481c3e1580c6000c101c00344d103a4886d000f40700c5220543c40450100e401d00d003145c00c0c410358511030b00b05584000c1c0d12512020b24080150b0850030011400200400500d8080d0f400c00b000f17481148001d518007072454891481162801415200c1010120095002c01d8002c400100c9 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 202545485 1250 202544235 202544257
    0x5060906101b080f09130203090c09040203010e0f1c08040203060604023a05060603040309030b06010c020303120609071103070303020912101b050c0a061112040606030507320402 78
    0x550303080c04d40c03041e0219400400310140101100312989424000900a59201c1e2486000600207000c81104004000c00041c00680c0c25550700d100310030325028140b001c0304090503120010305462100300c40840503a90340c48000b80800a080081c84010f0f0303004149aa003052080f41c000da120b0749404070102c0c1110ba00d2201070440c0d0500707030920030345103240401a1300310511000100a80d035111414003c1c1880121402400181c000f08180000303503624042980001062501100c05d09850303000c603184d48e0101d5813480c6e01c514504104007103031400784030065020106107000c03900b103032805004543e20300680d4030040505030003158000c4143caa283c211544810501c0840340203002c0c0070f81640c010501005280c8121440d6541d21050600801c1200d0020700010f0080c1800e20140d120800202403042d80035107111000c211108880c00700200c0b09000da4054200010194554170782189000d045a226858a00c404d0101540c4510404030142c0c0c500c40f80500b0b03c041c10030110010b8000d200e2084c0400d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 202546735 1250 202545485 202545487
    0x31d12030c0304030315030b0403021b030c21030f0301050915100302180901090f050a061404090503070212060708070e2107030602030106020318060f04150309200405060906101b08 79
    0x900c4400040a2701840c000d4003a5005450201440500b400c4e141490301d4042d03205101d0100c00d070030000301003814099844440b00c480155280c1c064251340c02154030041582c004001400782d071808910090b00104415015010400f0b81e601091907075544c51008414550f002c201034406401201a8000c1010002c03c10040c40d0303180c440c0b60000f40529040b2852062a040014101028030b1041000f50380d41a5485444951150100b1001e00020541103c25002c184413040042c6c0f6800307840084080c2e4880503114525103500b00404010b401040d0300d042220410b0400e1151312900c1842808031102d900340c1070001d4610034445e25002c100d5000510480c4000300000741e00342e0200103031818a000d400c07034000c0c00c0c0c2408200b08240c09550f68443c00f0403000c00082151000381154940840c20608020840000a071503040404581c03d00c0840d0608180c0d42c0045949440e22940d035002004840e83c4000e030414002103075103084040442070a21520340ad040e80045406400315501c00d07800749040d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 202547985 1250 202546735 202546739
    0x501060306021c0b0406051513090e0a051006030b0610021c02160b03010e0c090a080304030b070305180601060f1205040f0b06060406270b0307031d12030c0304030315 73
    0xb2143c0940f58041c0c454152412014020503d89406000b00703d4200415010108080000b02259a8460f040282c03e810104000043e12030b000c0c040c0c10391a000c00c1016020502c0a820554100100c1058041100d45003907001d00000b11a40c4250740c00500540320401291440d20050303203070040314101c02c2000c10b141c504420209134001892544001d0411104403400d6403120f44a006010031f0180904141c4500d00203401d001aa2000d0844000700074410282c9c10742c0d0341c0c0d40302d09641c800d400c190703500045001081041a01401269001980c908103400001c1c0c51105068071500103000350780c00c05c0102010302d2441031040c0044082405c00ea0030821a42c149482d180c8021029000112295106280000c0d403514001007039504613003050311100a0103607410b0381d080b6120a00400e030000070501e03000101d503022901010318031400858800080c400c600d01d10310040250000d0f01c0c0c500c1c90340100c0140b0042e415400550742c004441401072900ca0725585400d40141c40204003000d00d8911820300 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 202549235 1250 202547985 202548007
    0xf0803180c0d02060904090204110307120c0c05030a0e01121514030303060109090c0512010306050603010b0303090a06030504060603120f0f0206070804030503072a05100c1b050106030602 82
    0x30034000354010394116401400c0180910001146880000c0c3d841201402000520304058100c40b0b0524801400000c2003e08146444081c4e00706490000014003035200a03049515248200340440c400703802c09809442c0c00d03548059403841101c5010081200c140105201399010f440b2210b50b04000d25020b0001c0c414488441140d5203d92080c01074074140800c10400a040100490b0f0280300c040e07440401040c2460100c101408603210180704003c0200081404107008240150281d84140e0303001c0b403107040c110101420b43d04065805403094004014032041541c44d0940030080340d085007408030b038a60300ca0038043e00801290344090b211803021803041e04101d40c000322000d41079040da1200000b4070780101c0304070307a1000b040f190700022803440380228001c00c1c0114027440d440f0b49981350481c8031440300400b00342c08003c41140d8100700b1032000d8600302001409d116100310750807607080810021405a00c01000d440f010740840030210440d5042d0f1050110a4102c075016540001d020b56441081c441 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 202550485 1250 202549235 202549261
    0x2d130b0102101109090c0c120304030f0f080a1d0a1124031b07050f1b04050405100c110a08131e061d1e04060b0c03070602070f0803 58
    0x9006401805003850180390140300e4407a14428521201005080158450030b200b40710340050121000040c040c098402c12032000c01101000c20143d19025860b801c1c146000b600e250321401b00141801041c85461814030f0f4051172080d44110031102c00300340400f01582e03d806012070301c2a00206400345408800c10300c501c01c1c858502007403050750309002d80c118645081400100c400d24144030324004002190401c0100c600d5401c00030a0914180d01c1e003034180e07544c10315015100115040c00e4124070340414580c400c00c01e4620f10410155030a0285180c25960f440e20341c0300c05800c05032110360b00d083c0c901d941841103040e686a01c40d84011109000401d0811281d540c0111481c1c030b6130000888801b14005419001d00100710a03203294509001d4188541500c084503d1604190050602c1d00b040645a407001026000880301a0108100122071001c1c002640e407542c00040310b0000400940e406510300104407110150001001600c0780154940540452045880541008004802e114400844413 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 202551735 1250 202550485 202550501
    0xc05040f0b0304056c0d0b0a09020720060702031c050f070b0108070501030b03150411040606031a062b1d0d110f1209040e030304150501090501052d13 66
    0x500e50100d10315041048101700058104001c008014401c2c803071200a0b94014021400d0000e0100d40701c0c90b1500c045008a82110009444079410800325100c5190b84204000540c10140d40451800c0b01c690086565041c0c0d06844010b090b050f50301c621025031042003036420120402682ca0364429403410300341c103a074170300f070280f1000e50249510001d00396001b48281c205564000d0041c0800300401c1070002110600100142c450480080400c03e0307039503661051002030407590302c000440d2803002140c0c40800350403a0b03103103004000130089c0100c603c85405540d41404001007021100b1444400040041c1005c45520b80b005900040702507660080400d550340004030380d42e0b0b00a04811109855a51101490000f030030b5900202c126240c00c002c6034008142c9008050700105511039404003080c9190310480303056941c891011501c42c2000210301809004058a43e01448503506010001c0c10b03103103103041041034203401081180c5103e00c07070103500000b15030010f14a00708d00306a4212807003c1c244034 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 202552985 1250 202551735 202551883
    0x703082a0316080309010e070801141f03140c0303030a0b0f090403090b22060c0308090a0203060106050901032a1413060c020a090c05040f0b030405 65
    0x2446500080e0400001d560707500c0a8030302016103030200e648031110180c3c00601441101e5407070740c000602c0000d08005c41001080301600000c1c0c0d0041005092401d41d002401c26420b20104684d00302c0028040140c910a41e90080498150000f02403100d40c40c082c0403269060301804084200802e240c3c1b55806038814410554241c0b400e00c0c0c0341c03030070403100810441e002004180b600006104080240011f00700d441002c00c001302401442000100700000b060740140c00007504200c02e40c0030103612014841e007090014004198070f0030280e0019444030014040c1008001e0003144c1c20a2680c469000085040340324136542c1c940b1120380c00f0800650705c100d18400c01107080440c60794402c4100340b00700d030700c1a0100d9501211890401508035003084000a090342d02200b80d80000c1141560340c4519845103059480d40d99640745000404560317072242e50301650390f20b03205100b00000b195012a445451080c010950100000301c8500700074403845200d4158002c0b80243c1d0034603010380030b08110401025003 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 202554235 1250 202552985 202553047
    0x9010807170a09020f03061e1b030a0501060207060504060e012316030206061c0221060112020406090606121119050705060603070b0409150b03070c020f0406050f06070203070308 78
    0xc001c10305681f12001d80e0344295001d00742c00c400c00c003200001c0c0411381040e85401240d801b000d070149214295002036800b40708090f075400c0100704150701001500c00a01e5a07051082c1410300c1c0020190000c64040d078098148940c038034400f0001000303501c10310310035007034010700c0d80c2c69009160181900c0490003000320301610600340418800e29000b941c100605e10303200c10003460f009243e400c2c80650904148903039400340342009948580d401c140241c5c0d0180071070000069006030f26004000903281143d001c41400780c40c009061100940c800020646415000380100e0003a65800c1441c80c980300701160655800622141c120645601c0b40c010b00000c0c0c00784c0c040b9119900c500d07040503107070203040c400c64011040800081001d0070403508035640001c0b58041404d1216903980e00002c0643c0f04442820000d80c103d0200710852034030340b110550030003081e40e0820009003080085298402c040d20994031810010856000715941000032402841d0301c0f08680e0340707a48800c51020b1089030a005201e2020038 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 202555485 1250 202554235 202554259
    0x1020c0d0318060e1006060c0308132d060507020a03031506020a02130f061203082401030b060705010c030207050714010c0f0f0b041515030809010807170a0902 70
    0x711900400031200040342e101940c500d010f5403294010540200c60303440034018050202c000741d0151058000500094070b03115844540c3d4540103081c40001040c40d41c00d00038ad02800004507001c403104001140c00c00650070b0009000c040340c070400400600c8000c3c65641440c0c01c111030981e0120350720703840038481c0d00c1c00e201a940141a4401503048e40c040d004c0160b110340c2021025150146002c051104458000180d03100d600784044260707a2070b50401101c814801c800031080691081100f540243c0a03c003032101180c41710001401d1494081003941010b8585030040d0705580c075a01100e004960041c020060036040301c00c080c0194000e05010307940e900a4880c00529800c0880d114100c180e8141d540084a007519514035150102c0101c0551301403083c0442800000e218140b09400380d07004888040c0104202c1c0441d20a03142980120484001c4030281040000c3c4440d056130200c4209080208469480210440c1c4501d07481310115488040d443c180502d0910550280c4260741c0280c43e1341c0d444035 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 202556735 1250 202555485 202555487
    0x108040819110d020a050307121e0e181015090f12031407030203040612020c03120a0f060f050607140d050c0d050403020f040c02011d0312090705060f0c070b0c01020c0d 74
    0x15420085c0a041900704100000c0014a498090140c080c032608042e201e03103e40025106c241031401c080074022424910202c0c2c030501d099901d1044420411242444515040000c0070001b05e5038810b950224580180305a00940514000001b0380344108038094042c0c0c3e5503008883d510080182500445c07072000d040c0ca24002c0060850741e406405800452620340303402003c4401021060402c803031a5400c0c080ca0f071100c0802e10003003111440b2081c260042e800d1460301070781190540c01421803002c0c5001e20402c0020041070001c0c040b035004803003107a102e101c075007084600d442c1e0107410580c040c01490500d81c3c2440d00700e030180c44098800400c603100003a800c3c0c0162014891400007075401494441540e03d80e00e0580c002c03030451a4144000703d2402d0755084075a1611900e28035002a42d040421001403008100d421107500c000c00c1c0008100c528501404981503100b200601004440002800c95200c4000c10a1800400c0450150b80e50b0f91900224103000750040b11b510f00c02800707480c000f44015 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 202557985 1250 202556735 202556743
    0xa080f0a0c02031b070b070503130905060a090906022203030f0e09010b0a03060f12021309020603040807050c060d0c030e0604081815042601020307020303060108040819110d02 77
    0x10801d65001986000314030205442052441d8055881d244110000411200802c4000d441e609228500841c1ca40c000a1036561750300c0c1c6103800214040d0318200c1085030550b901501c0b02c0071540c082c0c0340020300300b000f41407a101070301c1819100c28941c0301e43c040030519a031080100740100c07806aa1707841e1182c0b040610886070804100791084d80850030300d00500200ca2520020108180542000074001d0b50700d012141e54041141e2000b041008003140c07550035410b103000240700706000141e04204032103459000484c64040034101034400000440d0850402a0400850b08820002840582c5a10070f090901003d4446801a132000a00b48920320141c1c0d500000c01d240030780d901010f03042c20705e0841801c5450401583c00f0050340310140d42c0015208140202c0180013400160b010300c40c070284140354500824860510180d45a03104000f003204856000c419030350828424a0052100c3d101d9041c8042d590084c007a0118400c0700700380210909640201044003480f0802003512869858004141d0315 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 202559235 1250 202557985 202558001
    0x51002070c060e0d12090501020c0402070c1a04080f0303071101180303050a1503080c0105071b080306060c010203090105040209130b0a050612070801020904181101120e030a080f0a 79
    0x40d180c80c0300341800307a02d0107003e030b20914580162001290700002e490383d6002090305072203040421001c0e102031065582c180240c91070710800341c8040d441d1403225078502989007120b02c105220a040e4482118048010741d040310000e215440403201012007000200da12540152110408204a4805c08034010818096111604245511020200281e071010f070050074000300b202200ea0750300c910341009100e43c81901405180a0200302da00c6200e80c2480f9030840c0c001624941c140b03c00010a02c82c00c90540c060b0a080e940d12101d0035440381c50742400709800e400703660881d11855002104004000c10154400c51117107008035011075aa860b0802000e401040545000d02101c1d07100c40090010920303030b045035410080142c01d42d0460211521141c1c00c0c42c1e0301c1c0c0c02a55407a5000501c0d100b007490140154400e12551030303903240f40120a60703210f8045000010a240c18014800c581d80b4000b40b25901c20f40f01600ca40e41560368400c6800c000500e211000c40350099615a81408a02c001d2114424902 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 202560485 1250 202559235 202559243
    0x30c150703230f0c04050d08040305010c0207050a06030c05070c1415090d0803040f0807031d01050f0901031e020f120108030306010e0d050f100b01020c031c200307030c05100207 78
    0x5110f441d04034040c03d50440091554424210401000409840f0341c00003250482c01303100c209803218210f1418509440c9075a400e04115071090200b03000e41c0c0e548905400c11151a400d0025040755403c109469a000d90f04000d003806109075400a45031403204240301400e04100c81d801d0b0000720102100c80070b070003007500194202100f0402d0000191703040b001141c00c1402034008522080880d070310301b9004d030f100100440004501020304141007070888000440c0c071009007421820b24220076900c5c159405458195410191035000150006583e0401c800794070620301010340d80e40381254042600b66000300341108040c8001c5000145824000c01900d01030001650f440205030201d00030000641340400c1d003510540101d541110300c0503000c00c1140c10b81003d4642c0460401e03c40400a4244900d07480003034000d801c43c10a40b4038010780e8106180500505082400c0c085c0c0d1115810340c402ca01d00e070800c00040c80b000410b10207041c0c104086130905403054045541c0c0f4104800f52509034010420014 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 202561735 1250 202560485 202560551
    0x50f030406032f1b0307021201022802062e1514031302271303091202010f050307030f060308090405220201050304030c050604060603021201090507090b03030c150703 73
    0x92101303208100ea007180004d850490b410004107400241c1112510600d0892503036002031040f0212450382c1c03541e000300002040c03040d6046c80b400c0029442d060014174810968003000c019211101c8584400d656042c40b03482072034051500c0e41680c2c0d294031249802c880100350000001742098000300112845035042c2c2e040300c00c803600d0315070a00c43c128800e501078075680b41102801c0c0c1c210b0f210044541c0d01c80c02800e9002510485141406000e030400307034101c20300e030070004020b01c809070740c00045034103203907039946000c950b40c0e550090100c008121203980c619800e82007000000901c1407107030140800c400110ba04001c1615018000440e50a02515414500542060a1000d50300400142d035026020303007440080e41030b441d920a4140307902190121009036603001c090095040604110103018841c8c4020400c0d0740780c5407a01c540d074041c0c0d44104042580c54200700d540c203480c00c1c010344030070000050449400084120740c80b01c10601c02c07190b82001a260600c0b00c801d003a000720a00d150204000146 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 202562985 1250 202561735 202561747
    0xc06040c0e1501021e030c031201180c05090f01090803040306020c0f0a0f0f02010c0b010909030206070e0a050909160b03090c040908040902091908070602060603070509070c050f030406032f 83
    0x880508071854a0b001c00e000600c210240e031070048c4028135200b030b481402d038a075540c1002c1081e009504082c0301a1000d500d44007260385a650810304030b0f000c0b0f0400b1a480c0510400c40d800407a01031b242600103101500001c20004100903a03500506000c0d14200151f506041c2121403036507170b4071201c00014041c10803282d60070001c42c0600145200c4c003030042c50100070280450711203601041080c4d0000380c3d0309686040311014141d0501407030341c01c150b007485d1800d820442c040025031024658022244101c036000702040c490f11007080705980803400c0c0242409040d544150f244d901d078104540450715401040d2500c03079546414865000100c1d0b01640d41803c0c41c0c24002000c000790449007540d07400410604099001800740e000b20300040200720b0090580908207100241400c401411343c0f400f03940a52401e200c50390383c100560781d2048451818403030030305650815514012541c00180d2003400001000b2500c980e0641040c50340d0031109010a254810780e19042c021309100d54114145500203000c5 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 202564235 1250 202562985 202563013
    0x801050907020a290c0703120510150903050f06010e07110a11030a0501150501031103010503070b0702060f0a0825021203060d06110304060b0d030c0b0c0c06040c0e150102 75
    0x1142ca280300795a044408111040c40030070794a510241d0703054007907140c040f50006c1019403082407521071141224091040c0d040c40d050b841e031411001e0045001440b002e01c040044c0b248620044401150403000b1210000c5094000030748408082c05059000780804001070707045401125650180c0c0d2110700102a2460203480c1c0d10505244003c002c0e40c14010320300da000100b002406410090f40c4c4050294081c2454040090101c8046005a200040c4180010802d50307501081d00ba04491a1403500c5980f000f00c0c0c07000038080d120710500c120030b02d5400b044041c3e030650b00035001e81c41650a5a840c035000c000302042d074200007840c00c8121006a10504010042529141c0550f40240002c0d0040300002c00a84d83c031400c8d148001d03041c00c04210301104210030301c11035015841904005803540e070000d0003035860040540210100c040d02c0605140046180b08462500300c0340d22841c1c030801c1e940070781050700e0400c0c070801d898030900071071000a0010404c0c1c51054018040e110070305070000c003036040c40b03100 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 202565485 1250 202564235 202564253
    0x806060a030605131406010c0c0509100e10050108070c0b04022e030f05060114040b090a09020f0304050c040203090c130207061b02010e1b04180507090c0801050907020a 74
    0x2030300d1040640300d1500007565102c19044048001130890081140741c4c00d000340911410004007580d040140300101040030550161103507040e07410540c0c020107c0d40c1c40e40103510345c0810b6540600b00070031840703040003c02525a404541550026600c0000a07202c0fa98200c2e150f58020901410b140b14101c0840d00501d842c201c0180000414412800c01d81c2c0086134420f207465201f00c4010110761a40c0040c08103c01902c6031550041e400d0800012100072411250340b10b02450203105020a0300041070047e9030340e0207920800508505d0000c0d5034030449401c1c590030b59041928101d94502c80c59008514a103450300980f403040c3d9051008294410a500070403004402c04180b841c0016804c000240100b001e030b0192510315030040c981c048a2007038800000342115061a9060700702d4005040700d52042500c02c0384030340500e00032907020403041012040d50340307040a5440001c102d4480c1c1c000000d03000100790402200e100b040c5d2592010390307030b80e1400e000060b2400ca402c0401038014824550014080e88 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 202566735 1250 202565485 202565497
    0x9120204060503030d0b04050c2a03071e021c1203091407060201050405060106050414060a0509040f06140303030f06042301060e04111206130e0a0609020a050a06080606 74
    0x1400407031060b9640c0082415648070b02c144519054039818000142d0038940109500110411001ca152030a04600302c1e540315101580c1c40c40c41030114105203c1c030241041034400b46500119002400401c00d5004058038403405005c0380190010005903541c011041c082d00131407500000303100061541118104d00400500500300d0300c0d103c3c01c070312980c5680700030414a0080c0c8015000020305040c01e0806503c0d1841c142c0c442e10400c04204014400c80d4042c07149190003110545020340c03aa0b484003801d584a00440b5216034009203402000e039800728540d041001107030000300744041e178000003005150308e03848120755454644150a011170028102680f00500c0035800e280041000510000d400c84081c00c203920403000200140300304031407894a4401c0302c807a003d000501c00c0c40c00d2002007103440f609500034216881003202c024030783c0191030190800d20440d4006000c0e500f1b4030f00d4a00e0500c0040040720400c0e030182d08003040202d03240c00c4c180e9500c42036a0040c0c555405a0703448204001c4ca40d4000 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 202567985 1250 202566735 202566739
    0x6081f0c02150c09010e0d0c030201180e07021006051813020103020c0f06010815010e0609040203030f0a030e0106050108010803040b0f09120a0201110c3a0305040f0e07091202 77
    0x4402e1411074800d280c0c8240154180c440e034a03501c566a50004203241c0e03907040401d2203007101c3c850071400519030001c8401265821b00340242c87d00400d240b64504001d00354050048032040c4c104005d102d41d404110200707441f42588040040c0351711030040c001480001c0c050501c0c0303450604085821208074100c80d4804074414900586042840c2c405a402e100450031000c1480d8066401803151007014480310100ca0081c00340843d4540c503103806003180b42d90150255008102c54800f040a5480500c00c903030005400282c0241e0340c02848000500603c191040d5042c55480c040011500707612444025040310035100c000e5080c9400c1a081903c19031040c8a640038400301017003521002e84504800612018026016012501280c000940102002000066a40c110f2001c2941507039860000a01d0320800711250b43c544104003a9100e07240c05a02150b060b2001180c064504040d8004001c2c030a4500d82c0d9040304001d541c802c83c00380e8480080c0c030303100c001c40c051980900c20031041400300860380b800 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 202569235 1250 202567985 202567993
    0x8030f0c070b040b030106090501030911130f290a06080106110304090603030e1201050c04171603051c0306050a120204020d0906020408070e1501030905070f1806081f0c02 75
    0x522040400150f20641c00fa14003450f000c001081000d8001a81c0001000203080904c0080002c7e500c816041d041000c40611941601180b5103070640103501191617900da00804014005a14914010a0b8500806031401c80d007034446008880c144014010300b181c13401d40355120a40d00f418416100c000c4081501d4440348418440080c0d01e01440c05400300940c02600da43c034803140a0800e100e00803a16107074000c001d80c103101c207110302e0064180c11941211030200d0340d407100a000514042c1050a10802e2103c00c41c203005c004800d0000210300311003c081d0680f440311132209050401d07426580d842c840d032a8085e1880204110f01610342e0840240c00e480141b00500e040c044941c40b034103c403010201030311071650202d0140221901002a0409410040341d54601c51800f070304000301c4030100b5600b150400d51940c680e0350800000300000400752803060071401c51280c40d00c825181841c1a00800c0c1010707403c1403800181042c0115031103682c8103200401030062a090f61408001e081480000700842c49 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 202570485 1250 202569235 202569239
    0xc03110414060c06010906050111210306060c01050408030f10030c05010c0204020c030307030603021e0d020d06090c060c02030c0108010617070e040606021005070509011205040809091303030c020708030f0c07 91
    0xc014059940640086d080000c0c04d54200790004020180450800d680c2c5d07070090410024030004094085107115440c01c4042d0f072903840c000400c08a000742c568980203582401c090108000b400000707588100d5980102c0f46059880a511a100d0526444054406070840405020381e52091103a40f000900282c805032a002014400074035680c0200d4444000a503668418011450444404031103903002c4522070782015460b0000a5a000c101c600091182d841240180d0401c001da810601c3c0d00c5030440701102d0741540d140f50140440141e014120301c00e000d80d501e188034540c06002c40034107031051640d40c1802c101c0d9005c3d100c10b4240019014009110184c0f0789101c1c1741c0d981d8010b100c081d04180c0e016140c0506041d04000035504040c08110034400d05020183c9640d92000320780402e01d00c441004211030f00c0e20f09001c04180b01342d21203540c100d02c05074201b01800b144bc1d0101c1d806140b01c1d80e4200500c1d088620103e0b100c016a00403d500e6070410008601c540002c880034255140242042c1c0b20b01d10707 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 202571735 1250 202570485 202570507
    0x10c0c06121104081b010f021f0b0301020f1b011404020f0d0c18050a02042108070506040b01140f031009020f0603010f06120506010c0f0f15050105040c0311041406 72
    0x1d0410707400201c4641c020300305c490b110316060f0b9841e004020700707003031000c02d45054040180d100c0e850b800c40c00740c000c0031192030443d40001c1c64105101e0090060b00031941c4000c564913140d00c960000f401d10509000307000c01d80d08203030814411302c054201d12901200c942d0b21030303508000e1202d407800090703584082c09a84420204682d005d0940061500c01c0c5100c8180d06064224000d862004205a84040c81840100702c020340e5145400310104010148081200507486c0a0105000e00400640503200e00000c00041014000c0d00c24180d44010203442413200900d410007000180c2484110b425401610300c201601d0220342020620900c01495500d00f1800f40c0c010a0868209a1091881540da00d400b00241340d0404507962842c9a80d110502c407614044002030003464144d580140400820041c031018001c400c43d02805199102548042c820300d2481c040010f03000a00a0300c0c802c0d0700c1c06015940403402880790703070800c0d6589020103040c586030181448100f4600415136410a100f00f04010343c3c1c03 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 202572985 1250 202571735 202571737
    0x3030c080d1e0209010e0418110d0b010906050f0d0f0818060d230103080306010807030b040e010c02240c03040204061203020303072a0b150d050703060b010c0c061211 73
    0xc0000102c0142c8410382200010154005040d015018500c1c10b20384205018603018075101d070b25001820950001c00d190040307800300859450203480310350044008190540c894101504403601110007007c60300c000420440548000728000744102c0740400345400007103208016001c642e40e00b20490440034036400200c0d0490b4411b00d60f41c4409540d554600b00d20080d100d07440880303100c040040f42103a60441d40e0780c409901c00900040e040c81011800960070600c05e41248414400280007030041c401991059806440d00e4070b101805800303401e82400100d80c1900c014403070950080d45040041e11481c6807000540d1001d04182d03005a00c85102044059401c103140b440c05200ea4011550b0386040c01004041003c00111402051041881c0d4002c0150102d816405c00750450b110101c2e070b480c1d902c0c40150b2840030250a60b0050750394203403d801e1110219099046070302500e81070207002040001101c0c00302000e40001e2000950f85001d00045110b840040614011084005540c0c2c0301040d1031842 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 202574235 1250 202572985 202573031
    0x50c030f010504021314040b041b1509060e01200f1e280201080601170901200901050a0c080702060d2f09010f0c020a1401110703030c080d 61
    0x250b91100180811410702c03400f1030072440202d04c800c02c10b800c0030700c90700051a500904054607011401e40400d0900c1190900e09822206858003a04080d544800c02914846160040408102148000540d4038041d40c040c005080307059455240f0303051111800c0070b004d400c1e02c900c201107200d2840c02124802040183c01e02c1c3c1ca103ca010203c009042d5030106140c04c0d540d800030b550214042031501180c1166118554079184e090030030308019668500125065079841080400c004000001c0c0242d01e85e06501c041400910140c00d510300c160b1541a2000310f00c1602c030401d00084041105444a44c461040a0021441840030354504242a00014815005101507112165850340c440d0340313203c00c011900c5412555410032100740405040054210b00412490a05000c600b00300d050b802d61140e0040c0c08096030041141510a884d10710030b10300b0010504c81103000c5040200595119400040e0040c103c0b03070b159a500101101503030380c5191503040044084c424545030f0807141001c104280e00130319 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 202575485 1250 202574235 202574263
    0x7030309051e0d03090c170c030a08030709050109031203020309030f1911010b130b04020405280b131809150f05011a030c031b0301080d12020c0d0804050c03 69
    0x3400110110700c03403c2403001c240c0002070520384080080006d448001c0c160450b2a0740001d5401c4104401c1490b0402e150304441c2d95040c0501e00f0010200301010010f1801780501e55617400229496000545050046001c054940c0b9416800c40018511940041d9402074103003080e681406040c4400a031aa0800e44002c0d0344207066405c04107007254440820105940d0410007131203030100320000702e001c5111408007098141d0b1205000c00315070f280c6804650040401402000700d000c46411100f0f59141c0488000d002910442000900c070302c0050142e50140d40d001045801051400c203551b001e401c043c4055008407502c812030f40c404035030308a01110341a02c24035404034000b808890682c00301d40c6c0507007004501c420010120b09100c10b44500756a07112400b08002039494959021482c80f505402e003081c02126030010002c519100702181800c4c0383d10b40e42d11107540c401c0391194000b060740114080845c40d40d01c50320b50708038414443c4e60b03043e80240c01b40c0d003070341c3d81d010180c00840d003000007561100b1 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 202576735 1250 202575485 202575523
    0x1203020307021807052d0d06050907030c2007030c090504030e09090c010503090703060510090b0105190c0f050f0c1c0c05062203030e090f0f0c0703030905 68
    0x6015400c10003031245851200c60681c3c2264980050302801c071313000d540c1c064225030315410441c86120510800104481c0c1c3c1a902140e2115000514031000d801103004541c0a5a03100f00400d001c3c074000d0003031304003200e081c0c0c44060300c1d00f10201c1b903090000c80810304910b10344104140040410700a00c804000b500f43c0c014089210b140600b4083c1c203203420350f8001030045c185002081003c0d0720201d506c8501c4e43d82460401d0792a00e070355513030750310340100754001034000c52408040c4202504580c100320100c0c0c524a02c01c1c0f20340c80050005403100e011300c2c5255642020880e0440d803801e4483c411a010b120700c0f1f601e101410f200252035540c41c0868803c048000c40d441001c040c181e0749821120a042a060810180c42c403000c0381e964600c1c030504074031812703002c0d69011400c250500d100c41304488884014a0500024999a003001071400720f13007122103801401020003044144a403003103014070881402020848589519900d1b0300c0b280e002c10070a5080503030b100b20a1001a1080c882100213942601401d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 202577985 1250 202576735 202576747
    0x1030b130c1401110c090c07051e1e010207110405060105070f1b0b031006030c02121201030308010506070f14010905150708060901150302031015020607030513110d020a12030203 78
    0x5003604c002007042c03011039808080b04248964898a01680c03244408038001d0701c40c051494440d2a0807a40750b1880762540d85d8104080341000d0006407040038942c140a00700b243e00e40045007900301c2c824440c0261250780d01d000000c942d400c040d04040d40205040c5005458041c1d1500c0d030f85445482d6a80807944542090907110f1900c07110a1104080c2c05080c2076545141045014036541040394402c0c802851740303480d4a005218000d101910100c80311002081c2d403110799049101c03009400740021000b10303031403500228940c02c7c1101507450300369208456042e1402c0d16103c80c1ca0402c1031400c440001e40d2030b00c0108000460070310218840b02c400305110710072410401405005d24000500b064055420030004104200305801d01283d00201d81c02c00681e01c2d2110b50f000f11b48140c0c103402910011080c54280000b03a9800901107103c0d540c55a02040036480f070250901d00200c540c00041c00c1c952444004c0002480e09410f2906d029100404d1031040566482c8101182404501c003900560404240 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 202579235 1250 202577985 202577987
    0x12c0a0506030d02010b0d060b010c0b100306060b0c1009080405120f0d03020309061b040504050c03060a0f05010f1202041d0901050901140f070c15020a110102070b01030b130c1401 79
    0x140c200b403d00240000d000c150070110104140350002c00d405007045d902c4010900c5240d00038014801c120741c02200c928142d29052001004484161200716800c0f031801100081d503040b030a0645031040412006040d03c100402c4080c1d014020503c01507498040c20040054140d46414010001130901e40185c1503900068980e40d06040041310780109060040082141e40000803e0050f8081c8000b078500b88084c9030720104448500841d0002c5802c2032510b17061000c0c0f81542c5000d035118a4089840c0e1144549800081e10f8144103403013003e012610007121006a6030103105091440c1503120790050405a0391032202c08002024107580c5405070501c4140103890a0a01545500c0161034000b03014a900012001300a83d4000302004590002000810342861154187c0d00400d0307040010000e451820108100095000818a10100b4004d85201d1045403040c001e641460381c0010558005a20310740340ca180542008000016800c0c481c4d204100040000340124081c3c4001c0c9000b100c0c05c481a40 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 202580485 1250 202579235 202579243
    0x14010f0f1a04050c0304140304090f02040e09070513020904110708030402150405030309040c031e24080d030b0a0801111215030622020a15080f0f012c0a050603 70
    0x198640c012410102045503a00c00e8000701c1b0f80265210076400e080740704210302c3c242180a1a0401c0105909042d84100d0040700d0b0b0700a4415101d244600350310984503084595915211445401c3d04009034181c1c3e01900300141e8058140290041c00118029030070080c4010f450344003540855034410701005210039424115803601f507200441688528045c10400020390703e018003da00b0b403007107880c1c4908031407151181d041441c082c00c2c0d04da80d8410025403a00444090214607480b98403414403050300c1504400131034010821100090702030000074a0340030080b0080e021562422b90441c009200000d1540c2003481200740505106045c41c0c4c440e00c80103080c014110700613040044801c00200c5441041c2e5011407099002511400780110303035204105030101c80144410060361040785c5074000948407041d41104803004003140e40304030480c0e07500030744092080320682e8200c0c5000740420040c0b16a40801c0c4440301980202e00c556003014489002075110300100300e4030b0140b516110780502880781030400c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 202581735 1250 202580485 202580531
    0xe030f0303190c0504030c0509060103110705010629030412021c03050603070b0c030a030b0103060911071101030504051e030f03090a030905010504060f050f09040501081e061314010f0f 81
    0x442e1079071170031b49981c44401501c0b0720f1307008a900c91800840850240da0190344507041c0440040105510344c00281030490003401070380714058a80041400d504104070380002258003001740705441b54159100d9460320700f041c82c0111110015440f030080802c5040a00401d41c03020002556804262071400500341414242d1540c0b052072031074021301c1a0841801e01009072041801c6919000a950a11000480207041164400c080741441c02101c0854284410002c0455078010000c40b140b03c3d0f0324600460840b0800c03035029060f50000c00742502000070500e00b159a495180c0d00301c2e4149000c0e42c241490301e603c10790302003026074001c0100381c080581046628000b0032007420454145481c2820103040c0011040b4000108040050001100d509400c251284c044001e001004a5a1a204800d55402d8007182903802d4200340a0785903210880001c080d880f420720b1a880400b00e00c440ea441048120b030070b071141100c1d9520350340301500c40c000505c142c010b44220b00e400800d18100c2c280c0c400540c1e80c406 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 202582985 1250 202581735 202581737
    0x6020111040303090314010b1c0218091504030c0c060e1206010303090b07080f03040b0708011a090d02121203070f05090a030305160c0f030b0106031b0e030f0303190c 73
    0x7400100040b03500b1404544c00c49030800003002660022013109401001520a803940c000443c1018141d01c080901460402d140300350303500910340184104041c0d0f030000460f000310740345e408499104002110b071911035400034400c0c02c1c4403036032050310350741d200b04408160003070400038184109200481c68100100003425050380c0c06001c00d5415074070021711301c10305401409114000050720400f0004280101e501c0740281c00c2100d81c490506140a081c00c41c4152814000a100c234800452038403010340c1ea803007540543c0800c1e18942183c40c428401c1207810007030142d900440b2030704000d4090400b40034103224525a01c2c8099541c1c44c1803100908040840d4050100300203081c4040c034001d4803400f41001c1500e4042c10450f4a4aa6004050002006528000302488800d03407000a075002c40c90900401c1d0391066808038981da072039800480450307501890070030041c154003001c0d9103c0b9010340704c505055403010301900c85100707444d0300b000d184d07900c2620610402d0803546240c0c03101c0c003241d100341c1140c1151 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 202584235 1250 202582985 202582987
    0x3010902030a0b27130609080301090b0102030406050322120c050d03060609030206030a0213081b1c0b06030f031b06070e0306011802040905070c0b0a06050a03080310050d0c06020111 80
    0xb01c104844d42c10040e180c04c20180440130082004462025500554264005014801d400103460003101c10382003889602480c6050494a010a40c000700546050780c0c070701d81e141406e503a260403015402480d4248451101207042d07075003030003061407078018440d83c040c03d494541c542c0f425450280d00d4480100151403c06181040511540ea1700a001f03004594040f2415070710ba80f03d050100c0000d10480000703180d004200035000500003004502507540081e880e0300e004004500310103002d2901da00c45111448600c410300d5040004284000d250b0304158007070112086d515100b00c05a245900900c079400049103d0343e2156165181003010341c1e80034103240340c90242a076207480420760342c81c8180243d65014212100311001195564155001403112440038000c50030402c0018011240e07404041d211003c0f404002864184980a070700f04542d005480001c44900d036482e84030807500007415450f0708407442c440000b85540c3e0030081c288181c0c00b40c0854a00136140c148080d0031580111204505000 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 202585485 1250 202584235 202584259
    0x30304121e080c2401050f010c0809090f0106020708010204030b0f0a0605030313260d0c03020c100906020d02060709060516080714150c12060414011716080c01050a0c0803010902030a0b 81
    0x54500248100e003100303080c10402c40652b85480c40b00c50080c48c0c181034000c180e00d030030054513200c0303002414100c5030302d038084d44c4079951640b001074240c3c412400054250390508000c40c52004003a01039035032200b155880010302c3d68640300081d0842e484000b0020000d601c00c0d9040c001d41e03255940060781d8800c2009520302003400035065503220382220040c04144681f4130740034001c1c580240001011079070000e202502c400719a000c007505020b0035001d00e200503c20000c0041080d400040c14500403c03042e00e03607004441ca005c81c00c482990200c4a8110031005140c0300b5000102c2507009003081520804d45070718030700c0148401301d240981d0180c410280d81c0c10703403050000341c80c581401c035128000295181f840c2c964600d000300c2d01401c83d0aa410601c040114000540c0010510128412200c10000e403014071400c00805444010180a0740545810070004004250301810045c00e042c2a60b003090f814406c02e68480d955650426030002205540000c10002c40c20306512560070110400c4070828107800b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 202586735 1250 202585485 202585489
    0x3010f060e0f0409031701080106060f02031228020c0307020102011b1209020f21011a0f0603070207120f0b0105040204060503040f0203071a0d0605030304121e080c240105 75
    0x6400800140c3c000c60380c0e40500c006151040000743c0088644005403616035030346480d000c0c001c04542c46500000b40d80c40d045180d4152020003190b114580c4d078003006d602d64652951308032403040010440c0300034410212100c10300d05800c4c0094902d4a60680183d5190712441c0006403c3d50f039400219403584000c07640d91140341b60495065110600350003c00500000b403440405e41e009849111164002e410701101c40d0780c90740b4444281c010004040c000d0080c9012000d0440e000c4501110840c0c1c03065042403040c0131410404084c40d4000c429104881040d59a6000d541054036008000d8442030303002c1a2850500c4001160b003401007030251411480c0a1500d80020104e00020300014842c105c1040d22000b550340410000000d84503002e00c0400c041c0311018002020380c1702410003008581091b10024240c5804403d4604031801e605400d10b40700351a668017540000006000440d003500c211600d0046449980a805078440c00402880c00d240b4600005500e001800c4107503c0c0c013207a450040c001b42d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 202587985 1250 202586735 202586749
    0x60f050612130203101406040b0a180504061d0703140d090308090d02130e100603030e010c0c030b07080702011b090611030d0e0303061c030804020d0510050103050303010f060e 77
    0x400c030100b000b0050003100348002810032809075400c029a505125410307900407200642d840c0116070403a802c100e140c00030000e01c006410b01d4400d84041d04040c01403071000348015002140d11030320424002600c44c1c01d00c580c202c00110711a8014106520001c0103001700540c03a0810000485d00c000101131410142100400419481c00004e0085002040d8031025840d800201070703910ba80103042901b074046406880700188051140c50541c1d10403040c440d840d0800510a00042d2501961000c1d011101640152561510302504840d4200d4804002001c107516400003806810343d03507107a00c95403c0c2035200034259030103242204800080038414170003441e00b0481c000c0c221500c0341001d00c00d1a44112046056014120410f50200c1c00d040044107102c03404001507101e420b080359604120300d42004034900b0b1108040e4010085400b40c00842d01604d0034170340000c1401d12501c2202d0040b007800c9501c505590f001ea004882d1a0700c04401803200d602030440c10701c007038240ba03e02000d6400710000080d00d4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 202589235 1250 202587985 202587991
    0x60402060f190f030f0509030d1509110d0b04181205040e09030909100f0b0d0b10080405010c020c03030d0f0608070609060201050c072001030f060306060f050612 71
    0x8500000900c90081520840c00d0310b00340030b5070407085010101601405030100402d0000b050000c0e1601c0c040c214607041501c04c850040201c0c8000310b050000b0070b1100b000805003548054405410404000340d204024012244490101d240070703070302c6284005144041d40c1080c541e40c2c0c4a02d080003075200c4580f521400500c052a00716000c0401d0b50078400091702d107441950403c4403180c01c0702c3c08000c0511800002010300c64010341d8038545640d00c06c56103605007005406282d4500914090401c0b668800320040c00d1880c4048000190072107280b40015031030070021080d4004604044204418002c003032050074001c41c200e002808185541000290310780c45082d00300707001c16945030b0f000c12120010b940311001424191040b620070544034500500124034900c18400103601342400a103800c04541c0c140c42103540d0007907058602100900200d9045414603460741c0c1019518060042900c500d4001c910056024442c0062458104103140000102d2034100fa800b54004000d44142d05190b044500d81c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 202590485 1250 202589235 202589239
    0x30307020a0c0e0622020409110c07090e0706050705011803080604060e01050609061b03030103140706050f040b0306130f0902040e0d021e03210a0f0c0806060708040b04080d120608060402 82
    0x403d41d14154005c2d0090246d90007002405203418080328045a60030010041e1090030b5089a40403540c90071000180d820f892022100303a0408401040818010300161a52610903030012444108101004520003404401600001c0c03501080c0300c090b043c14030650014116644920301c0c29030510001c26281e10904a85134003d000004650360341e90120695280703050303139407420f0725aa56501d05100d01c10341c2070760b2100501c0340a808030000f8032500803001c4130680302c5245002803c161400713001101507000240070a8200d691148460311250580c8200040301d4400d060003d540300300c5005000c22141640d9040308281e0140d10695440da40000e85d0302160300800442600315488091014258058521070120580403801c0012080c0500e01c079a0b40301c0c1801000030000024500d0201054480c010186004903101030f010442504108c0c005180d014000d00c4258540b0f03603105030340e0801d9442a8890300861b007003102c0e090030b02e42c0d000368613000c3da10f024131060104a04240e000d42e02c840c001f402c028 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 202591735 1250 202590485 202590529
    0x4090b01180b090301200702011706091303030f06080f0f0712080a0c050d03060302090c12010b0a02191202060f040c1202130903020714100e09060111030307020a0c0e06 74
    0x1451381d02500710350b000e404500400ca40d02ca1503502440b49a40100e81c0c1280490303078450761102e400721800c001c18894500281030071155102d03a042c20345480540d1900f90308040d2941002c9000c60140e0180c000240301110040103061085442c0d941000d402a8001d681a04148410041b480b2081060782003582c11400c1c0c60785e514003035202a100054400402841802800c2030f400c801601584401c0031640261075914840d5902d041c004c9103440303111400e802d500d01400c01070240d000500003500000c40e050048079400f50020741d114405054088048a902220520002e00154140450f41e004503001030399016a040c695104d101c1450301d0b00554032040c0210b40c040e01555035403081e4240e00c1840400401400410f410000c0d251481805035043c0c0312180580c6443c0c5d820700c10f1100240d902d103a1f9403560b0460600d4200705114130050b0000d410820040401501d58a090000b5406417803241c00810300c880312850041d46802c06a44000540550035003002560389503003581018842410ac03640d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 202592985 1250 202591735 202591747
    0x914060d0c0306030f0605100b1213020406080f01020409060b090117090102040b210c19030b0d0b0106110d02030f160f0506181c0215091f0204090b01180b 68
    0x2c4000f4034581d880580b5150301c1042940901c00f03998045401129084e4060b84680e4807040a101c8a1007424600001849440d002400300c0a4580c3c0d81b040d0540700400114042d55a103a0003460301000190304000350b540001c00f003144442602c1803100500b0b003440c501e402c02c0c0020300040c05e524640b16115151650300d60000b43d0440081d8111006000c6805109032140c080801485480168100d01d000c0f000c00503020074501c1c0009420707100c101c0c01250070385003440c80000041300505541e6024a40007102212142d000480c0c00008501800031947e44d80c07214101120828500810301402900795041000444030241040c011a01c10151580e00a488103e0034030b00303541b0000d0903440282807409481e044c003070f0001c06000b018203071201010840c0c0350b5a00308540300800c407012010000142e440030300034002c5081003840d2030381e00905d03000c16900340c91010907000201c12001d0350040c0e8135035070010341803018400324428201204d000303103001502102000080804c1410394080c001003403d02140d5 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 202594235 1250 202592985 202592987
    0x10030612030c02030f07140402090a050306040b060a140102030d1a030d020d030f020301050a06081801090308070f03021c020f0c0a08030a060816091d011406010914060d0c 75
    0x264004003800300c0c0403500c8042a0070020000290381100324424040c0250758100008001071900a80716001c4040c40100851002c102c025401415401d810001011002400b541c00340080c51049020b441c202580d0702d020300421040f880d840d08410f0208440704c141112903680001a90018661800c0002e121003030803208003052641015015810f2042074043c0002ca540401c0000212500751030074041b48036462500c4007640001d008854200c424500d0801070a4494505207410030340c0030071480d540f00c1125074460b00f954030281c0d09502040148043c8036515030f010b0a4503a5840d400e10f000c6081240070308500f900030380a107194030400d907004501d18002d00070050807141e241c0c074135a0032240300c07110f145001342042c0c100302c0d180b090581c505040041e405034040344881c08080b080c0816109181020310b000001c003c441c0c290201f1580d415440d1000303500912400103a286020b040d0303421464050001000600c8a4010008004040d55402c04e140c80b41010b03a16165955440455501c009070b41c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 202595485 1250 202594235 202594241
    0xb04060c0c0f1a0108070518100b031014090610030c02030c0d18090b06040303050a03020412050102070b07110c06091f051c050f150a03230f0c0307051003 68
    0xc00391007202c01e4010001005100c08000c41d1506207100c40c400c1503a668800b0f0380d15084035104807508410105d000c00e0b403000010f4442d5a20000a541c58018503840c2c1413039070200e4204440002d45200c10603c107001c01c02080000036001401120301320082c0c981400031400c6036a0a5004505141c0c440b90307482d0000d07000748280c500b002c807000100c2e4082041200014100c00300000c402403420060040400d111505014000b9003150103440c062034a80340d69000c680581c8a88102c108043d820700c800300b203100411600130f07409030180d000562a5812800c08030180c00010748290280f004483c2505107a65020421108a000440b001521609054042480102e07000c420080c0002038140f40c07002c8503000400b8243c404d142040d072140c0b443c826040c0e202151002c0c1e07040395540301c00900255031034105412000c15090060800202c1c19940d555900380090f87c0389a0344618010b035020701d01001e504205242080030040018036541c82c107000869221185401018010410405000d00e014000e030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 202596735 1250 202595485 202595507
    0x3040311011a090c03010602120f070c090501050117041e060207021002010516090605030a05090c030a0506150f0907050304051c050703080708071e020a0b010f0e0906040b04060c 78
    0x240080c01580700000c0b1545070340080c0c00506104045401c00b040070030355002d0a490503117180350000d010843c040101c501c0180c20284140300070410400030300d400a00e6502c0f14000806900102240c5541804000b5107d00c0d004000945003200700020400450146100042e81c804940082c42040800e030030100068400d41101a4102e250003e8484815a0541c40b645c40b65260010b4521a05881e600403034900f4120310400f800600244085800030503c2d0b4050307174100206001711800d0f00901004281001c410160a903060f40050302088410542001c1c170050310802207405141404d1401c000503410f10000e040c081c00c0000c044005001c000c810040361300040a8101c080b1070501e14a40003e2095005003030840004404002140c10103000303001c15801f0720101d4507100d89070603481065150010f0690200d404512410000300c0105031562403003400f0f8820030fa103410445040c404551500d400141120b81c07250b009a0411000c9004840c42e1500158819404249441c480e1003ca420344248 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 202597985 1250 202596735 202596767
    0x30603070504020c03030402100f0f0813060f0605030c04090b010e040807050f010b040b060307020a121e020c03070b03040507030b0a0626160b22150216050303041a030403 75
    0x44c142c01e04601c004042c44c800e6100700d421004040e40c2c03110031520650711482102c0030403402d200c0744c0d1181c0c0c0151440d80d408605900350400d802c0c1180c40301c409070b40751a140c00788419541e840912035820244040202e4420644040c002040d960307481c503c0140c014814000683c181c94042010030502404807881c0c07640003000c84e90011080b1030518003c2200b85000341c03281d40782446941550400006507071180c0743c141c002c1c2c518000c568031090a4484040350b02e0040000d0032061072300400c4101110501d14849500030161003a5070301c141072424285401448801c00300344104000250f0008521040d268030858401c1d2907155584e411000d004190440c005c4101e01c03480609a42c124414480d6000301c0440848158003101d40c040d070190700c090702070800081c100b0880040d04204c4160034070090012890140e1903243d466080c828541c0c11314000380d0040c2c22550070b40c52580000304a9030082c00040700031f5444c0c01d00d8081045507881124003846080c810101c002030505006030b1501000c1c81034 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 202599235 1250 202597985 202597987
    0x901021e0c100f02070e040b011202191202090a2a020708030d0b1c0c0506160f030c051002090f0d03121a040e03040305060c160c030b1905160503060307050402 70
    0x2005001030300042154034441c00502c81c80800003500c0c2c1c06c0c0031030240195080030340015181d00b010f091ba00c40c4001d0348001c0e42c0000044601c080034001000d00680204245091001a6540d5104005141d03a02500e100a0282071075054005640d2216208907005921a281a40c816401a059040c281c00f54058401c80c0004100701c0401c00c55a00580e5608078100c506010201340c850021307801100b1503e0203014060354031000e00041c10504001c10700c5e10513086820005040c540c0d514441d4808100044001508a00c529000c0140c02c00c50029542081001035061440c1e15004c204400f16201c1c206100d6000d0f901c0360342c01d1502a00e03041c000d041182034107004210064022038021400030711240d000b903203030013140500c016010007a903041d42c0e482409001c01d03071600300c4c4120142c1c00c8450350301140c0c04201c808400140f01c03041c800380103600c0b0340310f03103070561900f401800e1846800c221480c24075800c24003004111001c41a2182d41007155041ca2500c1c1d49a41d008170340b6095041d00a940c000d84 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 202600485 1250 202599235 202599259
    0x50a020918120309100c0c211214071b050f07030308090304060c110d1406041b05060409020c120c060405061003081c0e0307030207030203100209090a020a120c050c0c060901021e0c 79
    0x40a404c0002364503120303100c055228009103410022204c15844010f0040360713910202e0b4000d0b100e09904840301d00c0c9c0c84144022448103407540e41c20644020460855907010f00c0e0200f0405820007a9a80d002500700d019600b01460404043d04075400350000a01264800400640303ea030344080e0300035101d401c803601d40140c801005485030740c2c030020303582522100f07007840c0392402e44604140389005644012b82024141458800a0006900118081c801d41d001360100b4001d240c4000026000c003981000c0207181d00d040c1420018140700e8090b1120b4003401c81414180003003103070102162588140040b50020310b00600341480001c1c150003c0d00251404000707404020315a0000b030341000d880c000c0701918804640a100e40b822031203a080856013124041c0001202c5200c2e541c050240c40080c0c1c02d180856500002e034181c00c075a1119003190108502142c11040303e0400c2000002c940c0c0155035251030034040782c0002c1d541d50769035030400800320943d03010b00911020501c100c074100d6a01031304c1307040108 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 202601735 1250 202600485 202600523
    0x8030322170c15040f230c04230408070309050301110306010f021509030901020f211b01020f0d0b010e0310021809010306050106080c0403030f0804050a020918120309100c0c 76
    0x2042100a5400710a5500c1c01c1c03829004d03003550100c5941b1020000e244100310841030202a0a4008214940d40304402400607404080c1c0d84140c4181e201780b030307226034a804516001d440451070307401041c0a03a00d03007500d000c0c10003201e01c100c3c3d4204409013404c540c00c5040220492602c00140440400c11091905210b05400d0010242050480036001c3d1074506a10880d40d5960f110720203013400001414400440c000f113441c000500c0140810014449507a000c0710200d400c5e40d1103182c40b00c1d09524002401c8020003058411002514001d1800400201c0b009001907a5040040a407988441d070001d00c0c035051f6160405140c645860140030500c81e036a5a04001740103003001d01c40d15020407154800104002015002c48003613a6041e01d8403514842c0740c507421030360068002c0040740c0350b1040c0310092001da03890440940c481d50000e884210b000b1403003141641410b41003001d000b0389501c14010300200f00004644000102c00751100001c10130340c01c0d5004c0303451603105c100181410300e00307c111034804 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 202602985 1250 202601735 202601753
    0x40803250504061103030906130314040609030309060201180209100f0312090e0405071a2503031112060909011805010209010914060714011508030322170c1504 70
    0x3d0b2401c0d118038071109041640aa228401250b00c00c540d5000500002d145001e205005401c1c14081c0c94100307000d0300b8880e80c90301030380d000c0d030401c1000c666075078030400400d503000c040300b00a004184024010b42c41c0c6005004444080300c04001d02c2070000c200001e2001e00a003400b40300502307500f003c0071a0b09540b824002e14011b031070440000014040c9201040c001000803107140983e40c480002e001c20707072505d000080e0002510101d1002e5003010401c40e540908219010360168000f040c25072030307100c00c07454081e0450348100340400d01c201050014a40c00c0140c0100140d0145059411107229512218160700515440c44403804620b8280150420301805601400e0150b40a80311805038903140c40342d04400c02c9004800781d0340305404115400005d8103002a40b0800403000001141090382030054030b405242d00e800400c2c0c0360f4400f000300030303407826143e14907000000078011410078400c9680b41d00305540da19600441c103007000022105c1e0620000c0202d50010f0541a084518504240c64102c0c0302c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 202604235 1250 202602985 202602989
    0x20c0301020f1305150301030b07170f0907080c0f120109060507090801050c0412030f17010b0703090506030105011b110a0e0f0f0601020d0c030c0f03030209130204050603040803250504 81
    0x2403c1980c60740840c0500388000d0f07803030140c443c403041c0c0e0342168a1aa0741c41c00c10309009001608020100d401c1120003100091040c6c00f40d14036003207200c0fa5142021549180241503406110709a011012610701030b141d0340701c04039820700103590840e18031040452040c09885038072402405070f0b1030701c41004100b652081a44068661b004002e10854807100380310b604a004501841481c03580b840341d4040040d002d00040108801e4605001114050808040d80c101d40309901c040a0303960002081410075521018100160000700e888a00b194105000200807203001450f02407061103001b800000d01400c02d45024011000038080b00e0099110407a842d0003040035600c0340240c640503404601000b01590b9618451281a4020642d10300040b01c02c88224a4400003179081c02441c00711b0502150b80451302c07051281c029100540d4886016060000b10500f00714600b4189105200900495545030120b076002034002c4001510394803000381c0d5903a20150070079003d074258017071025400302075003140142c01 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 202605485 1250 202604235 202604257
    0x1150e150412121107170a020901030b0601181401030207080f0d0b040c0c02090a0b06041701021801020a0803041511070b0402040506010518060c0c0306070206010e180c10020c0301020f 81
    0x440d124941040e00c1d6040c413609040c00e84d8000300018040340034a810325180e5982448200c4a40b4481034000c9201c004080c3c0040d1540c0c5440c008111072940c03c8104690701d01041d44019041c1c5151588401d043e0b0328007000c140c1095000980c06042c0481c040c00da80980c80d98150703c6a9500d04c03103000400508020040e00d000700d05000c0020b8036180101c500ea000c8903000740010f281a5980820b00f0028070700b40410307070391020060201191072504d6034040c080038080f000006a445810340405c0b0070040000d40c5260440d44221003030307000078140340d0699030860383c04040c1420403a071102c624000b4003048895503100c02e0001c6400d07400d101d40840000c5c05a40251410002a16000c0044800d8490544c1340000841400120040c070b0514000500c0c0c42c3d08000d0607607a502101c1d0303001904002065907010016400f900050200e1409490080c1d04140501322000e01d04010601264070754201d0042a40704020030320840100c0c0f80248000040120000c1c0219500c080b01e611016083d00300380c140d12 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 202606735 1250 202605485 202605503
    0x30e0a032f030d260c0a030903110106060c060f0209131a1206040b07031a0904060f290402072a0503010e0706020c0303040602150a0e010c03020403050c0901150e150412 74
    0x411341d10080b0301d24010340ba04204249040d0f01c81c60103801a05003200b040b0104410348540d1a40d810080c0f01c0c1c0406407079182e40d201e00b002e80074141141550b0795000c1d4036030882d20411203070790303c0d640340d800d0020580c01c3d480000c1000c0c0705100c450074100606001340703900181c2c3e840c581d003a00400860310380d100b1480b40800a4040e242e6010490131501c0404546034022803110301c04c2490301d0051140d681c8248528008038800c1a0425000c095802c20b0240d004682485102e02104188008d20f50100c03c41c280d40440c1441160f845034401c04005103600c062100c01e0000030b01c005034060503244003820001c5d00900c48041819400c0750740342864820fa60040c06000350502c01854080308882c212801580100201ea42042e4109401e202c00f502c0f5075120380c0c2c0c0c0d0ba910340002100f8003031055400c01c2524010b844c0c51031818150308112001a015100300c500c0700c0140264400303407414208040c658600f03114190b04000100700000d0344247c0e0414405800304000031b4419034514000c800501c500c00351 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 202607985 1250 202606735 202606787
    0xd0804270f06062f100c02060a020a1b02061b1605010206011805070c0609080a3b0105070b0f0115080408180f09070804030e0a032f030d 60
    0x1070441e0168040c42e0005960191040785040340600c07214102036424204140c82044c0c10720083c6020001c900c20b82104d41c503000703640c000580501ca42e580c0038000303010a514109049a006115540485060000309081941c0005640f2600300340ea030240e454400007013020848426442c0e50360f000020000300c0c4044503001160b25440420010b048401a640014000e98100e600c6c10150000410100c1040410064800410241d00854608a0181d101555070702c0c80d8000c0140120001c2c000c0214002d88441082005240c0c44c61918500c49240101642c25101c400120369900c60100d010b045d441c44142880007207401011980d0407121000611040001680030560702958200c402a000308000d000001ca050101c143c501c00101c002012080c02d6002480000c044c0b903801e0700e0f0400041c03041402c0000f0540c00c0f04a40148440c00c44507542c0981c656601c0360b240c00310719410201e00c00b07001040400c81c49108907046080040c001d05031035018400c0341006100d8850807200d180d01007001500 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 202609235 1250 202607985 202608011
    0xa03020f130e10230f1f03060f030305090906010e040608010e060601030e1b19090b030d020102040803040303030f06030602030906040515131b0308030705360d080427 73
    0x41e012610484401c0944c07101820301507141440912044c1d0304030111003c0754403a030399140c0d01c0d01c40b4010841d440304c905600c4080c004013198010340041144d800070003000e20109400806888a00608444441e919528440120f8900700d98895040e04507003800001300b440503040d00300208880750b0a0031144650707141c60046095070204400a00190807a00d00c403440404050640000100054010140b2103000b80002041080b5a4805203000c2e0307648005076420301e0188103032901129030344001c0d410141011103940d187d01c500d2200170280740e0745080408800c46a50040710095400030403c645174608003058039140c01044500711003602401c149401d410000281a074020240c0f620368070800780d4a9500d0100c0b50034148902d0714000211103002002815030001140b20b600269503003900d40f0503a0440c5d5180101003006210306085140c003844210341c070044003042141c1c0480d2400c00b004100c2c10041e03424460b03034110300c0c0290b4000d0b25200030f2450355201081c1001e011f0808200320041c0240d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 202610485 1250 202609235 202609261
    0x307090e0c03010f170a080f0702101e030f0b10020309090a1404030c02181014030615090c16030e18060d03080c160b18070e0c0a03020f130e 62
    0x1001c529118509050180014945c03404103200c943c00102c0d01300c0203880c0c03111155a008040f160185844c0081c140c021410300e00b405480141003420000c7c596040761969010040349152010101a40d9142c85000e40b000354108100107000074114001d203048004000b9142d07803092410030702900700d0708003054030090715114005844845d01c0e00342d00d03143c907241d40440381c1800300c0c0c6c0d041c2e03804140484141050a89100a54010b40809074202505864100390310400c030510403545200e50440303820000256031a8070318032440c480031100304000341d940301030010103401002d200d9044c90301c203404c001c020107400c41c444140d27000d41280e41505030074410703a00c8001c090084070900e400110280c02c04001138001d94405410604050b0788a01341101e0180880342001ca28170140c90520700c000610040402010704807101d02c5441c409032030018185060f0f1a050300028148107549800028800c0080d07210f9030542c1c0c0040603034010280c1c3e80c00042001803851119020b107204100002000c143c24401c2c100e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 202611735 1250 202610485 202610489
    0x1e07020307060209040603080c0c030d020c030303040b1008070306050709050a030f0f0c180f0f0506090f0702030f040803090102070506030112110f1c140a0201050301030f0303060b0307090e0c0301 86
    0x19005520380070482d41c4078006074000b0120a50410389034a004800943d8440c00f5007000f07090f140080280c011200101480d040c44001180c056402c603082400d0a500c010045a034000e8000702d00c1100b98131101490040121550b02c10039013406400c1c40442041015004680a0103c65035021415070304c510400c02810f4161200400501101301c5040016560902149000e8000c4a1720b603011541c8000001150605e00004042c031943ca8030002008101032081085038041c042c03007000145048404580821701c003806031030a0100d42400104814400c00446072042114940c00741c4843d40e070485150350360000b910480c0580210a004119030a019054a04072031015821142000d45030700c1e8070342d6034588410b5030381d00004452017000c016101c031f0b07048551004c1081041b0504108504141c03480340b10301010300a5507000b030301e11100581c0c3e020090301e06582d080762249040000c00c3c0b400390000d003115403090404403004010049500e410034a200112000901c1d036070000e54070a541005188424 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 202612985 1250 202611735 202611737
    0xb030c1b070e0f280204060207090911060d0b040207061b030c02031b03040314070512030307210b040507080106230301172104170c01080403030c0e181e07 68
    0x802d0004074012a40c040c0640c0280d01c1520300c0b400040225199414624102c400c41c00705500080c08220b01981048400010100740340200240f4407160303141c1e03581118176403180303120b0b00c408106410984d5540e48400038103e0014400c560710130640c60000050702040d030103c0d1003d9210444001c0c040c0c024081c03000c003e02c1a40c099450a0240104100700030260900e04074140b1040c8804800214010458178008944500921000d884d00e820010301416031404007a90703070028028407500039048822458080f98908001c0b030418100300c1c541004000ca41c00882e40541400280404941c0200245060b940240d80f11010210039a600103100300d546a8501c8507107004200400545841b2940080082c008505441082010f1850702441d0780940c28031801c41c00e070000f000c2040181801c600211100180e01070300e0104002300020b01700e07410090014061580710001039035040e1007a0901500f90000419201540d02c810f9418001840c040740c2c41d078811800da500ca55000348070414218411106 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 202614235 1250 202612985 202613009
    0x90b090105100207090f05090601050102070e06040902010e0301020307030902010f020304030203070b0304050f0d02010c0f031803140c07061e0c0c120503121807050a120f020a0b030c1b07 82
    0x40c000611580e99a945900c0d403c6010344900032030081102d0003000700c00c000c001720205003828180d5205092160603400b03075040d5070210320200080c10007041002e40c4050304540018107080301e4001640c016042118881e403551000080084c03168040c1e010415150003030b40c0300340500e042254145d030390341700d40d0001a41c0341d4803074241000003107424802580c0c0030344510195600048200103031890044514640000350b5150400048032503445485608805203625003445000e9081c03c800400c42c0482c403020342005061120040100340660480c0c4440030141b080700d207495540c450003802190284503001201410050300c10190348600344111036130350040c01c192049403400244241c50a503074042220103020521400e00b800400011261007007004080b24600055002034580c141038060b00064850311280000340040500e05141d0044d455004100d101d692049000050394200c2580c07100c40650400007c1191040b0740e14050a05280c0080a028000300040322050301d444650050b2481e100f0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 202615485 1250 202614235 202614239
    0x503030f030a02090303070309140a1503020a021c030f0f14010b0c0c0301050f04050115061d04061208211b1602151c0216020d0305160516090b0901 65
    0x240d680045400c00b1401000624060b01c2d0303000300b030541d0044003042d0702240e46100e00304045030b64044040c8001a00300c07001e1102d03a041265405a070200a20803808269000c076a8000441c002c200f11401002c441c0110380da2121404001009060b104551454082c1008100d0011081e030740200302602d12900004065a07003010303080380b42500309141101e030a1281c110008102d445c2803041c54001c0080f480e1414052030315052450039150b221a1404491014030300802c0050b43c020700030405484494210f00d254441407000502030134640c2c116980c400b110782815410023034588002e01034030610b1101c07084801040c003010b000c08501200d640c48449504c0807004000c034040002000780c0540340112000d5210150003150384802031446101c00024002001c60b40d00c11060100d4100b440801811f40c500210320307009108079120703810000c7c0502180b00b00b181c2054012004d0307840c0b20020207041c801ea994142402a40c4030214649505511a450341c0407603101900c0c043c00007900c4010f00814a2a4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 202616735 1250 202615485 202615507
    0x3010f05150f0a1e05071703060a05130f140604141303050d0e15180f100c020c10031b0813020d0c09090302060a0605010c05100203131202060702070f050303 69
    0x35100d03c03104410000c0c0554492001c854104020301c42e11039603600c16880d60984d02c0e01c050342d40b90130194038075889420700411805070b886c0c5210501751317003043d2200141c1003c0151400003a15031382000a02c40c0342031003141d144d0400c082d0881407003040c0c200c8050000074042c022020240c4001e45404038980500d1100c10007185c001d0001380842c121602000070704500c0c2200550600c00c40400c0103d200340da1200340700d2482043d43e5a81ca00c240e040014000038072a00e6403142d0303200c40c00c4524000080c2c481c245281e58034002d0010701480100070382034030450f50218900600800c140e41c00745901100011001203200d2088402d148903001101013005d03210581c0d0200103540b0740d0786a080303070301c43e000040102e10941076000da141454442c3d0010291803d1100c140c01c00d49120750041810031880d05410380c00300c0c800040c001503141c420b02c0c006036a5215000e02080d00c2507d8203001c0e02e0246c84030420840c5960004540d40308000c0d46d0300b03507550151150202000010140b2604d0743c1984140301c565003031 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 202617985 1250 202616735 202616737
    0x403120b06090a0306021209030406021f060302040507110d0305010506031305010e121c0b0f0904051504080a0206070e060a14040f080115080a05031b2103010f05150f 73
    0x946002440142005070401c0020120007044d0022550f580d0049070ba409100d1080200542000e0b00030b000d113060034280b0b80003e50743c0010310440c0042c2400030802c100b851240d0b510103000342d40c0181c0305202074502040c000d494114000300c3d0384103a120303d150030609203100780720b201c3c16100010001c07032942c0c5824194039003903218100140c0740c1e550b0740c00940021401c2088550380c03184a280d00c2c42d03180d40401e41c82035004a40350f0102d584035400e1030102112590b0700003680740113440443d00c0c1c0f0082d0f12a4108585000314a800c07800411a402013403200340070f00040a0300c10103156901301c0740b01d0ba841c1c0c0c40481c1c80c510000300c6d00c3e07040002032242140450258080e151240c5050a1040c2020f594600c83d180b2180594818051650355424000030403482d0b40380103006c0c4c0040402802c1004c1c0075680c080e900d10070300035082100c4540c50031204056000b8840402c969003941400c82d00705241e96079032080b40d8001e00c1240490740600b400060303d428024010344601c3c142005290400049469070034031 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 202619235 1250 202617985 202618001
    0xb010216060c081b0d0f0f0201050108190812040b0a2307050a02100204171c050405100909050f0f011e21020a0f091a090a0e011803080411010503040312 67
    0x454803400d0b08201050713040002501412480d5924100800500b00c09812408070342044421079040c90010b0140080000301071003c10901d088040200c004c2e410320b460140503050b56880c2c0c20740e101c0c041c0401c1c8100380c0c1106000f5460315000f04900c114217409110740d0140100300507819400311000864840c0588090a0b924003c0e005980e880303880c030f01ca42d40c2242e0041e0010b1451540c000c4e248a40320f10104240401090a4902d003801c241c40c20002410341d0103644178091003410103884201c001445010030000516119401f8440d03170400d980c1c0a00101d00854003403984007880000080d00b43c00a10414009031402c21032100744505020303410700c805040c2c14070041e06103804441440140c4900205800505600500020320ba0602000009503202c0100b1050300c1c2c020865640d00e50b50303540c0303402508803010701c0307000490b81500c03c1031a0140950004030521801c401c0e0a000505070482a03162142c1d01c08c2180440317080c103110041d101030101fa180903000a81641c001004451180d1040390 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 202620485 1250 202619235 202619257
    0x3030c02010b10081803130314010209150304060b0108060f0d02182a09060d0902042a032003070f1101150608060d030e0402160204020406030b010216060c08 69
    0x2410840e18004540d4001003503031100000b6080f142000800c101c1010444016843ca0029515007180505e208600d40d803031707010240240740c1e80034540c409c8960035030407106410300146c9080400002810800780e15003003100d09484480c01d00078050710941c070900c0c240d44642402000e10000704a09020b00010b43c0389400f0032604000c0c400394241541490707080052156071407040800c442d07502c0205540008202501c3e0440e511021300041c5031039036540003660740f00d0404801c00907513070185000040142409004401c90786080400d80c404451403689841c1407000507450500c900c0e030702603050700b0000c069400c58560b500c000340040b03100c1c58440c180d00c0d040c0740c00c603280c82e40307002c80c08032462400c484006101d09442864070004214241e00b140c2410741c8038000301e650b901044480c0d02c015004090099506118550010b13000006000180c00c411030190090011903d0b5034440380301800600c00c15a10501520541c01010300c050250400c00054484680d2071910302c803496a01d6a1b01500200d003050 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 202621735 1250 202620485 202620491
    0x60302030105011401021504021c11130b040605010503010f0b0f2209060b090a090b0301060b0d09020306100b070f022107060e03030c03030f0702070315090614040f03030c0201 77
    0x405680d0902507103018110884086008940f000f002a07c1c0c60600007040110007003070000c00000d84d0301c01514810a140144209000e07160910f001c01c544ea0b4a1182c280d44030142002c421043d01c80365202c50848482a034080000ca600c071001964207000074401e80d80c041c096088203021000b60300d8090242e0b144050543c50400220f00903c03c0c0c0101030880c4074941d9031000c0e1040002600d40d000b118024900c4060451400a03240b0119298403c81c1c05804d01290b111600d621407a1025031040300104400d00c0c5803030300c0c1c04403040414050300003000305a104c0c3c42844086100100701407101030885020443c2e05180c0903060740e0741540b504028005a1380080c417000c0d40c24a80e40030889001c000403240380034003802350070004058168544080c48500070b500601c0700c80c04c004000012a80c000120140c07114482e42c0c1c0d01000c030310717290f00740e0401400f403034007400d11440011180c3c0040002c1c034412002440500101080c0c003489400c2281e02800f50f80480b81402e01003802517001c58588500ca00c004 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 202622985 1250 202621735 202621739
    0x20a03080d020d050109020414210a050303040506060f06040612020d0204030f02030105070513090e0c04020f04090c020c0f0913201c170f070c0605071101080601020709090606 77
    0x4400e41e8000c50061103140b034000440c5140c0301d1141c07142c60301600c0c045200b1414036040c04104001086014000c0b4081c000c8140306000da03054100702c09009011034407c0b28030f01e11040c0b0b805500d039003040d14100c030640f0800000c07a0030380ca800102da4132511005403507182060b151440032920a01c2003025400c02139420080075100d41d44030f000030809140640c1c1c00415222040c4149802c552008168101304001400340b00d41584900c00080100d501c21f280106002c82c071b041115091039001c1509039809440000c03a050390348120f0014104962044004002d110007034102a6200c40303946002640c0940e0565568030a854110700c0e41d900b00c501908140d4501815554400000355225a606003980c000c4101a00c541740462360081d02041526040c41c00780065510083c80c02031007041e1010406010506025642c0c242064624550700544040301d2a0743d02c0303034058515402404107441b0114108140d51065010306400703401040184c3c0284885498100808014020800203c0d030310380c2c0311100 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 202624235 1250 202622985 202622993
    0x5031b0403060606020d14040b0a030b100f0f0503090307060509010b100e0f0105070c050907050705030a18050d0b0c03070c05101409190803040825050615030a0f020a03 74
    0x54800307103102d80000100b0f0384c204400a0f1800031120070b11400c00200c1001807204800020996045a018000c00d90701d54140040079030161801c0b568464210b080000e03108941a40003411005411842d00c0e8403514907800e5104580910044848030000c0e8010450200052015448154080d40f900c0001039101d107402c0004a644445001d140001440c3c0c0009030b103185070002e11411b501e182420301a00c0d10303400e59100101059640f00310351186a80c1c4000500f00d5003c4c008031010740d03034040300750381e66006040c17406801ca030044800c0512509008002140908042070720a51441c0c100407000429030f41c050040700c807030b4402416001000f19260f00000024010004212540d13000e2202046141014030b810f4103c5074002e00c0d400300c907803100180d9100000400c140c2251a40c2103503910742d40766581e0411503200d1044901d4005503c401e002d00003a801c4031405640410f0b4860340507207203c0c0e141c80300001001c41c08a0252a07154001c494100700082207848600e03601c500c040c060300540359507519 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 202625485 1250 202624235 202624237
    0x7020d02010c08030f011410090e04050a0b0c03040b0c03090a0f150e01021207030603210e06030903030405060906070207061803081c0c020106030c03230d020a0201020c1f05031b 78
    0x1240d1040c03020005c0144a054002c00c5440e40880e02611101c446080b82d15004040030103511480c081c042600e0041418046d05100c40c0080301c0c1c018904007014103250220090702e5204580c1910840c00d90808600104a55030480e80241004402800c0d84a0301d61210014000b100104450600706000ca19203110868041c01d2175041c040c07400107803561100c840f820264900100340c4410146082002d00c000f42d800b03206c04401e40340d8003081c20340740981240c0c1510501d51410318aa40620080100601d41070300100a600c241c2c42201503c0c01900d40003100c5a0b6050b09a9001e00540c00c060001c0c00818803078052000d40f10105030955103802d940b503d4800e20796008092800c2042000c1c4000b040c540900d00a110070f10140c0d01c000c000e4945140c90728559000c0301e0200a10700d000b281c0035000d024070640f814803116003543c001d07100140c0c0f880d4000f942d200d6041c181280980030300b554001c00c51900a5001084800c0b000c0c011410040750801103e480c0d0004042c000340380d021000445400b40703118 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 202626735 1250 202625485 202625491
    0xf151f0e0a060e060d0803010308030a060f0e09011a0303090103201908070c03090e19050f3102090c0d0905070e012102130b0616060b120307020d02010c0803 69
    0x1000042d401e420040614190300b00140001e0040f040f8140c6075002a1101c0222811a6007103407040d034403511610308050103004640e0041289004448010465264418131940a401caa80003040f581d240300d0f01c040445d0000c82d09080e0b040c0c00501c010402c0354000d400c44028001c02900c44010103140b001c0410b6180c0110074041c5042060071100403800341c10107213031a000600c90030300080c1c0c0842d40d43c00030031404181c000d10055802c0c83d000304200002e0314190300d10380f140040041c00300e8504032124011151045074000b04591020f51682c1c184916484181a20304801e0b000d00300348100b40e024000f82c00ba0250104081340400c10045071185070500c03501d00c110784128003400d1400e00e010398445010406070032001607e000c400440c1920011151100442e690545003010702d0030162251400616070144515005000064903406003a00491542001d6225a108001200000c0140600321a400c18601c0c3c0f582d00c10040f03070015140000010102c1441454100d104041c3d90340d030320700150015 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 202627985 1250 202626735 202626751
    0x80a170d0b0a030f050706050309030a0c02010e21190309090c14040311010e0a0825090c03060503011107051005060301150303120b040506061e040f030804080f151f0e 73
    0x4e6980281000010b0082d2401008240351060441c2480308401d5243e108100c900c40900542c0c5001c4d81c11079005089084041074024506424001341c0144d0f90200a003580f1100310b01c2c00b036202c400090008100d80c2d0b03901a03825645a40516041c6130512004000c584401018408207000300c01c800090f01c0000c00166100c0d456a04900f0740c040005441da03044142020310400c40e9107018801010001412021160b4102000030301c020010312560b480307000c2d40c00a458080c1000200d80d412505900440201c400a0703008001034804041c80e0001c500076210020244e0b00704c2500329039030818580100d034118030007d00001e200c1348080c864aa00141c3c9910440c081a4024091440341020744101059804142c4007800246008000540c0d00d10501142e10782c0c80200704010b811407640b10003a503003e803030030f2103088010503141e05013002142c00502c0344803020310441102d903410120104481c0071081c07048003030942c60b894890300380a01a01c040c10b24840490301502c006017580e40e44c40c4d130030f020300c483c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 202629235 1250 202627985 202628003
    0x12040b0c010506090c07080a121a0a0f2d050409121e0221090a0305060f2a0a020109020a06030e0d09053a060204090501080a170d0b0a03 60
    0x4003201441c01e44500400c140e12850401040000d61020003044665442d030116407030380c1d40d0b01ca1041c2500c911a00c4103403070300340ca407030086600c42440c0302d10904508010225040079002707a81d0a5090001141409030103182625a070107000c400066480603400140d4200f005502c8580742d101160450b1035614041d506068034002c080f0100340c21500798003000c001d9000d00b04001095500207907650307840980d1045401c180c1c2e569540b04006140aa803141c0c0310041c48004015601e0501c60754808042d1030a070081c85c03800d4040740ad10480e042079040240040c0c030083d07400e42e04c4034141c00311641020f40d014096548414000700140d070b40b890244007030880e5860010300072001c1511180760078541402c18050105055040c03000781c0d51041c8135440540a416207010301c3c40744c104d10741511031220196410703c0d40420401c04c100b0001d0b80141090300d11aa504020607071f03869070155034508040c3d1010300041034000c0b03041c101684900c010030300f41120b090040b0303c030300244003c59868542c3e80d03c180c40c0c40035 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 202630485 1250 202629235 202629247
    0xf1b2d04090903120f0905060402061c0516033234090603110f0d060e0a0e0c0414040b040602090a030516140901170111070501024812040b 61
    0x52505c1a018480d007444820011205e01d5910030f81d54841c09803001c2d12607103000c11500c0009a0710b01045031000e084150030720850805807a220410104c41c005140424108484801103210103009550102000c1022845180c10b0403410401200c0c068404414002c031281005070015500e4402d03401b8541500b0344504404040900a01c1104190401c80401d41000180c1c00d181c0401c00540d601644c1c80d030403450350b414000c2c40060050016500c040c0d8021150720802074100201d0f1f00140d0301d500c041c029158220601d00802003292340c0300c041e0142480e20f450128007c0b8490115499004d03100e01801441d00c480c1383c0000b2a402143e904c00c5401ea401840f04442e050b601103611070040200c2003262801510150010f216540c0c140654030729548005016801d01100750840d54201c030942d03038501c3d034404883c100345010303600c04a030031402e190611130800418400ca620b0b4002007a40b04020b0441c0300c66040ca201441c0c10400015110340c41003a6203502a001c110740100004c000184119549003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 202631735 1250 202630485 202630517
    0x50418020f07110f2706061305121c020304030b060301111b01060f08070f081b011202070b130209070801030201051b0c1002031b030304050703060209180f1b2d04090903 74
    0x1800082c421b034000e8a045c0511003e030513186207984182c0b0400c480c500b030750300075008403189468010940858949000e0880301191074000c402030042d41c1c0500392000660341c0d440181400d039180d03002c51286403c82009683c1000030100c040005410a101c0049041e80d80c5520b00480c410b040e80050001c0e400c082410400001902c4c040b000800d001c0c405444162084c0070703155050035403c0050b9040c040c0c1051841c40c40d01c1207078101e41803598040b074130106904020441b540b08401c2184101d0080c0503c901103103a00340030724080790499905a44a41c0b070b11100703a010f100350b503a41c2044200d8034400c00012040c42d9660115080801030268000c50712807044003a50088030808540d8011260820400d20002c1400420b90105481c0c004d200942c0e5008040c0c0071401d062607001510445a0901040c41807a9182035501030288a640d00e4401494000340210b24091164031842c40b084001741400d40c01e486d0554610000c900032014045040c250b851200006850760102e04400080706007502030100c13 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 202632985 1250 202631735 202631809
    0x19060807110106030b040305070c09020f0702040c0305090604110a03080d020d18030e09070504080f0705010e03010605061206010c020303070f0303060e07120e0304090c050418020f07110f 82
    0x1010700d000303100040c074584400107021005040582007040014118044c411a40d000c5001007030340180456503040c01402e07001094003c2d25089105a0a0010400c002c1d4480c4c082c80340159000d40107041d0380d0301c0c0d03035a51490310041910003580202c0c01c0e49000021801500c0680b809640b5007002695030202d55081104503071011900540c81c148103100c02011903030020f40082d01e4079094400c031840e40c4481c4803e031480c4c01b49074490a40c2e4807032450300c0c012600c408220b00d000c941080c0ca81403911000003042500380d0707010b4010740b9002074080c04464a18907a00781400c0d00a84103041c009500c04c05a00440d055900240c4255918071440052508140d0706200780d030000c0110022070036460411540c0140440302100347c1c0b46003940c070740c407010384070401c02d00c00c0701c009016184003000011020a0040d2480d00a441a0580001e2960780140400c1c01402122a540c010b5920321b4500700e0b0691b42c039030f035505443c00400c1c1c104140d8520a00b0a0b101c1c5507005101800410040400da00304013519009 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 202634235 1250 202632985 202633007
    0x10e030703081b012d0603020406080313083405031509060a050115030506030705100f080c090604150201091a160c0b070c080903060426090603130219060807 69
    0x101e80c1c50005c925900b103009441e0707082110001150018060603031002640134007140d40000c1d6000785000f400003040b940000040081001000f850340d6a0b9a507212810340700c00e8550412501040034000ca0510108418040340d01d02080c80f800095294550000c0781c5401c3d503050290072504031040070300c541c01a04011080d441556190284100d41c10000400310442c003045541c0d060640341d4021402d503503400d014801c050306000c0d00891011000341da005150407401001e80c0c01062015021410720814202140e46004c4e0181041e4075107450b00b920309038004000c442040c1117560310141c0d0030002d40515501500c551401409100c179080c604010350905460b4072800d01840040ea00700400a03081d0540e07168011441d0400040c03503102418008030307620400301c040354580241d070100320810000300142c180118044012410015503c0c00b00c200074403c1c50760482c0d200f10103200050340001010002400c1c40e202074400e64200440c01c280c1c14080d14140c2022021450710790800014640c0f04d040020 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 202635485 1250 202634235 202634287
    0x90b03090304090f020903100b0112091a0403050c0703030c0b2206020c12120702060c0a0503010902090406080d0905090705160b0406020f0301080c1807081302010e03070308 76
    0x124504080d41016503074401c2d442007119441d151101c40f4400302259041c0d0b8141c800150640d850700039034819450003482c02290142c00716189036030018a0210034401c84c81855406000c013403c8182d20342042c4c90580d00104102c01f0460100824103d0290030300c441c01c0103500c2600d41c0d514000c00c600d041c40e0349100081810581c0b12441180541400b000c82c1041611600003000603030340c805c894010341c207100f060700b20401d40702800103510b0000506820040d101e0942d82e03003902d9044d152071060742528030519100c2d00010308140018880c0b61040c0d801000c1b4054010070020300799646111403414054120b28480c04504990070800950404041c41c540c043c01070300e00b65103405203100246034105000040500f800c8038400025003002560740c1118491200c40c18000d403690b03034886141d9a18404001c2541c000d829601c1c1c00d0704801d644d20500b5002c0e5095482c0c1400315a1664222070300301101c0902a070401088840d9525982c4040c04440050350055080c603036114500e1000f03c40d52200030041032 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 202636735 1250 202635485 202635487
    0xf0a030c0305030405150c06041101020102130311090a020406050f130f030308041a1e06060412050f0118030e01030e0c0a150e0f0f01080a09020612040b070305010321030e12030106090b 81
    0xa165400102d207232580254460200001385e41ca4000413402402462030208207802402c0c4007000b8000ca5540345880504100c0341034410f0f65032040d0070f4041e0300941c481d400206800b44406003c2c41c04420160180a008d0341750305010341e0340e030180104075004540c01540420040403e0005100c401440201c13050718071480f1501c5400c04020740040001d00340c1c041e1026908603008511717540c1d15070080360300404140c8401400021380341851500d5064007001424550704c0d1800221081c0003d5400d000125099141e0092400c0103000540180a945411f0610b40c0100c01303002c3c2c841d0743c5288020024040499440207081c50b1240082d002149200903d4410065004d0194041e500c420f0000000b80302883c1540c036a0b11001500c1d00904101c20000754041e1010580d0f02034095100d08483c416401025810003e0300c403410142c00b01e810a00024050010000700f0981156928422086c0d1311524500001c16a0100340786604240d00009812801c0c20004010011a81e0045018018080045201e = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 202637985 1250 202636735 202636747
    0xc030402032427010504080406020f0a080412020409120f020f07030818120f0109030e0111060403080c07141606090806160302070b09150108010b030c0f0a030c030503040515 76
    0x304207010300500308030b402903005214069040030702c40c43d8880c1090f0314000344098142858a0300481d007044c000c000040c0f042c2c1011000c0080b00059034200b03a0b4004408518017401d00004801240010405a0f045603c0d0034007400044d01440d008198014999a60109440e4696009003420107030b800700104ca81c4500402d1001c41c1c03200c2c0c110344404046620b0721035080e040002040140d0500180d403040ea0190400681c0c5910041d00014130701c41c801e80d115183c0340c92101c010346036130344030580042c115404680018002401a248039030040d110040003406c052035503480c05240341e41134248010320f0300400450550380c0c0e200c02107840985494144850050f080c628029600d4030001c10400100c2007500c44110018000c1c1e0440307504a402100c1c000161801c000e08035525000c4000701c0b1190304c3c5160000440c0903043c40303000240b91008028005050070791f402c1200c084d203510706450340500342d03c3c80000000c8010050700021803290003c0c40e02c482c070300400c224100b200e148191402c48410010 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 202639235 1250 202637985 202638043
    0x30a0b06040503030d0506191a0904110406090e0c0412060c1b06020c01060e0c0304290a0b03120a1b0602121602010e0309011e092105010b0f0a0513020d050c03040203 73
    0x327800040c00220400381c58070201c4001801511145050555020300042c011171507070f601c07c1c840d90075202c880704410741c02d8a5202101d40248103d00ca0182c0c41440ca00e5038000088490700148075800440c50004203034048030b0b00901010114401c11a5641d9002950314298002802804010079020181000d5441d00110f84411403100910041200e140c0c5100c07244442e00b41c0305807071354001c141004042d0501d841c01c0c07540010907103055200c4c4644141c00ca1010ae00e81303a08100d0f00d0780140390340e61050452500c40310405d00014900c0441701d09400b8403544011040b00d00079144588804d050840c0560001080a801c403035010b180101e080e0020403c407881640c1010644420200380b002403040403004010460780382a241d00061030020003180381b400c094800702c1c40b4013000c5020700700802551480e90304201a0901d42e1250359041943c644080141d4585110846010746c45408050b20781580502c0c448120b507401c9440c080c0072007012043c0801e5040c10400303d5024104400990005078072500 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 202640485 1250 202639235 202639259
    0x705030106031115070506041a150112020a020f01421206140403030b031509072105010908130506030402010206011a0c0f061605030705030a0b06040503030d050619 72
    0x4800740510700409542d00c2d4000c2c8202107030b107100c0c1c103e002d507907c5d810f0a2030210100042c248560b490709074903c000c40d1114050110110007072405071a081400700c0728603440b401039046610a00e00b507004020f0316541150b020b01034032294180e0762021103100c4101803c40c3d42619201c65109032a0404d051003c1e201580d00071298050314800d038803009164840d4a000000780582d122940413810304482400105501a013064a40080403819510002c07a03a400103407104a08861365401548034900030403a800e04001080c1d16020141c036900141c8510303484560030355117101021210201c1c0042e40c1a01d2103450b806920180a0884580b840c6041a0700002c0d980e00781801000484042010003548400403081102c02c0c0c40700d1300040d1a00150b001d8400d41d100c5904813412030501e43ca96544140c0a8447d0044070311400954a405013180c8034410390740c000b440c8082046411004c10000410039903800c0016055110f8804008180b501c3d0038004e010300b15a0128004610b03548521090003c4001d000d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 202641735 1250 202640485 202640513
    0x601061407020f06160606080c2d030304030b0a0f0902010503041502041509090507030203040f0b070903060e030306040b0108070e0405040507030206030c030f10030c05010f11030309010608070503010603 89
    0x20300e100c0d4845400c1e0001640104581c030300c2a61001002402100c50804038107140c084900840c410441a030b550703920036854036025203021764041c80d1640709081004072403880141e4000e241a801c1050641da0002c42c1c915440350b0800d42c1e01110140810114030380b036000307041d0400c0030107070b00b0b120403101507002810502015100174461600002110000355040e81170740d008040d00180c100c229200c01c540500781c00780b113016842c10141030000291456002c0d00849005640c0010380f41602c400b2900c07900325840d0003819035010024108400004208140200d00101401d070000d141e407030030080300f0070003200d0030f03c00d40905120080e01004400341e041100300c07000841c1610086010f56482c0703011402d02d041900001e500660103c2484a040680000356101c0c2c20801c1e02407445d500c40000c915020b4440d44001012144108401d2190b07502c21404903d800000b400c2054001c420a41c103a03085803c201d9030481d5507076481e10304200d8942c1c1000340d10010b2a007a0000c00040f41161a8094081024 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 202642985 1250 202641735 202641767
    0x6030c010c080a1107091a0402070506010b070611030717070804030905100e04090308010303080108010209030d0f2c0102100212070e010516030e120102091e01030b060d06030b0108060106 82
    0x3c0341e50200309020702e2450290354101c03010b941c0119100d092900041444280d0011420064216048141082c0c403c440402d6000001803000fa0b20308400d40e030a0b03920404c801c5030707150380380d80800100b0104c04d0003550207650359450341140880014003001020100506140403c0094001e001c0405c1e080030071142541c1c030603225034007030f85a81030f825103040104012154225240111a5090550111900d41070302d2203039841c1441c59030b9403100c090a0b8042c01d0a40c60749504511800038440d80a103d00300d2a40718141000c0c940c0d203c060100345241c0c82c00c1140c8005148480b182e030011582e041c80a660040e10b520400c60031f14081d21402c07018504000e0038501440000310b000e2006a02610955002a0500d00303800c84a600c51325004002900e9901d2160052002c110700c55020030041c000c0d50344440e0042c00e00c44416110341ba40f0f0610250042e640c50501d07a4925040c0d40070317240c840040c00c16401c0114040381c1585145081c105107a0140d000110541081d00113010055128500e07451030105 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 202644235 1250 202642985 202642987
    0x605061806150705030c0706020d09140f0a09020a0206010503162303150703020c10050105090402010c1e0b150f010903150617010f0c02032d0c01091a06030c010c08 72
    0x8024039030b42c480c440c02801400754400801c5181100900289070300a8661503030a850110b03150f03a400340e408010324020040c1c401440744051815052400c031084020000a043c981c2065071002c0c92002ca9015a40308801a00100c005000a0504111861603800c010038403201148c078044082c10724907070181c190390b1403d0854141d0501a682040381c040d070000408001007050030030100140007940007442c002c003d400b40c0710740080c400c003680c07150a0480720f0103400178503107598030342c01125094600c8008a418092180303280c403010460031071a0358650f200d0b400301605414100c0803180c003608111101445003030705281c004001d90f030060403003044903408000e000405c9417940b9588082c1034a90000d034070148a9101802c0c031000150030145d804d140c1c4581c1004a503c070028102d03100d1180319801c0c100c081d903050306501c0740051004082c0801c03501e20440342c20404400d0240742036440102086d40e00c4a0b2a0b06070411190b4210783d810340140c000c078010019404040c0c006080c4414256010300321403c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 202645485 1250 202644235 202644259
    0x3030c140f0d0e0a0605010621050c0901230307020106030c0f150c031713060533190303080f0a06080c0105071a04060519050606040b090a0e01030c030605061806 71
    0x60401c040c0064030fa01800c140029a19000011b01001601010008070100300f0758138003c51040307212b4079005410f4018418a8843c0800040d1504100c0b1580c0a01d0800840c2001c0343e40140c0201840c00b404407603001140d42495424041041c1506400c000e841607101e00c0b041080d694904031401d4210f41505089142419504094404031080c4c4080100f001400e010000443d50b607040700b2000e1449400200510b8441c101e600782d1802445409001c0507a03011615041d91300b034000582245d010007010301c0ca101d0351071a0718a0000c1c905910850101d81d001050105040700c4080c49580b0008002080010750b10b000a81540d46e10f01e05d994034140400021410b06208500b039a21810800341ca00f030302907a06013490002d0043c44101d44107401c202ca58030070b01441d040b650007207074001c1100a000500301403c00e0028480d0385e00190300c05601c40e641440009244400036404c6000718000c85452003002d02d50305180055500080569100b01845001680b00e00601d800054012030180c5500c100d01c2 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 202646735 1250 202645485 202645511
    0x1060c03050f04060206160c020306060f0402070c09270305090f0a0914070206070309051507050909041b0902041d0c0c12090f010207060203030f0a09020d03030c140f0d 74
    0x1204000301c00c0b440440c00100400d40c01c0d000600d143c0110b04070286100d10648000701240c0210641c40000e515030401004985140f5141d40714103941c4034001e0006242485903540e07010400f08070340c0b00054454a910401d040d440109282d0002583e50308101c0300c02072110381e4010030a00c1841d481600c81c0350804400f612644610304484080e04c84420308001810b15820b038000c2c2000111440c900501c04c550004040d54401d00590000302d81c0100144450280e010041c102414000c124408001c0e090000303822546c2e40b900b050303029030701a61006005500b6200300c8100d0f40421303001210348a004110030821208001d0100100607110f401003901034481c245401e65070320500d204803a0720f01c00d5003440b0f0340e50b0170254001c11100e0422280106440000001a61074441030701c90080560818400a800072601c81c1509511039076105001800c8401d81c0c0c001402c0f900d842e90184e0000703603203840c1e29608503040b010743d1107681405002a4107001c0241e020034a1441080c4c0442503c0b138680250085030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 202647985 1250 202646735 202646737
    0x150305040c050406091e0b0604030201081306050c1309150b0d0608031305030c0d020d0b07140a030c1b0507150201140a020702100f05030f040305070501050702060a0e1501060c0305 79
    0x42c2100600c01c0c0586551600c01002800e103424085003822041e01d20442a085d5910500480d400040c0246051510310317001034645101c020311204102c0620003541c0001620380c4211849220b040c1d2505891713004040012081c1c40480d040011a00c2c600403102d00f801d078028401800312042280110781e54495010712901810725648554243d10021807050608001021464262002501198107902c80319081000414103100045e41081d800100c600125101d100416400907050401502e100c0150030740562560015036031070000381d42c0701d0100710f100c1d601c1151038102d419402404602d168036900c846071541c54074828600380100c200c9074006454004c2d000080040780040c0550b41350315052400801079072090404900c40d1a045005001080c001c4c401c0c00c8107100d803999005d056a403240540020824082c10680610030306200d60400201c0901034280710364080c0c1e002c0c1895041c81c620b171b01b0a48400c4545018160403200200c40d503480fa1401950460b03080b403030040500e1036141426907103 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 202649235 1250 202647985 202647989
    0x8010b1b0706080106030b150406110f0d030209040e0606030d08070311030c0405010201060b0301032d050a0303060801060f12080f070f030309031205160f0e12010501080c0604150305040c 82
    0x2040c0141c5500040d01c0e5000707152581201d2640e00c0910840140c0410864585508451702c030704460300b03010620850303102e148540c151500000c1142d501c24045020b00746400c880e03140c110000303600020740324014141409034607071218449000b40a0f905040300000c0c2c50303c0f83c2d24401d80070402c01d071001079005840b0390019014000b044180564a0402007400401070f400342c001d440c00356017045800283c0c45100000c407412260043c508802c1c01c00742c1001d030810400220142c001d03559400c64140041035003803100b145941d12136140021050324080c807990940e2500c3c1d01503c10320000e90002c005c90444240e004181c0b40c1d000c0e81e8182d9480da0340203890030394060100080c085041c100401800c1641580c04001014080d0701d0303156541c01180100b0041c0c50301111845000e0600150521505004154003800100142060b000c004100c1011a0000744519425821a91544010405500c091101e5407005800340d51aa117010309002d1004000380c26180791108165a68001600380203c0240585c0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 202650485 1250 202649235 202649287
    0x40e061f09090b011a0a0206011a040f170705012c0415080a0b0a06050d020d06200418090b0711120703030c1d090601030b060f0c1507020d08010b 64
    0x101d0342c5110300b09000100824000c0f9003040300044451004404400c1c142d5990100310707801030280d0380c01c108003001c0c442041800c0100e108018013010409103002c0044c000501010310414403084640300781d0b00d1400e0203580c40241484041c1700517244401c1a403140d41844203100240704450382c104400311b002041160041e1501d50025a070105d011a000b0a03150b10850241c060150680c842e429288122001407040c6030341704400410000041c18000101d0710098040c07800054944500000300140707107208030480a0050f0002001c1c0701210701603d1182144600342e40820160006c2d0b41d03000358200000d00800c083c4141c0c3c4c28803821508081000354500d0307052522a58540125281c081d01801b290559413000c102000320704010600400f502e900510301c010110741035a05d070000190001e143d2600401d40002003081012030003440280202078201e120b100500c00c2c0c00b40004c01d84400d0001a04000440d040303040350100d201c0d40400000d064030360004800d0307502d801440b54620110790700c8010344 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 202651735 1250 202650485 202650491
    0x90f01030c0815240307020d081302090a14190606021207111c030305060f0f03060403050a020c040207080403051e030304030323040b06281806120501050411040e061f09 74
    0x3000c041070005940070344801d40840708c020034071a9090310b6005084074100300e00350451a50001520b0b080d0750044d00070201000008114134802c08064588104880c40b00216042015003600b45e1418800c04009003920f2003d03014500621412103018815203a02404050032138850b411659961140510440300d803088a5030782130361701e2802030064007088604500c50600001c182c246400c0035414207900e488000c0150449a603180e4051b203aa403c600b800e9001c5110b0803844000c03589403440100411409260030940300d6246152035480c10001c10003000e0b040b0002d900358000207000005898010b907040c100856403011030740c00754a151010f0000600348962500502c018042d0101850b80252410380d05041400307083c07020401503c011004072a44681d0700da004104404030581d4409149685c0c4e203000c2400c0d956500d42092420200d1004d4445035900c506001c2044000000c4080c005000d0340c0c00e001c1d0108a0341e80c541c540d40c00900c0c503940004a4444406900340420014014050312a010 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 202652985 1250 202651735 202651789
    0x70c08060117010506012a0320010e120c121e1b07090516140415020601061e0807080a0b03010c1223180304030c0605090f01030c0815 59
    0x1641d0440101d002200b951074940072913100e500c50300c0560260b00b56002800003400301c2002804101001582c00e40400c60365240fa056456800c140e03045d01c208500d0000304540c11080c6101d41021400d50b01c01080c89410801d00c100b40300c0100307070f03202800030381d0202544901d11881301c43c0010703056042c42101d0b00c800250450322545404044004586800100c0b94034645410346501100c00079514918003180800b001c100c16403281989a4240380440c16050038165504114004483d80e042c2010150b0461801401001d41c0302c0f8070189a400041420700030840c01d01c1014100000c05482481044442070018142410641022420782c901600030002c540c51755400400c01012945004400f07401d018028440c041868a151f1341da0856401746401034981844e68a11000301c003080f60802d0009010000101e4100c100c00c200500c096290710382d82e0100d180400c4880e0035841c8445060600d000f11004601c0d03403044001c1e90200e40065107400a12401c00019165070700b4140c06d28104002c10740d2 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 202654235 1250 202652985 202652999
    0x60c01060807091a0f0622081914120a03020a0e152106030c06090312041202010f0c03021b040207020a230d03020312040f020d0302070e0117030708070c080601 70
    0x8000030051305400941030f5801d5480070030100241c1450b0310340c0c0c404402d004c04011043d180c20900b00400000e000e00147c19510200e803401c206c18258035080c2400c0b910300c60020f10403544014045601e141d00940004014114500b0240c000d240c000c50400d680031075814207243c010801200950307001800a40f0218440040144585c0880080d5911600c40e02d40654040302c0d01241500502005020340300c202d10950500890350032001c2131640c14451400c610320035618000013030024108162516209003803034000580400f0b4003440b40341c10040f0055000f00400c1e400b003080f1920780407481421f00c0065440c00058044c0c0680d075400703540071030011000075030500c10007941e41d481c42200c808030701501207240c1040f00e0807040d0007014016802c1040b03248403480b5003101045d40984242c01d0a00701396210740220b4460559084102c1c0076078041c0c1007e1050920b0307051490b00404c0301d0401d404081d41c41000040c1c4a001c0c04000410034403020540307004000c8003111707100c05403614200b140c40540c0d60b045 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 202655485 1250 202654235 202654241
    0x5150108100204030302100c022b020c0f030607030b030c060f040503120a12050601050d050108031c05011203050702060c160f050603040209060105031003020301110901110c0f060c0106080709 84
    0x8100c449500c202250040c0c0311000e8003d50342200c0d059005401911505100c03040074000a049120850185003050400081624030822041c0361012801a83c03020f5404044c0c6400c1c4801c2c4050300c16000080000c9017554005202a808012071501213005501440880d10700786040c52601d40c4000040350142c00c00302058050021074008500f02d40a08000e900b8400b224032992005400165151520550104180d004140c200d88189010752800c0003403094070040382c0c000e0b00002c40603040080c40b61041d0101824401105400342c0c410405945860400041c4090440004050110100d400320565450340b040d240303440040f0041d0390321107000841c12880305c54180604256841c0e490004110313400c0c410107607031185034041c4c03000780592140780055419410081c188800c00c80425404001620f0a0080200001c50030a0b410349034130151001400d074030384010002000c0d0380410900d905ca2759951500e902540c0d000d0390f1290b902d00b00075614174003404540e0009001c038840c0c0c820004030041c4640c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 202656735 1250 202655485 202655489
    0xa02010902011404240210060b09190f090f0e03030103060902150a020c040209040f1e0b0f13110c010c020304030c080613030323240a0308160609051501 67
    0x66140070048560f00468545405a40101e502c0b00b02101004041c558a9540310314a0b00c460703004607640407504111020a0f14015004400e0b4418081151041e6060080384810910340b1001d0030101c7ea410428880103c0f4094840d203101e42d911034030070f1841080241d01ca80e6803810080166070740d0f582c40b070415101801890000b02d000c1c5500034440b89807140c04100351007119031071707501030803011500e2800c01029400001502d40d00c9640c0304405000204184900366103064030320028080300108214403400c072105a00814015541d40c8001140d1b40c3e64030701c041d1404143d0b1440013580006050180c5d10301e0082180102c5a03600e0151704512042c0c0002c00b40046912559090440c1c680329000701d0748a4400b80c900201d103503e02405440001d000c0d4226240b01c0e4886400c51250a88074030701220840310a403020034001099224038140e070155510a422141e0342580c20901252a694840404c0e108200080c10b02c0560800501c0400005410100042e074110084449031212004a01e140400038 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 202657985 1250 202656735 202656737
    0x4020d1b020607081e1015030c0e04020403050c0603100b070606050f0a0302010e090403031b180801090b0408070c03150b10030b0a030204020708090901121b1202040b150a0201090201 80
    0x980001818140300e0904c1600c80c4000645031240c0c415528000d0f541d16002034030324903400b00c2c544404903491111810f040d1203282665400329440700301d440094000106da24250b4050f6004010610102c0d200003143c046105083c0c0d8034540d25074a07400c041e5441c0c2e00e10313044032140a40009541d014088141c12940a90707000b103508001007007402041020b03d42891200a000c1111540f0101c1245408140301c0d500c60b0080c1001304400c145150724a84903240307803507800040743ca580d00080d0300d0314030001e0740f4020f418000020424407010f80c9449407110360040c0000e00e2542c0c0080d8110400c111181c070f2800031a4042103800d524070140e1a00c0700503114582020b80a0b50009807d104e01a1281c09050030507100a451080824190740901c0081d40c0301319015540302401300b108010944030112500d008208281000c00b030409a8501201c424100761380314107030500e01074130034855499002e00940110b603040f0b0f40050100107610114100d140c4026003034481e0640441c0d011100e0350107410812901d0b1003 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 202659235 1250 202657985 202657993
    0x1507030501050a050901090506010c0203032d030108031e070605070306030308060405010f06050c0312040c03020108070212300c1b07031a0403110a060f06091b0e04020d1b02 76
    0xb01c0c020700c59107005620a2a5101c101c18004000d03044044d40086d03001b07141858500f0010985801181c0340d940b2080e0300c5500144a440f034642e19050340d8080141c10071018517224619450f00742003e5403400b0b0100b034400e1041e002d03250800d0016580045900d0715034489170502080c0751426018006081c184020303030109030351000017991403502e8800e86050f00c4640c0111840c06040020032200c980002c1181051407204100785c02c900c1d0721303d002e5103201d18498018581941d04602c001010210301601e80703000c1d94802c1580c2c00e4642d010b501034507840d41c1c002e4031105084124000e1041d1001c2014400000c40d41d01805018500409000418cc030071044132081410302104040700d5580e080d5440b014258401d07000c80d808101300c1c004500d42d0003901034035000c1c081c02005034145040a20214080b14100e13564000041d81d00000e004840090038041c904003c00341701c0321720302810711190f0b0010008004603c82c8521140d40e0ba0385c152009408954001c00c045141c1c03800b201c03c4280c00440c10400f41c42 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 202660485 1250 202659235 202659239
    0x10609050a0902030d080703090818010e0105040825090f0608160501170405161212110c2e1d04090c120302030f070809180106021b040e1507030501 65
    0x9402282001c1d0f030b0103001170140f004015421070b40241c001c5c02d444101034841c12008045024070025054014022440400b45115000094018041c031803049050080a01081100440115550205d42902c024450054030301d108260741c04081e07a080a01414130703141c5c1c1c416035520154408801d41300d407501201e4050491011160412000384141c1d800140e407080b500500f51055a01c081d003041c803500440e0054441c41c82d1542800186070031010345492100100d03c2445030158201642d0040350414004a09a8004081e140d40d003000d81c4038028040f103103c2c445500748856040440c984a0003c00c0d03080e100c00c1400a00c0c428020346a0f020185078409a01d205203024444e400c4080d40c4503010050417842e080f12025081c10700c50781034065000910100203044a40310040400903c0380d00307441d640344284020089982c02044c0702078406841c09006105154002034107039001d0400240c464000d5084070b0000340a01485808614140206024402c4240704400c00038042d903081e4509011744c0c1c0e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 202661735 1250 202660485 202660501
    0x301060c12110304050111100c12061509170c031c0305010e0721110313230606011d0a06020a03020d03091214070b010f1a030c03061005070b0901060905 67
    0xc0030b848a01d04083c0c008001c200a298001c410055a0600035402d07030f28413007154a100d4003256004409140801d01d1880030108040a51041c0c402419102d19540c020003140031004083c0905c1b030140c4103208100b0003000c41d4401c002c018034010544020110344c2100d04015448030400c42d2980c0c0359000c213040100201e00c14203a05480c500c03440b202e82d1903083c00c00700e0039840000d2200d814010a8010341c0c41802420300d4506400542c402d0304404691190043c042c68020109080540f08200c6004d805111001846012803030a0300310109180051000400503101503030701c105014aa40d00614200d800a0034540100c1c1e0b04d440680603400340c0c1d0440044140a405958075080c00408455009600d80744017400756680da540c01c0201e12885003014804e9841d1045006c00f80c000c441c0740120410300704140c4000000d0700320070390742c0044861f045003400d1803622014000a080c1500c41c0292a0031848503d00c54400d640b000c64100b1401d200340c1c10110601c50003491540199003d003400c000000303c0003 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 202662985 1250 202661735 202661747
    0xf1103070b07141306030207020f040203040201080114031204090c090602150604020a050d1e0c0504120f06140f09060c040602100c1107060302130905060a060e010c080301060c12 78
    0xc1034101040c4000c1d95030b82401100c490705000c40100b669102400a0b00e407003084603071250040d102680300180d0304c0c10203004000b1480a4000c58a11642c010020080142d03404030102c2d0440b01a2021000340040080002e420441d440410070b9499801250000d000007041d00220900300c2a0b0301c4185906844940c00ca03190f0230806a1007032090840408540700b410f241e401000c44903294178049041081c40c40d9000f0035101c60002131141103d98040c1900384402c280310f040600d5201e81003d03446c1601e411218803810112030400341124201081010a21172142c12180d06032039062101c0642d0700d803403d400c3e41c48500079505035895100d0341000402081c0007400326002d4840c99002426031a0380f40061001034090440d52004200d40c0d4903050204950800c4004040e01c4070342c0300982c440340300300d000503001d0445511888040341408140181600c880c1068001d80788240340010040d5500c00c0141c1b1a186100002820044000000584254014103100301d55104130310800070700030700440407940303 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 202664235 1250 202662985 202662997
    0x16051b0405010e1305030403020a260721020f0d0f060c0206010e150a050306090d080a02041a030c13031109071404170a02060a030605090109020703020a080702060c010504030f1103 79
    0x1010604801044e4801c0e100514079003198031600c1103e2030180c490380031441080407a4003e021000300e084101c0e00701c251100401d0315680b03410380100300007481d110300c221b0546e0091111801d070341201c0030034000755121251001c11a01014042c81c801400c1403134002d0459003460300682e0307400e280145280c000b07032001c5061412070300840c26101c3d040e01c80b800074078101101821a507600c11885030001030740b43c0f818441b00d0b12a0071840060320680d03800200242206a000b405c6481041c8104801c0c840001c12001b24091401c01011305522641c41d4a24a0042d114200c06240c2c40001c2d1760b0004100800700150012220f0f003607c92100c1c58444950a4900c0c1550091340c8401a00c180700920200c0502003100d920341060710102c070b0854402d6004507506034482d190550000342c680c00280030508022011b54014a40e02108601d00704150300d000b529441c10000080140d90002003410542d507031107091301c40d980302180c000c100ca410f0038034018101114042c00380380400c000604505a00f038012054542c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 202665485 1250 202664235 202664249
    0x1009030f030305061201060b030a0b0d0506160212041404111806090d02040e0c0315010b031501142d0705031b1c0206010e01090c051e16051b040501 65
    0x1490000598081e000b4040c02441d241c2c20a21300d0038031400c104d501f4000c500040c03241940899030390074494034080a4a0244011a0090f00300501040000d80300003030b45507100b02c20240c009034040c0c880328100c7c10040c2c1003240c640780680c04107000c50540c010005040520304221020420001001c640117070900030100e8060100c80c0b00c41c42900281081001002408401090114000c14070b41c001403c03640101b603549019807041d41052500c0c1010051b550f40e031160002c4240350340d0f250007241c01041c880100b81e94486840b030301921410340d020300a441c1c110685d0115a80d111101010700c4c03180804500380292102d080501c048001d400450200c501c0300f0340000c0654645441200404101103081d40180b50030310804900a06e0808810300c0c000c0f10248982c003070600c0394505051440d107054181c02c14645180b5002c240304444c0e03000800c5440d07008805d82c0b42050144861802c9007240110038035100c1c4e001121250750100000440d50490100c0b500b0441c2026449001c1800110f401c00d00a0702 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 202666735 1250 202665485 202665503
    0x8040510172202040b150d0203010e06030a020306130204090b0a020309060a05010f06110a061b02070b13050103090201020f1b010305100509010e041b090504200f0114040320100903 79
    0xb005818075400500075a5400740056420707800003032084e08158032981c4201c025a0703001c0018080701808c1018250440802c5000300510115900081c6e119640580180001d15504101e03004546542d00058200ca40080149800303140c1042004c001e0f62040310f00c0c01d00c6000e150000f4010040e140b05903410f8070340102d030101100d420180255121419002100c41901c108440d200000c0c40901032003501e40c03044240251a080840000f92070500150040b080112040c0880300c1000b040c9421101121800d280c00b00e401219800140d0815810880310b5100d401044201140d98a04d072210341e440410a81c1c040081d5a1580701c80180e2000c80d008641d840f13003840c0010004140010724464009000781c1070340310140e030b4030990314504400300d912070454907071920304000900c40b22410100c1c03510b801d0710420190030004400101d4803800d550110341030001e02d0701d060b0718030b01c00b84007a50051544002204880540c400c3c900c2c100700700410380c1c94801d00c01c00689482c914400c00092040348d074040c05203 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 202667985 1250 202666735 202666801
    0x3051003050319020312012d0e1914070206010819020303030106030b060c01020a020606011403270a0804090605030f0f0d050706020906071113020c06040b040804051017 74
    0x40e07803501151030320328804c6100034810101d0b008002941c0c14020090440500200ca40350f0303c00214445203010b00440d110030b80d0308100480f074001014aa03100300c581c2b8903600305004500d40c0e50005c02d541c00407041c4000600e01042040c0e40c0000d171481c181d504c51001c0b5044659600c01e0441038210150009416400907c0104650b81c000c1e0400003410a0007410036003130081c00318100e801c980048120800607031020040c0031070b42d6000011104102603106036103240d441c1084c080b00000c0c07403030110128051144095445084400d000c580c10980c1c0c06071905d030340c3c2c95462a0074800f8018a000d414464019545548100b942c001541d004621a400c0605030230884071409481980040d541618541d03000c200301d85c4140e450170000c01203e4422546c44244001101c02c0c00b2902200c0218228079920403c44601d16150000f000780c0e2241c1e104101462a5980303180250150040c0e0f409240c000100404901001d500302c00d6200e05a1500c0c0d2100a4980c2c1307079161181541c0c44c41345105030888203e104 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 202669235 1250 202667985 202668007
    0x5041a04020c070312020a0b1008032b0213080106050418030f0c0f030f0201050702030c03041e0305030c060a0c020102181c080408070812030105030d0513030c03030c03030510030503 80
    0x5429810141c60666a201c0e903aa10351403850303c5045c000000680150038043e040040c2200b44641001818440d0f01646050041d42c6913207100d04a0750b40c0007a00118001314181840b000d01d96000b628000056484003010240130800380228000c403041c81d424003001241d40d040c02d101ea01140441e00300c44510040103500c01b551000020311482e01000110688000403c9911090807001d03840b032b1307079203e58107071940d00000d00315080501650119001002020b42c501c00000c20f8400303560881c03400350305c05111130040610a00d00c5910082003400045134078a0b5a002c0414100e12072900e400d000d00656400c0341c1308908030320441e440d0004640e580c62184d00f007030400c5055400800c407040351900c1c5128460700d80c00000e41059014081c3c80d0703c0903106008031003003030214010015041c548542554148000030303454400d00003900d403c0000100d0301ca84200d045c010180015030300700041103001d40c0c588c14001c0000d5001c00b015008681800081500d002e1349109086c00c403a0440055800c0203c0600303 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 202670485 1250 202669235 202669237
    0xa090b2407120e0405070906030515030d12180803010e010f0e010603050c0c010e340b0c031902150112050d05090604030b100306050903131a160f0b0105041a0402 71
    0x750b0b0303001c01400003030540b0580c5841c42054010a02034440750030b02d514101c0e00034151000140303201009a411400805c0c00d440008544d180100507081121110a000400200410300b94070056504071440c2d06400900038000021030688550101c040000da80328550200100c001d4894072402000140041005920a902c41904038201031000381c07a00007901ea15034252080e620310000036030071083e8031010000700b841c56a82601d50000b00c0c0e0103040340820031070382e101105228901c0700c8600020143d010038024400c031401542d0505201c2600e5060580082d07403452030004486030151004004a854500070803d64941c55200004001c02d00d4141000c550a421102409410030424480400000e54800b180d600c214240c4034000065071640c05d010040e41c201910340c150030742040060100a619000d1041c042d80d0601c10041c0c1d10601ca00002c0b42c2601c212031306440c946c003000e080c4a040081ca003010058050286100d49226602e60081208a0307100514046011041800307403285801d041d0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 202671735 1250 202670485 202670513
    0x708030f0f070c050607140d0f1d0d050601350a110609040c03021806121302180a050a0c020115030f02030c04020309030a02010e06070906110c0a090b2407 68
    0x200035038005581d51404600340e03400001c0c0840340b8103003102a082806804100523154040c1e18a0310185210602c000948021100405400c2241d103041800b071154803007000b80707140355a00400325413666070f6a441c0300c03010100521030704034094040140f0010800503000c008045100721009040b1108031aa40c83c1c4035220003000d200d4201c6414080301d40300c0c0e9564407410081e500c2940300540c0c2c904003000c9080c041c01c44007080c1031140c20284a6081002003038044140d0101000c1d0100a6814840c00055008805981900705401170ba03070404c1642056504228000c495000f000d01805000c01010303426114070300c1d51f1814050328000f003040420710110014090b40e001800740e4a83c400d03180c02240990348100e9103981550f20008021426590900c02c0404990300c12001d0034050800420003842c3d45c0f0386116000400548402d03a82c0d44074401d2040d00d040e5940204541c601c55560002c0344003504400c91107910648041e1000c030807461010080d82141c140c0340400f10325144955551546000c040303 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 202672985 1250 202671735 202671743
    0x4110a03241b02011a0406030b060105030a0f050106110d0305090c010509060903060403030b1e0102030403060e0c040e060105010f020c060a050a020a050102030c1e0a121a06030c0c0708030f0f07 85
    0x9072003a840210301c2d000e088410901c45500210f401101910f049520440c40452240954900306040003c034880d5080f10745c00610920f00907640761038502035035010700240641500705624103000000e120380c105090030071740e142030402e035100c045031b00c24150201d503002c642440305a08285840381e610341c454002403170101001098181810404404207260000480d81280425070b185070003031503403a003181e450304d400c101000020202c500e00c2000075102d00681c0300041810361600100270180c04103201c0304c03607141800390041241448010145035902c00038800c00303000c03528400711800d03654400300308545a8a0040c1059280404c0c1c501d0803280f99000361b05842c00c5005030011180014801e0000314001d214949400d80c0f03850150034441d2004008101c2145886010042e0b40341d09030700030040303002c4001400302c000f075407400050880d580000d03031008040d0b120398008104030005824801500c8225a48400c650001380c0340d003000340c1d0364450b8104140503003006015005480b050711008003091841 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 202674235 1250 202672985 202672991
    0x603150807030b060f030a0804051c050d080f06031603020904050724020c100807031e090f0c05041404060906020906070609060b100c06050c0c120304110a0324 70
    0xd1004100c0c10010642c20898548103404240502071408541410400200310f02070041041c1c140d4507040345110718400e00e405030704a15805040b02130b4850086000700e8002d4266900110705040c01000711108907851940d189491021956a050000314100802c065420b010803030350464080042c030030002841280c0500c1910404074000c81100780300410314100e02008029800da020019083c0416003414500400800d62504202503201e040e080e08048a4100054424003010b84180502004451900d20908003150710003001000c04621800030300038444000d01c0c2e52208100b0041e50f141c40242c1e00380821010205001c200980d02c0301d482140305031401480e08040b44003062040c0c11000c001d840080e50350541c20280201c074050070348030150495000681c1001e50101421905d400040078101e81d595800103943d1070782d60f20803201030100310000c0715a51010b40c0c0030080b02e5482154211510009824492000d05101c0a50b90983c0c0d840540308601031925400f0741065850300d0f44220030346407 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 202675485 1250 202674235 202674239
    0x70e030709020319150311010314010e0a0e01020a020c0a090606020616020a0605040804060f020c0a12020609090f090709050c030a0b0301140c04060201111e092101090218060307060315 81
    0x1902e214041c0c0c940001a00c6110172807460070090304244103510114149824002e684800c030015000160549445141040d01a00d42c61242c00c010074420324807a60795032000424545158000503070f8204807400b1900c0f202895155000d08059a205124104c05644a040820141801800503030441c800c18030490b90142c1c5d1603250700c029503e054034182e134803003000242441500d61043c02094903088900003010660203000c0401d40c3d0b40c00611810b2a05092440303048110b66501003100c101e080000c0005006060415035409164001c3c1d80c0000e141c80740380c02c001550080d60090300c0c820300c4452038550031560b400b254807025101c0050b51581c19580c4444985001045000f001e0007a01c504000903200c40c20404082d00312101495020170100782401300403c1c4140000c8040121001c403009145c940c41e0b1607011031a0000032501842400c0e0059441020b03841c0e05601a4201e24003c1341c0c064001000c00b00e0042908409440154150f04100d40900415002760040b004800d041c58884411507 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 202676735 1250 202675485 202675531
    0xa051c05120c0316030510030b1b1b01060f031a0a060306050a0e0d09050a170705031e0c1816020f030711041406010807080a0b04020c0105040605070e0307090203 71
    0x81d000c807a04585103501106000000c15460003503540070400341820040c5080000341c10680403d6031000410b80c8981a0019003104960801d03620b52441c0400041d4480800f60b407400c0c010303000c0321081031b815072808078006007004180e00b044c41100d41048801038421441c0c91400083d890050846c0c41e039980b1518000000342082c0704141c400c2c001c43c50001042d4490031001401c042402d9000410000101e070203002903699a840d8200720703074100034030a080411806000b41090055400140e15010310300301074100c0d1149600c030079140024907041d0b03511a0080010025110060b110818042c110fa1001840040034a11041e41000307050044235a505d941c8202c0a142d503100301c070308403000051400c1d00d83c03060800e8041c40d4507103410f0868014051a01000090006000900c030004109001010640800c03c0340e108604402010300b0941d80d80020f8400140a0201520101c50f000d00d03003400103206074808c040078003190750300a0143c05201d20b040c125401070f40000c2c040c1c2110b4503140c40410740342 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 202677985 1250 202676735 202676767
    0x150c090e09030714070f0b03100807030b040510050f0a230a02040e01050906063c180306010315020c0102300f040206070b04240f06080a051c05 63
    0x5080c2020045030b0715483ca1400c0c000085640b100000c00341d00051060101c0490040d0107404c4d078003420101074aa607141a01e80c0d80c606115130010406008000f0048184004040c0007441680180c080300c3d0342e94003031080e00c4122a4104e400c500f08c203e521000c600c2650894100540e00c03041c000c40c0814070142203030000c10987c41030342c07914801c5a0001d01044207925410015005100444102d0075501e483c8001c16140c1c481d806121500426130b0920740c10782011011001911680c035074200150050403180020154442c4400b0003202e002c00038646101d140004445050303c1d404140600d00307404161083c0c002c0e400000ea001003d5400344181c0000c845801390045081074a800c0725038014400d1209480344d0798024001c03482e0f007182442008056103904c0c0841d01031740e500c0042c01c90b203940da03400c000d5458138804003200c400c0e404242c0034403503c0e490341e084101d40311609a020030019a40701b901329070b184810840149241c020483c08880d40d0050030110900007103504040d46440168503100c131503 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 202679235 1250 202677985 202677991
    0x7201f090507080d09050a030b04020f130203160306080606010f08090f011b030e06070e0d0312020c0c0103050612100f1b0504060206070503061309051e060105030f0109150c090e 78
    0xb00d54051303d08511000d50011aa4000340000c0e0349010307403142152103454640358024006401100c1504c1101d4844d2190b400550580c1d40400c1c0c219141d04018028030118400356202000081c1000c0c030225206070042651409814140c4900446520005080e20301aa00400b11203990140001031094102d0a01030320030720083d0764240b03084c1c0e00c0c1540c0016003140c0910600803001e50144c0100010030b0b80140e014803284008030b52003000032030075207012240050300c102c07a48101170002c21800180c000002c0c7d40440b000f001d17203051000c3d0782c1d04424004545004680f000313640e40b0950408440300d4840c1d1000035840e03841e0001088404020a040c040e10099084070400200d0016007089956418040a50000c40601d4400c1c510305100c00043c0c544041260084c40d49581c95480310200282080303400c03c01c00d414410200740072040c0e09519200d903c00d201e00f90280c000c1c0500c05e44280c6062095001440d07101c42a030040b8899804008002c101c0c40d05040e05002d10440081504d0f003c04910601c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 202680485 1250 202679235 202679249
    0x60f080a0b0a0513111f120b1c02010c051905030d06050d0206180307180204060207080c0102280209280b030d0309020d0605040b07201f090507 63
    0x40c1151091822071103100000300390140091809041c00b00481070b001150700d00341d41040e090f079503964220307002402d003101c071540b44c01c0c2c80050022840c65a1385c00403140c200311a0b126404010806002e020710020600040030a00c411041001d680b0040d0b00a03a0180915405201105d04020015840c401101c40724007090782c1d69800030070307108002c0e2558060392019043c01d0b116103113120381a50120700e03d4000c5440201c005044904802080e031802c100c4240140185045a88260f10030088a0700a500c58012400140a0808040f5a80f40000b90341d51607241c060740100441d0a50a00c0c801030049050411443c02c54400d03809009603075035050b6a8015048007000300c40560911203864249a184a03079801d95074100041d8080c140d07004500d6048000c0d150801143d0410a4400200300ca05503500050100d450003003400180600e0b22019482007240e03449030b031450000300c440d035000c402401131a524503030302000e42080304a20307030641c0c03440304100c0640115043d04550b40f07182c01c001554201c20 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 202681735 1250 202680485 202680493
    0x607050604020a0f03050a020111160308040501020115180e15070f08070f09060807020c0d080331120e0310052205060612030f0304060501030b06040212150301060f08 73
    0x10551601c0110000146061050040c2d04c0c2e00d90356483d031b20341810000c00b03810702c100c002540b1070680080c0550303403116150b0b403041c0b40c5503078603450100400e81190003018015803820721020101c44015104005071880d42d00b005000700092041c80019117210403c07026640106489030b003031215503441c01400303140d0a031200710080503245802441c0c08401043c1c0010011a1000302c10400c1c0c209100c032056070800d1410060a0b0744070030341030786403c0d0018002c603080340c4041d20300018071215101460141080360b0740040f41c0883c0340c40c03048000e0240b0025070580820056a103001800340d4500e003600d00380c1c5040c885d410080ca000001c0c10020340980f004000381c2c5079400c00030400921100c40c6c26007410306c0e0450400b9402519403940e20035009002500a005d4400e011461501c20800d03034028640c0680320a0751f900c0d01c5d240c0782c1c02400c0284000c40f001001c21010580f00d24281c0262003003605110411a41c699811144011201900390903503010b540e21540810703003803100d030854006000c03418010 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 202682985 1250 202681735 202681741
    0x1e051807050d1b060504090c050a0503040b04050f070909050c2407060b04050c070213020a05041e030203030301061e0f0e0405040c0905090a1709030c010c03020f01140406150308091c0206070506 85
    0x7c4415162a03000c2e92080003410081c418030356400c1000d4070340298004054a0407962940342c0b003032400140b010500035512500b40d001034171803103582142c195903200b00140d99180c00030303805201403c1c0303110041921010318040c204c0d0b0303290a0326019206141c02104040740c00c283e9440403078100e41b4155859020524001504820b40c14a101d12105008100008500d002a030210040c524003503401002880f520f80b0400300d9144a10300d0000700032f96001020340ba80ca594074180030b0800a02e18031a46225803d11900c6043d040c051904400c0301046030302d8080302c20521808000003000c00070400c90b8504440d0401054160a034031555200345113040050005403d01d0400ca601c801d01c032030840c0c00d590b6003041f18601c2c03600c02080d1210003903020f00346448600b03140e25081e81048035048120100e90302c1d10004007580b000e18030308680550700410013000b8294011041c00000c40701030102400c0140200314003c031a040c034071604264590340301c10302d021150896001407102d034800d01c3c1c2641c5944c002c01c28 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 202684235 1250 202682985 202682999
    0x150103060b1206011a0c0c030d02150108030f030103080a1b050303011d01051005251208070f14030709030b01080604110913170d1e051807050d1b060504 67
    0x703440b8000c0161004101d99031419107a855140d064655900b01400003058040043c801088000c0050381c000b000c2d1086a08006d0000f943d800c2d026003400e01c0d03981070000001d403a1a002c8101c40340300341c0c9010300307525580c00c40d01c4044040d48017500301010400c1c0341e800b11150040d40030301c1240e0700d4403c401540d03483d40340c030402c3c1d5942c2c1c0090050765012407000c4010041c59032100d200d403500303010506141e030b1140840110104000c03214038003144c00f00d5001c0ca009003085182d01c4450303910301c0c1c0f0391648240c0c1c3e16121f90803513510b041495007501061940c2d9248942810040c05150322142514109802c1c3e1345a83e00c07502034203021307440f858043e07002d0000e00040040c0c544000941d02c800381c99a01c180d151031100740600841036140500b01d81411402e0b078040c600364208036500080c0b5850107020b4200040c50718210400300c2c4810010803490240482e20480c981010b5103020406a030090003e1f50a041c01c10840803e400021036206018a03100514190702c400300c1c0d0010190794440c0d54480c0c0c0741c996 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 202685485 1250 202684235 202684249
    0xf010b120402272a0c0a0605040206211b09030c0d08040810020d0c0201021e090105090a17060f06010c15020d05010b0309010606050301030f030c022b050714010c03050a02150103060b 80
    0x130300301a50b00060141c40341850002400b4220f55030480e50100302500d860011400c03a03c507581c5080380c080461500d800d00041200da034180611904080791400091544165085002d12030210394150414a2031600c98035244091911050145035858500b60303070b80780d0041c0784c0103190103041282a00821000c0411056105034503204000d40025450800c400918039020400e108a040000c040407601e0000380e44034100b5209520b03400340038119401d480b1036440320602c420301c0421107203206210000344c2851214800c24000c410684904401d040d031036640000e080c0c100b01800c0c10042e800d00a18103240000e0260714020101c030920543d0b43d08001da41b481c05e40784240c00010511104000400024001c1c1168030340c8150507240505116003148001600480d00f69403010840740b500601e00d500c0050b240012508922074021034a40355074a40031103025040840103a4081107020302c4490110303000754010702034801d5078415110012108824041c00b10307000e80050b252507540c2c4100c40150301f0031071 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 202686735 1250 202685485 202685551
    0x105210708030a0323010506030403050a020f12030a0c0c0c12030c02030d03050609070804051005060d021909061406162d0b0f061f03090602120f010b12040227 70
    0x454220381d25070507c804600d071448044c1c401410040e002031000c019510034030058021058260aa03046070900c01c10115050300305649504401c0d00e00018041c40501900705124082d9220780c0021019207003000c40c0f040d031260030f4001d90910070789000000041e64280842c6603a085141c40000e19400c2c0001441030074240180701c001400313065070501012440000d8941c01d07240600308041403581d241004244100d60180b402904041e6000c11884039026500d600c50640d01508002c00425079038840b60041d1022846070b19420040411003842ea81500607101d11105000c1c9028594808145a140c1d245440302e01c809403000c40c88402c1c070010452030f200349a0304070001c041805158180800041c02070988801c034120b48580515403504114001d811441b07040c0d0b0001402c54441c69010807511207100e080f01c00b1044c0c208100c0021071a01c2c0200242c84405c0d410b00c0604803d42d0b030f5907080c4440038024617541313010000540303c230444010441c00d07443c1c8030b001608420403c03002c11003c00d40e9484410 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 202687985 1250 202686735 202686791
    0x6040525030b04080d1b1103041a03070306030f05030c15091b011e12150b0f1309020417100b03101d03040f0612050105210708030a03 59
    0x109140103151144000e0840c256030704540048031a40300c40c034003203042d4032070013146204003030419200005900d00b002c1152001103a81d12201c001000c010b94594580c8914011130142d00c05201c2408919a0440069648201c86041c0090701c1d5459845260b04080c149404030782ca0380c4001020501301c0f00601c0b05200e8100c00e40c1d0505a80e04000340e4040d15490340c203a940f07011040c0032004035a240c0c4901011070000104d050038803800c000b400001006040181040f640550a1404000003904042c1143d004c031450114001d003040b100c0c6110500580c072258280d083c4520017103012980da145071000700002c10010202800030301a64100c1814080c410414814680c40c00b40741d0262910f02081208071100d40480c0080d0b60140c282030300900b01d1082e0081b85461001241c00b060313161000c030030b040c152146030300d5240e02071560300b101c80c050340d0007401001d40090118010801d50011813901000401c0c009d03040d6014661102030091550304140c0050700000c1e1510480740340003440c0759000b800c000c00 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 202689235 1250 202687985 202688023
    0x40f050607080a120b090709030314070c1a040e190f09020906060f0d06030503070c09020a020d050a020a12090510031802060912030a09030614100302010e061209060405 74
    0x90302c6105090081000a200344210914410062401c0390701c03140050700d004141d0b56a60601c0d5000030000443d50200f14046607020000742e45c00b900d100c00b5103c01d168085c1039654894140043d48a603c003c2d050511400081804085010600d0401c00d521a040e80314a80050f081210482c0d010b41e154541c268010520b800811000340e210f007038280d944410b05868207a92061000d42c059810320425a401102524040000c801c00c10007000815483d40900061a41551141c00e40c108a1003100e880c0307005a400318441c42e00c018043e80c00780140b6a1240140d4008004030344981654000508444001500c1c0900510540c680040c074081c5103442c40c0340803c0f61040f599034826528092010107403141201250910f00f0303aa40310400c4410440d49001c0d20b45a11030342c5000b51844140d400211443c905055010b80319042c0001100e10a0000345001c01525155800540c2c0c45034641c1c5841e078020320304001e070140e110306160419001d000043d004164514007030601500300305950b40c6007802004 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 202690485 1250 202689235 202689247
    0x909070e010f0f091a121f0e040611030a0507021014010506090f0319020301060e04030507060c030b0409050318060f030a0f0b120c090106020712030e040902040e03040f0506 76
    0x1a000c82e00c101d4648140c10b102c0840d602a01c8295800007099002c0302480822041d5114080f443c000074104110301028146180d44811603000900e4054041c43c0c50046144501040304c100442203840d0854000e400c005131180c00d0100300d1741c069000315150460a0b403503500b8004c4007039041154080e158400d400c1003029550b0018030b00c00c00700062113000d11582000c0f40450b0170340e03201d52100100000c018220742c120b00034101040e0500701c110f40d00b64429482c107200003070000800d0718514855076141c3d484514040705603980900515500340d00c80d041641d10590300d4103a880c4c6200b01c0704c1a80c0900c00554980302c031001c05144000c0c482d00000d003e214280006180e14103680141c0e50441070010012529144030b10001006003503844140d41d000310107183c014a401070210305030107100010344d0908203c0e0389404040ea8dc039400e5101d005607045800b100e15000c01d208480120001e0300040021520501640003d025211075030100303411504005005c00022010009905c024801074501c181040 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 202691735 1250 202690485 202690487
    0x7090509070504060309021507050607031a0a0b0a020f0105100504051f1203020307051609050f0712020a020c1504150f2a020901090b150f0714030f0304030201020909070e01 76
    0x802544035132024583c881d86441c08540e1019095406000a0020580c582455041081d41d4000c140d4107180824039003040b1114001d0600c40844c2d0852000d0541000c4a280c002180c0007680002d05980031800b0f20320000c1c1c5035003401e0041c43d0082c0c0990360910788440c1800104400c50300702a1000742c030350b120840014000cc40301c00300b16003120b50341603070140a203a940c10283d041d4421804010407600405aaa5a5500c0201c02c00006d5411403001040701c0e03580c6520185030010f05554a00101e1210313913501035011003540060094441c548195803c074a10803000c2480c088000c155440e0300d020101d0300b80030a0120b905002d070114070328581440a01c814140c003808180b82d900301904808054000c40985629201d00009000d50140a51040d5079507400d0b000028a462541280702e45a03064480c007101d000001a62103038001c1c074030110315000c0b003a901c02c0304200c1010020240b901081c0840c0f21000c2c0040080c43c82140690000340c0e84000400c20441c0e45000101170728240402d4102d00072880e = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 202692985 1250 202691735 202691737
    0x1090c020304080a1205130806010f060e011d04020714060f130807200907020705040507090f0506030615030415050c0f071103010b0d06090515090d05090f0901030605070905090705 79
    0x1245e003010200410b1440080d080301e00c0d1061103411040060790030400588214006040b604941e00c5095070f001054948004030ba41c0042c2440c01030004200c00078002da16058443e08655858008000500d07010309680d13009104000042c0c02c1c400c6402c900200f04244072242c1104d40d004142107400c0c070320292a0b950704410b6004900024003212107404102080180a10140020040c01410aa414034003407000950314180b0340185030059051502040741140500401070a40714a603184070300050829040c004590801030165034420b8480303840c0005064164010b40c0a075014490440c2c1d2505451005001c0d140041e0511200000030021130880e80003440a807041315602080b080d40c4240d4200001c3c0c0589001c900490f030140c2d201030810101303c6150310a100252080003540c8002800c12030a1024050450f01d15560ba08907007602207605100c1c0c0020581240002e1007245c18400c94800f08034100001d130003c450a039550004d009107290001c1582c001003004842c9421540380020380205a = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 202694235 1250 202692985 202693003
    0x10314030c030714070e18070906080304120c030b01060519051603081506041d01080a05070302241602030c030109020a051c06020c0309010906110325021801090c02030408 75
    0xc103100b074113201d181840e005d01031a0f005000c010b06014a904018000c4034000d80c400303411109a1007620000100305405000d07400803900700001a41c20546043c0518150b11420481200c007a00e0218004c40090124824203000c1c2140303699642e103500c411070345d400c94200c8402c1c088090000511000d0305030755003404191a429410b00c0c0c181103a4460440f1a88110070740e0794001d0f80700301c0101c5c012514100d41064030565804110f40f03907506903070305c03000c55498404051001d002c42c0c001c562b06201504240003d01c45425446000703a6504c0c0d00c0380510841d80d00f103044c0c51150b469604880d4015480c040003d415016012002003015203000d500095441c1d41600c10503025051404c0001307480d052040944038207640009056550340107040f480c0b034a0b640950368140c0443d1201c2008603030240328444160340c2c0464175000b10b180540300300028100e800d0009002d4030920141e6050001600c3d80d9100c07000e40700046410080359414107070100283ea040084000441d0303c1800100240c00c000a46041 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 202695485 1250 202694235 202694243
    0x6051507080d0209040e0d180905040203030904050c19030204050916090e0a0207051506090f070c03030b060f0703080103020a09140114031c110c0d11131d010203010314030c0307 78
    0x203030703990003407010402512406034820118040c50800400745600403023450100b921100c440c588258845c4410001ca0300140d4020b5003550041c0450102c1e41482e80c0000c6d00401034215003410a0780c06100907801c3d010031404440041d4001c2020002c9080c50321180382c201c41d4045180b0b0605404600007071051040b845070f5040d4005420100c0e40d51601c55048a6116820605aa00a070307500003030109440401d40700107004d01c8849000519580c00b0036130050017071090b941c9881f1444413a0302c08401400a072101d843c2d00850800880c20050407030710081c2a0f440c425100e05000358518010465840c130300340d1260030b1403410001180d0356080b1031106a81510700c24175641030f801452802203071400c03400003950704020b0024a01d6680c010b030840305240540b03000d5011607094034a107405200d0400c038544001051150102c40440152401191407000c1c0700c540d030f80001d0070f001500c0103c011810300504100481e580040184140803980c070040c143e0401e0f20700190b140106000007541d80b481011400340c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 202696735 1250 202695485 202695487
    0x50a1d130c0f03030c020306070c0803040305071b0e0a140c0a030f0f140f060402070b04020d02121e010617060601120e0a060218181f15020106051507080d02 69
    0x10040190980201010b03100c03907a80c1d50142034980c50017500103001e410069100340310300e10001c0e01d000d114000642c2400d5010308054159103c1d6507050b00c0b29040700d4001c840307a0300c10f201c01510079030340818104010255080501c03090304207803090000f219000021948070024600c100003006c0c80c8101100c2d240c4070039141c0040c5103282c00428400078800c3d40b8001e48403d040102c00c0c009100901c004900410001100480d15151201000100c1c8a14003001701403e84400008015141200b10031000c680050520000500b81d00d24260400f00d0028000070b00d90041407001c0800e041c24490312000c2c10003503c8403101041c01d01559075a910004040c0d504100708042c1004a04200b40c204507010400c000445230802c8107840d140780690000d0444102c8501600313100141d03480c000810503200341c4640c2c0b1110a60f160b6050002140000b100e03000004502c011001030000309100500034800b52540c00007882d00d06000070054060410112111907441c00d1003c2400b290b8034030100c6a450425403001 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 202697841 1106 202696735 202696771
    0x9060e0901140102150a0203101d0103081c0207210c2105070213240e061c050a2301021608071416050a1d 47
    0x1440c0d1110500004101d080640e48401c41c5614040c41078944040004500c0e00e000780c0259005c0e101c980c0d00104011810200119000280c0380001c19003140180ca64603110b9040c00c1804050100040041e680030803e450074450341c81d00c0b9030b8800a54075100981880c0305001103107698014003042400c100c061280c882c2010200b0540d005111b03e410010b10b40307618510000c085c1404090100170040c2e100540d42d04852030714600c0112101040c1012000c086002c000b0184000e0031040d98802c4003400103004041205a20800c02d451400000642c421019006006020040c0407800390b40c4000341400b4401b0030f40901c030107240a2207084011000e012908034480c0c9142000310134070980b012000688080020103080340076586494031222071000660a00e851b14007a8400d481740e6440802c000c4c200402009e00804012811220320221041413074034411008102c1400c0d480c24641c2d0f = true := by decide +kernel

theorem cover : BRFrame.Cov 202517985 202697841 := by
  have h0 := BRFrame.cov_init 202517985
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202517985 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 202517985 ≤ n) (h2 : n < 202697841) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
