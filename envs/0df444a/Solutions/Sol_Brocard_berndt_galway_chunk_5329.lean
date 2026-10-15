-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5329
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:30:46.449153+00:00
-- url     : https://prove2.me/submissions/9288fd37-4af9-4ef5-b9bd-8f7f7d07cd77

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 958273381 ≤ n < 958453237 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 958274631 1250 958273381 958273387
    0x50f06100c030818100608100501030f1103031603020a110609061b070909030908160518071709070617010803090d05010e010903050904050604111c020c0a0305030106020f01050f0c 79
    0x40310b90081300d40300103c403030003401445100100c1caa400d07041241117403142c81c1255050102100513000310341e001c0c0700051500e99030300840d01c0022600f03003040b91840c400030192814254030031005d50a58201e110304400503002140c81c80304011f03c81a02c0c200358002503a04905242c20840840c034688600c1c607100000030441c0340706002d4104204110005420141c000788a030010b035180203031007081d103402840042e004648408104c03100c91000b640c11602d00800904201d03040221005040c503002d030240003001900070b0802040c0180621341401241d40400419515150020007420362580702c44500400038284010010b2080c00026aa80b140f0301b1100d044802e211407500320700410780000900d4065082420031024076801101400d501c0500303890501c03441c0c0e42c0104210444020342c00c00800c1c94030034090020580f02c0c251508116020502005190418000e0000e2425400c440d003107002400010040c82032036414040c044003818017500a0026003045040c2450314207008101d5440b404004c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 958275881 1250 958274631 958274641
    0x10509070e031c0c0506131112010207020927010b060d05281b02031905030a06030b0109020301081905120304021324120302070e04060207080d050f06100c0308 70
    0x244110403851042a008424000843c00c028089480c02c1c1d60a42d07003800740740d00264070ba4080340f00301c3d00141d500c9000078400051103070400c6a10303800c40340d035245a9035090024034016110000d40902550102c6030441c00440815241807910021041c0300c1c10303a0341060603030b0340c0e25225070301034800702400747d034001c1481d80e1807400d85146609050440704090a2202d034007841d00c855030b40106041914442c0480800c0860042680d43c0e03c0b0b0016035400c0000d141c0700245019100f14003650704140b2140d00451482d9603500ea100c031850007a0412003400d5800001088a0321040250010043d1200d601c0300c21841d181d200d040c0c50b07a0001c0882001410000005021561801010100070303480c61020400300006450100d00e1076562981c10107841000d0a000c11a800400c41a944055141d4000c0078410309021804202e818042c1044511540030700042c40021041c0c4041c0024400d09600040c4526100e00c66252615001e88030fa0b0080503024200301c0d043e907020404150458140c14080002e07121 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 958277131 1250 958275881 958275883
    0x21509030a05060408040f4104022b090f380619080d0c080d05010305030307090f0501120e1e0c01080a14040f030905090a06080d0206010509070e03 65
    0x180300c20041080c0180c0041004000e1405e020b0015280c042c2140826903440308480c0446e00c51085404070000c00109072030f00c44010005000700c00b01100c071310000e074581d0440c0229040e600800c082d1a10f40101e100c0b2518190300004075402c500365512030910000b0481d480740e126503100d081e0050540c8120340c0189110070340409130102e42004854807240c2c111011420428003000a581503846075000045524041c50074040200c15190000041e00250f0003111040d00d05e401e40036011104110b090000100d0582c41d0f2007007034021400f90024641e80e14140f00010201c550680181880e11780c001001d21050764000d400c11441c0304082c8c0c000814100e030341002032911980300a00d000c80840030700022050030700070414000c076080a890b8950a41c5500d00910305449594100c850b485aa2000050224120904811906010f0b00b0001e520945800c00302d1503500c01242c03152140340e102e5004000c0241c0c01c00100144004a2000d480f2550400000942461003e020b8200304a04140711504c103a070 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 958278381 1250 958277131 958277143
    0xc0316051608030415050f07050301090e160306021c020c030a030902010c0210122901080613363504030b070e030a120302130810060f1202150903 64
    0x242003403071140c0f42c0ca0a4505914031542c03880e03410422504000200782c1407002200b02070f004866a4488034196800c0028ad84c00034002440540301500c20200c00e508117424101c482000b45005400143e502d1071000714410102640c0000d501200d4410002c40d0b10781180801a9807000a40e07141c0454080401e00048807150130403c03003e035200010324003021841c3e402840b207c031619007440d000d00860b1304408190034584410b240d4038400e05e101c116604525072081641c640d000400814080c5031040c844a080b00b02e1b240c404041801c2c1500300000d00c2002d120b203424054521400110f0091034007542e840303a000802d801c0c000c00440d01d0054a400d0303246003006601040110040245403202e5507400c05e40700b80b0905540400100308032003e500403d003404280d2050303060f0060402c01104030b00300b508400a41c000c507054400c00c006044081001e50090003813214101404c103010905d28149100d00d840034507140e200b40c01001c954940140140c80c2d0903a0110461040742c000340d01c030541100881e0420b1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 958279631 1250 958278381 958278383
    0x3070602101d161406070206031305280201020c09040819051e09180705030705090609090405101b020d1209080318060109090f0605060a08060106170c03160516 70
    0x1000b180354000348a815040124100c54400c00100b52003613101c2c0500000307204040c0f020307401100030000100c40c01000f40c01099071600c507008403481115140d00c0c44a00d81664900a0401d482001104096603410080306182c080c08491f1181c03581400d83d10b0031141c1c414241141100c58035121b490340760034051419141e0800c507404043c3c42c030341503c407500c43c83d5901c4085810f20070210040458681c2d050036507045d105100984078103107107403a00841640d50f5084541c2055210340100140845500ca14003207500682c0708038010401903424401c0e00b02900d1549283d084405000c405a50301103900040408070b44540781808010141d140060710080c120401005c2c007030000c0042402405c81c0035400510b41c154105c07003a12000c5e41c030f84454509451100c140500150032450b84c038008211542e000a4024100800720030f003940c1d44540c02814000300740e000e41c000c00c8070100689600a0800320030f540c46901c40b24000e16600c0c00708040c1401c898600d1103142008400300c0d100506850864140b1411b03 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 958280881 1250 958279631 958279633
    0x121107060c0915030f050a14010303051810050405031005102601020c160b18090c12041104060e010b04060c05032221030c0b060d02040908070201090503070602101d 72
    0x81190298050f0140005203400c0601c83c4c0b82000064407142c05208020075001d20300850400360342b07103450448040d0059151115214003a10000d1059034440c1e001d0303500c01c0015115036496a140500300340c20444e04114100303800d030900041000d0700403c0622142695070b003030101e06081c81d1000c0394010fa04030b0064400125840010440210305000581d00c0a641c0c4040c8120000341e200c0002024138003840b07c8200840d40d103010854132916000202c00c1e0b100c80250142030821a075004440302450082e182074681300c00e40e404804090034036015a4024203240950380d4030f254502503082016102c1d81c42042c0400000018400400005000700c0742000e016480403880c0f00034044e5079050380001882003109247c0d002c020240031020071b0201c0c2c01c03401c0d091380300c00b41500126250401021001480b1075404500b0354a2080141d59900c51800d00c24006c28072240c403185103100160500d007a940240d486a40000002c1007003d07800940115a80c45500c0c000c64925040c142c512510f21492101000c1 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 958282131 1250 958280881 958280909
    0x5240a0e03010204090b120f0705011d03150a050105190e0604091b050102010606091202040b0102160603021b0f0d0c050a02090a050a0b0103020a270f0e0403121107060c09 75
    0x44682650005081d081c001c0f90501c03032500302e00d2103441d5101c00723030041c901058101c4501004558003900400d9007400321403032120300348d40e420030010b0705141e0044002e901c4002501c050003008000c4c0d00c141ca000d4038080d5210075032030017100600c0310f4600b200e00c01c6003243c458072800100d03030f40ca030360f00542e14041d4805190140008080e404800f0001d041c0501c50056107030900c00541c0030700c61110704003281c0100484918030000d130740910003c0c05c6410081c030306500c45c1c50209004d41240d050050001c000b80d9400503103810701c016581542514800c0460041c0c2e00000654100010101d10000e0603542d9081036403112181d860001e00744650140040c3d0b11543c00030401030340760482d4001e21700c90880d40c801000782018400040d001c034012400304000140000389040c60058a400c849041503001d01c40c02c0681e035540e2084060302d400260049000560001c040c8001c060304550650000c040c10041449072884000a03842c0034002d000d009041c0a8032030310095210b40c0101840d0015203101e81c01032032 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 958283381 1250 958282131 958282139
    0x90b091504171c0518010c170c0708150702030306090912070b1504060b0f1e0403080909100605070b0c161101171608060111030a09090605240a0e03010204 68
    0x18a82580c21898200404030314501e43c1c84030310550880b003c03228106403e02d0308000903401124110340d200d00440340e0707540c01c44100b09012600b03000b60240c100391900038411705007051607060a0050080c1ca00c86594490418800802d070040180c9078000c01c15160303624199030741d200070340c6002100d42e10050030305030002d108402d1282100c14207202c0c5a601120102984000703092004558443c4180c0300000c40c240040b0002c076542e031000386031445081d4501c16000712030030141d40c0c0350307030082d8421100308200007420017403814018403407980310007551580c941d510302d846000303440c6110300702000b44101507070713030014200c0041001501c0a00882d0401c0d04c0c0c40311542d14014004080507444140801c0301c002050001b001c1c044081c5102e440700300404d5207a00e0700c010b010703161850054940703030501c0582c0303400c0c6040c21000c0002c1e0882080580d66084040e183c141c4681c104c44d09a00100c1c0144903510f0301d00206541d044d2441d140310030a02190382d0f04c0c181500100c412054018000e541035000080000f = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 958284631 1250 958283381 958283383
    0x3052203020a020a080d02070302040f0905010e07030b0c0a1d04020c0604030305060306240607061b051201090b0f0f15070507050406060314010e190903020d0e01090b09150417 77
    0x1820b41c800c2d1802d010050310340403071650303401d211046040182d000a005000606080e00828041210114040740c09903165403140d0944000c0c004518141d0b0021200f00148a2180c10407500042e03142c40300c910303011041800a1070410000c899900607480b000805806450300d50468000c108500d00340c5105040a01e4001c000d4207065504520078411038020032403004088a00008607014800005850803112007805983d400c084001d80300c1940d0f4154184080351300c00d80000c100d41065488560f1074610080c1c02a0441c010f03007001600f00e2421030202010341f941041c1101c0361804640c80d106080342c032400242c4500394105043c950200200c0c000c03040110004800064a1040b90180700c21a00d07400300700e0441e00c4441400c1c1c0300050202c0100242c850608110b508041e8060741913920401004042003600c02e008000c42c0140d100d0308668050301d506c030300c0100140c102464110b04081c0392910354542d50141c3c2d489280f0400115800c00c40c1c580308c90003203400030038401340d804556061181c041 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 958285881 1250 958284631 958284643
    0x30c06110310050415050111030f030106020d181805041103010f0f05011e050d150c0c02040b090903030a0b01110a060e1005091b060909100609090e06070305220302 72
    0x103024038942e100114062409000d45045d00b8004103c0f001c40b103252030011204401c1c1d5460241460108124050b01004404003c601806040c0c00403d54142c12150041c809940040c15030110b007100441841040d5023042c2004100e0701c84035010903540c4860411071040c00e00005415411341c40d040d5066450441034101c1c038420414210104816a0f03500c1c840c011544811242c012030f0720510000344024a406080c00501030300801c18800c40c541c0a280c00c00c1101d1044480001103110321240c1c0c01103103014014109403103000c1d200c2215504105003403079030320701005d4480262251680111803c503480382c03800f916885040401c8800311309150425500404025400c100280a94000b18040c80054042c0c503000d51200001400c50200c0c0c14014100e00980d255100c0d8041010011030310036544189900c3d010320001100035521b00d242c0b200203480c81c030041e40000d19413414101510b000d4030740032420f56405155414041000c1c1d560301e10040040340d03010300b900720f40341020390480c1c1411303400030700 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 958287131 1250 958285881 958285891
    0x804110a0807180e1c0513240c0b04021e03060c03100e100311010903060e010b091f1401020c0d050d0207061419090f0821030609070c030c061103 64
    0xd2039601032608650026200c4c0300c80342d0f021540c0300c00340300c01603038041c0184200e100b406071400d0750808000c0c40d00381c0340c1d0031055480a00c40c2c81e58a80e40740c41d804280326107100e170410355041c4098800d8207035460400000b0000c001030721500354090800c8840ca8284034031208074900a0503106c00e0301d0300380c021440d0313a042079503407144108200c030011501090500015015202181e12205014556586c115a07240d518492038100101640f001001903d20b0051409009880c000420041200c0c014400000c000404d81035400c030501081c11007003101800b1550030380700b0703040620400904c006c005030f1400002d051007903001074902a095090007004120441402166800d8400d0983d0300c2c0c2d0100d81d848a01301e243c80c9610340030800c000c445108052201c254410758181581c6c0d89640f00c800081c7d4683c0f5500411140d00810a90340c0005800e40030742e004000445c0c43c0c0c1c0c0c218104140031840460005051100340404c00000c10b0926025588000d440c0b9803041051041401220016545400585e0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 958288381 1250 958287131 958287149
    0x60801090b150a0e100f1d070807090512030c0d0221191b0204020f090102010501121208090c0402030106030c0f03051909061b080105120114070804110a0807 69
    0x7011a4940d081440c10249000c4028070400d2020f080c00031006511401402c00c0d03891030304000d800140e2504000c0c175640100580c01d500c0711104140d5001e4040078a00034541d01c100903d15017044400d641104000040e10820780f40401e1070250f02040700e2a500c1190743c440d4035489070300b94626015500240c290641007e203840000305a031100d0900c1c910b4081c1c8016482c0501c0700302e084540340d0b8840d41026142001d40d00724000c500b8203640100d0100d0384411500911040d0000c1c41c15a2940c09004031801001e0407144516682955251a0584910f03600c1000402075a100840c8100301e080203411148400100300319580d50303551030050010030b9201c4402d0046101d40c405403012038003900c81c56200d010241030b50030b800c0c400d035109640240030305036080b0b074015613a480d00704141c0d10703081540d60319030f81d207407070f0100d055060100708158260400c03810314890703051010724260500031610040d0419081e040c805040d484900e404400e02d000394560541090303492a0005812000049881c11075202007 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 958289631 1250 958288381 958288403
    0x31104080304031412120406020a0e0a030b10080a050c060319180c1706042909010b011413050409110414042f1018060503091911010809010f06080109 66
    0x3c017091800340541701c60040d0040c0608001000b195241c1c00401d0050f03a81d00e016203030341022000003100003641da00280c2e00c502010003000301d401d60300c4401201030590f6030010014424150f40309a40c405801824902800c0302001240220995052100a4030782803c014004810b80008072201c24410100546034511001c00000e0b00d522050720405200b10142d016006c40d03980c0e915030144001c0641c0d42e400c40d500d90104500120024402d603d8050040781002291a500c003000042c051082e030303550504121810032410031200d1040d149034044a2090f580441e01103003e0500205108017840c0c082d80160600c0300800340b102400c1210741c8030320711850104110051403081c0400c1700d041c04480821043c02e144c1c041d212454880c408880144181c604281e059012000d004116051a4806004644040280000308006111610300c002804039240303150310041c0c46036500310305060038090601c0f00c3c440208003148420b41003515003011214042c420704d40d442010034003c00c264031007a00c000c0850 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 958290881 1250 958289631 958289653
    0x10605090114090907120c090e030405030a03110c0409051c0e1005160218073b04110a20010b030601030209070c1212050a050c0a0311040803040314 65
    0x30040c50589680e0b103020060224032405000308070401900380d00140c812420002020b62a5071440d0b0724081c42184030560403440c0c000c10200b0340c0d24030009400142c0080c4000d10076528000354a4840580600d004100c4000805800e401c010b1401c1d0f070b164002d0305010010052020006482c1d03810b8001d1000d0500c5450302d49000c071101c000e209186a8081845441c42003054800c0b03014010808055882070540611680007a03400103000c12400c1c003400806042001d11500081d90000044103c122114419203a80030014025200e003c01006002503010309840d030345940e4414007a86403000d1206540307040c040030140004410b624080f0110a01c1d0000c40010700c01070140a20242c0e018005265503405d5900300204460001c10750300400c5a50b6544c5000b00c1c01e81441c0742d51480c266210f081e6070180b14203110042c0c86000301590b81950408061044444294040300c4202c0f105103800212214032100000442c07241d541320b40814400454040240304032110203685100078a01291805054 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 958292131 1250 958290881 958290889
    0x7020c090103123005060310020702010206010626040809100327031b0c0509130b060603130b0a050618010e070e04060308030f04050c01140d020a1718010605 69
    0x30900000381000340d03440c004940c1c0e070302a015448001203ca0140f030400f11200c8890403500c034007918000b40a075120000e008580c1010f00c00500300705580207003135140052940001c0d40d656018460761040000b9068078400700c0c0d034810303c18880e03400d5489940c00e550805c1d05040d107668010301d001074070904000100c0b4910b58003070f109109c10f10286007800032040958590030300b07090301154016000d1041d8400f031140b0400c01c1c0c2511120b01031054039101606070401041c00441d131002010001c3e071101c107841c010007080000c50a15030240d411210203960760380e809112641100d0300d03000244800c05680c20b01208100541101d48104015590b01303d078540700785415030040d50207118030309c10f080001000c1071825100f2510215042d50203400031400c507a4a503155020342d4401c80380081010014428841009010702c24840e4030714007480d04510828208808440d0344c8501c6000b101d000381d002a4807140070340500009509001841c00c001c0c040d2801080c10141c58003458a40d4109500e0000c2c04601443c0c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 958293381 1250 958292131 958292149
    0xa150b0303040530030a090306050c0f07063b120a09090b061b0a0317160c39150806010507050c040213030c050406080d0c110d030807020c 61
    0x10b40102000095a10fa003208151131114000c40c1c0004000311100101c0e92104000901c544a0345907684d01e020392039420101c04856003e060b20f00941c10030488840303103107001e105403403040e60400800074042d0221000d014a24400c81c85086805070385003031441260400d001012080b941c80c0c0213070340c03114618285040161184840381380c040f078002c6809004905041d031100c0350810004d49010324010030003c17400d901d0710030007011484503031140107180c00700341e440070440c0940d0300c440b2000442420700000300ca12100c2400c81c00e2003003252900f0021b0a1003103940b052500f0b010240d24020341c043d40c0204d01030700a1080b501508041003e000c00040315902c03801040c0c0300f088103035900652034407500300440307456110140588840c450043d00c90354690301c6100414402d0b5034102d801c5040e80c41d40ca0188001003540d031042d44101c0ca4200100701008000c1400160310280e458481c04002080c5490f040311003944440c213801036448400301c010550801c9025000340d13007d80860340200c1c445000c100e00b4403 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 958294631 1250 958293381 958293389
    0x1030b040f02180931061a100905010207060c06061508071713030c02180a05101a07110d05030f0d06120f060e030d050c0a030501120c0506090a0302030a150b030304 72
    0x8040c030036074200300c0242d554000317580d42c0c0420b2440c1411800b940362041901c80200c80c00321810070307070541c40d1000d2500a4104000e01e00e00c1c10450280ba240000207522880035105240c1800b1a0011410402c1201c3d0f000301c001d0f141c1d60603180b40c030b03600c049030040140da81141c00f032021500785070300c000c903506011109512607221564400c20b001403554084a4150440c50200d030080402c903002c522041d5001d10043c405d90b0800c00014142c60316070205290f460700d59100c0c0007a0381408144044412a65044400c59034004249030743c5114404081680c02c001200e020302180404186600700e00201d900500a0013a0301809002e01034071000c0f00c0098550300f0100411604080c480c4174002521038010108c15002d90702a1307424802c50f90550b40c180d0b60101c1d0346649207500003804001d555012300c03689002d411140d04e0038103011500d0b542c13007404800c2401603d208940120386c8821503603400d400c41c070280d075001e429114007002c140751445c90b0456454005d0195400d250a5800908001050350121 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 958295881 1250 958294631 958294651
    0x80606060f030105011b05010e15060a0609050411070803070503060109050a05010804060e010204080703030c0b0717070309020607021c151a01030917040326161101030b040f021809 79
    0x160346403100560303c614a012480c403a0036101c1c90140f010807800e109c2c2d18240441103024101b50304000c5114282440024842c600c104544102481503507400302100d020745a00741c40010300c0d51858850b401080c042d4003001403402c41f00008020020b61310201070350007003100380c0b54020210744820802245511034001c06000400c11700004001c00d8440d0400e14405140e407000610b000e4a50300401d04090a0f45c006401081c0c00c1594082088410090640d10a90350b144c580088050640305044005d4050151307002c25456806000665803024116000a41e0080c0408105031000034484400d98284006072042e030010720340c1d000d00c2800c5016511458507541c0d142110608014019801400b60040c2912001c00120380b1003000306d0a04002c0004d0750060441300c51400c25060040701c201c0e2411400c101184062010742140b1054482d0480440e42c0a54104080202100128010090300402940c41070130b000004071280c03c00e90003005048031b03507802580040291414080d0712042501e452140d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 958297131 1250 958295881 958295887
    0x908061302130207020f03190b0a050906180312070e040f09020112020706110d09020a170d0c050102090409060f0c020c0a1a0d0e010218030d091403070308040b04080606060f 76
    0x3440e446900404c1c1c9584000d000c1200c1c1c0c440c50022924040010f684050580c2c4058400750038071406210361a4002400f040030b214600d424101c0350f440341c0d0090030300b02e0310380f0515100344031a04060080c0c0340c14a07207035401c5a0240c500030748021700e444a19003285015603d815948013a04d81c4034002c0111190b01a1036080000c091504801e00950001c1e10a0395004d5403011364095182035080280301640c910000496002e0207030041102e06031240e48640c409214507102004000c6000c10112828a664144002d540039a4201170740a482201a00c03036225142200311801c101c05580310b08a00c84504038104110940071b80306980c0c405103540d20342e1b400050060104820030080310f0807468034500304449400c0c013200c4040402070301c01001041d555a50080381400810a800400800c04a0304500500c000d031000b42c006040c8001e603016008200303110304c0450b00d40e0b8400704282401158441400c6503101d540320300407a40740c7c0060151010342e01840307004c583d262614000f43c0d03080b580300b00305081c5 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 958298381 1250 958297131 958297159
    0x91e1c05120c13080105012c010e0f0c1204122303180c060f040302040b1503040605090f030412060b0907021209131b0f180626070908061302 62
    0x28903a00942ca000e40005000f01c0c02059a031020700400d4024840c000c034242e404105181459400d07901c500c3ea085982c3d01060041040802140c3c059400c1001306180440a403691146032400340721b1052001174181d410b1040c801007284100304d003101c4001035983e404a03524500d450044003613105902046100090000c60102d6000040d5020020362000458481901c1e000106800f0340080d0007030a00050081810001d500301405078400c3c000045460f04030400180700e04031018003014101900c45a03940300024100b81e401c010141e1340c00c105030102c0703440e91b070742d149aa290180660f40461388a4281141e0804030f061141c20180500b4a80d00a03050b0750388840e400030f001e50003c0f40c2c5180d10421b02c112040070710702544a203100c07010b00702117100c202c00000740c0042e1070120f10350103001c02c201400c1c075604002401759408101740e9000740350008000e42c50100c15082c88440d401c6500c8038951a50030f2048580c0c01500441c1220964026600959208000207443c4103419402a40007108100098 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 958299631 1250 958298381 958298401
    0x41109070e031015062d02032104080d02031f121a060a06050c0715090608100308030604020f04032003070e010e0f0c2a0115120b091e1c0512 62
    0x3c01b0414001603013105880000c100c1e102920309045038080580c00025a007141c403459000b0103440388011100040f82420299250001d03440380501c4c40b80825408008515400c07603041c003c0d541800a0b840c0b0f10b2460b0345a02504030440c2059404951015825a030020308490240c1094400c080042251882502d84a030690703c1c1c3c2d114010030001c0340194507011841c00c00d4283c2100044810ba55100c0c0345900b440b4014104000260064130400d120243c108001244102166400141500c0c0980ca4510f00014a4007a0040f03800040c030f030b032803216400d005203105c07407040b80e51149040301240d605903500c11103500c0500c02030040c034024040003800900f00548070415039401c0307960f6440c22440d0840788291000d0072000205008080c5280442d0303d80c1261f402d003d450301d00c1945103c40d58100c0d25003100c48440c00c00c3c1c400d008002c480c549000a1540d0300134000389580c0c070100c00e00c1e050755861a00420381c49603080048000281031904584038040d114500340d64042044880c04001c035210b24006d1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 958300881 1250 958299631 958299647
    0x70e010504090510091a0a05060312090402040503010216061508030f070f020d0f0b2809030525051c0c0b09030d02370215041109070e03101506 63
    0x40d541c9202c1e4140751300d01c055070f520400010707601803420701d1204201d50003116107819001c1c0002d920a8100340c240605c0303942c041005404156500641a900e08075103000c00d003c1d0240394001607041d4404189024403811341e50803945280c2c13044204100c170304141d1414039041c000d14010814681d03c10300100107128400001000414017988034030101181940c00103446603120607040741c20001c1558040104a858400240c11140c1c5004d00da03543c40301a0000c9208102c20208030141607151861740d8189402201200c280d0004134200e6454030b4154a000c2c0e020b203107140c400322064802c03555003420036031b11030700c0540758020255111803a01041c2d84500481078005440c40c1400d00003041560281c40d0580f004191107109801d00d0f10000c4021103021040404d24500c2d02c2e03440c403104000200f42580402c0c4407034042003004c0301228989803810a0521905843e600c1030b00a4084801c0c080005d800c1105000c00b410110100da9a8080c6501088240c0b0f150b030000d05134200c101c80003444024000c0d030342 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 958302131 1250 958300881 958300883
    0x60c050a080f070c03030509030d030c021f0f0905160902040308091011030a020a02031504080316030e0a0b0114011106070c03020f010501030f020907021c0e0112050f18070e01050409 80
    0x107440d00708182510750b04c40300740d0319500c1280414000181040182400d1144840c0c001080c20b00300a620582c0030081c1d2140048004210b65988603070062038048000d51210740d5070750308904200b260350418070b4050303030310341e10641d80c031030441884040003172140c0440c002c44040d01e81c001c0040b0305042c00c080500541017500c1e039004081c4039041d404859803460400181c00c01902907402030203480c6283c0145424041c44032903150380d04808508120100d03038501d04803a0800000300ca8030200c01c40215040b4018140886505158000c4400c004148805000001d050701c4501d1002140066264010340b244258210926041c1d0456000501c101d4011048003194034003038015103e060702083d10503421204240c104031a034158502000041d0308228691690000c0300b40018a50754090302d100c0c0e10880c6500703042c0800c100792900a1710346039215440c09c1020b0783c0d41480512090524000c5d80c0c1d40c01008451054009035800000a60064000b400500302c40b50980f0f494860307420b02003480083c0200c510 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 958303381 1250 958302131 958302157
    0x412060c05090d060501170604020d0b101e06030608340e01121a07020a0b10090e1c0c080f03060a0e0a050708130b070c240510060c050a08 61
    0x100c00d081e61500750401c1c0f00c9510408001aa540c1480301c06621803083d00508042036114008100c016115038100d411407a4100c1004100c9903640c21030030010003980d4000740c01840c200c6408100c400c1007442c064090307403c6520144081da8a584d5401d9a07030344065032035114002c0001c03070340010240001d000400e00d50044001509513840c0d01c00700c240300000ba03000d090b03ca51000805418041741a203800c00310b0b1300b5407901c000e0b03500b01154001e654011014014280800c0000031850314055200000c0040040460900200d6001e441c0e043d290072140d0880e0b82d43c00e00c541d04845a1902c1810f9401e01194404041420900524051409904000d060390b41110341d904d03000c501c2802c0c255603148104100000071541d4903254000a100d480c0141c9003240340e582c8402e00305c0000c0c04170041198403c0051501d02c11440a5080c00c800d6240b0b05a441e420000360b110120b0308002d06900007905c107036030030a200ca0b41c480d59208101c2d5524121540a0b0050300300f00034070b90004148100809003044012 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 958304631 1250 958303381 958303387
    0x402060313030302040512160801020f07141905010b090c04050618030a140f0c1f0813021c170c030a08090703020907031e05151005250308010b0412060c05 68
    0x180403404000d031280e089441a880508d20403600910000100054020b640095081404880190704075024441005202c0035034400080d0312000c0070885207080c0810340d0703202030200c90381e030500b140200000e507507407409005240006180c20140804075800c0b01d030b002d0400362900003400001301d031004225910907494021a195070006c250071482030880032905c03901800001c2912106145040442d80245010b454410014000d601c040f1444d82246011420038880e640c1c1c418030245910020604000d5200341c0f4403a07210080300184404248076442440459101682e00040280c03034000c11000362080c6e40208011940300d07110b9840c568025807070b40c0403220341c251a40d0024104040450b00000060ba0340c0c880128031a12801d582004071312007000400c03007030400c1c800764041c0c5c1101041c514042d15481da044440c1e28170410840c1c0c000f40c0001d5403400e08040b1485000a180002d00080d400141e8400c00805e900b46102c0c2110304035040d41030999802e62142e65814050400c040800c01408018 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 958305881 1250 958304631 958304639
    0x1006050310020d140c120f06030c01030203040201200d12020306090103380a1113031b0801140a0c090f1230031b0c1103030c1023040206031303030204 66
    0x941e40160003500c46803451034441524448802011031b000380740100c50500101400381940340890b002d043c87c1d00a18004d662130341d0b2800142c52440b01e58110052003400b052900441399400b003500d103c608115900d0344c0d402c0700052000405e902040da001c5030702202840040001961290349000100402c00706100c2c0c2d928440562650700c44961800c0c072418100c42c5c1041108052440b5581c0c0340c2080002580c1007500c444e85001c07040f102400020000741c8031102c0003c40b05110024035000f0300c48040203000e10b911814011240e0002030b148480500c2c00e090366806000e0192620800340e503410021405071611b840310180007210002d205440b01482d103400c0c800000100d41858092894036140f9170201c0e4804e0800a04991014244200f80c007100302945443c103601000c107080d403c0e0003007000d201c0b81490900003070652003214808040d42c42400040c0200201e50b42013103032820f00c084030101e12508960070712030341c600c5d0865000307501020400000e2070000011501c03484003402454014203050721 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 958307131 1250 958305881 958305911
    0xa020f030c03030906070f121e0920041103040f0312020d0504020901060201062d0e0403091403190803100f0602160b040807031401110a111006050310020d 68
    0x251041e1149400000c100f200300502003110a4010072646002c03843c0700c200c1362005000314152414900d0081d200c1580d20500005000c0360b9900801401c02000501c10b64948184034000c0c1103e94400b041c1c54004a00c0d41d450644131390f9081070014001a46141e03240d90320390a00e0012040200c3c24026842d500c00041c0641e803003d4501140c103888000f0f110305040c0104008603005911460840e0305109080c08401c550749181c0c00310300201c0b80c421a44042c407849980c01030846820603070b01c90752118108002e1540c401c0381c4800310f490342c9081c4071201a0007802c0c140c80305d0070781c0c110f00d811500c21506d41c0000780c0d6000c001c651151100100d03403c241d449541e004490740b040c0e4455401070f0f028404954003046103c0800c802072410140982c9003625190074940c8804031840080c040b00507403140c046082c402900000048d5154403c0507a452018040140c0380d40b45006001d0400e124120022142402ca886281c05941001300100f11465082440c1c002070b600148000e00d0142c0c840700151035200d0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 958308381 1250 958307131 958307137
    0xe1b121204140405090f071203050702030d08070801090b1f05070f0803091002070c03081c110d060510020615040e06040510051609030b1005100c03090503070302150a020f03 76
    0x180048030030960b07000300c0100410f40390007400f4812607030070005100700c51007800070b000e00c11100698a030703114811582c1000d590f94003409401075058002e40040c003600b2644071600c07500c42c0031b844d11410856601c44050b4011548035034003043d00580c5981010381031079040c40c0e58101c0c0000340e15007580f9020669640c041c26a00d02c420031036200b034010052004008043c030001c2d040b400d50007011424080c0ca40c8408201810b83d00c80909000b00010f8249501c1a0901004d80d41d414041800d000840c162040e00c81294000403603407a101e07240a40101c1c140c0340421012440c10440c0c1e000b0044d80d04c844a18501904000e0007159000e41c0e10400b182c14190306002462040340100058048081d00c0550310781520310081c404c401040403241e040075030030307080703400381007600c0e040a40a1086d82c0c9501d4000f0b030341c40068001c1507020105041001d4215071010a10030b203640700341c2e00d5140840d40d85043c141e07901030034000258054900c00d00100c1d0504c0d0300c0081c00f42c40e10184102c1ea8840340241002d0300b558 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 958309631 1250 958308381 958308389
    0x50d0206070f0e030309040506011e02151602251e170d0203070305070309360209151809010f080f06190507110d02100e1b121204 57
    0x80c000804010794503400520701e4829020a041c02421048090000707030300c078421881d9003842aa80c0f4000308509900c41d03841c811044042045a01c9064a03400000e965580041c0d440e0864411400000f580c00923031010f1454842c3c1c2ca5001000988550203200c0615101c0e900340d41440c40d5020300000ba24651659503110b8441e00418034040c07a410700d1500240c404505220b4400c039880460012101e640c000308950800d5010300d01180c9039034084c60100d608006a03400490791011803e5500d04a180310310f10745d0080b07040c1c10612114413910224420176030140c0025168000358845500300c00b094130100804800021103080c14a00c50280f001a203245000e810001190300c0411040c814000b0401050243c038140ca4014105841c01c520784c002011003400c0c0c0c60120303c1c2c5500200d240580140a144155262101074444c480070400b4000c1d528400560880851b034100004428035076008203c485e54095415190002d0703811403c28461511241d0700545194840c10110340b450807d0000500054 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 958310881 1250 958309631 958309633
    0x30d050712120527010c0504030b0c0d0501060302090306091606120e03130302031b090406090f05070b3402010302030705120106031d010209181b03040605010338060d050d02 76
    0x7030405503030041c040c414134055000c5a14206030407a4558010701aa02202e9200c41210b140b540c9100c510021805400c0340900c11a04000010a0141d010f03005081c1c81e21090301140e070b0983d03d94a000341d0b00e144a0b0340c1c0400c1040c01e40000e12140d440780b62244002003004102044402e882c440c6c56241d41c2c4208030081003510500b0061045150030f1008480d01800480c4204a0451020000d40f60310750103807005040580c0c071076081c001c105049002148580d00300054a1200380d69024055403940491501c5440201e030683c410f4083c001d0003c80c1440c20760f00c86501041d4a00c541c0150002e600150081003440000d0028021011803480100d000e01000c1d5400304800c40c00103402640c650102c0f242d2400c0c0c6e401404031500c2515903070b80c1010a02c082220341c58043e16203010b0a1a8500905030264030075000100704014006c07183c0142d4120781c0f252024109900c0b03d050411200200d5580c0d90701c9054101850b0329144903003004d503680107140240150b02c00155030b40d43c2480c06507003240f0342c009 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 958312131 1250 958310881 958310911
    0x180218060d0e070e2a1903141303110d021221130611271f05040e01050402030f0412030b060c0f0609071208160b090a060b030d0507121205 61
    0x1003140e40d003241c0441601000c8038000300b01e540035074694036015000f001c03d4240300f201180c0070024400c0c0c0200b01641481c440802311818901c264400d6042511401c3d00400c4c0c103107540b10840e0342c00250203522003806074040d042d0080c100c0e1080c600f5034046c06402d580b100001c408100349501c400f112501440002000428220300740c9040801d483c9204410f2003250001e005004005200030f03079110f94140b0500c15000609020000035060020801d98003180403031200300c3e105402e4015000f80142c804010041c2c0560380c1e640100026440100c42030309090504d03201281c00541c0c100d8043c901030f10b060601040404101d1701144640d0000854a050f960107150041c100190a20890b6001004800500b92050034090000c1034102c40080050141c0350000346108114110038660815541c0144491001d0030400ca006d60f82d00040309083d91940c0c80c107840400c030b910b000500c0d1403580030162940b42c10650691030300081b140d013000e0544113010fa2030098040240c00f61044900c00e12000c556144c03 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 958313381 1250 958312131 958312141
    0x20a0b03090c06090901033302070c090b03071703090405070c150b01020606010f0e04021801020607020312040210110a15060f0e160507080c010501180218060d0e070e 73
    0x482c0141c0d2039010b0740514001c211403045070b1074011010781035942092181c8111802641c4d100c01c4480041c41d12007120503052901c41d000070403074000f000254003a0280160480d102c0d00c4e141d088900c00a03000758540e020803030800482648801c151034014403241074904010b500302c0031038281c903011100c3c0000036100e01240303002c0048a5071380404034001c01d002001000403010010350381d944040d06681c144109440f020882501c501c48450b04c52340c01410540d1540e0417942080102082107032150301500400d00081d400c1480002681c40280d0900808455510f0b20307000d000b868162000d04800300720080407049400c000812003820800e00c280c03c4440ca5100e019442000ca0708240c0004010820030f1104101c0900112401a0481842045100164032803002920345204141b0014448200031072050468001036110b00e04940c00e40341c0c030b01151035189140504134031901c00e12803c03004070040640d1050034030388003801000100910020f144480300c000320b46050383e00d51080c0000560401088 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 958314631 1250 958313381 958313383
    0x20106150e033c0d020c010e0303070204090c080607050c1f0e0105182a040b010e030a03020f01060e06100e010210020c010203091e031615140a0b01050412110607020a0b0309 76
    0xd1500f031081c01800e8a11410540251100f4100d45220f042016201c50000c495905200f11858030740d0041040100045074580b2591006c95880350311f40e075001d0351000070b400e00e0148044940440980024100020080440d0315042103c402192125a0341c2d079590080103500340300305130140c3d403002081031041c05900c210718900101d011000c0854070190020340c40001c41d1032844100e4020403500400d5240e000c2d00102c900c4690380f100a0390500c11039090005240d00070a00030200a540e41c001c0c0681071310344071801540c02d0b060310826000503413100102c407228451852040c44003c14410743d44180354142d04a02030b60808103810074165400000c1c040360304010404290740c1e40804580e02d04c001c200c0c09600f41c032030050059504d000c2d000c030400141001f412403003080c408a08042d040242c40041191810410000c9844070045858031403428038a6028a0540d021030300186805900c0040c1c65560102005686940c507030000f009003c3d080042c0d88000c020000380c16013002081d160701d4007030145 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 958315881 1250 958314631 958314733
    0x140610090501170414011d010c0207060f031a1302040914011a0a020f060a020a020c0d0b011701020903030c0109022e0c0503070b04050d090501020106150e03 69
    0x40244103100108205690300403c1004441079800ca400c200d5030749031700740f00c1c01d0085404440d96455207080100c8640184c508106101c500582c1c0c000c1041200e8070307005a0f40e41c1c68600070540441d040c240f820b551244a600a074013900400f40c01001d450f01401c01091146922001c0256139039000705051081c07008910134906140c1950203848015494021240b030344a61303100300f061203024002001000c02c7e00030010800300e03504039812a41d4602d000c1c14000020b402042201005000341c25500c00d681c68200c0d50096815001014100944d1806c400b00b00c508814104110345950284007510b52954140043c202450b0700400102e28103810b40f04020b0005d4447d01300c034031142641d80f158071501e584101020b052146c14188011000010304009142d4040d10b0300050070114401d0800c8104000401c1035001200640c4603552443e440b040164240ca94034010342c02070804655481c6c1c20f40d4442c4a00e040d031000c0240940d15403203071300032241401e00070040b09036034011082501c96000c5c14441c0302c0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 958317131 1250 958315881 958315909
    0x608090610052b1523070311121032010e032d0712050703021e040207050106030c1a030a050c07050307050102130b04081c1e0c060b04050103260d1406 66
    0x8040303042017940c26074108601c0041c0030482015038804046071f45050315004c1351220640c0c0e04418001c0e143c042940c00c01c8150714000e03612444580c400b0442d01890300710403903c0583c220308030403a0300703048000111040c2c40b071180b80d01c2d41817103100b00d03030238134030740001401c0f201440c441c0400c443c440610200f03a450500154441101100e00c40811000b04e840030030b071503003502d0741254410040040300f180706050361044d12034240d0152000800c0c80801c241503000408403442000c1c1c244005070f450815141ca0240105040c0b001181000080c0800905900c90b540c4202c00d6241142056a1030b103410307185402a62080318160343c0000c00307040500c0625034590040c83e84000040c035007810013280359187c49074140e08107c07200c907804084029074040c1069080c0081980a4010301c000800c0e40240000003241c003e4500d503282c03581145207410580607050680c1d03006040c3c1c0070144041e8820720b583d0001c02411943c0b0280912030113003140300c82e01805030100721107800301800d8182082080b40805904417 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 958318381 1250 958317131 958317161
    0x70206070801030602030901111b0c030607090902090607050a030c030905060405010c081c1a2701330918050f011202060702040e01060608090610052b15 67
    0x4018295a001890714103503079210501684986540018901400044078072854038240840c03900c40d0190600e5044541c101c0c0c21084a01328255602816100c0764296501c00014480000500003000b00380c0042038120700103402e642c0740c40540c0d03c956082c080c4c0700900703e000400140c611001e140d032142d100f07800390030200c1e5028038151501c0006083c3c0d0b4002c001c002c2c01540049408407501071b08920001843c4940b0801707105403104400d0805404501240c1a84181a104624140548c940308403d0740c0404914403006940d007040d1110b400d184001c008a42d1008040036007610a0a00708154280000300e902c5414600c1d00340285c0c0c00c0788904007001c00d00003a14002c09c121412109890071030446141550302c40c03601c7c6c40c90000c15a02c1c410040c01a4100d41803a16100d0007100550007003044419540d12102151201c1d50303015107a00c0c040d01c512544a40155044c0b229261203007254400341203400700b0714600c988a020b5120041000ca00950701e840d0004060541da1105010744030000d08a19 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 958319631 1250 958318381 958318393
    0x110d02010e06060907202a060a0302131205031308011404321b0a03410f06070c0308041104061806080705090103080711060d0c170702 59
    0x203a990382e0741c03500204840d11904050000c104518014846400d60000c40550203010001c0080f02594412401200100c200104050141c294855030048540260010b0820f482e10103915411006500100206600081d4281c00003c030b14001005603207101c1d20610181d915000040e0b00100090f03031030760212807144d0400f04850112004248229441640462181c80c5500340f80c0082400c4e0f041012000c1c641c000802000c05c040c00001f40c3c0b44581036071140c220540004400900290741e038144030042003091180c0008c0c12040c0000412810101d07005403200a801c64000810b6060841d040c07038004a400c00c3c100301c031000c1170506c5102e80c01200760030f01e05240c0c50695001000d82c0350052002d4400c000441500c0c1c0995074039080b1000410f81c41e91400c0c8280300c51900000201b0b910700c288922881b070301c07100145508205100604894000302402e0410041e611442000910702e550300740d104100f0005142d54220394403074018401c20640c0c585030000f58000d4810500c010181c91740302554040 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 958320881 1250 958319631 958319651
    0x5101e03051002030c1902030c1509010b12070b180d0b0601091e05010509060c0106271e0c11191e08031f0801050408092d01051602040606110d0201 65
    0x205c00302c400210280300f950b002c400402104034110301070708440d55180e0250710200c0c1104030402c20150300491800008100c428402010410120036019030383c8843e8201d0403081010307005080140501c948101c014103100c80c0d07070380d001528030000c0c0e1500311031908500d0107210095034000081000741c00c0303c013089100c1803c40e0005c00c0708a03105202d1541040340000d03207105ca649951040d41e984008800091160315128000410417500c01940d543c0b03805003004c100102c08902d4062070400f00c081031503001e00b580d60707461024090103a000e505c4040c4540703811010200681085601c0c840d030a0328404c4036041e1194901040030f01804201384c215041040d008034086075001088079008034030b00d030390030103140040e00e10105e032000c0ca548405903035440d00c0208000c1c040c03810010840d20100700c42282405401c01001c20801e2101c2c060b5802284c4903101380c03180365000350003c0c4621540500c505000c00ca4550005042d204546c004d0000103800c4d400b00c1040c840100000d0034500c6680c0000e0181c121a = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 958322131 1250 958320881 958320901
    0xa0b090606041502030f0711030d050a051204320c04150603020a09030804030b1504020703170601051b030d0c1112181017010f06050d05101e0305100203 67
    0x2c50244400308101030994034000780c0200119245000e4080390315442d0354050800e08800f50b0044801800390003110052004184203100f01c03071414030191201c60a00c2d001200c94144440b000b8030480d01107000c01c190724540d080302d1001c4c4048010f5407001d4003a032190000890b042804407441c0d0b6005508002203000034080102d441c400b501c907249001601ca4017050001c64000c241540068558980040d010080c451651041c3e840343c00807440e00410111000d040c40100c0c440c010000d400240900c400110b041442001c450b04088149042824824032580003030300c803114610b0340c80c0c003944000340324251828203014140459442e400c1070302d45403182c018600e07201c02d6070004540b41c1080005180d030141b0400e58150912480c040c003440c2211044841c06000d41c07034604a03101d000d0025400028505050050356030658031955542828018060300c1107000c1d00c0040c1c009600413a04410202c0c2c040708428544007a1f440c0e0281e1908002e00d5814202d003006c036502054110703240100100512242 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 958323381 1250 958322131 958322137
    0x51c05090a17070312050904061a2d0c01150e2503020d0507170c0f07170c1219020105150118150c0605060a05100c0c050312030a0b090606 61
    0x211040440d0042d50002d007046040682940005200f01c1da00c0004a044c15030000207810f00c0a0282c5040010946440411007116105041280c0e860b40400502d00c10030b040310b04c101c51642c02143c0400d031901215903940c005410040000a0583d0b4031480c813003013000300801301c20080207028580000d5061104102c4114035a030b0701c801c02c0440c1518100360030b6a202c0c0d41281e01d00b1800450822880c20030080045c034211442c14041d07145070034003020402190400040320703861840c03400510f18210490340c071031181c0300e07900031000790220051154148a9106001c007061112a0b04052a03851481c0601104030841400040007103a1400e02084540c4c481c41011000d00e100900340208821111007002098005030303001002c1180215140c03e843c01d400940d103000c80b6220702028402641c0c0c1c031040c0701403444640300d5160700030141440f40351845e0083c0c421440e6a4040c10142c2d0000e500c40c00032034078003440e042114003600c2c0c0000400c00724546c5845200c0c0d4000c0200d401c4203240c18820002903041c0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 958324631 1250 958323381 958323389
    0x50c0304032a06020703050d0c03151406070b0108030408060c0c19081b010209010e04110a0318060504030203090a050405132a0906030c050d260c030304051c05090a 72
    0x4064890111000b0201a21407803503501c00015940d4180a140090003038001c0f400941c0703c00d0a050a4081182c001d0180c4200d6240d1132030105242032805000040c08070500d00980d0b000a810090f004c04a00040e089030301920001008503590351500c2070103894404010079170144441d06218512a484000c0758090070501602d148124440541c10210103e2184a6409082d5031440c2c19a41d40b4100c10b4001d0080803200741c0300d125543c14480c0c00e21050b10780441002d1142c1104001e000050750184e0701103000d03001201d4039100b62004554912040320300a40e01130700940d10210b515420351401c82101d00c00742c40141e40a100609080c40702c118910900036001342800110722868408480a800710a0400405007040c1c4425954641d03910082409003c2600e0340c030041d490105040c180001c4074024107500140f6600807901002e1b0b18161503000c9103001c0c03c010001c1000380c10f907860400c00756001e5805180900040342480d03608a11822060360101d080c41020700510046940c1c00300780004031 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 958325881 1250 958324631 958324667
    0xf051602040b040b040207050a02030606120c100c0b040807170406170903310b090102060a020711090f160207081b0f1002030301030308060306060a060e0103270204050c030403 77
    0x45030800300040c010f400c4d040003c50b00701b4400b01c3e40d8000d0010000d08000114020360503510540c40ea8818070110102c58020b20416034032203034019005080400140e441c43d01030f071802e8440d8004075510801c407404141d9007520380c0710700881c80b041888540c02c881c0d00070380c114200b10340c50f29140030070203400020b08030341e8909582a10800183c2074402441111034658a0fa505804001e1827079404070071400e180008040e80b142d9074800801c03c040300504858065074160020601540c1c1c080c80c174401f9511401e011150b507107444039451159220809501d008484001e83c4002c00c1c035106140010590512403024110341c0000300421007a0000700c4e401084403920100170254558460100720408610206d40b5041810009a941f04581c00300c0a941628801c0d13031600080e0f2200d4003050b554030000d803880c940c050301d00d402c100000341c007400f81d407031440c2010f040110705c8006201c2d031070b5444180e82071402c0200070b240c000a000c6141c070b442851fa11209442585080d41481c0d2002407420081c0c105040345 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 958327131 1250 958325881 958325891
    0x501091421010f0c020f0a020f10021c0509010f0810050f0f0a0e04051506180a0f051008150123060f1c0c0806220b040213060f05160204 60
    0xd401048038a03101d00080c1900030f0045224400101c0c1c001d03d803074440707180140030f0016002d040003008200000d00e1a001404e40c03801141450410030b40702ca03118140c6040d44111007200f034000c019203452002d01103031600c40e640c54607114030002d041141d10f00d500300200452482082903944640602c80d054800c26949104504144c0010444100119001a0f80120703081c2001034030501c80301030350707225038480c000f03880800011031680110140b0950362564848001d800501816640d0f031042da6201045a6000c100c0c0d24503c80903508a91b0203031221000d400c1d140d03c0c05e2040040411024941d0714089942e501590300d44000b4a1540da00c106038003000c4400f00c12201195035449040c0e40c8100c2c983e11005a032441a08000c1c0448a007032843d006841d424003d0000c0340303c5c0680400751160030050a04851114100d0030081502218030000842c50390718a03105006460300c0c4050906142222041e8a07002d04020002d031071a1142108002000000c03c04000700194402c5c0c81e668070b41d41503801082c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 958328381 1250 958327131 958327159
    0x506010f02030c0607051608040801050403090803070b07030b010c020d2604261f020405210316170f250c090507050d09050303070f020f0307170408120409050105010914 74
    0x8060038000d4090b00314480409d0104030700606511441c0560311a45805140d241e880c100d4075101e0117801c2019046146000024204a00030b4020b8583c0a205150810121141d5800150303840c440c0602501e401740d90501c0c001a00b85075007a4400c0c480401e500075400c01d440c154110b00100c0a000d403805980c0410724043e2002c090420881049500452005102c9400a0b242c3c0c07009411500c90a40310302d00190007160300309044485140d0403001d10303000e1894200380c4c41001214690040044501501c1c5010148030b2440b48400b0385000400745080e640e84043c40211150268405070046c4580205000400001181c5140406c1111400c0c03c0c0401d0315520733100d0a0b83d15010f80400f0051042c1002d21180c10040003000851007045103454044150341f03030760302c100d0340c1d101240f501c20301c50b900400580c40480c503801e1980d030300005000e491528050b102c580040c2400c10b031400305042c9040220f414000b00c01d40e03002c0c00e4027424086c60306554042c90002440d80000510203400e000303038840305d1215 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 958329631 1250 958328381 958328407
    0x80609060a03240c080907060e01080f10090c2016030b0702100204090618050f22140604021203091f0201150308191107090203190e010506010f02030c060705 69
    0x4402c0f48804104020b088960018101140450b8082d070382d400b44201c00304602e8040c6000fa210541c0694a8440680e1514a44540c803040580480e0b031446440d14001030301c8455025221840d4260341e948465109400c2072548206134117503007040720340c111000850445c411810502c00b100e802624141041d01c3e069800c5c0d080c40c0c1040001d401060000a011400e0111600310300120362903440c40020b0350808882000c03c60306d06075511500c0311420350104a00b454100d03030201040307240c07243c20b4031b00d408641e80781c40c2c0401d611210360340c840e04003c0412083d8070380000021880c50b190400f0303500d031001410001e80000f88076141c2c0f11440c03a4150141d8200d0303100b540608a0311014691502e24240c585c00c2001c6290080402c81000f0b042c0b100900003030b02c1c4203102c29081c14150100404e0f880f03041c44680e42c0690001030681445a0315140e81e110101002c0c0981511b01140c0700c00040c440c18010001070802018158a0b025035104014003d1a001d000416030380c0903003540b51241d101c21260340380d0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 958330881 1250 958329631 958329683
    0x2112180e0106050918132301051e01120503090913020303030f04060f0b0f0603040611070f0c050d050c19050a08071e08030703030c0e06030c03040201080609060a03 72
    0x909112003451001140d080d800a000700310045080380d281e41a8031184c2c1610720194400c440082c4001c10161405002803220402817940c10780404403140d2910940140341d086840498a400b640710b001c002c040003c2da4500c0003035024100440c0030390620800ca03104c0c030347d0f248601400d06020b0040f003030000d04851f015420b51403030194000d040d01e56a045c03070800d401014005aa0980e5480e10340301e405038203990340e1720445100000c084d204080c3e0382c080008100094000610550354540c4a050842940c01e50f000100003d03441780c45030540003c1c16050215903c3e59541205004141d1140b0f004045840024200404d80b0200d03180501c44503034454020802401e9404143c0010880e1804100101d01065620175078174030000b604403511440c0300b6901803104900c198907440c0c00070003543c2c021074420780041c001787e01e160500b9902100044080394080d841185c40c1d20040d0760100920003190b034010080d9400200c1141d501c0c2d400e0410000060202181e80700c0200584c10300b00705815960911340304 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 958332131 1250 958330881 958330889
    0x70504090f03030b100e010c050c06271905130605060c0312060d081e0c3405060f07050c27010602010603230a1506211218 54
    0x400e001003440d0346001e808000d030940e011000300c0d0502500c03070150b06111404545e000c1c015035a030722000e07982100548016840075020b54031802410342d0b004c6075440710750040c01150001ca00c0503030364000c4102110760719014201080e1140c0751356600e06403880c10070480d03601951403c44821805002c19841d17039004107020707808581c21a0780440d442d402680040301604401c50071094101130b6070b46040030441d48a55020b002006290f00380b1403684001044a0141c02540004141a14011080f0301c401c0c54180c1c4482c01207840801c800b042e90703a01140f200c03000680000540d20b900491f00300000030701c0900920b50b09410300400421720304144441009201030f5401c02601296050b03102030138035203080001507101c940c0140500e0000640703e10500ca171340100c8c1d401c00303266421584154200c0c0c141c5030091404850a214803055032012076058034600503203440002d00003d2491a100640301d065004c004031441004111030001c01180d0f036801c500600b44040d182244100c107408080c00d81000060300 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 958333381 1250 958332131 958332139
    0xc0c030c0a150606030e06070c0c2112030b01022e0e0105060906030303040804090b0f0301020c0106050109060e0d06020306010504210203150601020c090a020c01020d0603260a08090705 81
    0x1254010b010089520402e01140e40e1070500245855901c01d03410b651094011143c02e501c0034001a01107807059954174016445900c4414a099541528100c05407003000c41d80a0410099060400c1014030604010207524a050030f010f0500940c00103901c4c0e00d140c00d0f0000b0441180600400b001c2500400600303404c40c5000200000d46030350a031035000b0702c421220b10b8004d640c2c42d00850305a160010560348210b0344448120b107400d0401708400c0c06441110034094100b03044198076003c0b0f940038000343c488080c04000010700306140100041946010354000020300510071f2101e032a40c0c4440b90a03503200d5410140160b5a91114001210390307110350380c005d00381700d887c481c68031400030040004c0051041c0201c0c2225182d95904008000349403080d0703901401340c0d1110907075000ca400e04a04e4180d1120313012100508280070541c055003681d000803068441c0644e17500c81841048126002184030408450342c880200040c140321000500c10350208005000c14200014000c0c20100110000b0f001c1c058 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 958334631 1250 958333381 958333393
    0x403030201021308160b0d090f050606031b010c030806060705010c050409141e18030a02250e01180f092904020f1c05060408070b07090e0c0c030c 64
    0x1080080c003c3d007020f4a5400c8020786a0780004e03001900041541d0070081c1d910014544610b02421800c03035500050000082e10380325180c800201e2210a044441071703003d2005400c00340b410360105400c1655061480742000c01d0071807200c215983c405580d1800d2940b50422031100e4a030f0344000764a038020720000070074942c00d0903201858181c0c0040507008807900e012007481908900a030010701820115a0ba0b004404d00d01c0000c9080c0645442980e0003540402c03040c0c1103031100c00391030303421681f04e23444140260744080c3d8081c140070400c210000130454050a400d0000b410413811401120041c401d00b135142e0a20210390303540d242c3d19031101c5851f42826030100080d81079850080e01900224400c0b0f84243c5141c450300000c10900129244150382c02005c10400b80303802e80c00c01050324482410307032180c0c1c4070b0382100200003042000000d0085000741000742d2904200c0c80d046001542c000c22410410403003400801c49c0e008d40f004580d030800d41e456080382d2207800e0369100d20311b180550b4030a00154880e00c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 958335881 1250 958334631 958334633
    0x3090c060906080f01051c060f0608070f0e060307030b1b0c0c0a0902130506030c0f1b0606011107060528030519090503090411040302130b0301060f0b0910140403 71
    0x11881c40c0d41150056240c080340d03030340c8031120303034140b004244a03441c0c011608000b0622080e000c009001c054622400c400510310440303003410740c11030306250401076a80c1d20005041c4034120620810700c0c000c22030940c1d01d07445441d00d10f0209440ba10148002064000102c0c089074900000d01c10204141c00d080c060151142c9803401115030700c401d00741426000d51000c41d001700300c5501900898070480c6044256600c03862416040c00071940c40102242465502803282004640511000304030141001c03203508040c02c2007545050402501800c7c2d50306114104125540d80c000c0403403000200e0b6540e080068441204030740d06644605a00800903e00c4080c80710b640a0030340542c000342c0200200088c2c5011420700445c1d25085545001c4080c00d298418081d03c10285000d4202c581090344088140d420142d032039011659090490741c1c00d14195031a42c1d034500b4541401d01c00c680091010307642c215040c600d440c11003902482041c4e40e143c0501b94151381420594010240084061003100300e10b0f58940e52 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 958337131 1250 958335881 958335887
    0x70201090f0f0314122a0f031b0715020f1306020f0705030d02101109040c051b01090c0306090302010e07080c01021b010504061d0a06080411012102090103090c06 71
    0x50700c0480114120020500360b091004c81540d4400104051800c2e494440036403880c540d500c0650414a841c0d01e161903140e4070510480a8501b0701c043e0280303103403070341800034007406841059102524480810b2104d100070415820002182071000d0f00d005030366a4400c5000d18181c4030740a0610380c01440c0080009540c0d42c00510480c04401c1201030396009502c4001700b50f1a107800410700401a40444a0010520ba41d9446449206004060240341a0300311300401d00396440c20482c0d83c00b060300030a039600c507440410304003110200c9a0b0001c020b504010b44c1c50000b284c20720301020705080e5940c082102014002d44c000320a1005540031200615544c8038001c1c5e451240c060002c0c014001c41091404103202d01c03c40d5036490105850b4903040c03604200d1b00b00c0c1d440200b2000d940700d0442c60f07220b0300d4090701c6401c0001c02a0005a5503a88217203058245840c2030400c0f51820360400020102c0f0380c003190182c11145a070b40200741c801603550300030100101e01803d403895020340f061541c000005040c40d0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 958338381 1250 958337131 958337153
    0x3080a0209180f09120405010e01021509060108071406030a020a0c240b0111060402190e09060106090605070309031b0b030c07030206100f050d140a260702130203070201090f 76
    0xe40003107110441c0d030f604c014841c1ca031107054001d10710600d0240814041c96001c2c903121040080e0610440c0d070501c0400c0e005405205061721180001d421001c01403100301010b0107110050324074840013900e0b450054001c14024800180300d06061980410003011b214032440030108a690000c40e030985001440c081c1c1e000e140e0969000710055850a91184040e5028044060517015800f000e00040ea0761034003480b82940320310138084207a080000e004a540e0110201050040c3e482100402046d0f040810160000d040da07086030341406024050038001940c420408001c2d05d6001d4800c159085d1035005d000d0150500c1e400c15400c2c10404000c01619500c203001805e00c1d00d001c2d034202d4000c2d44480781d80d007403c101039010306580386c19a000140810b041c101804000309114060b4200207024a08d01c0d542013416400044a025040c589401149120514001440c0c40c0c1c0c000344c14907040c281c0c1c0c00034403d100d04174810403511342c0100010308098002e44c0414121a003081c86c8981991451408c501094 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 958339631 1250 958338381 958338391
    0xf1107180207150606030b0d080414030f0303100e0c0304080a110c06160c0509061008060f040606050703022107020f0402041d090d0206070f272c06030a03080a020918 73
    0x39247c00c00c101c50b20328186407600600c80d0000b588914083c01c0210b440e07500031124140399007601c40c15003240031900d010001144140d1411800083d42800e00c42403269044001e480840d40c51014414000410604403c460b0740081c2418a88084040b242809050082640d00c881c0c1c40000402d11401c10216010142e20244c81a440b04204645560802202e021b0503900b2603004a906842c2101640c0200e0300207400070310090007000202c1c138410000d015500c55400c1440059408a558000c043c0c0400074031a100c0340f08140005e8285680030000b205004503000688510034803115060b00f529664110b4000e06040c0440d5a44860714810303103001d5403800d4404402031b11a030081d584c0d8161022034050f01502c2103540701c25880309200310407602c6030040403444041181d0021002d10703900c9800d407084010102c81440b140421005a0714611111021b000c26003501c01d048100b00c225640800c80b0410964182083e254030740f5100d15200003801200f5955030030a640e8401c20722107a944400c1d051080c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 958340881 1250 958339631 958339637
    0xc080c030a09150509060f0c0111071202010b091308070506161808060406020c15180705150415020708010509030904050915041103010b060d0207030f1107180207150606 74
    0x40d42c0c3d803406400548010314a40c00040b01440030b110035282120003454444002030f00c07103040140d042e105500715070b0203c200c0e100402c0002a01410882140c1805000651500007000030b030401c6008240c9041c4000c0510750000ba03140080b000304510501a54092a00101242c26070300d0701d4000c0b80c1002c900440c050022407642082a049a000c692810b0301342d580c1c84010700300c0d60720f650340c42c80065041030079404009d000e0b03480005c0304000d04488592050503a0b012070001c1c11000c84006080071129040a8003540140701005030841d0b010040f05c0032254044060306e140c01701701360200d0816020f80c22041c80740d400d2000388108210000068204504100c901700940d481e08400782d03a8174108060202c080f000c8010008004c034500300018404100040d00100d40800460005401030b40b080c0649182968045688828541e201c4460780c000c007110b0400c0d803d0301c802c1d604025582c1d031280c4243c3c5000d0444400c40795402607241c045d286207907404200035101c0380c42e009110002d80380c42d0180c2c07000 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 958342131 1250 958340881 958340897
    0x5011d06030604050d080a0605040213030606090b01091e1a0309060a0b010e0d320106050103051320130f0c0503010f0b0705010b0d08030a060e22030c080c030a 70
    0x801e240104102d40140e51203401032014198040d030540740480018143c0c84a0b03643c61a0004540d2241c0c0002c0030321802a2049036089411840c14908460311342c3c2010a001d860200c082174a42d0f046400f0809840c284075070060310018501414803024178541111401806130541c600d80200d0003806540185040d1042e14102c0d45c5030340700a000c480b00070000e140042c0c0701401518441c00d08104c1c0204240c02506880c1c4545403034051052011040c0b0b000e600c41c004031040e111540718081c81100003502d400d103028081400c2c110508041440c0e0504041d0041500e80c12240d500c1c0c00c07030158080d00c4417000d4040b0701c1c1007101144071b1000b001e103492101800303070a0216002c4102e201e401180d060b5500c2c4ca8500c40d5003130904004800a81022404444965a80d010080d103a602c5000d0b80758118810710000b07580380f5080c5161070a480d0036070300100070a1000001e00130922820007012103c1039411082c0f9080101c40e04048a81c82c01c0400058540c0d50000381030b040c124004401407070050005c0d1101d0b0300b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 958343381 1250 958342131 958342141
    0x30d1a10091502010c2a0804172109090a1415010e01140a030f060f03053403020603090c04112104080403110d080c0a0312180605180105011d 62
    0x100380d5680f090704000003000090445415541205d990014074032150703100c0303d100b686d03998001403a44950800b01d50401019424241aa0304102d094a03c0b8200501903401140c0203410340454011100528820840640003442c02c1003190702032800c10300c515000186508001d140342d1444c1d071000d400140002c59141c860651540600400091001e14650b418941890707400124001c1c00c81c82c2c200a2032707586464001071020300c51403822000e180100701628111051241e025501980b01014640049009820b8846800484500d0040b00c1e010380f42c003503603540c50030140c50400380c50703a484030740c042e1401d00b4040140001350b025110004c110510304407a10002901c513042842c040b100108071002c1000144005072100407503001007100940003401441c02560341550300c0c0c02250346010207070b200f08994418542c0c8411070001c1444185810414848a440320803c0301640c0740c00540f8483d100d801240c2482c080705c2c454807021205a00821039561540e6880072070743e01d40c0c0c204411566145000c90 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 958344631 1250 958343381 958343383
    0xc1c0c15092004061212091d07050f040b16021002030708160507080a12030b0105091e060d020d090b01060e0904110a051f0906020f030d1a10091502 65
    0x31556a000780745807150001c0b260b40b2240080e2441c241940180d111040012070070100c1c981d40960b903109000442c0c195181e20f000410400156010f0040c050f04c1c4c48003030701d941c4a408000341d0030901c10300d00941d9030800001b005015101d6035100001040000a110a0701c1b2984030048280701d00c2160780c003a4840b40d008040381c1c3e902800102403c264000c00010a81c4410401c0701d08102d480745096403100d44d0b540902c139007451401801a00e000c0309490211401da17515100350382c9242000d003410b41c01d0a4142e0040cc0c7c0859031103440a030303c3c0f00c0b440e00c007101c0c1d0f07950074041cac80c25000704140655032604458000d201800701e213942100d0086a0400201e001c40c0514a444050500500480c0341e40d62030344c5881000120b0ba00509400c00d40c11440801c031a01d61050070841290010346818909103030310401404030455501c00b40c00c5410499041e496150044119040c11022080128080050700d40340c10030f5039546182254460818000d1042e91a000f02c60542125860710030342010024285090f = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 958345881 1250 958344631 958344641
    0x1605030106050f1c0c0c06050a0c050f070c1a0405040f23100305010c081f0501020607030c090f030303060e010e0f0c0c10090321060305120c1c0c15 65
    0x4140801c0e003c2c086680d0900c52403000c0c10075199040c0c2c0100c404585160020101d80c00d170824040010001d40800c414401d140c0241360300701b007044100b08056981d4240c003e149000e07809802c52130079000101c070010301c0750406840001c2d03c03800400c0c1500e03c0024100410581c400c0c42168081d6040c5900042000e103284603082080d455500085081c0003980e03080300009100401c6000380052a50001c408240244119000302d901a10f891040d420005a056010b010030038440400385194034041c007050b40d02107481c54200c1924100419140030090064038816050741048001e010f58000000516034550410300c00c83d000c0c8910700c805662205450103000c0d030225000c9a80d803904001060b103403240350380180081c01010b41a903105816685009040c2c804c0000d041c2c0001d620804c1281540b078044c80c4029150801040030031a051035030351256200c98041d224428028030101c1d4900b1000c10520108000072070350b03684490305800c48800581401618034082d2118100013248007000c0b0710318451 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 958347131 1250 958345881 958345889
    0x702060603070e0c0301060c03020307050d120f180b060f1f0f021c12180b010305010e01020703120b0102073201110604060f200315090f010612021c0516050301 70
    0x1201d05c2c681c24440161038034054150210114403040000c580403c0041c000600b503071400e543d400a10640c070048030026287e9848102c50313014070740f03402210132148240d0380c60f0b446a40030986088a6031120009a4500c1480c0b0045402200c203088540701030002d480d4640903034049488500c0c00c01c0b0803c5c02240d4850281d000150b6441200c0da00c000b070580140b00165180c21034000124a1034060000e002d83c1c41c403000c40489100d88034030300500401c0b100b0300815200001d5a002141048190b80b4001d00c11440e240320041c00c00d65500340d83c0030036403007030007150003518030f200314000c1d83c50744844a20440d90050443d500551220224140c81d980b080006140d080c062000030003968031152140c100400c2690b1003840160740e40c410690300c40c15004038413401001400c0303480c0e80700d00e0a103c040c20528084103190303209414002c1086030180100711054103480c401e01e400c0b01d043c0c0910700032a000344541450705000c00408104a5960001500302170300c03030b0345100070118004502d0340e0203440a00080c01 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 958348381 1250 958347131 958347151
    0x30a1109100305060c0d06091d010b0102030a05090613030204050c0d1b090b030702010e0f0f06010506040302060f07172b1512030c0b130b011505030714120702060603070e 75
    0x17045030115040c1c0500801080300000103855030f44c3d248000304035280708840d64400b11000000d8900070a0a06c51400c0008003030010303500d00a03041c4002440e500c590088944180c402040140d100c940040c007460146038080c00c10020350401207003407402034003c200009102c0b1f0418141051440010300004c840543c10303252200c01904081c50b4071000c4e00010091011503580301050109910100504e0801d160b6a1001e0070700c00c1c008041040c208a0140c2007203000e10020401000180ca03200211101c440c1c0f20110030ba1111014502800400c10407141c000444001040c00c0b864580c0910607044500300003001189030000140d80c2a0036070710001d0910410548006040001500d13101c90b51090f40d11916100200300140d0380d9000340c401c4151405851544100004030030040c010f420f60340500444000d03400c6e002d420705802400c81c403000f000c400402004102600303050100c54181c0e0001810340340d086800c1c0c548040000c2d40e07a0811191188284101040007a102e01c800310824081c0180341707 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 958349631 1250 958348381 958348393
    0xb131a01080a0e12040f06110717100920220b0d020409080a02010606020a0507030602090d050345150f030c0706060e060f010309060209030a1109100305 67
    0x8006651022004003a01d01c410b40303c0e50708400450040c010581c480010328401601c0b5414510006140c041ca0f40040d002d1010a044031404110300040038012507007018441c20844040d000010b05108400790326040031410105500104849800d0040400403e2520041c48a03132000411580c020044410842d00e0451454640130b02c484c2d400800380c0075400f502c44048500e9650219040703522070101034603100c0c004204007045a84c20b0140c0401040d0f81c3c4000d06400f02c160b1a00703501c59009100040c20282d0008000341180c071030061400000d50000156034640c07030762443d0002c7d14060301d107188200e001604890316000b008480006200711110380b1020501c8050018458608a24115910b01c550f051241c28800310000c0c0085d031240180450701c98903900149400380c29a0750a8110b001401002c10400038291160780003500084003d00e400316603046541011070081c800c0701c5120303406010381e0300b204040c0040400480081e00f01038841c52000d682d13850040c00082e450b40030003080d54100c0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 958350881 1250 958349631 958349681
    0x60807031a101e02070f0501110607050904110706020d110c0d0e0f0a030f0311150a02030601030e010501060c1106071112070f0608010305160e010605071a04060b13 72
    0x70200284004425003800e0000f451070310202e40c0d541e1401c481c1d4a0041e40504014410b1070107081c5d4a5004050a00307281c007851300c1d0024119124680100064200400131070b03400f2203070b0b40b1500605440d500035001e282e960a5541000800303035102003461000c0d14200030f5008105182d400844400e5101d00000e40200c5032000c42c02c960070b13485020a584c0c000b440b450204029612031030035200440c403c0b15203030340c400c100d4540541004080c0f0014521a0800c5944504d0345581d6001a45d100511800040c0d681d5170b86401a802040070b07880f062004e42c60000041802078110b18007042080c024445c100080f0800360401c01c0c1c031310071418000e0031000551441d81190130a000c5055128401c2410f95405076201c04401070aa1b5107503007e00b00061258004100b40141404048240d0300212120103805007000748038586044180300d0700040010008500080c02001003c201290044000c2411141440e0409202400d640710609102e0580d8040244411030780340314809041c43e029402c0704d118110 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 958352131 1250 958350881 958350889
    0x5041b080c040903090e0c0c0d02010504020d0209061f020105060a1a04090209060403140309150c0d1b0804081b120c190b0d0c0e0102010b0310090501021909060807031a 74
    0x82c039070031405d105a28001180030802c4e000c03c18400e21600309066221080b0301c2070790b031520311000282015a45040c00b8000562a008600d50010790181c03000403503610394001090014030303407030f600034508400c1041105d1f42582c190446030082d541190030542181d114a00c40d0099000d150b550a0000d000f0801000005134540141c40c021500608841c203166490321070440d07030881203401300500c2d000003a194215161154502890700028102036080c0036182003216070b110300110001c8207000d0142c00220300316130398801d038400c1640e001e10100d48032a0f403a40b8880e40d030340c41700f40d21642314103d40004488500342080020303218040a0010451302c1014014007940099000d411a8030228016001c1640390319003008140c0342c8a040c50000d620790000a006004e5080103011a04690501d0800c20b40d680e40014141e180140400d00001c0c85901440d19500900c0362a0210b146e40e01c9502040017141e03000041c1c43c04039072694456107415a9401c00480458248110401e440103c4c0000031080b414 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 958353381 1250 958352131 958352141
    0x6090a031416030b0a060b120601030f0e01140603060a020a0f08100906080d03050a0b01020a0602090a050a0b120c0f0409021e041413090b04080c1f05041b080c04 71
    0x1441c0341c181d50005101c0d031181d07050303091143c0003900c0954000d4180440050203103e40030003032a03030f40d01e4a07040504031803141d854014050b01d214105911542000c40c002c105502a01c54400c604008101604031246642e01818044030044d200c1e0044130006007010405008954220341b041e034401c0713814a4041c0c819100b048028140c180c1001081401148006540c4030b814068094000244041800300030001d050740c600030100c410280c145900062180d0700020484203903940a00e000d601e4070f402c076000c512850165400316910200348c11001403440400b4004140c0c01d181c240c811030f9181e484c1c209038107040c850340c40c0405480c0070400c010400800b00c0e80c06016041030a00c14500004080f00707001c12240c0154025524104c54584121014075180000100e134940b0060f040c000d41000ea21030950300c5c0401040500303000800200c40340b00311814004404100018582ca07918141c01c032101c04001d0004843c21250b03c41075803260400c5c40f24800d080c030100c4090300c00070a425241c1c6c3e014040501 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 958354631 1250 958353381 958353413
    0x30405150d06091406030109021012023a06030506010e25090815090d03021308060106030b010f0201140106052d0705011b09140612040b100506090a03 66
    0x5101802521010710703940c000d250040c88504000b2a5110040011303203c00c0c0707000303088188680c1c03400002000507140c2e00300041250425041c030098600000e04450003038030401060074101440c82c01c80b0042290080c2046025003011f018100504642c00c1801c1d0480f2a18040070b00541d00c000010440001e0351035840307620900414055244088110b04a040c1000d00000340011865001092084003401c00c0501d9018511640450081c02c0410b10030741c65001d219000c81c10107400052030b92034410412801c100411f19070084036001d6135036100040061103000405800a5010784028100c07510500403003014080701074000700303d81d18100080d203999010303211405420201540c10002440c043d4500c0d95a00500c110140d6655070740d1900034211f500303802015031401c11540d154001c0702d5005c00d801080e500c00e44110a500c603590000580135004010590400000f000100003c00841800c100c0c05250080c6586480c181c5070310400c007a9009604503180c001c0c00c480003c1011841240c40c1010740 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 958355881 1250 958354631 958354669
    0x609012106020c0102030a090b0c0f0d0203041113020406080a1a010e0f0d030c0c08030406050301091503080403110f0f10180e10033c05010f0f0c080a0905030405 71
    0x280d44610a405d82e04100c58540c0f0543e500c000c1e840a110313014208030f070300c030030320240051400c9401d9040c40b0b00d5004500c407224034103074040001001c101902c00c50100d00b0100600142004036034001000281d4014001c1d80d0025a000c0c01142075850940a04800060300080c5d40c05540f03d1000111980e242c0d080c4413503405007a07040d41c1400c540b10030b14200c4145019513105a00034800341003006c0c50300307615404540c1c9a4000c000c10803802c1e0b4840140c9055800c803d5020907070741024040c0c1a42d660061b04060101c0000003800800c0010f019906091a581980c182d0012604c03117041003808800480c01d10b810900040d59140c450340b04081c0000004180074010320b006844d000c0046200d03004071100311022002c0c050500c1400880c02d0340c80c001c68001c00280003003c148032a1550401c0381001100103026902c0002e1341004001c0d0021058241c004100700f00b62020103210380058500d0300000030110751003001181c644041802142032107a000b100451810780f4241c00d00c002c0e0310501200c5081 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 958357131 1250 958355881 958355887
    0x10f1a0f0a0b03010b0c16030b010605030705070506010611011811190f270903020d140d0507020c041103060d1103100f0213080a021e040609060815060901210602 71
    0x400042c1c20256010702540c1d00300c580ca500c40400c50519101c0c116007298182c0c40001001c00014500d40484c9056800da85403a540300d440368203040d21f15001d00360008200d40118400030900550181810460100401c024480d004040d6000d2109a0007184003420b850f02c610403e4040c0d0810310700183c9036881024000c0c0c112a42ca0140b6a05944140c01c0b4554007561862408250050342100005e00054000c08109446140d0f0303000c0e41e0754280508040501c01c0c1e5040c2111040c040000fa603800d142e11200a0125140c0810000c3d21495401005481039250581402115103250309892141e031014180701d10340b076480d855406010348140841903040c03160300c620040c2001d5900074420004002c0780c000d61540708044210b4100684c5811401c05640000298070150340e0344803140048000b10241e180328410240003140203009540c1040c030706a410030900050541d0000365000d46001c015908003944d0310350f0420099180310a214a60b8820300c0039051035164020500494a2144541c0005203 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 958358381 1250 958357131 958357139
    0x15040308030412140a09140a030506070206040b0903160204093f110a030305060312070807060b010906050403110307032102120f04091a061209010f1a0f0a 68
    0x1080e5401150100c40600d40850700d401c509421850314405070b030390088100c3c02d00502040041000c1410b102c2c000c0d00c03008441c1d10440d1521200342903805180c0042c1036032a00c0c6400e44004c1d6581c1c0302500d00310b400007014000030381c00d0503000c0b069074406003070b020001031000700b15000c000140c01c08450507500c4290b42d0208084143c0c0300018000c0c81003138119104058480060460000401c841040307042c0075a1640300c20342e2002c089592100030f07a26040000f00e91b1140c801081c81c0c00020001004004000904502441941c0000e0f1a1641c4140400c0c0402803280d4011240e42110388074a0000c50001d106c180006641c030b600c20a07070400054100c0e41e50507500c0e12090110b07043c5403920415444030354040202e1550520060054840c140009885c0819014440719584254410001d0640c0d5503409000409402c4400e43d8441c5030043c40640c80c1c8420303443c4040d4200045c0d42000c040d42c43c03e01e900d800201c0340e00488004000886060b141041c1440070b1281e150000140c05030f110300441c0c4080313 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 958359631 1250 958358381 958358393
    0xb0d301e020d201507260105010c0b09120301180609090b13052506080a0506060f0705010e010c0e01090f230d020a0605250b0c070f0507230d11150403 66
    0x94810142d580e01d400c1c103003810740d04200218103095010310700e00c144000140466600302104ac2d81d80b0707500424003540b580c0c414111505209500d551511204070004c000118803480c0130780d103884c00c6083c180800006a8031031903002240c00504008120409040c0000e074901651000442d00c24002c03c103441c001c9510003420400d85150b85410301080420300001e011103a48a0b002c0d079846150800204214100103000403141c5c050301021851001d40050000700300f10b800e400250702c2c0e03004c8800a00c8007841050303000c0c2808111110450020b0400d80c000104800c2640d4550101d807001c080c940c00d410180021410480030680081d0740150503100c1020058032442d510500400c0c040c1c1d40d0341d8039802e003204180900b1a05031a01a217442038258070802154681d2802c0c0d03040034400540380d648151602c0d0000c2c125224100103440c50095800010702c4825009004038850107400140030020303400400c000b043c40f07024002500400a10240d5002414410545c45070002a8604503040660340d980d94 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 958360881 1250 958359631 958359673
    0x40801140709170a060e010e0a0830040201081e07090303180f0b0310030c030605010501020c0d0503120c04180e0606040b0d301e020d20 60
    0xa001000e51510400c103050380d00a80020150600980c03550800c2d03011041e0715580d941d1200080c1c08295212041c080c0c907582584000d04075092081524025480d50070034141a400c4422000c0000c140c820400341070b0242d585e130801c9140c00012000d07400d0346580d00111074400c00181a8484100000360082004950b80001c078801c0840e961480d01041c25850000e01440700e5203250018410034090911030040280015801c1e0780c2e13400001522951240007040c1c81d4001c1d5032020344000c1d40a9008018060250402416503000b80c08850601100301d061005024402d10050b00b0f07a001031251071842110402c0964002c2065510340d42416168aa02150440694070f0b00680a42d116205c20304900d0a0182650104080310200729408400000c6401803040d1440100700a0b541c602003103001916805504a1003540500703942c031401c109101a1948030741103001d050501110180422a5200040007184055a03949100b03500c0012001d800d0340c0c2c190503034425050300949148000b110305020071 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 958362131 1250 958360881 958360901
    0x50d0f180803100608150103050a06050402131d0106080a02090102071716050603070519020304081609051b0f09010c060e0114100e1503010e1f06090519050c040801 72
    0x2140e41d4a0030100340f0346001d40181e034800003d018561003044101503c840da01c0724a030354282404a090758482c04810010031090300070039442840070541752491821000e105041d600a812071900340b25a1001c02d014064091003444006444000040d03281041c6402400c10940c040c012600c102d40c40e50001c10098050113001030050388418107003c94090060461401411706135200c501d18140340c03200070711a11400240d428a008407000d0308402c06c0c8200120740c024400c2c2da01791449542503101400c0210420f21030252030f2400d20011130445c0040c2a0000d003032902c403440c0c2501e0318451003110342c4190041580c281c14401c0c1844103001003042401440d0002190380b000142036003001199045005025001c8112140d08090501244074052011500140d4502501c02c400500800090142c101e15446041f0f9004203000303450800e02c50514a16080710300c02042c0310194481406200720f541c120f1340c00c2e6110b8680d4810140d002c00550106410590540f00d25260540b6103420b5800d5a4003032403 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 958363381 1250 958362131 958362143
    0x1103011424190c0809060a110a030f0e030f07030b09030d1103040231110d090302060a1803020a020603070315030b04050c040c0c11010306080f010608100c050d0f18 72
    0x41c00c400e0722644a805030034840b40e6400d20320008501515540302074010414a58016040000c0303c11312170340204100105100d403541241d080612615000700030031445544207000c28407821610b0744030301d40829442d000aa50307000070100c103403868443c0b892203000501008818001040741c000c00078024006d0801500741940881d03502e041620500118103242d01c00c810707402d508101c85401c4070000014880b04542200008104189040ba460780030388500d05405054900d0409003004164011804900c101d81d240b608000b400301d170117540b03060450034140013001a00f01010540051820130003940e040001d40c035000680f055001c00401e246603907504207580c0c61001004010401038200012030707a000c0c05440610000321041000303484000542001001c1e81204602c261f05e60b4440d600c00c4d40100382c0107084801c14402200e0380380c0200828060800310f4003401400e0f58500304036004007184003101d6900e00d464900006181c1005003110524a15441c4d1104010b40c1c50405080e100d02d42140112 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 958364631 1250 958363381 958363387
    0x8040503100b0306010503010c141309230709050607031107090207140105100302100c0f02091501170f070c05010605100906111c3b010f031103011424 66
    0x90402d480c144d4146e00c56032180e03040584400405a11038000c500c0d40c0006244107441c1c1d14401d0715070300c4440d01070304410700580c908103c2e261107990340409001241c894405100c0191582c04080702c44903894011281c0140040140400080c4216101c2c40061103002c291001941c0354071952059901030701041e506400305116030201c030300302840343c84e410503c0e4050300302038280303580d01050030381c0400c9130f281040c0032002060303005100c2184500c2c0314181d0300400c108510b1410004400c3d60b0070b10040d68500146030a4071036a011154001c01a018070b0b40710020410703130360312020308448481c800802140d4654a6550014898a0359540811100b071305071604219641802c42c002d04030784440381000c0c9103034007598080c000b51900c1c5009903402e20051508400007034104105006405c0c4502803151210100042040302c1c0d11000c84000040e0000da07903c083c09250f401c02101500d0303a030304103144940000c20040280d03510041c0340c41c0740e9141c0900041c50350030043c00d15110368035664040d81c101c41c1d000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 958365881 1250 958364631 958364651
    0x2031518031c020319140106030605010302030624071b09110913150302180106170f0f0a0f0c0e0102010c0203040b030f090703140a050c2b0804050310 66
    0x40c0d540499100965005505000b40d005490910850606107201107680c0000420a071045140f003003070b800c5001503001d000580c0b1481600344015024400d0300b00282c47e2800c00b254961190085900030a030040034900c140698031556000c00340f46460300c04900d941001050001000451480e0480c4c06844142026900e03200d414802c0d070f000c0c0500c0130001d250420040340d140d5581a400e07600c00240401c00039201c1000a4143d00807001504082d600c0f1040a400781c11092001240e18140d414513901d60000d0079038100600e49000c820b0301c1c481c2080e01c5410010700e183d03d0201e00144d112074881400718600d001c00c245503040b20b41c10050742d80011045074503071129580900400c00c400300984008c40c6030a00e030204000c4c03240070241c1800d003000c40c0800130074001c00302000740002031a0004030040c2d140078481d140c82c1da5a16150f004840706d01650101043c0c030f2a2060300003845140855610014002d0004e8800c006a00808205c5000c081440081400e8900304401007070381100c480006419175003 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 958367131 1250 958365881 958365901
    0x9090906041b1203030b0a090e0a1104090203030f03190e160e0702120d0609050f190510030206090406080634141305030d03020d05130503180d020315 66
    0xd0740520318901e40490404201c01c180c040600c50344642c040c41c000400742940c1c4002204041d140d032000750301c182030261f0140d071449c020070b40c40851f522844002c44409000014482a00c040c1100698550030900c000e02642c00d0503001590302004401500b4a009001140d0f078046038020030014502c2d40c00950400340c0d492003102170030064230481c0900c80f11803400c01e800a560342d0311403502010782d0001040d48035036400f807a00454043c00c0c0302c0340d041c000e5140c0180100520301c412280306a5000100807410301c50b25030f500c6514015207130060459120b0b4215000c0c010a540b014203256005a80c4a4001540f41824000c8901804145d4030b910003203840391043e103010505400d051000307604900c40703101c500e0382c00c80030140d10b504110050a4442d0f440d22500d425038500c6501464040c056100300c0744080c4c2d456030040215403d4031000300225150411184400c600d03403500100035600400032510840d94010300c06d014124010302c107003651080c80d4046400c0c9101d032414040d8043c0300e24148860b400f2 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 958368381 1250 958367131 958367153
    0x1c0206031f092c03030a11070803090c0907050702011b020d21021015052101020f0915120f06040b030a0809040e2415120a030e01050a081602030909090604 68
    0xc0c400e5010060050710380400743c1302d100141440d100950b42d07404050301202d0000a1b5245c482d002140c164883c42c100011903160003254901c0d5100e511050001048a8041c2003a611000d03011fa6071001d842c14482d8035840001c0c55403000b80d9001540100740c1c00040e1065401e615182c00c2e282423480081c5249030301038900301403105103071001d609148245003403402a0224108a500844103c210901800310001000403640d003220055400041e5603035031040341c200140040a010f9403150101072021800c81c0090240d641062910b8a51b1000310780707841d098900198002c18010000a801028080001c0c589540008210340c10603010924030b15528040c810b42405041407005040320680804540720f540e1140300001415500200100f404110064650300b5250b00140021143c6800421842d035030b40c1030050102e001400204410b00c0952148050b6030404110346c5400342c56440300c03049a40b40c00400700c5204114403040c04038603440d0b651030000b01e005600d28405440d290405080040340c4d05 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 958369631 1250 958368381 958368431
    0x30501090b0906040222030c0302010207050603040b061212070b06120c0d0b0403030f05041b0b09060a230f04030b0a0203040809040e0c0310020a0207051c0206031f09 73
    0x1601c1c000c1048650b4480c0340d41c1503400b010483d0300582d500084a0383c070580080d0000541600c1c0b030300903008820003203020911400c2d81d000340c08582c0e40c4c030386d244104401e5100c21100107241004a4011481c5803c00080e4452580303580400c0d03526006c42000d0403080354202060a03030711000a6801c3c81401d05242d003900d0340c1d1120352009001c1015640d8003162800d107250000420f035011600000342414466440040e0444200d0340901c00303400c2c5400c04095000d540705112003045c1c6129000518104030008840c1c1d4220302078501410f010455400307640b050301400c1c14a103d510b00782901003001c81080004c05600d035007440582c1d122411410440720b82d405c000c242848292041044c880403e0122041e50a4450211000304c2c051411011080c100700d41d450100c1d80500c11650310a12810942c0c0140c030b140d0215908981c40301d41e03a0020407101168609450741110700d450000704c09420040c3c01542c2c4042d070500040c0c8100c038940072000d204175403a400480700e42d0740c071010a22815a2621a04515 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 958370881 1250 958369631 958369649
    0x1140105030d022e090b0f0f010303140903120307080907080f030f0c150f07121109041d07031a01060c0222060b030411010f080106210902031c030501 66
    0x50090a0340c042e650b03511041c4510141020a03c00c0300c9410809441110540d03a40c0304c00380b050809902d00030a80070402e07a0318600010400c1c00088011180e805801d0480390580d54442c100c001c5040e03c00703c0c640c0540740e03241d01030181d9054094058900002580035140540e2403000c90328001c03022504044c2c0c1904010003e03008444c840041b85d05c004165103030301440b01729070740da03030151018400d24151340040702210811950040260306482cac02c40305407048569131100d00080c140d69011504680c0e41010121248001b403222602c11300307113030f441200b9094841ea03255060b45031080e0340603d06107483c2e0007144d145408100e00c007c4981c0514425004200504204415980e02d5001509e03040014010741e0301c00c4068240d03140c0e440c0c1a60801c070000c15003a41301c01e6a9041c0350810744501582c00580a000c14072a2103850b41681c465a100703812110a60780c0d0b803240074198031140c103001600461480005890f00b2226015039402d126805d4184c0c072080e035042980c1c4c8241809070583d0380585c804a01 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 958372131 1250 958370881 958370893
    0x601140309062d150117151302160609050a020315070207091b110c0d0f02030f1903030504030e0a0e04030f0815042c030c06061c0210090b0c0114010503 67
    0x1a03e5860842c031508250a501401e2040c403400740100c90744c110300100203034115080d0091018449841c2c420f2600b40c2c109503600da2206068032041c109034400c80391208144441c0c15030b1900800c400d64030405d040d500c45c0c410b45005501d0303500081e25128100c1018603a004444040c4500c85da010840c00780241103068040c031a00c1c4000700f60f0310905040310344500074005981e40c1411900414031810024000040c041d194001840c201146401000c020490280c89450407a40c01c0c00c81c00030300070302213107142d00c0e40400800d01642c0850151a01600c200d003440307160411405290b6850300401c000d000a494208036038903203820001c00070340780b1000c0301c1c091050b407909019401d00101004110340700181d030081001032803603501c1d0071043d034100f24102c4004c02c40b0400e100500f00c04030060036074501c0301086030300703940b036540030401c12002c0304403001c03018540d81c6101401400c20204c0031401d09414203108400e613a44401140301940208016a5165583c80d881d030104c1c100501d42c503024210980040c01 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 958373381 1250 958372131 958372201
    0x1205150f06030702010f1a0a050301050f19020904020a0503070f092402030f0406050429090409050c041109151c020f0d0c03050a0f09050d0305060114030906 69
    0x80002060140501071400000000d840c3c034006d400075440b011020301c00700048542c40411602912290a489115290002c40000c2a01d01406502e00428200c4010080c940710800880703901c0308441e0000000319000c2c0304070001c0703580c2c0b40301070940c401483d02c0e030903034a240c0004010007500c0389c00071201c184424102d0901c041d04912501c215600c1300003103141e6102e24440001e03469801203900e5200000340000340840e82c2a07210024000301c0d07a151003009008007640c0000610501100c1c0741c2c10711201c0c24442d07a031003442e043c1c000c44801c81c000d400f030360103188003140401e0a9412402800e2800b500004408a0f141800031000ca41603065016881c14500442c02012074104031003840d582440c0c003c500c4901044244084074103c1408a00400c1551b010f00006006484119030191300d20b0b1030038000200c0c954050256100c03903035014000d00340315150800c0a400624001e4a05410081d0000c080c0f40d0b4140348000450240f242c28008150310f00c0c2050401008002050b2820304880c17903010081 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 958374631 1250 958373381 958373389
    0x402030417030606070c03150e0d1d1201091110050f120912191806021c1202040e011401110703030c171c0f0204060f0c02041506120515 60
    0x1c03480c1c52003210380c2541ca88543c0300050071401420790151091210340d800000300a41c0703a0640c6048501340b1424007202085129007030b114a01d01d201035001c10301c040340e552400b10f4000307030740c001c00200100180400c85a03035481c44e00b10345800c402258202690016071406180000c1c3c00301c3e002c2640e2511174a480030502050b8058050003624655040840b40410921003040c040c643c0050703c2c081d4216261010702c00034070b6100c0020140400070840c174119501d0301e081040c3c121002e44605400130b05210660b24581031085002103540420041150300c076010300c0c6901d00080c0010040208648207550604000840c40b0302c121001c1c03414030030a8404207841240100d408402c4a8140c201000b1544103400c11708510341700c01250010f0f0104c0000c4501100f4200ca0355410307003205c408410090b201d44841500102e200e240140340c041500b9a0100b00001d105500d482909480030300080384408054a008080341d92a40007000458102e42c003420010300d5a02c83c2503445070500c40e0859801c00a50081 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 958375881 1250 958374631 958374653
    0x705090a030c06231305150412080315030105060603060d0606080304062c09240d060c0816140c0102090333060a030201050901050c1005070906020f0c040e1501060906080604020304 79
    0x46c0d405840a90502c00d0310402410035107004003012608109509114600060242c1c411590001c1d10400000c1100190405200c1c030340c07103a440685030b140303551151820480000280c20701150000c2c0c540c0c6001c81d90030b60900103131000b00103d40760303054291012200c904c84c0d4014282280010100c0f41080c4072103568200c1340c260070185440102400d50060302d003036000703212842c00c0b00d0380000302d40da5180108856503001d03a401515036a1542829101c100040001c00ea4128204000800b8030f580101100c0d03189004000820580e00010724101f520404a403c00d11860040d12a04503c003482c0307074025586000b0010740740f90103804000c9510300000000c003000080c0c000a4108800841d084020f40d00036022180c40c080040100d400000c0011040000b5000c00c0300c41d00d0024030010030014419000240b01c04402071440090b1580c3d80d4150706010013000a01c2441e9400e20a07041c0d80c01a1100707020b003007401f0380499a20030408604001024181c1080a0b207840c0c0200c1c410010880403da0300d41e00707 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 958377131 1250 958375881 958375889
    0x3140105100c08070803010504050106020307230705031c02070807210c0e0a0507030b010e01090e070c08131a0c031c0e2406010201140705090a030c062313 68
    0x4811006101014202d4129405038402842c03910000341c10404d00c5460400b442c100c42e41180d080c80b0340d80e20b54108a0712400b58120044c844080140250030701c12132070003800800b90542c0100e80b0419510320000b1b10f00222540c0080194690340d1aa0071a29414007404028003002c500800c0d056203812940e07004c55410001c0b800512981f10604ac2c06c1106080340c21008103001a40b03003005003000d08904004120a55060002c207280031000b800070350040c0007140301c09a0584415150910741414040c440900411007010000602c00702c07400940100050101e04642c1007218000d0b038104038171070066072a8201c2010b01c80301d0501100d640310303000108843c01e130340401c42d05150130a41d5031100009454404404006c1c0c0c05030f17078050310030604118005540001030510915064690200581c2204c05d000620b80d9140b45800000e041d150048004104100014110030242503903510342070345003200d40d007240340040c001a0450407201a4850804041501405072500d0a4005030256811400503c2 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 958378381 1250 958377131 958377139
    0x1a0105150f0f0c010f0e1b0618040912023a0e1309020112141305100f050108160b0922090302030405130b031506040f0908130603140105 60
    0x1800c450744800aa003900e800016500003951107007402c1094602030600040c820182510f000400d01900f140098400740284e07030504807060010888040c454640d1001e4441d0700d50342c150000c03101e03c94682c6c0c0300d8001424021000116903d8694000a040001c1c051100d0000d420707458204a030034244404c50a00b0201440c0854440c440c41030065a0360110400300782d51118075115000e20110a90b00030784c4c2c20754402d81e1064160b02c6104c051904513418002022184c4c1040c00c0042d40f1103c0a0a110000354081d1040f9451540800c4801080d03a007054241030a454a40f00100501107040011801110500384a07810ba5810800e035409280030319031049110b000c440f079503c8004040b2040c1004e0a1407010b200384030488443c00c0280d560f912500c90301340107030141d40c0851000305e8944030740852241d001f405400400049011a0141d00d4098140c562090b0b5414040440b110644240d104031413084c100503403510300759004e202e49111503030302090034503040000d0395101c103608500040c1524000c503 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 958379631 1250 958378381 958378387
    0x32609040b040921030605010c0c0608130624050102031908070c0c0b180303210403050c0d030c11011a13140c0c070b070f03080414030a0c1a010515 65
    0x2400160160811410113058500310708140409245500814001e0726040e89091281c0b9655600445611903400805000f21001840a1000ca4441c0c20340d0358010a020a20401d880595100c200460703012019a0880c0c08511510000400704400320200500b801d0010f5410441c01c01140341014031511840f00400c514000014441c500444c86682010f400110b0420401c1d01c85100700859806a02e0b031041300c4a0381210100c461030004101c80501e107843c10000c07901090b0900c4540c603460b001d401101403010034032164180b404d04008207020710070182c0d40410307400700f089009412005081e06031649641400008110904011500c0c2d02100081c1d0341c801c0805c4005444c00000d102c211410114030b8500780512408500c0720002d05036141545090701d52007a640d040c107a60701d1040c0070005103034069524811011078050441c90354401e000700070114041c0b09082c8060b00b5a407004200002140200c030046052100c4030070003181c8130040c0b01d050a01541000c0c0040c1003000e03001e0800c800d41d5400 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 958380881 1250 958379631 958379651
    0x60601080c0711030709020c03030405120403080a12060b0c010b090a3b07031406070801030b010e0403030b12010f0f0c080c0d060f180c09060815030102041e03260904 73
    0xc00c00c1700300902549500f151108012810036441e0b03441610191001d04c41c1100b008046a0640115800c9a80c003901840c505041d8400580b040608054001d1000d0b5031400f0024611030100c000301041038441c1e000140c041903a10403c400d03018003504c031103c09c9182c4680d4001c00d01c00d80001c15501585007440c040b40007019114040c21003244220b0100341d0060500002c00c00171804414010044040107885082d5505c2c50212800b1001b48800313402c03154403c00400c0f50030901042c09400138002c0c5404601d102440c008103210501c583c2550640782e65032000c59102c0442842000c04c98244408180184446400c000b03141c100040c0c00c4038081d050018201038000420742c01b0320002c050702c82069403001ea03241c40101007a0140014421340318105000410018401c0d0511700541d019900c80045503100c020103020414880034010303405641c200b1001c250340551340101d2022004084201d4800e0342907160006e034280c04030348140c4c10202d424007401401d10b0407a00382d41c80c440003500d00040c3d05080c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 958382131 1250 958380881 958380883
    0x70212071b0b13060e010c03030e0a050a0c080f0705063c04050f060a08070f1709070510020a030c170d02070327120b091c0908060601080c071103 64
    0x184109421030500200300020340b80c0c1c0044080c00722a91005040368a060362054140c0d00b81141410b03082c00150382908140000703000b0b5000408503c80c0400304c2d125520199226450b2110903d03017a039100314030190030080c1040420034400394125540151180c1441c0801042c214002c45441d6242c4003031a2041482000c3d4002442d40a482c41540f440842c42e514409241598000e006203405019241d12001d5030342840801c40313030b00312059540d203501d6035541d00d821101440c0b881a090308101c9250225840a403074031034140d010791544406812038501d00f508002800090780c03482010754100300070510100703030001c040c030801c244c004803c4440e9000451b4040c085226509400c0101d910214148c004d241d4030151143c03901203000301c0c14503003580c1c00b034600c540c1e0002440b4041000004be00c2c690001400d104407150482e07500300840d040e40e60510142c99050300794030201c0e8000745040c00c04020140d01005210b80001d000e0074181540c0c01d02800d041507608c114000508140305880e0311700d04c1030324 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 958383381 1250 958382131 958382153
    0x50304060b01110a08090109091a01030f0e150108100608070e070c08190801050901121506090c0203070b0f0f07051605060109091103010203090a0213110706050108100507021207 78
    0x3165080d1002d81300320349800b0540e900044004c0d4005205a080451100120700ca00d540d070899034003025070320b5942140110080e09181c544281602c0c0c48561070f42c801c03801004a200d21040c896004503079503040695039454290a140452102c5042c8a01002804004101101070324858a1612803650f00c58109075280d0003c00c06c0182201400692000c50542411114142641a81d0b6a085a0b40d8501c10442c10300740030b001c1d40c503040700b5002c0c0e0540016040000240d1074440b030303c4080340e20b80c0d075201c144088400c0704400c0f60250b0800100c2400700700c040c500341c43d4051080d21119a0908200301d40300549032004000100b400b60008403480c050b4261602540b03090307440411194070307603141e43c0082c001d000c42c01c00441e01c40c104600320b094546418000d0320301c100070b51401441c044110303400308154015401d08080c159030752001014100b05080000703040340b6018802c0807c01c1d501d0400140e180c080341b2000070102030301d0302e424454000e501142c52800301c02004038051715407042e41010400c813030f = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 958384631 1250 958383381 958383407
    0x22103030703050123031c03060306050f1b0c0a020907121506090801090503180a0e01030b150904020f06130e090c0111120919031209090b0f01050304060b01 69
    0x1200220410520a41c5070f0000390580c0c4608242265070540b240c200560040c03d00395031603241d0040c1022600000e01e2505280882c080d52501150240e0343e511804110780d02547d84c0c1a070415000104540034110012080309041350034152850003d0790a1680d483e00c1d0129002480754484601103950390b803080c2c80480c4d10903103061080000095003100203d414a09124200201d9074150f4002000c881c18841c3c0220160890040d40c5802040c41fa0038031f038125440116584022a42e0300450380c40715520b66203003e14403ea002111038204580c551001c0c08004501500c100101c01c10000180c540c0f0002007415001503601503100c1060140700010000150465009105941c2c104400c1c00400913840d0300000080c1c031511038090100c0c0e00c0c19140c0300b03d910a0300481c442040040004e00301000009502488500a1244a6166520100740c6041e54180382d0000391514024070500c002c0d4810018400000c680030a401801c60001a100d40030041002e4940c981e00c0300b03181d14a074022032200000e4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 958385881 1250 958384631 958384633
    0x1b370210031e200f09040b010306120503030402010e100210090212121b060708150102070b120f0601030615081509040f051204060c110d2f0f0d0221 65
    0x81503010402000f000e49a101066090070f51050070b82c0103030b907002104e0000703518241d030710324240c200802d210203881d08250b03807410903549001c0001d8601c5500c04426036144200c0155507282400c2c0001001006c03055060b5201e1540400910740403900001d17080001342c400b1318049002c1040b4000920701c0007a011a254085c024001780c3c0c5246c89000e0018220480307545c040f219900c0d161500c0310790700e12040391079802007080c54001c100e240f200c7c0a40c03540e01520510403035892980b141c508941c10b400041c2d240e60480c8400c002e03c8a9514020600c60b4071a1b001c0c6410000140707044501400031000c05510014410080e01183c000e9440c2c4a442040b01400342000701e050805180000e03503a1250384040d240782c06071140390030004da00d2000300c5003103410b50759860003014280d440726107aa200740c0c5c00e1203500441c003010f04000102c0c2c0c40d15030000c035002c20410064207001056040c0514040d20007540c820483d085c41041543e940c14500c861a40d0161400103001900c050700c5180900f0a4030340001c9 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 958387131 1250 958385881 958385921
    0x70f0311090913080a111e06060112060306021201051c0b15040908030702030c071d01030209071e03060807141807020f031917060108070e0102031b37021003 69
    0x2c0c0d90800c0b000902d5490b03500403501d09144c038080e200d907d41241d41020046030032041c0416041e40c8140c1002c2c4112403182d5001801903070307a41c6c0385c1089911007140c0e40b04a07018800100241d1411040702210520361502c40010380405a507048540e0b10000c041a9205202e001c0200e078544441d031140f9042584054500c0d9203007040880650b90b904030210042070bd126200d80402c4011030414051480030703668000c401c81d6400d6508000411000800c2c400401412030080002d14000001020710780c0040c3e20006426030506902d40c1c202020707034100d100c2d1101510440030345a1902441501940d81204106000342c803102030890500c102210710042502c00807840c0b1300b01c103501e040819000c0c0050b0311a201b00d881409185525100c1c106d81c7c0d035010841e01c50006001e01e01940800000c07542c144181c80c0742103e19418410540900034528400e940038220404c0340c0e4a4103407041482c44000c60110520b070460305007106006d1240c0c80001d000c1c40d881040c2d424014025000516012001c104c4800c0e = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 958388381 1250 958387131 958387147
    0x10c1113090218060a150905011b050628060608010b28030209040614180417130f1703070f0204090609061a0f01020a020d020f0a030b070f031109091308 67
    0x96003c01c2541e040d441442110400a21070a04403455503550120380c5910300018502001552644480003800701c04e00340d00c41105000607401d10480c0d11640c3d580c1c0c03907072155111503100540444c1120448114079450310703000340b003095000b03030b4494111000c0c3e4600a07568000c48180f1b418a17202032032070700c81d228410800001440e81540181c000c08a0544041000d40d9484074801c1d0104c1e402c1600d03036044041c40e2041c1180e4140041100c1e84580200080344142012207030b03c017141da1200c1c00360110348415160500c1541061100c80c40100307068100005100840884c180c0c03648640e01300100b420100d80c00e51401c40d00c454004520164100d6000c0140b8500341c105003001d041d19050380d01000c007e00803500d070b151070281c0d0008003451069005150031140c90303090002407080c3c003405903880503d4040c108034a607981002d0741d010f03505c1485070208038107144801401c855407215200d414103081140c0c4001141c0ca030f03815200b400c0000c517a0000c50f9254104122090150004003906880740050109 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 958389631 1250 958388381 958388419
    0x10e0115261e01180c03021212161b0506041509261515240a0e0a0b04030201050f1c090506011805190b010512091b010c11130902 57
    0xa0b4811550030000d2240301e031441c1c013058520800e8a00100454040c00d0207001504008540002c00f090030070403110509034903050f243d01d03a084024010b05000101030300804020440f03d00c01d503810b452102c451f41140c20b01300010b205001f90b00404c1a1142d007038080d1090240300308103590007008000d120121000004004413540040710000d09440d00c100448076140762000700c5014803800c0c841c1c40141c212a00e001c20800a880ba00143d00302d9071859524021485aa9000402000c1e50750b40710710303d0045850040c41480720040c0d000580c41f0b14140b10410150b40c012040700c40d07200454060326900c46145c003204040d0000d190340700d24030901c1e1150381401c1107000180c0c0d6050f00c1541c240d003800c000381c446080b4282d441c2281c4510b0100c16024649036001c0c1e0725041001c03d04014142681481814548050282022180202c03903502c1003202e071200c05892100441c0d00c00c02880c1a5114401f40e442303c0383d0404d000c020540c0140c0280201510040381540011182a4010545081c15601c101c0d10 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 958390881 1250 958389631 958389673
    0x14010e0d021e1305190e0c090c0f040302090f100512030307081018051503010c0207050f0a0e0a05070e010c0b18031603091505160b0a020f03010303030c02010e011526 73
    0x761110924101d03800f5418030b000920768401000c003c090990640c4c601c80529156042b0610000b6045000d200c00700c010394072070450034407403001c2003200b9040d07140c40e0345100240c00300e07680414080c00c0b2150745d12840c500e0200490f0350002103400d1a800300d840345c00d01c14510039010b45c004c80311400c4207000d10003590407641009001b250700d5141400e1600349101050300301e550740c1c0b82100140e408000100205c0c10520961816094020001c5540582d030700d005100c288030072600e9000b902d59072000c000a00741c001500c56a030100a02e0002da4903041c80e82c4a0031218030180c4040c044840144240038211400c0086418003001100902036148040c40c0142c04c0d841903024003284108094268045948100190b8165180b60600c00306102465103802c41090700280c070508d10b550f0200b102d0b442100f1038100950096101755000900d44400100c024210380c0068104811641480f07030480c2068900500e20065400c0c020b0450f15420b207500190702062040d2091102d03a005965882c0b541001e80010 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 958392131 1250 958390881 958390921
    0xc1113020c06100506040512010f110a03060f0f030206091203130806010806062107080d0c020f0103050f07030b01120c080f16090b0a020f0714010e0d021e1305 70
    0xc032101074444a16a41c1c1d0110b00380a041d40003541031004025620740640c14100e050138231000020300d08802500f003025240390501401d110180000c80151040d03061041c3d2009007200056111500d06112402c100180140304c00307881440046148000e595400c00071400000390700b41100c0c0e4900a0540508601c0424400d02c80c50740a14000040c44c42e00110300c007446600d0040503d050b100a80030740715004030750407011848520a0710f41c0810891400c003c4802d1b400311507190380c200d544c41c6104015400e0030f15024181014184801c0c418200403201c04030780c00c0051400c006c00d10004440c012200406041c2e4810280350901e01c141c010729801c54980c81c01000400d5940d1466500c2c211460485c0301203e1030900003c103000c804011810100010700800000d0b44182d0301c18281440060b0719001035030b00407080700414044c9482c62903070400850040d01c0c500b80c44c01100c80c0e14680000b141d03948600440300e20244004c141190310b80c0c50a000c6550f4003a80031003004030342400c0c03d05401981462031 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 958393381 1250 958392131 958392133
    0x10030e010504110a050f09042307061707020307050c01030b0616060204050a270902060d0207030801060912051f0b0306010305070317180f04020c0316020a0b12070c1113020c 76
    0x30103e100d003402d400070201b4440107445246e441e2100d9642d4012840c07402500c00009003501080b00c440300051000784002c0034556244000340c1948020312503030030300243c2490103661040080100244010031007066040d801d0030009101014000840c5442c132075103569030054180760114804020725035001e0b10698009884041042d915540e0705078106594509a40d0b2894104040d0154003215802800d070842c4040c0c4064102090000c1c44001c1c0c1c5c02c1800201c1c04180c1d400c006104540d440b2102070014400f82501488191190312282c1c0c0300e103401c114003c0c140148280303004a0b030b41f0940040c0d01a04000d42100d01560792820002c0e03c644a60100f1074180180510f4400d041c404602034a0b400c010710001a00010340c001d0411500400141105810a07024010065404014030191400000d110304800d0000103500c100b220481032604186403035001809034003242d03075031a0301995110b02141004462070050741003201a06c2d43c111082940301000c51000d0414540e250003070311400720060 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 958394631 1250 958393381 958393399
    0x210507120206390a1e02160b030c07020a03051c0c0206030c0c0c0621060a0b0a0c080403080f0711040b0f100c0209090303070f08060d0210030e01050411 67
    0x100d02261a10400d07240b0314880c1045403102e18a60b10070300f402080140981d0800c0f62400c004103035112064121080131400302d1421501015554445061052030820600c00b0b8100000b01e0754011001d15400c0c007800c0c244c54004000900c0c08030310a0b080311011034000702006112070b0769160003540c820a2a511400710b188000100103c980980c10f80c010256004003540d06660310740d080406250042e594060781407007140c20010160301da26004101c031034101c10721403002c3d60b0300412110880001510441c0960003411041154940700801c0d10000301480c68044088900f0703061035400c80c00341c2d40001d413680070002038459020f0305030b40080010328800e1140c070100415002c2000101c80c003841e8601e8100c204100e0590161a104190f602c01081c64100800324070520f070041140620212607140c550362002050103c2c003a04550384440c02c444920b02044a490f08a01041d100d2090b004001d00803103c1ca4a01c0d0f804074082e41288070454140c00080155152900f0a48840d040700c40c1c46600801c454 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 958395881 1250 958394631 958394663
    0x3210207091a04022104110f010e0a05010c150c0e0a1502060f0c0d02040803040509060901060c03050a0c1a06101103120a020f03010602030c011b0c030c210507 70
    0x40c051800301241116a6a0086540d02d081c070020390302492900b41d0107042061804d41400c000d111007406a400703522002d0312003402c80c042c015014580030344181403041418031142c0558900b1109402c2c0c8200f032800c00f00d11100c6103071118480b44c1c1da0b1301580180f07040003290348826903c03101c5070204003000c881c2034a81d00d0f542e200344515518040e001100607080840011107002c1c40003d1b0b1500404410710781c915003000118401c08a070855001200350780c000140130445c03032800c01301182d0802e01c02c03075008000d9494104040c1000781d01010087c01e201002c107102003000d001d0716601001c070341c112810036400c2c513545d00112040e500c11500c4130310621001e0f080041d01e6100740a00703510b8220034401540b501e201690901e500b601c0080880c041c0303a40070850403100002200280d4003c00050300210f40781c0000d40006800d50364200f552040720100c0e040c5001140d40e02c010749018040d014103180b014440c0da030400c1144100c0c1100b5130304822240305030f0004443e40c404010060240a0b0f078400d9510b50300 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 958397131 1250 958395881 958395899
    0x2060606040e0711211305010e0a0927050c09010e0c0a0509040219120f02030606040303030f1b020709060e070207030311010b031515100f0c02030703210207 69
    0x40c50082c1c1500c2c2c1e07501c2c800102d2035402400c1c0100e45603602811607030309690420000c0d080c1c015010400c2100c5902103074941000c81c40e0f00346540640300900700380c240390301e0082c080703020195030303100c2d1100141e00c0e100c0c0301500309001c9002c0940350158441c13000280c403440c188242e5920700d4410342c0c2c1c02483c08100015902001803010f0740507110300d88040d403500c2448007013200d013074111480b42c581c4103900700091102852000300b030040c80d0080d80c83e0850303002c5a1807240350484201403a090b544500400400c03200b0750707400c011a41600d9050030009824603e0315690b800a2010310401080170124100c08420903070000788100844602010a0007101d413201d0380e1002c2d0040584003400980e111510520010780240c0100c0304001c0c2c2c075000000ca122254000900e400c000c10040c8140214540900c000038500400a99500600380c81010395126000c0700108503400310b104681c01c001054446408642d000e010200c0103540140c0c010029107044201c02c10340740b11910601d030240c0700721100003c00d008 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 958398381 1250 958397131 958397137
    0x501062339120a0f0908011406031207080f0a1e020616090302090c07030c080301140a141818030c010b1c030507030c031e090e06180105101e050a02060606 68
    0x22aa02c4040c10640d200d0340594140e81800d1400040c40070603d000b05a00c402442490b644800c0c120150f010303401d1040516041c800d8000c00c8007900c00302044000302068904003141e42100266450310b6071164400c5080b07800c1c100010454a40e00e440c02d000c54650340d4005074542c042c0c003405421501201c007441c0c040c2c42e50740803403100942144e10710002600c01d48204000e80b0010340070b810303c210440c0d0140c0d80d128070380d4000d80189200340142a030841260518801d100060500325094070322003a031a40000740c150071000a800d03411700039900080d41e02d4a84422095109070018100d0b9160083d00e908240603044100300d0500554058100c0c1c030117000b0381c0c9400c02d0740b580c044c3c0301c003440d00445071400c407003510301c0b24000e5050100702207521460004c04822f0240343c3e0126a80e8034249414100242c0591201915191103803100480c80407070300745040c000700c0c11594100c1d0381c0450201050810340c1c00c0c69070b000d92080d440c1c0656000c5071001d030b040b400601a40b00703a5402e81d82c06a40303000400071680 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 958399631 1250 958398381 958398403
    0x8070b01031b030c0b0309013305010c0b06040c1206060203180604050a0e090309222009040e0109050312041a040803160903020a08070305100501062339 67
    0x5150407003c22001c60791750002e41e0032100110000c908a03030502d171310000040800c3c910700801c2da0b18100000c02011843c0511014000c02d1804846074042c60701d56a602000c0038003400e1180c1d03601c1c1304810b8194001d126080e48072485130030902070140d4514010392250086060820003402142440009141c410300301d0b410b641004110745c07061420500e890444c201d0060601c017071072104000441c040d42e24180c0765100040041000960511103010b22029214458405400510b90520301032402400a090b035040364000e40317000800c508100c2c0c246014001011b4088c01c01e00000030503050451056400520480c020040c40d010040601c201c038900032801c0f03a010300041814030100e80314407105038004c404401d00b403a00410541c0c50790001411180e01d40c3c040c001703a85c040882082000000d02c100c0c2242d01503184204407035890f0040141803001108218842405045500c1010242e001c0603209004035040240da4400d0300d060180d041c507154404001c0207545c1d42c40c244214010700180c42d11481c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 958400881 1250 958399631 958399643
    0x190f061b0b061c12050a08011e030f2406031506031101050703050d0c0306050a0e1605070809122805060f04050f03030412081623120a091101020613030f0c08070b01031b03 75
    0x272481c58070703840e1603849000000c4a1420118215508503117076a408204941004440001ea152031461300f0401001017140d5051001e0911b48100081582c488440c1e80e00102800c1660340c0e1913103032808441030b101d614030103c03105140c0804a038070140c0c198048402d0314015540004840d80f01c0011404195046032900c0406070000140c9003442e110b00090040f10303100c3c89401d4103207a4048001852141c00030358100c4d03690b005031200e201307070501c2544030824024030780c104910b00d00040d183c650316a4001010980c01000c07201c00f183c00c0003020031200000c503038880196600c3c1d082500e030100581800100c5a400a10382c400800c0764003100804d48100050140c845c40000021004d141c900b12071594421100044103120a03204103420b1007200344101044040004c2c030800500e070503814088600700b4181190701110070440d00c0313503004101d01b40c0c03d600350074a03c40e5480694812211458281c00c001c0034880c0104482c000c01c90303070190181c180d911030b031401c00c240c0c40402003000d10100d00e0310000e029 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 958402131 1250 958400881 958400939
    0x8010e0d111b1507030f08131e03110703110406090c05090f0f040c08061e09220f05060412081311190f061b0b061c12050a0801 56
    0x1d010440d0b08403007800c00003d400d031103982002642c0910a80c010760b5003540454040702d05141807075800450194000903400200d800e50755551100840018420245810081200f00391400e050183c1d408a001c0e4030401c0071148102c0c0c480ca03005240e115088a524096401c00d9070200d240c510b00c6c024015031940e00c6e55140e041021030700c200460f0000c240103c0c0d811403061120500c20391100d02500303052000c55110948241001001e1003400f400c20400604040d83c82d1400030115580d034070a0b280c1141100d82145c0001da0401740d514800f07450101d00070026051100c16100b04800418440c0c881c030300034207610750031949100060720002c00494030007520909041000c00001d01c5103040740c4512001511601100401c80340c0b248440c980c0341c01c01c0034130b003042c2003040050035800104070450b801c86810b000318100c45940e42400c1d8040c05480503100c1e2024121406008101c01002104180c02841c1c40c07540840f101e40c094110390104c1d407600d00095000d800454401645001020354402820300c4a80b = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 958403381 1250 958402131 958402153
    0x1d0f0c06070209060d060e060a021804111b0106120b0a0c0801080319051c0204050319031209020d0204290a080628020d05160e0d0b06030f010608010e0d11 68
    0x5e0300d45420482150030035924a8a43c078000802c1101e140301e032014000050b96400b10640d50620499001c0c841c0c1d00c01e038240001714491780c00d04410b0310f20040084603102d10101e02c603130340903016040716000840390307441180783d0318107100c44101607600a123051102003014400b0040d08544200c001d000d50f101640c41040041400001703600c02c2031190200e032078a00d00f4107a01d00d248a0060040b0004d0100c9075802040a0105d450b080c8444c18507010103100c0d2510301c0d08035030b6003c2c210200944245070b00380d6030307007910105646440c1020032031940d00030400c002001d0800320040e00d40c88081807110b001c880d581c008114a0420701841c0341030b60480c0009000c142c1c0e5040c02583e0515113420345444690140e46000005455030021b000c0c00f512451021400c0c0c40c04010707140d00300191244480030010328800c41c022640700c039401c55218503004000003c8a55954010a10380344243c02d43d1805580b0b400300000d0004010352121080902c4001038900041d45482c003100c46400c2080440080d82004084403 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 958404631 1250 958403381 958403389
    0x3070c080c150c0406030e031c0c0908060a050405062a07020a03050f011b050406050d38030d0203130905040309030f080903060c0a050702090a1d0f0c0607020906 71
    0x4503031199180c1c1160080b0811002c1c40c1402101a03840c54150b000c0403405000e031681501407000e00c2c030b0503040110304201a0303110b030340d0505010403d01c9843c640d58005000a56110303e0311840941055803c950300c5041410400c4010101121305660b01d00404021a02c2d81e200c00c17940c401011491031520440e66141241c100c150f600100c4120b0348010215400000240c05000001c3c94800c440000500c170140141c60f2091014a2080301c000c20008100501c0f00540050588011f0942e07080d0000d0071900b003255071181c04070746907908080391010082d46440040d9807010016029000e07800d84038100d2280800781d90340c2c003415500010007210450240006400350b40200ea005000786000590640d894480c400c2e8105929401d0380c0c41d41d00041d0a0806050400480b03411100106541c0e2503d44500402402809001d10091003503881402040302400349410040108007030760091502c10008100c101d60301d0f000c091001b1002d00404900c0c026514000059450082e00a809140a0f5a8500400c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 958405881 1250 958404631 958404637
    0x7080c010c030e04060906060507060c030605011704050f06090f01110304080f031312050d05090c09010b0d0b040f0c0f03050124020109060504140c0d080d050612060a05071403070c08 80
    0x10f60741099480344005582205405a00010805911b40c11344d6603405040180036079041d0006007041c981085020001030364080b9940d50b211480030400b9074030b030311540740150030150b5501d60440d10348180b9040c03088200b000306034400d040198500801c0301141c8a00c4da840e20f4001190098483c5205022131440c0c41c100034015940301a1507000041081140d41c2c03450480f010351010030300024800705d04041550f05511801e43c000056400401014800800060152030140546140c10340081201c0300c0f440b41caa004180820401030050110308201014a8010030b03488482a00182041c001740040c54040d1040781d050b121280b9a2030755414030f00301c80347e500c00100304110045660b122017600c00b045c554492036009610a0300685001132405000394641036142e002c991069500644500008100d6411181c80aa40b020003040d144c0c1c0d5400042c907841600807903c0403901a50041100b4101594400303031040c0803a480300c4403085c884844624107404229171350b202040c00e0746102c102184c03c503009 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 958407131 1250 958405881 958405907
    0xa051002160303030911030c03280c09091e0f060b01120f050105040b1008040210180e010e07050906090108060402040f030308040b09030a080c0f0f0f030907080c010c03 74
    0x4540d0000120158420910840c0d0b0003500025518213842e4200601d154442d40005011002050fa200728200041d4072041d0b180310a17404408aa200d1103846507080400c00d45c003981003219840029aa2903026000c1c0011400c00c403034079440c07644110f86e0103075400c070890941d030781010890405491554070703200141680803a481c184100d268003d1010301c0e150044d1700c00340c40031034000700d05545054140300c25508220b0009100b08918803d40c062298450701a5901c141c04460b5045041801601603c0c0540400e4451801d0401c04101060000301d00c040d19040340c0741c3c110702420710ba81d40704044440d030142c4a60594001020000690035600c1007203550307000b1500810041c50a592415142c004a0050f841200498648000c00c0f0a00285410055000c001d11014610744003a8a200401d0440c00510741411101c000c20381d0b484450344031007a50001d40390240101d42c0e5448080f0441c40640003200c01c4190b502c03841e038000c16421000f04582410079010303110740c80a4402958141ca000809402c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 958408381 1250 958407131 958407133
    0x90c18040b22210206010501211112150604050a060315051017130c05010c0809030304090905300d0e061608010e04050c09090a0c0e0a14060a051002 65
    0x220301e41ca841084506450041c0c440c450380c03c40708101d80b4142405150040480007590005c2d0700400590b60000c0403010180c1440e100390300d44880780d080400c010a0000d849924024000c40d5666001a80d24012806083d40000080d280404a8104030143c8a0303030080c03540041c00c0e104200005030194015401d4160140300d000446512100072070f003402ca49004074130014610421098580007040b600710b8110a125860741d445291a4a500d219294103201d81410000461401c009000d40c0c13105590411400074141d0390340e103958030840805061666016500c0d40139a1100c070000b000c154041e81c180011400900c403551032034921412107a003021542508294030b9030465079007288203004031881035414004000b00c1c184102001068844144c20001461001c207040c0004a4030001c2c000440c1a0200d8216503180e403000d1503d07007000d800c2400141441c1c0000c0002c5060104003c40c00d104003072030b00342003000d20b40f0f64060381104201502c0c1c054000001920901031410516030030310324024540 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 958409631 1250 958408381 958408411
    0x31b0b09012d03050123150702150f12060405150f120f0d0206160c02060703030f05070c02040e010605010c0803040c1a091302030c031305071706090c18040b 69
    0x1a000b5100a002c2402d11400a5500c000500440d054440440d941c200003250440e500d03007208000c940703c003200c400454201300c0042403041c00c55032003070140c48940283d0800c00d42c549102d00108807181e0400400032082028840000349682084e214503403240000201c400c0c40014110103201c40e4503105640b090b0003002607903a031130420204000d04545255064000c04602e40360140007800d0043c041c0c903000100e010300034811100350740704004000701e50301107841664807025460164003c00074400c20005081c01c2500308110317a0740003519680c0c1c0c54000d80b401d0000010641116080324881d019860118000380859404101c500014540c00b40c45407030204003064643d4002001074841443c12040f0002c0080c21003841e08202c1817a110701d40400f0815811800e05e485c03480d0075800024001800740c9151402403052000800001e402840c4800c04c038812800c00c1801281c8540d000c4485100c144590000d88150b8288194007122a143c0340744038180941380c030781e500c0490306009045c80c062640c0c7c00b = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 958410881 1250 958409631 958409687
    0x9060d0b060604082407090501050a080a020412080c121603121d07030c08210a030b060a0f0314090303010b03090c0a150f14031f0f030c031b0b0901 65
    0x208641e00c044261100e400a282c082000c1c0901705220003094642004400c40c000c101c0c0da6002030a480902c113250820300341d9a911050301714001d00131030348a0740040c400a0f84030000c0c8401400104041c541035015268000440e02d00b0030001d229501b040f03041d0b50440302c8008013081c850083c10007a0122080e02007a101012640a289410340c1d401c1c8415035040200c0400401c44075552031401010f48001600c101e085103140340701030344140c01402c02c8481d03000807491061440f95009001d181c170010855a118152840010500d00c002d01c1c2100c00b00345012041045000041d40700b03841340c5840307001146181c0c205040550160030161510300984920000b5030015a900c0340070501402800c007042805100e13440e00140400203103400c00092018800c10500e010548104607a070103481802807128803401018001c5401040798030018800c400030304080208803030b24070302c4422070380941e001030051000d45150700444801031050000300401009401c4c1e665000da8041d540c81019000070075020184 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 958412131 1250 958410881 958410883
    0xf03020d05040b2202060d0b1c0b1501020307020d03030b01120e1c030b010c031808011b0207050a081515060a0f0828020c0c0a0602071409060d0b06060408 68
    0x1055804540e2108200104003d03a480d1a16800c480c49071500320309850f0a01d0317000b20700c0502c10030b84185071054403620f4803480d9417144c6c82085078400e034403140b5452090b00b43c02c01400c0d02d103040c2e40c182e503030001c007440e2103001d50b1000007a551722580080805e00001000d6a05038001c20130400114140b080826205449484c0c074400d5602d103040700c0c0040d005a4446140002c6681040d507101d2042c14a400c0001e001d03642e0091002000c3c543c5401c1c81c464040741c6829201c0c41d07241c1c60f405030b0125070a101c2c580020440d01b11014000072f800342c00700c1c0d00007174840c003c004443c1110f028100c12907000003165403050f4940703160320750003040c00007a2403036460b124000300342036904c031020781004038884902e0b0488140c0d101e20300399400300034013134801c010510810381c5000360700810610322000d5402085011074203105012441c902403005106800c1155035041c00fa40343c1c0418072550210031180d401881c2c4605080a1152143c0790050030750140514503910200e0303080d400740903a504400b040c4004500444 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 958413381 1250 958412131 958412141
    0x211202090d08041415041202150f071407060314070c060b06040306051906060210020306120d111b090612160902070c0b0a1b110603010b0c010e010e0d0f03020d 70
    0x560113891500340c0400c42032002d503251190300c04000c50030030001045016801250b201540e5812900c488841d1802c00b40d00b540b50161034400249160300180000422031200028260742c02d404d0306944116984031415011582c055001c0e41850080a001881700d611410012a49521070007000076408105000308841d41c2154008684d1b02e982c94003848000312000e81c1070914007201000c148003075810103d009450350406214010700c2900400828181c0c4e070f41040c402e4030700d8580d10403500c0080034440c0c01011240700b60f611079814000c1910030265100c03185121003280e100906840c00301d494140c14400704611201d48200e09010f0002c580c004901002480030003072004c20400f50b00c5000b14141000342e070807030798448090b0800800c10409440e800ca98050702e85125008400e0f004415420304101590640e1040d0b076114030000004509a50220040c00b4070711340e00320080110b40e981c6d0708820308039250b6240c90090340c4d00800c03044052520031840401010326519025040551a21030303031017a0740c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 958414631 1250 958413381 958413389
    0x1d0114060411341202010f0c05090f0604080a060504210f0f050d0e0606040b0f030607081e2706070806040c03060503010f0c0e01090b030103060b0f0907020604211202090d0804 77
    0x6070721301d0942c1c4645909002e20710a4001d221401c10440d04214000703405449120340c1c0b1402907280c40311070b40607651003405640007032400174251b4100143d1450404018402250212202d840104031303802080c014440320055415140c8656411a02c02c00095500c5006c8104650030440e081000c0b03e10b00348540955402c103070040000f040e072803c118040005840704040f5550203403100500c880300590b00007900a030400c240307040002d02600c031403030944900c1d046034000d02d40c9800d03480207002c10312400c20280404800e56030301082402110a0101d0341b038072400e4a0320310000322080c0214840e843c056003d600703981518100002e0041e503c0c408642944c440350804401295109501c01c01d403904201a040551400d180c4842054244100e100c05408103004c080c140d00c1d9281400d040c0764030786d510141d030f00480c0100411224901207400a65451080310100da1000401080b03240203c40c00d9110090480345850f007030351076000f400c3c15400a4021001d41c40d40140c4410402010071400c10041001c1c1c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 958415881 1250 958414631 958414643
    0x1805150c0a061b020d08190b060a080103150203090c010e3601060203090d06090534050301020936190e07271d011406041134 55
    0x82420000d60781000c0344503e030b0390b20564105104801c10a40d204202c2507024a004c04c0b40508101032007107840c002e009082039150405070006e4900140c6802c0050a4100c07440b5407111074a4180103860340d4243e00060340e0150096218500c09081c540c000c00340868a2240039180314001d4000701111005000d090a4004819003810442c1c0c030800522030300d03107003d41018001540380c0025400410f03840070396004054490b59644100ca401c00c4024070076118503100544040045108142c108040315045203400e143c0d8a00d1500000703160309045c000d49100c100c00070312202901148060391440d50f0703800e141d60b0000d0a031503410b43c000901700c500010b004280000040b000c80401c0c0d8010012a2502c80010500d68007842082080e1100030906080060080007921403222060b0b081d10054503400c1180c41e0250484181e4103110241544514441c42d62401d40f80615280c50341031108544d42c80c066901070880c20014010000c00d5100f4038003020390012100840040001400c00080c20b00c1101141c503 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 958417131 1250 958415881 958415891
    0x70c0510020d0b09060d030c0c0905070302030108300c0f03070501050711160902071109150f1503010504020703120c031d0303090624040f050906071805150c0a06 71
    0x2e1040340d2154071518003040ea074010b02400d043c2c0c0066240c0e042120010200210308400c441040303458a4150000c07d0b4440c0e042c0054140b01e84041e000c1e4009008180346803141c1403108001c0c002e804012201d800340340d080342030b0f547e02c00e92039202194442b40b0f4014042c42400b03c03510380d0000410050800c240120300019013403c0c4110002c2500d00c9003514909103a100c1e0315150f4031a1078a100c80400c440c0c083c440180c0d500c03c5490603001040c601551f40354800044410800d03124000a0906001d05089403800d104032150800c00048004402c142215840180010b110301d04040e802090b0342d90180c100b1002d00302c0300c160076006603143c5001c0440043d4441200f100c4000081c01905400c001c070101541c00c0d40743c18407095569800090402821000500500c3c4a400f00c6039103039a01c0140141040c48000d01d1a04c13414043e06d070903030307522a031f602c10303a40003621741132040044412800c21026182c521601d0f127000c002140440f00e0240c03102180411080c204d0711003c11583c440203205001c0451 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 958418381 1250 958417131 958417147
    0x612150103060b1923010908150a2f0702030304030803070314160c12090803040807080705010e0310090201210f060e0709030201110715021509010606050d05070c051002 74
    0x20384c200b052440d2080322030410303000780883d00382816001d146841e040344174051184004012100c0800c164461255401a54001c82c0c2a00030b040c60240310740e4101c0000c1c00800514603040424025002000815800840720f4404c12089a40140075090008007100d0404d510307074a8020080e80240d8541e001302e0364a54602014001c01a40640d02580c40d1210790a40829181c000c1c000c0111040d0082849841c07600d002c0905000392040405002d800d42100d80b11500d428100c2d039686168003030580244104100042c096100e0103a151551a0103400340000b287c00304102d80203031001c450101d06210080d0700ca90f01e115001c01c0350740780742c0340001c0b00411968000100002110304540040c420480d01100304084150000000c0080f642d081c6030004018003400805410701c3d03055004240890203142c2e512941c5640002d0100008002a59504807601c8401c2c0302030807a210761044402003241484400e241004503402590300c640740d410800c40101d0036a07145814000b10001d01c99410340e002c2a1a4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 958419631 1250 958418381 958418389
    0x40f0803010608090f0606010801260102180a120c1205030f1801080a0c0e060d0207140309090c04080d03020906090301110408100b1c0302031b01320612150103060b 72
    0x45e0300c800d07a00c028145900300880020310103581401041d200c0c041e6220050b80d07000c0f488600702c0c075000904008540300d04c108584841318000c0114608d00c105125900854a60050b03404070440b55405100308400c2c03032610300b00e160f00d5020a0401d0360180014850642c58800321002044c256060000e00364001c4100000501a00b0340500301403c000d1400d2140080960008a000c1c0904001c86045842d1540761a203080a0720030340318020080f00d070810000403900f10000143c50740304000c96140322203030344a80c0340340c03074500943c03040e14440d60280c202542e02902030b50090442c4640640b405180c00da0160200f403c0d66064050b03200314540c0007408000a1000740000c0100440c083e0043c40b00c80701081c009502004c4222000811283c0301640c0820103000f00f04840ca2070001060407280490285c2d48503009005461f0000355240e1031410400002002400701401000300e0f8050500c2ca85802d002e1003656090342d12450070505c6550700c2d4400841021108d18005c51003003030081011070307001c0240 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 958420881 1250 958419631 958419643
    0x1d18070b0405090f1b090d0512040302040b0d030f0e0f090403020d030c02010c020a1e0f1b091407110f010f05060406050103021e0a0302091e030f0c0d0b040f080301060809 75
    0x1040e001440d0061040000c0c16504c0c40002d810160005606c440311500080c0d12014082d00044c058414003a07101034560564003d4400c80e03008175006c000940007281484540b9000c00c0f0001c00080c1c2039240f2200e03460255002d4501d950014140c41a440c1e600004076240000544040c0c0140e4481c214000381981e0500600302c00510030b200900c0701e10f00703030341c8041e581c5d414024004045404010b900075009000406205c1d50903004411031011a999041c80e100300b5001d0003603010012421f96000c6035480182c0202910f484400c20341918031355404000329401c2c00e01010500150040d81c2543c244401c2c01d000d000c2c0c400185250000b11420403208100445841e58003075418180184414141d1000a2041c041c0c11003920129941d01c2d005444128024444c00241c0e951003100c00c1600d0700260a035005141e9554826021035044a003140b051641e5a54003400c0726034000c68050a00c0c001841080081d03421500c66807120b15044a0f41c0c0c0c5405d4260800d07000600010030325030070040501410001 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 958422131 1250 958420881 958420891
    0x1062102092409041401020307110d02061014041d0c01031d0607050a1e0f2010020d02130e041b03030806041a03070803040617011d18070b040509 64
    0xa00e03840718101000c800b24400b0070030b50303052081c0c1c0f00030b000030700f44200c4e007030655614460f82e00219070341e00c1c1a034000790800c0d0b0040d8060107140706d6081c24419a13400041d07100d000d500340b01c3c6034a02561400c03100c010821503a04503650800d44480e281c0d40c0d088107181e42c0800c0c007416100500a4200410b000504440582640030490700328207900071401d603c041b03052608181107280c4a030b07803010000d03070030341d841d0030742d61401c61800203940c0f07200344584c0e404800003400c12031944e04c0c3c0c1c4101c0d02c22010f80034165030b901c4240c40690042d1041c4c0340501d0311a0300802421144510150070210500c0b60b0403216004c59202c5880b4260701020070042005e0103241030b00410001e05078800c040d003103480042010100401c014003490782c5450034641541c5000120605500003000c03a80036035110b00b5415201e410500c0741e040070640309600b200c6102811a840c078103a650380882401c0000c1506c048030001c82c4060400c01c0e071121002e400c08a95401403080c400540814030095586134600801d010b8a003500070a = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 958423381 1250 958422131 958422151
    0x4051005030c18120604050109140303151003090803010308190234031b0e0907080a0206090f0d05030a1e0219080f04121101030c0c03030e0106210209 66
    0x100880090b210040d07507405020100e002c5140c03040c1a0208984a644461001640c800d02c0200002c00505402c1101c16600c140025200d02c0740b400480c583d2070000b075502071884e210990440c80581030030b04409044240511300420b02c021280c940004941c400e03041031700d4090700020180d425071540382410030040041c3c4000d1002e0f00c00b42144501d150101103071405005c88107440c4400e1410100c5c60500555013000342c01480e21080200c5086130000c80c8119114030107600001801c2c00c42c081401e1080713a8444019050742201a0b08000880d4031081c10940e02c0004101d901c0d01d13540300c5084224015200700011550703082c200001500e0044a200451211040700c54005651503010440329403034160300d44500f064400a14084505000700d00c420500440e020400061103441140c0c031030310180c09640782d5994464000011020750f100711807400e010a6a054003000028482d5008220488000e4000a030f4a52a5007403c50000c00740d80866120080d0008000309518008415542100b40c2e49 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 958424631 1250 958423381 958423387
    0x1f0f14060105040b0c2404020102070501050a020709152103080a11070609152313030f08071704030e011701060905060c0f07030821010503030d0f1404030504051005 72
    0x240008141d8840c90040041e82c85005c12540c070050020041b5007090191b0821602e1107030600103040c00805001c480c00c3c0d0040c0f1407040000740a50169049070340c10009540a02a12424800507a015100e20a2281101d4900210002e080c1140e501c13031391607010030075003160021600d44c1001004440082e10340703a02e040c40c117201c4107201c4040e607003250341890344000086004d0001e400c00075200311507569485000340c280200300c20b02c649400045000c0d40f6412600d0300707103911100c0307080000103140140100410700113819400d403180070b501040d50004442c540845400046803080c02c1000058a084002c115442001c0d03503a0b40e00110001d03071a03101d001c150681585400c50050060700380703226003401014001180c1c620407074180200982ca800e00e40846003415070300d142c05105603020410030410b180651902d81c50b50800100c1d03680c1200c070003c0045040c004611403071002058440000500d0a036a10700c9200105101449a40f140340661104d540f55450720b01407102181d0750340d040400304a410 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 958425881 1250 958424631 958424641
    0xb0903100b01020a15050910020c0a020108060a03080a0e0a05061c0507030905030301030506070201050702030a08150a03060c03050a0b04060503070b090f0d0b040210092103021f0f14 80
    0xd10300151411a51010410110140050342441c0800704007038403003018840b1320400e0154980105e4000d54010049800f90814600740304224000e884240100c1c1d0000c03403d005c0135600c11304005810031402400e80d40e84a50321754401410350300000344003000c654100e001050920380011f008000345400e0380c5a51410046003c1080001c4d44c050035008040d5496000c035143c03e10940c4041d000a80c44003c60740c3e256140d050079955840100c49110041d802c0400088510f4808000e03101d658146172079280e0951108000d04900c443d00a50307864216011400000200e401070060011707600441e2000150f5007000c5800c00e0a494002e100c82d80102c0c1864010000c94600244550465058041464803080000b00041c584205071070b034280d02034014010078007801442c40460b0701962007101c00300c007042e520794402ea40594103489055510701d032700d1003180311540b51107409480492003841030380d00300360003020070203c0900c11a154682456403491012101ca1503403050110080881400c00c210b8940 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 958427131 1250 958425881 958425883
    0x7121e02011401050a2411150f1317160b07030507120509030d0f0f0c02061008010c0f0f0210230a05010b09010f0302040801140604051302030606041a0303160b010b0903 74
    0x80d2404200041184800c0358002da40714000d441d03c010074181c148e5245800d0102d01800650007036908041106007000803458038200581001c400c07562002c054102500a4a410003503604202a818501902c1d140ba407000559051170b29071180a458900140c1401e01c542d00518103070881802405003454441030140440f400001d540008401080200d05070344a0003089002d00340c00580003146a08140c03142c0003040e000305046108840040b80c034001c0e15503415000e4265502c101c942c101040d40781c22900c020903c0340c00e102114030414011500c1c081d00b801504412907800240224040316181c0900c2c0c08101403484080d000f410140c4180855414400720f84110310488140e41c1c18410f0703400c0404081400ba805890041504c0c20017080f00040e006588900e10204841d10303881781e803078000001c0d00300801d502c518440301c3d0082c2c020003080c2d072800280b000078600a480f56080303940140900d400c0d5030307081008010031025041c22041c0c201891800258410041e04803001240003404101d4803a20 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 958428381 1250 958427131 958427159
    0xf2122021f11010e01290901030f02061b03041a04030c05010807021006090504170a0c060f0f1a030f0a08030718120f0308061507121e02011401050a 65
    0x80c82140320755000401c07681500c000d00da000540c64654200b04640c0c140000651207400c1001c901148100764400d200c0ca0602c00448007100c2d654003030000e07401417010480300c81034a94014030280410386080c40c1242a2421920b580074401c03842d600000d82841180800d562300c1c080c3c42554107016061a0440e0344541102009020341d50400c51400e00240c1d43c1842000b0700750107485c981c00104800e580f01d06801014010854040d80c40d40e2005078540c43c1c0342c82040440301d84841303594441c28800015541d0f0005041001e04607003107a5183e000c2034a4040d0a4894400100608250b401ea01c04802c81814102487e107010703104c15420500b01d0401080784801280d41c8a651858030040c64981c2c4803c000c0060b40c9504126100d9550640c0340c0100102c1113071998003503000742c83c0d0f0b0704e00b681e440c410444840c006c0318407254059800e0004000041c45207050071003d0159052450508441100c40f9030803070038140750480184e440e4505c50038904141c0300d84034050704042c1d510320341203800d16a010744840d0f = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 958429631 1250 958428381 958428409
    0xc090f11030a0f110307020d0f050a12050a0f0213090f090c090b04020d0c05120c090d03030b03070503031216030c171005130609060e040f080f212202 66
    0x2e40c5a03c902c07402c0e207286070710001c180c0200c04507180d202d0400c510020b540b00300c034028030b2004c1882c1c0010f442ca1980242c5c00d4a0040e241592503c0703c0540502070900900400743c51081059215241c0d44000140c90000e040711240003401030480f0307490200a4025a03210030442c048440c5800310031000b0989902c08401560a0000b010461039541e502290081c4140e229540ac00ca180c400440401030740580240318001003007981039655103900c4c940001e14451034010b40d62101e6010710190000e4000d8029648096000b01034802096486002c00d0841c2d00421144180740c191000300006112420b408102c102840d241c20080340655032409481c050348204c034855034484200000c0c41d1594500b82c0703407005d48070260800740c051156a90440141c6400e0064059440c14654003152042c520809540724030b4200110401380350080d01c902d03056502c0003c008130000002c01010f03560750010400f2200b2050b030b000000c0514070301042040c2091061040306d07a0810405030606026a0f02c408035a0b041d0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 958430881 1250 958429631 958429651
    0x6050d0f030908070e01033c02151207021912050c0a020a06031505040e030708130f03050c01110c090c030a0204080a0803010f0e090a03080a0e0a0c090f1103 69
    0x104281c00e00341c0b042101039000000904c544440030841110507946641224400d4840541044443c00d00d0103020300000d610f08415005e500182c6103204160f0030312a0308a002800f06445030070840201103160344100a0000394080880c1402112903040001801c0680e514001000d00c1441d95185003038419507406010802c40041a00b00c0036240a2056140c4070b6402084039680325643c0c07001801411100d80c0718840e0340c0d2440d600180c40c0c1424020542002d007180082e5244c03c1503031391490b8a903082400020485a210540400c420305c0e80c0a9200103180154000d00e08544030000040040003a0105501c1c030740c1110380d10301240d440b00c41c2d03060340100300004565200d82e210341864000703010781d0380a0500c40c030a0300c40c0d00c07003403100c1140110b058462031492480e000c0c0e242d1010045c0c454080e1003100c03a0750f00c002500000300348181314040d080001d0140201e524000343e400c9a2130104040750039207003c0040501041200e0322803050004c1ea243c100014891034200c21242b40460000034112091 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 958432131 1250 958430881 958430903
    0x70c0504020310080a230a03021011070c06020f01050a02040e0601210f02040f09060b030c13121235090a0609080406230405100c0c0803090a0906050d 66
    0xc21a0f4402108000d04654000c0b10f4560b4050308060380800ca01d0f00c28207006010001c645490b048010030908901901500148041095449014014a04121800c20508040c080c440001d68a94030030001411298020300444055150b07450031554040d00301180720344104010040f2024503110315900a009003885120849411082d40000181c0482c0b05d10f55454412565642c2c01c40c3d5002d0400d0303684c00c90220f50880e864018040840f0641d00070044401414000030324481556001022040480c0c0d0038040031170b51b501203807131030076890fa0011151880c104c2400c000c800c1e4840704404907010070020480c40c3c080c42200c1c5800030000f8201842d80da1400a000440d03000040003007040b455403056007040704c08498240546150000c0c01184d0015103440c0a801b010300c0340c0c14543c1120b03030010030780f1441c203890f000801c1120100111040d040c02008120f04d000714415494200040c03140d500a180e540c81d5400030049043c0b656044140302c5894403805100d40d803a20941c40c00301e02c7d07010307649801c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 958433381 1250 958432131 958432141
    0xd0303090b090a140a0b011205030c15070210060609180612080915271c0303060602070b040b0406050c1609061409060310050a0209280605070c05040203 67
    0x340010040141004146a003404820700000503000c0c5071500404882812035103602050391250500e04000d4940260700c8014845440d407642442c0c8998424001c03640b40c9291360407141e0500311000c865008a07034520040204031501440300702150f500041c410400c07a0f05107030000c0c111500c6400303119010150b1a070b20410500040d8801d8014210740d005c1c0081c00c0c0142d1901c0c518945c00302c2502400340c0040503030b603c20000d0341c009540c4440e1425201030804840a462001c2a10040c40b41c0c5034000030295000078045c1c40d40c804000f60314002d03500492075504001c80a841e083d1103900840d0900420001000744054100c180d801f0f844603454855510120130140d43d203018401110a0404280140c00144107404d5500c4031040700d280e034910032441101e10f001c01041030400c444c06034064012100c4c4d00041d440c0c0303501070340d881010600014203241e14040810701044600740c44101d0b444070341c200d09180ca0011401d010052419241c8186071665030341d2810603841710f620a8a005a4020000c62 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 958434631 1250 958433381 958433387
    0x17280201110a2402390d0915090914090c0618040c1103120a0c0306080c0d2306100b0306010c1e0b1f0501020304060f200a08030109050f060d020d03 65
    0x1c403600480d00c44448408441600b54211603507440c1c40403d64480c0040717004090744046207031046000140c030b8001d007480c030b040205a048000c0c0340c0b5030410801c44100c04500301459102d104410360081c0c208504614041d0308242c605070043c2202845204244030340404015000c0b2602424442550081a500e40c3e4110941d12003004415440e024000401d051a8130302040306424483c150854052000680d07011094041b83d0080c06040007a401c070710721176200c1d800d09640350b070380c0c05100304d840403d809510000900500800c101c09845a0050014045181130212601c0003404000c00300038a913040880c00600000c03c010070041c512188104c80c04816480c3c00d2a03440f01681081e55107680f460b0a41162580200481c08201700b00d020303003004980da51000007170306c1c01d44110341c1700c1420722200c80d001542c08040800c1e03c01d40c07219010781215600042800303c0c08413944a440e0b21500d9504013541c500c02c0d52801004c0450403101c18040200583d0381c0124411001d0301079030200340032102800d0031 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 958435881 1250 958434631 958434637
    0x33140a1707080d05030a14010506040b1c05090a03080606041d04051c09050913030f030f0b04020708071e0f030c080c1b031005040c17280201110a2402 66
    0x11198010100c83c6101507801400441c4184d2041030200202244004030310241c03a001c0c001c9d960400c0c0140018000302003c0002411304c00e142d03082160000580d00c02c003005807107040341c1daaa455008810b0740e800f09034005810f0381d0840b00c02ca43c0107042608040c840342c030301c0200b5201218130003501804074041c880140003400c1c081510070380c19030150344844e03000303481c49500c0c2c881c3e00d009440c9240090128441e22081c0042130380c0c55a10303d0240c40001c072080b0003620f803170584080302c01d0340c5010001d0309039291310041c41c5051061521310386465141c01c1c00488100705083c5102c00814042600700002d51031007020420790760606003902c4001c2c140c1820f400900541c14264070500c1500c1000320500c1d101a0202004a000c404898141003030b04e5841c0240d95080e50000c0c0700c04c1c4994020300c04c4107400c18408100c2d42c150002c03a40c0c03640307691560b007260b2409103503064040020207858400f9564841030b0300d189800e0440081903506801c0e42d41191202c02035016441c0e40b051040d00622442c41a012 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 958437131 1250 958435881 958435889
    0xf300a050d060f0f0801051b0c15011206050106080c0a1805181506070203030d09260a0815090402010309020118090b12010501060816020133140a1707 66
    0x1000a0740e26040c80002c3c05a15006410050010001c0058110014010309200c1c69810407074100400030401801d0054014164685c81030140d544481481260468003a000703000340403120f090050542001c0e42240c2040e009513003000054020040000000c00488104403802d02d481102c1c80c200124804100a26801c11503001400c1c800c0714000340c2c05000700d28000c0408901954a40310710004000091040541c0290150424440101c400c246a40301c103001501400f0640c815810040d610242d03e8400c1400a85561003c50384040706588811115400a81200d4503c1003018500001d000e1340c100400007810182c40740000d1046910174010f41c001002d00c3c0c00742c40c045035100d8480e000540450355415018000500a020303c80304140030b1310341265103a4881c6005030301c40c440d80307030000214106031009540d00c0c1c50b4901c4107400003210281c201d80003850b03d421803034401d08000000b400300e58000c0000a152111001039030380c407140c9900441c0e01c1030b01c600c1d0403801c03130060fa40c2c00c107446644 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 958438381 1250 958437131 958437157
    0x50f060d0c03140c1201021e0414090604110a0206042a0b0901020703060c03020706140c0412083f0709140d08030c090108180705300f300a05 62
    0x2c4111421801500a4101480202c82c01c8444000323954504600780180e12600031107411228800311542407281c0d01541214028202241524040b080301c8240e500110131000141d10400401050020001c85020407000c005844200b01c00d501d01c8aa00c050040c0c01004203c082c000340703084440c0c4c0200800401180d016405001545d18808003074003c0d00306144c2900e4032400c01c2000181d2000581c05140710790702d9009001d0a01c0d0400305100d0308259801c42c2142c0e552802c01ca48074480c501910320307400034484005802803480e50a13500440ca0f0343c86200c02ca000c0c1c1c0c2c400040c0801d4a81010b8084103131102103291205601220b8002404c0d00d10745500600003003000030078020503a50b40c0008251044e42a20b85081646a80c0c0075045e582c0da0011109a03190044a424862464040c034400803180540e07201c10b83c1040c0212000410b11003440c40507081c0d0303100c02841c40d5141400d1109101a02c4ca1340d2450f0000e08444c6035149810300c2c1c0b50f0071424400c0f80051320b400900c0c000e005072060141100 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 958439631 1250 958438381 958438399
    0x60103060e0d030510093611030316110f190501030606020d0e1309021e0f2d010201060f140102010b040603050c090907090f050f060d0c03140c 63
    0x824150010550030780080c106004544032480c07a5402405542e001d45540e07140103145910300390040c0300801c41c07400d004a01c1c4511120540c0d04034400f21a418071058400074000c1c03403140f0380c1741c01e1103c2c0c0c84c00714000c1d01a800501c14403e80e01c3d060301c1140401e6400c50744448805c1c403140c1c0000d0501440880595016030140480c00e40c2da0b40380c0180d04183d84003a201013200603240c0c84143c1c1d4941c0304803683c00004200d25203500c0f041c20700c40010003c400c02c200000c2001c105943c005102a20740c208051240d03032056101018510b803c2d130f45204044d8081e1055201e100620b400c3c4841d070340c10b8100b01034004079500d450500c964401d40c0540001e0401e4042c8400c15030711215416420312107240010300560a1245152051505110350b03411294084020540303503004800340181440005c01481d13242c080c0c110006007051107801014880c10308000006141d00d048885040040005040c450044103c0035000b400110b0000d038034401d0700d801c00a04041c4034018007000785040e501e101000e410036100 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 958440881 1250 958439631 958439633
    0x201090810090c0f0b0a031a060720151602030f03030405070608070810120204110f13120b040311070911030403020105071107170a06050c07021002150a0b03010b03060103 75
    0x990042d400c142c415100c14405a0759010b191015030142c2c0600c2c071203111300304075110013540241d1240ea06040c0c0c0406000111044c100050a03a4003c030b401a20712500000c0702c0981c800c2411300c00152802c1c12680c0403130818010100707042c180034050a155a00615089800a6660400c01040780c0c0d017041040b0381c0d807490249066074651707100c0e116410110703148c3d102007901540604980e522400d030b045404061035143c07042c08110040006010390300950342d020340400070a4102e00500c1040354480010344d03900d0400702c0c254503030b0002e9400120341542c000d1901c40050f80b4a00308a400a80514100700d0350000407074681c0c20240d041d03102c0050340745400d0702d01c1078010300000998031503800707600204081c0d03981c03072000d9618007007078609001250401031040c481c16007a201c80c80c0c0000740e202c04035619640346a44402c112403080c2c0d910a4021804941e03201140340c00307985210360200600c042e2004158418400010030000f52603640b0303c98445000b50b000381c809500180d54114018216005540c4d2 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 958442131 1250 958440881 958440913
    0xc0c14070e0a050c07020409081207270b0405062107020a030e0f012001111204060b0a030803010504111207182c070908070306020a02072102040902010908 68
    0x3107100e140d4800c0090700015501c0380321031056600c0b456808090354905000d075400c0000800b4107802c100c0b450941070002440080d40440c0451269080c2e40758880401100c40009202444400c6408040c00a001d014821810008192070449000f40d48090300d03503100d625216803080e8071400845948501d001003124003035001031801c2c016400323500c440d00814210343c10301c0400d680d582c020070301049040721072001340c610541c10103070200c0742c003070000400c005a458140004e6105441e03600842d07114506110902806200380c000e0018116001041c0e10722b1940d0720b80650005104e20340c462540c0c0e48030414130000702404c44030700011100301d001c0c00b4504000041d1402d41a0010b40b0041c41030700c1000726000e25113405042c10018103c0810940d50f2441c0c2980c111500014001d004018002c6400984c01c030040003040040d43c41010301684aa0340c0c403030000e02d00f5005900107007940c1d01c010612000402d50b0304048146640507540070a100e420ba00042e02c60300c0c50355010580e01c0c4107001c11050f0701c0d44 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 958443381 1250 958442131 958442143
    0xc0a080f0d0b0927011107030206060f0103050f0c0f21040309050303030105240c15090609060105010f0e15041d01080307110d0606050a0611100608070501030c0c14 72
    0x280720310401c1041200c1d014410800740880d80302c0350104024900741c884110021884a07210b224800108601001c40900328a542210900b2000350307001000b8880d60786801208024800c400317190810503072409151308190582d02400c0300d01c1c10840098072103010040941240e0f01100d00d00a524540070090100228500d0210303410790019481d0240402c0a290202c1181c0c12070700c4c010485100100702000028400c43c0418206958810810003c00a060180040b0443d40301c03141d0120b925182c003e40c03090803c40003e0131300c03402c2d4218034014000d5a803c0070704400c00c0340c124a081c01d80042502c001c00c51890f000744224000d541c011500041c07501d02401400e0403015621140002a6a20550143d483c00703a1f1030014103140c5502c294407031030705202104100c0540601c01c0400d10030b0b80c400c046100c664040d00f09000103020b10004680e10345081004c180101203040040081901e009280b13621003940380907050426441d040d05801e014854085442203d411500d45202c000f031100c030507a528a = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 958444631 1250 958443381 958443397
    0x40b0d0b03120f0a120606030506100c03090b0d09060614040c02030405030607050f0d0f0504060501080a0c170c040f020a09050102240c0f03040b070e22020c0a080f 72
    0x681040d0148403181004200c10181c418080d40c0035040c622111100707411500000300310410003140b40900a03d103480c43c0038240040005490005030b50520343d041c01b503c000c411180d00144550384803180002584144050301710350f01c4044007603c13070b00c038681d014002c1d00306040058115810100003003400e8114400300d0801c040120307010030600303080d00c4042c2e80f613000320f100f45a41a040080007606560148000f0500040c000f00c1c3c007442c00d103911010604440c91110700b002140d42e510204070811410b4441c484c0540390481c0113114a250740d0340c400ca50091240501a0509441d0340e81c40030b01c4c0410012a000e1103001072062181221504000c3e0094000748046000240604000201d6500116500400150102c500715808070f501c0204103148002510f2034002120803c2603000d505c8500c4041c5000c2c81c81020485114148100010302c0c1a1500400038851050b0310301d4140c644542100300c400300210450007584035009440194100002c1090251a00070300140101e050818440185401 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 958445881 1250 958444631 958444657
    0x10e0f06060109030506061c0b0907090b060301080c191205032701021e03040b220e09190c0314061618060315030204060f0603050c0c0303071b08040b 66
    0x781e0703444004480c41c41c050b1102904507007001c8041039190400d545403420342034154255582c0c0307040300e60f00d07109081d100f1200c059851304950303406e020190301401030110301c04040f60010309550403c410507807549001106503105103440f401c81e0140304e04e00f100c0d1351300803c0020b0a0350002c101a042c040d880b68007450b000c20b40c000c0b5101d01100c2541010b03148902c0c11006900074228076120130b10000850304200f039410518070091000094940b071081c014041d040309012003000d00341c1e00e0050318480e04495080380340c600d40381604014040e02c000031040300100300303900c1c450308200c00303818142010703010b0380c0000e0300c1070844800071045424000340c40b42c000c4900020901e03400e0030440302155840011000005280940135040003079505c2a000805800d59102400d581030b6079a9001238112140e80c0d20541c10101244010402540c040c8509548a0310131103803140303040d80321406c5035201d100042400302070150a00c0c02c040a1240300316180a0141d104803034540d280d481e5240c60a140c0c005424030364070 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 958447131 1250 958445881 958445893
    0x30313090e0a05070302090a1526121e07080a080610021203040210020c040f0b010f1b0b09030c030a0201021e0721030f02040906080c1504060503060f03010e0f 70
    0x880c0000801142043c0c00401900906046a003005021780000d800d19015030b48845040140c1c0102000650061011099040304401841100c00200a0000d80e070006600508000740c07081c140c0e10200c9001030b00749070200c150040340d582c4004240c0a5441d000d49074030030107d102e81c8419040003050b401034800311500c1e00f0250480304101c0c1d651a44d40c210000850b01800480c0050901104060b0045507500640b407200c02e43d00042801c42c1c843e400181031058507400030203c5940c0060888150700c0d070074500815940e00c1d1a600c84032001041030024200c00c1c07982c0010350b407007d0a0095070100901d000580e0b99542d00450028041d401603051080500003a8202c0355031130001c601101c19056025481c1c00507203a4081081c00a41c003140840300a16466198540984055100900141c440180d000601d90b082c100d103545010304822009001d20425169044844924000e440c00c4428524000f0340c1c03070f6104408a101b04441d1703413609402d036003052103040c0840d40204205411f1100a800c41d25 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 958448381 1250 958447131 958447151
    0x1021201120c1809060905060406051501050f0702190e0405010b010306060e01030f06151106060132040302040204080a0b06031b010e0a0f0b120a0207031d0f03031309 73
    0x202401c500a009120742c2d2004030401207103000001402005910100000e000c1c409a00c441d010744240c024100c0c1c86800050420080064a100e03680e08407200c2030410b0b156140c4c0500290052103450a0901c111801250b08000c5580b441c8803202454004c070142100c09665a80306a18082d0a4404440650804001001d6948039101341400c40d00c040d07590314418600b16006500038030924003110300c0aa1203803030104002d100e401c6d0b280300b0180e40c1e0b83c6035510500401c2d0b0b418240403010744814100880001c15020b60070a002c00c08140598456034020b10800703203849514644107943c80250080d002080000c0c000d000801d41d100070601541d55201d20303039107940c01c06840d00b144209055407803c51503140c25140d44245c140d11001f17000940f420300c0e0b036525a40030001c1c0000552140c03240007400222549050351710364149401c20840c020660500340307030742c0d00a403144a400c00b005501042c08244040181c0d607130700004d103001d0800303019241e80c0c102584da4140d4004441c0581c030152801d0480c414 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 958449631 1250 958448381 958448399
    0x60c01020c160b0f0906070f17070203060a0612080c07080109030e03060f040206031503030915090a060e031b0d0c140102150105030d0309030c0b07081504020c06150402130801021201 80
    0x18104e040168900340f420301c10008214154004041c161754012022581000041c054550b2a401e19114220181c1301e200700d20426261400c010400301d030309820300c5c034200101402c03040d0006106078081078090315651304007202131030301c030603640b0040c425800d081c009002d0680020307050710003038002d03420340e8030369501e4a60b54100d0354410f0f03030001e4111a0810000b501800320740d80c4009640402800d9918044c2c900c0001a80003640c210504042c4030b0004000440703280401d0400300030000742c1007581803101ca090000703482e50000400e0100d44044070701e540340d072907840c41a07419000c0e62110040300d4864492100c0c0801c0c3c011055243d0262040c1d0405200402e00341c00c80c2070403100e0080003001d0003102d100045000d0503d03414102c0a005855005a001907400c5040f40c2c481c492650b1100300324174150302a9000e07881c9142c00c440c010fa204005540b2205400305100b980048900704203c030081000e40030800030320900c103003031041880c081c01c0440c1c602019002000d0f07444c1c5d40312152015907216000e007 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 958450881 1250 958449631 958449637
    0x130f0314150411030a0221070f080a02041517010c0e191a040302120a0c05040b061210090617060a020406050a0e010e06030a09060e07050f0f060c01020c160b 69
    0xc0d50702004100008000600742c5a0000c03c2d0a805425502c20104640c040345802090044581549000303003144401c403c000c0001000030040a4408003086242c0240103844007220038000c3d0041d602d0719170b0080aa05041b940354024200b03140f11204003201d00c0c48030340c000c0010120707000c00a00b4a208441e058948a803040e255411081080e1a5031858810000b030080400c40b0150074844040c0300003c0507a94440300030629407042e0340500551380c480d00d049251000c0c40d4220911851030022004510b40f42c0005075001001c1024000c1955101c82141c4680d008050340213007043d905101d404a04554080d48810600d6100021540b030b42d01c40c000c441080e40140e008010004000f4003a14030200c1c400c8040c101d15000c1030503c400442c5010000c104254001c440740c601058840e00010300b001b03458031030b18100b603c17014040d140850501c00040c1880c00200607191284154843c0a9000e0340e8100403100f50801c40d030000c45d07840040e030394455100e203050340f00d92864030b48000f00002d20810410031 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 958452131 1250 958450881 958450903
    0x603140f0d0e18090c0604180e16150917010218030706080412031107030509011b0209070c05030906040303180f060f03050a020d050405010501090e010b0609040c0203130f0314 77
    0x24481c0100d50f40000054103060052585a02c3d10480001103a10b44500b801880a42054103030003d680810702c1c003000a540415107604041c4c1e0001410f0308034403060105060035101c04507034401001c00100c0342101d80c42829080080310b44102d56810500c000154000c120381300417584807500980385a0101030703c62483d03110b050049501038000400141c011a00840098043d04002403a94072404c1c244c4615040300d50704402003040000c0c55a410360300b002001000d41705005006442042643c00329041002c0501a0818004046108400c0000c1401960440f1001a1119403119500d0800400d003449a81c074115845102d8240480e0303590b404c020000546465856400c1c2084010310128001c06000340382c5030306203909118080354001140144d030b00071401600003052070350420074014200c5580b4411140540c1c90200d0103042c4e604ea00054480e4954100c4000804c0f5041d008143e0541c0b0841841d10341e100c51901f0042400c2c104410307020143e1340a24981100082c0c0d5001a0341c0cbc860000079 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 958453237 1106 958452131 958452139
    0x100302090d050a0c0f2304050702030409020c01020301050103060e070e1009031505011412190f1b1418041202011b091706070807030207060603140f0d0e 67
    0x404400901190403800184111502c040486e0603444842c00740502e4a0328005803925000f03000b1303a002412041c5c019903a43d08880d10b114003e610034011f0501113803410001041701e106c0d5145180c0305840d070fa01c8030b801d4035240d94100300d42000691040300401c80411004000114038044d41c11603000d1100c00800c0d55418000305922070850160806d0080e43e2420394030030001c00004840d00610200140d8500001c81c0d4104030405a0b0070680143c9000c1c26109c0d41001c0004000012003181d040620480c40300b5803620401024984860307946005085c144003007030118002850b801d01805490000044040c600c1602164001e807800e1504086461404108200c00e80c804c205200200001c002e0400b6142c8808003a044400c00f4021340105a408101101000059072111000c2d40c0c1208084d0109e205810003240c0da41250171480400303004508404640a024125056040764014 = true := by decide +kernel

theorem cover : BRFrame.Cov 958273381 958453237 := by
  have h0 := BRFrame.cov_init 958273381
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958273381 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 958273381 ≤ n) (h2 : n < 958453237) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
