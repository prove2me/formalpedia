-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4218
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:54:35.90857+00:00
-- url     : https://prove2.me/submissions/f7eccc13-b0ae-4767-8d27-85b456ae5102

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 758453237 ≤ n < 758633093 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 758454487 1250 758453237 758453257
    0x41e170a12231c060f05130203070206220f060f0516050d0b03100c08040b0f070219020103150308090310050606190903050f1f0b010903031107030807050102 69
    0x8031440807103082d80c11000903035882c4848200b401e05011810896401805500681a40480110740310340000040d110300d40c2081d6189008103008201c5070030101d05030b00d1401d080d80c40643c00d500e4104402952a08018000c000d400c215400d074500c491541a10401100e8020740401c241c900f50f400d010014012005c050303021a850440040d45061039150310300c400540c0d0365900c0e4648006101d00d500035104441e400d640c94061031440b0703129500340c0d204c1d00c00075610035118824240703001c1c01c0a041c1d024006060390103a00d43c0d03008010026a01149002c42004c40d1204204000f005000480c020b15200065001005280f540402809280d801901728010210300f00c07685081314000010540d4001d484440d000742e0203000c0c80e0240303010a40c170f5000300051894894280c45e03983d2501403030300388a06c070b4482c819084110011011041d0000d042010b0380d241005001502030040004c0000105100c090100a02c40c141851813800a0085400841c1c01000440e01c07001c40d07041090007907009003112 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 758455737 1250 758454487 758454503
    0x8070305031801230a022b0b06030727153908030405010b09130b07140702010f03060803180a060813060905210304060506060f041e170a 60
    0xc52030030a8140622031584413207050b880249400b0458240307002c20302400e01004550217005d808070324400c14100400c11040b0300005404100b0004d00c0d2000c80d0b11555440c0c1c00384408204001c08541c105041d8495030900d180d540c142c40c4280c01084031441c0658000001041048440341d400c29807080d002c41211078010314440840302500003a6801c0c40d8488043d40d001e01c2c082d00c9480200300300001441d84075000c2e20000c60350941000c0041c4142c041290f40070060464801c0c864240030030019095031020860500382c0400d0000c00220b030150003020002810008070500952200e80b0a4024000604400341101c1e1500744028841c07036040705070506c07180902c403184d100203200c83c803842c102c0303000b15140400303e103006000343c460401a103a8401c0c16035076031240ba40d50b450307810401d5072030300008000d00c1c0c540f0382c0303a0070b19103804030590b103016054910400080c4a681c041c18125000c54044414908001d8000116480e0310400d0740c816034441c800200d070320074194580c2c00300490402d034054828000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 758456987 1250 758455737 758455771
    0x317010618080615060d060302030d3501030f0c08120406021b06030714070c0311040e0c09060607050f060a05040c08160308181909060504050405030a080606070807030503 75
    0x2c081c0d540c001140e1001801d82c82c04c50000090521600030584507105c0440441c8080d184c0d00400d01c3c0c010320118440c0010180718517184410b0300003c0706804080a5412910b1041d9800a031900004043c04007a210700d00810002003001781c0c0c10140ba0003002c1940940b2040c034a00b08031880c02da0001c1c403c030710140c0120100744031903030440c6d4a421682a80107040c5411500c8040003214500d03c2c000c4503440e004810000078020400211041c4015407023080c039520842c0b2403c040c042511105483c0400c544d02c03803020f5a05070380d1240d0b06103500c09030036110140c540c241c5041c124074007450409814003a0043c0001e00c03039034100a8000c20b200e1805040d1280b10b484d81c90401981d20314550607100c0c000c4403010f4081c8002191740b40181030541d80c0c800c844220b64038003000074005c0752101d802c1400f0642c1c41c07182001303c54464041c4100601046800b00460728007900d500c0d1302d0b071240300a000101320034000000c030306582c4c141c195100240c002a00a4032031055140192a550041d1054102a121002 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 758458237 1250 758456987 758456999
    0x90c081005130b130c090b040f0e0706030506030a0c080109021f140d14090a02090703091110091a030423030d0e10020d050604050c091005070317010618 67
    0x1910303025808420702d6000c042141c0d110410540400303840c1d0005104400240008620301800100282c030803000d00090b1a003401701000100d0f10318494842c035030790400b10380400488000c0350b40c00403205507050100d050b40d00c0100081c1052400c17000200a003581c03100c0030401100550120a00c3c07803080c0c50110102081001044030035a401401e0400103c1c81404a00c06001c400e01511401240c2103021840c0d18040c1e0801c00b400c14116501601c59001c480741200390b10b4000300d0503810181d50f043c20404208183c4600300e42103032120340b080c0110720240301e148895114518401c014617000319440c00d10074102d50242c2240d4015103098590b0340d020b480364034002075003a016042d40008103000314601b085441c5500098005802c5141d541d00849004440304072090005103111046070500164620b401410030081b1103014209407150700e800c0c40030749080e0321403008102c8407100f10b09006440f00740030710303084903481c1c3d04452142000b02184000108036400c440051120091012a100f0301600c0d09 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 758459487 1250 758458237 758458241
    0x3110a110c0a06080a1401080d140910120c1d0f0f06070305040906050102060c162a09060801051308180411030118050907060309170c0304080f030a12020a0309020301090c0810 77
    0x8081d59819421805207a000035000e13034414ad01c0103c8204c026030802a01400041c00640c86400c080081048619601c82a00c0c081c0f04007145070141d8202880d5960840102100d40c01004100070f014114425001c0d40a0755945000551004020311003996110f2a02d001411a0818420000c8407030410b08081a603600102d0580d2050799445009130809084d0041c4075440390061906560281120201403c01c220100d040c61040d0158047e01140b2454400024200d4003035610101040c1d01d080280841041041340d1401102c0e049443d864030354a4482c00c0c548a2031032801150307030203032800003030000d1501043e010794101e4003003003001c558203072072264407809440080324240d1841d0411034045c04018001c1e4400c0d290540203030b1403031003585a0b003180006d941c2c0c40203003101071a50021a0801034220108100305981c2e42001c0a1400c219410704081c005184081d140c1100d6500400e680e02c1e46840381d4494141160020000d100c920024104017000c08a140541041805141d0114920101034 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 758460737 1250 758459487 758459489
    0xc0609060e0402030a09170a170907030b190504060f050604020306010c02130204030b04051006081501210602120415090f140a0803090c0108060103110a110c0a06080a1401 75
    0x1a207460840200707034020040203500c024500b20541742c0c0d524a880210f152210b240702e80c041c41c1c0c04c00550b1540d08a1018015000c1840b840c03010104c0303c800c003c840f440109032101182ea01508071411030310341c070401c40d08601007586103a003c1c1d460001040144002c0307400c8a803002c006441c04100742d0301d03040281310680c0710480c0c0060210358070a82d880014100b000c1005251607142d03000500301307600c80e5240c502400381a40c043d03504c0d50180c2600c860000c030341c0c071881c80106010780061101900785902518861414465002c11400f541080140404071203d450001c1e68081c0c3c04664620f05641c0141c0f603600156420313180701c0204916000520081c2c860440c000fa0410b80300440d4a4140e03450300c50891108101100c0341c052199118001400100036501842070807002e009203002c106c1c001028524000d00980c105414081580580b911001c00c81e14548a40e161040d11440c3c8111410314100c10404516005403603224002103d903440140c230703801400c0300d200610046c2800c0524004000c02 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 758461987 1250 758460737 758460749
    0x403090608010f051c21030b130b010f1112070f0c050301050709050d0c051c14061509060307180e010b0307080325051212070f091503090501050703090c0609 69
    0xd0207803240c000d002c00c260320050f078070031b620901680034100c014011440c40408080003098998052000c5407603c01801c0581c14070166081110820b0800000d09101501800c242440f015200e1001d084070140552001010881e103036690340c40c80ca1a25603108801504d0545507100040c4002c6007600e4180540da000d151541d46201f4803900b410108494100070840440d0300f0328403444001003d840b00c5002200380018510441340032802814810a1000b0090b841400c64111320104500b0900e0005138008074501030b55183c1c050742c0d52902103072030080c050700300103a205001c410304542009541c105c10ba040a8500007409a011424103142c0c0d10b615600071780d400364106100d502d440101510181041c00b2450301a000010300d2900c8070360034455085003c00800c80c0004c1c1c00010226004a030715048400c61404c1a0102d04010009003a0300d910b0141c0200500c0240d83c0d24000c07072190300f041010640100c020481410041000307002040c00a00c12250400441070014445015081c500201c0f50 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 758463237 1250 758461987 758461999
    0xe09070806061318020a020d17131401050f100b040e0f060d1502040e2211041118030f0f0c04020706020c1c09090c140a0509090403090608010f05 64
    0x44840400c20740c1e8004080c0b41e403c0001409000031644070842c80d8404144154000680c0da0002010003420001e0710845407080c030180d504015502050200c00540c4901c641c605039034002c0c0329140000c03540c050704003140c00035803d000c28000429070740020b060082c03243c081d01000f600e80e500075183c0140aa807050f45540441c060025440170039a54038158410001000c081c1d60107030680c0c0c4e000f226012400401c41c141d0f4003103028022168015929600f0040f0380d031505010058031249145c003d0a0040010f0505e0009285002030341c84039000036810301249240c154840b10300d246254a0000398403801c13031107885a00e400c00010b2801240c00281c2140700c9011304841148001840007940c0448001c98102d0b44c02c106284d203241c400e00c0300154079050703140703146100241410020400001c942145407003a160600650360303130340c004840c0c050003007190003802c1e00c41d03d20740000d84540c01001d10241c3c10032680803c0001b0540d1066000741039841ea0748403552141d0302c41618000303085150190540200c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 758464487 1250 758463237 758463241
    0x40b21060d020d020f010309240b010c0203030a031a0a0b03060a06030209092406042d05180c0f13150c171b0d02030d0612081e1312030e090708 63
    0x104017410b1001c0e16141c18180840e82458550b5500c00541120750000300603200e1072610000f2201c40d000380306141c03909181c560001c09498000a1b00c9101c0e0281440501d0b9840120740300c11068400701000e950301c010b1a00c80c0d4140d644100700d94540c400c803042e51080b148940d000c500b450180c801d44802c1c64000c0d01d880226a00c2c000c130120407000d100f080010310000d8403013040c85541d840c40104058a80146600c401800182c043c214440b00481c1008105a95010074800394841c00800600700102c204402d100361150250715546205045a504040100042c00701d4040c440c040303140122104a1884004280c0c644011501d444107602c0007040321340c1c40841c0012440c0c022010740300084c40021004000580e080380145401440700d000b401681010400a04000316881a4401018504e03084240c41d80c40c0c0c1d0707440701c0f540b295030030740b0100120700e42e0a131007941510b078251034180d0008900c2d4034041d80c40780742c111040c0340d82c42030841c00111100b284403851308107402c0d1640034994a4549140075 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 758465737 1250 758464487 758464489
    0x9050708070b0412080906070309091803120b060d020a0806011d0f0d050f070807080d03140c0703020f06330108010e0a020904060f06080c0a1211040b21060d020d02 72
    0xd030502c0050b00c0305c010601200c02d05541d8407004182d1075200e0349400d40240d01e05642c0e4000c5c1c414215181d1440811000c01030042500000140030030080c949002402d803003501c1c002070013030140761600d0385140d2000c220080441d41280a03070380210000d80716000f413034004070580300d040b101c0c109800742c0092805e040c0d1144c41c1000c3c245a0700640c480c80079604440f8081030842d103031144a07407110306203600014040142130310512000c280b42005180c03d12047e640e0203000d0000ea48041d0802402480005440c010b01d4401e0050000183c1c06000b83c0307101f0304107102580c0d041440d48154281800c00441c8240004411200004e5400c006848441183e0718085103a440144014550f101054003000102080d954620034100506121081c0c01c41e081d0038000001e103000c4c40186803d070070300030401404810580055101d801c42e031100c2c0000c54041e03040e1040c100a03004039449000141008580c503e00c0b013030f80700d4029207021100c200126140c0e45007800c00131401c001c400d000c4d4100760105091405 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 758466987 1250 758465737 758465759
    0x507021005070f0605100602010b030307141e03282f01110309010c0306050306040b0601030227181006030504050f030703080703050609040822050301060909050708070b04 75
    0x20322540c908003241845140d4841c0c0c0041c64030620b0403602540c0d41c1003000340240540e20030307a015005c5807008011001c040340110350f4a00c07503c03801510020300041c0ca002c09030700801829400800c4101d070411038501040d40340b540e0f50400741c02c0e4149082c20f1040000f65a11400d0fa10b400e0b0b025942d0794000034202180342c07220130501d003c003159a410302c007400c4541104090042c000c8208540041c4c42e581d20300342c04040c6c21220300c0c0c0006420581058020850391303078002600c81d0095003000802e045502e0304030059000b48202d112021501016403898000f01180304044122000d06590b480741c98070316140400b4171008115140c0920030114030007840280d01c641c4c0083c4d4085d20840442e04696800302d0610f1841c0c01400044000034108000c02c0440ca41c075005242d0004000c0e80c817032003242825a1034914902811600d00f03440900d45540012680c50b0089000c01060090003c00610340c9501304400500110f0000740d4903442200300000d00c000c4001145001c8400b481c440e141807a05042c80000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 758468237 1250 758466987 758467009
    0x50d020d03180f15260c0d0e0115080d030e251e17010207030f08090c0915031b06041509030c090603170909060405090703080705030a0201050105030d050702 69
    0x941c4a46082d800f01e00d050201075540041d200841c1810708490600200505000c0540320b20a920515240042450034000c0115074000c0a0780d080715071200990710100d0014440d05070700034410743c202541c140585040c2c00c103c106440004080e1400a01d00e08002e4040e03c01401d840001a40501e000a40038007902006000e6103220f541d8034040541d0310040d106140070b4154843c0074007d0030800030011001800c0d11000d8903091007000703505164040c0c030003414000c6022095010b001c803440018241d18014041e090340c0c010002c0c411183c1d0704103000611400154108814003921801c0c908100e0390100080510303081300c004110034a05810201403004003902e4041200900040b07000100009540c1c124180c00340c40280d82c0010190725500303001506181c6601c85007242401000300600300c2e266501456881031050720040340b15224011074a151180b0380e44080c0009030007152000802401000401078030146900900c00750b602c4004068541088405090220300d040260b00d0050408542d988 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 758469487 1250 758468237 758468267
    0x190e03070c0e180106090204080d0c0c05010503041703040506150d260705070e0919080d0b030f07080606190b27100e04050f0601050702090a020d0c0810050d020d03 72
    0x4003d01d000d041500b561079680003041080c1c1c0204081c04907950800c01240103040c5443e1118a000b51034442c25091003880c081c150400000200140500011001c6c42c9030000490103029642c1c5800d0170403036141c020071b60741c2c00c0164520485c01100b6240010400c10311540100e5040d0030b0760f10b500c1185044041d20280410000c000b48401c0c000320380c0610070710005003107805400300b01c2c3c41c003900580c1c01c125242051144d415000444403010454250aa85030110b103480002400580c1c0302c00685064030255110300d052203404001714455038041841d41c0140001c0e0744000301c400c1c2c101400d082240580c040c0500600007441b103a032140e4280300c085003584a007540b600c45010f0070301c0b001c9400324034040400808992401c1911105081500c2102d5000d05105108075007800d054000070000c0c483d813400a03101b42c0855000c211516401e50480303111086206081200c41c040301800750400b03a080f550000648803403180003130541042d01c103a15035030f07500800d1100c60041654080c2d4040c10449511 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 758470737 1250 758469487 758469511
    0x9010909063206070506070f05072a08060c040e100803071e051608150105010905040b0604050306480a0c0221120418020a0215190e03070c0e 62
    0x1c000c60344403c4003e010160042001d8001c51034003c6e03002d403050b06da01004108010b0104400d00200f20001c0500d500b40d410381c0080c1074181c901c0001c5640410041d04080c205004007410b10410342c0c0c50400404c04c0754a2200e220840365609110301403602034034484c007480c903001040214001a4049604000c02c084480000c120005a0716220301d00400f548840e407503d2210301e814040c4002c01c000c455903140b14148080c88560500000130403800e0b003485418080c5403111800d40342a55041d0540c1c020b807001030308480c0300303191808000e00d01c1603030030600c03060f807881c0c541d0500341880156840000c1a19280540c0749410b00c0081c0d50201a8000d4490100b00801840d15400603941ca625110706170740040691b903450000c5c48105400c03d200800b0104103044100401c008036210600781c10b0760801000e00c0140ca0303040c5410140d042042803822401020b15640c200f084034809609404250b000400302040800340b460401656441143e6015040400b540e008108241311a1007140d4011801a00 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 758471987 1250 758470737 758470829
    0x206040b0a020106090b041a06030901060b0d020702010e0d0305070f02040e0a060f0f0605010e041d161a070f020d140d050712021603060c03020f0c030901090906 71
    0x4030030019002800e4540050f5100c0c0c1c0c2c2004070800d00c0c0581c01c14020100d03420070286101d1380300c82d51000700900b040c2d4001d150100005031003800c2940000000c242074400140d0b03905090400f00001d50140100b20b02141170a5401d100d5400c2c0a202c00d11440c3c2e150720790038500007070742d203903000b022480c1c410403603120f6210304070510311203410f02c0081c0c1460306c500c401054201c4418246410750742005e035034000c540d241c104200b0007a0380c404001c44040d4020b580008121000320404501d84840c5e0007884210301c80c09511f05506d49031501544c04a80c00301c1c0e2040720014110701c5100b928840d640d40944440990161140940f410200300346209214040c5041403100b0802c1940c28001c1c2e00c40e4403408214042082001c0c05051449030410401c035101500c000000203503450700d18000d5000183c000b507600d9000001c0180a54111150740c015506095102c00e50302240e107540390b02039131030640002c4155200182d040a18003804085e03071810b00d0b01d0400c1140542c1c01c0c00c141c0b900415a0700700f400d40d440b0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 758473237 1250 758471987 758471999
    0x8070c09090209091f050a14040b07031a0d020f030114070507020a0e13080c0c0a030609141204051c0f05070e0c120a090f050f031b16050d020604 64
    0x80400101159034010848103a980100402d448000303100c1901c0d608800307500c89041100b05800401480c01100002c1e090f1941c1d000c900c010910120a80c00b40310700701c000c0c031041c0b00340344955500c100c200d550240880000800034404a04080001e990421004002c0b08014070f04400d119521038005070001440094502c0e9256801c1002da81120100340d002031941c065080031011480074110344104c0100d54100005516000b84241c0c2c8003604142020030000d50f01a003c0c020044240c00061050440940342e00b455801400e0610301180c0451050803105c0c150769010800c5d00f0041a10320580d42007614000a00000403140100c01040003204107070400015880003508000d07174040c0c001814403d082120501d4a08405842e18080c4c000a000c0c0b041ea00341c405406607405042c450004c80c1d80c4a203443d084443d82e1003440700a0460086600c1c02c10560381c008046c0c00c0400c4081d900c1e10040d151405880c3e02e416025158014400c02004140000d042400a10000c6840588400c0c03815035681 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 758474487 1250 758473237 758473253
    0xc111011061501110601030c0e100f0303080f0609090a1502090a09150501092108040b0c0a05010b060703091505090d0f02181e060103110a0306030218010e070503040807 74
    0x101d41e8000d20303400740c4410b402568018002d03c403c4988900908055045854a852840721441403d102c002040000781c00d000da604000c03401880d07554001c601e101c1c4c0b6841c02030710035501221000c0c854068440028a24542050b503280110031100241520010580720344483d41d070000240f40e4042c0e000c100300e5005454414a400c01400007081c00100440c1000101d0034482242d070046041001054060101c055142c00c02c081c0d0050303220407544a0401440d219469009a5100f81030200000c514a0420311000c85c030306400c1c511030350081000410400c1000514042c001e8003800190703000c4010b10142c0d9041840c09004881400d0460034480170340002980780121440c100d8544805401000442c02c000d0f00d6070300780c242c80b140c0e400c407945403114a0001c0319002c030076510280001c0c24080380450740242e001116800142d41c0c020303529484042c0240103890300c4d120403400b40e8a903160745005040c0d0010024107a03030b0000d106000d242c0b112841104c668102806c02d5030225420403440b0006080a = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 758475737 1250 758474487 758474491
    0x30c02010219050a1203060b0313020a03060614030706050c0d03021e0a0917060601050f0306150d0e061e040219090203010f1e0b030720010203070e100c11101106 71
    0x30310000c4c42aa04645425000d00740c14181d603d0905061010911030002c80205a80d80000750002030b51105005000141c01c501c0e00303910240449240140210740740c4844205402010416011188000d6488104940c1361080b0031821159030411600000c1491294004002020a000c0781407a0007034030402d000d145a0007000c1e00300100354002c030f0400041c808949030094980c0c0341000341c40d9070300d00280040c10394071031001200322000c000000031300e4541e0307036000c01e4108080080080b900c0b86500c104510041102c511010003500c1520700083d5000c10880141e041131280a800000d43d48460f070a10683e80c10488640c11441203460020070910001d00c0614000c042c90007842e0300d1903203806d220010700e545111100705140c00c9e0304400d004100c15101106d402001c0c41c90b050000c0f410b9207045014841d120482e180013540000b0501c407446078070882901d40343d082126244400060001d080c0c4076049080350041c9040005156030b541490301038001c001042441c24400030030301c2d20a100074100481 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 758476987 1250 758475737 758475743
    0x140a03060c0f080a05060604170f0a060c090b160b09070e0a0b0901061b11150705151021080714150606210c1b06011805040b04030c02010219 62
    0x2400640b400302d5000300001c0c0c002e0b10444080005003880c40210b00d2511942c01075440b00304e5070300420b400d004010030610050715174200035103982d0440b0b490544060081107503090002042094080b83c406504021540d0241c90105100501212981c038410b00b07800040039070400e07014003240022103880c41c80c011845201d81c4a0000f40710f0030004100b16000d06c0680150040041144848007804040044a101c0301c0c0c00a21702c005010003880081d140f600040d01b00c60001c1070124502d0100800001c1d800100041c440c81220140c0c0c400f80e4512140a15104402c2084101000c40000c0080c2918810240f40203400091800d00c0d5034850702c2903500c1071220045c01d40c4c0009101000c400c610f0030610780002e802c50b0541d00d0314500541e1621a00d01001c00300f2480c03980f100202c2c02e1120078908803000044085503e11291480714030994681c0b009200e42d241c400b0f48040040c42d200018840d1500c91980001d078070009071100e40701120184c01c080320881c194455041100045440c9520004a40d44 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 758478237 1250 758476987 758476997
    0x6120a080409050a0c05211b0a0305010914060a150203040b040b0d0501050402090f01031a0306040b0a0f0207030f031e02030109021b1b10120f0c1b02030601140a03060c 74
    0x113100c1010740c2102c0030461040e04000003884900002ca148032440300007900d407080d51003d580c1b06c0400032031020030052640d41030603500144652140381c154201504860041305d042006400080003c0740d00300c01142c8150340300001000c103000c0000c48040302d021a540780d02c11a0706240c1c403070703004020f81d9005403c081a16440890700b00f800314000e0040074054003045d030b0150f041010020100f24541a40300c8154149a01c0c0d1050419801031118181c200714002021542a0f040c00d09110100c098207951540c0702c0da040511004440c1d2040c021501c40c0d5a040c0e075400b044280710700045000388810100c0d000800c40403a82600d12042c24000b56002e824941001a034450810403a20f40451881e103015400781c22580021501d00795a07480803d2844040e01d440091001c103520071164042c600392640c1c1c045162001c11003202086500c800d06040d0b0a0321455490803d0b2510f03c04078450714000207500d98007100042c821040c0701c01e400c039240d10004d00740c26285503c0e41e841c00e040e0790a03001c41e400021 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 758479487 1250 758478237 758478241
    0x3050c06091605100203160c08190804060806030a020a0e071d030d0318060609060f0617010506180405040b0604050105061303082104030e1005090906120a08040905 72
    0x88180304654102080d1001414200614040300341902c1c02407080c0d91040c01580750f10300d40300d8000c1c02240c402452249007002464804d181200c1480c00714040c10b500f41c0301d81c080540c4140c04540c14042001c6e0000d1102e400c05160100484110800600c003507054040c01da5100300503260418240050711500003404030502c0c1000d001021241140e4030400f050403280381e0911030351004900c0780501c00d201c3ca0046403026140007a080341c42001c07503008101c0d43c0740400000c1c4114256205605450320a00da401040d503070741e401101c0d00305555141540301400080100240c2c60450f00801c02240e040700f003130a403a1000070010382120011242074495411030010005d407450039100300d0f80585403c441da50b0802d040c4465101c208122400002c0200c0400151a0038258820300041000381c0a1b501c4442d9078586481e00034030a00c0242005030141c100c0c408281c04043c00740b002e981c0f80000240c05250983d0300c1c0300c1013101c2c4501410082c640c81c02202c0c2c1580104000e03000801c0909000c100105942c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 758480737 1250 758479487 758479507
    0xf0f0a050601172415120402040b0a08070906061e0e01110a0303150b070b01060c17071103010f0506180a0f11042102010c0303020903161206050115080105010f0513030305 75
    0x91341500c0e072485120981d160b43d401c00d41d24400e50701441c0c00c1c000403502603951440031400a01d0240b4005900040c580000151a07074006030040940e070801c901801310036a42c960603510110074070526420740150710401c000451040311745c880034080500d0b000c1c050003079045141c0d0a00038140c800703800180e116189022003000e6100040c00801000355900e14003043c54450f00390a17a018084e641c00c0010006581003804424185650100c6180000b40d50b81d00075490b18001c140c1f480042c0600a508100da5908a24043d02c11184210006060b15900c940e910704102c02c201c2c2c009181c2c011250791880103106134143e511a40100c6021030300b0300c590311b074100303601d0040c1d500c2032089100c0800580452100181d0f4003641d807d141651505015803504401d900007420404401b04006039000c641d14001140e01810a2881104c1d0084808002a0340c031042a001c10040350643d99002c0761160b401000294454020034402000030b14086003000103059042c600c20b0241d074002d80010f8004204207502c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 758481987 1250 758480737 758480791
    0x1050d12170c220b030f09120a1116080615060c010e0a050f010203070509041806050408090a0f080a0209100314070e0a0c081906090f02070b0f0f0a05060117 69
    0xa4292040084282c1c2d41c44d00031020410310000300014401e03c10040400c80020713041244800003500034040944640340c01600800d04010804054014070440d00f429081d083d0184419050b5442000038142c55920110343c3c000762040d901c4116007083c020000f07059160700c00e03c241300f580300260014000000460034000d1821360000d080d0785070381c0d2040050000c07054120b022964a400c0503180828109048400d582c2c0c0e45c04804030240c88a4108000c01c01081101401841c01d4402204c21415050702c56407581680300c1d15019601341584800f080c14058942449010351203c11102d81c0b4003100d803070740d80350701916a40c24401c84059110390b8003403111482001c130341c0e0343c4030000c0c100c20084590000002405000060b0070340d50048985035400901c21101d402c880d0203407030561010f000004403004aa4000d5100700f40c02c0d40d2a1904030045070054203404501d50223100c002002d0b404a4482000c3c9000400c0040c020505020070301c55255144942c94000318418005502c0d51400d0781f00c00c902e00c0c11 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 758483237 1250 758481987 758482027
    0x6020105160c0b0709050d05060a05130f02040b0a15020f100b030a0219090c08011e1d0a02120403110c03010606090e1b04081f0501050d12170c 63
    0x3544800c52080801200c1d0b0003600051055000404019503407150001943d407040290002e076000045050300c1c80c1030040008101d802100d881c80704000300d94a0144030b00320000360b008000c0400204103800c0004d45400d811102c05444001d11080c4020740e12042101102140d0210602682000c1c81c41d60b41d580003400540900c0c01004001d0240c107103076a0009850751075140c0024800c208890901100b0300c1340b501c0f00806050905001c000b000c078012005008650240700310210703a0b1106032240c010b00050452001202e154900c0c0c581c0e002c180344c1e6203210000300206881400c1340d00f4440303210445c0390b1007103c0340241d0203503c61180d00160030780d80c2c0c0c0c00c080030007090a01aa06158040014560140d040c3c02214030a0700841c1480d200c10b04c08040e0003501c2c0d0140340c400384010130041800c080200e030089054a8110596001c0a00c072200202a9002446120792043d6940b410f40301044980401c59551010341c0303481ca0b04c11080741c2800c1302940b0f080e143d8201081001c00e0f4080c01140c0c00b40c140e0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 758484487 1250 758483237 758483251
    0x150a090806151c0609200f0402040803090111010902031b040b0f0a090f24060f030b060a120209040f0213052b02031609230907052403010f06020105 65
    0x4070341400c01801052600030104078010541400581043c18403500d5402164840c1e0301c49080340d02c8014404c0303240380b40790703810403010b10072495412049200c1c60940700311000c03a00504040e6092000d21401501ca040104240d810307107540780d2194000581d0240080c02e5011260380c180800b00c0f00321000e100841e08001e01c4207024031001090406241c2c1ca20b4421000c83e2910800400c004011a2015000e40383e190380b07000c219101800c0d00325826240020580544d01603945440c0400c01d0081d044054a0f082c1d0300c441c0e0000410061101c03401c0c4241540e00302104004000b51410500002180c00c4440581542a44503230224803685402001c010100082008603400700d400280e0b00c0106188002480c0c004004a92540c2418110740b4140306151032052900078190741d041d659910351000e00001c95006000c0004e60f80700003080390480c448180500059070083c1030f04e80c140f40600045c29100410703264020140c000055075000c000000314043c1004605170f5a22914009029094640c040d00384 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 758485737 1250 758484487 758484511
    0x41e03020127030e0f041404050708120712050d11030a0f060f03020307121106071104320903090307032103021e0708041206020306010806100c060b150a090806 70
    0x110754004244654203104940d0117440c1c2500c9800100240b00c8041c0c0300c40c030084000200f000f40003001c0b40b40c2044031080380903100306c095644d02c41c01040c41103100051042c01082c0c2d140d09a140f050001d0f1045081c02e240008449041c451514155081259038605880d180e8500300e8640c011350081c40f0041c00d810f080b40d1103080c00c0d076000030f480303907818090f101c203042545081e0024490300050a0012600c080d001503a02d0010381841350700b2806011401e40203900304186c4040c0c14804070070641c00c0c0004186505206686c2113480415030307101801c100c05d81c0c40309000d0a00180c1d03043c066100210711408031180e80c13003410400701c2c40c4800c0f003003090001c0c5441809402c960006121007040e54040300302c0281d56501c02d07858845c0b1140644c1d00010300503000b900221040092a6000354020f590036242c00005507680010400c0003e00b5220080002d00302e4400b140c0000c896400c040460700c801003000004081605181c90107810100408000403c0e21908201034038081c0070030b82d044007460b03180f = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 758486987 1250 758485737 758485811
    0x30918161107050114090603040807030e03031e07060e0f0304030213050c0712051207170a06061202072405010e0c07030f260f090d11060f041e030201 66
    0x1c520345920081c490b26040c0030407400317108903d40c50002211000da100504158680c286410628410b40004200b1000702e03d540f4184c110500d80007040d20a070355185a42d50000981c251000c1c200740e0842e9504a032400c4d1034501c0a80310a000380a112524000e4400941d191031650042110b00904052120801c1d407405041c000c0100390602219401a049100c0a2403081c21910031503441c4141c240300e1444050707203000c0c01545036119103500400c400c042c04bd0f00c400e0b1111008601242d02d54401c20740402c0044512084071500fa03005807480c540a01d0080841c050130800522821101c0c04e802c08a460703440005001080c00300c0d18007600045c44000743c509207025590003602488205445c0424012080b400d8001e0368400c0164003218607940758001c0003802c2000700504468010b40d44c0d8095400780b4007441d14071070720030185d0340040100c0500408054840100706100303000054400e40c2d0074221144020080c0180c1c1c01c09001c450b11a038000241400044082c8204620035504903101c0001a00 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 758488237 1250 758486987 758487017
    0x9032b05120105010c050f03040b0403031413030201141b0d09080615060d060918030e03011512031413050f011e0807020c03010612060507030905150903091816 70
    0x1180c42d05641c420b00304891001020f0504924040800030341202c04e100005012585d45010320242007124801d40301e00010a4942a840103030340111803016036240701c03011003007016603c18407440025880c541045880c00d14414520200000c004e031a0303400c154080107074402da01c0e600120b1040107041e0350001d02643d0078809890171950501c000818850f14010503014031400403a4828801091002410440d2494400408078409000e520690101e003920040100600b410300400c01c00c075499810140c038071800e140d00c0e50901400307a071040e170400c040b68070000c04008034040202070000c8081440010700b0315007400c2040b18440d44a41504001c96128500c3c3c1200f40d881c1c00700d84083ca0380c10301c0b110b1a659214120302e082c031000f60540d4150300b8500d00207070806081817801403940c0100c07000e01090f69801019026200c850100800700d5001e1590103070340c40840e908164004040b4410b4a19200e5000000f40410182e0707231031300c0c40580c0d94000307204c0c2a0071201040702c8100118104540c4031500f903c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 758489487 1250 758488237 758488267
    0x40e1213051c0807080409060e0603120a2c1527010f0f02150c0d050a0213051c060504140d08160309050a050f030c0723010c02040209032b05 62
    0x503100514510f000315640080180000036a0003422800340204503a42e0b8821420701401001c1d02c42500a000341e00398414480c04a101f282e014004680310454000e40f2a0703501d04601d10056800c0310f00d40e85035203e110040e6145090300518000c940705403030310307154030740c5034510007095040c527180080d0341c00550030003940d23042281c05a9103d960300b4805050300310190240d0070b040300c042200e108400c128013003082050312080500134a40487c0c0080109a070313030000303210481c440c10407412190000307002c0411103482d00c000b00020300c004100b0755011b224a136039a0b035800d0325029542224112400140c9030509a820050b040c8004418a003892050074100710000c4005444007102c010952154400410f110b401c0050301c081680c440211402c0c007050f032400030340f00c1c5c0040e8a441344c607001e8850001044010591540070811501e10580c40121009005446001003503004980054007030043d034044c2d98083c040300540409042e92030000001d61031140c440081c0548840090080c140090072015a4034 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 758490737 1250 758489487 758489539
    0x5030f0a0f2303340906180e0403050c0304030804030b06100e1c1b0501080105030703050d18210b1305030304060216020a0f06090f060f0e040e121305 66
    0x1603040503580f622080c134000315218150280900d2150820245a0880302049030051001565501c12440a44414080305e0038104689552040140d100781402004480202e4980040c071905019140a8292070081e0075501300c1d51041e50030070b801040070010321201c1e070310180d4055000c580841018454402c0900103101c00400b036805040820180600801c0320f110f00e40d00c0913000110516080d038504407035a8401c2c001e0044a000941420001481e030400150000950303074444050132064900705001c480d203111040384820762401d4134270b0000365610706600c0c155020395503001458481100782402c560b10100074040c40e250002c084000404100040240c036006a4003900143e90307100ca00814091484c20b0342c030042c0d4030000b01d0300b0005051044682d40400c40703546417280708130143c0c4c5120f0103001c00401e100301c4010030500c80c40070400a01c58030300316601c000010710004540c0f001c1d08500c0c2c50000000d42003111070700c000501c50b00e0501d410100324014001140c519140d404481e40b421210501 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 758491987 1250 758490737 758490797
    0x90a0221060a0e1620070f090608060c0f0a141603031401080c1e1210060801020313140f030c0c01030b030f030723060f25020706050705070305030f0a0f 67
    0x4000000e03100c1400b6080d18202281c5002158a459107c00c824228a51580300303008001d4580318000039070180228500e44281c400b102c4176418100701c8404502c003940030b0041c1e003003081800c1a0440b0102d2200d8050101c03001542ca50290f020710503c2d01a04540c441c0c54005c259805d100c0042190050000350b44c0e814110a8804107801c0ca0850780340c018440c860b02500e80c0c04500d82d2460300990000041482002c42c00900502c8119614000079080344030549201c1360170f20088400b0030104100150303036a460011003045400980803110210f04507000f064482c0c860f6003100c00d00c51020742c0c3c140500f541002040f0064411810025000c51f90392151400c010000290000340c000e80c81c1b111b00c6400301e00c100345001e880383c070710f4104c040340c2c0344150482d1283c09850804000c810754030500349450414520341e8004182240c2442005c1c2ca40303800017001281c0b01d01c1b5101003c0000b1b40103001800c68010b0500c201501d07003454040140038090b001d0200c50801004840100341103e981c5a10042224 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 758493237 1250 758491987 758491997
    0x30d0c0314010b0a0801061d0922081806030606030a0b06070507031a0a020306030c0f0f0406151b200f1e011b03020c090a0221060a0e16 60
    0x211014150054020080600c1036500d9a000005900000000038940900070b951244801da8940d542914881e480c09462081404c010111141c41c4c1003c4a6040c0c01080210307100302c0d901c0020031003204094a41101300e42e070140c0407881d018140c2c0c41c0010480c0c41030301296071509503c2c020001c2540f81c040104000d898075180d0480d0005611350804540e000f07604081911078031916070409410003440e01d211102001d011070001200042203100360790107020010302030005400d0034401c1144207030500c56103076441102d21000300c03107595480c40340800500e00001402102030000b20007401850030240c42003803920140c0e00c914006514400210305014000740c444040b01d484401003020b26000c0343e0240e80190381300c2c860f85c90242076811160191f060981e42e0800a500130822000405040c484c0200560321940c1c11f00c400745440c06103164042c02e107a20050618150b0009140441c1a000040284566003070500503075040c00452100502002c800110587c00c0219078071000c00e454850081c1000 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 758494487 1250 758493237 758493251
    0x200c030702040b0411030c070302100225170c150f0412030c12050403030b09010f05131a060a39030e130c0509040b0d1e06060306020301090b040e0f030d 67
    0x83d8130b0380c0c000404494101d40c0c1ca038a91910141803401584011070903805840340302c1c8080450715045c000c807002000e03208250485540e14490b1254045201c900482c1c003c42c3c84440e43c410b4040708c2025000020009000b4a43d0503031017201c0417480c00e0090b00e8108a80314400800010940310301400a07040098507000440301004c0d0400c03610f1001c103c0354000c0c028109401e20081c1540360300b2918010b1000c0f200e120329270740e0711052440320425a224081d04200641001d01000c0580d80c01100070020350120111030500210000342e1701c1d4004210f15020810300b20b01d03107040ca039090707583d043e010840800c08103000045908040d44a0014107000f030400c846200001d089803149200505103520000d003d001c5524140d00180042d081405800e0260349480583c41143c5001d800c049003486e00900100300b018111200200007203000c200696049480c1c80300000018103d10096000300f1801c2c50000d180400c080400c0b064954101c180d241c43da0100008540501010040302c58805c040d101c0041c0f40 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 758495737 1250 758494487 758494489
    0xf0904060212070f02060609160e0a0305030705010221100b0c03130807080d0c11010f11030a030203070914031f060e0903040602010c051204110111060406200c030702040b 75
    0x82d1007008216040d0445050501c8070643d084132500340b5a00d0386400759603071aa0f4410620003000d408403514130003c080c00b03039070820b258019a00708010780c9021b058001030355125100d062440d4003c090403100d607940082c441d04608003903101001c0c0b14140c501c00910500f4001c00780380c0801c0c1344d8010360f200c1034000180b040da100c908104030740d4031203000701c802e030503255484000c140c480c2e10510075400e59026460b6094034080c401d490072203540e54040c840700705064120004455007406a02840b09002c02e801c100700b4412030410281c00700b800c055501681d0ba28000f4001007841c0c0607544005a00c181c0240380d100f2a54022aa5000180c01d12800c05061115101048090200c076070005002084040c00d10030900d0000c0020420780717038140c00070312010305840f608580c0e500c180d01110342280020b4001c2000194810b00010402c1e405140a800507118621010704161050300c08071902c66076000c8521140900010204440020341d03011410000300c0c80c0030130746910032040d00901c941e0b514602c01d041 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 758496987 1250 758495737 758495741
    0x10e07030510150e13030815061e040314010b1026041707060207050c0d120806010201140a0b18070c1514040305071a01180f291309020f090406 63
    0x5101c030703030020003107801c017106898a10703075100b14281d0008210100280300801004541700d02a41c02410b864030381a10b00e100c100342100e5015240403501d10030000007011400c0003030f00c3e00300c0f8000400005600c0d900030b4100980390250f0410442407146001007003e0b6182c0c3c11314007000c0d085103009000c1165461741f514901125407101260300d540004140784041c4030f0958003601b5400d00c10412986d50a0301d00c4c0400c0241e0300d00080c000c00200e12440d400301c0d4203100796062070f00880180000b041c0444583c441050381c0b6002c584804a856440700340c2d24031481c0c0703002c024901c10500700980c0d001e810400c800070030423084035101401010305000446401401341e40462051400c203241000c0e1410b1914000702070ba406160252845404800031b880a510801501c40c100d410401c00030103050540c001000161003003122101d107203a5100034003000f034015118401c03004408000e450401c0b803410410400c1d01042007981d209a46e1602007a000182c6490101d66510203080318400015942d520f01200 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 758498237 1250 758496987 758496989
    0x30605060a0b0a031e15030f0f0203010207030e0306060909070605090a050a0b03061509130c02010e01140106020106080606101b05030d050417120f0711070305030a02010e0703051015 80
    0x24000000203080c48090707a060f4020200c85070b10304680c2d01e0100484c141e0724146c03400c40b0907851001c2c00b1900104002030345140c0720441c0ca0300c5082065170340289238000900726040784106034082110610604140d00d01405034642c084030890310200581410035909170344441c0c0b03010f280705000700060065059921f122107207005090040004100719101c0c4400b410342c0e013064418601074a1024070b00c2c011450a5004d951466401601d103010307040724440e4a901411700280c0702c500f95541e03814440103042302802400e1040003c0c100074100c0c1c1d403424800031300712007450740f000381d45800460a000b9580e9620211200c044503500e010076601c4000e8800440c0010180d030024441d01c00060010404024cd4005c3c6110f24015000341c0c55a0002e0301e8000d859115881ca140811a040c10000d1031811888201035080052031070a075800d54121500140f400195400641c0d8650001c80c120000e0340c5d09010301c000d140050005421420718503079645035a400210740380010291540000c0c806a580f40641c0e034 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 758499487 1250 758498237 758498249
    0x109060e060f161202040f091107110103050a020408030a09031205070201080f06060c06131106030601050304021e0307060c14240a0f0f02090a05092403010e01020a11010e0c0901030605060a 83
    0x156116650107c640d20100c4902c0f44402180c100040301061113111002d86031b0305500400d0b1000d240450400460040600624142c8240e90903c0041007000040010301668401e0340c0710543c285003941015200911140744200410800f0441500140d80c8030039240e8014500c43d0070302c0599160100085c07042d00882c0c100c0c99440c0b1800342008100b14450140d42401d41c00b440c000040c03081543d00740300301032100302d0b8614003140c000c001140050a0407c0e1300400715201800c0302d445c80c00803070000703030030554030307900040000c0c0020078680700b801940c0c1d00c42521111184000d204004e0038030349101c0508402e01c1c090750b00c144030100060700003403280c100040030380c20500304200090021039650003d420030b1202c94000d800c0010040307000e00708083c2d101c1c0500b910541c20885080c00c07842d405650031411300700c141c06540b2101c03250700b001424006070207201e401e62640d18100342c180020701d0071500c04c0100c2150760f034407406007141c042d11f41c010100e040d00d0b00040c1c04111030344e925001c075402c1c1c6507aa001d1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 758500737 1250 758499487 758499491
    0xf09091302100914030109081605010f05070c0b010f060e2710060f0f02030306130b0604030b01030203060f010e1303200601090e011a0607020a0f03050109060e060f1612 74
    0x740d24070b140d03c40462415104080e4102601e0010a030605080311813518004154041c1000303411845410710f07020201161090b000400d00302004108042910000d40e90742000ca011000c011041041105c1000e01400410180c007004603c5d041c0b0041c40020844081401031514000090300b88500200d07441924000078052419411b00b1545400d070300713590b480b4100002e605803c00000d1a842680b5000c2444401d40c001c1d820741c1c90303241c01c200c4289a085844142550380b00b161543c5504c03100301a03c025400b42c7c5000b8040c2d89540181350074030070001c0048105131440c0e0014405402e07607940064000d40c1454600c8034000c2c542c50155680304945010050350310320042c4030000031500190700b078140c0c0c1e02d80c1e40c01d004002c0e90070f6080c0e0a076548850440c44c11550800203d00904085024080d420300041000c2042c82d51181e009400c0b044603001030310a83d442e07404400510865000341c2c602d070600100241030f24070749111b0341d000350343e0081c01d0400e60781614130021070624494043d0741301158041c901 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 758501987 1250 758500737 758500759
    0x80c071e030e03060f0c0a17010f05030f060412051e0d0515010201180602030417070c0501081e06120120040e010503030702060d020a0c0c0e040308010b0f09091302 72
    0x31200503100460490000c2e0b684201d04546040102e0560f010340c01c0006a00d201d0b4540340d00c44001d03074206440880c2006903180710641075450901615000b8080c0801d400c8080781020241410104241c0340020f450384908284000610500e018100d40305045c5422610340301404049024248200094010001d0204a403805100e003030748950b001d8002d220200c5c054180c468016802e03074101c901114642c800381500c13800425000d800860303000d442199920070021a4480b030041c1c94009080940d100720000d0001c1c8281e50704042100e411140c900d80d04500601417048148403c4002803180380190803030400300883c13100035003048904465001d4a1111549010040e04940e040ba00c18145464000b800002d854100030086a51060300908140d250a40c910009070195210141600030482d489a404000c50310304d0000501420305150070713800c0790a060800405d480c80c10380003401d2506003000750490400485084620501c001d4904554a903a0514a49014016140f019400c0381c03103080 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 758503237 1250 758501987 758502023
    0xf03080f181002150f010f2606070f030c0206011a070f08040b070203011b0e0603040f0f082a0319090902031315090816081c020405040f0e0706080c07 66
    0x79084280009500041040ea03135104441405c000b400c5c460003000c40d500b01030a0181071490503c41c00b402401960301200707501c000748541c1c80e012080312030400240c0fa18281ca031b003083d45805400100c82c160b100600d603a5060403010007030b44602a07584500383c600002c0042c100318a15003400061038010b4000d80d2150b42c0c49a881240d0b0b07100c40401c80c482c0d4641006c000341882c1400c2100050032141d0f42d42e00c0100300344024400c072603002410070340d100070f081e80c0c40e2000100c100310181c1c10b031841528440d0b141c003081c0500700807000d07070307400c0c441d40000e855849006a50000001c3d80c030f410300c0c1ca07004040c0c01c1c1ca03522819141031140b50019541c06000204100001035440c0c01002814410f4000003070f50302d2800d06a00c00c85d51005002041f90404100502519140c3c110b04018540501e2079107181006000c424650112444c024005998000c01c04100c1d500c0c2c140f0070710304003201a4606110f8000e9103c1c0c00d68640080780151008e001110010a5540d51b010b02074503c05584010710b14414140c2d10 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 758504487 1250 758503237 758503243
    0x15010608330a06020102040b0405090c0c0a05010c110f0a06020f040e01030507060e010c080316141209061308030a020315130906050606160f0510240f03080f181002 72
    0x224030b000e00184000090001d02c14400c0b10201e6880051039410301703080904105100a0141040c40d0240050000401c2e0000c00e00010000f0b910070700000038640702e5000301608070041c1542d4259141c0000b01c032441c0540011450000b141d40c070503001a1b40d85034140701c140d054025900710554003281c0c0d00000c070811100013158004e41d0380030340320005e0200c1000011a16014050001001c040d020b0000c10360b4000c3c0b503400181202a5818401d00da110740c120605000d42001000764003401010082c01507020040c00950f42101e14902089000d4290340c607585158480501540b24281d80000003420010002030564003607a0010400103c80850403410b001501204500b40c655900c0c29000c90316030300d8400d01b160b000022082118404407080e8039414954840303900250b40c14041c03074005004840c0d0134407581010003000c01d01715240244031001007864600b583c02c10191340c0c140440500100703010109880c0035142290159503a45c43d14901d100c503842c80691025000b4107074103603a4540c0c039004 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 758505737 1250 758504487 758504581
    0x120807200312010f1203030b1309030c21020a15090c0f09050a020a0f030902030a080f1c020a0512070e040911040e16090b15040608071115010608 64
    0x5014003882c0d0320307080c0400c40075080b0b00c580714419000ca00c01c000041c3c088c1d08103000e071400c010b04513860344003242e8001003550401e4070204c2c00238103074082031010003100d617200075420b01d800e900080319151400b03000f030756420301128003410142c02c00303448a544540030340000c1076880e4004400c1c966241d603900040c005900702d004208a0702d05100002e401e5103014400d2b200300c02d941d6918080d0b02e040c20036086c0c1c000c06d101c900c20798160040e0750020010174003100040c540511030400880d40c3e042c01c00c140c42c2962441502821a0f5801080043c0314594460305903000300d403148800f005503840340c5800b074a003140701c820a19003180c1400b0290051081d5080170a82c841d0003610107001155140300c00d181c880444009070729221041c0103080c00341c1041980b119541d503c0c040e10510f40303902c901140083e01d40250703004ca4001030440d4100101d06a0123410240d03507070303c100700920701080c0000040000c9001400340c41c00700007000380000c52181d14004040c3d9507901d11381035070b080a20a660380300d03550441 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 758506987 1250 758505737 758505757
    0x30709110a0801060c08030403050a021e03090102010f02040b0301051c0b0408040302101e0503090a0501060e0702070e09100c030222050111150115020a05030a05180405041208072003 80
    0x901d0300010742c0d580654545c2d00c1d5907511900144ca10742e500d64040d6180c0e004080414210303c94004080400d42c840a280010892204003d50b217401200000a080d2445404661610340c0140700c20080c111019068a065602c1200c07003039003101080b0b0740455099020800904203c20f64014803043c8000300c4014816680241c92100e09140481805e40c0c02e01ca5111030340c018090301241540115109034003550304182d9040c140c4080d01d07030507100d0754207440070b940000c13401c00929002c2c041001d804120f40f034028080c3d01d40002c82464400c01581c1c48001c441c0c2d1800d502501d43d4902030040f44241d04498114000d803c17411a49141c060000c02903d40c075006080c0801c40608644100000020f44a03006c07196184100500341e00700100d09440300d40060f03ca40542c802d908460340000d00c1440544180c150580d181c82d01d40410b1031070708d042e941e20840c1240c0110301d84820301000c510300280c1280110b100d41407401c49504c1f601000c03504049400c03182070000301240142a0420b070040000c00c08058 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 758508237 1250 758506987 758506997
    0x130e0618070503060d060b220b01021f09030c060e060403121116050312011e0b12040803061801060207051f0c022e2c011d030709110a 59
    0xd001001629030240aa80c040081070050000078040c0c07130003802003100948900d10100d9440d0581c00801c00c1038102280240d0140c0c5002a440d617110200d01c200d5030010b00900c001c02c1d24042180122581718502d440d1082002d403180c0d1040c2c18140981d001c0d014030742c1d001c003040102d8498580182d844a5080d901100015004c00340b42810040ca0b015071500e0910031600185030035482414907040c0002c000301203800d03001c140844200b81c900215928001c0a042004c4215030341003140416424046402500340000d09011150208050705440c1d83e11507448105969640c84450000782d4040400016400b03410741c403800415202e6001c24194102c6100341c48840c5c00c091051881c009104052440f01d000a041088020141ca005000c5441c590a082c4402e00100540c0c0c540100d0041d05071100000300e48c21148a00b941c0796425101c0400c1c2410081d66003030014001c000030030f8101110f41068001ca0154400040c0359030500410000308814602007180030803140c4a00f0349034002c1c0c410304000c15 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 758509487 1250 758508237 758508259
    0x18150117011a0a050409030c0503030c0c06010608090303011703092107060e03330109090c0806070f0f050906042c090a0f0606050301050415051e1308130e06 69
    0x20491021110b4000000388004070290802c03061200401500707205401b0800043c60100c0422002d0005501038660207190542e6440c9c0848010302e8028107034090020091444204846202c0c04000c1e207054032422010816a5582643d12618602488070250b904c904402d4400060903589e0440d0016101000e05940c03080d562a8015281800e02490050301074000601d85400d100c850b008124007181d040303038110300c00e14425409800d154000d03000080996500c40402003400342c0e19544c00c1c005c1003850000c0a4501d06942c00a240c070280003103013070502c081c01c24402c0c1e40074011020f50b17812000190881e61103d694994400d80440d0884840d100c0b050840c4179034a050b660f00140f00e2080010000518006406035618041c1c1c2c2105803065a0341d6568200c0429141c1c2c081c019a4019801025102c00203120301c0141710881c1c001414020100c0c000c040507154a1046070a9154000d1304402440b00340907040c20b10b1801881680c0442460001009021940b0903541014901450040e607000c8030031 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 758510737 1250 758509487 758509511
    0xa230108010b0a0f1401020a150b03120c0a030c03090b0c031914030f250816091d04060f020a080411150f07140303160e181815011701 59
    0x4012601603440c0000316000f040c010f030320140015540d45c40040c811508407449a03100e083c1044090300010300752507110314242c00c5515003007141840c4c0c4109000003034a42000d00c060180ea540c01040b008042c04034982c0403c00b0702d805000c0e000300804440c04500e035110450783c100c640702d07840754018500e074211aa00351001c10b88501c0b40c024000798150034082c41d54507081007088400c0801020341041040030503118540d1002540c080070344499645419200d800c2c000400c1c034981008825200402144200420007032441d907c0c0040d00011007010408143c451b800c3c0800549500000e9042203400020080c48480d4015401c034812405090403070702d007190485c00c203c3c04154412001d0843c1c0c20501c43c00060030151002804030501c9820990f4a500715000c2e41030070740d00201ca0401c044400c003480252640d401441050350610120f51032000c4141c0d85082400c0020040d001c4030f5030400100c600364003064200502c80550140c0c0000c8491580d5a0601c00c07102c0828614884981d401c00741d005100c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 758511987 1250 758510737 758510749
    0xa0c031803050a2a060908010b091506070503090a0305060105030d02070602030307050306010c201305100e06060d05091c0219030e0109120605010305070f030b0703050a230108010b 79
    0xa03a0b60000103448584000e48810030f060502a004c034600c4500d01464000000c031489803007006010035110b000000780352002942c21101441804ca00a030100010021842120b0070300c00701c0c1e00390440d2001d8070346100e400c10501c0d50044200c46030b00007000110100a1140c0021014102d40e02101201c907110704195042340c07200ea83e44504800b5901c18004901000d0265001d1a4030017810301d0112102c0c20300381c90703a8150a501c440f440c407088030a5041d4103200d0400301a115070300c0c070340d1304018491800c021103021042d42c144e12a510307140e00758002041203503481c06d040302c1c011148250280300a003003070358079a038070b400860200782d41d100041c29502410720300104e48501c2c1031036030080d09410304140e920152140214908101e04100c0d0b60400454070000d60410a880c2034040d40300040c603581940742c89441c000140e0409494011107981c100000384203004d55551101c402c6c40c1c08212074895400c040042c0c6104041c007601c11840c80a41399402d030300024400d0480300c00c4070080c001c500d900818480 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 758513237 1250 758511987 758511989
    0x4020309072c01091107021f02010501060504050f0f0a030506070201020a020123040f0219061d010e0603010603090c05060403050a0201080114012010060303170c1315140a0c0318 78
    0x2069000e41c80041044c0e81444d03008105520480841c2454501e0543c0050342d10310440180c104c50241d034082591510741d0910440d07001d00356a0400b645081d05250000d0140b0302031040b8184240403c0d01503400540794658080011a4070104460180c1000d5002034040c0d0003801d10280150700e011884402d000b4055810740c019403d090b4410143e03191902c6500c10302c94000b03002c1e81c02c031400b0341c0340c1c05261006d0000e0900a16513031751141300041d80c0d150500b00503181d9401060411010891f01c031026601d481c1141c0c1111054100080c05490901d04030307140e080d20342d018591004001c900002400404100140094800d80c0c81e00c43d541e881c0c4d00c4030b422013180040c03114006404d1010100c007803c3d81503942d0100100f20412905840c09403800791040d0303821604100c00003110456030400b050000d490031900801c0082c500c03420711702c91180c1c4006620f0b40c5d01c031310112103020050007442c981c01a030510b14000c3c820000650740794007204000e040104900030440c0010007010408148402e06c40c3da02c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 758514487 1250 758513237 758513309
    0xf030708300a05060d08040617011a03010e040c03150b0405090f1f06050d030c0201091401141602040c081e0402090a090311060403020a150513060c0e0402030907 71
    0x50391030711109188070040c40000d040385d802c45003080022012a134910f01520040241d80d4035811050400b1640701855101039002c4002200401c821141c02a1410266811346d0950a520051075481e810110b03c0010681d10141c2106000c440700000785141d5081580c0e005411b407000d0009440b1008519680c1041c03c1404109401c1070071110b178010104c1c0c1c52401c00d4075580310040341d910b0329400040c2645500207000c4012078103584440c0119600030300380304001c00107421070b00940d601000018140c1d400d41c0d00dc002c403d4500080030498440c051691001154018000704541a4461809000194180c500038a220303001c210090782d90444c4210688501d41c0034110242301d0b250301c0141c0029091401c01201485102c0580544601040000f07501c01c0740250f0041180340b4040c1000c45543d820484180c000c0c9041400f00110900c480c3c50002249034400d10000d400e039004d03401214140810350703109500c83e00010900c544108000380182c01e81d261031055551101401c02d85910441c0c1d4a4800 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 758515737 1250 758514487 758514577
    0x60f0f0506030f0c06090402040918050c060a08010302010f05070b0703051902040506120c071e1209060516050322030b10050a03110607021807111212090f030708 71
    0x34142400e100d0302400d1b91a401500141c14281c60703884000913541c000380301c038a9607071420750020b00340b100400203503004080c15140d881c602144098018460340c01404007a061004118883d4551445581100d58554000c181140941003000005021302000d4585c001030110007808043d01c24454800c0320300320303840146824a03000c808450f03203031142c0300101100721840f010b100f6038000c01c0440501d00100100d145d01240c4a01d01c6d85000205c03030303540c46664420422700a805101d0203400c8800c49000030900540e06642030018580f81e803a40c03184c02e10110301c02d22000b103c003444441e0700074404c0c166407190501c0c9040f80c0c1c0704d00d818500d060b41c41c400c07140d020034400300800c0401e240010904010002500300b600d1710402d500883c610f0403800340f010300c41710404400c0010707050380000c0044402c0d42c2400a0003003000301e000e020483d4090f401c0030404c0170307540c4000701d00c249100700300c0c2c5a016544101540d80310b11440c00d2091207900b221b00c1400445160303103001896012102c1000c00703016182068 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 758516987 1250 758515737 758515753
    0x105030f0c041d060c22060914030f1c0215130f0602070b071e020a050615030f06011e060302031b07060228020d02030909040b090307060f0f0506030f 66
    0x108409040c03440c0411100c803c03140c690182e1090207001c0f00e031144003075100660352045820b42d8040404149100002030340a880c0c000d21085a10080650894010000000406c407010300001d007010266039522031280b0555041041e13085101030103150b8201e403a000d03288200c03e142c05c0c0181c04c079022508564034503554084000010b00d030301d02c074404140c0281c000604013180342d911a10900d20a40d18007021a0803111074003103d1007032001c0004d110340d5900c06450350300c509a903491780d210405800704d450a0000d644161098408100c0200c00321800002c42d403941d6506d0a5243c42c101040d8407071a402c3c51002404034a00e8089e008890140c12844c100c80b0201c1d820b45501c1103260403440c000c0300c516400704001c540c022000580c1d0100740f805007134410b2105030224000303843c141d001203004003590000e01401229580e000e500382e0303116420000f02d00d035543c2d8004555007540f00c1c0c2400133003000e140114100d00c034100396205400300e80e0300f40020044d9855a02c10107035184c0748000c50054580c0001a = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 758518237 1250 758516987 758516989
    0xb010c02031c021c05090f010e0d02040506040e07030602030a05220f11030a1b081914010b0618010305010b0306090a1e020a020a120c02060a03230414060105030f0c 72
    0x80b10341108016032060f100d0b504800c81039120b000d140b10000d0780004c1c00c08100d8012610707001c522030764040000d090a4680c1c141c039002103504152030301d2000c2d104a59490001c2d0250b01e65822615204090000362480d050322803509000039001520304e6107034240b60100003a40041407071203100706040c0038402111242c0045d520914403581030401162520b42ca583c85080580341008107510040c46401d00c0d05141492850440c2d03c07440070b6010444581c4078100d944c0460f500301510302521604440c00801803804a103105000d44000008a6000807001600c02e100001d884400315500c60243d81c02e11176a60380b00d01c100054001a508141e009030a50082528546a68000041e640d02d00240d00c0d0982051400f4074101c0e0000b12594002d0303000311035068100104070700f0780c0e5800041403c0440d04030741d242c1c004c544035029640004061650301c0130100c611110880030540c8240904410707440919251910044241040c80954960b02c07130712001044030310740480d0740c10342145018020140312243d08 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 758519487 1250 758518237 758518273
    0xf051003120903020901030b0a050c1923031014061c0207060b0307090e0c090c0406180f030c14090f0a0902012715050a021902310b010c0203 62
    0x258510007800066100000117031a840b50143c000c42c010841d4240520f001425201520401890014032040402009948002c20007110003c50b81e20300e06030320070070604000c1d0529805071040d01d01c9485800710070480c22001c1c0c030080106450003055116502c4401c1401c0c00a0f0b8002c100030055901c14049020071444a5580981000c41c081e010100c2c1211016010a042030300c41d0b0010342040e501c1c2d0180c81c8061208204009140ba0182d80403c224508038294603000c1c000c0707004450400200450300c1c4207104082e1043c2029000391007403004080d65034036050320a404180b20710a00c018100c0c0002e103851510500740d80c442d1525880800c0750f42c0d16079103c08020944260101d05000c0c0190315007643c41041c5041204454090301c04084e42c5042507030491843c0c0040d07495208001040103078401c0960301081643d10159001e0804208266910001d02c20030000c401405842d10130300c1006c0f0301402d8805031081d00c140c041c4800c00002d20400b0044900044c040d00180d0941c0c42695103d004101d01c1c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 758520737 1250 758519487 758519513
    0x1101050105012a0605070f0207171908040e10061b02130f09050102030a02030403031808041a090607060603120c11270a0c0801090c0f181d04060f051003 67
    0xc8103076031815810756a03014129403082d1001d400181c44010410003c0da01000082c01501d4020030f8100860f070051031190795047e045003800bc524076100048000c11413000d042e9000340220b03051907811403510504c4001056450710a00c4000740101d0b4091919030f1880310321600e003a40140c800300086000080110140c844100c0c1100b1556650040030040342c0e00b803000d980900d00e03001c40942e80c0d0a1901703006060f11082614034403079080202c10080018401021902120741d00c00c003c0c040c041d800d40b803a5805000d01401c0e160001400911101080140c2e07120700b007902c1c03003014000f00c08810841c0171280001c0c0340900074460140c40000403c503240038200c22400d020358429050041078143c4211040308026120195081d8680d100000380e6a0040135040c054a02c1c0001040034045000c0f0062000091940c1d22007440781d030b10388820080022903035070805003849024074418480099031080414408070381c01d40b03400745030110394400c0d59041d00510740100340e5030f400d015140d41182c845c20702031514 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 758521987 1250 758520737 758520797
    0xf06050306040219090c030f0509070e0f09071d07090807080717070506040803030910090209010e0402010e04230108070302062a010504060b01020c0a061e17010b0307110105010501 79
    0x382400005d83c4208900407181c00080c2d60360040343c0200148500404d8401c042c00d030321901d40049005000f420300313007129181e0182c9140741580d41070f1143d101c071a0408041e134100f0255411628095080c03058241080781c0568940d55078262155600d6540c05c3d1501114002c107905500003140c20071091086e0040700044190350800d48270069541c0d40010240e0340700e54071101c6540c0000c170400441a5003407140981c00055103009220342002d5038000380b84664140200394075039224001150959200701d050300300400000d8410045050540440a460401030941c642e800a2003400481d602d0400700f410000c0b668090702c3d89050603c9508035031103403210b1080d030010a0f452151091581c0d1400d0241070b01440c05107000103203d80001c7c000904041c840b030015406050003840401405622010801d0015906504112800a60082210406445056445150703003400c004030f11007040c58011401200e980c0c03a00d00000c1c42d0714401c207098038024401c0d18041081030804284d91703041350000300b1503545 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 758523237 1250 758521987 758522029
    0x90f07170c0915090a0b150a030b04090b011403030906072a060801090b01110607030b12030c013804020307050c0a0c0504111810090f03030f030f060503060402 70
    0x20361034000c602e140368100c821503202c40154125140070304010b092036800c100c40300340030f02005603090042510a6000308102d28034800005030440341500c41c1d8015100c07008024018050844a814000030703001c000c1c020000c6d508403000000c4030301c0c038000003110401900a401d042c00c0010750b0701c421050103501c08030000c21070700c2001140154a090110a805400103440c2c0c225194100030018040f07038501e00c807a9050004c5030700304184100d80001c0003680300f0302901d400714003202d0300008900d5500e81401c1c104d10511010880605203001034000003e2201d4010754001c5001100c60410205201d41a05480840c40307121200c0e0b0303600746074009591080e03407410721500d03040748401c4044c07600c1e40300c00044e20840610a0140304c41c0c0303018001d1000b48500c1c0f82e0080d05182178510b0388102046000c0c9854460b5002541500045004161402c003c00e24a04414000d50381c9060103800051100c3e01c2c603000030320b405803003e030440c0c8601c151000e8840150040800d55526400e1100c04540b20500b110010 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 758524487 1250 758523237 758523253
    0x2150408060c210a060807060504060e040c051605071715160e13050601200c040207020f191403010c080f0604060e0a0f0b060301030519150f090506090f0717 69
    0x3903100d140c07482c05510700840001361170745064001410300265421003001c000040200308106680103601c010f444204a81c00208040682400e4989208003250081c900341c500e07145206001e00800d5010460703c421344680c103103145014105480f402640c0040b680c40390444081008059158030340761120105007803031050003580340001001805e803c0742d400406e6850300e003001465640b000368100000d003484a40403012a50080301c3e901c070800c40d096203000b5540418140150350300c03461850008140903040e80a4810075607000c1c2034001040c0964400681a04042c0b46123003070521404c0d1448030a80d07076080c00c070303101e0400740c0c01d1001028040a50103921036034085440c648010310207010320415240000c0e01c8250051000c15034440e1950184038a40603c0100f000c20300214804040b0040b0004000c1122100d152440341d1006104425000c0c03890070000302000b400b40e601110f2098094400c40300c0350381d992100955110002c800c401d4154100d00400c022030300d00a8143c00146c1a130345c065601c08 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 758525737 1250 758524487 758524537
    0x60903081b0a12021c02060718050a0605030108071707140409050708070f08150a020306010908030403050606091503100b0604080a050303060a0e1308070f021c02150408060c 76
    0x841d040c1101511610551426402c3c2250100f2141c0d000c0c07114010082c01010741c5d100080c0d01e9500c020886007e00880032402444801c00b0054003001d4500148000351094480c440200340e40c100740103441042c0701780035000c94500505811800480551001840442e041141c04584484895001038001d510f0329181c0c80000c03014800380000e40f0003d4001d0120707524022503680844201ea010342c4640d042540c2c0032081e20620ba0405901440c4884050f81c0ca880c3d00004035050001d552010700f180c00082030101c100403020400900500c4112a42c0016031205070900e0046d41d04500e156626600100811031403000d107810004041c00010303e0b040c14a540e904909007801d42511085075150000002c0141038503040d01c240b0050405ca20700c85883d0b00e441c00c0b200010098203c0050601c98010400008103c1c003e501504001e90180c15021030f040341038148060f80c485034204910441032160b1b5000103d6007030b0261400c494040700244035985451108030000d500c520b400b40f9915103039201c180c0074 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 758526987 1250 758525737 758525743
    0xa08031912021b1b0619090e07020d0917060402010f1e170a05100605030901020f0406020c211e03160b0a0b0d0b011e18021c06060903081b 61
    0x60f074121a100b411a104680101509160006101e1640e0000003202d182060b01d5010681d146400246042c00ca003045002c015601c2c0c0403158020505d4041460030005d07020360125090220380c06ca80c44d03c07040e107911580c802c81000710450400300c46901240000f40076603c00e0b032203052014101e00700020b0703007440c3c01c10006880300c4035401c0c00c01144030154440900f80c4080c18142e80700380748013010045401e06000821240400d8070601042081c044081410300100394122046080050b460b01e950b26030343c4002035141c41a0407030302407050340034032410b401800b9804243c80700407034500040c10312610b81c01d154440140241680807240d02c8188241448121102a10408035008404002003440c0010344482564000e00741d56000d1443c91008000241d000e07116241502c101403080d0408800241d6041c210a00c2a441006400844542994103516903402030540c00d2800b11015070081407a900141540e100703104110005040c0081000801e0b1554050070700441d1451000031104a050030441c9 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 758528237 1250 758526987 758526997
    0x4061e03110f180f1c061b0816020a080a0c0f0203010507080402090108010b010e0d0302010f141008060c190c0b0a1d06070c0209090a08190e0a0803191202 68
    0x9100d000015082994031054003c00c1c40701804072096291041283d012a80c041101c4078840d01c5605140c0c00315003003101c0b907004101c0f02e4540c54020401206c0701e240052007007000344e49548106100036031001c100d505c0811800d500c160005011032a00c02115070499204508000580710403180511a00040c0d600380207143c018402c1da90342c1c1c0414102401040000501a485441942c4c502a00c0e0400c3c0c0e40c100f8036407a04048100c0c0c80034000030b803500b0160b01404442c0c2840b0701c414541001940340690004140b4000e011060341c0c1849a62901c9000d075681009403610407880c1070038469880103406a10700d03d4500c41262820310044a01d03a551401c2d00319040c0d0b8004401d50300c844451182c041c0f07002d205610305102100619075030500c1c10b005061520010300103400740140400144214104020f0036021903030007840a13640d2100750041c2c01d00000740301303802d0380080c0c0c81d900403501c00d10f803031150001a40c207401c010f5468a08065a10560710b00c0c81003d0405002d4a0705d4400020103503440644 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 758529487 1250 758528237 758528257
    0x15010e031209040506011d01050a0e0904050d03230c07081c0c1d21010e100203090f060f010e25050c0705040519090203032b1104061e0311 61
    0x1e5264000001008141d440040c246410428505002268101d61070754602d01d0704c4003801c00d60350382d441c3e0040885825041540e0b4a8010803084140401c001000440785410740082e40c082003205541c041d111f041558240040104942600100b8201d1718558000d008041c4165a80343c41e180c0612020200a0401109008200e40d91002880c81540010704101104401d91210440c3e924000c00910500c03444064110400100d665002c80360310254014202055154120b55000d000c0b0000500654811903940c04035009092140c4c480000004006015903a44001c03600340b40e0818803820f640c404000d198410781450440110f944c1006c10142c075007000c040b59502d5544020aa55182c50315249034000d038003480ca000c0401c0403004441c0c4001d1007000708000003140a00407400024a903010f61014044802881200b8981400341a80551255280c248003484442d025109108a0340110300c58100800c10048130900f050040403109410000d842c07c5c001105056000d1a00da1500310501b92 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 758530737 1250 758529487 758529523
    0xb030312042402030c04181118040f050105010906080405010213030c05010834020f0d0306150203030106020a0f14060103060608012412020d0b090106031e030815010e03 74
    0x20002e02c0b48010000d800e2090324000350f14500307000d11600c0c8548102e120300c500d412106000c0080d21401c43c1c22503900040d4541a103602d460b9140c0b030f00e0071000c1da1a00c0c8188142d01d0408940781d10a0940651390484105846e81007840f4a4040305545c0c060300240104c9281d50300f0814160404080704119000c2c0d401841c0004010782000c00160503040041c1031608035a009403200701192040078051501c5810715003100304a80e0000000364074112480941100c1c034002c03820182d80d0581c1c50340c041c81c1241e95060340403a00f503143c4c1c2c2d020b85e1684003c3c040c0b0001a0410207203400801c51005902d03000d01d1040003120b201c1a80c4030718171400c0c110203030811142d403921071008110311042401058420710301c8600c130108240350107006103075200b070034890003081000d0181100f007503564000701c0d00c41050700320740c0101c020b28140702854000c00260200310769000310300d008d0300709001c003920081c0e14643c0c0c5074403180310588941d1940c4140e013003e415003c1c1002441d107042d26080e1010300096940001c85818 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 758531987 1250 758530737 758530763
    0xb0703090e0702010b030a030f020f070806150a140d0f060e0f07090c090e0a060b0a02101803170c0906120105040e0c01020307030e0301020f1204051614040b03031204 73
    0x84a40e803481c01502d6442161305040c5a403000381c1d80403c104011950504001c4011104440b0590070000441070603402c9000c1c201c000203903c031005c0790b01c52043d0803c01c0340520341d6400c0303030070080035000f00d02908404108184104400d418805400d48a0754003410031101000e2480d610002600c030003200042413134110384800710030450b0402c8044c5c00f030b00040a041c007000c1261503000b40341a025100e041022404400803604004d01c81d4048009407221500480c0c0c3c6480d43c24020396103000604052804918090701c0c0e503d03080000d4446d00925a06079900120046481802c450018024004820300c640400000225549460040591241040710044658940b00c10231045406141d0b500386190440322840d40141e9000c0122440341d589410103200e00c0801c09c01080c02802045503803d100c91001030344140c2d41401e000d0b468400c9116a04550644010004805003100c4038030407103603007282d001e9a020340c501e080d03000542c62743c002034100e0b8242900c0c920044a0043c00340c506442d4001c0c071501d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 758533237 1250 758531987 758531999
    0x30305090c24162420070611070611040602060a021c0e101a04050a05011d0a110f04031b0f0b0f0d05040f020310090308060d0203030c0604060f06140d02190b070309 72
    0x40c948052013440300b000d88402ca20805c2c1d00e0603106144000b0040da41d00c4c110582006042e10641d0855504050104000103002e4507134402d030350050040202500c1860b0014201840038004c541d000d640454040c0c0d140081080700314040c0181c00c2c2211002d016414200071202e1091103514242a0701c00307860704009102200740300c222071000c0e0101c20114200300040c00903555182d0507110f10007640521146035074502510340014040548803985000c00040c0e1407400702c11600180c02900d010740c0008440406004101c145d021441c811280d448004441c10000300304450051314800c403541c0501450103045144490465904a130201c84013680c100d00d00056060801103501c0c0c10342c800d03008200b4440e03203440243c86100001c2040c0d20620384c4c480c801e01191024030030340d90800605821203920b4140340c82c011025045015503005c040d0301c0e1a00001380300ba000002c80e108104040c00c1072a24443c240c0034005420780302c10000b505402ca080f0001400c2e1482c1000b0301540340283d880f000d09506082d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 758534487 1250 758533237 758533241
    0xe042d110f0304140304090e06040c2705180109050304060e0102031c0906060506120402010e0303390d0809070509010510030903120603030305090c241624 68
    0x30040c1803040410301c00d0210420307111048076009a0410403591040c034030110000c1c554411500840641030070b010031a180c4d2200040c605000724411070503025804d440701c0e00d98060140c81c20141e02803c6003044505416205540a80d410154401c1200500d4481c84489402d441c51440d0866080d40001000c202d4142c2c00248441400000d2002e907103000ca070f41d80081c900307128000840175030f1503607034440e1410864150320000040c6009052030348c4942180281e8940400216401c1c0d0220300d003103512008a140200880e204001040c811a0300040c4e8182a19030280640c40c240500030340c105070718035251004100004013107100341d6500085280c50102c00d4107100d91580003501070000c0318010b1007640e6500141c5d0024044514000801d0040f034103003120420007071041100000e00d001004001d15a06400840c0310308111412291603c031402c0621682040b8160982d02039074402201089031019070000b08100118980c664203c195691910150b19130a01342c0c90711088940c002c1c0c0e1005850764 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 758535737 1250 758534487 758534501
    0x190e030601060816050a03020702090703200c0d0804060608060c07120f05040509060d02041a03012019020c030d081807080c0103020708040b0d05071d030703030e042d 73
    0x1460038070003504000460040000e0b48803104c1e001d01502142e10181c0700e2096055840351600205030311094108102c020307008010748601c414541d507403400d00b031280740104811100c254103040c0c014030100c0c50058044811a801400413103d0945a050020b1003107002c0004a00440d11039501d143d07900300e180b030714203413510200315400c0078807480f00c01c80c030310b100c1d000070a4504443d800c0d01e8040540d600d8000182a0380d0030158001d5100f0714151001c008100c208801c041110002e60003081501c1a4800d000100c15041c020b680a4100400618044104200308458081503c2c0101e0300300c0216280000d0070700c0507541e9050005220042080fa2940017444c0a0100c46695400b40407260f0410303055540742c4582c07064582c141600010300c142044054401c0358000c10110b096191101d2174440e0300f2019103c01d5584200240d0002030900b07605c10503103035140e80594010000e1904902d550340076070311900c0780703040c01d907000d990b90084068004540030110302e05440b000d80414902c0350505040100c4041c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 758536987 1250 758535737 758535749
    0x61605010c0906170a110d0f0b1c02060706090302030409020c0c0f010c32010f02091809030306040504111206011e0311041805030a0206010513180201030b0402190e030601 75
    0x54045a25030081c4c02407016400c04e04810011600541c50402000b0b684100068000c010749007004840d216407156001024012040f2158850001c4840314900b4001c00074801a5100204114070b10000302d139035001d10020381c40790041d01c0c01d143d681e140789030480c0c2103e06004019000700c2d40c414154504510400d420002c01d091006104480b41c8441d41d00b050a685e070300c09010010300407121944502640301e1501400c4d207009111451002d00340101a4000065042c0140c034199007403401315003403030300d59403291741d10340001c0d821540c0d58010003020380300c0903209a603c0c0d05007400c0d519071a15100b0300142003130390100c0100400d524100415062151150340300014204039141130000800901c40c1c000e0f01c0354120303400314100b50864020050340201c1c4034001e0241c44006035000019402266150403507100311924820a110300801d0b40c146c1d0b11484105005038020300020f0700540c040c1e4000c01000d000504010f0424400d400301d000e6508200c0c0c10b520200301f511740124607604e0704001140c05400 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 758538237 1250 758536987 758536997
    0x18081c05090a021009050303041832070516110a0501050c030d0e0c04020307020d03050c040f06030f0b030313050418030c0b0714030106081f0602071202061605010c0906 74
    0x20701924100e0710780c0d80b11600244242d0301c1c52a590300c468802c800710805444000d0580365a83d41d00c42e4a1094040d460225006d050300300703903040e11806c0240c1c415a4040c0718019500d00c90100082c0c4500e080341d070080c50385003804818480c0038117411403041006402489a4600d008581180d0f04101030f44400740c5c0300c103040080402109005100100503030300b074100ca455000c5130709840030343e078142841411003901d40c1091010003044010782d4005588040c45960b52000c004a440b10720f031482191007a070207500d007a0440f050003000550710030b50042006190f2503800141c1c000d00800080d00359400113080d80022404290248080c1c0303003038880c20751040880d0401072002e4410f03940140c4922400c510140006429800142890b4045d80d0b074042101c16600104d581e0390f845c0c15010304a5101600e036070030780580640001044105e007440040030b94026030001d140b074500e41806030107000d050510880e00404140310380ca03903c0707041541c00d501a40c425000443d40307084070034004007801c40c2c5c1d40c44481006 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 758539487 1250 758538237 758538241
    0x17070303090b090105160c1d09030406080901020706060906150e1011120706090c1502100b06040305030f0702040b030d050f2802070303080a020a051b0118081c05 71
    0xd400110320002c4441004610742c440720540010303103085c0151030074050001085100f00f401c020085d0480001d841c41850030b21901c035004503009509150883e0a201640d000300002c1c0f00031801116503690080704500091319011441d52800b00341d89003948070340d04d502e4803000c003070106080d8940c070080080814581002c10030119400a194140301d040c10300148000d60301400c032840030900008101002142c0c80603030700d604500d448001410310040a0b00c18a43d0607201061032850381021290300710b00e0340e0007098901c0c801c02c05040100b51245020794000c00801000000810a20240c5100b41c0701d1040346480788540d00512040d200c81030310052003500806c6510b54070fa5003104c01e888074943c00c440c444c0d403504004040c0c06160349244070214080000c8074182d800c0b0395400200c84003501e20030b42d42e0311001c0e111000c15005a014480072400820360034032175642a24004a68891521010000030849000007040502d0101c1c4016050311306c0e070b0340020402c21541c0d003030000c0b4404002c40d0f44100268 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 758540737 1250 758539487 758539493
    0x190e0a12150b01210207020f120708070b0a0215151e04060812030708150409081c020a0906110a1406090f03070c060c170307020d08090a020306162304170703 69
    0x10b04c000343c0d540641d0507030215580e81075407a480082201800083d1401216074100880181d85501d05c2c455002284501e0201180d2030440e803041d140900400e4004000c100c65802c42104602c200a10744201c034141024510859543c022560300482c000e06015050341c0000750611003620156002030507154400351680c0c0d5001c110300101ca52240311440d05016076101d400e14080008011220141e2050a0004001c24402c50a0060000300f81848003800061405501e078000d03030107000301c240c0204003158410030a40b0301960081c2e452042e20030a42d54088450f50f40c00d0041c81402150101550183c0104240180200070040e41c10140c40004c41c10400e4984d134100344054070b40101c1c406c1100300400d90b401c000a50300c0c40501d000c90841003584038034141c2030007550b030304003c5496000500c01380c02007807543c1070204100f9000e98028000c0e0941e56a00710540a84c6820300014504024010800e80450981c02202860860049410303070340d00c41c40c10620007007080c47c60b0441c0803183c118000400c00 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 758541987 1250 758540737 758540777
    0x220e040506040b100f0b0301150801031502070f02030708152412010228090b03090c0d0c090c02070612151a0c061e01060203190e0a12150b01 62
    0x8080d610a40482c0c144c0d850400c12803004100d41c1c020481032580034008950f4801c0003001c4c6043c0d0302c07a4a01ca02620102003003c6502e44028400505a001d4648515040c403100390020f000c81405a11950044d40041d030100b40f500803141e00100d0b00750030200c158011104413075034194004170044a070a0f0001c1100c101710001802d1500300500c506280c4a92500c608402c0d0140c4840e071208a01c40111421031a54481500031440e64442c0012551040410800661381c00d60b0b024040c60001808460303e40010300a8a54044800355000c030a07200f00025605500d0051441d401c3c01c0d9405004840e152500150411000380201d005890a18034003c6d2108150440070080b00c0d0b200f0f071002c50a20020341d840341c41d4421781c0405034007030184204200e00f0b03c3c1e680d5028241208074015070310603a0303a684d004076100d016561152030f0300741110042e0701c80741d4460781d800429030b40010318007010256540e8400e06070500710b00f400c44100000c0b14018510300c0180c0304200d80302a0038200030000c4d01e054511008 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 758543237 1250 758541987 758541991
    0xe04020306070c0305040e0709030b0405060114010318060c0e130f1401060e0906063f0702060c0306040b0d0b040b0106110c2107030c080c01050f0409020a030b0303220e040506 77
    0x2007c440100040c0c06030b4482e942500003150041c84400f082c0c1006d04026494010034024040700c003442241841803035110384145013240030420030f20440940e8680d560f4000c2c103034261040c8208580000310581941c0d40000e04111242c410b4000a1096101c1e1071000a54904901c92500304ea40d44004000307654210007600c0d203204080359128019505c1c0400140c43e40203107a03617030103000d103202c800c40c02d12010321041c21545c5203120901b20700e1341094401c228008004649110040c0c2000d070200300602180303c05142c01c49001000420340040e0040402e042c0136551009452001340d40c4240320030710411300c50a84c09011703030b450104450521031003010768510039544903078050b81113141400311940120003202284e003400426183c1190b03482c10111402c1c0c50a00a4141d40c0c01a218207100d198011822101200b4880c0200c509040c0303060144402508500101d40525071204003140495a0070f00050885401c081005040b24002c0a81e07107001510315005400090318400501005c600d0000b0402c0d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 758544487 1250 758543237 758543249
    0x100b06040501110a051c02060105030622080f0a050702010305090a0b16020f0607020c09150a050d02060717040f0501021203040803060a0e0702010507030b01020303070c1403070206040e04020306070c030504 90
    0xc4040f42d0703280700b191515082c60b0026280e405014030b2160064132030390382c0089903030082d821a0300d00c0c2d80309e204040d00c5d110180c40000c664200034819407401d8114610700c9400798014010b0724288003800c039601d81c2c6079104145090020380f00159007801c640e054820130360880300610040c0301c4c85441e50740c2c1c404407803c05001c41e505034442c0311760000c20610070456460544411410345409040600c00a540c84042050052080c034641c0001340b500003200340d1403082c12400a03e44e00e5441c1c501024003258000e05402682c009004000000114804160003d8440d60360115283c0d01c92031301e01c45d1110b442c01e90b0071060454024412959101c480042507a4200360008003981e0f0320380b01e0400041060b00e0b0340e40242d01048a0030b0401060b590190300031481000d41e518144415503401c8012078481c03104445c2003000c00e49486207500800c1d4402650352011051204580c078180b8250006241c81d003050348444166030a0100308021402c0c184203103038004210307003000c0f180d1040550b03005d049070240d80030b12 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 758545737 1250 758544487 758544497
    0xf0b120c031902040e430302121312020d09210c270b100809011d0106080c150409020f270406060e01050a05030a11040e0108100b06040501 61
    0x3040b0361401c0100700c0386201c00c452900319a225641d040f01d8070750f52800c4840040d804001840c00d600c00b00c4540420703045461100411540c2909010301e803020a42188003c3c080681c24441907868590240c0c18a010b030b550007003011044085407030411015400d00c450041150800d0303d00e040f40d550854000310507150080c050316070360026404200d0190306882805404281c900174002081031404034025801d51034030540481e0342038016004000e1343d9a880019400c0301c181c4045038080c500c1107a040d900515540004101450000c2030043c2992950480d81c3d880c0c0d41d200d1041010950400c2801c8035003405603403040c04511031003102407040c00740d480740e0307054150001480d401380040c540845050003014048018110301203561100900244040c080c000ca25000010601d1805010a0012070205a41c2c4a1402450030001c880c1c1b034002600c154051a22620307201d541d400b80401501c0139117081c1d08083c5c2d03190b00d401c40e8035180c45003e81d400403d8901e041207a98982e20341d00c0440707064400a00302 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 758546987 1250 758545737 758545741
    0xc041112061302032a0a05040302060306210f1c0206130609080a03020702030c0f090a090c08030301060f0207060e0604030f02010e121b030c0a0e04240203010f0b120c03 74
    0x2040c40b4120184003816154400020003c3c80c06801c0d101d0051a40c50b04078004c0a9105d0f1402c04245101e0351117040003180c0144810401441c0000081d41e210502514800f0b00e4183e2407051b43c03000c0e0114000703900c1030b04607400725044c0781010444a41c0c20307180780408070650000040d010b03450b12400b510445e03855440b950001c060160303c3c2c0181c100e01e036204802590300c0012441c000c0080d008180128441d00805440c4613980c81c017017071521000000100702d03541d140c403260070500060000c28021150045074203400218000148095402420281c461041031142048000c0c1021001d03000b00003030100a841e002c01c0380c3c5a26095800752548190703810b280c50b8050005035040710720780d138070b580d80408010080010b10102190750442018a100880701c02803d180401d0b80300c0900801c019000b40c4131610800100070b000d600b05401a001c8c41358420840304844001c20080c000413850640c0a4001004000b070801d42c2d070720b6800030501d00354a10b003002c01001c40b006190b180a000b0400c2401c0c0440 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 758548237 1250 758546987 758546989
    0x1112070804031106011806050108071430060f0d08070210170a0b03010b030c15030a1b0201061a04031a190204090b09010e04210509090403110c04111206 67
    0x1100d100c0c1e090000f000c84d400b960313458200e04103c02c05041c00b283d8980c180807000520307500840200d8043d486540360a40c1c0700044041c111415000200d07401400791041101d02c10030061056009901040a40624407a140100501482c00740280009010b845422101800701c1d00100a0300c04003581120342a8009405c44421220300d240c02000000c0c5036001003d00c80b41c92103942c0700100e07404c0244d00901c42c052147c010143c03a60001001560045001e500156890511200456120b83c0071314000950785030607202000120400e07a1a800542c2d0b41d4941400420502c030036110344000030074031052419095a45e0000180c00b441c501c0e070040d400c5440030452000e07400501c040d4504400c00115140d90b95040c3e08000b800d4070707215484c000c0c1c8003a800071823400718040704d585c441c3c0e8000b501d05a00100520948002c0d041108004040050071310135a01c0f1695003041c21406540240d554409070150000094101100c119030345200e00d142602c4100418202802c1c3e84060081e07000880f480da488030 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 758549487 1250 758548237 758548247
    0x305090a050d03080a0903231b030a0f12060b07080301230d0305090a08190605010f0311010c0602040504060902070b0a27080d090b07180e062809060603111207080403 73
    0x10760240d2440b62240c000f0452548c1501900c40c814441040d054403c4110300c00b42c3c1c40307100f8003034410f0016101e0005031120b64041c070b842002d002d0724202c000940c41d40d03504a801690300040d0040340c2000e400001004600c4040100304505881070b50201c40301c078a000f0028244c20b41991000b01030020102e0810300507610b2848131001060801c0c2070364010b0208400e20380104a42e003004440162500001080650812000d44140d84c0d210440030201c61100c0e005603410130900c5001c6850a408000100e113030344440c010300300149624080941c40b4401442c1c48001804001c0c4507805881c41c008505808205521801d813024201518185040c0c0c0c2901702000b49206407500650301c0c5082049142c20040042001449402143e66605250113100081c600d1140c00d4458149020210008a03400e8a480c41500c0c03070b24140302d00b28044000300503418084c1001c0b030703a0121880c180d80f200100301584e058020351000d02d080e4115585401211190b641c032078640901540b0400240c1030006003018018 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 758550737 1250 758549487 758549507
    0x7060806181914090607051c09030207030303060b07032a17030402120604051b01030603050a050f010c0302040807030b040525150f0f0f0e0d0305090a050d03080a0903 73
    0x40044816603181902180d0b52600c401d4445003066454080940340d14242e464010f406520380d50080c103156120b540d811511604081c3e450301104643c805102d104e0500d42c840c01000303078402e4000c0d080b01803070760601508648a6510541c0051420040000040d511076003d030303418a49900381c980000b80480c091948088a00c0000b0300c010700e6030025107110110900070314882c40c82129205c0701c0307110240615480702010742e001007a0b9800701251110b58001d410141c2805081890002641943d9880b550702e4103c01d242e05684580082c2000c1c12a01b10a02600f2050449401d040d49050314265903241d03110220303c00601000940004503042290500c0f4403050100942000d403a180007407202c43c95050142d116500845e1520385090f180765004010080c0503022646074000c40010844081e9032003064041450100103035090700c00c0c0181c0d42e666092981c05d00a42d242ca480c2c0000b07909210030340c40b1981026111304400241e89000980c88039425500c20783d4a00041800230451070306484440301 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 758551987 1250 758550737 758550769
    0x1303030b0303160b01090b03030304062a030f0c08070c020f03070f150905010f0f0c030908100e0f030c0703080a14040e06040b09060108060f0303040b1201060f050c07060806 76
    0x350399031402800c20000e03d42c0d501500d4400303216680c59010801711081d8051a54140d003060001402065943c0e205040004810301a9551a0344a603602c086558043d0728003804699104060403030308201d4450112140c0d400d08004685090501010740105070203140244100a01c07529403901c2d03202800640d001703000d0b9400100c88103464140c0710b9040c0c1e032001700005c00503050060009141d0700c925020743c610b00098550820030207917140c00b02d0303292040b030006505119000300c2c002a945402c00030101801c80f420400030b1401c00c0799134081d007000f0700010707900c641754021310800c0b00084001c43e4100841f1380c00440d46941ea00f0380c5509a4a030344240400e43d00c007801c04100003800704464231030346100e48012075080107803000c18000c00c00929815641140041c480310001812418004031000b0821401001c41e0b04280c0d41d00c9100d5556802005140c074640182001000341035040f52080825000c103042140c10180816251350b81c902042c801d40c0100886d0303001107249511070041e107001540c8 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 758553237 1250 758551987 758551993
    0x120203070201020a120506090604022d0a0906020703050d110a0c030506100914060f01050d020d0c0f1403060103020f0903030a021509070f05040b180403081f0e1303030b03 75
    0x191400340a4000c0d04101c54030b0340401e10811001c0a80101071140f1172003840d0042c0f50090503100d00c07092200a412040d019620f11300e84d00f03011294003600c41c110041c01c003806c0c1c60b4966030700c11412000f400003803554407000039544407100a0000a5001c51101420400da00c0c1c440d0b00000300450492502e181c04901904440101c5008801c0c490003140700b511903501015072014207650754054000311126810507415082d20f09001c14128682041c0049803004140751007070901d1410398140c4200d030f0042c02c81c040c900d0754a51912004a810940c40c4c0c3c0c2c03860302c506000a030010012200b440501c4002d04c030f113041560001c1c2d486590284c4a044d07900001001e821139494035556400a561107505204580756803800400180707071f503c00018100240c5480c91803410750340b80341c801404080c04043c62159800070711019031205025400403000d2041c1e009a139490043e0405c6001100c03200c85800c0e82c0b000d004550b50041c03044100728038400b6006008407854a5564003d0700b01100100306000c15640d00d80 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 758554487 1250 758553237 758553241
    0x21218120a0309060b090103050a0f15060b07020f0405070210090503210f01091b032a170a2c07080f012003060f010c0c05030102040b1b010b03120a120203 68
    0x140c0c2c5039024080c031a204c1d800c1001491480010041004c03000d101c010300652007004541c0c0011281c1100307201d034510419000b51903541107000c40382590342c250041450940d000c00e0700019483c10f0750780006460030941c0c3c10085800c0c05d1400945031003c2a001c1c8544035290030055041110400484544268000b140c4160561140382e4a450340c6050740d013400802210000402c2c0030385184922040181244000e40c084903508405030007030900e6100314003d046a08800000e110705c01d49a68a600000d5550040381d0a19071451981c40d60024040654242c900140322846152401148000c51038035003000c40881d40c400305403440d11410360803840d61401041c0482c0d4243c081504000e00740400d0309001900748090881406450004480d400d41c0080507042d02030f825405501b0034801103004074402d02041d82c5070400310313081e64095032202181c0c4000103021007140105c110340d1550400b19900900c8401600c5000aa59a00c5c0342e490503289400022856003c070301401c120702161148803030035902d80c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 758555737 1250 758554487 758554507
    0x603020f1027080d080108250f0b0c070603021219180605060307080102030411040b12010915050a0209030d0e0301020d1b080702030423060702041d1002121812 70
    0x501c11500c01d0203c107103d00a0105410b03402a550130f4140c48090004000280c48200700c4088070080c2d00d0a892403114a0102244039a0110011070113020187c540c0c41c0e65030703495100d0303a140c007800d80e0210b000c052061010100102c244105035410162044042884003002042d020041c10442040f054101c259507c1c0810405541c0103913204160860030b071440580d0340e00c02c0d28240e1004448c0103040f00c502103450880e505c0c00b0741c401c03000104041c014032140c0e0003504a003800c5900008064511404034100220071107003d010310340d40103842450079800d02c01c403240401d640c0c007000f031180e10030b000140346020101d8a0950513188031480c0004c0c10710201a001c101082e171103c0c601000700020300c000001943c0180000b044404075108850f5210010840400300403d948409444a9002c0d00422107503002d82c5d40d0b405000c0c00c21010050592044071420a00792820039010866464640148a12107a04201d440035a030700200c01c8140d141240c895030312003030a01e090345a81e0791000b038001c82c120b0a8 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 758556987 1250 758555737 758555807
    0xf0e011b060b100f081f0f08011a0604050130021602130c0221191d09070f08040812160e01031a0d0302070e0108010207150603020f10 59
    0x4050140e50051915180301d00440c0d8004540030100041030701c103070100d020580b440d804403241b10381c05c29544181c43e4544291382d41040c1c55500c00d0358180e4540401040c043c01c002c1990001403012544d03d441c0929244c0043d00502d0031903220101c9400581e6100300461444034031680701085440215a0b1300100307105d001348000c64070001da0255a4120140b540c80480b42708000c0d022480350020140c6001042000c400240041c0107030f0b1441c8014401c0e00b54482040c681d1030060002512190940c2c1040480030b01803400c4038290354480c0058000b0300004c50780001d49900842007510705002a99140d0806102d0361003102804074120391111b00b000001c0e5085000e00e14040099075a4995140ca0200110251000c000e105c0c1c010204000204d2650b2405900050045100780140e400b81e564512910424403400d9010044617500090320301d04000d62004040040ca00c424000c1092a09640128100d4407070210303c0f900510341d01d240044582e00030491002c0e544140c008140d141e40b030108403071207 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 758558237 1250 758556987 758557001
    0x20c01110c0f0c190b07050a020402041401110105041e08120a140c0f0f071e0308010611030c07171f0b1815090615030a050f0f01060f0e011b06 63
    0xd43c09020741c0f4484500d00040800413558400010110301820401c0d4a5055809618101d03420301c903040c001d02c0141c0303440c006000100030b10082502881c002030000341002c4001011000e181e40340004220000f610140c81d2001d807201506000e504021615001c0c446110b180704000580e0700100401126540e2a0401c808100741a00780c1022501c0c0c07508218540d00070780130020312104050104a044410101c06400c03a60b001c2c60982074482c0740844a600c1a46003010254005109540140709903900301e5242e45410b0741d1140218a0080884510343e00d80c001401426003222078030032027100201c006c11991903003c49560030300c0d1038640710b202404001c044a41d4914090012234001000309807a814000e441840d01700d450450960362141008602c00000780f501c0e501100f905401c401540b0712a014600c00c407010700c00098281400c402c2d15900010043c0658510380050006109a513400b00349602d0710038045c1408001c181c0c03000010384040301104644004415850055810b115160700021 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 758559487 1250 758558237 758558263
    0x6050a050124020303010e04020109050603040b06090c0c0703023a050c0906010512040501061701051e0c1c140712060501080c07020915040905070608010b1c020c01110c 74
    0x40100945200d44095910062180b00c0c09a081800100042c00c03051000d2588a44140342c10039019480c1c900045064001380d50655200c100c020811000342002d403001764000480c41582da007880d0110b0750403590b03180c2c46d004c024050291190302c824429a050540074205005500382803888400e4644003000414050007541c03148140311030607400e410605500340c010701c41170b9030b4580380140340c007610784686d00060001c680341e40d03807800006003600700f04103004e54128440001203110300700003c2c0d0607550340b10940c644012080c402c040c4000c40d444081140d00a1403090b00240d5140340405010000b0325110004030342e40c800039410882007641c0329036250105280c404d800c1210648550045030481e030120392541e000641005064054648000825070040010071100308001e1348602103001e4038440c220840c0c40794003400080c000e0540040400e80502000c1d015282840d0000b18954222a600609020780c19070000d510300134828290401140441d0071020a43e0720b2113422501546d84004903260 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 758560737 1250 758559487 758559509
    0x3010c0c050d1419020703080a020d14040b040e2214010e0d050d0b121005190b010e0d060e120a09050102010501050d110a0f0801050121120e0d06050a0501 68
    0x341000070300640d00d83d09240c85600740c050a00d0b0b07110310614601020b840c3c03c1c2082d845041c0c1c00000086101c0000c140c10314a5a01511001c1070b1300b8000390891110f1610a80c140304203000c18041101c0301000d4070304503110300d20001c115880b1110402e40c0103012100e42140c0d410b0881300e220038041a945d19040c146507000c02004044100c18000ba115490041c000001520421070183c4c0301e41d80d5001105040c5004014a800c425100700040c5800074001594004c07540714004c214a1508150101503030461030441480764200c07000008000c0741a080720a880f98124040041c10b014803540030550401ca442c040b1754a010030516007a4460308400501c400140c444003000c0307000d510602501d41245c3e00a0b10049600001d9914403100f100c01a8109030400c030010710000c1d241404402c0707200100540d000008182d4100015401140300d404096a0480d462110700c80000303035601c3e40d1829121491a0111041c0c1c01e600010f0842e032803001015103240e0500044c0a4560401d03030116040301e02c2040d003 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 758561987 1250 758560737 758560753
    0xf0a08070e030d0807051315020f071809080906071b09090c090c020f060709140d03050315220204050a0609030b0103082a0c0901090e0d0c0206070203010c0c05 70
    0x12a01c101c000c12800e6010740010494400d0301c0d0148040c1c40c0c0101e07807400c02c9414402d0001c01c0d8901c40f1240d611a0840c24107900515051030307010b01900c10032061000140928604004455005a500469084000baa10a284401d0180e0003064600014000300f600d6601c040c641000303643e456400d0b50b001c0c000c0010400000700f0180300e100d0205542d51080300e0390001c6250054400041100d00b6604041d8061031090410440040c4011403043c0b4850b240c0c0140b9a00b0106443c14031001c50b002c0c58002c400c0020840042238005042d268030181102618110300031a0000ca04030441c1002400c81d03507018180241c001c400c56801030000e0310800d481031480d1690307941084400e0180c0344400352414240b00018004615140001c010a004888840891035420188002c9041c0c81e4031032112260000750340d02e00c0b0b40c98102001c0d40100034500b410302860314100d400c5921000c23200f10712030500112090450454a0389001d9800b159001002080454070410020f041b45030b6603102140c65000d0000f03 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 758563237 1250 758561987 758562001
    0x203030126100612062403150603140d120204051309170a090e06180c0703020c03100218040e100f0b120105061c050703030c050307170a0219170702150f0a08 69
    0x16001c0003002c803e86519031b407891034603010200741c1c0c3c96031403255154a511000c40031178052107442c806030074004010001900c03688001040c0f80b032801002c0c4442801080204500d0751203124000c0c0060300500300180d0390540f45003c4503a105140c2c3d062920340c1004c41c01d54501740e00706605000319410034814007440e07580c0c1c104201c100d440940141035120004004035101801c1440508095803080c0119034001002100186c07a00c1003880007140116000a801e5483c00f100b40e0410070100760503101803003140c585201080d11407004441c04c0101030342e107403101030170307000141c001c0210078070041c1208800c0e0005a400314040c000480b4114010031a4190f404002c15040081c0981d030368012002d0404242141c1c1d04a510801140e000e031814481401080082100c4456425a007128092426a16a003e101c040d00b8080e5050381020220203010380701000c40c020304000c3d101c4070600718102c0c0e07a40650744001143c040b41d015902c444c001010801700f0022030140000c0038040e07000d80300c4000d285d984d40 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 758564487 1250 758563237 758563271
    0x9141c020a080d02030c0c03030103060f0b01030e15070509060f0904060605041202091008240117070306022a0102090a14032e18020907020303012610061206 69
    0x140005024407010440f045010140e9805183c01290001d1110305d02030101d04001d145400c01e0b00705440040e41e440d4201c08052040c45100a2a074084c282072040d82e1070300506680310300c1a2992021031040344800102c0d041d100702c1c01c40c1d80c1000000d100302e0305d50360100d0100344140c01004515010f14a4100e02013107050054040d502242c4680d80300c510402c1540d8280907102d540a000c1c82640000f007440407940141c2400303625080108024030640c040d02d03070300d642800d40e00103a1001003007441ea040f084146000c0071459030f042d81c3d00500007517030b541e030000411a0302e036955030940380002e010141e01100110040d0020b22400f40704132a02d02c00130ba00c0d0541c01042100c0c03c031186274154411800b0003484841c00c511800c154021940701195087c807074820f9402d60300c003c10303a0701a814403d50110f04520f0301120194001d40c0a1000390f040d9810081b800d2540d00f400c4542840f01c4401c181c00010b020f00c02c011240d20224001c50903c0802d940e851a000216244141112990304008004500c01846 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 758565737 1250 758564487 758564503
    0x1e090604060e060405090a09061d0a080714030c0f01060801020f07030309020a0b0f07061112061908010f060e180d1d0a0b2709010b0a0309141c02 64
    0x5118a1425203060000d480445140400342c0e0005824030002071181d0303501103110b00c229001407021a910425280030340071100c0c40600800b1034400f401e03500d8615100042c101c500e4070307404007070700c0e50703c01d043e040c03d1115040320070b046005448000342580b24013001040c1d80ca0360700c40c8000248011502c480140f8281c1c0540b00d11980c0c0080144003030008a4440c4e0411880140040c2c40035540607203d414141d40c5512040340c02400a500085000410031984900f0010600c2c0071051350414035040c92800c05108041c181601c103100030b034040e5804101da4000b03d001046014001c1284c40d1440005001802c0140305030700b2555548800140801c110b02030241d54003c200c0060809034403007060694004003e540315003041c40c03624070b280185448891401001d0011421029150502048043c107030b0300003c80c0402055280c01081250b80c1c0b1060500760640d00c0c0381c3e140c203498101a0744114009d01030a04040c1800750090020010101d000c80d03240609032100940380c07100c099282b000d036994071007 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 758566987 1250 758565737 758565739
    0x304120824010305041104060308190206010b09120f0105070206010f0509090607031823070b12071b0506070c02030c04110f0703031b090e0f040b0f1012081e09 70
    0x44070300403041d50311942c4800d0b80b00344640e076204105000403003c64100e0750340c0c0e0000c4a40400006000c00b41d05103101e1050301d011550700c0201000d41c1130060401d401d01900e4141c500030740c250380351180c1c125414080d244001030120001c0049190500009542e8942031080c0904403014034030105080c00d001861900c183e01c0c14000704810344407910300314010240702c00b081680203030320810300700024034141040e0600544c101002c411021021052420401c0c190302c0010205010003241c0d01c000d81c91880d140d8000e0303032400c0400d8600382510366101c9070203034075400600d01d0081c1c5c03040150f80e0b40c0040a03060300da8000e504461580c4005420f12040b11a00c1c94122850403042c800c2007140c101200080c51098468980412600010b080708000020207058001c0814075141d0709004c0c24501102071035000c42c07a020000500d007001c2c0ca1f413440c1c51201030181f210507070140d0000388a0b01540c00e00c0c4001400d41c00003420401703000d0f0901041c2ca402502c0c0c54804038401180c1c5100850881c4140c82c00258 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 758568237 1250 758566987 758567041
    0x321040e0709030b0610110307060204170105010510031808041d0601081302210105010807090e15040b060a050901170c0301020a0918091704090f0c140d020f03041208 73
    0x1700e541c100020030702c2038461002002000c0c00941450802803018140c1e0701d02c0303064050f8481e8204203036080a40444160504c9513031401004200554030860f07503c0ca054401e040001fa084440788a83c031005034211006010f003100020002101e00000b41010884541030400c0240b81c0c80c1c090045500c49402d031068580308800ba0070880143c0751445501541c03031b501c034068642c0909060225820f40c3c609070300043ca00d42081000700709450180c0900b00700b820518018010500482241c00303501c075009400078280340507000004056450700c00442c0b01074140205031844a60f946d140340700b024500c00d0700c103c03014051546020181e0a0500903103410a1054890400c003d042c100d140350307460013100000c00029102c40c01e050120b103095181181400003015003564035810f002020040c4c40c0a19404142c1500c0c1c280208030f01c592002c041d43c4c40c401050700b20755807003107441030045c0039000301d01c4401e070041d100000384010482c03c4250f44001d003079940c135952101c2d910303848514900b20720302003203000c448 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 758569487 1250 758568237 758568241
    0x21070b1614010519110c0a0305030405061503120a030e0a060b01031404050606060c120c0604171305150c0708060403080f07090504111603093602090321040e0709030b 73
    0x1034040c0c00c100d1000c0005c42c0d109050103407803800c451500f00c13402c205038040b0f0000014042800713014001540d0054110460403100c15080700030a6680381040d503411141600464040003c501c84d406c00540107051504861640c0c81c01d091100060021a00d954046850300c42c1100e00b02a03941180340c070a030b8000d006003025990b400c0501440d40d100d0b4902d07210302e000e603103038031192244414090015080000001e00e603030702c7c0c40d20304442200030703154181104038420302c154440100b044200e6420748109598103003c0c0c851111441285000755a8040c004d4082c200c1c005c14038100001d201c43c800ca0107551a04129118104403c0034940e00382e0352a4000fa5542c0b17400d0015082542240b411500c3e80003000340381034148101c108a41074805d004600080c681d6a0800200c41a0220000748040803603001e0302c850310080c1800200d60604620560703054020510344100e41d800d0100460201070b10ba42060351340c07244c507400616a8454007031038202c413205202280305c0b58032880303040003070f40e074003030169541c503 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 758570737 1250 758569487 758569531
    0x3070b0f030a06030b010f080c0402030f040321020708090f04020910030b18010e070e0306070903020f0d12081008011a13060306060605090406080c21070b16140105 72
    0x107640300402900001e41c849000100284844004074000e2100a0350071485034140130340039040990084185100303500501c148020345842d81d9101d60496858100410740541c00e05505282c1d6101000c80d4100c1d510228851082c040404014400d1a50441e412254909540104012030180a900941048400341040e00490181e81304a1a61000604034003040703a02c0c1361a410882d03001d030421190150707058240b0401c00d400c0032008907800002c401824182c50412001007041015100117403082c00741f442000c1d240c1c0c544440c0c55000e44d81000250343c074000c0b0340300058000716054400b420000404a4000703808107041c8030740302c1c85200100e5034522040c6400c0030083d2482d002c02840381c2c0982e03030b40d0000001650320b01c01c02c001000651a107c2d182c00d1400300300f208880b40c07a07205600e940c01c001c141c1d0300c1550f42ca82103920f0b00112810a4403080c0103900059140c68016080b07031800d2400060211520224500d1822003180316040192580c07004404030b0f0300361007040d9010621b85034044400011 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 758571987 1250 758570737 758570767
    0x312080c040f0b070308060a030b19020f03070305040218010303080c0306030c0d030306091d07050108072c0a060f210b03030d050609060d0f29180c03070b 68
    0x805494403255050589422404403a20100d91000e0b03580c4200041c0c181c10182c016040301d40c4000c0440300450303498515180c0107041d0300003c01113180703058800e40000e102d81d50369040d0f4104109012110352a03103804d040160050800f6a000c4c1c7c440e40e8580100003030003180104c0a81640d0b40b59403800780c152200c0048001e0f6402c081c0c10540c1c1805000310b062884d4440030038512482c0c0c001e036000310709a861300d2010b400f241c1120030030004510f2011000858440002030341c40c2201c10a2038100e05541d240402124100034031411103002409404003008030415501c070880e411a411101540459581d0340150780c0d007041805400f0102c0d013190046c02040082c6140c04409510015022420003256400a811035100c14280540542c1d00c00520001e81054200d20307a019005481510304220181c60302145071444041c01003c0a52004060606050726101a030f00c00c40c24003100001800c00c031401400c4601600d0b8000200d2003180002c21440c500002c40804659040104504d025880824004 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 758573237 1250 758571987 758571991
    0x1106130609080c030a0f03110705060619050303040914070e030c090601020708010c02010e120403031b0204111b15330a120b1006080a1d1b01080907031208 68
    0x44030b182c148021460305505200400c400f81d065582d001080c03200300d201030202c0c0c1c0c05800da00c83d860340500010300000d50000c1c0b03594010100302c55040c401072040000141c03a00036a000035400d4040410000340d9448642c00441c4440281c81c14030b01180d44819086604100c41407005031700d075116801c0e0207100c3c00c1005629401c1501032040d1202103855480c02c0d070a4800794400500140c0d903070104218040c1d010701c60f204465540b0b115051400c3d203036031001056640784040c6588000c0d55101703c0740c110341c1c9a42c0708204030303a1203c100d65151110680c1e0000c480000516050641c018413a612a00308590300d502d034410b4010700800d0960103030211203510780246d101c43d201420b58200e000d0b01500c2e9281c05101d00240f1400da07110090721414a42001c2d410030161849050f00c400e01020720081d42c00403241c039844a4001070001d040c901e01001e07009103c058110080c0c0300d0242c0400c010035001ca141c643d1410781c0c4283ca61514507222401c50700d03510010362001800400c40710b80314642c1e040c800c5940715 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 758574487 1250 758573237 758573243
    0x10140f0408160602220f1d0901230708102d0801060b1c0b0d020d0302010b10110111070b040f0302071806030309080c0f012703060c1106130609 63
    0x70b201c0195070760004990000c421001160f034401c8072400c8988164103030b071010f0040b005020100500d0b05a04071806003080c8039103800308110100203240c000c000d5106a078100000c040030700d01c06203400000c602c100d0741911400001481d040c0000c0310001102180340451340c100340d07000b18840450410b40c0381800d4103d044119078070000f0001412030b0090103003c0240928104140c0e44010718080700c1e2818802c000f13085251810010202507a9558040e4001181d4065440781c0000c007084c0380480c0102001140d00d0340c4862031502c0e02034559400003030310340161202d0008114018484003182494021080300800c00260480000d000902002214550502c6030040340c81a50320b401d030204400b50b0301c030304545040d50390b60310030400e00d039106101074020a29140070340040c0003000c01150321500c05440b10307418407010140c1c81c0c08400c1d9110344100c0520386561b806800c07945038540700d0040c050004041e000911580b01c604030700c51010030340350300800304070030020034001095031198060400b415040d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 758575737 1250 758574487 758574517
    0x120f02011a1c0212010e060601020703030c0209190203090607020f210c07030b040803060901060f0f030e030906040609030b0601180909020307030614160206063001060810140f0408 79
    0x284005031a80c00d07544c40c02e03101d59400850b03080c10280b000e92903d0001040141194014802003000c2178020280e40c02c40354040d075019001c0c0c1d40d06880c0c4401c0070914069804544d100100b002511036001c18a0740c0245410750a51f02505100d448096540c40d26078502c00d9661250302d40444207012038070090450321034031400c2c0c840407a626181c000c0703442d008131025104c51600000300f000510f0110011070261540341481c9145800b4100011322081401c000907040c140c0c2c90384840c2130984100282e500c000c2d8004c1440e55240c1e04c80c000284202050b2000300c800628400104040750b005600c0b011411101d502c0301d0902e10318100b00280500466281a03825000b001c1010000c500316004801c10021040b055100e103042c055801e282c05030206210008642180007880116561080b0300802080303402e602e000c8049522011140c4e0510003003405145600e042400100c0c128003041c40000740d42900420804043c142071740840c1c09000300d0313180302071141100c0040d00065146002e8540e04209000c8 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 758576987 1250 758575737 758575789
    0x906030705040e03040306050a1b0c0f0507140a0801021e1606050103030c120e1e0f060c010912020c030c09070507200411070c151b120f02011a 63
    0xc10112048900143d680d600009000d1007031001c0307030099607085078181c0c4003007000c1d03c01c1640703070603100d0744c14060314041000392a1003005020700958401251a0804180c038640c039690350748070341c890780210041c82c001c8442c10741c0002c2c0b00e881842942c1180c4201c0a41403020a020a0741011541c00000c1410a81c1216545c40e40850380910481d8040c49c420380b1050442000750804812034580960035108000000d51400782d242c0715014051030140462100189040c0c10000180d900713040030b044c00350843c5010031100c0800c413054008070001130082c407140446c1040385104a0702c030b5541a007104d0705544a91a20f0900f41080012940d0081880c90036a050020580d200b0751a1f00495000040c01440728820340034500d083e106591099020350f1070703a464042d0030750300c4d000065071610804e18030212007245007050314044c07120800586222820115031041030310342050101c100411a00000d40701083c1c1341201750051295501e46281c0c101c5014400b11445c040115951003c42c0402098954101c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 758578237 1250 758576987 758576989
    0xe0d0803010605092107030b1003061b0e010207080c0108220c05010e0f011d06040e0f0f0f0c1b0f0f1f0b0904030806040b0d3207050906030705 63
    0x400303107000e402d03203990b410340d2080c0d0b01080104400905c08031000500d180e00070b102540ca0300186660441c1d912018403ca695a550070b14240800940d0000e0012030410300e140704c0e5400c8d5024520001c070026210041c800e03250300012030796801d0600a0340482c1d805590405d0703545d03000344941648401140201710703141c195001070500c000f0007842c0031030b0781d400c180ca820700c89507070072030701d2080001c406441c1340760b42d220444002081000b0900000007200710599008916440d1442194080d003032452410109080400c809020700c02c08442d100640401c1101241c0800b030644c3c061401403c5000c00310741001c1d05102c4a8900b6522400031152a10072000e03d014800c2c0c0620040794a00c808001400581044c01201502c3d0b6080890424006140209001166a0301d048064200e90545402078031071b658100400e00901d450001142e03c0702d07650714420100b11208401420b04040b0b607410b04010910442d4502c0d00506000d0f0648003074010010030f2080d824080e0909900c50002801c880082c0d03501c01c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 758579487 1250 758578237 758578253
    0xa080705180603032502040f050c07200a03080705060f06060906031024020f0304060c121704061b0c1104180204020706050921040e2d090d031406010e0d 67
    0x10325802c3c20030b1942803004d00b9890507201d88c0302e1219010b0300600151410007100b8005128554004014056000307454038460340000c0d40070f50184001d094000403940b2410030007612303000342408545070722402001403d811a0b40b076400f405120040d00d0f16050221120402016402c01000343e2040e90f0300000001d5180d550a1540805400580954210a074041070080c00c02a0b0460006001d50040004014140e407103940146216081188018200485082100c840510980c0b48aa030200346041c0000c0c00640d0b8408080354030380c00e42c620100450b000007600c41c1c02904101816200160007010090300f040d030000403103007055400f180403111300c0e40d000a04a8000c1501625856a98410804940e20402c812983e6180e140c0d0011408800720854501c0c9105e01d005c3c101d0354440b03c5000c030768040c254200d9072042072400d04036540c903540b13840d168451070101158a07404030300c030360b508030b0148501030310441c08010075110346803d1a07500d00d001524586071804103aa0800e03c02000d4001156841d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 758580737 1250 758579487 758579527
    0xa03050904090f0203060c090102010f09020f010810090203071701050f010815030705060d091e0b01031509021305041b03170f1903090c0509010810050402061308010b0a08070518060303 81
    0x4c441d1b242e15188e44400090844604461f40140c1d02d281c450307401c0c0543c1d55224002d103903a4092920314440d80d40d400002800309255803040a03124000700030720120039085000160703000c031008508442e03a030b030706c0f0200150114040c54450104181001081c02d0243c801c01d002604103014086812055481c004039415910002034010507607900c0c0b9580c0100010903071901441c0304010260940c0038072648505485c0d184c180701c004c203484075000000d000e4030315540203414a1a0010900c200e0384014550708000741808a8080314400e04c81d11080440c00c00032007001c01965008460340b5811030b05060302c4000c0707500541031200c04180510403103600c0700049000d10300803d004d96001c1480807892801140e0110035070000ba11450000c40188100351300010384074041c8414400c04102910b450010078864401e00344001090003044030041070700c110542002c040312100742c422281940e075500d035041d16001a8020726a024052014040601c24107920a41c0c01032001026240707405590300880601300c0745 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 758581987 1250 758580737 758580751
    0xd06020c0a081b06071b030306031502030a0b060301060219080f040305030a1d062a06010605090109050f010813080408010504150c1728050a15080a03050904090f020306 74
    0x1c0c60110380c880282d03008206031403c40140703185c3c10701c881c0141100c0c144c88880c0c0c5581410031180018940300350040c0d40259000664807505005101010000e0750040341c5c1400c1840c14940510303030070b040ca607040300d0480e0550fa014202185101c88011140b10382c510381501c40b0341041c0012034540302c0100013880118440e034025545d80042ca40c0240480040908501150821001c0000d0a440b544229084144803040c19860300f61440380ca404c4001e49100e400c80d0364804c500012a0454000c4010b00e0411800d0301e802480c1a980c0c4c04000580038124420360000e036003200031840c49120260b01901315486409500d044ca6119000304e4211901240c09485d03480a901d81e000c081e035050310070704d413406c1c0d040d10b00482c00805252a45d0268040540318058844c02403000030140070306008601c2140318202c00500031410450341c0d03100600780a84072401c02c0305030702c10001011900081d80e80c1c04290b064170b030141000100d1781000024040e10109441c00d06440c082000107a0302400000d00c2251 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 758583237 1250 758581987 758582003
    0x60f14090a060e18040206070b060301020706330305030d181506061407020d020105161406072d031d0f15150105040504050405030c07031109070512060d06020c0a 71
    0x120f0f8100300300b403890801c851040451040720a01c40582c9800f000c455190381c212080c44074a072945004a40240b298131406040140350240c141d11814104160710707600d0781c80c0384105812583c20b41150401548a11008105a00801406001c20201e4009810a000000d40714503402c1c0a0345034000c8000c0c1c0018500116551200103228185d0003400070f2203955484101c0505044c60341d070125031140d2170a0b101134144040826000448007515034041812070707000c0307101412070743c0c5981c04568030700080d60008042100e0180074040c885c240f1a000407003030381c04803d441001d5940e400540003491030702c0880018245440b405800d8800c100100005606804010982841640c00d07044015102400480760b0b010001c0010516a9010058030b082c0d0350122400110303a1103903d0010b1462040c2f0036007001c01d000d0214008248001c1802407480c2810540e6180001d6071400b800302c4007031080c2d544030008142504045480b6042c201040c8040510a000c01440c5c03a80380402c1e20325200c02080d0480e0b181c9 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 758584487 1250 758583237 758583257
    0x5042304090b0711120301030203150603010f230a180b060609040501031a2508180a0b04140610061808011a03010f0b011b05010b040f0c0216060f14090a06 68
    0x4c80e04021100b10210b421140a04550440e80000c1c4c07203030858022581c108000c5000b1800680d800c0d4403101100180d00c50401c00c40e02802041006d000007c0c010540e020b044d80c001504982480c00703071852155121034448506c40b001e540b40a41c480c00545419004a000d20481c10f841c1c407503201d81c03400b96014603080f401e6101c4441301e8180748580101007a2001c00d00c44252158101210031551a10074541020001541d0320010000c4070030304000865464820041c40300280b0220001850041d80503074054100110b91480c2c02c1c1c1d0b103201c1a520700c0c15072840c01104000c006c0c41003030620700000101d01680b00140c3d6805100b030030349045005214041500110081003440c0074428000c0540d6488000d001005000002078084500900190030480d211065081040000e60240b42c501500400030010340458103103c2c1c0041c03101030400350142c0308038440b080b100401c0c441c08104072082641c401c404940503a0040b0303140146403400c00c040407002d1011b90700a40c4c0c0d81030040064056503480941031 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 758585737 1250 758584487 758584517
    0xc0302030c0a03080d240308030609130b0c07020118062006040b0c1612021e030c0601180b04050408070203010c05180f1201090b061005042304090b07 66
    0x501e0914103a1041c03035050810000a24000d00b42c40b00208118000500300e2280d0407107140c40b26010300e14003010001041d0100400050304e001c0c50181c00155501c09499a4502022141400409010b0111140640003c0102c042000180304c00380c41071501c1e40050000f41d1340d005c6029043e42001020455a00201c003440d808401403006200182e8010005410903031101185000003038401c007014040003d10098440440483c009100d60012070f0320140180400025211846001c0c03d000c44160f45a8120304842d000090f40c800b24401e401070b008903403038002042d041c4482c2060a180881e242c0c1004100c5a403584a668802c0e4007c450040e65500140b04150031104098041000c1c08010b001e000c01101106840c611048403d484041e9280d01a10000d842c007111070001d00c110b5820200e00e0340411109900043c000d00c410764201e100255052001e55250086014030045030391f1400140c1405103030b400b641d100341c18000d40001117461031074803542c400d407008652200c003295080082d0041 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 758586987 1250 758585737 758585743
    0x604110316030c1812020f030f01050f1302010f030b130204140f100c122d020d030501050112051306020307021c020c011403070201060906060e03060603073b040c030203 74
    0x8810440c0c6440000d681c20700351001354450250280290f0413640c0342c1214115180c2caa418040035034000d041703c100880c4600e009028000441c0c03c8210a40400d02007a610070084841c07605090b416100e0001081c40590101c1c0100034010300c06274000488210b03001c00c01050f00c005c0c0050300080b2860300383c1869001c1405000c030201c200c0c55000f00f9084d280c038660182d001000e440c506900c0826494040c003001d804941000c078980000030350100312103000380320285207546002d4004080e000c0d2140d010103035100703604486003441001d010407440b407800b89010341254403082e800040c2c2032090045100a4071441c040749c000320b42d1240542d0210114038900000048801030307001503407008144070001003000a21404840d8100b6803034002c0480494403550003904900e000c0c02c141001000450b40d2610011b00200641c1e0125001c0e010f80c0001c2001403c000c00d07100c05403040702c5041d10b450320700100608a01c8060a4000d08000c900f0075076040a000d42440b005e000e00e000b1440c140009095004040c2 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 758588237 1250 758586987 758587001
    0x406050603090a0f0302100c082a09010f020f0a081b070b0d050c19180e09060c070503040b0d1d0316080c0c0306010306050103050105060607150203060411031603 71
    0x11180c0c0c41031003003180076480059a804502e40c0611000003441c110318040e846c0c038003001026400035043c13440000034250711042c80c0f403040c000c5100300b042e9001c02c0e00c02100c07070003100001c008010710708114040e0719502403201540800b026204403440112110a214141141040101c6518200095040200064900304e0b404000c1000141500c5441c0903800c00c0c581c450040e2000616450300d0015030310404aa081e1071010503004801c0c010314000c0740c801042c002c0c5d10600c110510740360003404079100e86030640303072849201854001d0050740c03034502d003a00d0140c008c0303403088401d40710401002c1083c103090406000c4124480d1404101c1e40e14006400408107809000305000d03078814404800c0c482d200016000c0030b141c0102d0704a0360f449540708400d0810031003109054040c4500b030000802c02c07040d9030040e8100c80c0904002c200315140eaa0030043c0c0351103507810192482441b00c001100f00200d6500442d0420401000014101140c000a0b0642d07081280c0b000c5a0302641d00104200c3c0d81c240c01015 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 758589487 1250 758588237 758588239
    0x30a0b15190602030304020f06120a090204050705070b0112020411040905090706051213152a090f090c09050d12090b041d190e0703050c0108041a061914040605 70
    0x41c0345203080490095503804000c102920846c1e10360008007a0380c07241021070301940708025502c44680742845080c80688024071040303002d5884c020004010500c41c100303488195034014081c0003943d00e8007820701d101c0340d038000301070340d10a031788a02015003803111000801c011b0504501c0803546203007001c00c1d2818440b00e94085400d1040410800384040c40c148043c5a100301540c464014514540c1441d00a1070070761410401010320f8a540c180003040c0f00c40740001d040091030345174150002806822a0301078902d105039200011040c3e018460090340d40c0010282505610b084000155900e0019800001c207020a0b900148100307208102d20354030044050103400070701405807038203217040d800084a5615050786841c000080c004940382d10003500c0d510310320080e002014080e000664428a03280c1909100854142c815011904115402048800d200e550400c407400143c0110601d001c20300d4500070315007a8450003102020000c15200c0070b100c005440c00e0a520904c2100c0c000078007007242d0f0b81c1c0e0026 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 758590737 1250 758589487 758589529
    0x6130c060f09060809010e0601060e1e090402090a09050105070c0501050f0f0a0b01092d0608130605180d0504090b04020408100209060f0f0d05060d0f060b030a0b15 72
    0x140859030b8018030700304200c2e000361810100035a500300d5407138010700703401240036011300501000140040d0301c14864281032008942803089485446a00101e4044031000c41d41c011040e040020054546018000e902403c01080031400d0026a40d406007140c83c225400c2006c1132401d400e40b020f1000c2440b03000d50010b1000041e00c01800d1820900600343e4000b1300210322030b1341340c080030191a441106241e00902c0c0d48846003805140d200c040400b440c02d00c200c0c41003941400c00300021602d2143c900303940030704001803494181c11400d131654405000c00400c1600c80280b5240d2921903c4000c002149983d0792a95030715850b00c0c1030400074030030b43c1e01580d006032240e0300502007030045a401189088240601c3e03440141d03207034941d20200346180500010004101d00100d2102c1d003022454005040807206a1020456591007404004400a2881c800740c941100400c0210005026900c403440346030009007200c0b8080720315511031800344400c941009100b88207078414215410030812420002000c8440c1d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 758591987 1250 758590737 758590757
    0x70f0503070e0907030e030d02040314071401031104051206041407260705120102040e0c030c090906150a0507050d08060607030e0a03080a0201090b07110a0f020f0306130c06 76
    0x4024070154404550b07601c1104440003148000303000e58816002540c4050070f82e0f446564031040c010081d00540b000750751050007211320a00c01040424281e040d84c10784038101d90824607803401140103000254109202440c1004040b5603984d0f00c649a00b142c04803040202442d15061410030340c0700e540d00c8440562580a140240315400460311062401c1c400040c1e143c0c09030400c922040c4c07410381c0c6903102c00d41044042d03846040404c4190028001c5d03801d8513001036056110101040b0785031000b10758120420005205840807460580d058940245000308681c4904441000940c121f5000f131136014040745001030400108802407107000065170060603c080c0c0c03450b000000c1078071481041030050400c9070b01e00e03807e01e80e641c49486880c003440c0c0203841d054594403900c401900078030b01c5e194103450405018000070180391040b00d8110b4078106400151900320720981d602d02060190880c120f0740b01c200b000e801412a01c08201c090300c5004285e100b00c101046508100d0213004140e04a0800c101e04490 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 758593237 1250 758591987 758592001
    0xa0504111e040e010f0f06140a03090302070503011503061a1008100806071110090809120a06050405010203070801061d15160804170f102c0303070f0503 67
    0x300751a07411020442081c0401d40e2955000c50714400c9400290b81860a400041451040c405441094640c1c144080090a84403401a03070b00311002c030141c04202208100b640d141901c00e420210f0700d248640100d0740c1d6140c075040020300b910b04400c1000f0400a06c00740400c20701c03055000d064000000003036690308005070b200100e05d500d0702a0010317006025a01000c00c0e81c5c8841c056010005221074401d882e65800c00e202d0007456440350405440b0785228041c1c9810703101000b8803403200031a81c802c0340c6e145008890030600c20115800c01c10504180550010b42000c50380c68012103120700c1c494000142d4a25041c0c5010b448284103800071000c00410300c090140102500d4406020036a0031030b610001402e00e040c0409085c40707180b600b12400d0420703520382820018000064802e40f1030301949042d1414812700c0c51070341e58418041d44031841d031040d054001000207039030020004445a5050481100841c4540c00f01c1b100400d0030032980794000420841102d0b48400079440400345807501c5461402c000f4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 758594487 1250 758593237 758593271
    0xc030304030302091c0b0601120c0e090c0d0203011205060702070f0b370806060a0c08090307050d14100501080303240a08210403050607050c011d06060a0504 69
    0x3032004060542c002107040403640c4180e01541c4200ca4000b643e80703074241c0740c074003180850010b58007140030035402180381051507003c0c003c542091803255104070900c06408104030050074064035450840f0b03400c00460b0452101c500045001e00700240021131000940e103002c624050300240781808541192000b88641024624101c0c102d03145501c0540c3c036620300e1051100780e020b02d40c0000822081003602c0b07049603803519280e1707100341b5281c0d2242c901c556510700c01d024403442021200300002e030a01d0150f03c0080c0c00c10b0040c05400a01404450020752500041002416028810f5030029001c002e4000707941d40c03c0011100204050a09000ca9450002d031103940e400040d210100403201d01008801e80e194140311a0216100100203442180d42d41051030b4030b6883e030180b001c0000f8061a504138000d80c0803000c9400316a40b010080505644040c1c0c01c0700d45c0e03000401c8106095403500901c0d014940385904484a42212070090070303131428880100100025264400c0f40514200306400e804100e02c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 758595737 1250 758594487 758594491
    0x20c1b13020f031305010605040507080412110c01030905070b07051f0c0e0f03150a0f06080313031205040815150103110f13050d031e2a020607052e020c0303 69
    0x1e09604c258a81c0c0c900d840c602401d810f4000700d800c945448101700075181c0c03207c1c0082c00307140958059200703181c0c03134a4120f98440c028442c034442076100d85600c0c0825442035229240c814014400e0315003581d01c580890425520002c1c06070345170350000c0540301d966001019502460031000c401040305044080014090b80800c401d16441001600e50898641d2400d219495150310711140141951070301c000b690005281a2550840d40c510f008808940b098000080b00c2e88000148403100c80540303969520300e401c0811480075030403c401800b0000703825404200f00103001850b041e64a041d0b142c469403442d441c14000740114100350501c052143c14807850030450b512080a40f054070303524280707010320b1a4910038a03800146c100d0341101c0b03d0710502d503108000110002c3c0100341e0742c0181505400071169084990501c0c0030f5a1405490181e9041840240c210740c0c2d44080c02103810700e642c43c0c40d0981886100c46012522024a6004034266000c03411710084007107541c2e000b181040302c0c03003c24603528000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 758596987 1250 758595737 758595751
    0x506031e0d0522093e030705070b0c07030e030a240b1306030c17070905220c0501020601081614010c170d180803040f0303020c1b13020f03 61
    0x69804410120711003c00d1048440c0c0c442804190f5140002c00007007000600ea0980c00462102100f1070b580d034800c1c0c08400301302c4182d40c0209042000509519036002404140600804000c80400074022605840c030a014070100c0366120041c0b810058030011070340319558400d400c140059000611032203190701e40e20320f40350141c00b070308903804040c24020040000b8860b1b2052142c0840d00041e0010703084a01a81d104004500007030f513841801c02d01d071003483c40c0105103c1c0c1000c80140b1030440d02da480950f00000806000b256080b844100d0107185032842020307551141c01708000d00a41d601002201d006101355002840c1d0410700c0d00d0321100c0c414050241c0c01681c0300d413590644041e88a13a0740300824941214095050007400100d22150354050711a003034141d42454408040040219014601c06800c080704030300e5540d40303940d64101d1030007044c011002d0560030301c401e1088000070003644180d42c80c10b1402caa41d10051b0000c11407440410145e04e440f890041103884e8a0003e80c405403a04031034 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 758598237 1250 758596987 758596997
    0x30d0906081501092111010c020132071109090610062303100f06090302180714040b040314010b0f01140d110703120908030601051b01050a0506031e0d 66
    0x41200041398098a0755100000200204500c0f00c0120000b00b1034084d0300d4030408540603028510401075441074a400700c06804103901c02e60401c4000c8080403071000f200d803905900341140d15045244045a000a0300c2500c804201084c0b0441a04140d500302d0f410016000c01001d580c6010090b55030b602e1200c0c0507400400100c8140700d210070440391a0000c4058044c81d0a54903440d01a485689502d554440c4c0d14000e40e45046c0061880e0181204a007660f4000d8010490304500f414000b032510006045182041000011080d60381103440140000c1d02c4051051903540c0c1c0b460404103008600c40142800d81d0b40746c60001205955044590001218282844142000450003440313032030041540c40d070038903410030401e8a00b020840d001000018444c2e100c9400080c0f0f00504d4078202c170940480105690b4040011480035801000644030a401c40c030500b03003a0b101d2a2110070300303603481034a0510b50642c4030014840c280c0f5041c4040180c215080800f40010b0b514000703019a00c4001c905270f8403c2c40 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 758599487 1250 758598237 758598271
    0x20609040b0f060711190b040611100c12060603050c071e0821090d1d0f060c03070c0b0c03030403080a06090507020d09140d02040e01061a09030d090608 67
    0x2445070040203000c614002d200586600320380c00e049040000d84174209114105205505e43d95469440e06501500d070007403000342c00c041c20724505681010030080403a00c144101c0c0c040481c4800d25000314101c4c0072035655103071441c04120425900b560702c030b41c101600b41403c042c00c1080a003818400d842d80720303400059800301d50442600109082110b10710150094800054490088000ca0011040b660000b1100b0110356030709000c007074a82c2240401d080c00588204250003021500f40301480000800812041c406140200010701980c402c400036a11900085820000d024207090440c0c000d104000680303107412180ea001c15100d1000500040a1140402c00702c2e4000401d40c3c44680038208000d010082810444000703540e9005801c0d441c0c0c002116010003080543d002003942c1c0342260701400011081c00300da42040060900400264115940c983d000540d814501d84850104000704120558501a10050505000c100340e021814050380342c404000490b0f201040f1640254140003202e880 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 758600737 1250 758599487 758599489
    0xb120c06090a030c080a03080601050315042721020304360f140a0b030c090405240a1103061804050106080607050903060109050c040308030711060a020910020a020609040b 75
    0x6480c80d08042c0c0200b50f00500170a5440c000644818098040d8407800407664451004480b10b21044844841c009001d81c081c60f0710f42400d4014045052225007011404000d1101d0458480403001c41075032400641030080c100e00b00504c1c1c44004d042a1480a103240a0401142201c084181e003c5247c1c451710310f001c040b1030418000e02c180300100e14510309114000d2441c4941e40681306a40b44440085400004a0b6680000f03100346e41c1a004003401403d80044103200300a8010002030064550780688504003503040070b00141c880c82d9070341c0c0f0003c10360942450307003000040342d08415462100b11030070824007190b6035843c000d007814941360980040095603185490f03130260020390301c00c41d0a48550014860340a03086000740c01c0c0020140c00f11966aa6100064016618150b8150640b0041080188007181b081c10040d41e2005040c1448078000b0060070030709180050880f01c16102c0d40e4007280d40c244034034003840d840d00041801d2004040e4202c4c141c002603118440d140c840c512880e62040c80c0c1d211 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 758601987 1250 758600737 758600749
    0x709140124050c1006140a08060106050c010b1906021504030206010e07021504240204050607080a17100302040518060c16020402040306050105040509030414011d0303070609060b120c0609 82
    0x11083d2810242e0ba101201c51300c00d0700143c8981c0c06010030f00c1122401a2001307042a503403000071181031200420700d81e480d0260540c5c0a60210018982da5500d07070002842544230500711014200281035268880c0c0c0c5044002805c0203468800d150320814500140000f20358006820b505641d12000c144550b5110050300340d02c1d0089030780071990901412030800080c028114070903c0018241c1419462081a40090504a10546c05055444813050089001081d03610001d015000c000e070800f00e038000d10b80740e0031080b00c0300111038800b001c01c2c103d2014021410035009403900400d00801121445489011b103688450700103100d505034007c00301e4065940d003462214000d01c0e540151045541e55100e04081018080c00d000e2a4003450424001c10031260000049508694000099442c110b0500b0011a04030301e207940c500100c140124065011507505100800040e4840e8100107989006840d006040d6502d04980c284902d220500b00888600041625041c2140880700c80c3da89140000c00110 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 758603237 1250 758601987 758601997
    0x11040e10080a0b0f06181806060a060903060b010302040503031b120406020c12010f0e030c0c090403050d0f110309030a201e010f050702030a030b040c0c060903031d070914012405 78
    0x1d541c4281b0050040066000c2d006076603154004080d1030302035850b607080c04015161403240d2000038010b0002007020406a501c400c44210b41494007518059545000034a10b4200807032400a43c0e6141340020075296007040720000340760760350b1131060415250000194440c443e4004042c080d020494403000310a100b0340c4816006101400208800c403410f40e4040e0b0790f038003d370094243c9440741d50311060240c684000400e00c126456900e862a000003140324402816000020310b11980d102c40540105420ba10081c3d4407401301c0c0340040d0f8888003d89030042c00740701c110144007a2040b00c1c0c51000c1010102084400100c5589500850a080c2c012541c90041c040f4080d2941164600300030702c1802c42d40480240404041564140301540301c117404c020803614814080c0022400c00000c010004220390000340b191170280c01c0000e82c298039001030b840300346c203c80c0c0c500446030030940e42405842e40b5445040841e200a00d58002c0660500e001c44000c1c1501080b4107400880c8400200744079440394048070 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 758604487 1250 758603237 758603269
    0xc03010c020c2403061507020901181a061b190f140d051c0905060c0c0d0215070810170703060c0e1e01020111040e10080a0b0f06 57
    0x40100e403500c000940710300d060103185100b42c0d03c030018100c0e1403080c61502001081086045451615080100300074510302c4002d06080031401d008500143c1d5620140500a201c40f911512801011707101070700441d84841c0c500c1c160980303d2220103055482d20010303a20003c12640c1090001c5d12b20007080d62900302211301119420000010480030400c04104d13084440d44a103c40403040085054519191050700000d00000b079014480361681d1045040c074412030000c8081c0008440c1003d0302c4203414a40300709d885000d2000d00142000185c00c08001604803031203103201a04030030b50440e443da064044080c0c000307405c22031400e02048102d1a4407c0580007050711061a00c0c000c0540540161230b40d0b071380d110543c1c40300e10b40519640040d008100c0406913580040041002207054600c009900c100380911504665845001c5200d51100030002e10242001c4d1a40c610549880c030101c0e607205103950070003036180c0c124000007400510b4020845401120380c141c660302960b580740200d55902600c051003 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 758605737 1250 758604487 758604491
    0x101104030506270703050622080a020115050a26031306080f1303050304060c0909090c08070602031c0f11030c090108060a32031507020601140906040e0c0301 69
    0x809004072051031100396445010b07491210b000f0003210300307580300c00700e81c44060196040b080020700c1d01d40440201380c0b404540d070703500f02c8142011925000703110382064502601503035540890080d0b0f600302c8408900102000c4520903502c6060100249480a00d5501a000a49840100c006c05d81c003c0c800d81e141d6030703600c0401104680e51000c00500704803056030024050a11180030039860301e440241c40c6041c03a05511818510740710b40d50b84100078203080c94001d00300440064007141d00e840a0140c140714600035900c0b0f5140038144504141024290f0b0310500030b552042002036603030100d012403000c2e030786030384080010603004080a11028110b4200c42c070720414400010403440505c4403010305041700c402c1c0d8880c05281d44850501141d000a8001c2050101d18440203108240c4030038482404c0600d00080105080c40c400301191600842d44440c014003e5504100010f103681041180c0c010101ca00b500c0304100d0482c00490341c5d00c2000341a407806142c5604120401080410059100010203002 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 758606987 1250 758605737 758605741
    0x3020c03040801020723031e0306040f060b07060e0f0703170405040632130c02070305060f1609060c030c0515010b1801030b0a26070612051602101104030506 69
    0x4000d031510b03031b0845000c91200107141020340c0b210000064038541047d131413070050813054801e41c00606410040c6040d500641380c24442c4080c90460258030010480000520b4542c182da10388107058400e1084c07016180d038803400558406d0f076400198402180d4200104804141d50090b0b805014840c0d6000103070008e00346680010100300d00f00c40c031040c903d800300ca11070202c242d80150b96280e041c4160801d90001900070070307401a0440d07a05c43d40d1200080c0c0101c2720015582d91740c1074100302d41200c00040f810b210804100c803450302d190f03400c4440c4c496841c1440c0c0003414050043c1080e8107c80e000b5040022400700300080050170040246100400c071503030b40181d0795880315a05c640c0d1000240034110142e50045030b2039540240a07080c1140340060062108600304034070540701502c80002d015142c44900107415190b4401e10441c0040c0045503180c104800b201e08810058600291904c107001d0002c00900e44416400714a242020080c50b101080440d1090a4600103000d80e0308040d001d4003500c0c2c2 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 758608237 1250 758606987 758606993
    0x1137061505011101050402180c09121e070b030708041416080d0e09010b090f10080406052d063601050109300b070c111e0103020c030408010207 63
    0x140800c55909980f01c41c6992401c1c990242a10001d4030029044401705080e880c140820a40c850303800300c4100c403200d0410303e14000040002d080c03400070700071540041c40303260011a83c8a04449003100f481c4020a00c16203001f00c20b90079440010440c03010040c0708000721381007104000c0c410700c19002c110200c0341c50040c0c0e0100c00c3c80340e001c1480744000c0340c8107640d120a5541e01940d07e4003d4204010602e510301c0e0f207000c0321540c40c0d0340580c0c003095004001e0512220250303034003010141140c18a41d01c01002e81380c03614045040f03480c06050124211110010246489003802072036810903c110b05e5440c1c3c0d03845040109003280008021407180080048200c507905840340d8410301490f9003001c01c515a641d8900040d19480518001c8120000818103440c03001500041c00340d007001c461001081054200e40c0b5814a41007041d01c824000070381c120420001c2c0559a04070001d01c1c1000c0300c0c070740c040c000b541b020440001c0b4041100d5050540100f602c0180c8201417060302c00508a00000303541d2942286 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 758609487 1250 758608237 758608271
    0x110304020913151103071d010f0c26040e0f15060a09030206040b071a311a06040b030c1c02030f0601060f110109080706050c1b0607113706 61
    0x4480200085a03e0000c40002c0000c920020b4008810786901c607181d0b091000484009070b107450305075490241007581109010712085003142c1d0142108585072902e00b05050501e640e1005000000c0902103b41800760480c003c000f800f020070012650b031903491007440d8080d9810000f60340065070201001ca40002c00d15070b41e00041c1031030b46c40351480017403d4403080c42c41c003000001626003488561903181818042c2c199044c2100c0b84c0d500742c4164030900b02140e56030380074118a41c1c2c28a10b01948100c10300000c1c0c142401003000c100c0c012005048070000040110f00c050404241d8840410f612583c3c82007952070600c070613051002c0781d906a03451582c60f040003030a0400b00520880c0052a030000c8e80e0340d007070301c188100b00800b507101d0621442d10350140c4807134014100c080c005170494602000b003880300c1a0b60812a260340f50740c60740034044178035161002622007217528030020019001051011100650075101d060358061201462200c80561311034000c501c03400c1e050017004a46400303500d03102e0728581 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 758610737 1250 758609487 758609491
    0xb040e010e070f030b0c031810020901030e0d08041e0503070f0308011226040b07030206090d05070b1801020c0a0b0105090703060303210b060f030406110304020913151103 75
    0x40458030b8080e6105200d6071505010312000e003080240c1400f02c1c801d9481c600045411181007a100d01e4040840010541050102c0092000003a4009200101c0d075070540204ca00660358040500001c041182014107040e0001b0300043c00d511050384084d542d00c2101d40c0d100a0550404100c0e070302c801003483c0200340381d550701c481640840d4141000207001440e04810710300882d4001c030010b0016506695820301c151031441100300511b02070101103182040d0b80e020309074890190340240314505010340842e0805401401c4902005004c028007030108131071410781da80024031105402c400c074113880303096070090280d203c440300c46000f201615414400d0030300740b8a041e11421141c01c615038482c5071007901141c0e1188001004524115a690102c41041c00716014903040789801081075418040041c555078000720400500b02804001e0005000c00b6108400404220381000b40c5141482d800080c40b0501c02085407200d03030a80c0032040108002020380710204039044000b40600c840c0c050101007180c0007 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 758611987 1250 758610737 758610761
    0x1908040f05030d12020706110705010c081005060a050c010b0a0806010609050907080f0601120509010c0816051c14040305190e150c0f150702190b0f06040b040e01 71
    0xd415804125071801107802d60302102c1c140c131000c2c1c640c0389921504010b500454401d560ba16503c809011012507c10024180140301d1000040c0ba200194009001094064640d0b00c414008a10030301c101d4540d1401c55010000700c1c100240c403442c03180421400340200340c0c2000d40040354141c4c000307070340c0900140c01030581d0100d40f031781b94105889a0601c00c2110045036610000780d0404041001c4494015003260003010614017018503400b2070046405a410984201207169500c0b00d40340a110f600a140366000003170341c141840c042c00000d000410a00600c0e040c42e0365080d4a4000c244903040c5644403030801c41c0000c01601d51880c0900b000f038803940002092804000c08030b013182403a1441110b00c5d152014006181c2459805140d0340c1c0441c1c0e4106411030040b0b4411101c5802c10018100401d01500f80c82c24102005440c021800a00380440b01940000301100c0617060700008411490403940b00c82e0200182e401690303540005070191101690303071500245020a130040702d25041d01f0113003a401d0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 758613237 1250 758611987 758612009
    0x5120d240e01150504050607140f2a091b04170c040c170a0b0607020301050103140d171605072a050f03070b0705010e061003030f111b03190804 63
    0x3e6102e50036014800311581031400a003040000344120710f843c1002d800e40134000c0d15603540044c0c00f0b04c240ca00d84070210390644c06641c40f200c0c41500021107041c0c0c2e0000d240d0240c0d11240100030304004940c8110010703090794468043c0310030880495400d50151001031400314440d801000b1a00505500d0b04003490216000f2030400c0c1409813800d0040300c13000040e6801c5c0d4140320095544a01c900c0c0145500c8024603171194042000d44056036003401118080d600595413402d41ca099006038a00d330800c1601d03288180b110f40d42e6455007440e22500d0b180d030311070f05107014040b95404000c0d045416100b400002000c3d030b80c540040c01c2031000c0d030400001c01c0c1602c441e0b0181c20309456808100c158046003244951650040c107003401010009000382030060303c144008541501d0080405003059002c88080229204e0084d04100385640a50f29801c031880314108408004030280a4070f4031041d0395a16054502c001012150894904104104010380c0e81c030180702d200c3d0a1403030002c3c9158024415045520 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 758614487 1250 758613237 758613239
    0x3060203011e05030c10032c0106120203070e06031006150201050702070b090f0d0512210f220b10081002030903040608190207030e0103140405120d240e01 68
    0x214440e40700b1003601c500400905002c00641c042100c5404141203a10805845100044800c0701240c002c007217030a845290240700c15048951a030840d02d8980c0500040c2c2a072003808005030300d0205001c0305031114682031444a59482001c04d14101480d03099042c0c1d40d1504800141c10084030f0000750100603164000c2c483c1c1c3d100d80d1400c03607076007000f800749440402041180c00801c0c40c01c2e5204000c1134002903c00100d011381d0792140c0c0c0c1040c2d0364141410001c5000208400d00c0d1804101c071a02840c5030140310000d03801c00b6101030700340780c10003010300d80ca01c000511480020881c07100d80000035980110204003511b886441e0301000400307846610920300c94541c404000030018000d4910803801c5800075030900d0b24048040300d001ca0064007000c03580255005018003500c5500040c402540213440320a800b0710148001402c40d003054040e000820411802d2000041011400d4070000d80300d81d500b00d881d8003021750100002d10180c010345180c0c10540d03420804804941c49100308407054034030803440903 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 758615737 1250 758614487 758614529
    0xa03030605180402130e0106090606020313120b04020603130605070f1403010e1605040315090218090c060a0504051801031406090304030807081603030e010509030a080a021605070306020301 83
    0x90ba055500a5000500ca141007011000c240e016030030354602c501c00414a103545110392021104190400001604005031441c03200c081c05c5140c80c001d00000394110010b6049854503581318601800c001c1c468403002020680e00c1e4806809681c3e801d40003c2d040205013040350000d0407482250341c1d18800f1174080c2070244031442540003642c0c104e810002690100e562465070242d1501445443c1b44284071040c03001101103084101100c008183d800c0000034181800d0042242502038065270041440422040000094010803804d00340300003640c01035103c0c1004c03c0c0c1916240282e4020395000b1507045408242d45200c00b0f0500d0482e40036142c0b072601ca9901410701900e60300c0072140803d00c0e9004110800026242c140280401b034041d031013140c1410344661721044800910241640001d0b00c41d0a080f0b26080284a101e8110003108000d5141540c10f80000e420300000030200d5603100d81c0418000d010050401800c0d040f964010300340c50380c154492400d00002c2d0403e00540c001859a40918404 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 758616987 1250 758615737 758615779
    0x607050f0d0c0203040b0304060c120c0e01030f0608101a060301050919060e0c070c050306060307030b04060e0102032403010b01050d05280c1d061207020c030a03030605 74
    0x10340c0c80100380c15850081c0110111000e0001400180110700c02040f002031650304260145010723610480c4045050b182100001741204d8074400741203200d52070643d101409035080202c3c4800c20070300382808079401d241c101d203d0b0028060b51b40011b150b1f02400e00e0300103541d4a41e900640440c808101c00411007a1081d040c0590b5020900600e03400180101c0850040c0d0141a59000c2c0c2010b001d40c003081440e120301080048140a46091150300000b086000c1002001c50f6a400a030500ba802054907250080000c1c2e541e400b03911024142400e40004a8240800c2d904100b2076064100001d5580303051080c0c11140100d280c0181c0d001d4a00c0c1000c0c0e4031000c2c6018018940c80b040140e403002c0c10600e01d103070aa001060003a04c00210481c099035220021004950307101c62001d441c100c001007100016030003038003503044d42c00c1c0300f800d14403800c81036000f43c2d40b1102034400880c084514008503a4a0030b000707030b281c6541c0080d1550305100d0b028540c0d040580c160449400d441c429100d9180c040d042140d1081 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 758618237 1250 758616987 758616997
    0x1440a0521070305220e01030b090115050d030e12160e0103030e041a03011406030106060203030903042705270d2106170d090605130605070c05041508060705 69
    0x581d82420000e640200e4840e202800c20366264502d4158800c017000f000c1d00e4101075640c004007070841c601c001001072014110005501000b840024000226804182d00c0d2540c070502426126441001002082c188074a4000c025810b01404020014898040c5540e0711281e00380e1b41201d00d5040c007004105460942c07120390490354140c41d050001e4000d0380c100400352174180c040750f0181e901c2214010b0156000d000784c00d0300703070350007400004607061140902d800d545640d080718045d540104144006910b000017202d007210b0f40c18a0f03400c2c51014000e452409104150404220315080c10180040d250b520080c48000d01c0d070100595098290440e1425120508101c5031400302d03604280c04610784c00901c081071140d0200707000000d042501d4640e49114051800d85001d0240e0181d20070901c0c2c1070700000820060011400c225040440248005410519034012039080103400b041d044104801e0300b044401030300d4000d1043c00525021030b030a0003401d20a200e0031606101c0e040101d102c090140040fa5 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 758619487 1250 758618237 758618293
    0xb070932150f0f0d02030a050613020705120f3709180b0609030f0c03060a15061116062303190510090c0f0f0801440a05 53
    0x150401c1c8400050802c6900a0412820303a07440070400c0c103214294510055205124802e00003440e81000010300595410400341120003070310411104010500000e0b13003980c601c00e1100500e0703495000003003101e10b40c000c86541c0003070311683c1f0143d21100e01c09075008000035460b00201e024200c141090440e18408184620a103a1001941b89021040c0c650094030540001809051405174008003291405010212102c410f401c1032035070b1a00381c41c06206240c0c001d400c80300305210900d207030558070100079264401c0c242030000500708224814010f106400d40607455010725814140c1e500310140a0000040d40c10840703c030000c1c03000c512030110300c098074010f0b649240414421010386030944001c1c00050202107000340e03245000150708241d4000d04400c0d807450350307600a18894002c000b80c410002d005440c0c0600c80403200500095010751883e41c13030b104407038193f00704101e0b40451220788101c18240d6481c900021104110044000040d0b542c0ca072441a0300310381e823000d10350b11000c1c4404800e003014 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 758620737 1250 758619487 758619529
    0x20c01050a0f08091c0c020901080d0f050310030204090b0618071b0c0905010b0418110910170a1a0105030108030a080408040e0a2c0a0b070932 63
    0x1040c2c4040c0301c2d10304550b010341403000310303400a21622111501e41381030324051400603180d1551101142008401a80100800001080103e41a410107883d021420148500300316011001800001c2c0c4219418005c540160007002008003a06000c02c0d0100b0031608140030f04040841002c10082c019020352144140d0340d103d8251a40c11034460242c0303c00d5040a030ba84c0101e00b803021440360202d100d140c0c020f204030490642c1d05c515008070210104007003070004030024501184c02c0c00d1110190116000040111030020243c2ca207d40d00303880380b81c0c0b44d5401c2c60314610040b0801c01c0c0d102c3c2c04d81c031030755480801c40307001a828103003031004480b140b00c24000ca241c0c41e00240a06464030340036000c43c03504644503840e2603003010b4842040100d60081100c0040446840b548030349101d5441085420a5140101440a2a9401043c455540c11003940000c050b84042c4001032002886426000007401c155602e02c0090802c005062031004442104070341d81140303050201101d480d00c0312003240b1080c144c8038a = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 758621987 1250 758620737 758620757
    0xb04060e0604030903240f052d060f041b1106090a030c06020a0e120a1b0b071b0504020a020309040c0206090d1215080a0b01140d17070b011203020c01050a 68
    0x400321401803a44010601d80008241c50000c80501d0055420368510941c0000c8c141c40c11003140340500c404183c0c8003c4524080c1480e03010b14285082456001005440d5880d08000b2900854000c115401280b9041d90406030141005a40700c00c1e18a072160007902181c01ca41c94080d96151100c0c00880010f000c40c0c0e0801e802e4001070190b80240145200c0d9041032202d01d20207502141a03400202c0030640726400001003007081040094400101880c100d04d005031042c2004000000751050f0003001d841440d6031070381b60072010480d01034800a0036000e40159214011200d0295507900700e588a28400c5090800c4007010520001c0e10f140b052400c0c2c00100079140201d02c043d41c0c1c01c00b0b030510126009840d81501400c2801154142004008400c0208401c001d6402d10000703106d011382004a00c5a482120841c8968a00705540720603604081c43c0c1003600038104032000a44900e440c01051802c00b44000199500d074003000201c103a0090302941c00e0a20014011129849810140004990b101034 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 758623237 1250 758621987 758621993
    0xc0201111920091f06051303110a0902130311090403020307030807030e0303010608011d24060d0603050304030c0816090506011b0b01050312040b04030303020a0c06090b04060e0604030903 82
    0x811061401e01510402850007842000708903c220200c4d0b0340c10728225003070071081401000910a10080c081854560300340800701404041007081c5110150801184140003982d82e52a0400c0100400380c1000445d03507241341072a0b05480d05420302c0f098a007601c000505007047c0c2044841039100d19450380c0503625204503542c0603030300c1c040040c0c0740308101030b95500003e0003c07108100441c01b0306026195407000b036152480b803003050050907400200b08103e0205102c0009c06881440350f007040200c1c05180d03180d2102000c00c1c114085e203e100c0c0351050802200109000d800701c021700660f4000c5405030803240d00c13801c00c196140715a0b54204100c6620b04010003410210350f1140340c10601c149051010139001d2002100d911803007072000d03a000702c085401008546000c00c203a10b032802803804001c3c200391a00c2003154560150b440050b01345038000400c40c00c1244500c0340080410307071000c1c1c100300c0d02080b810400d40c6130400320382c00c9820138680500410790750300004500d441640e150342c03540314103810b5039 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 758624487 1250 758623237 758623253
    0xd08061513080307110f10090b0c2b0305012102101704060f0605030f0709021602030f031305040209031b15161e120c11060a0c02011119 60
    0x201c41d00007191400c80c000c58400400d00090001601540148010743c1030401000340302100c0c0d41000e84640004000c0d0002183c000d10442d0807164028021601c5025150800e410030f80803c1c4040c008007441400001c010300f03141c6003e80c1040700f0707a0302001a0303170701d512074445074038000c12402130b12070560050600145082d000c14240c114051803d02e4040010710072000c9a448140c41c02c48040345c84291001d03081c3d18605c41d1400034007040b07008141c1003012046094450f20903001d5298841d0300094030100550781c1d404c001401c40da01401f2500f0749600409180c3c1c80e50001d203402806411007031030000e000e141038026507a000718024050314980c02c45d14a8045a001c80418180e080201079000304001032040018001400c40324281c03c0d40e800076850001c8170780740605503000b00c48101c2c04590003c2400600109032001170b85c20300216000c0c0c24100031249108030103903280c0c010070025008614503400140c0c855124800c0c2c0b2164001446200c020f0b0f00d03503000c2d031084000001d0b04100000450080 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 758625737 1250 758624487 758624497
    0x10e04080913090f0b0601050915180d12110a020f010f031104083003040f0c03021306090f0b030606061b060a060612090c0b03091c0206090d080615 65
    0x41034442c058141e140a00b050300c03101c4409035410308600d0001000c0c000d900340b07140da004000746422450400c1082c00503e80404040100c4180440818480071641801c000003001403001400804a11111b10301424042e1012840b0320014400c480d18851250380010152002580103100504a0403048011204c004210300e0020030591034089030131164001030020406004140d010300b0401101e1a00e401d40001c00800c505850380c15200a55100c0d00e0303420507250440e130310a048001c1c1921506102210f030749150400780d40040205005201c000969101a0440700040e006104c80000d070500001200c80d41e005254054000c0000207100d481e00364003c00030780c640823002e443d00c43d809201040c0b0741001200c24080c40c5681d90300501007907401515201d10340301c180d0414000c0010550343d0300e14903582c0d44107040c0130240110200341d055809003c58030841841c43c085160902c001140250b0b00d03801030305c0d1003015016000d41205094402c0015600c1980c000d404070310900c020411f604000d0b880 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 758626987 1250 758625737 758625739
    0x31c060807170115090b01030b0910170a0b0a05042a090b0a030c0b031524030a1d011406060703021f1805030d1b120c090f0e010815010e040809 63
    0x185122004c2529024030714040a44460f02c000904110300b44e0024084680e4181403074803400503071003001610785500303080c81c060319a916001c1c480401034146c160314145140b04001c01406281d0f0402070304c50704130350013144240d0040700c0400d882002d0611004807521204041400d680303010800380850b8101340c1101c242c94901800040d000ba940384c507240742e00d803280d40064248d124008140840c6229a0020101700401142d001c0350254001074070501100030b20215460100012000031401038640c0d01a403e038440345400504103003080c0c40c05500910b4a06001e00e10411482c0101d24070b41800030554801c0d6505030000c0500100d402e8900c03201c0380b5641180e81000b0f4985644207030100030300c000540c1140c030981c01107444101008113402030b14071011381c400d080d0380800700120320740d6401628800d00c030b540e5000c00142c0201602040710b181801da00300752124035503a4400a8601001610581200c200501b074448252401c407146890b90320078440c03180401459000300d03020500c070000510301080 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 758628237 1250 758626987 758626991
    0x150e0103020d030e030c1210060b0c0a060b060d0f02191d04111e0406031107080a080703090b0915060307060c0201050c1c03091a04120e04020702030609031c0608071701 74
    0x56800044035400107e100480f60341100d09202c417031462038003ca00150001070f418074100451368800304d03075035101041c0c06060320303480e1651420b140d240e503000c50b2100942071000340450b00b000d841000282d84144940007480900c2800c075080b80303228140190000c4141c403601c0e520754000300c0401000e0040c05c2c0c10045804c40c00c0103c8000441d4142072500c468000c0302c4080c0d116803820402508a642592400d40900010005480014040d00482d64a0030b102e060103019134a826404400400d1038280083c00241903005000d42c8060000b904040301c031131401d603d082035640500f455200c0c58a4400c00011448480c0440c00641c041c102920140e000c18080302c41581a00d81e107400300c444107464980c0400e030f56010801c24080c00c0003114000da80a200c81d19001e041c159900211800e01c000c01d1010403440346031440d116551a0110307008036800031304582a40c28480007040d142d501c4070806401e44c40a070316200f1458800b40c0181d00468445101400c1d500d868103102c580c003540c9a007070420840d5 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 758629487 1250 758628237 758628253
    0x30c0f1f020709140f0f04050604062a020606040c0c020f09040219120c080f0d030e0f060c0301240203030601200a0b0a2304140a020a030303150e0103020d030e03 71
    0x4100d442561410fa544d580b2400f050f00b00546110210000901100001c907000d104000100341c00141c02034102d40d0040c4c00068020124001c0c5800401100300c0741b5000d21034614130054180e00259550051170304440800c4606c00401041e41d00050b840d00080d00402c8030030903c404ca16224007a00c0d407140c0050710307164500c0812206070071800f9103074005142c000d480038404e80c14000b54035102c10280c070307040c001419885010001d155403a440030610404140c5c031290f402407045e170203009804d1402004000c80c1c1046c00c0c521005902900240617585920320703003d8080e84840900f080d484410a41c1da00a9072941d15101d0044a40c544652220b200d0030079a4001105000c2c020004d404050b402450f0b49800c0b410650011000d941000003100c00c0400c0303204107400205403004880e80c001e40e001c0c100003e22803600c0442c1e400d0034000b10020f03601125984000060542540080c101c04891806511805840d802554a010360a000117500554107241900000e4003c0d07841110740e080040c21a00c8c00 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 758630737 1250 758629487 758629499
    0x90203030f190806090f0a110904060f052416290403082401082d011502010204030827041d010513020102060f151509030c0f1f0207 58
    0x2a80300740d0b501007040b2014080c444000b0361000e41543c2001c0d04840510081c01d01d05841c8401600141602d00069a00c0080125240b1004125a54007401400620200d60385d070010031000b01003441184d004500c280c582c0880c0525017a0020044100e014225046c01c0600141181b00b924244003241d0390014444d082c0e0400302d0600c28640c4040308200011014078151900400800d800742c4914070350801c1000c0e810901c3d106802002c1300040c02c0c030b488480c130380e19a0040009100800c03c0d03081230554504680d51603000107921581a5020806601920300742d0300e03001c80c00c034800ea12010305000e00c00e00c000900410200d15005001480140701d04918244900060450b810b10620515174003c101484078103110078010300f540501070180c0c01d0310f6a00c1503000130303444080042040c0d40c21102900090034444080c0c0b004104054081c00b840b032026a1038108a84a602c1840031912a220703850b0740101c40c0c540425102c03110400607051034003079920010725400300808880a1402e6004120001c518 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 758631987 1250 758630737 758630767
    0x3081b070c0e011805010509180c0603010e07090b0c10020313020310050105130501240c1703072c01050d09060f0504020f032a0f090a0e010c02010216020409020303 72
    0x42c00505004031500c3d40350410a40281035840f04003495079080600400c000d40e0ba03c1040c80e0b102a13151402248860f820048078144406882a00e510007008800030410211504039240f28002a8441c494880d455444144090140c481c007000c0765840351185000900700b03038000d941c00010b540f105000b840c405900207030801e00d902000c0251117698500400547c9401349990744800c42c8110200640c0d414050000c82110100709602085010300c60384404442c810180c501c40380b504560111b240e1720000031440d03215072059039501c00050144907034140d00c1d0107904145aaa04200d1404003000010b0401941d65801c01d00c14000083c1da24488940031620030b0103070a24501c00700000140500d41807041088408100c141c2e28000d5000800644104241700009591300139050b120702c1200c0b48034800510750311103060030302c0d820195030410302042410507085003e60003052402485130440740350089080303008060f00d40040040810a03a0054141984400d41240c0090300390307840e000c602c8500d016 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 758633093 1106 758631987 758631989
    0x215120703050c25110a090c0314090a0f0201023a05040608150a030609050303100918080c010f060b1b07050d140c030115080111030403081b070c 64
    0x18004000c05d0350380c2c1e8101c02032600c0f020584681c04031001e0a0b07800e030310102080c01c1020320f030710300030304031040c50311400c150001489a60300c6521104e0b05400380d5081039040d0300503c00195000d00b58004000840c10107101d00002c0e01008a11560084440000b80010080248801c1c0103e56110003403a81290315820b0b03481c803404111000624035805170740300406052502c88000b04100011010750f02c24000c0e124071300c1e980e039501c1050600361004501410400801250007100103100e00700540700b4070441c40300000302000c4c500034003821070364260000001407034003040100b0a0141d10103c0d611000e8113001810610f482c11011070210b01c45000b0040103c408000018280d010401c001d5041c400001c1c02403041f0017020004034002d40040c01060519401e0651004191443c503007102e008030381c56520301207283c1d207107404039001004080e020041c040342049082c002c00d0450704004 = true := by decide +kernel

theorem cover : BRFrame.Cov 758453237 758633093 := by
  have h0 := BRFrame.cov_init 758453237
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758453237 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 758453237 ≤ n) (h2 : n < 758633093) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
