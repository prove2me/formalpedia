-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0883
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:26:04.851734+00:00
-- url     : https://prove2.me/submissions/2919effd-4276-40a1-97b7-cf6bb0a1fb42

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 158633093 ≤ n < 158812949 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 158634343 1250 158633093 158633119
    0x6090b0d09140303010603060f0b090a0302010e0301141006081e13320c06040602190f050706050414060a170a060b0d1b02010605060403060b0a030f03020c01021b 71
    0x1800760040300400c03504000341d481c00003042c100074005140a40142c0d640410b11501d8400411290b01c000c1c1c220400040c401c2103440400d65843c54003130200c0740d080c05c105008150100021f8011b08020322030390b024070324900410401401305110320050f120146c950f072440b900d80718424101c1c55664030050001f540c01c07401180d040911700c0c4000340d945100e12600590582e40869601150000c00c604000082c0040c0083e00350202c140a07642a049054401034107151030468029650000000103003402640c0c5000002801481100da01500303400a00f103480306170365032200801c680d10500c2007913500d90200021f460b040c50844102ca140f105180e80700079a281c40c0c91550340765a0005054010280d544240004080d0104000750143c203c000f800000e198040180c00e450f10315141e00c08a003103900d0f010061000795244020744c5e0960340c120100042442049020400b2182039030030141c10700c60603500c01c60406500003030b0548420002c0e4280c80c0c04801c01d294121a40c50000200c41d40034840025503 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 158635593 1250 158634343 158634367
    0x60c0806090f04080f07261303110409050f0a0b0f2401120e070501081b0a18090204090f380103090b0403092c06060d0f0c030e0706090b 60
    0x15801074000d0044c94500000760030720030555032002074111080b030110a500d54000905a445e03a1841d85d18038a410b01e401e01d5070321880b0030204a4000204548182800c110b06d9850340d0b44054649648041200d60503401d50003620750b105802c12080f80c0c1c08040500044c851800703080e405004204c101c00400007000c0140e00d80c52035001540b1014100180000344200100070341c0102200100c4d110060080e00d03061a0004000380d000400380a82c0c0104035040c200350080d210100d400c1205985071a00540000548403c1002c0060384024601400460f010903245c00f01d510248d00140e4101c4100120711800e100700580580d0080710b840d24400c80c40b0b070b101e140026a1010f9040a105140c0000c0d108003035a101801c6030b806440c1600081c0000c84207200101c0010206039002c0425458440d43e1140d40341040e5071b410008008a00450010030041c0c5011000e81040031107542501c420302211550030030050040085c040320086520a1020001c1e685000355009820766031441c0602d03150a58107160 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 158636843 1250 158635593 158635621
    0xf04060509131d07080f0c0409170304060f05060d020906010315270c05120403180e0702160609050904201003020703020c010905030606010305071e0c060c080609 71
    0x1d03040d00682840c191900110261280600754894425940320101810b8185803806046400400013a4098040c00c17440050018110491900868000c905020249450300c0107071403100813032440500c00300510040245580000c3c072908405407040181d65944c004002042c102e481000e90044200c07404102154400e400901d000e120765011689002d50703850f09801c00d52215100c0014201e85031400d078106c003903203008106151f000c0f1f14110382450070441c1c03d034030620000780005041c0100900c0741c0d100407010820074402448041d007003c40c14941014065201d45041000c013200320024100400c0f054040c0803e1002c1d10005420001c156079182c2d01c0385403800c101c0c600012100701c6442c0041c2d450382c0f010443c019041c1c481c0d4026803030301e00300d02c0d0280c500480a020981070122000040c0145c2e2400102c15a00c0802481d001c5076648034140280c42c0e0f8001c601c1d800001e445031508031083d0f25040920042e2003807140108100b4211442c04c12031301e0507019a406640000e0a02c0030548611045034 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 158638093 1250 158636843 158636857
    0x6100e01140d0212010b0418090201021501080a020117010f0b0304050a210e030102091309060b0a12140f06070c08040e0f061206010303080c0c01110d140a020f040605 73
    0x601c490503100d0300020a2840d00481600c80d030745038001502e00c03224049920494010410200818101401c01012501d180300040941070041d81d144a4103065a20070081d540028500c0d0b00001095612074002075201d62a0040030b901207032890b29048041c05800380c0050494041c690004d0b1300f2800c140594901d50b00144c81501c5610403401c505000c42c403104400c014400104a06002d03019541e40d01400c8416610fa04504c030340d2040c84611041c0c1c941501d0707040c00c94515140090280e01c1403030140d006068582c501e07030f00500d2900d0042014140c9021070006503004000100304400d202c0c2c055503545084150220740d580110300800d0b8118056075664041c24410600f407410180c542c181c1c50072030803044030480b84a904040600249060901c8103254845041c000307070903990304544014110180282002c0c00c4070b040002c03280d01c054400c1d4000301c070351488003054568451a00303000a02034000424003c007180044000b003008038405100b01e50301d2a8a50701c10f1801c0500d4004240c1c1c2c01d41250b1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 158639343 1250 158638093 158638097
    0xc0c020303030105040e2a010216031e1506090501061209050c060a0909050f0406060509090c012105150301140114010507030519110607021f0e0c2d010806100e01 71
    0x400c5594a0754140c1d00010030840c40c7d00f098941081c0d03240d000919142030206903003080c0052203800c5c03000c1115108000882e00e070000034420002c1944c940350420b01d2003240038041041c904900801c0a000640216040b10080ea41d011190104081141e04469003450000e14070b600c5100d20000c0d034104000940380c122160f0908100d200d6a0300c0000060701c104455120032648400100402c100b094400c50002e4081903038122603524100c0340003a07551302c9454005050006102c005a040300b0125a505800c1c0c00f040403e10213805c0c1910302422110003060018860350a012000517803c8280301894100d81a000010750307210000401901c040c2e208080035401c000c801c2006803692352031800c000c000d00415a0310508407180b00c0076501d00f0303c20041d104008640003000050701d4040440d81c0c1420380d004030300c0005000b84402d0516442d1510551403290810713001c8200d000701440c0161246550b042064284042040900044502c00d43c1102c1c0355901040e03d101448040744540c510b10001071040c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 158640593 1250 158639343 158639353
    0x90319020d0804030b04020a0b0406051c0f110304021309021003020a03090623010b090102120f09040501031a09060403050a0f0c0503040b070c0b030403021903050f1209010c0c020303030105040e 85
    0x41c2d118042264801c1c0c00543d101c69049017408114102064070f00010010b00c8541410642801c000800511641e012191034401400810040c421036501c805048802e403c001c0002d40114a60102c040d002190181e2103009601d2904900d128540500c18000340d000742100011222940150000c3d0440318109040598803101745000804600c5400a4a07411902c04415400119910600c2c180d0582060001e4001800304080a9800040c220f42005507426030750345600c15006030a11901640c80c07450307402824030000005102c600030030318224035080c04a800160b601c400d003eaa80e45820344c2c000300040c104001d060101440f07030306440c40000561425202aa540da112140755802942244a6004c1c0006281080212148030030004111506c0c0d15406c0d46403d48010391a21582c014400000c008113050900f050311810440b42424501001551101103240308400e0b40c2400712544011986014401d2103070354040c1805404407170b8010000e42c41e6a003804203000142141c8400d030300e414030030 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 158641843 1250 158640593 158640619
    0x60604021608030a0212040c1412072601151509120b09010b0414180a0c03030804031106011401080906040b06240c0309100c030c111c0609020405070509031902 70
    0x484140c10340582d0182e0310301c031001801c0c000301c100300c0f00501140d03a200e01c900084d420000c00f80483d400d2f0868100701200040048041d4200300d41044020300c01d07a40703510341140304151000c3c49103010f060f00c0611648600104e04100240d504840388d020748880604001986000500c241844940c04588140080303030388445c450200307003a14454068050003040386410003080c041c280e040c10003c040700c5001007d0740d807003a48502c2d85c0d0302c800d40005010418a80b0020341810b001b0440d5144450383e0008880c070070360351100140250640e0142450014034614041a043d001c0041c8542c000e40d0070403241001a02c0360b1040002d104540d00c070340b0b01c02c140030321102040f119800e400f400415404070083d6603105c0c0100c01308078109140440e4072062250a801040109070b01c820060b0249a02400c00d402c40d1445000003241800800740d640c0658855680110030040140c026080c01c9200f9035003840b5649807164140c0d01030148801031500343c1c5c4000c02038100e112651110152440c0058080300a50791 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 158643093 1250 158641843 158641867
    0x2d0d050f070f0803040c0306180803060603070201060f030809041b020c12010b03031206100f0f0c051203092b270e160908010209060403020f0a05120c03060604021608030a02 76
    0x1c54054404800c800c46c1003003840a940540d41c07410102c00b040d50303210044c031350b07c0403a90302001e800140140000710014500600035444035015041d03440407056a26920301d44078210740e0007e000c10f8010380c00c04401c2d000c4480610f5010f0405034054000e440b0410141d814032002d00c50b450b29503032482d9242e20301e60540351401c0c4020510035041d03020445452603c3c009200d500d0581900c0c08040141941210040c50341c884407824181465151030340201d2110308003980782c4904194440c40b40076002041c4803e100c0e002505c41c00b07100c814801841509038210054140e00391284a07907010980c10112101c1c080c00c0591182d5212070804000740d41e00e80c0301c8a43c2c806040084030808682e158404d240c021035504800c1c02002064050002c0d4604030600000c101e0a02a5103c001c0c02600c1004040d00302d595480070b400c02805020301680c40201c005107181d551030035a9103809001340034102c081445810540215108110b5400c4080c2003900303181d80398240b070b51004208214050f1b086c005921110 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 158644343 1250 158643093 158643097
    0xb0a0210060b0a0e0a030209011e0315020c0c0d0240021b010513020907051207020303011d041a090304030807030f08010909110906122d0d050f070f08 66
    0x102a02c80183c0b1803811003405080984c0a8401d039119034101a01000140d03154400c4a0648035861030300d804900c0f00c05131444146003990001040120230070607910020400b9805014101c410408440840031030740180800c40d22400fa0217034111110b1600030100704075a1410071500c4040c50300650808001e0840c01c11000c1c1c10800212046400040c0000d922501600746201c110b404802000242006624081c1c0c940c11902c0003800f4400e00d80020728450f0240e03064404101640707040c00203915087c6c10094480d0702c01d0290301700c4650300e00d0069401214508a1612990380b03c168a035000e106400f20f560440c1c0b0003002e07003c8500c0200008070029061700f02420425100341c440d44500c10300c0e41b102420303012058100c0344005141c031192a02041c03002446405202080e11008450b4654034003081101c0c196400020030b40c4286054818070b070480c00c8110303a5800004a440308075844122420b51501402e405400014205124081c503081080c0c004019007449803040302c1065401e590740d50056 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 158645593 1250 158644343 158644349
    0x2070801060b0408152e0509040b090706050c190c12030804060b0906030316050c1206040b0c070507030b071709010e06010f12031809090f03030c0201150b0a021006 72
    0x41000c2020401c0603420410782c080741074417102c02811881c1441e40000c0041d0740d03c0e82c565050400305018001c2d10941003507030001e0300f4003405100342c13440c0c1400c0142c00d1b03203403d6070b900f41d40348140c1310000b40e054420070544040b40c80a4001d026101e142d02403072a602e4003004000e580041007500c00040d030008103408111941d10070307242c0c13009514150502c4001c481840c60058003441101c2c0c1003011030360700841269245482103000202480700c0e0305206190501d40d99405401030014690310030901c0c000540d5a1285100f0390014038aa90f42d84207001d118090401d00410a42c461142840024585c0c031074594421145c1c0342803450943e0b1170b10100c141d21011f681000c016551800041c00103042407203414003410f00c0c10802d0000500d0b0503180012810350160281c02c000c03050b920b210303411011020701001003040c0c160920240c010742c1455840c240305507404a0201e45040c1d901d4600760b00601840d0007822881c0414900149480341d80c5800c0e07400740040900f14081d24541c0f09503881c4600c11480a = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 158646843 1250 158645593 158645609
    0xc0402040806041209050d0b150310060503010e030f030609040f0605160f020c01120b06160c180b0d0f0302102f0c0607140c031c05010909020307150207080106 70
    0x1414142441011842c0c8030341140c4c00c000112000303024940b1440554500d550f40306180100070381d51011600090041c00070400c0d8103008440d011000300c0c0f0540c10400c1a241c00b180204044208403014a689200d003490300107880c1e00034000108030b854101d2860340c1c45401100c2d8201050250358402d000c5400490f801c5404421102e060750750a98084034030003200400b40020110720a5103000a8100049810303204912034a0b41c2950049481e0031040d50020001d002c4800405002442c0081d00d80c6c0140c010060b9107950320085400c040c0e03440c050200108005007108030305200d2508c0d000c00c401c082d0a4260250b00c0b0320700040081340340500c100d09000403c9107d541d103d0490100340207101c0c40d00c00744000814000c1c40700fa454198081090740e00324400d414496500342204554900303a004000280c0f50394000482c0c54802d001007442d210708000c807542d400300a545e0b201d00b83c102c200d8801c4007020b5016401541e003070100740f03041e690b0000301040318011582140e030340d00706150941e40c0755007040d02d07 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 158648093 1250 158646843 158646853
    0x60c120609060f03030f11161505160b090c1c21050a08130209090d08060609090604050916090506010f0309050309040c0306050402040b04050f0a0302031209220e070f06021b030c04020408 82
    0x40880c0e00c43c0d42c2e0002700c61450303e40d180c0361041c180d02c1814201144050b10188148002c036a020400304a154104c0320302a000c034100341c0041c0e940c420078400c002820b03103034808800c03201c3c44200b0034003000c09007002081c0c03640c80c00d10707200070300807940c1400003440408120744680c1d40c00090b940d0200306510a0280000418144101c10740c014208007000d45154001c0f44240300801c01d5540c1c4c58203155000106681c006801d43c0d0ba4507020345008425900314883c0e41c020300b0302042149094001510039070007a21500c1448201002c12000c4070059500500190030620240c11b8034a040d801200003044103241c0070500d2900d88002504990095000381c1c403003500001e0030400d905000c1c8800008030002c0b191b000c011031541d0040b0740c48146900c5190100c01d80025170190941c1e800540d8180d2039070b802140d00c444001402c0100c020124817203c9080f91180720b06c0044c18a00421080e429150140d010b4840f05000c1910b0440454510503180d50501031140407014603119031003e4402008a000101 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 158649343 1250 158648093 158648099
    0x3060e0102161223040306020f0706020307050a0206010506040506030c0903010605060a170112020a0302010f050d050a0e1e100b01030f050f041b0503060c0307020109060c120609060f03030f1116 85
    0x14107513500c00c29805014200c4d41290390f562041043c103403402c42e40c00030405aa1403da0b4111280c080c85005c40040c03049101005000300c8981c0300b40584a4040260201d554507602c600c10803071140104e00c00c031a4450020030000e158000014050046545c0280c00403030031548410005036542c0005210b04001a032000c21001141a110130701d50040c04400090040111982c002ca00c8007001404064103000d04415009055481502101c4502e58480020041810090315010180c40c0007840001240b107450110102424262800c0400d030098100070300c0c0031071729680c0d208040c042a480141c180f5a4540040c40e03c0000703402180c1c41084022007596091a1614103001010b00c3d440580c0b00301e42c0610340500040e10006017141d0084c21070070445499954069080340580304a00c0300500007410f01d21039104c4150000e5100030740c040341502c01d004858403031070442c0403a03036503100e00c400303ca1841034100042030080c00d50b0a18030810f031800ea6903031417990210070316044500d000d0300c141441e0300c2010 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 158650593 1250 158649343 158649347
    0x40605092a06090d0b1314151f0b0415021e060c1c0c080403080606160803060a0b040e0412030e03071b320102150103060e01021612 58
    0x15694a92062070026039090100380104440c81d02100c020340140400602441c4641d030b40c0c2202014280d0060402101d80307090a001c8803c8442d1440455620302000320809403250003140c881a2a904c1000221743c07591490f01089110364446030180c40d00c12485400700c1c0701d2403c40001d0000d81160740c030440500320011002454000614400c2c8004840281c1c400314011004c181150003c1012007500e441c0d110b141800d100c680040c96411545a15003071410300199003212140d84198003c1d159442c0c01c0d41d8980a0000500c5007120841010704071488481c000b401c103101460b00444040d26107140e454450032600714540c080d03086034001c21223040030803003040f00d414034905459041c0d10b41801948800c80002d5640d0282032001080290000340c090302d0140355144940080c0340a56409041c0340c0c1078403010005803c05240d40101d01490961071645500029142440125072954640315030310b5900c44600509c0741102c4032030255001c009000e03000513140b0101c003c0da0f00800c030008140d00d580d0303c0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 158651843 1250 158650593 158650603
    0x2090303130509061008070f3005060a08030403030c1a2a070b0c03060f040507120609090b0f09030706050408030f09070b0405010c0f0501140f010603060305030702040c1704060509 79
    0x301c45d105030016458004442c1e03001041c075400c004a030809a00702031280005a9182064401c400c0301041402003501401c0702c4008100c0103491401c404203c262544802c2c005403610b58040d4a130180c0c000c100c01c000291203031001e544018010240650844006644201c4820b015141541400d814510708800c0845c1e2651902240f88000000c80c50038045548420b02c0000c0203100750182240800001c01c2c5440c1c03041c0d1030168410040041000e45400714028000d03224441c019140c062909101081034003062240e1041c8903001344501c01c5655074071052505941c0300401c40c403c540010b01c01400006c00500805004612951000d034803454003070780600b800300380103007105c040340d0101c8801c100c4070840004403000e0307500178a8070b2207010720705090046107400081c0000b0a690300e0314034407540b4100618905c900a0b0054100302450780d98400045060764000d0102400365041045040300501e00f5501014200516044c80e400000c0c051718203801e05001180d06480f40f40d00c0300304008000304203103c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 158653093 1250 158651843 158651851
    0x204060b040f0b0306090103060c11101505030a050303220b0108030d0c0f0801031b0e01290a08010501120902040c0c020306090109150207030504170304060206150f1302090303130509 80
    0x204182146000c05c0041c4004006101c050110f42c0c0e14104030b00c0c62449210385c860072450910480712490071035501c0f100103200d0b12014007201034242c0404521407038085440c65026810038000e50654481200500c1840d41074070110000c11060540080028183c2c0751440c000c0c41c403080030b140c41f07142c960700140c142c601d1603440307000b001507443c2c0484181d1b400844003415207070840c1c071005143c2003a0204100b030260541240203000e0700040001204100038403248245c0d282c07200e946000542451958505000f3712843e100418138020050120b94850300f03400b045888004008995603400717402150484140d01c1b5070000040324000c6007029070900f0040c154101050328020040c00c81152a0500000d0044000c0002e03a43c0005000040c5441070040d5401303050700b00c101e00341c184032040c003641e42c03030b8018418035003d40650030001c0ea2007140900040d0103008054507905220100c0003c00c0300c0c0031402210200350304e07400e01c4582c0d00c60b1000c10141410048801a009055042c2000c005801d01d00030 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 158654343 1250 158653093 158653109
    0x705011107022d030a05072c0705090f040203040302010c0917030412020a0e0f100608010f0b0a020109051b030f010603030c0201082805040303050906010b040b07050304030204060b040f 81
    0x1006000507110f00c040d41c540d00c10f410325a200d0700404140610b5a001000755042d50602c00c03034242c0002c1c01400707c2e00304211110405040e50310559941e031300581c0581c4080759002003a0200c000351003d4001d070002c15090200510068662196900180483c0c000355002e0340180c5d0358402402000f9000550740d8080c4c003000174412040b12803055119500e103d64021403202070404c04042d4115140d8500c520058070000200305103601d00081d641c0c00c1c2c90340483e86840050a001000141a40074040c4141601d041680c41150181000f142d038800742e0124280504540d612030030140850400e00c512400c91801189800c000c400400415150142c48142046164507001c02000001e40104000d25190703428244505940e59030136500b0700c1d000501210344592041d030500190100301e43d0b80b01a100b21321a860410a41e201c040b6202d9885009014200b680c0070100400d03c845040d907805025aa403260081b00d145c00d4030b0382c1c0480d0940f407159000040c401c80101e4140080130744031203c440544204 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 158655593 1250 158654343 158654347
    0x70e09091204033f0c08120703090b10260a0c06020715020105090607080921030a14070c0213020f0c030403060e030a0e090601050409020a0f0e0a0b030a0b040b03070305010207050111 80
    0x28080c1500340820460038a0a005c0b0071a0341400300544081070b078004440078a804480b0b40b500500c050b028110b800c0088030b89100180000c2d0849070065600000e690450318146107242c038030601c0f6010401e41e202910344910503558048005126164001c0c0070b84030304d90140c000646481703030700d6034040703400c64a074000d690405040000400300000c1c03c4d82e102d44240303455443d0340c545603030329403c081c1100f85104d0b0f90311070360541040c03500c581e10041d802040000740c00c10000b481c000c0c1500e5012015504007001400348641c1c40c02619154920f1101c01c3b05400c00145001300c03584000752154000010a4003c4c0c001040400030700520380b245140080e402d0015501c0d100c1c2c0c01c04010030070090200924491100303040401e07901d0340f141e429180900341440c011540c0d0005010089c0c022500c070f015010014080202000130742c1072010b122811a80c42000080c1140c85d55815140600394010586400c9651200003c01980e0200301440c002c50051b0001603641d5034030b090043c295a131010300c0b04512141 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 158656843 1250 158655593 158655683
    0xf06020f03031303090f0b250b070e0103061d1801062610060306020c010c030b011b02042301030c0504051302040b04060506030a0b0117070e0909120403 67
    0x1001c0200c03988a810203026404000c080c0c41c06a400d90382903082402906100da1010030160704001c020920301110140310400c1e45001c4040d007078050840f80380201503030041804078510a0084409c0301240c40141400b15095803108038841481c00345a4800c02c60f110385009000720341071000c110781508540c110003800b0781420501c01004154421442c03240d51002c2092450032040c080c081e04000050400c814483c41340da90511201a400c04550981c05510f00801540b0a600900c03408115000c10707190049070b010024990100410301400a030f0300140c5070480f000b003101c4a5800000440a100141b0720194194140081d00c1d0360f4a4000354001c03850b20041c08000d200104030000030301e5048030007240b03c5800d074000c14060801917000c16003000b400310a1008240305900725010707400702a40d9140c19040d07902102070340341800381d85800c01701c1c0c0b149940701d85034201001e106501c03400420803961820100018824030f035200707034010f0301d0340c00000e40c52480d54002e4900305508842c103001c1400450038 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 158658093 1250 158656843 158656873
    0x30209120d0f1e0e060a090317070204140f0106030b06040f0608190501081518120d1404021c020a031b050a0611120a0210090b01050414010e0610030b060705070f0602 73
    0x42584e400c2c070700c43c01c408078860306254850141640596070045528034622526801d09041d6000040b0032841541002c0c65066056208480540b2402c0004143d405692915500303600402c420441c45801c071008100c08201c817060700c032400b4018202661802c4251030400301a10f0300240c2c2040560016040400400100d240014404004806030041c821036072520f1800281440100010b1100c038018406042445405480a4004504900418400c0c1814001a50628041110000d40c09000d402c020415178518840320b013100380c4050030328501c036500ca848203072240b20380c050b02009044070040c09000a04060080d01c00401c61400c2003440c4070011a12551034504156018000540c0822880c3c0f102d4420820013074080304c411400c02c420b91807801d100240d01000d0140500540c2030101131451202c40b016400d049500f0311107000c10316215501003244191012080c00c00301a12003050101c5942c50300c000309601482500100030341031404045e1040c1e00b809a00c09019504080125883c82d9 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 158659343 1250 158658093 158658107
    0x1120c0501030b1f12270f0512040306050a110f1210120f060b090c040b0901020c04060e0403030b120703032d09080105060303090f01030209120d0f1e 66
    0x89090078040340c07415180012401c86132441a1150304020703a10801000150004140d0300c65071103181c0e0038461399030022580c01544070140001145110207000740c4010a00304003801100d14454425584031460340d03440d0072010b030019041aa4080e58641c14480c105205218a403e4002c62400030760a000d5210401d50301401041d04480c3d030038071001c000030101d8203104041c80c040d16a14105a004010500388a42254003080c0100d401625100700040d1500d030150042d8481d07943c0084452925042c2070001c2c01540014000b2410340c03113440d10fa003002d60755034090358004d00b01c9441406014070300f500b801825141090890f501a00c13008002240b0120301082d103a00381da40508008555142c505030005413502a284401c00c00214084d0480c801070b400015070080700d00090080c001c0ba1955010582c81e8481d00712500d601c02c0e01c1180c224605e50094029100568004044154a14612050904080091001b4000104d203c050030000d6500b0004050f5120b8a100046040400c520b502030014 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 158660593 1250 158659343 158659349
    0x605161b020f04020d0b040e01090b011406190530070e061b03070f0501060f0b040f06080903070501090809010212030f0406050c1c050f01080105040b0a02030c090312040e01120c 78
    0x759400107000440c000310b54024401c91b43d8040d004200f880d4179052018005d10001d1400c54894540100004105000c8408070070300d110024180c0d0704e0010601c10011100c8040d1074030009001080c0110800404500c00d510546016080445026410b00c0307400b002030310f402009842801414407040050b500c0b1030040d18503103410703502200c05d19001c2c481c0582c40c5010b80d0704010480c0e10381c001000c04000041d000442181c0081206021a0380c94042e00501c5000324020078001c000c500c501000850310a0703400540040c100000d8902c1e200e080e4a0f214252080b4003c29500e00300d00180c8400b80e0f590412010700500503080e446801d50404908540e800c500160001d0071035919a00481e0046100004442c2c09010700f0001ca4000512400854050507044032251009400c01d40005001a8103001e190710503075121302802d82c1c981c0c9070030761800250070160000781c2c0c8000c2403000000b941c404011100d0500c205008040d01c90340341244c2d10b074910105802c26041e05880e110303c90000f80c140d942071425 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 158661843 1250 158660593 158660599
    0x2090a18120c0f0c0302030f0f12070201031805070e0703060503070e0604021c0e071401171510080f060402070b0415110f03070e090603071206090605161b020f 70
    0x1c004801c40c00300c80820310a48080c1190400d0344140041100710600070003228426000c1d203907801000071aa94442240308800344054001241c6c04005403055001404010301c1410b000944829031449841229015101110f071075110783c000340300b50070000003040c1d070080c2c0601d001e001d920b04040c04287c5801d403520504044142030740c0400c7c1265143d0301551602d101408280196a40d0b6000c050080c003c2415600518010b66a0100f2829041d6105006480d0f040e150441908800c014a920100004101c40700304802e00285d400d003070b5150140c0910301c140c556103455540c100311490b9008010060041351103107204100c050b000074000d0031104e80c059046140b0b2010031a041c82c03803c2c06003142414240c2c5800d0001032009000c842c0202840c05000d40b80c3d114400499484144140381c50259011941940129010464445c5841c2c0c40766201d48030340710200e0025601d613151015200259500c10301e1080c00c5d202070b1406940901e503040c01e007074988111100d2031195000b05103120114440303680 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 158663093 1250 158661843 158661863
    0x609050c09041e05070504030c0501020a030c080d0b03030d0207020f0303040f21021003240513090302030913051e010308040b031e090105070e12070e1306090302060402090a18 77
    0x70442d4076085200c2820f00380c0e010038886840d01500042c16980b00380411903c0c8007450070049125480092061100c2d941030721003a179011321a8441c60295004003144d100019100c80802d86141c130305002908011b0318403940075840700c50700e1040100d2801c01c000711a000340e10a1008000f01c07102c4840034421903011500200204d0f0b44c3d0f000b090310906a0345000303504600140803010050b51b06901107002030584039924040d80b90204d800407840c0301c0900c5480c1d40881100e050079403900c42d65210580c0144039004491400001c040030940c800317821606010042d07a54410800381c5000c900255581607110600c4449a605554445a0700e0050b07009500408001000180700e480d001c404054003210341254181140c601541007034080d04c1e044590000048000c224447e260804881c03000a0341c5006024200c1d40c3c0c00e10002020721000100305055040250412501040b4640f09000103940640c0c040c0641386058014000c520320013510340c00360a49000a081112030714050b0084c803043e80403010903 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 158664343 1250 158663093 158663111
    0x7051009050703140a0c08190312061205030417031c0b0604080f1f090b0a05040809090702011b08040f02190b0c100b01050301050303032d09010f0609050c0904 70
    0x82e01e00501d41d000200407944180d55694040c070002200a000c604c104103000c0401d403501584c1d0f8950104048060340784044148000029000c0c03400404082c1e528480000c111307030344001c0c3c0e03440c060340741c0d5041c2c1d80383d00005024408000b0800b0103850440544008602c1d041e60905070b90804011454010041991000c00b410241ea50b1401c4600401604088801442040c3e50a82c5c440b004142544850810041c006040b0911070241002013034000b4401e142076074840038000080d120080c0219a460410002e81599036072b14100c9070f000d641a0707400040c3d2800c0c0414010000c0301008120001d2010613803c10000945400d55400340b140d055801030b5640e01101704c20144019242c100803200807010030000340b0038400043d4121040410b0707030240421060803005450510080c0191501600100001501d01c3d0b01d07920001c10002c5081c1c20031070742d80403417a1000955607041d02c1f40301c52a5100c01c1c00d8241da0750f15008080103440344850401043c10000c82c41e800c24494189014091038482c4505 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 158665593 1250 158664343 158664353
    0xe01031103120703020319090f1e081203010f060806060301150e03010c1805120c10050409090b1806070516030905040606020c0109060305090307020402091c080c1207051009 76
    0x3070519904102c1c0d0030340350307075861602a4490704030034420000f11901d061001300b030300d00c610795010454441d500011b4069090854007100140144c403201800301a41800089950302000041c020442c00e0583c07940340c0d414540c180406284c0c170fa00132006c1101100a004043d6600c03000c41341125250494010410341448081d580741615464041d0700d546441c42550f091508a1142144003581500c001c025a444030704006070042080300d24409503019445e20489414200c106402880142c282030341811365900d1440306440d030340081151403400c0007051004005042c43d006080f41d4100300a41081e117080407000305076004041d02002084140c40d0098181401500084050a005842804100c1d110325010350b80742c1d250064940068815400065810b20a2143c68005c2d40d800014500e03261154082102075040040f500d41c1c042d0061917400c01180703c10504100807442004411b4a0394030404a2a00f807101e01ea000c09001082003150400080000c1000301003400742c42c9000507030054605003 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 158666843 1250 158665593 158665603
    0x100e04051504110a0614041a0c0115060e0607020d02090c090d0501020304030215010602120d0f02030f060310021201120c0513050f060d0f030305091603140609070e01031103 76
    0x407011041541402e10050008108405000043c2030311014507250740c1c2c0c401106d004040002e001456103003400203215090346004800c2a80025a0030b140c202108040d61500316150a04042c1c603541c1aa80100512a008982c42c1d0a104089480358100312103500403615080180c0d40003441220000700080c140c0c400c02c025a03a401a0141000788403032100d20741107000354000c0c7e03010740140c0304001496a40d080b8070b0001e68180c030b005601810b000c0c400715500210903040494400c0b482d50303c074040e0712014440d9201940c41001c20840814541c18000c1c2413500300b00b0b084801c898881c0c0104203e00310420039592250454003910700c234a100c1071290030600c1c1990b42c00d4003c43d61218640800600944c41c603000b441c00780003020600d100903160300341001070081d0325000c000c1c41c4041408000380403074003075804164040340b420140c450800096007194282078581d082101e66000512007100030b048100451b07a44990480300900003103040800800c440e000c14440205401e640d921038a09584007800 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 158668093 1250 158666843 158666863
    0x50f18100f0609180608030d0905030d0e0a15110a12091a0a060806040b04060f090b07050403030306080c0616030e040203070908010506090609060609030a12180905100e0405 76
    0x308500190b616070000501900e82071240040d09030800f92180e007403024600c100740c01c64401a00452420f001d000298010b0152410706540a02080c00601810401c40c01843e900481c901d004c2d02030b44030245044140c140c1c1c03070380700181000c0c6040c00c1c91000040d03c4e021039a44680714107209400810850b00c0ca40500001e48008103032684181c103006d03d015400c0b60190089804800030303c007a80e00c50398105d6072100c0c1160b0280c01c0710301201c08078022071140d601c1680080d000100c04100414503031078007446c401c2c00b80c3d505800941c00143c10410f0603418410344024240010241020640c1e001c0040c20710701402844801c20254070000204150045201d450f4415014100b5501c1c1c0c90100c401a00701e103800d208190203542003400260b00f61524040342c6118210080c03400c041a21814240500c1c0c4c1c02404c03901d905403040c5960407020032404607214860801c03580da1448580750484011814003095032052201c03905100500160205000d03905c8282c400c98140c14500740d0340e82c103115260140c186 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 158669343 1250 158668093 158668109
    0x6070804110d020d17030708090a050d2d0504141903030e0303040e071d04090506070315080a0b040c060f0905090717180d0c23280606050f1810 63
    0x80e058118075070705c004c0038600c2142d0607110b421443d03680c24442e40d2501c43c4020000c2c002d420500d40341c0340c524020032403000715940e6401d15035191060b614030b854840c8100790a140120340701103002c10807642d50f40049140c4840c156040c56203c503201100191703100e141c0c0002400d100e00400140c030503890070001c3d00d00500c0d8180036400c460501600207000002d2080380c103200d180d104034036248181418091014074540c0310009018550740d035a4118010324500b102190854868400090481c4041185408180c0143e06640ca0350625207000e6101d00071075031002052010b92000018101c1e08260000b08482090b01d4030aa42e603070b4004c08072800e040500044081040e6803040c407414034038032410000719401150488032442c040c02c0040d68440b481030b02c02081c031a200b051501c011101c403403460b00402d55210450303d100541c5072800401c8000c072242ca540070152040c044007800b0043c0504001840103451488030040c4480100780c07050842c542907100e420703000c40401c00c4070412809c9100241009 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 158670593 1250 158669343 158669363
    0x50a090503070606080d0504060813020f12060f0108120f0304030302070204090b04050106080c0607150e030708030907051e010c02030a08030705040911090105120c0d150806070804110d020d 83
    0x6441d000c0c000b01201d010300c5070b982c410000c48140d200c2c0070f8408ca60945d0385945030214165280411084081c8a00c82c08907005140408409501d0b100c10809154858042010308800d10340b4002c401c02c5000140c1c059101c075881212449002a044c20440e440400d030b00341d12507901e98403802e041c1c1c00b034400d6000094000c0d143c08207103030601c01c40101030303401580324900a00c031703d50741c420226641c2d640c00c4c648a540301c6030800c4082c0019402c070700801c1a021350501d01056010300c00000c0c0e0304640099400307549900c000010804c0e900024040340740035210803100c18140340301c02140020710002180c10310f0f052241c140e111406554040083c0c1104c1e40d480f140640d641d20348050018100e400031f100d80038059081000410901e201c100603130b20300d51070694909060074001d1800001031207000d0700c1d401c0c0c01101001051005520760007554612000b0102c030320b001034030342071126151002c0140007000f042030503001c4c48000b581101ca0000c048004450f10104406030340002109030b010303044002c0c204090 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 158671843 1250 158670593 158670607
    0x9080d020d0c0e0102061314030a030c1101020f12040f0221150f070305100e1e0601020d0c0204020d02090402030f0406060b0a020607180305150a05010b040810050a090503 75
    0x4a90001e000c481e00710101401001c90044003520044a0800582e0240e00041c001603c2c101454105081c0e0034010600307400c803c0042e24825040d0390155820030b000a0721400c4500059801100788080c050b188402180340c100d2104000645003d484420a0f001c050080414240400c3d0441350b042c40360000c26664034801001c03c20541030480e01c400100c580640c051244e00e501c0700b80c0b4500c0c803c0607440d0701299a03542c1c10004400a0100070104d0800362800c08000c15000e456a5100340b1591004400c42c00300340d080211000c001d0801860380d4115403101005580c0b80344c0c803003000c000d1154155000b5032a221305d1580c1e00c02034050f15035855002480402000255170b4451501030066000c1d84c01004400d8980745007500780d1154442020140e030151022956451207446106e400444030454600032607100e503516411300132852170250780c0300a051700340120640a031140d14018a545005949060303d0008556110500c00072242151959180010352950264100380c02180d809003d6135685c2d51 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 158673093 1250 158671843 158671867
    0xb09150c0703030e04090510020901020f0a110102011407020307021302040b130e010603020c03072904050115080d0e0402030a090f140c09070804120c0819020f0a020603010501120908 80
    0x10451006800061601042e0403090405106d2030303074000e4018018000c0c0301320351118036000c0d510600e90745046114400c405075841802307028428845100b0b903a5010a00800c00009080d224540d1540404613010828064440c0d00041150201c41c3c3c16922500d60219050503080207004a5100c03003440d5a0020390291002c95490501d0280c43d01c00c8602942c2e640c85000841c124040d4001c140ea035035000708a0180030503410700c6006041000002d2060700b4200000c021110840c0c2070381c08880c07d80d100c0050661500703850064101611003a40109500c0390403800041600c2102401140a59400004101607150030b4102c0340000742c22242e0b550242c01c0c58039252001401c240008201401804124546841d10000c001c0c0600c840b038be607c40582d01c4549507200e41410b201354540c14000d9040a840014050704050106040d00c001c07284c00000f8200b4019084c0420211110310a4214500a2005a854000b40d1741510428a4154005000309210300000e002440019000c504003003000d101c1a8 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 158674343 1250 158673093 158673103
    0x61c12020102041a3c07080a030b0916030c0306080303150915210f0607090501090f120b272404050c040b01020c0613030311060c040b09150c 62
    0x51815030030007280c101c451303080d880501a4048411101c441300b28424020030032440c10710600028288441c0f0f10020512000c002940034040c01c91314031201045200d460340e05407140c4440600d066505d035040745810380f40300c1e205045621200302415074540e076010340680310307500c040054a0014104c0b076503070030702c01c4448103900345c00441c00c3e1040d405140001c4100311440720211110a02400700250036000040460004050b0f0b09001440d219071200c82c02c04840820690f0300544d031903150141600c2c2400001440000395801c11801103130ba0a004100c0324001c400c850000360703007019010302513880d002c08604050403041100d840710003881c01d0f001c140880224a80d1104902901800f48800f1494500081100121405401508034040c05001410305410040d038583d0144150341c00030146c800020420380080c200b00e42407812242c024010141c0105c581043c00c0542402411189499409030300c0f0340c800c2d4001c07912020300118048a00791100380c49081e0400410421a0312404540d0034683c0e95 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 158675593 1250 158674343 158674349
    0x10e0114060405100e060d030e1c020301060503120d02031b0310080706260a0213081606030212150303070204050901200a3212040b100509061c1202010204 68
    0x240d20f0940410660068080031208890750044406803c0ea40c2c101003242101d441c5a0980601c40c051005030718581e603424003c4050000401005900d40890040c14211620382c1c2101c2c1c041d030f010400003e1b0241011081d13502d51441d504004d81d40742d0b901840c03002c002d1140300c0b00412750840441848803611140c81c4280a640c856011100c00a42e9080101c846840c0e90400c840c441000e02203079030303840d86101245a40300203110805481c0c40d089c0d000000c415802c0741e01100c1c17980c010b0300e00340241d811413a41c404020700f810725041d420900030781c0032049621009400c60701e1040d5031000714030568906005039401503030000c100304110718144101602808400c40700350703080d007244004905111001c209883c0000810f41d2001c220300724203d0254005001c14401c1500c0345030f440d0240320508500304c0203101e0394100c10403201d6141024070b000e94186002400c01c44040e44807140500254407522030186e40290202c4620042614810341406004804080548503031071200c5031910301e5405400520031 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 158676843 1250 158675593 158675599
    0x40615030e0a0c03030309030e1302090a0f03210912080403020918030307050f13030501091704030807030f0c060501090b0307050406030b0a02070507090509070513021207030e010e011406 82
    0x10803241503281521480386102c010001070700100c091011030703c241c1c1318003c960f21904040907080440300004400e8404a140304004a400042c1e60005041000558000300240c1d00c409c6051421a59100310781212000c1d00d0740c01c4036007103c183c00561710840000c0c0c01007080f10030880b038848c2d540c100307961680d11a01050f03024041c44408a111150080ca65031261881c003070145065449980c0100c030300d0b500003030032044040c0c3c00340840994621a80600401140700b0303000080c42154915198030b07003480003081c4005001007804108041190307281162042035040c034221401c007058071700039200d0790000000500410b15050010a0320000c940c403154224004600300c8611950341c100300010303540b82d0701000704007c80c0d482c0411031200068001d01083c51181c03041d54011611002c4c440b00b2200c0450340050141d1100d03900b000107051080e0310142000d42c4100640c17030041410303914070b4809400341c00720b0101503886d10001d00002e4217500c9950f401d04480c00a010b030351503003c560413104c0001c1e618284 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 158678093 1250 158676843 158676851
    0x4170a0b07053601030b0d080f0d050f0417030606040909050a0c080d021b0307230405070509091501030f1505040b01050c0a0b0903040b030c0c010b03031e0702060904061503 76
    0x740c0c2103001e1240c21043c845411615a0b15800031004402503e2880d0203113402032514030820300040d000c240540360b04c1c3c14286090f0303251100700d480da000317449010b0000c0303e802c074845c400e0002051b9403950b07107000c01c0b0051020039907039182e41c80880c0451140d030340007540141c5014034a03c100100445d1000f00b0134090314108121640b030760301da10f8403200c0b41c042403000b680c407a40041001040c2c10ba081074403880020161420503503500d4140594845200c20f000a845258812503041c0c40c0a12030590004e100385451818101c4000202e40e816502a01d0f80c5002002c42c1c0c20403810360700c25000381c0a0b60388a090248440034034002d800580349140d008840c402d50620100003115403145040c1e4040c0d002500041400340351648840800707e40c01340c082035071800100000b080001c0741c40c000310301480280340241d42d1490006507040c219190511150301c02d81040004c5c0d15904419262400d0020285041035628030f401e10024183e8419802c00c140c0060034203000040f00e120f40d00c1c06100155041c0c400b44 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 158679343 1250 158678093 158678137
    0x1b16060e010b19050d0204020d0509100c020a23010f1a010201060b031005090403030222140a14011107050909060f100303020a0602090102010b0d0507150203040b04170a0b0705 77
    0x2081c4514020103840043c4402c450800c02890108295841103001420062515030307180f64040640b881100da0702c0d031540c46003503c08504400c84c031420000c0c0d1441c0c07000d00f40080c41079940c03c440004102c0c2c440d020411034001d0200305c810a5001580c104205102004606650b0800313000801050705c9040c099444e001c00000c9001e04034080b02d101d5100110381c0418181490100544060b02a01c143c1c100350b4284002580d00d240c155000495058140e8007500c00b40c03600c030000d007503150400c10460040e0800d2001f00134a00c6031001100d504e0f242403c05c0044548d1070050b031440c0039101d0317001d20f0f4000d001c1c82c1400311481c2d01150040c0500b06a6000c45020b90301e131203250f40b4070121848000e00580c049039809010503266405451035400501c0007040159840c0c1c000b8082c0d10407454183da460b0481c240c04c0082103145044402990814005141858500141001507020303910840c0401424801d800d00c100c0c10501a00e04482d07408260880d4906240c0c00040060708450082c42811505040c90 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 158680593 1250 158679343 158679349
    0x9020127090c02062514030108070302040b040b010e040c110a0b06010806220c0903060509060609090c010801031e1e30030b0303130603140703060602061b16060e010b 73
    0xd0300c00c045002d5010300d24480b41c4402c10016840b0700ca44000c0101c0700800b292a4128030001f98003e2003031038001c1500c0750450041008031100c80c0c60703240c482e914000c141c1080366086a82c00c1e2010400721000503500c4503a20f806c4c4c441d605620010318140c080c0c0107649040100f2040703558000c0c2800e03601d002d996582c42c0e0034401c5007c000000c44251b8480c0c000003245403c510b412020b100002032405810080e038070750340d68050314825522008690405010007000d0b0410101c02c076131001d4a54014840c02444600280c040601804050001c40c3c1e01c101d14540b500b1007039940c0c1080c1d0350100040207040c0c2c41400d085903410645c00304a8a00c0e400c52895510001c9010a0714031140050006030b4400c200c4850982c01001d2a11134960035000c00d110f00310300d019021030100001e2031140c4010030b094010300d246900c00301004104001341f52402100303210007940010364070740c00803400100c22581d4031510b02140150260740c00d0b02001c5892560110200411504580d01900c0e18000a1000a0082d810 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 158681843 1250 158680593 158680603
    0x80109150b010f020304031e120f03110f040e22030906090806040b07120605033003090d050703090509070c03021c0f0f0302041d04020a060203030c090409020127090c02 74
    0x42040185c0c0f0600040c0080b500484881420b40c400814001901d8101d584000d004142200301d8004a8400c1084055454050040d80c0d01130384540f00c0c2078a8509041080360840c0074034001d000712003240d08001403400240700c20b4050381c41e03460310070300c2020541c2b8500186001014029900010344c5030340d00141040001800c1801183d01c049143d1142da240581251a240c401428000954840000040d01e49092012444003002075408a407c5151046034008561111800c90801b410405c108000c01c800842d0025907100350f460b009581d0b000b00e04027162030300702c10303000143d00c503070480140000190014484054a8425001c0e64040d5481d8185880002050024000800c103140000c000c0e642c440c0b0541ca140382424140141001e40398540e101c1d4801440c40700c0e900c41001541448107618180015a0007495144000c46c51403501d51f4006246001d000e440c640620f490f40c07400b10031680101400030800c03481c400040c00f808408040b00039440e40c4e612940e00d0b45481c0c120080b150b2480810 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 158683093 1250 158681843 158681867
    0x3010815040809010318170310061403010e0601110102030c04090f020903070312031e050912130302040b0a0314101503050718020c0a05030406020d05091c0606080109150b01 76
    0xc081c9007071441190041d40640405820f02c001d40400446c0c420000b81d16018403c4030200d4010308507104c2c81c0080c00c100903214980c204106010b0110040c03d800301c4003030201c905503400c100025056071560b20060700d0844032850825215400881003052506001c4050320865469a03814049001b55000540c101e03c1000121501504041c0c418000b041c6072640382d1070307004000d103000242001c102201407491805d8112001000e034a55041c0200401b080003211100c4542042e1079261170700070580c181d20081176103c0280100d0326208502240e0b5034480b40540210342103484068090000d0381903640340d0721201008012075161030314580c800046020044162548400100105070070a0402d0f503080800300001105560204050310328010705001300066544684000c4d80c8890820f10701038140b200f401221001c200050114191a56464004494903802100740100186103400c0c807001800040c1c11521166090442c90030402c03c0098062158601703181c005c00075008000011985140c07860 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 158684343 1250 158683093 158683103
    0x1e080f120106091508060f100e030606060310060305041b0803070224090d0501060504061701060902120a090318060914040b060304031b0c0f140f061c0906110301081504 74
    0x2030040e03413020300400340a074100030300800200c0d94028003400621544c01c21160341c80080c458440e41403060404000050301b0200440b045d5041d0b14046400d0b18503040c0da88100801c040c5ca91000c1010f0101d43c0800b07065002040c082c0f4000c0b59120151203550b0351019a04901400080b0301d0a0301e681d1414000020360107078503103510700e400a00c8041180300540c444080c1c0d041e5594500024107903640f03128020041c0b8403c00d04954401e12513060502312740195000d20b01c0e0b1030041040d00340700c410385031006074044664a40028605407500b012903108040025910b410043d404002c0750385038010040c7e41c1150540c4001001c14a541d6042c4800d640120351001e41040041c00402e0010340600e4498141781140703d00d5008110490316185200308450b404428200007190040c42003514410344405004000c0e242d407100d45081101143d00c0d441341c42c8010050788800a0a52100350542d00040798194200006000b00c070f0542060701c000c1c1e0b000784520070140c45003001003465075056080a603c600e400ca = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 158685593 1250 158684343 158684369
    0x703030509040c2d08090f06040807030c0c06030501140a030b0f190207030503240a060f09050303030a021308060f011514120403031d06041e080f12010609 68
    0x40c0502000c2d015544804044c00300210ba0031225400e43c09050020195a030a90040d11580c458003a0401c01e01502e1444c0c150401001c00d00520310004090b034015500071038541d038820440c00c6c200e03426140140b000784100e12002c0001486039260308041e044c0d500102454890812200c20030002c6005480005e02d0a8405000922841341d0038a10960085101d503070700c004040c2a0502500b2a031110000b100070800100502c410784d0700d0501658000410f0079020156540070200081e008086072041d10b0400c00c1c4002008042885080c1510041501038201c94a13070810480c018048d401c03407074412030b84160304040007c3c03800001031498060764010124110503401c0031214580700084241100c10710010000f5a4010801c0c100180003504050110080358240380ca402015109004042d800c5083c1002d0910100c14002c2280340e040383d8040c03042501100e412584824605e411500503002200c08a0240840038112008000740c4200e0409101e007070303032030380400d0f1511000c0340540840c1401c0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 158686843 1250 158685593 158685607
    0x50f030d14030c070b070306260307060b0102100c090504110f070609030302040b0f030a050f0105010e1306150c060c0212040e07031d010204031a0603061b130608010e060307030305 79
    0x40780009641012201c2440752502d00c1d503440b02c900f00c00d400d5400c4000256039103c108201c1c0d8021200340810a20301d41151038000084d10074598038001c041024011680d15110302e403550380208028404003042520501c45c00f60445000380000c201481414015818041d1610b12050300c1421500010305c0c6003132013406c201107600c07510000e0820190403414903900304008102d40100070050038580c40300310f510b1a980d182c01035924044c0d0f00702034407076810720005400500480c3c0c1c005048a000c610296205400d02080505c0c08000d841b00768000d800010b00d9401d0340041a0340208031700140790180200740084000050200e1b40c0b032214030419103480000380030070700440410f1341d08250032185504d0041581c400500000003000142c6040d1440d6030f41c0094100f0410490910300000450031035074044007880d1003800b294039820000c10855902445407a04c08610310328005444800b4407144480d034083e078070f031075010740b4140d4207010380340c5200c070817000041191500240c50020349500d5901c9900b4022 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 158688093 1250 158686843 158686877
    0x2010513021005030901020c011b020f06060112150b0c0f0d0c02030601120813060905010905040603110603070203040b0c0102030406050c0304050a0809062106010818030a0c0f02040c0801050f030d 86
    0x101901c1505d02d95001c12401042480901031500400010204221052a010303000b0303107014001025440143c0000040103a81d0f0f03004400360010030103146001c200c140b00c200c0c4100d001100d98000c021125000f0a002040c1c00d0000340c0e60010408920071a01020f5141d6000c5e2070580f00035200950642c8101c0c0184038480b810090110854860b03c50941007190b4980c040a40200b180c002000084100300d0420496900c0860900204829030781040240c0c1151200d6058a0300011824081c820000100d4106403081080742c004104071009652a034460361101400303075005581c03da520b40d0602020030714101000d02124001e983c000010b0002c2c94580c0c1d103205654012141c016480b00c400e100c4004c440a101071090001030290501340c4142c03401800150040501805054400003000e40030380c0b460900000301c0343c481240781043d81e0710f10b04503d4442c070300c11b19141000390040e04004252844542001c2e1990580d0401ca8040c44035905030400d03d07665031556082c903400581d1000741182100 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 158689343 1250 158688093 158688097
    0x6031113091107060915050c121305070e2404060e040201030903110d03020d0c080705430b01060e0604091a0910090b0303130618030b01140102010513021005 69
    0x140070310220b18100402500c40908a543d056400c0d10038145a20340e410004240e03104c0d07503910080300c045440c00c0c1034403020b003280c0056000703021001d8081c0b0410f0a4082c040100007000040445600829079031912200300718078035000554121850342d404401d0501c0707180c076014034002c2c0c501508064a5070341c1c441e001100a003415400c10380c2448403100c0d006685020a00115850411503240035987c3c5a076642000101e99003440701c0020004518203200b81568810126020203941d4448107690740c0e407580c407810079020400f01083c451820300190b0b12f903806418518548407800b80840c10000d03a41c5c1c3c4029110103407017801c140e90003241040240000d20607a0301089032800b02c071100f42c0642c0343c6007020078801807080e00c11100c00030708000201b00c0710041c1d005003003403380d055028508103159603400d010303040410b00a080510001990307507080103441c61251402150003820300c1c4242e5030744407214010814103030b40d03580c01542010000b40c4d104004c400c2c12180c0c4e5502400103d0800a1440c040300c00b5 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 158690593 1250 158689343 158689361
    0x4030c030302090d0b0a270b01030308100b160b090a08030a0c020109060e070305071401050a20011407030609060506030103031b081810030e1f110d05010603111309 72
    0x1300d0700390b09000340415078150000f4424482650300140310b1a030240345a07845022221004088810b17440040005800d900318141101d925042031503154030303104070401c0c00d2401500010b140d841c1c04500741d40c40489004800c08001d00405080d8425220500f040340c440150100160841c2c00400103c0c140c02d40c1940198107012003031000081c00043c95440e40107640d80e01001402c9584102c00c01d209103e018481c100050088e11000c40381044040c00190160103800008020f02005164900c9060b680c120003500d041c21081c000c00036003460158246114000f0344159001900c4c181e000703c1c03109224071404c016584000c1030141568a1a90b040b5440e4203811044448020854204400124180c0c0581000900c50072401540011942480100074040703030f10104042c02d003a804124403102003160f2031219891400c02e440e01d815940c1406c06880002c1c4c40e4080e144002445100c001829404141a11110340e003d120b014035610301500c4034003a1035103d40602480c01001c10074014103a2000f440 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 158691843 1250 158690593 158690599
    0xf12020115032006041205060606032203111005041101030b01090314030f0301080a20090a050402120f0f010f06031a130f080a030b060307020d0e0d120903050c040504030c03030209 79
    0x100c41010100d40550403903803046d5002d04903954200d0401c8028440c00c0ea21030019a6001d080d85854a410340030441800b00d000f40d4007144500f5481810320a0700c3c1c940e03046000c10215061410610700070710051030112800d503100f03400c500210140d0b42c802c2c0542090080705940791041c140c2107442d055101c0701007e130440302c0d0348010001540c0c040f402d50040d600038915000980b19411103820024070408080c00d20b500045550700d051200c0303540c2c40030000c0d00031300d10b003030001100e0740e0314804074072808211105060b261150b0f04204100c04000501c40c941540620700901c11030f40a80036001c15103040d80001016000044480440c211504100980c001d42404014855001d5615021032010401c03030140c4c2d0840c0b00241009848be00344c0140c1e500e0a10646c1d41c0c81c903519100000a4a441e401a41002041802c01f140940c43c2e8541e2488400c00fa003000445040c540300c5e500140c000300d1540b0044865000d585285038441c5002c0c45031501c201c1d01901c603502a250180e900301d0096100001d6298 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 158693093 1250 158691843 158691893
    0x1090f320901060504031a071418040203100f0e091507032301090c0806090106030c030b030304090c0f050705030406200f010203071b02150c0307050a0f1202011503 72
    0x31103a40c4000d5914001d00c0e884c3c540366030351802c600344018201384441080d1200824501481401d691002d085000e840c0200c921949401d004404005a0310000e201c00d94020300100610510056810081e0101e4aa9041040c1403a44e41c040480c81d844044407402d0031501701d03c3d601d440b01841d110040d54080c0691070000741e00d0350844d1107000001542d1041d041441c1c071050051000b450240b154240c000001e0904a0b580e26010340000d01c000014000da20400d5100d0798031030b0380b0307a000703070001d9001300e4004050f26200c0c1d4980030000b0003043e802a00c040068003c0401180ca10700840442d404940c1000c0518900350402406542407940d0400300e003044c024010104010350014404500c03082d04020001d6568180b40d400180300b242d0726a120f0070b2822400341d9400060344c6410507071034003101030b25026489900150049056000e68500901140243c103103035020400050506009140308050750000c41a0f80b09080b400c0381d540d40703e0b151050215400520118008940c0901c24001e80d5100103 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 158694343 1250 158693093 158693189
    0x3030a02090d050a120806030606030c01030b030a0b0406022d0a0f090308030f0624070f0201090e09030d050705041421070e1008190305031b0301031101090f 69
    0x1d8a05600365605445d0b200307204d184004503690040c2255005201100100300c070f07041c084006600c54000e03a4520781810b954441d8114a61424482d001710150419502070540ca8079040582c0070394043d0590115a840107030f20300f0304400040346101d204284608a160070200030001c10b0302c080c07e541850748144203080000000082c03086000713512a1071070440c0500b090615130306001181c3c0608440300724001c8143c0310342d4100c00c070340c000359420543c001d1650504403030240016200b00d0b4142e08004084c6c58084100505200004020200544807441c1003081c2d944054040b6100d0107103010f0084c11281c09100041c0c0d5151140c0300703500003907240151031511a0202d003190701c2d214569000d0003440e980d8408015516102e0800c8200a210000160801400c1c02c000c4d00c0f444440403c0003014400c012020466580141406112400341181040e42d40d50f10303800d291070807541c0e4050090009119110200c0d55030050b801c1d81c0100c0b544150407010806078074002c074544803105c5d5007901014036500d80070 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 158695593 1250 158694343 158694353
    0x9030313060b040902121b06030613051305151006031109010f12020d0c18060509060304080f04090f1b2c09010e0f0109051003120c12031e0e03030a02090d 68
    0x10701d1b04244100d001704141c5030010850456808194507181c442c0b0005e00400c90180c17a4a40720440c0304c0c2c0052400640760f076440070788490019030300b240906140f16052514140c0300000c5441070084480004d40346074030f0750304c00f03084003624418041020020414090008994080d100c00840071080e42054040e8038002ca0030740041380c001865200510b515400041c0c91560480c0380f60f0060322040030000f80781400d01780040c0c16481107544c05070240100000240138001d2800950f8001842c3e44041ea903034070703501d40044019160078800c4208a901e0031034403141002d0000c01010346105282c0740d01c66032046a6581c402000c0600da030029203140da81c402041e00b0342d140c4003507074064a11004ca8072610f0170420110500500141c1201400030303d014180f154201c0d0980e6408100c9138000136a81d140d50b5000011103420780700c034400400e050608401c0469090301a0000081d20322500031503c0140004100d44003501c80001c49010107400400116030303a00840d40080080c0c01000d0481b40703000c0030781c0e590 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 158696843 1250 158695593 158695609
    0x901030b09091c0e1c14010501080d03060b09090a0c050403080403120f02071a1614010518010207080702040209060405120604050607030501050603270d0507020909030313060b040902 80
    0x12440b1240c206000e42c088015600c071000c0c10b164010314181120901090200d0f445a81a0030f40c203000e00441103462080000741507482c25070038000c4000340700e55652211003039a150704406481e070210b410f1400101d0961041c4050b00c1c01203000511101d025150a00208002d080e801300c00420030808120200101307411600410043d845030021000103051030390300515800703001e0a000d00310f4010a0302007144c503000300c5000542041d001d03091076a90700ca20b18091000100d000b80107007452110300c030070340450780e065201c4d030703c01c0845c5103da01013001c45d40b40c168200c0c8503014005212403020b00000016050a070701070000f881005c0d1182d0f2030030381c90b440051009410142032080c0c96100d042000200031090015540103560350505101d01c1d4140306c0000d4080c00014403140700c00c84a030000c41c48990708940004d2a200b641025210004010701c00100a03074030440003030303000710080d0010030412000041243c1c880c0d040c9403042102883caa90718070003d01250750303440d075000b5210100c10b0003590301d041f0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 158698093 1250 158696843 158696851
    0x6030309060708070c0501090b0a0806031005040f0203150106021b0307030b04081b01420605040509100609050d06060f17100b0102250807030503030f0c040f0b0901030b09 75
    0x40aa80300c0704d80785030004120915402072810444046410020034101000341c03040c0c03080030300340f50200351f5402000c2071038070445081d0a0003207420700b0140001e2020080c2e800c942140203a065481703810724000e450480c0c0400f8802d0400582c0160329800e5010215039840703517104030003011790b68166502c4d16581121101958140d56425000031001103500a8242035840120480c00074001d441141060249211660804150000202951040c84040c03544601118039488402690007611020000e01d140c000780034840c080e00c1e810010882d6420340c07006100803030b10142d4a8210300c5091070240190869510011070f900c42e216240230540120500ea407502400c6034409503440615240c012a141078101c25001224520f4107a015051346d81c01704120320f1150f10744121640c0d0551258110400c048254400051401260300100404c0001b0000790700580311210449465280d04c21101d082d481184580040c241d28400100400b5202c20080c0000760f03414140003070b441010a001c5004208111 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 158699343 1250 158698093 158698103
    0x9030a0308100906030c05130e0607020f0c010e030d0e010216060806130c02060c0c03070609060506040c140a080a0209030604060b010f020c0a0b0306120a030923090f060303090607 79
    0x1c41001080581c08451030018060540140301e10b40c650748514080d10b40e20b0080c0e130f0007504017580c2108000e00380e1b04401c0d02041d0b0a000c0fa10189002c0000a4680c0103403034126000b800780c10b082c00d18940c416203090300034a0005010303118030780b141d25094400b1480f500000341580644002e4420000b05400c3c40ba0080900c1d840c0d50342d040c1341c00303010000f4805400481c03028440c82c00a081c816590f002403810b60181c800d5500c0da58a4001e00041071950042c10401032441c3c0c140584031003008019001240101401d860070702c0b03040c00600742900d07500d00c1082d207008059418054030581c944503410090300020300440c010716024922000c60b0900c07a0803542580c10a4031001d6030902960b0203c1c0f5280d680362107202410714482c6040010700040c06d24071500301070070320100106540790f0b1141c82035421004520300b12200c0140600c8c001e4145d08840c440d1030703c2e851180303034070305101111300c082d034040b0600090051403d40d0764111085411000a0051900351001703001903842d45c0c0700c140041100500503 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 158700593 1250 158699343 158699357
    0xb010c0b0a0c02060a060605120604060902040311041104050303030a0203060a090515010f03060501120f020d0203010f0311030102040b09010c050c090c041a09060406120908040e0f07030c050d090809030a03 90
    0x10b000040e142c458060601c042c028903020b4100403071603021003507403804459004403180e940c4034140010041d10580d0003400310544009000403c000301c0c2c6050b8144078405603004c1c841d4044403056092180268411a40c042e0802c00004e4068442a030003540d0001c0000c00041e052034a643d1100f049442c01c841001440003080000b42d070568001d45408021020303440c081c043c03d401d000001f410080c0300e01880c0380b40350b21200700032100f40c07041e0141c036650761002d0404c54403980d442c2c20100d203140c101d20099402c0d1144079000106802c040c001c84041d502400411858403401d00d00450321b002686600b65000e020381c00c00d4800a81d00c2c059880c1c0100164100360303840718203000b4054982c0104c415068500700007001800d0580e2108419a4200c501030f062280c080300c42d0302508009000490001082c90b0000100403c0704140000194010320040b01d00c561301350ba5102095007101e000924640c0481d0b8140208243d91134140c11510825114007901e605004043c004280b4018211004030302150301 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 158701843 1250 158700593 158700611
    0x3031b080a030c120c14070f120c0314070812090f2d0f071205030d290423060d210e0907080411060c101a220b010c0b0a 53
    0x2021292113040103c25504110140c0c1180c400f5240b40c40704d074980d40902d8400302d5208148550300c1290084650460a40c00305c0f1700203183c1c014402103090100301c0109203440002d6034460410802d5494030b0f68004941c41c0340415815415000d00030041000b400c82c45800500480702d4403c3c4040c038071100e0003807411881000b030354403440e126110102d01a10964015810154450000180a011078141d10013a1000c0099800c0c0782c1e081d4403412555444c181c0c1844107004500d400f51020380c0444103500c4441c019100d21004110582e111404401d12001c461440c800c0c0d01240c005106802000003000c80c910800700d0b07500c24800704850300e10300c0442240042603a46240e049004c00e950400101c0e59083c0b00d10348000003070b10100003d080540b450b41161019000340c1c42d80c0c01201c0140c8440d1040f5801d03410640041000b4100030a1281d0046400d0840c0c915142001030040c8504000384001c88111903c6c0e003a40fa00030f025403003071981001103040390500031507280f04040d030040c401c2d041c001c952441 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 158703093 1250 158701843 158701847
    0x1212050702061c060f1a030f07020c0d0c1d011212230702040f02270d0206030f041103030a0c08030c070804030f050105010812040306150e09031308030406020703031b080a030c 77
    0x5c0540c4c00354030007401c0100c405504101c1a800c89500c008242c098400c15142e040381280b40c00030007215550400c108a82d840c0a00c101c00000341d0464080700200c0c8403d02502807500f0100f1002e206003801c0d4066503506200041c1c60202c9003000310304501d0006050062032044014281da180945450440001103980542c1010b00400c1b8108500c0f4009600e480301c0d0301e1030300720030381d001030b0b522140c000003001428821b60300d13a28200750b040d07001400140c4904250102781100501603400329840361a1040901d01400d002c000d443c140700c41a269800c44a00c181c68060309a840100058820b030b40c00c004850000710050042c10265002c3e400b40b180003100d6242490840f8030607000394030a03600c04003594084000c0c0f0400c49080d0ba030300c04404150b0900803a500c01e080c80035508140009006002040001000000600107035207090340c0e41b40240c1c0c0c0e20396045882c0e1295002c1d40e00160806c550910100c1d0040c0e0804200c15007212502c0c0c106a4107454118040d0016004100040c0d100c40035001016 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 158704343 1250 158703093 158703119
    0x70203010f0b030c0d05031207031e1a120106050319050d080f0604020f0705120c010b091611100903050d050a0b030d030c0e06031e011212050702061c06 67
    0x92541c600801108041400084d500d4044480c054411010708400c171041080c2401682c100c411544040b6100e81030103040075001d0700740303004000840004c00d0600c40b02e454550080d0082c5203081d01b429800800d01c0e10500c00c50310ba00252200d000c0d9242c1200050b551810001181400a1b00c8031991411451349003850030803105455800030405a10203022800d02208101504210211001a5030344c4151020240601a80a001d00140284c0d24010f13200314030b00004010100b0301000811a0440410820030314031400d440c0c3e954811100083c204116001307050b040c0020045008465810308040c4032030f41690500902100018004101c012107180da500406421006000060220000c1c0b4000310355a200c00c21041c10805454050084580c2d0083c0912005480050451035072444e04c0c00400c00f007003c00440c0580e003c4024000004d0380c0e8610300c2410101e0b98051000d0310b86002620301180c480d0000e0301c00f0781c0c1c018810043c01400d8005d4070f01d201c81200300300130041122450507100c2e030001 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 158705593 1250 158704343 158704361
    0x3060609060e060a121a040f060e060f0102010605030d030e0601050402071a1f0308030103020f060a020304030f02180414010c1e0305100308040305060906090a030e01080414060a0207020301 83
    0x40103003200e0512490390030400c0340028950035500300383c84810700700c01190403000701290300401c10b180c088508010100d01050902c0300c1c03800d0f1400e01015150603403132011101280300d40e48101c40c108001c202c252804c546040250b0342d0520000c900c2c2a1500e00003420100038100c06c00100f0341d10b00c50740d0b604490501c2083c1c01020112000c60030556a80c88140000548081a00303e80706030341d0004044c242d90f0880c2c01108820281a480f00c2a02c17450034440aa000380001c0c1d2141d04468400d2425140074001c807100385159a010f14202461030741e44040d4001800700403a80043ca141112403601c21a9042600c99406a000564007a2000500c182142e40704803429042080a02c4442c0702054100c4045824a8280c070300011590346403050030500c1000c6800c0100341100008000061180028160740035078a040151025500c458000c642c1d550303803407035000380415016001c07030303042d90301a80e1415406806041c41141e40ca810441c070740d00300741007121000011580450108294102440380f541c003 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 158706843 1250 158705593 158705597
    0x507020d0c0b12100b071212292707020a020402030f01090c09150f02011b09060f05090d03050306030109050a0c1701021305060a02070e04060501030b0604051302040203180609060106030606 83
    0x45810054101406c0c40b0f5500040c140b0081c0c4403e011941e0b10581d0101d81e01401c1c2c1008204950082800c0003150104a0700e9024000c02c02012480b5840c15100900045030308200c08141031041001d043c1c1107100c01014001035000b003004c11005600c544c0001c5109800009102801c2e40c1030000500485141ca91420204003441406001401414261110070440c2c0c0c24004440e000000e400c82c0905814100d054010312000e844002054003c441d0400303490a5486000c04100c04a004403803501030a505240e00088124410b008a40504001d540062021780085030f02d0f00b40e80c580c20326284c0c6100c800c4800c0c0c07140c030100708004041c0780030442c821070030f480013945421203452020040c42400c5c01041d10a050000b544d01207980200300660003030111444400140c6054144400104424841514090722000000e9002e1400c1e2003007612542001c0311178001d501051f0248402500010b180081c05003004601034150302c0b04014103840f0b1802000201a07030b604206004003540c03002d92240003 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 158708093 1250 158706843 158706871
    0xe1507170a0c0c060b040b030304031a070f0507030c0c030204151a091e011b0b0604050a0c1715060412060f0e06071b060203090a0210110a030507020d0c0b12 69
    0x108960f030000701c1c0c1c41c1c550741000000c1030b020412400500202126440c003035040c0b100150010401a10402e00c0402c00424580340c40c1559a15070152010180d448030380c800940104203200c0006e000308a100000ca00072880e4514168603039002c24120703020000c460714540d40d105001c104c000c00c50581d90452401004180b81080300120214030b03c00034003a040c0c403410b00381c2c1815180701c1e445200451001d08a2245c1d0086c0400282054100c0d5801910007030f001d1410140000d5641d0010301a10100700b030b040d507440080103045401d1480151000c0c010010000340f84086005036074940b0013500103004e43c0324240d01c18000c0780ca400c1085585d03921a902c02541091031038140b0780400300d1180c0c0e10515505004035401c0611014000160a001c80206010310110901250308030010385003004c10310a071846091a02d078140156003544012440034007650003207080400191041c8043e1a4070341c07001e07140401c5a01c032540d03040d04483c030a030004140081b0100b0390f0107408440f940415007015590b01604 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 158709343 1250 158708093 158708111
    0x1204030305130f0f170114130c06080f040308060d080408010606030506180c0f160308070219151107020405040501090317060904080c0c041103090f01060b0406030e1507170a 76
    0x1302103c03009101c0c1c41101c1a02c40c1603451031010a40002c0701100101440c6141450440040d0945614284090f06c07802040d4101103000c078041c02107640103941d211122600b43c3d4940d6012950000e00070b0400d9007000e5a00026000288540050300c003420340e400c004140c45040c20401812180010951480754072144810725440c40540083d0380c108078400e17070300755541c0700e042c1043c40103104001c1000301a4040a0500317042c1540031a50302e0045509900356541c0c118404110650072040582c0038084503091007103680340c8246607100c1e449102d9040081c40c140501d680006049400c01c68050326265100c0c4603031400c05034040012061710641070100b00d89814107030082444600c004000600801e40081e0082c00380f4420801c418421000400030b1200440d00041240c19400503140924103200c0c4d14900d5400c00018000c45090b1401160851305040c0b0340182240580000e980f001e603540039005814004c0402e41e0741c0c0903c90f4400f610b5040d580981e0810f09298841c00515202000d031a010f215 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 158710593 1250 158709343 158709359
    0xc06091505041511120d0c0329041503140d080c16030e040621020f01090e0606070c0b030c0403020a0501030c230c07030b0a050105031f09051204030305130f 69
    0x1d881c50b100780c944004440414081340d482e000c00c00040060986000c55000856a000c1d013191080d6082d6a0302400344d10b0f1108480c6111445802c0006c1d604400c1d03480c0329095007003d5000b1001c100d8201c2c800c0003d240d0300d854400e0010008bd80c41d003216000f0345005002d4039004031440c0c0d04185516001c034500b40c1c0f01c4104602480c218100241080400b210b400d4a40d580c540000700a4021400600e111092003207140c0003150710040201e0140c0707846000030791203601a1501c0310440b106030325003d5043d0707509010000190b2140104507141e00010300040b071400c292002139846441e031291295a100c4c03c0d401000900180c03a84020304060525050040c1c0316803010402e5500fa0803c482d450b074480c9009040c2415015020040d0047d01c1800c00020910108028030ba00420500c40c040200e030340c880003855110303201801d02e0310030000010550b61148082c2d90140013801e000300140c9140a100b80c0e58000306502941c016400282e000c68668850700c001d50340700b4000c0203070300d1ba50700d5454034003442c5c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 158711843 1250 158710593 158710619
    0x1d030f030403050d0615050c07231c060204120c09090c0b03090f0d030f061707030206031e010e06090a0605010e0d0303020f070602041502010507020c09090a0c0609150504 75
    0x700804001d0702280c41941c140c441e40103240035144481c0d0041c40307a00c140360001e215800c03011040d4100c0c13050040020310f50990b02a14059401440c4107103500a41600074403446005420104901003100594100070071405c0c4050000792444208121111005041c081c02c9250a500b00111083ca00b030b46240000b0204d500a9048034000e41c401500c9a540001d403506012589403100807038011560502c0e1540d034151f0001322072461014003044040e0310b8580ac4111072240301c00040c0d403075106000501c0580782c00c4003d554410004c2e00d00030490807200c45034944070b041c284c0c4840c03500412a0b0500000d40340040400d64404c8034610204855450700f000242002d00714a0074030700888541d0b0540c400c1c148250102c0d00c0028402d4102a0f5401046c40c2c141c0003944240306801000381543e074001d40341d07403042c006c0c0c40c000c0606900070400c140c102c208100308078030f014108407950311030341e0f207813400003040c40e80580028902c544a840e0032503d8070070307110010f411140031031003008402c11061110644500f0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 158713093 1250 158711843 158711851
    0xf0a030f0e0a030303050105012c01032406080601200601180908030c0406030e0d05040506030c09030a060506130e120a05040e0405011e090305070b1512011d030f03 72
    0x161030040c40d20840e000360362809440700066002904260040141134041c0c103e24100c0c1c00a907030f003a0002c03131418019103608800e03185140c140c2d03902c42d010385070640c441d8028260788004048a50501540c0a072020894005603100b480400c024500b04003241da00000f07001c06102d080144802c01c3c541060816865401c1401510b40c84ca400003204490a1041da20a03410b40e44d00800455503401e01c203600030043d402510941001a0410590200310080402d443c1d030030b220070b0f03201e0905003400d00c000c000d01c80e0001050300e8058401403060800035a0204070701a00c41c0e010751000149410200d0503c40703d400c2184a0310070345030500c0c985a4002c400001e061219500781c006440d20b07580c0c0000c085039507220f6030b032184001c084102c0034442070000640c040044803070005400404034944441c03030010788220700f00c09004500b0070b104400100d10b55804c07481e88415800c3c0d4100070040038000250310a8104901c0c0c0c1c2640e9134540c0d0304d0b405c042d42c01034035520801050740107505105e4034450540d0544030084c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 158714343 1250 158713093 158713097
    0x90e0a050c160b04051e031602030a0c0b070201030f0509070302060d0b040507050c0714090105010c02011101020a11010506090906061c050718050709080d0c020d021c0210020f0a03 79
    0x1034000c40c0c4600545016020001c1c2e005400300e40e9040a02e01020107a03829038640c0100b9084015021042c00b6540c0d6483c0d400c00170b181061208419400e1060b0104026a09405035004000000d040340c841040602030414503103482c0c0100380001821148122048a00c0c03a2500007030044140e4000b800740210307031341100d0b8180d8a00943e010302e4041d200040130f003904541090b091002c0c2c16001005091013441010449041650792524108102011000d81d6000103d080c0180000c3d4402c010400749140107040c0000e030b00c02c103680e4150880c0d120450140002c0c9420b58130619403c428058690010802c8980c20a58284488050307240c01000c4d011920540448c1c5032104480d407040150212507800100759024a03a03030302081140341c400d001a50041c00d16000005044602039010a030541761904020a000c0180f180103482e0250821010782c0c1c01002d20941c800180d481201200c0e552080300102c41400c5058414000c5160300c6d0b92240c41950011894100240c00c002a4040c02c0c0d030700340c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 158715593 1250 158714343 158714351
    0x6131e1a01150315031e080912030307140a0e0630100806010e01050405060a030804080a0b060907120e010b0a03080405040c05040b2b0c0e030f03090612060604080f060601020d090e0a 80
    0x741f600d04114484c0540c0281c2080303080b202c4004142011014612480036901c50301804d5605c81d643d40320f01d1003030501c0b840c01306040f83d1611845040c008084c01e4a440200da80c0241007492440003c060149800020094a80001008002091220001d009141541c02080a54180903440c000390b101400b540d4010b80e035600002e0300740d030384410501004580018100da652500c0b40540740e00e8a621440950307000311514086080f9040c40d5041d24480c401958400c0f180041090390034020788580b0100140541d220b101440da50380c1c403102010f00440c440d194607562a450081403005485003c242202800000d00c0108079072070225084401c0f0995803940030301442ea0150b60020072220f14010030001500e45003030345c0c40154005031000c070300c1041142142c0100941030b000c90b80d644128100982c020304144420311540c04e103041e2103500444028012814a034441405070324106410301c0b8a01c4d2a40400248800d55806118280403c0c0d05d03460030a82c01ca080102200c40c0c410040d000c1d80c0007036a0707 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 158716843 1250 158715593 158715653
    0xb030f0d08181606020a031b080904151a0c060106020c060406050702010207180f0e0d0f0e0409050d171501050a0e0d060f0605010206131e1a0115031503 67
    0x280022034015840c0803650040d0f60315060f000795242504002113000c6040d82c0003165007400c0c24048071410541c0014562701d000d071010148006007081c2c0d100c1c01c2c41001e0822003c1502c0d460b1489003990020002e41c0151191028521603280c001d040c0c1c440c0c0c00750b4100e00c4036402240c0700c0c0d1044505803801410525510051480102d1505007194481804a581d103940820400300540000503100c046840a000540100070180e07144e200c00d1a0b0040402d811982070165540500707400a80007100600000d0702500980f030b03c90400d031850b1107102c000785c40e005c940041c0011544905030440c0c0702c4220400010007200010303082c3e2140d070880744d003404001c2400000342da070b400b052040900d602940511080400c05440d40c00b401c010b0180364090f0196000040302501004482610301e600301c10300084201010035a20b140300f580c640c060340c2541041c0140448511042c14040c000c045144c004016110382c010300904489429884c1040048102410004036240904d00414044110349201c2030340c403 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 158718093 1250 158716843 158716891
    0x1050d080304151104061706060307030905011b020a12110a03030906021b030927060d05030c010c020616020c100806010908010908070309060512010b0714030d0b030f0d08 75
    0x2c16004800d0b00241000341590804c075a4002400c100d454a450b103015580b039000b14041200b80498816402282c1403000801725842500603800c0d16016000015405204140400100c00c00405c80030150b8041d040c4030080006910450a90038258645000c26482c402ca51940b80c1c040070702c0c00340c10140c4074481202400150f42c1181c90f00d80a903260045100d189541e5142c80350800c043c02d920980148a4540801d92103210f9000805200703019a40306a03079200812504010252050396a03110078400e080c1ca1000900c40d000038072280c0d4004040c0d40c6010510002c1c00f00d11201642e0071074000301c01e9500161906910b0054100e110300f0310080390360302e040c01241c445045030301c1060190300340a81c0e402401016002040c42038080d640f040d00360740d150001076405110b0b200900382581404401002a840801c000c0c3c100d00d48249442884000b0103480c451845d0003c184005a966444500400301c0c03808014182c181030b0b010300984506003102070041c2130524020a0660038400ba41c20400000c0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 158719343 1250 158718093 158718113
    0x1809011406180d05070302010206070207050d290a02090901090c05120601140a08100509010602150402011202120603100b0f040b0f04020c060a0c0e0a050d0609080c0f060c0301050d080304 82
    0xc8001d4400703c09403600f400c1541d038071800d40c13209074054091403020484081c404240c400944030702034170b0709030b2995073385e52a4100b04640044100d0402d48a020700c2e041d40c40340d558420300501c2c0c6904003580310040501004941801a4440d0303c1d05131800e00051007040d000f5047da00380c00c01d02040b4440e95030301d030f01c0180c0d103012501c20681001500021070031076641c4c0200c1440d015018050041002a403980244150740100f070007404007691000300c240996a581a921a5200b4811f1410800442000c4404410790b005070030700c060790f503035444104500303410f0402c40c1041c040c145141c2030100d4060070001c9070800c0c015a03480c0f03004544960311440107032142c050b801c4200300060300843d550105901c0c05606d450040e44d081d110342e42440114500c407032040c10b0b440560a00100030b500b4240c40c2100300480469202000c40b00e503030312800c01c9008144410060045290081d014100c0501c0300940603081c100d0080c0000c1403220144014040c40c3c807140b800c7c555690b880622550f0740d80f50350034003c00c06 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 158720593 1250 158719343 158719387
    0x40209060d020f03192105030c0c010e0304090c080703290406152c010909020d0e100b10170103020103050c0c0610050f0618150903030f1809011406 65
    0x18802d1604c1c05d034452684502d0355500ca402410341c04071130420700c080c2c205218203541000002410078404203051561081c0102060400d0314000994018542c6602d800c5030400d1344514000c0d42d032603100b226003d4005007041c0e40300c602c074a03082040e0035500314500550059a0004520010b81222070700581e00c0d05c0d448280500202d0354045102c0c03c0900008051411a800b04250000d800280303050324205405139031a03052050b180c040c01c041c10071315484000c1d008004510317501500e41e44980c1d00600d050054400000300084042882d0400d4000d00010204103200a400c008489505082d908911a1070380d054960920300420b894460307868604203405961034428141c0038400c2440421a407a80385c0e0400c4850a5034015207025841080118901403407070b01581c90100110607940e2450000000c4c1b0f103507076140f101c3c41d05021628000c09e00d0f641001c4106c828442001400100450668010a17040c0c0070480f2481c04540c101140c208003c9040414107000f4600841c40c07500802d640c0b1000d03100c3c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 158721843 1250 158720593 158720599
    0x50a03090609061a0904050a0b0709170d09050f0f13061e090c030212071404090908041701060602030f0a0e04050703020d051f03030e12010c05040f0e040209060d020f 73
    0x61002d207418540c0040050a4040050007100300d0560700b00d09042d88401e201d01e412034050114032000d40c540c045844030041c1800c04008000e00c020421852141d90080c0790005031000301060340040320041d05045150b0805849508140f500202540d500c02c640981c010040e540000401d030b0400d10f48010745840c0c1c00c140b40204907240c40311002c0d02214400b008440345100144030b03000e03d450003a0128451886915260300407080050403260040c109500300710301a80881d441c050b50345824000f201c090300422500304000103420003c4200040700d666251200c1c0303008000c418039144019541e885216100b8070308080201d651060907009100318400501c014105000900d0100f44c010000c1d0700044101d8412860040031a2070945d0354100d01d0b0040000305400746e046411500c00361100d1140ba0080c540c007036020502e031043e2560138041d222030350034036441da50340711400d10004c1c05010000e42c000c0c4031514580810070015a43d5220714a401030302c01d82c1d11a45140c950700106040c00104620290 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 158723093 1250 158721843 158721851
    0xd0507090e0d080a05010b03241201090b0609070203041e0f03080d0c030b130b0d0c03030201091406091207050109050a03050409060b040b0f09030f0703030801091119050a030906 78
    0x52581e4020840c203101803016aa604903940c2e071a80c400c1c040711020300660816482c01e0000031419401068450307002d0800f44545407030081c024002908600c28040000216511402080100010034107640d400c0341046132036900c2c078a8011402541c0780254892600b101d04900c0c24699646180074146001e80174030624031001580b80d082042007903011074010b41c3e000d0303d07000b00305100354460300c00c10f840c841d4000c02c400c0032400d9240282010313001801c1c244e6441038440710300ca0001240c2230303100d9005510a40009c01c201c400c9041c00c45025165004010041d04684100010f02c034001c03c801c280080c81100d165100c0f580e504040e8010700051358010814801c4002c00d80c1490b4101020f0001c5414602c2e052049a0b00e6015000c070502442c81075a00055003842076254a040c0d80015104009029040f200f10007418150980780290384e500c140c000c1584840144203512080c02648600001c14000c18a4810a401c03800b05414159148d0f00030401d003c55602c40007480ba400040b036091300400240 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 158724343 1250 158723093 158723111
    0x3030601030b0a0e0405010606090b091e1c06140106050f03040b04030512040b060306090109020a0e0a0b030d1d011115071110020d06060801081e0a020907030c020609010501140d050709 81
    0x87c02802d4900550000c40c0c0345400005822901a045403100c40015298624015131040700c00307208003805646a40c801c0458a9070700f01b03143d581d07107a4082c1a000380c3c80429406402da951860460060308150101f00080100c0460441c001040701e030481d03805a01800c031a6a0790500303c5140c011541d40c0724038841a4020320040c1315904045502805086066039119251103211508803200500b0080d00311202040030403058000d04182c550115801c10003148102070280040e041151868550011a1150f030500c484080310011601e095442803c0081d407400300d41800e00d40c0d800815000b6007040000a000811061103543c811480e0100142107132010141002101d010f50008400707030039054580240007420b1072003518094101c84101000e0304105183c0140c143c0c0c11044030420b59468480ca2641c1d10050b240c006000f07100c1c03078490350000750700c142e1020002c0c1400e0000e0024045a8184001401440400030007001147c4040b12001d100070414a4180d061600d1a40803c882500d403100207 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 158725593 1250 158724343 158724353
    0x204030b070206090601060810030b0a0b04060312090509010e010b030403031b0e1207030317040804031e1e0201080c09030c15040f380d1d0d1103030601030b0a0e04 72
    0x1980a0b13000341066034070f030b40c1c1c0f07070041200c0300784044070302440c0a45141ca0820104000090140e00720b41c1c11000840e1101c0030001190984465600840d040c403407a150107140380e0780c0000c145001e0503080340c039201c3c0c0e9450040684450941030040e000f44541c00004030f02094040e85c09410300419000c14614030512490015000c1d03804016024050142c07450801c140e0100403035020156036058a43c4d814038200c0c40040f04007030200810880b0800c104200210200d49885014110280c00380c000080e00f410b10701c2d12180171147c0c5c5480204444a0140040050703070413002c41030b0f028003906000c50302c4600c210006880d000c00003500070b41201c5010f00c2030035048a81e10040c0140c401d2100081d112541da044840891400c4242254050360501c0760111031042c0020b41c0500c09104d204410305241089901a0458075a000b882e01c400c40c2c3c9102c600cad2004400e11840c41c4145507407c01c80719000681f64a0b03510781c40000c003160304241d0b03107081402ea540e40c4e4146c03c0028182d4041400341ca89410320b00 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 158726843 1250 158725593 158725603
    0x90a020c0c0402030f041113111b2103060105041701090b130f0201080a060b0a0807020c03030a050904051305071e05090105030a140c15040f0509010e1501030204030b0702 75
    0x100385994041d0382030008041c00c0034000c5a000312048542d401031680e4039266640d582031040b0038550b00030540402ca144034105400341c0001848130f071083c65501c940708040c4200300c005400f01501c06401c141d50081e00d8482e4030079000c843c9110b10402c0c5940e0f81e6030700b0040b20030384030f160443c03115a80d90545044220005602c504070b450302c50f82280810381c441d000302601c0e2840c060030013800396261039440c0c0010751007085500c1d0000e00641c000705c3c02c50303120960016250071800c0d0140010b07258004124485074108480340c00120140c3c0a1031800541100003000d0344190442e07103000d25220001300b4104402441c9549080381c0080c1911076841c0c0f9007550032441e1200710b90f05000d03c0344544c004650751038211482c5040b290024018070301d0300929610000e0050103500146014050008941601e0b1500300d8600810460409165503c5040041841d00d40d416500308074080c0c4013843c0103001e40c00d01001c1c819003259054000d841ca9103940b0300120040d11550300003c000c000c04a05010045800081c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 158728093 1250 158726843 158726857
    0x1103040b010e0408030411040f020d0c0f051305221107030e06041d04031e12060815071b0f210e0303160c050a120c12020d03031109090a02 61
    0x125004059a070788030060755402c1c0039a00a02410740070408100000c1c101121946d00384c50151003c2510344014004d082203030081c2c4030f101041511b41c2412060b85500c805941d240d05503c2c140642012810091422034070a9406418014400c00b0030611901590b80488010948410000d01c40190030400c0b0321420342183e80e0440100b15030f0003e00780c0138649074095505848800d0307031b0015a1402410f05100007070001e0020780901c040441c640c003262031401e56840c1000c0c0d954862021a09502c9005020ce0307002c0d0348111496004001c120001481c2070b40d245402900c90b142c07101a002024400c0350041703036601030042000e0411340900d410800040420702480740c5c04011070281110324001904ca40c0714075031841e94190800c106003440070800080040840b40140018040a40c685002c16440400790b0001001002403c0c28031080110f0300c450a0042c2204017801c9494400c640d000c6808091101c034010103050700d0b002c640001c040d00ca41603400e03251009010b40f005061a6080000075440300ca = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 158729343 1250 158728093 158728103
    0x503071d01090204030f060b0619030221061f02070f1220010e04020d110f0d0605010c03080c03070e030a0c05150a0c06020c03090612010e18030a11030409110304 71
    0x50001942044600c2603d040701e40182c02040b4500b5150344144c01402003440041c0d009d02c052044c1d0b0094801400e441c88601c115403001039864444800401030524030100c18220a8032050402c440d5840300c041611080b1107000403400c900c449144143d04004140d080b032051500d4003180012040e50465001000a00640040c141804114490300184421403070b400d001c01d01c0d64281305a1801d01740c0c0104804503010784001408030910241c80035941c004000c11841c2403021400310080b00380f80c0326500081c0001d081421480a8030b9078007600c8810010550701018802100141c4024091200c2c2c44035018000e041e076003621254902354060f40c1c40c0b80500d40c0600d15000b40b48403581003100c102d40c5644443d455242c0c184141c3d903242e001a500c46892150140004d009580e8940c0760200903210303c0c40c120116591940c1010054003210b04000c0100c2d18032416000008203090f0040100d81058025140204408002c2d9001d107141d48500d0340070414142c0b1b01808544090005030180d800313540b01d0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 158730593 1250 158729343 158729399
    0x504110d2001020c0406030f110303070308070509040914030706060806090c15070501060f290304060207230307050105151807030f05161209031e020304050307 70
    0x10040c0300c4004168103008154140c0e504032240510001c0d80c00d105490070510496602c0a08040407030141c858680c02114842c41074508002006117201035110040e0099000314140816078034018400e01014000d50184030780002c2601c400d0312560018900c0a400880c103505c000b41d442440d6a803a40a140d0650f0309610f00390340810700c103002285413401403002c4001010526540340c01c10501c4c100038003c0144a090410610b0002003082c0a141c00401c448041190039521b0301740c0c8a990322800302d006107903914400c00101701c9415100d080c0d0b80c01c40d070411001038442c159071600e0b510310050400a00b02c051140c05601040907400001018200d104100034040c81d00c42ca6000c40e06102d520718a03a03800510602c036040141d140351110399201c552454046000441d01000b001241c5080e103001130030300e0709250201110381d00502c012040451a00c0c0c20415102c0b9a140141000c44100b50841c00d0402d154013002d449208000703032800303810b0040075035600598400e04051311141d071020031921000c0d9 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 158731843 1250 158730593 158730623
    0x80f031e0703060f21060608011508010b030a230109120e01020109020303040605221d0619091a0913030306050306040b07030c1e120506040608070513020910030504 72
    0x441e004070800c803407a00505152140c1045c0040c0c01c242406604c0440d00b41e1000c41000108030f407406a000140b000c0710001a8440b010b035800c40e01d084035900101000e83c1400700040c0191000500d03200610780010300174180f0703580680c005440101f42c143c200c1c2590300740700c0034505000402c035008203c0001c40e00e44000000182006a00b41c4003c64030203580341c1c10620040046a000e03000034440358404103009034800384040781807241c0d0301040e0425162a001d0303105401c1f0002d030b40450300750400000c40720a03005555846c001c0041f54034034090419070380d071100914446804110000c03400c00200501c0c680482c5050040418a80d20840090340002d080000019040c1008038860340619002506200c060f91800029005490101e03074480030021904014040806200307182c0070501029a110b506143e1280300e28416150041e000e00c0c4110b11f00081001011000a03c80044550607030b441c0005150391410782c0c000303000301580545c100b20b5141c0c5004195505070f000c0ba106911855041c0600c0b25 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 158733093 1250 158731843 158731847
    0xe0a0b060910050913021801060801051302090904020d03030b03031b07171b18070203070302101505040b04090204090819030b010927060b0a08090309090c07080f031e07 74
    0x30079100700d81c0c02103404008a8221400c0d4500300e801a80080c04107100240c7c00030940740c1c6500c00364404e0001507000d03c0103014620b851401c0c07107020419800290f08100240e80000e40a901c043e0000384541144040b0311304160080e0400e010030322008042d281c892840c070072000040c1c1c440c10400d800c20300507100003040803120078210710b0f03004111a000b08207005440110040304203d030200030394803a19220008a48440c10212144a50f5980d8055611408149000f038a803045070342030359030024100613880c084421010740d8201201d404031804501c1c03481c4400130500070b08048c18003940050500f0701c800140b110920040501d1440e080340d003204941030f00403c40c1100c0c10b1003c800c2c0000c20504040001d21480b00701c3c5401e19016144002900c00007110480440c1d00f01d9001520740c0e0408607200120540101c41a41d1002c80400518500030300100022b400c508028146000d0032004a541d5090207100760640311a03060004d2240c0e6a818141484030120640e040f2500084075000002078080b4 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 158734343 1250 158733093 158733121
    0x11040207030e1201060e190f020a0e01050c0f030a2a210509040c050a020f030412020f0f0d050709060f080304060822030503041205070b010506030622060807080d020615040e0a0b0609 80
    0x2b03882daa41c3ca1040032400703030044646d41d202000c0b500d028400d00c034a004a403a0184000c0c82107100703940300c0721000c0c9012581d0514494084c1c1c00314010504215061001c5160703030705801482501d0100038800342e003009a0982c2d00e40140c004054226141400001d485900b000c0100303c2c82d007094007214008015100071540e03c0c4a5401002025601503103000d005040c07686043c1e2217004018480c0003c00c212802040c2101e1400c10191043e501903801001002c1c1c0610a0001401c2074103c0095024145080c440c1c1c3c91180303124a8081111203000a80e4903a80342030444a0400c458801d0f02004080c0e00340186143c009070340a9030715415090041c1200b900420498180541c400f03034203207241c0c0c41d010400c01c19800042a10344c111005500c01007044c111444128402000340100103051801c100c0345a29000755a00300c0304499101c61440c0003400d030005032499005a4540304080d52410742c0c1e0104020349007013040061280700c2e550485003088051600544203420503640c4a02640c0c1d01100b0a00038 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 158735593 1250 158734343 158734357
    0x9110415060c030c11030a0c03060c020705060723031b0c040b030a0b0402010302040b12010801050708091c090e041202102708040f0303090311040207030e1201060e190f02 75
    0x30400340036000001901035100c4c841098010703403052400c9100c0c40c02203410301140d0f5604a0304180c41603c00d00800c1443d202d43c080720780b224030040c040720b801c00003c99001c0c412080b000e0721341f804080b4100039200781c41c03022800c0d459290050301d4442642441c542001503440b408038840e4060030401c0106801c0510a0054120000700100000401c4c0d40340c01c2c081d2400500b041e4101174007040007003050715400d4002c110b0b03502074440420041d85428005807c603a000b03000c20080152540c1401100701e000200c402c403140c1d9241c05c3c2d45481d86212029541c200503588802da881c24008100700500900c1c0240c0100d90f00c81d60241c0704c07080642131481c0100e5155208100460f138003881c49020341070145d00070ba0700003031142d00400d00d0f1580313450528800e902e003644110300050322103105004106400c115081d41c100e041d98107508107003240d580a00725044898249000c0e14500000844490003500804014016200c2502140c10044550480768500d031801c0c1c2c101d10b04040700c400c1022180c3c1300b200e17a0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 158736843 1250 158735593 158735597
    0x3070207080d05030601050c1c02160509040c210605101d010f060f03020d1401150504080d0c050c0a080d0f050711270114010e0409030807051c0911041506 68
    0x6145e03103540047d0b440e5009495102851303c641d24015107004542200a50b9443e0140c000b00103d40f00e06039500391762400c1c1c1d040b10303020b2601a42484001048010503809441001c1c8019501c080b01c00c48140c0001d80031200508160704200620295244110b003900c1540c0b80c0e0440107405503121141084082c03c00c4c4608410001c51a03010424144500240210040d152802615122590b40303810203640040018180c03410101004001c40071040003558514281c1342465400c103450034800c0c58440102034000741c00d05ca0201000000c100e07090192400c1c1c80402458100b82d01c1e00c0310500c40e6115508540100030482d1480a10401c07800340054481280e4031030400ac01018400c4240401c440384d4101c458080c01c10801c080e10301d030121210f154041d01c0c0d20203604004030390080006100c0100c07292501d0041d4a400d482801080d441034820354002140d06101e9512401008070506d49410aa800d81840b40b8050303620040068542c12032840e42002c03036007409020507200042d100010a0703c60800 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 158738093 1250 158736843 158736847
    0xa080a060e2503090f0b2707030227100f1e120812011d10050f36090105060303030702060f04020105070b070507060e070803041e030c060503070207080d05 68
    0x34245001c2c005101810940b840c001c2800342032995400030091310f11104943c805884820811484e4410300240c1100c80b40d2070750003049000002074982c50710f4182c040030340034192062031011090a581814250503042c2c4103003d0039494403541d07003038608a42e401009403c060b1040001200c0512030030700800c1c03201609468800d54605410f00c01c4214160101302e5038500d060210745405421141141c0c02440105040768140840b1130300701c80c09000091101403d5075030f8500070302564891501c2414811340945003c44845201e2803608070003441101c00320881c0350310b60303c070200701403961800324002c00040000f444030380c07030b0681056181d00003183c160300140d01290018840c2e100c2d4522907a001401030504518048903520307410881481244d00320041140000c444040120030310030344603a9155480038001050400c0901912403207075114000310001c03400b1403d0b4040300e5880c540c0c00110340c00b10070168056600da2010f07045801c21513400e80540a0b41c2000134290001240c2d009094900350348241c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 158739343 1250 158738093 158738131
    0x30e130b2206080303090303040303060501090e040303050601020a050304080312010e0402060a3005040308090a0506070e030c04090c1806030206070204110d1a10110721080a080a060e 80
    0xc000394809106140c081d488400c0099454011310096000d0500c06014694903e864280a02660050351103541080001402044070740b00c1e03003541c81d4011364036150208640d210980100e24180c0505005481e0b4007000500150084000004007002e07000c0340d40311083e80c1ea07120703026003070400b089a01a400a400f000304035007444c401c40704100449489960401c0149064500d6800816150418400039540354140010b040d00300c0155640070050f2002440c0292007651240c1d20b070400640010140420251244001d0f982840b8030800d080000d0f000300f00384029810f05d40722412840c400c9203225984154510f900c2e580d82d020742801d03a600540000d140c0300455080c40001c2100d8000049851818002030024410302c0c001d0101c3d16a40c012180c0c01182c0f100d04002002031012410030900100f007140024148000c540042100c2c0d41e41c039101400f40140b80480c0f580090031000412202d80040c002c074107079800c911080d02402d1441c404004130381c1c5411120760040d05c2502c0a66401c001c510b4070b4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 158740593 1250 158739343 158739379
    0x303030606120c0d0207050102030a0608030c071a041e0620070b0901110f010e010c09061d030102070b1609060c08090f030705040e1e0a030c15020f030103030e130b 72
    0xd242c003d10410b80503442c00d0030350140c00c0300b01d03040b100c4c0c22a01070350001309100401c4028000c00c0003808455010394030f080703e80520160344584500c244688803484c0c1704044039880003501030310000d2110703a05001d43c0240c2c10354540a01d034168011100860200300290000e0f05240c0c4d01130040104440c000c040360750802c0d500c5800c0360841d29256040001f10b001c0e90300340000600403500400c1c117410002c90500802d80f50b01c0c1c00c1d20324412180081140e000c1040061075072041c1c0200840032000000c0d1a54032390000444d000e441400c90203801091103c060051050302c40c14a400510550781e503003041e0741d071110b600b11029045c01901810610341440407060b44d28123a01100e110f84401801c031015586c1d0b46c000300f070a4450200c000181600301c92050403041c1c03a110101c82102d19048043e001480c01e50750041c10911401d1000303071805d503581d90f07401c1c180b03c120350440b02d0001b000101c81c1d440c2d41e56890001c08c0c44030400c502501800124007a000301c85141d0040d800341000051042012415460503 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 158741843 1250 158740593 158740627
    0x2070212070f0902030a110703030c2c060c032101170111090907090f0f1706010f0b070516030b010503100c0912020f06070b0f100308070f0221010203070e0303030606 73
    0x20a01b1540e6074120490a1542c000001d28a03907219481c041041800752501070301514803003025280c0b0489107545840181010a280c601c22101100c13700e45542101340c80504c1e40c014201c1000324420400a518402180c554508e4100c2d0050701070b0302c12190700189050709950000307800101a1005000141c070600c1c00c0c004c86a80700401340780c00c111555642145011401e015131005542c410198030621111014400c9900b04401050080045502d40380c2c015001c19040e1007010800207010070200c081090a014a03803083c1340a01044010603200d04000480c99000c5c40380307511a1060030024610882a4043e0440014542c1c41c3e010b00c040c80c2c000036070b04121400200300e900c0980c0c8170f44803009641e800080c11815004503500c00752850503088160761410058242c22010204010400010313448904650600d43d128000c07040c0140d8500c08207a1030750500780400306140c002032030407041c0d000540c0a94070400c4140e0304c0698111110050540780e110540c0d1064102c9400c120b403048895482e24 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 158743093 1250 158741843 158741851
    0x8010207150c2102220b090405040309090921080403140d0608030c160f03050a080d020f030a09060506010e0d062007050304090b010e0d020d0c0b0a0302070212070f090203 75
    0x4041e003c0c00744100d064042d0f50461003c5409451340031925101c5a02c00c080d000c0450800381c0d40c880200d40c2848400c41c054050045003603c91501c400c00541003510400c440d1008141142051010380c8943c980fa000305148007291003640000220a84130440c030400302c65000d0b07078050304c2c1c108803000a0100316040c0d501c1020408440ca448030720004910804000801440342400c02134a407504071135840c018902c080d94498203030340211940a00101d04082142108c00d584162a43e50301c00c061500c150280c05411064420098080304200302101690020b800fa5032103210700b00582c2e5503000064904041c50445070746c00014070307400e0000080a950217040c56400e90707034081840c0d144400700c0602560241008607420b030404601002444250701480b15004002d017440c07101010201d01054841076003c1d00030348201d18010b5403078203000c65030030b51401500d15404030755aa803944482c00b9001c1d61085404034000e581d110a407100a041c040750001c141d40701a0301c40610a03190100a101941000d0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 158744343 1250 158743093 158743097
    0x60b1504031a04031803050c190305070b0d06030c080102180a0b090411040807080a030f0e010c03031e0606090e06040911010f030e06040303061e0614210f04050708010207150c 77
    0xe030701c02030000d5000008001548204002d00303680344010280710074010560700498060272140e00510000301b0101e207032000d032848000c855484120940300314014020640c8058504918060302082004064005042d41c00700400c141b00c0c854158818411900240c1c81070780b14854046c002801d003468650054480d401d002220f580c2080d8640c0011400c10701c0c684c2c080e00c4180c0c0455444000c258106000c00c03113070103240c10014040d80d44d020020b400a080144001c0406541c1e241c400814015208040d10300c60b42c91104200090311000c0c00340580171180510081c4005200005010345054090884265404400e02448602c40001503c407402000c5481c801d044d2a098120141e60081000170301c0765002e6a00851540e2600d0064542540011310740100035070340c41014410903410000458007803501034809503a492018150f01603501c1e45007104400b10841800f401007031241c4e0102c0b6406140168280c81d141035440c01850300300d10446c080242500140b820018a0200340d0703201e000100818 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 158745593 1250 158744343 158744357
    0x601060e0d1e03080702010204052101021b160b09101b0b0c0703350c0d090602071e0b011404110304050a0507050303120c0a030612060b1504031a0403 66
    0x9965200b4002d8940301082d1410303045070350440a2550041203150041e600340000c62070541410302042610740d00c0804495072101e810446000080c00754101c401b0710b4504480700000b4925482c415440d41a4a1407003040d041c002d100200e80003042c60225541c884008154204060304c40c0d10642d8450340a90311785440050030710240700030983d07480301036100e000d81031141ea0351005d1500e400f03008005c86182000780c0040701001881441c1d0b070000c0c002010756804400d0b510560750051880c000d031090078146d810b0241804001c404025035600a80101b502c52101e00c095503c101c1d507400a078040343c1c0000752400d009040100b090305a60000350080b408060000710f075a0407071140d4080140d00c103550031203156014183c07800602c0f42c103002030009080110050b40c98001007500c0e10303d1581c400b07080b00e11381050009031600c46c075009a02040081041c9070b4000070380282800c0000081503902400c0f40100b14940b03209154107130410803a8180d0754880480310042e29400300b60a41880001c004405100341e07 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 158746843 1250 158745593 158745619
    0x807020114240d03020105060a09020301061704080c01112d040618030c120212031602010302130f0b1207020307021f0201090b0c07050c0f0108070f0c1205030a15080601060e 76
    0x1d03c0343c0300f0f4807680c001c0e00040382c0345c00c00000384827121820390b02100070248184011300849030b03c140541100d80d51100104001d4407142031080b0320f849118407000b030715843c002c00c0e1003650b2412800740a6504a1286016961040485211600d640b040340e203504030108000c24046e082c0a20703400005012041010034106840b44e4402d00003500036002080203503a81c00300c01045182090301740c400780030360102071400c060b030001d081000201c107004024185078010507020200404200f0b00402028a2000e52207525035404500f44240c5c0001c0440418101c450000707108c2c18000400c80d0070f1503501503c0f40e4000142c401500c01e40b03aa452500c1e40440d500e484e090408100c0ca010b0540c0a4003201d00311a50b2a2840d18010346843c0f10b00340b00c0c0f406208205a4480a80c0e0002003542c0d01039a6420161a030a0007a1070031121642d0081008104502000050301d1603507100010754401c151646042151a1000c0c1042f505101c40f80728070710680c1d00c10801408190310480380c40ca41e205001e03140100c0b14071 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 158748093 1250 158746843 158746849
    0xc03090a1a090f01140c070f060c0804020102061b070305180901090605010e01022a0112050a0c0806090621240a0507081005010e01140c010606080702011424 69
    0x15000c1a069164880350060100485040c00641d4030803a0f0000200207091000c004106031203401803620004000c00f0079080240190001d020038420717800350040081408410025203504416101640144034131800280c50040305080c403483e914030101800e04109942d44e0072181070344841350502940b4400111640641c840009d1035020703003d840400304400d03003000c5c001804071075080200750440d40900c9420035001e5150030307510070816011034484801102e4400580d00721483c5072503542c40614141c200649103646034410580c40c07001ea80c0f0142180c4a980070881b68601c251009075104c0d14081c051059011810340b03211803003444106071602041e0140311500318500c010010781080011200700900180300c0d00c211036100c01581065035941c108540c0c14034a25545004190511074400000340d01680580e0601408410508290f41d80361941c0c2c01080c01b0308514850480490500d1010900d007900602400c1403d108400c41104295119200c4800c4c543d1050041407580e071441d2001c00c0b96032 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 158749343 1250 158748093 158748113
    0x10f0e240f1c050c0103051f0b090102030f0301090b04050109021c151502010911060f0403060b0a0e01031415061026040507151b02010305041a01080d02010b030a0b0c03090a 76
    0xd4012400703000c4d118892000941900d2000300040d0061400032080000500c816080c075003580e00410400740c48402060050b4035500c111600c0702580e007408400041d1038102500305285070101500d0500059985400c460141c0c090312801c0c100d107844140031104142001d42c0440010a13a0004c1402c080d641c0e41c0d0b09020300b0f60035003104001230351182c501400b0701c4401d900c65400035005031446840c4c1060015001e80b14042c501009000b540c48403051000c81e561740703012a0290100c80e946044550f56450320801403807642c0608040c6028060a151074849110b420340e101c0c1102416802c2c800c901c102d0301b25000d1810340c00c0b914045400342c22280f0707d442c100c0c02c031a10079881100140b01c4035080c0410b2a00041c5104045d4080111042d8a8401c50b10150001d040d010380c28200820984c40d1882c00c0080c0022424039120051903010000500300c030000344d440854000d1350020001c5203941c03802e0644981c002c84000d0024032000300402c503c2c8070f02c3c100840d0701c00008421703a6a080d1203503440304001 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 158750593 1250 158749343 158749399
    0x100c14121809010e0103030e01050a0306051e03060603070324020d09050a05070f06090603020d0e0f030306102618030c0106060f0512070e0103090605010f0e240f 71
    0x10070074904141d1a5410400440c501604884854100d50362540d64010081c01401c1c030348504000303001c9585001c40e4040d8100300050000201903c01112059944683e02650004040e1003403080c070021414506011400400752600a4060346075103941001c5030f0f2207903507507007000c0030850390030170842802404078400c450700c0354455005001078648900303202e46041c1158100b80450041c1010400449400092042c200c944da17080140c0c40f02d071801c21000c01400c1018214006004d05040400e84000110040d403242408854a008240210304201c900d90008541da01c1c04041c1407803c0303000c0d4481845010780c4079118007129280ea07103460328440c0c2160071000b8802303156034540405201241e08682c00806500703e51410604180000081c40cac0650380280250040c0000f0211501490344250046182960405801d00c0b00c0d581d1003802c5414407a4903c03070200c10050400105040602445000c8010300e242c02d0018080c0145008100c2d004400f0f04409a21540008200c0c07280182070441c4498 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 158751843 1250 158750593 158750617
    0x30601030b010305070506030705121003080d060306060605070f0b06030307150204060e04020f0706050408090d1109070306120314210f070e030a0b0402150309060108010b100c1412 79
    0x5540f45103031183c82c00540343c02040c469282841009030706640f00041e609645050104940c050300e4100300000524440d8102a0241d4070001e000115000036030890000c0b6031161400b001070550340c0d14211490701400b407004046082800d00c60000c501c510100c0c0d90000c000409036032400c040b03a40ca03144a2510341c0800000503401113410890140c2210714461030321f80035602503113820f05540c24400706204505000b8055030366600460140b0940300c0c10b8603051708010701900b50310700072424014070700c008000200c4d114080c0b00f40081c20003403180c0268401c039011414040040105903070180c0f4006240c1d03480c14507110041c40007903405c401d00c0700c0002c3c141104001203001c4d820842d448881e06080140140107102140c543e004c4203032000a0389003142c60300403800e51801c0d1202d100103800c2c64118071903460040e00c040203005068001042a03412035034040000c01040c840102800140c840e28003984011405861241b00030921002000d1a600f1880090300d840e40305592028215030056102000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 158753093 1250 158751843 158751863
    0x809041b0305010501021207140c030d0e040608030f0a120f0f0204030b060103050c0a0302090418030206011706040302030a030b0105130b0307110102132705092103061f0e03060103 79
    0x14141d4061040601610082c40900b018040704000809a1300c500c07080208210b0111903007103245403090040d1001000c0c0203085e201450010780b8020f0074080f0312124184224905080020b007580000120342031105001025402c10031100c1e000d49590781c0c0c0d101c082c5843c0743c0b01d6850605200345032180c5514800c820070300586907415401c0c9802c02010040c9480d05140c941130502015400781020345540b01d40900d0003613a64440c0802140207805100c00341c00b494284000300104060300400c00da8166401c03d01c203c28004942d1124941d15007081d14041c01682003003111000d41ca20942240c080150103040203407911480192060341490b90361300141c000d480110502440a80c840c1d40f10903400e90410081d803c1210024402c94003100610a07404c074000480d0114151440c9101034000030818000200400e2400703400c5552119400c0c452038030301150000002c900b6400d9482620b01450b400741400030300c4244c4051540038038000758048405d00007003540200499408025042c0a14400d0764808 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 158754343 1250 158753093 158753141
    0xc020a05030a0815100e040b04020f0301080319140a1d10020c0a0504060b04091a0303030f04051203011410091a0702030f03030106020303130c031a06130605010c020607080904 77
    0x8040c5440207a40139101c0c0558050b00d01407141c0c0324600700140001240d00041c0100500002002481820507440007031401000000c1c0010022010380711020ba802c506141d2000b000c48102c42c101801c840c4491205070601c0300d00d03001403040940d03003080010311103001061300d08080099140c9086469680c0164014072403010242030800d410b0380140303c292030600c5840d0804024001034007480c0912900107aa614400505d801d4641c044524030300040d0a0381d640c0e007095104a2070602040b07074103486a00c681c03080341c00c3c07400c810011241211000c0b030f200001c0358999020480018030306032000040041220b004175a486140d009001003c2070006000d41d03800711481414201a02c030b104200f01c0360424001001030300c1d0044100c6c0d030700c400684440e200210003490284410314140d04060b040b441e801c045292244020300181d80135540440b202000d103111250008151482c80c0074681c00030b41a68610001030074014054540700b44038841c0b95081c83c0030358000c1400c560202d40200820460503002d0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 158755593 1250 158754343 158754361
    0x1c02090301060611070303081504020a021005100b07030c03020f1606081e0112050312150f040c020c060c01090f0f0c0f080d0f1806110f0105060d060c020a05030a08 72
    0x28070014003450810404d2001001c200c03541350a00e5100150900441d48002210040d04146010524400030011034455224200081d40c9040c46980390404a107007101151000d80b8190700c00080f40c4031480d6461030442c49a4081b511181128403c90a600c030b03000c8041100354041c042450740c0069400c01c09000c0c0d25141c0010070342c11010b0f0002028000510a86048051246002c0e054640340da180c14201601c40c90000c3c5184211103d90100c13800381001c1c441c08048103040e402654000b01c40f0407200100100403c01222a0204d040026030300015240b102c47c20820041d0a180444000004a81000741c030f03202a0200490403c03141c085000c0342e86810400444a40409024a820264202410310036101c2ea0344140709080c07000d000214000c2d40782c841c40703403c4003204250403000b07200791507031380b6074014010306003041403006030b8003c1080342d0032004c105210302841154020400741010f1580d071903400c010040000c07880e007140598040710002c1034003000180590420340d940d0766800c0c82c0002807 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 158756843 1250 158755593 158755601
    0x905060406140306010501350a050601020d0c02040b0d0614060301050907031e0204090602130306060603140c09030102250528021e131d010507120905031c02090301 72
    0x11060b019401c42c180d40142e520001485410b5850a0a001100c81d42103c00281026030400c5015603611400c2c1c80400214900c0d00143e01030008910240080c0e26200b00583e00c80000140c40e10000360b5a44c820340140c40d0a8201c50041e0a0107050303200f0342080d6031544800d03201200b25840c55200703240c0c180205030409128084e030001a40c4c2c05850003030708540d0b030190082c00f181101c03c0d00001c00103003007040d0340c1c880d808070030290f07031040e42159103020500c0180e042550750b100681d9018034160000038460b000e40103603001e09141c00808003099070f0711407800081e85c101ca220147c040d9801d001004074120b260001440c040c181d00b4005214001a250007403901124082440e03103441540d0824050000200001d0840d40e41110105125105012145204038a41d200b03a64801c80d0038000e0b000c00c03415a8007910188505200d00800058003810a9007030360003e03601c1c440045c404902d41e10310207440c0d40c40101582d01c00d00943e89014180b4980d4bc00d50702c90110f0360411180c1c000380d0340200c1d00d000d201e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 158758093 1250 158756843 158756849
    0x4080f0601301403090406030302061005010807020c01030e10021c051b09090402040f0606050a11010209030634030219020a02150a090503070b0408060109020f160317010905060406 79
    0x7840a0b840b02d02c0a290b03800100c0000c001824260405521202d0040c24400d4524040024204200039690b900300207540d4641565100c0e08107014080c0440c142d4400c00e00d8902c1030030349400814001c0c0e45030004400a060042510019000d564080102c9c18510b000400f910f0030780f101528180e00e42825948200c0700007420440701e880e5460350902d68000c2c020140c49400d0f00403612226190741e00d0012070041d00d52170642000141c41d01401050403034015024003a504e29075904d907071040ca001d00d0154201c0c0300741d000b41540b540c4500c0019105841ca010000d200507118641005500001700c4042c1504c81c480c04d0500220390003054000d00103518203d0710881551270f20090501d051240c02040405070130000e1781c034859800148088000340605089401004007808070347d0f6050b41c440c40e80015800c1800790b000180254800094070140358001c6e641c840c1034540c1d100340741801d640003000075034502e0710303007281844a5200c3c4c0460b20b24544980c54000c20100c13001081c24a0b0a4013000300702c41150b0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 158759343 1250 158758093 158758139
    0x5011103070c06050d150603020a17011406030403110f03030420010c030e040221090d0c030248040c020a0c03020616080a09060f0f08160504080f0601 66
    0x102080d004a0b00844506045902a091803503440020a103c6405005010344402d4441e074080c000260f032962690050031090307001d548000c40a40b851611450b101d600b8456445000105112205507152030740096811a10900b07110341e484140c01c0c8518200b40540c03907503204070b810100c1048148000607044108814443c000140b00040d0b03600041d00790110700c1806020414034501480702078595038112a001058810400041740f04071410080c800021a0042840d0103089081105540518084540203038035401808244500c010178910400d0aa411081c50a2103a5135000c0840054003165829101c007003114140c0010407800d21042c2c0d8603600920703045600580d00000461400102e01054a0341151001da0f149810304100b02001c10001c80601403400028040a145030001c2c2c030700c0c1c04c07a10a500c420030298802001518034042c480c0900b4041b0b900360002410b503945011220850340c0c8203060583c1000c1d1078184003480c0c01040104001942d20090040c0194030110f101501440055 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 158760593 1250 158759343 158759347
    0x1f02190908060117100f15080102090a09090b0106050a05040302120d11070b04060311120c0705150114040506030a050706230a0c08030901090828080702280f03030605011103 76
    0x4a5042c1e03554081e01c04c2c000121b641d80241080d005194102462840c800d29120545030349070a0b081d4001d500100715103108400b04280000d903801d142c081e52441e242c1010040c0b01c16880c03d0b0301603e40380d00056286007000410440840141c0d9014070a40441199030001c180030f61192001130100b02054507444002c0c0d222a00401c1201904412101a1a02441c0c042180d5241080c420700174000c042c01d1501c0d42c0101e00c1084400c03281c00c03000d405a980110b0444441020000031865640300038080c0f0395400303004148901980c182a00640c0e0080000743c111804040385132601401c01d01940c0080d0002034403044c5152580006400c681d0721114200d0759030785400c80b40c8401400c02d0307055600091a4940100010382c4480c0b0030342c40740386c00300e41080c0b8180c1d40340841b80290106540c152100d142d00e280c05940964424800e0010603c1154150014907448034502d20b025411001d4908551f51040000006000910f05c1c2949007055842500c01143c0c1c0c03402c049c00580100701c1850781102c5036000b = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 158761843 1250 158760593 158760629
    0x91b06030e07230d050607030b03190807060902060d050708060f04060803042601091113020315060d090f06020307020c09091b06070f0b0103170403051f021909080601 73
    0x114901034200c030940b21080500303070760003c01140145196003005041c42c0a0a000c2185d210b0b0542c10510020a04030141e440e4030000c00960340022584034005001e0789000d2000307000142c0c40b60b01000d42d20380010a10703420118500502e6050b105d0071900700000410901c03d08c10a82041050f40341004011203044c0240c03810b003042a582c0f07004500c65111901c4403c40800c1c803240300301080e150545030303d000030b0007007044030304058210f101e000d0304260181900c0c01c50416501c5440c400d50b07000304c0114101500100c1540200280b03600411b0070142d050381d6400e20b5000003041751200440c030f14480c110242c2c985c03800301d001909020007102084d0081c1420010040340700c4010901c50800d91101009005240000d804102107002d0044010030412034884200305200845141c079040704c3c0300d9500da0040c0100e9102411041c090391200810f9035009542e000f50340b41028220301c5400e40e100a0050400341e00d912654103c292a10940020030003810003441106403d0280d40d024024104518004840b = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 158763093 1250 158761843 158761859
    0x303110c03030a0b011106131b05011d0415060c231207050c10081812040e0604180b09061e0f130203060702031210080606060706091b06030e07 63
    0x110043c055284155102c03141c204980c0140c05221400c4010030440e2203510f00041d10000382210f240003030740c80071031401c91305111034101d4001c03070282c0703806070345144400000d05144141d400d013424030030ba03109444001c520000780600400d10020840c03a035400e01e50200b6400c0440015208078000f0f5000002c0100e510442c510020f5021151113203101c1303048d1340d4002e6041950400800a008640c01b0b114001079500c01a48008424060014a0706d003a5080c21181104c5036540e40c14544802d0191050004102c2612200c000d10703031004028001081d482840089100140b921302e5040726040b82030340078048003c004110b000cac0d0011004002e03620122580740c2c01c101681004000700c111001c4000000d146d010072600b0262800e9005c0d00300c0d10703e410b00754806501d07604828622004030751000001412562022010401c444050024100c0c50301d83c1000e008450748801b2003035501035101c2c00307174000040c801141209000c2c03041e504016540d040001c024240c444103141003071035512a81051185823 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 158764343 1250 158763093 158763097
    0x105030d05070602040b07110405060a1a0d15090c110a020f0f0d02030d050a0e0919050c04080f070e010902070b06040e0a050f0a020a05030d092108070606030303110c03 74
    0xa00d090030300307a442e9441460300034068440c1e038105031518103002c24203804118090315180401082202c00b031060703030780d0441844170003000740c411803c1031000300d03c5603212242240002c10240312007200105644400e0000700050400030380c0650280c550f00c1400104d032a074041ea0741a0103070400e902030003264075540c00113100c1c00c2410f1b03103191003003a0b0003a07100c00300da03501540c210800d503018058504a0700c1410000d080d640005d5640710115030300b00140e11081c50240c21051040f00003403813a4003090034005164005120090200c03001d040d00f0800484d041d10300b00503801010005000400d0020708103404600400010383c0800103241c01806030740000750303031400401d80c03055058074001102030050703603900d141c42403950000c0d00c00c0c01198a618400d40000c078850944900980b50035100c56a01c0003895503402059004100092400c003040c031004060503004500303080640718041680695449107040e6502001084031944c0c1da44904000b01038160299501a03e24240c0c81c1c0d0908000644203a128 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 158765593 1250 158764343 158764363
    0x40c08010b0d270308160e030a1112070b0a1701080a021e0d08041d04050d0c020d02060d0b0306091204051909060803030901050901021615060b13030201090e010503 72
    0xb15110b00ca203020080c90858000d010380d070501c1010403044141c1c1409840c2150030703110340c0d00e00d07400380d4050103803540a20682c503541d420107801004003548646404500a00d9882d08542c058140610003007111402c01081001d05141c00c10030344c6d035108400d0040e280800280906021403c110010040e08002040d00301c12250155400c03104002003100c01c003000140240d0155200c4050030045080c00407000c054010380d0100a00c03035288400c0003a08501814003220020040d611490740030f00da807440344000094052018003142c15000240d4000342c016001500420250703030f03031420240040c1c80d0404c603483d040395004020742001d11880114294030300c075501406026034006811820303100c2c0201c180340000d01d40d500c420080d0946400750207403660302c15189001103608000c00316a00c2501803003120a2020303000c01012444e01c00c4e5484414142c680511401460fa541c2000038500c44000024010421488141c0017180c0c01d61001401d02c2819412800080d07040310014070190710300260080103 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 158766843 1250 158765593 158765617
    0x503060c1c14070207060e1801030f0503040e0a0209030c0108011a0f0c0703062903060f070c0f03031d03030408031302220603030908010212061009080f030306040c08010b 75
    0x45552003150030702a14006082406140c0c0040c00c011409130301143c11410303a622950b510911058904c1080b49800d00d40b9030012040b140b00d001080010940c4810b4288184100150381c28256071f250505000030302125500c007090340000e2084a1803800b80608200000c0c2400c101e1841d5060030300720490300142070032140f648640002c96021001e0140b05441070405043d04694500780c0700d1500308050011200703424051007007088260301c0d4a20501c0c51401407c00900240b100e55030350314580d40c5482c0007421010500c0703042205000441c40301500c88031105c0c004d86000c81c1100e0f902c512030300b103242e0245217440325802c140280400078000004881d08000b03a1502500c800d030180c00059501000e4021110325400e1007101d030381031520150020022a4040d80b1401c814550712884c40f4240d01c80e2070051640c080c0c031100099403501d03088510000001251900c0840e890b1a40222890050055031601503079001200b0031559107060301400f03913980d03018509012194900000007d003401084030602c0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 158768093 1250 158766843 158766877
    0x91106031302030f0a1101020d0e0907032406091401050904050411130b04050105060a050a23040e0a050604090b0415020f0d020703090f0b07021e0303030106180503060c 74
    0xc400d0070751519180c2420340050545001c0d96588050595510155070125001203080c5a102215030000c540781c07000035011b0712080060104c007000c1001d40c85004050205040d40c40f56038039600040b03004005040300e290400c0070505030a01c032000d031210020754008905102c1c04004076196913400302c1070310340d605001c0c1d4000c03440d61154505140410000b50685400202002d1003103000c840c1c5400441c1d0441040e1001c0186903280c100340301c4544a080030420120790204000d00c940c1d4480c40c500544c0b400e100800303030703c07001068000501c1e40c0c2c495030100c12850119410300440100c244210754100b401150200010002c0d0341d00c40300c040c0030080001e003c034440b811030200310400c2d036012a41c0313401c540000f0603030300d038480c00018009401041d0705800090100c400406d252803400c401c503040e030302202c100750b04000a581c200010003c811800410009248100480585040000d140a0101d50b110000c1581444840689203155907110502c60360000e01804250f068120440d4880707104005555 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 158769343 1250 158768093 158768101
    0x60921070c092f04120b0604060f060507020316120816060612030206161b03030f0504030302120f040809040203070e030d0809010606030e030f1309050c13080109110603 74
    0x3100121658814a40d06081240d540580c5a034a030201d1007000314148441020030b003d1084410b64059400343c0c400880c00c0a100101003940d07007034040c0c0c1c000340050000c21855181c800d00642660613501803004290040340c00f40452406204102c1c954414942c503680ca146805945c03001400c4012018120b10000100030202e4220411900c41082c0c00c0101400116034429032140c03d00e0038450190010b010b400c1c00304404510620841c0200c40c0300360b81d0301c00c104038030b140c00380c0780c1480d1040d0072828990380d900c00b0b210a40c0580145407007203000c0c2d07c00613100c1d4860030f18002c11210090220000b2440b403420000060400f00c10f45040200c1610016100d694208081d101507000e5204da42e894810182005500c6a01c411081d10071007046c0020f02c0055030f01c44082d4240c039010f14a12072302ea00103000c1d44828072145d5000e00040c1020901010460703030785514074401c4444c1582d607070703142c0d0000003540380b502c1c0700d4a400c103802004900001c00110034075071642c488203034400100510a0308000049 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 158770593 1250 158769343 158769353
    0x4030f020102032502090c03090a03080601110a0506091c02030403060f06050319050f0703020a1503110c01060303030c050307020607030b12011404021915080703110c0a030206092107 80
    0x6241300b1001c88180120060244488255020461000720300c0350320941c00050081caa0340341980e000c2c4c0d408034028140400b003664250b400c440d008100c81d04020500c03048060600041040100c0140100d01906060416060070b030b0a1a010400300c1c0401459440c03070003140c40d4000107e804403604034000080700c0381c004100901400741070b8000c591500c02c400c03954041d03409444400034600e00c180106e90715103640d0418503886821510020354402c0080720f0420880e10441c14900d0080c8141c034000551441c00340104403545c221001181d00e0341c2d51080144100340c0c05108074940b010f91810154110b15060500940d590070003400c0804050701c5502c412000d4507100581400c60442400a0251101d424040c48140c4400c4906a101c3c581d2005482d06003041c070154041640d0314400303d003207a290610815502c1c248054820020180d64000000c400c2a203a0040d1100500c014040d01c0a0703c010305000b403800001402400464100080c074214207070b0001204040c800300d2a50503520b402d01410301e = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 158771843 1250 158770593 158770597
    0x5030c130b0f13050909030d050402040212040f0311010204140d1a01080a03081302100f090e0f010302121518010f060b1b0d05091c02130f0605090c04030f02010203 72
    0x11481c1d00d4600403411281e684103003000342003030403d1507043c01d04443d543d90410404800039134400d000c54108010741c104800c01900243c9c0e0050000c0c0c070151815041000c002d0610714115070654080715414080c5040640c84650a811010240b009604040c02c0410341c24490700c20000c2c40d80b01790880803641c410040070041034001c200860044600d5981d50361a4245c4504500348110001100c2000282c50701da58820096130040d0040c0100515004280090f580410030785560030074446003040001e0801c448009841c40748540b014040b40030b5140d44140038003068803500c1d21107160885006041c400c14000001548480f00b01c0c22804a41076904a0b14010304464078560f0910741800030125941202000900c03a03280785000c0d403004640c104000b035132505060030300703003000402c10026441e20f4038008002201d4918448000e03c4400030b02e43c00514964041c60307050120548442240f01c26181521400c4004c01d8191224912031505040000303007485a4040101410340c1030703650109692003001 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 158773093 1250 158771843 158771849
    0x210b0a1a100305070e01090b0301060c0206070b0c0403230a150f0e060114030a0302030406030519020c0f060109090b01031401110403060f060609060e0906030f0d030506040c090605030c13 82
    0x21840901070521004003d0b10080b562a004202c041c1d003800d19951040300003c3c21186c15029030703030469085c810101c1e42030002c0d050603648104144641c1001c2030344801100e00507100c001109599525518003a1042c00c0d0080b0540004403d83d10300c0d00e04a603020400340005a4020301c0c22580f4842a40060700520881903140c000600e449400d076680000050328030305032040c66400c20b0133100360303104050717403591070000041c01a00b040c44200240740c0280c03c21038100c12502c0705004103800c000c1c9860100c0c2c010000400d060340c04143c00c14040342c4181700b40c07400740c4403060090029195507141c0d0b456004041c03200501580107010300d4203405400390b0040c404483d03101d400319522a9681000d002901560150a0000386003800014040e402041444120749040d00c50060309040f1004100e003d032001004107802d80204d041e606c45a24090000703400f1103202d0b031000240f071300304081072000300d4404034003000230305c1517810003442119001403d8079801441c0d80d000b141d9990b0344541c10904131415038 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 158774343 1250 158773093 158773099
    0xb0703020d020a0806130e100c0e060d02070c050303030105010207060806060405120a05070902030708040f030c02041d1b032d03040f06020c0d030e1e0607060204210b0a1a 75
    0x3103003103807540380d2080100d40500170807100b104003584040040021600c6102072540c0690210b41c0700080859580c000c1c51918505040294605040c5400708100d036000350f440700001c0380d00040100420072142d80800203441d0540c015400c540c1050f00203503461856000317030800c1c02440400900b0301d80c0d40800302c4000d0400900603030402d4a059060b00c2d0b0303900c40108110742d5805180004921415144282c034442c0910303541790a143c1c0c07241c1e2203407942c03082d0f4a88150b041240030080130015071a00d0103030000450621000c58000c44081300d4075424000300300f43e88000503140840304141654006060b0680c540002485104400b44090703100c0302c0044140640002d0001140000701c8620701e10410b412510903400755004c203403107401008a90120f01100402085c0416042420744c2090400000c101d10312034907440070b004e84800000e500c1c0d00010703400c580d26900000c0c02c0c0a00344030740e800d81034900300411a18403410303c103030b80320140803200a00c0040500d03a5000000740c203014213000b1a545440c06 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 158775593 1250 158774343 158774347
    0x30a0b04021303060b2d10020a0501060806061008040804032d030206060a0e06090c0a091a0d0e0a17070609060e0d09120b0c09010207051c050c01030e0a0b0703020d02 73
    0x10b840c02070058140f5031756141c4190841041040d440d80c078039001d40040740515068200c01251031b0108160034900c2098802144a09044400010000d1064030003030510800107001078540ba50400050b00c01d10600c4030104101071007070100107400c000a0318145c0368450300800003070903a1500341080d20070050360701c4011481c0081306818190042038842c090081620514109902c50701e80002e86002590b50f56080341c48140054a400381c8000513041841403032610120060b680c140944405500c20304813045a0700c00a8000c14040a92054403c0900354001402a981c00c0d80c440d049011440060b80003c6900007907400100176060f8054000c05502410810038401c1140e10360b980c2c0c0100c02d807a2004248000c001198007056500321041d0140d01c6011603100d40c2d50404030010980083e400b0606601c6008070104103030741d0b98000c40103941d9005410a43c040202c0c1070891610303003881d03da181410320300400c05003540b40120741d900555410141c81c0e0507076261a4400c4000744038124101944601c0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 158776843 1250 158775593 158775599
    0xb0316090204090b060a0c1502160b01050306011d0403260103080706050c18010c0501061a03041104150b09031006080c0111151602030715061809020303030a0b040213 73
    0x40c1d038040d109a8826500810030030607600280505031064810352001310380c0c252075081c00038410002c1042c50850346d010250800482040e0745101c1000c0c560225a00034201303005100c1428200542e40c010650005543c1c01d03070702c0d4840c04003c80303c00904064108000030342c0d041d1004c1071094440f07031150b0f43c0d01d6190103603680d603040200300c40d000b000c02120340c142407101043c1c8000d128425a000c03040c940608103800d00744080159160540424100e485549403000015940380c507440e140c00419141820a07a41e03d0316191007900002d12004080c03040d890200313100e281d0b8112051070030541d443c1c00082a982e44590002900c1c0c42103030403d4070b0b0741b2424071401142601e00811886111102a2500c09941c02180074807521004500300c103208074505a00000c844455810002119210600680b0319043c0c2c03540311445038100007065607002d5a280c0f0410080c028501c0040f0324401d41c60001007180f45401d50010b40c03280304c00f500302005940c440100e90516a5030368100c450f1a400048c81102e0156 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 158778093 1250 158776843 158776859
    0x140406090312180e071106010303021009170304030f09170a030f0e1201020405030d0e06070b0601110607020d0801050d0312050a0e0307060510050105030108100f02090607030801030b0c07150b0316 86
    0x9001c07a517030304c0019810b5402c15100c40b40080c1c21810b90740c0c141c0140c08680d410720500401001d8240c000c4c0c81d9184a28030707968071442244000c40c0103030f000343d90794181c1c0c001114001e804200700754403c0d05130070780f03460880740c1c010408290341001d1a407500d044840388a003500121001d51040c00700b03da1240402d50b0801c1c034050154014801c40d40140e0a650881b00c4103a000d450343c00307680c1c3d41241c00c103c0821451000805200307030580e011b2014101140e485c42600b140503d4004111943d42c0917911503559141c000d034002c802580102021a01415002e02942d8020311048103a140640072a03201d002044d1070f950b103030300144100703003000003140e072510b0841c1480c00140c041178600480d99a0301000c00300d155446403044038103032809500104000d01e010709007403004203000d540c0706885c0e543c280a4140265144401401030364003075940c406403941941045006400c010301049240c1104218081c0004c8040b1016441c0307141a40f4000b88090340b003400b013410030380040594404602948404500d0071 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 158779343 1250 158778093 158778119
    0x4091406070c02190806010308071b030b060301050c090f01080709150c0605060d020619090f03050a0c0b2110031a09060604020703120f090b090a0314040609031218 72
    0x90013101c162070366801c284404110b07458540036658880d0070003001800421407501c000c151842c03203001d583d010300c040c0300c2c0c04242068103504200e480000c100c0c20f2003070f20300c0c0900a898100710071100c1285426002000180710160b003100319414402c45400042c0560f01580440c0c00900591001104034866900028840080140c080b2501c0d03252501003911414503000c440344d20f40d400740205141480c40220801c41040d1400b00343e081020300300000c9028021020070714001d601c55001010580c0d070380d192126250100d03403c070131040e03c000c0c00782d0076200c10f9051664103807050808418003680c40b84000410141e95982020701100720014080d00b01d4031106a455100d4110300b402ea81c03007030b281d80c3d0420050384100400900051691003100704405000d6000c80c01d859100300000815010607502c1c81400b0900b190028410b8001c500c0c640140742e0008592140b840000034500c1c580b40c20a080508540503e0101400002d4400000709601d03002d2049070b05080c2d500380074001c0f903990300e2130800285 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 158780593 1250 158779343 158779367
    0xf0a09052706100303120b030d09031e11100e0d0503091908060703020901120617010b041b0c0807060905011d01090b0c0f0d0f02180a140409140607 65
    0xd000c103400c5001000c0d001088203802a403d5424000c50b182c59600c080700c01c05015007031003d000c1d42d43c5421040d166801c20400e414121141c48800c0100d10354200041d0207404410340140a625240b00f0000184071199030083c144001c4400c0021049034040444002007048181034100c25458ac5103014068000044d00040c5000c95003043d0510702d0920302c859004041c811000180c0c82400444c6c2014043d8001c1c1c50100b06c18500a015200000d0031b103001d90760607a04c0410f04003403038001d138100c80310203014041c002601a00c003071242c1940c401c280805800698500e4082010720601441048030400c1120202a00b08070300740f00a01d41420254002d0a1210341c80c4204a1907030284010070806020300071125802910b0000d07680e940c094941c113960310031000c1c0b1401035403c1001d5071040d40644140407042428100040e1643c540317075120600d00ca02183c18030310402c5a00010425114644050201110700395808584c2145914203986441c1a461868815001c4c0700104117009a0008940300e403 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 158781843 1250 158780593 158780641
    0x705070f05040b0105040b030a09060e03030f040c060c0c050f0114180306011202061b0c030a0804090b010203090a0b070f081b010f0506030706110a0c06050408070f050607020f0a0905 80
    0x4003d249100666052041344074602100c0418000500c0c445103030b90121014034002c0c0004900704900c9240141103030b0040741e044100e245400c0600c03080c814181541405001d850034100912132464503082c0e1002800d01c12a0b200d5828400b4880c040d07446010b41e40e9000d4075100d04d041c1c60b4014042402c2c0c82c2604000740501074440d0600002d4600d0140b040c8103206074020f059240f40c5408207003078104d01c40c2c0011418100e849080d0100d041500c0800144c01068010059540c40e24100704001041d41c00004c100c40c115442407113002c00c0703a5102000b0300116460007000640d20b8800c1d18042c02001141080500001c902107491a0f012030000743e0284400050301c020011800c0a03040c1c5000c8800659045400d580142000d110f1940506c003103508510b004030403034007030016a5540444078203241e007294000910108007000141303010013841c0f01420700d2481900400c3d09102c086500e500074110003920500c2d2000c00e07001640c603007200d10070280804100030b1110b072070182c0300207480b8005044c090346 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 158783093 1250 158781843 158781851
    0x100f03050a03260105091003150204420207030c060302030609100305060705070204090c03031e0801061d0609030a0605150906180c040e01030c0303030507020c03060712020705070f0504 81
    0x400e000c1e0343e242c0754200284000300c0041c81c1d0811091266418004260035500a000280400400c803607030503a85c42050044030144c1e503a81040d0440342c4d4602031034840207110200c0d49061510f00c6546405901d901030016030b01002031003903501245842c08560000c0c0c81c00c40290004101c07503034150000c40c814841628042010344800c0d080580b2510984005172032900420b010071040351040c0002c041c4940000d00100303c01d0800c0d11225100c1034564812400f1410307901101400304d8880700c5070807181c034641c1402d000661610030042d1581803031611310790407600c000c559095559030f080c01fa1174460070b001d821501204074515040d8018034040c0c52078806e50b210b0131025992031408401d400d01c1a903010b05811301b5000440c00c40750182001520b00c01600c1000d00020401707151440340300340218060344006200c6490350401030200c403800b030040021504100039034415620300261130b603003180440c0f4004801200e0040300ca80240174900c3c00601b03a0241110004001480c8101c1e00c05454003110200 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 158784343 1250 158783093 158783117
    0x306021201060f09140a1e0906060f080f190c0807030e120d09031b0609150501080a03080405030c0106060c051506130908070c09050a0506040e15100f03050a03 70
    0x288100c010a14440d00103503018909021031948000d9100c0c49550280c40003034120348800da004a50302e07c005140303200c1c89030306d501080b01d000140150b50043c03429040105800043c07080040c1a4100103110010070009040820381c00020354003d0700c2501c900300d20801c50f8a42e11200140000015582980043d0501c46240c10315140414480c0d0601855001641303807420030012200a40311818064041c01420448503641d259102c103020000d034800d48001408200760704c3c2024104842c05a003101d11854000140b00b80a00011000e00309600f508000038150350302c0c6022072079485010840b1281e942002c00008a06810550780b0103210b00c5902541d80201e0790101080480d8411290070b5441501c80742e644d9000703080c0f6481107030340502a00102d440d10328683c0ba40507040049503c1040096540c000f0407101441521030076070081d80845003400244212030890b40d03121100c5880b5a00c24007a400820407100e020000d48000300303802403d80c22407550b2810082d44664620754147c012078801c0004c0303 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 158785593 1250 158784343 158784347
    0x403020309150c0d0e060409020f0d0c08041509050c0402040f140d030906120609090b060910030203030307050a0c060e0a05070902030106020a060e0f06010e06030106050102210304030c0b01030602120106 89
    0x190b1000481c1d500200040c14482c50105d40403000c0981154022504000100d03900c610b41c0018082d007412448282c0e5610313503c2c21000102c6044071029000c12a1050a210001c0d10b8a65914101900004041291901404c10360309100d00c100d02c23180e01a200240c00110500d4031019070040b1540c101800e40000085800c1c0245000710460040c00601c205030103101590103012080d80c01810044002400750711949100d00b241c0510b401036803c80d05180c01c01046240a20035a5400b56201d141b002c061891980440e40e01d002c007805400900c4804144102e04500c50720940b680c4a030000003e00c2914041003c00381c607619200380594060240d60700200308080c6038000c40f41250090b074020203104007582c558100400c0d02c00501c4102e40503000540b550110304022946c0a00382196188006082000c201070171200b450b4441410340d007180344c8096500150760305410480c0c0d0708140c000e1387c80d07a0700d140c11500124800c8008105818040002c81130019aa0140060310003030090191941d881d4041 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 158786843 1250 158785593 158785597
    0x204020c0123010602210a210906021b0114190e03040b03160c030c080f0c1b010f0309030503060603060f101d010912020d06020412060e010609020f0f03040f0b040302030915 76
    0x4520a03030001000102d110b144204e000c89072231044070f005100c1c0e200105003c1c0050b500841d8017a14103a40120322107043c60700200b0448408822240200700440a8089600340140024036003501c0031a4002c520403201c9c8590410100d5912050940b5a202c0d02d40c004a4000e800c203442603080c030b219107031420b81c403240280c908160f10790b01030311a1001101c042e40d80c8400d40d400607680760300030f01040c00003494111041185107103078005c039509191403402000c001804130103807194000405040c000079002081d0070030304480c1c004800b80c4005550356240c801182411040081d142c1c3c01250400100481e154021801c1d0015506200d0242e06117095800444491289001b0404420841118003006207004010950b1140c8281c0c070143c146983c8809025013484c1e0341c0b03401d0f2000b40e1207400400182e84284035042c050014003004500b003a0004d80708403e5070044440741641804000040b03000d1100c1c104002031900d5100740401d40503d4a40f07802502c0390050140740780100041c8010300d00902e00581 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 158788093 1250 158786843 158786893
    0xa05060609060318010902040f090b3102030705090103030207030b240105030619080703020109091109010f0302090d0c1d04030f18170303180105130204020c0123010602 74
    0x3201d541180c94410b6402c81c0c14403503413a851070940d82c1e010010b0047c0c589000b4414207021a40340012000c95a061550364a8001454101e02d20481c0c2a00e10070b0358106d1203c407200e8001045025645981d6101280c50070b1515000150b00400600c00001090750020310f40342078a2007141c440b0355580790818010310000c03601c00c500c6038007081c080c0c0d420903a51007500035592100d8020070b0141c1e020056000d994003000750303811154151708100414429541c02003081c500070300600361700308020222421071070900e014080a05042000c0d01d000004001e20940549107010001002200150003030724002c0710f00945032040d0200b030210225080c00307244031031074524810b503095240e1800056640700110381065091024080c0e0320f83c00803001c183d80c0b2480880704440300403e40256a02e00b000300449066001005081003968103000400c42d4035040e40c030386c0307000140e41034034056206c07c0d0308941203000d4096640244100e28804445140301d50a0481550403150150256402074981507200c142040f0452 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 158789343 1250 158788093 158788099
    0xf02150121170a030b0f1503040311060a05010510050a090621020c0322180f062310050711090a06030f260903060a0b01050913050a05060609 62
    0x400104071695524503000e1044a5400c0408100202582c45002001e02c0318030503003a006001c81e460b09281e41500c0780c0715070450221100600c094000d00052891000d0160f640450203010006c80e0030140110404290108007200344c695074580912440010308091256620070748412001c069040d00900c102c0e2030719131065230768000190070b1400a542071100c41e0100304c0c03160755610502d900d04420f44040d100804603240990780c5c40d8440022518503070027130644100c0910344144100504201300350903507450401080040b80c54810110034800400c1d06078800d081205940c000c1341003000c980412000e000b0710448851107007006171241192a402001c0005021740c0d41070410300098900000728032f0340711003c1400810100d8990340d60189441c11544104c43d41c030390100f01410404050303060360b40c603a5890b50b40d4a0402407140700185e80e58a0141c40200c170310759070320080c0300207910900c2190070101c2d000d08500c0004001c0002500105002c651a5409618060101d4020301c2c0440848070740c54001 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 158790593 1250 158789343 158789383
    0xf02100c030516080409020c0601030c0b04050a060806060d051314120f0d0f090b010806220209100b0309030417030a020a0803070903150c03050f04030207120c030803090304060f02 79
    0x240031810440320703142d181911303556414840015070760390900040c0240f40340b240107040c0300d500d10714081c0a0a0f0007500721002260040c0014401c6466400f101000c03100c0e1858192840c0c0c0711000407940c2c0f0310601241c44149420701d82000545800100550295032080e01291541a4420300d41c41e11041e680fa1040061101006080007080a02e4040e115000c0c00000028003000100884d50031a002c4103000c45504629400421059000f8424a80d1181085004115041c5410180078650080704002440380c07002102044210640319003802c0901110f0f40c4680c0d40e4103003202d0030b03aaa03400a100d0708417403007411840011064030110580c0c851f0309583d0010100c1114947d0f4103c8503030002480301c02002103404002001c1045081d00c0d903000758040c00009003072000110028181c46000b0101e18510800c9014800000d5000420070111031014400d18241c441510700460002c00c1d5901c00342c0380d904040144014640c0c0840200100c82032f0762528001c20050a009980340d00800c1f05c111041240 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 158791843 1250 158790593 158790607
    0xb0102150714070c0e010e16020607080112140a1401060609030206040306051f180c2d0c02090c0306030c03160b0d110c0109060b010914120a020d0f02100c0305 70
    0x10740040e00f10180701c4c2c4444203180f5241c01d04103040d560245c0c00340700c03600245014041c10b00008038502d403a0065610140205160141c4094210801840380c46001c2c8091021031040c4552070703c1800f0741102040941e841051700382054a29012041c40400303030340d440c015001a09034003c2003550101c03607024018600f082e20b1500c8040003020001c00303901a815035841138104515800c0c80c0000034010004903400a03903801030081045030a2507030118141b00c01c03d9000080c80241c00180c25043c00b44503512415000c041008603039403546003000039000100081400301c201250f8014521642041d000c8900c141301c850308043e501e01c150b600c0c0f0703c0e034424004028084030400078010101101200c0000c00d440310199800d48140c1d0100388178a050b0395407650104100300303150258030315070368003442d00b010b425040c100c40010541c49041803c1c4034803005440d4010034142445007020306500203002c130040ca0311301d040c0105980102c0d04221301c16100f10010300c0545018086024016415640341400c0001c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 158793093 1250 158791843 158791877
    0x190216060b0103060510180e01060519050904020708090405060418030c0501061d0a050c130603200309030a0201050f160f0c15020408010609020c190816060b01021507 73
    0x211882124101619442c1c00703d02601d074035661415401c0c0c2507647e803400806083c243e0705040401c0d001203000c05000f034010004254404181d40c100a402009400e1645164000743c0e80c901c50620001e4100b030010a0031410700511001800c038400c001d407000d005647c0c84001f0002111440a190590384215081c5180428800c5400000c2144940c2c00005c7c4584c81c1e60307600c43c001c200d032118490b140b51040c040004c200c4050048982100f081101c00341001000b00b0310002c013480c0c5010304800c01d40c1c3d40020031b1076010503003890540062036600056890800750345198680c1d00c800e21a9025608220120b0303c16a11640d844d445448010404030301d4003078140c0112a80b0b1035010300e5001b045842040140481c8a07142c606040441c040707001683d9900c0c180006007901c07401e91140c161140b041c04516035103800840d00400c04080402e088000e0700c4145071202c0d00c1d008101e5a810007902e11122181000f41d40e6000c07600088003602200c411224240030000c00b000d08640d1800010320744d141035200e4103 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 158794343 1250 158793093 158793101
    0x71205102003151c02040b03011a04020c03040909060204060207080c0f04380a0e0c0703030b031e0601090f02031608060102010e0f0607110f030313020a17010519021606 74
    0x203c580e003420f14608448001494050401c0034403031940c40b00c07071000d008501d0079106002d26604154001d0011010034510700c4458809002c00c030f8040c980025040e80070042c03c1c01100d025000018003000030048a003410740c000e40042c0207003005032080405c0880c50400028018608800c0200b2200c0c00301081018440a07083c000e40e0f00a0504441c0545420501c0781140008041d1500c100c3c201880c08140130400005025804801c1c802100400d00440c0100042120307401d54041c2030202c0c020160001003450800c480100010003060080030f001c02880118002d8101c9007285410f105482c00d0110f520100c0c0300a42d5100e41c4000311048603a40e2900840110360310540500002400302c02d47c01e0f1039818000c40c0012072002d50042e600300080241c00c41d031159080b100640c010301b100d5222800c1942d680c40041c01862207454400300000c11075491501c0320015120030038180008404c10082d890107420240d071504c00110030b0955140302c3d03071300520a550409041d40304100c85c048031511540300070 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 158795593 1250 158794343 158794351
    0x601020618060109021e03070e1906052d03090604030306060e0f040903270911070f060911040c05090102010c0f0c1707020907020a150203040f0809040e071205102003 73
    0x1c0841c4100d481c186c80c0c4080518420740300c5031135003e9411200d4081140c04549000704400000c08001d0a06c134156201302980d19030540c044d01f25681804881e03000e550a1ba181c80302c501601c10000401c03215084c0444c50a0045101c2e40341802100e807940c0c01540c40d0041e43d000301d9044400b5648018040c9840c0e00010030080c000d08080300440c0c251905150f9045a8020742c60300c50005240030011840d1500c03031245000880c0301d04130b0034a6510740d1030615160002201030800303900d8003840302c10710021140315029000014810010071280c000081d040b504806900350240d46000319102d01c850059400501902d4240d032807000441c42a84c81c83c4482c04a801501050704c400d1041c5030040c0c46103500c0c9030040300303641c0040c02000c0440c40d001c0d5001c400d400c15040884d0050003408001100d0040e480030701507000301076546515100300424000e210050311048140324030400000c00c8555200e000d1405405541620410000743c03031002c0a46030700c10342600b01e41c00002070408802d01d40601441d00 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 158796843 1250 158795593 158795617
    0x80d0510031703180601120b0c07020109260307061a090c040603020a09120b100902040b0702040222030606060f021b06070201050408070602060712050402011d0a08011103060102061806010902 84
    0x43c010040004c529004090b0003010300a5407a01d122410b01000b9a0541c4c9c0c8401d01e0076046240043c01d03070008102172168454400c02e0700d035118001d14807050303c9007000b07030500700b55040380d485a41d1420b0102c090040701c00f0106c1c0d07813000300c500e0141e2030400c0c0201c01c0c032828040c0a0300e407403e442c0210440095020340700c1c1074104490303007102081c0b071207030f8030300242119005c2c2843c2d45082c10032910240c1c144e040307070303000d00201803041000300085160313007044e6803075190100d0b001a00d451003890b0860040c24042c024032075140d14083c0c08803c00c902948030030f0940d0180d039107a00112102203130a0ba903c8070004000844444000400c400703905c0d00000401460784103161a07030619944654507032803c5450740020340517800240401207455402095808a05420399080c000ca0800c1c1c0c0003c4c2c6000e41e4071040d0b940c400c40d13030440700180d901c0310013201c8020b00308140208080b1442c2c188044040e0000d070b54050050082d240410b4061900c000c2100b20301f407507100501312036480c02c0d48160003540b00c5120121 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 158798093 1250 158796843 158796871
    0x40209010f0e04180c0f0519030305030c04090e0d020c0102150f1e07091a090f0103050a020c030a0e0f03010b031203070915080a0c1d1c0c03080d0510031703 69
    0x1244c003582100c2c44c413046104034190b4004c607041440a143da2034154002c9402019410716112003400c040315641d0840b50141402c581e00e40740d40d00303983c0780c82c80344d5001400c5060401a1498070f0080020388000440034175801d0b10f1081c1d0030340004a0701d070180ca041d88606804a2030110740385407522000150082181c6c04006200b6414890711900d071881101c5a201054500d03104122680221720503c00005101d02c0e803031b00e0601c1d003000054840c00388200d9581003564400c0000c805000c0b65045428410030981286d444200d1207100500e8400401d40443c003600c0c09080d11601410140182441010000c021780226000c015900c08640c200408032010021050701c005080d022150b64802e01000300e9840300740600d00245035030182d03402040540d08102010102081d80443c1d0780704260504401ca642e10700c001d800c0806100c2c80071103250040c0070f004400000004024a40d001880c80b807040c080c0130300c43c41d99410094090180306103c058005840c1d18588000b8408140055a2040074642500 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 158799343 1250 158798093 158798111
    0xc1b030d1107060506010203030f0103030818160801200703050d29091806060607110402190908011802010503040203150103050c18130314070605040c0e06040209010f0e04 75
    0x406481c210404035851060018500b8240540350203101c0d880b00c000c0c0029851403c3c90f010344980000c0521020342040300c1c00c80031404415807441016000c0c4651011202440b07061941e80c03002c5101031140c003005618290241903429140301c205038808500e2001e041c20000c181e02c0035207440c0d005003504100e040c0d070b0b0900305075842c410300a002040030000009004a9039901e0603c010110702901307005601d1480440c0401000340011030369401002a034105441e8196031408408260003041c54960150001c5089507042c1030444c1e101005011030380d188180260703915055400c91380009029840c00e00b81144c2a000740d40550f000316001440642140c11144c441d000801162000f80c104844541041d94100d803186041021003800b030f500ea601210312b9042c204480106904042c0b001014445155844440d0100a100740c03006542c001809100c1440c2514107040003c0042c0100b030800c040010200c0d125051034402c0d00c143d0301068503012039100c0c0c04102603a000005840055006803115111 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 158800593 1250 158799343 158799367
    0xc050409020c01020a0908010902090103110a0807030506270606040b010c050105041202010b010f1e020f0d020a0c0905010e060d080405060408031902060603030304031110020301150206070201050c1b03 88
    0x10000d603040800016142c1140400007491040591f00c1600d20b0b030304000c540340240e03032907400341070440784d10005a0700d041403d90045406441541c1c070605542c05800000403d04c040480c4091081301c1003d651110f036956a8142000e005c3c0d11004480103920000008010f420260700442c03007880141841c104826203a0340303007400e54008030380884502d801c5c0c2080740304090f02400341c01a00700e03090070324510048002030002e1030410b404032075019802c0d40c2da01190846000340702008050b41c8541c2614641c0c020300304003a6403614501c0701150000020a000180302c4401c0c89070505a6446100d10b40058960804000600b14503030303c2580d4441c001c101c00202c80d80c881c0001e10040800002654a6156240000303003002c048914000954200700308000461b94040200c0b94455814100040d50100c4000045d01c0c007500440c92110380307440040003081c000c8880c100f00035049556800c85036103554098040342621419165661010310070b002010403403440f081e0b000d803100c0815045170b041100c08104 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 158801843 1250 158800593 158800597
    0x5090c06070602070c05091302040f090f1a1b0a0302090a080105090c010e040501030206030c03190614040c021b010f03090503031807060e01020a06020307020c0d08130504050114040c05040902 84
    0x41258925400154101003000c2841720f10014141203600791018a046003101e90110388418000f0b105d44c0e0f50b030b03441c1038600071035500c07100f141c942000400d4400880341ca0b02a84c44036490f0880b000c4400c1041c001403480d040d520016201c0c20309e4001984c289034200c03030160081d40040d002c5960121034010b010664060034842d041c8a1345010009080f800c1c81000050052200c0100d0140964201b200620150301e40740216508441c039500c503960380703907a41d401084c1c0c002e4030f00c03821082503800c120000502e00d103c91402d2002900c1103404105503a402e000070b07a59818200b44511311841e48180003600e96020b1070390010703d40403c1c02c020450b05074955a40b42941d0088030100400d0340704095032030300d01f9030030004a4084c0c921401c1c0904140030140000c0d69035062244c004041d642c0020016107c548280110812548043d00308800d403600707450400c0d00703a00140604c2c40701c91510700d00010075150034081c00d4101c8041180c0305007004010f100f03002c00703082c00c51828020f0042c1040002961891840 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 158803093 1250 158801843 158801857
    0xc070e0a1a041107050f0d0e01020c090609040206070605070f030b0d05120d09080309010f14010803121308030a0902040c0e01091e0803040f030302061501120c020f010c030504060c050403051005090c06 88
    0x40e0032446690700001d230001030351710740444c110b501031030380405241c840b40003007a00302c141202c104903550303210700c0051254800e04400401190404090003420358012010780b0380e0005948082c4420a004c3c820702c441c4400350640946194031001890480c0c150190040500001a0501180c8100141c4a03003143e5841510051000d0707660b0820310010840610548020400481c0c0044da103500d01404203035640140e00304001c4c00204000030500050b03030150008209540440d8454891904201d0400240b000d804142d00450070080c05058092140a013510583c9050f180c0c0d903012030a003560325480080d088208080030788100004180e03100204068402443c140c800c3d010000d09501e00242415006032130154103030140d06810348940c0e00300101100c540a600000110890740c80c40492034252501c1031004154070380300c40340503401d9260f000b0034821401a0010300c82c06001386c13801c9500d40300310310010342250052a80b00c10786148135000682c1002c0c030303281264014422071002420790b511180c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 158804343 1250 158803093 158803123
    0x518010905070503060109020c03040608130c03050610090c020d0e040902090c0d0e16090c0c12200d17040c0e1303080a050127110c070e0a1a04110705 66
    0x240400c15413408000300b60260440382000c1d800d009d20407907134560f04e02682c021641030145100004898001c0c070f81c69000c4e140d0704508130400003666400c00d251220002d03141107244008d001400b00303200a6501400c8482002c2c0d03070040c03a002600f03407800c84540039041031a992050321482c951740541d540c2030b1900c0c016400f0390002c607682d0b40300304207280c200c690009500d075481d00203100c8024001ea415540100300c0b5804000440c0e8840d11070406c8807040c138a40700c0203151201030004c1741442d071341c448100702041546802c1c500341041480e0304a075039108041c2c0302000150040c000c0f44d1601410480854105102d2028106a60b840b44e07070900300724504640c509942580280725038207065000b480d050300003030610400c000d19414031550303180f01002c0c8410110342d10502503031074020303071002d5000c150b040009110840e250810580841e448030b01c01d00c2104900c5105002080010b00544035940d20128012140c40c41481e800007032201816104004040c401030178007828000c68014040450016002 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 158805593 1250 158804343 158804353
    0x1902010c1b031209080306190e0f0a021e030603010b15030c1303080a020615100f03020a05121005030d1803060908210402090c07080d1d070305010213090506130518010905 75
    0x140c103205484900c4030b03084108d407000640801103250380616064000348040c020810301e64819000401078421544100b020303018281308200105400130113107004074411802400b2419501080000c8200031844201c64100204045850b000030a001459503024003600490241e40d00c0e100d6003203a0b005030000e0390140e0000420404003a541c9001506803000071912401450b4480000500b07240d494031403c3c0525600150210042d03018000391074801101d4484003ca604e003100804d03c158549100381802445181481c0140c1800745005902e10f14015100b03409061940d21102c000c1d00618030b0560707030310304104126410f12205e01c00200b40e6800440c852207840c1060301c103011070624001c0c000c3d4003098003800094005620541200d030080c00f12140441c50300c8450300381c468100c180c03116048a40c4242080081000019000b401d484d01207013100c0e001c3c081d92404020140c0744115113a0707602c5810720309007942e8010560702542d000032540c00b2120030443d8030b0902c076003143c1404105031042c1c0c5c00 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 158806843 1250 158805593 158805601
    0xa0806010303030f05040b16030b0a171e1b060f0a0309020306010506030c120603070f0312021209011b030e0a090e0616050a110a0203060a021902010c1b0312090803 72
    0x40c050510501e030444010002c0e0710f0961a800e800141c0034141e105848d04181c0e180311814402c1d04820b12542d00100004240c6940d0f6503041416408400220002d00642120001e602c006901494044101c58080c004003001184800c141e151820081755000005000c01d002c240c2c0000c3c0544442d00c43c03030303c001488110a00401d40741c032105921091042000300100450180040292020380070884142c4d110345e2074150003c2c0c281072280c1c01c8801008001403000050125800e00604d07100c0a0b9026900d540040c610940c1a174490011054007003030703280803601b01e116080240381280e18060314000058042402c0014884e04a035400800100d40f1084814000380c0d0a100054000592601e4001c0300d400094024005019410420040c07141c030500d00c0c82409005d01000380f50070781c001c2c1510214603080b0710840094102d03022442220340e42861520b401030051080c00440d103002d854480c2c981c0d9000a031254412160300c1c2c00c030100005509a00f110145a000ea842001c0c45407940c02c1d124a0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 158808093 1250 158806843 158806847
    0x50a0501032f01030b0607051009020a0603050103020108010323060702011b03090c03110a08061312050702090114060c01021305040c140a0518030303070f090906031119050a0806010303 81
    0x810b02c00700b2a00c0116480c41800c0c05580d16a02d0312003501e0131300b40400c04041010002d02c0030b009030714014005001e40b09024444407044d61094030050f00c01c503031a88010303444240c110300f240c8090200a003c00c4414005102042d1100f0a501d085140281480b0545c0415100e0a0034200e0503a50040943c0d100c02607818509190392141200c10b015103410030581032680c40d2105100c05a03c00074060750344002c250f18582d01c40e03d40500c00ba014650071201d103801c0030508003031294240c0d40b0554004494801e13000c40c0e68406c1b0129502c0d0b0760020505803199080c0441c02d10759030001e0740c4155001604100c2012040b8007800580400c1c02a201d1284c0800d10b050140026566210120800c10040d5119100c81e417510f903059900803160f900d0030326112001d440304401e00340c014260703541e03042c4004010041c036190b021030310500c1541d04d99034140219030390304541400d803115800001e001e42c0030594403942509080d8039074103440c22040000f0f15040d40d17450100340c13040c0513034105d884250050b00050060503 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 158809343 1250 158808093 158808113
    0x1121b1809020c0703021201110f0c061003052a030d03090b01080705130905100608030a020705040e0705010c05073210080f100306060801090605090102130522050a050103 75
    0x12044078015441c2500710420141c071140c05000092250b4510321464584010962100c00030f82c040900c400c0e601c00c07880051443c01d4021146890b200d02c1801d00103550760a0b04803100c011280d10100a1030042048010801c0c108100d48001c03040c002c016801c02015078040140c0d49140c07000341c60000380800a81002001600305030000e440360342c0030010030413040e01c0303100c000382e1003000c804800640c402c0c080c5089410886804a584c1156007448400b0802020100041024179069000c50300115507810901007540d10031090142540c100c8541001594050000da4240364443c03000c0e9240d264989103c0c1080540d001074020300c454200c42c615040001070104c40481a6003220043c03100c00542c580203010400040186a44420601c04aa4006201c0070342c80081e551081042c4104c0e078484085a000700070b68242034030124100000304180142c10f00c201c80d00142c500201a114074144400e001c400d580c0802121a2244a03c00b0b803030403000984101402041e4001c03000c2025491814901141 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 158810593 1250 158809343 158809349
    0x210908121b041e09090f080309010209030a06061d010f05060a050f120925180b1f0306050913140307060207060b0120060f062106010303081f0501121b18 67
    0x945080c85d01c201084217001548040d507800081c9030f9490f07841803e0203019008219241b42c1511800420342c00300600360300003405a0310680307041c81c207002c2032048903641c8180030b01c81c100348000c0c940010b22160401c9001002030118604044d1720380212001000c074150b0051f91a51000403201d0103100f9000c0c42401810710f9031138007802080040c0e640c03a00c1400254001d104030100c0140107009a6040c003030540101c4a0001c00921302c5c517852040150b5800440075803024040041d14114001c00d40c3c0c0b0b850010300e40140687c078004000c4a00d103030b40c1c080c43c1018140300104070780700034045200000d50f0ba0005090662051402040c035040d100300252004201d9003114200c1001c0410380e803000600010540e50115103451042103e0321150082805070300c0d460f02c01d42c20702c41505500d0311040c0c0002007442c126403081d0b44051041ea10b170b00340343c400c03600f02c508a40702e10403181c40e0800466200d100010000780009000083c41890b0f80d40107260406015032030408600b4560300440242001c007000001 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 158811843 1250 158810593 158810609
    0x1e010b0a05030f07140304030314061005090405090a080403050a020f1c0605060111030f041502071d1018142a070609050d210908121b041e 61
    0x6000035a14040c10324000200680c603159054000a04072a10501840348400c018080ba0790f504d08250500401801880e4109201640710001140341424084e2814081c007201e596014285920784040002415018203107080c10712030031405c0000b10f41a08000c0c0004d610400082a50040300d10600c02d521444281d03152180c03441034111040300207101d44d41d98502d40c0c0080000351664803803005039901d00c001106009a44004500f500c2c200907044014000e4984101d8143c24050b809002203a45402d40c1c060340c0480784c0c010894040c40c03603c0d85000c68014440c5003078a60300649541c103001d6029140d50720030220a45440c248000b42050b0342a01c0d8018605845542c40c03106200c070032045020310701c1000d1003001000030386d51050005035030203c0c0e07950b64058103584504503072600c003c0204548d0260603400050442201020014030300c1010210343e8002d55403030414001210042040100404420340c00301414071031047d0b40c910b500140080c0550030f200141c1c0c51020718140d00b400300b203500441c0e5 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 158812949 1106 158811843 158811847
    0x30708160303020c06070503071214071a0f0108070605250f0201090905160309060b0d03020105011e030b131b080601170d2a0b1e010b 59
    0x4101c900030b60842d24030a80312000c1015510070407200a2080c7e104102c1100049e0001d883c2c080c00c045641070003011010114520b92443d4840c80c030488070482440c80c402c0d4a0101c0c3c0c0d04068101150401c5807800303604040003039030365110b50b003d03840134441c010821400c0200000400d01142d40302021041c10030555280c196001c0440050803804034064141c00308a400151146511400c4002952540c00032031103c117400900d000b41050710001c3d1111080301d11a100e94501300940340c802c6d4000510b03989815200b42c40c0394040201142e1112011404101043d82c3d40c84040c3c100d18801c0d04140083e0300c40c502000f14020900010762620f07001d000001c0c0c0c01001140640c1290750541c01d0094004642401c2600c2e03250000040f400300700d4030700c0702d144d03581c01a4544c8081da4412015000b2400115103a110406c0c50807500d48551080e4003030b56240c030810400d1500e00600511b03001d0781c = true := by decide +kernel

theorem cover : BRFrame.Cov 158633093 158812949 := by
  have h0 := BRFrame.cov_init 158633093
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158633093 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 158633093 ≤ n) (h2 : n < 158812949) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
