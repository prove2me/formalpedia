-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2927
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:09:24.199673+00:00
-- url     : https://prove2.me/submissions/940bd7e2-9108-44f2-bfc1-8a107225bf41

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 526258992 ≤ n < 526438848 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 526260242 1250 526258992 526259003
    0x9040f06150906020f0d0801090216080f091806060a0815130605040f0e1c050c0304080a050d05180409020607020907051b0303090712020105070f112e0327 68
    0x703a61400e5802032400a4401d054001a000950000d4590380d00101c581d054801844001d80d55002456003922f100c402c80001500740e4001181d88030758403030030034004c05020a044178030200385511180141000c0c0001d840960744072500300b1103002a940503410b400d50103150703c1c0802910000c11720120f1812040d020300100029034030001031190b4a058410031ba050210030701c04108140030240c9450f500d440900c9a070020552078001c03400d40e54428412941d001c0d14003410707030b0b40310340e901c0e0b6029079a5000c040044546000e21904c0507001407042c4241e50103820301041500c81008281c041c0300080048050583e0800001c004000240c2c86043c02940107880b141d843c5951404040400d08a4518920f0031810303076002001030002c00e00c1c0008404090b2841d20005180c082003c0c80140c58030310036164020f101d20440c0400ea4103021081a20f440c104005540d924803820b51070b094441c0c007d88100051030f038010070079181041d5520076804622550700e00c1981e18002c8a0340704020100b40907480b0704464 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 526261492 1250 526260242 526260257
    0x304031b0c0305012009010c08090d0f0b040203060702190308070504151e09080c04020f120a09051b091620010e01060b161113020a020a020f0108070509040f0615 71
    0x15040c0d0805c0d03600d40785c0d41512241a0503d4201c1d800203101e507290b47c0c00500b2031407000c80d4815241d03944080d08505079510071262a14041c0a141017283d200088500380e100740105000103095500200c1d64407001c061f80e282040d840d00035a0750a8452b080e01401d40400c11100703000c0440c00f04c4e010a405420103c0c183c86d06030798444085450403600b210f0b500100d0800000081c200403c00c1d0000d40720344101411200581c40b01ca00f00202c01a600034071000b8004c845440f005d00600600650003500400e0141c1c05507140039141c2904403003040d114841c80754000000000050354225403040c1d201084060b442c090101c035480c04000040b000d100842850b40342d44d203500b040420030742442140c00601d0f5050841d0305142d04001000c00d10072140d00060050070100042c40c455030354100342d5000396021144115119010410020740d105814a0201d01680c6540c03051412580540041ea00ca01320302e2341e555142c0070001c02440003a101d155a014203d540701d01010901c0082621202100c04440e550301c0c4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 526262742 1250 526261492 526261511
    0xa09031401090b070912030302340303060b070803010303030f09020604091e061a030c0c030d0f1d19030309140a0c0e0606030c070206090d0c290304031b0c030501 71
    0xf00c808401422130030500a01410410140c610a01d0081c02c26405040068848080000842d002c82080100c1c501c603c04082400c0e0513801d041d010b41155038001d660400205444000c000c280f032244c4240a8840e0340140010170000e8404c7c0c2003d4407542a0080109469502e5404501e0a0708150044000a621092007107000d910358102d200c402420460b0507c03a03c4c0c50507800200c54a69003064440c0d0b1800040014180b400f200210390030600038004403990f41041c0c10040d0f00410b1740d4180030074000e090440c0400000303410300c1060440c640d0300c0080d20118108420340c24208241c28811018162240041c1d40410784404204001200003000f40110f0300107032800340c42d0181c0b1608002c03000c0c1d048906100c0c0c80d8031442c0c190307940564100040341e5180800c0c00001c41c14010f00d01c103640e1041c4041018004c002c0d6040a95046030809000310f03c00080d05008440e81200885903a140030b1003d01c0000c020030310440c8184e01c4d40e2a004d9032420010496112049070070301d10380041e1100e0f91580840d0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 526263992 1250 526262742 526262753
    0x32915030f060402180705190504060905060a020c10030b0d0c08280b070504081603170a050d0f0908040e0f07090303050904050403030f1a1c0c0b0a0903140109 70
    0x780e4a4400c00300190003645003541c0000c0700580e074508800d42c2040301c41c0005009034098008c48400004642d00700c208210b01d058000e2142e40301e4010360000520042001685003000d90565218902a8018040e2507244c8800d02000c0d00d070b0b00c1c8800c02007580b2244030420549510f040c04006c1802000098113040c20070791000d10b00a115022103009114080f110a201c1d0054001d12001c9c03540b00c9841035868680c40002c545070b00503a080004640035111a0103a00300301880f5501c1160f03c107000c034a0480505001382c410341c0c000c1c4600304011980400c2040c400040c0d5030703c020720501e140c40b000142800325803500300c2150060f4101103c2040c1034410b0044881c400500164095200d02d00803414504543c1d00401030f000d5902140c1c0519190030208040500981103403401040307020041122034038240312203150b180c203418124014680b42c0040c03195a899009503105160708070300382d52a51031900300b81c03c246a220340b08076820805146d6010001076044904801809404000490303141d00d181041d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 526265242 1250 526263992 526264003
    0x150e030705040905061f0b070308131a0f060a060504140307030b1609152f06090309010822030c2105070b060a18020702010306050a24050301050a03291503 68
    0x1003a0844080c80410407040c108902103232641545443c00c202252115004909005000b480082c80110303240d01c8541900190b0120906c115401c41c2812040c0d15174034103201c600705550190000050040009100d0141403904110054002600310303104141d8a840c1d003001600103855840c91105104480880c4950101009000d0041c0e041e40c8095141c001d03202034454101e4006503028072420810790841d00469800d888623040060003550028130f0300040c1140c90350700c014251404182c105022a000d41502010311070701d05000ca00d40f5442209944090740c0a0302030032800c43e011224240d9880c9101030300e2006c04540511601d44548814042c68400c0c032070131000700064003941c0d1030304003040400761a0b03c940c03000341e08440b00181e1392469400100c1c040d1200381c104039080a90300074001a000070b900b0003002d00e000c029415603090520b140044605100a1251a83c080107082c000d20110b240120040c1013601100520840364507010441c4000e05411a9201c0b0004034840c2040c4403418180300 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 526266492 1250 526265242 526265281
    0xf0603101d0d2309030c010806010315060306061d09010608092e06050609030a0b0903070203060c07060501050108150114090904030201090b01050612130503090d060204050301060b0301150e03070504090506 90
    0x1a184c140716100d030100365182a00541e0b18100b12600300401e1050340294881c00034401241e174880490b030344805e809400303044640302d050005103080140340740361f1141e13413050749880400603c072108c9039207440d40854030582d010b031910501d4007503a008025580c0c44248440b0752840707a9180940e4080500d0404c00450308268081d07401400100301288655401141c4209a55440310b030f03080c0c46403621140c09285002d2850020341510608080c070914000c2800034000c91403181b441400079030780b204011a07003600240e41e40705400e0100d2050891540c001c0c1410410072001e00c07403450410343d401000503801d207401d580075800744c2d642d08a0309040c4408426058003502007510102e2402440748105001a07200420003802900d004e507a250400c070041c011150261030007403442c84180001d0400b0b01c02540070f4400e2511a42c40d200c00052920b001a0071340341210001982c0301014181051309840021070024800d0f0305010b000c90203d90b40c0e8031449120002e9001c0c500405443c40c000308107001c014030148 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 526267742 1250 526266492 526266557
    0x40818191a0f092107062307031b062007050f0102091018080303010b1314011b0c03020a090f0605030102090a05060a0203130e040b0f0603101d0d 64
    0x400120190394000321200d41c0390594021141c440c1440141c4400f1040310340913540342c003550324000340ca0390303200c00c0c8000180c0042c40c10f0040483e001e06040708034810110014041481040f11075809800805d54a8442c1c0c01804041480c104040e00580c503401b410030103014038000441e80f04c09100e401c0064488240040000311b2a00c541c0c200024010f541c3c03601c07128100220000700e00d800460241200e0000c01000044903100d584805c100c0d1003640100320f00d004521808000002d54641c10300c01c02c444003006031201c0b9140042c507510a4407007072401c54143d82107aa034410000040c1c451040c500d008061002c0c00040040c220134080c0140d4160764070040c4607a005201020150392603081040440f5001c03200947d03030f8070070035070247e044d806900c042020301440c51100092807560000c03400c1c4110310511401d0700c269118680200c4410059a65a416074080c6012010290b800c2e4444003661004004401000c02c501c01814034111540703010100044039181d1080d607000d6031007501c094800048 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 526268992 1250 526267742 526267747
    0xc040611060f13020a090e03190311030c18030a0302010f140405030a030510090207120f0201092303070609060b010207060906020a110607050312011a04030b040818191a 74
    0x804040740c00d8003003d450808052a580c010b582103545200b030280c010700703001c0f00a101d0010007100c0705840f604407040d000c1ca0f0680c83d802c66510300388244210f41035456005c11441c15911192442c403001e811841201090307807058201c400c41070f03504000942000b03210340e0000c100c200340101c0c0300041d070302d400c0890070700b008540e070620000a00220980e01500d016260000c1c540e80c45660394607141c3c05a90100c90141c0c070000d021020b12a20b1400210511040e4072001c901908040040382202c03208480507122400d848074a81e070b44602c400030780c120641d07000c046a0030450320b52501c00450f00844001c81d0b1059035070780308035501c2d60140503a000900e4242000041c00e8580036000c0c0d1124540c1ca40201041d4101045c80707019620b45049d540482e4004007100c2d1543d04510007107560b010203000d5140e6603047d1110b603520081140c0202d40580b030780100302c03409546032941c481e005a0801c070750304400200149080702046d294450303244031181500380b000b01e0440c5090381131031413202241001e10900008 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 526270242 1250 526268992 526269001
    0x30207021f2003120a140c04030303060b0309100f15060e0f030d1b0609140f0609031e0c1005041a010902030c090f030c040510061119022101050c04061106 68
    0x4411364402c84480e404401d00341c2d03103241e1210010b020451500350002d051006100c4410701c80c0c806003050340e00c0b07500c0c10803c9688031000e07070105000c01c03038040845034000382c440460568075800c4002d109168050105020724200910100107815421150005000c1310103040c5501e0210440780b03000d40141c0151500c080c980b2001400e914420111880242d0383d120110b0421905030321540b4400e8011140030040c0c050004242e8a40191868980441c4103007000f088092102004075101c1c00e5032120f8406030840e101244118680102e60713031050a000781a410801540c003801002c0c49540b00700d0203180c013081c83c1000c24800b140c0603000800003620610030000c00d03412050072901400e07030450700440302240040002e854000e4100785c25800508020078040080c40d190302d0502904c0d0591109921051000c150540d40e50340b0a030040340c4104454420b8001d0304050401c01c207401c012a0312181d20050040c0d629083d0340c0256040e0b10b5040000a003008801c0d0301c0803d20350218800e00141aa40c1071 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 526271492 1250 526270242 526270307
    0x28090c030207062703180914060102010515010504150215180d050703050d0f090203010e0f0c010507120f0908030403030504140913030305090a06060305070314070303081501030207021f 81
    0x32201320040522190712440280d079003059a8040c01494480010700020315030040e5a0306080007034030322601540c02c020210786840c90848107110f02c10010780d20b240c24949440010080c04500c3d100820075405050250356035543c01d075051a00ca050364220064a5048605099142c07620000c9442c041040901032100000d600900300c800342030b003e210215a00c1086000340e00208010f281c002e6156280008042c0c05c51408a80c07400c1c905502415129600344043c015603a078480d44c000100019416818194000c0c018654080790440e9440c0c4601d07841c3c0c80750051417841d84160001d60205801203001c220319038224140b2401002c1c10b8030421020304080b6104402aa6014070060605803a0000616054800c000c60b05a03540c000300b050101c1a600c1c1421038030348005000582d00d040c000210003001c900300140d2902103076410380c0e0703800355680d444c40741300a80e214002240d41015000c001c1000075a442d546e1961140034950510a04e08168a2010f02a411410081804072800764076080344000e = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 526272742 1250 526271492 526271561
    0x7060f090602061303030f090b150a0b12090106030507030803041509031209020102191a060d0515060303040f170c030c0307210f0302060108190228090c03020706 71
    0xc40a684600358130340580303400d4010742803000358018814a4207541c0c8043c801d0000b0820300403081800d120b040d145182d0b050006118036070003003112005040212114102114841aa000c4198000000d0f450303141e5594a0600f501580140c40a40e004401d000501035102410b104003070b442a400c002404280e40d0241505848445030b034040d60b600c5c2900c406590090203e4402800440882205620b0b28500f0200702060701d8074084e003070f01000000a400341001d610320b10f08250484001c0495003d80c00c0ca001d241140140f07450b405020a010004a200c2c1000250000e000c501a01040f0b00c2002c40d045880d00114140640c0319030300082c07015107291008030740001540c20b80c01401140d841d01005c042011680c040e00241030160420812050580c04a03249040e100c02c8001d6a40c0403001c17400240d40744140b0303e0040c1d40700c190a00c031100e00000c0c00b40c9290034180da001030000340a55510852040307400051603032012030b40000c0e400301008114070030603140c0d084001c82d44550303a1025503840e00c4103 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 526273992 1250 526272742 526272751
    0x160221071703071218020d0b10090903090302040509070e16030b060706021c0b100806011b2001050c0c0f010c060603150e19080d02040f030507060f09060206 69
    0x1000019200040c48260060741a0740549508615628140088010420082150142d0f8039500d45030b406201802000d48800410b5001000311200b100a511600b15080c4090604481e60784000000030361a10240282d1020700c1c000e44465511610f180144015104002c01d00d80c00c40d008000288111300c00e5012081e000407401c8951004c10b0041d803416402000c03102417003035005c507000c10f003a010090030390010401c003041010b03a4881d0b1907081c2801c206640740181031607400004620713005502407098101c60340c0f2440500d400712a40104d00b0b0b800640301d40c02401507941d2030000c1d4034540c500780303d094900800366084c600a85040c020000743c41e210715040e4041031080740b04008098207680304019901c00e035070700308104210707881c1c3d20300d400640000b4000f50348043c1414500c5290b529003002c920824620007284101813181519650940550f0103520381801043c0c0c00c0c0008200303c150b84a5100256208900400340710342051405840c020050b41071008000c8480000d01000d54007040d0035420 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 526275242 1250 526273992 526274053
    0x2010c0803090f03030c1329160b090c01020105070c020a0e1b04080c090a09020102060a3c0b060403021012090b0c0a0e040e0312150d05061602 63
    0x76038646140740c608080110035114002c0c4404814040c02400d540000e040b1031100c8604106210307030780c40c03144454440540f0340361180d04c003040a041c203219104004110880d500641203085c80700581d900310b80804145c0301c42c480c03580980826407071960244185900f220305814a414440c6580c0e002444010650148a9056044801082c040c580100044420127050110380d038170349440c0d10070655144640701059104016a2002c151410038500c101c00580c0e806901138510307580e4800d080b101800708500300d03800034050920000142e0180d048180d00050000c115030541221f1510b6013004e0382c2c502d080251190000304002c0006982d07c0108015106040c00c00400c0510031400388001403a2085002d815445110200200d41400000514070240d264841107044980d80052108030356040d005501300350700422604100120300c004455120482004098503800e44a001c210003408221044500c0c0d400703a4148511041001800b842146191000704000814510384084480c140100c0805 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 526276492 1250 526275242 526275247
    0x70911041701022b1505150a200d08150f0919090609020909010e07210f0501021b060606072d0804050a092918010b09091302010c08 58
    0x1c0e01d0007034040d01d503105000c626103950482001491081443d0110000500d40d00d043d40702601c1048140340102900c0740a808203000b43d40d00d080b480c24542c003c6041d6001d1101d1210509010030400d80500000380001c0040e1000440d0844042c00e040b07400340a084030448080e517001d640d515400c0802604480445400141d034451007070360b6130030041c990000d6100c90f05141c410000d128142c0c0020308001d01c01e03241c01c482552034a4481e401c0350b05820710503003079409c40340007040b1408840311021980300b50b0401100c0a00c40c2da07654280d210700c0600b411126a50003040b03a010900389400b1004460503a5005890140703000c400150b40c500c161100205400031490181888181d004011402407162641c1c94a130281c2609003403000360014403a40d40305404001c8041002202e50046802c05401207940d8140c42c002000030143c0d082054a00a0b040148505004240140c030200c0c3c5d40204010444075031f5800c12401400b689500042403e40908440030100c00140d031b110f40208080c83d0003407892034 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 526277742 1250 526276492 526276529
    0x30307030e0a0308161202030a021e0c2112040f090c03060302092a07170c120313211b05030405120105190e0a03030e101a010207091104 60
    0x1a044a156007010389424400715422800070030305c0e0022158603001d040a0060140c141000326580d100d400319446c0140c1007a4640d0382d41c10951a400c0020325240010b4503003180310280030418041400d0070b42d0b00003c00c0980080041030302446a4415002c41c4111246407078207040c0008400240c5205281406956600014a8901c0b81e4050360180d58020214401400c2681d00d23143c031000400c46031401d0300d50901c10000c164255104598980d58800c0041c00381030800b09503040a50007010b02c000303881c002c1400c60208401c1c5000250301c40c004100c16100c041c511410f140d45a90b82640d080710300d1004001e051481140c000c0301980b42c0940d001b9000c9600c540910702b69045000c1c81d489950004101b04608038010010740080d0311820400460200140003100744000b0388541c042c00b142c2c1130f0080d034010000700e4440d4009210640b9980c1c01ca80000c0b44550290003200c0002910f003001c04c000000440310b543c2e05000c204002c0c02d808506100051840b016641c0505c80d40c421031805018038503541 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 526278992 1250 526277742 526277749
    0x106090305031c06150503060901060e0a170a08040e01080c0d110409060b0301020301060f0809060408030f0a090b0f160e06040b160c06030e210d020304030e030708070603060e0402030307030e 84
    0x4409800000501085c3c0d8110401c05000380d00240c2c0d03514446e07001c8c2000410103a01ca421002e102d8003004008070a103e00c1d00103942c00259440000380903e0151540321400706020f60000c2004001c0c1c0b1400340c0311741d032501400a052600c000f10302c0744035003d40d070096404580035100d5449500e0342118001685401842c0880062003000007142d0507500100c00004c80a4110358281b40d43c44d255140c0031580c1d910040034640303e05045400800322142803010400401c851002503904c03401e00100082c245040d619600c600603400c032802803044c0140010801c01240030704494400e07645900b00703c0903142c40c0c90b00207a0b41d80224000d445001602003065615203400c0c2102c240307588e030021071501d21180c440300024003804100c6500c103414440c801490b101e0b00e00e0700030f031345c080c018508907135034206105254100b0107540082c001743c080201c103102d031003c10354042c46840000c7c211000200301c070b9403074020090b00b82c4c0c41030b170302802840c84c0420401016032404400c5400aa5161900c0d461405070200003 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 526280242 1250 526278992 526279001
    0x30c0a0b06030f0d0306050a06110a0803070909050408071202061b0f0d0e010e0c091005040906021c0b010e0d05060606031e040602040612091115040b1602090106090305031c 76
    0x1840018800c613100d41c0380c0c2c1605513200d03c040c2c450540c0c1d990380041c4c803000141c03021802000e030000c182d4400071400001c6405070020b15005499846c0050101d95102c103588207981c8140c406464031400052154100110b902100c4c0750b02083d800540f50507d49103400f00c0b4034100c09030f11003565010001d0520380c0c0e907001608907042d10010400400c908a00c0010303003030003406141000401413142c1c036000080d902d403606c1160701c503d001c00540d4202c2030a1109000242820010071964280c017400103600450032100350b00048840d070320303000604041c140001000b001c280c880b540c2c02803d803d001031010580103c1c289c1d903c88000c1d0382d11aa2621030164400c445580900c034940213000b200305010810000390020401c44069580c3e8483c40e00d51386980d801168001c0b40020410150507409203c2d90514058a030940d0212062283c2426526030001030590b1041c10070f6091400309580741e00445c602102c0e00c0340545560320300803451500310f980d01c551f20b1145070507024140e03080400c0c01d03412100310b411 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 526281492 1250 526280242 526280263
    0x71409040e0a05060603010516110a080304121d0d060b0a1a070b09060709060c0f05011d0730061119030c030b0a09020f160f14030c0a0b0603 62
    0x4104001210607418a44460b05920308480d00e00554000c50011315050140f03c0c05144c40300101d04034031030064019200c100e46001ea04a5a014500a483c0803a11000180d4441d83c0901803007510200c180a0092695900c1d440d0f107001c54850688c00c02580d01d4040f501900503030712440005280903039100041e003080139548000450f401030f41c901381d181c200d100040c0c0285803080700500c10503282c02040b1030b261001101c000000031080002000200e2284207a0245203010b844c80c901608036a480b000d082d03070030060380e070700300302c0c0b40340b2000040c01c0301c204803000c0107104e010130309824540c2901143c501d609000b4040b1540701c4400139000b06001c2c1c21ba102c1d0101c3d11a1800c8a6612500031009042002620600c100841d00e403440002c0c03002d0090003201c843e0708001f040c1c02c08060402005074000d411110340280100030601000495100007044111854051121a00c50b40c005141024000d490020340309580d81042c05441511500007459507241c039401200c0c4000c1e236803100d0200c2c2c600000080d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 526282742 1250 526281492 526281499
    0x7032f060f090907020304060804032f030c07060306030507030303090816030206040b06011d04020a091e0509011e14040b03060708101517130c0303032f03071409 71
    0x148409225041d50010310107518241c96030794860f075889000366180d000b00d109001c0400c12100c0000c001070303c0f406501c3c01c0514482c2100340e5a10610251201c1400a10001180c0740e00001e205000e80d41c04100c0b0300010055031a0510500e4115a2499100c80143c0300c020281915451140100041c3d902900c11049085880079149282818029039440d0241c40682d00300f00c0c21008a8615441100100f2030f00f510405481c09545085060000039404120600108058900049280050021580c1d40c1c0c2c030074030380102c1b9000e0074642007000c40c0c3d034103070321400d4043c0c0c8802010342c18521198549085841e03220010b04003d94400200b0007030480000c4842c2d05000e50402c00c0542904001c03c02e0140500803400c0b61025183c80507900c0840038090f1990105900c070101e00c0c20070701085155540494255032061100741c00707075a0641910700980003100403d84441d03e455004d54048024201e10080b021840c0300c403048a000a151440042c1605080020644400003060041c1c02120350790280507 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 526283992 1250 526282742 526282747
    0x9030c06070801090b0906100e032509050c04060c060c050d0c0810060f12090204140115020f0102070f020f030a020a0801020403050606121e0a02031203090c0307032f06 74
    0x801e8000d060080034007403409014a0058031400710b0501e1940c00d0700c41c01b4058461a01c0c60500941134422a250326910b130343c50701c1290308002069140d0144160895140e0102e051740c0c0d41402d03a69010f640004011100c0004103010400015501401c1030016a40140c0300141201e4103142c2110240308007030607850450b00b000b20984000354454100351281e404030001d80c00b2203842e41d4003190204000c10100d070000f801c50b043c03009280d40303c0d80150815480207000090100801e8803080310b600e000d0303000f41c1c680b6904c840c001c071034690148460118009644021031170319100342d43e00300a4007041c0c00b02901440703007201c4246640e20f040042c009000e40082c16a00c40030764a0a44501035402808119141d02681004c14004d08004825059000d000c0e03010b4070303544516242001c41403641c1c6841c2029807150a00344009a1018406464100ca04124071a41c81c50111100c1c7e04c2c0403a40c001d224040c0c2e10038002000070a1440340c44840441c0c04444400c05004071000110020b09422401c0382d0042c3e00 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 526285242 1250 526283992 526284001
    0x150d0203010e04110a0810020d0e0d0816080606160302031315030b0604180c0215070c031b031e0917150f0907050628020c0909030408070e09030c06 65
    0x100a82d03522592040610f0305820409105002c03040da824450403625510904000d07039050328a801418190701d521100107840c0d104d054156141002c03203026200800c440500740b04940060032601d510803092402e2400313540c20142e0200e1203038030800d1940f010b10384081409404051092048810881d04020032448868031603040482c0c240c5001c3c59000443d10300324030b41c442c0b82443c0d410b840c21220300540e4144030452104001001d0308014a00c0030840c002e40665a00e0410380440030b42c09200340d0f03960f05260071520300c0c020708000041090340d460b0340500b105501c00242c0c00003002d800c1c441c07035000540190440070340a0701e00c022550080b941e0450800d07500410008009003e41450b165024500100d80711b00034090b140300000c1d00c0001d0280c000032014022820716000401e111042403403107401c48a4409034000c1000716000b03039640140c1081111411a00e0882d06840d04220b6043c00b43d03281c1460001c1e0a580d031403043c4030305500074200da80040d64008051040e5543c2c01c81030815588603190 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 526286492 1250 526285242 526285259
    0x4140a030f030e1902040e0102120103031d0a0e190612050a0b180a06020c03091e13050601050a03090f0204020c101b05040612060302060a030b15031302150d020301 72
    0x34504000000e450312040c0d400300580055134628240354a1000c42101e040c2e0340034400900200030751101c3c0d030b64007000b442000345640c04d800350007180070359251104001503100303010f0782151074400c1902c83c0602c10030610030782651000180d000324110310002080d1180140c4038002e080c0710343c80b22284c8091800c440042c010301107203034601d151043c00411890b50b1048294001d051012211120f1039101c0f011080002e1815402403030b10b200c81c44100c074184250f06000888015074040103103010400922a00040d0400461850740005965014003080c5400c400003012405501c2c2036400305070321240034606125042042c001d900d41c010740207660721480c1c1010140d840b55420341f0080c1440c541407640c665132002180c20444010a540c0301450245011304c100e592020746d1400c01c0790103541d449d000005035207840c02803803001d00a4801142c1e144844e02040801c0340d44a04550070600c2c10006c100400c55507000402029034129411111034402044400c854000c0422040005100000102d9100b4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 526287742 1250 526286492 526286507
    0x4090905100509030d060f06140f040f120b07030504150b01030e06100e010806090715050903010906050601201c050c060f06090915070302160204110a14070804050904140a03 76
    0x5c1c1d429038240b0a099a40c00c884900244912500c0f001503440c0511500b56151070b00200114410380c2600c50829072107171f1044114040c2d41e44280701c0b6443d48810b0f2000c0100030400c0075409100380c10204120315081d21000104d038443e0300704184c10b6a41e4000d902e0503a009a202c0120000060b08480c414a0403001803075582c24140510245464400000111140700040c11071007103040002400c2610b140403218940c1060340342c83d072414040d090000c01c401e42c42c02d02c944c022041c0207440119143c00c05c0700014001d94102c825070789680f002c0c414049030b416000603881d0004200c02440d0103a200c40b10000b2106030080380d801e10b003180505030a025403120803070140d9000b28822680f03900c90351a07084800340d94030b4604a4101c480c400c0e0b8400544124080d07800b401c0d466241c40c1141103000d00590000b002c5407424402c00c0540704021556000065106603d00d080580c3c49044c1454024203807140d40300c50085105079803040c2c00400016003041404502c140c4e8001c0c0d50400c85014894900d006007000307 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 526288992 1250 526287742 526287757
    0x5070b070c0b040308160201030e03070b07090b0a0e09070e15070209010e0906040209191104090605061e090103020912010e010b030705010f122408070602060c0409090510050903 78
    0x140002c1039040888040f10100d81d40940300510308400381c0c0049000100c20141603042c10b503503200140b0300d2803080c8002c001c054807844032241a0310348001e01034418083d0385c01c54050004c081c41403040380c541103000002192000c440d400003e54510300301700d8010307000c1c01e402500410009500507040b6016409080a50701c21a032903441aa00d80341000034103401184e040c0e01c0b40d44188046405401c000079030b142c1081314820f00540c043d00b071400074001d8135406130341c01d40302900000782003201e140c091003a0005804102d92092800ca00c51090038149101020807500d9800002003588050380a039045408501c8090650031024030f400d130001e4001c00b01c84402410710750802c401409140742c041810025900144c44d40c03410010f1010048800714854103100340200d035140d10941d803042082038042da201c402c5501031101141003142107414444030b0792040095501020500030700d04032001c2910306030b40340d40a00042441c0b0f10309040d407404114110008030f807441c110501007540f00100013800390 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 526290242 1250 526288992 526289003
    0x2215150b18060f031303020703050d020705120f03221d09010c0309020312090105070b1f0e0106080115030b0d0305040f0e041101030c12060f06121802061605070b07 72
    0x141c5040406000880c8205142c0e103c030344000b0800601403030110341c8620030036400380c81100d1034242c59541d228035100c43e1020b41d0002d40c1c002c460070807452504d02c2402d4817440801b40039124a20545240aa880c0540c0241ca08850041c5e60850103a90074584200e00401d280c103203841c4512001006e4001c003503821703035101106500704001056030f5070180c000c0c585081d9014005204204816014988030341003144094100203081040c4030110340001c200e50b02441c20b0441182c8108004603415548030b800d030b030140d0002d61088004010980c0c11000e49070464558000407121800380090480003400070200451344214050644824142d010001c1e2040e10b10210005001c1d03601c82c0030a021002c8221001018000e11000041d0325511a800c1104011130601b0321002c0c8040307070701410007903d0b050f4100350201e03000a42c0c10032205501c0400003440c0f00380b1032010801910341d8072000030100e40045004c0d0190f10000b40091000c960400b004803a0b0380c02900369058281c46a05140080d81300344070650b00c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 526291492 1250 526290242 526290277
    0x12060406140906090d050a17040602191b0b0402120a11090106020c0a18060e0703020a030507091d180d2705010801061409060409020d052215150b 64
    0x80d181c10000e80303140108420001070010800f00681124154001154881002100c880814032508d681100601541c4203040c0540c81e03036014106035500031a40d004c0e4030100700701d500f0810039043c14040e2030f800d4240c0240c051211580e5a001042120b1f4104692003418451070f81c202090110150340554020400c40c0c5030a03403a6640c10080b030380c4054802e001540120309503801c126900b10344c880c644400000e80310100702e031540d45842100d645030840307180740442d8001508088156051182075444078290030400700c2c49090503040e110044046802c51071101e403440c0440c0504070700c42c042f0001801ca03582100d00102c007032040108184030b8405243c01400700c5564921807070407910128002c0d03560603034586160b60700c3c0c5941150401d82000d41c44100080805c41350145483e01c00040c0040d080da40001360380c8a000040003421100300074400452250708420094030315007109a02e103507940d0000052100c41c1c000364480c0000300110713503e40b00070303030074110700022542400f07000b4002c8000441c01c80403 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 526292742 1250 526291492 526291501
    0xf0614150a0602030a1403090a02060f031605070f02060304150c020d090e01060e09040606050612010e150f1512011e081c0c03120501170c06070816021206040614 71
    0x3030780c4e4012480d0640101384e103440c12851240d010701c083e40c1c1c0940341d40126016100c00d90045222580440c00103d8022800405c01100014075007440b8901d135014a819841c0507456101c0d0f090111002c0c200034450800000032038184a11074648140d2a02d08250801c400c204542001c1d40c2c40741242011000704a6040e0005a407441049206048540300e031a20804030101a04212141800500c2142e0380c03641c40d000410180c0f50000602150381002920070520350402d0080707480e00b60000c00303a010003550400c0407800c0f621040131a049451064907103492824100000144074000c441e989a03692090800010707009500065030000781614540ca001d000d51035456103522410307540900c48282c00c840242032102c901c5484100d15160180c5000e8245402c480c0c145425200b0a0307004d46c5c0d0f500c0360b5280400d40484144066000341c1e204031409440d1124517a244184d50282030700820b1225400b8800d4400e548030007117440c100ea4814816a540b5160924240c8000e1080e160102c401c000c003c40002d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 526293992 1250 526292742 526292747
    0x1020309070509220231050a1803081317090933041116020f010c03140c030c071203020d110a06050414010606020106030b06100c0f0614150a06 63
    0xd0b4054261603243c13980301400404d0264a2400e0010100d17044681c0840480c01b4513008852012103498041c600090060540d0803d003d481c000b4003284000317803a0002c07402a6070040e003120002c1660604100d1215620f0001c040b40c20b55102c000070b03112100c0d062031540d070111008010300f4115402c41d5402c0710750301d40205410744002c0020385510500358483c100e02e8003400420414548030b600500106080b402c0c6240c4515607003201201100c0090020211070452814040364042802c0c20720b0b0030303050314a0640f00104250087d44604d80181000030350324082c14010710455880303182d840c04076800e0780e64032450260011270500065005010b6101d20501d40792003100c4840c190810140200780f0110719483d0b80c00180380150040703403811021611810116028054800240b055800020342d05245003400d41c11050300030240b61043c560400501034180c1c2048030300040a03007040715800d101400780750403c020802c5171a0b244400b035801303040180030b075043c8170640d44d0301c041a50a1108280c3c0c58405 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 526295242 1250 526293992 526294009
    0x280c050403051e0a0b0405010b0d061a0102011505011b1202161a040312030e0715080108030306090106050c0f03070f020f09090d030e1603030201150b03040c090c02011508010203090705 81
    0x300c3c035154020310b140b03801003540621001d42182c044c2e0000200c1403441030020b510000040d4003240c2c0d143d280d2074810140c6000944022a104003070000707224241d11004815002c201070b000b0349040c81440801507688541e03231041040c460380d2000d0301c035600c002c207104065a108442078080c0c150950660010030700c13405101c031980407032401c01023540c203050641d52404109140d6400500070140c2c0c07115000c0c1c4103441040080003e004034513846110b102184c41c01086620141c2288441f0b6000304180241a29540031a50460340c1e180f51840e100c0c48200749040c10480c060145401910021031840280300c00c801918141ca842111700745001c01d07582080c429245c40c1100c010050350003410724250f0850107500203203101201442079440a101228515504e40c3c0b040e001500117039511155404419982e50b4000e000c0e1800703030000c0381546860f41c1c404c240342407180a4140140d8440034041d42d8103000f50810400c014000c01d080b01e0b015107800c9824000c1d0001c07a0392001a200394040040d250900001c03 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 526296492 1250 526295242 526295293
    0xf03190f05032e0f15020a050c06031003080f0a091d1902120c250c0b070804090e0a0201090504180f02010e1519050909280c05040305 59
    0x4589085945074003000c1100010350b4002924080c41050200c228510480c000c8044c280410740c8055403410f0421081d408107540c811365041d54444940c00000c034000241c015504041120300e1541c0380e54a517800c000c0c41010780e100801c0340401044610180d0070a40144c0b44081d440d03a100c904217541e40a01019241e580001e134442400b0a0000c21000c1601e000303512240c800070f040251414205050300c05254800f162115003170f42001c1540301400b050718123140a50106181101c43d41c08084d100c01e8200c0c0708c81d204c0d20301d601038005100c4040241c0705d03042e200184250b19082001340740d281c4890351a1140c1e014100d00182c1c80c2a0049181d01d441c3c0705943c440c6142000c0d400c0c0d50388155550b02d00c0d80c64800c10a07414812400c01c02d81c000d41d1091035940408030b1580440b42c45412107004c0125401c08e4101070401d20006001f103034030796190200240d901103040c1001c410040c0003030b00b1920312100c049483c00203684c2080c8840c0c8015401070300400849100ea0205e4066000c03d580701d42d8400c00200 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 526297742 1250 526296492 526296497
    0x108011a01170601030504020105090a030303060905010e0106200a17070501051810112a010b01020c0904020607020f13020a1b020303071407090501030b0103031e080106030e0705030f03190f 83
    0x42c045160f5500c03a0b4846a40180f041c10403030326160030900040c2c01c086466200700d0000f0b440310300611134000e01d40105401804890349920741035040c00400b9015082089045581d82c0304071946040304041000b900d0741c069080000349180d0000050411703900c1d44264400c0d103940d0309040101e600451002030805924802a010f000248900300f4a00c018181d010104c02c1080401e1151100c08540054600e030644140903240001284100045095614460402e4199082100000442d4540303001c21540305604030f8905503103c41610002e00d00090080b8110b401211082c600054280700d5402040e1100c00c42d100d5901280d054050b084d1003c0c0b581000039090b4100380301c03c000050a812802e11412403440c10343e8809503c030101e034401c680e802d074000c5d01c5c411590401001810f80000b440c1c01d1020851404c10400350161f180a1300fa400d041c4192810141d4500247c08254401c0c8501405007078018291200c50281003115a42e07a0001e5122052443c3c2c0404032190480c081c0c00800003805554 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 526298992 1250 526297742 526297787
    0x602070605070203030d06080f0f0109030507171c2301030f020918061005010806010203030709150512040605101d0a02031503100f0f2009010212030108011a01 70
    0x2003190650005007041381c00d4402840134002c9410140102805404a04010841066003680d501d1034001380f03984215169142c112602c0c04240e00004445c015600711030111070650404003043e150f441528000017407a43c031020515503550464221000c4040814091844040403c09a0900d4003080c07200030101c001268059006082140009a020801400c0344d000b03450482482030400c4001c81d860300c22941030450a000f03640e001000507421400c00e00c01035084d89045040541115404e0103801c644035030781d6181c1881c0d503200790300b05d0309105042204e0481a040602d0500c02404050f103421a0300c41c908000441d12110f20010310624800300700040681780c541480c404002d50021b8600404900d0000003804180c0341040540e03188200d00100055258800221a0444d05030035401e40445041c10304940a40c1c03c0d9840c0d00000c05168080c2c41c0d912195100140d03c1c006500514079242a0007100004d092081940181c00e0000c148140f030101d030300350303800440301c46034503101c243c0000c10368 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 526300242 1250 526298992 526298999
    0x230c0a12050f0a050601050a06051801270608090601150206070e0d08030f0403120209060414060d05090a15020f04270e07080f0a0519062d0510060207 66
    0x5200002035500070000d4516581c10845100d003005041c060541d001c1e40240010000d50070a4585140141003610304642019040601c039031440b040c11b00390318100f11596110107001c0c0380150000711503140030340740702c10800d5460b00040c1404034110b0322480c50b4024400005210303a00c44203a1030301a00c042d80501001d94401d0b005a070009040d1035000d40010708490a0400108404025801120800c20750b05440c90a843c4c001c000081240c1626546401440380c142c40c1c1d01c2e0841a0b500756038500744d00005209104000c9043c034040ca101401c12681400e082c0301d6000400b1400640f00d40c015030501a1f5160709800040070b900c038045042d2091541000200700101d1030034400c1d0000141c1080602c40500d000d40d02e0020f8030394804108038a504054001c01101c0010400403203042070f40c0010700101030194444c0da4841c2052400044110102281e00040110716030005003c6400003c10102100451b10340302c0100d080e041c8039511951401e0041503040943c50101e5017224203c1d802040a10306 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 526301492 1250 526300242 526300259
    0x307030c2705060318070e06091302011e12090303060512010501060818030c010c020d02070503161406070516031502120a021c090b04020a05010504060206060105090d050a230c0a 78
    0xc01005008000c170142140c00681206211450040002c4d044072010b5042040070081e2090340a04400c0185881c0035030000181d81001c007039080326001d04103414441c01e000c04243e4180c90000600c07200d00349408007880c101a007642c4204141d902c140c1c0c1d88001e240070202420b00705d03007082c02102c0c04640f444000542c0041c50399000a80b0004840a4138101009445138500355401da40d0144056001007640d0000070313604001c04401020214001d010800480d84035045c03009041c01407981c1e9004910002a00307441d00c41c121000550f122084600310f00b07201e400d84001003164003040342d1420707000703c11580c0101603000b0394144510040203071aa6480d50ba0100c8001d60040003100d060503000c801c114901d610600c1050740e01401030352080b603585001d204000104c4100d40107181440b000344414401a40e00190495100c038081c2040765480c80030000250002c400880014820b1090070807680401c8012464104801d003940340e032100803012806c1d6680c41b20014582e454104940c400c04009113070 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 526302742 1250 526301492 526301497
    0x10914030705071a1c0209030a0c05090604061a07061d030705060c0406020d0804170d0618151509050d050309090601030b0d030c020409140d08070c11090613020307030c270506 77
    0x140c1e1702e07401841c148551021a090502c407000c242e80c0a001c800c405c00403428035881583d03111004035010045a41004070396407054116010b0403944c582c0204080b0204181d0b60b2040c1c000706003105021714070700750526010780c0e2580a0002245c0b51300442c0082038a0703135507440a440503188240c010700342100300c603141120755490040003a550615001a07a021040c0308400810300c48200300c20104509040c03001840b003c0e12095212502d4514202c4082250002840c0d24400da5204280d981e02074120b500c0c08a400340349a8203c2a880b180707030032440707081200020003031500d911700761400d900913941c0c1300054003159405000d080e04041060740c46000a44110340d02c4803010300c01040014a422561541d82440703161210380d078a5035104a4a59400b00c1e0064801da52049045c902145142032a0b1340303011140c0c076500e0f0194003503000d22002c1441a0b030f0700305045c0e80351011400d00b15241c0c580050001c3c0a01480500c05011554003501000704519940d030142c41e401c0c01000d80400c041ca0700084c0005035 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 526303992 1250 526302742 526302787
    0x18010302010807031506030c08060d081210030611091c020109060509060f130e1b0f16064205060304021c0c320909010914030705071a 59
    0x1030307440170440854158152103d01a01030741d0750000b80441c1c0c0d258080c044100143c292445419a0030b211800112140101c824454000000030019218980020401c10050704010039060820f9504011100741d040038140400c8201c0300c3d50781d46103a402081c450607101d000060b00280c0201d07070502281d40648010050007501600b0036142c00302d100d1400c80c554200b170381104038603100c016003089045502c0d03100b59006000f0140304c86154071440c04140541c804c464071401c0310f840c0494000408104503c0845219401800500020031101c040c2d03082056540d51709485440710302c2d04440040c0210314400000c041c218801a0800d0401c802c215854000078000c07070340001041007007808030701440f101c41002841640c201c0b074001e003001046400300340690b00d5010350325092030310a14010460001c44026032401c0d10040c042d034851428090141022200241c6110300b95460030100200000040c204a4022403c0e1045641c5a03814400040c40c601507000c1d00300b806011451071080001c13500c1d03004 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 526305242 1250 526303992 526303997
    0x190905121e070b1e0c04060804020a05090a060807060216090e0c0d0302011e0219030b01030b030102070308010801050604060e0106210c11010b091b030c16140c18010302010807 77
    0x1c0420030615206550045400b100c452288030140400388110200540c04420155494030051410301d21400303483c003039841090100541c002c003003025511003560140182c24050300c16400b5245c00c00e003c402030b120500c1403402510842000186551000c42e0750032043d501c0001c2040e0b014076095054000d007229180007151070041c07012000107075481009030a0428423940001c114600700000f100c10080524150841c0c0c907004200c00e0380c07100380301c0d0754031240300d2110300b0005108180b109c012401410312000c0d0903003640c8009051407d040d0445403543c100d07100742c4024001d65030340e041171001340e5686116104404d03e0110060050034080d1064240c2559404002031000c101118014292800001d06401240c82007c0988840380280110b0b4043e15040c0c0704044203007000e651044400030008a48a054500440890300f0ad11300802144c40703c0c040784204103000e15050604003402a25003140103018801c04030f40e00828240941c460000b04a240121100303a03182d034006480700f1100030544400c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 526306492 1250 526305242 526305277
    0x1215050d051002160b0601020304120b0720070f0f0506070f030c02030724111c0c0b0f010e18030714190507060201140f040f0f0c0e19090512 62
    0x2920b26242c0f01404008081d4007204104400c5400c210f02e801c5070290882d03045401c200002c0c400403280f000e02c030341e141c0d1344400c2c00189592052007c40d8010340e00000300000311610107240006010004c0c803e001d442076807030508113090307545070554425041c51191507007051007404404081100300e0b50340301c0c00a000c1e0034200c00c80409540080d0400181c0c2c2c1080b81d0724a200a802131500001c0c01d900308040c00103003410386030719007503082c410f81d5441401c4042003101a010041d020b99481203a09860581d4802a01c201d1400c001450760903100302400b800c01d002850344002860b0864040e040481d940382c51024520b0460203880c0e403000600108610b11907881205140700c1e100c000f40b69004042800707540500205030920500909641405414202070710600d800d004582d118034640a400c25071041541300b0b5582c0503c0d000c0c080c55561540030b0442c45158a00060700c01141c00c481307204d075007020803010301c2c1000c0040c81e074108e5054007000342880d030050001564150400000b4011248105003000 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 526307742 1250 526306492 526306513
    0x30e0303070c0b1b1f0e1006080325030c33060e0c040e060d020d0b090610091b0e040e12090306090109020d0f061d0d1215050d05 57
    0x240120319030f48100003081000440350180c0d0410340400c1030500c1290050103043c03408865003042c2c1c44100c2d0721107114950300c9400c1000f6010400900403103800003001401010785d9a00c015440c1d40080c45400c4907000400108032101e04410895070701c0c00d505440c1c0010340b0703400e900c41d070900300c0c6802c42114188180c3d0700e83c8808518210305100180352007410105811381441d00111207540041d08e105000c2c54240000d110900440014a620460680302c400e4541d00074000944d02c0b1014400252000d00040107001c1d8072000440d6842c469200105010461a580c8086000311055480c0010182a1802c1b1043c12a84a05441200c04200800118030030030403400301e901f007150014520b0790000001035032018904085c0319095102195000802a181c42c5401241303540d282d601004000360b001084482c204600b80d40072210120400c07d884054409481800355104031030b640603000700f441c100700e800d1418030354043c8042c0195042100c9000e40c1c541001d004000b1410790084403140510f0110a = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 526308992 1250 526307742 526307753
    0x108070605090a0b16061406030c060d090b010e01060f090b0a05070c0b0d060504050f0906060d03230418050c18010e060d02030105150a020a080c0a020316080d08060d030e030307 78
    0x2418480c8807a0400710702e062807450191b08660594140d400100c0c16842080010f580108001001c1c14054a090f039a845581205400810118400a0078054554008100851a251424140c2c0c400341c49080d180c541d015416100c0c14554420f40304a1a0200040c00c0d00d684280c014011440c801c0e409900120b4907040000900e402813511420020740d41c1d07008100510b40742c058a0382103c03040030104441d061403800e1544071000101600e001e00d2440300d482007014070861502e001c1c2201c0442101701c580c0521221802507129105908030ba180321100303845620454840e49000d0050540000c0c500b07802d0030b0078540c0b69000a07120b181840241d41502170755441c0c82006207a45c00c81c50300c2c01a500d605010400501c50141c26030300000d410240900c04000b9000103d0075081d94020f483c0c142c5440c0480d108a2a0501040d070094060003510700007401c003a080030001040e144203206540040c840d84000700d9005504540c1280e0000b916403013040482d001d08414550700740090281d038075051003903c52 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 526310242 1250 526308992 526308997
    0xc02120906250b0a1505120601061b050601060804020f010201021216030f02030a1b0c030c02010c080702060a0f02060a0e030403121e050903100614040b01090909060e0c06030108070605090a0b 84
    0x1014131080d1204201840c03450b01100c0080540411a0802c0b0202080a40165142c005005480034412000482001121140759072010b0030344c884201d800568551100404885d02030300c00720700440c4040c400459960040c002d54005040e030441c0901590b031050901c030413080c0b000440c1002e2580d00c1054440f0380e000c40c0000c0d446526200d42c0421080150110440d503241020111820800d00780c00600000394400104081c540c2c09107001c4c2c8034440c043c00d000e078061181a4009611801c0040c840a043e42c00c850819a000c281d5001e0312800c0d5202d03111602503031229034966078031380c008000a000150342e00d4000f444000031031500118028010825130241c001640700d1102003600441c0181462030f040013290b6040748261001c1c4007075840c103c111b1500036441d00140c0c1c4282c0d207070005120a64403ca2082004041036070702403107402264240b18004000140c5040001e004061000440303080100c21a070494a83e5030042085038a00541251603401080209038050000200004c1c5110120301 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 526311492 1250 526310242 526310251
    0x1d0a060501030506060301090b010605030a1b0c06240603020c0f071d07030614010c14060a0f11030c0702090a060308030f010e1f050d240c02120906250b 67
    0x1400612075055061035450312200034039592181e0b040101040014590190b43d0741110400d00b012500d039120004000042d046401800e400031110300080301d40d01c0d40c0b22000b01c213494000c10040140440307240c0e00350520b1251810b066194121010100705a40c425801004011601001e8513039054a11010601740103081c1d0002e5958901d201e0b0385904442c0c1c043d40190003502c030b81810000c16240c143c190304461029010281405010038006052083d020186d6181011351000c0d504203140c00d211440c02003101c4100e80d07900b030f454814580007110341d400449000700e4031011200c2c28045164204007405c040107065202c281d88600380040040d0340d8030003850091070741d40d407100401e604040b88000c421000400d8540e10340481701402d103030341004078004401d95000380c60110403290a81881030105004030108488404030035182240340c00766a001da24110401e030709451038183c9461030760840c1c1c06403071055944203400300440c0c48043c1d42210200460f024800d280045a96140c85100034140100c0d03 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 526312742 1250 526311492 526311503
    0xb1905090a090c1103090d0b0601111c0f050306090408030603101b03052d07090b07080c300904140f010806010b04030c031e02060c0c04060504020f030601031d0a 71
    0x6103583e1050b60840c0400c00920003d4000718280038180c00020790034030020401801d0031429101041159210f1802028401c0c81001120200740e4003200546050314200d2500c0f0004289002901d200d910400489001d0040100340030180e0300c0f180c076595031983c0054a500e525100d840082c6102d01001d000304401d8003d9a80c061600c0e82d1041400703010f84600400c5244000100340b071030410310390a03c0390400640c041066111480d51a090140d138403142e990005c002c060404204e4a04104d5200d004206070003802064404000840c88130305000f04400300c2c803507104841c0296030801c498043c000361001d5900200003203030711000c80380725034035107002901c505141c501448014884003d00f080403a0042c48150985171625245490754402080c80740401840d41c010340000000035140420314007c41ca8004000a54070600c00e900c150b55828010071890003103092000c0000d20b8079052084c1c035070008580448500d036075a11001100100a030100b100340d61084402d4aa009103010008040c5c0c0c0340c85103 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 526313992 1250 526312742 526312751
    0x8072d03060e1302040506060304052a0a12050d08010e070f0320130f0b0703050d11040b070c090902130c0c06060909050f01020304110120030706020307180b1905090a09 74
    0x113006010540b00c000703110601851301003081c40b00069000a480c1c5004000101002000703807031008540d94003001c0011658001c07003910001c500070303e50801c0e40c00309502c07074003c07100c0346042828140c815207001d2142c1480c819012002600040c0117030b4a91610b891030b40303000100c4800748900142500040c421444070058003103280b0b100704a000b0700300d1000c4c2000c4540070980b0340c500b0040054501c00d0010043c200400880c0c40402101240c015010030500000441c1e00e40d0340321220fa07822504021400d4581000201c400503c40350701c2d06c03940b000da40d005420101015501342d0040d001c0c04e43e0400c2a01046408044100415001d110b0440645403404011590321003c0c1000c41ca0a05c0400c059011644100b06000000f05000802c80c0b6806c802c0c200201035500c2c0b0702d088610002c1c00c08084c901408006196410031920b5802140304120603265089400054840c80d00c4041460040e02c41d8410308000100350079907150080d1079060300c1e07444d1091422240b940404c91300d00c402c2e4804c203060f0740c48 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 526315242 1250 526313992 526314031
    0xb22060509030f070b04050409020a030203011802010f090e07050705190624050609210f010b181b0d060302040f020d0605120a20060c070608072d03060e 67
    0x1400f14030600f000b0031005001c04e03800c042440d0002d11552007150301c0b0755559000c0a0454440748003400003160014001c02032502c0140d00f103140894817990407400140f04184202e1110700606c042801e940c6900703900c2a0300c0c1d0703440d1000e4601c1d511548090ba041d00c60300140070119505d00d028000003500c0741d4808510184100c41035401a8150300342503210f40c04040c000c1c80729071900300555034040000c9a00200300b411980301c190044161a1048485d070203501c0d240b907000d181c1500400145c001c152414900c044603c4500c01c16200252100c141c598941c0e01d81d04d001c0c0000c40d002e80300f403003c036076000101540d480e40010300b100c41810414202c0f03900890440ca41007214400d43c00207207415100e40468480d080308240e2140b8000c0b10080801028001260801c0c48071070001181c02c00142855544481314600d031076482d0301e54482d88001072052400242c22030300c540d0714600b8036102d040c0b040515010000e210810744003030415041c101507a9440010740c0102d00056180280050380e4500c038075804 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 526316492 1250 526315242 526315249
    0x1b090e070e100b1c021905040f05010302090105070b07091508150f18040602071502030405010c02030f0723010204030b010f0b12131401150905060405100b22060509 72
    0x344082c4510010b55010444900078a08039060b41103031103d0b1104028114a2140c000c0c014050320f0b40c480d10340e101c1c900d0100d5800c0002442560682d084403420595208011000d074400c0e039081c513002800a00001f400541074114507608554030f0b00340490520340b10340300f8034926440300d41e041e4002a02c0000744071400b03461801403400000251004542825504040750f03428010481c0031480840b844005018083c482e4140c840c901d9004c00d4a03072101040802e1400079410981e02a2825480c1009c030a83c860300002c215203484000c8035045d418000700b51641c81803100f120048a1031814904243c044901080c4004c2c405140306421441031541064105445d88a5035000080d1200041000c0c440d4019040035207a8041c1e140d12070a0004800c1e0b14081900000c0322015441641c01c1005050030f008005140d001036031481c100400503503480004003c2510301c169103e0880042c400c0040c000303072a0f064001c0203030b001e0201d041d9044540403a010800340c901d5a000340d0008001082d03c0c02c0e07038503 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 526317742 1250 526316492 526316519
    0x32090f1b0427030503040302011803030b010305060108040c050d02010507140f1902060d18020a0303260c0a050c03160b1503030a0801061808010615030e06070c1b090e07 74
    0x20103002c0c038426002c00d403480c000d1010034403440541440b9000c0b00040825200750860702d50400810410030030030140b0710307015000d0b004441c50380f8003086c01d00000402d01d522803170005128903003190740c0b001100d1511051104051b11000141e0401104109440100d00b01c1e51800e4212a8083c000b044403000007201c9030304100340c0c81f5101c03035500403505200e00076a4900080e5102074204250015840786107101c8854140310302000250468040200082490703008001c04000150040d901c90585056003c90039044108503440c24a00c0b034107003c400b0500e1b10070800761000da105101142c0c5800002e5110358481900c218088617846410b07410040c0324042450300c0d40208206030b00641c140a1070b04005003001505001b01c008015900410104550f1682516130040804200821200f17032036880c0e80300300c1513a0300c1d01000440c0c105490082d0481d00021500d03c65a9241e031000404001c5946014614828504500c8500d9207c440032038a200580301e180c01c005070400080050503e00481180c021 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 526318992 1250 526317742 526317761
    0x301030809270601030b010e1c0b0603190b07180e04020310050906041103070f260d0507060c1211180111070303050d020f13080132090f1b04 62
    0x260440c2c0202c10340c1003600840729030022001d01740841d00e090740400403070341d100031080540da2101c40615030740c940a00c4011500f4240f8002c060740c1107982d0360780c01490350b10700506650101c2108101102d5002c6520906034503040881484c0218421000c002c0c10204010b81d504140104c0000702d0a20045250400802e030700b000b403c1d0010720051402c00201611510b000300054030111058040c1003880c0d80501408000c0c0c44e801512001d51a01c401c0400310388034141c036001c1060221048c40012604000820b28140c0e00290740c4c15217400e0700d696419000d01401c124200601201c04510080702c40705025895409104509a035220071212004440c4604d2024260b81402000ca40c0b14050100104526042e29090b0800c1680c0c0c0d0a80000c4200034072846064000f00800403d0361250500b6920880b030031926120020700032510008003544030094111504586802040c0c10140c8110080074140e5100d500401034030f2008000000d040e081200c80500000e6055210100c07441c0b91074240300b94800c4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 526320242 1250 526318992 526319029
    0xf0105090115260d11070e0402150d0603020d030c060507033b0607030c23090d0203010e0d0e01090e04080702010818070b070228091e020301030809 65
    0xb554070420002c4442a014020585000c40129088940ca00c02a02542e000501c0394200d440c524550840201040c0c03e03404c03900160301420384001141607502c2d80740760246800030461400c859400c124104640c4c05110040b445540720580000580d8a54402c2c40340e9074000c0d00d039503107000102d150603004c4910040c43c4100381464007061600c2c0310701150144100000740e00400d0103030380c007010f60a06104c00241401c0300502c01d040800208540c580c1119840c200240c941d4510440c250003901c070181c81c502d0f002c03140309000380f00c071403a180341c2044001c50300c0f8005000012880042c3d2205400c1443c103a105d000441e41c444028082540e128150744010903800416130014109982c2d10500d500c00c240740a81040004c030041a483d62a503501801d80c000102c085a200ca036a481a4041d81e07001517406034401c048801c1a00d91364400c03107004107910b844a0112100c00c9042040d85402004060300b10380e070995881071800301810491005502840c000c08002d9101c0229404204540001c900400003 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 526321492 1250 526320242 526320251
    0xa0615020d110102090409080405040c08040503090906120f0c0f0d0c03110414100306180317041713030c0b0f032d0c09040f0509030403020103020d020f0c0f01050901 73
    0x1202540440d07200c0c0d0074040c9240207241d00d4512440c02e40a40a22280c941c1c1c09850706510304108006e52000300211007017034a0501410300c51503000c3d1030109080707401804a0b00200b07c0c0d4a030038030701165202e90003c0002c0000940144000040c2d01d8450030100303244956002da84051180d00e8401c1031444019000c03a2008400a01c81e03641d98101441e074480106411222940c0c00190781e1a0382255547c46e980301417450040c034161506100b601030904c0180c1c0c03024942442241c0140401d500c2d021029095201d0006610103044140f40c80e03a07008000396030031950a064002c0d00321358200241400403915205085c3c03981103003040c4040801f16800513890b03880401c246004034a80000b541e510084060040b480104a4003da200e04c8240d088030943c205500750801080041c0800a05801042607a041000444041603a03003100c2d420359007200706074000d00003000198800d40081030761244c405c0c4003500748907114044400c2c03500b00600201442d000522400581d2009200e00c03036008507000000d00 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 526322742 1250 526321492 526321529
    0x301050c0406091a070204090b041b0f0302010c1103161404020a020d11030c01050f071d0a050415051002060712060e0a0e150106110705010e061819030305030a06 71
    0xb8000881441204ca036000c0040c1940b59068036081030fa810300d60060001d00c40c0403d0b514001005002c1241c00700c400c0300d080e518200070441c1410f114400c0c5e817040036184800a00b5500152440c1009401c01c03580f00d90765884280c3c0c0b07510144148109903c0c081020084141420204520407440091040c06544148145c1042503030000e54410900450300f4090003520a906a06d03045209990f2000e44642c01d1405121083c0d0914010318807440180e65a06040050307001c998007030140404841c1c1e44000d41c4201442141303800c2e807204c0c0c0110701013200c04545940d190041004071410064890258000004122020790000c55402e45006030318000c00456051285c45800d0700805820b40208039600e05032802052001c106881d1404224082103a00b5a0364180041c002c400c005510714031405442000180741d4001c20b40b051030601c00074030303103400d1076100700694045079280c0340d03040e6000325940c10345041c2000b00001039024500956550f5580c1c900120320f0070a494085d48101c40f40c0040380c50b800c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 526323992 1250 526322742 526322747
    0x60f1a0303190c0510050709060809190b060609130c021905190c09050a0b0a092f09090f0907060c03020d030c0201020418020408070602070b04140a09050f060301050c0406 75
    0x1004070001c030b0a09070071a070f2450400502d17000d60801c41d1845585000c0900c41419000403801d0102c4080f42c1c0c4440c896610b05a441e500c4d0b1004c9020200720740200d1100340005140c0159041d4003001c0908280e040030402000501100c1c540c801003070320140d0b55a248030035a50705000d400155408401c0b440320f588510340d07850b80d6031035003007101c40d0204003042c0e02c09040191051010008003c001030902460504440d514028078010954912480c03400000040e40265406821146400f07030301e4044040300b242d40c0b900401c814075000450301c0381c41003125000c00c1e40c038402100d01426a45000d600540340111100707140c01065009017050021001840c00003da00168030360b401101ca20380400c440c01c140c031050b80a030160b41c02445540d0034802810f030511045e036000d40101c84101003101d03081c55540009036210000ca004191a400c01048140b00c0b04404008105075588064440320a0070b64444a50080f6041554001c00c098004014800145000d0059035001144441414606440c10201 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 526325242 1250 526323992 526324027
    0xa050c070803150d050f06070809030a080a0b0d051011031b0a200f070b040b03161b060603050114091c140c0f0706110a0609050307060f1a0303 63
    0x2000c007200000024601002202040041c1d480500302d1640c0c0041881d1003511030701d20b01d011130b0846c130890780010001403081042c00d000e01c0429000e5450204000ca04070f9104200078040d1000355120706400080740c55182c000b01403180510054890220440c1518056410000b03075546030782c2050082c803e0582e901c0c0c007000d00b40062400d04541d6402000419079076203034a20038090b00000b0050030080094404540e070040f100e8030005850345151a500d400b62103004601030303070010b044148000303007011071005040c611850395070410b042007a8403081500d03110700d40e1000480b00c0340d841d0714080003000b00034021145c11b18080e444551507440c042c0c0059541d440504c124240b015441e03080e081e40c0724091000552256003024003190748001c5491051f42d18a400b15a02507284150040020018801c403010032180003000e025114150b240e4440d6001b40c00540801d0710130307020030049131000070414411200c0303107542e0000104000740c002c9607094000c142080302341d000e038204204088207030090342c40 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 526326492 1250 526325242 526325257
    0x10050915010f0e0f090421020f0607080912030c0405150702011416080d050405060105010207080c011805040e010b03100b33070b01051f020d0806151206090a050c 71
    0xb04100c0b008800f81c00154000e0800c1030443d00002d072001408240b280804403501c05207000c440083c841c6800c004120303901c030009103e00001784c0001d0086480b80340b10301d1003241c00401c050103e07051055044003081840d401611044050b04000408102c2c1e8100003030061110142c100305c03107007003035543e4001030192440002d1805414400080ea0710185040c1c032100380132035170403442160710349001c0c60005005042c2035030192a148100000041d0345d6200044001c00e603195040a09600ca5039840107480060f075104610121348a44034002c034140c0c49500c00d070456000c00d0070010441c00c0b0079900f41410a800d96031038512040c10001d00100f40d441d032900c40216910b40c06803150720944480703154030040b11001e000f100401c100260b61000d000b00c85010605070389007105c222030385640010021000101d41481d690260300044400a00c2e00c7c080d1180550200b4060800c09441740e20544d002400e03130000041c04032510020050000b54100424102d41c8050701a10070016400c1c003aa0741c0c0c10b20b004041 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 526327742 1250 526326492 526326497
    0x30f040201090b0c0703020906031f0f0f110a0f030e071802040819060c0e130c11030f18030c1c0f33140a15030b10050915010f 56
    0x10904591045000304010301e0380d054966140c00484c56001d8a0b10b00912059100307080d0746012401ca403602042c108d500300002c0409020351061441c140000e4900725003044803031035031050021104003650040801c005034441c0826515034243d10050b01c81ea20700f507005410945048031025000c2e2000a46005840c0c914100091020482d00a031010748070310b0700001c0c40c50142100080d410940c000c0b80100d81446018280403d0328403241c12265403684a61807603000e2442081007075040c2041d07100641e502030618216008419200000b8515070025603080d54209001444990b588120034a0ba000c00c10100e010b0914006002c0000710701d04444190341c00c1112686c43c032401042001c01c0142402644440c4485440e10a417810310242c0e01082148007882d4129200104003204c0e92003804200702c2d60000103161a103540c5411401400c1010284021107011a008030105403038800c072902c42e41c0c000e82c040703848034104402d0111540d40030b000c80000c0c01c074004540d03070103a8001c1d602402400662 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 526328992 1250 526327742 526327771
    0x9051009200d1b0f080a0506061c1205130e0105030606010305070915030b01090e0f04080c1908071101050f040e22050d0306060504080616110616020c0402070803 71
    0x80000540180340318400521460b41a5142403004080800003c02c6078543d060080032075645401c4162a01e00c032070401041a0400000204a031405215804030803900102c0001c40d504541d5880031002c1000051234081100414106009143c0403da54060510710f11120115450000401c0e640c00c0054040d0781130546840c00107100500c58840710000308003132a025000e2003d0114050300401941381042e0000c2c80714540466100e4181d105e0501440304591600310643e100e440340f4407150040c10450103103001e411003698064030541441181c0d28024420b8983ea00a9498035202960103c0c251034140202400000d03800d201702c03015103080316074041c0101ca290303075115482c0d24180d10304501c1002c41c262035080d00051180000709000d01a4980d2401c211580e180c2c0da083e249801036101e251a00e0340240002191044d105c900d0024110103810701d0104da1114216107800e0640441d812803c07081c286980d2451640d0401500700c4c001000d03101186064040d895507030291000a00c48150040303103 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 526330242 1250 526328992 526329053
    0xc0405040206070b070504030204110415030906021603090503070e09060a0c0e0a08031c11070312020403060e0d02070b03070801060c020111061e0c04060f1407020603070309051009 79
    0x220000c0f0380640c1c2d44105426820329040780e019100d40c12600059024914102d208840886200200c5094613003500d00840b00c2141518101c01514503000100d82da0758091010316400440035038070f5403c880c8a17465000015040600703251070b0140c00d60042c4110a0b1410034440348072004110550824001c0f07101054046c5000d80c00c4d40d0582c6030b100c0103a049540d050000806040100240003001041c014801c02280c0540d0910180c0319403c26408115034100091000240100b0f0180f034200c2d490400981819500e4a5003401c4507200540301d40c0c15000312823030a012685c10701c80c0002420b82c400300c0300e045007446000100718850500680080c0540d44044005581c0144506590580007008460360752410500c0d200080c80c0c40c0203010030b00f103a5140407440d005145030964040d41c41c1641c03088248201101c00300c0b8010fa070203084a001c284104065001342e03c07034a005600c14161034901003200c0d030141c1782c218a0725100c840103075642ca00d07103036040002900e410f5800311101d50401c861541c4615 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 526331492 1250 526330242 526330249
    0x11104050f0a030206032a2b0533030102040f0512010c120207050309150c07080f0d08070903140105070e220b0316090b010806060f030c0708090d0303090c090e0c04050402 75
    0x5480142d0341c0011001c1644c42c2d040d80388080303805040c2c011060542c071b00b04454030982300b6584140c540404e4000010b80c0f0343c8041c0000c00141c4030007120003003d840041d00c1078012900b282d0042c2c01c1940704040040c801d0009007040320412400d2500c4000030000300380c182030300030030340a6004095009680c0000729041440010816030344035a0300103003080c01d0402968002c48450380440300b4190140541100060100f2002c1101c810459191010340755402500320b045501c154024840001c0c06485200480840c103e030804124003400c035000001e05060103140980071540a001d8580319405c01c0f850740455200000c04003c080c40c10000210318500d92000082c2450003580b01d5009c040211040040e566045811841c6e280e4020b0301c90401c00d40710b52040c44454411285000c038080320400108000080c00002400340d00d003e88681030400701140700282c03c1c0406441d040e00000c3d180e5680d1420300070011100e400500080408000e0101c01808071a1508068840944130390755410000b0700390344 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 526332742 1250 526331492 526331551
    0x1e0613060e0708190e0307021c1209080c0901060f11030f0f03010f060f05160f0c060201050a05090304050109030b060d050304030f030806010c03080f18011104050f0a03020603 77
    0x404040545001d00e04903000910303035401200c2c1420302c0b0007120b107000144884d80c03150000818035070703001c0c61030480650203020103c80802d800400703944009035400f000c1a031808103c020301c422a40d0ba00da0362842d01a034249060030130071040c1c5c860b02e03541c40108001600440318140b01491070402e0b1b00701ea0906585582140204103006494800000d4503810105d4030100a50613200c0360400c05440c1511100101d0300c0d840d44040e41e502103030b010040600f40050014450602c2889031885005116490b0382c1c4465080c8a9071210f00540e4580051046114060090301c1d8400301c510015414203240c030000a060302c407148805800e40d090080461030341d0700c07a800c412201a40200880b5035a580d0303481c0c0381c1c8484501c1d0348182c1c005500c00f0302050302503100c1c070780e6074940ca900350703403009002d8803448503244002002030407245605500820740c200001c42070290380b10b5a14001143c2d87c446140009003e07400308600d00c40c0303114600c0c002051005a5881e42030303c1d006104110381440e100e111100764164003 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 526333992 1250 526332742 526332749
    0x7150804140304140901090504021c0c090c080609090f2e2a18051002011407020106080709061505090d08071113050702062814010e1e061306 62
    0x180400a40843c5200320a041303800c0196082c1d0b82c01403140c0ea00c4c841441121802e0301c00952001c480c1c861610344080c1040c6403a441c500a5040500165880c0e01034400c40344241da10002061121041004614040000176030006000026100f001500e081d40764642016620758070b03c0c000d8000c64006c403a0b002121000700500e40c001c0c100195080070000c82c0d071107600307815802c0e4500030074200203004078801c00340803141c10b0384902c07040b4100d4200820050180580d4101108542d80c034410610441c3c181d54403140102144d4000040d07003030078607808034100300d000c1d08081106030500c00d041009101800c42001040103618001d900c0c3d043c4103002416610351840c024120b403101003611310070721900e0403100402d064200c5080c0601107800411809445040721600050380026000075415000501c4024140c10500ca9000a50380c01c0f04140c8222640d400c503034903220751524010f0248030514469190071116001681c4108403004082c424011402445540a926070b0024685900392981000014 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 526335242 1250 526333992 526334033
    0x40320010e03120313140102030a110a0207050105030c250501060504090b0f06010c2907030b10180b12090d0302031003031b060c020109031202040503070e060f060309030d0c0207150804 81
    0x102d100d40710807d02030341081c0c2d00c2a000a24001c603600241c071622040b00c224181d1500503282c1c0c60f01d49001959646c10041130b20103000010406a800c0009504941c2206040040407400292050030206d007103404942065001e80e24221000e408682440078180e44207c5038000c2429a64130707000100c40741d18616000901c071000110031080c9412503010b0540c0300008240900303195949407001181a01c01d00725055400001c8021000b00d898483d8400520324a07a001c4950a042d5890f500469654007175124626071180d5081448010401800007480c400d0b800d140540c25420f002e0410307281007515110040078410560000d84040c076010307041c0c4e128260090f1003080110403070140a4003801c0720f0003040300001c811441058032404d80e40f0988040d10b0014005280071414a0981100c100b005007209520800c1c28840c4119503a8800040d440380024801442e182d21500c24400181d80c3c0c8940364000f503401c6180184001801c244081200315120b10381000306440b030342080c10a0303400c0603842260 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 526336492 1250 526335242 526335263
    0x70905040b030c0301360b010b0c01090c080309010305060a0503060f1f150807031512060905010606050403021c170703110a03090602150609010b0717040320010e03120313 75
    0x2c46e10b201c60140c4c8042030ba8940d20300b41111245502e02107030102088000d00c464406401400300150300340150900024030800000c0a0445407070b04030064025500c02000d541c0000b07500802968580603468110f58295450a4101d0500e00040e4440710000c126403401800b000016240f400284800d000c80401140c411381c03100e858564079034441401c0e001040214030410041004e844c803910907030454000c284c0501740568101812a6550b510740c01003601c06a8030742c5e102c9404a40c0c28810f20009200c45c2c0c446980ea43e1031841844003101039610003420b04060007903007001040c0c07150b0b881c0414214082210b076503210f881c60145c03801c00c410f155020080c81910360440c101504a60302000b41c4001c0d40072a6030400c01a0b40c0c40942003411180c5917003040d15200100040e45201000d040943e1142881d42850326a12000710240d4001da03009580031100942c5041c8800401c0140b02c881920a29104060282000100c0d81d91a812079040b1002e120000000320905201c3e079124a04590050300003c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 526337742 1250 526336492 526336511
    0x70f0f080d230f0906160c020909010e060106050711010804062705060c0408120a110316120e030c0f030f010606050705060609010312050705011b0c0c0806070905040b030c0301 77
    0x200c0c001c0c500400b4000b00e468180441d118044603480306108004210041010341d540480d03015104200d01554001d0141e100c00913001a5034010400d88190291400000c04441440206117490410391003071092000c02c0008001142403c501d0f0f4941c0b180c20300341014182c49078038008008200b01b266000000550410302c085071081581681005030185040740c0198581000710302d0136100e01d2203201c40c1940500c0d20001030500040242045c140c05040c808003208580325540e003140d012035442031003141c503600c800040019141000803442e486180c401241490503000c240d550715444481c0b40b241c410a00004210b40e8100301e6000b12b8910b4000a2001d183e40da540075146401022044405004003030008070242080c4103c81c3c103c0781c1004405000c5014010165050351040c58143e0f099501d030350342d0b501c00020544013900c0300112036544000c0320706c0601340001c0440e501d4006203c107070080300c24842c8045c0d1145211049c0e40d42140c0c005070b07040700070000030f18000500d0b020395095400d040c1900b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 526338992 1250 526337742 526337771
    0xa06060308030405070b0f120a0212041b080105270106031407030212060618090a05010516030f050f06040f020d0f05011d040312050901090f050d0e0303070f0f080d 72
    0x2c5004070302c10803c8510141e02c85050f0b05a078028040c01c81070081c030034041600303c1c4415400c5580c01103000e0400518208140840300c3c02030700e044a0550750b080741a5581c8416819049458004084010003049142004042500110030b1000240d210100f8024900c0c54080294418002184c0c00008520700303548003000540c4030a0710788000e0f4411051119002109040444c42c1071281070b00a081c00308400c1402040c3c03242d2400500542d200e881340d121150000f800911a0724040c0c07440c6908524842c0760460001d00352000c0310909040141098188160100781445a07a04170804450104d0320350001d40c246c1009028181900a0035403d042e43c514504440e80d0029050310014940926400c01850708844043c0301036400a00192171011504a10601948405e820100120021036124140d8860b00c010060840055440790440300e81001c0f05508a12070810703840c019009581001c089403a000e24001d1129006490210030010000c00c025440086074022030300020200304400d1590f010 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 526340242 1250 526338992 526338997
    0x447220b09010b0d0b01050904031b030302040509060d1a3d0611030703141c0b1309030e060a03020408030414040b040b060d0c1b060b1807090b03090a06060308 70
    0xd01005503e424080b22050903c4042d0440143d0412003041d000c0c0d203840c013801202200180242c040011060b8410a22800d00100d451003a010303940c0561030740d0400c81000201d09014103244d10232002a8004030001e003084510300030f6240c0798951001680c1c0c0742c80001c0301c502e02808100342509200b141000d12600341c03123004140c0d00000d011400d42651100340c1541d0580c811a000b44032a8020b102c0000041d120b0001c21110f98910f500320350415032900300c0745d240000803241418425440e0f50030007040e42018074519884410f410403c1c400151940c6022b400d02c5112840d480c040d800000d01d2660701703802078040718010819601103903515982c40c0702801c0c01c1c0e08041c03003240c4168103210141d240382c0343c14003600b03404503402000d0600d040c031038401c80c83c0107214001d0141d003030101d00a4003a510116514003004030034000c42d0003040c6104004100144010104c800c2c8046504500c18400010761065060f010b0790410280d40703a072030322006c07812840c00002c181c0040c100c40c2403250200c10081903001 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 526341492 1250 526340242 526340251
    0x103020d0c09140a030b1305070902030a1d060c0f0d0b030d0207060305090c0a0501110120130812070b04140a03030e0c0306150f0411030447220b 64
    0x101242c003290f500800004003410303c8040c02e000200400b050600040c043c2d1070200700d00c5a42240d420aa60301261000d0740c008840c400c1000d660303404000c00e0813074800c4207240507030007610140c0451b2520700d01c910118050041030b1111550045415403842040e54481003c1420080803110358045030100255511154080c01e80001c0c2404003061224100091b003420307449004141c0f1114606250044490781030314104000159201d2012403506503038000400340100503810403d6845c1c07092400602400d080381d024800540c0301c1e00d0002c3d41e0344022410341d00c0150f4030011200365a01d6030700b03214202c0050b9880d802c041e406914840420150994410803402c18103100791100103420108158462200b124074100f490078a25031420a0702c1d00c410142c0464100510010b00c00d000440311450507003089508a40d48058010b810017150030303400c1d2444004020300c00c03c10000b4000090b0f02e0b030100300d504d10134006104d480d0205003001c04040c004112410f0040460010075450708240300945e90699 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 526342742 1250 526341492 526341509
    0x1090b090109030c0b09360403020115060818070e010e101a19020a030806011103130b09040501150c060504060605180105010e151905041802040305010f0b031b0103020d0c09 76
    0x56491100d68072810b40c044d80c140c0c002d40307020201c51f40d4045420600000510880455595209500070722032100d4484020b00340c941d45a10680c40d2003000041104803449185866030700004041001904804c002c40c1592002a851520750719540d5039501c03000703441e4000794051042164440d880d443d003032002d801074905c07000d03880b006081100416030700c03061203620250000f102900059699409024880300140c0c2c80030840746045450030400c0101d0243c0e030000c2016040024030b075100e5150500070140900400f021810045100038000342c4201800c0000a00302d903150000141032110a51025000380b1014088124108840748151a1a0800d0081c80e0100b2881045003c01e42800c1c81e0215500040700031052501c40185843c1000d040c12403100004c0040402001c900c10340d1109480719019480c010140c0c507a800d500c1c0c26400d503986020401c80f103e02d0710b03200b5031690380c00007000d01282d020300b0742c0410b0300d0b031308940120081c1c450701e103250310442d0502000400072030b40301c04d1303190441d00f210 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 526343992 1250 526342742 526342759
    0x703030c030b0d030f08041401060f180e060420100309150516030e0c120303010f080109020a061232132105091905040c0c0201090b090109030c0b09 65
    0x30020030481c200041e5010f400100e103082d00c0121a03021b1070070700341c03c580a800c2c0c1d20040003c120715182541c2603074111818505201104015006090340c000c1d0a4000301c410602807040201480b5a903480002c01c081c003201d00d14004030310100c2031000d103200d044801030a0030096100410b0042c004c2c1c252208100c5c0c55030144c1e43c2e44400060300c2e1060b01d00817400c150401012640240044005e46981468600c040c0102107140c0d120b540c488402104150f40e21002d15100e61400c2140c441c004180d41c09960184d040041010041e9510581c072020f54009090200624441030540c03001442d00e40d0901a081860b0401005808000240b42401c008080c180744c60303540d00d020b0184500300b5800310007040e122980303105080303504986100d407105450310f140c06400c0c40050b4002038110111448240035440052005101d2802d0034000d441c0c00c5025428850382c100c01550008100c00036a110301d892007500410501916842010240700941d00300785c1444466440c2d5078080400c2d88105862480380c20300 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 526345242 1250 526343992 526344011
    0x506310207051002071a01052103040503241308091003020d050a1a010203091309020607150603060c171524030919080405060d020d1d0d02030c0615060702060703030c03 74
    0x89200c407605a403006811f0052a03041546200d040c007110f1189c0c0c40c2c00c1c0c0014003001c9480d0301c0070446c502c2c5c2c0140004070212400011284440a4100078140b00e00c0010654100c00c04078a0000480d40c048000b924202d9950561000c110002d0290320035414000d4101014800b014400d60051807004500c000030301c040044000c01a640c0740705081e40345800032181201600034800710b900000605001401903482d014040d23a0b2000002d0a9121006480e551000284144140c1d031051240d505240c4c18243c2c1c85002003050b0403102c9000074400700000b81702c00e0220985072107001c1900c000c201c0061054400e07524202c62111580c00807108107040340b24210704205002001501080307900d403c0600a45000c0c189001d0000780c0e8031101218190715020084850031001380c0c4038091111030803041c2c2e1508000004459810315102620750b00c210340c018000883e0b887c8020402c0da03082011050a070110701c030300ca40800c0c0540101c1c8c0010b50b10140100d8040c05043c0c0541152009148503070f81002401030 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 526346492 1250 526345242 526345283
    0x1b020c03060117060402040b03030405030a03120501170c0d1b060503190c170a110301121a0c040e250203030108010b03120703230d0c03050631020705100207 69
    0x1d5650f5618168040404580981000e03403000c0c03804200501a60725258135407010924008075540100d000480141d40c00003015101e2150718090081320029050b9034603ca0342ca5540c3d00301d281000303446545413441c20b2003040002416400c0303060764405a40403130342ea02e09019010790004c844851807500b0035409178210b014180304044200d030084c1c071307010714480034030300303142e4a10400034401005581d540c03603861a40200030b00a54003c1c40e0000302d600e88007000c0c0c5003012158035034078051054007020105101503400c1c00015038060356101c1c1e10500725a65900b140003a003080c1b0320024810584800800708400c4c0c2e01000950580d000b10009100c060f0810041c03694480d903050411200c524180080c9000902c280051017880746102e51100101c0802e0510050b5540142000d020f42980d69400c2010700390180035503607011070110b800ca0f01c80030080d001e4114011009030b81c1803190f51440c11180030500c0a07030642d02e00540100484480d8121403440c0c0000358030015082d1050900c81b1503003000c0c041c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 526347742 1250 526346492 526346519
    0x6060307030b01122a06110601210213090501090218041505070528120509030a140f070c1a0705070e070207120b220c05060a031b020c030601 62
    0x9034005001100b50703107020316550441d188001c1c00c46001d801142006018801c800c41607a0018148820010540c90000094981030090582a09a400200041000480b1001981b1815000c02c020624101d001c0c8000b5003070740110100990b48518102000060220540c094901c080c82503401802007030714841007035100301c41160020001300809050a0b120862790304540d420004505029080075000e403400341d00a01c8070300310142d54070041c481003106254000c482c80c5003142d901d40100842d0034440012501c1e0300c81d42e41c82805204443c0f00710754aa0542c80c3c1110a480d0080ca1600e40f075a07403d20705a1900e2840d0310900007906605035000c0d41c00d5a203034080b202203a85c048002c2c03200ca480c3c1488035070f500000400722410b40c0115400040c40c03ca410b1007203406103202c0c1e0000c54142c07030907211141080c0342588040c50f02d100c0402c0498002820326083c1e800341d401c101e420380d498001c504822405070140b42105100400382000c0811143c5c0c0004500344000000c80660300d540ea210b0281c0341c43c00c03 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 526348992 1250 526347742 526347749
    0x7020f030304200303030702060907050d020112151701060f060305150405040203120a021606050c030d110f04080a03030c02061b160624081c030f0b0901140306060307 73
    0x58000704082030014800d00d22800c07501445240c65459200500f0009086030021145400941c001c0420001d00c0c0f03000303000c0030019100440713060b40c0c42141c88d00020913149944c1c404501d5a582d540621a0349001010390b04002c100306c107800300300098801085406807009200b40c45955024481c0454002d002e402168442e03090b4a94492280602d1400c01000d40405401a80c250042c0c00ea04142c1080000c024141c04400f50020603160400450f030324040c0700c0301d41c031600070031005008030074036504080111107181c981481c021804040d00808403c1c03911030003101c624608000500040c0c0c1e450b000c181440081d01a480802000364100c0090b038494034116914100e0040d00101042400b002d0380150501c144c1058400c0f2441403941d03030700d10807200108a200030500e059947e8418041544600f01d02500c00d11000d003011540354440c01c2c2542203032172800c000741a110f2202c0b9079203510701d03442101404001406000b04e96900d1501c01103a8a20480359401380c010340001139030350b0a000580b078048 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 526350242 1250 526348992 526349023
    0xe160b280c0b060d05010f090b0105060408060f07031107060c080703090b0636100f030803060405040321020406090902071e03050c060411210a170403150609050702 72
    0x102040e54800000400c010f003200d03848072090000c0404500248188444400711070703400511209281004e80361010b0590289100b803004002c20f1112590200701c0c1e035081b4010a14412035038403090801e4000e4020a109150400780116118061160035000a030304500ca50b11040c80e80c2c1c49162084090318148203000d0a002c41c00c0d0041201800c4c00102c400c0f0030480c0d40ba40b40011440400000340303140e040740044110300c1070441070129070070b91560040000e02040c0709404041e03240d59107825032400024402880303242d90f40001400d05004480002a400321010780300000c40f81900000000e4029018000003e40c1c04803021810000e6442100c1d9490380202150f03c440d83c154070301270442001e658080701004818494940c0000c801c0008078003840c407070400744c1c891200e46010f020000c0107a0315110280c146401d8000c01942c00400c2c0e035103225801c004010801c00d07105640000314469907000a041048007041d000200220b0303403010b4180c4800c2d160a21640c1c81d080c000700d990f8401031900a54 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 526351492 1250 526350242 526350257
    0x51c08010909050d0f17150901051e0d170c01050121020604050904031b0602040626070c03020f150a0b040b010f08090c1509030c0a0f03060e160b28 65
    0x44441c0100c81c0e40c45c0b024000d1400641242880d9001031096005035055121402d240242c0d168610300080d126015040a0354540c0c1c01814004090b86000e00c2d601c005c07409041d00118500901211001d041400032240800340c0d603e81e04064828001c25091184131010007001d5240480462a09816a055a00200080d00746414081080325950003c0c00803810300c0001100c47c0010b540081d2087d92031405400300685462506002900060f4024039245100c2c4211107031480078202c840c980b607000705d0390b86400020750600b403030168a004940d000010707442c8140304241d1522240c44425611480304041c081c001f950015061009035031a4040b0540800d04007285010224440c107412130f0300a001c2d001f02c42c0d103064000045078401d803448411081900001070185501d0608001110789a507050310201011071405d1040b461410301408000c01450301c0b9112107103000c078200524020140c0d644481402180d559680e0749241e44454518858500d401018110301d8a0001c03107240000025115202e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 526352742 1250 526351492 526351513
    0x30512010b0a120b06070c0803071106041a0702150310031e03090e07090b0304030503060f12070909020102010f0e030a0207092a0314010303030e1b1c02030703051c0801090905 77
    0xa015124141515170400307010300540380480d4003c2030050081c06514081c654440d85424010022542007102c0b500800b03041208000491005204800403c641080c4ca62504e46510029803070703540d001c0454080c0003000c01400030841020b219981101e1058028640110022440d0702c2160410b0102038082005150100a042c0c40b80704100d50042640c035041c140f20b80c8514050605810503242580001c0000c010880d003418400d00700094403c003121516801244e2404c901d80c1c64415003c3c036040c41c1c0e200d080d1802164000d4104108143c00c2c5d8405000c000c00320340140d40d8a07086851950018032480d10002001c000d030b4400e0000d115038140c50000c0c1700081e82c2403455500590120a000c065840c032044082c50341120101e40a11710030303540450b810301c2d1405020319201c442c011100d00d2101e640c42040b41540c80004902d0f48046101640c0e46181250002030708154055001400398056283c481040c0701814943c52000c0445071203140c52a62620704000840d21b0b81d901c000c08641c003074410034 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 526353992 1250 526352742 526352777
    0x1030905100c090b07030801050a090902130f0b04020309010f32040c030b0901050910020c1e0f03030a0f1406060717041502070314010902090a0203040507030f030512010b0a 76
    0x740711192075414015000c0341e441c84c0740c50b9070381d0110070309030002040000180702038644400c03100000c1022035030500200c81c0075000205030059605c003458a0a95841a280310382401d50071054054800500454407072070098940780c007805500000d10811860607000303c4080c0b400790003c40580f41072748407002030591349012608010f400500b0075154000c041c0e2000000404c29240140f084c1c51000012800c2d01304442c03003a26108070300c80900310080c018451000d98980000300131310034030728207482d4032800010342003050f003000c0d0300002484480c0000820452058450340001040042c160401c0006d0801d00140040f150020784505034800c0041085201240e5080c560000740800d1001d45450f1680e101e0380d04e818a40b211203c0c1c00942c100c410100288070304980403d0302e90b04e90708002d01801d0241c0e40050001c080080c00301446990100124041c4013040140300c0182d80e01c0305680e8802c0700d07242006817641d0080310b03030f0325a172410030000030890a018001359141f200346a02c0c4c0d21072064a01840 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 526355242 1250 526353992 526354001
    0xa030203070c0606062001050912070c050301050f01032f061b0601060e031c0827030409020705160b0a2a0317090f0706120b040509030301060e0103090510 68
    0x907a0401c8121802e103008a803840c4125001854203403600d00495071601056110240300310703040c4030345034540310421181c490b02240100100d009854501e655004601d0421904192a00701941541c0b030a410091090a120074650590340a0f24600d040d031000340c00c042000c8501e04400030700701203060412840da4109040645007103000410740c0d00d08180084e600a20f421002d900550020300c200c000140d1a04042c09403603801c071704103154480c980c1d02282d00503291375000b601080020103012044401910140480710780a04c1510a6a58030359403054940040e4002000c02e076105d01401050340b0b030081c0088000303021906840302850070000030b00d0055621700d19500010310086036001e00010030140c090840404a0710980303d01c001041290803074005a0360040c040b10706580048054080010000340e00000c880c96442c0c2242e041d584004c2020103028250f0349250428100428801d25100c0071001e5030682d0081c0c0d444036150318141c0011010347d040c024015000c0c1c0c01c0f10214a4040120307401 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 526356492 1250 526355242 526355251
    0xc0509041a040c051905041203050f070c0b13140d0204020d0213080105070e010801080c04050a06150e130207020d14070302090c0703090b0309100b0a05030d0909050a050c0a030203 79
    0x3500a00d11103030040b405641c0c10490707100025000041c104544250304249490040702850320500b02400c100c12803070301b440941d00203418017001040c0142c1e550036031021159110741c8081c50f00a8288d640e40c002503d60030a01d804100700010032400b08903640c5c0c0940049200d0b9000b001d0880030b001c0ca409010007540004111000b10307030204407401c2207045511b042c01c01002242c0001500b0300d45001700030000000300c005c081c104440740d4010480c02c0c03c001000d600c840c4045400051549820310302c0801001217900020200402c5401030381b6190300079258a4801c00103031050584a02e03d000040102d1040700740c000d61183d1124150310114107403490b44041c0e0041c2030704035507110341c4035000640d040100310b600301040880004c0c0c6404140d8800d040c2001062015100d90460400c4030040d0b071541200384095119503680e21000541c5e070f485648560003040050709131050007444400081c00481c03d400740d00411070904001c28003940785403107054420903880354000e08006c513482042700030b98005071 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 526357742 1250 526356492 526356521
    0x6140d23100e030706180f1b0f0311090108010c0c0f0c03020613140105211b03090d0305090f072c0c0315180a1e0204270c050904 57
    0xc40920408482d00c1000300e9118082d006580700c1401d032802c07500741c0c0c811b40540b904020711700d01d000c00010901c0d2124441c050f4012000980d150b500344103501d01c05005e84c407441a8444441c0008244201d00303803c0d07083c065080c0c41c491066a202c440f46401c0c0e0340344007181400540e226000101040e8a0342c2103401c032900c40c1012483c8c240d0b40713070002a0341c1e07000100d00880581c40341c0e108001c41d03040b040b00704050384000e003043ca0900d86c2c01d5280581a100a00414901d90411400a0850000c0000d0002c000ca0700c000982c0d140d00f405034aa83d915000c1110304030200b86481d02081d0038890021320500761b411035800411603a818000d042101082c0f0700d100c4502206050300103066042d481c03050500c40c5c0340c030b0250315881340b42c091074a1540c04042a801e0f0b0140320740c081c2c401010001d100c00680d0011705014003061607030000700406001030200580751040d6101003030100f0150440c4410300c0303640583c7d0754981c80f25009489103100b01c0708002600c80104804200b100c0342801c054110050340d01109 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 526358992 1250 526357742 526357753
    0xf0c0706020c031216020f0705040b130603230a0c09021b0303070e010e01051206150705030304110103050c0a0c060b0d05030c07030314040807260d020106140d23 71
    0x82d0080d910350f81214840450440d40748080109550020001c803a00d1906032006082440e40d0488950b201c1c0f4083c020140039603102d40b45441942c88844100340094010002000650307681d09107140720955058044003c507100344407207400320000003100146a6084034901c0b4000d0b10301416500254031540e180b0300c3c000400580a00360312000c1c009144540c07840e483e000001495540010b00c0305079036103441414000d042c0301d0b0314039100c0c0c4406c0003588040199142101c8682c149a1200c0c1400f8004004045100c0002008200116841202150803003a2028441741e21010700f506418020719000b81d00240e041d0031101d012580d207800c4003160380409407403401e254004c0d0325410704680c0170300e0ba05001d50344503050030000c0550007150546a070b100b40b08250304003420080300b01c2c0c64081d144180c416102142440403000400403241c40c440007918411500d60001900cbc01070301070b05080c410b00c00c1c81e0400707180d842c207582000314400d40c8459000d500c0e038117104852041d2186004d0302544d019070320300c41c4 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 526360242 1250 526358992 526359007
    0x9040e07030b0103020a0f0b09330d0501050402030106021f090b0c13052d06090910080118030503010501110c13150803070c060c03030207080a030e060a050f0c070602 73
    0x18060389001e5405114070381d6840d0f040d8014010a4811035200511615103000e04200c0c007517040d03095a0f017400f002c17100000e00040a03c0340301656003110551040c2c200c003000201c11203409407002820a6400d9420070301460f030340c0b20300b0030003240024420040175801012003920009410b074030000e01c802c00480c000031008155102c8283d10030003150800d0800b00001100b0b4948003080000e074000f070000b2511a80802c0740c1c142203108030119a182c00501d8240400c40200680c0d40c0740c251040110701904260030751800211101804201d8450f41c5065440c1c54218518040131451a8181d030b43c06d0340310320340f45034030b41801155102c00e08403480c1c44030b0003029110301803270f40d6103150381b40040c03800e1102140040100f041c01c51070200c9a8411411980b0402640c0001140b120039030048038107034100068800c8041c2816000b920804c0e400400d0800e00050440001c0d825901c000b510742400310444000740da031a0702c0201158026111a00008603400014000d0444000207110491081f0009400c1284 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 526361492 1250 526360242 526360271
    0x102010e19080319050103080904200901051e0a0203040e07090b07080a1b03020c030c0d1a06010210060905040c290306010224010501020d0f0503310302010f050604090206030c0904 79
    0x4c1e007085540348c00010384060107151500406030b41d02c0c00d00348481c052550400185044e0b11620130050306010020503e08044031a20440d50b1a601031001520307070342e40ea0040000e40301d910034021700f02443c50b01c0000c9880c0c28481c04401d4155001043d100f0f1402e01d65480b40003654020414007810003103504028038030210410682480030344681c0040910640c00810142020908140940120700f4000000b020800c512828902c1b580383c10108151501e501004030300b4101841510748100c0c1c1000000164410241d04c407030712550244455a103901d8443d20740e0042e1520700002040391310f41040d489620028039030015900100d0500480f102c041c12100890703190540420f0762000c005089004201d0340d6010305c50044c942c512407800240c598052107002d0708030b00000c4d01401420441b00000a2113421015405058440490042c0c0e860807041c03600901a145580000001c00d042c44003141440c10030380228004958001c0ca410704640d15009000c035590000107403e5842600e84056101192 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 526362742 1250 526361492 526361501
    0x9081936080a1a061c08030702010e0a05070612090503071b050a1403060c070807030804080d060806061906090303140702060408061f0e06120f0f03090102010e19080319 74
    0x500c1803455a440f104103007440e608462000740035900071440024407011980e00b144052081c00e500000b615201e0310303001d00403801004a00f07401003007445030101d10010711400007000b0040310100c0c0c0d604400c10049504100175185000c1005046a206000040004801d03000d8280003190a20000a0b00e5644100044000c0c90360f0b400f1038088460000c11a496081c00c0c000c1907840040d2107516440c0021076503840c0054440c6900c046c01304058040450200401c0c4011101c41c2ca410000500110784c40c0d188154480009450304c2d1f1107005181c0c40f4081d03041039030610303034115100d40d190454803901d107403800d58914688007004445407404000c1180143e03994800350002c1c01424005000c00d262410311001072400c1c40b800001400b4820740c040102c020b0540b00c2650200e42038404d0b090005041100524100c3c0708499502c45009250000040e40380c000045d0414440c03d0b4000d20012030000040b64450202c01412880006204054404150b00e0401107410017022480da00c980340002c22840200e4 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 526363992 1250 526362742 526362763
    0x90607060b03030d0b030c030109020d0237050102011b050a1409060403050307031b0510020c01180b161106070507021315090509060f01150c02040908193608 69
    0x5690765031740e1200c141010445601e405000342c00820800b0308540020b1084040d40000038407a00340b0304018460944920300c908618000c0790308050010307664101c4481c000d081070142900661a100300c24103255201d00c05040150104c4e01c9080c0390032103941c230407100208000c1c42d43e1042c3d070080003030504644034030b4000c00065008a01454880209250081802407102c100e500c4d540040c0c010900401e0003c49d41502c40b6000c5200180e80c0c800302c0c81c0c528003504002e030580c200d10107940e036400140003828151300e00c0748985280b00040e2100d01d900580300038851440c060041d83c4114000713000a4000e000501c01c16000038502807031201d00801d418241c6584d40d00304c0113084443c810800c080343c101e00805800c05071000240c2003501d4059021070369948148500c0190704880030041052901031002c2450141c0c000c1d00c1440001101e00300502c465001c5021510240d002d080c030100051701c41c104005d562414080030f44545403d20070603894103d00c444600300040b40007030b070000b82540200001d0f01e12 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 526365242 1250 526363992 526364017
    0x90b07080408010510080c06160f050d020c03010e1005060312030403050a02070b070b060f011206080604020f040b01020a3008100e0606040915090c02030c0f12090607060b0303 77
    0x896082c11116401e41e08040d00002a0780402c66081c00191030203d28134100040a0702c045442e21790360b17901000c0041c4c9040c4007800c4031a002c080c8000f402400714623000580300703075021036100b203040c0410f060032503011800d0044207421200307449081032502c1d0400340c3c2009000701190400c018407454000183d0064800b02d010450010b0300e041d20342c0d0144048001000d80180c10f6081c6402919214044a002440c2038400c2601d040a107000740c0c003032403040038600300c50f12041203c6500d803240242c0d940f038152002e81c802c509040c070780c0180f45024002d10700d4058045c4d01804003c1c4050f561804081d02820b00400e0513160001f441c0051440c0707480184480400d6a904046030030604038440390359103541c005031540f10740304007089002d0303c800040350100d840c01d40000a10164005101c0320303508180c1c00c5001000d08000441907a50350010160400c0000300e0240c441c28030f42642e0307459940c0641d28861085000c14440c08000d442c0c014094500e06001d40408a01d12504a0000c2c0c1161b00c0000031451 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 526366492 1250 526365242 526365247
    0xb0d05061305071701060e06030c0c010e01060602070503060606191211031006080f070f1b080f0a200a02040203040501141f0f080604170f04030f14030304110907090b0708 75
    0x14250004c005581c01000d00e400d042c013042100801013205031200602c45200c03100005003013054800301750310181108841a0003003207001d48a14009480d210940324691003440f5480104555150003001c940840c017145400c0c1c0d02601e050081510910042d8580c01d02e466a243c80500d81003c0700300003035100c2c0303025050b400c9080c0e091140107441d03400007070000c00c41c40c8040030812240c507030004a0340e40c0010817820083c2e0701c4404501e6800f02100d03130440042c285c0030041038030302c0e0350801000940307000e0404d40c80d071000545203a500f01c00c0380c540c480c40ca000240c0c00f044004000d414554029034126000700c1c0007081903030030401139202010040c0e03000030a03540906050000c03442929880c0000d0001d100500000d2864030f2040e565450f000b80c80600700c4486001a465248416001c0f40c56244d0b024500035103031552810000301c507601b0b0754410b035158100c043d140f030300d40d04001c01100d2040703902105014040c8120001d200c860b200003840d400511011107004114240b001f4040e0200b10700c1035002c10ba = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 526367742 1250 526366492 526366517
    0x1903020301120609020a0b0f0417060f010e360606030a0b1605040914040210050a08010b0a030e1204050102070e060904200607150f0e030313060b120f0d02070b0d0506130507 76
    0x6110102a044010543c001c0018450b4854038414400d044074ec01110040407502c40d992016002051070507a50840c20200e45003400411030700d40c11111036281c035130a95080e40d445105040d00c45d0440c0c03200920000300c4a0008104825820821b01c241225103861401c0988034200e0380c0c2210f6840c0441408403015000300021450006001604100a89025820041d01500140c0200c03010b00a041034010081000404244a90700c801e8464440314100d4250302008125090756910030b000386401801201004038480301da960304140200b034068209182d60380d440d120551450000080c01552818045000c000c9545210140c61998001c114140c4420680945413040fa1440265201c07280e040c940ca548845d0804400d5a0b80100000e101020f070542030310f005402001201116035010400c11303459040d0403c00550b100104422100f00c801044040d00141e03915140c0d80f0900e900d42c0400c029910b424013a0f90802c070781129001d4001e5214101da05028400d40d2821a013039000544040c0905 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 526368992 1250 526367742 526367759
    0xc0f11030c06090a03080705010b0d120206060108043306151106010807030308130f120305250e0112020a1106010909080d091110051903020301120609020a0b0f04 71
    0x100501c040071140d882c43c02881d100411a0b04003148005000307400701048000510500390085040303420b0003030040844200610300600031034046000c2d00c005204500c001640d550040f56914051600800d03004404c0c281420f10020441c14005140c5040342e910034001c6a0f90201c0c040d0502030400d034894100c0700900c290005000300e042610781e0300c0691201300100311019010030351400f40e80e094a410355803035031460540c0505036541c1c0c3d0001c02c904480c05600d4184080741c071600d01e0b030005079a02444161228980c0d49200d00c80705a4010394070030080980e000481c05030a043c9241d40042c101074503204194200704081340c0100c1e01180c00704050701880c00f900501407001a002d0710703141c03004005802c807035190540503006210302d4035a0325030f507001028103101d4041c1020102c4030b4014041c00c031103170146c180185250014400c200f4491a04441034002038080e000ba03d0594104c070f42c2200b51074a0580301c1601030009464180e0300200300d144045804856900100046a5000c2099a42d2031030300083d03 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 526370242 1250 526368992 526369003
    0x10234230114030604050606070503120610030207021513030506100314070815060604030203030c0d030c0c05061b161a01090204270b0409140118020a03080a0c0f1103 73
    0x2035a04001c1a02e040101410100302a00d811184c01e5900107442d5481401150743c3e4403880c54090f049200210300c1101040381d108505101d480247c604120a91120000390180c3c010802d001390b01c4007540c1540b0b2800540c6c00040d0900304040703511004641c1c3e5a4590504041782680c0044030241c003448280180f05c0180098080e504800c00240f20306440d02e91001d413a0040407180c004041540c3c0c02045080d92070f10250f034044c580040c2030303d0b07455001c550361903903404066030741e080403c0c1448490383d5268010f0200240f004c1c1c104010b440c140c7e859400840768044402c0100071401c009100e28000440c190903000651440340040d80320f280140f0442511401059205d044018010041841104a544007484020380752949050503c9a202c0d6902c0192041c51041d03a0441d2400c8050300c1813103075482801060351745c003100800030710186559040d42c0c1c0c001404043e41000c800704d810000291008000c041c51242c034541108442450740d0390410058007440185c8030380506041030181c03480d0a009 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 526371492 1250 526370242 526370309
    0x305010b1801030302120c0102040b04080102121f0b1b0f06070809070f0b160803130c080309150a020a050715030506100e04090203210310090506010234 67
    0x70500d841d07602d5980d0080d40d8150034408900701040201e00d00c129201c0c25010344016020250b100d60711241c0700c400240c002d4002204200d00c402030440072a40000b484502015600003011801c2e40c01030410600c1d0320158089180c010030081c098814800e6000180b0894407105503c1014050f54104110014580300026051440c960003410003000709003c03074850f45088a1045a42c070703450380c0752003540342601461a00041c0003000000100003408240480b00c1c1d607182d126650407501f55031144240b640ea070144c0c6545a400c01019030b1031760284c1c0a814040c02d5110043d1045414180d40c40c1e49450400e1b08542c000340c0340c4203240340701e0204680c050142ea0b45c05441640c1c84124071141c060000d102c0d10b00c030b00d5280c1c0901e540d88880341c1551803d201a150704000c0c00342100ca08000f040c80003d169104036054000c04a03403400c0416402c1d914011140503050590090104030540d005030404040109211480901144030340c4145005400c041d000800c121040e4140c0c0458440001280e9a00e150 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 526372742 1250 526371492 526371529
    0x80d090501020c100507050d03020c150f0103060b1201180606061b060c09080f0307050f070b030c0306131508071509090c0201090f0b010f05090105061902160305010b 73
    0x50501060b6400940030310071020844548034500c0c441d4070140d0307561062040c054594020f45c3c403904070f5039405400034030b2005440343c11581003908485000d045c421050720040c141690312001040854502d0b04800302044004000140008080103a2402c45980b10202c80305004119000b409001c4588070384802000d150038221001018003c00ea506150100e43c000c00c002e584496034420944503000d000080c0902c4001c4030203140144080d141d9a0300405403c44803171050700030300c070ba150f4000b094480454060000e02070645e103901a00b070020ba04020851500428604000b40d01c030031650140340c50035920750140340000d60078247c400f0b08001d91500030891024112035240d8000f640522032200321050b4407400034041c905440102e0141c62101e9020f8040580c5459210038041c0451002d0704861111554104a0350703150f0030700c08102c10034030030154884d20070700000e4050448030f107402e064500d0510581d10b40006010740c05c5100000c9030000e03140e41c0e540354442945030900586a65918050a = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 526373992 1250 526372742 526372757
    0x6010f0b04051f03021b07031515060e01030b090a1401050111030703030b031c120b090c070b06040b12010917072f090411031903050a050a0e0a0f080d 66
    0x1070126180c100c15800c91103100c03d400311500b0156110b075054038600700a4201b5410951403040740c482e40d8143c2800706448034248800a81c9040c001c0f80300d081e919001040c5a064142e2510b0001d4800440c9000300754141510781103c0240340c0d43d08003101d8400c08001000007070303003610f0710500c11801d40305810607810f00a0000349146078802c00000c3c2c803801175040c0f4011400400c40e5011a003800440c0303000c0c1d00c1e03110070b903504080300a03044407280040044200c0104900c6814408001514409949104c0041020480c0c1c10201c0d14025209500c1742019201007800b0000c43c010910400749420000003c2c7d64410f9407404102c15580700200841400c050642403503603d84450740009040703103c00030a0b51112600406400d040240c140c40a20020303c0701e0082e1920381008000c24500f051800d10a001700aa030402c068203003038151500c190141c1d01c60b411f200f10184251420390040800038240150389501c00002c1e601c0d06c2c42c8501130684a100c414810740792210251800002c61142800d21901 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 526375242 1250 526373992 526373999
    0xb0c1005280c050921060a050924010603090501021303150c2a03110d17070206130b06011419090b030108030a0507110907090303020601050a1811090603040506010f0b04 74
    0xc03054502c800380c125140c85e81035030b11140850300da01300b101990140c0c1c003a240400c0038007921a07020510801d0b249040d1189101d014034800071801109203140e019180403001441520300c65070041030140c0c4500001490724101e5406c001100c4070580c4226043c1d080c1c18480e02a01440b8003600003440441e00382a070103e03420f83d803030780c41101140132018480d1941d02d04400c107051040b0210114420060281c880c40b0440100003009202c1001c404c0c6010301302880801c0685100040c2c1c03d124460810660381d0b8100540e90b5034803003400c00780c400743c1040b03c0c0d001b00c0d6114652180080c0300d5401480c2c0504900403031040302030140042039000700f050001c1440100f100c81c0c0c020044a0005106142c02507482406160280205c3e0080400ca41c2204540003000900c80d002040710040d68000d400b00c68090380c0c1c40d0200304020104d405050a0070501410407103000a668100039140403408400364108103d07840400d1250300221816100b5500c0324004005a6260040b11070142c40c9590760b40745450305 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 526376492 1250 526375242 526375247
    0x3021f1218110406150507110a050d020108060111070605030405010b090403120c030617010507030b0415030201030504020f0d200d020d111f0c020423010b0c1005280c 73
    0x41c0300101425160b000340d03260b26140d9850380240c000e0b0940c031001e1700a02c80c801c54000c003203070050b0741e00b10b40d58440710100c120a86402c4204508540c0020700801c1d0160440e8011a0529005032000d070501500308074a0112003002c0c40000b000d003116035501510703445c0a08140f03003560000641c807806606072005100100703901c010a0809148540b5000c02c00710a003d8049009168640c00810942e40e42224049022010741109010320701a94041c0f0511405800304800c0380c00c0e04210114280c4c42020400040d4040d8001c0340c0c0c0a0b0000340b942d050030132024040b54609030103101c01c0758058901e049107224410030010100700c2110075204903401d40210303408541942604900508000c41501c805400d50313443c400d01050142e607844d2201501203d0b000060020038047c1d03404c9100324240141d14060603500d018150214030340f00750556150746821a01c2000394444d00041510703000745040c0d404569028024a8010b004e1000130314044520700041190a00800e00090103040c28002c0c411020381e0b = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 526377742 1250 526376492 526376531
    0xe070e0c22140d170d09060b01140910021c03060f08150f18010e06160c15020a051314010e04020a21090b0f0a0605030616030504030903021f12 63
    0x3a000e0341e07041120f82c0c4500307040d01011018452640410380000e40000b84d080d25400c00c068407407081505021000d114801034500180c0b00030060f1000781c0500411a0380d28000c00c0803141003109006036007180750a0425a8180741343c08114001080d1030f841d0410040c40e5a0007050020106400039040c2c03158240c2d2a10003011b80942414a0301c40c1a0003ca40b10389800e80d1100f90400c4410020001704120307152050b12050211800f0307040104546030345003028010307001c0c02072082d030080411088071903124110000350400440b250404c04180280e228449403c070003035001c3d03c5031022a541c070710180ba0004201b22a0940d850b4091401407024040480e04118a154035082900e10510007060342d02ca0000204034001d8060200e10501e0203011446040d9180c0900600707600d10300740311040d11007003459a100c40559181d401ea5030306c007804420a5100e40d0055030050b10a00d0300c940d41d107030f0300d4001441c1c040030480d00c10b0403c80c82c100c0c101e0306181c028085920b0b0781c01060084c0030700d090040d01d110b83d88 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 526378992 1250 526377742 526377779
    0xa02030304120908031201030b0106020c0a1719051501050103022503121113081621060608100510062a0606061d040b130e070e0c22 58
    0x50b04a0858521401084010050068481180d40307507020280003a941540a21064030030791511000420140c0c40410074103603107000541200c3d01ca03840d007001c01301e42d0381e00e01a0350005070241c20320a461003019400c22285042c080d02c0181240e86042d13503508103800d01a403000f414113104005048400300a8a03c2c0d496501d9a07440c4015052820708054519603504203204140c546002d903d0010100301c07102400c040c1107500e5000c4040754445140960300c011300b0019a80032404400208041d030700f031072004507550308010f0850140500c2e0390b903090259810b0f60800089908003c0c50320509201034450540d0200d000387c00001201e26005001d4140384007507059000300709410101c841104a4070101b4402e065100c202005441c0e600c12006040040c01d401c2903894000003955140103180600a0340c3d141c2030000c00314503010155600103030081408121010141c0a040070004440078040e001d00c0c414041d401125540e200c800005485901002c0c0f81b4446000483d402401038101400f00303141e84 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 526380242 1250 526378992 526379003
    0x210d030b09130303060323060f0403091e050607060b010305100e0115020c0607031808030406050a03020304050f071e0f03110105130905010b1209030307020c1903020402070804050a08030a02030304 86
    0x24516080413005481d060304003416890782481c94001d141c040354200c86042c0549001e940b900c0d114101500c046035400d860160004100c00014491701072000c81d55005c0d040e02228144403503a41c1d1020448a402c40e20007983c0d40d9941d04803001031540c160245c560b110060504c18840c180c140302141c2c002c9541805084003010f8200f000c80b01c61802080100c218500c01866070340c591600349402410142d000c00030a40c0c50a4401d8001200e400c000103403801e0b5151030f207903d420011050401c40094100030710560349031054100c1c2401000040c4081400340485100e4034403458011501c2d204004031075400315500044035082003000c0303543d180d01d902143d80b0034030b0456a94081e80511340711910b15074005003811461305c4000500030020710020b2040c40740800d0b80f4415943d800b0300c4030780c813400b0448501001d600410007085181c5881b061f030f00180100030b000368029a0f201d4001c01c0498001e038008841150000405026516020040000800c1038000543c0791044030344000392a400040c00080c40d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 526381492 1250 526380242 526380271
    0x90c1706030d05030c0d0e0f0705060703050702190306050406061431020903060f0a0f0e0c0f0301060b0a18080c031b0303072013200c010605210d030b09 67
    0x2050010381182ca9144100c441801f60501e01c240d103a44400d1030300500c0c9050702c0340020010301e9040c0201035518550305070701e641d4180000350302408462044404e41c0c0380c0b0b00c01008400f00000b0b460b84643c80c095806007000080044c1080120802588a0711000d07100303580e01c03810709204d9103841c000b030b035080301c180c0b150a4010500024104040d0140e203c407141d040c05500200012202c5451400c3e01c1a4102075091100b04210301131681110000360807000720340c001134115020390a0030010028080070280000805035a031340440306c0c460308154400400a03030003132550f441504801c44200c0203400ca540241c0001c0c590400042e55500d00d108400620341c11040044500b40c2d810301c02d481e10303c0c1d08a94403080000910040c40d148408821007284903102c000010501c02030107104a1130220003034440c0041d1059071100101094100780d500d800030b1740d01c8030030200d1281c880003940c25a111151505400c101c0e00e4070703c22800d2900c0c7d0080c0008140c40c001d02d89181382c0d6556813041d08155000c16664 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 526382742 1250 526381492 526381501
    0x40b0c1c0b032404050c010e18060d05010609060611070e01180b040213031a0105131a0406080c01120b060a0507112809020403050a020f0a030c090c1706030d0503 71
    0x2428541c03006140f0119880030f80b0310840208800f481a8882c51003502a00c0c040c06a42e00151154407080800300c1d0071601584007a004046828001030308603100800091032484982e40d01c500350b0f16035811201c90a80c03900410458190401c800313901c04420100039045035420311256081c1c0c004d05220f204070080e01d4082c02c140f403800684c0031884801700500295602c00c1d204a011014090900c0708a41c1054000041403c010400d002181038400041822580641a214920280c5031540100c02c000d139880c40d0344100c40d5510b1189400500140c80941900e1a60348005010400c40304200d10007142000001495075995030129507440d219418682d84461076414002e410701c1140c11034079002100000b91501c8000c0c03201003034020602e000d4a543c4c4181c0c441d40080207a01071407000401560004488100601d801410700008003005080c14510b42c0c3d81e074944074003c520689c8a41d92150751203030208aa6540030380c4445420116080800e07040c01c01c238021036503c3d240c0b0b1042d40108600031000c80c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 526383992 1250 526382742 526382749
    0xc050f030411061b0705011115010b22090b1005040f0e100b0d1508300c0a15061410120204050a080c10090608010b030402010215040605040b0c1c0b 65
    0x280d00c1c400c0043d41c201c0101c0d024400603030345c0c1c40e03a9015540c0801d0114030b4511010100048000450000325410b140c941d1a0445070006508070110b1030107885c0a0059005807001080c0c0c949004101024010808420010911041e8541710110108000c4c0030001481040a4a90100100c178000c41c0c800d002c6a84500d04951180055007000504002c0091012400700c071a0700b182c030a40285281042c0400d503502a401d586a0152010b0341d64148154100c000d83c107201c6000516030304660040701e02c1c00d180c2d40019803e080011400301daa1079100c0b219049080e000d032052001402c44000001400c5100100188140c05000101c808100507400944000e240a8041e41e006010280101d02100c1d210082151140a502c1c1050b018648003130b113801440f441409240100d55a07504c4012481c1d003412645071441e0f100801c2a0305520900c82025418049035200510440c001c0c940043c19007803901c0e050641d01c02c09001940b00c200103011421501040406010311102511000a1500c081c140030 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 526385242 1250 526383992 526383997
    0x9030c0e0c070c0303110747041d15090f0403110f0d030e160506070503070510020403060c030e0318041b050319230604021b0c040c050f03041106 64
    0x80c072034146084004101030700301d9101c80b10180d00d242603d41f8a6210125211107020108446078002d000c2c0134984200503400321a902052089503004c50001c880584049803580150b0081e88054420f41c07215250080440a542d0014400c080c02200340041c40d0005052035805803604200c40d91100c041020940680d90b00c01d4101509016540440c01e0312843d43d44800d242c24070100030906001e0754001c4614007080e2595235480320442101d0142c02c100510166400000f4201c1312444208080400714100f0480c0007822030103001c000d030b5104e0a514203001a00c41902c003120925040c05910102c54902000385c8141c845515001c100780411000020045c002d45800040d41201004694501641c0100290b10a01b81d00140401030120503529608176001c615407100542030741c910298140031131a503099080580108050708108104030388450703140da80b0400800c3c0d5031160003415070900346801110310000c981d0900d42d05060300083c400c00c1902c00144002d1607942e83c0c022003e003542e522001d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 526386492 1250 526385242 526385257
    0xc060b01050d090c0501021e070311060d050108010213080a1a06060d0204031a010e072309060d0902040c05090915061b01020a0306140d03110106050d060902090709030c0e0c 76
    0x1d0200700f625003071085420704107001d554018001c16807042e100303001c21952900c643d401480100303c144c0c95030310b0790144000212620742d8458070030001d00040440c14020903001c0c0c02340000042e526000d02c0254100076205600400d12500032a00160100f0b40241802d5014020080c820300c80740e44107000502a84034145003402c0303452001c82c001c424000c82c0d21403c121402c400310801c4059803500d0700040b403007600315540b20000344607208402055402c1036030703000c40c600c504140a04041031312002416070b420526400050302d40d138024140640c0b40901030581c0c00c03082d50030101d140592107400b040590700001d06190000310705644018003070315003104845020b60f06021607210904c82c041e46030b010354420490240028142a0081070f24a094a2140042030000b4400030090090740e03029100444042c041e07120b076550750440011103403114180328403510721840c0d0005e81400148100403446001611220811509240500008400d00c8600c0e09481200451400c0c0399591040e900661081e0300 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 526387742 1250 526386492 526386517
    0x102040909060e07150c1b030302061b2502120102040605070c06030203070e27070c030201110c0c010c060b0a0909050613020609040b030705033a0c060b0105 69
    0x5001540c004503900c000c80300c92140d07009202e10044021443c4e0355036502c1c002d03e00c950b10320b400b100001901442c2d510061500c150726400b02288040020b40070441113a0095001d60449010400340021080c04180c5075151804402c0c20800d408242105207120412024404c661074095002955990301d490700c1d8503200d16009550329030301c1d4440203146801c00002122030f01d4100d240414020b0003402600d2142403650359004039031440208000720b2441c2010300d903a0b203030383c1d5000100c05200550081841415a0384804841c64010b203002801c403070180c3e024150424050003807540c141008140817540744400d290072102c601d0317a402d106d00205484100305500204040c40040c0c1d1040c2500850b505a000340c0c180c03441079031480c0a1500f10380700000d000703500540c04c110600c081c2c0b030160312455031200d0107800c44420356118008685440c03000586002c500d401e0080b02c17108049960601c010724051007100c1181d9a010f150003078115240481d00910040e00c8018001c001c1e440303001551502414403 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 526388992 1250 526387742 526387747
    0x1201090b09010c0f02010e060f0c2a0705030a11091008010e0706090b03070e0405100506030921040602120f070813030b01050114030109090f0f05011a180f0c04080102 73
    0x6480345030080c051521000040742100013004500ba0041c400c241890f40034002920721651960000350241500402e00c042d680001d020546a512f51005012005001c1105600380e5441a12400b80703020301c240e02051003940001290b40024011014507100000280d8403282d05d40c59242c8090303951203082d0424901c81d031070601c0440d0341c0440050040225001621503c01c0c4030b481c1c80c84031101b488225404004250058140c190070709140d4080307035025a617140c0c280310240e04c0f81e0026a5070b500c1070720514104d80c403405c0008406034110908000c102c1025619510709443d000e000303515420340301404000ea050120710b07110000d410a0864aa0740c0d48920301d690380b041412a207040310300c0349010544501100078004201d40d401480b4000500543d494032a0450707203481c0801c809000e0701030044901030b068042c07003c0003502200034030092601c10400418034205c0d401740c21b0380c042142150700344140c40c640340001d2141048140c440d0440c014004904e0943d40b80c840c0ca400500c40d5038001c08056200 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 526390242 1250 526388992 526389001
    0x905010216030f03050703050c03070f050c0a03120e0102090102060a02182d01030605210106030c0b072f12210c060a020406050406081003080a200109030e1201090b 72
    0x216214503c3c0003200d0f1030070002d58882400840848134210703000c07100c2030020030114008500440304140e00d5075061600610f8010404040c2e4200000f86404030040344003c11380d0a480c60182c003584801c0e004d080001c50914200030b00003999140054807038103000e903000480c0c558844002607c4a1342950141c40d0403002d0f84050190000d900ca1100954094504413a0850480d1b200c0d01410048480080c40300e040ea12444060282c0f501070540b42040c550740e6800c00000084002410b140103102d6601d8450b00e6000310b0600c0d41c002070480241c00c44040a100c4805c4a42e10404041c00142506484540684c200e10401c01c2c0361a9903030b00301c40d11400491002462800d00c8400812080c1050001c0d214a612042c6044041c2d00640c0140008204148001c0c004148039a402d140e00031241015a160b00d6645c1d10f600ca92544100317802000a058404080b88142501e400c540a1000c044000c100d0424692001002003040c0345d5224490150650384041c00e0009401084006d034000c0201a01400e0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 526391492 1250 526390242 526390247
    0xf13050316050606030f100c03060801050403020a020a06021f090201200d09060e1e010c0c0308130b13090e01020d06090504120f0801060503061c030305060109080a02010c06090501021603 82
    0x8050204071024443e0500040c1c181c1400302e440c0c4002000c09008100c0200d5040070310000e440c030f820002040554803000050002c1090003524007481c046d070094070342c082450040c08406d40c50307500440290350102c440b0078900d2030560361854041c1c095030030009122205d480100c0b45e6a00d1040041c03101402c0a000b12501c0d00d000c120040454203d031103004d00c076543c0781026203055440c64402c0380e04c40008041000f80c201d0346d00108110010503d00140325821584e03400c01c0c1e00c1c0046d002510150808030718410b10b0510351442034080c0ca00e035207541c1c1c00c3c00c04080c48134950101034050341d856540c0b54400c000000c0e070250191501c40d985a1003d004443d01d4208000080000311026100c001d881a40c1d81d10310744c01a10b01d0401d00e40e4590780c5c1043d580c240142540c00340d1000e0503a542000342d6040c4006d00c81803017022000190310980d0049010304041c0001072241700103030030144094010030200c10040c0c0c0c1010308190510340c4481d021400e4019800c0c454024002e20b03442c01c1c94045400e041c03404255 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 526392742 1250 526391492 526391527
    0xb1614091017040605250e06090f0a08011a0f1c110d060209030c0d020109060813080403080a031b020c04050a0f02120106080a0203060108060d0213061e0803070b0f130503 75
    0x107240382010310400054841b26035158910034240e8000c141c400800061074103058004100000c03000e002681c19543c41e00106445070000d80c042001d40e5921295424140300e1010b481403c080200d542c812030b00d100000040d003024403907040e841c20700d1201119004020301421606601d00380100075010f402c0650610801950050354843c1c4240500c000300e1429240c004121440e060b0183c1d541e00502d800c025050f0740c429000741c030b00d4150244c003080200005000c900144043d511595015482e00b0980ca40a0195184065510100307590001080f2105900003400c116a100486d00842c5a489030101300300280040701d07400015500001c0c0e81100c24060b400040d04860b01d60341d03040c2c016900c064454040f8002500d003140001c0307015010551070700c0d012102c1704c096400104000d480282035654041110309640c450a00e421442c038883c00c500c9181644a0010a220070146150204944d640707108480000d0140d200000a040407404200800a01d085042ea012085a0b82c5603884488146843e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 526393992 1250 526392742 526392751
    0x90c01090905040809090a06230f0a0b0d15030c0b0a17040519051c0917010e0706080912030103050601030209060f0a06120e01090b1614091017040605 66
    0x580020800140700d070151186600c00c0b50882c644505145009003013090408000d07010750380090b211030002c01c0c0c1e0215402120030401341070060300c800c58241000d0004003200d8107200d501c030700d060440802c0703640d80c45011203008038846500021041e0503201100819055900090520101d44c40b01054203070110740200010f003c0303a100e009204c01408a02c1c0e00405040303600a20719003141c000c00e082d8441598005061742c0c401c9007543c1d010000200c920b0400d0f00008004000200f04840400c0404240509040080c1208000340151084002c038560307951860f01ca007804004404c00010b462a000b84010340410240ca11000e50707e50b581c0c20090b98824081c00141e100340301a070081a46442c2841030804001d90103021800d0481c503044c001c0d5120405618060101c0b500c030140d00c0030381142031040241d114815800b42007242012074000140c1c03500034500d50300340a6820310264070034400000b0b8600c0f020085070480c0c1c145804076000c480c14984100c003100708071483c0060004001c05600584d126 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 526395242 1250 526393992 526393997
    0x100213080a030c0b0705041e030c080c03031e07200103050a060e0a0b061306200102160f02010c1a07020d08060f0622031203050105010f090509070215090c01 69
    0x2900e484003042a10340c951104000c011450120208000524220100c1d40c030807541e042c0a401d040e9104a10b0240448811030982008040c203001d004012015500001a00100004000060810000c281d4a10640600341b00807000f91303080c050801c4048080f1800c0072340c00504c10103000d5506494070721407000294502e0219052000203241c0c2041440342c80c0031141186000c1d041519508c084200500081c07030841d420980070410802c410700071050200c010f06442e5298141962040307412542c2d449420361a000e240d004010707010002c1881d01030782c01015042080d400700c003e1103200507070750140d00d03007030080c52480901c1d0726844130790304107001510030305c0c2c00c4c3c0030f0b83c0702c40406400864000d2011151079502c20304006618010f420314070050013081c54080c4507040c00b01400902c00c184041140c0c000c4448500c0603013031095141e40f40c06040d004107001c0c2800000f00004140c0607000d041103000743c1d401280c060001502481c400c12542c056962902002c07490350600301e05964855038113120b16400b = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 526396492 1250 526395242 526395277
    0xc0b0720090f010303120605041506080f090a031214040308040311010501081902010306171e0a0b0601050c0313030b012c1308040f0b04090f05090a03110f1002 70
    0x44038280300c05442e00c6840d80c02aa8580e903800c5980c20303107201074a043c0052205070313190000b103400c0c1c0f0341d4454004001a5400491402c2d454440c00402410b401005150110150030501c00001d100250107400c803507040c2044a82a0398600d500e01c001c05412800b07081c3e04425800303001c00d040d00194114040e500940e1102010003800150a017651028441c40311568000c02d105207884c0c100740ca411400d148145008181d03907a841c00304002800c200f00305000d0903000800c0c146004070380a40c5100a110306000900500302030343d11748400407100100100d0501c14001003001d050b041c00d1080b00c5210b1410119600415120b06001070044800d0080001c201c2c4405045525184280070038890100b00c506005429905d052200030041700441080702d044a09100100b4201d94941005018101910a01c3e850b50300d0015942c040c4c40700300b05d000c00038624240a1206103039003c101d565106426080030108166100d0300c0300c0c44c00078401e112616a01580c3c0e4591411690350700103117001551004c0030325 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 526397742 1250 526396492 526396553
    0x1030c230421050705010e0d05030315011b03050f09010e040f091205120c090d0b0703020d0c0e030a020f6d060909080705061b12040c0b07 61
    0x2841079000d0001034810303486802c4c00c020a41c4a09000c0030391940c003500d040d5010780746564044ca1500152800444280007980d48040703540e11580c08803000018009462094900e9203015016110300714008020000003d680da0407640198504c808020028000301700d040c2d0900e603480000e1a81c084102c0789652210707101c1240c40d108801307646608a015000310400c0e143d41681040e10342c4001c000c00d40160302072149101288149a0083c8124200e440159032500795051800440714280c50a20520480050040e0191070001d4280c00307490341a04e1041e803010003400051100e642c611064031605070f02c82c040c1d1060140002c1e0346600c0101d407140c050b1070034520041346281960650001e801000e100e039111080b11079a51145020748100200c0010b4494807560014292038008100f0755101f9030000d6410200102000b107a68044010400010f03030002031244a07420384504040c04110f00a00e102050a01c804115894010900607030017680da41a6450100301215200c078411081281d10780006 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 526398992 1250 526397742 526397789
    0x60604181e020c0c01050c100608060f10030b150f040509011d0604021807120903050408151b0706020f040f05030709050f042d15061205030901030c2304 67
    0x481d0f00078940c80203080381101007401114030350000441c1031460f1250100c004450845882800090008400900101c0c81c0140b070f800d240c1356020b00559011501c450080021030b048003c8190131503211002d00484503401000140b051007003911559103d0715003803d0154030347d0150b000170551022503000c04a00000c070703058a07880d200b040318043d4211103c000000001c0080c100034962017040360401b1a00c0c44580302c5400200d0b141c1980c00c401003200000c044c072030100100100f5043c070b01c0c0082541c900b460310421f400303200c000e074200d165038034240441e00004000058069a159001e540800c94aa944e10862142200650705c07038640240503140000c50ba00c0954025203100d083d40c071251951688950b5034030204c5c0a58112000c201c48210a90105907800c038044bc0140240030300b005010754803400004a084421640c0000301c941594000320000540100c00d860440009080c0001c0c2904402400d4400c090b0302c0111350340c2d44a960440d5003250750000c015200307036500e800d5010924001000392 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 526400242 1250 526398992 526398997
    0x315010311040302090c0f0a0206150f0a0b13090f061703070308071b080d0e0c0409050a0f03050c0a0f110a06080a110f070b04050c06120708060604181e02 68
    0xc040794004104418005424007a402d60b411650b81d035403007840e04600d5108110190010b080d8100180c00074001d02105402901884c41c1c0c0c020b0448034910410440c00000700c080e040c0e80b1405c141003001042015035484041aa44010483d0301424003421005401c100018074180c003504005140c5c00c505c0c142150000000da5552550503215008562601e5005481e0002c21075285107100c0b0302c225809000034a440040c0c81d0061040c1c001049008a80b050709041c013101c450788134000c0d4944080c110208000150f50036105403c4100d03c2c03c440440d0804540620902021403013a01c1110300642c01c0100c50007000103000e01071002c09018039000410403504c40424450500010180c0c03010840507082036102d00c003500e801e1a81c942c5030042d181d82600e8540c200766400e89481241000b000148541030020340a0f24404450f098944488148400512030002d09084100b11241002820a8076032408540160603030354040b840022503003245070041c110b0140030303e1a5a40305c544e001d0350003000707009 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 526401492 1250 526400242 526400261
    0x3071d0433030302031e090604140f060a020c090411040507090314011b0e010c12090306050609010e18190606031110020705060c0c04090c1a0f0a08070c0b090303150103 74
    0xa50f180280da0007400612900281050f009410104a0b049107543c50f480100002c244113420704440c402e40c00100650301008402f01c0780602d0040098031515540410101d001c00d100310343c0110729865a003041c0701001c0c01d80102c00c0e001071600c8107000c1041e8211a03900200c070b1186d440740e2040b255140419090b50142d14901d5195040c48030b11405880c095450305540d94010701d4208022031040d00c8680c1c10714481c100f40004200c1c0d0840c1842404154001c080d400307041500c0740c00d403039490903861b030103001c4004042c400413100148420192107400d1180c10003503014504a101c0480d4982040b00c000c06551200302c864020000b0320603001d0400451084000741d00d500640310044c0360400340161175011503000041d500901d007400d0303280d40c2c85118460615000301c1c9280c92031800e03c3e194485001c0801d2103415060070921042c8003040b0031404031441310205203403c0907030b40c07100c0704240c4000e415030b8401428891400100300200340000069071003400840503c500181d060401502106d91115 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 526402742 1250 526401492 526401497
    0x5010c06090c0e0115020a0506060f0103140f06040b0f0d140a0507080313050f030c040e01020c01050a02070303060e0103110f040b030d0f180b03011e0f0f030201030c1403071d04330303 81
    0x840c2b51501804407400300d00d040c1030120340921030b2800160b2445080703900e42d02000c403000c1445500d05040c49800c8910f241919925112110000007601170035448a005100c0300001c03002c144411000d10080c42820303403003000c03641401d03101e0b13030b03c1920307504005130305403601f0005000086c152030703c11a0003023242c8010300034245110780c01082c4005402ca4009040d001c1d90208041c0c40802024840d2901c1840072540060700e0f05624500102070b10803e030b0052446496030001440071517415220580612021520303034480c0040e036000304000d00210b44400350b00d4040c42c10040240d075000440341100d15110390314543c070f040103100074500007000f60040840540301440140b008010541c040b00d60801d00007501c080c040e6a6010001c00d4121f980c105a1f40209544801c00842d601401600b250006906101c13110a500c0c0c1c1c402e803600e0000a180400304086048020301300e000c1e1403444d29607108040c2080c4994600340e8800c040a5100329481e6410010f8143c2da0100b1012604413003013036a0303065 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 526403992 1250 526402742 526402753
    0x513030806090c0c0717070e1b09031002030a02090405060a180240080102072a0b0c030a1e1b030e0306070e1f02030405010c06090c0e0115020a05 64
    0x900030b1000ca00401070420a1040c0304201000010f0001c11240004200103407051254488590f601818004940d21144074034014000340420682d03000e511041d290003a241440e00d41c0c000da030000c0d141c10301039400c910480c6d10000c14420080c0240d00200103041054800b4041d41d19501c0601c0078401e041d10400400c10030421020310075494940090143c844a0040d8800f1103409400020380540c00c000f41c4003032058001040b003c00e1542c400d1520060070460300841c21b2001c161a48031185400080300040c01d00100b404020949940c04544050301c812011252542e84e00b00c243c0d42d80b684140c0070071000ca80345880d4103800030602d0440070f407295181e03551508000580080107400c3c20020b40c00310203014140030040c08a0314100300c0c841c4142a21b5484440714070b0711506200080c1035144447c0c40007428000120180c940000031181215401e123040410340045007000070080a016800030030b844000e0310000344c210300103180305050390024814004256000c0740c041c0d0f030300c10703c001d0001c1194110 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 526405242 1250 526403992 526404001
    0x1606120c230705010615210b060403020111011506030c02120301120602070503070615090e19110a0f080309030d090f0603050411090f01060f031a0603040204021207021005130308 78
    0x1c0002a01205106034004034146882c0c240e080300b400e0754041c400001030006800125480c204a00580c3c016940041c20000072001d20045207032480344e80006810312401e13412030543c402095020b810400300b0f407030003500d800b51144001000b03010807140da80b0040c0b0035200d5099496a00c002102c3c1200c0640c0741e00340c2c0a65855507a90041d4118810559580c0014070118000c20403c0c0a44110f0b42c3c0301403402d07038880d410040e1080c121241c0070f00b0940d4582c41040100ca004110350b442860b010741010f00001078407002c2c1d0000e1070406241d002143d03045124030300060760b40e1001015111007031040717050711000030101004a50350240c0384580c5038088240d203420461030740664095600680500300c4000602054004619690410740d400c1c6801c0c0150b40040144076400401d400b100e002c0c601d0107010360420801908195040340ca020b0344074180000c0841c04564640c0e049070718506900240760b0203483c20b90001b070344030010400300181c02410040051041000c06603a4644103a0503110040315071038 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 526406492 1250 526405242 526405307
    0x11031605011e0e0a0b0c06070806090a05060f06070c090c050309030a0e0402090411070b060f01020705090907082e0213030809120304090606120b150c1606120c 70
    0x21a01d15050512585480480051300c03510406070141030700c5680d860ba2046212030320351408500800b0301c3c04005040301804010764640c1d0302d49420503011000800c254850000044110f43c005035141d5001900142c030004100300030300390310f085502e04c280030400c09603550025a01c52108039801c000c15041084001d801c0c80c02603c0c0c0765150080a400103041c5100c2c440407604482d094503407000d0035100807801c42c00f0008083c108030750045058983c0c050728910480080d640f94510701619211b121400002510f42400b08030300c030020b00d1017108441c28241c00307014107940710162070160700c03c00c0c0d004480c261106a06008444245180c04a200400c1d440c3d42c03516a0300d80c0000c0d2000da80b00b0500040202c450303004001600c003410481c440001e96900e4040003070f04d0100490b90116420341840000750076a0b4a030b00d4000000b89220070441d9903105c4c0f8882060402610a1010200b41c9440c040480c400764811955030400410741001c11036509820016641060641c1110b10700c141903003d40e501500 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 526407742 1250 526406492 526406537
    0x705030c090a17011b052a06070f08161d2809060e040c050105030415050103030305160507050c060a03111611060a0203120c161103160501 61
    0x40419609908000c41c180000b01031101d260300003207081d68404558405490300b8411426651100308001c01c0d416400c140140280c00354a40d5a0600d402c4620036899100c200c41d00100301441e044250351003898110f0016081800c0011080c0024550400082d40301d40c2c100c1b20300f4221002900c0b00c0c000007070000713038901410414503c940e4100c3c1c030b076660301ca050324180e5400d1046a20f041d90f041c0381349801e00300c181e021100035a000701c21284500c1c00340300116154081100640c1e40038a040b0340e581d59182003040840c00d400c44449010f074940360001041c90760507408a030141040d41d00e07140aa40e030480c0119100d0151582c0078059400545c420885032411034020310322800b880c18040742c500045012030714641c00420302000b450703e601405034100001c8140841c50003808560345420200740340c00080d9a80140c1a09031a070380048808100071f6402c207001d40300714812410651040c2d0f9480d24103001402c0d0807032603031802841550742104010009890900c00c0d220181d50352103070200005600300d0940b = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 526408992 1250 526407742 526407751
    0x80c0102340e090105070305090109030e04020a0c0b1e252007060201200c120313151a06090f09040221061f03170304330e010b09070503 60
    0xa01c102100098554400c800c054855110480005024030340050042c00b5650014885070560749040210f000181e046070010440000503540161070704035881040e20091090322010340b030b4598210420103443d142803400040d40b55414401406030b140e41c24490120400540c10044903a5401d03200700d0400e110300708000c41c00721390301a0094a9450590442d04041c942d41043d00142d4580300b00031003420100301030740822a411100c06150982450100d515441c261040c004065000004242012030245a0382c2840c0d40142040c40103445420600005141035105c2d0303020035440e45040000c40c6003d900f900c1158902a0800783c03181100b40420400b580c00a004aa100c4088605529a50520070842c01d25120f4030b8000d12942c14481c5082d034409880c07040c226090510401d090000440b1028040c0075007940d048540d41780c2d01d99240074682403c003000680030311012204041240c850543c0302102000039400104072540c3c010034407500340c4601c048544d401203000804200b034241700304003c5500 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 526410242 1250 526408992 526409083
    0x204060e06070c0b1317060f0f09032502040b01030b0303030601030906110c0606120f07060302090f031f0b1503040237051008310503030c04080c0102 66
    0x1115151510203655170462041d00601d02d91025003800b2914003c0f035503400b104d140034020040351401a1028603080340081c10702c01a00b10038400f0402e07d250400c25070310542030110010000003211a50184203802d0307860241d108606000c0401c90300d501920070021001d80c0a005149140c1d2400c2c019809410310340f90847d00f40d030b903d48120350147c0e000004ac01c040100d01c400391540c1d040c01c404200e00c0c1845002c61050680028a0800b007440e80000c0381d104607103003400e001d80c4406100002519003c401501160076005004402c2c08600e82c0d800c2c1140b00c40400b640800c110100c0301d00303111142544800381da44008040000c100945403840c00350031405112445140c0b2040002008101101e43c2d8802e0500300104002c103100518103120f408d83d01c19004e01d0980c9440c44c1450480c0110ba01003441d403ca401186910407000c0008e8070010740c441c82d00107003180d559003465080048142e01c00e100380302c802e006070420451070307610200301c1d0034295103c0c030040c900040080080d400a09001aa614035 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 526411492 1250 526410242 526410263
    0x3090608042307170304060e060a0c02042310080601080a02030a17040b12010e0a0903020a031107090e100b040b060409050c0d0501060f020d0e01090611011103040f150204060e0607 79
    0xc4c0707071242c180c541900350090b60141d40c5841c9007800c054170f045030705030300789102d01000e00004441c142e010409520b130b5501101e010070120400344011082c651803850b4070043d910900100b018600901c00c0310011a60200c0443e403c5030b030380314412a2928241c2e14000d6140d00080054000310f40382c10341600c0d000c0120068545400c3d507603145918950700007481c1c3c4030040c204c10010400ca08804801540c0494201802d04c00b42001e0782e030082d01c0d080206001014000381403180764640c0002c01110740544101e004c10407005180345101c0340c0d40d03440040012621418080080500e041500550401f8200030703092600309810f20002e44080c02c80180640d00202c802c0c08074908003c1c490140c18024a6151504178050b40e41d0f02000317080243c1600060144442c0703a91030f11080e42d000400e0700866105145c9003541e410307110305003070140c4550309002c8510500401840107000f820290540c07654801d803400c4410310390f10141d110580c0070b14401c18012958140b08888103051030001030440500c1421200d8 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 526412742 1250 526411492 526411499
    0x20601080304061d040618050601081303030c0c0b071d120607111f050109180c0612020415050301081e06130302010209040f021c1a0d050718020703090608042307 71
    0x101203405517400b00c00381c0c1c10901d07c0f441410044d441a95000317003007880d1000e050301c0c1000d0b10710385002800d0001800c16a4a1004070102840b4598000641e0f500c8070f40c06040742095180180740c04204000e11884050052502e4294034049041c010b03014440805400c1c6561004420f8400c04246000c40d42c0600402c1c4400c02c80310301f8405c00035820842e071113000660b5410408441d003240d0511011035030b400c002c0b83c0310001150450986008540f110f02d49941c00e1541c40f0b110402030b014540c000181208200403501041ea008405181600c400c1000c4038811b2080c1031000c40100e20021b26541540c00010205071518100e4200d050058001c0c000585449400000700d422140da50500d460310a5012404181c0b03800260980301c05420711400600c2440390014140080c0300d031020140d80b2501c0704111200401c803042c0310440042451441032280300b54103c1d000d2020f980203036400c40c0007074100c00c1e01003078482c01810402c0c040c5400103400194414068a218800841c501c08901180705041001 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 526413992 1250 526412742 526412749
    0x803250201020a1a070305070e0d1211030f04031a0f011208041511071a030a020d060b0c03070c060f05160c09020f0d0501050301020306130b0a03080304120f020601080304061d 77
    0xd1210315450180340d0b5951170040f03801002c40d000940035001300040b03040e484155665400c0104441c980058a6034030131006500706451740407600101140c00c0c000824820355149141000c0c004a9000c1c0030980d12940606c41c07248040707401160140403140100c00140036800c1c1000c0c007a004030b4824100503161940f18030052800c018011411000185004d08007240d424061140030010b112400801401c24240d601c00000350100a20800b9103985c08a2405240320450308050010b2240d01030480d03494904e5243c0350384903800400203483c640c034080800141d081c416060001300b0400ca949046c01d0400d00c0d40c18021459803104142c902c3c851300b0364080b41c101403078401011715100081650ba80c1340c009100000907100141d0041d80309920600c20483c00d5203a8600b1008a05e84045000808a244030000350b0703083c202c0d400252043d64040104010011030752003419001d400c544618241081c203400c2240c2d241000d00650440350028081081910300441c0d40350405070300701640740a86404d20010 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 526415242 1250 526413992 526414013
    0x120803131716020a09021305040207020609150d0e060615070204060509130506100b1b070810020315040614010309050a0f080720010509010c240b03070803250201020a 73
    0x107641d0b003600b2400103021868001074030401400211002d5040c01e0b080c508000e125000780c07003628007880e00020f43c1000c55031040c1c2198031540300141080e00c01890000c403650710390000f41501d00450701d841200d84200d0400114a0702c9081c00906440d0746440c010620742280e089264126042174a99002080700c1e9500b64156210f02102c0ca04980303c01c2007802d00d0751802c070003d030030f82c0349003c09403c01703204030302c4810300301c4155414074916101340740842c120711403411155500a024078003600440d003172160350f1380c0c000f180982100d054090054000b4410072003214024032800041e880107004c184082d5020b0740000302800d00560655001603547d403104c4416604c007032011250080001040001c2260300711204071030380e100742150107000750700c0d900107090361080300d404a0502c40c0443c2d840007008042803203211580c290381e58150780601c4000c5078401074240951020301c40e0203401c1000c50040b800005564102c0302c2c0d08080d01c0c141d0314443d000b05d0342280701c0c2c00c2a030442c00380803900808110350055 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 526416492 1250 526415242 526415257
    0xf280906022a10140103080a12020c0c01030b06090136031506080d0503010521011d0105060d0f0f020a1e080c0105030115030c0e0a0b03010509011208031317 69
    0x144000d032415101c0c0540d007844241c401e052280307450244003500f008a102c4a40303054983c001c0f05543d544070362300c500b610012800240c0c110402e000140b4503425100124203c18050400e89080c080c040890041080d58012080c00345c2c0081e82105004403440081841611100f400486940f409039070000300101003080c64000751111980c0d0040017409800c5031181c031004015490280441344945030700241288810310800744a189045030544c00d101e4a540f480510140d29402003000480041c0b841c03055003040080d1400c15440c01d0001010b6050003155404282d9200014244094442d520f084003580d100000340c0c2c0100d400340700856012100030405208510800d04166510b00d8010003904e0150429015810030805000400079601201c070030114948480c10003040c0030b4400c010846244841d1242694004220000013500302c0750400154142c0c1c41c2501d510002c1c0e83ca030607115042c0703881400c0c010320b101c00400c00501400d201c1c49040c045076200b181d0444100c21620b41000c103a400203031 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 526417742 1250 526416492 526416547
    0x11040b040e0f0a050906010b0904060510024615020427020a050f0c011407120608070501020a021c150c030e0d05030105150403020301050a050f28090602 67
    0x2014800b111201111540e07119060440a000e58501903552075160b01d81031142210702c40d00444c06800596864002c4e5014010190414130706d003a007400020368450000589000e0800204c1c00c0030031500780c805660591315284c407543c05a48003a8010030074034000d40e80d01910025030007035070b07d10803a400340001d00043c00440c800c8805a03c0c0301c2c891205415400c2c0140004503c100009002140c101080d01e98101c0c64481c0a0f031103852944070140501441d003e88000e20f001c40040140c0c180e04481a100201c0407200100402615806025a00c26280c082c960250340104019401403030030103100c0054500d4000304816019481e038401010103d4509980d1031aa01d035520070800517410f100d400000d640c0c4074001e1001a034100380182035407006000d1a405182c00620664131141114125030095034040d00801182ca06000254010042034a00e03884000861020070040395404003400b044110341c08144400c80d496000c128002e00a07000704451007602480348102030024604242003ca0140 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 526418992 1250 526417742 526417769
    0xf050c03011e0609170c040603081c15050402031f0b0a0807260a090812011509030b0a05060d080c0a0224091e0d060b0a0e090d0311040b04 61
    0x2a02c2541c9954548a203203080d51200c01c11203d50b010380c41e03100301c1e103a15041108451042544a080c001740d0b10505400904210000040000c444010700d010b00c207804244490f4100c90110b88180d0711a082040342a003003601e0140f209140682c001c1d034001441e1440855440c400e4028032024407465402240c1b101c10100e14040e0345904402d60300c1e48140f40e858200c0b85e43c0b20311010b400e03039044014000b071810054100080c0c1d0818455100d485225044072201d520b9140266859260340d8003400b500c103145000c0030b041d4440601881c0e0804c180e0354800031101b01a42d0342d13010440102002043d1640c004004010315000c100000001d014440064028000022460041c01810221014200003607856505d441e4035019500041c0c8824801c00c84890071103c18030721030310b109440c0b14040ba0368440c1c00d161030b8404015403540300c0c800100e02925903000b526515241446101030480c2c10b0700ea00e80100b40e88094043c4250f0041c4400f00b15456840c2c109610303001d030070440d44c0203504041c1c400c4060 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 526420242 1250 526418992 526418999
    0xc030610180b060a0c08040b16060608030f12091e010e060105120a060e030f031602010b101707140d0e07050a12200d0308070e0306040c1401030f050c0301 68
    0x2100d0704091541640030500c046451180451041c1c401c0c80810000c1000d00900c4400b040304e0ba01c1118018540300600d103403998003952143c802400e0620b011105030380382450010380c5400110039a64202001c43d403050514801c0c60001520072401003650a15004030f01c0854003034140b4003030540d202021240002180658214071500d4000d042e0441031041c0140c1c1c0d20722181c2c0100040d081382017544030201142100709030708224510f00a8410300d801940d80031042051346812601c0010a60100d50300901260681d0000c3c494a0001003140600007003246407402000d0703040065558100030181b4006032046005002541550000e40001d50340c2501e508400c2d0405d20200907203806000708860040d8114508600c02c065610440c4008010340c2e00709000b88143c000450118901820142c1802803c2c0300d20b180003404c00404076880404500700b054405410300b03001035141e100e5540541c04410240c18190103107980006c2040703e03810191901882d10224615026250007001d0600040e9140d504 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 526421492 1250 526420242 526420259
    0x3070309060513020f01031a09010308220b030103200405040302030309010e0309180c0c01060305101103040203060117030702040e070e0c0c12031503011a01030b042901020c030610 79
    0x42d100000b41c1c45052081c2003daa590f15955581d54000d00740081c40d282341c00200700005980340d01c0c09501c80c112000010034041c0c44001088a10070345080c00c40042080011307043c54038018098041c070540203000600024420903040070004810400965041101c0c0380003d060314400c880860050f04084203004404800b40110700019603078002a5042803100c0c0301080000e100c42c44900c155148200c00f1401c003012510886882c0c0042c00c009000d107948038101582c3e0755030360480100083d0f203802545020741c100b80307040c1c03030185a00a015180f507900e03102d0300560584800e511071815020400c2680010f0341d592081e9038003043d5400282004a1409540000c50540248880030303107802008541603085000c01c43c850420440e0403075580341d4580c29403130035141545244c01509580b07070000101100410300b401880950b0246d80a120803036203081400107681d400c0000202804003006101030140c0b0011000220f07541c103104480d81402060006490810117690544007a2a11002441a1803 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 526422742 1250 526421492 526421501
    0xe16080613110922120801120807170904060807080c01030903050403062427021c0b040f0606050304030f170105190308040803040f050a030512030c0c030307030906 72
    0x5000144010580381c1900c0360681030312012451485550342d040010309601c4030f1500180b807182500c4400501507070f2441d103440003848001590001c00c1e8000d000103801c0541e44d4410b00450f51040c41c11f07052200b0b43d0b652103d00c030365890703081003100c0c810302036000c003074481c1d02c036036002040868010241180b134100211708010039070401c0d50400d818500c00c2e80210f6080f9080320b003104d5011138006401006a405241910041d0b0400302e000740d415640000c40d660b1400010105000d602c0c1c0880c9042a00d011031401c038440da0000c001c03a4812000410b040b0ba0081d030082e05c113620044e0021403c506100000e0342298071a070411004682c0c0070003480f040c19407000c005809942c0e0b03810038601034801c03000030301e01182051080c18851825404040101040025450015039101c1740994440d9280c000c0c60703032280c000d0f00500e520078803c1840040c81d454415102c0742220341020162820640220821001d0340c002001c0b071801c01400c021004500d0010001948142096079000032441d240b490a6015038 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 526423992 1250 526422742 526422751
    0x6220e0c0a0305010509040807120203040b0d0e0606010929160b1b07020a090c0c390e1f0b07030917010203070f031d160801050117030a120e160806 65
    0x2086001b04110009030100c0032039404507009048562450302c44d0804a20f584a00d03088501041004a10300b408001540c0005e071000440300d094130055a43c0c4001160303400c0391449a0300ea030440c048803d440d01c008400c00d20100c1612003486c03c0c5041c807002c500003207505101d80112560341c2c030141080101e004001440071240c08241026107010000d0f00000c82c1d0b42e88601504d820b45640c0e03104e0901c01800350f10007200c060340c000003441541c4003101c081c08040c02200107c4a403060030040f903548592840f8104400e5510700d1060590b19103800642c504a2141c520504034042c0c20307044045100071910025280d4680329a440410b89424118a2343c001c108404462419a00600c107000100360400c40d02040105649400a00c0d400c000d0380d04610958000f44060300d0b0302803107144115004030b151009003a0307000300e0000d00032a6a81c0c00010312080308510880e90540040c0b00c0c80d106984036000070a10301076510000700c1c0c20072032520b1980c00c140ca002020404642000c00c10869214240802d6510 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 526425242 1250 526423992 526423999
    0x81b03040b390d0906090609120e030a200a03050106091a030307030e01120c020a060c0216030b0604060b0408010f110307050904022503050c150606220e0c0a03050105 73
    0x2103140c81414034040c001c100068141c011010070803c01c031107101e40c0411030303454001c0f5003801030300b0050905100401003904184c1d04080c40c0c90042c081640102083c92203150301400800300c075031660301ca1410340402c010115a0f0101511044811681c0e052020006140140000290726240a03022021103d01e40000c1c4180b0116030450b440e280c2d030110554200607058180444c2c483c8070744004840003004121000c0300d00b07141c105000d901c60390004000300494071454081001e0300c1030400581c3d036680350389100741021544402c01d03c00541c0c0484602c1c0c102101420200da0b1a8591240030410b4205800010190b99a803044140101680c02500114517410b070000307286d0300740030714003c080d8400c0d420241d009a40010b8414000004107080d01c140d000002c006000140041c40c0040240e4040a2005441c1c881c02d081c0d5080d50f003035005c0b018000e02c401005036140282d1404061590014121813a040c0c0e015031100180070b0780343d13010191089081c1b22241b590780003480409000c0b210181c200e01d00 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 526426492 1250 526425242 526425301
    0x1060e040201050d0c02072c010f1523030a0905060a1e09030203090a0f051f0203030601030e160e07031508070605070206041a030115030b010c0201081b03040b 70
    0x542d80100480325802003002000c203040d032900b0000d9107820307001c0e8000c0f07800c0140811001010342c1949002da0307141c2ca00d14036040f889c3e41c3e10140340c0401d413003502880c1c040541100e540201207000c3e64170040800e6011346001c0104000c010340300e080380c00403518500321540ba451031804000c01030002d11303030140c2450410052200d10950040c0103030219090395400541d038035240400d15000704151006100c00810640b090b03074a510800c6450422486083e00a0303919000c01000081c0414881c3c0c500d2405138002d60075661154011806411340c003040305602d00440c5101c3c07528800d4600d440000d00800350402001c1d00b080c841c002c08070b5502007a4010200b03060340e001e206c003500100309041250000d1030082e0f1104000c1c0000b07400d0b03101e40e134800d541685040f40d0600c072010300000511b0480e01018500030310300021000a40c1600c40c14200302d80025100b5040f0001507018401864110958194682e0303100c0040e441c80310550300503942a50306411134020407064024642c401c55940700e03440c07040300 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 526427742 1250 526426492 526426501
    0x15050f030312070305060a1a04060f0512070509010e031903020f03040e040f022205040201030b041806050c09030d05120915072303011e050f0121090f0308070201060e 73
    0x100c82c0018055408050725100414000d58690910720040d10942070295040c5a80c00741c52840c60b8001d20404002c1803450365811103481c000d01c151401d002a000001d0590759925030111002d5200c00d91090500c130307105904640c1078804000002d10a003641c0322022000e078480c10040d243c00701c0c140d60000b865104000034403045000f038a400340c00075403102540202c0301041c40050000389182040c2038039605e00390b5184081d440c1503007206010324001c0c0c0f0b00f080098503c00c01d101c199150f035484c00da800e100e00c03111180054510b500603a40300811032105800d00829500003801c003c02070441500061000c2401840d08a08040d0a90031200c100000c02a4064811841f0f010110082415040c001262088091414829544841c104100700550703038035a143e0340c100044800d5030b80e29014110110001082c0c40c00c0200110030180016100c0c0303404400c0150700744070b0703c641c40d941244003261a5210b40740010b0b00500401141482615041c0f0b081c600030200a0840c1c0996209030f1021640d2414030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 526428992 1250 526427742 526427767
    0x3140705150a1412040507031e0c120f020909010603170705070e070905030616120c0203091e032b05030408120717090d03061a0f070c030615050f0303 66
    0x2d9001c104141080d18011583c88000b0032a80110102da9002590041c2000100300002c0307448800c0c0c0740700f0000f001d0b19a130314510211805001130303002009605408414800f0082101900040314401c1101814110055000c00d00e804003c1e10808400d030b444d54400c4c020040e4500c10002e80454020000b03080a45544480c1e544403100c0c8540d24400c0144800b14040c00d100d080020007418001c6c4c21110b00d4200a0f030812101010019401e00043d900c0a1205069030035005a85880a172540114180300e074082c100461841d000b05003110114204002c0103c5850602c560404070b031b940601c0c614903001c0c1102062004050402a03070400030304008120006503042e043d1101220138030300060455075050341c10f88261140c100074501c0005000304010001c5400188100310540c41e43e802e1040ca9644c1c03da88007a40b24402851030b000f00d0078080c50a040380303420040d00950f405404c00c940025501d440d028200e480c802800d0448140c2d84406001a003402403400c143c4200c19402035180c449112001d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 526430242 1250 526428992 526428997
    0xe0303090a0b220609090c05070309050112021b01150e09100908090d0f06060906030c1a0415110606090403080604110910030603051924020d060314070515 68
    0x2000a8810003052541505600a0050701d10031030001070b43c1da2403a1141c0010b040028548039458203e802c049218140e40d100c2c90680b51031035030507118811011f081c0f50064850718a0380406001b101e44c02e000f00100d000d0110307185076946a5100000a079002c4008203000324801a0300300300c26495542c028071084040000e01403c1038419030200050945407403600610324403031040071990000203040f990007408041d40c2d0680c0258803960b4100100c40e92a04060141d070360510014200358880b8000300822020450f8807045041580182031505e6120801a441d071201c0a034104001014007016101040c41000307051b030030040c1180e40c03090714030302954000c01a110081ca03a038052500d0307610441803c0c0a903001c1c0c03480c03034200402c100160150aa0001d0080101e84019940da108000321841c00030140c00d03002424a03006002c5420401d194500003225058061200a0340b9600700103598a01175548150130166100c0d54001840c4040c1c081c0d500d140100035040345100c0c1e204c0500b9416599149402c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 526431492 1250 526430242 526430249
    0xc0603061d041a010e070809010c020c06070203150438070c03030902060a120f050105100c1403030a0905060604060803090f06070209250513030b130c03060c0e0303090a 74
    0x724928290b03298540400000e204901c59014105080000b241c04030005409911841c02d542d1002001d980c2d00c5030032801d81e0400105540503030009000030005041050050107202d0001c0c04580000160b5403001882e10804c5809442e180c0300461038280d800c43c01001c50815100fa01d2002c118099141c1d5105044c843c050302c0d100030301400c2a001e004050103034001c0c08002d0380040201e907c0d5001d842c005081e0700c020381040d0088500d08001080020f05901c15a030580350098451b205508045105513030041821034151b88a6129070074405144e42d042008510580304a04041020307401464140e14006003d0a03040c4103030308014003803000c950004192112118119040d4141b000340c200800c490384600b05c0082e4100400790100702d0354080d0645c01c1c01070504055440e40c540d0441d00c2040740e0f00d02500c6071003051032030800010404542ea050929800c01c0d050554031540342d00340e58620a004065500807102c003911020080c0d50b1503000084070040039001d074042c40c41c10003c08005100703011a0300 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 526432742 1250 526431492 526431539
    0x1002011413061407050406030623010e03150103030c021201050601020a0209190e07030203190b01030f03030f020307080609090d021c09150e030d170f0408090406060305040c060306 79
    0x441d800612030560401284400300901080807810700307400c002d0859019004400200341021400199a200c80079034100d02800c05007000e00520814004643e1600c110881035803510401d0100802100080d45190085100340c0b100c43c04042070748144110000c120301038038a1a4509410029282d80100710703a82d00c0340d030403607011900c3d070b40c1c41500b41242c0c072100885920580c07070f18480002000c400104a015a8001c40c1207500e1405840c00c81c0602020681004020404801c010070005441510048041344641800314130002d2070200b4100b02d0f00129203e000103442d4100340212410540c1c0201d4001c9400805091455506500a0340d105107092101c280404d1040d090b03001c3c1071041e541070014010144c5c503401d00d0b24034010b00401448440500c14442e00404601c0c44000b40100b4102400c0d401000500707401f0764400080e0010301000074400d45d103035041004a80d0051fa624401d100240590352000165401d088c1404690800076411080030f241c54103406022010340c0f00002d0794500d1014 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 526433992 1250 526432742 526432771
    0x317092407030f1107120b1b0f07060902090c030406050609010b070f140730021503070c06110414041404120e060d06090b030106150e0105040305060f0610020114 71
    0x1550859082000c0d0f034501c21340f402442d2022a190072041d403c01000c0c0e026100700165a05d0f001d40b100b108000c40250360f40000000c1144170b80301c034420300242c15410300800c030010310580d03543c004c5292650212131603584244000100000c0000d01d1081a401501c15600400e0303541c141303210a440361203000f03000f030a1021024041405c1000c0c1101040c0306040399404e407080f1aa46019109100c8a00c0080001100154003090b41406802c00c0c0300103090b40041c0001008800003001c540281d102510348030810110350751420106000303000b120802620450803a90756403510082403640403024501c42e200d14208440360b070b1040d001650203a04a6001642078101d25544401500c5031100d44600d107801402c00300e01440241110ba02503c201c03001d280d000d000c40c00150003007500b00d50030f03405242e00c8403a4560b0800100d600c900e0b0038050b03030203040c1802031609441e030322490700c0c1a030102c0701c0800f035401010401031700b0700b0040004039161500b40020720034450480300b0a0341c524002004c00c180401035 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 526435242 1250 526433992 526434017
    0x30f0c0b1305010e0703201212031006110607080c09031c110a0f110307030605160906020c0123280e01050f04050d080d020a0c23030d02070c031709240703 68
    0x1d00c540e0300e40780d00028080748c030910290010085032b41c00840304010051300100001030b00320b01602d80400440c0f03100b8090042c950b1200300540b00300304050890f407041c410500161407640c9080010350b41c07a10105088501a40050b14020711a01e80803154002e44c2d0802040c1c000080d41180e040600703203500180801840c5142d2020a1600350150b002915403400d020500074500c1c1c3c500d400c400c1c1d955082e40d0b219100703a06c403482aa52045809102800a80510010861843d4800b0310840d0280740e403409900e0300c42c1143c202031419401c9100e071075542d4003042c24000c009030400036800c03c680d0b003800c285041c96000801d0360364602a07446014040c5002016140802502c0c0c1f0490b4800010b034142152245810200140310600ca0881140c42c0505c40d444044c1e56400190700d2508000e031000110b1500e120b07205058044d40002c00120b5031600d038400b010000a40304442240c80902007404070303403a20010010002c80718500340d00035014500526178601d10400c8002140d071032039010704007480140c15 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 526436492 1250 526435242 526435249
    0xf0b1b0c0622020901061101140106050d05092e0501051f0e0103020d1404020f2d0607050109050f0d050a09030605100e0115110706020a030f0c0b1305010e070320 71
    0xc002500070361140001001141c0940c22101f44420020900020810b0500384140380c54419420b0040d140411804e010344001031042d0303003240e50b102c8040b000703481125a90070125540c88004040c0980502412604c203810b0b404241304081c0104403c582c50881d02e011101c078101040340c102c0c2c0c3c501c100156510080c03020390280e011690042c071040030403c2542c1e40b032038403c0440c1c0c0e0191400c030300c64000103412440303601c0c144100480f44100d01003100e45030140300f8413aa4202c04020b005a41084041c461000412800e01c41c620909001d2405498070400c1800b0380c40c00c0c101000c2210003444402d1201100443d489111103090f02d0b0300a00000701519801005540742c00554082c18503502d040c0d00120340380855100710303903403404141c9504510300082610992030b40301d00d00a00d0f00681c0020300050210384a0b1a01c88528680780c2404609a0402c2c0c0398410320910440f940010410103004280421031309200d20f0b0b0079802c4c007402400c0003608654410400b10340f20040840c04071660021040b00780e4 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 526437742 1250 526436492 526436551
    0x9180a151a041407050705030f040b0408010f0510120317250f1202090310092001050412020904080d0c080105120f0c0405070219061a0d0c050105070f0f0b1b0c06 71
    0x24018520710f0711207074bd4001481c0290b01074000c420712542400e41180220756039000720390003000081d805254441c00d00f012050b011031198800d80401060012a08a180c0001c1c0304a00440d41044171480b4860300c030800c070500c0d01c103d9003d1400c21502a42500410350700200104601914040c0580e9901c480b100207454014904a10345600e450180f4170801c00046580049152481a880f40728820180d8015600b034041c510800c00c9021f48600c40703000529100c1080d44d4002c0c4180e030780e0b50070040405102c0003250140c40c100008607112400611a9190020740714441050440042000e03154048410f5103d5056021550203907407180c2c0450501c1c1d0080c400c4500c054800c0b0b0814080c02460f003480c0000d0b100100f01d501a0103d5541c058800d1300b4214200c24040340c0041e40c5d0802503241000440790350380251002c0c2c40103c1d41c103180e0400540d601c50380044d054066800034019007000030700c81d00002160f40110304030320f00820070314210040205d443c5030710501c40c41140b003864071a8598a03c120 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 526438848 1106 526437742 526437757
    0x40f12032c07170a060b0d0f0606062019080904140609070f05030c0d021303110f0909190804030b070216050a0509180a151a04140705070503 62
    0x284e034a810006c400d600251494540c41e5541d10303042c00c03908010b40210391454590004010440d48400349420300020b04000010100000710707400da0b00c0314804074101c481241e6104800902c0940c105a078074108001c2e105008214142d00b00100580701100c246200d0003030034000c500b032240300d00010013041043d030316100d01d141c40e4902058010307088040c0004030641c0810404911502d07017040c40005600c2040c0c84010284c00b80200280311b42002c0d0885e0041c3d550100308001a0000540b144502c154011000029072890402a2039031180c1e810141c0012601c2e81486810b43e80010300c101c030651415001c0780010746070380401031000098410a54031403459004141d162040c0340614201c05802c2d0100d4642c4401a540c6544a207191901c0040499899540aa0380803c81c4407a04805100315010070041d14500390030f85c3c040fa0050010004c00202141240c10800104100e41c483c = true := by decide +kernel

theorem cover : BRFrame.Cov 526258992 526438848 := by
  have h0 := BRFrame.cov_init 526258992
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526258992 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 526258992 ≤ n) (h2 : n < 526438848) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
