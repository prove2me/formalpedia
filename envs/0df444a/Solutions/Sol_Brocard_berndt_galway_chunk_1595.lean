-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1595
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:46:10.228645+00:00
-- url     : https://prove2.me/submissions/1a697d6f-631e-4d0f-a7cf-03ebf73ab862

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 286690647 ≤ n < 286870503 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 286691897 1250 286690647 286690661
    0x7080f19021b0607050a090602070f0e180a0503030105010e01090810050624120105040b130c0c06180302120f04090f061203090e13150f0e0601031b0b040e0406 70
    0x400c104034034958040e0b505810094200e40c0c0d030000480000d2000c0d0342540140f444005400d07035200600c9481d060402d2240101694018444215201000600c0403800c05100b20361110481c030651300590307007515056940303400030b0040314042110310701740039407951080003040221840d0714010710703084820200307242c014940545165000100700c01d12104542c002045001222000740095039104501c81c9011483e40068210070302c01e508040c26021aa60b035410800e81e1110441000114004c142e00c0942d00030400391002441c150a112090109a404182180388a4000d40030749802d030702d1645201205204004c6550460f45041c40b00b800385541583c080011001a03100c00244661a50003414203105805012000030702c02607010300110980c45e01c21600024114101040c0102960b00c0014003000d61562a800c03e54580760400d49500540045c004a000c05050725141d503100e00386030704e10b04211030404456181031080020840ea241044800300d1300c0308120a440c5460f2503131200090300e44 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 286693147 1250 286691897 286691917
    0x4110706090c05030607050309060a020304051506190314010605030a050a0b07052107094b030804140d0b041112010213090e01061412010609021207080f1902 69
    0x941d14010070f05450810000340200d40719155607841e460898040c1d031501c2d00042c813192030140140305010000700300041840001d841c1c2201d01d20760380e544401080c140c601200380c01038000b21421000040c4485246c40c808060356402c000e102554032803003030640d11603d07400001d2150f84250a646c020401e110071184d00702c24641b074030714035000c0e42c048001c12103d4040e03841d2901c550144240304225400c10111002411844549244044017814801b4007050130380c036802071006410501c800c08480c0684d84070228203c4010703018196124103007102d440c1c005010386441071029509265032440c0c81011030000e15880440088143c1e101e5480d0b0500036000348007540c0120210941d03882451081c005099002028060030801c141342254410503104c4d080d0081d5000e03450000b00780300e0400708400080e40c1354400d0b02c845988090a900300c600410640d40308101d90b40c030108035503a00c46a1001d00c580140a2035507441525180c411042090700400da402d0324091041440350318001049402030000c0080c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 286694397 1250 286693147 286693163
    0xf07140f011509140f150604050a060206010620031b0c09011e06081501050903031603030518030a020a06050601121806050903030112022b030c050c0411070609 70
    0xa4140c080c20341e01c91801804444070154010b02030140ca40c03141a00c6406028408042c5040001700d082c0d6036180500550071480040201c4144c130340340c03402102c000300009480751038202ea42c0c1200a440e51400c0c000d01002030640003100341d03069103208600c0e0040719000065417401c1e0604011008110120440369454010440910076030340e00c030081c4078000c0200c1c0007c7c2c01e403e12821114540c504068101c201841205010b21910100d6441240c240100a0a00564809100c0e002900d18042c45202078141c0803074480c0c0e082010790640066000b06203c09418449658070000c10352280504182000141e00c001c040d8004510a50400340c1c010c1d10604006407116100340200c816a08401c0000d82c02e514054121410132102d445035503404040d00024604550400610040c40002044003a100300c042c00c5029000e0f0522035461164030080c01c0b17400580c180a40340c003505610aa071400d4900e0300034250341c3d0340070342458000c00751b0780040041418580401a41e4a00c000c0000c0d81003651491 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 286695647 1250 286694397 286694413
    0x50a020d0e010e04090f03090503010e07150504150f0e040903080f0703062102100c0201080c340c090c09290f030f0105040c0509040f0e030d0b040e030f0714 69
    0x5140c0d44284002c5c0c6000c4c4e41c1902120719a410b0140403000d82e41d0015000fa0302d4045009a444400329900068980702954444c544500c040112141c1c000d54002c22403854958554800c43d940000503040c142c4810780740c00d000400ba5200b000225070080c24080c011503d0000059035a071200e040659110b0f8040c140001d08545070b0540310018100702c0d5500302da24800c1101803096190400100d41c5400052a1044815056500082038204d014020703031001c020200e0b4000340051410140174002ca5040c3c140381e9807011002d0b502d05000c0403400300352030105e18124081507540550040000030340990300c41c1009240b8100b159407090240c03c020a54140285102d41414983c2500802c074035452200c40903200e08108070802e0015506030300017445545081c0c41100c149070408143c6000ca50704a500203442c15101800b0340c05418010080d450b64040000e003061042c826512044181d00d041d03a08200c3e01e408146919580c0c4101400c41540807424044600050308000308940100c007400140c0d000c113 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 286696897 1250 286695647 286695649
    0x1209050d020705010311030108030910050c0a1a10060f05090604030b010e01030b0121030e0105130605040f0801060b0405150c030d05061804020d020f122b050a020d0e010e 75
    0x215050203805401a0800c2c0e10400807582d2502400c401d1119071010646954540200103a0313034415114250302804808170302012142c01482038590000c0480c069503541489882d003141c0c0f110080c0741a0f400040090b010034075910402451000390380558403610041180044161080e40021038002d0b4000c1081001100107102074032417600905e0907146481880d411841c05c2800f240c1c1c16040308804a1510303004c42500d42130079216112060709410201148400c100040b920340c403e84040c0145050b2051000850700e52003001081194686400e006c202c0c0c0c5c90300301482c01e882d010300c241e80c0d52130001d02040c41146800304021000340c0080c030078540381581c11880c0a00355044020b110310440d903560b040040c0390809a0022400b03519002c240502413400c0e030300260082c0101a0080d000e64041d40840c1d805d600e400d4a8620b41c1c4024208a640855080030751b202e101809004034a007000140d080004150700603800d8840c1d40c3d006802501e280303a182c40e012611030030070000c0e00c0d0400c20000c036a0305403 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 286698147 1250 286696897 286696903
    0x14010807080919080307030b1203070b0a0204031202070e06240c03070b0702010504120e01171008070e09070e190c090506031906051c0807020f03191e030c03120905 72
    0x24070313445250400d842c1d14089501078100c9039200004c9015200060911346008000b0003200c14441d4004100c60b010b0b1154541a4001e010f960001041c0b400007031005a140b9400041d21001c803031314080c00c0c0d4481e66030041480110710444480803da080509800f0358020320b110081d0500c1099481201e0a140b03041c0c44078084110241d6444015035500c074180402d00c0b02516180c4203a078600e0420711b16203003010000819000141c0760010304021800c010174003840d80c08059200600450003150078641d100c0c601c1180f281400d84505c8040e216a0400145003e000b81806100d041c45001c643e80101d030b090392840140100405030300802c6480400800c040da104000740d80112100d41208502043d488254002ca500300c1d0002c41c03140c10f004c0c08881041c4401407000f210107901085030f5844141d1440811125004030034401e074180142c80c420310014032045030000c40d49005468442107512568040c140c040c07800c01e0043c000034400024500424080d503149418030f0f4002c1c0d000a802c070401d444041c2 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 286699397 1250 286698147 286698193
    0x51c0f0c24051315030605041b11010b09010315020c010626070807090903020a050304060e090c1801110a05072d080307020d0f06021210140108070809 66
    0x70854a030401e204948280d00c46400c510700a507410898984560400f034500e60441c188580c041c01d100741d403030300504513109410000082074042c2040c04410039140c4985500310710300804100013404007182c80e0240a0501810240c0310010300031064076425a03c0d100b14080404452041ca2a002c10048100c10401d128100040030f10200d4584903071a0080160b96886180c2c01c40b039036552240d42c081c0075810006c188001210030010002945000501d4141e003050b44820020301203010220340000d0321030300810388011440c4100d95184a40e600c03010010498000c034051005e21490390044c04400c0c3d4043d40076410303843d07182c074220b03000d222690b960342d4580310054200d8060174642a400c1d1180b0a650025103c0d08100307124100703200341c2040c4500383d80380180d22000e403041407444903170703c20b0220500280c818240c01c6141036646445034201c500300c0030415150140c06e9502104009000861621144491801650741812540340d20300d007111310003c081d00252590150b00e2005580b0442410710385 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 286700647 1250 286699397 286699409
    0xb0609040816030207180911060307030e010609060f05100203041e090e0f1006030302100f140106030209030d03020a0e15160f1e050d0f02071701050a05070306051c0f0c 74
    0x20400c0c10000a4401c8265070f4041100303647c10603440300001401145c00c3d01015030140c905d0340c0c4994510a088020300014110a2819481c1c00c0d000300d5a500990019015134865000884180340c3c2c5034288034030542440428001070300280700600c005c1c00501082c1c0e100e048881c0c010700d1040e407a0410170003115000010044079074441108505602d006101c89841e034001e00600304000e6107907480c040d480c5e2980705070140005039a60031007074500c24660b0001d2030300c0d041011007896944e11008050020761044890361700c00e10482400d900614413a0081b00e051802540e15078610090040c1805143c00e2ba145188243d15014020240110b0400700e5010840d0700400c121000342c256401c0840c803a800440412000300f0311090b18030b01040c00043c42d5030300c130324041c508a014040180301c100d04055843e00440120780301200d40d40d44404054020070b00580010204201c1c41d151040151b0031594148210398210f0f9083d0138098503a80760b02d17014a80305005c0d020481408005994404032000640c0100c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 286701897 1250 286700647 286700653
    0x901081501080102090d0213061502070608100515090d05030a3504080a020a020306070c1406061507030e04020708031006031a09041b150f0c0b06090408160302 70
    0x455840620310850a004102c840002c610f04214200030130344070079000070083d00810098003c403c0701304560340a80c0c0280100030582c90708000051000f900c0d41d84920400000542480200c1d2482401141c0e800440d94024a11080000c600c0480c88641d0400003285138040c050001e2100412000d00c01400d0f007402c1d0369901002940114554203c1c4001c070780380d804031601000030804440c885111405d82040c2c00050494035103c262008034644101258000d402d03006078014002d0182c1c00c000300342da41c030b40720310444d815149180d0074440d520641140c405502100301001810041076400003405058020710340b94400b8514280803505980c0103180071181623034000100000301c500140c0e000301904040c82c05009441c03028207403c805139140c5403014400c0300f40201090130800030880084243c01e1460b00220110b98074a184424001c0c0503004001280030b0b03851011000e441640300070742d0264880c0c6c640036507884a20030f0084ad060000c00c200d5080768100002907000d8107040c2c610310018825402 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 286703147 1250 286701897 286701913
    0x9260d0201050912090306010614040f06021005010608060109030b07020c12030d11070c090c0e030607080402030706170a050901330906120204050417070b011d012301050405090108 79
    0x80303030304d070100345404c40c0e0080c8400d0012100750b56020a07128112400b920342020b01c0d06140107021940c0c451944a01541d1080e0740002400d1074001c1100082c0c44042881004540c3e65044241c910200031141c80707000a80c08002032001511400c407041e08004140304072034100000d000402e45249070810750300c4859001249203001b064850081451404180c8000c030b04081c400d69403403003a42414002c110038251200c0c0041e80b414804c148a900450008048800701d00740080c000c4e2030100e068500381c4c06030103135810100e41107020350039101c1c14a4032294422025603607407040c43c2c02070078041d10010f071a540b03c0d01455404c4903d10350480a8142e2409600705c800e40c82e8031180045546a8801140c00b81003d108000c80e2103104040a03600350184c0300401c0580e6180f41149001c050441d129540c4800030030f1744400d00c10f0485505040c1c1c0d4194514451480765003220780d8002d4000d03c941628a030b0f90717810500300c211107426501c1c80140c0c103041007401c150f00d0741c2c00180794040903004071005600c4585 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 286704397 1250 286703147 286703161
    0xd030302160807120906090b09030c10080a0b0307050d11030705060406080106030605010c080d020a1713060e1605011407020607060b010806010c20120d0c0311060709260d020105 78
    0x105400070541403002190346401b4000d05190b8980c45550841c0c0340101e040f07161501d090210b0485014000c0c04642d80740130344000501812030594403128aa031415541201d181000988141074580c0102000e0441c0b595075a00b05400800d40310943c0c050062080008003a242d240141000c1d0007a1f88585116604042c0010b0807144a54881c50401c071000c0e100314041008002260891054040096580d040d102001d03240f0010750213071030054100060070046051680c60000101510907401409602c0c50380c9686507036030101c03860124004400d0002084030758040c10310440d00b8169040840d040c421240c0001d41a0b4000c40c000b503400d00e49030005207040e5030703211554503404202400c01c102e030070007503403a900c0c4880010540f0000d68940300850040c155503001601800c0140c0700d01701c514841c4041c4000b0191552400218040b82d5a42c110114a86001c210b040c0318001c6940c403929010f1a00c0560001d05a100c0324203c42d000b06411800f0503945e0a101c1e030702d011501e075000071800d030510751 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 286705647 1250 286704397 286704413
    0x7060506011106060a171c02101a0604290304031206080613080904180809090612030a1b1407050907050a020613030e13060f0506030103110d030302160807 68
    0x8600940b5541082c07040102c1036640800d035034150358110300c541d240291003903021890008102c06640c004800d18074580300c029400120b03030029185d4400184109080c2c481c098030001e00100c28194010418007007403101c2c0c45546000070181034100c1004c00500d48010540ca51980250342c2600020300d60928a045801c0740c2c02910010b2000a000f841e0f6880c00043d0b109818110700c0700200f42c0040059600d0940da1141c008248520003602c80e0701c0040147d150403c0594403000b000b43c043c0c9802c900090191401101410100c0c03d020051440d10038a45011200d036403500c2d107003600200803c8140000f0a188176400901c00c82024000c02c10b46041c45c080020004004110004205003001080d1181c0e60120b00d15400020501008040100034a0240d034004a4086115084600356410004c501c0c403a4100c50111a0f01c4004004059110024040944000d0201a160700e9804001d5402da041c40c581240c0740b603002e441d00606100e04201e81401e06400c1800c180d902c1c0070b010038080203201800b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 286706897 1250 286705647 286705667
    0x90b0d0e030f0f0705150708070309140709060f05010302090d060c05131827110a0302310b010c0b0a0605040f0e0f0d0905011101141003060e010504110f150706050601 73
    0x8a0340599507d0002e100401e621801070483c81010b44920a4008205c2200e030703c045521429001c0d104c5040d2174440314002003100e44100002444e00f0140000e25500a1080ba030b062803016204000c00d038843c3d12140080d03c0c07410110341c20840100a107440c824682072602002d080f404080b00d403039003401e51245064800058190308005140340ba090201c440541110700281d80c4950321018042008000507030026a660020303420000f40d80080c90f08152426180846800320388007034270f4550411050300100c0d807003003c0b810701055007501e0103000b241054140903400b100c1910045410b40c2c603440858141d41e10340004e502d1880e2241c5458859070000d0124044100b081030040601007020640200207041c40d00c116814000c04801d400c0c00340700b0a41000c00407401c3e0100c04465410152845000a0018072083d10030b60320382080c000110340e06002e80b034056034200c0c44451049514008210a111242c010700d5804090b4421400349000088040c0c0304541c01124009800e01d032030400903041c0846 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 286708147 1250 286706897 286706923
    0x31302130b0112090606080f071a0a0f030209040b0409080d0609090c0302060c030d06030f1101020d02121803070e0601030506060a09060503040204020403200a06090b0d0e030f0f0705 80
    0x10300404400300c0e40d1043c4244020008842e01040c103031040d0912900409054024680ca8000c8548003015180c000070548111800000010021550086020498003d482159000500300c0c80d000004502c0307a00500704e006030007800020b84c1c03a43c8100142c100e80c3c0d0708030304886200c00402c0d807480314002445050300520a15006014805480d0740d103294913005800020321030702000c1a20040c00004005983c3c049040100c1000520f803681410320200480307007003c6850b918117a21210180d44003141182c8040c135150001c080c1000e18104080d0030303030009461034a80c15038010819031961b8042092a0003055102e001c1c0b00c01d810008001002d56034000e0616000322001c100402038242d00100b0f000c101c82281c54419140d0f2220310014020f480b640c0c1c0040c01d1196031203070007229000c0858907a1441ca000b101e00301c0130703d0f9440d20150346e079402c2c9101d81aa400c8043c4400784918084e9003041928504a1040ea440c1c0880f0004050158100e01c0642da101800841e41f50300b00042040300c1c40020740 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 286709397 1250 286708147 286708151
    0x1b18060f1413050a0b090a050103290111011122030206220e0c0c0d030b031e0a05030c070602120306210f06151e010503070c150203130213 61
    0xc280140500708940450800107078030700009502d1407844505a500c00648001000070600319501c00c02400190091209280309216048000920703601a114440003076a00544071713040044103103001c1541111400d01c3c103040c030280000c1c299040c0d90a05c01c0c9640318406001c119110f00c50010018601c00240c00d40c0e00d544a5940d4040c805072741d516068a003200984d49500310710751448101c1d04212640d9900003030202114105004ca140703e5003018041040301b02003220a149400d00c821015140c500b2640d03501740c0c200540b1005130b4880710565101212849007110414401d580e0341074074580c05101112600e41081d01c007482075a505104110800a80e1400641182031140004039101840c1c02c1010403103180400d0701e03001a0307060041d9039440c40ca00c0251562494024031075004140c1010302036100788015101c0c1c200200301e80f0b150700c0d00014107942c2c003030450b0341c3d603e8240e6000301300e410b007560411120039601c00d8401d25400107512640d50004002d101c60030500c1072115054190b15000c0900b8 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 286710647 1250 286709397 286709417
    0x222150302061207050f070309290307030b060909090114070804050312041b030303020310120b06010507050a0b04081b010b030a02040b0402090d11030c22020d1b1806 73
    0x10756441c1c01c1d107194114800303e04505468101e0140c80e2072182582c401c83c1d245e00400c015040c95000114081140c00d03190b01500d00c408101c0983c8900c0600e00c0c0c0c030394010642440803504d25440b075400300500c0b80c00504024641000c0c030000032112030b004c850410480c0c0d103c0b0140c41e090041c20419a4104a00d410401e40c641410f41c2c1d042d4407801420795141e550800c0340c0000301808400d0342401036040760f042401c558140c0b20706004010b50710896229082030b080402c0010001c800046040003190800e140808548071403004403510b6100303d2098542d84145c02c030010100d41101b036000e000d1031107940c0c180e564140510141c4000c4000560036016649050001c00c0c190701c0c00b040402d1003e904480010b5031a0150001400034010400c0c1690010035500c1c01d10204255181c0a018030303403007101203680c0c0f00700b202d04000010000e01c00740e00c140118060806243c1c2420780107803515800c07000d00401c0c245240300700c03030340046030480304903001440d442d0340e6040544460300380ca0003600403458204120 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 286711897 1250 286710647 286710649
    0x5010e010c0c0e07090312030c020111090a1203050f04140f0d021c1b0b03090c040b0d0321020d0b21070b03220302030d0e0105010509040f050a0222150302 68
    0x1c840e261143c0303000c9000b030900007041c00740300d40c8140c800b455224034040c0a80c1c0d40a81c00030028950030100802541c601031807000d0f505054819245020300081c011008035080284030700c0400c1c0c0f28001101401405d104c00c7c1c0010038010040c0025002040c54004c0800c0808200502c064618004d180188030180d45c07079015031205100101c46e20103601c80d42c18281d00070b1030041c2e242040d0071035035113070b10f210142d0104070410300300010350050350031008030fa9207030030103070b0401040303c0b036142c03009604c5441c0b4011080040d02600320502d09064a1103d10207003100181000142d030700020010440d0350703443d1400301040c0381000c8102561811180403607107949030740001e6a03440301c04d8050910314a0000c0002010342002a21880807144000000520404a880d001c5e5894200071500d100a60038141d844007081c605100310b5040f02c000501111460701e446c1c440c07003608011141c09903000e00403c9000710160711120010307800070090030082010340d408005a002150322a07440210b5043c9850030030005 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 286713147 1250 286711897 286711913
    0x50f1203010b090628090305060105060c06070c030c0c0b040617010f120f1403030f010902250303140c1803060408030a18170406080901290301060e0a050105010e010c 73
    0x901c4000e80e102a580c01c02c000906900f8980d0f1010508071200d12000c0f985c0ea140d1248062003101e10a504481803640c0306e000b004100d010341091100d25070301c00000500d0b50f03803041a65140781c0c1d001c0e0500046080081d06e801d0074080694006030880000014100009036001c01d1198056000c10812452941040c240880ca68a00e00c15500c815486003004000e10803543c038a4001c60707a0003150f140c40841952155501d175041114414009011040000340351250b81c02112040c0031001c026500c120f0200b103a11400018000c0164205030740e4400c40d0710140c5a8903a440d000d00014140c95440d4a252004058043c2c02e035851303540240c2200090000003903040060780d81084501c2c030b01003445009000285210300070303090090708000c18400142664400b040041007501c409980e451515654200c009081c1c54030700b221000804644905c038060104018141a6008001000414a02d80d1100c046440240075034240099503528001049a503810850b40030005a0030300340482c0d003605603254916 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 286714397 1250 286713147 286713157
    0xb0f06011b0c0501182301110a1205030a1d0f0f071223060103110a090b031509070906090e0f01051308280309050f0f03071104060b0403050f1203010b 66
    0x7041c4804117418054440ea2410303180040c0103108884200c5c0d144428000c0b5405203000c5816011680250310010b9010010941503c015007100881c00d80c0c10b08110308032140d42c0b00500b5125001d9840c0901d801c4910250748807104000860020400a01c00d1005e44c1c0c00c1c15503103207110803a98041c1c4c004006804002c00002600764024108807007010800d155401c00000c044280000c50143c000084200000c40c50f8202d05e403c03066843c10002070f202ca0144085590f503040069059002c41d4000d01c202051380c1000e50f100c03441000781c1341000d9039403c04605845540c1c00c0740c5400303500d4200c2d4100450007000910341490a40e00244100e0034001d00c5c0c00410f45006501600b0480006440b04501d503801366041c0c0e0035108461605000c11460700b00800400c03100c9001c4419000e50300d1030990421000850007220303410840554036244040e41d490031000e02d02c065854001e62982000500c00c41040082d100035802507000d041c03502d02440a40c0d080007040580c02c016000244010f100c01864103050310 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 286715647 1250 286714397 286714399
    0x11e020415050f04171501080a0308012303061302030f0102191202130605070b1501020d2f010e10060b041701020d0f022505030904180b0f06011b0c05 66
    0x2d43c1c1ca541c54010300f003543c482e50300207240496041640384c0c04890b0002d85000106032100d1007400070f903240c01c6610f8a03840c44440c082c00040340c0200500203005080d0150128813880031352042c4c0e154a0402081c1400e00441d5001c80b081d500144010950034188440070000c0a440001c602d010700c40e0110282c50700150300444100030040c000504803851550440d9070100500c0151620560344240062841d0300075030040300c00642c50340100b0180c02c541c011101811070160080e00d60a45c1403c4220368150548849400901c1e180d025444541010482080d41b00b1095002007004609a07440904d041807a401590701246800001c200480c1d070081554140d6848070308030b500e4a04034a04460190046030b044070340d038a240c00d0401400213442d5004107000050208042c04621241d55413a03001a0f032214041d10980041280714060718103940100f18030894a401c0034074545c000e44a017041d03a20221800315015840800703200342c0b9a00301d003e5083c01d045a84000200005d030340c0d1980c1c41640907119003 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 286716897 1250 286715647 286715657
    0x141e0402010c0c150e01020307020a0504110409140709060f120218090a0f0c0507033509151b0711010e060c03040e070e090106052109011e020415 64
    0x81411a0702c00c500104a20350814a0350750400c0c0c8844d1184198840c50400300c1c0801e1102c619205554000f00960f00002e4004201d105068a090140300207001e82078200810341c441000081100001803003841a81415804000042d19080c04090001c006036000328040c0a00e080101c2d10280e4010510024400300440142c0c486107984003800784000c0c450502c0354001142400c10101c5140d60780700038403480e4032103818401c01d00c2200003501d03030344500c480c090006280529400e4491417100044800c11540f210843c003c21810300d10003042600c107481000c03d5030450501c3c10f10754001c80c0f0209401112030102c04a41c4020b4203103040c154840d41e03030020306080b440e00c000c2c20668018000c1550740e01000e05500d80d950400d901c1680c407588540581c009030400980882e00b442d04c01c03000c1d00c0981da00507104070101d0b42001801c0d102500071040884400d060541400072100c654030405001e5184440003280302c820a100312049a03012600046410344107000410051000982d810f21038000e034108 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 286718147 1250 286716897 286716901
    0x9020105072001030c140703050f090a030c0e01050406050d3309031209021507050118080c060717010611030706050c03060109080304080d1b02090703020a0201141e 72
    0x40c0d50900482202074403281c151031031089200344400b160030910340241c0c0c0401c4045c1448406540c0025510042d1001d41400c2c402540000e019600030300d08850212803c0781484a8180086d120303a04540045482500036030701001181240d18003540035160032141804001d0400c404a10707220001803000c0c00d00c6035885c1c2100c1c40701d002c90190401e8000e030111040e6003c035296910f1400b411081100b00c001a980e184c501401d05003520603020383d02e500611000b40c0d060302c80c1000426400c646000d5846560301c0a0990300b21810030750b401ea16910609016032940d110b03258446c10014000c04c18401d2003080e80d0760221101f06225003505596a605150010400d0710b00c03844d103140501f09000f0030a42c0b4120500841c3c1c0303040406188101005d985052404c0d468425687d100e002d2482a01c441d030b884503400c0209640a1040319076042e0313141070001401c01403500052540b034000d84140b00441d034000703643d600c543c0d0b082c00340e2400c3c0d034600c0644403080d04181c41400f040c01c40da214100f440b0022040 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 286719397 1250 286718147 286718149
    0x140409080c0115120b0606030c070f20010305010b12270a0b0603011e020c01020705030f04080d05072f042f07050c1c051c0825030c090b0406090509090604050604060902 74
    0x42a900030a1300400d0000b6124000c3c134185051058100033000451807400c844402507200c0d01880d41a1004c3d0311002d400c00e891624000743c4420054030410724280d00508454040c12088942d101c070504d80c000402c1d10307030074070305240005440c0030300f81038020390411200306a40e080203010110385e000020700060b9a4542e10190500901031036100034800d000000e154510582c0d020090410782d2148010350b03a8000120f94180d401d4818000e0040804881202801c0c0a46c1705c400c10310001c1081503e004084141000040e0031105103502d101d8030350001e041e050008019541d91016440b09015855142051a45529075038004550707030769100f06000c0b56030b038840045101d1052642544201101e2002c07402c2c0628480e014140c0707a64a0000e466000024080282e034125028000007602000d0502d403041003040b405091801c00c10700520503240b000107002d40e0010004e00060049640d007604190a1008204613954060031440350f580c8031030140300c0440c1d000310341103130450303030125000039940c8281c8 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 286720647 1250 286719397 286719421
    0x5030604111314090705030a150b04090c060305041205040b0f030c0412051f0504021f021608011d0c030606100306030204060b04090f060807140409080c0115120b060603 74
    0x201d45a1060750078880c80f08100308452074000d01440c1981e0030b076407496490b00145031340c4060303e00000e090498070580e43d16070920240d02081c000c18001c1c001003109281502c031400c2d00c40d2030354402d030002603840c0104800e1003001e5030b1203030000101c1e250103840c00b460101c2e58240b5000c1d1038000503007900f001000c1303140d9100e07840403100100004c442c0851601c8060408075100c0510780e00c40494006000500040e00c40d0074072440d80b09550013051118038000011085181c5104144a40c040d480745c0f01c40c000d810410031110100503c4600c0010514885074009080101c0c40d003058061b503036100002040095502080507980290151402c02001441c0315042b00940344550010790824500100428942090030090007902c402440a0203034038000310800b8203c4401e440f035101c5980180d0710034005040000941340c0c220400a00116081c01c0e1901c3d20000340e40701c8524045030340c4d912098818050b4140b80b10720001c180c64040c1050803c0a40c0719500c0b4124010412841040c1c000005a040b0030a0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 286721897 1250 286720647 286720669
    0x7050f130f0603022101180b0102030d050f07020d020f06040611190503071b12030203311a09070605030a06090203070c110402040f09020a050c0a0309050a0902040503060411 76
    0x101c070350365085950b03645000d00258819040052122080d144140c502054130f10024121601540700400702901c200060008012155100c0c0c11800204000103040e46140181c50040110154400240c01c0c4860041c4c603008403002600c056401011b0703007100d00400441e05a501980200f00810302c0d0f80030310903400640c40340030000b05111302d24190036002d032584180503520901403074880f0801c07000b032010802c400380c206903402406800c010250700c13410b40c443c2d000b66070001010b0700344a01188104032102010b880c0c01c2124560092072108030803d2000314100301000a0034417403440070a092522010352540d90701d0040106005001000c11600c468661240000385901d880071902c1e414450402412201503000580f601154a0503d98a500c3c0510032201100c20303282a600c003462808440740042d4011031081400d0041c02d001c0d801c80b2010034402c000700244130365600680d03181410208980700e01140c0248803002d00c14801888940c40001e04140c0154200301d020700c0300008038002071840010 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 286723147 1250 286721897 286721909
    0x1090b070b01030c0509161107180905120309031603141207030506100207030f060b032e200d06260106080c0f0123030c09090f07050f13 60
    0x200044403401e01c101c1d110000c1c180d911500520f10301d19030f207804203c1d02e41e1080d610040780030101303156058024040d503005050703940c42ca01a501504d9030b4004140884a0301c000310080342d600c86040c0030810505112600035031402904180c2076003071414000f951b0340501d030031402801c0640c01161003414050312042d6407680b8505a219620034811948580144060301c0c0d0201003410300b4040b07609450b003c5105030b81000164000c084031342c5140ca40108a000340300e004d03140c0075910510000c003600e0510951a800081d0024003111003090b068111780401902a081811032500780188100700342d000312001400b0004224944645440308080024441680000326580e203d0311a0b00e9a11a10205400d00b610f0f460b00801515640d00300c4951680500c200c0b51303500010501680d01b00f50f0043c402030600700d50140d018498002c1d4240603260980c42503400b200200c5011800103c289000e445869102602c1c0341c1400250070400380280c814080c01c01592424240450090141c02c17050820000804d1703 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 286724397 1250 286723147 286723169
    0xc2304020318010c020601060f1b020d06021e1c020a1e030c020c010314010e0c070605010f21020d02090c13030c06030e120412060209040f051807140d020109 69
    0x200303440141102c1c90703044041100d55080401d00d81e0032500124590341215203130307100c05111a9001c5401c984070088840c508103900d202101e081c0140e124480e41e42c4132184240d0300180c6d102001960450094500c0c1d03105562120200a00321003540065907012000b0f54403c40940c8072003a0780b8056a2226440d101240c005084081c000c14880d0300d40c200000c17802c03454023070760200d111103001102036034401c0070b10000c00c44401c401004142070030801070754410b02c0e5824113400c1240f156503020640d41c080e40084e4211843e4001800030030320040250044100102c201454801c50350b011aa00840c04800a0701c1900614002020701840a080300e0310305c0810480c2c0c640e110b03101d00d054040c1d08410700a00e00024035029107142104000104010f5864801c14411700341407508100714060b1500140450701d40d1b030203220712607154a543c013a51401e408407100100c0c9501e0315070300f0301e104e8000750a0512281e900900701040b0540e0020044800000d041d41e010340140d4090005076000005580110701901c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 286725647 1250 286724397 286724401
    0x50604030c0e280f20070b071103070605090c010507030210151706011d0f130f0b070527010509010503060d05060f0403020f0111040b0703030e01020a02010b040510030c23040203 78
    0xa0210f61110302c000151407401c0141861506842a005d40070007024168880704000510102e4000d0154a80c440d0003842c00b4040c030802d9103400b50664000f00002c1300d94944500c1440000760b0117000440940400707280040c1442c00303640b402035a40080c408408542030351148403403c030072006885980908050060022070fa0908a6507954440d400d1261220803402180e540d0184a03175110864000c2034201c640440640342d119105100d203041c024101c40740e0b1000d01812002914507888240f0602c0180c445c82d8a402d102c1140c803410320401c2e000c100400b042d031007100d501e6a800038140d0b020601c080c0f904544035625072000c110300740d0030f00c40c02508503c80d8008000d60f48480a803803034890341c807070750031b807441e0040005000b0309032028020000e414160a0005001900c804405170031441d02034680880e607035125800560172079100b5510781c0b0050751140e2003030801e03040c1401061340100742031540d407581d136207107403030351001100e407401503159a95641000003113040c42e020a026003144024401c66680c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 286726897 1250 286725647 286725721
    0x504030311121c0b04060b07140109020d03030603030e0103050f19060314031c05060a03060b04150f1d060d06090201091d060f0d03020d081b0403080d0501050604030c0e 74
    0x43c9800805500400e050118019040c1402d0040c80112403800f460701d41422100d03900c2c1d00040882040251722036503211200303805070313403890446020340d40643c500207016406d41c140107140e81c3da1030708100d050500b050b00744a1003040c42c100a075803003070340003108400040300f4100540103440181e00150080c035069924040e024008001000003000311641c440100321142000c4d025584216040f079445460400c042011070800e0700003192a1400800014601c095135000d803035000c0081e0061588041a40c1c010311200d4400d030304801b150f64603900f80b008a072401c10001640d03681c409500400451712003d1203021640120010005402401202c01031400302d4515100d400b80102c2c0c0051007001112440d850f43e0400c03850302d8108580650103000c0c184240304003610f2040000d0b210031110070402c1121808885100d02801c06180f269501c9a9550a07005101d01541c1c0c4c1038201510818041000b000043c0c00c50325400c0448846103010b0002c0c0e9a82c1151101900c11034800501c02c1100072510081 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 286728147 1250 286726897 286726927
    0x17130212060109060510050702061804020a09052713020114040602060702070b09010503060d140304030501020304060b041b0f0302120c070203010524040b0a050d05061e07050403031112 81
    0x140d440c0a80c04111309a81c3e0404c1010640d608107200e40804c204101e5900541414001031020500d400d0400140c9510800802e040703a028401c01d41c00110f031044184030f04e103089640c0302280640a0310076002d030645542e20060030040940707403000f600701d176940300300869000d110524000e0036428440e0751944d54401c400383d264a41217490b000140981c1102007010480754058801418041c6d60300350460742c1d1748081c08003148041d2030a171003030b541d0040159440c000400050016502c15000945c1f2400c00d0f01e05501503070240d0726418441c6050018041880ac007110b44614008210b103054500c01030254011340c024801d03e9901000018043d080040d00324421004098040c1300f68020807090395610a1011070750b032281002c00c400d402da410143e136640303800d40040c0000800201004070040d5124005941c500c5012001c0384c0d00c0d0482c01c20400012a0426047c0440254101901c254601194010034900c9680002414482d200d1486108224100300207050049184015030baa50002c1e100c48032 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 286729397 1250 286728147 286728149
    0x2031903080411010c030906030902041407021f05060d0f03110d0809060a0509030d020a1803140f030a0e040203041b0303120e0106050d0212030d0501030605060a050f01171302120601 80
    0x107207a030200004400321354800c005121030a50980e40c3c03d00d10504050b411400b41c0f04200d03007668480e481d01c031a00c000e680440b461a01540c4150001d149040d1a1a0004e20403a400c407ca5402d00385070504014858451032001c42c07045a206152024280322840c042d2100c040d10780200c0f0f000d2003a01d40c007a1096422a020a01420398803088500a59980259206860003141d941c40380e9003040c008a4080d504a8018000104503800d0007080740da0200034014004034294001c0c0c40e2440004481484c414043c030008014440e241d0141d0b19102c0700c6500a4124403004064900031640000020180998011460b8410311000c0709540300540d00e0800074100000360341d40360300c0c0501d0b01000c9134082205101d4a4211107001d0046502264640c080151950b00a103480c6d42600003000b8504d02c070400c1d80300e0180a18811100011541000d80500c0000c0e101c07900840d010703000c0c00d45100d481c2d0303800c880640290301e079002c460f0b8866a10b00d2071080701568400802074101002c800d10f0b8400101c045400c3d4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 286730647 1250 286729397 286729403
    0xc140301090c0e33040e0c1b07030c0302010c020d02031c020d0306030b0a0e010222080c090c160303110a0210050f1303050c0106030f03080f0708060f0904020319030804 74
    0x1088078030300142001003041c881010240c4d04c1340c0407903c130f5000c1d0040040902142d80c0d18004030741811350b540003106402c0811101002c80400014514011011400c070000c90314141800403c8041c0c11a60341c28001400b5000113418440034500a904560720a00480b5201da40a0240c0f03041764502e200c5800550110946000940580c00c480b1040368030902c65401125009122150a5242c10740350f04001c020781540800c00e550200401e40f500031a4466602c1900d24800210401600d014007030307400c1c0400380ca884da204001c13000901800d140c1c3c04041e14442c04907007481c82d40c101d040d4034068005020642c2c440c02d80500224840d0301054010407004d2207482d849900780000c0d03880248040a11318100c801070030b0140a603442c0d2000c64425030182c119000200000100b0716140c0d03c41d1020740c00481004c4002640707150402441c0000e07080c0c4260008001d05064401d428454001034108544007c4140a14451400030741076603000c101003074899084021b0100502c001e0b0500400c010000c840c1a = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 286731897 1250 286730647 286730657
    0x19030315090c020d0516050105040b0912090f0f04060f09060e0c04080348010b0a0515070f02040f0903020d02030c19051006060e010210090203100c140301090c 70
    0x900c04458051001c2c2034003542d0280100b07980030071055400b50400c40c04800b1069061280310300088092007005e000e680642d15428952910222080c0740111224070030890503000d01066587c1d4844036100109550104e8140d0005450040801c0081002e07a10820014152a20009082070158090010341c1d071071144180d81c5076204804403031300784164460303101035a204001c441c01b00e034805d04a0341000d40c80f021200c1c110004204000b0b2411011002e19840034441c01c580b40d6580209200304c01031010305581144116190100140d8450645414920307000e500054680070000c0c0307511122800d41c3e0051042011452000d007580040c9055041180944504401144030f2400001503a0a010448005100c414401c0040004400704098115828030030420884510b0940d40030342405844c03660b0300c0081d012540c000091400c054081b0540e181c610b8034401c0009610b0210b210200544400340100301e50410403408c0342c030900b031100c450b103515502100101d54019a1f40040c030b1007034500c1e952 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 286733147 1250 286731897 286731899
    0x5150c04080d09140118320904211404031511040b070615080a110307120c140a050a0308120a0e03031b13060801080f030c030f0c19030315 61
    0x7540d6100042c080c03400c2c05030004035080521340c821b0108a140d0050184640007199950300c1910070070140100107400036011004910f003260380764180103201d01e400c550b914168141511500c08003102c11022407004c0c503005070220581070060500d0b50408041c41021b0f90b5440d9130303042c65032000c0300070b0502160050500c0740e000354800c443c50954041e104950304041c94980715a4038a002044000300d04858801c10110008000b0410f020503000103020303490946452800c0c400309410100d058102404140014411001050603000041e095940035140003400088650000324045099840168025004100032080055034006803c6c00d580121405440b501c0b05007401054902c00508018590310a1000072440202c0040c0c02508407440c031071092034040710034407001f11245180c200c800450b030f00c3d100420444204110041d48800d4500c069810001118446500c901c00d0ba081860b1203000420b030700d044200240f000c1040c032007005003004200c4d42e241c503016010f0020f50500b81da0440440c04 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 286734397 1250 286733147 286733173
    0xb090909060105100c02031612020f2b02030109080307090603150b0a0c0c0918110303072619030b041506090b07060b060c070e1e0601080405150c0408 66
    0xd015043e50402840b600c1c004001c0482200c0c0445422070590b498421a1802c0503041608401c0e40e015081841c181d801803005030061000610307040003904d01401540c0480b2a00b009100300320742c000c0a60301d0039070700044003900000c1d000d81080b00c00504900000001e0022031a00035590000321038141c1c8060114480701c3d81c0120300e142e40d03031260825946080061900103842841e41c0040c03c1d210701c105800301512005007408540240c4c2d01c4146000403900d010082c0410502c2c0f0801c41d080c2200218036200082e6124050615081e403500000000801c2c00d00d2400c1e04902a05c5c010811504c0b01150014a450020051b1900400c0107025500d440030314003844428a100c042034030495111007544034900103045501c2d038400c150a172281a510b519014040d5240e1009111444004d03006020160600300c2d40c8890000151000103c08031724007a998801d4141503115510013001d080119242d501c6041c01030030710310b040c0d00e22000007614200f000000c2295001030019148418202d540242c8464 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 286735647 1250 286734397 286734403
    0x180b0c010b1e0108010302060a0210050a0b120a0215031e0702010b0405150a26030f04062705220c020d090902040b090409030c08030702030301031a011d041103070b090909 75
    0x82041c1c3d0024003810018000341c248080104a009283e00c121354000c0d000c03146850840d002911000b510a0b200d0445080764a00441d44d803c0d45100d00000d448420115800200c450907800881c20f2001c0001c00059201090300400343c084000400c04644c140ca0000320090023026001041482545403002051041203110009101c414012b0b00b0081f10344e04000f40c810341240d00c0501d040d41c40000090f040d10701c41c3c051010f0210841030481c1203032118202000a42550034401607807143d40030700210083d403032140000c113104842040c0d07010301d403da4100352881c00518518009000141c20241c510210031f40c00141c03448900c403240e139281c024584030300c3c6440c140d228034800c41002d6807040c0801866460298071903000c040c4241020740c4940301c103a441503035a4000b100c5807400740c0c2003c4010407e100d0942c0d1803014141e114404101c0f1907051500243d00340b100d07000c1c11945000300c00700160400143d00a05122160f004048886003070f529030501b003407640b03c010101d004d0803a400200f02d01003000 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 286736897 1250 286735647 286735699
    0x801030203010f0e0d08042604080c0d020310020702040612050d08070f09091a03061801060801061805060118090b0f0604030308011208130608041202150601180b0c010b 74
    0x2d4080c005c80486040111554000500190741c03118881d40c08202c54009000542d41d01c0500c2141c83da200c0c0d09d40b044044c1090300040e1000c0c051007802c4190780060b5030205010740703584030910b07006807516081c0c0040b40050109400c040c5400fa51a282d540603c03800080c1e8191015455440c8042d5641e03210007150904060003202c40460300020701030013544890740010020a55101c00c07039000c2208140080d1030200203450640f00a14a544480040c0d002070081d4005800c203a002402441c0c504602814844500f403400304516594602080301a8820841c210341c00000b460803810458403000c299005200030140341380310b1440180c80038a40d00301001901c00300c0740c05849107103036a880c0090201c00d40d844031800302c0d80d0a90070031550311011500c54448000c3d00440d501c0103810318203403406d54070284c5010051029075002540c203001c004d0410a04d650320034000c1c82d0180c070100b00d85041e0316100140e80c11410000e00c01003955004403605510030003000d041151030010b851450142c0103a81414 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 286738147 1250 286736897 286736921
    0x61305100b01080a09030e1008040308010e090604140a050a0615050109080a12020a0515040b0711250503030f0d060b030103080409020f09031605010f031104150215070801030203010f 80
    0x154000582c100d146a4001c030340590003421f145401b030000070009102c80b030800d8403901c04118030209010a156011000c0c40c058280d8144845860601e11900da955280042005029000441781001c1010040c082c00c015141d01404440c0e00c61524901000902078084400f41582c920110014043d131141d0841c07000c5a03441b00c06404d00c4038164541151881c2ea20700ca51040d84143d80404000070310070890480c60701c1d030301c008841c0d00d800c0c1403a1043d050b40020f4401020070074144001e03010038801181c26000030b00c2c030a01c0d10380d980320341d0342c804e09140300c407584042c0d4580800324220101d10880c1e0011b005000300982c0400c0b078239482d01101c500d103000070700000d00b41a40512080c441642507038010704121100440b01c608010a810020349000086003c4000c00c00072a0001c201d01d507040282c0d103071112410300741808075100c202e4100320503003d40c0c4241c2804044101054002c1802403019028280c40031080c25214a804030b4058901a020311003280a586450202c450704c00881c422031050601c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 286739397 1250 286738147 286738157
    0x1b06120b0612060f0a080d03110910080709080d05090a210f0812070e04050a0c020a0b0a0207061104150503011202060d0e03030a0e0f06040b06061b061305100b01 71
    0x11165070101c50060000c207160340210601138040780031340c1c51191410080180c40020300c003151050100800341c50000d4a01429080103006141c070070781d102c0117002c4e40b141c002c1c64180d0b8039035181d00081301c101c00d05510003181c901072a49038214540d03002005203000c5c0307010350b940d420046c1c0d02c41c03410600d0303038264000c0c0a586100410041c005080c881c1f180c65000d0294003039509082281c6000690800c00352038905c046492030844411701d0903d80a501e80c0304485000c00c101d5541540030181d20742c070304502c0003880c41182000107410b0294540c140e0368135a4210300708119040001480203095031003401846405081e11500e01202d1b442003048030b050700e4500701c0b081c907840c1641d420711446802030740c85000c03000e44440000b080e0704c60800146101e1011410301203011940c5200e01802c1c1403a501c2d515143c0e03003140d800c02020900c0c041c00540c000509884d015500d804000b41410707a48121030002000740140c200b4012587da402c03200e0083c00f4001e80c1a28402202a01e00c08101c984040100780440c23 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 286740647 1250 286739397 286739407
    0x230606060c0304180608030a0906030c0809070603022506050106080115021905030c0a0503090a17120f1315030f0c0807050d0b0402040315231609031b06120b06 70
    0x3030005413843c100d20313204e110041802519004d40d0381c255001840c3e8030000601d00441046119494012039480444d00e05110300e10341440900d0b1611109140642c2080c1600068208480c843c102d41d407600034884c3d0b5804201320a003500e081000303004280720324800120b11f10008074116903a101403407001c4034150000c000c40c01d80c880b00206110410101521540002d201891030110144400400c00388114043c0d07584091020401000d40d04541100b8101208030b003010307c1600d0005044840142c000302669103038807411140d400d05104420032003092001000c0009224864104071003803200c5151001d209140c8144443c00071a4224002080011038820216685901a50040c910510381d00e401103828a48400032605a81c4039500c119607014901010781c02e07444107403141855000051401d03100100e0541001440c0040c00b510181144402e24108581140900030b50401981d00c100301c00d0800c1c0401101c0d00c401c60761841443e0100718600c0125100f01210b00c510304081c28010010790900c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 286741897 1250 286740647 286740659
    0x203030c071e150b04060605040513180c420806011218110603061003110d0501060c120207080304030f05190f0303140c0322230606060c0304 62
    0x600c40b8410300144150b004032540810049078641c40107121040001c600f0400e10b006000880b802d65000d04200101070000f40441e544280c03e010980608510100703043c204068442c000c801d00960041503441c0b0044001130014804018055440c04155028941d6002c03c1a183d85030610302e010455030004401a280c0d07141c01951250340180c0c0c1850a544044401001042116241c070a541d44c608081440e1408000c07041c03484940c0120260303409801c6062510128200c40c1403c200c10041c191134005c0c40405010b40000d0381c03802c0344150f10901440d69607910103408218030801c02e881d503460030214241c6450000400700300312400100110303c3c062564540c440f0010304450100d6031805401c404009800c520030011450600030f4409044040c031516002d0111180075000c001554000010081c582c059003055070b034400e641480c9100140a080c28a441403203040318014440c3d0384000d8130f02c1c10022404070300c034562001c1c94219113030303070b01ca0204110031400b502d83d60b034469900c00c00080c000303 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 286743147 1250 286741897 286741913
    0x1151202040e0a020a0f1404111215150706050907051003111917090c0f12031608180108011401050703020f0d0807030c030507020a081602130504020a05010203030c07 73
    0x8190142c1003902c48080040c4d00003410244e2991081c4d03040c00500f5803d01034400b43c1c0d0101041c4260407503017000800890103daa480740210390f04400340000c000c0001d0484100442c10800100d001061007000d0100f03030140300e10365008040140c1d0080d103804005203000c4070000b20842602d1004000c012320003c00b00046018107020150410201410700220301960f040005c4441844015242c856540140c1075640d4100d8030300825203049980001d11042151301c0c0c448070302d11100801d680100115501c5d03500303a4a5841781c100b29003084c440000e14102031004841c064450880706211341005606202d00440b2104804c3c015145641c40e0649a02913541c0180000c10b003961180c01901d20308003e810605041c42582504480030684880c1000003d0390f051048130342000f240e041c208080c3c100b40c90000e42d00c0e01d0311071000303010200000700708169501d100920b10700d6690041c8004560b0401840d40b401a0900760380032805121207140208980d800801134074400e0407a40d6110341400c1030b076107400718 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 286744397 1250 286743147 286743161
    0x50f0c13031209050406140f06030f0c0a090312080105121614040e070303030b090708070507020d0c0504090f02090702030307120902010c021c030e06130b18030a140115120204 77
    0x400e010102100003880d880304e00406c0002d204203903a0400061054040c000015400304040d44542001c208100d916400090140e402103100b90407151144102c0e0800d450380c0d0391541001e003550b2005082201036503400b4490b41e040e01d106446021068034172403006030f5900d151a00c80007180c4902c48082c01640411040703d034001c00e00620208070850b400e03c9150810745640c0041d40040d88503c001011402c1030042e540c1c01844034074010b6814900307114024981d014494001744161080c0107143c0c14440300b109008091310005104002101407440c1014680c400298100c1c024410b000000305e8503070000c000c2d24407070005529204801d0b40301980d00d80081141c400124103002c0f000c0440000750b290b203070017110480d0203402044006a45802c02504012503120480d21541003004940004100d0032010b00c100c2c0c1032800c900e40c941e0442046030000c504660005501482109164002e110004840c101c18003000c0b0300070882c00320f07903540040741002c4034080c1d1040510300006003c010305180d84010 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 286745647 1250 286744397 286744433
    0x31213061107090501120b060a0b030606070c050a0816170303011701150311040b120d030902030a0b090a03090e07050a0f0c06050c0a021009020a140a090f050f0c1303 73
    0x50b4046403a0b00c00d81e400c40d103080c1c2211091108100e412001c011005c101c441d0895070456816a2a0341303030035030b90104c61100800d068000e11010641c0400c111214404002a0100420400d01c05449004203942c0e0a42a5007460f40c19203c2440054010704040341e5050524814000d5491a800d2107042c44280700016070304500b41d0758600c5a000c044282d24028401366114000d00646428064108800d5840300310000e4400c00484516116800e40001c903080b000c0c1d285c3c240440e164059000007410b0602c1300358043e00b520307901d80800001460210b004c1e030a062007512100c80c0310780c40300143c0e01203030b07003c449804c00b240003005450b1405002c1d00c54a0011000f038a0140700030728086c2d89075020790720305030340503071100b1400f041456040340c05100c03a26030b105059000b0400c48159400107001c06801e81b180405154020074508003640315844010301400c079150003401064a007500c00c01c01844225041e8114807040000720701e020490a08032604a0040c050404002d411a241c0080b0384070210301300 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 286746897 1250 286745647 286745653
    0x10150501050714030d0c030e0d0e09061207090504020405070809070902030c0f0a09030303050a090209010302060d02040803340203031206030c1e180c0403120509040504110312130611 80
    0x111200b460420043c44038080564022805030101350007d07042e40d01081861603c0c0d0840032003805041d50200d0a102c04c42812118810aa15448040340780083c0d0242c0c00d4955000380b45000c116080f003a00800c1c0118400e4604010641c1c1c0d4040860380000140c82801094000d014104810f0103290007540d041114101e40514201442d80303080403a0748061050310105005904c10400d054041c49919403180005609001c0d582940d070020380584070501000744110808180c42c085000658155000741c11074408990381c032000e02c541c0c0960800c200b0f41e001c0c2d20074084030203130080001c0c071000c091b1010381c090011410002d901c1000c0b40d070004000c00e001d4162043d100c00c14410790b24201a0510f509840c1c1d0ba40b96403d0088050042805501e1003c0c2c804010b0401440803c07003041040340c0881e504013101a0307000d80510310440e05d44c425120a16071141c00c00050000380f0400840003070b03078a44220704840f0341d241961560382460140c0214810700509205d000c01485000e1082d4100369500d03201a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 286748147 1250 286746897 286746923
    0x50304122619050603030901031e05010b0d0608031c0b01170106030c02010e0c0607080d020f03180606040905030901110c090103030807020f07030b04080a0c170c101505010507 77
    0x884032a1107007a951102109411814826404202101c0000b081c4a009051200d8a45580400d0741c070700c00c064006040603a01c004011007080b2203a8040c0300702d00b500e0028811135940311032124031a009071025540c007600d0400c001503c07950000c00c45e04156400c91950442e40c401009070740060084025407418000e000442c01e0403108050940c81c0a811213440c005109110100b00a0840f03d42d00001401035014115020403540e0366015109a103174418880c96496140600c98000f07400350310000c80324124044107015801c0724041c2480744a8082c0012200e030b82e951801003000740e90005801a000707401c10800a1a0707035205540c0d03035041007a0007046448154000c0702080203101d091340150000f4040c60280450329030b051050341075081841c0c004083c030a085445000c2c504802070401080440c00140840c4450301030442400d11079004407400a000328031904485080e8418200c10042c1d00849000300c3c500d240381e11640303044600100c6a001540c0c1017000564055000344801e488016018039 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 286749397 1250 286748147 286748177
    0x303020c0f0315090f010c11123406140f010e060d0b0406060302180910021c0207120801050409080304140c1e010e042a0905030d0306031403090105030412 68
    0x741c800c1c041c81c5440d0007172400c03800305016542182c035024800420092044a20000c4c4940000d0001d1030090408403d82c1c0d4908a020300b0b0900d100e03181e8510340c1d243c500708903804400414a44100f941e4020b01301800908088900d0284003c8202ea003900c2001c1e84900511002075141001c9611410180060355048503a84030142449000c40d400c50703405440d44000c5c030841c280509082810240b40e01c60360301d5400d28115280d00c8449480901c511035a002c20091035000c0c0c400341400c1c500c00300040031940e038542810054441120521002d010070110400080c880c10140b07d1000800d811081050558031190f40b0b82910b2000000a0910392280b071104a601e03646a042c140000e5003c08090001c070708544001501c036080200410388a2841c0018540400414014034901e01c010303085088291403402400b078400ca51300360401074052188100541c01c141d01a4170903000d0383e00406012101e41305a0030001da49114803440240015001c0c80868000b07000ba04240e60250810b04001c0c40d00c0003901 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 286750647 1250 286749397 286749433
    0x92211010212120a1104053708150601021603060203041b081b01140a0e150a0e0f061321050d03021b07230d06020301080a051203010303020c0f03 64
    0x1400f00c42880300b4071003c0c0044184039200340c5002c0442d032201c141c1047d10f8a0001080c10511418825400c0031140444c41155007515045c5ca1507030000c4407008040e0f840d0b120301c640d5001c000c00d54210810030364020690560000031584001c0c1c0440d021a00300c5811946d034203000e50009001121407150860900211007032040341b0501a0014000500040f03d000700c00110310900380c0083c5040c0601101a03011031064901143c6518070982400c0c004240c0b00008540411842e410b8003241d08008070b030100c0e4596010ba40b010050720300301d4045e000d0600c401d0401c2002d10a600d41500f007030089400802c241d001040c25203078004241920034050183c1c64581c9424540c850f00100c00017030740003400301819400c84900116140c0c00c9001051002d04082c0a01403030800c4008078041c03031128140041203a0380d021000740516034490020740d12540d5503504a5998002d0250851300d500441e031a43c9030b4900700005070b0f4122a0075078000c041c665680414043d000707428020154040c0203081860316600701c62 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 286751897 1250 286750647 286750657
    0xf020408011b020d030b01080a090f060905060106140f071106070611070303060b09031002030c0c0f0604050d050a08060d03050708031006270306110c1b092211010212 73
    0xda10b03410a14400810003401d10f4401c44000060529082104240342d9100c9031680d4007182c9290001185903240c00c0c01150350399503143c0101000c3c01d00600c0410010045081030485140d900c2e4625200c0e60700c5030301c110b2070084030a52404058244440c20200d180002c40c02144030000e0403d500c2d003142074840780180e5160012951201000003074031402c059152150500030501102e59a044c00766150000383c0740e003611a400303441d1a13008404683c20b0b4044404035099044500111034001e8140000540c440394121400c0e0340310300462440d001d69500440c201c4440211a0f544c040d51035507050200302203020341c00025020004240104000242003c0046000b613450303d02d22a825403a10800500c034405854121480540b180c18503032131884004000c000780c81d4003500100350803a08650681c0580242d168050092051891030303040c0c1c1c40074541d0901016030540c2c0b0010300345e484141c0d0521004c0c1da502140c044c100061204008582690100000f040701403041d035005460f041807010554004d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 286753147 1250 286751897 286751921
    0x130309080304090e0d08221e0b010924060f02070905091b030705060403020609061303150b04140601081008120c01141b131215050603010902030606040f02040801 71
    0x180c0d090b207032200182040816104480b82c40d06c901203161a280250561b41401850a03111003902240005c10004010740080e012a4242203451030703295090a0400440038852841740340c1c5491011400b0120400b03544482076188502d404c40c4c070b480c201080300e0410704600240d04501403d007010801002c4c41c02054000e07a00320000306101c8511665034050400c482c10254403903800a10100a5a05d901007074034122074040302d0740c03611810842c0118001b071144001415000b058600040100090b05180b0303500d404914104002c07409540e03083c00708503050003210a240c0b1212400180b101d40c483c0d0f4480358070480413101d0890b42a501c12040e86051002c0361681c2c0552070118210b00701d1002442242e00c5110802282092340c10007440650184442c05d09004800000042e07206481c0c0115100a0041603c843c3e02c41003e504c0f801d089141d05003085000110508050129400d490140954103000d07800038040c2885486030340c100002440d4054822031b000b5028800042c85444c280700356050841 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 286754397 1250 286753147 286753151
    0x20915090a090201031503050d0f0c02060d0c0909051308030a0f0e01050118061a0f120403020303061203070201090e091009050a0b070906270308031312090e13030908030409 76
    0x1c00351002501b1303245a008a104d8690102c03000300301041001442c550031440d2420100b0200405100444080703214a13000b0790851000524840340c580560303ca4120102140e03a40314641d0b841744549001d4034000d54200d8403000d01d4074421404515001e000b0f5401030b804c0c100003c0c0640074442c2d43e1042c0c421078030075950b9595642d00100655404281c84900c102c3d0b0b03940e010402e007401c10098850031600b2481c50001c07243c1c00720f030003603c0c02d100c1350071202054034a07001100d00b86482d140084d9242c3c012903116010362041600340d0314209000060303850301a4140c5410003400c0c20b02224400a180c010404111849081e00d02c0d900d058032886103440c9030b03020704080c103071010b1181008020300b00301500d2300307040101140f0100030045d40170340462981290602d04500d40c0da9400306480e4003c0d80307a08090203042000081c0300382420301940c0460258403500940c0c0d4152100704c41035820340f0491050000300c001e82000a08006201d903103081c0064421309000106544a02d160781c615041508070030000e035 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 286755647 1250 286754397 286754411
    0xc04051c061a060711030a0b010b1909050f090403031b05120f0f01060c060f0c02010b0a170a0f0606080a2907050702091e0703060603150f03020915090a 67
    0x224a41c016850700496258202c4110b554140c04200e1503c500c10000d04441c12401000ba1199070600c81024200c2d001242c2c14807950f19140c1c25005035214040681c00b447c0806441c2007118040e24200d421510010b0000807400208401e00c503031224020811420942c3d92402d104c074071090341c02c00c2c000c00402565044d8a41ca1002c2c42605c1242014101c0c0203030803072040400c0790128203644442e0646071545001030303c0c2945894800041c03d405950b03041030a05064440c040c0c594150700c00783c03a1714400c5440716443c07542c8194a40c1c416030240d0050041782c00c511140000b15501002000d031843c452040002d80c19075400e40b0b981002c502c201c0444a142545810740c00c83e08481810054030840c08801c8070340c5040c250005080c520803044024014815000082d180102ca90400c0218030351348c010b1211a45400e54008008080e04c0c000c60011a01e0450a081400385039048901641d02d00c0d41d424841d907045408001c0340d040f00400d0ba038520419941010f00300e032217041400c1c2c041c10040b40007107a01 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 286756897 1250 286755647 286755653
    0x30608010f0b0f0f0f010c0f0f1406070804050303011703040b04030c0e0906010602070312022109030d020106210f0507030b04060b031b040f061e090506030f0c01080c04051c 76
    0x140b44441554450359100c200c2580544c0e40c50000038005c402400d00155410080c50114103100388100c000e4465041e0145900078001a50420310215064006495050707031080c100341e50990040e80d002e801580144018045401d400c00143c0b21901708508507400e0590741d1105951a0340150022111034041007010004160f40c0301051380c0103140d01006e030001c0e60602400035603a0301a84406080d006840307041c20070090090100e00b550000b101c0000380000d03e000327500300040d40081005030181c42102003401d686441031040e981500e200100301050f058408640c80010001188183c07442e040c401460000500200a80700085110307a0016040d880e03c1c0c203146086644049220380280c101800800782400c1c941c0130042c013220308690000d950003144800e00c00411194214040865402c880b80b41182c800740c05441c11101c10460a0109640d482c05043d19994021517110f034690054803844070f9980508051980503056034040350426603500001800b09a20000b00d125006c8412810024 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 286758147 1250 286756897 286756909
    0x510051e0901020106232403070201060e06060c0c0f0303120f0603070f05012309030a0609110a06080a050c09090a090506060f0112050c0d1506020c18070e01030608010f0b 75
    0x10f04901d4810301c80074201c452207000181e204105984145000c4001c1640c0c000e4110f180801c0400c0d04c244d6603268502700d00003900030207a0703014201d04074400e4400a400c40c5001d004488110510702c002e00645200070b0203000018400e507030050380c180000e0042039010300e969104544600d4038002600003a04082060500b4038056800c40000c49080c101700380040c0c0d03002052011420702407151940220308980c2080ca0601a01000d9036160086008035014005140c000340c0c6e50030b000d01031440c01040981c0800c42c0449003441050003080314400000c01c29420b07a8000ca41c8003150210503460700b1102c0000945000d030803103041e440f065507461000c00340207080151035844581915014200000c04001810042020400101068858000405500010701991032000041000380100d051101c1031982c41201070040d0b000500c11020313071003440c1c038004410240c100b00405500402d5282e00c1c808071540703202c1194172410b050b200e0b070000030807030001d200e85400880c00520002d501d00c642010840 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 286759397 1250 286758147 286758149
    0x30316090b040605030f130b0a090209060418030c110a26010e03180607050105070c02100e09070c1b081c02161e0b040f030c060302070506010510051e0901020106 71
    0x10510710148814040f054000d030403203400410a800d494600c1d070b20300010107014004070070000c04448c4032009110702000a500a0ba0f00c0c40d00c01c6034451016a01c00017400119408010106646855000c0707842c0405c1c002c1c1c3c1009062030191603024280030030400403c40038042035206582182074200151280401006400c5039020890000d10040002030b003119524000c422080400f90041c0a00560a40e2221304445002d50f210340240041c0c03030503490141030021001c5060b4002d110300c45010343c56510400c80524a408000e02041481d200d44200312081d400241e07048032142501141c07a000d403110100c031840103069060081004090641c65100402850032000d002c0d544400410744e8580c4100c90390509031401c200f0072280d040305590380360950818a60282e00c15520006021540e01444803d50301503a0181010030400ca46c0e45508500703c1c0f1600d600a0610f810080041c0280e180010b10302d4001d001034a0400e06113410251701000d158001c3c4458501e0f0040012080169602802054 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 286760647 1250 286759397 286759409
    0x1431060b1305090304051509150903011d0615030f060f040c120b19150b03041b0305010c0206010e0103020108132102030304170a12050c0417010b0310201b03031609 72
    0x48c00c041c1d81c0c034003080c0011181751000d11030780c00c08034000c5000d0721b007540901510304414005034121862000545d40750002900d411080500d82100010315040c0005ca5285030f82a60005003840c0d40c17136902400328940007400850b200c50780c1c00310015942c0e8100244503599801200c0c520260308104072071200740300170314460b21291414400d441c2520b20028100070119015120910342d0f0b950b451420040090982400c416080a4088080140107055102d40481c1c00d242c0c00310b920998030b0307695403121401d003444001e0018102d080028460b03601c42c240021040d1181c044c4400c00301c005000300c90041651084107006070300104c00c10040c05441c1c03071524031003000d03001c129281015a00006201c0100c3d0144800c0d651f03103a17008500380d1075000307003154002c001c143c0300194100440c41d44140a0005ea2001c18428800c584145000251522139081c4c0d046044242840c40000c0c1d21245c41e094001040c610726503040807201c0e000c80d800c1800117500c07404c6403220b03001944c100c1036070281244215801207 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 286761897 1250 286760647 286760689
    0x310150e090a053304050711010606020102090a060e12030307170c030402010c20091006020c0306010b0d0b0a0b04030602030403121104060804050f011431060b130509030405 76
    0x300100000400c10751801c0c0b80549160524032031450351590301301400c908050f8205140008201415510064811082ca9500c00910403075035a004c0c00c030309074003901c0c13001d80c1d2040c90840200166030140010501101010748401402e4501d21980750454004541200109403d803040395070f03503040681901c0d440750780081654194207054000900180300014010022021035103000340c1c8082d032180c2548841c0340108100940e25165844c552100c100f4404e0b0009440307041e8440342d05150104100d03040c0c510b083c601e80e061058680201000e41500710302c042d0800c0d02c02c0c5003c00c45031008001400650f000c0c010241e1741c0d00305444c0040c510b15440d040480580e00e0240104180f00e0740c0011a012225035141615480d2034605006040c02429010070b40c1544c60143c010404000c003002e251700c61510b40d10501c403917800e4400a182180409045c0440901a911503000002c400b42d020081420001c0d00356604d6203c851902d404403041a82d0180c1c240d0f20104d0100858030342107400d1b01c1c50f0411100b80c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 286763147 1250 286761897 286761901
    0xc030501030b0703090512030103050d08090c36090a020907090f030f030e0306070306030c050d050303011703070816051612020f0f06040f0312020706020607050310150e090a05 77
    0x182c5080008081d00041c105030302c400c00f00b41402010040d450480000c00d900d40d0303495070760349000307583c03924028480f10119002100003981601c001c21041281c8402524100c15040c203181d0b135028803c240e14031007072070110000810b00385800030a0790074481d001c414000c103016041c6004002200314003c0030082004075207041408410045001c60003201d900c01300c6030600700414542139030a02e29107081590180718403410402c4455143d0440801c59008a40e80760701c894a0300c090241c40c10303410802400d41d90080004100010383c030000300541d400c480713007a42c0c01c1070100d9a86490b554024201407002e0011312000c0c0081c0001800034118450506c0c084080891803c0c18241c02e0004070340c0d0286c420f0341483c2c1c503000d681d00c4041e50b50304138840c001c200300c1e0355540b502640070362200c49000030f07901c00301d0040c1c010028a00008103c01500c10903001000e80c0ea03541c0784100c07074039400100740d0b03610325002640000b03001c0c40001d0609014825522060003030a805810f00100140007499001c04030b0528003 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 286764397 1250 286763147 286763153
    0x60d1401180b013002070305070b01140102120c0a050d0c030801090603120c03090b16060b1203090d0c030524070c02010e0f011103030c1b01091e0f05150a0c03050103 73
    0x4100f2007040c00c6550051346980703810000c1041035580311041d000e030b400040c0e01410168810014a810f80c414900c8001c50b07602d5040b4035800b078070080c080c0d41c09a03011032500341ca10880d02014000001d5030f80c04035aa0015155201418036000350a540c1c0030845144034281010f4200030201d000d400107220030000c55203180c80e41201d10116440b00001e100c42c440890f42414032075108000034112030f2180c581e0703440350a40d8101074443d41c1a01590450310700b140003212031600341d003100c201c0b4001c1e00c025820040c070b40e0200141e102060000311840100d06c440040000c509020008207074030040d000d68824400c01000c0b00400300001d04000401c503c1c401c10100507a000303504507148080c240c8a03901e9400d404001615419404000e0707031740d240700100401c41a03d8200e802030604842501c2841d040640402c0c0c0d82d403d86002c8a001424903800c502c8902440c0307003120312200d02c0d5008070086c900180803612183c2c2050030a071190903081da403800400c40c00060a014003e4448181c0c43c08004940c51a1 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 286765647 1250 286764397 286764407
    0x90506010819061a03071401020c04090818030f0a0b0406050c03100312020f0f010207062910031112010f2304050a091703040303110f0d0b060d1401180b01 68
    0x110000f01816902c1d00f8510f0428080c43d50903611080c081c040701d81d621303280d94443c010484030400e500e006100e251241c0075141880d026801a180d88640001c1c145900d0749804103901900c072005030381502c502800d1400400041200851140c020340c0c141c005418035040400a548008204840313026041081c03181c1203400c401c40c02c0889802541501c0d105031103800403410510740c0100505244158001c8421045040d401461202d00c5988100b041b440401c05080c25900303078041d512106c00300c9100071010790800326502c034010280382c0380000e8400161841c50783c040e004400c8400494480b4001070110000708200a005049a42d128494200c204001002182c6240c00d11900541e01e52011481c5242984c000845d150b0b400380c544803404804d40c100ca841d070340007110107400090400c0c5e16650300d40f041604585280d501104002d00e05483c2d012200054a0f003038114a8002600308a25280c080d014400c40c4420050155041c0c0e0a52401c041546200612180420050b103480d81506141e80c01c4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 286766897 1250 286765647 286765693
    0x1506070506060409240e0c09040312050a110c06070f1b02010c110607150609150618050303031006080f070e120304030b0f0642070807060905060108 65
    0x102c0c1c0200d034a0042d440d05881c0c0c052804151071005002440d040300201740d40d0441511816000c046a420352074803420403280620540303014011420027400d2164840d00c4e80c02c01075228181b074001288141d529180c0003502e0f440042c074100720381c01010074010500d50001c442107010a0b586010880c500d01800caa82c080c0180500003418040026084410410400e45c1c0a101d800c0041c2115154821420a0152500078290701c511480c40c202c4c0c041610b1055220354503040403a12041042c00d410b081c010b4910003049c505a010000910000042c0b65a0401c000d40c80303030003007091080c41103180c010043d18450019052080561900c01000a4503900420348401c442c405c680c180c00c1e04100500d418190301c901e820181107040e42d80c0811400000e030000840c003030038040c0d812514200100a000b40030208604040050b610340700c03848801c032101501145171441d0003409061078a021070b50b03045103d030310105080790319030b072500d102c2024804144100d500500941000c4c0440405961800d489002c0d1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 286768147 1250 286766897 286766899
    0x11070819180909020112150806090a03050409021c0c020c030705060f072604080a0201081e06040b03010b090103060609060f2108070f032705091915030803150607050606 74
    0x3c1c0d44800c005580c850304400e1900c81c10060104146805c0310096a89070119001d558010f01c0b43d04082050520700240d00c0c2e4946400d40c0d600ca04040c1000c140700041e47c0710400301044010071503101c800205c40e62040320f08010140e0010040d1043c1007041c1401c0442a9220718402c800600c00822083c07220000c6a071496400314901001041030312607a0220840c410411469600205001c18003500001c2c1000205000b620382015960351541c400302d40711140300d43c0000c0710540001081342e504041d004078144540040c001706501c20124003044440c0b000340c0c010741c1e803107071550402c00413045680f01c1d0700c01400400720b1000507039060000888000c88204001c00c10000e0550044061115040681d104158024000c607040c1505040091405000b40d6031000038071401d98102000aa1a0320700b00111440076158540503600d20080304c00c10544498810040c3e42c03117100041c0096103040c812401b540c03040300c14a4407410080c28115211011041e800e004a10801242001c9200054000c0e40908 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 286769397 1250 286768147 286768151
    0x303020d0e0109170d110f190f080415082508040c180b0a1a0f0a030908120708070503100e1008010c09080c0303030105011d1210020901030b040c0c0305030703110708191809 76
    0xa05c609d03010300011300d50a405010f40e01c0209000c503181c0904d203120007a520540e500c08031141c032003a40030701c0c6170343c450302050202c4c024000b200b100060048805a40c40b50051100c2601c060b43c411200414a04072140080107695502504107203280c1140d449018222842d5041642c1d6070ba200c1540f2103109a02d864000e400000c5221180b0a10039040040c00642c03180302a07803a0094850100001001994000e000c03070300d2840003455544c401d406480c46030000d5070000001e589460010041c0701e07805805058500199040814404000d024003805d1040554035451000d01d0801c000741441546000b5030300c20f070800c000400c0780780c0c1d2089214688500c60f061044443d00c600001520042451001c02c10030b01070f0240001c3e40c001658041c20000c0e00a0b01c0c28040016182e0411084803900e544031030104103080e0b850030100703200e01c014523401903c900b400140160001140355180e0000001107410030400a480113461405003d00240101c481c200605d0001110702d1200450b4070a024207000f1070703 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 286770647 1250 286769397 286769443
    0x215010e040305370305060405060405150d0f12020607090b07050706050d0b0a0e07030e3d09081c021206100507061d160303020d0e0109170d110f 64
    0x603500c0c403102c581c801407a0307550064500d95504c3c0038010f0142103400710b100c1e614000004130341e402c003401420712031480c0c5152a94811006820401081d405504c240d80c0d0303210740100710002441910700d945101a2030307001400b0500d400c09000b06078000c0340d0015215000705000501c00030380e0001d5281c054501c10b040440e102e04c0b80007844030080c203c401c0500d901c0200410001502652490350500441c1c00f179900f4064101c0025800381d90760b5980304000744a0700900089401c91000c80240c4090142868100074128004078101064840a180c00d4903120380011348103000010b04c106482424000b00c800354240203074200e62504c00013000300107074007039075030b4400c1c800c80988901c04132103165a00a008001079a011b142d8000c0042c0c100401503400d116961410400c8452600c421044035896402019080c921220850700c101c0d0729400320303041c00640d19020611801072031440451104107402002584500f130002090345071405101c980750b40095402001440300410448000415901600546 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 286771897 1250 286770647 286770697
    0x3030c031b0c0906050105071502072924030a0f0804092406020c06030a110409092009060d14030c0109080403050c04050606030105040506030703050303070215010e040305 75
    0x3480d103034101c220021511600701d00422a103035006200b0341e84000410071080341c480f00155046d2050900240403919440500c5107104425001043d24610030864003603c98a02c59612242140303060103100141c0c0b080302000a14188513640b01c1d4a0040000e01101c01140301c40421303100c20494002404009a01080c00f080c0480a4100c900400940804110b400700102800c0c860340d004440003e062401c010001542d81e01c00034140c0302421000340345910b13584411201d007004001c2005030381d0b072584051000240e01101c07403183c4c2d0070080c02180004c100f110341d02c0d412018032281c0804240700300d40c20400e101954032481194010f855000c1c00806005005146880c594010101901002e40c00e140149003000f40e01401f400840b84200c00315105445c3d6a0108030030340b01d0072034415420590901c0100518078281d0021a003000e0040c060b980d4080c1c881d1507036401e603801241c2030030160303119040c2e00c050303a103128605600400000742000190f06181d94010300320711400c260034903949121072041c2e445c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 286773147 1250 286771897 286771907
    0x703050601021f0c020705030715110a080310141f050a110f0705010206010b2b090609140c0906030a02010818060709030c050105160803130b010b121f03030c03 70
    0x440905186030f11540078005905000c0c01c0d058039103900500900c20005102e00f4002243c80545441100d030300250b02c0049001c8039032042c0340c41c05d548a4030606a9060201d515207004500a10241c0c084484050804145056080d20044507070b02581f01201c416a6106158264040700140d034580759542d104284000c85003070b4213807003501255000d01c05546001d41000641d5104455080e001d45406030303a00d210806c0240225415005851500c0640c41c06901456903100c1305500641400100400306071540b4007103640c00c82c804c60b080d0307003c4400c007450110104040014007000300d81d4402503181802c0401c0d11100060f50082c103102c900000300307403c102d900f218820030001d02070445142e80780440d0001c1c14503000f44002d0f0394010541c500411554402d10895200d1031128402e0000b20b0b06503500c15101d41d00c01860300e10800340c0401c14100190041d40e882d4000c240207400310352200c520659040121201038299038203280020703200041c600004c14004212a01030030040c0c182815410f00b41d40c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 286774397 1250 286773147 286773163
    0x80d0905060903040614160f021f02010902040b0301060602030f030c0912010c0e1806010807020c150405131e020c0109060906090311060106120b0d02040204080307030212030f070305060102 83
    0x30324080c407000c200c0e0140c000000b070402c6400a40d1030306c03c1c182280b95841140d00c1813a83d034030200050001c031900030424110164a0461020300401092264030f6080401e9004507a00c0400503515054400298176041c00750141c5004118003c0040368074201c4041d540b880b608650601c8481f01000003460784054a090701c0c0c000c0300191032080300e4418114070302d0090030759600309000b0400c2d50a8952030340c00d0111421805545122040032240c89040c0152900d510040c00360f0700f10700c200c010741900ba07200c101e080c4040e4000b400700b0a807030340d09007000c0102400c49020204400c600e00110008502080174200d0002d070071442c00141c1e555465035046000d0180e13503c01900d0325040420740c0003040b2181d0b00503080c0354002c0d03590340c0300b00c140d00301c0341500c51000703204031000900e40798800e014080340ca40c00400141c800902a5140303180715804201a070300150700444190300003040c03032414940c06000444140c849154001d14520b82140042d40450010702a1410941e603140003034040d90013081140 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 286775647 1250 286774397 286774403
    0xa1d071d1e060f0a030e0106030b060103020702030a1415011706070c030203070507060c21120f06050d05071e050607080309030d090615081203070f050f0a0509210703080d09 76
    0x82e0392a10f1440c0c1d01c0c8029400481800c00003440d0500c9070841140601c160001d980c1d1000221071aa140c4000440c0650030200040e6858010100d07440c00245d10302d580e0074615540007015002241c0c21281c83d45000c1c1c0c05034440810341003a620303140b03603c100100d145035003c1c880b03080c090010a0642012465409a04401000d501c5038a00106040f500288500001c070710841c542c0e624958605400d041a5121015401c0810134501d14440b40c1401c540003003501c518841ca001a1059072130002450002c100c180981d110340040d41c06008000807038841c041d800c000038941003000da20f0503001ca416442200310290260340d011012910741c0c1030500403190180391031070042c404d0700759600b07020004082a40808c0100000103c00042910700451400e126249c0c20044c87e00310340d50300b60192080c1e03030f01c0206441000001c1042d8002400d10170081c08440045640760368032818543d00b80448010090f0b03034046000c202a0b802c000c01000000c0344420380c1d9000344055142c2c60503880030009042e20034002 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 286776897 1250 286775647 286775659
    0x6030606210303070c060605010c0b061201020d020f03060f030f0c040903140703030f06050f090a0903090503100606030507210e16030807170304020a03031d0a1d071d1e 74
    0x41310015030701601d0035000ca4050581048590b60760001174903005800500188054142e600181c00c5241c078100c41075090791002c3c0007618104280d11080102e078442c40da40e000d00c1c5d1001c02802050b003000d06414040c0d400c142d00404007810700d100c032503988a01851500740300c0c0303032102108020144070383d140c018148480054291a07100e1490064060314030880122041c518004002501c0d203040c024603191340c8806411180c8036114480aa00941a0340c141030f000d110404500040546042000b41309040c44e118000a426040c45002003d9031005040c0b00100b04451301d01c454080d1030f40003104124068450002100c1c0c010060030382c2051542d01c007401141c2505403001081c0202c440c001d00c6090710484074003050310356807200071419000c00d80340a50080c0d00c3d240140300290142c1c50030003030224a12102e840b00441403001415019603a001240e00c2850880c03480007103812000f45540082160501c0015030115040d02c3e030700903400e4000740d44110900100701540010f04104449024400303485 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 286778147 1250 286776897 286776901
    0x2001031b080603061b1602060918190212070e030c131401090501030305091315271b270b0c2107150e1f0b0906030606210303 55
    0x301800041089502078082d0141d80d0014100c0103000b5450303580920303403408641c148500340c050900402219038040340c0140c01009004034558a0300071881c0175000809200509180c041d06a099101701c8640280046005101885910000140060740200b451a002c804520b0090019203041041c04810750015503880c9910f2840c0b69a03007081001d0480c01505241590783d44d80b141c000c4600c244800340002d00b00b445454907900d420340c86000101041c24000c100901e07503481d610070000040d442600b0308000000c1203400425050801140303404c00a008102c80c80c510b0f00c1c0312109500e00311440040164030604403130601d41218000d013014041c03034910204503803513100014080d445196548600d118442e58004029035030300031241c94500071039005040414658503801c02014542d0300b903501903124040074490040801c4000c80c00d000f4510746441080900d04100d04440300d00300340714010211002000103640f00001c0700b9410030700c10b8542d989044040c0110208501204107105014000042 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 286779397 1250 286778147 286778201
    0x7080d050405100b0d02031002220b130b032806030f06020a020c06070c0b091309150c0905220b0603090703150911040507021606020102040e1003200103 67
    0x91080750540514608200f1003083c04201708403101c5646000b5407690041c042d8212200003a0050104001402040c60105001121481200700550040b8403046004103149030410118959a80100040041185981010300d002e0703185d10641607912604240d14101515445402d034054001181c10640d400c2c07020a2070b241038002795010f00d00d42001072190b405c400c0110725040c81200c0c001544002c040d400702d0b141041102094100c800d515511400108030110030401a01511250511802e4480f095061807107a41e01295200c60660041000b50101840700b503d13600f1808646c112018003900796425071506083c085c00165004035001440802400300d8804002410030540c1e00c6008e5444c1c20640f0452a03000311140824003510b564100c090302c030010b003015400315070020006c0c81598400500000c54104598031130380301000503980014100117280c010b42d00c0c59002400141c02e02000f030718640f1800d44618001c01e517200c07910425103400905a01940c031041024849140880f45880b40c91 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 286780647 1250 286779397 286779403
    0x712020901060807120b03070f0b030901060609180515061c0e060f010306090c0b040f0801050912191b0f0b0f061c140111030403020d020601050109050607080d050405 73
    0x1001240526000400801c400d8015044a8480c1005640d2410280311044400000d04910351103a0b4160260610120b80000314250721400381009822007070b80e82c20583d010038210303029a40100d01f04100c880e014040c0c07080b5884901c468503c034480229940d180d1001004012002d900038551201c00041c0f14051150301d010381d4002200100b00801030040d40310055a103514007150030116811000006000066040c1d114147c1107000d10550030885841e0382030004640d200b44c02c13004e038000c00e04c0e6041040c80f80900030958001700903000f07810b002c0c1c0032208101c4280900080340020ba0621081e01c926107100344104012120050094012100d142c14400d5004518810a40d24048280005904840800b440d94010000a009440942042d406040c0c0d6110340042c21510480014150444d03c1c00901171048128000307550180e40741014903002c0c1c5811002100c80c0b0070340d00840010001c507a04a5070403001c8850681c1c6555940c00c140c41d088442d481520103441601d031400041c042440000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 286781897 1250 286780647 286780679
    0xb070f050d03140126061f06051e1b0106090605040c030219110c0402040905160801030309090203040804090f091502040b042c041104050106050307080601030b011107 73
    0x140060798280300034031808030203075240c0740c001d043c2d039420302c42c010032003e40b400104000007800d9040c032503100d07503144604908003d8240c071511402c0550030039109007100f1555140d801400302e414070a150504a0785522400c0c0042402101c0018000c2600d03108911000e9600380c0c80310000d0020020151640d015400810440c0143c6008901e0104124540390003442100c04030400013000035a5010340c00b10440310341d0500181d0004900906103c007107991a54005400644421640810079261410213003401d510700800190400c4941d200400110350804410000e40c0c0b249800540c3c2d9548600f40801148201d0b0310403144940382000480c2103a03201d81c00b42681c0380c480d441d65120050b40554520582c0994001d04540c40360401042140ba81660a0b507580411100e98404020300c6401890000c1e5404503021395820b00d41c4143d154a41c6042c1c85140d0142c000380c1071082c110f0502c24401400c4d0741d0024840380c10700d9501c0c003144840c0ea0003120b00c04206c40c0307114100d80b090350302ca00030303583d0302d8003c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 286783147 1250 286781897 286781903
    0xc1309050709050f1003080706050c0f071a0601020303101a0f04030809010e1e01030f090f030807120207030e060a090f0b0a18030f021c0803130b070306030b060114040b070f 76
    0x104d8004160046a1004004122a001101c407030501c4442d44900c8d008090140010011200801003071004060200240111b2801758601011800aa03075203201d240d2402040e40c0d0454000300200000360a0017840710040d036a0482502c9441d04120016920700c1c42140b40310940d4035030210300003041002075401042000c00a036190308021200d507080c003a1100c607031021542d961048496624555110b988401d8200d2196580887c0d45442074032082d40514041c4415000107095504000030b9503048600c0441e4203042c40c2c0c04601e0205143c034010a1f804650400d240b1404000031b850201d140b0844180c00038041409040e1b00725940c0358084c0c2d545a102c02d001d140840c1840c0708d2400c001d4403010171401165000744016030070394007035420030a00c0c4d846003d0784407072046c1c000321003804550070b04051441224804440301c0b242c003040c1840030900c04e0041ca44030070981040403d00000e6003510665400070780a090000c3c1108101844151a02441d04080d01603480441c0801c20702900303180f070f030000f240 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 286784397 1250 286783147 286783171
    0x1c03050403050a0809030c09061012150b03100f08030a030207030c0c0e010f05030106260f0d030902130207020d020910170d0f0504081c050f0d060306110a020c130905070905 76
    0x407411f0507c1203001c8101d030300301d61000103451441d100c1d501841002c1c1c200d43c4100030018082003c0a840c00c03c0e045150011322a01c0004010010303800f1950070004007420b411100400304920708091150b0740c0c4501c101000c20190041280c00c1058000c1007051001c039417080501c14900e03114000120040001d00c50b20101c2d60415000141030308042c8a00415600788120000800990341d10841c03041c0259a00380403140314007807419001d074070705108841001055950118111441c2c2c0100301d00d070b02c541c00020789043e10410645005988042c0403048282e41995202016594028125080b40c03883d8400030001e2054030041c1c4101c3d41c0410801c03030242c1c0030f486100300c11450310001c642c3c6000b0350040c140668070200c1b4081034440e000200079026140f40c03401514000c0c50840c2d85406410001c403c4907800c0d00c51a06008120f070b50301440c0d0710a800c90036600d043c112540d800039030f50101700e600c41e80214210841c0600c5038200703401c07225074903401c40704030742c02c5981d110307641d00c0100002c40d03010031400f03 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 286785647 1250 286784397 286784413
    0x71b05042a11070e06122416020a110109080a030302120709030209010e04080d020a2001020307020a02010c060905030a02151b030f250207030c05030a021c03050403050a080903 77
    0x90141515040d502c2c2610001c00c030590415404615503c40980515400300e1610742040110344200700b00e000c021003140c40102e0700740c0e01881001e04888003405100b11500c091515410860f07001801c0c961007601700b2401003040b0901d100584002c02503400c04407442c0501401070040c0f58254001344541318100c8401c980540c0e61040c1144d0b4560b1901000b9881360340d41004000b0015920300c140c0d042800341400c41d1909010207040c000300e0340031072418000714100d40c0602201502c5031442c640e003040c49a0080d8a14030304035200a44400e00000000c0c140300c0700b88020f0060104035400b510324203038400f0440e584c803580c14001035a9034a112101d205005034510010ba80c01d10203002c6003c0c0c100b424654607040d07450300020410906030062807070364030001100c9014504060031480d803442503015006031840c1815820301c407115022640250f0700036444140f90707000686070140c00c01038ac0b9001c002e03000480d51103850222002d2042c0d520241c140e11400c0750342c806011402c402801c0302501101290001 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 286786897 1250 286785647 286785731
    0x306030201021506090402090c0c010c0e01020f16170f03070501050103140304080d08040305070f03081801060f0603020903070b040f14040e0c0f1809030717040b071b0504 75
    0x280440790300e60840b18817008600142090140a074009080c03420050401403141030f003908440c9880c14207000035138180000c510b156014070898100c9240d1402a01950b2441a4101c501c007030644214001040d5041107405607440c24010704005801078030949a403041300e4109203000e00828003041d10715034041012500781381c40c004101d034200c1d07a140340502040011403c058940350b20003481a400d002d0100700340800125000c1b408507103103200391103a1032241094030041d8264000303150b03010760301e0b13151043c240060801071441100300c0d140b520b00507a441e040c000200b8141034055008540780140810045820101050300d2003d48410221241400b841c180c00c101c152013050410b552150440014054613040030703a00703d01070b10b00241c411850450855240c181c82d010840740e894941d000030400008002281c401e038009035050b0b2510900702401d00d88145514402c960f0000c081b800d140c211250f130010080100002003038010001c1020010203104100011192400360b01c4c400141090700c000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 286788147 1250 286786897 286786933
    0xf0705070c0b03090c19090c05040302030d020607030b12060411010201020f0d020316300e0f0f060115020601060804030e0405130312060b0d020c0304121208090601050d03080601030e030a030603020102 88
    0x40c200308441501c03586c62a04003101d00400d1144200c0080003c100404009030f2000c0112184200c5194000d24081c03420000060890b00010200c0d03201d0090141b034401c9400c000212207400c00c1e08040c0861000b0200c00c010b03402803260b03812003480e01c034020540355500716241d4003039481801f462400302c3d200e40b035000c401c56200102c8030902046a000344220482c82401003c481040c040030b900c00144d110700182c50500d811100c100700c030119030000b101d15240d0320301801550300404d118408401e116600080281d1140c0d01400380c0d4003001800c40015041c10302c02e9625580c0340c4800341c0100043e051031380c082290301100380000c2e0081800c0520b0354540c844688202c00490b10410001410480628075040c061b47c45400c0e0350f0180c1c40140b001242c2400368140b09a0420302c60945008414600d880c042e0a00000402e0881550015401000b682d200d0741800c904c1c041c1e161501001d296200b5005070300901050174030340c0301440041503001301103070907610a1080e24000d0702220156840c1d030030f81c126 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 286789397 1250 286788147 286788169
    0x3160e011503050106090e040f0b0a060f0f050904031103070b04080a0f021606050c070e0f010806070302090612180703080307030e0102030c090d0201020a15020d050c0c060f0705070c0b03090c 84
    0x400030301b903101c0c1004590b60619065410a02c6101c10b800c507842c09898840d865a070079229002119036442007088104003803d90f020050056020300b034480c5142c0400204c07c903100401c0a800e00801030030800c080e400900c101c032030041c1d01c0308580001c0e007440d0420544981080c502c503404a031418180c1c001582c000540008000a035003007101c012410301d5000c8070240c03c1107802d6051071080440208408002d115154401c54144050b40780d030390701d082c00340b40c90001d01070142010305104004200e0301da1544006ca554a80d5140f038528629107541880304c00401250115034140e014581001c820443c0d4000154010042c0341d50a009007071040c8952402c030b1205541c01200c0c4030301044242c806007452308911f48242e00500503190f0072030aa07110810001c01c0d0b1000128500c0d030000b404140001d95100f0240c01c00480c0340c1d42814034201d015080e43e01c080261980300c491210340009100c440c401c0301102c070300301c2d0310044241105540c1d40d82c441c03040d041510025035034095410b0042075400c2054100e0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 286790647 1250 286789397 286789409
    0x2030306030a030f0201020f041401090501050a02060103080f04030503070605060406060927020408030c0313060e010e0906030c130b040e0a2406030602161203110406050903160e0115030501 83
    0x30400700200d507025190100c0c1c10602c002035540900c07501030040103080103000202b580201d2402e00c0c0a40000040403821640c1100e03040c484148008000c540d800515181500e50290500707540e40300c81c10486001e40034075130005002d07100000302ca0040080c15048140104015503013800312540300c0c0c0d4140c2d1100b20701d01903d07070418903e00c00c10300c5c8000c2c00b2480312102c64001d4001494035440386422411640445042e081c135610002d1541041c520785a41007000789550b2030024035040820700002c00500222003464030680048000c40d0380e503070701800403024000d802040c81d80c248002000420180c01881d0203940300b070b85800d6100c0d5108401140144070198051b000e030300604100443c400c02ca0244c40b5881d202c1540c3ca500100001d0104d1008100041c40000440150b0566107410024074540c241001d082500745020450b022020034281c0d400d2320340701c0c02c146403151a0640442d00e0101c0f008160031030196500c2000600a82c1301189030306a03094030911130701c2000c5481d01901035403400e115103 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 286791897 1250 286790647 286790653
    0x31080d12020306060f13050d081e09010f030914030406090302090c0c031213080f04141005090139140109030c0303180605090c0109171b150301090b09070203030603 72
    0x8010241c0084005142c0660348041981800351580041100340c0c5074104104d695000001cac0302d40701c44000c102100019401c5204681c0b8100300900000c01e22078401071404140b41d00c07094407004104607521281c10302008141220340741c507507030b540c001c25000c0c040c44182d000700c81c0d450100e0403010308502100c0050600354010b51030b000c12406c00458614000300540c1410100d40d0141d000200c0c2034009242d580d0001080c1030710b4034204803c0400721008424050300c51000000c10072507154214040e03a00b0241c090a050a000c009032240042c102c41400c03181c405d82c440c0b001c00003d0315010144281c001400b90324003605208022020508807846800d024012403222180940041d2003600034900820041d00007000c501e0507951140c3c03e840d03064441c0b50598020442c079440c2c55034413000700307401000042448851a9004a803c03a02e8108000e9482c4014881e00592400d5854007900c0d0014008a625810365940e5a0303141d0200401d4021111446052030902207070805200100f5a17028500040103 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 286793147 1250 286791897 286791907
    0xf020d060815040b091e0a031706030c130605060d060614040b0d02131e140102070f140f0303070507091811040b0415240906020331080d1202030606 65
    0x240513054000500003601c51140d02210340c00422040b010030096010302c001002c03038400320316000c0e104095504810b2940d20f0300e081084519540082c90740900702066802140e81c01200030103c0183c40103811143d085000010000203003041a0301490488240ea680c10581c01d030f888558002601c200e110b291000f138001d00038541100c5003035000f450140600c0741800030341c07a43c030204049062820724030110b190825420401000000d01c1d00d00103511070074400741650341d0034400128203e02c1103005e6a41c80004c885c0300503000f85c4807c00c018807901c000900b104d4860100c2d05d80155120924023079030b01c499042480b008202e03464501c0f2100e0942e440010369801c2c078a1403007440018503805000039806611103d82080368141c40d0850000b42244205610501c0960044018202c0740a0003200c20805100000c00400307501100751410052110ba0000d500484914103044e0a2a80031041e88005d13017040000524210005030050460460b0f296007280c102030016000403400100c41300c580002e42080 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 286794397 1250 286793147 286793153
    0x9010605160f03170a05060d0f1a010e01080f0604120e2d09061507120203090406060302091c02031c051308071a071a06060c010f020d06081504 63
    0x30140c014600542403451030100d00d510380e084108030750707031064004ca02c2d26801a000c401c42003032a154083c00c003c4c01800b05080c03110100710406030004028021901ea400b0030390801c9220140e101b82d80000300b00344d0290b03584400c0403150202e401c1c4101000d500c102200c40c5071880d000702d0340d14800c64008603406c40d091001305040e02e0038440b0310040f070b41c03080751a1400c0d06041000c078600c0020410301e9007100305420300c000600c4076414001e4019445042c00300100307185002d841c02100e892a52205015600d942d4004042c0c1c958003d205403035901038240781011a0840c1d165000c1c2c846100c00f02c55074010008000059600250a814041c0d01034021400c4c210184007200f10349503001e00ca034544507180c500b04041c4a000000180c0110b1003d40201e4810001641500d00c0000782c000c04070201840c2c0649642c41135040710f03981c2480318840e1450b00001c5d41582d01c034010b813403031614110700a001b068146007800c00251700c20305c48000c1070351410201207104800003441404c0c41d44400d4100c010340d102c0b62 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 286795647 1250 286794397 286794407
    0x115030206030411030a05031b0303010302150702011403040b0a1b0f05030c07052b1d0d020409080d0c090609030c23130c1403070c03110102161b14090106 68
    0xd0013601c03001e40340b895810041c0c40400180500a001e0700195455145401d0415031500355600c22000700e600a00040c0056a9240ca200c3e000380c0001801603035800140c401611038440401c10100d828034080100000c0c0100d9042c11842507113030071810840311018024401460501450440011b04d001c01c1d1407031110700980046411401c00fa1489080801c50303501d161801c2100e611103012030345031541302c00c004901480c00d0319600940b13003004104545a50100d00c00c00c80318484241c480e0301410f03800c50035503d6980c888951719800c100c039150703120041181d0b600a08011030400001031205100041d41500c0340802000b9039500108404100d41317032441500401c1542c0a04002c040101900810140d542c1c614442070681000b00100e4038808031440500039a1140000c005402810420004aaa40710005086103940350500c04803031107510b040f00e402030082c41c0114080c103292141c0030040c80030100001d1504400e503594010480e4907148413051014000507555084443d40380103026280c091 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 286796897 1250 286795647 286795651
    0x70906060c150b1302070506130510090305040905010b180f0307140f0a060807021002090f19090606030e06091c050a0507080301060e03100603080301090f0e0304081e011503020603 79
    0x4800d0204401854400055811400f06881c84c03410b0b0740019182d00704401030049541c050b8188100140104080d25010707158101a000c0c0b01c40ca699404e0043c0405011b80b0543d130103020950300070400ca40e11921681420381c403023280302c09030400018114000345491504c5080c0c101000d8003402e00345140480e08210b8815840000780d0184440380f6441103501c0300000704004000e0342e921101c0b682440c8101900b40001c04043c60144d0b40104000859512520b102c40540d400540c3e404514040d08a100001c296407a00303c114418103080c00010b9103075143d002255010401415151581c5424001c1c90380c51b4108040701900208010690b1001070113880541007455542c1005440c11b40c442da5a01c0d460740c02600180041136200305640124102001001035071510a00d08220080c00c6450344503803404144943c540c0e00c3d8840300f0b0081c1862260700001c861406080880340c03100d8813103000e44d888040841d021954100c501020071100c82d0140150320144240c040c801c2c0100c1c4c11602130041d42d81c80 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 286798147 1250 286796897 286796933
    0x308180303070b1303090e040b070e0303070c0f05100306081506011701080123190b0111060f0601170106050a0f17040b0109060609080c060901020c0303040e09070906060c 75
    0x2041c00b042c408a015010810310030445020755111414a902d80a05840d401e9089581e1f03000e0070008020010304002c6881c2e410107074500b1300d10b9084d604a00000d00d14031404000030000c04c000c20001819469130b021440036038100303c40c1d400042807281000c030100d41c4c451040131050352085d0b20a60501d48500c8101d50000c4d410301d855540100d0860100c00c00c0300007a031195542e60364980100307014403000c14a14a909040c032100420900340340a8040b00c04003d162850402541da402e140e009a015503800512103000c03005652142c98410000b220700303407045900c540400e00807004181408021401c1030f0507910180c84460a01204080c100c4009000c15180001d2005526102005a0181c0601446180309400e50700656042010b2a400e403461a071004e010300100f20420b004076503010a07a00e004180565841351030310300083c0100d00e495603401d062070f050300000401041054002c20f00f00c1c46210803408a456183d0344402002c02c41c2c1c0d55200364000100300420806c00104008208076844034 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 286799397 1250 286798147 286798153
    0x231602040b041d030301081c02030306120c0a0803090f040204030308010b0f0403080c0c030c09100501111e030a0e1804021c0203030c10050a050c03010611030c0706050c0c0a03081803 80
    0x1c4480580f58003884004a40c1e076059101000400a582042058a0b2200726100941c5d0b01600130b820080d580780800b4003221b100d441501c40350303c484002042b0081c034000c0c0080046e0303440f0390744658494807139000032a800c0c0a14880c502031740c0c4130f040a008640031640c1c50742e41c4c40c3c5503030300c0c00c1c0307040d402d640155480e00340444041000001140d040342c040c0440101040c082c200300c08503c4101858100394210003401b400c4407004201c107110481c0010012603c0a09001c45241080103006d41854118455800081d00d00c441d002607582000000d42019142c0e42c0300e0301e000310841c2041000b801282054004800403440000340141485c412a40e2000070684404402d5806a80040c0c00c42c0c01146004085a11070481440c00384485d0180320340181c2005000c201e58103020455600d01d110500034039048c8810422440712150f8108222071280c0c1005c0c050b200c0c15900c8000040540c1c0c428001019540301c3d010440d4085d140c410031140859610141d282d01d081142c815540096071010102c6502d40 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 286800647 1250 286799397 286799411
    0x190e0d05121b1606261503011104080706020d0302040e0a02090303070b04030503191503060b0a030f0f020a080318040c03141f08150a200a231602040b04 67
    0x207810000c10340f4040c0012090b044440c28840010081c08843c0c0031a040d12600400d4119020343c80840590080343c40c0d00700140300706005001c00d015007000c0e000041f4190000078001810721001c039203e810b8032041e5003034a03018281117008400768007481c0640820500c0c0c078004520b400c82c940d801400000c001400352400c1645139102c405c0c0e12101150300382d01091002007041680d01e0184c60000007028803080030000292023107a09a801aa14040204401d658400c154000c0d0ba40c0040c074001140d01c46e40c803035220381151402c600c0844460340200c2c0112208070300130501d41d4010050350380c1000035403d040e48010381031041101501740e0024850038180d0310003501c0400030101403428441c0d001c4031200f00312101d200302113200140c0c042d07010120070b41090071703201c01d503660f060001a0000c1800306e000c01c001e10041200000c4c1e0000100401840c1070005460410580160a000e050150200980e1840c2c8183d03c51150b5885604100881d0303101c40f03000d21006160660000e461041d010380300040c0b003 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 286801897 1250 286800647 286800697
    0xe0d051b0d2405090f0c0d030507140309030c09061f0306090c09081b09011a04050a03060504030806100203070204051510120c090f0504020a1103190e0d0512 69
    0x1a030b0907142410018082005000c81100d01400744a400120001c000c00701400801040354a40d00710a040318403070041e400f04001454800c01c01c1c3c4400035045074105102c0c41d042059143e59621607801c81d270003800389200d030782c0b240d10749048540c1c401c05d030181c525803102001d882400103089980d074900c0241079480c8070124600c00503115000e4000c200752600c001c071904100c0d0340c0e858030134010505000415403a1403480b0a80b01c81500e03a04480b44010a0002d170081091001c0c01800341e504016003166603244004107016043d08841e0055020b0380319000544c5964080c007100403203110740074015900400c1580c4c01801c042e0700450b440400c544030021000c04880004505101200c0d400f00001c4a89400440000040c89000c80844050900e03034030703003817900300080f44c6203599200c1d8030300c2075034040342540042d07014000840c1d407020031000740e0303969a000007034003103010007400c0407000000c91020a03c801410403508010756190008010900700140d172459000507400780001c52880100400106a0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 286803147 1250 286801897 286801913
    0x4020a0c060e010917070809010807020a02041a0909010e03030606070c26160e040618020411131d0a02031317040905070305060f01050a05040315020403030e0d051b0d 73
    0x80402c1000124241d105800c16004040b460030460f0807a4500b00000400907a0381422500845000c2c01e01902c4c642e5500400c0e401d0160042003c1c1d040b909085d1070001d09000b0040d41740a03042c3c00c0320904042d403a41d0209c14200e600d007105c1024203510030000305e1039034a84030014000141c41400c8030007040e500c6003815181c0242c4560000c0514948500c50000114244200011440401a0a0242450180540442c00300030b403000d007003e03980b0140c0d942c0ba41107240400d4149500079005111500d0280c420740d0050340415a011011100801c02056000c510950041c00300101a507e801075107440161a00951014001d8184d4540000b041c80002d802c00310400150500800d2640c0c50b503150502160035a440140312108240ca00002c2100795501d5680c042c5401100f0f00e0700c41e0316110500d03401e440301d1081d0780018100c440d507035a880030480c00030f400030006d40307109940308010380d01c40e042408580d508103100140a03401268440b195841c9400c282949a04c00410006043d4003a4880d074003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 286804397 1250 286803147 286803161
    0x705130618060e06010203030f0c0a030f051003060b1005070b0c091c020108060406032105090301090804050f030610030f020402090405040303020c011a03030a110708161e0b0904020a0c06 82
    0x600684900b01005114140380c90a544184280065480e5240010f41d1001e80e01d401080c000000d1404500307113441c18840e500c030100d44601100200042c0c20504000c0c440c2d942c0520040f50090b0030000c005000c0d051844540914005640b152070a1100a90302d480321100300a02c0385044402c00e0241d444595264420080800d042d40f001015040f0640001094130700e00405060196080c42002c1002620203038049060200060030300e0145200c02904403820312a0200303141d4103600b016046000d10544100900454608031003c2e030704612800c0a02d5111241101c1c807401c0c4440e81d07102000818845040101c3d010300c0240014030340098000090201c85080e82d05800003039010a0000c0740400920801600d003000b040e500d51500440360029a0324071908008400b01304a402c10800703400820025800074200304020b440300b0709403d40746101d060030b061281c1038460304604891031107006901c140b80244e400304100c1178685000c1405110180d03000300005410455040d80e02008038800d441030b49 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 286805647 1250 286804397 286804439
    0xc0a06020f19020d0b0f18060402060d0c020705030f1f140103020d0302030408031216020f060601110703050f0307050d0906020307030f020a020909010b0f0f0a12080f03040c0e01080f07051306 84
    0x400601f00040340041e014003440f001001588250b041c000983c1d0b406098400182001d0b0003c100c00311000302c00ca003025056400b50390540f141100c0c1d40e882c14404244505503038020343c030000c0c5a01049242d041900c620301c00307a14062007079100600c0542800c985000480e406801100d141c44c1c0c1d0b480510340b4661103160000d04c0700352481c042c440024003540c00050688190b100600032040d48090300d61300c81c1c0000d03021034140150440509071450050200c1001503400c6401d58008008020910741c0301e620150301141c0074051138840c54103c6019101e110140e074580d6000f18100003240e503095900c1e91840004100303500c189204000180e642d1104540b06004080c004200803500038248104282c203036144034803441c55111100036a071603548601040703641003c0c86044190850515031070174411480f0340c07407180300e00108200070701424149101c21901d00d41840c440580e40d440400391121506601d00c41680c10000d405c000b689400403130610740c95001040010201d41d15a400c018000111400c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 286806897 1250 286805647 286805671
    0x31a1f08010c0f03360c080309090117060a0504030509030a11011b03081906080307030c0c060825030204051305010302211f0b060301080c0a06020f19020d0b 69
    0x307450060b40007000d8160308029040500028001c0c4117001668a0780368030b49000816035000f518504542c504454058076000f0351007180e25074580340142d44941c0411030190080e182003000007081c82d0101044580740d00c42d0b0740174010075192581d80d00050440644181d08011051003500d08580e401c4c045406100c5c1703e1003400801c6c0c081c00c00094464008514400181031094481d1804250030000da140d00261101d07242c06186d81800e5040300074521908030700d55171701c40855224109504001003408503400740e00e900c4807a90303131803004a95030706049900c074460090b010080600e030328540f44900301d405143d040c0503040c1a01d6501207000c4540c0f2805c907144d900e44980c010000d508140ca0a500401e6008582e807808920321280c155031143e80c0111994910301f002d0003030b65603900031780c840082184010b1009540e565100c01d550350710740f01803c1e0680704030003888002680500003d16119403c402c00302a00c1c50340c108021442c00c64010103400c2c1d80140d500c0c5004030001d0060484944189104062 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 286808147 1250 286806897 286806911
    0x304030c06180e1b090307090c050c060906150d02030120120c1305220609020904050703050f01050f03070f0806070f02010b030304090f09140c010e010306031a1f0801 73
    0x40b00802008907400a00380709501070902a025041407101e10340e4004a100b020ba4648154012a16062941c0d0180302c400c0d00c1e15014070300095208004250540b00c4604961440d00e940c4c04050700e480d01550248903042d1600044400e90528505400c13200380000c2c000218003004034000b61070b03494030f003044800340000000e600042601c481c625940281c0c10510040c1403e204005041b10b60015001b045d20901a0415103e4851841000515032480c80c140a07c8030b10b0f42d43d081d2402941020610714421760510b000503a00b1482481500c0c480c00300d200c0c1c003069913482c040a1010004109141542500461101241c2c049a03944800011f0101d42c008051724030380b13180000d011150304007090307045906060705508241d4001094030280c511542c80003071030f421b02d10040c80041044031002000c0402100850010b03010120f20054460381c21380742e5010010300c450046086a40074000241440c03000f60602d8051040c11a40941c0003d12000c16118060668040d8500036400c1c0d010b0070300c90707441d512 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 286809397 1250 286808147 286808177
    0xe0c010f08010503030909040519050106090b0f1e041103100807060908070e1810090201020c0105040b070b0a0905060112030f2a23210a1205090304030c06 68
    0x500036644125600d00107038030b075040000184c1c9a11038041a18480c40f68070380406c0600c84103214150324a9038400d0041d60041e2a0320380f481c041c1c17000c0d1080e42803007890500071801c1800c1454215400d004001c1900c00d040c1d450391a050744c010803d0b65030607007150b0398000044080c0d4000c03006500882501303a0003c8403614103c0107900d00715440e00b086d01000044103040002c14000203c41094031a42c0003060482c1c0d654100300440160052203200c403e1050595600d00040143e10100340607000303038240c0340e010002d0801584c95102d00d01c41c0c507090650403c890307004200c0c02440c030350700a1484040401e10002940f141441d0a03000c0e006208610007400790b0740d00301500f0040c8010110044d082100442540e01640c883d0b0041da8503690004100c5403010500b00006021480b0814451110b0b0104021381351461a550b1002d1703407807940e8408082051b40d0401524071080d60610703401c0b45ea0700e0060004255035034004d00005401c04040744821701c404030018100401046c0908250b175228484035945078 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 286810647 1250 286809397 286809407
    0xc0804090c05040816231f0519090f090908070803010b0d0605010c0f030f0c05010f15170c01050a09030f030c05061806011e08032b06050f130b040e0c01 67
    0x175040c0c2c0301050800d034100061000c02c40000d09078655000b20fa000302c1000c0000c2003c0e5081c007107100c0c10700308a40340031003031080d0881d000c0d1100c0c0c03000480c0c1c4401059040410b0700c40592a010700a100700040070100200c0c94190051207115109829090404103a50b80d140c042d40c00c00c3c1c00071740e00400e003c80d48820070034262151200802091a01091110094032101c44842c0c015070090100402017a07061921802000f13041030b250341c064001c00c8860401549100142031800c036152071002c1d0001c000070004917407519800b0901da241e0141c440708040100650b03840e03000101d0b40d0280030a1a81c00000300f035a100c01d03001c2c654020f4580360503c89888c034000307090142c018001c14050b0003000c3d4203c0c017214002102c5054600b90720709050145d03064201011442c05030b40c0100258400040c2610030144500c0e04a01418081014442005000300199066a1040c002e55411200e80130113000f40745010302d00d0104440302040002805030000c0d000c101564085019989283d0108104840c06c0d6800 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 286811897 1250 286810647 286810663
    0x70b0309150906061f032310050d150b0a0909080403020405071b0b0a110c010b1f0807030504020d020409060b0a050d030801030209061c0309031b0b0a0c0804090c050408 74
    0x100700980503601e0300d800000c010030401d0f051140000e00c10b03039400c03032610b000340d010001d080582850344c1c6004844c00021f02d41c0c0001103581c0780d42280f0308100003482e070a11302c43c40e241741035200030701c10807c500c0105203c006022220001d030b480001103000140568551085810403030007410007070ba945007580144019528041c12450801c100c2c40002020841f80000c00c00c20242c4c03018501203551595440280540450b80c1c04c000140b00000d0105e0f0030000552040b100c1030000d48009043c13080c60942c03c16500c0508a0f408013140510000540030340c0b00f5800700fa40944024281c40c2e18107019004201116103071002140c40d103680303410140042c03400207040f00090204455081c040c0113030381c0d4018050003040c40000e004a80c0e103804500c1070758640340141d80c01d80800a00c1c00018610b420010400c42483c881910708403584504101140398189458054458009000d880c04001c00d40480d0080851002603818080038032000c90380f102c680c0541d070b24054003680c1d600d8546081c401410f00388144 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 286813147 1250 286811897 286811911
    0x9051504030e12010b120606120c0904030f12020c030901031b0c11120d0504030b10051f140d060609090204120209090c06160b0f07021e070b030915 65
    0x40080000203079120300384080c1501e0079039081e12507040504083d405440a200e24a0780300c903648111001d407000000f00544204070071a05409260708402489031950100c1c7d88154004001e0400a80840d000d442e803541040ba07107203055080400701c41101c034100c1c2c001c4080742c10a40c0000034265238a4bc2c1c940101e4134010341c601034000500e181000b01609003010003400800300754150207401c62a51782c072140380e41c81501500c25186a07e030f070070034004c040da40300c0d0004a800b007201ca404a02c2e03844540c503280702602e1000d400d000001e99201c0d40504a00c0d9441b5117542002040c4200842e580c07a28406811200d58180e00440c50506000006c0c10f0402160002c1c103041d40305200401900d1a00c400202145405031103250054466880160410405008141d040280040c80407840401404400d500354047e214000d425103a8a0060604600a031f58000041e44403c200795100c2e1800b0b03c203a901c800b05103084a0046a5404000b062034000f1a01818913800041541802a404c0b0000c140d201c40 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 286814397 1250 286813147 286813183
    0xa0501090b0a14161b081b060c090303090616230f0f060604052203020a060b040e0703030503060d1b09050f240a03020319060e0a020904020603040c05060d0905 70
    0x1d0403503139a0900304041111039003002283e00b1507000183c80120140101500103021982d103840140900c0c0302c200b44074419298510174000000d20a44c10071090b2403a003400107002d1490070300c80004101d616006283c20000303505403d10b40d500041c418240820700510003084515084242003141828041d4603640f014440d048501c80038140034001c51030941c42041100c0000302c03520f810000600c03045030041520305c410340c1100c040061640004000c1c00342c500c20035050115280705410b00c0199101034805408a81c01600e080c00080e00500180d50321220240c0031740115110f580300c01c0d4082d00701c0d0340b41c946440492201845102450b001d0303583c2c0600204002c9450b800d024102c1c0d0418603240d010992a0b201c900c840440690359482c51900442e001021114003940b1100501c02c4070039164011a84203280503103090982d1400301d42c02c0304142c0c00915a2240c2d54843d0240049070307100400803a112044c804d008a02640e8840242c0034040c0c50200000c0c0c0302045281940c98200d4420706161010 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 286815647 1250 286814397 286814401
    0x1f18060b0906121c0905030f010608011d03070323042601022502011716031a0a091d030406020615031c051c0e0109021903081b0a0501090b0a14 63
    0x3d80c00990f0043c20100007601004030001c491003150780c11500c0c0c0155926010301d0824265203141500140300751528400204684402140120810103402d4001c80307144e0028025440070901070901122003c11a04a580d08640002000c40e4682d104d90040a40310200b1f4185090301d00d101e6140c4103104800000071890003031072404003028500543d40043d00c030200c1644400071640714100d410030301202034402c006c660400004061700310fa514414400024a48400300d640c4909e1300e07000a8002e1b2000d04155076040c10108640050079a10448a0585005d0b443c04000c0f00c0c401c00081004100e1030707016105601b1310074034801c104a40c1c208100e1103580441022900c1c03114001000b00d01c0d1200e401d00030f640c0d0000f1415414440c0552808003841e034500203c413006240190030a02c5018403c07114400302c0003403141907401a0903d800090244c00040c440e01d0009080f02000485180c06102116032003400f540d551400e480740da542c110307026851502401904481801944202000800c00c94114 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 286816897 1250 286815647 286815679
    0x1b081e070e0c091e0409140c0d150207170408060103031709100203060103090c14040c0306080c040b01050408060703020d050106020303061008070c0206070f0311030304051f18060b0906 81
    0xf03003d0a03d140f44520144c00040c085016640d5481c1402007014000340003e44050a100c05c0840f01e00001541c2806103c00c480d0365850100d00221341141d108260300304012500c50345070002d40140b142200e4a00a101c00c91036440000c4003d40010944000105020743c1035180091500c011209100741c0c4042117004e00c1400000801c06001d0300c00c0c0ca0070010b84079a903002c0120301400406c4000b60034166403c030080341c00b944c1010012a2480c003030718184000c0310b803414200c080701c0043c800c14a90b0380182d03003980c1301e91078142c0182202d2344051402c01e04254a41c10345c98201030060b18204082580050658244034050081c9070040219001842c211300d0014045541000201f0440381041403907030000d04802c0c000c1502480d8640c0147c000b503103e50b07503481c000b081d241882d070054001c07604001ca240c0d00caa40000c11a0f00c00c981c0840503100c0c000009c5804e4210403601c010b130000043d107514684024680340203d61428074005c10000c00c4000001d010301100d80c4014000d075008840e9581d088180c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 286818147 1250 286816897 286816921
    0x6060f0b07121409040c090504180b04020f03010915021c02040b030403081803210a050c0a031e020304030c0204050c04050f090604020f070506090d050403020d1b081e070e 75
    0x4445818501d20781403200e2407203d0719103e003404065000d85002c4c81040d815501542a0b8261201560304000307014002401c03c1070041300c0c040c01080c141c01c2000040041c1005000310785035280c081e0002c244250941d880c01c0e040400500040303036a6a010030500c0c01400110b0001c03850f41d40b080006c40c907042c101301c41400c540c80020009007c1c00080400306407216607072007545404e90303204020780e43c4807042c0b401d00310118031001789950303403110a05000c18040e803802c1c810f00b03003c0d038203182c015890318400360001d90140800c8648003d9070b0385469000e19141c401d03400110710580c8282d0382c481e03c1005a10402041340c501070108002010148001e100549a0a00b10f001c49002214004416901c61001801a00c25405807824004000c00c140e02080340c00103001c1d00554048060b9100000c0071982115640141d201c00b941c49004483c4080104200c1e115101005403244141e0540740d8881c45150319110003003010078070501c0251740088000b24140320740d80181049040180260502c8076103141 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 286819397 1250 286818147 286818173
    0x40b0616350c0a1b030201030e0c100c1b03032d05030117030403080a09080708060402010215090f0a20090105030705040c05070b161d010807080702030903030706060f0b07 75
    0x80000000520801e081c004010624902d40d00c451120140002600b8080036007903130b840102e01080c02c207400006000c50108801d425131030b025000d03201e000000c00003168150000a0103031500141202d04103044281d480e441d4015600a803181c6080740e00c84c1d08450303404031030030700940c0500c0704031450915032a80c4082140d04465480f0381c1c000003040100034890540c800c80c1e20003007905000040604000340c0002c105002c0b5001042510480d945c0c6032805607c5403412100240140c01c0100c1098680b449429074507040b085207402c5402e0701c804802140e10f4046800710540c0c15807003016103561110541025034810b284217640e00c007455454100070030764503041350284070310441e1100c0440d0482da102e603040c0c45000da007290494a607400c002245c14482003030840002c0010741107641502c0d0407006621030417450001a590b06400d595030308000c4070701003000303854241180010004904295801c1028104042c05000005002c92030b00d64641e090340c0495210341c5c9164400d025000c00310b109203071890 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 286820647 1250 286819397 286819493
    0x5060c0316170c03090709060e060301060503030a050d1812031508070e010b030a02121302010e0603010518180102070b0117061303031a06040618050f060406030902040b0616 76
    0xf540300d451340000d080c00c01109410114469241c890000f40605c40f03002194002d06d401e43c004c02115448009140d168440c400e1100c010a1080118800d541c2140d800000d901d000ea442142030340764140c1d660002c160030345150a000a8907070110503100c4400c00d25200040145500038004503150050544000c081440b03051040000400007a81c40240b1390100c40210079051641a02403030450070f081c404407080941a40024003003500c00c61a402c10504880c16140c00426284c24200e40718607072103c07a42c008045014421040c00b4000041109001406406114601800003981804224500c203c80e400c80320009510202c03d000003808a04810800f0540514011039003004400c103034000b41e803100c0d0071a5003240001400049040e48500c0500303110749190700ca481269a64020011101c400108880d40940c0804c000c01040b8043e510403040a88040c00100b098421840000c5c03181d0800400c1c5c614105454103408204004400c048201000410040b0031030710b6a41c48040395400040ca101c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 286821897 1250 286820647 286820671
    0x8060d1403180901060c0807060b0406080d030c02030a05030412020708121b0601050d032303040b0412030c0e060a020709060806010617091c0e040e160f08030304081605060c031617 79
    0x45402e01c514ad82202a0720040507000b407005035941c0715200d96500900d0306070b400280c80c000c600b035481352003c01120001c4000b6070381c00d07045403116101c09181e801004940c030154402c40d4000104150305205492011000c80000c0740c40f80d041001e40d480075541103082d200b0300e82051005000990365080320840194242c40c00584550403905c64030b0700f030441c40070251010600407042004000c6103071000c500c0f8078450140085150803851040e8155001d03640064045001c08102d190941808030240161181e07034030441e43c4081d60313032551004542c0260403d4141d504080c00610046800241c07625404001d000182030515024506035252042c14400140d4400449614040300e0301c51401000c60500040042003400d80d034590301d0350380d01c5d10f0040681810500c01800614645070620080850b112240030314555650740e9610019035000b1644590102c00903500080400c904000092051130060302096503401c085a1011140860886030f03000c005005443c03041d403490707003c131260f042a00c0d0108 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 286823147 1250 286821897 286821907
    0x503030a08040f17310905091005040507050306070912151d0a1103030906031b1c140604020906070201030e0309190317070b0708060d1403180901060c08 67
    0x400000f00118a0150403504202d013002c1e501d181070b60003070488240c07000320401314512450484001e005a07100545096288000422604c042e0360405903112240b502a035142c01c1e104100c01080fa1011784042d542a40060014003840c00c0802180c2d80029503400c000d4140c40c903001c002084a01d0000e80140081f4000175503032201c039000d40150b03110b8890005810500c00d10711100b20340c0c4580c3da440603140c00b040703080e00d007042d414048111184148042c2c0b4072480c0d9030300c0b040000c207003c0d4002c1103070010304d004102840d1110030030742010f0200c1c04410030101d141c0a909030b03035446103a806440307284035034410000c2040aa4401c0c0840f00b40c2a428200403c41d070000b4414a420350145421194109800c0e02540042441c64941d040c203980c840c103048020100c45140c02001801481401490b901104000c00e000b03500a1a0305644400014411110702403980e441c1d09801c2c400c0c4c00d0319891a4800b0400d90340c0312401c040705490700141998101c003203616045005005039400080039000c2000028 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 286824397 1250 286823147 286823153
    0x40314010609020a0305091002031506031506160c06180306050402150d0204030312020a0503180f03040b091f02031603030209030a050601050112020307090302101808011a04060503030a0804 83
    0x48004003151801103443d1304203514050b000d0181291040b449000c1c000e00d0300000e078024404d0f24014262030341c00c81e9004446e03405100060740040c000d54032520a450300c0c01e44580d200401031116550503610f908140c9003602d04280c11600b150810020300c2107685a070f601c2d2040511044003240d805c060301041d035440d1030010419134000c80011000c0c1d00d03000120304003518015002001102e00c280d907028446551540030748102d0003408a004c0002e10100041056103a00d10304885401c58000e0640728a0400202c142d80740d82d00640c07004105004c04038007640d40d031500184941a00c80c006240107034454400d20029120320444283d1000c0310500030004040c144a42c0c10350b808210050102d9880c580503003070040e5150424031806002940c403959141c040c00c0c160007601e01501d8561503441c3e01d181035500b009921040c510a8108025a4100060b03480340c443c2c0c003100c0103280343c034000a01c0901480300e0416003c600b1452a005c2c1d414032004208a0b140001107582240c1189080c042c0c64075685 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 286825647 1250 286824397 286824401
    0x403080a0b0d0c0518060f09190c02010c14070c060305150a0801143313020a0809070609060e09100b0c030307090f030503070201030b030106080703032c0604031401 72
    0x1040350080075102c5503600f08510652440c090b01c0c401c98010508050048035044a0a0212005508400100005082801c05610780c94126008041003001c034065000d03507078211030410300501d006030f4480b41444a016000700364041c103007007902e109614045d00c540751003181c0325962041e4010955174000103002440082c44032060308000074848540c640c2e032034032060701a00c0c20f004107040c45041400416110400b14450500c85000e088800320564402c0350020002d014410032035801408142c099045940c05200510189078582c07114019410100982441e203c5039070010400c1c0308003550140029900448440b41c044d02c00c0b54045003543e501d9901c00c454110079440494080e6006c42c0c3c1c8015110003002842c0718080b01e40d518880543d8540c21406410002c1c440640513410420006000d540b10343c010041850001e0000300b122030761451101e180c0400c991080c1d0020f504040c421803074000c06ca200052040c43d040c4440c0700f441c5000005a06032103248801801d0306402c4048551700c040039 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 286826897 1250 286825647 286825661
    0x901052e0306080d020a11010e01020a030806030309060c030c0c06090a14060705010618050c040f09091b06090314150705070c0e07052101061202180a140a17060403080a 74
    0x20800e0780c0301c4c2d05501030065503035144c0c2d1710101c440b00316205646002d94031944c821007461760141e0081c030400c0340c16101075401100c00381541da01404100301e10340c195141c1d00c008080e141180300065648408124003582080031144500384119003c000445090b51401c414400782c502c0680040700700e408020005460384034000c4010803079402c0c15170000700003070781c0d01c1e50808010340c2110600c085d0f50340d0701003021207100354041c404496070f000106000c041e440d079010030501c0c2e100c2e40b60074540c4070201c5100005111207600040004a60b070505104010b5204466440030119a005051070040201d01c001900c00092125080040c003050160610002480d0343c0300901a80c098040d02e1300300480003e003540d02c40103d05110051030124203449140307c0750040e04985040d5280043c000c00004440040d40c00b0020b044407101c56a140c60040340d46107451400103142241c1c034042d001c400d410078004a0300d0154040c02d00302c1c17060b91008040d81c4001c10003640c0954103140a03022503440c0784100000f4119 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 286828147 1250 286826897 286826909
    0x90604110c10060e01240e01050705070e091603050705010e0312072102030a121d010e0105100f030804060c151802090c040b091201060e04110901052e0306 68
    0x50040000112a001c1e4000c8040d668412902c000c246c0c0c9074800d0f412001e40421048044654048209000a1082139a10010380d030514200d232070003015031521450b04440d43c11400e0219502008e1080704c950030003407010082100c0444506481c5180c440503194940b601c5010705000401004444581e0280444405902c0a00555480d07141c282810100d074110718101140e0005920f038010049400002500c3d181c80481d580c05542c1c100640d101400f5186411001d03a04684e6000d218080000a000304440034801100000326480e0100c0d100905001c1640300c514604070318401072010401e100210f8040c1c07565410031141c03001c1c8500d4900403005080180c0d2103040d02d040300174a52001803010060605008a031042041d03143d05101c0318440c4990720840340c41d69020400c0b0801403c090715018814040c03d40001070140d9524503030b100b40b00c03040700e085907025104042e074940c40c03404a29081c050307c010380c0c080056206048003666020a00804003c0c006030031740d0b00381d03c0350703200b40c100740c01400c0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 286829397 1250 286828147 286828153
    0x1120b0103060b12040308130b150f04090b1f050117060105040b0403110f04020408070e13060c050307021903050d0e10020f0d0b0f0102070506030c0c0703080913050105090604110c 79
    0x2d1000c2d180d1004441664100c0000f802800230070311818507849000441600090f82401c02d460b0b8150b41c160015440c50541c3c0c001c6640b03031803010991349d01d00c18000c1441c01042c02500600d44103070030307220f2004804103412200030516414061a41c0c040081c0b00403e0914801641e41d81300e500050303820380103682c429001315034001004030412028250300d103403500007a544914240814800c01040e40100d009111955000b000b041196042e4142d4180e0031001184201480000366120714080d10000e91609010a40010034001601c0d81080824060f0601020004c651042543c00401170300c1680140c03003015407140c07100003100c20240f0441400020218045580d04541003151805800000700c02034124a803554011560400c0c24002c000840160301a0844a080c0b00401003d078102400101c000b12040c0060520303844100641c002039406548942d844210000400c401540c07031984e0410345a090100401580d00d0701d1090540000e4120780c040340d00c00c24071442007180d024001c8001b441d44 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 286830647 1250 286829397 286829407
    0x2031b010e0102360f010f030e030309060f09010515040906180c1d06100318060c051b0c010f0f02121201080609120a05030402120a06050a0507030b01120b0103060b 72
    0x1105090210000c0000242d40c03903502041101c00e4130b803008441c07113213410400c525040c1d06150302c40c602134296107030341c0e08000030702d01c51095501c0d2660b0000c071116506940410240440011f091042d594407620130b800900507482c02d003489013003042034240c0050159440b141e084082084580100440c100c10210901410156003400350500c54140705007002c0c9143d114200030204074400041d442004064189140ca55032910101c1c01032215000c40d0f210030208584d13440001d240343c080d025401080d959010703107410001c40f02040e459a6076004c0b22040d400920b0024941c1d8002c100b149207500c00d401c1c41c2041190024041e400e01c01e880200d00d21074500020b0b915040001e5200d031318103845148080b1401c1e42c1e40e01c0b0100d135855814000001c00814103000750700722684580e005583c402d2000d0208140078400c4454079140c54082002100c4c656191000c000d83c5002c1d510401c0c1c0c2c4440c040c5000d00c40e0480000c00a00000000c0200441c40c603190100342603d41d00982000004240101c489a561 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 286831897 1250 286830647 286830667
    0x4090b210d1107320306010303080105040506100806190b0a0504090f050705040b070623061f091208091203270108060d03090305120903120301030302031b010e0102 72
    0x141c0854064180030680c0000e6601c0018400a0600161459007a140003a00b89490b03000121003048007003000c200c848000890101c0d1000c2c400180254429154035005504140421054690051680d0b000f500107921107006254005080b541181041e0f8141c0c00108600d0b0050341c1c0080c2c0e42d044180d039148009000340030160f00c840240708541184c030f0200510407107a000348d010383d4020b60f06000000c0080c001840070004c01802421610711030100051881c01c1c0000344248554004c60b0324807114018400c02405007041d410b064000c40081c0002e00004002407006800150180030385011b541d843c00d000c600700b1103808111081244000c2c503141180c1c20110107681d40381d00c03100e0000c501c80610044289480c100000c000d074001c2d41615818403c1d0348050901ca1024006101582013020030607001000ca4818000b554001610102c0c030344da41c50400050614050a020302803140541c01c200420200f40d01105480340001b1985000408091000308a405444234076a102031951000408807a0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 286833147 1250 286831897 286831903
    0x203130209010f060905030a050715090503010606033c09020f18010503071e0b070f0f0323030114060903070312020d030e16030b19140402121204090b21 67
    0x1201e000e45d031500039094a54080c1030311058048030042c030b59031100382c0a00082c4200075206003002124903000c010295900c00103801e4892503401040400e40e1044484502e0360303035444030b59400c0c070012840d20142003080c0c1070741402c20000031a00f04040da03d000c61411903442655035001075900610400c000740c44c0e5151980f04c0031080c1300307003446441941c030300240464090420b01008524020042c0259181402e8800d170f50303200c50700c06c883e50741c0c190402c07100044d60a118a05e0141c042c0e5600308045468074244c0c1646a51400341131080c15080c0010044400051144179410405031400c0e600c42c41104046032030040b0b140c200400300304100810505540c2d000590041803115030342c0901040103540e0846840d140e040d0120030400e00d00c2e440500100361004080e540100110415184503000341041d007044448210612680300d503034000b40010340ca8080e00e15130032a0b00702005010941d0940544004911427885003103142900d03116540c00f260780e43d81e05d040800e11840ca40101c0c004015180c551 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 286834397 1250 286833147 286833149
    0x406080d45050f0a030308040b040602070b090c040b030c060301180207120f030501050906030d0311090402070809030d02032104020d120c0605090d050a050306041512120e0f01030203130209010f 85
    0xc06000c3c00d4510008500d4207011120840e50036480b80c034081d80343c40d210a500408010416135410381c007081054005000c04d020a44280c9402000e4144170756443e04100c10349a075054824429846200a0030b1180e80e01030850f81101c09a4a08a0003105041c0c402d90182c040c08102401c212840903118080da41c11400c000d010000540d8104440da803241d0412410341d105564542d010f90290540c5000b10340260b0085038200c119482d8182050401c10014040c4d030301c210022500c0b00c10115400e4801d0800b0400c0a00540c0300c4d0000d10706100c6800d6108102041454a42c0c040e090765070042001c1d5150602c004280750b40084201a54065001c40501420950b400c02c4610624050000707101c13110214100c0b0b0580002ea82d200e20b000d0241108603000c1d0009048180d20603500e410545080c940049030400034100300301020890b03800c1d4201034640d05642c3d10280280800304500025a030f0b2001c00b03220080800b42401078694031010030380c00b9428140040250000346d41800860401c0d02d05030084 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 286835647 1250 286834397 286834399
    0xd020f040c02030d050a0c120f0905070807050102060109050906040320031810090503060a091a0916091104030206030403020c15130501020309030303041e080d0b0406080d4505 77
    0x8805a21541b1800007141d4507103185000043c10140480d14905071a040f8022400322a20302080280c00b81e22024200400340d03010f1620355005407420400c5503010700a45004140518007000586003424480743c0310500180001e0170000511413900c0c0384c0003c2c00100303084c0042401129100c09500400440349a0b400000c184907500c4041155142d034400c5010a042d210090050202c0d500d5401c0804080c003141c43d000c8030020801400b03c20010301e420911071017402c05e44010311f58000403c0011a5260040d04080d805504203032415105058481c12501220f074140e0703025a0707a58443c2012070410201c40d80450348002404903038240d005000d0041e001c24424448036222880ea40d000581c0c3d684290b500840e09074006100040100b1006607603556059008020040c48070110317541c140d13131580101420001d107507450310902c0701d50403e4491180a440c0503030050481610036000a0072101447c0444010041b03202044880004c1c0001000b012062070618040511002c0d02c6202c070407503041c00f0389 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 286836897 1250 286835647 286835651
    0x71208270109050603090a02040f0908030c180a12081c0c020d18060c06050403020c100503010806010e01180e010209030703030507020f01051201063009021201050c090d020f040c02030d 81
    0x201e25413800c0c4040b2409802d04400910345180c3c6a400e00024240e588030007130350300b503941d10a0700208520350000c5d4403801d44403081c640e0390b4800324000304a41c0c0820070740390300a03142050180318030b030f00308203404000a400182454940244a84010079000524a5402001d0520315180c020540004100070416281d4031010207400c816403541070300111038031480c00022072042414012440641c0020707080350080c410b030740041304124045580c0414400d1a00000f9030004010000c03241c0c14828139025112405c18030589516200001003c0907580c8020040e5554903041c00c0c0c01c40c00c09504450445030068281c0e20907a07038a0a0141440e0410395090f400f98004201c500a25071080341100da16401d1000044403603420110112070b10260001c862103080420800c0142e949a000c51140c0b403400350f0750021a16841a205200c908105000c00303105582c1000d092001c031145000070740d00414025514442050850f0000507881d0008040720ba802a182131905282c2903400b000900b4030305504241 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 286838147 1250 286836897 286836899
    0xc06240303020c121b0d06021908041407031205090a3203030301121b09020f030420031b030307021e030607140904020703030e060a1d0609071208270109 67
    0x10b00d03260f40da0710291701d01210407059208101c1c034101c2d15056207117018020050030f00e11102d40c1c440484082824090100740c0c200204030070040b00785120717485103030004c0190109928540d40c0014142d0007142d0042403000c0451030f141c40e0386440c1d042a0042600840303190303400c25240d520018050f01c0506c1c40380c0c03c00c110310388480d59050000031281215074040b00b00380801441d0303d8047e0040710111100542e10480b000c00034880455001030300e080c56025039031039901d040c2460540310280c030303424a001900302503401d001c001341d0b8042000c503146130341d02e514030f6001001c070b00010b8110b100d000310003580b180402d0050b445030541500da41e480b100043d4101c0f071594690f040c0956a051200003e840da000b4104081030250510f40c01404115200b400d01080c010140c5400a00f0700c1c0c0100c8103106542e98407075038514040311035909190348a11413005400c0c0707802c02250490700c82a15002d421859403800b402e210030815104210390310100e51100404451030354241110001c0031001d400342c005034641d40 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 286839397 1250 286838147 286838179
    0x3050c100603150203101703120a0b13050901090f0516050d0b040303020f091206090d0e090f040f02090106091d010605191808011e020301060c06240303020c 69
    0x22401d02075a80048500f51080e0050b0404006540014000e031100c03000c01e04001288404090017456800b4104084c0d40c649599103440c0c1c21240c0300520150045041c00491929915200c0c440c003989040e105001c9000c1d5100034440d030161003d044010300313480d029528103051100114000c00500c104000c0142516501d00800181408803076019103110031210124000a020b54005c003005441c41058030301f08010030300042c806a407100c40020864102008225042c8018030400c14081110306050608031544000705003028002410b420f004a00f450114003482460540e00d11450360040a056941d80c4620009040c8143e901c0f1310b68000301c1d00100080c1d122031005050703040c1c8080e0395906040042c0070440c0407283c13103600c03402c1050103000340000c1c100ca5108078030034014140300c40001c940d04060f00d1405d11507885203600c400d81c071071040c001842704075400008842c00079042400032460020005547e201015119005c0d9122010340d140041095008901e0001c4620110381c5e002000080031 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 286840647 1250 286839397 286839401
    0x307060807050307052104030c060b010206100e040f08220522150504050106031d0706141e070f05010f151205031902070812070f080f12010303050c10 66
    0x41c840201040d0144009034101d440341000d0000380401074040004030080381c4580101c040e05071000c1c1c0c00196103048000a10025026200320040c081c8028101d502d001413400126145034040c40c0200941500490288084102000011a0481340c407507aa0030742d8000314009055101c50001d01b4135900240026103251008002d83c4040b51710040700a100e4010350f800c3c008018003400c1d0a986c2400c040302007281e8540c0d11903103000c6c00c120744000a142c1c1d9250402807506c000c43c0360340400c0c1d50003920107000c40342d8000d040071000010141c0c01c544901c0001704860316082e00503038007500c020b0046400001e02c56014500ba40761070165008101c0344190404031000e403030b040d1690380000707413210504000c0c0004441d40302f61558010000e403401c01c845080005a42401b40200f103005034019001402500411300490103140469012140ba12503140e8915641446640010300640404a41c541d0b0842e5002c2c100d624210704512207a0b450342c0c403071401070326641005400e4405072040c00e1450005614038 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 286841897 1250 286840647 286840651
    0x5040206030c0304021c051b3a06020a050301090506060717030a0e03071217040b070302130806100f0807120b0702010209030f0604030201290409030e03160503070608 73
    0x600810701d542d460044908580c0d20151040360000c0c4060243e4103500c0f01e450f00c074005507100384050700f0003858121180b410b5000d00d0343c400784074a4030740e10465800790320500c1d111440300c0b0350603191000e5600c0142c241020385a0480107070505000082c031202142c0e1000003541610440320701040366444000c1440240d0040030002030900c405003202c0f02100020102075544886020008201c0e55000c14007641113400c4080101c1d2031107107008140ba007d68011001c003440124206101196242030b850307400d078602c4003811442c103041e80041c10b4205441c500c800003000e40400700c111149400c0001c0d01c044400218411740701d00e5034403601c01040218003c103c2c01c00725803130000400d000210f0741e1a02c100d0004068180f00a5650030040d508083c0c40500c107840180c9524400b50000380303800c0c00c01034203459070300555103040c0240754040d190641c1a46101c03441c1c0b0030152400100a14945821b0b144c5055018440b549880b848400000c1702c0070401040064440c00d5064492107030381c0b110b003507a5580701 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 286843147 1250 286841897 286841899
    0x7050f0706031e051017030904050601050307171302040518120a020a15090b07050a0e0306010302090f07140f0d06090209011b0f020d1109090a08030118060807150909050402 76
    0x500e6012030041d0342d903401064120700505030305462295101b2183e040341c2c0da0006200c02c5c030380000c10142c1d6540f41c54403941d5070000c070030f00300249503181650006181e0468034401d0307025204110b0100d060001d510100f800c00c19409001045241049001481c0780c0c0a007c2c01078a0b18464107076900f580065400c103442c0c1d5000b0640040c502c03100c0940d070b600e524400c081103520400e9559541ea50210341030008441c01000161101d641d42ca0050300010710b0700e5000c10303c080c041c0d03020307500400c010384580d0b00640d80f01403010b5090301e00761200c4030200c0e03100345045515028060049000130829125070010b0183d1000d080081007041c3c3c1c5c07a44200c0c140e005440200f80456000c0300d01d4450780d212115030104507031048003014108000740d400140c10340840d40090b518410001580005810021503d54000f1003c40040034000f1465603642c0701e61005000e101004e081e503100c103000f00b6020340c2002000d00304030029182c5041e103a2407404150594290b0181c000f0701c49840009010307006104043c05a50 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 286844397 1250 286843147 286843181
    0xf08061c1209090c120b1801230604060504061416081b1608070608090d180e01030606030201110105040c09020f1e0c070e1006050702010c02040c030501050a08120d18050307050f070603 81
    0x881d25a0701150302c0441d5841e0b16500e03000c9c40c1d060003141c0d108c1c80184007074041d030b841340d50700d950520000800d00001e50190102d606000c001c8480350303c40102008a2040d4080084d41c8d41e0100d0740e804500d455150183c80100d0720840541c040c202c03104000340c9080d5000007044607101641c800c0100c1c1c1c17112003680d107207441d904000c0607020098810b041000b81c44085072403c5100507668000c1c592002e500b6441624500e50b10b0300248215a401506501103040010086c841c40c00c0c81e0700c5140c000800c074424941003270b5001852500d5100d034103041d02c0c032001c1e044400c560500710f1060b003d80c01d0b9012030002c0f51140215080410003244042000703020700d90100003108498104042038406500c00c403001c1e070600049900003001603543e4095005100110340e4003042c1d5500d0001404100d060325000904190059442905508041c0341901d034404145000482c0a603804401088141c5c200d0801a0041c040080c0c100300380500081e40d2400307014810f007108d0752190341d80700c100d00b2541d061503c01e030010 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 286845647 1250 286844397 286844399
    0xe1c140d110d08150f1005030603010b0a05060d1d0f01050402030c030609070e040c090e0a031e0e0d02060d0204030803040c15080a02070507050306070f08061c1209090c120b1801 78
    0x181329008011010310000d0f0200000c41e000030300041c04003100c0745414000420000411206080038010140c0a060030713989082420709003000298140031b50448500d0792903541c592024006c0760404c071708943c0c03030050381500e18000200c03400f14007820f0304490683c003a03c104007946145040005850b4491070004001d0850541003044052030f005000e441910088081140490b910f00d4070702c40c003414404d2080c020010111f0b50328014002c411b40c80406052440108004d00b803064003e41e84090038042242c0144440c28540700084d22802001040e0b102d0358030108000c030810480c0b600450040e402503c800448a0b0348ec4a00b1416109200301d8400083c1400f0116071140306c40d401508400e032145040e0b900e5540c48001103440c3c0310040b2075060010b41c3c0d00a200301115000380c1050382103030007580c8000c002605901c50010703ca40b0903c00404402814641e49001c03880368500c40050601294140000c0b2100040200303450b2401d295085001e24100600b14107107842d015500b44070200102902c410707 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 286846897 1250 286845647 286845661
    0x3150a0b3c030403020a0501021801200c0409021212091309050c04090f02090c1b012c120a08100e13060507093309060e1c140d110d08 59
    0x7604081c0044081d40300d00700c46d070000a0828005488012441d00c0c4038020b0034660000105400044c410301e2044814030400c00940e00b40104180b0900c5c4400d0b10301007024001d0344046040a58950403a045074010b840b01101d103054488014030840004440d152109443e0145150031104544001442c503406001810fa40f0305060300030991180c0152110300303001246402003499481c08480c00790542c940007403201d11400076019401d01e5050b02800030003a030b90301000a954100711302c00d1041284040c1034103481c8014420001d900700015860240354444180800182c01031000b50b0700e1154242004001050801402e28614423031030f00822090000708080d1658002000080d0410042008a5101040c0c052007020706a51450103010300348462411000d0031140e040c010120401004090001001002c2c1d100e42c14040e4010221a110208445032084100200109100030029440800214903c1c0f00208030340f000716240340c035804c100c0005200c07903546981e0800000404103400380301090035 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 286848147 1250 286846897 286847017
    0x9030308040f050105180d050412081e0c0a02210a06150503030408060a050a05040b01150e041b0206010b0405180a0609090b011502160b03150a0b 64
    0x80c06984000c2650ba81600c42030300395141244c8402c4180703401e2007402c40c19001081107418403842460240c1c103050900200d00504208204098601d11000c5600000c00c40d0710030500c814015940802d6580741d2000014a8880002c01c80a900c80d074a40e0304c003c0003a42484000c00f41940c203400140400720340030394624004162070400442c4040052001103540e884c100018405002428011322180c03500c000c5440a803040142240002e600700b00c00c1c0b00c0002c981d050000d042d01c4a2110140ba03000c2400d0782250341003482c00c500d0307500c6410701340c8884070500072410f01c0b1140580795007a289141e80302c00054429126130700c80d0542014115030140000a00d800d1802d40200140c00d001c24000c2d51180840240c3c1e842c244248d41494041004011584404241c1c03104401036002402900b58280382405051030684181c1003c140c0000001e96002c244004079219140018135500086403640040e00c40c075000301000d8146110004070300c20089600459200d140422403001501300141c207030000103 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 286849397 1250 286848147 286848151
    0x20304121d03030307022b0c02090a0e0109080a081e06100302040302040f0204150908030904050a0b090403090f0f080a171b15060103020309100e0313091d030a09030308 74
    0x75038074803007010700c5819507040c001540519a642e0003803100342601c40001042c46151303169000041900c8a4490009401008a400041d011500c2400d0b0341e40304002c034000b400003046220141e501e09020707002000180c9001e003034940c010f651810455614050b800c82812245a008031a00940000040c01840d01d2840d401d40c0e50302914015040641d0307940400c2c2541c0203036903c0309803550003050600c5419001401c1403110101454207003c09403138a0031103500c0b03105d0901010302a98542000411030310a17504510304050029091420b545004c0c240244082c2e201d008120603442100000103103000c03c40b03c7e400c01d0b02e81d25000350000003407659900201c0800304a003128106800d029080f4400c03080e1031000c611081c01e102801c088070b0800306c2008800c0300100202d040c50300c144240083c444000600603d40c02858a00151245240030090328600601c4501d659030480520f0108503007034550050102e00a040e4529184205481005500c81c050600000b0002d22819010001310388500c003044e03 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 286850647 1250 286849397 286849427
    0xb060111210d0f0c020111031003030c02040902030a20030d091e0806040503090319080d05090319020106090501140607060203060d060c0c1211030f090622081002030412 74
    0x1e4900503a0310402016100c0f0442c1810580340d0360003009a040e502802441c2d00700328008226440c1d40b8206245800c0388a0b01e020217801c2088c4051070740115240c690001e01c10940003011a28510081d01e044041d0a20080494060106107020346200381000500040c100780c1c941c4982c04030b01e0401c0103a22601141d125824a482d01c40800091941d40501c4064015405200910380e81e8001d4403e06151500c200e01d109200503680d142d5201042812080d529010900d03103002c501522040c418038514001c03007400741661921420141803594055000c442151504542401305a90701e540d80201c6060741d40902d60040410054880014426030086520010040040e13007007102a031a0202100c9040c240907011401c00340356042840244100788156110501d01605149100100c0c20388078024242c2000d848000442d52124543d500000c0d501d081d001013200b02e189000a82103006c00901a20520245004013001004002401c1c02128030031a000002d80b035101c680c40c2800c5514802c411129 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 286851897 1250 286850647 286850713
    0x12011e18060e0d110c0109050f1810030c0e040f031812030504290f0a03110309010903090b07020a1403030c0604030503070905030a020a0303030203060a080601030804030b060111 78
    0x40c0000c0541c0702c2c5030140380381c150040100f5014014082c000295804807105264031035183c955441c4c0e030119011003524425940c00708004031031004119040030b071902d98403100d03c50204100240e05150411012640168603000c0c06682d11030400000440c00d4402528800000e003551000c01e0103419a010044504001000d62a0342c1c1d2602c00d50341d40422804400194001504008011026901041d821001014440d01c4803850042c2c50103441044200e10b80c4d80404220b01011a009500a942000d403000505a4030314040c0900c41c020159240114046803500c040414210f01c041d0903a58201d078013030b0207444050308180008000703280e5a06002d90500c410001c4406d41e00d42441aa0301480c1300352900ba4423420540c40c0a41040800e8111314040c0c0d006001170000340c0e44040a03002140e405042c010781e06d4450201041c40c9401c9034005090500c03d8000020800c1460001442202d0140c2c6150b05507807510001140c00440f403040070b0703043d41d010200d2200070905965800c5103600fa0342c410 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 286853147 1250 286851897 286851941
    0x201031d06090312011e0510030b0904050d091e050d020409060e0a0302060105121c091a0738071101060806100f0e0a0f060317070212011e 61
    0x81945004030450307221000f6080455414104108502440e014103501c00d1064840c40840f8600d90a03080a4840e5520400508000000303003400b0381d12102d440d80010b840d51009242c43d081069440900662620000f5030a16001420745011402e0f0700c80d104a4a410b844468540001c119482c03624440a03688207a0350b0380031070005981ca216416072440c10f80d000d0a903030b81043c1006810030304140d00042c051381c1c03482e92b580d440c2ea80100c5d40f000301c5a06010801c800000040040311601e615403c195544a0b20401503c07603da840380c0507041191088000101896804102005415140209030304400c3d02c024507658040081481e1070380406d1500c1d213852100e9016261a00303507000b80e4401c18241c0c201100744140e020b9441d10709805801c0c9030109000d0035280648a10480f00001c0000700c001d0b903182601c080b03200103074205030300941d0000d510881c54203c012540744c640e403000c032080780304680603480c4129148042c0512a4521904045100600100b20314840a4071481c2488030700403640e601 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 286854397 1250 286853147 286853201
    0x30612031202160615150e0d0501090503120a050c09150c1623120303040b04050a020a091a0d050304180b060c0102070b0c1303031209051b1804050703020103 69
    0xf803504032083c003c040c04645044488104604000c15030856200c0c07807105028991901d4104003100b02d0f10300c00340c55081d40c0c1400c0c2d08100703005145080c00185a03000000f08e0f481c0541c2c680007014010303030040710100001c9c2c23906003078480213100c0c44a9040e000041e01c8201c40c00e40103000050700c0512030000a5a00d51450314440d4500c4070802e40080f45c50040c0b0326040052280700002c1004002e20580e01c46d0f500c0403400c00c0b41560b07808001e000803d0359000c4400101005010703c500111164085e0640d5201500c48100780d0142c106801040494001d0100303041c0145002c4d00d60300c50040c0c009001d90300d0075040c20038036906a5040c45120810a86401051249446e40002408220504400103888280e01d01c0c100101d1800641285100c20040c080844000f081c07814030030849900d406c3c0600660042608000a0f00004401802d2800740f001900f04040c0704a02c100c5c080b500c00c944510442e0880c0104003601002a500a02039500640c01400107501a0340701030108020501c00000c5031102d50 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 286855647 1250 286854397 286854427
    0xa0509191a01090c09080102130911040b03070302071403070f060f090206070b010603061d0c0315040c0f110106061709120c07140904030c0b04020a05030a1b06030612031202 76
    0x2c1d011600c00380e5110904c8910f43e0f84040c2d071030701030700c2d80100952528019003814403a11041e0b0141c1003203e80e5a41114001c02c500c1c0003100d00030015200304503140e1502e04406802904030700000e03100c060319a03840f2001a01c000c01121a042e6101220400d042407680742d8000614404100b035841581e01d07200100940d407540c0140407220311a903402d6070b50703604009004040d07960036030150030a0010607000810314001e9055440e8072520f60070449481342d071040d1150324829441e4900c0c54020b031404507a03410080e8403c108800c9071482e6201d99400c0456241170074200c8400d40304070b07000208250101036202d190345d9400b5800c215800d040781c10140701154005010740c001c444081c1107070b2000f038040140b172032903001011215008550f0f8205525140c1c602504200c0c01c40802002020030100013421580e0b148425409400c1c0501100d454021601e0200140081c0e15114401500003905c001340b101e219000d0201961071904814500b0000c0c0e680c280ea280d034410a288011035000c0c0310800705e44600d4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 286856897 1250 286855647 286855649
    0xb09062d06120304120c06110307080901090b0705030c06150d03030b0303040305030a17070e010c021c05030a0e12060709290a0c03030b0f030304170705041805060a0509191a01 77
    0x22142030b05040d005c03858072245004043d840302090185d882c41806681c080482030f15085900500f5a0b60f44001c2c2000480740745e440340d04419140342001c18070401344000000039116000c0c00f40200e80d150f4903490240c0b035054a07510000b65003ea540710760078001a200c2d810005100d50042c2c2242d041549a0307071020309640140740d14100041d2445000002c0000041111b60001070505109200e60781d4400002c100325031803d0b019006e02d0b002c2060040003070081c3c90700440c0350b03003180070b50351074007441c01c001481c03c1ca040030150312401a4820900c034080010a80320302800242c0c41c0c151100b80380440031400c0c136815032185411070080001000c80400b040c0010007100700b0594031070306140b44a141c0030707040781c589401031809910328068691040e10004122415200165142030360242d121181600d05111a041141c205082801c6041080741c0c1c5406041c2c2603109a09072a00ca90399200350f0002c446089440c3c0e02558003001e2010030701c0f03c20b07042d2000001d000e580240d6074401008541003041d602 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 286858147 1250 286856897 286856909
    0x6120b040302150615090f0406080d021615080402031204080106030228170f010f0209121204060807120911010225050609040204030f0b09062d06120304 67
    0x14280811081550501140c5902040580104024101000402e1108000e100044c0c0401d0300091881c650350346100400140c540018018406c1544520515840390707101c82c02c541c090b1007400c0c040c0d02c07a102d98a050b542665010910035075010010700d82203441b03040213802a6014001c1d665078501d012600030080020700340000001c0395846c55031042c0014140f04044820021140c0148025181c0b00030520004452051042031a0f10707030a80002d03428100415040caa40d9864100a01c0c511080c5401030101540202c03005070031100318040c9035885400c000c5140e07003003600030082444485d00030328027140c010300c0d03518001d0420403420f01030408451038480c003558141e24140300240b031503031b041200740003007121181d210030742c00d40c07050a1403245c00090085500c5080e011a007045c940c0c0325a03059600071a00100950702460352414010300e203400c1941c00569502a280015500e01e92602180041440f14800720b40701803030342011401d01a201616060307000b02c0e901b40c00104a10100050805000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 286859397 1250 286858147 286858163
    0x2030c0402030c040b0724230c2b06080102040312050a030f050a021207052106180f0403020d02011122091d070503010506060304030c0611030a06050f1504090f0612 72
    0x2609905406100200200e08003400c0507840000e01443c503c1c4e032031401081003001e0529844006004606005100703282c00421340d030032440c4d054849840c0203240345a03a00d140411800da200c400e041c2c2030340311b14040903042980474126554014421002020002418980080c032a4003074010b400541e1000d40f80202455004107000074150004d4424540004450804626000300008000391001041c01905240300603000083c00c507880b04d28008010300e000842034012031501482e01da07a0540c2c1510141d00610442800031003203401485840d04000780d1038511802c20740c40b44100e41c800744044001043d13000034200001081c0b5228090a0038a03411a2444001d1581c0c2d800f58510b003d1040c0d0120344a60705200034054a600c5800031030360401d4044c0b03001d0012108a0400d40050403030880d00d58903008000041040c1042c040e808142500d400300c1d055126541801d041001400c0000b407840d00403030701000200300307121160340b00c180c0f55003c0c910040f62a95580e01c1d01040400450b009449010b = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 286860647 1250 286859397 286859423
    0x21804181a16050d321807090b0103020f03010806070f030911040b040f060905061302121305030c120a030e03031b090d0602070f050105091203160314040c03030e0d02030c0402030c040b07 82
    0x40c461701140d6502440c40078440060581003507031150f5983c440c1c031501a44903a90303104186264480d404584100e40302440c403681d2380d40e60b0388500c0d584080880303000d800140c1580350f90404502c04e010703045501d608624070207140d524241c1007000500010101e01d078071654410700d10040601d14005d04005001411001585180500500c45900e4400001450051040103400d003000314800950341c00110000ca251390305015890304130300d035210380190f40c1c10384d01c2040f40109400301042d0041c01046032564043c024620303d0610300d562400203481d030201c60040d800b11104041150030280c4034124005001ca040c0400a448200c1264002c0105030b80d09540f000210b03080c4a824000e242e000fa0380d103402083c1c5604954030700c0b519400301501e00c500300503c04401002207407182e00003a802c51010403410043d8103081c5024414802c2c1880101c000c2180a100381d110b528213010540012134000d0302400345d607001c250401001b50701c010054070042c5800d201c041443e101e070901800c041441901220f00c21 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 286861897 1250 286860647 286860731
    0x10030b07110f0c0105030c03070c0b040c09110a1b02130f060816050109060e0d12020607080a0506010e0603190c090603140403090306021804181a16050d 67
    0x1800020b0404075075201280032015664404204c95000280c103800c15100d0300e1310390040b62400d5442c00050a0b001810080c0401c0c070034042c400d641143c05c03c2d41c040140c0b0766509181c0301d1900030301c215107002c01c50612185c2d40241c0e4848009000ea84002d101d0182220b8005c80715086030851801c0c500c841c0c1c0d84020038001c00e0020001c1e488032205224080e0921440c0c000001c1096509014030b0040019603510700c0400d841e501d0a108103241d0000540340700c4004000000d50b0350404940703400018071075101088a0504c0d0307100d006e00400d4103940e00410b661450b014440b0582c0090705400e2040000381006030300580a126050380031040340e680c480c85601e01140101034030a2080e16510380b141510a00000176004a15202180d60111000d40c4030311000d0422083d0300703484444240c200341031803000c0009224030480c10260740d1086c900e030051504c03040c0c011100344604840c0003111030800e5404d0316038180600098581c3c05910300340803489040400724494125145107005000c42c0115503502c0308 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 286863147 1250 286861897 286861903
    0x2011a0906040504111c02210705150d050f06040f050f0a0c0216032a0b030109110c06180118050c040914160e071809020a03090f201504030b10030b0711 67
    0x1340301e11901904540e4601d89235450307941e9803107818400d0701041c2c00207280c0305288c8140c039001c1031300f90030406c4989002807441c0c00c6c0010032940310b84150b10740312089041440d24420300f0300400c0110000416a51111403400060001148000c00d5218034104000713104541e5898001840c422070000742d0516410403001d1700d508400d5003046030f80784000d0017444005551402d5a0440e40c1011021074100b2000c1d1400000d4400c840025041d800350000b0005420329501c0000b01440142c80200a00070819800c1c0148002d4114024000c0d0041020040b0030314280e0030148580e40550300301a00c00c3c8542e100342d445c0810f0007500e5401005050000c02c0104a40000e060b4001c4490a010111100c8e20440c140f0160303090151a83c1240d0101c0d4507170310148645d000308142c6901c450f041901c0405030400fa07a40c90031006481c58040643e403000115420965011400580b648284034106030071980d84c0c0841700e000034944c1c81a0103a00000001182c203902d1400c0c003d0f141e03a1200385c200700c488041242 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 286864397 1250 286863147 286863169
    0x604030b101a03090c0616140d11010b030604060209040204081b0901062a0804150525080f0c01021c0c0305070509030304030b13020312030702011a0906040504111c02 73
    0x81c2e03040e05200304188680041032003841d080040b0f40d1280d503241508005045070441d5030300600358411307064482031100390010b48015030b50318544600030f18030219982c05003656285440c040d0181c11140224000880c150003400428600500241c20f240c0c503030001e503103040b59a1324200f98050041c56544420304083e5001c5000d07016915001020b00710710680905a0720044074404450308a0b1640101401080015a405031251541d410b00d1110080c00061007504101c41d0f4696140001c40e4148180088000d4050002d0b07001e21241c2c18a00d21480d9101726401001c942203465400f00300d003840b00c129400007515491011000011614217181009080303c4004200e8401d05c00104a81e0355550b500200360350860f07501075410301442d80c50041008010140850081d050711031500000c0400c0980b80107184201c005900805c2000c0561407a80c04010301c00e42078540020320400422802c0c1002e8100f1035100d0700404c4c900c02c0c0a422040410024032001d0701b500000c417610102c1c8001c501d44484442 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 286865647 1250 286864397 286864439
    0x40218040c050714210703020705101101050f16051c0f0603050c100e040c02011401260c0f0d0206120c0c2103070c020d05010f0501090b06070b0a02090604030b10 71
    0x4140c1c1c00700d401c0305082448117010b4205c8080008039204003014401c011328070252034044d055010140b2000c002920111100d0101201c55003004005010142d112000d00d201b0441802d00c131070308405985094605a008048081055140c1c41c0240c0c0c9400d0707103004180742c3c01e0060000140d2a40b82d402c1490a2031401d215843c882d0040306821884d04e5480240c07030716040760480d000261030944400c282d00600400840c0010b00c10312800000e8000040d5090107c00240e07419598418003202000030740750304203020000c0e03100c214869082c25505041d004104418800b40c80c0794540034403869040d180302c108807504000403000044c2035070001c0080c0200810014a00c44120310300c0c041c04d400d00303c0e41c04024000000c0140f50300d40c030070555458408412045d600f18008104030b20005164201401007409210035490802071b200ba403c0c10aa01190040341e003002d2101c00c1d5407917000c42e840183d8007030800d00d40d008406000c040081980f0341c00b424003c8505085106001d0b2902c2040c03a0b0341c83c12040b0030 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 286866897 1250 286865647 286865653
    0x1e03030b0105120a0b040209090405010506010f0c03050a03090602090319050c010203070f1101030908070807170301080604060c02011506020102030103060b060405100807050706020c06040302060a1a040218040c050714 95
    0x303e00f0300614074000350408480074021820300d0b46400460005d001d1200303000d921510740d4041c0020b2140650006020b10702c280c3e1500d0805142c914195804004180002d002500c01c00480040314032961000407440d1140314007628200c1902c000070310300340702c0304880080e10203034800b0300082100c104540310203102c003070014605158094030b50078098410402c014014030b001d41c0780741000781e120707606c1050083d0b80709144a40710b40040c20250703041c0e0811a0104e8103200381d04d000134003003040320b02070303a04032000c4600034142582c4984d00c24000e8085140000306540d02c1711645007525840800c10030250100303a000607143d41c55801d011007031b43d0808550700d0152500301300c24440d40d1605130107054a10220300701580310340c175580350440311485440b030043e020910108403215182c0020443c140200d020303900b16845a200c8852180446800520661066130385211003d65828a900a400040d181880c2d2002e1141424007142c03d0310509401100010000a0a81c041011406042da07039003c01e9001 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 286868147 1250 286866897 286866907
    0x6090f0106020d03020c15040b01150302030c220f0602280233030c1908060906041814072606070305131a090d1e1b1e03030b0105 57
    0x2e5101d402e25599101015000604595101810840c0c0d92103815400569603003031500f42800f07135151a0a00400e4801c240200ca901d803200d100703000b0703280580c2400d0b0701c0c81d00d40110802d400d00102d10192007020040002180001c9a094a845840c0140840d8003c1d1007084034100070814004038014404103a152171900c90805a08c0e603201e241151400722400e040d0490341d03940145401c075181910b604403068000304005104039260098182c41041030140c1094510780388080c0c2d500f0008403581070b0000c0d1580006012480d080d0006092641d441c2c1008245405a8513583c1c0883c0c4900000d91260307000440c100070685903182c09440e040e849140d002caa000a0070941612208058026400c1540f2080030600d4020800850001c032540100090f038240c0345103034429a03c1408945007917140c050152030034015070103460030b0548007240c030100201d81d084003c41030341c40c00495082501946000c1d400c00307001414848469421540c104880c7d03040720964600201135076000e0345058108202808 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 286869397 1250 286868147 286868159
    0xe0d030603050d230c0109110301200a050708161403070c03060c0302160b24152b050103110a03050c0103050718030c03020414010b03040605040318030302030306090f01 74
    0x2c0201e00300e0f5061400018600700c4e20180b9184003110101e2901001c00010107510391941503112041ca40d00c83e00c4541c006051f068100340c00c07588031600b0300340f460341505101800d10380c0d464020304d543d08050400343c1c1844581e8880008130703008860300c21145407a0039400014030080781f40c0f01c0e008102100013146000a2642c40607110703032032444001d20191b2181900d070f410a010381c0540713244c3e101d8640300d84038078001030401d010170071003d0b160920715448a4002103008050301900214854001c0c000c200342c110790005a03000c03079214262980c0e01c0198030102c00c005400000000c20801e03280c000c0881d0035411420701c440b00880b10301c9020301c16504854200001000801c6240f90000242800101030b80c451304151017407000c113600d1112003101180040204440000500d06032070003600c0403c04010032042c41c81046c1400c0c052a1440f84051001030700190f91500302c04d070300512901d42000600d6038200398010b101d100f03810450160700040304100c010b06140f4601d0b94403450700c003407904803540751503 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 286870503 1106 286869397 286869403
    0x201020a030b01110a0f08090607050a030e04050f0a050907031209060e04091e0c03080d09060c0206250513090603051e0601050904051504060e0d03060305 68
    0xc8800b240c3c0d48113200c40840c0b103115500a02c12003280e0385076002600c0b10b072001200c07100020003000e0310f1030303c4076005407556911030402060407900902d009048171001d003a03424000c1d0318240c200445004091680c42e0011305407500041d0030344500e03030a03504049643e0405000c010202211824140c0d21107202c2c400c07035855030f5484100001060401c03082c1e4110440150105070080e158510042e02d00013440c00c441e00c190700c407400d010387d40c0d40c03030a08a40095106600a9135108204001d00401d4002d0b600c00c14500d101504c1c00e0314245100c5640d001c2c855240b21400000c1d0051044418010800c031007407100480c41a5a28581e640311807005003805000494140c02100c0c1e96400c001d409081441007900e490010300541da0804040c0b00384201c0c010001d40b039500c0365890702c440041e10402c4480c0240d024050118002d9845c40d069481c4c0030003840d48104261916800b000031070808 = true := by decide +kernel

theorem cover : BRFrame.Cov 286690647 286870503 := by
  have h0 := BRFrame.cov_init 286690647
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286690647 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 286690647 ≤ n) (h2 : n < 286870503) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
