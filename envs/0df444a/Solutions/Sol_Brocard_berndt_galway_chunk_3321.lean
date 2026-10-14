-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3321
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:19:06.621547+00:00
-- url     : https://prove2.me/submissions/82d8b309-839e-43e5-9cfd-2bbdb7d5e873

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 597122302 ≤ n < 597302158 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 597123552 1250 597122302 597122333
    0xa0c02120a030e06010e33120102190e011d0a0b070507090f020304030e010e0a090e12030133120209060904140f010530070515030105040c0c0f 63
    0x168440030f07401072045090110300e0103032140d1007003090309051510080d9880080c8044e56900400c28003040d12007080043d5451000d030004803251004842001e11450183c0070303070942c041c500340e032003000c80c1c4100f0340018408405403400c7e0303030f001c20712540450006068805445c40c1c80d080f188444081c0030b00400ca4004205060060044038405640c071070780503085500705035281c20215808024401019440300303604240c024240380c06100c0071741150008810f280d00340304101501759500400c80352000c00703204030400300311000c1c60191650b959800b020b0b043c50a40c02ca00103800800c2201c070804030800850807501d58882d07503484510b0b44005190700025030081ca140d9511600603c4071015a039600e005400800f0710b0280100120f0902d0542c01a185c0340c180c024a20800380401c01641044408552803405003250040d004000402d040b01030810b00c0703d4000d10703004442005d070142c11075240c800a6041310000e540030070542039140700c00c0b180c4008004e0002c00d100c2d80c02d038041003c078690381c100c010807 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 597124802 1250 597123552 597123557
    0xf011a090705070803010b130b0a120507092d08070e04060209010216120b01050a0602100216080f03040b01061d0904060f18050f16030209090703020310060e0a0c02120a 74
    0x3028144e4031409401d40090384040001c078400503d000103582c15018000080c001c51049500301106030741c0160040f448044101a40da5540000944a900c80c1c9004070040c0440c2d20490304c011074000a000082a800f419640380c203829450008040800203220001c0390004c1644148a40700c55440e032000c0c0d440510218110300c83c1c441c508000d000c1049210008044075102c0c44127095962402102d1042d0503444a41b0905a0031010801207401081501541c0c202e031400607500c030301c20081c040c00d1602c5003001070b10b0b0f60707000704809024248550056008500a070306140c0d181ea0388241c100c454600d4074481311074049030840c0342c0e903c6090803208140c015204240c01301c0c0b8488101030300021100c81c1d0a0380344002c002d0002c5074050010a11031056400030070b00c05008265100c25074801c00714010700c802406110b0300c0000a41405040c4910000340d640241640c0d940c0c83c01e0400c07200940414002c00500d1640300010a82e0710005100307070ba540052136005070200400250b03503042c01c2d40040d00001c05 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 597126052 1250 597124802 597124807
    0x2090f030607080414150123031b010c0602040b0a020c0a080d021c030e06040c060f091a13080d03090c05091303080702101409280b130819020f011a090705 68
    0x9080e41401d441e54062315000d01030040c8145000003d0440068080249000740c0015803000d02c909480c4204061031002824100800c9440340b41c250000c0c4900d6000d0310701c0f80c6d03000c19000d1440d0380c00f107070a6800c0789046541c2140c0e6070311250030365100d950620220002d41d01c00300c06182c039000c1815102c0701e81070751400d0004500c0c00142030241070420071901215964100c040070310003180c0100c0b415400b2182c51829034460b5080411031000c1d01d002c2203d45134a40c4000c50001c214201d580000700140c190a41034400c11401e401000d0003500301d10108940318000480040b80781d003004000581709004580d82c80e5960002d0751010395400d40040c0102046020b602c0c03035417041c1c5225024015a0405c401007a54031071800200b00c1e07061090000c500000b2228420700e0104000041c0c1d41071070425007003501100c00e0340b201c00740c00c4070606071250001c0400ca00447c841c5103203242c81441051900c46602551080f00c0f21028080c2290821550401e40c0c0041c130f80603c9035418640c1b88988d000c010340c2040e43c07 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 597127302 1250 597126052 597126073
    0x8060103030f030219021606090501020601030f02030c0d030305040203010609021c09141603060c080415020a050d06081005010b0c0d080c07050723030a0b040b070c140102090f030607080414 83
    0x2081c00d000c00994a002d68400c05500b002800c50141c844018408c0f460300c40d500300e051100003511590103100181014191066a4043d1b54003480200c10000d00140000407034a018075001e406803100311000d9200303500e4030300c0c00510800075000300c5070000700c3c0202c0c6641a00c11140d00c0b0740207124016042e207030341416106101413540c0c100b01201a5450810b03650b81c07030626500d003130001e840d4803401480c01c2004e504180000140f8140c80c0408000000e140540c0b0340c45040822500c6014520701e41102074213180000614143c0400e42c0c2c1c0400307651084c244440d0383c94215040c440d00c19400c00c0d0142d0b83c0413004111040d449a04000d400c078030b4841f019803408602c0e80342c041c40d08806030001000300992040d03881d0000e034400a1944407003c04d81c0071f01805442521804100c2e040180044d00c0740050100041c4286d21624000300d00030790207218020414601854503000b500080c2c00e940c0103d403170a407409650314000805038440c5100c5d41e11a0180da95a60b240c0c514138040c0782d18100c0303a20030f800c50103 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 597128552 1250 597127302 597127327
    0x61b07110105280c151103010b0d110406050409140c1b01021605070e1303050f03060d0219051806060a110f010f051501030c09051c0b0c030406140108060103030f0302 73
    0x3507082020f603907920a65000d03508000c5003074491004040724251910703095403070556003441034a045440b508401d6444421503e42400904142c40307140b000c0800009010503401d4016000d80b00b9102224820403170981d00788911141080c0030345004041c03500074020720b8001e242c0c027004c1240d104901c500142c1850b61769429030a10100910040f07916412130f5805010f00700b0301140d180d0780100a448892000304c2c00e0f883c05091845510300e4080b20100000005a10341c442002c4a4ac02c907501401414541e8603030740709501c010700b036406024460854100075250110189541ca4021f207001450185400c0c00c0a00c282c0e503a00b0328410000b070390f000d0303010881d403081c20a129174040c1001c89040401c540c030381040034041e001c03008114503050601d080b502040a41c0e00040e0340098540a40f1405c4002c0d050100405641ca800f03080244081400d401700461151024055070040c4c1c45190280100c03100607000342c5803400f007402884419030000c130040010a115410b00d01c0e164006060061800400080c013 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 597129802 1250 597128552 597128617
    0x70903060c09080a0c0806091c260405010906050a060503030904020921060406050112080724110c0c03010b28050a141509030d2d02061b07110105 64
    0x151001c0a41c900c00b0044001b0900c985580b100500010b80707401110618440c402c0e1000401c5201001312142d21845016907007003211020340410a601d000918080c44c009001c0d111660b0229450303418900400d400d500e81c8c0c0a980c0540d10300901641c1016290400c6c04025004182c459a2140f441e8407002101c0c11910b86019404940c3c0c00505141d00e400d0510b102a0341c0b0686c80003071060342c1507104202041d611343c1030b1183c83ea44100c40103160b00b40074505101001680d0050140980fa29002c5290b03c03580b40c0052024070b6504044c1c0d281d4240074003c05080395002d45a8a801a9680310000401c0300c944446424a01d01d0182e48102c65480d0b50100d01c0001254001c03048540e8401401c140700d140c6000901b076005488c0e40c03c0ba01d00042c1c51f01003074403000420802e005008199842e9a2499624030805140c010400c04160f10103008000c000c1d0b59850a0f80c0002c11111951010b400c401e02c4003049883c0c094010014014019907000119840c0c1d0288a11002c3c00959443c0c808505005448 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 597131052 1250 597129802 597129823
    0x10f09030203130f050609090702072303010b092a160b061e15070303020c100605120706022a0a0312090b07050c21060112150203070903060c0908 64
    0x35521090030301c00c0c128030076806030003900103581101300c10403440d580c2404036020640140c4005680380c503010000e91402d1015000804807440c030001c90340c568030480d1680000054110006e01085100100340943c1c206c0a94050700b4003802500040000102000400208034840106910317105a40315000303140c441c8080100c0340303240c030304041c014a480c0c64485d10030501c5214032280315126498000442a50706c4caa0b80b10314260703000c640c031030030f040c020390503a20088001c106842159080d0502c0b000101110300400d4425802d03074155619211001441009907882e94000b486540010760b14040c0c0e80703401440c0c69442d10001e8210303080c03a4a4141c01e0070020340c85203441035603040c14588040c140b880f00c1e400800c0705540502101020400c001101048041e0a80d250040108040031040f0460015020408140301d810000900303100145403044500c3c0c0107046e800c2c4d1100803e91001c0581c4002c0d503c143c00070304444000e10100d000d0f64003031324801c0424145540119178448446044c00209103 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 597132302 1250 597131052 597131057
    0x218070306060908191b03020406030501090624140d060e07050f030a0203120d020403141f02030108060f0a0617061803030c160206040314010509070504060503070512010f0903 77
    0x1d00401a20343c00c03a010710040c10300340003d000481a08480010400c40940e00584001480c0e00a0500c25003a01c100780081c6801400a200712500e90034610b01170301000d0ba0440f6924076200148a0400f280301400c8101011251300c42c51091608141341d0b0404000d80380c0c6607015414441c60000901c262089164200c555006020020b00c0c01040110304030421204d01d00075084904410300580e00400c103104a804004040d9072102842ca0b0801c0080c004c5410042a11006038401d1002d0240052085115080307000e00e103c07003c0d0138a040d54280d020a1040e100d41b5407000000c0752420280d01603541d4003134007c40c00042d003559201001520300c5404142c5102d00d40202c801c3c081112032541301c1000d20584003005600c4c5041a01800a60740f15440e181040c04820700d600c1c904640c0d80e1000c0703d00460b0054020307036402008954190007414150390218103072040c804001128209405184204c03440100503244282c503050030300c80c600801141c0070546550341c010003040d089603803040022460103a17 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 597133552 1250 597132302 597132311
    0x102340b1e09250b0d020d0605030f15100f05010804020316060c0506090106080309010503100909030314090a050d20010c0504031a0f0a02070609020307061101150b09090402180703 79
    0x4002c6503408100c81d5880e0b414103010350702c09104c081141d40031109800c400c12070040c0e4850590034044018445600525450300038183c400a5158000407215100c000e0001032081c0c641341c813111062424a14424031464424100041000e0f41c002d0400d40e500c0750014041c0c034682145044506503200c825044400400ca941412a003803100800c26680d0141c0244000c100c0382e428540c0c170a0341c80c010107001904110700040014806c0000c0d001600080c0411081403103034150514014001d8440551550114409980081c4c0403182c00540581604d4010300503140030600c407401140c082c0e940c003122981188080e81c1400c4408002d10a03d244829035548860300d41e811032904001c000502c040551025050760140032480180000300c94214802400040c2d44080701e280803c040c00403060042c2d0f040c02103c40c0003c0c45504012002e10000c2c20000070454a090380402c40c559001038001c841c0303030460034040d400640c1050403c080c0c00070700041001c84103e8a0b111034404010003103039130340000f940741c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 597134802 1250 597133552 597133573
    0x1090c0f06090e0921070501020a0e1507110f0111120a0806061201140d08180102100c0206061e0603130201030b040507051e0c0a050102340b1e09 64
    0x4011035030040e0840c03c04490701c90401d004100e65900844100d00034418a50302c58000580381502118a03d41d03200c0e0007551180039044018240035503074249103010b4000c03d24280e0741c0c03c0c0400b040b14520380e48032842105d4840e408040c04a1005c40100290600c481e0050034945c0310070030001d401030f09090b2941e031643c551075090020f04018002d0b14490203800207000c07500c407501044002c507042d200f0006200b04c0c8205848009140d8108084010700001070003d000e01c02c024021041c0c41215a003a004c83d540b8200d406a17180c1220b091035036520060304043c02080282c0f80001d03d0030410080c040d0740190f10b003046400107400d64002d98100405003004100d41c1c0031940c05026a40b1035140445040020303107442503000d4194411501011884900c9002d101c41e0207400600b660840c1ca07030303101294401c074180e140c458002c2d8423081c40c0c1801d5081a140b20b004000c140480c00010841c00c030580891402c40355208900c8001c0a07045c000b9044040803903c1c0600c240400540c41107103000e0007031690042 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 597136052 1250 597134802 597134807
    0x19032009040f020f040b0706090b07110f030414060310030203010606081503060f0a15030b0c0d06141c06021e071109010806060111010605090c120c0a091701090c0f06 73
    0x418180038844140103110713012001c8074907420303142203031450b160710b0f41d440c002c80ca400d200402c0c000000421030980c1c40e080c04410356010705402002c012600898200c00140e28580d5501e00440c8100100c03c400481a9105404e0400c090341e0040d0342482002851500e03980080c0c01c0d2500f40d0070010029105a04005615034061040d54120000343c0141226080001d188040c4ad41c005140ba0107192f00e421031050205a22842e20006580201c0715940d10304110300808400e52084180c075581a090100100b1000f0b4014031b031005032000144038003001a0f14016181d00101c01d140c1c1602c5040e400e00502c03942c2024100c02c1d00c80000f9451049646011618080b00c420116800300b03030040700648018003200f9000514503400003401d08100200c1c00b0740c000c40d00d01414003500402e800682280a004113401500c4c0500b080111065040030ba0703958489640006005681c504800076800c840c0030000000001a03038060301e016000046500d41c0740d6250710f4080f0310701d80d00240b807400c1601401c01c02e056 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 597137302 1250 597136052 597136061
    0x2060114010801060c0f02191a041214030d24080f0a0605150d0b22080301030201080408090d0507030b0c07021e01170705041d0402061903200904 64
    0x211912011144019840000b071a07448140140814080590b8101c014800c2124140c80c41036030003002119204800c80d045260b0070000d10030354985030070b40901c800306e80f680f02c4283c0d016a00b0100380c880700702940b501c4064207040c00880100711b41c0410064018031f0807540c0107804a1102400c0700c00080600c3c5554902e520b141d030f42c040344158000e4030810308000004104000026008000402d55440c0c1030354040120038907801c6079034031142035030ba12410800d070003002a208020740d80f04d08610024400e040c0e0f82d04a003551000340300003801c00045c001507004081ca0b81e0001e000b4030b0301e030381800b5000011400c0b8030803c0005807102e521051081003004407881c816580214042d024078101100d6501007549074200c110030700e0880c42c81403210105030744203203030801c05044080740c1c4005034203040780041e22070790080c0101001d912000300c805188954034549e01d0300560b0b014051ba0725003004002c48002c1b011000304418101234455410902d0410301c02c10004e05542c07003c02003947e50050718104021a03 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 597138552 1250 597137302 597137309
    0x90d02190510030501030b0a2a0c0c08010c020304120519050a060f020906070f020f03190b0901050c16030c0b07030c09081903050d0b0d0b01080d0c0c060e120105010e0601020601 78
    0x2d07040ca001030000450b501000c507003100c800100800c10382d80140034041403040c040390042d000e40940085104065110ac85052100d009111514409495154850903110060b800e100540e004000803c50071825150000d0b10038050f405852a110720303c09040044000d10340c6c2030b55190b000c410380b881400014400d40e008590710304011440c0050500114a06002d01040600f00d504c81c03803204e0080d915a5200289010b20080940b0b0300c2c48040d84490202c4000d41d0030a0f64024210400242030f030b0310503c03400d03025094045d0711500b0540c0803180340b591008040c00031420015005600400980c0a04005000b40f010341c44c0402c0d2001400300c01810700b05640d1001003540d102c0724401030b08a4200f041ca81c0d640f0340510700700d5602c00045000c41c0103009100456904103c01030307007031400e101c583e81146042c0c1d44040d040d14844004007900301e4020000f10405806194276000030028107000b94140d01000c5000b400803019803412902c05801c44900364001140c540c650030170800c0947c0d041c03004c140074 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 597139802 1250 597138552 597138557
    0x60f03061005100302040e01121506030b13060f050a020c24180f07090903090e330d08030709060807090612020c010c0c050601090917090d02190510 65
    0x80c501000030000001d6140b2803140580062100c0c04051403098048401401010b40300002c0e5503501d44026281c8103c411003900c46148016400c00f540e45140030300f10071290080f01103009a11004c071480041c1d5601041191070301d603260381300525402540502407080424079001600e484480c48001d0910428001c2868000d071541a040b42180c0c0311040150003c04101514101c1130341000c2851818a805c41041803900c944440014155155000540c2c00d5109540300c801440c0d0703940b41002c0070324051312524100c2242900d01000403009032500005150f400741c855001c00ca00c0c40c046804111031400c2940c102d000041080300164101600000400e01450500d8951030480c1000b070508089000310410000044882c0c0803200440e015280040140b000800055095680140584031900001c070f55078059240002a800c58501c644040241c0080c1411100c0d044003528202551116102a62018001c001c2e81c0158070369100960b84c52401c5110b04039044d0a00c000c2004901c204041d1804 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 597141052 1250 597139802 597139813
    0x30705040b0307110a0b010501140a0903060b040b0307080703030f0e030d0f12020a050306090c040b070b0403032c0c0303180108090a171b0a0201171b030709050a08070b191214060f03 80
    0x100d24cc6d001d00081e040b07a4000c0310000310003a030480010040d0019040715036146c0f044074030129090401061036402c9034440d86401c4c01d07440540c07400391102020034000d130f03074140c0083c1c0304840028040d01c40201504514540440301c40c4401c801041246c0090580c0000243c000c81040114209070280f40c1c0c1260320070903018280740c41c15141010501c260340c0020901c40354a07000c40c00701070003500400d24483c400590b82e000900c101550b103081c0740d03002c1900300d541d119800c1c42c4540360402008591041c07192070750303142c06c4c00c28050041d2007a10015100c00c0030b40c0f2403148100041105a0100303040705021500d4142d59481d0800d5400d411303065880fa282e0613804c0700d401b1000603a000841c045821404407641c01641c0e4942c0120304a0003921b074040b2084110000c01c02c46040c2c0d110040a040d1141103a80503403058441004966480440c06040440b640c00c0100b240c040b0542808a000b1100301c0c80e00d0a46892140b0140040c0c903000c016114030200300300306100740d40c58290000f100c1114150020701 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 597142302 1250 597141052 597141067
    0x30f07021801032a1a180f0a091515050406080f0c0720040c030518070e01032a030503090405070e130f0209031515010203030705040b0307110a0b01050114 68
    0x91120000500f494800135400030800740f61350390040600000d058500e24480d034070f00c201d84031049541c010143d0090401148113602c01a2078190340301c00031a0000341c07011a24609180800000707081d010300811790200e2a031000120304282c1c0d4095070f056052555201d441d80d1412034064000b80024101010354410001009040394044040d80c14003604850502c1c1048010544203070324440080707109800c02c0c24011500c039183d0701072300114014400d0121040381e4504c1c2501603500c51401d130180040c810765072801080071a00013503900c814040403001d20710703550f4100340110203058806d80c401c4135a82c00102e02e000e041d1510707100c3e066004901d401d09503c04400880080c000e0b8441021003000c02d540c8203009543c0341340c1d690658044103c05001c550001400c0c48900128120454404000703158200b0343d90320951002c03080d01c1c05000c81ea00c0b100e080ca414120151f0188d04010308030b20070031202500d05640a9400c000304001e0764021901303907517a941810b00040c004000f0018282c0700d00740403c012b0f03 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 597143552 1250 597142302 597142313
    0x13060f090b04050d03112b0204080d0c0b130839010615110a02010807140c030306040c2c010c0804060e03011a0307050607020a030f080d0b01080103030905120f030f0702180103 77
    0x30f40c41b003220701f149102c3c1c1c00c2c0095174200034002c0ba00039a115100307901d0300034180380d0010b04c4003400500a405090b080d0b45e80e201803d0f1b0020003900d000300303115824400092484200c2c0013051000110120000440c120000b18541c120003d15810005a44074501002902e00249002d90131a8592030000803144480780056a2940c80c4e0740020f04001d003510000380c0341441115214a00b1850281107a544d082c10117015a5a8109941c0700d88503614100e0201d0300e15001d800d80420078040410400c5a560030000e07250f99401e802e41c5018140a00786040300d00084558006201420144d01c036050800c02d500241130840c1c90100b240300004e105203086189642e000130341442103c03000c440e6190754924510120f08550807540c0010082c0e0030725000d6408102ea210090a9404a22441048082150f20045889010a00c80507020030400d4205100780d040501a10181e0704143d82190710484090000c51304d91b6110911749801404003203000411498411291404d11401c1400410154115100c4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 597144802 1250 597143552 597143587
    0x60b0d0b010e04051002030a02070c150e0909010b10030606030c0e09150103020c100225080a27030c0f05030610060804020307360513060f090b04050d0311 68
    0x281d240300a8904000f80400004010000341c604503c00c0075920307402c0c000e61a50294021183c110b602d01c0d0400d8020601c0620360b80b00000ca083c41e80d454150a000840901a0400021382200115520f030610000152125050600c6185030340d030b000503020b880c0c06401030450702602801410400c042d0340c44006a90f407843c619410040000c41c7c42848500d00c03005070001e03c00ea401e10350050080c4000200c0c188840c0d40038103200615055541a203000d01d241d10f000118100c0002800010305020444075a03100300c00f16404031140c1000801a41c5140500061001c22070703100329440110701c2c40610141004040f804010315060b4018001030901c40040c2c004880c01e802003004201141c1b0015040d9941004240d0090ad2212130000c414032110480140c181611403a040c02c5d414041c40078000c0103e14480c1307074802d900403142e0b500540b290741d85820181c4242e127811491103890300460350105d9000f1406a020b54801c00041c1030072003044502400b03441d100e900d007204a00c01400410384400b0849103 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 597146052 1250 597144802 597144809
    0x702030d20160303090509040312090f15060501030f090f022404180501050d02011d01030b1005090411041a070606090216050c19060e0f0d0f060b0d0b01 67
    0x7005007112510a0240095072034032410301c1c115204410b0060010818614403006583c0644d80e07480134951034005001030b4800c240c40060010307200007010400421151700084000f482181a42082091610380a07641c0310034501080c5003079a210400c202942c4c06102d244807501c5028014041244241c51300d141041d114a800780c01600420080800300001c0c80e0b81c1030201c1000c180c0f86131950744a83c0c00d28801020048080510780c40c0c400081458609400c84030b1005905079568054910310700c44509054804406d0541450b45440f40520b20340e4981d05d0b0f06001d6810360f9940354507518541c00700019980380c48007480c1215002c100922011100121145026058225281c2d0b00c42c40f070b2a00701c0041141d0b50109600d28404aa06003142401c070240301101e0b40900200c1c0d000403412030400540080d031070140107001c00c0440040080e103005500c000348a40005080c40801109500881e00070030700b05008070f849156002e001c01c10041948140840d0071002d1b00c0c0c500040d03015030b4581606900601 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 597147302 1250 597146052 597146057
    0x90b0f030a0b040504140c0f09041407031502070308100305060601050a1119050d03050702100b0a08030c030a090b1207050c0f0706050307120209061912090804030c050301020702030d 80
    0x890480e59500b01980c5000060700411041c500760900380030482143c804903205009000c00c6524910740724500c034000301d0005101092588441c1da405030b80c00c807190840c0800340120742001011a103500209104011200000340e6140000d2600800c850402071911303403e002910070038004100009495a4010400c0c240140d03220085002503032810051110707260244035134000d40e5591502c4c0740c0140c01d0a440784c0704a0b52a020f01480c241c09880701141c01c0001a4091541c0107c0c42d0101c2d00220242d540c05040707090110b840d54105800d40e404000c540704580d10000300301002c642d000007048024000507100c01c2c02d18500f440c5180500d100034000c00208600803d2044240740140b08002aa6004200b150b5500d981c0f402d015096404c12140303000410502000c03010385816500848409080041c48540303170085002115401409141c090802c0140c40c1185807002000c51060010560084882540b42c03480c600e040c8884003c96004140640d0052005500580340014415008280b60 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 597148552 1250 597147302 597147307
    0x2041805100308130e06010e0d061d070905180f0d0509040b1801030209070518100c080408010920130e1c0c02040506040516030924021801090b0f 64
    0x8100308204401d900080c00e09076000584902a4034009000400c0301e464404c0d81c1819510b007401500c00070a02180560403408011041002506642c4044660041d081c400c00c001000c01d15034601c1c00701242c0045400c00c4d559030034002c1400343d0345039a000003103c400044c95820a0b0305011525003054101003824400302188010003036455400c41002c003a8042c20410f59144000c0742d010010b40c0138402079010703403821000714440a03c1181202c0c103003524031412040e03400004080c0003200c2e80040e00c0b501042a000103c0f00010401001400100620320011820304940d0600485a0708204035074200c00c285140c4200341501c2d01c0c5108103a00200702030000b6580180348002e420a0200450f1043c070ba00000b480b810110740002000f14118004c4c2c904100ca941e9405c280401c0310000d40b144030507601b01a1228001c81d02c6038000389507031441b901c00d04900c4600001c0300c0b2610184128dc2017a03450b0007060f41c14110000320342655030b03170300240f030300c000903525156140065208541ca242d0401800 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 597149802 1250 597148552 597148561
    0x604051b0f0313080d05061003060b040e09010207140601080d020a0b06190905010920070c051320030106020d0f05030a200307031401090b061821070609060302041805 73
    0x4a6408140e041d42210829564400d041746002c01040e040f58040d204006d580748031203915100f84546010765048458030f610340307401c082c0074023207081c0002d0060981d5074080001c0000502c140004458644101c0d00411165051102081c184144244000b0840d0700034035032600414580c505e120380010007074840c140280f480f070f080740440105036000340410a0034080000741c0a001c55004070341d220074100b00e0702001c80b5050b1481c2c1d40b9114070040900300d00201d00c0184981d290000006542c0c40d0012400909100005204801800000201c158110010004000168040c00115900103c2c4c0c5010560a104500080c21500018003807091061340c07000d16030000500e0280741a4001c05405400351640b9003154010080c01101500298019200c000080c01904500545c5890070b0700811050910340d02d1140054109065003103154013101c148501200d070104084108814034583c000740240d28241200580306412651052040510401c82082503040c644080740700081c0115010590342c60307 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 597151052 1250 597149802 597149821
    0x3070305060f030d1d180f25050405010e1002070b030604110c25140919050403030b21030706090c081e07090203012103020709090b0604051b0f03 64
    0x40315600340c4907250300c0b0307125150050a07034141d4400c002110a980708088050004015040180810070341e00780020a0300d40c107100410032303800001e503081c078403c007217051142c44072218201c25001c01150000a0900031035a10407290642000169000c06020040401c000d43d121414071443c0c44044010000c0313131843e0f556410030120503d821031460b481e299848071154a920a050003050300030789421214a0411004400790212410110804800d03da40030620030744000c000c00d944e90300001c118120071400d609200d150300035800f82d6000265200440d05000d40b0b1040d082c8050007c2c07440e80010b40d4004000821611025071090f070125042880e441d0069a201d45900711108900448012610310492003030741051121485040f154259507840f0528100d200a010352401507480e035030301e40c01030394a0220710342d141840b900c1169441661008260111910303410200d4403120982e05200d1585042d019844e008072058100d2004041e40e40040c0009200b11000c07070700702050201c000b4001c0300 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 597152302 1250 597151052 597151069
    0x60f0608010e060601020d1707140403050606090906160509060d060e040c0603110d15090218120c0d0b04050c060703052101030c09021606020f0301061707050307030506 74
    0x1041514284082612025258040d01003590b0034990307441210000741541d8800226154502800e0719901043c2d466596800c05540000b071000c810b00c5528910f0401c0c04e01c80f00c000704005d5002d40054011400d0040410a44140c0901904081d62041061010100100c00a1000c0300140d00305641e440c00b50a0103e0b00c0760081081c1c60010703502c0c2c80f0000480704000032aa0f84124420260900142d031100015004c841d42c8a5403041c0d18a02801000c803103142a42c0311442e0b81d40700b0f00c041d40e011643c40311404107990001d07020420f40d07186107907494414101113010440b814500e07001b51220484420109160312101d22000d494144268042400c0c8a018410740138144000740205503960750724100505070792702c000c50f00c00000030b91060540081200c149102d05990f071180807800c000345002d504102035000b011078558007004a6100b40001403440c4003c041c00640300300000d8680d85810800b6111a000105000c00512120200034151b5800f00803640d215800b0304000a164444402090404 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 597153552 1250 597152302 597152321
    0x61209020604030f021002240a1e0b040b0603060f060f0412050c120a0201020a02090a1104120c0b030708131a10030b09030c030301090e0f030d05070207060815040906 73
    0x540009400b0091040b807141e03104c00c8600070764400010000e070500480c0c0e0b400208442030016048a221003c0c4180d105607801d400c140342002c0421203084858440c4840426100140180c03540c03000305907207900b03140c00388000e1300f03c080312411709626002c000b20b440749031042c0145104d0740000880d00541d84030081554041c05042401004103105407030410f9440f512102111302c07a4406045401210b40005001c00989606a015200d5040c0c030303034244050003401505502d1010b0722103102440803d0800c0141c80103240c1c618a1020240356810316502c01c0700d02d600103442180d000c0080008003900400c1054000e150503040489001d210304040c0124030b40d0a01d61456020035500b03002c0d403d410090b620f820f403800780000040f20344514035099038901c1340d503010740450f410a000400c9110142c0c0d015803209010103054420785e1481c42c0d44079085601101c50700d0720040e030360f0051100b825410050701c005441306092588050800b07864021500101840c2e55119540f12400c400420281c4c2d004081d40 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 597154802 1250 597153552 597153559
    0x5060a0e060a020a0f0c09050f15090601020c0d0809090f0108061807180906050622051e0702240103150902030c0a14031005130f1a010303030617011506120902 70
    0x10040a14205442c2106c0b445000030303642c14400030a1a12114000543c007a40036560740c0301c1d8198095003803014184005000c0c40c198060ba200c04a1513440300d2190b500c07158454042280c1d00ca0040d01000354403c0c02808030304001c81806c0c018851103000007401500001c4502216115031903c60180303203040569000110540303031100c54034807809281d403c070020a61103440d040c8050b540c0d00091120000ca0740e0254040002145c0d02020103c010364807081e0450081211280c4460a25600302c451180580f80705005a2001c0c124410300c072122007120304108440c4500f24807a504d580c0340c502c01601c031180004840c0d41da41801000719036040041804005003d0718403042c0c55501d21924001c100c410201034003038001d202d481c0d15054014800c451140c600084101e2995500d038a502034210090a01103039048040c0c0c3c10548010111000c4500a40c402d541c00300745035040c01c0d40c190311141c5030702c0724011582c1041c0b49404103c10640488040d16454a002034600c201c4100420180c120700601030340 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 597156052 1250 597154802 597154823
    0x5061602060f04081908090c090c03070c05100507110f1603060e2b020d0212070f0302070b030a05150303030912030a060f140f0a1409060103091202010b0a05060a0e060a020a 76
    0x170340c0180c68984034116450035034070020b6005040c803000c800101c984448040007000001c103283d014503103940d499030041080340c40b0842c5802c1c100044a00c01d950705004201e40010a1065039001c0010890b180c1c02180600801440fa0140c51402d084500006000a8950440c4443c500c800c0001004040c1c0c0c02c80310000b40c5041c010681c0310000410080130041c001d040510b0442400001c80c3ca92116410803020b02d00952616911040c007641042102140685080021034500c42000395015504180b00029241000c030a110110402e0740501c9000e900b0a0081041c0ca5070b010501400f40d464500344e181c0d07a40d40b06120b8800520058000380d188800540300401d10075144020710361101c105861140ea850030742d2041094a4440c0c0c8629031002c00c4c10032074180301d41010345150340c019606040102d42c89855940d07084844200c2060500142c2d9144802e40061820311010ba004240584415240003a0704000031310000d01c10005a00800c000140d81c0c0741648200a20645203800040305003 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 597157302 1250 597156052 597156097
    0xb0d020a0e090f0f16090506070302150a0b030d0807020604150e1f06090626010906051e01050108060102030706090c05090c1c02121f03080309070305061602060f0408 73
    0x22038020f0540e4088520300c0d18070001004112001944002d600c0c0c16140c0041d03141ca01030810183e54811300c421000c4bc000c03d2540d0340d400c000c0c920481e00070007541c02c0101d8401ca45c1c00906103840c2204d182c40e42048010300034000303516000326010f078000d03800403450540b054042a1b50806006e000c04440190710622030300c410600b1100311841c030440075040b8213000550350b4026900503109075008210682d0f900442c259100c20703030800c04010440c011000440d80d403045403241000c8680489811030020128808546074100d5013208c43e000d41400d0070402c000d8203158000070b40e64090040000c020643d1030904000748086400000d0041c00d00034005c48241c94081308200301c0d5004481510041c491980e07110074450a503000380c4121540782e4101c07003a40d688022180030360400c101ca0044264820183c040085520b0304002c501c01c1901000421200d46940703040342c41c0c00002045424000c2d16221801e60050340071440715009450040400740726256400c010075144039608803018200001c05000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 597158552 1250 597157302 597157321
    0xb100f0306050d0210050711031204150c030503011a0403050d020330070e0f040e030306031b090402012f0106170a1a090304210b060a0b0d020a0e09 65
    0x4401480e54003486040d40d00e000384415040d00c036200035442030038007541d84840c9124401030000c403800b401190040e501c02c007002c00e0800c190385001752898a0005014030800704445a0100030703911a2030030617164421600c0090480c04103000d00345140032147c01b040f81980042c3c0580d00950b811909a804452420501075521f03800b450381800b2030424051011106821114100c0b4820003d03d142452650b0b201e0003140d0030151209000d6101803000141d41d2aa147c502c500000e40719110001c507600d0400340101858034034800c4035a88100071480c50400306440700390030560007540c2030920031600c2642680150203aa51481d0601d1001020b107810f40007d18150400390840d410120030b01000126540c05a4550083c1c005c050044a42c0f01c03d42104941050741b4140e000c00d01030142c03401e0039118001000d10403401c4240d02051040700e0b181c44c0900ca10400519003201080300c00c881c14a1400c41c0c40c8440f07010f00045600d84c1540803800c043e00500601400d400c148004086012910f4100a80c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 597159802 1250 597158552 597158567
    0xc0120060a06170a0302150a0e0604140c15040e060a1a0415050c25150809010e150c0d09020d0305180a0f0e09010204091805010b1e0f03010b10 63
    0x708207140f0280d80d000e0f02c1c445004079401c900b540c0c02d50b000d0079513002030203808010981c1c05400844080e80c1d030921208140c40c10711105004610508a881048521000e018680aa4100c3c607070b1081000715181d105406401003107504480380d0040074016a51110000380444500d540950081d8403440008c01c0c03000801d400410070744941124122000318004400c44a5025000c81d07206942d0040c503800324005c95201d8886143d00c20007030502ca49070f0301c840380f40c02200301600c00c40d00440d406074140490a602070141c000c500f0003800c0146a2105106030904107c4005017a0058085000811001c1030055400c503e02154010300b8004912100f450002d1503a80b00c00c0e0356266000c2c42c81c0b03420400e0302d0400c001908881c16140400802424180a80c1500d040039100d00c056650800c000038003002c480c0a203103402080d4028100f1700745018181182580c880b15203552150100c0343c00b095002d088000c402c4451407082d0b4110748000e4448010034018a60560380741c2e800b2010001140c03016074007118 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 597161052 1250 597159802 597159809
    0x3080a0f0501120b0703060608010314011d03130e04031e0c0c03031d0a0503030426070303020105040203101407030914060c04061d06070b090a06110904050f090c0120060a06 76
    0x2080130956590710411401c96840b40901000146c48600400100d00200c844101e07803000704000084904240000c2540d004c4111400b40864202160b800140035405011200070300511641e600d0740d1615a1b802400350341501d46090f980c0a42640d41880f2502c178000b9440c1840e03002c007080c5a01c546030b040182c44108213a000c0500702c69180710350342041c01e150240e4000c44402070011030034241403043c1442d8031010b030341603208415441d4403c81c0c28032100700803890040d03009400000e180e082c00d00500d824100c030880c0010540d0b080c05058000d00400d0302040e540810545400100c804c2c00d4540310001542000c60700c911840307818180654050742c18014421a811a00c0e940e803400703140800003945245e6041e040f640900700303000d94004141e21840169003d1780c52410740d0321140060761000300301c0e240150301c00b00c641c801040320300702030602d4400c50707070020800064500b00d444c0c42e850840c2e50300500c029150403c03c0284641c559004611210b042c804a414207454403403800d880d10307100402c3c003480b = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 597162302 1250 597161052 597161063
    0x3090f0605040306051303170910050a02091c03050301050409031110050105040c180302041a0a030302061906260106090204080a050d090f0b0c030d0504051509010507090303080a0f050112 82
    0xf80420b401041d181b04143c20103906071900d0100842480a4410b8440014170b000b100b4000e01d081e02c689104148107091003444182070060700c85159006000c2078002c84009505240344410004011941207400d03241140d00c100d5001c1841026881e080311407810000c1400154410100c5403201741007a80c00490583e4802d079010018102c908004942070340e050b01079030050326802d84c0140f0140c04c0c030750001d000725901d1380031340410369207040d002c5403d81d900da030300583c0141c0001d0b0910901081d1407404100d80d0100310400d01010741481c083c40c0030590100003440406903038240028a43c002900201e0003401343c2441103450360b541c1c500036504c0c1c2d02d6039035040b1140d01a050a03c6030b218040c104060681e6001040d030410541040400001307a400080c07004850301c014031103040800c0c0c99000e024802c0b440b5201610180c4020070711021447c00291101c2c4059050004010140b54000001e41c01c49405180c05039160b240e42001400030310512100b981c0903402d0400100d014902c00c81118600c80c441d1 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 597163552 1250 597162302 597162311
    0x103260f16140d050406030209041b11010506060f09010c0609050610030c0504020c03040501180915030312050c181903030c0312021e0a210e1603050a02060703090f0605040306 77
    0xb2880b054650340644000004104188800c2c05200c0c825406071115040c003410020744400c5150036410484a400c420000040e02c14400303d204200031b000301a0010700c150303403407404c19040c2e19040c0c0c80c6000b4071800c941080074899400c07003840b0154000d0301e44c46800605079a140c1c03e00400c0140350403c1400291148100c5040c00106401d140c0f0840f01d40700c044101030350410b0f041c0303001101c0e030704201c2c01500c2c03011842020110311315401d80710342e403e0701c018a0b1161b1b503407501d54030300940054022100c0181d098944000c00400c154003000315482005034080c46c1c1d075503201c06400140340302c0c10300703100d00c49c0a54905008030415400017050201140a500c54114a00307001144005921a002d8600101d80a140030f040e001e64021010301020780c10307030074403020021000416480040309500001c40250b101d0350803d81402c001d10041080d44800d0045160150442e11130035600c1060400080c040d610006041050510520783e400140800c000c1d0305000c1651803034020041d130014001503a466250 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 597164802 1250 597163552 597163583
    0x2106090213080f061b1b01021c140a020a0c0c03141603050c130f0531110f1912060f0606080609040503040503030715050105090103260f16 61
    0x39940e44981e0007903004201580d6000e41a190161541c00242171050040c0500481218048003c80603000a2800182c84850160a4204801c4061003d080ca10b1521440802c02058070003650351008503000c0160342e03042010000c44078a801c039100600312401008020040011044094020800e800d00711811000006020401842c56100062140d8031031800b018160500300342e0717458004811140000c40710300610301c500c16580c0032510508509406205691a4003084610000052580b1f010361450307043d65540c40184644441214402c5851010b070700415501d001f01744519445030110035003a0b55440c0181d00b40c1c1c0d01d260404031880ba0034400640701d03080c2c061103244200c07201e5a40d04900c81d06c69009000441402038025580c500007004041465101000203101080c070641100e0b4101c42c03000d02a008503403041c0c0109114030b6100c00104040b460510501e41c41694201c0206400c1014002c0d100051088500803c05541c001c03403020302c8008151055029240506101602d1524 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 597166052 1250 597164802 597164819
    0x21803011508330f0f280f020c0a0f1401150b2d070c0b0a050301061116030809040e0d140c01060b0309030a0f0c030507032106090213 59
    0x1240107980c2c560740500a60103840c4822440351041c054007800e400a072031400e50140c000c1c07041c01c403050344040410106200842652420312584100000c072801c02c807036400b01b800070368007031501403810156454801c00284d03502d0603411a0702005400d000c031184c9058514020070140c5194038103840c0120408104041d1110601030041d0255280000242141c2007240d00d40045d0403420031021122003042c04050400c014588448281d21030070241a1901d00516200b12840b0190300203100240e4207100c1802c403650404140c0741903c2c0c49003081541c1410600790306203050700c500f82024031070882c40400414007a42900030800008255014047c40c01603169550703440701041d4032100080d461801c3d00c0b031402e0440c009403141c0c2988800209480e0380d6052050b034030390010780300c654036508000359028140c0e40111914000002ca1306202d0804901d0b52800751803805074010140c14000c840c4940d03000c189015801000f12907a80340c0c200412a00c610042000303400026026101e5014201c0c040344551 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 597167302 1250 597166052 597166091
    0xc050d022d0c03161401050a0b040e01140403230f2106030604060e2d0105012c0a02040b0c0c09060303040509041203020705030304030c0204050610230c0102180301 72
    0x62810011844c1503000e08144135000100502078a01c0303c0c0c21194011030300000e0051030701034110320f02c5c0400d020002004100442e900c104070340030b882c0e1501d66030100e03100c1d030031a009030300a0b09801c0505180f440c80e01da201c034600708140c02007000070000801290010b18079001d881c42d038000058890f0018800d0820042a40007a290582c0c554810800280013403241d0f04a2944d8881c0341c801e40c0c440d95520522240030071800c110014048141c000e8030b01c03010b070342403013054018485c00b00581122003000d40000c2514610700654003580180a0001e02c80040c0e54044500a122425049070340b01c440c86020303501c0e4280c0a10f620320480304000452803a16000056070141d64000f0018806132312544e0360400c003000400b002106140c1c00740618004070380180042d502c00d6000e034031018245683d520400c4103c07507000b0081c2e445010714042d4282c90b190310120440700c1e00704015005c2c100501214888501c0d00079203044c44241d600001d648811105181800f1620441c250300912401007520304100203030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 597168552 1250 597167302 597167317
    0xa080a120f051c02040b040306021c05060a0e0601050403020907110706030c05180a0b2a1c2618060c041d0705120a0606110f100c050d022d 61
    0x781c0280035049800d03080310444075601140000062426560b4207480d86d66822903401071f03130380342d9003c11030725903010240c0c0c0c010b034040320801030800075454120001078801e0301e02d01a018003144202c0000303030f003a4001c4080380d01175a00101038829501c2d207040001d00c02000003500c079840d80103d040001c0c1143c0640903140b0019000d0301d8260504105021040001c42a10591a80a40700d40d9000582100070002400003402038225100744410010040c4201240712000712640d6101e040070b40d0811030440003070514140300d441c15141030350300084c400341c5500d42030155860131410f00c030600c0300345022021810202c0c1c6046054410560321081d1291190040b440340b1682000c042c814401c9520302681219405500340c208103050001e5095400c030035200c02c03110840056584c21082c400550045140800c0c00321480083c1101c03a140d00380c654440200007003082c03050b600c40c00c0032030f00e0318002c07001e0f10150004082c04644a110b0f00a54045615910070300021344030061001c0c001a041100450380031 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 597169802 1250 597168552 597168557
    0x16112e0b1c03140a0c0309120f02010c02040b03010f0225050c0409150603030e040501320a03060e071401050c060135010b0324011403010b0a080a120f 66
    0x700382051201202080c0511011020400121403a011044114001e00704001c030683d203030454180b0b14030b4050b0146403503810101440c1c1c070b450b00d203d002440f0701c581c1d000003960a00e8001c3c0342c0f244d80d10114003d40010005540c1c95402c0c4031f594520318039203602400074250a00e070051500c02010802150190b02c204c0050103d0f0011002c0f9242c5080c03980010168901c507202030003151004030109003c42e003042d04120002020906642d90514090240d036014101c40011318032007503609080141d80c1680024900003680e24540e01b4a032941d9a90700340c4c030065402c15811301c0800545504181c599200b80501207110307054090300c04240d445402544c02e901c0354078005090346e908003070b103a041201d0400c0440300207209161454080169070b039619440c4408200000c24600082410142002d6240354880001c900c002a419054588942e225044840f11001903080d9100b2401003400f5141c18500250428140300f400244000e0010340701c2c89880c0102207040d042c15140c90101e44c0c01c0210b5410800 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 597171052 1250 597169802 597169819
    0x507080a180b09090115110f07060306150f140409090c09110405030a0f050a1211100510030f08090603040f17120a1e0516120e0616112e0b 61
    0x24101a500301e5145046c801e0a09001080a800d046450b00d00d0b00d281421507a088600204003640c1c1500980001c0c0001d07003101d10300708503500c6006000c80104884481000f511007158550512140300301d50140528000500856449040002203050144103031041c0c0d81c60310301028070010b2608241e5044d0b60340180036108a401c1034898035650106044141d41c00d0140002540c0010403004c102d6401400b540c84101d0714a04907801d5600380314151106206141c20301c01040300e0342c0c3c0400218420740740d0103280b004107100c65041c00101c0340103071244103812040001c18801841007005003150300c03d10501200380b5212840b000300c002c5001c2c401d0381c0982d1050040110700c04641581201041e400c098000489907180401544280d03001525843e0b901c105034a801021590b04c4444441c074101c0c20307081481140303801da840079980c0c0401480c00250080c1440b48002c00752158000c0c001c807070200002c0701c80307500801d034000c20200381040c0210b00b5070f0011483d0310b420101c50700400f07001120080c2241c1c1c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 597172302 1250 597171052 597171059
    0xf060c02030f0105010b090910090204090507030e011b030c1403010308091039060f05150d0804060f12060305010f051e190b030f0a110603090613030507080a180b090901 74
    0xd405014040e06803070f01100001040ac1c0d00b90744041d01c0100f10295010460741030480b00a012640e105202d01d6499041c4a00038128210080024070400c400f0300d40051150040481211625101042c0c0900a00700000000500c130f0303400c0140c501040c00312001d001e9500da00a0664000800c801010203484400d100e11688a00c0030706000e904c0c1d56001e078100440300c890f54501040b103041c131041c0000c09580ea424043c407410412100c01045000781e031a00c800000540751b4082c240514802c82c4104103400d100642c03c0d40c41002c034220103801d01300702441b9403501c903e040c1d4041d00d140b8082c2c0c584546840c2c0054140420b1007a0002c44100d89000c0c050141c96a50100003c031030821410010365455120340c2c841030310100000c002c20101000940811012860111034034120044094420b0344144140201040c011070010b4204200c80403016403441a0f20b015502c5000349a40941115004296241400d070054003002107911074039000e282203a00d400c10780341d179406903060850b00107400c00c0c01030 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 597173552 1250 597172302 597172309
    0x40f1b08070b070606031505180a0506130c0e0c0d0b040204120f05011d060f01120308070806150d0c02010b041a0d0f050106150f0519180f060c02030f0105010b09 71
    0xa143c041d00a000c080b80c199102c0e02e449004154803844902000e0780c55040080481d41d64800003074880e03038000600607112803515030a550729806040d084005040980303000400c003400090f080200311444040070360b450196003101e840e80184407644840341c1407031444000c0e4034140c82241c09551000e010342c090f81e03076182c5500c25500011070303080318259680c2d2110421107040d40c20080c1091041c800030011880d240d03d08003c05a4184e003d0500c00c40344c0c031005000250003502080e40055140340c0301d88103581c0d503030004a4840144560342850100080d40c07100c080c80300d40000360300c8451500284031105c450f0f030500c0308440b04948404030a05c1d00e8404d1001900e04000001d41d16400b444000c00c0e900c0c030304d4545030700b1130f051580b1040382d006a41d4460580140c12040c08401280d02d81800e90038100b0341080c00800a060304400010020000d86c1f01008500c1030200301e01600c00c4107140300381d0980700c22001e44002c41a2509a120784100241d07102c07a8001401120b040c1d80c12060414141851241070 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 597174802 1250 597173552 597173557
    0x1050a030f14062706010605031909021e030c0901051e040902130c0807080402060a050f0c100e120304050705120f0105040c1419060503100e040f1b08070b 68
    0xca4a481003500b042030401c1c000c100b2103000b08846034040034400380e54100c1c83c1914440003080c0d9865040f00300100405500101a42c0c0d101c031003400300410303040400390f050b0002c000710b84000350700400c2c510b40f420b25208810869244a1402c0c3d0485288078a00410410560000d105143d40189401021544510040c001030b0f160350010b071000c00e228140d64002040c003500140380c600103c0e5034454040d800d070340c460410350f08120a410f08240509280c1c0126039140700d020820380c01d00c000000d211030611742c224201e940c0c400d800010ba8621454051800000c0c10b051400070320544030b890303c0034000d09500001c0f00d000350352050061400514100c240b10081d402070121010078050b654840b14103500a0103038602c81e84c4100e007c01c1d035203810200003940c40d158200d5040d0003001407004c824081e290f0300540e4410b88286080441e125510035004181010a50304500b00c0440c10b00140410018100c2e07285101c244100c03c40540210070f0071040c1c01c0425180305e484507560181b40204071701c3d52001300 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 597176052 1250 597174802 597174833
    0x9040f0e1b03160306090b0606030106090302011818051501030b03030712020a050708010c180605092806090305010b0d030f0e010c0b010b1908090a03260c0c0106060801050a03 77
    0x5550086940001d200054507541d130040d1080354030340541808008204801650054045070100d06650400d0402800d50a0030f020085c14002140069442884900850401004001c0703022040001c50305511000d0a02650038040341003045c3c200000a6000e03004a03008604e024004504002c40c4d03441d00a86a08071942e0702055009018010000c41c005100c502e001e00021000890105120031000b400c0030500c0074444c40910010106005540d8000100d40e0b0075141228a00e11154004506000c00105c82c0c0088401000c51040091a183c0100507003080300c0c0600000c20280b04003e040c030103c0030384881d005000504a000c07218800380603a0102e0501d22040c500400c1c0b0000a42e41c1a464a60a820510f50340c0c4011a10a05070100380300d10040b4600c103841c00d2440c0b170030070200880e51040040c00040900280500c110011202c500e50b407a291042250305007032070f0405450406696019009403141e41d42030200c003243d0907010f070821a04075540500503c0c080381ca107403103c00c808400b245 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 597177302 1250 597176052 597176059
    0xf0123041406041b050109050112021803030408070f0b090a0611010209100c1103010c1b03050904150e0c040303170403020c0a2c15012001020d0209040f0e1b 69
    0x280c21040c807400300296882035101d001900101001c90108510f20500b69000a040020243c42800280d0b40095507001c070940c0440301588940318000060744034030107000b4032070b01444040340000f90400c000424004580c90749168201e1185c485020000f14840d611000e0b030081c0c4c07950000c01c440380c0305000000040c1c11202c001030920415000103078019140e4082840051103e00321a824002c0801da46450300d08101d008120141968002516004281d07441c184889004000c039400d1501503403c0760140c800c000d00400109181d2540c0c000c112903540511300b950002d030b03800107018070282d03400c58081c0c0360140c854064892182080c84d010752001082203045002c0c48210b03003000c1d20707807401a001814122080c0744650394088048075002140d202e80111040341d0340e0900a51b015895070303502c06034200f841c0086842500781900301c1c10f2000c2003d00c1d08150700c00215440810111b074082c0080ea40101d4041c0b00c0b075041941c0103c199081c41684020f550850f0031818501c000c4120b002c02d0024028 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 597178552 1250 597177302 597177323
    0x20304090c23160602040e070318020112180b0c0d0c0c0302060c1b0d0c02040f020403020f06220807050a09050601050319060801020a050309150c0301291b0f012304 72
    0x2a80d81c4c0d8241e0700070ba032240d0a9400aa814008880c0c0c040c0200014100c200c40119906000c40d00000d114064103600c0b10901e0b99584640491040e0300d060715071500e50003008031002c50610309485d0784181c0c0001212281c07a031900c620040207510a120380d0600e146c050340204541c1d110381004c0f05181d40402503a69080c01c8810309d51114031400d00c111500d01e20703603880c0e1403103000d19401030000b900c0c40050080f403807070320400c424030040e60f40030f0101d00086000e5580c5901e4504a43e400d0160350110300058400c0c1e01c9054000034010700016103c819528191502d15a180d91804c0b4641550010358a55010a0307040c0005804000c03c1c80400c05d40e01d42840000c111241d590742c0c0c8500321390024400200042c0000100102128100400240c0d841e9038000301d83c1510300340308483c00c9404107004025a0042c08803244030001100114081010001d2429550300c5012034071121120038400580300c02c1740a03298a18400800c11311038130700f5440324015034203c08590010348100310b10004208454881c01d0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 597179802 1250 597178552 597178597
    0xf05030c041a0319051b030c091804120503010b09060306030a0c06020d11071217130b0a02160b03060607030215070809060c03060310050403031b020304090c23 70
    0x903090000740b02080c040445540b420320540d03004021200c810740d4100c1908081c02d02c00c6000d2000300328a00340c50654181500c0380c861103071402a40c030469601d01d40c01072010001818100049540602881c4a000c11058821340f400082c0c032203000c02d04c40d204080c45d0a0049801c41c0c149800210ba0080780203082c0c41803040241d030342d006046080c0d0012001031340141c2007031025a404c4195907020f007145000401d105032400748440d0104040c3c200040016840098240000745031100b41c0c1d0954203801d850003032483c0c13204c2406c600ca4000c00072000052003004540f50007560f001902d001a10b80c00301507989141d0b01ca01c244403140e030016100301c01f14440c0d14040030015940400c214050740e21a50307002050b01b80b0f62003042c40c0840c00340008019503000c001b40213031170f540060a0300d40c0f140c0c4032001103081e0740c55040640050410f0500e610211440441c983c000f198044010425900c0160b001c01c06d05440b0001220481e040c0c5c0503441d42c01c0d1000b5802040b40c1c180c100640100c3c028244868070a540 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 597181052 1250 597179802 597179819
    0x2010309050c1009080d0203040819140d030209150a0f08070c050f01150b03090601120f020303030a3e030a02311211040504051009030815060403030f05030c04 70
    0x3c003100000050305000103110041007403202580300e0b411440207605007418280400d4441d024030080301001c04407043d20404110780d074241800c441502d030090b50200c94030040043c0103503102d28030591003800480b070450041b031664803d84405030302c2a5a6034860310000031041d105500c000e0700550602404e10300e100001102000b0f442d84c0700600b60004204542146c105090610722078201941000c8140200100b01c000003c83e10704407003c610340c0141845031410030321007041070250060340501000080190744141074011152a48a0880707a0700312100461a8200c2490307038151510402440070002c203901013408010315000454440c0062411002d0405040810542c2c41010620078030169003203100300503608000020408046101707403007003aaa8400041003103107074a0718801da544070041400c0c820100210f209681081030308001d4040242000740440004075021404407090310207400b03880c1040810f84040721b5051f00e40900020081105641903000102010144802400002640e44 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 597182302 1250 597181052 597181069
    0x10c0501020f0d0608070b030c03070518090a05060a080d0e0d0c26010f050f07051602030d0926150a140109091202070f05060706020d0501260105060d02010309050c 72
    0x355200f00000d8503038a03104005003001c1c925800a2a900e4091081140e807000ca542201e5100d0700c54a03040c2d960315401c1c0304001c034203038180d010303a80c100d50840100100100546d00440c000c0394211001480c1e141c2c1c940b0300e2a66202c03a1407010300002d001c0070404049003019200484902e1141014100c1c054840c05d004100320300504000c1c105036403109040381070000070312801c0d0010a00c54014020f502c6c0103107078031844080c064041d50801800040c41c00c1d81d8031650f5131032240c0a80c000d0070795480703540c4c1c90001001041c4034015140000c0c0300080100c4100c00c00d0201c51055180000504070460180070b4028400d440200307a641c0960f1201068540da6440300c0941d406040c03100000140300340e80d8142000c806074100c8510041d03500084013401895064134404003181c1d001c079440303030740e4880602e08240a40103074140403d646082400100d00541139088400351040c822202c2848401c0010101e030a0700c0b4140c078026004205242c8820141d40b01c1d8001048290241045803c41c0c2d409401107030014 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 597183552 1250 597182302 597182317
    0xd02070f030c1415070c0503130e0109140906070c050304211110020604080c2505040b0105121611030a090312020c030318030708031b06010506030f06010c0501020f 72
    0xe00045030002c100200101d401c0da903980c3d03442c01071018a02c4854080d00a100c0600703601e0501440c8140d000130801e0800c00c039140c0711020700c1c403107111607a140968480c00e0028011051082e04000c031054400540181851061030907200400d5162940c07a0155024282c0000548140c00300300b201040b61a004031800a0500280c40740140340030302401e1804442c2d110b48206841104031843c1c0315252580012029002604400a40e41c2c424044242c240b9049841600310700c440c0301402c1070307000c07403d080d80b41c0d00c00c5560542c0c0c140840110070b401120750340f003070108000c1c02e180190302040614140171595806020b4505100703007100215440f180c84e540150154100140c50504180704112105079484501d0016000400203001d001001075200c1c01070030860710078060511441502e86d60200704810080c000c0c2001d403130365040050310002112402c201c9448a0703100f04000018282050000c80f40b01321903008814815440302d000441d40c0c024001e03000d4801d903400384943c1444501a03401070a04 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 597184802 1250 597183552 597183557
    0x70e0903041a03010503030d0c1b111302040f0303030f09021c0507090b13050618070c0308070206070c0b1b0d0207020a151e110304060503090f0c0f060d02070f03 71
    0x100da1a1210100d07081844081c2460b00304000e00042241c0e40340002520308502d80800c01007262078050700122151050302c08450304801e04140c00c14248040d41115200d40201502c01003034201030381c4450b105a11851082524030302d0b074080d0410101e0302ca58020880c3e01d050f1440403070f9040da1a000148140c201c0c404445401d40350760416030400c80100862001080c240200703010300340600000072508802c1c0e4418541050f03d81d0006503060340d92582a0307043e40520400d000c0c8600705000d00400d203180045040300070540301004284a28000104148182c0c0c140d61190207020305540c1b00030b806280a030034258810701c80d00c1800b1180c0d0401e0094400d51899082c0141c440c08140100243e062155201400d4040b48820150080d98000c501e00941e0940c0c140f581c000e140b04c140112034007170800481e180240400300c2e01041c0780e0341c0100114010100750007252024007442c0005900c6021000450b94802282d0440f0541801d0a03005842c1c403008480005050941c00d0311015080301040000300c00 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 597186052 1250 597184802 597184807
    0xf09030501050a0b130506031b0411070b070207080a050613150509010219090f030618080c010911010e0102070603110c01140a1514010e0d2a0b07050c0402070203070e0903 75
    0x6820550b207081d0200c01000d8040c0721b982051000b080d103030103002111070240c0012100c04c0d403c07a12a50400c2520000107100960f0750091418200a1a54107544610040c081c20000155015000a000740c3c82030300a4040c10b5030351201c410b0b0800010440384112003652608604090049443c4100c1d440b078060b0400241c0e6403140e54880c5611104c421100c0020b00240c0c08052060446180842c1c0075650b000900089080e154080d240034050710000007414100006144a0b200d1019003014000030b119810b042d100440d41c4006460104001c102140180d0020004104031480b0783c001090301c42150f9041403400211070480c9007074403c0c2581c203130200d01009041c090b00071000d120b01a0540300482140c00c84c1e50030014500010442011070f5070421480d0403d52180780d503400408100f10360b210800c0c00304c643d5590402d10003403200c225800b032081c0040e140000d4000000007169107e0360310601401c14142d54004001c025045004142e070107206000c0040340d0000045071b02409800d05800070758 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 597187302 1250 597186052 597186071
    0x10020702040b2707021b0609010c0510020d0f02091309020109080a0506010e06060f040303030b061201030f02010816091a130303021e010b01090312030e03132c070f09030501050a 78
    0x512410281c08141158004000e8010703442d690190b440038a91b00320b444565078078043c40101d586030040840501907000d005910100c6480550090038154012201845913522101c03400c0e00f02d004100392543c10400c100f0075030b000e40070035610004440e841410900400b540342c40500e454034040e110100d034564030550044c400c0942d2043c8880c0c1c80300040b19a1032030701c00041c0303a020f40c60160348001014140c842c006001c06507651006d030f429800b9a41d98041740c0390781d00e040404007102c0103101a8040b98050303011481c000d60301094403804113401d0b00d1f4400d1345407411408495108a6181c030800e800d9050224072144034880d08000700650080c1c0c02040040c10940c0007110f9021b46001c0040d00ba89040071800c07590340c000010b14112900030a100c1361071841c465007600645003040c00c00790640000a01e05003805503065180b01901d41020040404605510490850801c00c2440e40d1a03640c030580002c0525200c0c0c10340f9445000c81d803801e44030302581d1380d40341400e462080d40c000a010b5110716980 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 597188552 1250 597187302 597187369
    0x5030402130905101e0b060406051e0f040918020906150c010e030306180402100f020118080d0c050c03030f061c051c021b040b0d02060d0501140607030210020702040b 73
    0x15a1092031000108006c000c040001030301441107103d41c2c0140302022811507036640d448480c540010741d1a8401641e0303020b55012140700d69215003e612601881c0c2212440c81d2038a400000410300d9002e0122501c507100c8400300881500e05480f0624410410429168862400c0c003c1240b104041d00046031070341404002c0241c415070034102219051100c00400c00965600440f185c030824507030904100154045604a0140005407a00380181d000341d80b2a0781000103180082c844c0401c400303002c0010061074503045070b507403203002c00d401b0450f07106201181d4002025005150442030040000e0040c8207209410b802c1010070a40580c0c1540082d007403072124084007a150984072141d032002c3c00016141c500c0c0c1400a03801e18bc2c2c00b07400356658400412031521a41c4100c080c044e001802143c81d108421800c0b40681800d004031001030f50607080c032071003074100344040d20030455254001d003040c000400c20000080d00580002e9034040c0e15006036910f6178880d0420a50f40c020640c85804d0b0306503610381d16 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 597189802 1250 597188552 597188591
    0x71208030906011a0306100306030816150e0a08090109050d0c06021e031b07330f0c11040f0c02031e0a360b0a09150503040213090510 59
    0x9004d03183c003503c41d0004613220b042121b600c2402118480c0d03c0fa40601d804800030181d582005298110000c0c2401c40c406000750001c40c2603200b090648a40c10780c42d6980c10903181c80c060000041d502c4101d0180015400d00e002e469035031410700d0030400c582c1c0d407078000417960005460151803000c4109014007000354181f200794030021168803c103513440b00625141e0742ea882002465a4003140e00094120700e08014040c440c010024441c6001e01d00091004072090390322600424032a40e01440003078201c043c02802c2c0200b0390b100e19280c2d01041c5001782c5032100003400960352a5803041c4d07211421141d2004601c0703007505d071514582c02141c9130b41101c2d158030122a114506045c84003400d202c4040c800b42c0c01140e90041c02c42c060882d03800d1803c24800500007420300310f942d42400c0c950440100b401c1c1031000103064180d01603030b5507682c2d01d503030380c0c1c0049101d00c00200c500c40020001c10014002d07080228001e00311750002c0400140300c521903200e0a0400d10802e4610194030741340da01103100c26410381030 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 597191052 1250 597189802 597189809
    0x41109040f0c0608010b07060203070207080609070609140a06080712060b0703020606090402130216140c0108010e01030b070503070c1b06030e15070819061d15100e0307120803090601 80
    0x130701101a5051013124865406a1000104001e070000300191505109111443c000c0c505c0b40101d48040c1040c00c6c1d400d40b5505c0902507a00061100300f4001030b200e030540300004405801900c05c0c00450306006003212a000020400018130180017180194840903209480007010411190fa465441c1480c0003030034030801800301481520054188805a0340f07100c4244049078400d00016038992280121500d161025030300503040320200e0003065600d42c1c000c40d90045c0b45800741e869181c5682c803240914055002800050308042407880010001402030008640000b02c508112012101d00d50399840e240c00200d1049400380c900348130400a56803d070080b4400c0c0510680a0100c54842c04007844c1d0424000740803e013004444c4002c07940041454042040c00d1041e00740500240752103407560181035007074240300b128a128450000c2c10300c003c81d0b6030091000e1030080040c100400300b83e2040303c00b6800c90f000158540645000002c01400f441c0401d0a294458005a5204c0c58124400c5051440590 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 597192302 1250 597191052 597191057
    0x10210c1e0c0c0503013303060f0b0901061103033409090b0105041410170702030c06132003030c0d030f0b01090e04080d1401090509010605030f100203041109040f0c06 73
    0x12001546d00f8002e8054a900f07008840104451112545682c0c2a00d0740c4007500b002e1918604e01d042e802550420560188160b4490703103e42d990381400c55504103081034001040d00240b001c0740c6045d650007212540c504460000d5821143e044111200b4500c80c5483d49012402203030040001984601a585100c1c0090074124200307441c2c2001902d61001e106c0d0102c0c0314000c12404200d203140512520440480d119415911900d41200040e41d00d601001c454181842801e00184044001d205400b0b00580d021156543d00683c41c2030b40d4403820721040a6540c0360000b03101c8004c49a0007000401d1600025540100c4c64a016403003502c12520410b00483c10031051400c180400e00514025a822540c003855590b602c040344681107004118014082000c0400c502c000108294a038000600422248000b0003d40344d0728010140d503000b90780340e401e06580003440c2c200390300e800703039805554042d0080b1450005074003d10002404024101d0702215800d102885035010301c2447c0b00048054480c60 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 597193552 1250 597192302 597192311
    0x30901050f090d05180d0c1e29030a090b2a0a05090105030c0c010606050306090907050f0d11030105091f0b0303161103150610210c1e0c0c050301 64
    0x81c100138070074850b440038218070315801c04d0780e042c00f5103c01100170141c43c2c0011400b40c11a8a581c03640c44c03501c04111311038040b040c01040200d2003c124917142d070b00b0040300e2505920010700e10400c608903a0002441164801e54034110030303002c14000021a0b00c80e9100e00c01d0b55500310001000e0301c4608804555400350040e0a01c41d5070000f940210450344650401d003082d9880e5681d5001d1140d043c459007113220415400c2880c00036090b07800078080c6010f010100e408603055680e0070001e5a0310f401c0391041d664041200c0760006039609285074001c9038640038400801c1c80765580800f0a00350b40341502c5120b1180e00100d000c91807000c0c80030101048002c1d50300f050120389000070009a0b80d000d40341803040c0c5502e0185840c000c0120b00c030400440d10a014041d10b48808802045403d4414111203180c025075014000710100f03442039000c00c941211400d55244c2078200c007500800100700301c500d00000d000000301120503000c88820200c402e00196518444400080e1401c0b688000103507020901a80c1070 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 597194802 1250 597193552 597193573
    0xd2a0b07050a02040504020307030f0b060a0501020307020d080a1206030506460e15040c0803040b041e0b07061e060803091012060f0510020a02060403170708030901050f09 75
    0x402d002c03402c10380481d004140b603200d81c00005d0400c06c0c1c55000410160003140703e0002c1000300e1300350303500c110012580070030819540c0005980f80d01c9405002540289c9800240000406500182c02c1c17000c1689880360003040c12070904021103103142c100303039410390104040203207091040f00307201000c103081400d07541d400d2100300c070b40e104110f03995840000344400c5a4100f016841164815008000110211041102c441c2003809200200380e40540301c9149048010030804000004c642c00c45280c654018039040ca044181c076030701e08132114580b11009850700c0002c0c0a00b8420f02400c54140110030001302c1e2403c1a101c0b642142c411181c0c1140542064410028841c012095a08488068900301e04e10040d010703080303a500040071000d040c1070f803034004040751254184076a242580e205651840fa0700202c1306041e80d0701c04150308001d41c8144208414000191096100000940d405da4210b06000c0e0a507240aa81d400840b03644000341e644904111134003040d04440794001c681e000140c11407801 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 597196052 1250 597194802 597194813
    0x70f05010e13020c010f0218090c180d050304030204020c0709050a050709051e0a17011409060118020f03070323010302092217071208070c0f020d2a0b07 67
    0x122070b82107601640e03022a29808900b000e401a446441034100e0856490441003110701611040b02c8400c0d0280304c16000140c1c07440c2d0b041c0115102d01c903258901503103030b00c0001e08220414405d400c0854141c001800000f0050301d81d4005071803864110005407814034140b14502d022110014a0300c06028240028030130101d80003a48107041d500c0503600c80a90034141460b0790ba01000c00c1e00355070703000050707054001541541009002c2005440030028000b56807a640364017640c803c29180e5038142d80001c2c0040205510130013214140071003040f005810030b102201004203d410480c0c600b00442e031160503101001d40501513030040140e5810501000e54110f401256a03441d0003850f940307140000b031000711500c22401e17070011700c9541d100390170880503140600751071555004010b048402514507081d1070200390280241c070303201d4256aa41c004070990180c46030346200004640a9801614480107140403c4500c0c1d01e03000406141c0000c0c0900c00c4c00041d042d0b01a00c02940055250041444524009138 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 597197302 1250 597196052 597196069
    0x4030201050a14070b01030308150103090b0c1b0316030906030507020601060315030f0f210e011d0603070306060807030c0504050d1e051b0f03031e0409020a02070f05010e 75
    0x10003502c0c1500d103e40c2020180e8959128218014203a00c181c580004109544a842140b0070558440c1d145400d188800c019415110500310092250103d0000030b075140640501610050f0103440c6400d03400e49070416010f0840e4003011144080c003180c102400c041c035400c0b4414100411840c9401c01c042d16120030020f407100d6060180404143d03c401e1145220380b0071811180145401507400d560b00c15241c03a001025003008401210707800a8005403800d8111020048610b50741c050b11b40d00c42a0f180c010045400109800f84006003650100c141e940341d40741c1002540c4200da0700d440026245040210150041c1001884c20040608010012554540c84010f6504845e403d03074001d0629400703031a05000d0387c0ca0b62101c442c0d00c048400303c84001d0007000182081664415600300b0b0103e4681818041c1c607224601c2260f40590080083d03022030020b00007005c030f0348002c02680034100303515009664180d034045c0c81d01d40c0060b88846400e000c401d01d4000120000e00d02403e0480440c259000810040c1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 597198552 1250 597197302 597197317
    0x306041e0b01290c100e010618060f0b030402010207060807020106030605040320031e18101808030304020f01122406030e060411060d090804030807061b05090d140f1507050403020105 80
    0x31612400381b2501d40f0001d4000e080901b50308260b580b52030b80002c0c4100010151841400c03680002040005203503c0544102c0380210b40681c05403898504050341610440700141248003159a1450000b000c110706206041c091442642c80c0110f001006503108450b880514112034643c1003080048a103900540080c0c2c0c9452407801e005448009050310341c41071805c02c1001c0c81d005072282c104002090b9100c102c061440c0404040c0b40303070540d142c0911503506d0104440003504007620f582c3c03001ca2913010307401e800c61074614850040741100c2100032854103c1140d004601c10071401d25002e025454241c0150855020800000c0c070441c54952621003d4406400f0001e0003074030001601801c200c0a0b0b00241140c5400c0421680d9442d40c0c1d180202c1c2070f9000c41016540e082c60300146207001480180b038100707986078560710b250500d00e0900030040c013184030b440c04a60032010448200f40300c00c000e024000140036040081e10300307247ca120462001c204000c0c140c0041110402c410300040c0e8100040e074014 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 597199802 1250 597198552 597198583
    0xc02120601080c150d05090a050f0102072d02030706020c10020105040203030a0c0516031b0e06090613061a03010617010e0a0b0d02030f07030303060506090306041e0b01290c 76
    0x240c4520340840300384c6215901e8650021410310041054022001442d00c12291096013112981c8281e525194200c6c003900038024101003038901000c600c09c084aa01145100705803400b810134842d5580000e2600340d95500500150b004169401e034289000010082c41c2080b90000b4011850180e0002c1c0d10ba00c1451450001d1001600801c4203002d0100700c1000b480c0c0442c205694100d460741009890001c4440400c074441c1c4280e68042040d030840c00407540600e101078518091511010100100f6644640494080c2640c51800180362850140714208514a00707603195529410800005c0c200f40c000c4078460110004480104004544102d03141d0b840240310200090100701500001e074490450301019500d8400c1c42c40201015201041690480780320352001c1107001c1d40c40e418850f290060305042685908510006404111075540c0403030180041d42c501072503504035603106915203400fa0041070014214030140004050781032001080107100c40314040c140f8172212074007565a10403030021200d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 597201052 1250 597199802 597199819
    0x10e1804020a050433030c06020a020312040b03060d1506031a07051923030f10060f1202180d050303010305121201091a04020406020c030115080316150501060c02120601080c 76
    0x40000020305c10401940e40100141310f107656880c4001d503038016481c01640719001d0b03613401c2200317084840101c84c2111581f08801b03095a035040c00b0052074170080e0b0800e9502c1e0079815194480004140701d40310107540305010703840c4000d0725541610440d000003004c4d1030500000708003d9209015200306660301010303e2501161020a00c8030301d0740d441032034029075140002c0201c240820345d1190306010348a4913840c625032543d1a82d440b0121101c603150068080030510781c0c1000280000c0c0c9030014104602e080c2000070282c0c000301e021548115101c1402d6645400100040c010824140302d190045105007026500b0301000ca4040740007280c061090048545e940c400c10542e00900540110707590b20010030454441d96580d0000c0c0d00c0c1d0b001d244120f4880c0d46002c1c000f2071240c200c00608800d40e001c03e8011800c1203a0918542c06e4a03210305019102024240b030302101c1302c3c08600030b0f04c1c0600100d559080c0e25401034818801841c0f0030003000039594000710018407071000006140e0b000311400321645030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 597202302 1250 597201052 597201131
    0x106090f06140d0510020a0e011e080a0e0f030309010902130c090504091e0b06040c110d050306130603030e04060b03090a1104020702030105040c03140a1101030209010e1804020a0504 80
    0x45c5040c290120342c0c1030441c004942c10404035084400700301c0c03120013a00c0348503480f07807811504c4207000c4402c0c91300408511402c02040444001c1d91200308507020440c2241c5c02c03844412035003031440d0403c0310301c1019a0b4441c925003085040c070b20040150501080300521410090308400750460285018880c003895a807152070062004040c01101d00c100f149011a074104c2403800c1614100c039040329440d010354200500302c1c00c40b9114114182e807850782e00300074000d20101040202c4071036101a140c00d90043c940a60f04d950302c0d400c2e11900000b14070a403200d0160525540502c17050764031991244210f402c042c400c0100720040030804d58603140c2d10092801c82ca010180004000b03010300c80d00650150320300000c00c401c00044007240000e687c0030317800202010b00c6103584c10f80c4e44c11650b00000d00d030b045130740c1d044d0380c50754001c3c1c020308841c0405041090b507404d940c501248a0540c225a0303010380b80b081c40c0a210560500b5401c000207072100b079070b060203070b2440703404503c15111804264040c0d02116a8403103 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 597203552 1250 597202302 597202313
    0x18040e0c33210a1a0102120d091434050117070302041d04050705060f1204030903021e0405160905010e04091407060e04090c0e040c03080a020106090f06140d 69
    0x800ba54150804107018100f4103d110004c02c1c44c4c092884001070101c1200815600014036245884140310307101d4900340b0004550f101500c408142103031820003208082074007170b000f805800104080451220000070541c28130b04202c0043c01a00e8915100c444024880c3c1d0742d00000704a868400420361700c0c0b650316062403c5009211701e48c007600801403412480380441244000f8103020364007810455602076140c0c000c100c4e43c3d218a01588a401004200b410403060f0048421035020b4064142184103658940100f0b0300c14050007032407510014183e10f00007003880c00344074080e00301c061035a51000d03560ba000009421000c05003d080d0500c9850342e12041175943d03035000007a50a42c060f00340c18a00520030600750f9200100d00400001c201f0000070a081c0782414498600180d8124610031201445c0c0010001c4005e80038009481c1c40c0301d200700110200b4001c1c0000e01494166030f00004105240000700b100320f460b0140d660407030300d0034214200010720410312024100301c0d040340c09100120080c03a11 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 597204802 1250 597203552 597203587
    0x90911030f0f010e371a0412020c010f1805100807230403020108092a01180b0901080c1b03070605060904030903030518040e0c33 57
    0x245589481200c0d0003401070880801d1404803110700100900000c02520440c0751034540a42140c1070088500541d0b07484030b00c030400c200c180b038114201d40c0c19507030b00503844028040100d110514680d070070007003d00080114080c420a8a001e80f48041c1401c1007034040024810041841d05108101d000c1320114281001c0004200040c1002041a00c2105444101400c4440e040741d02c000403034103c601d035082c0d11200c81c0b203118404003020581c902e050305541c01034800302400342c080e2800d84a400404110f031180302c8840b04088010030303074003109036500200040140c001007441c40c1d1009200c040811020200006440141109091000c4a076940ca02040518014000381c1d0b0722500c0384031070700402900c003c4001c00e81d4500a00050150b66940070038822050002e48000b00002c0128200300302080c031400103008802968146540c1e0000f803000080d040c0c500440e2500c0d001c0c0c0114100480c549003244401c440d4051013181d072a0031a0700144400e00d036900e076000300b41d100d01d80090082ea444890064 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 597206052 1250 597204802 597204833
    0x1e0b190f1b060608060c16080d1404061a040c02060112140709050910090503090d021203070c0509090d140a0915020c0f06090a0918060c0203070506011e0909 69
    0x140d08080d401c941400000f40207944030701a40c500903400401d042022000c21104400001d880381c081c03040d01540d8030132807640504091500c244c1d54a81104500848990584c000d90003030310301140c1d89042100102808020b54156031040d407415103840d48560300403404d00d0444400c3c00c3c48181001c8542001e49406014507000099405070300c002040101565019030300075440c2c40f04452201c004045078000b01e58074040b0242242d4018410f04049140900e00d00062501c0504a8915031001002d06131641d00088800c49000307030101d0084c00301e824015445548681e181c0e004054030140c181d4064a0040041d002d0914030303400003661040c640c00745010303400500c40030310301e03034030101030382c00300079200d100018080344070341c01c200c012241a207024400c1d1018080f0080001918610300060303130008000c0c402ea0b00f4903071100f442c044404140c49114101100126802442c2d4400071468403034100300c0141c20030140002e95802040400b8a000c1d190820f84030101c900164080360780c141400310403e20407 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 597207302 1250 597206052 597206087
    0x60609060a09020315040905031207020a0b040b0a0f0c0201020715110421050a0b01060f0c2112110703090f0305030306060304060b19060f050c060402010f0c05071e0b190f 75
    0x1f03140c43c01c04c000000200054603894040d02d586488818003282c031090250400307011440e0b2080840d020811000795146c1028101e0130000c1d1840181c00f404d01030f036405002c01e4001d0b0b540460313001c09002c18800340282c80c0451082c200944e400103858140680614015003402400310200700c2104010300c0f00d000d01c074540100884d883c49405140c08800070390709025090001e056030f03003078540c001d0250041101080d841400319003400c2c00c135050f600f8810007503050941003001504a81c25020703000c2c403400d400b65a040184a9651809080142504a140c0d0000b05d10341c05075101040410350110a40f50004003c696081e80c82d100c0741040e078050600001440d510004030303510460400400c11030103040300e8090310740d2512854800f5041d911401f800070800100d030881000680103612420010341003581170704003500300c04081c0c5c0ba00d80c41d215490308440c0000c1d800a002040d8004940f1400b0000c2910011040c94211103c2841a080308a01120401c1c050208a20741080b4042d40d44520040c0d9600c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 597208552 1250 597207302 597207311
    0x60c0f06090305130801020301050a09090c061b0c031101090b0c030909060a0801050a2c120903150c0c1009031d04060801020f070b0a05060d41060609060a0902031504 73
    0x205d14043c000d40c0288140c61092004030b1001400d19a540a0b21480c031350481031600b10646454000d07250000240f0a800a103111030380e01d040040d081403035850207180a01138054a803100040050450741840d04030190550040c00400303540030002040b10043c60050311520050f44a59020500d10b6550342c111038151750801042007112440c582c84841e6008180100b02d400400085504560703081860705400c80750000f1020001c019641c2008101c410350140850301c004180c4801a408004140c80c0c180030f5a90026658440c032a08100b54108020294010030640b03c59903005031804c0102030340d402034640c04002e18141907580b984004003c0110b58000d6545a0711103690342090392161500725001f40400010030500e40e001e2141030b100e0072000d4028103050000761110420303103e074803070800d00c084480d00d09106011002c9504801d440000d40c0c48410303192000791580d040c400c0c0181041c0c061050b417400c0040c0380e076807418038100f02c500c90000107940391a07140d0920440da025100e80340c1c019090 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 597209802 1250 597208552 597208559
    0x403260f030a0b0609030c0d081207021c0305010b0a08040201020c04060f0306061a030f090115030311150601080c13050901060801031208040f030e0f090702070807060c0f0609030513 80
    0x280001c500c140040d040420260381c0030b0003001000c4c010a01030a400d540300c0302e508021420401c141007007140c083c0c2205030520000310080c40e07003040101c60100c016040403d03040300d078a01c00f81500300c6400c05800e0038003056042041c00744442c00f844004004018182c40070a081d64024051040e00b100094803d01c1241e8031511440041035851204581d200d1400c10001904010710000c514103460f906005442c1d41c48000e40043c1017480a0310307a0b42c5035541e81c5050a98541104100720085200352142d100d1107074000750f40740c200f051010640c1c0301e8149075010018161303070000d01c0b55404031503020702e1500d40c0f071413511118444030942c00003070708050707907100205555801c01d0009040324401c032000450382c003259004030341081c0165401070094400080c0c020000f070156054600000001d4000c5d000c01c55610700050100c1c40903140c40b00940c01020702809000014010300703024002c2c0d0b041030790315126140c1e260058100114005000703581c2c0d450780d1104161058044515a11001003011452901d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 597211052 1250 597209802 597209827
    0xc020a0603150b1603031e0e06013002060a03090b190b06040305030301090506042a0306050d020121140103030e0117060d12051606050a140903040326 66
    0x2000e4044503001442c00c24005088502802100e0001d18007080c8004a1040740c1d406034060400030303124030780246460075407088081462080301400364042000b07002075450700e9800c4000600d11b800b1041b2030740b43c1c000851a0000b5842c1d00c480d02c56415a030080e80c6240444080b0024407540300d008101c00300080a104044203841507403020454420010084040ca00041042500c12440300a00340c3c0c005000420001200380e000f82d03403041000d4404680d0704000501800000941006012074200752601000c681d68588500400380c802a18407200290090700082c10303000e44410084480d00c80e44d40c0c1c2284200aa0304210002050055248040d58492a010b00301e02581d051950000f002800340000b06c0315815805406030102409824004109865014503a0186d282d01028054208a984108003104187e2750b25035008040005080c102a010441940c03e84500c0a41c00b100074800d00002030804021a01143d9006411002020b40e6002c000701c45007201c0144255848003140001100a = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 597212302 1250 597211052 597211061
    0xe1f0b060c1b01020a051911060415170606090f030304030c030b04060c0512040219052101051503032d16030f031a04020a0210050907030c060e0303070605070c020a0603 74
    0x10000602850000302c00700049a41c3e50107100c01614950042d00c10003101c3c0c000300000e0240d071707000369180f0044803195400701b130f61a40300d58010241c43d200303080d0441000d0740c0010b003a070000c410008856424100301d0002101805950710076403181044d806411a0740da020000c88004503404891000c03110358078100340c00c0a4104645c1901c0460410200c205030b10300c240100e58035124101118400354403140c00340300d004220080c8014951540706008180c6e607035120003010352103c8003c040000c07481d041d000c05d404d640c0c0c080c08800717000021090380143c40d6000301c1a94090750000e841d80c08880b0944041d405a11104404800c101c003000810a000390b8100d040081d2321402519554400c00c8124011011100c402001a0b41c80740c00050803902450705400408000056204846c4400070780031411085134816a811b44069004403401c0003000400c2c54610010700c09420b094140142c075101082d12489818002480f85641d840025100341c012480c085140345c026007411042512014040d0007003 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 597213552 1250 597212302 597212323
    0x40e010e011e05012001090c0f0602010b0117220605070509100206060a0e09033f1e131e02011d010518040b030d030507120e1f0b060c 59
    0x440880002c1c041ca140e2070031a5800c594041e981e0541d0383e40c0140441e10309440d82d800032500c554a0f508040c011a0440350170a01400c00b0b0701c1e440a110345001c10181c01c640041960070b050001d4004616500d01035001003503404101112200c0d6084c1101c050303070015036004080208414580020310501030340c85406011040c01c1951107074030841e26080c3c140c0c1d84000803104558022a14081804823006442d00c841d0807620b140126402e02c1c1c1d610200034a110300c90020a00000204000040760104203000302009176030000d09a4000e0511381928807050f551490b0054030a503905c0c002c00d5182104c01442070030181c00524450401030501c0e07003002400720303640050340050041040a2444006031809420b202d2058444c03500d00301700050a10302c0c021100401c2c96200e0744d01c0c071144005032428801d91a00c0c2ca680c0e81d0014140c9410031300500541a02c07403903954001d1070700140c500f00420005240c8440650403213005134621411100d0030140c00d285150580043d008a81e4a07100c3c0000110607480 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 597214802 1250 597213552 597213569
    0x60e0a0207021c0809010e0301021e0304020a060503090a081312080903010f020a020c0f030106030512070b01140a140a0906140a0b070209060d0c05030714041a0907030b010302040e010e01 82
    0x503400802c0740f40b401114a640c060040c640420080714958010160100c81440c080c0c00503040245202081c2081d140358080041107030400020801181740a4600001400d0756007411410b60401c0d40c0210f54640494500605045000801614100503a51841c2c01008030500400e0340301c54600d0208180e0300101800c601a42c2003541140c111b00b01d9000b0746400301c981c1d0b4000e010f0000281d0420080e617000443c459055540c074000803010030424031039401c1c01611003441d5a502d0200c3c0c50711790780002d0140d2203030304101c00395803114030540d0791800380d40116000300003c100069a0800014500c0c0056400f00302c01a180c810000359a090040810058401c02c5440c1d61809586285101d218850b0302e000a60004c00381c3c0008060345002c4134182103003400744505041c1c02c0e440b0b80102c2e150002d01e403c00e5505e007280c0030400b0740c1e40c5003d0098001c0c0014000261801d6a04500801c00018002d40b61000341078846103016003a900c40c1d8181c8000b820300741544c01c0c00d03580da03d4802c030903c1400e0080f01c06 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 597216052 1250 597214802 597214819
    0xc0706030911030c03030f0f1605010902120a0b01030b042a1703030103020d0b2e05120d1e05072103050f09030f0304300e0102010c140d060e0a020702 66
    0x80e24001c590020607110150155103031000d40c40d02181568401c21080e0b1558005101e40050100e02440a52700184201c00000300d8640f0386c01000b01c00750340c202d02e84469038446948a00080c60400c81d0b41c2c1107a911030320002041d103443c80d00b03510001c003214032401d01c1e1185940b6444c400200e45064003c0f01c3d41c0513802c1030180380002d00951079100c24080a50820032141d41c44c0001a481c0d541c991380281d840700c112944002000b0403103990381c00480340304203400200c1000d100f21b141000e6407000c00c104402c01400d070b1000018015013006c240304590100120088030602d070080c003c10480340c24030f9200984020142c10200700c00c07000c8017030140703007400070b86403c2c000b0f40710703c521607c0240100100c40003181040d1200208540c1030384001c204980b8201c04058030384500814511103200c00c000d11012500941440000614a44654807041e0441e8144840380b00c400360444813030a0400a038400b029030303070303440b0740c50020241403258807403d038018000c02000081c207060f601a014040c800ca6403240e = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 597217302 1250 597216052 597216083
    0x3150105091006021b0a180218180a090303060f080f070b091c02040209060d021809061e0d050d1205060a0509130f0b0a0b040e011418030c07060309 65
    0x840b441524010100540d220382003c21045c0540e18600d80c140398010542da84294071102e81a07814042c11043c910b1a540201d00d030f114030120200d071458030301d6064481c0244401d00303240c884030229003d804140030650303403205041030502c203070000d5000c0d14180d980c54003095660180e044d580e0401405012060140352408107140386080308885801100818034050700d6048a8040c0d4a080440740407607009500304141d0160751035840191003800e1040100507100c01840c1d0150080c444000302440c4100d00400822002c1d5981442902e0f5950385442000c21614007100881c2444504460140c40c600c2821084420710f43d105026400e44940ea100c144060b403188400e020000a10b030050360392109080b40002c0040c1001040420114000d00030b01051155031784407050b88410658910340b0440c1c4900e405d040d10b0400740a02418000450000c100215040d00001340031080a03104114888481058a108981c100103445080071010156964243e450788050001c1c1000c040440718200c940c3c1d001d2 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 597218552 1250 597217302 597217321
    0x1203090d0206090c0609060334020c0d0c090207020103060915051903170306010509040c090518010305031605120408060435090103091b06110d090e0705090315010509 73
    0x4203059480030341701c0c505210040b81000241c0e00000c0000c000c008030b000800d4001301604030352100c0c08030b1002200d41d01d0192154001c0c2041494100180100d070001640f070000740c2e1146000040390503c2d900140c903001740d0310048010344160752140c0341c07084c20107811031072107865906903030100c0e502111012a000900fa24105034902c0900c40540003105007214215070207520002141d11050514010b803800c4819400141295150807180300010250313072081c0600c0c10300c202c3c01440d40706a021003242d01e6140d56642076584c86800c401420407a602c0104104201082050317000c1590650210754480751280007140d550142160103485d4203106100f8000101884590380120380d10b2100e00a0340788407803501c0f000711948016000ca042594a404400103d9681151004202282d40c407140c0c40d1031500380001c0030340420703030345d4102182c01000e4030650b0a6000701112040312250001c034841c6a072451010703a070b40e004c2d101c1d0041d01401141c00000d1016041c94055068400480701c1081545450104 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 597219802 1250 597218552 597218563
    0x1932060918060c0904060e040308100609030c05060f04050d06090204180b0411030f031317070b0406080709090c031b020303100302061c1431020d051203090d020609 72
    0x41c4103181d00010007140d00c40001400404036208050004541c1030b5036010300003d4401c007264207400051104050200c3c031000d400e9000010080380c90412045821602da40301000d900303204140c851000020440c0c1b4284808056a00070040200644d001c0c00300381c1040d0024010030701089200740d28100160319988002c5c803200a82c650802442401903490756120600b00500c140042d41c03500c0381c4407a0f520a50300800c0289960042c94074800589031405401c0c0c40981d150305d20a4880d500720040601c5400c19200a45084400070724004060380c981e202d0075a0003403015084a43e40310f01300358480d0003598150300041c000204410101c41d035540030f03480032a200d000580300c0540080800004001525040c030241000380c116a0340280401c5002d5009821240d01c00c6c000d20300c540244040040b203400c1c94502e11410509040006903262007840080618010b004c8000d1060303804501c6e0906010342040904100d900d0264015501c0c204004002d5175a481905c0900042c4a076170001403503404e000c140e = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 597221052 1250 597219802 597219841
    0x10623071a190e01150506030403022a0a0e0601050f16020d080702130902130906020c2506050c030301061b0203120327030405010e0d1b0e010e19320609 67
    0xb03051420750700701400c2007c40d80c0b0252090b011031056034040d41d41020b40c0584405802c030210084880340e1483c0081c40750602c1103600150f1560740c000c041016a913001000c88070060100d1080d0303551000c0f00711201921188140019421400c0c00b607064041016441c018900c02c0e00031103080d117440f081620108142c0c1c0302003400030b420a082c40504a124801d0703030410100203101e1803016061858001032a4070302100010142c40500c4840007041c0507015194130380000c0d00f0140b07007852030400d111403020313038903c01846110204003081c40218a6070183c010101d50b8554010182c3e29800740c1002d5524490b0026500301d001003d198a5058000c29500700d02c5000842ea10059803d0600e000d00555410070b11010303694004000400400000b02000306420910f180c1da03029004050511543c1e80c0090360580240c0c006244940902c0003520000c40060880702090030081008c480002042c0005014802c021440b9506030009100a4580070401441060180ca03c0401940c41501d000c4100c0741814 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 597222302 1250 597221052 597221081
    0xc03080d141303110705090408090108010602030a02030403030e0a180b01110c0a03020d020a080a0f1e02180402060d060b1b2a030114010e070305010623071a190e01 72
    0x141000009000d468404d01c141900c0d41512495580d0340d012401444080750111440103000807240c0a13580c00800b0640980030502c0290304002c030324540655284140d000103000c0c8541030b207514885541d0050070601070806a0b1000b44003024000103900a09800005180442c002c80e0354044108400070b0307080001e00001308043c105500e96003d0220310210080260b0308100c07800c5000c82d2942c8200020345c1d40314812004042ca80f100d80c1413400507045403481520041c0020329400000da9120540c1c4205610040d040c5d82203030700c440c07000495a00c1307088142e00200381005c20001c0d105420b04042c0000042d2121694070382019070802540300c2002c5a1418a888010710250158480e01054241449809070001482041003d42a90070200c02d13408080c500445608001409030301d401014010310850408525603007140c80e800c24106645001c04040b4100800c000080c007000070030f50000040e00d14a14069400e0207981030034140c81c82060500d1042c20481190402071052050040380300c042c9 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 597223552 1250 597222302 597222331
    0x20705120a090b090a03050d02150703050f01181b0309030e090103030f08190603200307050109060c030c02100e031b130b03010e0d0e0f0103110f070f0c03080d14 71
    0x554041540e800401c1400c5d002a5041c02c04000904c0801049440d591642c00a000e40440941c2071065580001c003860101420f150610100560320202a410340e000c00c0900e8440d05903d200c074400a1a80d503000c04c51226071643d00d95505c0360554000d1818038040d42c0c2c1d0b441280346103010f000070500f080c800100000d58021a140039184100b200710341051001035078000e0b6501c0401e884d000e80c0c40380d40080c2c9400c0202c03c110301140584102e90010701006801814150345001c0010707104643e01d02c0390200740911110340108051007000b2031441c05a00900107101101d0f0b1a8009040c1c40d01403480e54001d00c034140c03110040b5514000f030f0103164500200700c042c036003107022200c101a01000300000e80543d2250180c10b0b20300c4091003900800c44060303072403d282e83c45280070820440340f40079900341890310b0803000d0108100000225050600c0c0784900556407038880c50002210440030b000982140b215100100402481000611180070401d0301401401c445200a880200040d00c0c0c100e086400e0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 597224802 1250 597223552 597223559
    0x90b0c0a0b04080c0105070e010915021f0207080c030a170f070f260709120206070809270406060501082205210d0609050c0708030c0d0f020705120a09 66
    0x581c241d40750300c01e120b105410f01300100e40c5451400d43c0c50603106080410300030116000c1c1561310001000060007494481880d42d1b540c544013075110841c3d0700c04150180b04140619103100c52030740407200880c0d44001420307511825030b180d984d120f400c160345c0d140021380a041c6900da070000381d0310702d1405100b0f44010f44d86079880340d02094a41842c013082e25814002c41d001400442e507103c0a6100f4035104541007281d140c81d111400500d805000d411003c1511541d0042c0741c05a1610310995102d10f5005800983e105100b0340000c9004011401900595906000c2e550310001803a0809004a100d044140009612000150760b5807000315803100811080f050f420042c054181d408035482401501074440b41190541c03800c0da0f00b45c00216614a00800044071a003038075040c802d0b2401171400030701c00c0046044c2600007000500c41c1013030150840700084003141800ba1000704840000c821280100824024408440065044008195040d000ea01c2c031000320829200100c0b400c0e0a2160340ea000341505 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 597226052 1250 597224802 597224813
    0xb0a020a120e0c13060807060e0a0b040f0906080a1101030b04240305101a0607050c0d0606140d0228050a0306270215090103140406020a090b0c0a 64
    0x200300320381000031008000303500720359500c50303084240c0607140a07003000c10480e41442543c0c11038000044055140130001c10a4660101d0300c8825200180740c01c6807031245000001d039543c1e4030381e0041186c0401c002800140c02400310309a10490380740103014050036176141c001c1034603440041c4002c0c12081c03003100c40c0400e56200c0d5125030b800410090000940c8404800b4180e000b0b54200c2920f8941c0d0084101070081c01410001c06121410200c400c6c01590318400b003a082001001c0003040c002c5c20040780d40b00401c0001c0c007600c0c0d60401e02808504440c0b882c2c1c00c00d03038083c0c0118400d0041541136080d6207841d5050101140460703540182c005d5680081010b0750001c04006100c2d0080500511440400e00e0b0303030303103540100c001c601600010032840100d44100c0190b4102800c0c1407582910340703e100c001a221000145800740700400c08548a10700d600044e009031003004810003995800030300f008100600f690180c04122025501c2c41d0380c840e261810550f4a01c5130704500003044d031040f10b1b80c40004a = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 597227302 1250 597226052 597226057
    0xd290c1201030314160c1403211b061005130b0f2715180135030a0906020c0109030c0504020c01020c0a0503120c09010c12020304120c0515070b0a02 65
    0x11910401e80c0d1074001c0480079240d5400d085c0804607960503c01c0c00030407a400044400d002e28440072805030288c7c4c0340e5054000102c804007005401140004160540038220305070a404101c44900140c41c0146041440824580c0103409614400d10500c0302c2d00035100d1aa00c101c41c0c0c03c610181009810899202c100152344003030000b842440c81a1420480e40300401103030542c05030075407404000030ba09a440c2049015842903800c50445000e09004000d08007900c8040300148841420802e5040c25084807140403803442503803c3e40074803002a83e100c0740d6601c850200210317256036094400044240c07004440209c107030320001c0c043c0c18120b00b00b4080e92030b040d0b0041203001c890600052030004407002c0c0d1800d000c41050107403041c0e0000f14a11410008890710150b2004034845842c0c03904144000103802c800828074040c0c02c0d03802894026404600030411100a001d0418000f002800b170f81ca8000c1c0b5012040c040c1c03c0c0a140c4643e2003e0100c080a01aa40e05e06da204c60940040c1d07452010080094 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 597228552 1250 597227302 597227327
    0x6271101080a110f0304060f0519090f120e1002165406060503040305180a092304120507030512130501140403120b0d290c12010303 58
    0x8a03903c803000a010b500c803000070145008003802441e142c0c601800d04000f00c1348c800300e81c4d040890801081014a0052039000c1064900790440040c0010f03150424441800c140c0c1001802000314100701000307240c00810f80d038502001101c125130f10350808041281c8400d6100c030400d0180710192418480e034400c0350038040d10f130001110f0b0380c02c18120f826220803d80c11300d82e1940d0400709054000c0c0c000380e1500540b11319001e244070010702182c3d00d030441c001c085101c0240301804004020410740c010000f50801420148001401c000030f407616451500e0081c144480d40c0042c05a0403a8030082410005034000d2003a6049013105108540507002600d0350384c0406811020000301f000302e50b83c001d000050060164001100800d881c41c0c5500d4042d003101e00c4a0352010740d04440703c08000000780d112440079001504560040b842080c031300049040000d90110040032901c00f08148500710403582c030901002820100f441c407031074542c14002e10052045103003102159039007100520200b4015040007503c2d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 597229802 1250 597228552 597228571
    0x10801060c03121805190f06020f07020d030e030d0206060307030f0c09110405010306080a0b18010e1203250507030503190f05060310020906040e0a090f0627110108 72
    0x30b0700c3d207104403081100e02e104401c62130600b10000c0042071000c20010301983c20581d1804444002c3c207501c0f80008034403607580c02043c040c0c0025907001e0304041c15040d01d401b41c0e03001c0c0c5852200d10052402406c0c5c0948035070a44d0003807090125104070240b001502030700980c40071700034242d1281940c41d5091602d044000a80d10707071003294800600c885852003051040482d01c02c05a071958142400113040c6c6900e544000c41c04d910002d09030010814044200350440303136200001030710b80c0c143c84045024060000c603507005400352107480400c04d010a8000e5100b055010701c040303144060302152410440d50300c1c0720900001c45c284003c03000680110b00961704200401240700301110485c030a441500e002c5924030044584a5090201e10300f0301700070341c012420b41440c00b03605245205011030a503002c1d500c43d003050580c42c2000f14025004d150302c0510820b411100481802000d410303c5d0b000340401e0981454075072049001758030728110030210031802c5544007801d001d4a80e10035004444003000540040907 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 597231052 1250 597229802 597229817
    0xe040c0302091203031603050105030d0c020109150504030b010501050c06040605040c032406061d06071e080310080c0a060e031507030e0c060705120708070209100305061005010801060c03 82
    0x3000c0e600e43d100390380c94101d079400940c0c0e0ba1600501446620001b9401c0384281800c0100600903a0f6020031a02200c03203061811030700c40080f40c0012100000d85500020310700d010b4002c1d00ca10250b001c001001628010701c1101d4160b66030382d0046070944202e06582c2c107150030500102e00054a03941045030440d005003080c003642916511900420050582000008441d5111000307205050f0301810740186554104080300305070445071880500170500c804c502c504c0d0001a44000c0101d9400c0c101c411141c0340c0b06030705948405103480d1004c2c0e401600d41e1220002c2030200003404081c00a04182c111501500c01c40b004c80c5400000d5642e04c1c80300540e0b580c0b50140c0300c1101d901600c032411462050809d45e60125002140084003030a0a01444401e4000c2d8402c204402c00f003400095014121034510a900355200d400b410114402e00403890020350003810304080c8000c101c200034020b000d0300e0003001558440d49945182d00b200030218852903001c6480c9c140100035031030107203260000f09030280c00c0c48030 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 597232302 1250 597231052 597231067
    0x1f03020303121909020a17120f22032d170406270e090f0a0b010f05040b2b0506040f0b0915130c0305030c0a0b090a02010e040c0302 58
    0x2401c6401c61846041a145100100070b000349408500c2c0e00040c01000040040001c1d980104840164900500500110b0341130754000c00081081440c140b802000351180c2c560400d04400c00b55913211541c007200303060040030301c05651030b4041c820740d04507540400e20270540404115440c20b0048010801418055589035010200380d1910700c100320710b041c5100407942c8d81d0409002402c2c0c2c032621034003441901d0245010144112a11029400f607480c2480c0070520756882c2d200d01858250490a1120b05000344885007081203000d80300c1c281a40c05110f00070012644901c1400300f02d40300c20300c0c12984080800b01190703140c2d01c5c4803407179144c2c1034028a001c14a450140ca6082c6007960603070b01101e4415206d09910b0a10030b0000003283c0045181000e82074000e980c8400c0c0548240103082110020b0268580c2806c2107890303402c1034001e503444010b803a1103500e00c0b03058544a9020500030780e00b441090303001402c040c1c00420749c4040305505842c0c0100300c00311b20080c0001480164214024582c0c03c00602 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 597233552 1250 597232302 597232309
    0x1615020f0a0905091e06040504060608070e090606060f0901030e1e0321040c0608130f1209060504050d0b10080703291e06040f05010920070206031f0302 67
    0x422040070541c407400c4019141c041844000d0070001c200a81e0b80510100c1c80d200c0403501650340790456801c41e0041403079115801d0950013095a507200804038401d800700064690386d0000068407607004c04041d150b2680c0d0700001c2c0000752207202503ca10b5100c3c20441502190b000380e001508072003842c1c0880707444906000d10711001c3e00054400051580c80401d04490b444207100c21414500545144161030741481d96a08030b00700201e00442091010040c0040d00c003404030001900340c40d40052030100400301c039041080c01d01024464600005001c0c001c00320791700c2c1c01813084404035040503100c03100c04640c0d13440e100d0b070300c51014025078581c00701d2190006140d0000c21100e40a0350080200d1a4000d401d100b002c1c400d01500980180016182010028860401040e40e484040703800d5207866903560b203100150040c480e4a4a002056203400300106841245070f01510802d800c449040e400074800710b5a1100c50b0003904002548000c0801c00910b0140c0ca18607a42c51004203204012503540d12507000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 597234802 1250 597233552 597233557
    0x10e04081e030a0603060b0609090402270f010602060f0118020d0605060703050408150105100503060d0515090d0c0c17150103110f040509100c1218020301050c1615020f 74
    0x10361400f0398444900b4018070540d071040650080040780c0091521800300e020403103620004102038481c40703840c6112120748070007c0d550708022601401d54815840c0401c0d089181c1202801404014840c00c40000c8801c40e005446a05aa080c103298003200c46000c503449019502800c8a1265161120303000140390b110280074000203442501c407a0307200c41c10010307030078503140e920314004010303041d07002c01041151140c0c62070500c03141c0f030340c0303401541ca562f500041500e0600000c4001d0561150340c0400740600a0456003d014003c5035054982d0182c1e0900c044441c0005800050115610804c0c20840030316005510598000590f040c0d61069598440000e10000300764401d80c3c18084110810b005450b04042c0084130b004200c60812160505800040e5a01c80007003035110320b55503906040000c14003a04240f00c003030300780210900155840c0300d1494201000424102d0181d0300704404140d000154109036516217000c80c0d0303480780c181d0a40e20752040440d0058040e611040d420064455000600c000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 597236052 1250 597234802 597234811
    0x10c0203070e01090b010c0816080f032502030703021c0e03070602060603100e10050a0b040f0902030c030304061b170f0a090b0301050f0405150325060305010e04081e03 74
    0xb0100d070390f615100d004000d4852050965041000012140f00010070103010780740c13424051804031007040e0080c50096210b2107004a40c540300e09020081001407529105d4940100b810741c000d50f0440c2c0400c61701640d59000c1d812004016030000d078030000101c2942030102091800c3c52030500f003481d8005010a042440580114005820000412505090401140400c0c0c00d0300c00040046942441800340c030b0f1000c0440043c0c0c40f91301c1e271001c02c0117035100c2c0d04415241d0100a0041040c13808003003a8400410704400128024012110040c0051801009a0b4210f902d0742e03c802000010012003d00c03103588400e400c40d0700054004441d201c10803900e0150090783e0703140c20081d556500b0381c480501403070042d078000241c907141080144183c1d2120101d8042030041903c2c0410562140c0c0c103803c03540215050707182d03014890341c01c500c3e15905a0004045003001c044261455564035290211300741c600034090b074800600d03210086400070303000030010032246850040004403091030781c124003419402581c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 597237302 1250 597236052 597236069
    0x602090d0f031b0b010b0a230909130f0201080702100c11060f0103080a0e030a02040e010b0909070b0913140708070311041203050a05070b010905010f060c0b04020906010c020307 78
    0x1d640010180c004000f62501e040189000c96502c506580d18403201005029207003001d5800f06887c1e0509000301c1c45041d07140c1030403104c1058001d8164218016420031a0740c14400e8100c40003040b00b105d10005d60400450f0498003170f0303500701c0c590f40054414481c007609030030031486004080c40d940310051180c00511610b5940d02c0342d000d001d00c10001e190140c00303820b0b1700b48001a0740c010400100d40f4821200752040d40d0030301400d158000b40020f0709040e100e0780c1c06504241014070342201e4982c10340c4840511541201c0f100d260340c9a1a9038113944036540d02602c5407083c2d0412004903907242201012040408020022a40c0e000b15801040361a00a07910080401c026800340306280da05400703481c08040b01821079900709450302440e0b00c60304c8a500c0000d4103100c2c002403444c0001c0c0c03140044030724a5420413a00702c610759413071514a0040000344285600b41c003000c40003150180c0f1460308211500e80010b00e08002d51070359003c0005000001d45003d0622a40d0800040141c605002e107000800040 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 597238552 1250 597237302 597237323
    0x100c05030423090a050601081b0d020c2b020a0204050c0921060606070c03261b07090b0d1b050a060206040605060103090201053a090210021f05040602090d 68
    0x100180300402001a00e01300d03031103091008110f00c69038800e201c954841400c1e481d031844440c03000d20206442c4181c2c00c0303040c1000d0000420b40346074070300090401240396495000110803071031500c182c0e0860101408100058209014440161501d500016000360210205514141c1a40b001401101000d0070b00b00303851701d0500103480c5800041c40701075400001600d070f0390b16003d000d03a2030303900c442268000100f4030040d04e010146440d0603659102407080c604a032090761b900c00424002151001e640d04420184503000004c14078185a010b1140c0c8007401600f4007000b50407907603524000080020008060b00d018640020703003a80c400d20312400814141c0c02a0003541014204107080e42c034001c0c21141032508204c070150060364080201e550080400001010108004106c0110070010f105080485407040c5400e6070752070003a5000328001d510072142499002d001c4141aa2940031310340705020712480700182c00900300400d40010790301c184104001490a90f00c1d100041006803030801c15110070620 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 597239802 1250 597238552 597238619
    0xe06040f0e07020c01081509090a0606121101090612050612030d240503030403020105030919080c061605030a090201050c120306190b03180f0f0d1409100c050304 71
    0x14070001030305420078a0148200d180100344d5401c0c070f112001c0098064123044000505400c4103005100c041c2ea0320680601030103a079210390812500c0719140940c2d840882250703800711503015801041c104d601a44903114421040c003690ba004041c001d00716034201c039545042c2c1c003161205000500c001e2583c03a5002074503262100c4240d0101a03084120003014070807801c240320741d82e80041503d0407a80d092074400c0d40d039034071002c24500f0048080e21181d03407204040c4043c0100304642c5c0190540b103141d0b2045910583d6825090540c2c00e12403484000856410008201d0380802c40e04000d003a640181402c9140c085184241c514015054503841c40e0351501005004a03481c1c00038403a4101040f01c019500f02d9810b1403500d06040c8805002115007045c115001c485400f001c5c0000f095905c0d08a090f24014900e002d4042e03111551008004000382c06901ca140c11511300c001602d95900c0060034000140c40e044d40c0a85010703a80e1103007900c0922042c44000344210351605980c203010841d5520355100c001 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 597241052 1250 597239802 597239807
    0x10e1804120f0207230a0806010608040b060105090f010806030111041e050d120305040f1e02100f050d05040c0509010602010c0f090e0f060402250c0f06020303070e06040f0e07 77
    0x4184a1080440d040700b13000b005003103101c0c810000c2807030840141444083d0351000161884d207865001c50600d01403480002030a07900920707050301c0b450180d0f00c16020f503900c0800448243c4a400001c603801400c40b8900c40c02540310ba90919402000075000140051a0f81c400305810b8105a020050180d591882050f800d40d540150304000c2c00306130350488150f4400d81d180d10700c0000402542c4201580c680020f800d00c43c5007a80c003c0c2840c2c1000d030010700c0340c510140050701e548090340140c0c0902a203444c012145480b5503060188668590340f040d0414140d16044005004090420784000c00205000300c1c0c00d075503c4100e01d0007080103030000191429003820152102440581401c284030408404001e1400344c2800315034416002c1240f8815070f600d00c00000d009008258900e1036604d5001403010910f0303c94400900c1107030049a28054003660703000c00152120b118022200142c1060000c658a540034510503034001900411090400e9210a0319117803128490f4040d008a038603040070f000d030868 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 597242302 1250 597241052 597241067
    0xc0604030b090c0901231305010902130807051c0203100606050a02060c030105130e0709051e060405090a03080a060312030207061a0a1403070b031017030703020705010e180412 77
    0x40e07003039914048940c980800e6200c00503511b0325001d11403510b05c600c3c041a5031081d211041c103245940080002e540c541060400075000428100740b404d82412002c120303014001a80011650002d01000388100c0c404030070000c120010070100e030984540d007248012650140201c001400da40e544054903048107000003880c00102400e941485403003040140142d80780c00d005c01c500081380c28001700700d0034413408d00945082c0c9954480c0f03e00c240b8150900111018080b01203c01e80510000400c080c3c49034420401110020b41d83c060b8a03034450041000000e02680c003280c0e000754842000589195aa15880c0f00900e503c5003450000c2e600103058410000c0c248207150285500c802c00c550120303240004595000654044d8103903410340f03080c480102c1c0d41c0802c0080c0142820040307180d00d0f0b042007050000c00000c80d00481300e210280845000104d130002040c1d490103501a8020b04240e407504006603406541d140c4202e8005e41d02d00041070b1101c00014910380101c1c4140f50b0a0b02d10035442d04006e0410 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 597243552 1250 597242302 597242323
    0xa0e0f07090f030b090a0b010806011701050610080414032808040506011802040812300112020406030602070f06050106050901090b0a0c0c0f03110108060310050403020c0604030b09 79
    0x410072007800302801590b03150050300e502c010b540c402d40d284c1c0c509203454002000340080411100500104501c980811903e048800d070300c500c0d4034090710034580982a00c2c0f040341c110340c0003c2070030960380031148600b080d590010300601811080a082e5507030309081da8071904030b00e0b04414203100f51000e04018901d208a102446141081060806aa44940b6550103106a0038600703400800c070f031081e00b115030494000b0b00494007215070800b840303001d00300c1581110904501c4c2c85400d480a210704062050351002d42440d01040100581c20903035248280c8110720420703608283e031040d004c030025026100600c596400380c950308103100311b03900d0402e05440f4160041002c0000c140301140c2c4590300074400e1401d07180c4007a44a45c0b244526041264440c0f82000050078180140c08001180317a40702c0300c21010b0307070302520b440c11006501c1c00041d80c1006d015190544c055010156281c64401c0540c840da400038840d01c10b84601502040c005000c03604140c0080e14080900b00902543d100304000c520000d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 597244802 1250 597243552 597243557
    0x1204060b0114120f04050106080712120e0109031214030705030a0b031c080a0b03120c07050604050a0506030406110c1501050d03020d0807021009080307030c1713060603020a0e0f07 79
    0x1020203c8000b080011009480078610382d80c0c14000c141084400e4100d5000351021741c0440c2c0a5039030341c19110040c175010b00d8040e903401c0740c2c001c00c0d100102d1041e5200581080c06840ba1401b06240d9900d28030340940c40380d00c25040110341901c0c42e5994070541c009500543e142c1e65000d4880c1030813083ea13000c0303a403610340882c800c0d441001214510752640311500805c0c9610300b45201c26680e8843d511001e8009408003a82c54000c41d800010000064400307000303111540c40849011315116003e00142d84a903000d240e901201c5681c04200b036141240085a01900c01c4001040058007542214640d4008c40180c5009400c6068065405120f205074103005040807664240c18004980b40a034603088200e040d8020004542c001510060081001100b01105850100400020b504005400360419501880064141007180d2200d61050700e0701d0491103010102044542c89030560002100c203075031400c1755800d0700ea4100101680e0b07040e60600003021403891030010340c41c0c910040e000e501d0000380b00a05 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 597246052 1250 597244802 597244807
    0x6041b0210020c030c010c1815050706020c0f2b0212160f0b0907170c1003050601021f05010801050105150a030207020f0d03030c0e040c080c0304081204060b0114 71
    0x190603400680c2140351981d8400060b50380d40c00380001c90551150758a07107041503082c08070350516154460641c1200329881140b036810140c407403104807032401d0401c0b04440000c40900400c0c010518960052054205150484000030000301d01c0c241404a5042403008403280010b641c0da8403401150b402038003250503c0035040b10040c4a40700391030343c0560702d088407550401100c01030411040d07000d0300880d01d801500350589440c00024495980c81a802848202049000280008003000560303000c0c89d00300400781e005041e01803100f14014100101040e045220f402c0300010400302945540c0810090400042010340c106003820b03081d6441a80600d010f80030340c3c5003140c0d400c1100002e661600040d0724000d41e40c0c1c1d1035800090021010450002c1d0300c03441c81e5102500300764141c3d1089806040b1034846407104c1496500304411511500e03028404140480c002805000c0407400543e406846400c0542c1008844141d015a80c3c0707044074100e0304250f07100c00b03956540d13030003c14620080d10364844961 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 597247302 1250 597246052 597246101
    0xc040e011415030c030108010c0509010c020405091c0309110910030809041d030702030c09191e050108100e03091e010c050319030b06090102070e070302070b010605030604 75
    0x4454550500c5503001c00c0c039502501000710b6890000c0201d403001c1100d00c040d200c2c20311811015581e4000e2141e94a44d628000010050500890640740e00030320503118581043c40507020f210107030000130040740032401135400701c82440340f2000c2c100304140c5031a80c00044c02e14071403030500d1010007030310b024600c244450360401604801440f03150742a00c2e4072000e683e0b03c3c0c141020208010340a6010031040341e221803a00300203103290000141007464021000c031442d00c1808c400713201d000041590708842024800b09031801905050700045044603400c92086e481219503540c8008480c000c0c3c0156150750805410401031340024059051010700e884051403030114040c001485010352442e0304000155101c481c23181ca6070052042d0000c02740c12805980d941d4100702c640d0511402c1040c07240c00030901d0440201c1e00c80c180101030707590741c49040c1c000341482400c0034661002207400500b04401c01d6000c1040ba000144140c0703550703008029986a0340e89a08062080009458a000710f44c030050303d52040c1403 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 597248552 1250 597247302 597247319
    0x60c0311070506041203020c09073f0c021f050115050309150702100609020c2a04020705030d090302071d1b1c021218030a0c0305160605040c0602060c04 67
    0x80b800c45170f0180c0d00140d121054a010f80c10411034000d9203078850400010403214036080140c401c10014040e081d40100d0f40c0d0034009044401d02e01c10010040d000703030425407071100441e52000c4500381c0980102d45121151901c01502e19018010600b0050348520040100b00900642c00064a01508045080d03150904000395580c40781540c0c0d500440c14030000c584014028042860102c00341901840071039141e0150b0806948042c074810b020b031040e4880810390100e14598000006410070180d0341022070801000041d40203040b0645040c0004c03c00750019100610550031213601c240c02030040e00303151294052081060f100c0313042d038500415041011247c4c0c407400b401001d0805000301902c5400e0140100c400088036400d08080d68400901200d941c0c5154000c540708a16000c1c0321071085048001041c4c0f01c1c02030600d02c00c0464071088010001074001e401403c1000a00450541e0002d8181c0740c40c01070703800507903040c3c590a4544409228243e810320815070310003580fa8200c0d1a040c07802020 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 597249802 1250 597248552 597248557
    0x305061503013c06120308040c080c01120504030e090f09061b030414070503030f0d050a020a09060302280c12081012020a1e06020c010e06030601050c0708030301060c0311070506 78
    0x6521102e03c02d03032881c2108201980c02a0050000b40d05008100070140c50003402c80700058a043d1003043c580280051010400944101d100714117a541a600d4903503d402c4202620b00544202c0612503400d400088907203032016400d00c6423a52900c046103900340488076909201c805407a001801c058401d02140321130085040301d800c564442d52034106c15500404403814650581c0100340c0c14040040c60040811240c0003a000c3d0541ea100c04001c00e03101d0082c480203e1054080c0070303001c00c0c101c03003003000018000e07806420080010852058400003c09000c07184103007030f120305000301d030131211540288901207135654a40511400c0444860900100403d180aa40d10815011000801c1e1701800c6450f2050400700410351440c92490903201d4030b10303415000300c0500038071005224016440b100c3d90f11421030103140c040f000e8025451500c90b00011111a84040c419083c98400c2c040000b640e034101700300540c002c121564800c04051020303c0c00070241100d0000c001e41961041c40d0a0000d81d85c1d1008 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 597251052 1250 597249802 597249881
    0xc160b042607080d0c050c0f09010b180d03030606030506041109060d0f0e0a0201110d080105042708040906050f1807090e041b0e070c030f09030506150301 68
    0x20400301880c400c03241d06141c00481c2d0008229030151403004060301d9003150308241507500c50026a0341c0d1b00040000d1009400010180c00e41c007204850040002e04000e00040c00c03018034010504409140d050041840500d00e00d0341100025991081000503551500c02c450304108100e4040c0b1500404200e03000c4940a20b0030340324403070a800102807464005d10f40c400d48403198680d4090008980300d080d102d4031220000e005901081c820200c07004d01c107502145070400c46c42d054940d00120790070001884010020600d80a0188032038620084481100141203c0014812141180d59a08010280040d548184c1c00b490103500100004c10040e6600d444080c2100380c0c1e000d900000d42e0300c00b03c080702e10b814190300c0110090715030410f0005001301c40e00302c00110361a07001e40c04a125901c000da2100014210ba2000008110600d84030019110f030000030040107103072500003006c503243d49030b403400e1040503503c1e6a4075890301c5560140c02d003001c1c0141c0c080f9490f10003840c420340ea40c070307110349061101c4001c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 597252302 1250 597251052 597251099
    0x50a0e0303070c05091f0b090102061b0d050408071506060e0409030e060706060b0301060e03060c04060e0112150603050402040c0f210f0e0c03010e071203050309030c030c160b04 78
    0x8000407846e600000d0030152121075003580003102139646a1400c2942e02c068044da006004e04000691241840c2c10074490704910540110b1a11000302c0040f401003101030011140d516080000300c0104041701d400003145070a0940004402c5c0c9444800351140c01300724000c50255091003501c20100740c01407910070140c0c3e4152050340d5190f1480c81d10a004003441e40100e04405000b0002280055002c0c0414203d03507001c1d0110f0303036191901d00c601101801940704082c005509000e0b03007107003548a010312002c00340214101080340130312204890f06013101c6d0703000307400000d03510700070001546424011209848490304040340409445040145981105210b010800701c1d60001c02c2c0706410698040d03d07030541c02c070104001141e100e40000d82c0340c2e610705034070510a40c00c0c00140b41003c80d0114018089889840720310107025142ea07030030341d0386810080405945000910081c0c031081c04c02e200800300103548202401c5011074000094401581c135130441c0b21790708030601c01072043d1004800350300d25812120 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 597253552 1250 597252302 597252319
    0x3090c1f020307240915140c030c0901031415010e041b0c0f050106061205091209130902090f07090801020c0c0d05031e040801060909050a06090f05060403050a0e0303070c05 76
    0x1600c803a0680c0c080c0c0e200c240d4080e113022911414020074070300d03040c55034443c006c0500030b4181500e411041d840c429207200e034189100300042000d810a2a004150f00030040c10041401c0c1c04111008428460440d2407c04400c1042c040280c1c940c0e003d1021076512000302c2e800c04c49100102c00e0b000380d001d04901c01c001401802c42c00e001c00d102000302035001855000c4000e00031940c450034018204890500690308090a080204010803008920b109240d03030260007460506680c41c0c10803207841c900324404c03d111650b82064401584606034000c0c4200e08203080075105003406000241210560303844000306920511000b801140c020821640c402000c4401490b840c4050510714110720a8051034030402d00e50410008402c0180d9016104a848410007001400d517100c2c465400c1e152022401040c40e00090100c0f0700050241d803140035944c0c003840510301407001e203980b007902e40007041e14241c001c55001318101301b103181e000148010700c0c18142d02441c28215255900c0d450407405000321407254014 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 597254802 1250 597253552 597253583
    0x609020f092b0302030a0e06120a0203100306111b0a2021011a010215061201020f0430030507031d031002070b010e04020a120c0b03090c1f020307 64
    0x5020054020200902c102d10810702245000303550790f441020030700c010640046401c125803a040060750b0b010689800b0000c83d076070782d10007400f00a61000701081e043c44c58815021010401500c24034030200a03071410155590f0030b81d40c941d061000000082e1407940e00800389100003c09810381258464100707588e0403041402c0c503000491910902c041002034841800503001142c005420140c0140201c101c40e0b00403121040c01261102d8221000801c030403e500046038450400300304a1701560018400103003444d034011031552865006030704ca028120317440b8034220f80b06040c00c485103211132907244070b0045100940cad602a01c14002c1e52000340c148801e03410303800801da001d40d10314000c01c3c00c010141c2e0700c101008449030000703402041303058800b203240600103d10381200c0800c1d140a00e03002003105012a00c1c1082c1d1305541180844100c545000f92071703001800c4013030700000e14000c0c4081c4028181c07803c403440900c003070506020328111944501900903541e403600481180c0c00700b40c1254444091100 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 597256052 1250 597254802 597254839
    0x50402030115031a060a02060709060207210804030b0103081c0c1b0c050306180601140f060d020405030312191a010e011103031f0605180d060b0d0507090609020f09 72
    0x203021803501d420145c000340c045151a404035815100341e05a44030001200d444400403a55071641d80070b822007610000704440c142e4504014488022481411a240340c03a48a40d500e81050500380d100300c540b8800410f140a240303603481403504072582400b804008260103c0001410b6000160945074100910516a800d1284e0880720201400380501114140d04200b4410716030030800c00003129030b50107410000700320252002e518001c9c4c50402000ca11f04203910604120003a8400342640004c55070800001600f510b0030700c06080807156500081c840c0e458a903080c007071145884030580c03040c05d2901440c80c80501c0010a003200d800400e1070801001d501850051320740b4039201a043d1610710003c81000f00c0c111a185054010010340030201e814290303540b000b541c00d402003403040845100b10109042c142d041c400018807800d0300a074000b00300d150798000070604c15055440306441e540c01c4444103005030074660244800800440b0800c6260100301410300809001d0300d07041e0741c0312701594030b400707615a81c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 597257302 1250 597256052 597256091
    0x10f0e0105070b10091109030c09190f020901030609090213020322080c0d0809103c0b010f1b060212130318030203030d0e1609051005040203011503 65
    0x9520040c100c3c61414120510f480380201440784030b01c41130400050113200c0104100b84c40702c100d8090000d1107421401000c002ca20b04000780000100c0d4a40b00500310041c040e402440601d803000240160b03150140720004003a120940c0140c0c4850f41031918560050710354400c0c1c3c001c0c695064400503200d448a048000080b8040f28403c06a014109000e0301070003540381c020601c0d04400c1c0304440c101e0070b0f2544141c6d4443c6040702c1045a079003041c0c1003c0041c0141e034006074200010210030980701c2c0d00d07400071071140c0242c1007202c0410a1001001990400052091240e42034003424580f4010700b10100040103002e002d00c0c003a00e20404440c0a000304900e64040d1503d00c0c1004103008403074a4045c01018101e59072503c2070f000920018001c11200350b03001150421360342c0240246290030b0b4600c5003080544544850503c2034854a540308001044511011002d441841c05c041440c0c00c05085c040744803000c1e03410043c407443c41080100b2000351012070200e460000c50901240030356281c6140c000f0705 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 597258552 1250 597257302 597257317
    0x608010e0a0507110703030206180d0504120302030d1b020f06130f050a02150d0c050306011709150106030204060905030d02030901210f060e0a0507020309010e220b0a060e010f0e0105 80
    0x144505c0102004042e0081040e610480140c817954140981d003840ca03035502d600c001400c0000c1001084213100d00780640b48640c04550281c011645400e0718241c00e0300841c3c03c0b00000040ca940443d015145656060201c409501140f2000300b05500380309000b2641071540b010028078005011401d0010400207100303499000d4bc0017458110000c1c204089948141d02c07259000003803900d88555074801d24099003d49005141c10f030346940402103a68009070b00040b000d01003c1040c458404400c1074105032060450281c103042e50050f0301d4518010340501010b0746600310074403a402090042c00900c0d070002c02c2c2ca90084003480c01c0d600e10742e2828240180000b00c1480c014041b82400c403091449803443d0044000c56010090250f010381e1005e040381e080b02c0d0240d5101c80107800401ca9515258800c1d4032240d03900300000d01e8012400f02030424040c1c1c0d0916260030380420f50711060034103481c0c603041c101c0300b00514181c1865066180000002070643c0c403908800303070034480406c0511880d64801c40645508 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 597259802 1250 597258552 597258587
    0xa050d05070f150c021e0706200d0203090406060c02060f1b0f1e0d0c14010b18090c0312070b0a0b1c061a0d060f0b06070b060a0608010e0a0507 63
    0x8400c03070082c0f242c042c0541032507040151286d90f81001185040e00c050600380300c2c043c8090101503003002002c60fa4100c19000700d40700744901e200540706408060120070103d101c3c1d43c00466032040300c00d00340803e8900c44da1003041444045440e1102580702d04080343c02108046076030650f00c940b00004441a01031004c4000074034400e400401d62440c0c0000780d02c215244d0311208800315100070304251035803140c1ca54a003c0001d410365030401c000440a4001d0303610010200004504101c140c0c0c08161008841840c0000c120241030074015002c105104111000354151f001e86200f54202c3c0040d0040d02c1110340c010400342181c0c00003034510384036511078401c026000300909407502d511003900c0410705200320290b804610b03004c420b0140102010412000580152a1200b110440c4c0c945800034003881c40441d1001f03485495a00295480c0002411224410007403103545043c000240525000141c01c41c1c4c1c10300c041380700148501c800420106501c40c10751f850101d003603907610600302c80501040d00310030403 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 597261052 1250 597259802 597259823
    0x91d07060203070b010b090609040c0207080a06020915040506030f04110d03110c01030e0705040b06070618030e01030b211e072310050703030605130f05090a050d05070f 74
    0x40c010307408401460f1442c0108085851643c940e00c00c00c0d80c9129035421664800020058520380c0c1c10541c021900010f46401911034440d6202c08890400881046c2129126400107400b2220316026501c18800308003026103504103801c04012800c01d01c006000d843d41d10341d00381c00140820444034200ea41000300a4a115400c0e403841c43c2c003410b10b048080105500e4080d080c1c5034111548070388900c16400c014413000b0143d0720300c0c1c03405101c02006030b801c0f282e40055007000a03001141950203101c0c1c030b003140401c1c00c6040000a04000342600b8182101504250504000004540d109110540004101c4440301001020524018603018007001caa00c800c08500c0b184200030100401e503113084030000200e128480d004002c2d002030b9190340840007513010346010050070544c1e2141e0003600c1944d10a04000a52a445000107407041c0e184d2123003000400d443d20b110040c0c24009005507900680b00303e00808055009907240c81d120290202400c0c1044400b0039684103000380e22200b00c055a800040c07003403 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 597262302 1250 597261052 597261059
    0x4050a14030a080d06081c0806030a02092d0705042301080a0209030a060c2a0506070e011b080a14090d0303020d0f0e060108060903040605040b0901091d270304091d07 73
    0x2694911f414025000c2042480080d10b641400318500c000140d00600c050119603035080340350300c4000d80d1443c4e200c04641c01c2142c90400380d00012104e0040281e4bc035620b07102d901d0a0301408000c03180c00c854500d11036000e0398243c05642c10800c42e42d00006801c602507112070b80c4001080c680302428a02800490907d403800c45165003012100300c60124100c1d910620510042160039107084142c00149281d22110004100c41d2083d815801d1154051608100c11100105100c030b02c0640f60009403038030080090071140c2c0c1c039002035802c608891040105410040d1003400511050400107005c1d060580000740003a000511b907100308001a1028000c1040b281c20440f01580c0740c0c030902400d20305202d5600800e0101303200109440c12a010b071340e2490302c0c0c40c4c00e006513548180c02000001d814044000b002080381c0031070074490038503541044010159840c190301000418001c0304c148405003812030310902014a804001c48080d501d40b0341020441ca030442d41000c02185081c0300c00c50f014080c41d140071 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 597263552 1250 597262302 597262333
    0x2e050a0506040509010603021f14040f06030b0a120201031509090c09060501020a051b01050d110904061505072003240606090109050118091104050a14030a080d0608 72
    0x64000c4805441c10071440d91403804d840c0c221121800043c0d40034928000c5521040d08502c42107da40c1c0d06031400a81001207140c42d0105a0400d42045120490b019020f000d07081d4544941d9601c20000c403555120249007030f40c409011100c15401a0406496449030158800031001e070f10300070804000704101d000c0340c40c2842900d80390300c0d0003000006820060006503544c40001c1c400c0c00d19400c04040e0608150b082c075400c03200e0058500d0305050040500c1146000c16191042d650320011845400c3c1ea50540042004212506a0801e00c030b62000503017011803059121045c3d07001c155000381c40c940b60302e19005140001c040b2060503a0780c14480c0000c90b1803410494080e00031200401040384403151608010000b060162000040c002150500200015031041508680382600b00084040c500d0302e8030302c80d10070b5034045200381c441b26000042c10030150070010341507001803c48001002204403d4800691908403052024149070004180c83c68074a1540d4400402004518200c2d080c1031410f9a48 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 597264802 1250 597263552 597263561
    0x30412110d090e0f010f120f05030708070b070f0203180402070c03060618020c0a2307090c1101020408060604050705210a060e06030c01180504050f010305010c02030c2e050a 76
    0x542c1ca0b12450f802c0400c803420341a4440c0c90603150021011a00d080c140081d40040d005c0c800b8068600501001500c2c0c0820f1050009050f83e80c01401c14075038a00d510304140442c0c04014001d001000021540740500310350100554815880c24104841aaa880400100a401015005030004901d42400810415507a1017041110101525202c802034410303101c50490041d0300180080350061030104001862000c004a643c106010001007e444240281c0d07281c2181900306c01130b520b9940c070340d41c040d054121403140342e12203141c4000d615160800700f503e40c40c1c02000c1d100c2c031b00035903c40000c600d50500403800d446140c600301650150045072524451041503041d2492807001d8640000032400140c00032550340700d213202500504a5240c4600119030000310104150800541080c0c0801c0660311405205c0c080e206050a0b9416541107050850842e40c2404100c400c2d0b41c0300301321805481c280820009140b04250701000645501d41c01100d0241c02d40c1c880c840489032514003000303841c0c0d036580d02 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 597266052 1250 597264802 597264809
    0x42d02040e0108030304050d030903050f030f07081302031c0e10080a061a07150f0905071502030a020a1106071401091b06020304050603090307060e062406030412110d09 74
    0x841c8466640e8072030782191244400d440c040c01d141c104c01d00300c5000c603000ea0004210b03140f00b460114a05400c5401e51101600142c442c1c1c0740040a40007400a034681c003040e0ba41d04503100c0e4214003510003960780006d6607010726180c80300e031417090308401c245500e014820f411301145001c3d21408100b0351407800200386840c00c0300c1e5416050324043c004591f0485065412240300c206042c0c0f40e03d0070540351101d4107802c1c00442080340d5181c88800700104078401e0302078504c2040c458401041050f0030190304190056450500d841154002e020340b0502e65400100702440076000f03a0303420071410340000854001d2041070005001941c1480010140001c15402900001c0c01880c2035150781d80c00b03181c002c41e1000e951007103c0c01030340180414071251601000030740d0030100a00c100c1c2d207440869606c25060761105082d00485070040800c0000c140300400504425064026140f00815141d100240160101410142040c48800302000c1281e008641c4c140380c1c20000d5044a100851016006004842601 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 597267302 1250 597266052 597266069
    0x80d020f01150b030a1a1c03030b06070c0b07110916020c010f2001090209090105041509170a11010509102003010b0f0f04030c090b1e042d0204 63
    0x220400d2842c02d64071080700548100c26469444e40d04d9240d6000e016003a1030380e00c20f44d940140690300c00a5a12050114951202500e00b01c1480f0640d0501130100c6081890701e90007a2810004100001c1c1407144810650715803024954845407103042c0f501400d840403140c160000f10072000d11851083c02c4400c9401c400721942100d5140c15500011120b48440d842c2c454041039012080e03500d1090030103641c0c41800161400040c0d1005280c0004500300c1d0f09980340e40050359544140001e001c4401e0b1000e408030741030300c81804903585580da8048002070908150225a86c0810080f104512845c410941504440000c0c40305080c000f074441d44400310062155441c914004041c0030002c0300080030342d54620140c11244c2140c1c60081c1c2d1818603071000c2003000100c04100001c29148200340c0250014500500c40c0c0344440b4100072016040342c0c90442003a202d18111a580c00c9a1120000d4040041a0964000c01d854071005030202d0041100e0490303141031a2506071503503040032158040c0007151010b2 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 597268552 1250 597267302 597267311
    0x1d0a09151a040f05010c050a06050601051612110a05030a03150305030a1d1c0b040201050708030702070602160503060420130b0f0d0b1f050409060905010c080c1b010204080d020f01 79
    0x144e00569001c0c1036540c1c0207005800c00550040070900c83d611196111406040c0149401014200104010103459044902c8103103041100855584901c0320394503010820028100c0c2e600903261242d0340c1c0100a4800201612030707811034180c48030103103044015940301049a44910b040c0300c0c090240200f00c3c43c8800b08551000820842e0720380341d42c40c0940102d40d00c408070805032040d12200030219005105034140034003000142c0006501070000d501c156215405480d041d401c000000f4101140d103000741040f08034804003404190f401042c0c490700607910807240d1802505200011041e100f8800310b02d0751011703c580142d00070305069000781c0130034081100c0340c2803030144410070000080c60448005d0700c250344070400a0640141c0461064401446c2d5403118102596640018103480750071104949041d12102814104982402000e24528060800070741600e800079420b0541d003d0134810b4211004000142e14144a080d4101c0c2c002c0d261300401e0741c206008402000e983d0350f403641c17005540c071b6180 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 597269802 1250 597268552 597268559
    0x2706360411040b090f03030412111e09040311241e0408030c070b011419140d0204020705011802120d050a0309140f07061d0a09151a040f 60
    0x1501c034501c201220a64120b090a0820000c45002c0d00601c0c03000703401044034001e80032181c1d003c1001e400205080d0314082c194001501d84140c03420001d40006008502096001447c00c103003500341c180f101e0081e985400c25a50300e0070304a40302c1c200d420200030346002d0b00040d00b01c0c000b004003540384a1124000c1629254507001600000c03032200c000c3c0406070440450105001400c9c041c02142c008805c000c0150801400361030705401c0c42003ea1048031802d4045071091000c1c10140141c518125020302410951440d101e00070103036400c415052449003070020300d403e08550782d40c0d042c2c804158001e00200120a88443d1442c49510141020b9208214a03242c240321040009440c50440c0328076030b41d8500300907050609901a00340044100c419001084052201c80d0003089484c031035090410040110a1520102600303032880540102c1c14010313994452441a1140540c101c02c85001050014160703000b13180000c0c586540d0382081c1c24002c0403296425104a47c0d1010380161800c1800a4480316039 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 597271052 1250 597269802 597269809
    0x31312020d0f0309170c0a1e0e0115030c03201b1507090b0a05070206161a07030605030a11100e0607060b03010605040b091302010201110a051905270636 67
    0x2017120b541d920031070502c0c0a108003240b441740043c10305108c81c1409400ba840f40440700381c0342001d80081000b00290765061003a254140030300c0c000c03c4a50304003000354008124a20501d81d000074003040706107000144010307d080084490720b40310340d481400c4d10340c142c1020b844002e10700c0003684c504e000200d0012011900b0700c0d0a50498000446076150f040c0b0b8400c41d039090100a82003160080040f2620721110030218001c110b200074500103031601684c551403c0d000140441d011078208500a0b4002060f1200045400030060341655046404003122011440c0481d80c04a000050a810440100315501001100d81011001030f504800902032a80c640c002c1c0401c85000030b005941c13100007480070681c10501202000c241c240113100100c0d0b1212500c8140310070350b0104051000060001485002c114040803013000a101c1918190340707401c40da511000f880069580c0e035043c103800d901100c203005540d2002140c1c5450a201c49071481c94112007000490200c042c0300e10921501640d07661003541c50b = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 597272302 1250 597271052 597271063
    0xc0a0320241e040506191a0603060613120302071d0403030e0709050c0d060b0705060412090e0c19030b061b01090204020301031112031312020d0f030917 67
    0xe250300785024908000c0540c0604940014000700c010394072036220505688400000b4501c0307103003c0c0340101071030304100720700c2011200001406601c0b54074040c3c4400e4000c1a07a01c24107400030b400c03500c040c0c40c3d845074400569503100300d042c94110f441450400003070441d032303840d0b00310601c42c003036003c3d80c8070103a90360361503010814103166500d00f20051000080010b8000c1e4040c0366040c41c200115007109856250300000c0f100141d6101d40c02c0c080101d00200898000c0c0600c401a0511340641820800280ea640340d0b40d44029200902c00c1003a4060b81c072616115218401c000c06500c5120b006605255440d81c8496105042034402c140f40b645815189174001d000e0b020203074101074443d0b89081030000410302108000702d2640400e54807481c0d0740b400342e950350014601035400782200e000343c40090420404184002240007101d030700107100381c09210903604a4102110b944a40c03070707814001c941c400182603c1d80e9410090000c0c3c144e54404c024943d01071080c1e0244c1d8507507a0b0803948005c000380e506a882 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 597273552 1250 597272302 597272323
    0xe120708010e1018170c0d090f12020f0d171c06050301200c0f070305011505190b070305070f0b1807030f140a140a05060c07120e01050c0a0320 63
    0x5496140c180070003c0c912240305c503190004c5071a0310307040c6021591503500307000240030368100080444400384107180400f01508000c05811084034102080380e0b000ca11038070020401c1ca0304c03482a06000f00f09103c40521001481c210140c1d0b080c0e070765900c0340395038410100400e4418408524001000c5682d080c144030b800100c1c1a00305440c00e1200c00b0000303c649030740c802c5d0b125030064013468540d0031105208002982c003540c401c1001181c2c80c1c281c242c508031113031b500b42c0c09207104141c00740c600c41003014034940d07140c180c4000c2d4000564a14640c01c0c1614207100d006c034000c0182c06003068440500002031281401000b507548103ca1181e00c5165187c3d550354140400707042ca003401d80300c84c40000c42003400004c80d00c80c204151017840300c040d00c4010b0f814038081c04c06540c0c0c0d00562080c60400c20203000706913201c425003c409080032165100e80d201034182440607018894421130340c645d00ea0113603095840c940c19010851b0460100c03840c0050000d040d901c0303181c4100070aa0086100040049451440b8 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 597274802 1250 597273552 597273581
    0x1d0109170c060a0f0612030903170f04060c08040e01061106010e0105130b190803040f05100c0201030209010201060b0d0c080609040308070c0c050303030709081614010e120708010e10 80
    0x3103840c0c1c15a5800105a84c4204008a0380e449200061007500807841301c1c1c0c041e009072180c2500034954240446840411076140121490401000d15048080c40c1600e003a03c00c0e51400402c0d185013031a00d044c5610858000e409410744032000024405d03032010b00e038090b00030048203460840e6078518100c40081d10a001d615480800444a0096003001e907000c4046600b000f0480940c810b20304002d1642ca01d80c42e040262242c200240c20300041c2c03031008404000348410f44240e000300140300401440c030b03400300e60020f041680016070b24041c0da1007500240c010b402d540e8070150751003190f254810010b104180401c0c1c003040042c0005583c91801e209641d21490301070f1502c064550702c23040111440102c602e0212102e0b550100045010744003040510311030310b25520b03009032950134068854030300303960b03a0050804414020400d20a45a106041440421080c2028081600d0000c0000d10944045034104591310482c40006103a02d41500000f0401c80a08141d03881d41c542d8408560a964902e030280ba00b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 597276052 1250 597274802 597274813
    0x40f42030c170c0f070b0109091a0108030a03090813170c010201091703090a0506070201090209011502070e0c0c0f01050105240405060304110301020d06060219050615041d0109170c 79
    0x81100f901c20007081040d91240a003440c1500555681902d03400c2a0491000982c0c6d0b4040b2408200402c00c0e452001102c0c5a000d00303041d031420346480d41d030344140080e40e4100b644512002d020800c402c0306a0f00e161880ca600c4c2102a038850b1852480e500400b60102070a100748014481154018890380c04416041501030140c1040b9031080c041c0c40d40040d203200e160344a0f1007101c078042041800403502540740c0380e002017002c0d00c0e5401040711a0078180c1181a06403000c0400740c0ba25a0001814000c0f11804a05580c00e42c2d01c002c81e10340c040c043d01001d81b01070b0140c1030a0591606045d07202c039050b104111100c49660301c0c034650403001030301e61001c42c1d25080000c01c410700091400001556000f8401e11203001c220980c0c0000c603083e0381112100c030042507110305050000e103806001c00d101c1e5001c640c0341c1c1d865451303180e114190f86020281001c40d08074244181018a5102ca070010310302405005030030803211009140880c000c0c07880c00c40994604818514a41a02c1d007980201c1d40b03840c160b80700030403 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 597277302 1250 597276052 597276061
    0x90c02061b310e01031406100e1311030d110607020102031608060d08281103040e040218010609090c020d2c040606030c080c040f42030c17 61
    0x115000030501d0440c2c000701424400105560030280403030180d80f0070710032010f0b08099184801c1c6071640140c10801e2401d50300301d0030301401c84641501c0b0740c0803249d80d1014403110001d003450508400c24406031501800b0715071000c054990444038000c90ba0321002e0403100b4641c0c4100c4103e00f00d000a4900308030f1240e050145280142c0300301406504134000a162a41e8140c16a6460490b644a004981020b619052624260002d024003a290541d00d80c2000c0f9604460324101a8881c82503000348100100c1d00c402080541d154081c548400e200c41e400340388840e503180e80b03001e445210f0324410888101c0c100000c03c10f006202051039145400715440303515040307903c1c0e8074070842c01041100d480c006120210200c1480d94a07800385038002c00103038600041c1c540603038600411690000300301218900c010001044a48003070710028003250290000c3c0d02c03200d80030040036805142c2c3d02c0e62041c4103136070848078034030211000950000c0010883d1030411034038400e007000742c1d1880c04081b45003a00500200014 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 597278552 1250 597277302 597277357
    0x807030b0414030a11010b0414011a16050705030d0507031202031321140c03030a050402030a08040e0f06041a01030f020903190311120403031206090c02061b 69
    0x580d082807242060400a540c0d070540d0394078503081480144001200c5e004a01d10496080c4a00045405c0c20750303090000110311405c03449440070601c44d003580d1041c4180290403040c404015a0030743e4001f4600d1401c0552642803450351901d045c01200d00c2030140d114994203040c000c400312040c555042d1641d5589404a00c545002508004c125400c481e080d0240d080000d9582200c950306046041889000803c1e01c0748001d10031000e0080c4a0700030f1400700300c0c8401d4a54000140c039440a600c80020844e9a201c3c030100e41445070340f22004181c000045000704501403414045442000000349040071030766a1401c20040d43e002904103451840d902e410540f075544603800c441d2034541c400c0d9001d880c082c3e00c4008207240c001c9240441e1001346406000360100340d8041c1d000d02c90840340e81d004000711222210689918800d61100405001100d0007591401506412850080840080c2044000c1d0b012001035215101141c82840c2003900900d60f8000f20f60560070356240310100c2e41c400a241c0ba407a20903 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 597279802 1250 597278552 597278573
    0xe16050307031113091508070e0702070f03060209090a0b13050603070f0e0108010e0109020112020901031104030b040b0f090a11041b020304080709053606070215010906080703 77
    0x42000b0181c850100c0c5a031114540001d0003c1480b08000002c2286481c0c40340341102c80100f003070302c25000390203000c00c600b1400061060503076408010041083e1074551f03040e0f152100036032050620302001c071800400d00407a5030280a20610546410140d51341f404c45010844032160509079102e047c43d584415040703950350203540c0c020b0000d4200c0f2045a180d0701240740001380d962141c01c10102d00303030042c80540d60038002c1e100015071340301c000c0c0700030b52030340d40081e050a944c002c146010990200e604906a80301307070001e020f03020040100350ba960f070305d0740cc00035004a41210142d4981c0442c40114613042c803074680041c46501500c0290410910a6039840051040307040350340d80c030607110a00c0b50a090b10804881c2011101c0742c004641e6640340200d100e040000542c090101c031442c2000308100c04e640061415007034117580c03001c000580150b4549840f01d040c1e00c2c0150b034061103042e04000d12243c0002d4210070044242d2504030702c0c0e030399030100e5000b90341481c0210076141d00901001c10000303004c03600 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 597281052 1250 597279802 597279811
    0x10c08181f02090a0806040b040b07181502150c0f0702041409010c0807030c091838030304030f02010507030207170601050111161710051008070e160503 67
    0x5540c610300712494049036884618603400360540e03000404181ea480c00e40852001044034001801e0b5914068540580803400100060030340c09242c400285124411407814200f14115800ca0321050388806640007a003200442c00000b41c8280f40f240740b00504010401445203440c181c0d81841c14011903045812030b0010340c0101d8000f6143d0401ca090070343d8120341144076140e04800010013031803101004100f0080070742540141441c10f44030f007400b664066440c0054569492004801c500002d00c0300c0007d24440b01d000e001c0d407116074042c0a0303240b10003c03410154500105020980c804900406489100314480281403088107202d1000550060000e071010901a0040d5115290b40300380c00d05404e1244000d4180d150008001071102d580c010782c0d00c07401050080c00605240944003181541804240140b15a1200f89000c041c0110b808101100e400b4199110500403810044804c2c9841d20640c01030038954041d010010030000600d58125100f458681c500d21440d440c0860300365080d610181 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 597282302 1250 597281052 597281101
    0x30b040b10061b080c0304121103060c0a020c21013e04091a0307030501020403152f040b0c0705040b120a030e0a030204110703111b041a030f0703060b03010c08 70
    0x1200150340303e00d50308e10b00b044134001c04101c0f2040c1182d90030141844c00080a49540350f405122114141ea80000d0301459010b050b29100504e1074400c14844c582d160b0a076950ba495820b0204071158600d404407181d100c050011510880c5259000400b034281d07000f01c1c0a88a0755106003c1082555410b40001c842200300c03003c181d07034070b0524a0209040013101c0e0030599090390005010001c020f441342103120807650011040060408010880d04c10040620454021405a501818042004a0484000300021024550340b10f01150400d80c450000d03118241c81140b070800c86c0c44050a000d5140c0d807081c001000a000c1e08010766a040e581c00502d030b80c04a40140c124400400162681c0c4600d1900190f0780514944880039450300401190301c0b0070b403034801c5400100701c400c25485151040e0000400448001c40c4036113001446002d250041c07407407d03a0502c1494160381d0020300100315001a00e0040d041800101014400d040c20381c1e0f8806100e500003011000000d1403a10050b1010000306000d0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 597283552 1250 597282302 597282307
    0xe0303093a0809060a09020a1710020406020705010210020f040e070c0b011d15060405130207020d14070f0b0d020c0f010f05090c0d0b1f030b040b10061b080c03 70
    0x80259040003401680381c0007044010081c8001d44a00b0070035198001180141407100250701d90216058528500c00d100c0d1900c9000c00c100208030007408007010440c1e804004640311030340c41c038000350b89480324031a242c00350182c1d2200c4c0304e04000c10b000303c03052006906030092a05107440398004405c40024a03400401c07004c0c0e41030400040ca280c100074020481c50b510000b80003ea860316618240000e45082c12503180312405a07000c2d02e03030383c007600c04481003200e10b8880842d840c0e10940c003030702c25440c0c001d504c110000d0380d00082140d64030405005250038401c0302d410301d03211003c4880c1c05926000d000c02d0b002c6c0622102c04200b030300383c00600c218a502010707640d08041340c002003800c0d51111095035031100e440340104006800100002d400c1c51074210342d10810451541ca810b5800d1310041c104003101c100030f06030420102110000c800041d980510501d40514041c00c2c824005142941e492240f00c00b10b400000309144205c11803c02c1c05819520b00c11081c1285d5a20348060348452005370490105 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 597284802 1250 597283552 597283633
    0xf0908030f130602010b130f020706020d0207060513050601050f01030905011802190b1e090a080d080f0f2a04060e041b27050916030e030309 62
    0x180003900c1820314070401251100e0008a1907810410b0a400000071a0725200c00d5014036a5002c1541d103c42c02103410004045c1c1c80018000040d104e40358020b4111400012603000c10f175030680c020030909000b04810031040d101c00c0f2031450104a0400d0141440c1d01c0640140040c0c90310403c4034003030309014100012038100f20356030345080d984401010041c00506c03044d0602035050000c1d80100004021380852129030502c2e2a14429010340e002400c6002d09113001550035100b0340080305c0000381c005185070925035850821030360350a1000b05003000213990001103606c4003005075219028411680b1200785541d07034480704240c6600c0c01404410000070300c0802c0740002d0300c020010b01c080d1110740d0380c00030701250320824401035170160700b648000300c02c55458400cac80580c401510b02011250610b82c034400c281e2190380410031036042d040607503c00392500512400050840e6240d4104a0720748007070204040088405880340400c40e206a02504440d240c07541c5d490700490444030b426031400021610400 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 597286052 1250 597284802 597284819
    0x703050915010303320d0203130f08030106031a0109031203060e0c0717090603130305070203070e0109140103030e0d060905030f1b0a031d0126060f0105070803070f09 73
    0x14281c0c403d501040e2000b80700c3c01500c048042e40d112201c40d405c0001c4951188602c00841c3d4852403141110040e070110102d010809a800440300c8642c00203500740d1000c440f401c160b20503500a109002c0400e2920007021101e12000d08242c00340304058442c015086d145441d40d80c03402103030b00d419800b013513034400c1c0101c0c1003d0110015801031006007501a280c00447c03810f10424405100b01007001201442000460f43c1d40c60216648550586500c46640d0820f02e0700703843c18001c00c0c0009506d400351400c0407800d100c0c5950b5240c12580658400d00884038034404041c082e100c28040034001410041d408070660401110018407103106003000240314500c8e840d100d045800100c0510b040c80300000b100104030307140d45010050045124094410301174240d402404030441400300c02041301c40c007807081c000e0713030302a90011085404100310b08424210b40c1065240d80801110703101e1080e0706000200090354815001c0d10020b95010803c0d9145d9110a41c099034016035101d030280c03c120150340f000c110b122 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 597287302 1250 597286052 597286093
    0x906061b0105061c02030d0c0311030307020307110906012304080a0f020a0608011d25090e071b062007140601050f0102031209070902070506010806060f0907030509 72
    0x40d124000a180e050070810040034180e008010f00c0211046410000540d41c049203100307038040682000746a070101850141e0742442c401000e2841408040108881d054001c8004c10701c05108803041d445840d02802000700c0300c2000d4030003d00043c01790120900c0c001c08801e400b09080d041003402814142e5810b02d03075140444001003200d5004600704681e0031070400003050809480641070242d0550305202d002c0030794500150740884104030090100d2100882c094880030300d018004145403404041501c06000c100301442005414005040040c0c001c0c1d204021130303041c2e40c8003a50240c00400317003034807190003411203040d0a00c0960501315600c103810701444028001c0500c184d03001020103141c0d04d5140c3c14250705900c00d6010305003840e1110071685e400310443e40c2c2c1c100d4001408080f6100c03110803d01d804c00d540c00a01c0641c1c8005600c1003407143c0050f1481c12141600c1c1203505603540c603400c0c842d50001c50041d040d04140c0b01e00203d0b50701c0f4041d401840d80810400c0490790800410721041c408074 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 597288552 1250 597287302 597287347
    0xf09070206130c090f15090501051c0807060c05030f091207020103150b12010e0a05041104050406060b03010803071b0b19020c13050402040b0108240d0b070512130c05090606 76
    0x6555400021b0807040d48003541000400c8402c004101961410340840c51803800020080c103000d48454020040109041c16500120b400100c104201010800007800903442910041d5050604200003100343c3d5000902c40c240e800c00c20300e03440c01e00c505540198040e05c11040303901c143c000c0980c404221200a14043c4c00c0803803554071005032952500d1005444960040c000160345410002008042041e8180550703a8190603100014a91354606244004105942000c0801c02c800000000c03003030400409800b80e90300402c0103400f26a04500c8002100f01c0522400c20484800d04c540ca4070106010a14001c3c0000c0340140c800205140340000c0c810f1454150042d50281d4503002c0c070055050504c0b070346001440a00304800b581c100501c00110f686041c1c0406c1c0003a00c102241c0c1411511105810710180c0c0c1c1c042003040e81ca09160101a0043d081000e521000780c1913000040d11030301450720100405074001c44020b5481d41800300348031007100300900060f0407023020001841c50151600014005 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 597289802 1250 597288552 597288581
    0x91d01030213090c03030e0f03060702010f1d06010e190c0f080106020a020a0b0c01090f080a03050702031201360b040c0504030b22020612060f09070206130c09 70
    0x258110300c10080d100441502000c0c00d245000d0100001030700440c0004c0c1a01d425040c81d0324035050040c0004c0c030058003034031440c1c1c05000b101306001c202a01500803d100007078403a1300b404070700c800c09207030803643c03640c10b03e03d00143d80301e280104500450f49a0241d04080304510240a03154104c0c451340070384011150801c0000e0a009a808440c5c1c1e1010100303000d0140e910150020340b680c6c0c0c0014920b07100d80d00807803c000e600061000300200096000340701072944001c2000d40c0e6281c0e810800c02c2500141d4a42002c00c1c180800189100d04c0482103960201000c1a81c100036424008500700c15006248010341e030400e8452441146103a40154080180351206c0c003186a860b10000d000c00e0301d40f140c1401c3c0500009000034000a000351540c0ba038084007881c1c002c2c2c420072074070404410200200c80080d400000005040300f80070540c40750541307c3d4134190380c02159400418184080c0b91400c40c3c0c880300680101d004102c820030300542c0c1803041c5014a00c040c00142d200c030300c4481107824100d10f0090 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 597291052 1250 597289802 597289859
    0x503070e0a060b030106120c090f0f050f091b07021c0501020c1002090105090607050a061103090c100c0b100305071403010b04090c030813260c0a230109 67
    0x40155141c01400d0107820706070803044c15545003440203041c81200c0d400d081d021940741e1101401040c4143c1800000300220421040030a6480204180641c15800b540380201080e4403188560b0a103101501e01070421117044d5071588045400c02c41c65500440c3e0202c2c1d0214100d070001514140c0030b85c0306250f4a025000060b5540e0140c0d8071585010282001a0807a900500c03140002e03030b80180944049003070907211242e4072100792815506042c4480001802140b400e422442100045c901451150440c801104c16482c044420001c1418881c032030400000e42000c50743e00020269043c05411001c0c8400a2480c50b460740e80c1d03141060034030741040c404162652540c0c100d61a09018419400d03105940030003c0c01e02c60b4640d088001d84500024040d00800620412a130305540700071b030024044e20b2016048596007803950047c1038104440d0021920480880d00c4081c90045880d00455861114039445034229104440460780880c0b0700d00d050020800d40090340f594460092804204642045107 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 597292302 1250 597291052 597291061
    0x1e0c0312090f03120a050a09230102041e05090903070209010504020d021e190806090a052206020703090e091b030c0616021206010f23120d030e0a030c0b04020a0503070e 74
    0x5d0031104010f203e038031b0702410010480d0204505840c600100d440c1001000445260b06462602a100310762044149050340d18038008032490540081e0140ca10446240c000c40d03d440d80c0710303903882c003da482c007030f5018000c400100080d261907801000e035407040a101504100f5100076075541c040b80e1085100003070b0ba00080c1201446440d50040baa0024a07051120103818040c001ca090100000d041d45c04031507544021640410041100ca00b044850642101d5100386c00e01e0b04101035000346008030086009208081045070300104811f21950492004015200c3c1240401100740120740300b040d054050b580c5401c41503110b130310080502090b18251140f00940a106000400a41601c2550103030401c0005020000c1c00d9150700c03088a402c00c0c40d04a280f071041107078061034000500d031160b00c11106407101000480110b00c00c2c2000009441c108182c1c44400740d166115800450010000b0b0382c12034052000840d05038009400c503001400d800c0e0b103140c5070700100340b60460715001401000303107490801 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 597293552 1250 597292302 597292321
    0x5040309050301231603060305030307030903020601062109020a05040e070e01090c020d080c0909010806091216030813050a0b090d03060f050609041103010b1e0c0312090f0312 77
    0x4142505401440d20449611448021365140901005010303101481200340003840b03034124001458002068036600d00702400c0140007480000d00407400744c0120300c000a1503038015450750341500784811542a4120305040060000c0c204888100d07408003e004004c2969180d91103511841000c00c80241603076400c0c5654628030041c140d22010010b810300362076100d0254007181c6070300d240090703080c440f041d0748803800031421901076441c0644e04084104000a01140b0014801e0702621500043d0b0312100c00303d084903070051140c066448076a042e20701c01e42000901c1981016409403074598a42c100070025520582410711602c0103030740040b00d21046c0702d4501c009100300360700c000a50504001081c038042c20124111194800c86116401c04a01145283c85503000f00c10f4039820041e0280e45c0e9a116581a64190048101840b18800505203a400380700070004594261a85a00541c14400c1e140f0503c582a0070092408131940551865407481d50420000b0700503400b82495240030b585040c0010 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 597294802 1250 597293552 597293561
    0x16050a2708011a1e190b070c05101418040204080106080303070216050d0b190603031d0301060f091107120509010813030c080a0c02151e0a020309010c110405040309050301 75
    0x19109402e04070501004904518113600481000c0d01c0c8440d0109081c000340c1c0c3c03801500c0c0d0085460003000104501084818885001030310000c4510824810b07004030103c9844018420350b48010408000210181c0c00c0d6402c0c580000c400100050315043d291400c0900303507031142d440380c40140d201006200c03a454040c8009840300b11028101c00e580c900d000300041048401c8080501076100400c00320f030010001c401890150300e41c6c27441c00c0c05020380c1ea01d0f008103010801d4495030200000601410700074541800380008492990700903440441c24110b02100800d5010655191110100011000518034410744800c4d0842da848564454140000161001000600300118048070380d1404000a4008104070074440d00400d14035181d022080381964100c4104034045c1d403000c0018050340c4103441e8400145594019905070070f4203c5842c107200070407402804502d40242c4c0082c02100d4065204545405c42117004085284415141001050841e041558246c00140140e10140241d0509004 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 597296052 1250 597294802 597294851
    0x80d1e020c01200a0c06270302010f1e0e0c0904060506091006020318040f0f0905010c1e1b060212040302250302010c171c0516050a270801 61
    0x1c0182d0b500d10001200910801c4040d100748805a0134103001d000c4158800086111f480501c854003001410318030502482c140c030214015803d001e40d10303c0c03001310750184108200d6000920454007080941e90400f901c0080c0000d080c0d8031a03480800e58550380c00c1241801180200e01c00625030030684284840d0030002040412001c0307010b9410084240d0010071105000004502d10300c1e811081b8000401030902c040d80c00e06014280a0b410100340c805034001700c001481013000300000d207009601500e0715100740b0804410514090301c1008614000d83c0c0064400d8405014142900c00a503110400c980040e44011900c00c10b40e0204020950108903011017462114540481031002e8100490301d5699400000c0c10821003100c03d00030042601401040420b4040c0e031035803584e051750a0542c049140080600900d418903001c03501c2855260f200004072111951004d1070115640015102a0500f842c040c1d00d540725101c0780d10100c01010009070241064400106011461140f042c003240e0301d042 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 597297302 1250 597296052 597296081
    0x70f0f021822020a14030c1e0f0d050c1002030d0f05060f09010e06041e020c010915020c0c012006010f050a08070e0103020d02400c0c080d1e020c01 65
    0xb05400c05070f501d4454040813a01212244c801810560020074180319100031101c5c1c20100f0309a0703400c0030f00d5001000100c56202614410001c03a884020000c8205040c00003034a5034100e4003042c800c03030030010206d02c8021428011a8a044d0185c8480030882e8641240703241ca1998600501c0241d00e007902c404e800d003150450740e1500c2355040c60f0400c403e050024060910455941c091070038500c12402401854440d02841107407107044000300240a0b100480c411a15040c0841001400480700d04c280d940c02030183c2c00a103005100b210064070b4608101c1d00d0003102e99185071807003540b01c1d000c0107400d0180c04180091441246000c0a02079801c209411030301081d084204203002001c0141345483c116501102c20011000c41400490030260307031401240a2901808081031b034000c8421400b040001000e04d030901181c0125030540c0840c2c42046402c00016244142071010811000c041d180642040c103001a01480d0030303c5080d0040040d03076042104a4012a074400407140a1082135030348003502 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 597298552 1250 597297302 597297361
    0x30e0703140a0605070540030c090b06072103020405130b0306060a120f1b09020301030c06080f1503030903070305010519060302130e16080c12010c05070f0f0218 71
    0x14400c9249103d40c0210001e04102c1c981c01f03540310900c00c07440300b00281070a80c201d0310000c1d00c5c0c2c10306c805020210300400d040303203081c120036440600300b0008030340350250001500c1071444202e07084e0208058604000008040d028030000c80e0b070341d88205c00c403038003030151100004028052000b07141c141603005114500c1405c1c03840e010481c07207074030000040059034000c400e1aa840c2c090301e4960801c6410301c611003803a20403103001041c10700700d90b402541683e00501038416850343d40c1c24101c034403d03030271145078080e89012808640101802000c2042640d00101500d04111503c40031a2410596130b2040e111a9121018490041000404000041c1d140c0005100403030560700415004c6a040c04091081e03950380807201d01c804001c0c0504445a219044580c00d056680e0042568694400114601c98201b4441d201c000301e40520a4004010594030b0300ca0400700c15441e0740000900520301a504140340702a114010b90b43e010aa58105580726070508042c02d01c013408054900503c80d0981450184 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 597299802 1250 597298552 597298567
    0x141c08040b07081527040b15100e010c0609080f0409050a0207081b0304050307030f030f0e030c0409030203070c17070b0702220914030c010c03020f0a030e0703140a06050705 76
    0x908401c0404c228244e9200006001a0500c4021419000c08001d044001041440204080000c205000d031800700c4256441c610030b0300030080d06031414082d0001064002c121040b29500424071281c40500403100080c2010154a0b11030003644001c81c1207034050400a003d00c5085002d02c500c9410582d040710031410510650f84003146446044100030240108204480e00318804004039000340c00c000e401d80d22002d95a1070309002c0420b08080c00c41c0454100f9118280d203501c199920841000300074020600c10b0711341c000b80002802c060b001902140010070000c408a15034890440044c402800e030044042c00315000c0c00d003440042c0e006054401020451032001d80d641464000c603881c0c06c1000101644a034158075001050804802403c407002d665802000402c08809003d90340d001000900c5031100c0c00b07a044049209900c001c1040c100d090002400552080c1c2c031a60700550300e030741180d942c030b0340300e40300c04824180b01807140d011a402030603043d08000060040c160011228204113040040 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 597301052 1250 597299802 597299821
    0x60c07090c0906021b0103090c270b041a01110a0c0e0412050a080a1104121101110c090f1b04080a022407060f11071110020703020d141c08040b0708 65
    0x407205c400c0c03410182c945146c034041c082d82c0c04448000345402c4002c3c1c0c5c140c40c8000c08454007108080c9020b48024500704409142e41050301810b110919840036a506d00c00803a8015105041c2150b0604a94131404610800007900c00039614042c04000040040381c1c902440c081680100c1000c5150401c44144018120a50031105c56900941d10310000b08511080c0c50b507400d050302a5030320000849200089040900144540c09010584281da5041d22030130001e181907030b0303425400c01003078120b8540000a0f01000d0b5490103140c000e5210b5004025001041c41c16040c0c1e90080c1d000100c00340c118185c0802140b40882081c400c0c2405182c0307400141080080040b4180540c0202038041030b116541c0d1050301d90300754002040d0514402e032007a01e440b6141005594021541441d601852801144400742400041c05504070b9500420b60a10407005a8419400c154182e1030500d140c8221482440108505001d4140301c01c0702e50f81c1e410781440c1c10305015170403502c084d14041c00d020303145041c454042c0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 597302158 1106 597301052 597301093
    0x30a060f15080607120203060f0306101d070f0509030a0206030114030105090118080a031103010b071a04050d031a09090607080c13060e060c07090c090602 68
    0xb510780a565540d0384060307a00030301150506400c19080c002c16001583d1080300035043d43c98074200314020074a000c1c03096480ba030034064070120505ca6100e0121205580c004c10300c0c510b44041c148804c0180c100c0c0a101c0003281080000580d240c5191010001600066070207441e10783d0325a5500e281c04c1080240c040c05903c29400d000c08903410104c14022060141c00001035448419841e54815005620040720b0809050311000c0103100f400540000d18000e0031a041110750355403143c0360041c12040b00780524041c040c00d42040c40046000010083d03a24901420006003040030054000b000000200160381d0107070440c2d08101001e400824001d00404490316910b580e612001060700d928000c03580007000101407403400300112403182c041030f6207280c0040e040925021721224424142991074104401954884502c4061181d01034402c00041107144003521120070141c3c40e1582c0f61 = true := by decide +kernel

theorem cover : BRFrame.Cov 597122302 597302158 := by
  have h0 := BRFrame.cov_init 597122302
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597122302 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 597122302 ≤ n) (h2 : n < 597302158) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
