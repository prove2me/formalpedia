-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3079
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:35:29.503552+00:00
-- url     : https://prove2.me/submissions/63a6072b-698e-4d96-94a7-1c6e42e47aef

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 553597122 ≤ n < 553776978 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 553598372 1250 553597122 553597127
    0x90302061603120509030406110601050303030126030c1b0d050d0305090a0501060f03031701270612030f1407020a12060b030717060a140402010e040b060a09030b060907 74
    0x9400d40030350800844124081098400d0f0900a18031404040402090422001d0503699820070b02810000c103a400203a10318007000017a440c4d04071000140194551713820189250042015400b00744000382c2c0d4034041402202c018005041030000101c01490022002082c941148440d182c07424000d504c140d90340d0000c80c03000704900c04900004e042c00301c0c484e00c40c00e401528142c0118005000c81d403800d240401e608200c81c512800300c074000d0350340d1640d00c0c074640007020180f00203100d041c030312950300c103154805010f00102c44030b00b80c1c2500000198140e0340d1460541c81d100403010132000506803883d0003903000e401c011180010250b488a140c20401294041600500a0f00880801c0075004010200b00a4036400c0981507600113030940d134001d540d810021200c003040013480501400380e600007031608102c0744503018040c0006500b440103901c5580054400c0c0c42d041c510a90400e407640c095000c1a1a8a80101942c0505030342d208505851070503e607030061405010f00740b00ea2407800a00101d683d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 553599622 1250 553598372 553598377
    0x1211041401180902073813240c09090c0e040911040e0f0c031902060714061302011202121815131b0501050d0c093309030206 55
    0x20300303042d24540d124008845a07640706034030100b06640009000010041c0c44142d0404c1040c5c0e284102240c81c0f190f020054040032054284641c00180100159100c50001c26581c442405000070000d1186800c001c0603810505e400fa0703540030768560201c0b40215502055840050089510401209044020080c200c07500030304100c1c030613900c8011010600008419107111009c00030400c014101c0881c80700383d01d40c41c0d00300e0060200d01034075a0902481c2404161007130402c400340c80b4004602c595a0802c80680c0100720162020005070b90720182d158420003d04c0d0003500d90511003000d01943d0b03c00100824a411800f459607401800040d84074407003441c0c01031f0045c5903025569043c2c2040c0003d60300e8240c0c140d406ca41c030310001005000e117484008084000c0c050050310030401841480e0301002d082e5180b0b02c038040c00602c01b000340d40000503856004070382220951a0240b040d50303454440d2019502c2d9441c10290000c0b0788841c0c250806e11984040c2101519420300c403d1451841d00080c85a0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 553600872 1250 553599622 553599659
    0x6040c051f120f1509060303021e070902070f05060403030e120c030301060c0206130e01050109140312030712050903092b0201050a03060b031504050a0204030f0f020a1203121104 78
    0x443e222500e158010040b030704051907504108000d01d02c1243e40c2d00c80003010b40440d00c03090307000d4012240050f02801e0303085801824120324800034840207151071101e100a61000d00155240050701c4482800500309000c25801a80070f5034000c250100300303000306800c041c00302c102e80149590401584071480070102c03d4904441041c148200008001d0021039840d200e15032100303034060762024001c2052070751044200e050303401c2a80c43d040c100d5200c00300402d40d112035140055241d48003202080304030b064803004551140a40c500881d4039004000240300340d8006640d04440c1d500041822905800c111903080007400c4100c081106035005641e6442c5d410300341a4010381088400510780b04418020780019009006485409030740703180009251041e01104401544140c0c1400081401801d4074001c1d1019250801d90386400ca2030156290303d00d040031f070b0fa0220317003045628500092030580110b08003100c60094903a01d00f5548068041c0046034200c0c0702e895440d03003047c081030107908008bc1910000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 553602122 1250 553600872 553600907
    0x7080f070e152e0507080702040515060a17070806011e02070315050702010b03060603031b0a0515090c010219080c010f02210c071707030c020306040c051f 68
    0x440c0c03642c001030401001c0e0307001110b40192074006102d842281220f180c0c0d82490329203001c6003e0a008950859076807040382405070849905004100141c605540b1550b081402c6400c0c4c82c0d10151220007090440e0080031300d41001c9125031248210042c01c0381039265220000349071102440c0f62a400180c01c0030140400ba03800180d80308000308145008204000103150045141c55100d005421044040c10086803075034019420103000c1101c50400158050055100a0185042101074a44507a010100200d1501548900800c07800880d009211000c0040411505032100345003880100e4038207201d00b4003090455000030918040c0c150303140351313401c08164840101591485040007142c0541420541d680076980f000075103202e105405412240b0a0301d0142901d0141da035001c60150090252203005005014010324041d242c0b03002d0401866000d00c2420f11031038848031500400e18041c41100c4c100d900c0031002c1c00501c00d03864895401c484907403504070406060b0009485c01042c1e0500d0080c046403 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 553603372 1250 553602122 553602149
    0x30507170703380910050c030601120b0d0615170307020913060c0206090f060f0703020a0207211509020f0f0301061a030f06030a080711011412010807080f07 69
    0x5020304140f8a1404003014202d440310081e40500001071081d02500e045106118424080801401c14000c00d4465045c9070350b2103055548040054034171082c0c49003442400c5d46d85140000300c0d6550210319102441c0160707800104030120b0002d031082108690024442c00d04001aa40d090302c000104640300240e0580e03042020303840d4030036010030300c40d41c00c0b800514680c20b0050080500b40d000458511403102d10301210341c90743c0c008120b42e0300c0d603c0aa418000420200380052071040c0242c00030f15090300b07181b0440d510b165946004240a5002416555545080142c42e00521070b0060114140e05407104080148040c50703030010700064906000d442c001d10005220720440d60702948000b0040294021041e118421968a01c5c2d42c2d90080790144550300c2c003d80402c101d400e001a2002030660301841d05860554a515940101c185090861b4104160a80800702d031640c03010190403080172540c8400e0007541064030550400500350400c1c08164007032208185c150703400082030390031100c5c00c02c01d415 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 553604622 1250 553603372 553603403
    0x103090201030e0a1a0c0a090506030c0708040b04090605090708040b04142b08090a0b0a0f0c0c12020c010909020c030c0d0215090607080c0d24030507170703 69
    0x8002e05410300500c5801e000d072004e00014080400840c640144000000081543d50b200c201d224a000c0e04c10010001440c1000600007824113030002c68000b0050b0310b41500700316a50341c4a107810f078000c0d04848114040400c081108540b58010340002e064101c0301409a4a0524801030405070010009002548443c1c0440e003844900c1001c04c558200755801e41e0300100c1d024110507074185401280407050a04161801c50b01481018154042c12499015044d030034160b46483c20b800700c0140c60345603002e503078212005c2c03600200e104145400c402078031443c401c3c10a03030a0110800159075108802d5412503c0c2c0596140e0388040408103030340b00c00000680b100c40c9c1c10300141c9140038841c01030740a0311400c802001d0054002803891610101d061040302c0598400210a031212410f03581f46010138a044003150b44015500003405501e90080000100d0721041610401080054540061780f10030344141482802000c0c05a00e000d804034802d41d4601941e20b403560f940d5050980710103891078000d00440e2 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 553605872 1250 553604622 553604627
    0xe070608090a2001201b04061d0c091e0310110409020f1215240d0506040902181008030f0a0e01020a171305030d020a06110d090b161d0103090201 64
    0x6000f1148504041d8a051414003480d80e00c5250812095406d010541222030b00c0c90140107280c1075a280c00f0340701081015086504c4d440c0302e005000d2081b010800e1200542d01c0c0c40380c3c80314484103c03e51b046c02d00e4007115002454103140041200c1c0c60b2042c20f0082009041030507204940403152004801a0b5900e49801a00b03002c0c0256906160b2001b0707880144a10305401026101c0850001ca40301c024100003252090199150007405100040c010700c00000c000c5020303070007070f81d110b44c0c0640007060030f800703560006411450140440003410281f80500015200341c540c82c0001d003c5c9040214906104920040010b01a011003942001040c1425034003a074070a01c401464550301060419102c0a51245100a9048980d5071801c0080f000f00c00140c5180000301c000e550413481d0081c0140d10306070b40350740c0c0181c200504c0403251040d00300590b1a090001d40300d0700ba100d600604513180c00b810190308081d0300c0300b4120820000c1104070400c1d201041845100000419800d00300000c5682051005 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 553607122 1250 553605872 553605887
    0xc03032706010620100209151215040b09040302012a0806210f0d031a01051c0b100203030a0b06042403060b0c0c1003180204050405100e070608090a2001 67
    0x10744c002d0b030092003104a011071068001d40590b48040313070781c1d4245d442d213030036241014001c0201e0451150050360101d819501c044500c00840304000d0000314500401b100070807490701c4281c40490050b9583c0016161040c1c44007c81c440c4001803103c1c0070317203d200b0640700605160000d0a400c1c4200d840540c105c04101002188002d442e1200c1c054540405181e0546519070001d9201080802e0038041ca0540d0000b90900380d0203080c0e4143c680c50306124000d846191035644000b07000f6101503507440015807582d541c0a603016100d609500031a981d2521845000581d040c03980d500e03004080600052054070006012800e10203140343c1805c0f03203003000c24802c40180c0b800354405501c00304c00003030140b9400e101096003150b880040c0e403c41440c2181450460460755589030b000030700c0c081c41c1658001890150405504140540308039040030790810404001c0f520307100c019a0040e440120704012881e00304405503404250100035085451040d154040424805984d80031483c01c00143c9140c40d0703015106 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 553608372 1250 553607122 553607177
    0x1303020f040612120207060206060901170120180a14011b0804060906020c19150c020414070f051201060804150c05090f22050c0d020c030327060106 65
    0x16040304256050030402c034a03000044d0f450f40180034580010070103d0000800f01d0003203802030107010f416031a00399140c21003241c905512505540310080001d0401d1b4507040c1d113200d00403100d0100d40d90030a0030120500b000340010705034040e0301c408500b00480407501c449414909028240143c84800089800380d40c410450030081c20380a002c500450902d0b0700c125071030140c03151a0202c840510403c1c0c2004410720015030100459014004240040c4c50306a0b0005480549410b000310031420302d82c0001c082d42e40603461074a8460007072003000325440d8080428040312030300742070451800356072036940e8520607814080e0009015040000c10200140100210030000240b1010070070865040c200034810303445000024842c410035002101d03a40350024110078021505c0340038902003070341c1c40700301405031074004c100328800101800020300261041c0000c01c1e140031000040d55607443c1ca02a41c84450200e42070344502e20b0000114091003c1e00040c1d00350644000b810900691003040711400d00d83d000426 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 553609622 1250 553608372 553608389
    0x604080d110f0705010b0f09040f23010e030705070e2406041508040309080f0a12030e070f0518010b2a030d0614010f020304090b0d0609081e1303020f0406 68
    0x1d280d4240070066105d98141b420803a001441203d28900b048a5050251000713860f01c26140302d6100050001d40d901c10000389204a01c00c8100044144142102c40345c080320909600002030b5a01001814804031000e4800d40a4001c1d59080480d41c40483c241c50b203800720b80d40e100301c41014113240d170351406607401480c603070500c0d0b00c00444c00e807801080980700341d60882c0403c400c1c3c28040782811000c00c2004100c413200009101809c01900c6a00d460103d40307221009240d551840e8101100e802e200840240542098101c040b91410042c00448040c5900070664400010014418221980103c0703112101c0180001e0490104d0840580f9003c50115188010b01c000201c03180f40b19099045881129012a4810444116031006580035102ca44405006800401040c0726003000350b44081e0026a020b0003c0b5410485903440508070703011075005403880d413008564210300340b004041300d440c4d041510803441c0c01c20403401c030240c2000324603000003031054120341c428540d262119404000148880e9 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 553610872 1250 553609622 553609627
    0xb1e0c0d1104060302090901151413030215071b0302060a110c0405090c040e0a03080402010f020a05100506091005010207090908070605100510090609151e020318030604080d110f 78
    0x1080044e00039405a00364900507640300c40002441020100c4421544406883c5e03c0b00603810b03501d102c0d69030f50111000c201003e15021000c0050b8883d0380a2446446044110540d50903a9003030024403010985010013a400c8810021b20060300c584e000d9a0481050b0309100380000701210f20141040404d2822035003041c46c1c0000c0215000300001c0c1c001040005035001c01908010300307070b404d8135240741d8031000c1c02040c10726011600552003480c0c040816940c82c030581d00c040c24184d40300c0342040040417040701103d0700c48090052900d060300181d9000194511014103640c82e010002c0c0d21100117200d07001903640d07101c0c40344c4180a500003c840e14039510582c200040d140400c0341010480c018015180076070812881c004085005074065000c1d44e4407510341480b4245440c0015451542c1085148c0c10011101740403155075614100b289500b5081d0380217162142c642d0300310b0001040b01842d10b50300c250b0045080c800403070f100d5800c5501c1140d480b070001c604c0e1058a040081c2c2446118042d0002c003400 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 553612122 1250 553610872 553610879
    0x70c350a0e100f0314060f0613090c0903060b030a05060a020a05090a08010c18030b0f070c0f0308070e04090c0b09010903120c1b0b1b16030305070b1e0c0d1104 70
    0x30f40106401d1880b52004c201410036081c0341200110200ca0050700640c031080a04414034016003d0300440d010910800042ea845081840603200c0c501d01c05404a10440c0c418401c0000600520f4a40041940100503003c40d5498495a031348000e4000c81520754000751107007900f0711803c02c481c40c0c3e0002414041c1031030f40d150902c500030194101c104002418040450559025982e41130085942218070740009450b0f046003511044000361803941031002480300d4000055407245018910790003a102c0c400030740f50080c1d01810240881641602c60742c40c11906000043c441040401560801c0c403500d52540c04580050b1001c9820740c001801150410104d003541503440200341000f00c1c8682800115000d00c00c00104500c41d6501940100c403805101648500e6680340d07100c410448071600b201d1402c8220f02040400c84515002135000410004d01c1c1ca00f840522800203401120a401f42c240b50078072018881c420103c0600400c08142002a00c0c101d40ca0a41c2c02c10b18a80c911001d400f59070319507 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 553613372 1250 553612122 553612127
    0x90d110c120f0706020c03030708162918071e090e032d0a1809050a09050c0604030c0312020312010603240b0d0908040e070c350a0e10 59
    0x1c2c1680e9440350320541e80c01180c914170208031408000030240046043c40560303034070850150401078016400032980b25018011403001e900150b114001d045103400505210032507a10030210080c40b0180400c120008000c2005d000a8804201c0c0d02c0c444140404c0100c4000c02842c3e07000541c0049489428021121030145001c0024200c212001e9024003103d107801d0802c0c400c40d11920100c0301200304c01c1c050905414080e071460059182902c4100500c0350b02d0b48954030403035809440d80094195103510002c2000b900300a800000d6004a0359542441e25580c1c540b52244000e001c01408038000524004405000304265000f8884846080d1080d6841d00401402008001d4007001c171a48a42c8801800d4042d1201c03e07000d03540701b1900c3c24079003c07440c5004005001c0105045908810810000920a01c04000325009030082d588550941c0c0c001d00b00a880d140e01c100000d00854440c0c0c41d40391029140146840b090300000e00056250721040100381d4500488502d80c0f504a5950024110b0315503 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 553614622 1250 553613372 553613383
    0x9210501140f090d0207151101150b03160305100501050c1f0b090106050a022d030414090903030903270d03080a05010614160c030f03030203100509090d110c12 70
    0x105000104c2d00d0740c80c007616040382c2c1d9004901c210804025400d010030000c900c103407040038202541400105011a010050b0100c840850780545107619000c17050200300046a44c10801800ba0761400740000e040220008819481d188502814010001340e070000351034003404254401e801045c2d0a05034200092a044e01618122890038071603400c2000100d2050700074401d81c1c134680d2540d402442150004820290240c0b101c6000300c01000021350b04034201c810030070013440030348480c05044040300c4544051200607000540001e205070000e108001d8050000000c3d00e204e00080d460b003000d00f40403101e444c039000320209210380d0407500502c00c200c18180c000c203040b4050800c4006c1085260381e01c81080300d02c002c4581c28190440c4017084010700d5100007440e041205c0717020300e90b2005001e40c0d940d81c10080061a40040703011076000b10030461905c0000f06424000c150a0f43e440740e0380c0c64070004540d1905000b040c09818040028a4882d40800c00c010a041e221000b421405050005110075035444 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 553615872 1250 553614622 553614631
    0xc0807090501060507051b06040503030d0e060907060219030314070e10090f030b06060f1b100911040222180f140c0f09030106030809040c09210501140f 67
    0x80d4141000081c032548684101c82590741c00c0710140c81081c0d990496144405102c1141d698801010700004c601c0340c3d000e20040c0340e80681008005601c9a0759141142080001040400c41d500140010809550040f500840314680380e803288030030000c03e18060740103203954954411540410710400c001c444c2c1111014050700c008491001100c80629001c0b40e21855500400d40c085200103c104001400da44082e50068401813406041a0011401c10209d81000801c602e14401c44d0b41100440ca4050028400e4080389000a004c144e006403902da4989068481030f0740a00c0c0c0c0001e4100c01a5004031020030b01112429001e0380c055540d20701102910703030072144241440d18000840a407050140710f0090307000172a400c1201503994146903c60303940c0040007018916001040b02000c2d564081c41020b010718450102c2944626500c0240004c03180740c0c40f8013200380b040d140001d11080380250844031044150a540340d0a991080c0307003440c090004400890800921070003404202852890001d200c1c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 553617122 1250 553615872 553615889
    0x40302030c120316050a0501090507030218160809030705100507031a0f010e030307060c09030606080c0d1104090503070f02180f04060b1809101b05180d0c0807 70
    0x180076460401440b41c144201d5800315600810421070b40300d441d841c201c2c2865000380f055810910303880e2681c60954070300080458882e0800322090046240c001031002da0b1406420700c91040e860049111710360388443c14405010300034204005800e8240c01c00c1141c148540c81404d8455624004107030740e02811082d1060710109040040001d00c502a080c242c43c81c030a0010002509010564012b541303a00746041300c5034060204202760000f0a20134050359900c512199901c041d06861410450215440754120f914550882c0000c181141c2d101c80100c64142e811141204d80200c0e06400130300144094a4001d00600001c9651030034800d140c410f18810324000c0d9201c203552810110f03240602d0b4000c49040480010000108001c03a070305038400c0310400b4010342410300500412880c1500e0310b908581100c0c20f41d1184445640512403401340c0500385031200c40c240d11031003103501d02400600542c0c1082410200403000c0b84626900c00610561040e049501c2c40d141c0703900d40041d981c5551030703030040851 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 553618372 1250 553617122 553617133
    0x3060c120e0a080708070204060b12150402070b040b190c05090f03010501150c050a0204020708070c0501030c050d02030c28030606020a08040b13150c0507050a03020102061f0b040303030204030203 86
    0x20040460108185030f886851140303040302e02d07641c01c000e0f50000003080ea04070fa41d440c804101c411060005242d030945000a00c80c80c0d20300710380121900201200307006d006034014440303c80060714030b0602c5900954803000d001050764450800391800c1d42401d88010b03d280c00c0c001704940c6903400800901c01004185c2e00415030703514010505084c0c60302881100d1504d404081e40214107072042c24980013862090050f680c502c403103a000a010390b00014000c1c4c3c1e0545001456904224410350380b84010842800d003800b41906d18140500540030f24024014841d40020005284800031400c0b51951107070604158452401c107510003941e01640034404010a03c0e04a01064040c0000b030b100010380d60180c2207528080c186076502815410240707a030400e4440744600401c0810fa848000300201325156640000303041a401c05514000044c0c1c0614000d010200c81400580d90203c0c0265224000c62441210119407055844081c0c2160303100854801010030b000c0109981500180104c0c1d0007102100c8 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 553619622 1250 553618372 553618391
    0x110d0b0a08010213180207020a0e1915060c030e030d0509010210060b07030f02031c0b101d04020304032102030709080c010c0b07031d07050306160207060806060403060c12 75
    0x10b00300c3c03240720507908034504013507001c0041550b284415001146038402c0036042c61080c1c1d011450a054070b81281620300341800401103002c0035406580000e00c0c2400c01400b1400e01b07118030104088450003100c003040f8441d0711180506018404000742041d024003203d8268203024270040c501e030000343c0c9050060084031000f1168201d035000b11000e0318000c1000e1881c010041e6070503500310540c24005002d600041c040c0b8503156440d8000e0041a2009a801080403032800c81002140c0c1800e05003101408a80490300e44150303c0d5508007440010241c40050b030b261218141a509400b15080405103031111480741950491640c000e9406540c0a444084210391510390b042d44880858801500040c0320103403c42c08601c0b00201c1541054403414001031100245801070b1160103a00e101e200c040e800303450700b00b11a047c2044000c0d44515001005044030101000c003d4452401d4819041002088404942199141c40c21200116440041007050344407000019058009040d00c210043e803600d06003a = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 553620872 1250 553619622 553619639
    0x8070b0c0307021c0c050102130321080a150b191d010f20250501090e040f02010909180308010b040503072105121201290706110d0b0a 59
    0x803400b8076499006000812000000700e141008140c0c0340b8401c005070002c0c07100104500f0b1000700b03848903600b80d09040d01419400c00d40141501414000c0954540910400ca079540c0400001e4014001c2000854000303519054141910100d4010a50142c1c00103401001c20f000c0c0c141e0b8100301211a20340813a0888003000740380c02682056035076408940c5450520416501ca030040300402c880c0d501c400c0351001c9940d89004d103004480c080c09001090601402ca0480c1c0c0ca02190702c0c0204800d113050000345081034404c004c071071030141000b012159081c10b40811a80201004c81c0a002421403c21074400b0141c0082d0f02c902e4608000d6011610880010560342050300444064940c064024031070a4070b00318410050900080b0b80e09081c20320f02c40f03410300294061002d611030a0154061540741c440d0b01900851018040c1e00c00d5420380418440015102c075105038094955460646958440c1c2040c14060b025002c0240c901c030701c01d1000102d1800c3c03c080d950000e00042415282e8140031038541019 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 553622122 1250 553620872 553620877
    0x3010303090909020a080f0705041d0c01110312040f140705010e0105131e0315180201030c1205010e150405040812090a0605010806062b2006040308070b0c 68
    0x40d0000324981800d011404081d004104818401344c003105900e6540c6880505000481c5003159203034120040400c018070702801030440510745e41d0000403042c508038002503550341001c4403180c1446001e010700355403800c003401903e0300301004d030b85561418078040c5407081c280e4030410401c607004507140f2440e01001c003002501005840e01a102c00041642c20801580c0c5a0410109400020760120000c40e8204014010414a0fa40c820b00d120103d82146000c102071038110600962940c41d000412034000c400207a507142c0d0300d40a090002d040541c0020031144030314011134036200340b0f040c60b00008000c0754080c2428403510118030040003588503c0b080200342d030300503a0054904041030140301e10046040540c1500484160b01701c400c3c0038600d030340388003d4070343c240d000500d150025020800b690404032103c0c80504002c0d258000c00c09081000d03034a204407513050251443c33404401c49280610b451400321204030004001036112542e0385080e81c0590b1015000319070b003a0a010100e1840c40d548001e = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 553623372 1250 553622122 553622129
    0x312090f09140c132402071a0409020d0204260c030d05040302150408120706051003050a031206050303070b040c061e111f05040218070f080603010204150504030312020301 75
    0x1080b07061500c82d480c0c0c003c40c682110b0b10042d029004021300088000d42803c01600d82d994481da0034580720004100a414031002d075026009000c215001100fa810308038089030305030b441c00e05005841d5081d000c0188024041c6070400a041d40c1142d03000b882e0700030020450700d51030001c08122640e40b501041810784030030041520b04041107040c0b20038401031412100f580300100c900d14030070b400c040d680d0b22040c2ca012000380141100100006242d0240440f0303000307055001241902800c4442c0c07441e80c0341d1f030b41e034100010050104844290b042080c9034540d040040181801400c4a44031202400c2c0b60003004d405850441e00480d03010300005074140120422003050803d8610100581811801036a903120900441c8040c0c1c002e5007066020034640001c0d000c07003030f915101d00084915003032042c4007003c240c2e0714007503000f41144c0c400c1020480d031002c001c5117003655910f0012180e07214140401c0c06401190052000c60b000010003420322903111001d442183d00a996003008150604104c0d4220300c420300 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 553624622 1250 553623372 553623401
    0xc03080c0c181b09100e1302071b06022b170a06062d11250e06043312051f020702010c1211070602100b1206010e100312090f09 56
    0xc11141114001c46c41c4029856024088055280300c22200500302ea000c440c003100e12459400008404458081071500602110700082c04260410507101e14034140b45401064101841583c461049108810401440501c41e100346540e08006c0c040038041c122070300a160004401380e0400441107110690030040f04101d0b903030900c0000e8104412100a00d11010038503c3e8070804403080001601e11021486240c16000d40b05849400d1041c074028a260240901d80310b5030508081302c01d1444a4081130b44402e03c01c070f60791501c41690000140c4164140d84c03001a48541396544003044c0480842c40303200003055056201803103c440d0102108074000c04201a0000e90ba61441c4400215100307501c00349960242041c04542006460062510707655410442c016005121000b003442c01c40e020b174003040c0404071030400c0034519400c07805a13a8041449529296080400460440708200d00301001454001c03c962444000411014000341c10510841280500d55480025403a803d03108007200303852141d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 553625872 1250 553624622 553624639
    0x115050901090e030f0414120303040c0e0709030506090a030e010c0803010b0f0f18010e0d0b061512010603140f01150c030306090603030201050a15030c03080c0c181b09 74
    0x101010b0024100e0115041c2948010003100080155000c007400c01031804540040700402040e052000310183e1007804c07a110b074020f10a220004440f003000400b6035144450300c42290b924840100c130100025031001d0200e000d400213002d4041070224019400d18085c3e203070030296000d85070045a0303c0e4021034014081c0c20f010300c014420000440024424118101e41c090f003000d002c04200c062070b81c80040741000310a0180303c201103558101c8400c901068044a101e407480d856a01e800c052190001d2403140b1800d10707100d2911a400400b030994260002d02c4208004540e111000540240f074100c50101303091041d4030001703032040c00c11480039050700d011601d807000d14201c2e66000e030303019842903804178141138403080c010580420300e10400700114000c1e8004543d0b030a024200b9800ca0700d01c07944602002d00d14230303c2840402c00407811030045035070001001c0d9458030a80313203040c2800420100346070305c203209000410442c0d61007143d8901800390500a65480c20b4101300c034088621036512081d4004c29203 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 553627122 1250 553625872 553625879
    0xf09060804173c0c190c05060313050606120d1b08031006090b13090e0f060a0605040501080a0308010b0a1b0807030305090d090b0901020f030a0f180509010306050a090b0109020c0115050901 83
    0x341c1142183d00c6c030030b920f4105a9900e8100188554008865540b880c0900007003c0d014468100141a0006001d6600f00519500f4414003511020601c1d0014240860182203e00706032181c410401a00d4018141c50b489003002ca940703a0b0060014809c110005041c0c20300070134031111103411030760602e5400340350030980f0340f910304540003600241c03010448602405542c0d030032516060044520a403407400000230101d0519040104898040c0c0100f0b41d140e000041c502d000941001410b410b5032200903495440b01100c9008641e542101c40001310300054141035041005800c030098400c441c80f945040c04565035102a160303841c0c18949800c400219042070801071800b0070401401d6502061050300c0b42c10b0540d07202d00b0302c2c590000c440d880001c0c080d000883c00107a841240002c09941030000011014034050008150701e006000c0075020641c0c0e41c000c5000c0241c0b0b580024000340c1d000c0c014108541c3e540e082080203401c920702014165080c8000c40300e0503274003824104180c81000b81190010307402e = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 553628372 1250 553627122 553627153
    0x150f070e130e010c0201050106090602060f370504020112021303021017010305071d07021203070c020409050c0103060f0602150703090f0c03030f09060804173c0c 71
    0x35080307108641d514102010050280294030715200380c2c0e0004200395150040c020002c0d42c291f4070001c210f4001000b4840006c8078500d4040e00489108400044c1d40041e15426166201480301108a2103109492580e048813030740280388554003d8891400420074012000242d2040d44291103400b41d0990040c40140b40c01604000141c0c028030b80441d0168215045501c1d800085e0001d42d02a40542e03410000d040d0b6090740a641031006032110038103402c02e40d030301942d10b03903c8005d04020240080000361160f0b10460002c030300160000c2c014041600c040c100740352100d05070000c041c00a0704150300494010000c820315401c0344c80f0b690081c061074046000c0c112000d6006401e0404240d250031501002c0b80079240107400150141c09902035031481c42ca00034100110742c1c0800707018082d01c1c0fa403c1084030381160441d43d0154010845528104914000c56480e21920405003107041e01c00340494180318082c01d030080b40d107210302d01001c08101010140d0115000d1a40c1071251640001620402d0f100d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 553629622 1250 553628372 553628389
    0x170c0406020c01030c140403050703050c032b0507120e0301050601020f0a0b061305070203120901060f12050109080f091504030f022b11090f07020c04021803030408150f070e 76
    0x4091b180144241030707a0141c05c40309500651044c0c84a40c41007800780709021041c0b02036510044100d0080c8644081400704002200d2800e05030051904051468003105029108442034a41d028a034406104440e40010f007050000c100e01038040d61030407001034015400003881c12203890351400144076802940c1e80c1d91454280050941e9000301c0341201c091a000d06500405014140c01c1e000f654a580f2058800c0c100184020010551681800c408129480940b41c00303400341c031610010340c181076182c1d0600c41e01404c40300000034804000011541e01031081c040103440329100031138800da000005102a020340340168000079119400c1400c1c06e00c018a08410f02500b880350701a8106008540350074140c000e400c21002c15202c0c2c1812181c0c0d1070700c92030031144d155442100d80451040508007140300070341e0b980c0c02001c594011540060900d00302403a10b580c4d2514210020120b81d81c82d0744a120079507c50f89950f48503002d80303601c54049178860342240748c0c813407080c4400d95400e035508401070104540382 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 553630872 1250 553629622 553629641
    0x31112030d0b120d080115050f0702130b1905030c0a14041d070303171e1b040509040f050d0212030606070804030f0606030b070e01120b0f030d170c0406020c0103 71
    0x20340d55520690f01000d2103010025a141e80b120340c0150314201985500d0600e603038000003082820440001c01c410000169000181c0654800300a10009140f00c0000c14440d80e40f01e0b0300c40e1221a00ca400030380b404401809450083c0d05440b4030302c5046091202c0100140a020b580c03010300300c111401400d284d84110140c212690402d0007002510101504010098000768001614403207102c24034611891199000780c261006c0c0062441400305040b91040083e081120901d20182140c0c0700b0300f075000130390700506402800d2141e1820103140c403811664000f00f045440380915104880c1d03a500204680c400752036883e204034a036903034003410003000d0340c4550700440b01d403c402d10000c40416100c01504161b44e00c508000035402c0d0841c10503064241000f0a88000c101602c000500680d034046d0107001c2120101502250000b640f0001440c0700b01550f51141d0107200f03040c1102e00440e440b2281807d01041c840c4144026100c440c40c44030688118000c600c0581e0000b51010440d5100e644000080c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 553632122 1250 553630872 553630879
    0x6030c150507021c0206030c180d0807020f0a091a03120705060c0d0f0c0503070207050907090e061212070317070801060f1206150813031b1a040804031112030d0b 71
    0x7130028550000f03929810544943c480715102081d12884010401122a420142120303200201c03695036484400743c2c450717a4402802001a49c3d0302c0540c5896030601e44000d051500030038040301c103c0d02e00341815404003c039424400c0c0b1907034144010b800052011680495000800740c401c0f50760b0240c5c00c0002d6884041c9440c1900c1e03880f07405440f0460340d071140081c40c000f140d603007559030300344440c00a00e4012242c004030b226015110078060440e4020300e0042c03c680400308142c00f02d640c0c944c0001c960310a902e036049203d0054514103054844900018001d00d0700c2a182c034007803140095243c103c44101103d040380455a004018003009008201c1e43c1000e049528200b2111142c0c5100d540c00e071240760b4001040700044040211059401c10109640031030449010801241152001030050222803401002202c0344007605003400780c01070400b244c000c03110354810076a0400b80360984113a8010312043e100300c40d1012021159141c0707146141250310081000314284090403076a000107200d1030031155030 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 553633372 1250 553632122 553632169
    0x18021008091006060804030e120c0d150f1409150103030e0d05010608030309150c18060403060501141806030d3006060f050406020a030509011b050106030c15050702 72
    0x3a07001c00da0003440301510984d03882542c0c5080514001c0c102c0080042101d100b09c86410309620322140001c1d1f10031a041044410000f14610303810039046015010039140e5a01e4180010340c50300410f160805005040c11080b88051941c0701f00615031174600d601f03a0ae201c40e0203000300402c0424812000f0014251008000d4178040f110307980e40508640c16603018510503000481045034041080c4503203415080ca4078100c40252811480c0820203124100340702c006a1402c503080c55003611000706443c065030b44840b0070411940c4840c04490410100000c0710b10400308a43e51080d980c91801c0e0250260b0001341c020b1006240300320040c1c420703100c100211400310110810210340910700b0030910140380c2000600060b11414a04002d04000310403000d0300a00404100403c8a5580014120351070758151a140e61910281300c0101ca641d894818401e003e0b2003250b20003828804190700c400100c0e031046203c0e0542503a034004158203540000024008103400f4407224015060403a0890300550708a8418403 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 553634622 1250 553633372 553633393
    0xc0a08120f0f1b1005070e0109170a240c09141e0d060b0a08120a03111e12070927090f0506040b0105060f04150903080a030c031802100809 61
    0x110f400101c800c0d00300c0f040d40400036042590300e0300e108140d080500c511f4a114645c1c901c1c00003801121076440b6455140030310200030304942e0010b0120001d5960300401241c40c0340759080780015541a00c00f0f201c030701c80b850071a07010589809154544100c6107422070f1914803100c80b504000403142c0310880041d00080b000e2000c1a103607190030386400d00c94460840016403070000020b2000c04003054000d1074481c0d001400c0400c0c60700c40c06003600d80321034240c80d011942040085c80c2000c07500480f11107038001c0404255106889182c400030300403041d1031081c040c070705903a452811034a6100c1c034443c0321701d00c540c071469034010300c0c0080c0904190311428640204a80041d80e03a0080d4111510006039a1074116000f400f0405c410795036401d00400e011103015042900010440002e071040703114209003100615460038015000d111080300840d000f40038103031140440e40307001d0046c00302100203000182c58030030000001d0010301d000130303013040c1c018000e400160070b40d60341901c04542c0505404003d02c1005241c5 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 553635872 1250 553634622 553634647
    0x1a100903050f161a09190504112101050f0d0201360906030203060f0702190b10090203090a02040c12150501031a0f041a0405090c0a08120f0f 62
    0x40a000c1c2c4401030090000d240f0642d111a0b0064011640c0f014482020001003e4168151480300c1d00442c1c0b415841240017403900701c0c0400581c041034015081c07111140c00a041100500380804001c407070142032000c40c18072859400400d00806600280c0400541c0041c180024038038141413040c1002d12001c0b44c860002c2d400b00503400002c102d484a00442d02207005942e103590402011110818020729086500007500e40c1402001c824103d02c4c5400011500c61082100810701800d02c041d800c28140300341007908800c802103544440044042d1070014101c00c0c0c0d807003100e1044481001400310b10744aa800c0002800b401c041e240204016582e900f40c0d402c1440c403900042c0c0b000600700c20031003840c00c000982a1002d490040f02c451445040041c0745480300880102c0584040700c000900c545d0000b03000552100d181c2540d03802614010801c03446d0b21002507544402c58088400a0f001c565621410380c1d07e050350018410035010600208003005c0c142000307001903004489626080c0040301561 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 553637122 1250 553635872 553635883
    0x30c0c0b0c0f04120201110706021b13020a02340b0c0c090a060302130204051c061805150f1e09070909060207061104051503221407091a10090305 64
    0x900305084d140b03140300115038000504500e83d102c0003005d0300d1500d1034070b40d01940300c1c0c2e580504810480909007030003605594080c0d01c0111801c01d940110344907808904000d583d0444880740b41c00200500030034840718500035030310300c041c050516909411035041c071440150b2030304041003400c3c051150118640080d52081001403080d13480702400a0a41e14500400241c540c0b0206460007040c070420050000d6110814218040d10191221240541c0d480c94410000c0c4500c3d8850003030714850132480d4041104c0861082840424040c20801648031184940080507083d9116910608100c003604003000402b41015481300071102911821941c4542080958607842c0085480d541c1c00a9540308001d80d612410340a604900c0f5001e013482d04080214000c5c0c2e14120307951262030300200010f58450004010b0364001c40c65410000d20803c800d2400c0311c14003e0450056a031801030074004640451544138540180704d40981000c0807207000c46c240010704841c1c0c2d080f60104000c0c85004008500304004 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 553638372 1250 553637122 553637129
    0x6041a210a020307060816091a1308070f0e100501210b06041d090d0f0e0303070212060103230604230a0309051e030709111c1b030c0c0b0c0f04 63
    0x44400680c41d003403014101c002003d55405003884811041130141d00e008510b40e00e0114000c0c01361a0b590100c0ac000f0850300c044541c1b0010f80c0d40704e001c0000c1420b551000c81c1104640d00300c0c08201454480c03102c0c44d140d00040c2d015040c0003c0c0e500c90107241001c2c181000040ca16044180061a48004000310f0115403150300300c042101d88896299032464550a000c590110090001e4014499400b030000c010540004901c000c100c0c0e0070000f0011580c0034822507400781c0d0300070701d001542185c0c191615110340f8244000d40344d10320a201c001c04291940c481c5801c013800184040c0c01030307907600d40e14400118601146840310045040301c850000c10304220b03003501d1a000b40c82c1c4c40c004915090070003142c000504660380f0380700248134503074ad002d460000c0c04005480c0329032800718884000540c40340300d9008521041903006c80d0b42c41e040c01700d901a41c0c080042203400d910008480b94400b01c06400740c5800540140c0060807004490011074461f4031040e4000b00700a4205107800b918055000041d0020340 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 553639622 1250 553638372 553638377
    0x1060f021b1c021f1d030a0b0a0c0201180f0506010e04151104030f060e0c1009170f1b03150408070b04020415081606090b0f0304021305010e06041a210a02030706 71
    0x22482584400f1744404264200100c0003040202c94550f1240c5e810100680030317200054030f9a035034800704d5001707400482c14075100384944841504030342860030501034000000d6030180075010010441d402e00300c1780c89204540016140b0400c00e0140c04080003030100c800101c0c1603440c14000800010f500301c4403280c0d414000c10000c1504006258003605040780f15158601c00c1c00d01a4216500130342110001d01241e032020301c0740754050700c1c866105041c5880c4243c2c000150040130740144d28241200d0702854551010340480c0c00f520200100c21880d0001603401a082100034455607001580716140c81d540644054004078100021210100e241030407608583e1141c0c00c844a14260304003410480707802444141703410001d00b45040c400007420705c512a200316a8078000400142551501c6005100607035030603400700103540e540c04000281450a88a50348101d0400901c0303244000502a040b00c004d03c0200500401401048a420f0001c00810b002c1c48030b0280e0040080941c2c3d0034041c1030000c0c140c54 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 553640872 1250 553639622 553639637
    0x30506030601050907120203090111040f090b04020f0f03090717011d03090a060c03020a02030a03050d20030718090c020106050117100b07021801060f021b1c021f 71
    0x11800c250074640141c10140c0150034030003c100c2119070050400c030304940403d40041c0e480c0c44a07003082c0d0140c1310101d92440515030001303000508401c100b41d030501b110120300d020000100190300b004103038880c0d60a2901951810300c801c0d030700200040f00031500300d00e0000440d01420307074171111041002c10303004520310b043c0d40d10080c45541d5240c400e044001a0b680b140590f04d0020101d00185642086000f03a00c108102070fa1207104240c000c200344448560001c4c02c46040d0445450300800650020031003100c1142411038880c03240b5500540e42d580c0a001d002010704580e20030b00b0407600003008038500c00c0e2800b5030103c005205900c502c652903c12203640d0002c0380c15800d0000140065850054142e8120075030703000c2060a100c1d508015080c0c40312045034030b5030b5940c07500000c0e9110340d4103060b107103e41a0b803500006205400c0044030032114400c0d000e0b60078112851010044901c08140381603005180f045c01000046200010094101e200a120340c00004c00c020301c40b15800404001d02000c10f520 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 553642122 1250 553640872 553640881
    0x3010608010b010f0e18040512031542131e0e04050303131406251715060f03090706170603030901141b030403061d030a12090b0103030305 61
    0x1030504044070003428248102c49040c0c0102d0b2519088042541c2c1b04000c0c400440d0030850244000b40407001e5410345541c403424102811079000c50074052580c4249016250b514003070706500d44145100861582411041d02401a0603042160b010810080c0080411500c080c0c102d842c01c0a8010341150780010300c83c00905954280354910380e4109410242002c82000b00080d0b00000301d9510036030251581c440030105250107a40d85000c04080c1c030042c011041041641e0701901342c1a01d0010700320413502608a80c41d9000c1c0c9603401d0b8961480d180410a000081b40d420082d800c40f0701150003e80654074103004144c0c14051074100f034407a54056088820200141d03039010307103010580e03504603031007010070300f00760001981d2441611040c0e81030004c02d2206045c900d241c2e8050325404503d1240c40403000a00c990950703100e03070040c00100c1c0c840e1f25180300307071103140180700410100d0700b82100151f03d4420582016100c0140c2c1c01013040c03d042d103c40c0d10400042c14814482c4c001d61180e1008500c1d400d0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 553643372 1250 553642122 553642127
    0x230d0816030207020a0b090613080115050f03031b03040f0605280503010e0604060819051c080105010809010e0106090501240806190e072001051005091503010608010b01 74
    0x684480000c1018010311440015a0f2000001c5003143c03a2020813036038440558010400c3e83c010301c0c41c0d2108000811000080d030340410741100305000241703500380b46120784510401100e541c1d1000c0a5805920a004201d0408145c0030fa01c0d244404c45000c40b411b1950781d0301a002031030907a40109002600114a01c00034141c40d0200060204080926841009500300d00810a000c14454580c1c22989200800c81c2a200d6034842c902416040c01500c5101d41711904a08982c0401c0300304a809119201e14410300340b02c090701c80001c5110076540d144c443d0346402e0046524000181002c2119507035095091090442440b0386001440c0c14080403c103980742030b00c828030718030000e052000114448694121002e0340102483e0380500c080710f003036141000420011201d1000c50704883d1100e2121818000d1481c1c10000c84525005542d01c04031400c40140c50030390a82d5016569103180c00c40c0c0d204140105d150900a095014010b580f50051141c10f0100107801d48150f81d00101903170359942003081c02c0c1e5a = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 553644622 1250 553643372 553643401
    0xa0e010f0f0203030c0a030b03160602070e100905071707081510020d03021803011104091508070306020d020c061008010e0c0603060609010e030307031e0f0804230d08 73
    0x441c0c1402080c00100307800194a9210041050244080000d290440d01c1d0290740808010003000d4202c600c40a608403a0300355070701560041c0000b6100c0c1c06c0d000165075801e16078240c0320741e0b4145007901c541464401618003400e805861a82407040c808280d03d00301d04e1410f00c0364400c0840d0340d107540307880c1401c2c1640b80c8004402c10506014200112403d1103c5400051201581d151842d0040c2d0300d00a81907040400c03801209050f905500380402d5a00803070314000640b003600d4201d0710070000b10700b940d000c4002d50240e52040d14080c0d040290204080342c0300c0e5018244510fa4840007601c2d1040124440d81025070498140003184044801440010402d1103141c000c1803101004080d40600c8000046080c00300400c1540300390300000340e55401c1d0340301e42d024251b0f0000250480c1d0b1104000e1a006d8030000200441d1484d143c0a110000710103403140003120000030350f036280c1c0491a00c60361508420800c000c55040ca080355a000e0311048040c04105480d510f01d019580c881c41d60401c130020a0012 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 553645872 1250 553644622 553644647
    0x80c0a1d2b150209180c0c0d0305150303040f091505090c0304050d0203090d170d0e032205061822020c06090a081615051021080f09030c04020a0e01 65
    0x1078818440619107813612894080d11015800c103012140c6d03038220001c0b1b25441040c6038401c060140d011824040c0d42c043e04814052901c200103038a4044820003815520b004a1084031290b1a40c103d04000f410650740c0000480e107802902d103410540c9a0021401c5080c080d101040c00440c00001c01007440000c4c0710b50140e0083c288091480e181c41040024806002d40d072014102c101e4404920800491000032070740001c2002c64180210354040440c2922600b0010488a040c0041040215111609000d140036504020100390500c9003044400c03505140005c001e54000849a4075181322100c4800074818051900754090303602c0c00e1103142c0380c3c1015806408160300b90701000d0020001503c03a8252110400c040c0b15410ba500320034209048844444206982c01c0751412052201e03105d00416403405690000ca03407111142061200031800b0000b10b80040c05422090049035041d03042c0a004041283c030060880e0003004200000408030f0740101d03d41c03400702d002195405031035600100d4603ea82d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 553647122 1250 553645872 553645913
    0x605060a03050d0e060c06010806160f1b0f020a090606140903030304140312010308091f02060106030e0c0a092007080f09120a12080c0a1d2b 62
    0x5469640c5a5075035611403100c3c4000c0c0015400d10803501e8548506460300c100c2402c3c115205940e40d12115034484d04103403041003506401000c1054414080c003036148004003660b13119180c45445401d40d684a00640307074121001b524851042c2c1c05aa201c40300c01019001d2070340300003905440c04401a04c0c480941d1054000c3d01000d0011405a41d0080140ca034895041782c41c031403d40d8a505107407801c62040561850300c0c52070000010050003414805000408000e491040450000e00c081c014110210140782006034800390062005500c01d40280002d40400c0045843d0110208001401d0007500e8004008803507030f454200c6481003c015403c611385440c06c81961030100c05da220b00d40e0074440c4001110070400f000a84c98000c0d25201446098800c0304400e680807109a458003d8030010352844007000038084d40b0200d1900c3c1c40d07507022280c0681a135150116104641c0248036500600010419030100719002c0b0503441401c0345203020003008010700105640044d5103802010102c03544800101e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 553648372 1250 553647122 553647139
    0x907150e10030e0d1106040206030a1b020d02010c030522052404110f0303040e04020303280f141b0c060f0a02010e03070f02040e0a06020f0d06080c0901030b100b070807060506 77
    0x444001050054106406403001d9a803079885040c48004cd10301a0b82c580340e0400650320142c00c455020803060074001c00e660007804030b541e20880407001d540d001d80306c4608240003804080c1c0001c64029600f80c03a0fa03c0781040c1c07440e03018409900e0801d159845072000300c0c80c41940401042211500401094141c03c031141447c18148002083c1e803402107000e201c880060384000304065560030030564205502e020b41c14028130020684005a4418840c203290106140199211005000b90184052009801d40b0b45042000c0c40100004442c4200c5000205002d00703010690a5120a40185500c41146000c00d03035403c6108002821a8500d1012124541007400b0b4000001c0c8803000c24098260112408a8000304a070043c83c105814908018082d6100041400030000b2a10240c240c0d002700d403008108155403034007401d40b41c2d18540022503000c0080d40041c80000c05004c8140d40040b40d5076802ca031220b80b1012943c0b080c1e480301d54196503500f0f0103d5150100700c2940a002c2d03201509680b180f4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 553649622 1250 553648372 553648397
    0x40606090e0921070609050604110405090a0b16090801060602030912010509030307030c1e11010b0402030c0307051303050f0304030c170703060b0d06050a0906140907150e10030e0d 79
    0x10300c01400311107030881494001608800780205d682209880607048426149030341464500740d03e8003c580141030f4052400c2400248084401259a0501c1e582081a200035a6100c07900c6400640d00003149100b03210712020003140c030040912601028003800e0b00150741d00d10900e02000901240b064a02019a05001c00c0140b0074030f01000380e942040f1641804035a40c1010035084e03841400d2220b0113801d210b00c1c40311440390598000d90032648070400d04002c2007a031031244103000591008803000005000b04202003045203114600030000c1003010310701c0b24221a200e654080c244440c1c1402c4082c164800704041c41881100c0001c0d400500c00c1070b55840c0d41042202a0a0700c641d0180310103043c0300e50fa80d00712502a181ca12810b481558881c400b0400c0d480c2607802d8000900744008203589443c41c1c4000071480071a81c40d19180a2a0345070000d040e43c1d80341c28560340100411400349010401e00e40c210100a4555030071000c07182800340c402291001c42c02c849140340c0103440800608002c0d1400d80341d03 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 553650872 1250 553649622 553649653
    0x50f070f0507030302041508040c0b0a0207030f05071221030c0206062209060f180f0b061c05060402030d23031324050a05010311010804060902040606090e09 69
    0x1004010a080a64071003510b801d003134000b4000c6601840d844660503c80958003980080a107200d80e200301c08c3c03001d8491711080c40011900502c001013002d07a015038000e2010519000440c0046446401121130f07203600e50110365404004400102c4084911000c000c81244c40544207400502d16454104040103080350025a503810151503036005d104600f00c00b102d0003070145845415980c220707000b48030040b0149443d074001e02c07551032090042442d04200603086d1a00504001c0401c1d00880c0d002c42110064907500a4030340040d01450740301c0244050b80c80441c10f000c0c0400c03030060080000d00301d01e02d0302d8014503041405104104040041d04101e00610f2850031071602003002c000100503840382d99000c0031405080d81c40748041c0224440b11820005600d441c2c0d04416000c406c4c200910854541341c0b04003050f9a001e0000814400491441c50203951081e15525809400340d003011684104580103d000c0b11342a4000100280c003112092108443c100042c40d00b0103651401002102c4048040c07 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 553652122 1250 553650872 553650887
    0xc0c0209070c02100f031104081c03020408120d150b030a18050f070f080d1209080d090c060f081905072105010e0108160306020a1202070f0303050f07 66
    0x9108152200200d900079118540000001e5400b0700400310555904101034109240010510002414180b50908002d62101503604076801745d801004440c9040e03071800d101211408501c001c241d801e00000403c170004100140c0008030101044c0d54415644c0c204074190b0f281428994508000c284c0f080202c0b4001000f103c1c4d11035510100002e02e8075504440c83d4404040907005006032041a80405292601003201001c480000058480300c694441e01140c0b1560740c456850042a0002c001c658501c07032907080784000d184144201440d024021288004494800c14140c4808101010038405660080e06099040e001c87c100f024892130021410b43c145a9004050100c1a8440c0e000c10007280c01400710034041c03884000684540707840c2003810740042034244140030310b10118000000340c00c1070108100f245e408c0291a841511810340d11a24003031350100d13440703104012801d40e40d600c0403091840030703000080c0300f0040b1207140d127041d0600900340d4001401200c00100d0003010b1100071900301d0403 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 553653372 1250 553652122 553652147
    0xb1003020c0a0303020904110c030901021e030702010804062a03201606060b030a02130b030402131a030a03080f06180f06190806070908061501030b03010b10051b010c 73
    0x203015035160307021b00100f40984040500c940d120800414442c00019010026019244c42070b82100c1011191000c2e944500041d0041d080071500200102c00140d441040c030550311034007608012812114101c01c06540f14003505100307180c070a0100382c400d14541d00d8001c20480d410b07441404030300880310490b4001c0e1803203034030384410042c02540480000c1082c141c02140060040c5c10560342c492a150988101940c0701008c404d40c4e0100035a070100e250842034055902450300a05000224080c0d010240f009080b80f004411302c0020034a11190203030741c10007040c40403a01c6a0ba801946040158031540204000362080b031003120300c01e20340b03040c0081881c40c032984901a0700c080300741520381c403000c01c540060780002852541482d01e8040398803100020401c1c042c91165841d07041890390f40c000c568488000b81d40c00d40325480c10b080440c1c40c03503200307800c190f0391890020000100b03a022840000d44c1510103400e040089400402c847c101e0803040c11422240110350380003841203000c0408018901d401900 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 553654622 1250 553653372 553653377
    0x16050a12020d020d0807060605040212060d03110d020f0115031e08070c03060902030d0e0928060f0e0a06080d1b0b101403150f0c120a0b1003020c0a03 66
    0x301506540e504240c1010042e0050702c3d04210305801e003001d1403190302070b28040d145181040300c00545420184212103040c40c00d152019800c1e12200b082003041a500c0d40e05078204000303800c003501d8a100502200c42c01c0317500d40e001801c507404906c81351402e45201c11001481c035001c08600308041242d10030300c102484a104000c45001940d40380c5156035001717900000c1c180c0e83d200c6801004010f4964040c0301c03450b0088003110040000600c0441340d40200603d407640240705031011400e103040c10764551406955803640c3c60480382c01d4102c04c80440c0d001364000168400e05800400c40c903884044410340105180d84240541820003020325035805c0e82001c0d14040014040348248603540d41d0307052001e00c9074807000000d802e00f00308244028801150140d080003102425040c00030b45000180c10300c0e0b1644501d14034140395142e83c810b0007940001400100c1c5040d003000034285c1215012011445036006000c009564440304091060b5112030740350840502d441000f60300c030b00d401d00040320030f100b50345071 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 553655872 1250 553654622 553654649
    0x30b1815010e0d15020a17100311040203060109090e0f0a050c0906010503010e010311010e0607110310020c06010e0c0f03041a0c0c101e020a03021c1104140f09010e060316050a 77
    0x107240854640300701d030001e81c1100c00c0d00300602011123032205000c022a4040c2c1e080d00078030143d24007000100e02c0300b43c40e0b045c04503800309030401c45007500d40c009045065480c07094034800343e141107640b4201810230304111425001554030001c1450a03041c101c0d044078080c608107096604004212042d05410f000c007801d60003030400c040b54160f1050b150396403001e40c0982150345468032031600c3e0341c41580e6009a00d1182c00742c4079019030b9040480c0309039a86004003200030581ca901e4884141992030f00036152001000c0200700044807191040002c500170ba1291441002c4e042505115030904080234080552442d010000403401f41000582016810020748000800c0c071100e40c010308220310318a8035003030010700100d500901d01350036602900ba41192a04e014130381c1203d020881c0102ea8645050080c824824007090040c0c0c105e00d158080b0702d01c0003824074400089058000b4007611401d0b480078041ea041c00c1d04100700d905091042c442083d0725800d02d8000ca609060006406e0400c44c0039125040c40003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 553657122 1250 553655872 553655887
    0x605010503071b0f0b0f010608090a151d0f01050f041110110706023003010e0a06030203100e010b010e150c010912020a23030a030b1815010e0d1502 65
    0x207100300b5030f000d103500c01d0803028a20610702e40780b400080101ca06000450b207200000030424002e60007507120301d070403070041c0024801943d11a10a000c040402400081d076500c0c41c402164010303090f41a02d0300d420f400070550942c240c40b4043c01d40b07100402100e87c00124506020000d0101102d011244800300d402648040030349604a0b0152254030143d00c19204060b0002982600442c640140e00c184130400b03040200c10700b50030b041c984240c0c60703100c0020701c04000411042040d4910250002000b207004034000d6584d4001a01c1c11051407180c007109aa20039061028403000d114500f0114002e00f4100c94006810300052864401c01500c0b051072940003d8a4510007002c0d481000ca10743e20400e5000c81840c0d00c1d00007940e030204038800322040c5c0d14038115105d86494010914000701543c800031482c0c440c0741d42c0110098074401c091980c0294040392100e42d142d20054140d44144001d010244686540d1000184003194402d4094020400740441030081040f0a0340321410321190100940c0c3c3c0c170035 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 553658372 1250 553657122 553657157
    0x10f08070801450303020a020118150e19030801051c12050d090f0501060303020c06181e12010b0f0a0e131b0f0806100b09010f0203041d090601060201060501050307 72
    0x6810340e034080007030f03081e8030b103601055019400380c00c1d500b01c42e90003008003a00400c4181c4480c7c054000180490301488900000c00100307800c12007072004c0c1e05045d03400409052160860005a403c422004034017000010f0000707040c000c040304032100400f803982c0c8800a0b5519450f02d08200c010391041000301c00190040307114410b402940e240d540c0030611280e1494181861350081013107010882c014040c40400801e2860030a003610382d09007481d2100302031508078008014645407070091211980030140000401c0f99165054501d90b1940707880080b408003480010000c112100c507540e9841690b904500344042140310089580c81503000b41c0c45462100c0c181420340c1c91240030b020304044605150004101a00028904011603503410110f46203500c8003c40090858800d0240421442c2d040c40303440d4040d84a00103401406103035005591138103440d00003452642c110041418001c0f1070150900460380c00c104807031030042020384000c111050070140000c215100c05403001c07080001c00381000f2030302c21 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 553659622 1250 553658372 553658471
    0xb01140a0b120405031c1409030316030b01091d090c03010e031e0f070f1a15010e01030e0601230f010203040b0708090907030b011b030f0c03090e010f08070801 70
    0x4043ca030380080b8541d1805544040c19007200147c8041c0344080101e0240180001680d0049412110f800040e0101400440007052001e6503281086106403002481070002c1034031826a1001290440041ca002106070346843c1151451a003e0380c0761104080c0c84d810f0100540340f03414020f4600541041e00641c0c442d03154018000220040349001070b0005c00c0009c00c100403035400e841000c29460302c0c21045992a01c040044441c481c40c8207040007030024070743c8150400c2042c104141000900c8031120840345141100036003082c01c240020052801c004100d4856100d1000c1c0100c3e030800d4120701d4200002c3d16809103100300440c1c10030204020f02040034000c151115030801920346000351030705010003005400010101ca01042401c5a2400300715051401c800d540c0c0c3d007580354510403103901170046844c0d1007540010f504101c2d0541000c0354010406500768001c00940356064444c60030700002c4c0c0e0821000d80d1055070183cac54008407524030075180050603030082c3c41043c00c60300c1024403003080c40403c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 553660872 1250 553659622 553659637
    0x615030a050d03090b0a0e0309010e012609160b040e1803030703050a0e150f0a0603240c0f0e0402090d05030703031a060702090f04030207120b01140a0b12040503 71
    0x10b000391100c240000d54181d00c043c00041c0504140c0000d0b0700c54090850850744503044d810400c1d0020030401d815035010708a1500031820614000c0d0900314220a0b400b01c161940e10003009242c885030a0242c0e20004201c04204004800c144c034a89500d0008160405d1040d8480d0f03c0c2c6083c000800240e100402291012107107504c0400e60340d5916148000400401085410056803482e143c811000c030440010800301090700101c0740c50060f2110f101480ea030f03c0004005200e12901e0303810100003c0c440c0804010304484514482e280307405000d40010954802c58004020090141415100e035030307100c5050001404103450040ea2a011640894070704411000c001d0001d1000141d113404140c0d040d485000303e0307010500034108051a11040122511442c03601a5208507540003290407017060b1a2000d8000d8841e0044030241c50b510204010014550881582c5071207000d40100600102e21070032042c041412141c8001e2181018580c08050103901d181c002a000d80300300280c200402001151540c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 553662122 1250 553660872 553660883
    0x40b0408071a0609010f06020a0609060e030a0207090c0e0a33080a0e0d05040501031107120f0909200327010b011205060105090603040503041503050106200615030a 72
    0xa400100740b0800c20241c098a01600500950780005208800c3c8030018013511515806050102e8882d2504170107055a81c0c0291400e99803a4030038030404804000401b07a01030141c000e08003040c50140c080d021580c03503010340030902c80f070917006102036922500521300343c5811a0040c01075900c4014648282c08003000440480388540c1240141c80340c004001d640708040d081414081c0e01080b1580d0b03500c0751614041ca0012072400c0c00117003d82d60184d00900c42140c48491241e09102c015101e6820020068012402003260407000b07a80c0310f580039000f000903010841c414421000545c5c0a01c8240000fa0490340031100040041605003661151004190640d5143c6805400500c5030080c003c220102c41580030030408124080c3c8420307240200c034803e89058441a0514401d40c0600c4015480100116441d000800020031004c1800125803039408460ba00003500350b0400601800500c0c0001110002d87c0c0070340d10407050001c0c0000c20380e41c4a000b00015000390801440400c0c034248007490000d01 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 553663372 1250 553662122 553662143
    0x61005070b040c030b06013b13140a0203040f170904060602030a021e0613140a030915020f06071b02060d0e0706180608131515090212040b040807 64
    0x184004203007800c0c1603d004105d0032105845820054844ca40000c1080f00c8038071040b503488546450f401c0403143d0800310700e001c1804500c185400100201c213020204204e00d955503040d11481d407900c00b441540911660011840d60174180c58591101e1034407400100448403003208500e0802503001a1202d130311014106214880d11658069280d4210940d00f400500c1040301c901c42d10711286142c0410011490081c18481d1039030301d00c08010414803181030790854480e1190003051201000fa105040b8000e83d144101c3c40e08040940c411080001401c608662064180c4802c10402107012504104039041c030701491000441c051102850b4444040c1d849000855034400d00207640e0410701001580b0400e41c2c0e4500e4440205a03521040074801d0758104404050038042c00b406000f03420780081e10626034608102465a600c1d6100788818000008192102d41c001c3c036442c03000d1701d4400648400c4d14190304200001c0d1a40c00c8140005002505010204001c2014031610a00f11410140c10229241 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 553664622 1250 553663372 553663381
    0xa1104150308120a05071d12010e0f030301140f0f0103091e03080a0b09090307080307020c0409082212020f1f020d02060906060d060b1216060201061409061005070b 72
    0x281e81c200100d6503603030005e080c540020b903000c0c426056202d811071941d2440b41030210380c030240443d03688010340c3c914a41d076031411240f503010010071640c0d070348000c110000c551701e6042c90300302003500d0254071026006100144d8084140d903103540980380d40d420286000100170441d070030110308021006e40030200360a4400580428107034001080c0d48684074017881804a1003120050200d003000032206402d090b00140254000104041c4c015500300310325204131a03200156800140c1112521744045801e00c5000540410300f600c1c110011702a8403401e4128be12882c5082d034551115035013030800a11600d200a03060341e056546120244120807114480030710380502c00c501964900f24004420003611a003400109540700000b0007520464001d007a54015070400e0360703414098001e54a8113a0300945075144168010004c00c004030069040000200c541e5151040103030844481c1d800c10300201a030790340d42c01c55130746518001d035030040030035a108005603d801d0170448181c011100004c001c511600e0a00 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 553665872 1250 553664622 553664647
    0x60507050c0907090603180507050913170901031d030406050714060c0702030f2b0e030d031a1c0f05071a0a1214070806030a02090901050a0e0a1104150308 68
    0xd909803021074031b0800041c890503a4840d1580420040205107a025100500950410b950003580010001200010080080d0b8440b0180421400702c400c1061003c10251803540c1e00d030086215150302001c2d264414084c10035091380701d06c520301541040c0840000c803082008400311203105200412015507034141408912162517a0013030390305901c240300e056440b07a400907010400c62402d2a058012001076441160280c3d104a8a00300003014840780c40368640301c6850902c540902000c03942d80005000c1113a40c1000700a0b040415168099050201c20108682004400c29000d81d08001d602c5540740652600e140341500c241c1203c001c2c3d07811182c9c0b10183d02e030490080c00c2c02c500184c648441070a0580002000c448100c0030001016043d82c020615a80c0600101c5410810250070b603160405250007040030540c0540307207003c96a55403010800442d000d4480c11071840c415101812006043d611680d08042c2c40e003401c3c6101d5a030703a02006d500c10044051074001150f114030b409455245030f035400c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 553667122 1250 553665872 553665887
    0x40b0f04030204200406140903010e0d0306140904080d0b19031a040b0402120705060f0414062107020c04090602070615052b081306110d0801060507050c0907 69
    0xb28016420b0801c00002c3c21101d101914602900c0d40441341450700e00102211842c10000e03071059041000c010074600ca86081c001e1851507418100103225074020280d0007011500903a0101c0c2070076481042d5065243d50340c040b031070303009600569900c2c0c40740004a4800014003414070080e174000f0341c1c103508002044e031907240001140d00035448141000d940c400303100f00d903010868000b0070036082c1500040c01032070800060503100c1807010494100e59210008200c09600403800c01540c02000708023000390780d841a100d58045075081c0c0d040390421807000800000c0c000003000040c0b85044d04800155498801c2041c1807001000400c244001f5442d410100c0080d0b06c425070980d2100c1c2003c4400200c000c01565000c01ca42002d405141245c8070034074980400a0f24030700d0f034bc084000a02105010840b110080c2207070010764110ba0384014544840503008003c4015002c44070340058810406858004129504540309400c00030394850b00d624084d4200000c0080c1d559200d8030f10400d010700749901410 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 553668372 1250 553667122 553667129
    0xc041a031906052401110a02040213091104150f03090b0403031a0103050603030a181703090a06030c0203070611070f05100e0102070c0308070f1203140f04050a110105040b0f04 77
    0xf040300740c8031050110080b802e40300341d454080650303c0e0000710a5202e07140d400354044d180010b540201c00c01d5030001d01039a1002443c400328011040042c0401c074228031611001d42807400c14189441d18010015051880b80c103007540c20b00c41c0003075070000a81e00030341110f1450381e8001000f828510b41460060020241080c095160501603094411554028070801b07024080050041d070a01c0252a01210386600014118503e401515800a03c040d400803400d000c0ca001c10303020b5034540080d1008d04c580440640d024104260400c0b8583c15110b40120486942c1d980001002c1105030a514100d4228403801c00020580368547c0d20b900140a4080f905800c180c00381101480501040c55881d8241e02034018080c104401c0704408100080f9180c00401d401c52144040c1045800b0940700c001a25861002540c04692500d80c12030440ca51038a0740c541c050783e6040320001600b05512245e0351100031a030020508501501c1c0007002d40c1c000e10544c1d0007803009518480d59030509000d0000f16400610 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 553669622 1250 553668372 553668383
    0x20d050106171b130906060e01080c040302270f010302030601080c1e0f0a060306050102060c2803180c0e09060403170601030f09050c090c03090c041a0319 68
    0x50010079014440c04440c81418284902c424850b103452011280b409070030754103080010010448016030f106804502001030005c40000140706c1c2c60164050605081c503803100b410884603108201d00950007070291029250107039101c200c00c0d08503180b1213030481e5100d04200c1700488104100b201400d02080124140e0f403084e8280d4910380da88491166456030030004941d4056a0940040169001381c01d200c0c07003e0030000c000224419010340465900d908a4001c01c1c00241c50303c10a12841d60100310705c2d60402e412245c001d03d0448030a103010000c030100034003a00b4080c0014401121148680c0090b00d44119000e2000c41c0c0d65914501200e0208151248450505c011800200440c0d00810b545100d103070140c40b00e002105840005000c038186c02440e55042c90b0707543c003488030f421f00345200381041948104010003a91515204103c00010010880c0d0010b403000c000b044200c003000320380454142815117010891140200728000300401c942041d58041c801d5034400c103145540080ca020300a40101e = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 553670872 1250 553669622 553669631
    0xa020304060e010c021504020d08030103030906111b3327010e100207030b010b090f0d020604061b05160e090f1e1c03020a1202040302030d1110020706020d 68
    0x40c02203d09851400c1c05040c0540c200d10110011801020388441c0d2040c40100741c01210001561010415002a0415000195403000500006030009482c0b0b0300b403401d00008202c14500070030296041400c1c0c00040d0301031000d44016070b001e0400c20321902d20002c610452410303251065040d2a280390407454070324500340500c280c1004404510060212901e4042c1d668150f08811082488890504c801c1c0c8042148a10940000032903480407003d80030785482c040c036a0b030b00c8080070108518000b02d244076034880c50040700980016540c08044604032201404e00d423007690a8042a8450440e803502c2c058114042c8281c0944107455203d406000d03102d0040c55403c3c6a00d4101c1d00070f50b03e00401c000c2000650214041000f080d11809035401c110a00000716842c01e101d440f86507488040300b1001d500402c0d0042085408590400a00c020a9030070000131802c192540d00080e41d2070910039060014031001800006a1a0090208d0300103070090103c191754512107171810304002c0d0700076050410141e107030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 553672122 1250 553670872 553670891
    0x30a030f030c08010e060402090109030b04120f050a230f0c060603061e060f120d0201060509060d03140711090f040b0609010e07030b06090a0b030109240303260a02030406 75
    0x360640b9045c2c4030108803204160341c0c0c4505210003540305a0040303041c80414540000001c64490780e03603105500c07564003025011fa07440000342c81400002240b40602c50180882122140d00c80300300041d903410f0300c00412100780c0390039040740380e8440c2d510400074401c00020044a9a18005146802508240c00f1140c03aa6148040419203103c15507010000c078184001242c46807a00f2410070b900b49100520501c05040c28140c114a450f6030b42c03450034051f075141d50741040310b898014a06680300c0410f80d4140ca0110407990018400c06024040a1302074a021840b803040c0f048500340d8102c4c010b0080c1c010403c3d070070b02c407000c1e0140c0075084404481685200340000c10504012038250704843c420601c0320a2a101c2901c2903000d04119a085500100240941111665002c03440c0300282090884213559505003a00d0a01390b0f00c009002d5000c805010070b040091420a84101c0105c0703826141c5400f001c0307026401035142107048608c0c0100c04140c03c080c08520030f4281d00460180c3d20030380c4100042510b = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 553673372 1250 553672122 553672127
    0xb060714070e04051c12020d0b040c02010522050a0813090c020d09030201121518050a0b0a031202161502010c02150a0e01021b03070c122f030a030f030c 67
    0xc2103030001c01c3e42d0800c0100b5448905170f440c0d000716111040c00d0580a50a80030201d1080380c01420b5080d18958458040800c00e0801e44a204904081d500c0280010b1502035400c50b03a80b180c0c0002c107091200f52420350001e0000501c40346100c290720040310b41c0c0d14040a002e12001e03d0301405402615850300f0f400724081c44c0002110340c0900031641f80c640d40a07185030019980745541c00d4046041c0c9031242c2d10031510020031020725001d013400865150645161f08190f80455100800050b40d883c54a0008100f50352609004001c03a0340c000907441400c0c4080130101d043c003401c1003800d0a1070010b040c2c040b810401c0040032156146003903000700040c4180200481e5952509028440310b45560804900041c0c0c00d90800028000040005480e05d50079050380c4441d130080440c0c1c060302d50804070f0141d08220600c00040010000283c1138200c408030b9480d07d4500140703200520226800f040643c1251504d01d00d0381c05c501032001025500460b00504010b050ba000302c9030610002460b106c10004620b0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 553674622 1250 553673372 553673399
    0x20307080105180112030f030b0406180b061821010c02010507120c0806040c020c06042c09100b0a120c03021201140406111c06140d020916030b06071407 67
    0x44100309800c08032002910251f4045140204c804d081503142c5101e0b0340c40b91202d0281c41c000b07100d89128510280e4554006004458001c101d4501c1071208000075401002000350007807030945c0c2100e01e00c0340007400725030709070020340040003090700c0c1e50030041c20791001c980651015204600325159295805180156501140c110031a0307003010420340c10108140b4286a80701400100503801100d04074680000040c249410660214150710110310000445103c448415200415001d20a02807420011980340d1643e0301e044140704501d55440c5041000e0340e442c10418014013840708220680480b50810049058030f030300040e4040c9004108070207030300d0014403e8900d400c40085040352181c4442c2d0310a0701410034a0002e070004102440f44807040c01118194001066041000244107441c0541000003842441003140c89840421400400f5884402a682c0e01a01e5007030702c10000070040d80154000c0c05442d181a0300814081550b10422400d0305404000d001d20034202c800c196610381c543e0007402c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 553675872 1250 553674622 553674629
    0x2090a0c050a111603080d0e011e09020105090d060c3e0106030b13060c14030109021e0d021c05060d15061a21150d150203070801051801 60
    0x64040015000c02c0f8425010032036404508000e40d044014103400f149400b0103141c00c103483c141c00020300f0880c400c09520070411146510002803000c040582000040600c030b070400c0c9400c440c1c031000f00c0c1e011a03203d14100c0b90149401072590126601508040c401850308491040c0481c00c0071100b00482901d03490400c03000801480040c14185158200c0da104890703906a40d44c466498440c04400a41d82064042c401c0741d8100c1d0032683c10320b95040110950302034410f0001480480380122b4001d0341682c1c1181c3c155040da144c056920500400046041c42040780c14445184010a050b00b40300d021f07800511110031038400044050740040346510031150262001980a02040c486d540020340007d161801a1150307400060140d95071500107180041003480c0307462400340012940c50030414014495062480301201c11024503000b030741402e038082c44101c0342e44580e0205140008001c2c1c0000c1c2443c41000100040d0b483c0e040040f40074140c00c10a0140754032415114417821584200000c140f4103c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 553677122 1250 553675872 553675877
    0x40605040617010b03072609010504020a0e010806010e070203090406060201150e092d060906040204051608010515090402070803160c03050a0e040e031b0f0d2001240302090a0c 77
    0x558403100d1b4141e6280c0e044600c0c0180805004e1006a5407182100f12544112071060002c6510320302407040200c451190703080990001400030041c4000320000600fa0b0650380394007011b58172511091016460b6000340c21425074058104070000c2080d0b03606401a13075045051081c0180240e0321961500d64034101150941e1840c0d0024001d61503003981280c120401030000182a1506079440000030f007002011a00d81c0c900ea80610180b1046003058402c0c2c60b8010b90b50105880c04070901100141100c40600c91507102d5120b44480000700e0200c1d0049401c0d16500030400c40d551003103031810f12007a40045402240079140c401d2010401c40c05418450041d903415900c00c1d1401c0b84000d816207545040c000c003190407642d603112150b440503007040104845c0c2d0440c85004040040000b13180d281166107a075008031368100091107c0001d030013511054148030405111103260b8028544113005000c04065020012001e0051920052071100174506581c02502c542e8100d41d9444040c0c0c05030740b08600f03031900 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 553678372 1250 553677122 553677127
    0x306060111060f040303023a0606080402090603071508060f06070c090915050a09050c0a05100c050c04060609061803110603090109020303030910060807051023040605040617010b 78
    0x203d49800700d9515803043c400d040c0107080050504c840d580c1c80f10b040c00d0910311001922071481e101d40c491f0703101044110700214184000e030f003003001c024070300500940000d025000e060081507059900380100800381034014903001000c8001c103c024400c210036a9000e0040c250580c0c0880c090030310a08807000c2c40d8101030403156952901d51143d0003059001010f45003004401e003540311100c170b28080c06001e01410400400d9101307842c20400e08000350006098490143c9002c200038546902c1210f1040c0040d904000b4024640350410906000c0f2014130182d000e8031305900480c001c1c1d000511501964000e54941c0c07010300c400b024030003c2681074000500170380010006030142e0715284000315807013903100700041211a00b59012901d941c0040d40c43d52210382001110304050350462103581c0081103013070000c0c8002803809010400080780c20055200308a0a80200c42800320b5410400c1c1c01154000d058585d41c542c0c41c4001000b82c0c005001708400079007040c0748254055030b4108814142c0310300442c0b091 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 553679622 1250 553678372 553678381
    0x503060403200c0a0b030a0e060106080114030703061803121514030c180a0b0d0809060c070b0301030515060303130b0319020301090501031e0506070e0a090e010b030606011106 77
    0xc0302e01201c405070390500d216990350880320b5110b500061008014540c12070340c480c01c080c0384500a03a403040580740342c554001c1c001009542d51185445044804039030081040030078501c0030905054a60300007070045402d00b8154002c11701600d0120f02c0c134501135524100032170325014a85064a0b5011249204207424801c1446032807440c0c2e000030071a0364001e0032103c1440c20f05011a40000b240140b0003130010104081180629490240780c4410104480c0c00c05810f030965030760009030041c00092802810f01081c0c82c0440441004a840070b0001d22070265141e40c1c1d00c4c900720b583c40c001c1c10b1841130340d90030200101343c650a000040c0ca103d60312503c2643d0085060403d0102c01d500014465114000350351440c50390481035100940c080c21440c003003c00e1543c114100500700703040340d0310b90300000d030b200d000e070580898408108940c004419144c4203032080540c1000070388068081d0000542c0c0d502c1c1842c446c039000415030140c640700e0f105a09841166880d00019102c000c2c40c0151031040760814000503 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 553680872 1250 553679622 553679657
    0xc07090506060a0903110d0b07080103060c090f090f0e0a05061f180c09090c0c050601080705131107021e030c0907020703060209043c0207020a030201080403030f020c0d090503060403 80
    0x30b50b406c0b030028041c10a10300407911b0f0140100b005881c10000324050b074006209012040c0294000b1100390b00788214410324011400e900c401e060310501c03507031300d0f80c1e042080c0540700356403c2a4002038841007201c40255203400c015440d8a42601c07450000d401c0101501c08402183c8940d0703044a1030392041d843c40d00c401c1c0ca511030207007490110b4401001168100403409043d14400e03800160030995500101e00b21a21340240b6081040c0c01900166008007020410355990301d41c0d86451501c546008140561310318180f80207030182000c02913000ca542401c2e02e240c12440b001900000c01304604840b11912100240301010406841b0800103030448001030012071b900d50001e01c61100d01520000b481c004000b25100c03103140c00742c050402c7c0b02c074156612f0f0500d945592201c0c1794010001c01140342091584c001486c01083d0b03c00281802134140025007858040d07400400340b00200481550307511045c4020303d4860030031026200115022503404a10340c10300260483c4181c1d0301d526100004080300780030 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 553682122 1250 553680872 553680893
    0x40803011e05090702070e0a05060d0f14010911130504020105090d051606321603051303150608010b06031f0906150f0f021b0d02060c07090506060a0903 67
    0xa41d10801c009040004043c0c0f59000f43c5407156889a0141c4a0f82c2d0900b10030008209000c0c100c420781c18107100078042690385031300003611103540c0701d20100c201141d0380c07030400c54155485040011551800456809220500103401010b070310495007002c004481440301c40c100d41058601034002a02402603101303504181c0041401d01d40100d0480c0c002e5040c2d241074090341035a5401c00c1e00000c11301d98070145608801a003450904c5a1121627003003000d0640200c1040d0300500d28416540e4040a041d0428180100102c80c88400c065414076000758490410104055a002c0b11030003251a0210000e4896018481c42a0010000f05400c1c510340f146c00340807104e40340c0f29444401c1100f0140000944030b2a502c80c4200034151f124080480c0a40880302410498114800b80140000a05080302c03031b65000c43c2c2d540d02c926103000200001d1501b0400300e030a11074440c0f402500b00d403001654440d80c3c140055400111402ca41c800d2001c2da59080c00e00005024042070800422034200c010b20016400d88803 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 553683372 1250 553682122 553682159
    0xa0801051501082a070c06080106020d082809150204030201080a0b060c030c0c0a0b0a121d0d020627070902030c0f12100603060605040b090a0f03030815040504080301 73
    0x70780d1083d00d048100032a900c59200403c062040f0000403070008005890340c40400a2803d808d10071043d40c0741c01000303912003900b031240c04208068000001c80c0b41060744014684141848865508601c4038100c00008010750348041e9640b400034204a0742c6120b850007290140c0fa81a0b58400711a242d05404801030203007100c0c80c1d503001d60180041c42120754200017515402443c00300401c0042d44031428800183c045030450008224100800103081d80c1000e00c13200d00d103640140c00580961407800404079060005c0565129004001d0540034080d1b00103007081c041c60213110303410384002050050b4a000c48000c007201e491504403101c2041301e18400da010315409107122015a10740350080040320443e50002c48803140e039410300e02c103001400780703260715080281020341030401000c6e003008005042401144101c100c22803000a0401b00c58948200400c000d2804000007915aa03da15010707140c0710b01103841c0d403603941c0751103488513052070b00f400798038081c0d5040f0708828510f0f400c050798000350108074003 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 553684622 1250 553683372 553683391
    0xc0702040f05150f0f0324131e0201171905060d031704030c02060313120228020a180c1d060706020a031b0e010e034c0204050a080105150108 62
    0x154138680c152021f00c9103e28441944294599030500d1030990f140810000d880480003082c0303020560009030414403500342800b54240c041c40e0820151004031001c00703c0f55a00880e5418013000c1c042c1c40c0c003205413010f610f07800541080c000c50b0349610074440c046142d1240030b00060240321030300c0c082c540d01b03001441c0c10034064940301500c00b299401041040e0f000741da8000c10075400340183e10a0180040c10130029000d1403001d0000701c11040002445006840b60341d040810168400c0750440d540c501180e00181501c00c0022100c441800300d110060a1107000c0d00040703003641354126a0b003800c900451001c0c1c0d100401d10f508000441d21220001d411068000062580d110440b41009812440d0680384590030ba40754460f070100c0c0c000050525030303050031030ba0003039201003078400070f4290010203420520944441c16100740400384185030656240c0c400858502c3c4404041c00303800405800030001c2d12400e0310810b0480ea07032403580b2802c80344101c491045160400081c1d615a40c030408806800a80c0c08 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 553685872 1250 553684622 553684639
    0x204110d020c070302011d1f0309060905070509100305030f0f040302060c06011503060b092e080702070f0b18060910030501140d0b0712060e0c0702040f05150f 70
    0x84003840100e074494421242d2030791006004104540e403040c01c000304500d010340f04141c80780c1100e0104000900720036900400411048034000e065120358082c1845507080001030004c28110704080fa2903407607a000b40c0d40180c41c4032000130342c0132202107076032412690301c007009610300321900c0d501d44255048260794001c82c0d40100b10000159880700d0141a48041c04c0c80901580d514203004c0300384810f0750140a1040c942440c5c13041120109220603220300310710580d102100740e41c100c50388460000e802a20410518000814075401d95405850544106010340803110141d8480a04d20201000c5105405182008000f0140d1036038014001e0201c0440281446007400510000140300c540c40c0c0d09030380c0001e81c0e4ac9004100d221150300400312444d00903140130b050220180c07a640700c4e5000050440052115a0090000c52003042c1c2c0504028902d4842401a6042900000e0b0995104803400e9115a04261021100c1350540c030a060181804c03104040e194140b200600c503d00011050450b0b203c00c94 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 553687122 1250 553685872 553685887
    0x11707090312031415030703020103150906080601030605060612270717012307050a050903070b0301060e030d09050d1b082a060a030527030c0d1b020411 67
    0x92042c014910b40b2503100800d40100305031018000070001084901480c0465020304416240422000152902880d021401440200848003d0303101c940c4104017903032500b480000c8207500824214140c07485000c06000580740c407404c20016000341402100c8a80003480404d8460314107055802826195201425003510599407107400c0212a034044110701e030806070040440701083c0308101201080807032416415202e07082546081c5001000c1074180f29001501002d501d00507010f44041003001411101140c1c1c403001448001c2d0020321900d004a000101c600103280b03004904052030701c01c165220076900d413801d81000101500d0510698080080c44404c02564a002245074054180c0c0c03402454400b413800500c8001c14850110745032800080d070b04440d55a9903803000c0f02c1705900d0620b07020805803561103032000c4a502c5450552618002500c000c0d901c0c04010016240300350b00300b41600da40000008080d950080b105201040b0710b44203162000040c580b682c0716120442441d00181d0420382c6 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 553688372 1250 553687122 553687133
    0xf09120c041d160803180307032406270c0c06050f07140406050306010c060e0115140a030218041e050c3f0c0d0b0a06080c0117070903 59
    0x2d420464104403004980000541004100e11035440e031260890445941c5016041038590042500c07294100d0040322544006640401807e00515000300100003900403940c3d0b941d00303c1480240c2e110201b0305181002406800c4a158160b803e0f14026210501c10f00790b10071580184030f101640010f11042c500f40c0008200b6074071440d403254290840003261707418400b902805c012107520035807400130403c01060095030740c010b003500c0e0000800e00f810510b142c418078040000e801030224010300c662a20700102d8014030014071000072a0038801d000c804a007800014440192950f0002941068200202c0d403100e0140b49001903205020320014801019000c00c9200403005116090307031141d1243d10f9100303440c5080c1c1035a4a040c030b00940240d40300348001e8040c4640805085c020b4501440710608500848414803618400c142e00034035955003441c0724501004001800c3c0c82840805240c1740300441c0c14680000c0741150240c0584884441d10043c541d4180001c2d0020640010861540382c0000002c0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 553689622 1250 553688372 553688381
    0xf05100207050102032401021c0c08030408030f01060e030706050f0c01051015170601081312050a02010f0c080402120f03040306090605060301050103020f060d140412020d050f09120c04 81
    0xb072042002503600c1c20300311100ca03201000804100380790500030203800c8260381c001802c458440922040d40104401d1080c044d2080b4050320030141000d40000100000c020311000190710450b000e00b002803851740c0300c9008603094804001515010b42c4010014480070f40183c02500c2c00c5140001d04c28075014060f1009402d40d0000e8400b560300414406092000603052010016404601c2c40d080841520542d84000d22580260120f1305100300c01d070101e00c0e4125481040c02415802c41040382d000c1000c000001e25540c485c0000c0001035280c0600010300c80396034010126240016070707503c0c0040d144c2d502003001c0030b011441900290311600d00000c40b003e10500203080218001d1034005064030752410520309484005109603c00e9240000510050781d410700740ca01000b0bc01d842258840c100c106905009000f15031a1448080c1400100410010494200e9401680560981300701d90038586050710b550282d0300c000c480f104000d004121250070303da03d10500c00a2035004464001d05004040340444 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 553690872 1250 553689622 553689637
    0x71103130906031502090a030b04140a0b270d0e010215010306050a0b030c180c16110312030c090d03050403061a150f07020d0c0e07031b030e03070f051002 68
    0x150b19448104140962240b0300c0802c0300130210300394985040000000d41006860200908244485002c02d091100c00100d00c00c1c000707002c00071034940c819581024002c0704012507447c00341c810105c8181d101c204140e0241d40006031000010451003041d03075001d075041c840f451445070452003405401d56101c00342d00c0310030b40218016440040c05040c0307154408141d41e105a04c2da402580f141c4084041c6440f880c5480c182e45030815600070503a22144210b04e014401e22810400a003035023003445042c001c41c111040034008d011401c42d00700011640280d02d0303e000450f05e00c04000c0e8140445516418210740c0d001c0f01c1c500c02e00d003a9203001c1d01d903960700741140c0141d11540e8840c80402551200c42c20325448030003c5510005030342d418100c0d110458aa94811440c000340141070003058081004800140c0700003074100381440346000d107040f0030024014100080d00141d804680b200441e02280a840f847c80f121500c0409140b60010740e0b11174014009214408555621603411202c402045910252042 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 553692122 1250 553690872 553690889
    0x40b15030d030507092313110c0601090b0d0b19060902120711070807120501020d14160e090106030c14030a0b1810120302071a091801050907110313 65
    0x50404010090203081150001d201d0003802e408004000071b81c0d101a0b00c013400040b10040100f81c2c403200c050000d0b02c0412562100008046005083e2150105406060b81c0341503404200d1041614204520301011144c040d02039003ca40200329600b1080452401c0701d02d542502189199580e0390000403680a4600e004900501c2024070404070b034060302d032a100810400082c0407160034070341096101d0001c0e00c14064810300807424942046000e4040c1d803d0001c081c5010001c2d00221052064450b80c11500004c0e04a08110180300d141d002c3d800565072440701030300d5a41540e083c15000e80081031030303218520034000d840c50b00e0141c43d0b4164000794815031400401281c4240441e0602103080d442d150b192441c400e003042000707031450150a9010071519072000845098680d03083c240e06102a0746c101e05004180c400458040c0c02d2403074020030b460301050707138418025145144840f22001c030070b002e007981c0b00c1c0c1c000c400f140480d441200300310014081d403011f41e4130784441c00f00030b032b0380a4003264000c155 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 553693372 1250 553692122 553692131
    0x729032706010e06010f0921170f03040b1008060a0506040917042606070c1b032001080403020c010e01030b031006060215040507030305031b0c1005090a0803040b15030d03 75
    0x945d64007581801241d506810200503050601425001341c0d40c651070b0400072201d28204100600000c2c1c0b80318a40d040d0524403041d900c5800032808207541e4000c1301d050b03420401440224080c806005486021200b0b4200501207640300e0543d058050000909040e5006072500c200300041340950741c4905180440c1c0014035900ca203020130035107403c1580c0141d004400c01c0f0305481c01c20060b000c1600b60340b0000b240b034241d525520504d041006a0548080b854002ca00414080100b20b0407080e5007122076a9460000c0100418100448105c482241c005005030000c00b0251180d50041203840d039072000504020504076443e40210740f5000d030318146089120740340d0a042140d1034040c040b0451886d068080c4850502d0503850341a41c40806200090800c40c0000001d00760350035003920002441401c03500d00e0f907103903031400c0c00329510f80390a52513000c26464000425004100001c0303258080c0d0340981001d09503601c3e5207900008410040a886185802041090503a9014040d05460410a460019 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 553694622 1250 553693372 553693381
    0x5011a030d0302131203050f030115410409090f120305040210050705010f0203011403070e10050f030109080c0d0908060408040e06031006080729032706010e 69
    0x52411038031903140e100749481040881c018003460381880e010f070345d040c0882072030780c0c2c1841c601200c9a00c2243e400b603804440200010901c155032410404980c1040c1d03607100c0e0740314002003a480d074003100811400c0c0614903403854402007554206252905035010100c1c42c0c20300d5914024a015aa20701c0030440e11700311000045010008a4580d0304100c14061130100192714099010426545550301c1800a0003c046141410071009400c94003000789a04011b546a580d110b81c1502081000c0104910038010740901240c0b41d01c01c1045503220310301c0c0c004e0b8119a03d181c401440821220892010307055503d41c02d0300404115800d00400c0c003110700d0b000820022030050002410244140c01050064002000b80804100c42030156070594051b900948241c0d120f041c0003074944139406c0700e0322203107509041002404010114002003180c5101d4084c030b1150b03110081d02f517642c910700f0304040400003042c001b0810b020f02c9003070605401d80d0921001a402c010310050a440d10500340c6c81500600750020401 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 553695872 1250 553694622 553694629
    0xb0907020d140f070f142d01050702060a0e010608151b07021020120d0f0209031018060f0603061107020a05010e01021f020a0201060b0c0a060207030c05011a 69
    0x6054649681d664182490100f031000a154450300c54094401c00e40005214140300341d6110318091007862108586c5c03854152120009501c00b88410b1f4030400c2c1948050100c008030600039140b10b48000e6019280c10f0b80c0703075071041c0c00410803682110090765032a07602203958402000b912005208001c02540e0a15040c0e05000c070304004284d109038002d409010700001030300c84103003503000f0360150705010f9010031600f800c2c2030304000b1251140c0003922803594601c1400100d01d0003008108651041400410b15440714032099208601805030168440f40a00401c811107900c10000c001c020403803800c00070155100c980c16624480b03140301403a41d4800b0f04208010003803180c241202400c8000504000c4035400285030b009483c45113505105824050004d141e1090103000425084100c0080341180c0c5045e01e60f0003074000603203e001640c81c12001184003610710040e203024010f09001001145516980c94000c0c1d0081e0070214103011130300e00710a00060081c0100342d00a10304503000601c25282d8000c0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 553697122 1250 553695872 553695887
    0x5010f0f0b070605150d150c020708060609100509040302030d0605100512091c080414060c0a030b030c1503090c19030f0512130611030307051602040b0907020d 70
    0x141040c480403410800501d0185801d03155401c1e0410340003d500d5640d11209210701d0404410264132441442c5d40074108209101202095110440100441c00340100d05a03550840d0340140400369010350001010b528100280c1c6900c241460341004000b0768500100700964002c1d83c007100541c0010030310440c260f0151103010014001141c950b45e5041320000c01404500c0b5039804c085041c4280400540b5002003080065101c1c1c89158440118140c58000100652000c1d501190320440c00000e5403038513100000c43c2030040c1000d050840c0f8040c46400154002e0168410301a0075008019140351195210344645c1090b400f0b00114654a1810742a01c0f41441c0a41c99041d129480d0810124421450f151a603802d503544090b490b00c02c000346040461030f02030859800351444400083d0951310007018032042c001c0b25003e480b45104c260448101d680c51b4081106e0a800261f02408480400c401210040c6000360000c0d00c0062080c00030380201d000d0a000701c6d07408d00568003d40880c14840e900100 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 553698372 1250 553697122 553697129
    0xf04091a10050a05040902010c0203070603020717031b16150c0e03010527010902060403110108010b1c0b120105070201021905160b1b0a020a1e11151c05010f 69
    0x20040380307040c00c01c2c00086808560340605030084d40e4032241ca404690007100c400d0b060700e1b0020102c0d6403059403074500401940c0620750442c2c04101084942d10752030024415a0f004011110b035102048a10f00060720480c5c100400300001004203114440100d140c2e407401c00c07081c100085021950a03032100f405480d8200ea5400140203a140c0010085403205e50324103a0700300000040c01d00300300101e00904d035002d00501480030303502010000d000400c0080354140410249800e0301c070f0150700d0380e1342d2101070501e00585426101c0400130300710452804185500203104084014000901d10110700e100b00e085600c12109900580c0d400500001c05012401c00e0001090726842d196241540074088540d11f02c0c0101002044603850070301050092135100002d6174804041a1199107413000c259000f991681c005105a4600a041d207081904501101c0089141500510b503030405e0100c00c41404031108086464800382d16051100c01d9020800c088240c12042070440e01107425414900e003d04210079990 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 553699622 1250 553698372 553698391
    0x303070f020c01020a02120709021804110406171308071401150b0f0c0f0a1101091d04030c060221040b070f09060c0303022104061505010203180f04091a 67
    0x10038840071a80c0c002507450042c0c4d0b041d180c6040c0c09211f1461b00d85080c0094002d1030a40d0300100752003101480440e841101300b801124103001d0748011580407002840b85000f9480010f000780f51542c1c40505076960142c10200c0851507140c00c0c04136032103401d0550010b82e070441c0c2070703000e9030510a520343c0d00740511000300b802824251901450825104007511038403142849041001c1080d80031480107000d41d0b02c22951100665000100c8d62800c1d0103240e00e071a0308603010501030500440c07112803100142054860350141e041c11030321591000d50b0616100d4000b16500f41e020051001c0040c40c0270380c83e1500f40100703e210b00320780c1010701c0d040324007202c0106904100b000076481ca08140398081c02a000311f4440707017090710300e5031024142100039204503035940841500c2250f4003c0e080e884840614811401108100701c0341106010000c15141d2038801c0c20300580c014400441d44800540076140101c04c0107102d03042c0010300c207020806946c0200001e49042e00b008031300444017030100311803d80c8100e0381e0313 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 553700872 1250 553699622 553699633
    0xf07021005132c13020604030819030204060e012f0d080a14041b0306050403050a110d140d140708041505070815121519050f13020a0306020c0303070f02 67
    0x40c2c941d4040e00050b40000030f1200594001c00d40916400d100c820815402400d25075565840e410700c1d01c080da200c0c1d040a62901c0d169240492503500c40e10907681916466034540c045000c0c500c0c0111068a00a11120140c0b440048900d0707030b10016200b002da521081c400a4101040b044901510415004241c0021181004040042820312a000c1988541e0025100220700040d441c02600d4440e02d070001880c681c80c0c881030006058008002d4074000c451692510890b183c815015511f50140301400c0000c9000e400b6500c4405400e10050000c0e40301d000c10004800c2c0d040eaa003203030108170580c3c000340810361070001c0c0020b0007121001c01c407803200580c03001c0c4924141000d004200e6600240000f0980c4c041a14900702565007442c15031274030352074604503011035404a410b031840f03010645404480d050314080300d10401ca40780c0551480b401520b020100306603590742ca48907285040d07560481c1c0c0080300c41c4c1c0120024065201906050800c0c4005503124600110041e2403465200508002d56004 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 553702122 1250 553700872 553700909
    0x2100c1220071e0b0f1605071a0a0207020a0b0c060709080a030f0516030314011e0902030a06080303240d020f010c21050c06010e13080f0702100513 65
    0x2101c1110545540701641121204007020310664185a008004140030304500510015410b00d1011038005c413050001c4666040115074180c87c240300f4040010400f03040100110b00100c40d10090f96031201e04010098981111a4000750170000980c0040240f8880800e002544140801980d5440046820720f00b030002c1c02d09203100e030f40d120601002010020500001c0081c5881101960902d00246468004440d41450050302a041803880c0c0d01c1d400d20400f000250002414811070031806c0411040ca038180d04040ba10300181d071000b09960b02040c1c4544001900c8101003000b144204029a00c2503014101010f11040d500c0905116600c174103042c3c3c043c81c025a0340c07010b428540d0f200c2401c2c100c000c04041c1c902010311007085540e8003404000001c0346040c0d0354000740103042c0f9840200039542c1d04e80e00c6d00c0b00d0301c903107070400d9814900c2400c01c407200e18009248003000f0300c64082407070820350804c03101d40d00080004161a01c08030015002060980c0c0035412002404050710b0381205182c005a030 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 553703372 1250 553702122 553702181
    0x15050a031a0c04050d0b1b0313030c0f050d08150609010e04020d0f020c0a050c030109030807180902030c0c0d1106060f0607051504020108090a020a1502100c12 70
    0xc80320581c1411000540224000344240c0045a0080001034800c0c50160018145203180f00f40c1113680103550484030320f90100030409001100d12500d402c02c0081c0c410242d94074100c41c000301c2082c04031360b1002443c0314140441c000f013040f00e100352000e03507400b00030345800401c0b0100402d09a802c02d01800040c02101c06c50780e04203100041d5600d040c1c4005131200906c000c420080c244940301444c0c0c1320720014070381c0e950100c0854292040c60041003280c2c9061360f098241400c81c1c034070300e5001d40050075040210751010701c5a00f0440c810702c1410001441e464403240e61008070382c81602c0140d28200000b41c410300421041c00204441001401d084810043c11072949854103402012075101d03d0f0490348a0440b80d0700e8205841e5081c1d001003c543c0700c0ca400000352381c080320007540c05034049100440050480507000582600081d40a410800b00c1e41c5030480102c81141d800e4008401d50050713130344507161100c044c41a0964803405544030241c041400e0b0f2044220349464200c401d50142c1c68038200745160 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 553704622 1250 553703372 553703393
    0x100c020a03060b03010b0a0303111203011802030403020a06181205030f01092309030d0e07060c030e0a051e041109010914011115060a0f03051b0102011e15050a03 71
    0xb5040000812442881c100003401040c040071442d40c800304001c2d020081c0f650220710500b91a5030101154180c1a00003600d40850000748501c4006000714031041d8110001d036006560010300c41c0c0100d6149010781d98600040e02c8450420101d0401440504024010341c0c01d0071540d80d480c07604005145040010301e04104890500481c01150346480c03411003044a00d0000c03450241e55170341040c4690a11200c69501ca9014500c1044a40c1c200130820400c07500c0800d035441200d880b030315080982c80745980e058079210107002d11141e02c07072000800080eaa480716043e0b42504007400902c07410105c210000c120848000c2100c80032102018400d06107903980040b000300564400e940308400014400d00101c40d145001740700038016000300c150b130211000c00005031500407502110000c0d40240c641c1030500401003e44009080340e4402d0301303078012119042d03003070004800c010700c00480d550281c40f02104242c82015a035503401940d80d08102441103000034a0740180c082200d000d8241e91458503140c8821 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 553705872 1250 553704622 553704629
    0x602030f0a1b14041e09060611070608041a070201090308090c1503090106030516031709060d0510030203030309100b030606030606090a021909210c121718100c020a 72
    0x1010308880c0000c408040240e030f0050008100701e60b480583c94245c0c1050110701c0c461104028105003010031505d020b14501c103007900182c001805c03064a8404201c60700d00001e0015941801004d0381600c01c0111418030368400d010070b800124202c981441c00a101801c002c050030700070780110034441020360306d22a001000003100055141c881d04c070402040c1c01000d250740300500901c10059407002e0368804405540443e4041d030250f113aa0f4101c0c20181c406803041030340486c0d00c042c00300306030300b18102141c0c03005c0d0300418030100c10300c0d209441e0f60110b85198015039032580c603580071454a0008040d540101d6800a070140c028113190f040c83c8002c655250300103441a4420b21041002561090391541556840020f044c404001e0344443e09001d00f26030a64001e00502d5290b004001040407104440c44100c0740c1c3c44800103507a03620f007589906000d81a420115603410510300c405425400c410080c0070384c0d6110711400c2002c0c0c032a070410441c1403a5070105240c2800400108140940ea0310603064084 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 553707122 1250 553705872 553705877
    0x607180f0e090d0e1c03050c03071103102d0e0601061206230906010c0501111309020306010c150908030118230c0315030a0302211c0b010c02060301030602030f0a1b 72
    0x48252070141c7c2c1c14066501020050700c00402ca08082c000340d17081b2000707000400d03419155001e4921340c0110641d0362052891a55940d04000b8000c2c40120754002d80012915a00016143d02e02c00c0500e420004207074000c20002d20080b00c0000521002e228000c010a2460105600700c2d1007003480c06290007424509600c601004000103480740d000d00c4200545a40c000d00801001459045002c0c0d55000203007007820703510900030b01107644219842128068841611506005d030155a58802c0342801c0e1141003a20684480e002000a1004009503010701400c0e0840083c40748a100402c049541c510340011109503c489035101c081c102881540d0030000d1070214030354a5440c02600041c0c4010001d000f84c0500c90700e56841e091550125000a100280d40b20202c0c000025450f20354284c000c014006c90740c0b42e030f24450f00c8402402940b00405c415018100184005001d400040058000740c0c03003500e509800004110f00780c1561078a00350b104050101c1007220020342d018600fa9210709011140c00e = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 553708372 1250 553707122 553707169
    0x13090605070e0d0c0e27030a020105181e010e070803090301110a0f0507061b0203031608090c0139060e030a120504020406170706080c09030607180f0e090d0e 69
    0x20f80180303540d4144010030406c807040c2615212030000351b940c0d81c840b00c0e0710f42c0154a40000300d410514914002403601d982880105403844401000500311034881c0b42c00a055135841190380c0c030407141404130400a2000030080c40d203400d1200103050a4603c1d00c1c081d00b60b203503030401c01010170340e8001102c45134003889403800780d80f507024070720b46107005020a0315414003038500050001d0555500000840c85001e00c0740d1310341c45440b0030b140d0030b0703034000420b41c2c0d0850f05402c1000010155481504d00b40e0440e181520104d400c0d020310782d0710300d80140106000f501ca009a0142e6030040c02403501a03491403200000c019440c20001c42401000b110004542260b046d844102060a5650749c0e040940580442d50000200318041c40250740d44440c1d03441040d02046c100c038005100c222004041c3c44880700050701514196990100403202003020900f01034240450740d401007120710b403101e1224041d083c0b0100b051000c0c00c1040019107402c10b2064450104111403520f81380a8031f07000441c064003506078900e0701 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 553709622 1250 553708372 553708381
    0xe01080609450c181810020d0b040f090b0c070501091b1a1326010c0905040b0904110f030a2f040c1d010905180a0b0d0302070e0613090605070e0d0c0e 66
    0xe041402102080c8486d500205402481c0b58880c0d00891111f4400c0b94200038501e04007a40c3c00c15625085405020507008000041c1c0e42440c081c010f1150a00c070340c00006a80200c0d964015050342110b080304100ca88805003405000015116071115412480310b4904201d905d06000d9014882401045610541048400b4540b4101e150307040c81c1845103402404a44403000c0300800d4051144a0648203508200c410107190800c00200340c0201e401031400b01454104400f8000c01a525926490f090f1051844000116003c401170070341052400d01411450102d0f00300e030850800490150761300c51403812004100c210380040c5150309e1440304071880d507207865000d401030350068900e40c06146c20400500b01010000d8a9600561203005071103002c01244c40488103100c00d85c3d00420000b005a03110142c03c0c011503510552071542f20500400032544a4500340c440c9080d20300c0b658003211069102c3c1d051100362504035442e000054030070fa802181002d000d44600b81c00d42e071f0718428007050f20b0781000880c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 553710872 1250 553709622 553709671
    0x80a030509040f0c0309150c020309040911220f0b1309050f0a08040509090a02010516020d0f050d02012409051503070807060e01080609450c18 63
    0x2822154000c00341000a4641001302402502140c2c03002c072852134403454003504080251007100e80401e604d0780107604010701c050a100003014000000d50300704030b585a6031a1a681e5619042c0e4000c603504600308030400c4800540030130f446030b520380004130b00d050402c2c08003d515240341d0382078200100140031400381003d0030041d08014024102c010103000310200d12043c014040c001f002194415500c4104a94a44018540300c1405000081c001340c0104242049500000c2d5044642d50000306000314107811599403030360560b5035120072185a00510400c42020740c0a01c1072810400144190104041323000c0060350502d2064042c002405581e040883c0c8064010451444a10409011561201d860741c6940d99644400d200c0c1e500010440e04490801c3d521560640340070384005000700140382c035207603a21042c6e45e615102444110310401040200080b0440d52004090301021500d440440566130f880d040c07943d03540c1011701071240c45514075070948404503c140d00032250a105c254111550a00 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 553712122 1250 553710872 553710881
    0xa140c0d022106010f0302012a020d03120f0501030209161b031404031a090a03120207050a06060b0a0f0809190219090507081e040305160c0f0302030606030304080a03050904 76
    0x1110b5040c400e490000c40c41c81c1d40380501d80d055a000742c03101082c11000c198542e9600350144140c20351020304220f00001400d00950900240e4031a0030b00e4019010080c44280844400003014008140c4900c0108150304040301c000382c1014001c03007003030b01e0498813140107459142c21508040c20b0107807400301c0409051142c11100207802c800090103035116601d00307011500001d500050001c003205480071402d081c1c000204400040d80c903440e44110072a050313030340d00006e4010072400e4400303000c1d07400301d400090001d100d15005402d0303260f0210745541d2006e400510301ca503945903500a000b417060500103a04000640c0030503100e54040c040080760b12520201d408a000c1181c41070f40a481e8001c0410000c61a80100b0300c07880e480e9680b41c8159130359a00071903030049504103800d0030344402300c045804240705400038542c0d0400703241c04000c2031110350f0343c00b440ca13100d9510000a00304841000d0003186801d01801e034222008030005d5003041d0238420f440303464121018008060280000c0c0c402c645480e103800 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 553713372 1250 553712122 553712179
    0x12030a0b03031909080a050c06070602042c06030712121e08090d0c0f151b120c030501151d0d1a092d030c0a050a140c0d02 54
    0xa030303900c422010f01c050901075a04549071011889102c000b04e00c1840c0015180c030420f0304000149488511581800f0a80e8403004059601d96020040440d45202c40c83e003114070001c4070341088203840c4d0800701d81640c2240140195120340c1110340e08001242c01d146601040e1350700300d807054240b0b0101e5003040c1d80f095004d0216400081152003c00d42c40b03a00300c04280e1040010000340c400211b80500e0403a8000400030f00101a86c20036020000410305406181090086000c0e0020710300d6010f01c0a516982036100305400010105440d042c1040d40500802881030a01e00381030041b03504104200071568a809542c40401000d83c965104107045541040e08421001d0803044250f0111304018440d1000000340422000d1440081081c0c401c0005042c484031010110004e50000c44000c00b45141035001c0d00d100b007a102c01c2c00803030b40f4808140040020300348218000d020200d59841c2c5a210f58030f00300081000c60f041441c0c8100c09454402155082550403903d0356180e22010a403a00400d4a400 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 553714622 1250 553713372 553713379
    0x1020d050c0d1b020a06050d0c020a02150a170901150807050609010809030409060e160e0604060c020d020406081513030206010315150b1c020435011a0f0108070212030a0b 75
    0x110001b01c0a800c50014120b003a8505420b00092943c04000d9a0350b03400650020741022a64030109005060748002d00445001c605e000404503480490700000b00409882c080c8840c2d559440b09038801007180c0c64140280725120140506900d0980084d1660080080c02070510500c1e81c0021600d40081c411580501404941017040382c1d10360180000c594812201459403520548400801c01c0c041d820301d212105005001c903141038209601110914035a0750102d0b048006406e8107030059075140103817009407050000a180c1040d1010000e800080068800302201c042c030760030240820f41c003040382819650000580d9240d8069040410000c1680c0802c1031501001441c010840c5006c0c1c10060840024114002d1803a40340d100d060000c910a9100786003c00313056001032032580400104040d043c048040007406c00c9040388104500355110807003c2c00383c0c90460340c007852442c9804020040c00310700030728000c1c0d46840c103014069565040194000203003c00800000c019000e15000019401c3c8081e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 553715872 1250 553714622 553714639
    0x305091207050d120527010f1b03051003050a082a0c0103060b16290703060317040b18060409060308030a110c0d0c2105030601020d050c0d1b02 63
    0x18104241c0b9000078900d10800544035500c0041c05440c2809814080c024544a4040c840b8081c0702601ca10704034000000251f5480b0035040d10398000d1840b6002456613001c140e99203800c640340004040f6600100743e0194504441c6090010880c0051664080c40d401512a03542d040c05504542840c48041c43c11080c407401440e900e4149040401c0c0c4000d204400e89007440541d843e1140c0c030481d8001d02070b0801c103080d08a40400b01043c42c6001003041e00401c80c001d40200b0181b091030380c00c180e01c101c1c1d206001c652180410002c00c44009201c00e000c2446950250500d810088180070610422448a081d6840520820300a03501c030300c201d13402400266000c010f881e41d40e1402c04d00c503400884000c8825841c01413005040e10b101c10490b0103000c0000041c00103509071075000e40d000100628280c5211010320b0448940300340005441e40e42030456240d00e5204e107400e6000a00e0500c003c102d21003000028070210300c80b110000303602d50b20342d117076400e1020381150745c88200d00c1c41044100020b0b6105d07150 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 553717122 1250 553715872 553715887
    0x6020307090e090a060c03060b0a0c170c0307050d020604030f1d041a0406050d020f06160c060801081006030209070e130203070807020f03040f180902030106150e0909070603050912 79
    0x10703a130f0300010702c688414402000c54401c00c0e0100c0d9a14807800104100800c20b44207024844d48e4003568139071085a42c0c00341881e07080d28580ea20f41040100820035400040c2c3d20b4280030040241c41030181407440209852303c2e00e0303a0300a02090640c40c8010a01806e401040c0802d41c070307142042c10004015004000355000c40c03680c807d0500071560414069480c00c800401c440c1002c9401c81600754024007103d4100c0311040a21095502c0041e4803604c0340714030b03801c1000007581c0384c07404002060103039200030b425418214014241101840c01041789450000208010703200c020a4660150700d50130700c4144224488041180c5000d003006c0c22404900c00410490b095801c80c0d6842d014951560840d82c0102d01a12002c2c0d0b40c1c440c5000d482104189100200542100380c60b07207110768542040003140001055011074256042d42d00484002c603500396400c0b4440d41e2000d90200c102000329480704d26400c001c4503203038070f401c102c0c01076100705612040000c1c88200d04114a085c00e05032028213650f603c1a = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 553718372 1250 553717122 553717141
    0x20120010203150604030503181f02011506030b0a090e03070605010312020706020a1121030a09091b050d05060102010e071e0b0306010e12070f031a1305060406020307090e 75
    0x70403114a110040c010a03e1551810201c050f602501d902c02c00035842c03d107055440d81c1240c9a0300300b6050b800030144c4a44c1400b10002c650380c40804420b50004201190840700d400044445030f080141050710340840c084099031050054002c42d5910400020180c5102001d2420341c841c800700074107c2408c2000000070030442521081c080300241d03090b940c045850700400c1782c5400740900041c01c0c0701c1346110741000b5407414a102440342c8210070407000110b801c0300403d45c1580c001042000c042140301070700300071703039082070203481006405c0022313014000c24901b001034103502501418240c1140e50fa0700150042c1d000b5070000051504030b90441e200c3c165100417020495200c1880541c641800d604002030b0b14200c48141d034000ea005840d40c04c6003a00c00070900045004001144a41d0322840300c00158207a40c4d001c4200241d401102844500c050100c12003c0150b4041c3c003140a600b001c0507079102250340460001c1d001a0301c07181c0580c0d607440304070b4100c480941c5e58008507080984003050069010 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 553719622 1250 553718372 553718377
    0x204031a010e100915050a030b0901060603020901020d120b0a030f051510031202150c1e070b0103261b061e01092d020901080c1804090201200102 64
    0x11030300c0d944955140c0c0c80b8040b5908202090300c25908180d4120000c0c4a503248507005040980140128446416914800150300c0001903106840058010382400784030701083c0583c001030006c1c2d06041d0315001d002c000003942c0e200401d5100c1c007017120480f03869228801d940c202c0d6401c84401000d07261030740d849040c0031807024807959080301c440c03003032118400c400c10782c014003d481799880713100c549185444e40c6c03122a4a40c00e2110b00c070003140074070604482c1241c0e20103001805000000c181d5911100c181d01c14031301e40030100c10310082d212001c1c0071034000182140d1042d030660b0f600440d58032240c000800c0e5484e0100034401032103020f00001c0392a112a01800c0400c050410401e02200d107035803070309075032400d201001403286080e6081460052003580c9482d0401d401d00035292150003042c00402c6401106d030100010102c03a0300c0d4001071308900d19a4415800c98202d00071a203030916000074900c1002240c1c0d8422900c900558941a40300d09580c043d0722138481182c00d460344000003902d1400c0c014000d5 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 553720872 1250 553719622 553719653
    0x5181c030f0608060f18030f1c050a0e16180c0504080a0b06090a0516110a050703120f09080327090a0501081b0102061f03080a231813020d020403 64
    0x40300701000554040d010906e0340d04c500c203c0300c0550314180d00d540390320180d40d021404c05440c6480d11030b01800c4002161050074801c0102003400960a44600b440904020b000c5d000c0407a054101a000d000c0e1803038030414103040c00d075005400210619015400e43d21801950300526042c051010350200340000078811034800c10045400b10381c0f5079a002038502c1160019902c40d200d10681c1c0201c4064640201030860b5020420412030303a28484030790390305251210a80084418189c00d68124014a0b00300c00264208409814200ea0290800380456924000d60840341184a01f100c115140b40ba07401214050340d4101415424003841d0080300c4401520702880b4800303091142181c0d11754100300e1714040101c44141640134001c6500c800340034070685542c0000d071754009203a0306000000107000d84010002040140c0350032001c0e034107044070302000e10303108184402140420030011208103441300d034041643c2c07011204071501007540e116032383c000d00407203003204d0446100082c04421f2100003420121171 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 553722122 1250 553720872 553720891
    0x21003050f010927020a05120106210f0b1b0409091b060905090a020d020a08160c0f0b0403021e0106080123040f150c0509030105181c030f060806 64
    0x2642d8a0f50341c101211400044001030441d4a414403001004a8105040d030074001444004d0a41c0c4440c005940c0001d4801405407607950f41c40108402c0082c1c401885d00b00c85001c2e1034440390f91242e00c0f11080f00b1000e0700300402840b0341400040d031950b02150421f040210706850143ca59855071003003001030001c42c4d0292500754050714401e206201c5400c1c2d480070346089503a0030350b0b0340740741205001c02d003000a004044195024070905911010701d00c0a0100c1000c0d9585050302e070700740b4444061400d1001c1c1042020406042050310109402207245542281c0c00b502007507803a038171400c0032828030405003207200726451030a502541c80d240c1504504c0036101c00310020006806078544d6624000171102070000c0c0082407100140102e6928442c02c0c0c2c0079030062411840003900b032b11030b4030101d0780c41c2002c440c04038602050b880c0c1709007000d00c1400c0d480360b000b00403003454840074110b80748d40b102840c244000d641401407803a084d0500c40d41000e40d0755000034100b48840381d200e0030010b8030785504503692031070b = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 553723372 1250 553722122 553722151
    0x117010f020d0509300c03040e040c0314010501080303040f030203071208010801110316030207020117010906090c02010b0d29100911160201122306150f220302100305 73
    0xc0b00f485417940a00390582420120016070007a40003441580126413005050300007070000152506039034800358030861142080c6000a03045103860740c1040844c800414243c3e2400b8010320007820000b04890700030790041d408032190b0b491403030b00301d141d0b2250103401091191040e0401d908183c100078518140c03000d0700001d00c20510144000551030004440701c00302c030300c044650280d000d40250300810704940103140c09030800148111011280f4400c0c0d02c0003200079610700c8100290407281c0b141c0d44040d00030b07200a2003a45819400100702c1007042e10060319070003102d4203104408500d940d80240d01140712b102c1d00c2441c03400540b0715225143c54810f010446003401a54012400408110b41100d0503040a01d4503d000035001141c3c070030f190340b80d69005541d40d45000024401100001401c04440398006805c0b450048284040030643c01281d601c181814004022103c611800703407001c2c18a80c214413280034501c26401803800645600c00313500541018400340c85079915400092241409020001 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 553724622 1250 553723372 553723393
    0xc0405070309110906030a05030406020a060b01030e030306091f09151406030c070602042706090b0609042304080d0606140a0f02070906080a03140702090117010f020d0509 75
    0x2002e0307400b40d00c8010081641c0002454442c0340040350300c0c0e00807001404607004200680d0b2050701d1588160880c03c007503031260881c0800c1200d240036000740b0a20078a400c2c00314800e5602c0c1140e407408050400c0348170f600548001000c0740003460000d50100850119265081d9440f0b401c5001424031090020144110b5074002c10030102e2150840e100d5400076100900e5039403001c14041581c0c02c1400100d03003440d002c10001403010940d504420a0031501400c0d2030060a14001510448289900001116040112082081d80d44a0640c0c00144040e9004141908024021000c4189204401e180c81c04140e040c4418400040c2c040c14540c882d80e0810450306440d042d0a0384d854141040303d1000990405c40c0c241c02912807025008041c0c0c40e401140d003d55101c1d80323500d0070356140b500140345941c02060728400f13140e44040003108100c500020320b40b81000701c0c0c010804201050290200c085030329440c1440c1c0d400251300210030307005102001c540307986a2030300c02800341030f090f603522800d03100b00350202 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 553725872 1250 553724622 553724627
    0xf03030809010903090b030901240501020609010c02030d0e0f070f05090708062b0213020d0b010e1f09030c12031d240d05010f151e12020409020c0c040507 68
    0x10160103801d600e17518441403a207040340c0c1ca658801880c00d50b0329500d810410b07880d048402031044514081c0082e8141460074180020328018004003010282da050403503801710a0380100c04c842c045110301038040b643c07120ac040c41d02e145c5002e01440110303d11450300001414909004c2c03100a0300c03021a41e807062510782d0201110100010b44945a010940e40684500c501c0014204840500d01924240d241212500003549044000c2e0644204030340008880340902600d01c5003400a070b20034248460820500c0d804075610146583c940ca1240800c62403107883c40340500701c030358015079000d0000040385445281c88041d90106000441c08100fa04000100000c80441405403d86000d025094401c07014802c0d801d83e80c0000c0001c2c414454108028a001d18450103114060b00d86020050b452900c1d108200c484100410500400c010180303080201020100d2000780d0848418038050f60700f040d8007500d210092046901c1003501d43e10002c2c51000034034020500d000e07010310468041190342d5500300c05 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 553727122 1250 553725872 553725881
    0x3010b0706060f032f03012409060806040611120c0901030b060f16021f0804020306010b03060102060a020904021324030e120f0c010c081f030b0604180803010f0303080901 75
    0x148904c0f1500005c03030740d00000c40101450210641c01c03560044840f03001003421541c10101c4c481c1e100391204024038045100901400c001c002c200c81c100074092400c641c2c5a11070402600041481e503ca080e81e50280312030300c0c1500c0707500c1d4411303681c000c2c80d040c982d58032640f59104289441c0400c1c2002c2c0510864600300c2c0950315a550b0442080d8a0101c90100b09048000b51204c100d0303014005a0300e002d040b0548000e8510070803019190041241080d00401d860504143d2003082c181c0070070020400942d0b404074100b071700241c3d00380002d44c46991840c001f5000c0e01902d9819000b14080b040000307030000201a00b80c41c9140b004c1c0420303d22841c1c280084081d00d040c0b03024000c465002e92210f44600f20904010030110304400c91541c1441078088983d400d640d1584400c13000901444113100003a48404800790040c81e04044449941d4510b17170342c49001c000b000385450310803990340b02142c209c04e80d940c10079140381c0d0303001c4902d9540750303122459420f42403000d020907030009071548005986140c05204 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 553728372 1250 553727122 553727129
    0x1b2505060d021e0a030609141e0414060a020307030b040605061c09060533030c0d0813170f0a1e030507060905071d0411060904090803010b0706060f 65
    0x6940c035084110715110065444040d550008034498400000d0000c442400b0303050703032132255030040f1300103140480b4a0140c0c0c0340c1c0c24081c445000c245080c13212203014003075144002c28260506260664803130520b0500c0c81c2600760503103294000c040030401c092800754011445050141c504001c40d01248003400100c501034040c6540140041001d840700c040000d190000e0703498016004140082203a55088c2a21029038510a035020701042000d03185015a0071500c000d207488007070140d1040784400090f03070380d108a82640d019480820f041024400c6c8201160151020030f6055258071784e03540c070600c0b4040f022030140d9510340680c0c02e480712240b9011804005154005940c000c0b40d81d108020b114500950310b90890600000f00000d10014802d0300a221a140c01180609940384c40c025000c480030134124255803824408104000c000352060081b00411441624203545481c0c1410105000703240c841005000c818000c400081d203a4000300085c520640302e600284115035036120844170002c594007 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 553729622 1250 553728372 553728379
    0x303190519023c01020403200d08120c04150206010e010614030a020c0c100e030105060901080607080411040e0109120f02070b0c101a1914010509061b2505 68
    0xf8035160b0f91101880c065000000300209810383c20300e980c00490899000c3e5000721107404030030410b00840c1e01e600407451010b81040da01070b01e070200c8a82e20300f00c0c948100c1c0080c101003605000420404c1f00c10005440240026480f810300c001ca0035280a56500b600340300303100948074000c002040c80c1e4840c034010100741e202030401c50700f1611a410000301a400c000014501e92007200042c82095440101000c0082c1d1161a0040010140c2041c51300f035500c01003e4074041d00412004118445002a056501210501d03201580d61164070700040300450041d0803c0d03001c3e0600d120141c0c00c0106511800040d88540d03010036880313600701c030155a810740c0c0030701100158005c00c0082184080c03040041c107011900d10150380c00c01e8040f40030a42200d111401c070840d00c0c00d04c0001095a401c00121028130844030740582081280b41201d21001c3c1c1c0c40400c1011304009000c00c000302d49807511340a4a0070402c40c920030295141243c0f02c0b0584c2c48141050050241300202090b880724002d09001509a401c080d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 553730872 1250 553729622 553729663
    0x3130c05240d11120106021b010c030e0a0314030a03050901150501080405120304060b0108100e01140a05130c02100b10050702010203120106081803160f02030319051902 74
    0x20248000d254204072884090350b602d80c1d401049105100f0000c1030301d2480c51010100d40e50500100030b103488190668691552150000360f00d20360b804c04110f080c1e2652504d88829134030070380404181c2030701840d440180350000b00015000001c90101c09426454081d40d0100001e03070b80e0025071070030782d0b14141038482e1250640900380103a5124440303040e8024003510032100c01d24207664920320a944201c0c0d041e90540d0b9541000c1840c4d690050403079400000c41c4542c074141c2810040420780ca060107101340342c0d9a0982c052003440d00d40f00c0c00e8040d401808010302d101e940d4520402c8610280c44180346150040c095440d030301d1140842440b40e040c40010140410040194004003a00da540c441c0f6401ea05520050010a02c0c03a844003003028060b1025959410849c200801d019882018190400816400034020f010044440040124440d0717000451030003800b02a0012a0540c41545259a401000d0210004640d90044001d020701d44000b0b210312071070a20980226280c1120000e42c180341c0c500b1 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 553732122 1250 553730872 553730929
    0x211005060703110a03031506230c07090905010b01090f0b04142d0307270c0903050d030203190603030f1d030d09030204051005090c070305040b03130c05 67
    0x10015000703441c4641818004001c02407401032818940d03c004900290b01c66000040104101303140800030f0155080c0083d04c915020754100c4224401144140781c0000810b07020f544030000c10403c401412403890800107035a980c00c00030f020300f9103100d481e8041208800001001c401808520049410b504e00c0300303050500b408810050f20520282c0a81e000340104005220041c050700364991982c0c51382c41c0e0806540304502454204441e45d40080c1401e0f198418000202c1c120f429010b0310356400e0340c4001002e1301040000d032400780c0315401c068060710400b12b02c03461158160340111b004031302140c6007400e088a03940445055031240d0000400203010403890314403c0d80660840801e01048015140c0c2081034140802e1810340d07840c006800180880c2401c1041d03041500c9800d0300030b051802030300609828640400e05040340a0b15880c80d80c40700060a2042c5031040080d01c001c3c01d06010301d5540c80c200b031021910807005014090324050449000000c1c0d03440c0403007102c0b01c02218281580710500c1c2 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 553733372 1250 553732122 553732129
    0x30518031c11070e01081e0c0d030e0310380f011b060f060e1305420411010207050f0111120301030f0b070c051507050d0908211005 58
    0x5008018500320b01c558000821503041140045000e003070840000c1c610500802c00c02e21900787c1e24081c000103078000c81030600d0329803551407900b0151a0582020300b402d00900f0040b82c9070056664205d5045440c1181c1d0700e105400c01140f1034100d9841081581c481440700045003140705030b2424650b0302410328a81704103a9409840841c80201800074041c076000b4685e100c40081d070f0a018030600c20155100340a00105407142c0741d00d5001200e440900c000b05085664050360740c1100b104c0d401150340d510382e4201c99540303003108070000d03544440d2100c10781f0010314200350f410200580d8111440b11038880490000c0d440000c400e42185c00040034000c290300c007180103441c9003550240c0d5030f20301d00484000c81d04c1501c103d8001c41c000c51050716018070701806404d2502007400094000c00c1040003221901e4045140001c0c031001c8225817800303072503154462500031b503141e103c0c281c0368269480c280041c0a060112500180c200e10b403030b01c0140c0146480c895403035450100119502540c51640c03c0b002d100a05 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 553734622 1250 553733372 553733387
    0x3060106020d080406051f3b040f0f0812160f020c01030f0204211412030402060f0405040903020f1605061806040b03130c0e04110d1b03030518031c 65
    0x135404a0482d40c1c00400c0f87c0051403203250007034405882c8500a001c001e5401d03104000d0120076012007014041c1c21400221400c410141014054103c155030f01014030041d80300c1d2200c415407080c1010b555443e0080c95600c8030104940502d00e4010800b48802068040c050b6050f802d05035034054603200d40c0c0e40c0f00540081c140c001e0f9260f90742d50300784030104200c008a29101c4034032030300c0300c0c5040c00115146000c80c8202c519034081c4c4e181c0c0e0441502c0e1000700328402c0989030815070469085444410001000d0003600640d4411030744141043d0b034050034140c0104240f8a020141c01c20303601d0454041400d1107101c12036200781608002d0402246090f080e2040c41849101c1707000300324038601a60f4440e031140a800c00d440998110106031030030810802a04400c5004004012090489107801e454182d0b914a107000103038000c0f07001981700301c1000201e82c000302038000c5100350130100503201e04008140d50070150302001c24072001c800f00061841c000450a558200c42c444042d0707a0107992a0071100e06 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 553735872 1250 553734622 553734631
    0x302012c09100315020c030a030c1209030806030d0314150d0c410913080c0313091a010e0d02030601060c020109090510230603070c05010b150d020a110f030903060106020d08040605 79
    0xbc80300d0a100040407402d4050401868042d41e208001401d042e010507062800b0f034010380c401d046c50004804030b24150000311030f90100307549215035a000c919001041d002c074443d810003080a41820b41c045003c0045942e804000d0950a01c2003032800ca0750f540303c030885042e8030f1b800b41d000c19149000c80c6d02840d00402140e8402d4041181070b42c6404955940340690300100681502904089071100000340c43d0004103000341740c44e0106210407951401002d010401c040b882c0c504210340349881e240b080d21052500425198060108d40c45983c0d1000b0003001140072080803070008400d0440081c20040c00e0107002e0048242c140a030348194034085040d02c0d030358050840f8280b8002202503207001c83c0e40d806c02a512681441d220103a00d01441d1500c2400c64042da4082c0348200310001c1c000307100407804070a44507214280c0800503590600c082040e00c50b0003201c12601c0561141041e44e40c2c140c8004001360256410039000c030b400c41c5c0d88450050780c541200e94404800202100c002601140150300040d421 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 553737122 1250 553735872 553735877
    0xf0f01090c020c0a0f030b0f1b181002010b01030b061905030402011101151706071d0301180f0b10030b0402210609070305160302012c09100315020c030a030c 69
    0x22410200440c80700c010765800ba0160b110300007800c2041c03280114510340d2081c82c040d0030718040c3c60214107032000d0302c8102701071040e50780c0301141c104600ca6034400b050750f40d0030b002807082c5144200c000700203020300b10820459001a090090400703443c1032003000d641180d06507090760130b001803803003804480f1a00020300a030704000c01c8400c80070f28a0402c0c4203405440e4580750b00c01e0030301410682c20070382882031901504400d81c054020401303910b611803001c01010301442c480600c0e41400c0000207000d000045226404082c00d110050104440c0d200309440302842110005450760b0350301900541460340d444060502400f181c000360051400c0d40c01245240f54603c03082c50720010b100e8199142090445101802d40d000000500030300034200600ca0207041c0b10218540264250340c0001d140c6103254000104900640004581181d04141090070701c02001d0050701044c980f0701e224542c2e4804a20041d685c4201e0340c5d1007101754503174070700868204d44078807001149800000a4228010b1804560b540c04 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 553738372 1250 553737122 553737133
    0x9010f0c050405060f091804020337240906060b120103030e0a09020408010e0601090b061606060504020a0c0b01091103060d0203010f020c03070303050603160b0f0c07031203050f0f01090c02 83
    0x3e039645980d034581801f4022400040545060700c14103290110001c0f2101318100045081003108501c0c645820240c0907d1210644a10306032411030402c01c0782e544502129202c0001c504002c884c2030740a0701c0c10078040c0405000340380d80d900e8014068441c8440b008000300441c001400400d0040c8440b071101e0002501600045607035110190403030b00950000c407010f035119451011080001c0010ba40500185a000c0149900c6840003c6c65442010200070854103c845420b05000140e03111030700074200030b841955604203541c40107060501402044528112010011900301001e1046854600365a10220304c0c43c2c032682c08002e40c08100704c0040ba8190748944c448004006240042d0a03c400039034011a110b0b40940b41c098152000209024003035804207040a14100700352501e88121124607200591b130b01d809031450703030192050b100d54060900c14110000100034900744007030100c1c81247e80400560300c07034001c810b018074010349040e41c100e01200e0040c01401800d510814445800c2e004488 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 553739622 1250 553738372 553738387
    0x18060f010c211205040c2706060f0e1206190f110306011206060e0607020f0406030804050a0603020702150307090f030c09110304021f021603060509010b01020d17040305070b04050609010f0c050405060f 88
    0x10341c0c1489c1c10400005000418000300c00d40c215072030440c244011a91000424410303902650303145401016403000300700036043c18441001c26400300c1100d02e2041d50620561400a50071030b1964404d0f03c1541c000355904640341040003c51088409a03800380d42c4900c9411400d008209407508460001d0760302c064841c2441c0502c0d6074910440005501c143c0c90552200d24180403c84c405200790b112805050040203068010307960707040b90300c00c04007900750419102c0e15202412121368005400100320304c100580c1c0031040c8451f20140c40c00300c8590980c00d001c0c07520703410038000300c40c04155402500000d941514140b03415410b0100441a0824412281c6980c080711f402c1071010302d190b1041d24066614000e001c2844001e000310a41a007080c0010040042c00510040c80c12903040b0241145509000120381003501c208111203180b50800e015a4040c10241810754803490142c80358480c0c4d601c0d0400b0003054041c1c030f002d405102c102d1903e0710740c20645401c0a01002c1d0380003030150442400c0c00c00100c0d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 553740872 1250 553739622 553739699
    0x302040e0a0c090603112a07030305070507090912030f022b0b010203090108010b07030311030903180a050a0603020f0702030a0311070518060f010c211205040c 70
    0x10720400000d4804181c0c606a4903018021051581202c410503080440310300c40c80382070400700c6035600540300c42c6083c040e440b02e0750541101070031440b00282d4024200000241a40300f0060421240184140d440080c3c0e10000b040480b4441c00d4001c201f80840c121400074135000c0e40c0b2440107c08590009407605200150303013030712601c561008100c400d08008204015141610600d040b00700d0070700045280c4005400047c014600510a00799101c20002d503907010544680c1101c1015040b802cac042d5180d080c603004803900d980205030501c042d4a2420091521454030051840c00c4800c080d01c030411700750401c00d04034082d500080c58880d07003400400c450401038508129140701c45010b6618040c000c815464040e040624541c8405e100d6107080360102c440b481c2100d90b0a0f04160201c0d280b80245500c0c6006842000614201030301041c01108400c03000704100030b00d0f034040c074a540c0c0c440520811802c48002203500c161000b0f48100321406050044209407070400d00c041c6030003c0e200c14030312140c0989 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 553742122 1250 553740872 553740899
    0x6030a0e010c3204150c020a120b06040923010612050a0b010602030a120b010201090b091b03060c030609042102030a030b01050c0a0215130807330c0201030204 70
    0x2180021403c00101c1120940551850b003032035400030341c0e9244000d011411580c03d014074018104081095a00c560740c89001c0e40d00d050718107501074282111590b50700a404015500000c064802e4482d40002899a1070035208100b002540302c80030400501c0f603181ca50310b4440910031590070540d03030f811010803501d100300d06285404d841030700200590341d480d241c10720035184180d0140081d50320501c4942e80181d089031020b20824910b0344001244284940100d025105050001d0300e0403c0c04030038071610710000706504003507801800350340340d05031654003c8c10f6689004840240702c12a0a002084051500d4071000d034002d1301985c2c0f01d0000c03103c44001c011400100d0b8201c8005a0b000151034402d8503090301410f1401c02c401d0800500b4007400b807400725103400c1c81100080c8240c4d02081c00400e80e80081007510703031000c4401c41c0c0c00b1b030454658000c1030b610007007405000007843d081000c0d00c5014800d016045401491440000c02040c1c030001c00b1707107105905a1049040c16001c0c8400f10704000102203 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 553743372 1250 553742122 553742141
    0x30d110d0c08090703020d0c050603070306090c050a0503010b1b03030708010e0f0106050d1e14040c12150b1f020d1106070f0e03070503151008150606030a0e01 70
    0x40590355412000c69200c1210030010389a424050101c0401c04401c2e00031810004480c2c040c0e6a07103007450614078040c0c4201010307410840e0700c400040140705029034190f00180540b9415002004102d03002041030381c0034009c0101c4100043c0003000144840003252029180000e0b124010101603040d6103071072429a00f08540c120001400300004004115a0b41c1d0f580c1d03000403206941607101d50600000819a214901407000410b8075040e10928081c0c5214074111342c00c500c00e504104c100314001e01440c00d88000c0e241510324203000e84020600c100d2016210456551211210909080301d0700c811001d8140045400d078054a003005c0580469007030b40181010342d24a40c003504008c007880401030301840400c01160720f158000d004012036240c10084008000d992420454a88000301001a140501e581c0242d074040c000c5003840e0340440199814075006000d058410741e481502d405203203548644d00d1405440d812022000304200d800e00c00d00035500804418000b082c4203100b0034115095644182 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 553744622 1250 553743372 553743401
    0x1b0d0b01060c06050a021603051303050d0314090c030a0b04030c0b0c04061d0f010e030c0a06031514130c0e18010501031406150901020a0606060203070c060c15020c030d 74
    0xb903410811820b03118003540030480b900708500300b0b1458040c010070003e031801c004003400000a060140da40c65801d21900a550213400c130346440615940080160120b08121100100c210b004521050000701d1110201d42c005001060915059291480601009032041c2e060000c816141c001051503411814869841d07010300c2e551391841d201005101e100b2001c000340800b45903011102440d52110030b0042c1c0f21400740307031800c403900c42c40c00024188403014120590000b0f96100014286826400002050062003460000c0399940c608106038040d203420040c0d0700106080311000e004810b80d101c034800034254075020845456010110b58803005132608040c051814100400482da8140141a0b1032140f80c100c400445c2003400218401d00610b0280102d2a0808500075016034401c010400b81150800030a000c256552580170b5241c0c1d01c50441619440c9011101103003c1d80145ca0034032031700d030340303c01c4428040d040746148100a42051b500c0e1105400b0800081c00701c045d480c003403000c80d040c440 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 553745872 1250 553744622 553744637
    0x925020d09090b1302031b0c07051207030302070608190903020a230c060309031c0917030103261309060e060307050d12050d1a01090906081b0d0b0106 66
    0x11401030300c120800e902c12560142000c28420700d5482d1014103040b000c48804025860303440e04001e0180100c44403020225040001c06c2d41c01914a0025140044031000d90304074a0040b8400c03c01500e03101d1a00010b005a40f226100308070281c810620700da071011007005034494042c0240122401d503071305058154016030200d0050428000060f6078440c02e2a0601c20003140c0001111049445e00000f144031445403402000083c15500c2c24412101c1150741d01c1c40c3e5a140c1d4404054003001090300303d40c103a030031180040080c0303100d1001c1c204070b038140c0c0d030005200034a00714015000d964882e0181d00c46c00440c8402e00000451054600f1001c001d401c0104c8045001c600f404080001e24074010b040038800c0e03003c02e804122a4645042100c041d40d0810b2045000c3c48000000381d40520407403c0090b1000e10303055035a89003054001e600182d9400c26605d0700e000d02d079a500c0c081d0a480d00c0340624240c81c0c002d407143e02c040002c10314130240301a0010b080030740c804040f900d400c4c03141d45003603001c0000719440 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 553747122 1250 553745872 553745893
    0x120a050c07080f0a140a021f030b0906010801141f0302040e1b0703080c040803030c090306091c1808100204081002070c061d1201150807030b06092502 66
    0x24041c40c070161000400a003a018015600c1d542e50313026803030019040040c08031a44d940014148500603003070b500a000200151150600000c00306a240000d000103860400002c001d445d0401c8400c0c041c04051b901c0e070409900f04540044032905141017254014100c503440f41d2808044511b850302c00d070058400585076841c01c0780280c011400145884084502820052044c194480550383d070950503280c5001c00d5600e11803449560321881e04254068400801046a141001c0b00101a06d09058060f01cae259151007a039a540c03018400308070780c03041103510390f41030149215034001c032400704418054104a035900c0302d81c0c9042030054940c2c01b900d40e40015003030001e14410021500501c0045d1811844d001854035005070409040c0540e208100c102c5040c5c1090008800e023a0041c054010300d4501081d50f550070f850300800107001032010301c1794a40c0380000c607840c02040d00011070ba0040541c04240d0365003810020350b200028082e804101c44e4402c40621490700342c2c4400b26810300c91300240300c03a046 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 553748372 1250 553747122 553747147
    0xf0f23121e01200909010308090114070501020d0b010519050903030f07060911031609020304020406051306050108060a0320030106080613050114090a020d03020c28080d0c1103120a05 80
    0x211000f0161200c0c420040300d001d640741c034250303d411250019116500c0b1031200d001203440a00f4008080703404940464020103104042d4004c06500071140c0302040106030004c01502d25019107915134020507103000241d07552500480c014591100001d050300e20300a41140703401c42e00c0e00700d60010340e4410750b00c000700000c1049009400400d03440890061800d03100c41c0c2c101c070841e4007440c021844032640200204d421902c1d00c0d0000d07005007e00800d00200c441c00ca00007100104a6442503a00042c1008003003011420040300e42c0003a0b039080484048043ca039103646a9420320320030300d103a41540d070302c600000b03c0c50020f00c41e070b0307014800b5516072205c040e0141c18660b0940b0a8802d8540d1682294014010301c2000010701c90940d030303815a41407029131064101a4148203910440c10341201e0a514099800e88080010100c665100f60881c000d840c1c8846005030f0301d001d01521380d4041024008039401044014200c00c3d0030071002401c440f000003040b4000042c0390441e0322500e01107100829015100e61 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 553749622 1250 553748372 553748411
    0x7062c100f0504020319020f040e1c0e2b050703200906090610090f0f080f010c0c03180b040306020714160522060f0f23121e01 56
    0x19541c1050000303041030b0700000d07224545104d000c016400440803000031034603225a0704940d810b0040003005043d0400e881191212400070300d94070300d1140c4d03c44e0540e5460007410720700507000028080d411800002c0001001200415030055513007400038181200240d01080360001561003403800004200115902d101ca994144202034441d0341440b00700700f006c0d1150f480d455480002103c3c80b42a5605c480c5060382c545809810030781c44551030020116080003400d80260445a0a02c11140f503454495025403c03160b82c400e90307130f0029100d13101c48000300380f092048251101e00055101082030f5104400612503025520482e40d640d000b1552100b0301c42c0e81e01405120508a0000e803512000030200c50480d071800780209071040900f01042d444041c4041048208083c903145e040203141d888440c07406103003e0354411900d08030380504001c43c0302d2500c0010341812040264940000380d00100c00c0008003e004403210015110b821941610742d601e040000c03442008a41c000940101800b07048101d21 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 553750872 1250 553749622 553749641
    0x1306020705031002041505090609040c02070501020c01050304080f07080d05010e070318020a0603111219050c0a02100b04140711060601020a1e0203010e15090d08060607062c10 77
    0xe0380b0600c81081003400729000501031110a11f02560741c0d00384e03800002c05c02d01503030400301e40080c03030040b4480c41580c0003d250820749109808451006801d000112854803044600030803284c0f051110000e004290070140c61070520800d107c0e41001c4500468404540d0f00341e014005040c41a81803008413038062050040c29080f41c86264200c10719a0081820300d40d00344070300c40c10150303030b001403803810007c000075600d484070340c060a118581800c0c6110003001d09004140c0420a280c440411000c00b62141155010b50300784c0c0281103c0b034113220350030005100034a00e05801c41d880740c00c5402862009840c06100c1c41140e121070340c65190364210740303103041d100401150547d4030104004000c611084500d071286014914441d40c10070151010a01500741c007540200070b44503002200c1020400300c5142c5100303040d10022100e078a4050741007103508010640310030381c1141003040302e0b0000c590603070001101002080759000c00f82c0030100d03403a440109070040c0340c195034201420060000d1a94010501c18 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 553752122 1250 553750872 553750903
    0x60f0a0c1403060906010909020d09020f030106050d1209090f0917030603030d153f0b0a090302012018030c01201906020a021c2003130602070503 64
    0x1500402078400718510018080d0f5100e940d0300320000303195a1049500704040d0020704015510303040ea0326560000381000004c1284100c50f2400f8100203824148100000c03104010f12541146803a52180401540510b208030200240c0e05804035840b40580640c5440311100240000c1300040307070070452603190302c8150518404504106016040d900001038850100c83d1000c00242c0007014050b0f40110b192591004007000081c0c10345001281420551601400e80c0e00380703140d01542008010000c0e80782d50000100420540004205c0c982d00c5580040402e6219000000d5030074039981100184048c2c28030b20070350f05803001518510503061880c03100031410054004003500040c0c0070010704800e20100107400303850003180300710b03586c100d00f007040000006544e018050001e6403030825901035485407210402502c21304684016400d0110504600c0390b100c2d95844d07054604005600748084495643c1c1c075000c0c07209100700905481c41112003001010190002c0c14198980b1081c0f50034443c040040916 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 553753372 1250 553752122 553752137
    0x1501061e090806011505120109201303031b061b120608101817031008061b220b13050303030106050f091809070302150f0702040903050705060f0a0c 65
    0x402d520009040781961000c030144070b58000d520b41c1c102c541c1c0c0141e51011042c2ca52450000504600650124140101501660101c13041400032202d0354891401c0c40b0341034280243c4204080303407042104494000751801d03841d8010313049444820507944807098800072058005000340d1980e1300300000c26844208034100388032a07450600c4454840480c05554140c0d01d40715040c03002c813902000b40c001c2481c3e52080e400020545045000481a0000c4682c880a00c0328070340081590180002d03070a1003501020742c401d000301702d0600c0040e919081000b00540e400d54000400e407070002c001501d000901003c1007000c0c4c0703840d01c1e040e81620090196103c14065002040180001503000080707840c1129442e00c103665480074a8007040301c5201d20900c84910103070369010300c140380d440403c10008880c004c4a51852071a07114503640410310407a650220f5010040080c0401401e20b1380099200c58024100b203410090951120790401408840a005400c180703010041c2141a5201d4030300700302d04a241c00034 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 553754622 1250 553753372 553753379
    0x10c0801140118030f1419020a0b0301050d020409230102070b0601030e1218041b0206060405012102040612050d11030702010503010603150b0c2d0307141501061e09 72
    0x300f00c50580d000c003521581544410700d0a000c070741e111244070140c08104540d9000c1c000b440a144498040608030b2280c800c071a0001852420ba85c00d40b4180c1d44c1c000c154602c1110030380d00304401040c9021080700d0f002e140c8108402a104600395145800312000c001690729903541c6058000c00c80020a124185403500c80b00c4012914000340701c989504803540e12aa50355900d0802c0000c00c5040c103283c179802420000c6100380e010034001c00d60440c1081c1d80890b24161075003010482034034024010402c0c9245400d151800d41d128224071303074501d54000f07440021040d071550728200c403400d402d001c10f4805070f01c20100304141c81c1e801030f40b030003002c004940074504014680d40000c182d444184104000c140e12441c41c40d0900c841d02d04c03800000c003c004c0d800c0d592820303554880d80d1182c446061211861200034402410b9403c2825511f00c41c112400c0518603201c00b5a0701c01100a4820114000343c2c45030a42e08804203009088080c043e00315070b21f822880040084c11750004c45243d0243e03e040200145041 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 553755872 1250 553754622 553754657
    0x9050406080d17100312230409050a0e0d030b01030912080910060815090115030302071a0903100203070513090b2e1b060f02040f05031207020f0111010c08011401 71
    0x50064a43c05980c506c00090043c00494a08a80e440c814407048002e83e20a9003101e0b0f240300400c11a895100107000f96520707900180103c881d06036556400340c01103410425070512030380c40648000014180003808440d16141e0414020813040d000001c260b00d41d0030321805000401564207581c101c6030382480441c0c02c140316a9110000d004070300e91011206004038180c240290444180c0201e20b01d01c3c02101a03032424001c1d512812482003004c41c5520902080b03003407880c04202c1e259150041c0c01003014171a115031080095000230041d00400005110500c0d0301001e0b050f03c0310082628000200301882b4210070848401062216901c444c07194440c00700101c8070b10201d03040904098101517809000c030401a10a43d4400000140910700d4024204c090441645c0079200780d46240311071100140d26a000d2507030300d070348861019190b6082400040300610780007000322120300c0c040c5001c001c402d64840c0c5003030035683d0b02002c10707021504580050180d031354412902e0000480034a00b5038104481d05411 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 553757122 1250 553755872 553755901
    0xb010905060f09041e06060324051503060606180a03060209012c0f130f0e0f0a05030d050705070812070314100603050408070b010609080c090c0f070309050406080d17 73
    0x118005d0740070f030100101400680d03400617009503008280810004101c451801d0007110152103003030300704c0c500001300d50481c3c509030000b14140350240c01004a40c50709420000a40c2054202c140c540391030312500c021a0315608820b01c0114480d030409a16400f400300094100d03120016940042100700240a02c58914508007000301e0800303403500700c001d00c070280214000e40050b003d9602c6ca0780c10410340d445001c4440c0d02110301c0082c0da9084d1090340035a030741001d444600d00320018045070310500004d2155070060b40003680110b00380c2807282c41d0206541e13a1f21184d0f00202d00755107161120b2020000c24035014003c40c80c280c150450995411b01d0b000b0008440e118071405500e040595480006040050100032244440d07001030100380d140d0794400c001400d1000d640100202070140344ca0300c42e002c1c1000ea4451b4090440703140401c0c101481e140d034402c0d50350020881034042042860f800541034440b84201d2001c0c00c1c1180203020b400824910142c2144030041034405c042c0b035407000f00040c0b900f81d10f00 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 553758372 1250 553757122 553757153
    0x5180d18060e010c020105090a08031c1a030d0f0201090f030f0206131e03020c04020d0b15070302060402090c1204050d020f03040f0326040902072d030f0203070b010905060f0904 78
    0x2802611402300c1c2022511800564000d000d05100020f84405008440b07002640c0c040625a02441401d9504c81d161211116455072180c0507400031034180a00c901a507881c0c240c8050074400010b40010680781d4581d40640c410058022880500380d40b0030f000d038188401907000c942d004002c5010146030b82c0e59070302c8e03102a04a50340e1440c0500034040400d882400811170070b0304014015910307102c0c8548550003c00b0072002030b81c41858842c40c0c00440c0d070f081e08103540400b0381640150030b880d43e0715003d1001c0c5d820010141003009004202461000c1c1c06100e455010380d01072001003c0404003c000a071034201034184025080c0d2040c03204201c25180c42d0191810f072988024030b1407400135480021406000125080c10f900d0350041000300700320400b5400b03020001c2c00f41c520043c070301c54a060003030004409103913900180b0004d00207a80c04280903c02500d40c020035031041f00d01d45441e607102c41d6035045c0300f82c000e000342980784e0050083d00d14203845900140c0134101c0d820ad12070309090391006800c100150 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 553759622 1250 553758372 553758377
    0x30804080a0908070b210106080415090203010f140919110105071509150501030b0403030c0e03070f0e09070806011401140307020606181905180d18060e010c0201 71
    0xd807010803a00c54810403000f0b09503601242ca00c0742e2665032a5138a0340001030582280c0030b150b910b100c0b0b85191400817504940307031511840c05035142d640310301400303502c038007a104401900c0d00d601da0b0050302d01748160302d064403010100080000c0c81c80c1d03c5070384541c0c000d00150040d074404490307068650b000c0c0982c0d0703071400d85c03122801d519014514010b81c0c40d030240d094041c0844500e8411f4040148042d042041c0345803041109800040d03008424204075a420702002d0400014a0000380000f40281d20140541070b050074007050145100b00040d2500f5000e030017184611a80e640208028a421011503400c0080140684805420b050203603650f200140b00d48820310000140c03803480c0ea402044801d00c0046030400c2a596450700e500c1c0a9990601540e030b40b0700522049001380c60321040002c444e40a0030f400940c15402800e2800c9910140070040e24a1034008259101e54610f40400c00c02c1000b44000d40c0c481e44403c03d112048c0c501400e00c85d500607400d010329907948c140d0316a80a0307008440da07a07090 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 553760872 1250 553759622 553759627
    0xf0f0301110301060903030f0306030f020603090a020a0801140a020f12071b1101020d020c092404020a1e020d0836031806040b03060603130f2d03080408 67
    0x400000e000d84199203032410318850000011038866407100900003075070b000b910340e101445551a0100c048408922014003112085034543c801490014000d5403c1001d25084680441c00ca80014030312865070fa00042d0315030b54074150f1401f01d001018506501002c0c0380021410108420f552440c1845030208201010045000044205000700c404042800b038100304003804012510380304140303c500c00c40c6603026105003103c520780c90303200080d03404d50820050420703580c2d5214042410309009a006002403007510a0100d0103113619540301800722515aa41d580120342c140080440c1030f45100c800140454200808100e02941c0200c001034001400c031121254075403107040040c60113140fa001e0380004c07284003129030030140400405440e081240008032081105c2c290301b0890103124610a03840100c4040c80003800a00c0c00d000659808008165440c01030070042e9100750255603000c0c42243c0c0130984038101c080c1c0d2100460783c12503446070a60441c3c6c9600f110744000e04110b000920040108000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 553762122 1250 553760872 553760899
    0xd02060313050a12030515060702010c080a020c030a05070311090f0123031902090a090317090c130501030c23091f060e0310050105090414010b0907031b0e0f 69
    0x4203c04160035400c004103031100101600b00502500d000d5559021283d01c80306400f915181c020100c0321072070b60507102c044000704169a549070710b400502d0b0f014150b0043d02c1c0c2c05d00c1136032402d02400d18514410360207441c3c40c900b07518010b5640c480c0030500302d0081040c2c1701000b8001c0c1c070180060381520b0421105115100f2040d080940c0b0640402200d909402900c070101c41d010301c1082411034091088070349074440c0d950a010001250760b000300c0900050780440440c00c0c0340440555107a00160744205070303004c4500c0e800209200d00d860222003985aa42c803001001030151150010019084540c0504264800c3d910481e66041e48800713075901c1207210b00d021a06501380364403d4070000c5141c1c00b410303446503680c810103013106100e5200503001e805007006400300700e0707051b00c1054162074000b00301c0070450310385440c0d02ca2000c0301002d01821541da94107960303030305559081c055449010150b42c0031404a0010384111448038600506030288440c90070034010685c0c8140b00c0d52603422040c1c0d0f042145081 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 553763372 1250 553762122 553762133
    0x6090e12130506040311041b0e0904050a0501060f091a06071e060606050a02010e010603031b0602041d0726010b0919060c02010908060f0417270a050d02060313 70
    0x120b03803096500c0705001500000300304265003019500c0e40b049038204034000c040802440e610f8413107140d0b9400105029407142c400d01d00442c01036040b40c003410840d62a0000355503550b0071034190345c00952400f00100410048a8003c7c01045840100c064490100810440105d1143c2c022480000c0403c851721320000c4240d079038180d004000d5a000241445010b40e07440c0081c009600c0114940015420302901010b0340c0d03814020101220340c10754441c103030300f001079950800c1d17002446800c80303100b030b020400010014540d4100ca0740402180c1145501810510405000251400000440c04000c14043c00c0c207107040c41409030454404400041d91200351400142c070365861140a29140c59801501060480c0d1201811441c00c0c402e8990726482e686443c48e1603520341046441c02c0e5010181c07400100040e0075142e220a0100b0704450340da06140890b881c4841001810300040d82c850030049030306e00603240c500762a500900068512009010103034020441d94800240050050201c444d401e404105 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 553764622 1250 553763372 553763407
    0x1512010303050c0a240b0a050303040501140706050108010539030603030f0f04031e050a060c051912060f0f03081602100c05010501090c1706011e0206010906090e12 72
    0x41d80422480c1a040741905074801e5014414117180015142984115080c10a180003100341e650050045041524081c0115408005100030032441102030144200240e8980103c0d40038041c1000003081d5454140703c95a209c0c5030007080c0801640e2140c0011050304140d24240788dc00c0c00590501c0c1d62959a20301080ca5031180d80c0c402ca40c05240040c15440080304580030348180e901c10060b94009030b01e100c40582070308a0141d0081c2158009400c07aa00140095010038401400743c1022814200e20300724000b200c110410390b20011410102141c4c501210710f00c40d41d40540000801851810b04041d141d80c031065090000400607203001a0300c0e04211625000c07a00d00ba503008214940c0f1100e04bc2c8014841c8102c01c804035115820000003103242c4845001e1404110601e646030450394140c420464094113024104c1d5042c84215580c12100c0740009000d0f808a810540080101d9490075501e0021503070b80b030303000b100c20b07e26058248004e02004070b003040c0743d081c5441d0019242e105114041d080d48 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 553765872 1250 553764622 553764643
    0x206150d03140c070905090c06071a0a0f06120b060a082e050c0403060606020304030f06051806070302091e0a1214030a120e01060612020f0d0f06051512010303050c 72
    0x4e22036024006140403c5400551181d9210701c2661800d00d001000d1040394000d2038802044003d00c1300b0f03075443c4200e0403409194030191004011076a50b0004070000119402500a5660301e0a005ca00009001d01c0300b01c00c64102d04159103000036145071500003503c80b48013400302d4903d40700306141180320701054503856110b550040810016402c0100b400c0c40f4960251000303c614074284000050420300101c103840450b50040542c141c04000b650394070f802060001d103203001500041c80d0f590714080c02000010310400d91034070016581ca003c3d404001c0207024540a031200c552004280b0351960b00d807141000c084071b203140402142c1400034600070000140b150a407002d1413001040b0340005651101342c122040001c1c03201004003000b81f02e141c90a0341c00e540104008200032160401682d00c3c1d80e4000e0403010442c44195003000b5541c02e6040584810700c010300713500d54449005004524122404211414000c0329140ca40b5a8842c650181c3c020140300c041c09005000c500d02c4007100080c002c01020 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 553767122 1250 553765872 553765897
    0x2190908191a07030b01020d0c03052a01090506010f050d080f13080a08070c0608090a0318050621010806010e0a0b04270507080a020f04020a030b09010b0702010206150d0314 76
    0x440c500f02c80c0c020020f00e8103204060043c0b01d02c180e8150340c64003500c150b4404c40d426075601c520745060325101705030400c42c1190607040c04030741c4041280740942c03e102c0ca070b500318440c0300500519458902c0200d0140a9500414452007544c501280003c010404807041c400d0034a1040d91200c402d40e461081041003035001285500030a442c2c0700c10012a00010320505208480103d001511140c1c1101e10301021102e101007540160526800300e4044d0400402c480c1410b42106a62030304d81300032401076041000c841102e13501c02110660b0075040c02d03023528050080400100783c958546586411842e0018022081042ea0380310b500c01c1ca03440342c0d00140300d4440d0f550503035405401140700700b00741c144200c001500e9074007580300b021880f0300001c6964904540c0040050100341100400c020082d0f2140000005055560040102c29110450316178000c204005100c0d841d50502c3c0006410101c004011654940c51044280000da03501c08210b88000d401d464500001c01000c00015664401c0ea03808441 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 553768372 1250 553767122 553767173
    0x1503020d050604020103230f040204020f0a200307050a03050d14150a0807060903080c0705100504080c04020703090312030f110a11030a0507080a0e04020703030219090819 75
    0xd00000182c1503014602c01c0e03070200074102a01e840000041d04006e10700094054040100300e41c8600395188036002400107200510300502121440d45c41d80c0310042030004034070101580011040504400c1c0322002d0000041c48c075101055031071586416440c0001001c1c0030006c1603140c1400050303844440600201111890706007052803c1c101c010011200441c8100c2d80c0e2140407820310404907101007241c2d041c1d1500c0201e0b609654800d8041e4011a0030b504039803003030750380004113070b610b540700c020110041d501c1d11981c0342c0c2000440e41c107121003100014011801044410002a400211002160b4202d81c1d403a0307650301801c004401070720202140e002c003141004051f4192a1000f401071144200e603844040d070340e912a8080e1600ca008100030280810000d101903404151884020318a000c040e181803c82c004d2094006800c1780c0001d0800c0c1c00196000c6070942d4002503140d40d90720200c00c1401c1c50100c103454006004d03a911202c21003a490b164001d0031610400c810f4101c4e0038402030f0358407142e05 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 553769622 1250 553768372 553768399
    0x308040e13050a03030f05060a060219020f09010e04021f02060109020703020a0c090e010c020601080312040203120301091a0d02101b02040203011d011a03010509060a05061314060f0904150302 84
    0x300607021107800703000964500741c0808c0f51461301c1e03043c400460b2003980140c82403512020400300e0915100f60243d82240c554081000a030351120784907806030460360342c104201d05050052041d419540000c5180080c4070180f4150000e800080b02d078112404c1200141e40c0d6809450120306240e00342c1c0e001080c42400d81d0f0042030ba0f10b8560451480004408003c00c20304c640d80c00c089036110002e100d254100d81040001d55180011020008c0e4468000b43c00c03511502d80506c4036001d141c0c001d900c0358418603603ca0b0124409250b40c3c1e640841c6607401c0750454030440450300000c1c03100e110480300e070082c4400ea2900031903421000ca40e941a02e41c00410440d00c0c1d40e501c2e41c154500c803c810350200300d03100d0084004915100400d05252140b003c03120703607904503805c06090214408020b421590711140c19080054a40e80c0e0304001c14040d02480486049113290200b020060907031004c00038031880081c0000500c02100d8001d80d0300ca14000c40300401c40011030b2050301c0701100700f904042d402060401018 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 553770872 1250 553769622 553769627
    0x110303010f2c180c06040515130518041110080a0906060504090c030605072a0305040902070f02010e1f20011113050a030c140f06030a0e070b040308040e13050a03 71
    0x4684071240c0300a0f140c2075000e1200b040903a100d503011700d503480001205940b10701075023400a1b01c440b1400d846802c204030740303c1002914084c800c2a55180205c00300c82000200200c2e042c03609046001981c40c1c481c242180c920240c80e40b0f81c0100080b001d296941f0310750b804d01c040342d0008402010050002c210f51602c60600c4201415a4007080d21240c0c10100442c8025200300202650360200c03480480703030210299400200c084500805038200001400040381c1c80740540300411119111340c80c4c5c4000058a8400900310161107100c841c45100070000d18805400601505018103840d442c00701001c400c4021001d918603600d40b543c100c9986000d080541c0c84071111300602180d070440442d400b0b825603400800041c042e090000811170002818100000d840030b03c500304240f01d004110b484041101000300307400d50800c81e404201c1303949039000000020f8061000c41d010b00b0511703104c6440c1c6800c40e26480314522451151503080d0061800080080c84016108500c03107078401d068a0b1414040e0400 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 553772122 1250 553770872 553770901
    0xa0b0403051203010e16050c070e1602060c0d0f1103090304030c090e030a050307020a1416090908030f04032105160c020a0b09121606110303010f2c 65
    0x49407103100d032a00e150040b50114003528101c43c55030812500342d43c0c8040c00150081716006050341800024054041800b40c1031000c1c0300030b000d50f481d02c0c1d006844c00540c40e00c000f681d005c422800b550864414006d1b0021204201d403c1e48800d40804151b90144880c288010510900c401090410110601c4815017001c80108100c074041e000e508400c5032104000f00443d200340e890b80c0c00d0f95100b0080c2915550056028680c807880c0c0f0b005a4500060a465081000e0900c0940008681000806c200071802c1d0010041c09003034008001c01c042c5d6084d82d5007000922000d0310f0311414615007070000d02054880e510801c1d9080300004044142c100350000c20010341011f459a42842c0000d031805080c00c0d2259210b1400300b038008040c89a11450300e81407103895030007500c050b82c1000400d0b60184801004000302804903c403007205600341841c006000f00182c0031142c40a03555042040108405030701c045000080e030b1b04000d003003100d14120110801445d0702194403112441d025204104084000415 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 553773372 1250 553772122 553772129
    0x131406060f0307120b0c12100905010b130e1b191706010518130915060603020f070308071205090a0c0e0106021e01150e010317040501050f0903010b0a0b04 68
    0x881c04500002075080544a2081d4043c254030b05403035403000e03408a42002c0c04c0e160032100800703034039150050f68425800b00d018100c4020b5103810103000e080001401600c40c80340100b50020805081026104400c025080f0300d11500307002d80c841c40f0105545000030310480104440c00c5031110b503103034807184c01c0b00e010401000d2540046100c2101da40f8251040121b0f039032040704142e4699291081219480191281c901d40e01a04400d81d041380c49a005c0b21442040310039030082143d41c075a6070b158101081a5001c5820003004c1500600220007800c0c1054191040c1c182d040c1040a01ea82d41ca00c02120450700140c080400c150078503040c007003142c101040f05410709015103207105001da117548607003501320001c2c0700320310040e404141c908201c1c044e003001e46460381c0f08103400070580d43e0203280402c1c842485038121001000c0008010000c21140314490050f0061f007019a50070245444006407040c00340303200d5061800030004400d80786580c2076100c40352a220051081c045039850300d842c00c21b250850701 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 553774622 1250 553773372 553773379
    0x403170109140619050a060302070b161b031202040b0306010f1403070c14011a0a060306060e01080711010504200108040c0303210e010f0606080601020d0813140606 72
    0xa0010a006a00d0b0007066180e0702c1641c00001141c0342c42d010b104103040031007451046203294420201c2c0350740c1c90350113400040902c2e0350701588502550401d2804120064021070180c0031000d01101c0301504140201102c100124507580380709124103003913600000240000910a00c0010040b803000d940c0070107140a01d03400c1ea81d400d4622030030041510001ca948584031070500301400010717034061003081048031181c410801c440001d000300d0105420740d00e10001e150000f01d0021484080c0d81424600c10300140041e140912081d858030360054a43d0740c10051180c100581c03c40000d0810b070150f5203980818801000811440c50103040c002a880c01c458036200e40c0c940380224696a070761144000318080c0360030034800729200b490341d40d040c4c40d50402c00711409540004031452a080703105609c80c1c1000e0450620021401182e001c0c40752045903265003140003032000141c24010b40d642e0000786a40354180c0f900b00041c15031901700c058000c1c5000d000c001402140c2206420024a1000c10f00381c2c0108810b8 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 553775872 1250 553774622 553774667
    0x10060909030306080327030c031c0305102d24080a110d02090d0c0806160914040e070b0d1a1c110f12150a0506010c02060c0309090403 59
    0x4c07803010380c0b03902c6001e581c50562001044610000300c0d24801d1b06030340e48401021160900210000f0a08015018550107504202e040141606507018060194021003400c2c4600a6600300521140c402d02025101c211701e140c00d68030555600383e5640c0c03000151030600c080a02141107071f0f5906000d83c000c0c1a4010026010301c4c007082840d0f20602400400d02014039500b420b010840c3c4208000b504011041580140c0851200b0045403414038140041c01c80e40c03000e400e0a1030502aa89010701182c65408100701040c44200001519650100d5110a0866010602003409080c02c0d192403d42c1d04040480600050b04051030700c4103a10540400b00f00111a20340040c203a0f0030041ca00b69000c1c0441c4040074840030840000307107070000101e5003a1004050000607400180454203032207850000d010b03560b0080d481c1040010300000d071194001d000c4481031060345010380c0002c0400300748030b00080c0140d10200b261002141c0500542d800800003420300c052621307050070700502c4500c046a080c516203000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 553776978 1106 553775872 553775879
    0x5062421010e070c150b0a030b0903040602120c0304060f031e143403060b0a091d0c0a1101020d06030501020a09210b0910060909030306 60
    0x241140c20115604080b54030041c0c034070161a190a0050502010380011080354080040c2c0003d00b0001c00c4d1000110041580d112480e00000c1000c540d030700402c2104100040500112001c9508507075110154882d424804d00c24040000c100350405c00040c044a07000315140301d40b5207828580090300400c8920300c40701c018800440b0300e22075078135000c400c00060801c3c107031030350060302c40f80402c03c7c010728020000d1714014100c06030240c000c0c101c10009201c28040c1e80728800601f503100c010f960f1103a2500000748110038074094000341c44440f08261070180004d1400d13034461003405203410716110400744155201254600c291003190b4080004440c101030a0003158000c0d48920000358413002d0a100140c040300280d0003241452940050708200f0052440c000164543c01036600816a100d4108480c2445800d1100400640c10300760700140d01c0e042a4000d1f1005030003640e040184585 = true := by decide +kernel

theorem cover : BRFrame.Cov 553597122 553776978 := by
  have h0 := BRFrame.cov_init 553597122
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553597122 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 553597122 ≤ n) (h2 : n < 553776978) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
