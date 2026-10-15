-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3901
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:00:30.251986+00:00
-- url     : https://prove2.me/submissions/5182d9a8-70bd-4c7d-b2fc-b58609efeb6d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 701438848 ≤ n < 701618705 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 701440098 1250 701438848 701438861
    0x20304110d030203120c1b0c01030c030c0e1c02060f0a080606040b09040f1d10050604180f06090b090a1a010807030201030203100803030405031803060f1303141804 72
    0x391814401c250041d60025945d00c5142c10611030440400081030040500d24101d8912407103d840511001e00c81c1c808980c0c0340e03080c801c246404246003600c006000c1740a4045c0c10051216529655002c0c24400144124a240b05040120803803080034074400699520014041c00c200d560400c036154112640d001e0801c0d100901102d01c14030080c001002104980740456402c401c00f5a4040303440d002d03c050090160404200d142009060940d0480c41c5543c0080d042c480c80354054010302c002e0f11480300f0300c01160009000781092000c042002004910307001d100c141c410340704500004001038035445080342d21006803644d03a11500034020b900c06000d0700d00300202c1a00b1340301d201c1429951600484981c2c131401444020f041c95004000544400f0341c03041400028500481500e55902d0b0615010b616035014515041c0340c041c22078083c1491b0300340098182e11407100550310701419142d106021908603036140044081003510803c803900104014094640401c00c500a420390010030000c11003074594 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 701441348 1250 701440098 701440133
    0x2090402180708070e0603040209190f0f0c1d0a15020a080d540210031514090403120f110415020303060d030f11150414060f06061b0f01020304 63
    0x200f4010308c00075a507680389098002c100b015810340c5c91400f1547c80c501801c0070b071040b580003d103840c2d26000040074130f8000800e0f500c050f40c1d40d10f0303100c4640c0d414034a0010040308001d03045041d6034003d0005066030325180300e03c08650700456074010310304d035100c2a041e0f0014444480a54030f940328080c0d003841002084000e100c02480381c451199900a5a5040e0b801020b942280c80d41c5003540030201052018a4150141d00540640d40d0054880009006043c140301e520780c052008034030028544807800d24442d030703c8400418602d03640c2c0300c03a101100e48103440b042c0c4a41443c1e80303c64603018000b161090000c00d04400c58000c0e22286011102c00300840500c00c5982990000c00400060355203246000d1020340d45070503d13440d10044900101c03401401e0115909641c494480280c072481503900c1520310503449540203501c80c09500100a485503026106101c1485079580828080d103001e5028060401c10709402c030b1121820b9611039841d00d01403101e03030b03451a54000140414000d9030000c410441c0c1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 701442598 1250 701441348 701441359
    0x803030f070e010e0a0905010e0105030316030f030209060318010b03010e070302060c03040e0108070911160b18010623030c010c1b090911030606010807050702090402180708070e 78
    0x589182862100c0400501041c02c10180400c100c0c2568041c2d000c40c04081809480480c03015140c807452401842e00f8021040c40342e2000000154038613000040b104112103491056603110890b0350262081c3c40041c0200f4103268080c01800d0344c03611804042c500c035035a00b001007049044030741804d5084410394145180664145a0510a5242c000684804813603040c0d8165030351701e2540400c242503000d260040300034001400c00000346800f0000b105001c0d501d000e0401c108000c03581d046120640b081203100301100401d07096400c045195055007544c0981518501ca90503d4081845402c59015030400031044090204c4030801d403044159945005d4416401094004080320000e085030b01d0442c4000d00d04900d1848100403106050380b4038000700390078001400b00d1000703403404224801e4480c1c10507000703100d91030015078298412459180162a40e0321040d1a0004a030284404020024026030304030198420911040e860982031a1003100ca41d80c6013046030610301c2d0003c0404586d003a2152040 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 701443848 1250 701442598 701442601
    0x30c03271e24220522020d1d120a1403090a02060316030f0506030604021201020c121b0d08060607032a0b0a05010b03071223090f06011d0705070c0909020a080303 71
    0xb80c81c0c1401050005c410810440600300203a000d40001c0c0c840c99030401d504504008400c0ca00c2c0f82150f40c07201c08147c81a040d52884400b0301c450003000e01035000d105001840002200320b14411040066801c200d03818103903071140c0c0864000c43ca0b00d034402e54200072618110360000003002d6140c414034140680c0c0c1d044c184294180200000c2c5e0310030001e080a8442e125041d40240d12020035811104801c054005988010760400c640c40c615030055000900c0c94200101c2c88a209000480c142d12030040c5a1035880c91600c50030184003450300f0422040302400409a60104210542c400079018050a41041000414540342610301054040c003c1004a82458014000320030107400350703030f408074041ca07209880e41110f06908024144140000d001d8004200300000d040003d11002ea1241910304201d0344442c842103103295549009101c0d10164424007070400079030a40b551403558000d4020304e03245041480f0b6480d56006840c00e07a0007540783c15924800d0904504085529100500203040a0b4ac1036 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 701445098 1250 701443848 701443859
    0xf0b0613061415160305030403080a0c02060c0c0304090617160308030604020d11070f140c0105040b1317010605360c0c030c03271e2422 60
    0xc84100c80031a52050b403c151540000011540c240d4040076102008696042c0d00c5050140c4139a0080c0c0307007500010b460030000361080f25540a40b11502e02a0340c014105076450308003a00c1541c02c4080020750f01c1c0030422000443c240c3c40e010b024060444003040e001321400200e00c840c0f90401071076041502065080d800c00101e00b030a400c0d258422001c0e01c0c050303034512800360034400078155030341c816800c800042040c6040c0b010700440c06a28074840d4640302410609082d100f0b0765002861601760004401f040203100701c81d192406000c10310341c000c1d000c007040c54440003448003000b4000c5940b8800e0390340341800c0043e1700e0841e144503000361080610800d00303194850181c01f540d07505110003403a0701d0f02002041da0391031150100c0781101928410b594881000184280d180d42c40b900303d0342c0e0f031080600b00c1000a070302c00c8a0489148ca03001800c5c28045c0c0d0f045031036102004840820720fa4003004071a01035092088030407070840008032f40078485076218402d46104002441c0d02d9021034081c2d161340d0f0180103 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 701446348 1250 701445098 701445119
    0x50606090a060f140a0e07030b090c04050604060e030307020306180714090406180606090207140607052d070606230f0f04020706020f040503100207020105040e06030a0f0b061306 78
    0x2681c1814010132400e9501201064415403103078001030f84500c0f21020440070702d80c141d0081410042c1214416620746408000c003240d40224040c9a902c8030b420001040b0b4180a550340e503001e4000602a41d09240c00c54002a0601104682c01c099a10341d010200c880d02d2400e01010010b4180c400043c0100c1c248000480d0810100502c0104000c0e80c50040c40000c1c40d104500701c3d40b107235106001f030041c69201d03402c44020f90400b42c0d040310fa104d5103103100c042c82000490300310311503445951101d084c400300c0d62000200222007402c003216015010b030a2410611f100b8014601980030381c2011030714a184c01c1041880d070b090415803008405d00c440c0e00e002c41e03507590b80301006114011902c600e01403202400103002841007040090100e0301c00900f841d00e131080040904200c40046060307509040c8041030141c1030b4824510028000740d810482030000e04420140d243d000140501240c2c0d0800f041d6035080038120135848140ca000e40d2080c01c0100380d1926550f000c4c0d280c84445170610040340b500701000c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 701447598 1250 701446348 701446379
    0x7020703150e01050702010c0318020315041e03081005030a03020d030f0b1903030306050a141e03101b4b120c030501150c0503090607050606090a06 65
    0x10924500348500c524405099000b03000b2140480c402044141403041700a0300a00a00e003026001c42d00304204050b01400a0403602c00d0550060090500303000741200030a45420000d004584d07081c1c4048860040541254031030817118842e8407203281600b092000c000e0707914442c0c0c0c841403099000c901a940002d034045695100030baa9403c0100781007210031320900c05042101c18035a04102d492000d200101807100d16102140d02a032001c103d815141d400340154500d00c2d016122a000784030080058504202403407452002d40a00d002e40841720080000f4106001032610842c0c0d0741d25a18803201280800d00e0358143c01c0114107250808501500b1801c0d2195032a07034543c0c0c1d5907000740180003184110a404c808820b00c0341d004102000c01d4408002e80304a00e82c2d1140d02101b494076514110305406031090b40d058842101158941a00e40041200d40c2854200129860302007402180243e45803c009420340502c00c00180c0740c5468010140990810000d114901d494103018013000001c18846611 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 701448848 1250 701447598 701447603
    0x10f0309050f0a080d060b03090a0318050a060e030606061c05040204060e0103150c020115090e070906080a0308361c03020d0b04110d0b1212030603060703020307020703 74
    0x10658600ca42845810300180740300c001094000d0300c0003042042030345801481c084001503000c000d0b06803a034401d9501c600044071540401d03408505d050300800d0243c1d00d40003103100d01c65010b004d2141c48001180091100750b1064002c900307800401c06191400303215076540100c0545500e4100a100c001a0081d083e82d280644031040d5600042025901c1d182c001d0750140c6040416124194ad4910300348076500710380035541580b01c3c54410000196031040c0241d00e01094101d05213a121414204018005c20850b41071411034441c4040001c1c090781180a00d00041c002d200142907101118107001e01220130050590704582a4403c1c800c1090340b643c6081d41ca0004601180041c5401a00300d1034903040c3d0084120110320281e030603c1405c6a45a00100640718030300200744150104081070000303403880058000b11880e0103000e01c0003003480c0c952050700355040040036501002491400c60342081280168108600740000400c6801e0804102d1250011424902103245151400000751261000e0000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 701450098 1250 701448848 701448851
    0x40b12041104050405250302060c0a0c14100323070f0e0411030a0203100e090616050702031b04060f2d03080d0c4506080a050c0c060705090f090402010f03 68
    0x315805403011b070711044065607001d0800d03a40c0e900541c070000e03a11140c856007191120380062020440d03210b68400c0d0f05010300c014200003c09080d500065000d01042d205080a5940d480d100011031081e50036001d0103071066840c1e603541c400340c0220050804c41203040b001d0044c0d0400d4424030b1002072031011240e010811f0f050050700c03601c40091006061103542c0c0000101c1c2c01203024402c413030790041851030103407440350f03000514400c2010003500c183c040d1150295054210414545503402104207842040c0c40081000517100d03151450034444e2540d60700003c408545540868880000390524082001c050502100c0258550b5840c1c000034811141e004852035201c018924166001e00d0850181c0d00b403a104075864025001d100000b4506a5041c0300c010308002d00381c140b2525614081c420030364002e941e401d801d40e0b654a8810000d0040a02901c1641208009044c040c41041c1f04650064100b41c0d00c0b1542c0724a440704009200941c880442d01c01c2d81010b0a000040c0c2e00090f0030441e03100d007801c0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 701451348 1250 701450098 701450143
    0x2a0905030d050930030403031e03050601050306091f0b03040611040b180d06020309240606091c060e0304060e030d0519030605130f15032303040b12041104050405 71
    0x22099000d180c0d1380341c621448041030100416801500c55200306c2c6150407541e080d442c1c0e5001c22001d958050b50b1182c08104200041201360034108100d507440800358285040e54281d907401c00c2981c0c1503507032001c15044000f000344000c005880c000c8507044455184034504090404080604902c5070b4410807080809100c036402c02c0d6103070b0300c00110020790001c0e802c548901d00011056100c42ea1354116003400c44032001180711004012100702d0103094050310b020b0808806000b1300141400e545c1c0c144c00c01c01240114200010840e0043c00c14030b1100102440e01c55240c800080c1405d144c0d00200d611a40010410b518101c2c2c0c0842541e40901d00344e507840e541600e00050036401040c03903403c459041140d8400722f4455841a8100d2010399a0070322007000034210459200c80c0540142c0001421106500702d03503d400d501030f0038108000301e1700d01d06403807130940c0e1407900d03402c290310103041000250440c4c002c00040c80004161076040d40c0f01514207000d1441c0c240e45140d00d4409800d01d002d9000c10180 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 701452598 1250 701451348 701451409
    0x1290907120b04020d021803060408040b1318140c0412230f0c21060a11120f10060302070b06040f1508010203010f1e092a0905030d0509 60
    0x204000741c2d2400152003103540d50041c45090010790700030340008003001c51880c4510201e060000d801803107980c20071403c80c246801d0002c0721096602110740746001c1c0150000c0800d00945076462040c0c44140b80380002114101d000c42c00307000e0342006000995994003071004210400e0340460845110b5440140c10b070803074002c8403026611070003521041409101c0c40e8404052000005171031118207500321006203110301e2004040900002c100748169060f000a4041402503603150802003076044c803481400e0a04034280140542c03800100d8240c08408039101c04e01151185100c081ca024109504d02940b900c07030b03070381ca501e200613001401540c01555a08215541140e0300c0e03012028000303103262a580030b160342e8003903d4080e4100f8002c81041c00514680059203404d202561071b500c04c4608400144035203000d120000505a5504042101c480440c10328103070401c1322001628400c0c15110030142a041205051610b08038000e02414000104141c001310750303407180c1d206460f0b4a01e8070150031742698030 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 701453848 1250 701452598 701452601
    0x30308060d0f0b0f071202130909060b060705061909020d1b1a090f01030b030709111b010e0c03031303080702040f020324090105062205120129090712 66
    0xc1e0800b805510f1200180001c80b020350410300d01400c22a034403c1c080342e180002c41e5007284901c02e1414aa0348050310100030740c0d24242c0203504464011400040c0c0c0342c8941e000310f09190b000203811141c41d0410002c00604807014034207100a182002000c0103110f05641c013007803560a614030058030800c0c4106401401c4003074145510058080d12950400e080100300c86012250455600c0d0340c41141200d01242c19035100e4800c045813904018000c007540351a01d610382c402041d40e03520049140a0400c6003000720400041d0714083c20410300f000080207000c3c0c88101d4244540300a0303e9210307810030401d00d0800c04505980740e080e01e40100625030340d0303490380c4009001131410307030003000e44280084100074098030008490748601d41c000c0d01003815424900100329404409002c0e51391301450620507110f250081c0e992000d03203040010007005071a910340d80000d0400c202d1480c18041a9150583d081c00245c3c1c0c0c2004245480040c940300544010000001e550b001008003c0d0b400c11154401c5112290050b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 701455098 1250 701453848 701453873
    0x3050a120906091e180204080c121f021905040e0a05250215070206090d0207030b0c1809010e06181b0c0a0b1303081608060f0111060a1a0a030308060d 66
    0x5c0d840189040740d41c0d0120001e5080b511070100c0300e0140a01d82c0030785041030044101340091010103803071091400c0c5410f000240d042c0c0d102081d41e90b401e100c003400742c4a140c408601207200c0740e140c642d281c80c0703008074940c590080180703540b1026042505009803800c1e8810640c2d01c3c1201607001446c42c04118800700e14100903a9149210260150180321400d41c012900c54090440300003920b03480c40800720141d98810b2070f4407006080010400025150503400c03405000394481d0207407540c41211090002407204035003078200400d824428002e006c00f5141c0351800c0b5100c05075034010f010081c070340461600501c0344190501181000d00260407003004009200c54050350342e210904000c01d04005504070794001400c4c004801084220740800c0d00c0e41c0000703600c0c45100c42250f448030078641d14901441090413582900605111040170320849000c0700f4003a8600c00e00380d00308009042c11984072503101603190481d45500400c00b0b20014000700e80d1180741c040c1c1c4518140c42c04020758000e4079014605410 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 701456348 1250 701455098 701455109
    0x50a030b060708040602060c0a17070e03160f1a0906030a0b18041b03122106140f010906080f041a0106020c1002010b060a11100603050a120906091e 65
    0x38005140c504001000002d413050714415401c581d8103607516001c05d0040d20a01c42c0100110314076074a4001e0703209564071207a510078128509641003102800120f0703d0221070785241e4062842608041c0280aa050600e03001045e031500c0c0c02c48013050a001000c0b0500c1240d82150190a000001510480aa411400c41403101919044079440305070700c20408150261000c45203080c62120030050303030411403c190260394000c845110f200c1181e19040c1c1700010611122900c4009282d011140d01c2210f02c9040028030f0308400743d48021400a0400220b4001c00c42654103028100c24244041c075800380800350303c1a001694150355440358141036403014502c0c00452100c0f43c407403001182c3e42d07a01103a4801004401e6920240607034081009a083c0c0301c08500c0320303030000f0042c04108034040c0700d04104424030b0000820b90302006c2100d000328003903546580003a83e40b68005030507c010482100c2440780c0c0c130312007482d000b804035043c81801800313040b00e8410604c5000350f10b109038400b6911060200014030 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 701457598 1250 701456348 701456359
    0x12304061215051005130c0c0507080d120504030905210d03020d05060d1203110c0d09050a1502070b0c0f0a0b06130915020a020712080d0b0f030d050a030b 68
    0x158035182c482920300620151851040c204400301e880900944c80d101c0c00e03518002c0c20205800c0342d0244038401012481c902c4000c100d49414a503000c24000e020000241c11040c0150813601404140504a2a45d4180224005182904103c042540706000406036101115885000b04600791505400f0100b0f8400325000e0045110f42404c941c0c03d68018213006403422001e0000303558841c20000700c429100340217000f07455000030160b240e078400e038000340201600712501c13030400350b840c0c0c50240341c144241c0d02d074804a0b4207041c05205038544540715900810002c4002e03902083c801d60000d444035050b01c00d00c82e00320000b207240b554441081c4100c41c00354610004071014641503090541a6039010b462907400340d0310802201c110640c1074050010310381d030131980000c924110030340d0a070002d60000c14840218040c0307000128802500345400745c1904c0c000e13000c2a817114203640587c41100d10799000350344600c3d054804020242c90206407004521131b0750a10035142e240c501819009840032505040d07000 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 701458848 1250 701457598 701457629
    0x6080f3003090d0806010e030604030324030506011a04030f1112010212060406080a1a0a09050307050a020103050a0b031c0519050c07080304030b010e0c120903030603011401230406 79
    0x1079000040c0e4a40003283c607510044a0380b514801034038041d40f080081038140d00083c00090100e80242c01500c0140801003da51141030702c428030394078075003464000f124140c10801c010061603042c2c690310350002c02c20007003013440e1501d1507540b09602d0f124400001c2c10002000c0032051155500032060300142c03072600080d580c0c0e0400c0c201c00c02c040d0b541120442e200703601e442d002040b40e507000031700b0019103903000c1914411058400e101046a0600400784070300991107182c0e110000b04248098068036204200402c15040d040c0b0003d0182c0c0c0c0c2c02040c0d207a415290411b94052a40c00060341c03030f81c000c00f802e480300481000c94400c446903c9940d2810000140074400c0d14030b20781e4407200900c0142e0285090b14034083c1c803984010349901c6544400780548030044018007444000d02e0300d080e04a08803602c52442d0002d800e00c01c4800304012910400300b50070102c204001e80c2420302580c0d01040301000c4040c13079581024041da580030304001460301065072070410510240c407507601c644060102500d00080b031 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 701460098 1250 701458848 701458861
    0x415021602030607050c0d0509040f320709060e1f0924051c0902040614100809031801210504120207030302030f070f0f060c0306080f3003 61
    0x44800c0c2400890081c8202800124503621030801d8030030210014014102c0242c40310411241904000340580d032090b51a00c000d1003a1500344200079121030744005d0186500340d8480e80340540002c00200c138101c88400401c0002155100040809403003541c10911031885120011400d00c0850380054401d07420450720790148550480e030980111805901c00d09480c00441e00b002c02c02c0c0600552140c04214144000300a2800e50303c13026400c1c40703841c02c001849009035000101a6181640007a08207071130103020002a080006441020b05494140800203040c040d03025507513449140707200c1c01302c1d54010030032030050781c400c101c44400e6440351005c854642c8200314118004041c2070b5000c55541c00d080d10b100c01090f0000c580b60381100d406801a40c1800c007003104440702c5030b002c81005c9400106030381b03842001070030b05400c6c0d8035542d001d841c001a0000711403c010f022961182c103d11240d0b4409080c951003001c00169402524400600041428041044030202140000f42c640300034103011040101 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 701461348 1250 701460098 701460127
    0x14160f050601090f180803090f030d0b010f02010c0806040f09051005400c15030c0201111c0e0c060a0c050c100f0e011e02010501080d110312041502 65
    0x140c8007600d404000050304120404120f0300e4080809680c401341c03031004408035020fa0041c7d0307406124401524100041c41d500b00d411036219078000e203c0c1650b100380404565070f2010090034000003500080120103582d240103000160020f04032481613031110f600d1400000b4580040c0d40c841d50090813140004c0c0d03160214409440100c0710341d5107004601e45400003201c004a0f27000460031210f061480c0c1408207241841064280c441c064820020180b40001c202c071849031402200507139035500142c028404c40300242901e00c0b01d02c0180c0841010310a034859041214042482c0307a400c0c0400141d02007013a1080c83c18032040b1106c043d44a840414074480d42a0080a0000b0580c4104141c91854804804016800946c040c0c054000788019a140034828041c200c0401c5c00f460504111120000e0000008941941d0242c00c4006075151801007081d92800c105012004030b080c1403909440401340c55290742c90050341c8100840c000e00c43d0224003031144001511a070300a1003607082d0368034a01c0c1c0201d0314 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 701462598 1250 701461348 701461351
    0x90d050c10080103021504030b07080709031a040c090615200105010e010e0606070b06040b1206090f060f04020303070f0303092f100e101101020d150605040614160f0506 74
    0x3c3c01240040102c1b100c02c10068222810350341c0c0310450300c0640d11811021100c4030001010f80e81030045200c008400726481c0003540e010720b0303400c1d02c0901c1140b50504e080b80300405039500c0000c1550a108090250200d07528030021000c4d11032414102c5d8580c080c3e85030100810140ca030040c0303546414004520a040c0704135203030513942d041500c070b4583e450703040c2808141e02c5003c102400340400c5c2d0717000c901e4070b2429421441c2d1040d001400b6492400007003034018240002a148030307126900070b401c500000b00c024028554000d0303620295650f81e00e869000300342c4034410024000c2c222800540d19800b014000c0d0701441c480307078208401551a8900361910500c1c81a0030b4107402102084c1c0801c21858a8031800d0207400700305503650314206400075014442c15440c4114a0414400d0107404841005801d10150030341c07102c0f1400110b6150300d640c81025200360550409810094104010700c54150404400e4912040c20114195544034003d0400101e0500c074130000c00d03284234003410400f484030005619 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 701463848 1250 701462598 701462603
    0x40e0c03120c0a210224010e040203030c070608070f03181416080c010e100905040c02010216060b0a080d05221509152303040203030910032708090d050c10080103 71
    0xf111450354902c4400700d1103c6c80c0c000010a50000801805404c00c514030b10354116201030100e9003803c40d18011981450354923001000010b144c030701002155a4000251007024800e42000c025034221914940b441c44207492014210b21414101020501e40030424109050342d0b0f419103844088e140c02446880e490310383c841ca80002d6500d00140010300c0c040350500c810317141c503031200f004603440c10b0103000c007809804130340c5801e6540c2800412005007540d18a1400d03540314980c0092501c04c10401c00004408641000e00710303501c00c0f08182c500d9608031085034040101c0004a0010b0300c400c103812000003480380c01241d440408104d2050000f0b4000036104251500d5244003003042e0030149049035403101c032107980d50b0104d51903451112a0a58100159005800601540e180c02030314000b080c0c05240c5201d001000942e5281d5200c402200003010403101844020700d41040350113902e40319030b64012901624411304558040200300142088040074614010b0041c404107103020002808203031092109 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 701465098 1250 701463848 701463853
    0x201110a0b06100e010f12020d110c010e01020313030c1b08030a030b040c050405040f0f0608031213030801030201030b0d05060a0e16050303030f041b030c05040e0c03120c0a2102 78
    0x600184c003402510072034400c183d450010131040c80d941110908640341c028620107900700700641429185000c1c0072a80d0821400c0e40c1ea0f5034070b03900919401c40c0c0c105071f800c5c03030a40d00c10305c00c0c003503018600d00c2d002c0007440e054684451492000d007050740c49080c407202d04181c124000100003031807a1000c0085e02e105421618200406030382c41040c030054541c2500d4500c005030040000b808507207400e0f03010082c0700391151400070700c0d041450f0780c0300100d5080750010400d6a10208100001084410746913501002e1600f00700d500b000950380203441002c4c103000c000d05141d1607446074000c1d80c030b41c2031841510039000400c4419a003841540c103802081d1052044103180900c041407140401c10b20420000c03200e010380294035580c3c8107580c640440d40c028008035030798901c2014000c1d4510f40750380c4500146004041d42c00d4480c0c40c1904010440f55a0540f480c07503038000d00404081a6004036000d80a000210801c603540e90451100310700305500800000c0c44282c1d104a010742ea0100c906d503444150646808 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 701466348 1250 701465098 701465119
    0x80d1802030609070303050a050d0b0409050c1306030f02041e0903030c090e0c07081b030706021c0e07170a0b091c05250c0801020304050607180612090201110a0b06 72
    0x4006444d0440ca000113400f2a40030400c0e401072522130360040c849072078004400180b41e240c40d0005400c0d26104081501c003944400c2d002680d83c0362650828481720380b6000200020f40c07440d07880e900011a141c401a10a070350301c0d80a81501900f48410707208a1901c024100b200c40600e02c0c1c0a030040c109951120001840d006010661042411001d40030b00c0c60305110340c3c14519255100d06903984040501102014000c00f0001042010805060f45501c03031100540c60f0000c00c001c02600445a0031040c4103603060421280f80d00c040400d8100c2500c981102c6d10341a9000c607a480303481c15240600041040d049403080107004003002c520880708000c10141d5a1401503070100841742e0340660051240e500420380400500c100c0d100081800d83e03442084a85206541d075001daa089030412201a06c268000904000c1d4003a409440ca11407000d2028004060a05160004100a240000801c00c483c1c3e16181001568018207509140e00c003031030100c6000301b1462400c40c031180300684600b8010003030000c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 701467598 1250 701466348 701466361
    0xf05010c11030a23073231020f0a0c022205010f1e0e04210e2d0f040b0a0b180d0b07080a110c160806070207030807080d18020306 57
    0x1441c01c0c2200c1c5407003e4003220400000140d000c0c081b404031a1418100340c15242d0007981c441e10310000201034900c0c03943c82c80c0c480405040e01c080480002a86446104000b00c0c0403400d403182c180d60f0806440c1c41c0c81c1511240c14404a8a40c5251040916183c6086070384541b002174682c00c154181c9141c0140101e075955100c1040220840c84401607241c89040f107014013540c14101c0700280c1c450f0240100c1401065100c3d660842400074088a80c0040c0380b401304a84242803085007084454614080240b40c0888581d110024103d1003040ca44114210710300040603940b2904107201c0c2020043c1200c2e20b0f96500c00303081a09074000d04c0180c51410300c0965095140c0f401c1e1052800c4180c10000881c55a178440710229a01e8400414140c4941d03a654042009031010314090301c00c5e400e0150040440801d2225444600b003540e0784103102ca42d0241042028060f404203003101120b610a0b0b000392502d1892800c0030803405213210240c24207250240400f000c0c00300500e1030070032500075415545241c8070b00 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 701468848 1250 701467598 701467603
    0x62403060c0708070305121003050f0705090106052809061b111026070924030b06070b0a05010e06311805060603010e03040f05010c11030a23 62
    0x85600408444042c04520080390b1104000c2101e10301c0791a102d032509001072000c3c0300010090b01c19007814144030700d0a2040080c104618002c00380b9500003014940c1c0380200180200405005400400c4030106012400040312050f04000c000c04890b10002d011100034010401e000c0c5100c0c0314002203d01c0c5241c524014440c081f03140c51500a1900010100710100f40505107107001e68190401130b080d108200d803050072894890542c01108020303009828482c0005107060740a40101c2d48042101d0441c403284050b407410107004009504000c54291000d13000170780d072409200c40141103182076008024014880d60b00c40d6050300c282040c50003445e1540801c0c4545007000404200c94004030381a10001c0068440d25001c01604000000c10403000804036802e002507506000c8a00780d122a0501c0024079080c0100140351402030000d41c113140c9881c0c09000c041c40644141810301c1560150701c1c007401074501c0307110148080902140c1c460342e01c910b02a4a12715026a0786070886034542d07841031074114007 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 701470098 1250 701468848 701468851
    0x12050d0507050a0222092303090906090c070f050609011d0a020f04110f09090a2717120415150b0c030412140d09031703041406240306 59
    0x882c00801501e491903080c80880c10440b020aa425640d0500521000c099801108a8a441082c410481a2440582503400001d8000c008020381003481007500c41d440d080e1038079602040840740b0070490340b80c0300c10711000c174407401c5d034042c0c00e00c600d041201e414800c0c0016620301a0100340003c006070100442e01a0080c440d080c0d03a40001d401620340080545040f01461102c154000c1002641c02c01547c00c16030550701c105413020300c0107800f05121020345440e1034004d50200e6008800d01030075007420410569003902488613023203203042204103400c0c8036180040d846006040c0a0640c0d6480c2490040240783d01e044904a0f0134442d02c03401001400706a000b03c0309502682600c0c0c0ca02c180c1070904c9840982c200f0030701c100300c07844140000904980d500c480b56041c580914500c080310450207801c1424001c43d200346005001c0700d001300304005a140c8041038503903001e0b800c0b032540740d840e00e03e046e000030310010030703008510f1180400b4000c0c0880c0201143c51500c00e080750328441c08400710141038a0703460 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 701471348 1250 701470098 701470103
    0x60309030a020f0c0a06030c030f0612021305060303120c070b07030902090a0e1f090203030301090902011209030c060209010318030206101d06010c0819080103110d350412050d0507 79
    0x1e04800308071b000d0280c1c00c462401c0b44c0b5420086501e00c0d0702c8000b00225040c80e400031601140144d108015400c000021341901c0c0c5c0c02c4a024002c0d0314000002c03d035a88a42e885403d0078108060002d40b1084124050b40d003040e030311190f600b0550038109402000740c1547c450691107080c1080204155000d540701d0341c4000a2424064810700d50b0a60702215131440541c2008a40c64807150303d1001a81c0a02c003e60280c0302418000540e250a40001445c815407204a030310792902e4a4400c101003504264503d000c00c0c0d2101c1b000d44e403102c1c041c00480250460a1100d030880003c0c0558a04150300825039030b1244c60610040f10455035185944030300e0b004080c0154403180400f60200360030b94070850a0b0344000e801560001d1800c1c01d070301487c10000c0c140d10440000101e0400040c8100110205604419017040342c00006a100366220a40c07c0798031f50503098616084901c40d40300c1c43c034016203104008042e06a0362a102c5664425245002c1c0e0313860801c483c58050000102940d43c000e00985800300c0c0c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 701472598 1250 701471348 701471359
    0x20118033903140f0f0328081306093306051c03030e19061b0807083304141b0705030f030702010e0607080112061a060309030a020f0c 59
    0x525684a080c100c954020300d10350076004c1d4005819884100301700040031908244000c0d60740300c4481e02620504448452129030521201d00c10346107540c0e105810780d4108042d500380c0800441203141140003085180001460300d50b8038a000141d02030501d048040d0303403020050422000406030806800c41c0c12a0040381d90203014a4019041420383d0b4041840b07052081c00e001600040021401c1c0c9401c41c50040000515a46003021040008900400c5031203004a40780381d04c0c0d0a1041005420304000405100801c103d5800080e000d98501400160844040c0464007a0300503031a15160412100d500c902e01880c01c10548140200500b600c1c2c6124185900650700782280c14682d5020039442400103941c184024441c1c4484940340c8002076001d41c006400018411a402044a081c9400104000c2c10b0009201c01004050060404e5403035503680404001561080a100300074115001d41c0c0c101e42280010081050054000005090481281c0c080315624008c04030341940c1c0b000401041504170 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 701473848 1250 701472598 701472713
    0x236150a110a0204090f03020c010203041805100509130303050c030c030103030c05070f0e090d020c0108011401031506080108070806130206070f120302030a0b0d0804060c02011803 79
    0x12849085001803980041007607592050b01d540000302030b41d100300703c2503590010054191041640401002058180038009141400c0c5801945003400041e800c810b55995158400220b000c56841090b0026200c0206a1001400e081494101440c0700b46005c0b80401d1510b0301003420301c00c0c40030940307110300b141d5494140385031b0030741d03030110740068018004407200c1c4664400880c10303410301040b180c003038160202d140405181c14040c0503e403c000c100c41d10150f40100540c00140d1f60b1140071281520203056500d01c1c841403110049000f8071800c00007250070038081c0004929507901a00c0281211b00d490222441e0a4907500403e483e024150b0750303240201c10030481c140060078980b018100007030003104c0d01e840040b80390b01c4101e9031030301c0480c0006c0069800020001e0056081c4200e00447c40250b079040840d4203d0b542e060502d110b640202c40503c459081128116845081074040d040709011130519000d07604d151190b01c654407004100801d000d02195401d8444c8941d14402000d08000c0b80f500c0c90 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 701475098 1250 701473848 701473867
    0x23010c020306071407050a030e10030212011e0807141f02060a0f06030b0708101706010e09070803040b0712082707051008150a120303050604023615 65
    0x1c0442c1032a80541c21018010b00c401b0510a00c29441050701984038000945854001c01004151018204082c503106001c944c0286582544050640303185080c030b8050070484c40c1070b00c216001c141d80045180d100e140401b08503812140704003080000156884800c07045402255400e4021a04040c00180d01030703800500303c401c1c0f540261140403900c080010340240c81c0c1c1c9900e98505021100040030510510034131142242e40320f8081d00500c4076220410801004024064036610f06100301d403000f1030706401080b03199005000540c018008507049943d50341d0307180104800d0780c010100a44908244208982146004100b0b4501c03900c101c0101440c041c1360410001034000e480380541a0034411050080b841e0384644400c03540c080103584900c40c0c0c514200c1200280c40c0f100d03141c190301a102103241008178104016004c03080c1581400c02241c0350343c42c0d0011a009004042662500c20314051010480ca5001c54104d40c402c02e00c00030381d40c83c0f51149414030281100c00e044001a205003017142501c0c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 701476348 1250 701475098 701475107
    0x10b0a15080f071b110909030906070b041b030b0907090618020a0e030d031e0b210c1c050d0806010516021801030602041d04081611090123010c02030607 67
    0x3e12003001e06250550408203440d841c40701c0003562041324141c9003442e414505140981c8821703800072150004528207030010005c24580e0042181c024001e40048010030f003002008501e034620580c04660307200d14241c1da42018000d080d403d90b03010030f860161100204080040b801074109844148090340d5066105003402c4000f0344c008072084080042c084004240c41d0b400b80b0110301d049023180e501250074081c202190000f083d01c03890541d051480c2003e1494507441c0c00f0108a4005400b03208484540b03c540011400d03d40000102c40d030085018070b218180d554011079001000b80554100c1e18404040c8805452803641aa4080c1c0495807d100807226002505000c0e84407900c00703001101c5000784120100c4200000781c000f101c0c6650040b0f01400801020203102412288030003502a041c2007644034840d4a01c10707000c41039640b05811002c1800d200ca40c0f1190710341000c000d41b000c2900e681d00e655032801c640305001a0701340003481c900380d64150b62050510703003007058004003d0100c9440d104019076 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 701477598 1250 701476348 701476351
    0x20304140d020d120302030714130b0c0f0102120a050121140316061a03060103150513020916020601050102030408070b0a1b030e130e0303040f11030d02010b0a15080f 73
    0x9078055584a03d45001603404180903090351110b4030301503101c0c142010050b20b0005100c0d80c416000c9428850160f090042c14045001c440100e00459680d94582d80744504259100c1a1360150303600029503021245c2506400c2e81c801d5000c4c0b00304021903621404012051a02490760001090700381c18a000421401024000e156207010100d9182a01c800301e841c410012581041e1402c50b82d910390042c0894014a00d4481440c00314090a595811a43ca54007055100c2c2d0983c4181c0e9941d200081d120300ea0f0020b0801110340050640307003503143c0840760f03841e82e0003801c0c080700041c050600006050b500002c00d80b03080d155600d000d01881404c0c04101d0100e600040b00400400800c0d082241c0b8114906503040d191034001c0e50f0300002c440642080c4802ca05040c40005006440d100c3d00d0f2114040200581342c01035800b04004000c12410300f0403441c054072801055a25000b1034540404040d015403101c180214161450f42e8035941c0e4065014580f40c4100ca5800480c0910300010341da400c5140ca440d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 701478848 1250 701477598 701477603
    0x51005010b09031c02010f060b070605010e0702190303021e0d0b0402031302091308030711010e0706090303052217010b0316030b19050c0a022b030903030f02030f0610020304140d 78
    0xd00c8011f000d10300b802c0c0c40240d44415980100050200f007400658040d050161803c030031469007900b4601d000070f50750070392019070b5420054903020780c404140c426012a078804c0c101c04000120b40e82880d0344003003d5032000c1400322007503107015a005214205402130b00e01c10100094180d0078081355400348800070710700415070304c004480940031800007200f080c003031805250150346e44800350661304191800c4640540c0072442540c042941046001e030700c0b09580d010b0b03e84c9483d00940f514801940800300e0340503800301200d28071034030f140030913103601c400101002000501c000b4400c022151042c15110a03020351490ba02007800c180620100350340140e4150004800c0000d1a407118010040804450b02518240c6580b403002075144800342c0d04200c101602c07000400a40010003d001019a5031140940b03a030060644602200d81818000d0b804030010701c4200d0404d558030300c2c009120b18104c0c0001c0f10b000d88254410020b95502510000c2980c00365000301409d40e4030f0100e20301c01c110300c2c0e92008004 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 701480098 1250 701478848 701478851
    0x92117161d040f0905190b01121e05030a1403060a260102120601080108060f01031704092f1c09060b03010207031d03030f0306040207140604051005010b09031c0201 72
    0xa407070503031640e2140d91024500ca0000007441905450414201207030700c1c1b94603a80c40001040000400c507081140c0b0304541032502c6180c8241c000d4a80100d101c01c8600000f22800d9a4003540c0e4103120003c4004d00d040d4410ba40e6001c50605051a003008a010588802e9004141c0d110140858032002c030b111410b0a42505c2100790310360100201c1801da900084669124016030400c0c0180c07540c000800710301506c6400c010341090302d0401101222804148070180005030240010842c1807054030450380541280072043c03103d030b200840c1c0701010221401c02c50aa0462070710703a0005002c0000240c0b40111b10424200403800d0b003400040e00a024011020388086a9561a005c1269800d2000302040792098980032012031340e071010510581d0030b0011090185c0c008000032074404080d071084917808041183c00680b00c010a04010b200440c52510f00307401840f5500130b10060080008400240004108051000e40e880300c060351700074000c81d90b0300b90705503010b0310000151100c070004201c07180f0080d200 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 701481348 1250 701480098 701480147
    0x100f0f061211160f0b0106080103020f130b030706020303091002090d03030b01050d090b0a050a150608041401060e0f24010e1906030617012d09211716 66
    0xe644010310900c81219030b81907044d0180200030820300307442e00410702410144807035859900400c100c2440d4440c906d11072003070a03402c0d81920b00329038418405c0010107021608110f13100c1001030350341d034415180c1d1085841200344006542560f40202c401ca40d802a01e120101c1e4510798054000e8140902d009050280c1070146088004581c8500c2d8a940c1c012007170081c9500f0f100e00240201d8130060295800541400280c002180401141504550840c5064682c5540d03d003410070080307a500703a0b1040a54203043c00003440110f0104101d0198111003005c601c5910b0f211036901184484840702040e542600f00081c1e000d6004101c006900705014021000b5034940c0d08030b007002501d40741c1000700401d9560209000e4882c4034829043c592402e06c1c0204004002d03440081d03030654206103000c485010340440011220000d4000a410343c0e805017803620400c800802c03145480f0701041d401e030000364000340c013001c10b0040039034505d00513411107180c2d00b00d040c800e00086542d20440c984e040990188041c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 701482598 1250 701481348 701481367
    0x1a07090b031003030807020d0912051203070512011205150702031603020106091d03121b0307020a3807020a020d12031b02070b130509100f0f061211 65
    0x600540c4502d082d001d4010610f400d5190261040f82c0140c407200842d440441080030450f00704610405540d030515101c0041501131030994070300104150700101d02d050101c140903239190404050300e4502000510b0b80500d81e200c1c3d89043c8100800500600542c1c080d60040080310b8400010742d0b000010b520649142c00a0100c0c81d0b80c0d00c030102101200140c2d525202045400c40510580c021404519101d114915001c43d001e0380c0da02031001c4d110300413451038010a1424440006e01d141c814003070428192245001d00001e0b440d029040b4080c2c9400030001c41d42e0309a901980740300707904500003400c15005540ba40c0c03202980120018100015486000e5601b409652402d0450207414420880c20a000e00c4591004003a190700720b0207401d00311b8118032040005500450454166542c03000480d458201c05185d980101030558480c1e074220302140c05000300c4c4c2c181d0220350811340342d0b0114407010890b07803000000c03c10152441213800160716440d9984030510742d230304402c400c5200038036540e00384160038 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 701483848 1250 701482598 701482619
    0x1e08090c360411150a0528081f0b07150b0d0804032105070b1503011d100b18130609060c030b012610082b020307020609040e01061703070507050a031a0709 68
    0x1c054440403400d880200240b10568403006603400c09c3d041c2003100c0807803810201d4006030003207110050a9108502d100d00034289280d20194001c0d80060100402c03070320314100b1101c2c0707030310900080d0b031074200c9200400f02240700c451020b405d04007517556992030400c1d5500e44601040e0041c080c0c5201d0310703035500440d516980034011800c80c0c44121500380b102c7c1c5000d442c4079240141d611600003180b802c00d40310f1140f07a5554034841011000790a02211070360b449040d08107840c094010020301f5180f038200044180102a804800680419101005500f07065001558145415036502c0a4901000000305010100f06852500702d1070810740c070392020b500c402900e810304220b8443e81c400420441a015890084101c4242062501c0d00196140c20b22503004030b82c0a03c20b444405000d0364444440708003c041c02d501100c000c04942000ca080000062005602c3c0c0d803012a0544841c0f1941070041103d1810146c41c01c112540031464006042c0300c20701000b441c0c24020060018803810400010b20300001 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 701485098 1250 701483848 701483917
    0xe0d0f060219110c0a030320010908030402040b01090806010909030c0605090a0506010b0307050409022802070603111207030b1804031e08090c360411150a05 69
    0x5680b120200300412040c02006894003c40c9412542c0c0500500180e603203d0035940400c0d6034051034102c01c8804003031250766010102c00620b031307a1036180c40c03180402d018404025501680c03084806114400701c8400444100c1154001c1c60020341001d001000250543d41c0302100980c840c4c2091b28044c10340307441e680200c2e9002c0711500c1168000010b00001c11606000d014003400d40d407284d003400d40c00d064100402d41e000e540685083c45030b000034a44640c076103040307654541081c1da950361b80400c40001707402906c03034000303100d00004a41072601c1d890365504010240c40c048107682280c40e046980300312046000e0040040503035044203848500c0c00c01d0029241c42c280c8190701984401c201101c403050550000580690300c441040815824001e5008012503000400c503401c550f170001d0842c90b01c10162031251100010030143c0b030640c0250b010441801521842507000f5403c0c100070354050000d00000c1d1000c0a404103950204200d0341507030b80e000303a005c2c103840341c48d0042e1408085c2d0781c0a0150004000e = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 701486348 1250 701485098 701485117
    0x307170d0908070f1a15091b0d0c080c0913090609051501061806172e0807080712080c010b0402160c050a0503071802160c0e070507030e0d0f0602 64
    0x3c2c11130550040c0038805496803001e03d4907540000d41d901e04000400907000c01c0840c1030344140035460104180500d01e0301042503060300a8112a5a104ca03401c0c00c5000b0030303440e0780500104d0b40b07035000540510300f0030050740d180b641c001d0100a00c06403607071070007002006000310454180d82d8030031004021a40821900d505100749822040065040180c046c1c4000781ca17403807401c45e2483d81402844070341d600450724840210540c0d104101500c0380c6d80c94180c42a145c1904200d40c40058100042603d20390399640d085401c4001583c001c1520341e0441d58071440580034400c0c01050541c7d00e0800200c4003c0205010318400707000094025402d000907082c0d90002400804c150a002030040501500903c03040041c0300480e03080403050314000c0400c3c3c030b4580710300c43d488401c505040e40c0011150560101c1d040401e03139140c164420305681c54810341c140098001e01080c000c0600008040c2e07409001280da14a0301354541d0f050545010041108030010030100b15000b60b40114100005941800a0881002c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 701487598 1250 701486348 701486363
    0xa06030816110d1a060d051b01112808090301090303020405040f05100b0a1707020706020706020f0615121222051509011b0303020307030e0307170d090807 68
    0x180d0b402d04006402c2c801c0761081c400c0c0802c0707044000003070f030410002c01c14030b82907000025250f80390000140c0c030b02000e210180c098014865100340c1c01c0c907095000c050500098890018401da02d40b1026a605c81025002c03294400c0e403940380c5403150002c40c2140b4840d2040030340c0c078500040709001c64203454890300201d000c030f40c010605010070300c1c0600844101d11000002080b0b2440c02d20621902c100170762140b1400c41000043c611002d038414122401c18006c00c40d01280705040c41100203586000d60300c1a80d006018500c003b03d9814400301d0310180f40ca001400412080d180c2c0d02806051031048a41550b0154044244043c10070003402103800c014031610a454070307420340e81241414805c2c07224243c403074402004001e104d560342e500314030201d6540c0b00f48100e464080040040e030300c07100c03544882d54801c60b0754001241050f5064000714400d0f80c1559090001000340140d1540e40d0050540060000318034410254040400c44c020709071450348503002241042040d01c80c031410b40d0007040c0030341d01d0f170 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 701488848 1250 701487598 701487637
    0x90a05181f0f020901020709020310031a041b1a0a0504090c0305070201230a0b1903060e1c0c021002010f0609020c0f0a150b03030417010203041a1e0a060308 69
    0x8070701c0d9100b02c4290345000340c4154544129540002e454092901401c40000e03070100104148101c981c401030702550703010600c3c6d100802c441000c5000098115811100c80204200704400c000791000350608855a0785041d003501080ba041114071600101c820004001041c08000340b41c030001d00504031a2800d0381c6000030f0345d0600210007170944440584250301c0240c46c0e0041c55070b2035003602009501610854000400000d03000c005410001801103c030007006900d00c01200b8000725074001c0225460315402c03203100c5c0d6400b030b152000c04100c200c0000003041040f104040581070030701c81d10745e07040028800090110a070390a40341c1144c505070819214240d02040c0f054003000104448040e0414900080c5002c124a9030b071a042c5808034407544401035181d13221311107562020410389000d0003001c050501da0040035582a8001c1d0004c540c103540140c1c0d415901c10104841c40c2c2880e005a118480f10701a0011040e5188883c010141005214540d24000040420099009090025002d88009030358 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 701490098 1250 701488848 701488903
    0x31514010909031106070203040b030903040e100906080606010e0103050402030c120d0329060a110d0305190b01020c01230310061103031e04061d07180b090a0518 71
    0x1000034000004c0040e4480410700c201c6a800005560403552a0002c5554a507101c1241a045028030b600041c1300303c8004040c024031450b01c0d0403482c140d411400d800c1200c1980ca41289590700010b88006020500035102c44060394480d4020f198054000740454001c0f40105010441c984082e45010038150409660000c402d0741c1802840c003801490004070350305110245610485400d48a0300c103209550001d800900580620403d4030291000d0f81034502c4009603044c003802a1108942c02c4400140503560b0b89401a26849044100281070f402402025944001034a0401d01ca1025a049031085114507000009c00001103114204034613030100750600e8001c015000000c1044a081250414070030080c46010b404050111030448104a03040d41c1c41ea03091080003080e0b02c1c1007003860700701e0f003012078488030200050000c101c9290700302c0595841001c415100844040c658020b50114440c0007152008000d90401c030b030014919189410f5046e1002504d0f4680b802814000a4644100290582 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 701491348 1250 701490098 701490107
    0x60702030d0f0e01020105040b0f060d061505043c0603080f180108041e14060709050a091a060306181006020d050301030b1602010b030709020d1805030403151401090903 74
    0x10740c503c20b00007807100d4105603031110000f00004219401080300d2800069903a6106440f00c8019034110508220301088c03c1501d402c588054083e2070b0259040c41410145c001f5111242c0358822035854103501c9071501d260400c40300807030b841e240740d40c0d007905e84a000c0017190611005201c102c2d026522340780d40740b402801d40c074843d0400908043c14050f90a0810010402079004072045282c9889000d8109402d07180417948d9214050806140384114001c01c6201d5400107c21001d403001100d030b102050395201d00300e4040e02c107001d06108107080c00c00a40e00503400c028000d1508410014a00b035000d803090031002c46000750840b180c0d440d80c01c0d903c008110981d01400f050f041480c06260032480c1d503056480b04240e4500140c010404d100d5400a13035048680f003988900e640c500b0007015256800d030f031809140003a4010300c2c104180f4502c0c120080707000752100d2584085807640301c0061806d203071940c4c48a081c40d2611400300503045880c2c2e601c15102e10303081c0f10000d001e0700145200142040340390034004d2 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 701492598 1250 701491348 701491367
    0xe100506030105010803040b340215030702030711040b040921081501080a0b12010c09050f1c03050d09140f06070806040c0513080106052b08030402060702030d0f 71
    0x140283d1400c40140300c01c400c080119425100341c280c4040c2e5a04030405003401c2185a1086107500c040c0f40c207d032a88207005461422800340c000c941c0d06000c0740c802c021030f103401d1005445c0100541c1c020002d0000054202c07007003400781c820003080050600c4895002c101a58030802e42101d1440f0b41004030099074446d05510526111249000026807402605d54070280c400c5d008030340d0501142030b00007800c8940d0341d0030044030580042c01c0c2c2e45540080d0a80d4a000c2d001c00302c5403201061024802041d40e050000011040b0903000f45001c4100350100c0c1421801050410180d0030488204400501040342e03024112205201d50940070644101c160362608040c0c06105400b240c0d00840c0a02190591094226400100c101d4000560140032201940c140c400c542500c510101c41d920000351040741940101c0484000741d6100f01c080800700d0540d09034a480b01c03440307a2181d84030314660b00400e20900c061a031080c03002d0505480d051031034002034506510040030f10006001034280d01c11180e071024500 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 701493848 1250 701492598 701492611
    0xc02010216090203180c1806240316020f070605071e0507060912031707121505010305010602030a0519051b07180212010905090c19060e090f280e1005 66
    0x10046000e803140000c8164a07078001d4000c180c0511f4010481c9607a8501c4940f6042c2e075100c000c06c038101c04d0354121a4840d0400c80310310340c0401c0d0204260320700d2400802d030700b007040c0f02c44005030090f941482020395941c0c1250300161042a59800664509820290820b5103d0b001e00000d00b80d1a02d8200000c164906a80180c01550f003030160420029412199080d80340413680d5403110b00b940c854034102c84000d80102200b80240c20034207070041d05411440744500b41c2d10203a0781405540c1c0c94860a9940380300b001c035a1800100104101c10a00b04501e040c452500c006203031240c03604d07032000300c860078a48800c600014590042481040130904001e130311848202008020340c1001781688030011120014030400303074010b0b00d420006400350410700c00b076842803100810b503c83c003110200c00e01d10181ca250280d040482d0144081d104549000e250140c403e038a2000c2085060307542082c8924102d00468000c40523801c0d07001000c03000100360241e2480080c0384001459201d075084a444180c41024128 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 701495098 1250 701493848 701493853
    0xb0a0f020a0206160e1003090506070e06030a0905150a020a0915050702011b0c030f030206010905040b01051210060920040506040e0c070510050105041505010f0c0201021609020318 79
    0x21040c858001c41c0143e407009648541a841806440c3e003070383c9492550f80e030701b648001070206010755242c060f84401d90550040b070407a035541e500c003482035948040060303405034000c50610000d03031012526040303803080610079002d507030140c080c461440c50250f4041c0d40c00c5005940203d240c00020b40d010704000002c120000c0d21240d03044010f072004d480c52060003006410003000c40c941d2001441c5004e07500c04c00c5e80d400b2141c03c41072a07403414016808a0480c0040f40140200c40002a421011340201d501643e04035100355a00d900e00001c0114030445480307004804d0003610f440521044191240c1c9005042c0343c01d01003404e40c6c0c80030800c0c2c012001c81c403040f41035010500061265865010540d029900350040c0c1c11069143c18030148401d0044400090180c07141183e001e06036001600b20301c0c100d81d82600e0174400b06016013054007221a8502800d07000034031280e1520340c1c440c42040c0114541d4011b0064415184039558a200d0b0141a500500d141f00d0b00001885003081c51092541c0740042c18101 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 701496348 1250 701495098 701495107
    0x3150403080f1515041a0903100b01051801031d01060503120c210412062913020906091903050d090311010819090302010b0a1e09090609020a030b0a0f02 67
    0x3c01c0e144a41403403904600400d4490005030040b134104080f02c3c0503200010380b0904a00400f024030b0156403259079242d0280c010113a1019038900c0d030b0b000c0c0e86980b49050b111141400c9001080b00340384561005024105034440d0458415241c0502660040116450021036064100024103181014516062140c200200b000205115000c50301c924424214400407200d111007841060301c900498004442c055004860f034401c01050368051401494a07080b01d13500000c01d40d548044010041540c2c9422125140907a0b00304005030b401002d410b44010129410400b2803000b1404e964480c5000600505860500744248039040140304400303821441c04107900c03401c6640d917101c07500f241d0394020705100e2180f01058203880c1c2c20100402c4100288405c010401e12410001d0180c0785181e4400e014005035400030a80700410700d00c0c0c100c4804a0414035a456192285080c0140a245403e4030f03a1652620030900680d07400c00074800860280501c0d00703040c00c00d0000344080307400c1503641e490303198030412 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 701497598 1250 701496348 701496361
    0x3020f120907080304050603040f0201200303151005070f1502040305031e030402011e0e060c0c04060f080d182114060f1303020f0708030a09050f0603061e03150403080f 74
    0x20440360b0096110004ad800d802891006864103030403040120100d00510703a339003220441c008059849007211206410140110f44240800001c1e912481030000714200706010220380b0104100c0c6960703104815400b01001980083d500b20703000f90704102c4094000040a0720344c9000d105800815030150b464a603d5030030258001380001130206110f0740314124245010545600640d00b02c181084050200d950314250f000d0310b00e072144030042d052803065141034408511010303000e0140c2c0550301306030010034074451003101c1655004070600b070712242600300a001180c1c025190340048030080113454801078001d050710b0440c4d02812601e00411081c1e11000820040c0390000901c207070050803000381d2800780003c508040b4245104101a08814821041c0c0056080000001030a544e41581d40303000314103854030100070691014803002030b8404024004560180740400507142c0f4452a06031410400c06030002080c1400362051031848031003622001c000c20305801000582c0d104002100040407454480c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 701498848 1250 701497598 701497609
    0xc0703030314150d1104180317070f031a0d0507060807110307150f0504110f030a111c054603030f0b0909101d0a021003020f12090708030405 62
    0x2c04800d80b0580303130700f19000188071184000c01c0301d2460140c420b128000101501c1c030700d85d40c9170010807000500301e1905141e01101961500340030f80c905a13120403c40b450181c1c110b01400352103480c64201c3c002d03625091544e945032510308054500c918058802a4039240b0003620001c03008040005000e841c507101c0300c2170074010046540c060b40c0300300707036078021210b05181f0700091000c81c0d415011545058140418840c50b0491903104040850703160b01c00f510858185500c800c001c0d00010200a41600c03000075a140c20003c001090903400d65035034032701110361500740c41c00030328400c5102d100ea514908171207070400840002103c4d62910500714174070a04182d04410750f4a1064000d800c01d9907a40b204083c10340144c10504030f103c0b00502180c1079040404205440c1d0b1404008102d60a02d0925030a45940c1445400001620780c1c00c00707480c03510038580070f1108100d982c0800508040c5c1c00c11507803040300013440107082d9482c2c180c2e0711231703005292580d1200c0c81e000c003940040000798024401000240d551 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 701500098 1250 701498848 701498881
    0x2102070509040c1d0a0606020c0306060405090a1712060604120b041112060f0604050603190804180e1213050f040b06030403020a03030b0117060607170c0703030314 72
    0xa075030264095a40e4180202e031a401d54011440c190b600711441e10000f140703095401c1c02481d9000c0c082041e942e03a4031040c0d0766800c5200c1080c0d0181c0103040013034014605540007550150446055400d41e601030b13520012070040350101881d085402003048030300d009000900340d41c094401d945151515083c8407968801e4040384030300802031800d4a00103010048019504801c1034000f80c501e000c159603421a42c4e4441108032400303050713168410005800c5e45858056503018800203005050203441200c6135409142c410101503485240402002030701c0d03000d4142815000030440d00000d24010020401410f080324803020001c44401884011000c01d42c030724003813080761011a041c1101540b0407020030082e00710341c09001d90207140882003000f490340200f01e00c41400e10a95040012800450040d01e490756259045a200c40f40710001585508000004104990040501c00c2515041000d21009540a008126110b42000c00200101a010f014601c149481100a0780301c61901040342048442c8 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 701501348 1250 701500098 701500109
    0xa0b0706020d09061b022a09040303182121020d0b06030106030228080a0203040f02031c0207090608030706021c06260606090c220f03210207 62
    0x600062910382c406280d40b18240e200d520020510403007860b141c1580d08052601151805400303a242d00c1d001d400281e00c4841004440e0010383d1806a00e0310060200d4980000d00031824541c2d07031070300c81000d920b2005511010380d00c2000c40ca0041400290900c05440b03020340740000344807071b20355021100c0e03480c00146021013410010058a0b10703040b00d41200581201c1400d25000710b000000401d05070f504da0010076046a10010203042c04001c8406890b001200800d0500020988004510100c507580c0066401034040e0a80207007020180e0002800c00500c051018152902c898010310129010b01540000300070707001e001c01140b80780004603a128403450f40d004046903400500b0070a1807280089e0204c484201c3d8404008107074844150140e0080000322404002c92244254000e4010001c0d50710b120306030141100601c3c0c3c95440080b802030304290000c03072641404200c10041034852500e023600401c615240c01c42081d00c1d508000c0810206201401040210708120481103a00050060111034 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 701502598 1250 701501348 701501351
    0x40b03150f07120f0e010e07030b010e07050f0c0708120a090e280e011506230d0c021006050a0f15120c0216080c010912060f0222050a0b0706 62
    0x40e511034040718200003940c40f22500701d180070610030030340d2410340c480001011a44020000c2c1c06010341040c0c1e845006200080c070500e8588c0040c004c00d104468400d0304001c3c2c03802d00c1d0b4101441c000c00038080742c00146040740903910104041101010170401d0310400804c0840052800304000c80040114150340a0008900000404552096130301909a030760341d500080785941040c0b60110490142000507a620440c0d801c2101e040032000d400d6040f03804680c9651100d003542e030b11440c0342c03210302c2400d285150036840c000d11072000104542c1c0911460704000d540074140c0c0340c50302580c55007110b045802280c080cac1c0b00140240194813000350030405071040c010050f14440014401180c4c48943c1c01c8034000058104804200000c1e00002c96143c3d0038607903c0305241141d140c00b0301a80d1107042c00d00103400903140603020030414407190340c2d031102107010b00d0000c600014592240c5099a2041c0d012584c100400c1801c850001d201001d408003501c1d00701c400c20096880e1200b50411409070100c00340006 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 701503848 1250 701502598 701502601
    0x8030a0305311110020f25050f12120901080c041d19110a0f0e03060a0b0303070218010512150412020f0601240c0f0b2703040302040b03150f 62
    0x803442ea046070360102d00082c1509407000004d80000c0d1594000017410b0114425080e80706c00004001d02c410104181d0b407109200d005262104008d862a440103200360010046424000185070900c080c41c0f075030140b402d85070303a0b07000d0b00d200050491740014a0b40764250740a00c0180144085031491800340c50118201503441c3c1c462000d07101d220a480030007035601602d0207020b42c419110440c003400b90b00e4102d45a145108608004c1505c1d01c5a104140c1641508580f0028280401c0b6600000003814090201ca062625943c040f4030309038203101ca030158044049004000c0c1d841c02a010900200108002d0700a81c243c07003030b81e0421954068402400c4100c2c0e042d20940031882044184035040b484811a40256502e0b0100790482c1c03101c641561528000f49030513218140200400000c152f03204e01c07559008072040d142d00c0d111010241c01c030b000116030001c02c00f0301c40011580c0c808818403540082c41e590b5180d40b04220840b13540e1807500303000fa000310b02d00340035600700d661b03405911110540320714074103 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 701505098 1250 701503848 701503853
    0x23010c08011e23190f05040c030203060d081c02030109330e0615070f0501050a0905060a0c030e07080106090b09220303061203020303011502070320060403080408030a030531 76
    0x100c24004103d1a0a600f5408002030088034501c1707840444030140c1d0104800019140100c059110490b951508074591129080000f01c6400062100441d1601c592503a5840115150140c0e44280e0100c0c0d54180c0382c4100c0194050036030640c01c0030b0001100300200c2c521164039842c414203100c1c40743d0300c22420000009025501d508012241018000ba10f05036503907110314081003401c00b1a0700c26074040d8600000500104d03c14070403c0d05854001005005554440e4200805000c40300c04803010580c03214003400481c401001580f02408041c030003c9200b0781803826810444522280e054031605480d0240030003040d04540e8841030380c07980403001c010782e0440e00b426030207016140d0000d440b01c15000201700902d5404000345041c0c400c0140199070403401c4003002ca9590100d400050400011302035013290342000c10150702800d070340103803849081558a442c4d600d8950003035449040581c10005000c0e100301c2d0316110b0180e10400d075003036815070f0b0b00611004240b41c0319000c6040c0005240440404203 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 701506348 1250 701505098 701505109
    0xf0509010e090103081e18120a0605010806090f01060501050301090207050c0604060512090f0c010810080709020a02010b090106051b010f020d0902100c020d23010c08011e23 76
    0x1540805481d02d04556075030714004003143d01c01d80d241100f02d90304640340d03210281c0b080121035101c0829160603010038100004c00064800d0100000c040c0c2c891000d403980014018004e0034001d203d1a000361815191408a883c24039851040d42c0c1d503203900d04101400300d80c1c1c0100640e4103564007454010b80740ea0b12450711602c1e020700e1a0700c02e580400c01040004d02c079580500200480d07405c95800990a80b900e480c3c807a603541c100580c0b80a1500585000f0040b94400c282c3d1070362240d6034003075a41c2c10310b540750100b900b8403040e40c07c41850f080d00040d058ac090fa0302401190f0b0b4001d01540c05004a42c941135005203180038041c0300030114040ca00c9089070050094000440480500744110b42e6142c01001d40b8006004210003203004103412400d0009450084480060980d0080c0014030080700550702e0680071a007000c1d100041d811a52845981d82c6c0c424440c60b0603014140d2916002c0d541065028403140452507902c1500c01c500110900c0321a40700e55101030301c03000d01560448280111000100c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 701507598 1250 701506348 701506367
    0x30807050313061a1513060c170a0f030b030f0c040c45030b0a020307050f0d0e070b13140307030210030606030524090405011e1505010504060f050901 66
    0x2045035003440c0d21803c213410001d0034100740300c808032500030190f1142d40110305107004940c0b030320300d541c60145802c01800c0c3c029218000c115200303070400300d14038146600036011500b10805900004034203580d0801c1c1d09405104017018403904074000e1420603da00001c9940700e2165081b036002d95200c806a0b6503840c003c2424020022012030049034411910101401c0c50030001d0001d80030600c1d90b2914508040150424019239402c8090700c00195074160f0b8a03000b96101408100801c17004100300400b2490900c080c000c4080591004512421818804c0e0f1070179505400030101c00348204444100d00e005106810211031300308140351030481c900300003e0f04084c003e5201940081c52544005a1154154040405e441030341d1001c2089448000644420180021050900c0c0c0c1d8940d03400f030401d180030708003907600038400e2001051040c1c804001c8914030803211418082c09480301c8103604c003004500c0e008006003000307181c990308051070a0001071004041004c0d200c01e100000070080410f0f4415107402 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 701508848 1250 701507598 701507603
    0x71101020d11191403070309050703020a030f060f0c021b040605060316090918080d06090608010b030f030906030f15040203040c060e040e030a050d06030b15030613030807050313 78
    0x4100c0040c00082400950340300003054058043c4442c14a41c0c003038003c1240405001500405508580c2c81c40d805400404040c4010b039035622444600000603540d00d412040a50700c500004200c030b801500d4803106640007540d0742007003181800248089181c0c0002c00200b0400013904950300c0e440c1840c0410000d10003500300c3c0d50481d03030000c04c00c40b004005241942c1081d81540e20300005d01d40e14080e60048542d010860f0544108142d8420041503104015211180300034600040301030396600c1c4202102c00e5980071801e1a5180d1110380024942070095a20840303c00e005540380c445c01d60002a141c5c80010850320724880c04402040c00c2015641c040703000c51801900031581c1e030809051850000e9007500c074803000038600d5103401c1500cac18580903001c03165200e800110704141c059a000e559982114610483d86561a070740000410084030f10540504201c00c0045510b030558000d00d414190014040003134000702c0520100000c0e40081c110754010924504070b0748030b442e451725000b41040d544902 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 701510098 1250 701508848 701508851
    0x51e0c0301050606091e091611060106020309090a0e010603060e010c020a26071202072c01030b070318140106120c0302040513050a03110616051e190203031009060806071101020d 78
    0x20000a284550a023a440f8001da03100c05450b20741c0d04880c0b81c1d46600c03d01a110050300b0a01545040d4141480c007d90481d019010200300704c110085854215001135200340d0750307907440e4406504c4418013031042c0d0360006a5403003d49801d60a5845605030300440000010182c820200c07010500030600051300c1c01540c0c0001c0e003008060f0750317082c000e54440d82801013100c03400711040d141289020030602e81003265080341008019030f10715100d03802022001803614003411340702c100c20a07004450080c6400030f6485001034540b900d00c006202401c40307a56030030010716807980000346404161003008007400c895040310003092941d41c080425411801440740204a03100e229002c600b015040f28140100102e014102c6440d0350b20242d40802c1005103404240100340104801c080c0b641041c0daa9100c0840c1200310079152101010304009c02c9212081c412005030130210500402c074410820400c0100451030045c0042d41c07c2003841600c1c0c5601911070b4042c0040d507030300040d00800a406a40484002500 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 701511348 1250 701510098 701510101
    0x2031c090b0c0408070b070b19270b01060f23070b0a05040605070203031003032303100e0114090f040303150b041a12160c051e0c0301050606091e09 65
    0x10000c850f40184c012402c25000c0d1050114100c00d002007594040d40c1c011070f200c0042d489240d05041c603042c440001002d103e4860f00800724411080d44200608041c1c82c8a03c0380003d018249801c00c02c40681081081007010010704000035440b0101101d40c036610038001d08080745056182d82c03e441a48802000d40d524201001082090f0358404e5204070b000d46003e01250351400022601c9200c00c4400c2280403030b0840d400c1c07000c00e2181808041f40e101544084139407009280b180c146c0ca400803140d002c0032208001060015210300582030307004100c0c041204103290307140d1b03000451402006121152a401080c0040c09043c0319070400d281c4400d005d50441e2440d81c90380c110300850352041c02150f0300c21803805000c10016070711104880c10b12644c0c44c4c41400c5601c07410700c1300b00550980c81101307003000503100e4090003083c0c0500030780400100c40b0209048a40403000800d040415030301c0a24402e9140074100009a201c44003241d01041c02110314843c014a4521040385003900304076000d410904620 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 701512598 1250 701511348 701511361
    0xc0f0d14130f060f020c0301060630090b061806030a150b2e08010b040302040b010c0818150705060613060e010e0a0b062704020c150103170a02031c090b 67
    0x4248450a84c2c40b0b6007074500000c00d50050602386c0e001c5105a0380001c0e0111100220f2076001c280904101c0d044600d0200c21411174880d44040c2c0b4070b244016a5070314501d0081c0f2280f0318001c44a2400f04804031032410441c41e00e480065283c6042c040007500708032080026414850140d07005414005000740030051007180d0008021908003000348200e00392203004a45800c3c50302078803006040318000b0703d400d46480e05517401c0c00081e01c01c002c0c400381070204448641d40000c04075809040350001c802407002d80110035008208618400009070b4425160822509000c00c10116210b94020f1041d19401c0000c0d814410607030043c00190b01009960400700d0000c201000d1b01d00020340600554038040c03018000d06002c0010900c10100e40748005210050307840c1410824840d102d80300300c402440141080c0094481c241012082d0340341840b0303070791060014801c0200100307039082030a546559090501c606c80b440650340307109900007403c5520424400b00701104442d00108001944040d05d45920309006 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 701513848 1250 701512598 701512607
    0x1b0703170f1006020f03090f0301091a060103061a07060e070503031206030d17010e0c160f030206101a0306030f030a080709060201020304030807030914120c0f0d14130f06 75
    0xb81c400c2d4040c4695140300003111440018200c10310071102c4042d6207404400f0741046109040c05141c01d13015520b4025420210b000302c0c40710111030140c41c5007680d40d46010300c00102140d1150b004003100440710345142c1c0f40140c1c10403c3d40c0e4601d5005100141a60003c000b292500c0c0e000d6110561512000410a9280010541d6903010b04026803c40d00f810f28640016a80030b402541000036044460004200740100c10300100e070403140e800180c524002a4070b0100494400e08502959651070220700a0b040650420419a12032618207405850500f408104090075110360410032243c000072010400360b940030b01070f030003030601039004070707a5030310a03001000e040040304807024004116044000034103540103000300e0388a1549607841003600d40e2200f5058008014a510a9030016403110702c6540781c500030840780c1d00c00c0e000d07044619142c040307003006145001041c602040f0710303801c408040d421950b0400d64502114142c2c1e6003241d1282aa0880e80d61032409691044401c0000100001000e46c0c11 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 701515098 1250 701513848 701513851
    0x102040302150307022a1512060406050603060d0515090604151b0311091002070915080304030f020d1a010906060e0a03080a03060305011a0f01081b0703170f 69
    0x2d54680416400002200015000803120390000da0843d0f0203070001c0e04080b5100040f581520101081050401c60110710001002c0102405075180000d01c0c0e13444005201c0c56650048045070284950750801000c2003142c040a0702d0580200b020480d104200700040c440d408100c41165490061132030048241e95a684051311b0644130309511850604c1c02c551140a00034800d40400314013a045517003001c00b04c00030400310310304485c962820310090000d60307506202034012202e0765004062082c1882c00c40b50440e0030001c0000c00c1002c41c58410001c0120100982d01221b8000e00350410044050020442c01070301824014004450a541800c8040e03284036110305803078000c0410044107031a54001e403002c02c945030f4400c2c2c2c040602903040000a003103000603d058034983c07401040090380e0390766003400e55100350f20080044030003840c501d140e402c09001100480c0002d2078400d02c01d09205c40c2c8a01c1c10680f001c100080350b9400a009014180030b02401e035038805500d48001141e24040e0f84040c140f600 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 701516348 1250 701515098 701515103
    0x11709010504020108070f0e090402061b010501090f020403200a0e01082b0e090403050c0706020a211407020409080d0203070809071d0406060b030414060c0f030a092301020403 77
    0x3116000c01c4040740b290940f00751f83c81b46900d0307003009034410350100314482e800100308071380c00481045a084901103c11841c044412500004a0746505064000e0103031b801500350806c03058030610082010810000510410740d540102035a08101e84502044548081c0e41002050007a280c0001401d150000b5503a003580c104010240845410301c003250840300c0e805c03507078040041c080c43d40f0b03c01c191500005854000d80320741801c0b4038005076a800542008416403041016030071001121007809040c900307011204101407000c20303030a03010420151000d100c846400500c8000403c00c401192166485048100c5d08004121380356000707102418042e41c4110759000024001c040801c0304004001399440c241d450140120282c411507a41d070010a1100900c255815526103400003180019600298040c034010b8044244030110800a1880d00b00090840024640200110307c0c141c92010243c0e034000590260110f01c001170741c02c141d01c0c3e06200c1202c5040d2460800c01c99a03941030158010320441b032 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 701517598 1250 701516348 701516357
    0x1e0302070614030103030e010c1b0e0105061e0a261906030309090f060504090c060216060905040b04090606060917060112060c140a0f031413110117090105040201 71
    0x25200c00d0200c1d040341032075182d6041814140700600000740540c0000b0b800400601d0300c030814a5480d1600c014003240c0d401e020345a20b01c00041444881c5800810030b003d084161a03492030194130122200b05460039404440903084081480364086215110340080507003280552501800303842c1e141e0590f030300c0984110300d40d8ad441007090030031b8040c1c074014203048a4068075001d010170700d02404900940715950007041039035903800c0c0104241c0c0d41e82c03292159090240c8101c01d80341d030410700d0284c603107415a0440d25240000220420800b54005042c800303641050f2030110b10518030b50003017400742ca00720740010400b9040a0b400300c3c0b041d60003042c0c03c0c11102082404035050340c0c00451151070340404c3c094001410014554500441c40b607070400b0720849018500301209814282403000d998028010000005821040b52341c5c0ea5603150142d100700e090303286003090321400e00c810600d00000491382c0003030144100c40314041c42e90703000d14456244a6200000c00c0c40c245032800200e4001c08084600f00d0200707 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 701518848 1250 701517598 701517613
    0x70315060c0f080318030c01050109140f06060f28230912150c07110a0b0703030f06080304090912090b27060705060411010e061e04031e0302 62
    0x2485a03032007021803078004195001450440e00d8018203503000904081d20005583e0111810800030070003414060905c2d400010b40c1e50500300c000302507810f0081c040d401180c2510178011080860004150851400c641d030030703940c2d143c904180855020f0f83c40c1076000006102c0400011115145c0741c40904030565695000c6843ca444410700842c0c040305112402c44014005c0610606040311242c600c5c5142c801141c143ca0080f10b481406440216501103103840c01040080801c41c04001444000c2800c503036285109081c00b1400186000340b03e8090308050701d61a607800c5201043c0e00000142045e6019296141d4907424401c01a1580245c00c80743c1a03103070744012910f1841040c0c07140c01e80b10a0840305281c01440ca0f402201d500d08034080d080407004181144510b0390f0758034003c1003007612860240504d4170f81400e01c0e8181ea18000101c9044c4041c50012169903901c81e811101c000d10304000c101c110001520444880340100d82000344001200000d6581103540c035141210520b11942c07c07203842 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 701520098 1250 701518848 701518859
    0xa0b0306042717190e190f1802090f0603040c09050702030714070e040224030f090d110c010c0c030503160b18070306050601121a04060b03090d180e070315 68
    0xa200d01c1e51007444120083c002c40b03031814842e00c4170000301000140929414061501d0800304094107074006004c5141c8002c04221180503141030b20040000f4507001c600f00120711002c00d2604d85515803051090200100160403c110816140043e0600600c1003202e4502580c2c040e60300d40c0402429101d046080380122844000000c07140d00751104075030b440105444560074400000e45e142041c2c010880349890f1800c0404812001d1849440720a5070b80c1c2e01410818102c0b8102880f042c3e26104104090000030b900003000034298800c50070a02e00031b03801c0304041c10b180c0084d48071360f0401091400001840310b40f60549040b900c2030300e4052a2048011744501c00500e001005003041440f03d6006000204041402c0340d101d2548004181086502480741c1c902506c1110100e242004006820304000c0301c00f402c00344524030160154140e0a0324604040c40303c543d0341d41c03031292f1203020070036061691400c0c085d101503884010600010390100c0c27400c000d10084d010b010780c500100840448020300048 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 701521348 1250 701520098 701520143
    0x61d06070e21070509060607050607020c040c0e03151302120d0201050f0f0a09030512190506010504062f0604060207060b0f010f030b03120a031505040504020a0b03060427 75
    0x72642c0c818002820014601014046564002000c0b40d42c021000d00180012030700500000e0f10030180d80d1b010309002c8010804010440b45138a240c4000c1000b0303184a100d603034400140d85009080c039a0001d20342981c606030309121259007a42c0c020b4000c40f5040da1154003610005209900c4c1001d60000e021a40c0c640045101a48040318070400526140f4007040d0540101c0d4880d2000c60701034a032042c0f41640d170001707031042644180c82099030f80b10a0f90041002080600c0f40355000802441d00301e2a10b4030b40b01000701580c040000d95503c04880c0044070311150341c0d0305480700c0d9034034005058404a280c24103040d0000d400200f01511042d080090031100c61402c0c039055141c210b416160510040e04a20040b001030603190b007020740620a594064403100c0c40030014210b000140d542c04503003810002c42400329030200b44d000b41c2c051403e181c28000182d6406580d00c042d02d406802c030b10b07100d64801c2d0009000c1d00c860384a030005240302502ea0000601041890440325008580c0341d0308040c43c040c1c0101 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 701522598 1250 701521348 701521399
    0x20a051201080a0b1609090603031806091a0f040f0e01090c0e15180901080d0212030c0a080403030902130219021f0902010c02190609080705010c061d06070e 69
    0x104070009031000210417000400c400c281d0901c0c545000d0b462070303894031512000c035074032034009030003048040a889a440184100d0b90303000e0700c031914080d241c45241c2812090711401e4407034211088840440d806150051180544006003070400300d000000323070740f890401ca402900380540d01e0803605201e07000008a010300c882c1c2c00c0c0c0352400b4100b200c110915000c1010260404506844a15600311203001282d0f80c0c0d4092034041e16010020701440445494041d24100c1e00a039043e1000703005004000b0010894020b85000b2405070410f012145e13250b24040380242105107000394009081030341c1e04d44d4005240c0c06010740900200310000c004a0f15041665a25040480300306441c890310108065045250020911244181040d2402d441c090740018038410300780d0343c41006400495005c00c003aa9002110100404100c4041d11310300d0b0074000000d204040e0140d002d403405072242ca0203030312198030361801c1ea680300c142e00a854417414821001400002080d402500c110741c10343c80e0342100d0700c0904114 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 701523848 1250 701522598 701522603
    0x1315080f0304050a1a1c3206010c0305041505040e0a05040c090b03070302041b020613030c122006040b010501090b0316020c06030109050103020312030c03060f0301060504020a051201080a 82
    0x20021070340781c80b85c912080021076180c014044014464182e010000c0d006140d003800c0c84400204100c584120054000c8480304441d20300c10a503180d17051020340750800110740240d004e280104135900c4c1401c050f82d90380f00ba03074030400c48000d5120004450300d911202420a41d11000c1ca1301350191038603007100701921410f541c040c0280c0d06900041244c01e150f036004495818000c0c040d0346285e82d60349c0004007103454030500020051000342c1801d682d554188042507003c1d1106d4510a5141c00c15100100301c0d0300000f5000f04190f2855010413074440c0207040c04031003c540401c1780c0002402d4211820340354a8240c808607424a00c0d00004541580030362a87c00c141e031501c042a50461b0394080318680720684011304a1700398002c420b210701c09074803a5801540640440c64010405524510615140c000c04450501d02504144188484144024112a000001142c58540a09100300028010642e039403003240c0c420b100003070236000185c000001e4552a007181000d03180d580c0ea140102074561101c803100 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 701525098 1250 701523848 701523859
    0x5060c0f0315010e030307060b130e1e011803050a0201050601020d020a0b0c09090f0403080f040c031407050613090f0b0d0f060b03030304030504150e0a060e1315080f030405 76
    0x1120081c200072a40d646142c1450700e2051100c41da80464115400b0300c500f541c0050319a450960b03142044400c000c0544143c01003001500418030159485804600d00303140703482c44640d50409030080035009100007000101c2641c9814209190141a640c040120f0f180554282000501c40f07600118441001c418541c02522000005542c0d500100d10300078010169502c05020703442c1d00e900c1b0080e211780700f401d10707000340c1009041a080260007440e0051007008081c0000c000c01c030000f42c4014003030b0212a80031042c02002c48658005a0910f44550041030b000800460180c3c040301207000c070304040395042d500802c00d091542e4069000d9803000e507072107078016804055040000d00030f14170850340640114000100c0302e00f103d0010341140c1c01070f1800e6002841c003080c188092588040018170700e5100d0304100e1100305207031000c40c4845000784510010b20406141c510301d03d03224010381e8a0442c0082c0030404c044180713100f1001d40b21350036019561051095140d4110710302c000004807001c1c1c0300000c01c0c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 701526348 1250 701525098 701525101
    0x31c0509060a0504090507030b18070930060c030c020304030209041205040315050406060e06030706050c1e06040317090c0f0d020d200d030804020609041d06010305060c0f03 76
    0x14444264440440b042c1002000c00000a618090b4030a42d4002d000d40d560106440703103d030040101c021a40a2444203030407543c014009060341241c0c92070201e80c13039040e00c1b1103a4107050f8100500700d2a4203141d031010441e20080c0004100c07041d44071210f0300702c031a28200614240343d403040b6502d02490000940065485003ca00450342540a1120850640c82c10b50314140d00c955408014050f018900300a00e81c035941031108000c1280a400060203c0d0300f81c0e108681380603c0080d944050b184a40c400340000082c08800840e2b0074426040302e01c02c0351030a0160722072600c5081d6500d1b942102c0c02e40015001c0d078000c92000071009105405030200c4c40050100380c101c0803c001d00520b80803140c540c440c0038030788c4406c01603e580021f02c100c02d00400101c020b0b0520245010528003a07012144d03c41e520400040002030b410080c5503030416010365170591242c020300d000c05c004010440d031000045140b08108010144002340850590384184151400303900c484005041c640190f01203210458400e00 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 701527598 1250 701526348 701526367
    0x80603010623042c3702010804020a23120303040803010306480905060a0302030a2a020d03020403020907050a120e0102180312070818090114031c05 65
    0xf04181c1c0884d05501440107003c0d0000c05074444104200302c0460940c015020074849510300301d28441e2040194061011501955050b070017004429180082c180040c4001090940d00d03810903c030050003150588250141500c0a80c9404030820641548a03015148241039a80008001d89014a0f4070000d014110307400c2d036807080c02420101c030340001c10200c02d51602010303a00c850b1510069607a0749643c50b41c600c0c60715811000c0e00151240e02418014003401c1040340761501011240b014100b0329006860b03440700c00002000e001101c0c45801c0350841c0c0707034214400f07a12040b1403a042450580883e80031000030700c3c09030260f02a521001c0d41c40007000b000140303807501402c010700444201e0b241c444480700c1008400c404580d0804440303203240c0e60100790190800303075921103401c0260013180140314280c03582500f03400794415400300a0041c0404141420380e090542480400202c0090100d00c6c0d41da101c3c1c2e13000c01100d00100c034180c820310444164120300440000c4a248100d00c0313035116403610207081d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 701528848 1250 701527598 701527601
    0x9020d021201230405240a0b0d05100209011b0c0b1c09050f0d050c071e0e070e01140a020d0f1101150602071e05220c08060301062304 59
    0xe903481020b548520712030801020b244a4074a5011280403045820306190415030315002c2d0103c00c0a41d50000300305440c00d410b020320f030300562110311580701060940c0e114002c2100107882e080000c00c28820641c0c2c529801100d0b4020701a201d1081c0e0b5150440c1e5282030550090102e114009840362625600a02c240780c1070200402200c80504008100d200c0d02c0f81e2284100e400d00f00c2c2c15505508010790300e40840380180546201c18280d032520ba8104420920034944400c0700c0d12403e00c20302003031440001c6421049240d003000b060f0300c41c001d018501d40384c103003e8404284808d5640c0080e1192200c0c00303040c45010192164115141d008215000d00d4010913141c01c000c0407c601c0a0000c084800c0030076010034020301c011078043e000810302c09032400401030710301803180d005001c540d610a1484030101904100c018200e50040307501c3ea4054010b4900315540b2003032154404502420b00a50342c1107203800085890080e2400d400800c103807562524501c3c50b001c10380c84100039000c001018454a45402d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 701530098 1250 701528848 701528869
    0x601030c060e0616140c15090d03090b070302070602010c0507030509130e010e010b04110406020a0b0601120c02030c121c05041505010e100e040f14070b0d0b040e0109020d02 76
    0xf40110303140001044c25111084088402143d040c2c001c211040d600c0742e010b002c8400c42c440c064a0700c2c100c9481280251941c2c3c06100c0049000320030b07005114041c144035283c2540100700d82c3d518a9910350705418025105c3c010344c000c0201541c01d000e5402e11891180f0202d813190781c0c140d541c1500341b10708103040042c6503042110051440c0d84440d10800000001c6c8607500310022007500000306502c885080c0001c4e5015905003041700c0318117002c20003500d500441c003207084a40c411804a000c0e6203480c01a91003004004000912074900304084803100e400200808580da07606040b02c20750f001c1240d201c0c1d101c2c45100c2c0e240001c420b280000d07030b0012a0075001340d41c01901c596515651242c115001304200c4400b40d0018400ea42c0003c14440303140030059032080a17048040a0301c0180c501900d96540c0c40465040081c8030740ea80000122811a0920164003d415140503c03651100200050300103031800000c101e00c80d61401d8090740100740144105282c440c0d010384083c050154580802030131802 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 701531348 1250 701530098 701530127
    0x6040b031f1712070f0201270312080f040c0b0c0a1401050118050f040b090a0c24020f0c0f03161206050901200d0e0601080a12020601030c06 62
    0x81004080408603600c066001d0911110761189602e0203148051070302c5aa540070500d01007040107840301051314002e181181d907030282009603c0d003884145038041c004032000c6110780d06607085d0340402048140780c4000084009940c030690380d40c884c2a440d0b00306400c2920018000d01d84500100a030300c1450300900721190015096548100c5c00e40ca07030846051900580c1c00843e555040140702c600020810208006904a000c00145c909410904080b04e000751007c0c05584a0000080480c80704000759421254050000e225003540c62522000f51900b80215040c3c00303181d1130041501c1c1d0310008001400882c40c00080500d030030b0440600a640d0b00070300d0456018003d090485014001c1036070060028040c1654801ca001c0303413400c1c40c80440b10007400180140e410841010020380b10480c81142c24070303110b84900d54511201c00900700804c01801010710728000c140000404250208007e00e11a0041e03545200c050414841242c44103000d000041a0042101e4280502840347d181ca81d40d41d02c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 701532598 1250 701531348 701531371
    0x708060307030602030f0604230714190f11010e060f040303020f03090c0117040f110303090a090b090604060b0d05091f0915051918022d06070206040b03 67
    0xa40342c0e02d0341c509a038812203550703900902110a101a80c00e182c8200d07580d03e149989888500941071420313030702c27000c0094100d10030070401207182280f2141c11803c41e802d01414181140e9050404d000280c8035403c0b003075001010a500fa442080c5d03010f010f000312504402408003920056032004100d107000c02010b8800e804042c0c0c24002618100e210743c0c001d41c0204075800062008004000004107512245458501a088000140b10000d100d003040f103a11141d21158100f901c40350320010918501a220406a01010760040090f08200e5581709510303840040d150880f1517914542400306036042c51180c0c218070f00d0100300c00d01c020656a4403a5403c403859806aa5041e140d00c0c02c0001c1a400c00c00010340a04e54030000388003001840140c220803241660301c11704c5036160010350946401000001c0c004180c3d201c0034000f0701c4509003018000d02c5a40104102d0600028082c044040350b13a20000c40900180d04402c4c500500c0d0a0702501c5042c0e9004001614080c10300c0303080c407288d42002e04208040c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 701533848 1250 701532598 701532613
    0x90f040f0f060f082a010804020f040f06031106030f070f021c082706060d050f01020301120203100203010b07150b0d05060a1104030c210602030411010e031507080603 73
    0x4481c00d0080ea00145210318191071500d0910300c0f990705026030758a041408003810046070182d4984091641440e203800d007000101e5654500216082c41c145191050748203207000c070710340120b09050340200c0035a4090140340000c0c8582d08140321991100742c2c0c001420141110024000501c100c8100565400358416201c100c8506280380c3c0c8000500e03903034400070407180d000b04040c0c1030000d094010b4071489200340b00400d000941000c1d4446202034105405035000700002c00522034100110104010100000c40da03d40e034494450a1101080c0c804078840c6c0038a21350240b641d40baa00070740e03060b14001d1140390b00d0301d54075a030703100c20407121a9581c135135658642c0381d101c89503a203510301c42c03141b54000c4000d8540b034074040240070200c400c140c0d220911840b00344003d201040c5203482c86019180d01856412080800500b0341740030540d200c2006094a00000401c4108160715804101011081e01e4401000c10150101a102c030b2103800180e010b20740d00f80c0000e210502c00d001ca141c10100140503079148 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 701535098 1250 701533848 701533871
    0x90c0e061518120a11060c0f1203040c081507230c010c0908011a04090c0f080106031b03080909040c05030d0512060a061202090301060f0303030f0b010302090f040f 72
    0x1d401244502510410030380c210301650400880b10340070500f040018201c030b607229649440210507035603030241c0580404240407844600c03c0080000011a103030844090341040300c3e80006942c41200c0417940000c01d48070000b0002c10001e0443d00500c251050b030000f07580c8007181200c500000039100c05480b01d50540e01031087c84100c1c010400350342c50b20008070311640e88801c00340051b541079021100070380c54040c0b022142005c0c43c4507601e500303c046030f005c40e0104c000e007019007117000640c2241750103480c4c145001420b69415840300c07007141d1007500056810009104089111080303484058150a01048814807500d4a074051581c003a10612a5035115512000880c3c5440080441c0c1d101080c030000d42c01c2030a50490581c1a403050080750b894003100d04102008140d01d03480c10761003140d0342c0c003c102f1262a40d400c0d0844c5024001c000101110590ba84c02c00170090860300c49070003291072500c1040f50565110380200c40c0c28000103400c0c0e03607280a080e001d01c0020000600054403055544041c1d00c00c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 701536348 1250 701535098 701535139
    0x6150c031e0203030403090e0c0703050f090901150908010b151b121e0903190c030512030f090703020f0f010903020402031f090506030601030b04050f0a030207080f01090c0e06 77
    0x41c0c0007095402180c680ca031920700a850300c411074101d4034070302c40c2d04810031417501c1e001ca0031140c0f650b501d0702c1c2441d200d08038819865460301594982b2640300984800214150f4007031900c0c00d08040f081e59541111039651082282201c2116250356000003108215603400c0309260000c1042c08a20041071084040708040c00d414000920325800b100344d40010580c1407021001403188403256007400c40707442c1958010010750b6a002c00c40019020418a090340741c00d010428003440000d5412005440302103620082048295100700c0d548142c044002000c10190100010508141c13580580380800315000d6100700000d02c0c50702c3c28070504100c110003000c001071710b55001031801002000c1d0550743c0403c1144001192441c0c54100c2c007401480d00307041100399500010a103045940200090400f5281c2d4203200e030030080c0c1801054500c1c80784440355801c041d40054490110b44001003a181c500c1c0c0e81c0d00745113080c0c1d10305440191100043c0c2c0000d1111100010398031740c10420041c0b000713a0869040305e0009 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 701537598 1250 701536348 701536397
    0xf0308160b01150210021303030e030a15020909070806151e13030c05010c2a030813080105011508040b090a0c030303020c16081011090a0e15030106150c03 68
    0xc41c80f003a0702c4050390801c2e0301005504555070301c00300d080d0708000c00c07060300c0600c00205101c050f08000307810144900f0307030328117103c0a08030a40080a1030096031000c88504060351200100c10301601d100000940313403510828045006c0c410051030802c06001c40ca02c140826080071580c00070b219804550750703000b02c040c0001412a0f6004c1c84252140e1460b5003010403644c4200c3d8085814003180341c1700140060b0359103004101c1e0102588100021506103189001c00013501d4100a05070400060308194004002501070103d0f5903d100901813030303803960b40451607515088950004208080d01180000d031000c9600c0b45d0001440c002c40303511000700d403584120716503c1c0d4400e601080d0b000039025503e400a11401c1b254101c0790040d01081e62074121200d95482401440028080da1008a4005540490215580002d008040c00c3c211a12182050000d0500350790103014070911243d42d24080c10306004580450380c41c0c1843c01c80c81040f43c03a0546000b80800401c40420240c20303651410381c03c9415880 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 701538848 1250 701537598 701537609
    0x403031a0a0e1e0c19050403060f1a030c010210021e0f1909031e11041a09010e100611070510031a0411030106050f0d051602060705040f0308160b01 65
    0x7056a401c1000803c0c40034a41c1c8408a07441c20821000c00c080200c0800c1120640c80006003030b0440c3e524900b50440f400e0041c0c2d0401411141060100410060380e034000c0075190704074400c010f5140022808043d50390030700031441030250300003101200f0b05042507409000d5090701c580078079440c203181010200841d4019075074001d40202c00720300d141d02450074052440001000c1d0500400c0305065440c1d42200318160706103095401c121a01d201300300051001d80c14043d0340094400c2c08100034100c04030a0031317003884541138080e5190100020300c4001481500d801003801014a00d6564200300c011241d484090701030005034468000c0c0000e15888012a40c2c40b11003042d600005c1141d12040c4000d10709050282c42407045084c0010915544a000101c904403a0541001682d64002c1c880c000001d0082c80070035030040d46030004100f0030007007010000304461b03500d50a803151940c41c0441603400d4020707030080d148001030302c00d02400041d00b903100070024200600e400412105440d80d48a03003220098211 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 701540098 1250 701538848 701538869
    0x120906160f030207060309021c060f05090c101d0f24120105060a0807050c0109060e060103031830060203130b0108280812040302070303260403031a0a 66
    0x70141a4184070481c041c0035685018441c003c12500061030604030910303104805072000c0721107000c009056002c00610904c07600184031919040b030755180c4035803800f104a40110382c12410f4015883c81110303840d09031903000c68036640805812060200030f0200180241e0400407042c00c420315070350180015a00c02984005070b41c0e031103030b0b10007885600ca10103900460040ca0280220040940c210b40b500c0d902020510b41680c40c4c18640005501414128101800091500c059040103400204040341a07070f020b0380b00e03186010009a0071440158103807180e0200ca038100315a408140016015185640c0020a0501148240c41d01e5503404c0b07a101b51007001114680c4641041005546030500d801804500082c1102ca020807000801c80440304000d44405200c180045040100003c02d482000c1600584032101c1c0c90146400303542e0703001c0c40c001034000c0b03841c0c0341c80c4007241500c0300d8011310100c48400185000da200d41d03070140e001d08081c28041c1ca01e50b82e60744070304d82c140d210906441d0081001012 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 701541348 1250 701540098 701540123
    0x140a0b13060f020403020d151b0c050f070825092408010e0a021203070503040609080712170703120e151f0506070c0906060807030b030f12090616 64
    0x70003104480980e044125464014841080507a8600080c480c05c2500300301061000c0600c0d1581b54003c18074194005210b500d00d00c02001680c3e40410f9405006202e603084900c0910300051241d95200144500c0d509035111440c00c0d2603006c41203e80d8580e00d41081e140418450301d80441200b610f030503003020300c07540c0d410480004901c1400d003114802014210002c20808201385840c030f88604072044040c1c095141c00c1503241c610741c0304100301c40406401c041500d441d143c1b2602c0040c84034105110306030f19407142c414045580e200e030002c5c20b812680c2c03102d4000d914105111441d003403034208000c140e082c0050300c40c07207082c070703040d14000c1034011020940501101e10140500002c00c0f00083d041012036208031050340a820100c101c07040543c0c0c0119007503a110000d5140c1154190f00b070341c00c0724103a076040410008003d030300003402500030860fa890520464800b0014035646945041d0004110381c80329041c00e40700362907000248800c2134040c0500d8503020310206d60a40074483e9884c00c4402c1d014111 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 701542598 1250 701541348 701541353
    0x15020c01020a1e030623150c0c090717151306031b0e01050a0524070507060e030303270109020402070b01031e030806010509040207050a030e040c1407140a0b13 70
    0x83c80b120120140c1c142002140d0508268000c05004008810101ba142000404450b500e600721030308003d13200b50310180d980003503040180c1c850803c1d06847c3d003d82102c101143c051400f030350a401f6080080c0c42e40040e296555800c40300c0b1030103194007468201c1200b40701501c1c07002c43d40c00303013401450041d80c0007030305051503912032005004a688080d500b144c8000040c4007540c1e0341c0c94050129a0100e80c5101c4040d240741000c80003403c40300c8442101036000540c04100035000c907100301203400341e0f00c030b40c001c0805c00c8050548a110444c0d1001842d00041042c915000c000b80013140502c000c4000010000c00b00d501160403644207920aa901350500c0c0c004204002d10940160102030151110300402080340ea4003a080150107132050b4140240410349043c1038481d5815650703015000700403a6124407444c02c01412401c00350300c1c030328005c0742007807105102a0300030340c1d154005201e4a640207140c03056507241c1140d2198400080600350040c451560045110203105030300440c0306d807218030161817591 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 701543848 1250 701542598 701542637
    0x81b0307140f07080709020a200c030c060a051e0405040c09051005070201050a0e06070c140f03070501211104060f030b1e0d11060a050705060a0e0a15020c01020a 71
    0x1450b0300c800fa4040c14080c054080041011011608010805611940d61b03a209a40c078191080c50400d42c801ca00c030402e131518500040381c0682d40c10076000e9601552014007401210311603500c0310b82c0451030800202c10f5078102e0354076844200f50f140804600b42038403480001d00b5108004002800100c0c00141409203143c40a2a82c81e11922030030018541030459001814500850111005200100b456600f05884000c200c5003038590100d01200c2c002c1d240c041d0308501d200e291005a000d04440880074030b0708e0900007030f0f10054500586034000542c80c04000101c1c161a0310361059440341d00d400002c460410ba02011304041e00c1d4988803d003992660704001000c803000d441e1041e110b450038003101c2c20070f103031806e11103240524207480c2460540280d00703002644210548280703820240000d1804899a8448054880103200701e09940b5682c0707440c0b8241081d08e401051820031904404c00580002d10f0100240420304c42c01d11026003401034a540c110b0882c0c0180c2c081c803010441c030201e9040c410420 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 701545098 1250 701543848 701543863
    0x1506030b060a02120f0d1d190506010b07020f040207060b0102120a050406140c0f0717010912030c0908060108100f050906010b0f04030606140315040807081b030714 72
    0x7a5103441c20300c80c4440009650798110038881601d1100012580d0f040409502201c0c80756860300014420800c0f80c101d810300c15010440e000c40d0034003032405100002e2001d981180c2c00103803c80010401a420204003100a612100c4102c0c3c0c002c10b00111401140c9690010f0b0407000e01031440014a03d034010006401d0050a102c1c0c0c64400d2010407059003031030303042001d9a040e10b0042c5015174200c504094680814490341d0901c11961040940307141c000307400050003100344d035091090f001c020342d41e12624609903460540000d04030b140b0b005490000728441c0e441200b9180740d51030008602a9182d41c0b50f070a049080e08840015009410380707074091452400b803100020010711082050b450010b0040741ca50744180038842206100044c0e0b954600340030010b480183d0f401c5071040004e0390f038030a5103055865900304424041c1c041c0008145804060708610b922071504007500f41d1800000d5a80d80b90b4030303400b003254524103000c155899024480100090401244985038101d642807060100c0e901d880c80 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 701546348 1250 701545098 701545121
    0xd080702011d011505120d0804080904021c0c030c14030703090c0e041a04030f0c0305130e150307031203020903070906080604060b0f13020705011404050304060e090601170a060801150603 82
    0x8004c010014171740d0b00140c09187c3c0403951901c428540c65034540055140310b02c051140c1c5c41400800c41c01e1040c10440c402c00095480000700f0414007064100070380650300180d088001040d010195064046200c0b4021680081c0b10714001900d5034190b507408080729100d4116000d0406c0400400040cc81c204030102c0e00403002050b10042440c2030381c0d00030f00301c00e51807554a040140316280c0004150044c015221b0303842e0b9507004078483c00c0d01c0390f240b41c0c04000c0440d8541d40500d0200c0042c07400381000302d0032034283ca410001d104100005035405034040e501c0307201c60640521580400041c0b0800a210301c40c003030011040640900e040c181811810303200424401c901c50b808503a2044c2c03140e5601900b80756290b1103e00003680b07034111400c1040c0104041d00c8048640a810380c2000204003000c030041003035824548541810032205024412051412156580072072607802d503079a1600c05480032550302c101b4410001c207045488241c0c1c0c0342521b40d69580d200d842000042c00340107803605802103800110303 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 701547598 1250 701546348 701546359
    0x513060503060a0b0a0e060c0d0e0d0302030915040302060a0f030b0406051c06090c2607181802131a03150a0b0d1a010f090507020d080702011d011505 66
    0x41190005000341d40c10302c101d1644d00707400101003110a0065104145040c0001e20561700c44140124850700c139034a025401c40021451f540c058101c2c90308503260411150994011420304046809000d11100348001101d8640c0003804000010780e0340d03078002c20700c041c466900d4004074540a44041c0995650700700043c0300e242802d2050150b40c58500c0e4840341040d01004154401580d03040c000020712618401070003603040d01401080c030381c5100208010302c1c400315144c040746012000c0525203413545e40c010182c02c0403507030600160748180340d0801c8011450000c552442d009465000071601140282d18444540e2640301d140c1c0c082604010b0711040712016001b4040c0301c01c80c0d1164581c514001402140c91595400a4442c0e035116248151040c42d801072801c20072420280800030100e000b44a202c3d00c600e4101804a0406994021580903c48540003031002c0000064142d9080c40010854000c666880d85001c00d0100882e0600d00320341e84207000003a280b15032420400110000c0e800460007003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 701548848 1250 701547598 701547601
    0xc09050a0207021e040216110913030f0c0c0e07030903030b0402070f080c0c0a080c040507030e0c01140c161d040c09090510020c10061509330513060503 67
    0x60b102c0300d9010030010101102c07005084c4219000400034092024040041c403581401c0303508100384401c5011200c802140c10b012550399885041c8113030811100000e0002d45070800601c1258083d07000d621142e889603144408203520b0301203180c41d0000c210788000001e62031380c03940414150140700c3c02101c2c1c0c8003a10b0661078800c1da40c8401c0d6040601c540000c01405000a099450306402c3c841c00e004082c0052115600c1c55561510950350600d6040c5140308518020228042c1402441100c1111000ca0b018041c0c0c5812000152212406421820350001041200180451060000403501030b0001d140e10340090400e81d001c03100b4148402c040801c3c2c4400000d0002040d030300320074081121040500840d480341113142032402c103450708104005035400401c0e0800303444070100362a5030b0110f000c0c0003044455078800b020098029100103202c003045c1100c0040c403190b451503003101ca5680411603255060b429861115031304400001c1880c001641c08038081c2040b0100d20983c0008200a00e82103055 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 701550098 1250 701548848 701548853
    0x6140a20031005130b03060403021f0213091d01050c070605100f1806051801150215071d090403110d0801030c090b032d2806050c0c0304030c09050a0207 67
    0x30742d809004251081d00e103940b2400042e103c940000c0101c1d400a02075a00a04242c0b80c00b030f658095103113040c1100d400010889884260034426a04070345070f0051030b84102c0b0b00d0920a403004000381008140704024501d90441140000d010b881c0c01022910104e55031007519061101c101d54001e000c0a50182070140c0802482c824003120605a4218200460303852080c00440c0e4010078980d0b00503500102c034006480c4110030f64206250403200340d41050250302c4003548040343c4a0318100319210481000300040b0324060b100e41c410705015101d107541803141da82c84500094842100311b8088000032140310350f401a000042c010101900d03c142409a255411a91003900024181c050403540070b82d24014800140c0c1d007088426240d42c0c51002c0103841c4405c0007014071030b07110001410074080c800c031b42b520329280301d00e00380b0910300d1010b410b1b282100d2059581e50364013410010340703241e0080b402844000020501480100000d51081c181d880d0030f907113070513801000d440000340480c0c0381c03d1051041001 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 701551348 1250 701550098 701550121
    0x50403120e030a050105070e15091e04090605090109020a080a150917030709050109060203040e13060b10050d15060518150c0105041a010b041206140a2003 68
    0x922403090030603940481c500c4001c07070f24000100402403c55030034a0b00381b001c0550052007500e0b06031400e4656600c4112100072000032481a00d6003141c200b2400e04030038203d0400100001103001c0c005001190010403621000306640095401840c542d556501000461034900760410040c61800f0240588040c65210610ba81d4050030f0038495070303600d6036402c500304507a913400c1a40440c8114281d030740300d050884000700440361500665010948051002c81d00c1800041910200c1c0d8a04442207001d986100d94000020901c0d2802c40f002d503292154008503955850786403903801d211307507106070b250111001c0000588440804141c84c04448801c1880070b9540001150030002c40b0113017035003162400e6800b003121507000216a8100e14001300f0494403104045d08110300950084401a03800c42c107801d80d04942a00030310640c038818030204030400c410f142c119108010503000b03500016110b01640d1030014411400c0380c000041c10354410340c580b41c02c15559441c9142c10030b42d810003030079843c1902c510407 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 701552598 1250 701551348 701551373
    0x1103040b22081b0102100c050714010506060703031104080d05180d1101200d030608011a0102030a1103040302040207060207050d030c08061507061407020f1207020105030618042001050403 82
    0x19202c001e41c070f00086603a4020000800c040410350b1040040503880303440181123411422003102c80102107404607007000e01c14001d0703502402d4000c0400b883c128940c2d8059005180304009050841c1d410300c03000584c1407051040d45003000d01030312145d0343d4000013103412290741d681a1440340320b103811030581c0000c201d0014201c02400bc0a0030001109106000c41010802030040c3e10740043c491071000c480c01c86c0d4503802c218100d5008200901100500183d90798030b580c002c1801038010b0740240442c0d00c080e8070901340c04a00e0384006050300e1070683c41c0d4010405136071008030191143d50b0002810002c11400300716406441d2003030b1070b00304000b9020300f0008050a20107802180304034083c0c0419904040072104507103038240d014904108089401440c40c4441400b21100000345c01070108165009002150080c0e42c0c00e401d02d001460300101da0300649160308054409030b00805000748501c5680169150540294040c84494000860010610115440b0440c1150402c1824041040010401d18018 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 701553848 1250 701552598 701552623
    0x11d100311030a240f0611100606121404050319140c030711041a040c020c09131a0f0f0c2101031e2105090d060b1305251103040b2208 59
    0x11f4010f441c1000c0246000480c0600c0343e441c034900100083c240b46c2000e00704000c510081024031111060050005c144102200c024055030001c0046050b81200040703171440300c0743c507401c1c401c4040f40d2031103592059401885d0540d400e90700c002910814407151513403800e058082240e00b40a003594409821548541000510340030310740310003a00011038001c0c02103120940004e0030f584060310306403d80515000580c0816543d0104d0314046050074110301801c64400c900d80c2c40c0c00388403a1107820121403c0140104006003c41c018402d204061090021032402d4130105521a121541142040b4040441341c1340301c42e11651190b0b0145001032001c0c00181186038036003c1602405103002c0040da8188504c0559aa222180c68038900401945511000c0c00d91400d580121038080b5102c02a801c8440603100400c1c240040e6502c507980c407000007429103075050a0720708000ca41c1003541d10702e4610b801c65040440c0203200416091044241692525002403038088540d40c041d10744507145880c0c4200c071007074 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 701555098 1250 701553848 701553857
    0xc151003200d060c030e16030209060109060c08070309260f19020616021206070e0108060108040209040f0c090b01020c060703080601200607050315011d100311030a240f06 75
    0x600d44580240e0064811004900a480c078509107005000408915800201c0c41109590700bc80e07129449000f60100f40c503081e1319441e610001c079840b07d201c6030700300c500d044003040504200401c40000c40340902204100c500880e0014840380e00060303042841401600c040c603407002c170980e611104440066170350140c06441c09562034030007200042007079a0210002e50040a00c220011511600089440c49001260740d5031341c014820800443d08207009a0710980020b907a00701180c05483d00d114001d401c80e1140111101203452031361240210206c9511030000b072540d440c80c507000e958041c0030141401c1d60803202d0610702200e695010706817440182005040000c00342003000ea11912480c880d22200840c411210146048140181380d075108980d0180303035149000302d040c60f55010b80395254590049140c02c040036680741c010301c8040c18900170f010041607121601c251022440740c00640c01809a0b41340422803961101e0b0780c110041032500c0d580c103402c9441004008100744542a001a10300c540742 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 701556348 1250 701555098 701555111
    0x50d0e1e100521011d0c0319020d0209040c0e270703180f05100c18090203090c0a0815071d06031e07030b090109060602060a020c151003200d06 63
    0x481183c00d060410701250041c443e00100c0c4406a0419108030080300c00340345012503403a401d000102d03010035901890300c48481c0411a02c1c1c600c403034000d00928a0f007000d0043c10a045403000a00307440807000c200c0081101d00038641154240030005944080510400c2040480b80540c0e111060100614000815654a01071640c0004107200040f089411948101707180c1520b0514945a90103d840f0b401514034203654100715502554001c03d8440c10310f02c3c11400645000c1c0c1510107540f0048c01003080e40101c0e581440995116046103000c2c0031940c008113020b1007281c081c2c00c08400c014000c0014414403001010380f64821050102510109550b09a20303900c0d042c203401241c03445a00c05408020b16003081280389503059010303000e010b604a4050b501d990b0b17150801c2d021140540201d1005030001400200c00180c1a0020306080903110b08480c104810f03030301a440442400d884848400e05002007c01c01d0101229240c00d5111504a94084640520700010307404182514005c081e241c4851 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 701557598 1250 701556348 701556367
    0x60307050607121b051b0913060b240c0706110615130c050a02060109021303110613060906020105090106240306181e02070515090a050d0e1e1005 64
    0x10015012003404c0351042c110281460b0040d01c40380382c120b0406c0e8a4000921030b09036403800404d100d0050f6140c40b905a02c92000341c46000140c81c10080c1e0540020000783d855803500100309002580c080c040e440c840c2c845520000c41414000345601007420000d88551036009240003180340f5070441d0480c0705070000509040e010500c1091030001803541e4030314043c0240d02942e00540241130f441019401c0c0e500c2680c9500c070b001c0c00c07809269200c0d810118131220030300005030b100007101010700009040504001d98035a5600190007a504803600066600b0402c024243c2c090144a07040340001d402484601e08007510050074a042e01c2801081191110130001914001c0d44848050582500b42c07124024a82d007404003d8154400c2240c01841414240d1000218502c01e03205807640c0103020303210b4152040c070a600c2001e40603003a1600b0380945815000010400c1015241182c03081e2203a0001c00e501404106003020b03010082d16440208421009050392a20100c0940820504003203031502e070641d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 701558848 1250 701557598 701557607
    0xa05100c05060c0705061f0603020d061703092706010815040903020616020f0c010c0c1d0f01080d090b0d0204030b04050705030d0f210e0d0908010506030705060712 72
    0x100a0128060300c1c2c144046420400010b210b03040c001d008030703501916803480c0030402c4601d44984070f540060304041403180030f1103500103001020b00d6101c08500b01d03854032410b120706861214019000c0d84001084030032401c1138002111140c80e8070460481a00c5a881d50141f440d500a00c5d880c104802c0f10300095203144620550070031514060010444e4081c50b00d8080d6030b03100151410740c1500c141c0d410b0380102c6840020040c4a050025018200d6014458019640040c00020454240d0740c02c1c100032138051040c59204158040a2450404c0c0381892078100c0300050060708003ca0540008950b0101aa00490f01f0001c55000c0511165180c09c0402d55a00178042e0780c000508242410f41070000f0321a000400200b518012002d655200005000940d03004a03806201e0010525070203c2c080c421034001c50180780b8801101000c1480100207001c142400d220740480804207501c1070052200640910807903601000540c000c104d0303d1300340000910301c0c1c080d0190050a44000441f0f800025214 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 701560098 1250 701558848 701558867
    0x40603081912150306051e040809040b0109060813030e0301141509040b010e13081603020c01020d021908090a060c03080604060e0118110a02010213090b0a0510 70
    0x100c4400e03620340c001070300c819101c071040810120001e220400c1000842c96244611210f83c0d01c00f2001100440c55541d420020340300c001e14001c4640210080c1301c05152402c203101d4807603840b60000304d0b55880b441040204135030104005c90304000f002c0b10140030b55a0010b8219400c01400ca00c40c0030001080e07d02150442c8402c800079400d0b5007040c445102c0e045442d0307001c030b005c1c0050070492a040400e00c811721002a104450180400034a00d00401c07040003842c948640011641c80c0b040c1c020318040d103c3d00800d6000c0b00541b01014500d00400d4181070b418460740c120789a01344013070015100c000c040290342d003034030303d1201d03115a174151865010030641d40704488506801030508110700f07075920300c00303881314444690075004582818001890307441c041c4120020307504c0e03071b242800c501d9091a4a1024840c52818071002d826604d40c0f6444555146134094003440742c0c0b40d40050313510042202842469111540541880c0c0d08060660400f540c90402940982c0c03001c0c5c5444140980000d02210075812 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 701561348 1250 701560098 701560103
    0x2401091d01021602090604020903120c0f0102130518070210110c10050f0f01030f03140909152106041103101104241e180905040302060f09030a0509040603 68
    0x800100d4a0200f100b00022298190089451441d959201c00c02e020a0340b207010f10031a850707005603079042c215101d03c6016103091038800080b10b4002d40c203424902e0881c0d00400c41c0e500524100c1c40d003000301e0315050b00111303015158101c0003901c0d030800010103943c03480014030400f040d80d201c0c41404844400d5800740c0b03490418800858600c2d041c00014080100400d880c00c40d8074a0341c031720000c0c0b2407122100e80281241e9102000f6160440241ca040f1404131503203042000400c810044003086640c0c55100c2e6000f1030031408400c0c0d05a61600410520524004411f01c03040350000f802d8880410109040e41d00c103400a12030b4141056280c0041c1c10a0907804c960221285400902d102a004000c0504107442c2601c4030700406440032400c801c1c2d091100070980c000100e112503c04400d00b2400f0106008843c43d08044031a9100f01d2882d50400103950043c551250340e4104100a050f8100001500410700348255151400c04c400559102d100700605030382480740020f09151192101d510034002181c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 701562598 1250 701561348 701561351
    0x80301151d040b0d0b011509080a08071b03060504211b120201090803190f060302031b0f03030a1106070e09010b030907151e05040b090f0f212401091d01 67
    0x1a100c5107c03010b10f07044404844002000309002113400360f40001c0c503180702e60f001810380703040114a59419688440303200031141ca0742440040000002c10070700850340110b21034a0005008088150842c00d40d06e500c16211080086106014000d045080100c140307003500a462400e0083c000d4406034090b0044035002001c0b51740000401201c1a5003400c00c100212050070284001d41c2c04200d042d09070b8a2500019600d030304040d601d03070001c10a6901c40103880c2030113482d489a01c20458002429908880c5846020401c109607041003540c043c40407a52010f2a8142078400f03c0070080070801402050041580c115000804901c102c2002c01461000341454a544034115101c110000d04210029658004012a500100541d0341c0140103540c2642c40103001e560604811500b001800c01100110503000014a03a10741d074103842e200c0c201f00c41610310215012040e440285114500f40c0c04850b6140915880d00c6441c66a0504070f41140c1120401d01000c1112800c1524014195090390071190a56 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 701563848 1250 701562598 701562601
    0x80f09090f0405060a0c08010501030e0a0501050115030f09030c03140405030a08070201200c042a0306030b09010c05030f250f090f0f060c1a04080301151d040b0d0b 72
    0x90450394110340300ba0b01c10410b54904c0c0e2a194800d0302540d030342c1e1802c480030400000c018000c9511a0f4040b10a1000c0b00d01200c44003c419181d032421580280c1218944e80640030041c48210303014040c1415100260300c04004000040c2c50007842201c10010013010400707082000100d0701503030320a5070302030800182a80c003610034526043c006980244030890100340052800032200741000b1038400d403091104041c18143e07125004010050141e0a10040702d0014000d00c0b0498920048001404100d10344001504a041d82418509164024090203803681050440e505072075200041d2034111458087c00c540035111141488280740c50b98100e0455006008602c1c0d0200382d00c083c0c038807a41d0307100c1c0d1a600a2180c032000680200342c036901906a1019991200300045032140d0b0f010040d031801144008500f2031205030b80140420b0550781a1a000c20200050140031100b01c440e00354190716040c6001400c01079840071070590526407072140308940c3c82c504103d81b522a440c00a14051b406031006016 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 701565098 1250 701563848 701563861
    0x6191d07120203041109070908160807170c130b03060f2208040b07171308100c0e190b071b060804080711010c02120102071a010b07080f0909 62
    0x2400011240031000400c00421128004010720841c1d0086802c1404030003598203010074466a440c014000004101d19040b0000c0c10000500c40d42071056651400e5050b80e501d80700c1590315100c0190002640d98801041e400000e54000540c0080500d00340c8009160601c00d409100052100d40f90751605030141d8400c20414403150703500039200c3c4191300004480c60550551945480b0142c0c0700040160700c0c1000700344072104400f009840c5040c456026a01105400c105240703a0741c00c0503c501c04140700941c0140400c94050005645009480303004124550920740f00a06400600000ca03001d0000e0f0040c224800c010040003c020b071602d08134095a0344030a2608031040404801070702e20080c0003048c0032805a2240740000d01442e00710b00708600f0009036071121a606007414610605014000c4000310058581c8600080744a03d41c600050321400c0d035040c0700f00750b08004002480c60450355001070000131103900070342d00502e41001c506500c90803003c8101c10544190150290300040c0b14080011 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 701566348 1250 701565098 701565149
    0x6130804030c260d0203041406160302031e09010c111f0c020906040504020f011215060503041101081605180904060219020c01050324040c020c040c1103030619 70
    0x1103911103022070142842c540140c1581304c140b0050f0980040e0002c001c01c20107048188010440c20000424803450041450b00e064109100c0f0766044026030000b045215208000a2000a00c0300c02031003c113180800a5000070310340440047c0040001e8428003160700f0750b46690131103090201201455a00300c0300c02800107804205100c20492150041d280024903e0826000325401194068401d54501008800549010110246c150499a61103040888081080300c0c007500518243d210983e682c209803c000300e56400701403131141030080e21030034001001080c004111280c00c1c545025502c508100c0e150000200e10101285e60000390b100c203000911a1640c0108120a007100c03600c51400d00c121002da886580c00c00049003c150309000289007401104036042c08241606100071aa03056600007c04554990143d0b00050740315079201e40c07050a00e4482c564400300380b410291150080410300690302d01c0010111409007101200e8103400115240703a45019099818034114030102a015100 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 701567598 1250 701566348 701566379
    0xf0f0c12030d0c03020d0b0102031e07080f04090c11160611192904110918030c0c010e033903030c0a0303050609012303030d02120114010201050906130804030c 70
    0xc46c0c40d00d000201c640960002085441101850700d00c0c9840201d03002c8801507d4120728030546465008003c807130041c0d40114010000307000c00d0300300050008400e920003030402080c1c0c400c4060a40c0041504c210403c00c214810085030064a80b00b0400032160030740c2400c0c04c0301000c0586803080413801707000030000201c080100205451141c500b0450f042c0f0143d550030503043e140a025080025042d1000303040821280d9070000503500d00b4011343c07544440e5145107a024241d1060b17644c0003012203429641c0c0c800c0d08013000d00000c5004003c5001c020500034920b00030314801e1003049110186440061482c070b564201c021500406880e2594103418529484201400c0110002487c4c00006082480c0a071170841c1070350034050046560340001c000c04180c0c9000303000c18660502c0103008103c4514414001800c80801501802c0c4040d4540003070314a400c0b030307094ac0490569040000b0000d40c100002603290b0301840b0700d20010050a054100f10075540300315080600310f62480540407550040f040d4080 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 701568848 1250 701567598 701567617
    0x4020612090f2b050412060209010e09010608100e090d0503100f06090906090203040f06150902030c04050a120503031f0806071707020c010503061e040f060501020f0f0c12030d0c0302 80
    0x40b45025903420200d0f224030480c0907986c0c0d0b4000d640702d120042001540030381160039041c141400b11030510b00014038035100903884000001ca0100c00c008501507195402c10050480200c0400c00381030601c07649448880c03410688003040350110000e00c400070b0503044000240782401c454040d00781c4544009004203c2c601906002e40d003042d0f00041c02000e42c2c801c9030b2007190010300007c00b41105031340c5e01c4040e100c1103407601d4440c2c0981c2d201003813800031803000310b002d6010500e007a5a01c0e880c0c2400d20440c028281c0c0305540090090400c40301103500401125803040c00e0b4440d51441d0341100c0c1e8001c40c01a80b6400c025001c0c40380d2000c2042140e000741807901c10035211f080e1180307203070740c2c40d24200d80e00c00c03d41c01240e000a0081c000318215003400d14440c09402d81e40b45032480f08580440100d4100d8001540040009031614030030401035806000c1c01002a9440d0090b100071840c0160a940c0d504600d81710340d002e54030316002103100d41028015600101e0820754113001d80004401d000f4040d40200c40792 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 701570098 1250 701568848 701568913
    0x170c010203040b0f09030901050a0e041505030d02010908030c070f060203040303063003080606041e15090e04030f0c050a140c04062d0b0a020d03060e04020612090f 72
    0x20a40ca0022001a02e110704251030046d40f500c05a000116200e400800740328080c46413401c3c040fa4250350724050400c80c1840745d004600481e00d40020140390100000d070f07250940e4502020303d4013158201084a500141042c41c141d6100d61501c0d0002c1504070320600640380030300c0403040c0002c05502d81c00013401c031660a000d8500c460640400022400c0c001a0000c00841180a440c00042d010b5080980c0c840c90080685041075958240008140c80030300c0c01013460030750582c05001003843d0001d0380303054036414074201c60744604046030382c1c1407002c0240025040c40b920f01c4202082d5880b0705124000300b5480300903194094181d180001c1003100c0800c40d030406000e0b240301c01a45003841c0c400c00d400c4640615020350702400e101e2030309200102007030b5040118014920701149401e80380c40181282051a4010407075100c0e044800ac00301c134500c1d008151a0000e120504c000340e9110070503203000807440840780d0702d651920208503203809c1e08245206040c0c0600c3d0f0050140701040341e000c900c41090cc618 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 701571348 1250 701570098 701570101
    0x60a030605031002030c07020d02030106080a061d030a1b0503161a010801020f0d33060206070507080702040f1b09050f0a0608160329190b04060c170c010203040b 71
    0x301100b84e005c2110a0003003a581403000c00007601c0c1807461010308500150001032040d446103000c4e810000c41c00310680e116a29007180c02542d00b14801c00102c0600d10030701450500c0c4c01148001c12207144440004802ca11801340f0300107024080c02180c54901c1410b4916200340b41c0c030702d8505202c100e000c0300a60340c8103200340005000b0406000b06c80344488407001007131070300003c500d4440041c4941042c10302e4440d4000d1912204015081505080480000281c00d841d480d0441c001e00e01380b00202104208030060100c0030000c1c02180a0311507943d0304035000310765044005090401010083e0112203a808884100101c01e6048002002230b41d0041ea05903001000c2881489001041c9104600c0050304c03510004046885035811100b0042c02841c0101c0d036045c1c4101100381c4048a418a0041640320742c648850314600300416540d40b4030ba0417040b8039100e280483c00da00d14042c61003081e042c8082c00c22800c00b0003441082403031703241800280654850303a9508240d0f000750003c68089504130820360 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 701572598 1250 701571348 701571373
    0x3050a060b0f0a0912050604051b010801090209040e01060e090706080906130f0b16080106230c030705030408030301140d11060a0e04140a1a061b0705060a03060503 72
    0x40600380c401c00c004003840c2214606819000303500001c0c88100f0428103000200c1c0c074a00b080d00f1103005030300803070080449040504055040444907212044403c419103400c1403242d0308281c250341125902200103882c0c80100021070003410820391402c000b94a000c9010a910700000102c41c010b030301100071101e0b419100c203803d40e4250700c2610309913225031080c7c0000783c2c1c4652101a0b081d14500c1564010465001340c0d0700d54076511401d07540c1e0350881010450300d150301544800b0302c500510092506469100c843d091410a1050203407455201d00380c0002c91030700410081041301d02030360740030088035071301c035503801380c050700c0b80c000780181d030344101c80c0c1c08130071445242000c1c100c01510b402101d400308650303055003000384035400910302006116001160a155664502c1400c04c4d0b980002c811001c40d00d0000f0506044854440c564040c00d01401d41942d01921001c003036810307041118543c5100000b800d41d9491820301143c1c8a60392010000510580312980741e0042e404646082e42100e00c0c104040 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 701573848 1250 701572598 701572601
    0x2a03010207020604050d03090b040e040b071b1101022508010f060506030a0f09020d0302031e0406020d210e1608190204051005030d26040309030206030a140403030c03050a 75
    0xa60020f58082c0003800300780000c1c90005002c040d068480d082003505640c3d00d032199103d0381c0240c1d0001d074001c00e9100401c002c0c044003150203035010343c6500e0240c500d01d0f020724030b6072070b05580c01f407000e400140d40500780032003030b4001c10025505e501040120000c0142c07070341048440312550b0003540c0d155400c1c45056156003420740100401e494004291702c1c00c5d40e490b0300c540c0c0001c05120303c40c0c3c80b001d9111025000035860f0b042014030301500030b5003d1540c03181c1030300f28070500503d5417800702d81c100401c000070070a2542c0442d641e08202e15501d0300d551b1103500c01050681c0070b102d442c59607901602d850142801c100e400144140002100c02030300440c0c035660036105440d955446c2503180d000100001c0c210040c40c1c01d9120507484402e05003c0e0010546503030219180c4040da03d09100880c003034140c401502000703444548809814088100d032546400c1c1e4000304440c00c01d05c4000e0050b100480800d000501c1500b200f40724090507010f4003418a071034100100a003030320300c6c00364012074904004143c1c5510103 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 701575098 1250 701573848 701573857
    0x151017060105210c1509040c0804350a031508031207080604021b0c013c020703061802100f0e0f03010f050c18030304030f06021602032a030102 63
    0x2088100e0003030f21104001d140b4914260014000d02811310348a81a540304250803458601c0c40b00201e0720741010005200894085c01100002d200d10081040002900c00c203107001c00300c1c03410035a56044214803010708e0302003228507034440035081e020a407900c0960f89030b401185010320b0716154040305aa01c0c07155039101e200d842003030011624003400003111180940012a00401d001d400140f8007207040d403103001c0b41700310600c50210303170341007400e002d10190303403146440046249140c00740003082039000d295103400c0c0303166001a00c25200c1100060406000384510341c000c6800400c28820211703480800c00304090300e5201284101080c0320030700402441184903c002141700d860b90442d000d5600c0801039000c00f4129a1039156494101c5020441c506009640c000c4410202c465103d41c000c0503860000002c5910703250080d8414001040451045003502e00c000b5006240180c0d1001445a1440c02d02d20114000c1c2d018459012003d0161101c006180c0300c0d41031103103842c0c1850b400074040500342d208 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 701576348 1250 701575098 701575109
    0xc01060e070905190509040507090e030f070b0411060408101104060c0f080f0414030f01090305031f0f030503030703050f191109030105091f05010b041202031510170601 74
    0x742c1d00a010b6801c0101035414054850003400300800d03034400003e81002030482c1e0071603081d082490100641c2c25280500504515080c0203542070101844100d003290183e400050000c0502e900409c05000c402034010804000c0a042c1907581c64940030020b94490100c0030f50419035280c604550040342d11401a05d0542d5072980d26801440400d0b00d0750000b90300160b00c01d84900b40c0401c01602307140041c0008200514944201030b0078000c00804260a1510204444d00e840c4d0509030401c002035800012681e00200c9401c1c02400c08894401e031b00c456448580041500c0c0700c03400004801d00800001840c403a220340c2ea800d111990703404c6c011040002c4283c5003038900c2c202e10b0000d0949070074a0b40104a0f10480c0c00c81e19424460484002030940b501682e0008080e01300000c0b4020503400c0c41003445c50840d40341800d01507545803400c0030b0824490b030310449021800c10341081007107650621488244007141a0540c40310309080001d00d040002074402c1072000d08007030158103410480030408a04a58 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 701577598 1250 701576348 701576357
    0xf060822030518060307030b01021c050301120c09230604150b07020607050111070b0a0b01020307080715060b0c01270803100f030b01031109092e020c01020c01060e07 73
    0x915550103071a01c1e04203001c01901c000f0040b01880e081d8071014091845600316680101d6024000c10000e400c000c880038040c5034603d0034010049000e038000c0201d0307044464001144984103224103110019040b075420030030074641408000141000c0c102c1c41c1100c4586194000030b2075031601d00410080391a400d1614400c2c80020900300721280302803011707142c0d480c0003400c2c1c1c600d06940c0b036441908407500c40042d0045003c0c00b00344402800903030300781d159003c495060208540b81a00c40040e68900450340300038540440001c10004101030200750040d40706032a0740074005c10f512000e00500c1500030300042403081d86410160b102000c82d030000d145014510004000440182c2d4131070080b6688000d003000d065131500c0c400000c24500f5000d00500030342c022542c50540f9411850261091680c100300c25209030403200c01c0c455207000210302500c840318100340888400d0814842d464005601c4901f17030550300d02c0421903140000c0190000e08103191580002c10ac41030b280d4160640340c110130b0301e02c4030024 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 701578848 1250 701577598 701577661
    0x20306041b0f18050a0b0a080c12130c08031306020d02010902090c0705070b03040807020a0501082e0b0c0703060b04020a171e24010813030806040b04060f0608 70
    0x18083c810f11003448941c0115250a151140d0105842144950101404280001da501c03451076001c0c2105401413000201d10340f80400ac01140f004071000034100500344800c00c602001000406a2600020b2443c001034a4882c00c0c6014000407504040c4a03040240c0070b61462880c0740d91043c4150148190300802c01400794481d801d40091a40040c10201c616104000002c1000c0c407800e00a984628072441c080380d0b5400c100c0c03040c040480c4181d44a5418000d131881444405045d208207191030791425606c88950500350036081002500700c0e8000c0081c4400042c8103145500d0105000c0c05490260301d060042a01e07540030b00080388074800342000010010280c1043c00031401201a4004080103200001d1002d6441c100100b5841a100360420104400c1c1c411011000e14030103203001a0709090a00492400c41501401c10f4000040101000096800224980c0e034540c0081701d0b42c030005d041045410b441d158980c3c0d10280c02d004920201e40520b0009440000814004e514100d0748280a00e02 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 701580098 1250 701578848 701578877
    0xf0905011e0507080705010501030b011a090a05060a17010f050301060b04051c0c0e011215060e06060a1713050f0a02100809010207141b04050906060d050f0a0501020306041b 76
    0x2d50081803080ba00c00200300410401300d03c003401282d002e1401801c085605503d08403c007180707100320030040c40311410180010982603a402203d901264070030783d90b894bc1c030500900c007156811510301c100c1c0c90b02c0040400201d00780d480700380c0724011344000354000c0200540351240c0c800240514401d150f4000603610300552428002248803125078424003d512803d07446141c0000003c400b60030004481c1c071007002c0c80090002d68541c030034035050f07050003c00038030b800d20011840b15170000b45400c1c005c2c8800130382e1201444c85402000804948203003010501d083c10340c0400c20b5903600b200d09555503c110b1040c034421180104021600b50740c028207190345841e00060640c0c0b100002481e284081d5070030301401d408201401d0104206441ca4405045501c1e0040004585010079a000c180124501810000e03030b1030700091a183c0000b001c03030fa005a81c08692400c0c074034020301c3c2c00d4082c00301d0040032034071010086d054025500070705003210203100e0310160345108881884c120640400240035990700002 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 701581348 1250 701580098 701580107
    0x61c0213290a0b07050f01020a08150603060a0608090f06040b0a062c0a111819060e090402240406080c0705060a050c0906040f030203120c0601060302090414070f0905011e 75
    0x403118422170a03220041448550780c1e08a82009240c080822504010044d621030004107142d1450021108a401d504245010441c0b812a5000d81d205000020000c68000f00e41003000311140c0072100b0440d2880d1520b442d007000d4085095525469050401c030003c10302c12099185a00074410010701801012a0000420011752014000509260b501c400c4c0d0f00002400c080100a140f01801c1e0742c00c040c2c46a041881080c0d6014540e15614003995003081c4404c80e030080308000c05400840da900e03000e17250350000511003851218050441010300395401c5001103c1c030701602c11980c0e95210b0040f5580c5032010300040e440b40c010010416084103001428012044d0f02c042d401001200d41c550425031503a01141c502c0e400380d00080410030960000700110b1400300000b106108500f001c0908000c800840c190761080e0602680040c140c020481e40e0381500c82c0d234011040d044191800004904006070082c00000c0300c8402c4c240003610f20100070455500500380304041003c4405002a940603d1074200d4 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 701582598 1250 701581348 701581357
    0x180f0c0a0512101503020901150f0e06180307090c0c050c01050403081204030309080f1e090a0317090406030c061101150909020616140601120b061c0213290a0b 70
    0xb8004c00301c0e0001c00561194807102d406803442c92043d680b10b0b0b40c1403030060030700c00d800000076007000030011540c070aa40b074100c280d40f171501038005642c400e4088907000070304101c1d280e0401c1b40d0061401d100c600810364010076030074805000d00c040d0303002907a4105c01156644150302000e8502401007064490840c860b07840581c2c014000d103400510142c640d0780e0014240d0019030540d281c0325001c109000040c208010455592041881003494403135804082100b0105500c0050410803200380328181035a50314040f01d02c8804010010804a5120b16045181189600450703001036034881a642800700144280070030403021154802e1442c0c40c2001c240c3c06003078000c030104e80040b0244108890819040b800d248403074414403072000031010740c050181c0f811405034008504074490350880800f0800784c2d01d10503007044d001d41e811000c403080c7ca250781d1512168200025000080142da9a148401c2ca45c02040f01d148502c130b148581d000d001700680007c59900c03507000d612000400e01002403411580051 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 701583848 1250 701582598 701582621
    0x10e01080a09060905010b010905220207150e03070b130b0a051506070c21030c080d0603051f06121a04032610120308060405180f0c0a051210 62
    0x100c1c40a082e60355800c1501d2108104a509031344401c0d10004035a08605407030040c0009030340c441d030050080415440d60030035031504900110b900180711014800200c01041180e2200c15040c8898503003003401650b25400354800b500c20030245404290904040c030100c1031026000302080f021070300c4880d0040c00030700d0b014144002d0400f001507007850303036107800000c1c203c000e005910b074003501c41c40c00044040c681241088002c0400c0e554070350800290304070b410b20040e10340103404140c4400031004803600500e426000a4010320880700e00525003607001c40100d03440e500c412400d020301a520a901800c18a060800410303103003600d000900c09440101a865000c0e000f031619035181810410200c02c00c0080382c141285500b01d0604000d1807c14402b07140004010001e01310602500c1520014a18030001d8500303440341d900e62011840615048a01550314680b69040e01c1503900e113240e005660b9140990050301514030200000713443c1c03511000f210640700602014011008a000100c4020161100c9a = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 701585098 1250 701583848 701583851
    0x10f0914160315061706010201020a27050d05060a1406010f0305060303160f06360507050a06020709050a140403051b0706050903060a0b0f190e1003170405010e01080a 73
    0x1030920a040d50b03c03032001042c103611117090341100c00e991448450f40007440241503a0041100d0003103660700c40160000c681c603841e0100c003000198000c3c0d1201003442d030f200c607511419020f2100c0038800003183c0c1c84e014820706c03503041006d150f01e4013203014420021255503010071005501003844c04d00a03048140c0c030020007002d803441e03d03003c40b104490b401c055010a130740001c0000380300401c101c0780c0e20a844581c4080c0d0500d0305580210740c0d1603050000c40f91031080001482c3c0da9654200501001050050700006104080e1107480d444000e60700d804512a4881d401d00308000301710459020320503a41c604d00040180c80c820b49d11038406407500e50010307003890b0f0900b040041e11042c0300800e10030000644441e944565844400c08101342c0b03810009440709002524060f4020b205641300d00070300c41d182c801075030440040590302d0b170303e0343d0050b03e10703030181450308000c0e420060350303503000329803101640d125110641c424092542da0080c1170055006241c0454525000c0080a40c040e010040d8040701400d030 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 701586348 1250 701585098 701585111
    0x7050603010b120108211602030a0b1501051303060c02030f120f0f0f041e0b090708070602030315010c0c0302041b0e1c0818090708010f09141603 64
    0x45005980242e00800340d50401080308500d465041c50100d00410106004010001c4058402981007910300e00d81100c941d030018103414262110494a403a80b60002d040e03030655003160804c1100e066046640c007040c10503c2184080b2580a03200303445031104103080d08201142541c1c3d0380030007008184c103168294842070002900300086c5000602c4449106000110315003400c17844540c8a82014155450840d498070401ca9031903040e000c0c0300c4d4800e401068004104008030aa038010026046020f1f210880d00c0301040380103500021030800300c40c503c40031075101503591842213880c2d001c00e036142d0200e40d81401503070341c46600c06c40015007110b00a000f10400c0c1552135000a080707a802d50b141c0f11540040700c4c81c102c034068000e50514400c071000d5071700b80f4180300780c3d04c0050800c18070210010414603001c10b014034803103141a082025004c01514400180c1400c09015240e00c10034442c5040e08461108041411034490107414110300b98070b4203c0d000d6445d00c000803159090f45030740400c20103980342c4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 701587598 1250 701586348 701586359
    0x30f15090103050f1b221508010b100e030601060e0a09020304061509020a0504032003070e010e0702011407230d1e180b04080408010c030506042307030e07 68
    0xc4854001d500c81c00040210300340b4810801e04001402986000c4e40c40042d03030b01c3c0001d07205c0320701794002c140181180f00c3c410040c2e60b0300c074801400d1b00301390085001141d110206002505600c16a80b000b0b0448501b40c10481d1440e00301d03200c0240e01c06103901900032100400899001d00070032100f10000034030042c82c050b00d0304403080881e04110f9083c0d400c503841d40c65920b254042490074002401c0c01e0030b025031608100c0c42c0d000d0203038812880018400000c50f1800b281c1903044a07005c020100005040d2100181c0e110301c11046130720280036543c80703400074001290440f8014414091600c00002c10b0300c090b560342640035a00b051440c146580030715040d208213035181e0301034801807a40d0340c82e005000a030888001144030b8050312604c0350307032505844e2081034410014012a034442d901da200581441035a92441c090609002d158032100e269030811066910386601900a00d1240100f41e404120079207803c442a6506a030f035002c907100c145031480200301080d00c40e0304130b01c64642034601141c540035a501c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 701588848 1250 701587598 701587609
    0xf1909031b14030c01020714010c0210050310060921020609042405030a0c09091403030c120c03160305060409140a0c0807141905030a06060515040b030f15 68
    0x120401c5800c20034141c05110a204040690000707030016001402c0c1e40900e900042d41d110300600481120f0440d55842809036071049405c061742a0740507100029000250074058040d40054404112804c1d4142c008654140310f8003044040300d402c6d40080e2003c03001c600040200a4840e01c082c0e8100c04104418510340d140c502030718424039000e001c0022a2900407210f95141180760f04001d20a8102000c03000201d09480304120607950440360010b10140c0300d00d0031171600e01103043d40084900000c4200f10311001240050b0810107211903c49002c0e9450341e61645251000b00d0b50221780c26200c80b40d06034113070f100750f20031503200704050301c0010040d1168855201c0080d20843c51f40071503001c12101010810000c119000800c0098020440076050240000018103884222030103010b45021202c4c070498182c1900004100c05016251084140e00b0440c0140110380210341c0241042441c00c4840c0a110046804503100a40170904584a0510001001a000d4164503003032001c1d458103160780d59030 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 701590098 1250 701588848 701588873
    0x7050d08041404091a10080a0317071e0207050f100206041b0801060b1806030403080112030314011518060903030c050a060203180106120b060d03120e07030213020f190903 75
    0x1742c0220750003503e03100b6001c848940c901e821403030351a0090021280042d4100c0d02c100c942c3c44c1d442c500403600b80c0e40c00f0412110201072520012501001e020000c0a0580100e0800142e9400f5180c3c000e507042004180800200301c08a0100140c6c000800a804920800d452000c4138043c848011803040e40d5900007400c0d190150880c030250000017800c6007100150001e00300040005907841c0d801d501d0f00e600c4c06041c9020510885a060005050b000c0c1010302c61380c000f406451a15081c203016584903076501c20b80081549243d404580342e049081410f48110100314112111a600c1010050540d5400c55021900d18402c0b035030351041c21940c00003c4c9031070006e18440c00c0e5240382580d030440098005070940c0c0d0b45070700940ca50f403103880c0c0c10400f207800c08036120380c0040d05481800407032500d80390031a85210048402000c0034604520702071400408100c0b0011a03008803603580d009944685c07440202d00c01c19034840d141107010020b1203040014240984c1080c2480e06203035003100e60300d44400410610 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 701591348 1250 701590098 701590133
    0x91a12030406180f1a130f050118030b190f0c0503040b0a06140603041109010b03091002191b0b010e1608060f010e030118050f07050d0804140409 64
    0x3080600606600900c00128a0fa5588209070010b203480604581480302d0b008060607900c005480c040b0001809045034000c2e002081e1800070380e60307034150410601c0340d540242c500140c1c01c0ca064147c19410b0380074035829a60868035032000b0341c4400c00b05412426201e903014000301d03141c0203c400810342c54442d0440e09941605c900356a440c003450400b0320707160010f05c8007901d90b18065040c013220051600c844490101504c05a551f0741716800d00d41381d900424020143c1c000240030010455516203005140100030203070407562400020640a410b901a000110341d484034841c0c42074040a00c510f5101350b2408194402889a0f885034680c804c2e081c1d0240c0046e11048500000e01c20003489000b80740a001c803c07842c0941c1a8100b00740054640300300304c090340e41000071080041429039001e5106580c5c0342002240c00714855018546182c43e04140e101143c218060024001403c0c104015084005035004002c0e514042c200583d101b5034441042450750081c0e90b07400708000141048001800720003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 701592598 1250 701591348 701591353
    0x9051324060f0b040603020a050c03070609060b18060d14070905060307060809030706050c0f070f051e060a230114090c040b12090f0a03050a030b0108010f091a12 71
    0xc0d01035036030020303a01c1540c05800e140c22018801c0003d907205a05807816103040e03103000350f40e440d4440f400f100c3ca40120490400300e408001009000c00100e54001031a40c2e10540081c020011321200704808000308200312054044514005803452030034240a0f0a8944120305003546940c0b8130108515000e80c1d600300400781aa40c0c004c4c421503140401240f0b00a22541c6001541854000e9901d41c5074020b200c401003c1c1c1d5201c50101d006400d40c401030b10300c150500c0711090f8a940035828008154807044500707030b40ca0301400c40ea80002541007440001e200489100820b600e4079200c02003c01445203a62540280780120000c440b084645800c2900030b18000c00d01c0300343c40c82448100300541001a04450307160004203c104444150203083d00c8403201441400308042e5140800359013010305100d58442580141d01e44201016000f00c040d000c2c044080d6410041d04182d807005451341c00081c0101c40da9000b0b04c04007041030003442d403c020080c070910b091410340d6407051404228020318030003928001c3d8 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 701593848 1250 701592598 701592653
    0x90f032d1006141e03010e010c03060b0906041806030b040803061021020a140706021309020c0a02040b01020a050d09080d020313170703170a0e01050c0601090513 71
    0x124010040261a007440d544104206850482c412400c85007429400d4020010580300090380304180400c2d03076071064064002c0c04003003401c1c820395000b401c50300300450100386031071030200340800f683c401e8403102000580322900d001e04040c03e00030020b0340300110046050300c0b200e000c0000344849842c00e0090348981121601e0341050340801003066505510002040009043d08000c0780e00e0003101340e001140380d80300580d6000b078a2011204086c82607210440860005551000c000c400d0b4002c214540c81b5080840101e5124510042648108500310701140e10403940c110140c5003d91082c00d040505004451b011314481d500c0900300390361001d2480c0030502c6000200180c180c180104040b5903400d20183d441d2500c103000c0a40d0305030f054010f8407500010f41220354900d24007003003200055500844074001030600344c089402185d010303605050000b080c0060b2000c25500078402c4c1d030800000c05006c1d09560b03082411042c01002c008000c103040c40300c414180c034081001440c4114644c035607155240e009 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 701595098 1250 701593848 701593933
    0x607260703030c03020304030f110f07181d070504020315090702010b01030506011b15020c19022704020f0105190201050f010609030f151104090e071a090f03 69
    0xf2a80e550416609150040042100003580408111030480c080d06120489110220115240c00340240c0d120115210f40240416490f00781036500b05080844101404589044c2002040340b04800121440691040e1018440c500d810f801541d808910b11121160140b481800118060010b4400b00d026075900c000000b26541c1c10300070b081d07100c6000e003001200c070000003a00070b04120f490030010f840c44200c071203501080b1030141c0454856590440480e10003060012070b07100107918181c0220b100f20303c004e0030441c2d4003405004c01500010443c14050a0ba035a039000e000541c4100011a0b0404c00100b202c501c60540d6045200c400755800c0d40002544d03e015500240c881d403060308154244070000b0390800009143d03000700c00040750b10114080d5400628030142c0d000c2c2c500851407905030300c030218001c11a544240d0080e140d03001490104c81d050b907506d130207030120f2000d17803400344040c2d0400300100344150501d01c1d054040808080c003207443c9001c0000780c001c21085240110a07071048582071103640d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 701596348 1250 701595098 701595101
    0x7031a100c0c0b0c03090f0604120c061e140a170a0605270412090e0c1c0c02030a0309030e09040b04030801240c02010c2a1a09060726070303 62
    0x2802c3c030141114903103d13445946640c0ca0041d40b940921030011100d4a80591319000291002400181c0f60000349100394035018281620502036540003841d41d0f04140380d094403030703440c803500740070035840b44921a038071070080b210b280d03104400c564280884581c158141400340070070030780b00b0403160100181d410300f440208020040c2034098a0f5920b02020001c0e461180c8075000b031504643c4c82185038420801c142020348100c0000d500c0302815040034010001c05460a00003009141c0034041500840c40e09200e00508840d0103401050040e40144041e4074450f000c2e40c003005000e0300034200400c10382c0303941001543c00d000c1281d040f2450030510052104054200c00c0b003d006d0028450540d048014011152070801003504606080211005000f0150f9018244a00031a0341001c0c3e012103294101c00d0500642640400c03000d201d1400d140006440c0c5600c0d1140098a84500046464400682c0420420750041c031030581e004115000410104070260f0030440e0114003059805407102c04c01e060240 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 701597598 1250 701596348 701596373
    0x16090c0203040503030a0e0a0b12150102010e0a0602030a0b0d0f0204230a020f071208010e010f050312030702120c01060603061d0a0905010209100c0b091507031a100c 73
    0x42954820b20043c4144e6902005955540c003a07440d001c8595040040080c0043c2640d81c0250815440015074000340b090303502c0303901d1003071a04000c2e038032074100b22100480c01c0325030050440407190041564980015569001560400b0f22441f002c100d6464000000c0d40900c1c07a020b0440388800da0100040c2103089c5406000b021a01e4400c1d82e42031064003100c0d080101c14002c00358546c1550000350030b051018903000307803000d2070b4001c007251a085100000c080e11444080c001c0c00300c825601c800009004003c0c0e48400e09446028000d03007041c03040c03944031b2191504054680170030744c0911030144801c0350f2080090561200c0f1031001060051502c2d0015084405513006010401040f4050803662002d40074584d412400c034800c00900c048550510500a0041c51540c82d440745502e04a1448135900c80411001c072030141e40701c0f09850f01d030b04001560328040380b0501e044445200e800100d0040c002d81c040e500311490803103419a40d480ca81e001901c20a0548100c0e404615900507240500c80701c0032180 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 701598848 1250 701597598 701597621
    0xc21061206060d060c1809020318060915091e030a030b0409240b040203090a0c090e1c0903060501030819022a13021605060708060a0509040f051609 65
    0x2001d0301c0c20010082000340c020300b0b602030242511102c1c03603011140f2581c4031040c07411080309950616a11418840083d6105860088002980700812200404080b0360700e40105011001401d006607900100d0491500017803414800c0d002c0d280c03500c1c06645010f0380543c00d070b10158000d19940e2219041c041c0031500d0041c0000c0c081c52501e821000020441c512024054214084504000e042801c400d070150180b06a081d412900100074000600390000e5908030b243d1050b00885441d58884e80b4200444484807400050390b40840c2c50301240000c109a8410aa201c07450b249004a4590700c510050b6072013a402160600000544900390862254000c8141c90281c40580111000c80c00c4483d0311071410310207550103902001c0350781400e981d034500c040740442c0501001e5446011003904000c44103e00300d0207440d940274a2f80028003151013080d01a110700001000030303041608000c18021080c0d401070003118490070340c14940340465020007400c03084c1000420038a503070310708282e400e0b003e4852a1285 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 701600098 1250 701598848 701598853
    0x150106020c010801030201030f0b042d180602090a080604050c0a080c0306011401020106180f11190e0103020c031603110f0c060c030f04030c03061503020907080c210612 74
    0x44540700da074000ca101c1e0440c0c6d02441c012071280c00d0441880024501e04010990291610707804440343e200c89018801300651003840100c0301900190b601041d904118103082a10071054941d000081d6594064100110090160104180c54940a038544a416101a1015840b0f682c000e180c80c945544480003401e03101019002840c00480426503070380c4103025002200804040c00c0b075203a4801d40c4450f0091080c0d240f500d200000301e40401009180b102c1b40150000c0c2042c0700b0300502e0207041d0495952020001d03400140c034503200000c4420a61103102030341050b408101101c4060402c00140c00100c100b103240180c03810040c60301424840748030041c003150f6003108064190f4001c0101e11a60074610548900342e8480440c1c05003411841550700c0d203052600b0200b0040140315440e8004070a880c41054204010203500c0c1400806503c1440006c0d4003244500010b420b9900c500011504408101c007035908003010650007100d04090030a01900500140e4100412803412000500044000c0e101 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 701601348 1250 701600098 701600113
    0x30d0509030307020108090f0a15060605090d030e03010603060e0606010207090b010210050624250c06030903181205060606210408040f0902030105011707050a0c081b15010602 77
    0x10a40700c0c010501c0190520038018001380040c1c7d024811542e64000001c1030311200102171a02c1d140c41c00308908000030b250f190400104006000d5000ca8000d120002d000303a0030303e409030341d044503003040403200e1070340554985800000251403400303405900c1e50040050300061408800092038005c180d440021014205800e1113000e0340c0114445a00c103007400310110b80d40d40d400001c2581c00c0400a0385a44910142c4001d49115001c00003900c91410700b900c3c40d81c110220f00d00011032040308001d000d04800d4003c0b0003000f171035000303038812035044e1700c01d00300403407882c3c3e40450080140d1480e07401007140d43d210512540030002c040c0300403a80600100c030142e041202854403807041101050101e942944844041380c1805080c4056030010071078903021745a10f6480e0a5184003030f4000788a44c5003c070742c015000e5401c020422940c1c6208411607170350b0506240c5541c10844030814288003d0701e00e040104a0300c100c2d0501b842603517021420000090440003000c00600030000416444202103420001 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 701602598 1250 701601348 701601367
    0x609020108070e09131a0705120f2419030c060324030b06030316110f041a0402210f06090c070b0103060b061207170106021501031b2102030d05 63
    0xa01c4c180c0020441038201203400c011b240072140070b040b003695505203682620800c00100e5121008103905003c0d04400019900d40e8441c501c1c002c08143c8a1034441c901000e20000c00c000550b02c00d00d817a100060400c810f20803420012900e0100d250815103240001c14418400c141d003500410382004840410000b04141a1001c0d000000190100034505110310020502036a23040040e500600c148507400c010501861419024421030300c1c07041c1d4000d440b480b1504146141600c5081034040d040b21031041046812030403c4001d6110f810400c2246003040c40042d9051070100116200d10180c030800941400e104041190b9071100600031002240100315080000f00007000c06030440c0d901c010041032421003c00022158000c4450001c0c4036640b9100f00040c10364030100c1c0c10700030003044c140007044d070740c98030002c80e15907c0020550141c2d6024100400010b0307680d040000307030328501c004480c0c011511171060040d000070b580312648818060400329001c0d880d06220800c40c0c228203044c45850b01c0e2801 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 701603848 1250 701602598 701602609
    0xf030702040c0302040f090c030506060903030a030b03030412081210050a140a030b0a200316050706090803090f010b030307030905010c060b031c080609150613050a030609020108070e 80
    0x858020702494881c4242081c0b50b020340c068a0241107980d55140c00c3e2038035500140b00805400c85503000190500001c81c10f0303400e1110880e059610050003171440c15010840075009041403860181d058401000700155800f414840c1e110034a104800040c0c0c0d60050a1040b9a581009040f080f02a00e10000410066a43c44002402c451465441200700454100021000074003a071024004110380c1007001610300d40c036442045070300a9050310807041e26892440f4660b9000445003030b0402802101007101d100d00820203003802d01d224140c007280d090910b6981e044550010382c0c0d822142d0b0701454130080034031020f000d528801c00c0150011800c210080c0c800401a1707206200d514140941d0703101d0300061100ac0c0c1c00c0b80c0710140d00681201c4640030450f03580f05000d40b105000c000021062070102e1560703c0c11241d418080e03601c0101c540c0741810b1620400c03504c0e0f030049594541c0d610004d02d0004071505d80460040007140100c0c0c000480d2241400090b291847c01004502001900f40d00d142c0c040d0b588 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 701605098 1250 701603848 701603857
    0xf0108011a13030311060a060503030319020c0312190516050a0c0609110109082a0d060c0503010501110c1302130e0c07060e03070312050a09150501030308090f03 71
    0x16041c1010340003004980c041d115109411001800940b8194003109040e00680300c1e008100707002085a2140d40c0c0c0c1500300c000c03950035000d250340c1034204001040f004a480d800601440201c00c40062601c0c0c2d001071054556440350060103940c000c6502009101318503072003916400100d450b81400039241991401410101c1504004180000403c2c040300300340c0f0480301c9084940e40448208400451800c0c8030409506242e08640043e07030030200170a600b8000702d1062010300524441507004643c081410540c50300314040203400c40710310a240c1010a0081c001c107070781c0e0310035a161542d4950500c00010600c40c0a40741c2e5540d554002690114551201d004070300388081c800100603294501040818982d0300380c0d900064840b040d407400d010ba04000e000c003c0041d10300c80d000070002071031620141c81d200e00070848090301150b10800304080b8400d868009540c041c00a8100055980c41c650f07443c803d0000c02200c4480095444005004164008081d03a8015081e0300003000c040350342e03814141c0d4a204 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 701606348 1250 701605098 701605109
    0x5010c0f0303090809090712060602032805071707061b0c0213020d020d050105120703120c050c0901061d09090304090e011b0f0e01090501050306060310030b1302010207050f010801 79
    0x165030a400d021300c41504242e4182601c024030b000c40c036007004800103060061050518048034a00100040c00500000803200030300c10300d1058080d4184114800c1d038515000003400002e11104110010001e140d0040c04440a2241c03000503032100d0990400c0000c07160780c4820311819859104801460981101e241255654119440d06006d140c9500c004041c1c021802c200011500200d44d1200c001d0880d00850306a0700141c4140440c550013240e955910001440043c16100c68010003100b658401d41d200856140140c0860391000d03070350b02c0403c1c5000030991080001403010303804d24282500d801da44ae0f160f100d0845d5020003c1c2050031000d901d07880769205c0e0341400c135540c0d206885c4486080d04079180d0003a40c0c0e10703429118401c03804050040c2d0f54070341c1d0040020f0160603c0c1c045e0f541c02000b518040d0381d03040c0e4a160450380c80105001081d8009040c00780c21054207800000000c0c00c007000140f1454456440c0c99203d4003603c00a85002401d8002e58031480e006440114943d921102071030449a = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 701607598 1250 701606348 701606351
    0x90e1902070b19140c09120f1e0106030c0b0d11040e0f06030109121d0301090c03020109211211010f200c10020a1b030201150501031806021309020d0504050705010c0f0303 75
    0xb01c180d0002104100c5640e0b8510303042c018622232030f41802000c01c501c900c0031200150504400d1000c1d2000742202c2641c040100b00030a034002c02d002d80300160000d007102d09008100010030500300701038008180c00982c0500d140d80d48107020800d040e285480700680292080d0000c2c01040c90710b54400300d0800c01138010500f0003500d09282c00f20403086541c0360300b151f00090020420010700342403869503820140416800700ba0301d25000600e01904581d080d49034a040305900702c1c080303615a0703105959030f84000c80000f080140e00000c030743e032402807107020716868844000103084080303248150803c0c1640c1c02103203c0060240306a003420040421103824941d610507005036501d02562064650b00d0902c821000e440400d02035100402d50158420800d20a800110024003a9650b0045003078031200360090b40c035a18032107030700c000291213078000c0c1804020300a43ca0451030344075054942280c00ca14034082126031900d0a0100b404814801400602400c1c81c052250010644600d504119803600043c1010f = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 701608848 1250 701607598 701607607
    0x109050402130f0b0a0e1008130303060305010c0c12050a0c1403040312050d0f0501240e1c0b150d1106040302040e0102070204061401090e1902070b19140c 68
    0x440c1c0b02402005030200440702c0500c2903ea020141042e008509031001003a11400382c442079250201600782208200d40c2c60043c2a0745101020340c949031103074000c40031b268442101100041c4203000303051b940002a038405050301902d04101090901d012644070500c0380c01c0010182041d40b05802c061259042020682064103035503107146144070b0f40d48080c0c4503140583d90a00c80950040080008100d40c80e800e028400d4401c001a0407524203125803105244640d040d40030141614529900400d0941000d41045484a0110f0384003000d05801c4081c20040902d44000c010143c8a125000040400c40006064040d400704600d2211000d0282c515045095107040300d544000c2203a010710350282c01800840e808041e650301035000f481b8200d2081d820190003182c01112803040c0c90140324144e507804070140c0352024080e4035860191030307000c8003225601e0807096031196000824019200710007552080c035001c1c012071418099032041c03000c0c1c1ca04058882c110321510080d49900404ca2210113540d6 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 701610098 1250 701608848 701608867
    0xf0301031a2a090d06020a09240e010f020114100503151512031c0603111005160201020705060c1c021204210204050a230606030117071703030a0f0b0109050402 70
    0x100c02004c0d1000f004140005080c6282c1c9074801d140c0021541c1c420310311100d181c1402e501681c031115400e9044009282c0c41005043c0b03620506090780b031107480d4000080c0c955800b490302d05d08880216101340800040c4c0d0020400350404129422840907100c0d4100d02d6030614441c062600302104807414071820040001d900c880d002801100c0c4c0d0615102d040c18043e400b000800c0000c0d081511080da0340241c0700c510113099003082c101030340e544122541d8080c0b07044040d400105400000302c0007a41107100c0e891020032943c031424010009414900010128402000e6186805801c00c44c05c107403c540040708507040e4000d070f1106443c00d03604031070f41c806450307103515885483d0b400c1a004040c0d800350800050040e8107816600c41c0a601c16003000d0a4070007408000780c0034105400f56601d94104904100401c0000a401c5001034070b03020700e070241c4458641d1403841c94059000481011201d42000040c050817522030310402c59072084003c0c090214146080000e0072400f0f052160780e000c1c0c2e030000343d08001c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 701611348 1250 701610098 701610109
    0x501140c0303070903030f0c020d0b150a120c05150a0c03210c12060b0313060605090a0e071406180f0307080f07090b06030a110f0301031a2a09 63
    0x40c0c10240c0c41100c1e100d1604083c010409211407009a000c40d51281070500090700c21800042d065030090204101064143e4601b6001d4000409294818000b6250142d055030750724007003030081c000e034116a08043c882c2e0900a42c03050203a4401482400d140c0c0300300380740040410640b04c220040341444071fa420b6a41c282aa00020148070f580603003000307400513102e564400d0b40951546111079944a038100442082c42d806c0380c00d02e0107950505101803002810710745160881c905068414040030500e2035456000c03521100041e655503500c2c50312080b4441d014102080244010718100050800140040001c51000d104503280704504842072840b151032070f1500210b20010103405800c031907180355982c003483d4803456070080c01d4282e4020b000c40052201c813180030380410301f11300400c40b0f8034540302c0301c0c400b00051a040090002e043e00a011130070002d10044040c2d4020745c012042000c8240700b54100c40e0034460000c080001d020202c0c0c0c407907883c5480354400c11028550b041c4000b035a4554500000c1d1 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 701612598 1250 701611348 701611357
    0x7060c0c030227070504050112020f070b180c030c131d2a040504110d060b0a0306060501031d1b0109083a02060a020a0c0f03020c031015050114 63
    0xf0341019283c25824000d410141015554460840b0714003240d46a13000700300e40c18411842414002801e2541184c2e07904640d034000c003141000300400c0d500d001a165904192010115040c03207002c0c0c005003000d08520301c1030007042c514510071800b50107109000c00c000b515000042c110480c0d5a44d98010045443c0901c44211100d003800c903049800c1c400010030034140c2481c0004c46020003880c250046003550400340034040c005c0c3e900107010204c5010358024403101201030b09041e04c0c10350300c0d25042002600c42c050000065030085002041c814107220016003500c2510314060f02120300c0456003510902d02040c14090000c104600740c3c1740b003c0500040350740da121a088083c2c503004101c00d42d8002c0e001242c5c2420300100d071040c49a81401c0c041542009480400705050150b00405c0c0020341ca9041e5a00510b00c8405d50300300348101c0c1c0e01d0740d20344104080300b4010403005030740b2264a4080c5464100303c2c0e09030b0407214910074848111840f1000c0c05900040c03040714103005103140c401c0c00d1030303002c4010385 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 701613848 1250 701612598 701612603
    0x1a070618021807110a0f0609031202030412030507020613060b010207170304090e0636010213080c060403020d1202010e0312011e420215090105040507060c0c03 70
    0x81c040c0500007040d000030000b050380c654011a0030042808480e0201044e10400160050900381d00764200c0e0b103072407001c0c06801004508011400381038026522041c03000c0c2d4000c03806699100b590603903d00002d001c4800c007034076540130755001904000b0760b4440d40310500b0000c0e03484440480c0c4541c1620050f0310740075084e00144802508814000341c4440004003520032182c07200c2040c44025220311102e522105d00341c69845003005c9410502000070321034114050f0f900d072108161840d048000009500f26004030000040c0e2010071031040203081420854a0032424086400c0f03450245103a0000d19003e144a0f0004c188240b07200c070500985000f90300c003004e5000d50b00306481d6158245035123003111030001d0103030186040f0440100c5c03010141802460065460070910303d015031103000c0400b0581150101a50002d035020244012900c1901c824540c4051481d002002d2000d5050842a2140b600600c101da86d03031f142204002c042040098180c040711a01c0c100310500300c0710340c100700d0005c04054101 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 701615098 1250 701613848 701613859
    0x1f06090603080702100c03020d1b0b070206190c0210090804051c0b0a110301060c0203100e03180409030c03080c0702041103060102010e0609062d100f1a07061802 71
    0xc00d20002d40c00501c1210300c2150500e041801c4594103a504010107070002d001a03015081a103649170068003508009000c0c030356500c0d5000216074070140814411105000182c014030240700784016501c001c515944a1544288a4003004500c025503920211120841068030355000f0814072101c28111801303044040d08600380b00150001d121800e4840c0c10046030b003c1802030004050300f80f0f51180310000c0c25022445440c41e4030f421411074040481e01000da0385402642840300c60403444c1d11542440007a54800346880c1c2c00f00240c103544c51118503100b05d01403030601144400080d84441651811649414910300310b4861601c0680c041c054414001e401a00c0e050303110404204280c00b9500c155400d89c000c2c008601c141040c541c0b00d5000707032140d180c01e902c0070021801404d045100e203100b00d0341e1903101066400052042034207010703095035001486030760041f061160680f1000a40007606450800c40f005010301941c000c440c1c46002c0d0050300880c0e84007000740c104010358594940e4150000e15 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 701616348 1250 701615098 701615111
    0x160908060a23010303080103080d1409010605101404060302030c0d02040f180912050c0f031326032a1f0e0c010912020a08190c090203091f0609 63
    0xd00d00034914240d400402d41d11041d08088103200361400d040c140c0f64943d036016056440d69980704819080007c4040312580c40d42c3d80c4041260490f0003040c841c91401c000801d080c0c3c07920701880826902c540c4001c0c100501000c400210202074012501200c0c41c80c540107907a43d680418000f20742c02855800034219000250000300703070305616400c3c400d9a00782c0c400b5500c0c66003002d589004540d002840105000e41c508102454ac07401100a007604500a8080da000c0c07079000c403020750030b540c0310361a00281c0d48500312050140154900b0014803900c0810040d020400e130f2400e01584d40d0203030f0440d40400759601c00e017140c12803400701440b220002c0030100b00c842c00e0035003441c03010010650790815a0080c1c984080207002203000564000c500d50183c464403055810240702c205015030b1024207130b07000108040002140d040c01c101d800d8001d00400c0c0450f0107643e40c4d02d4a2943c020301503010b80589030040c010b0180c20320010525885042a2445503101824000b4108002d0300956200d2001145040c0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 701617598 1250 701616348 701616361
    0x30604050d03060b09011209020f0a032301140f0403090302060a0e010212040b0d02070812091506030c0f100c06020c011a0d0c030308041104020f0a0e0111030316090806 74
    0x81c84000c8210103803010711025444555011260003007005c41030000707200c2a0401450b51117584208205030014000c0c896504140c0f01040c0f0b08101c55208a0360907204180300c2440d02d11039220243d890720035000900c070300d824000800c0700912000d0014042080d0382c402042c109801014518003c60340600101e44402010b480681140105100b4901500070840101c84007801e030402c43d401c1d501a02d0720f45042c0744500c9244c00c0290014003007100c012004101480348101011a1103102e0701c10400101080600107041c1c0303840d40ca000e03000e81c0c0203901c01c07580d0701201e9031100b428510041080e18034015518002c101190300300c41c0d000300601003602c0007800c41600d05041d048019103000e0215046d0303100c9600c030240400c0750b0510070b01400c40440381c201480043c3c4108035248c0c005010794100741441d1700b80f400040490303101c002183c4001742d0000d040c100264009a80d18426403013400e004480340c001c50b2120703880b484000c10b00404c896082b00c0f01040107010f0305803070024160880031a16a07141c1203 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 701618705 1107 701617598 701617603
    0xc031e0103150f090c0b0403051002040e160c0b01060905031501150f050d0509030409111206150d0e060405060c03011514071a1b070b0c130503060405 66
    0xb0b20413482c082041c001541000c0c00d4803140c1d4940c2d5514515080d4a40807481da4003c1c5898010b2008101582c0281c024542c07020000b01101941d4107a035500b107030600366000c0d008188200c207000124140341c0c00038038501610b03800e4049844100c1d2102011200741000d1089203201560901d400303c0316441000e1000700055981009800c5c5844801c0b43ca0640780125890b0820f0317030000c5000c03c640c800a01400540382d60000c041890802d00401c000388840e40102014068002803040d881158648030072900e1401c590403081009501c0d0412241c3c5410040c1c4003a47c852103500d001c60b0301180c40341d084038102c803407889280c4d4429001120640d02c003004004507444040c000d100d2180030030044d4501c0f00320003000015409641c9010402c0e42d074480310040c0507a50300c030401d00516000603610552103802c500003e1880d83c403049921309120503441640c010a4050054509020811000 = true := by decide +kernel

theorem cover : BRFrame.Cov 701438848 701618705 := by
  have h0 := BRFrame.cov_init 701438848
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701438848 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 701438848 ≤ n) (h2 : n < 701618705) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
