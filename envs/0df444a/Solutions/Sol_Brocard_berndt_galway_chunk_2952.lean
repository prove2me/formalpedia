-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2952
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:13:51.41492+00:00
-- url     : https://prove2.me/submissions/c4888de0-1f81-4931-9abb-207ac8c166a8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 530755395 ≤ n < 530935251 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 530756645 1250 530755395 530755403
    0x6120506030a020102101a0909030702150f090d020103060b0d0506040b0612011a0415090303020d141b0c0406080601150306060f030f090c0b0304110307060e0108090c04060803041505040e04 83
    0x695101007100d042e00e603902c0d41081075003108d00c8000b08500e19001000801c0c0c0c061085600d00c1c3d002c0c00d10b0341003142e64040d4190340303102940c3c2003000f601366140012540f00304610516011540c2a00da41c03140110b500000034230064184c4880602141d0700d01400b03145d2051105441c42410005004040700c91428107100c0c009540b0601044506840b0210342154094040740e4442c01c8050b214a80080c00041e0300d10084e401070007182d4546d41c40c240305013802e040c0b451b410001c3c9401c1400c5030b076101480b017600001700801c43c402d0720329080054885002c0c9000820565001e405150301d000c1004500002c110b100c0d00416240950500146420000c0601005098600090551203664041004010802c40070b41250030f1800c4c0020401c0e80c010045104034030517590700244001500c141682d0301c40713a02605002c21000030307611115511442e0241c0d4040200310480395001203e8010074110b41090308503680e0b503000001c1c01e001c4141381500082c4000050b2a041e40761500c0c2c5581c4001001d00980020 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 530757895 1250 530756645 530756651
    0xd0c0501091e0c08030a0e010305060f09090307060b0402280c0206030c0405040c090b0a0c0c1d040b090a0c0b0307120c0302091c12050c100606120506030a02010210 72
    0x401800025406951034030307030003800281200c0350361546079000040d140e8102d58503442803001156148004c01030320043c00c51034480c54041c16900300158081e09000341800e030010700000d40c0c0d0600f541c8145200380035204181c042c50b03a4101324245103040e218a03008d07890165004100400620100c509040c415038041d000105403c2d551910440d15942c40c01001b03588202c003c0203100408181000403c1103900c11501003104030300340c00c400d6582000a01c281c4c00140428868000d886006640640302c89201e580480e1045898000c0e01c03040000c950404102c100c40182040300300001d195030a0307081405074000344580041940d401c94091005d008203081c003040030020400040c0144a00c0e0204020940240544111103000030003d4100180e154800e01380001c040c062180001d69036282a40c00c00d5820901c0300401c00d00741c94a5100e404000b2440c4502025149210100c0c4590f00c0540425901c0c1995030812600c1c03c0141e40740940034622075000f14200e000140e030001090520854105004 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 530759145 1250 530757895 530757917
    0xa0b07060e030c030304030201021306111c050403020a0e061c0b0105010e01030b120f0709140c09150406020307210e010f090f06050d0c02031e0c0c061204060b10020d 73
    0x1a42140502120305003d40300c0401072000305034064000d4240e034040f170100c66040fa0380e5031070122006004080c001e0155045481c0c0d01c0c2340086090300c1c06894480609150b4a41030ba01d60104010f90b5896100303101001115040c09005e14001700c4c0c2c80041c5503010700d480191181c0c4c0d100c02100e90341c18814541400f030314001c003050030b0b4041e820640805400a00503403002c4105880247c407030307070401c0d89116107025124001c25840c803103100f114070844406240500310340e1070010311102c1d82d006a15040d48680101034800d80c038098031300208080c0c02141d010f1506c070409864290300001c0342120b095035299012000100c2c265010840c0032300b10400b440d003551807012426042d40c440d4196000103003181550280480c0c034580100c01411001c901000c100a0614070342d20032a220301500481c040002e208000d40c0d09406503003030280141c40100c8c001d94110b00015030006002d41e0112201004044010041005000d407520840403502e000703942c0b24140c1e20820724005c2d25145041344810a0009807142 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 530760395 1250 530759145 530759171
    0xa0608101505040509010e070e2406130b04090501122103060803040f141009261507030b010309080301092d051602070501090501050d0e060a020a09050a0b0706 70
    0x140d41c010400604100200e08064501d0350282c03004030b072185410321456400140780f050f44001d00e0700c549510b41c1c1c1031720b1950345441c440b1000d0190450b50350b0f0002040c084c0001d10003172441c00d44004c04600e036101d41c0d29481e0005440584005a008400905078600200e0109588010510380041220100040f19940c54400e80041c05160800d485038800842c0105079492220b0400e01540d018240d07260141507400c0070031003c1c1c0741e00d240314400a0100b40c03040124031601806c80e03804a02c4029044840e0081c20141c03031800b510642841c82e804141014800c441d030701441500001f80302807a092040103903585030707100d440c8010301ca98072020381d50b490804d0052030802c2084400e40d559070350703900e41450b0404005000c0c16040c0c0703400c000700d44000609101180001001d004a48040c3c40d46502a4074000040d0340c26004280440090b41c1c98081d00ba12024041c02600d1103607014020058450344c00c172200801c0380040345c000c00d000d064654000c0c0420b0380302005407041c56074481408218a008020 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 530761645 1250 530760395 530760431
    0x904030e04180602030718050a0501110a150903080a02180f0406081b04050606130b070c0510110f030c07030f02030106031e05060a050402100e0130050a060810 70
    0xc0784407003000b03400e03001c10b0810406400460013070741190303241502c0116031205064401082d00c11a0b5105c510003804000c0303540074500001c850168403094075003104084d201c0c60740301100140300800c1d582d40ca600100415400c0724a00713030410031860b000c609220007480e01c01d00c4107119903805407080080d9044140c00c4c0d07541340c01400c0a01108170507580b1002c14034560014060310300688038816810800040c030310381410740c01d0302e501910608000d0503092401c00c60058550007484262240c2c00340e1100030655440c0e40740c440304008015501e180109940c4660181007019034495440e4582081010b100c0c8500e00245000c143c07504841500c10009142c4000b078010310f2940d20060200f208240c055a0694469141480050056040e11100da0b942000c0070704549040320001d44c041c0c00c0c00c03c984001441a8140c118004040c180f030903410f01000e004000200c60807001882e4900164640b40d40c10001c2e01034030b500704c0d20760398007070001c00c1c2481c103590786994030b541000e4810360750f550424a10082c888 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 530762895 1250 530761645 530761661
    0xb0903030a08090f10060f0501180b0333030c013f0510090f050c040303180b0309030705071205030f031e010303030e0f060105150703030204030614240904030e04 71
    0x60200c2c1c0501d00307410003a1740500164410031810510700300740061254010750000c0c0801d0140d25030040428100611842550806060005000b50317440508550300d6203c0d0592044100703240980d80203980c0081010315240c07022090034100104c07074001030a600000c05903071a80810107042c411a003070042e07003604044070119070f44c044020300b4001442180c208004000060f0b5516030014001da480481400058071015100540340c050200000c00c0828490108011007000cc4c1c2c1103000c4080c1d0b01c0381c040310180c0082c0d03441c002070340000511108010f41008080010084003440b00d011120646030152280140e0b4000c0c1d90b02c0b500000024281c2a03145000401903140500b0f82c00b01e961a400c00500500d01c01c41e060004c0d01c10210300c2c960015000603040d041b2080105600b02d05c50342c14424bc1c04075001180c1c100d09042d000d0001000091103401034002e04103801d0704107000c0d0f2030300405001c0300d0000d068070b000c212a41100c00300d2003a199142040c2d40582c1600708504040510b42c0841d00901d441 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 530764145 1250 530762895 530762923
    0x2040b07030908011a2b20010f0f020c120102120109020409180b071b05060f04062702150904020f120106080f07051303140a060b0a140d0614010305030703090b0903030a0809 76
    0x1c7d1000540790340c4601d0404440038084c0c0e126451909507240548042c0d1a0610450242c0e001c0c440200315454914410070207507051400240c1400b0301c0c039030051005007007a00142d6429401090a0000281510a1050180d104600006043e00329250400c20000c046c20002c2080303a103d4a01c083e06015a95211940c0e622804841e4245450b004c1c640d440e400030781381190300da810040100b00a00382810308040c2c004003c02c2041f01d01d203081d0308000e0368440c4014500710386c4500f4060821282d80c0c901c00350044194400120b40d8481140e05125030011050308080d00f072000800a000511141e0f50384a6440421820107950356085403034602008d0206603c02000d605d01e070501e01c20481b001040040c01a4498030302444095119400c1050343d179164000c2544030344200710210b15615140352501032041c000c0000248583c119401c0c03140c010400d0f001614103500004020082642c0001c1e514000e100f14800b1034241000301002a4a81c407519183c84104640d90001c111804400d0121440ca800c80f = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 530765395 1250 530764145 530764163
    0x2040b0d1503050607091805040b190e0304080705040e0601030b04110604090227041e3b0609070509040b10081606080907060c03050a0302040b07030908011a2b 70
    0x2000b900100085124090051103030780c0380d40b1fa40c030008028003034140500c0d44000d02c1d1400c0c3d40d40090840020244007154208252105024021000d0610003000035010a00144c02c0450800c0107010a13541e01e001000da07558060f81c010004100603100c0d070b03038103d031740006040704608068000034214040d640041d0103291001a90390130800441004d03ca6410602003c12007240b624020030048031170b40750306242d12205c00405101d0000a60380040c42d5611403009110038080340411082c5c51100f080c05540c420906285401a401c5003003107000e03407100c20708000701103140c03c082c0802e0b0710f5403003e003000785100100c001240700c183e420f0750044040e0105500b12101d14004081c1c2e244071070028850340d00412820030104000b1080494900c0680c0c429403a094481b00c03565608a907540c3c07200c01c081003019424813011035080540d500a20b4201e019030780e601c0b50142044285801c480c3c00316610b000391112001030900940700c1d511441103000604000403c1c00c1e81c0001c5140328803c80c20344c01491114 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 530766645 1250 530765395 530765401
    0x30050c011b03141825030c0b090307081c0f0e092409040203031909030b040501050a1a030d08073b01050304030203121902030403030e0f0102040b0d15030506 69
    0x1500d54400c5103220411440701d0341d1034072000d1054801400045000000303400c96200d0b00a041040501ea40350702050205d119000c50396500c41081c41141500040c000d46000540d04400307140c1000014040c100c0c0a024204410308003030908041d04155a02d003041c042070081501c030540c010044100014030190400c40380b4542009182a0746040010b41040c00008001a661034106100780c24801e40e8060000c624081c000c0d85010801d000c4140c0e003008018202e80040002900360b21090b0150348114000b00703450030400b81e0b0b03a0941d81c2d0019419501001b03800002d4140c0e400003159001036000741070403459500e480c041120110b92520a681980700c642c80464810811064124a108003d003007102940d06201d00440e414442501c015006074030034001204010152130903d034000581c1d900c403d412220099101c826070700304503400d80c04070781d6031000401801420f104000070468400021490203060004c0306605004031810540780aa031000b809120310005250301004d55005000c881d00fa00e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 530767895 1250 530766645 530766647
    0x60717070c051902030d020d05090402070c1203120b0103050411010305070509031e070f1211030a06050702010c03060b13060e03030c01062418050d240930050c011b 72
    0x31030f140307008034040e1144000b6014243d00c0403581d003c0581c580d83e0b44074a00b039242010040a0b400c45c08086e40d101c21000800100680c0c40140c103004607119071503001c44003044800d000d0480341c5c5490000d051505101c10040000c002c5200322115a00034200000e0a4a40600450341405100c07610303901845075218110091426050b00003545803180d040745e01443d2074504251030200c4900c1880b651072101c0283d075000810003600b15502c07038000740c215000ca151584a42c0c00765041a501080540d545c1c42c4580c0c20243d26000e07001c050510610f00910300404811000740481d505c0c031442d42085944041c4a80c29903040c4101d508403e00003000380310003922a0f800f504c5401c440b80c4410701d011011041083d105000e00c15100f84428800d8118400616000034040c91403c900001c07201d03009020030008806071410032507082d00c1c0051074001480c41c064a40210a030324180d01d0020350000200500d85605c00d00828603034102950700c0d00580750454070000601524032068466020545c400c560002c0b1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 530769145 1250 530767895 530767933
    0x2111070b07061104050a0b0c0309030a0312140103050c0f031f050106111c05220e07140f030103020f011202190305060d050a0209130f050102090111060717070c05 71
    0xb4001d40080001410741810030029120728498550010b9580340108010300340c6001405603c0384410035649840b500000003800c080e0b480c0401c801003004414032100072402c5c1d00c0b412880a900700b204c2c2c0d5040d4115180c2c642c1e41d001c06403455100f51408091503145480130b0180c03006459036540b00f1202034401004000180c03c09001341c00025081603c0f00002520025031445036000d051010383c00543e08210881311030348034090055056a615035031072011401d56401b0700062140240c9202d00e0704000ba0000c00c003d20050301c041000380305000e03507440a00d0030001c80381180e504a40d0b1242d0050307104010b07141c010030220003074500343c03001c580c0c208110b0560b508409524040d80d41004595a07200821880a21011014060303a200703007400c100500b4034040141d0040342109901095082c0f41d5116045140c842000301c1da20b94001c50343e601a0f50700f01d00360426203002c50010b04068980341a00926000845004128194a01000c50b1002d40a20003507441c070b6400100740d0310034490141c084944 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 530770395 1250 530769145 530769157
    0x4090b0c090f040e0606090f0f070c391a120a1b080105030607140d0f06050307090e06010b030c0a03020313080c011e23090c090f07030b0405042111070b 67
    0x1501c1f860000a0403a1400042140318504904190748640c884602c200c606511100c012540c260600d0b804072900c02104a00010000e50510740c0340100059030301040480e40964048840c51402d25545041000c0d88003c0d100706240500c01115190f50310342c2d41c82d0203814004001500c20940b119003821051340100f000b030584200398201c9089895000b001c46803000041901d13060000c00f40310034001802503410980c05520190804565981c071070001a003818400d9014129583e99003904801c1c9480502400b070040c50822a03140c2546455102c051151040d00a20350030581c2c0000000c1f03070a10702c000c08250312500403001a4880f00361074150380c02071580e40e130040e0101c40740a00c00d141d0142c083c0520043d241000101d2003400c5494041001c9101c03024000601c80e020b000d000e903219841d1900c65a100d101501c442c410070b41410140501114600c0c0781d03450085042c001040042111f904140d085082070710000300420510b104101c4818554266482150064542c0003807803039110000b4200c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 530771645 1250 530770395 530770399
    0x13030f0501110901080c0a03110a200c0f01110a231c0905150f0304050d080c09090c0304140f0c01030f05010e01031403040b040b07060b04090b0c090f040e0606 70
    0x4850300c5480070b21060b41c000d01c60004c2c0010007240003e000c100d00c00d0b014280c0742c0c80909001c07403c402c010b00402c0c070680008038403c0005c0c0104d100c5c82c4807c0d032603c420040047c0b841c800780840c42d030101c010030f40d0b0114424026052207030000b4403108101c020030240f0380058016030309007103c0600203021070900326aa601d84005200b283d060000900364000040e0028101380c030780040482c502014015030749e44040000c0101e48043c811003400e40c0c21034008511903132045002d4464801c040ac800b80030190040d180c0b403c044800d0200391101d488a49529800074241a88070313840f552146000740c6030421025954100c3d00503815191035070300c1d001407400e1207401c098a041c04081e2244851400702c035024030902034120360300f138010000f140c282e0704030800000026090b0b038646900ca040701c85480d4010392140f2074808000801c1d0017400300a10420305800404c48090144544c0d40e140d800c2d440f840a8030b243c000304000211011f80350341e5500d081c1d42e07421001d881403041c2801200b0700e0b502d03010101e500794 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 530772895 1250 530771645 530771651
    0x1203120c03020d050601080f06150c15040c12050d031d03070302070311040e0309040b04020c06090a1203020a021b041b2003040305071202011205191104140609030313030f0501 77
    0x15102c1c0d030050001500c211900281400c0581d1818201300038806400ac0c1ca201c211030400000284801c203003c503440440f4100700252443c14185456a8031205a41c8402405a01d820030300000410104d281000b070040c51502154000c4001071f000140503a0f10311103c903911000460104241d0046401c50803280903030926107242e0a40010300041d1840780d07001c0c0810fa0001c06c000c031003038a0194802c203081500a0801401c1c00003000303040f0b19060382034608446a038000c09103082080701c0c00070846e6802d180b44c030f8298204400404040e6440501e0b404140044002c2005410540c60740d501c03c20030702504509003071100c0c0d0401401b900b48010341c0c59164a0240d00c824102041070008101d0f001c8950000c02007400361300c1c0107256410b01d424603034200c1c100110703441c180c0e81c415050b000701030107030032098191001d140d40355164004682c03c0d4180441e0a000500042140c0d60140c04c0600b8124010344010755140307070307000000742584190100c1c1c4000001404002c0144501041c001c8046131142c0020 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 530774145 1250 530772895 530772901
    0xc061112040b010803030903041a160b040b0c070b0103290703290303090907170a050124081305010f020a0c0c1a0a030209030f01050702100c0804020303041203120c03020d05 76
    0x10b480e1b200446885071203620400080051280348610403100138141c0c1c11040c10b205050105500c403120300c65040e41c404400c01c1c02d02051180801c145a00842115441032400d5425070f5001d006038014440a0315003e00490344900703504c040995252802c540746050312983c40c00610144c000d041020100700400c0d0b049458041d101c0c07410300d00030220b100c002c1c0103509144c070800400130210001403981c000c1040c0f100103841c10310403000c900e1380030300c20180020400c0d42c185022401c0105d00300d5031a2584140165600c60015004922135402030901a0914000c0000d0b003061400341803082c1138607520a1002914100e0302c0e6101440300c407070700e105040091a15942d00405011003c01c51220303880081c081040034203031f81c00780d1b005241c1c1c03843c09030aa40b1801c0001d40400c0c219602100d480700941c0100b518407080c8580707881122524811410160320506141e00400d94034043e60107002440106250204240341c014903d034011100c03c90b6083c0009c5540720350040c0a5001310441e074960718201804 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 530775395 1250 530774145 530774159
    0x105071e120f062115110712050403060b0405060d0308060d15141b03010e040f02030d0804020a05120a110a15020c09070f021903030f0f0501031a04080a0c061112040b01 74
    0x80022150410b00c2001d080130817612420003003440c4101c8903141e1404206110026001180b41d006c0e01d66a0b440d03042e15281340d41403c00c103a0315524640703842140750104000c2d0301c3e5240760340c44d110b113a01803a205280e0341c2c03050080f5040401c10100034246803460010b1300a450099080707110b40c01a000400120f0341c1303540b44103c000042c02940500d0349042400144032140b0074500c05540b182c0140c9109803038ac1a00d401203424000740d18469030015198604010a40c20441c0d8520000d020540380d8018100780c04140d29241c801c0004001d02c090348546110030380395694001800a495003840c10810503200d280c0c041d41d84c6c4407407510540500502400210701900610407007007145040d070040c0a0480340e040c5220516000418201c0505581c0c005542103269117120b8440100c011140c00240c2d9419410f03c0c005e24140901000e189000910801000441030000da0f1006400d600f00883c205060345400d601405600031b404107a2000480e80f24040b0700e0384072825006600914440d00140d0322110 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 530776645 1250 530775395 530775449
    0x803100602030c0d0c03020705060706051f0807050607060b120d030b011806120f021c15030302121303061806391701080313080105071e120f06 63
    0x1103c101c540244040d04031680c0105115442144248141d5514030b0f1030380001000d503080f420701610301d50380e80e02c10003444194a081103594402e4007070341c10403800d181001480d61105079018180c0580e60110301c1c4410040e0380d400090407140020004070000e210010103e80c1d940c0e400d43c000d00000d040440f0380704603500424218104940400381600200e042000c02d03600000c0b0585800c0189036903400001e5001c01c20710150246001d032500c000c0c030b9400703d03000120940c0c0b0000740c40d04090000500402c0001c1c0c00181034210342408885142d100c0f11801c82403075060703115138405080036007000c6c20244018000d4411760811031003400104003c00c41c1e41d602181c3c0111405981e903501046102d5036640c501c640c81c144008807058500703175640950003002200250400e0380640c546900102e13a46003420109424800581500c10003000303d403500c0701004001c00400c0342c4d04c940e0100e0003100300c00c9591060341200074050407100e091000a1203110003000030403d0b071140c807440c4060f4901c1c0c0c3c109100940 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 530777895 1250 530776645 530776657
    0xb06090f130602030408072f030303011404051e01030c0515092121030103022805010e0103090605040b040b06030d170a181a0c04061209030504090603080310060203 72
    0x490340c0501c101e40daa900c0000b544090802c0d02c806000380400e90020300d0b8120841c05003441200803406a003901c0385403180c064001e0322028401e4109100610101c601c603e15003003034610458003c138550302c03071070304407000152030500c20240417003140008410300c48a51010f1045030000e940c000c4071000080501c1d210340c041c05858541c00700c400000c01000d0000c0100c00281d8102d020141d80711001d40d6003003400701c444070040ca0191140080010019481d008075444030a40d103181038840400000c4004d020341d00e00c02d01035203060046105440c40e40d82d00c60340c01007481c10340c04141000103040c6800d2031080c0c4901120201c0b01d655210b00018a03a080c0845e0004000308a5101c0c2100300340401d0602400f034500901e0000829a11681c10400e840c60030100d444150081c800007440071030741a800910306a0007840f5501100c42000f00300083c0ba401250180440c0c8140d0000800d50014602115240b04560003a41036604058000c400d0002440045d402141420501c805060380d031141a41c0368020380c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 530779145 1250 530777895 530777911
    0x20604052d100509010806040b1e10081018091e0c06020708210f030f0a0e010c080a2307170604090f140304050d1415241c0b06090f 58
    0x1441302c400c1c1c550045650b5a04080000e1000ca0740070b0045c801b08002220500b441842d001207014811410304014500f42d070b138070006150007140c82c6040b0300c1c019502800d40c440d5a1600001c6101001d030140b0603808815415840980390000041900900d051400803420581d0b012002110006003503000198041c221360b49540039110214031a4003007030b071100c4085115040340f60100111640c003a007400040d0700c0f0301e04c1c260803e5540d00784007019608a40d0a49121039440c0e00d0300b090b0755115504403048a50102c0c4034000030a80c2024240309614011550348004040e141c031409001c0c546422002e0101111220031031469540d90b10400c03c0147c5143e144054a0803084100d40d07004210424000e5500c071003008200d9140c55601c502254a951209609075507030720301c512401c9013140d424031030b04008107044502500e06007443c40c000b50800c0b0112202108220014440c1e00c41c60700d4520628522095500d0410901c49950502003c0d40d00700f250468403601710707000040c1c542e00c0c071152514003800070 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 530780395 1250 530779145 530779147
    0x30c0c190303090213153003020d090b030f0402090a0e0f0f1209090a090c0f12060b01030207050c01050c0708071502070803040308070206071e240b0d0f020604052d1005 74
    0x25046100f4100402000039400155082c003c446040d034484440a007c1c038030a81c0100456503205030300030f0a21100d5000014569010003e01400d00d044840c003a41007a0100c0d90400d242d2501c810140c000c001404070070380c4a0044aa00c6042840d0110b0b00a62000041003602d8000100114000007403240c4002e4507403052402c0c0c0442c650a11591000c44914840c9420501c0d0f1916980c9041a6248035480340780311a10a640312020001240105100f080f070a00f800c0d4105501d80c4d80712522100c501a8060400001060389141c0440030090740000f810400191103d55850390321001928003801403840161107035600004c0d4211000007103800303d036040708299080011070703030030050164801802540c80301c043c44e071040c1c40201d01040303440d5614460b0452840c020300e1407444c0e401c0125110425510039150042d048016143c4a42d00d80d6916804510781e4180569840081d40c02d00560704000d800c5030142c2e00400d0300a0440c8a480515030104400d20340c601c201c02c0c104410907580407011800214 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 530781645 1250 530780395 530780399
    0x120e010f0815061315030609060e040209060a1206090c0509010602031207090e16021002090d080903010624030b060a0f0e03010603060c091409010b030c0c19030309021315 75
    0x20404602d01c8031040c000c080e5494131010395160b92000394144c010100c2446240c0206180c00c2d018840c20700213020390381040c08460b1800c149403d0780d100040c00079004000c03210004d01e1b2580c558522002500c1c001041a410340c440e400c002c070003010a9803040b19410703070500020906180c0980e8240c12a58035034000c41c6800c100303c0e000e00300d5a03400b0304001d080c02454403020074040740701c2643c00e104400c030480c0c1c6900f83c0c81046000b880c0010b210f0003c6c40c1c10380b041000301031030f894003202c0e8045180c2205900c2e943d03d41b0000864010031a42e0300c4450300f6003050420310046400440500300f204007540d03003880450081c0d01006603521442e005600880c03a4017210f4000d440c090340c041e40010034018000598580e0b071342c440e0400c0c3e5400303140701e400140220b14241700c041440000e4110100e42613030315000310340c140100001c1c2440040e103240080744010594a00d844020005201009030b40c490714046280345103000b40141c4001c40b0304034071554807031003000000600e9220340003104100a4440759168 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 530782895 1250 530781645 530781661
    0xa0b04080c070e01171b0f240a0806100219030e01210e01141b0c0a1a040605070f0903060b03070503061510020a150f1404120e010f08 59
    0xe4004851121180a09480003d0302103c1e0042c5500811004620740c3c00030310103002c41410078490412000310201e564440c030906807584000805840d206071208040c04803074070011503114441340b0040240e4000054242070031b03503200d0001400b81c0030a490304010b000035002e05a85550a800c445a402c500340000c44001c02e2140c500301d20f85807418102800800c1c54030300d00040240c12010030b0300c4001d84600303003400000024880c0298003032a80a41070164101b0030081000d5480c625000c1c007403040d000c102d600c40040203104805002d40d11160f51440003600001038990724100300c0d402e40741c4d5884c2c03000044042d80102000c00400c6984d40d92284d025045540300c500901450840d660540b0074420b0100311a14200099030007401e10502c00c00c1c646540d603042003164245814a90f0464014103101d00c0083e114080059819941c0a004600800d22520101c01411406035200590344070906200902a0410340380003c41129a80d182035000107000640380000304040c3c5400050340240002d90071 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 530784145 1250 530782895 530782897
    0xf0510020d020d200118121403010b033c01090605090f15120105090c06040501050d050c07080403080c160503071214060405150106080103081213020415090e0a0b0408 73
    0x18202003c103001d406044407a0603402c50340c05411045510b05043d4a55087c03202c140340c81c0c00000c4052400c5844e50036005d8044a980c081171080d410038420200100d448945000c4c0c02002a6020541a221610030003010501004141c0350410240d803080e0004501c407403041c040d442c1507a4024017140a03d4031030b08032212050100814004882d50701058000065940c038949003129483e0000214050a14140b104c2c00d10a5039220b0074411001084104040d903002000e0706c1c50304242c0240050103994902c54101288150310300140032440018020040191010140c03440041e84012510a0750300e1050441c0940c0300380c010550b2640c4550020040482c01e942c030016024424444a6040305101e8000b030328101058400300d9203600513114040348900d40c2c1c0d41c2039004103024a02040c031949192600722903031007080005560740c4520305c00070b00e01c428001c4012040c0c0764090402c00c005034011840c0014800d0502030071420a01384500e01142150000b00c000714550001e461989540f00c580d110001 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 530785395 1250 530784145 530784167
    0x2070f15020f12120c07050c270f010810090201050405150708040305070515070c05040b06130303120e070f092004060206070e030d0c080903030d060f0510020d020d 72
    0x110310078002c60b8510307400e081c0b0504110201c20040f00f91240c5915101d280d404500400e03868494500703101044c04104009080c0712154010740b1039224022020341091014800705640b42c1c00e403140301c000c1c0442c0c01e40784001541212007031016940c100c04c0d8609030400343d40002c00301a0000b00140030074040c529001120000c006c5a68032035601d4a80c003551b0350003190b00250b1058880303070802d101c10000c50810146500c5106a0802e900e0300e0811660745003004545c05020317884c0100d5603284072a25a80f144404c882d003211034085102e040c10342d2450300070250755001443c0c24089080840055400c0e800213440c600380c1d1105e001c03200307180e4101030b00000103100700c407140780c400b1408a900302900700150005001503c00d540c0541200d10302088090030801094200358002d911600c03c2c25070843e1700502d13003803d4940c046204d0b1f617a81302c003000092840c0203001111001da0325201d8000380000764000303e1000c8a07425200b9020300c00b2900c07016a140c2403680301c1c90740542c0183e007002d015a840f600c04440 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 530786645 1250 530785395 530785397
    0x1050c03091504060305010e01030f260309010c0e030f151b0a020a060b010504030503070201120f020d1b052d0f120403031d210c1f060602070f15 64
    0x30801907104005490024580d02c050500340e80003c0c248006a414000d09001d45207840d04548194511f80d10811100b00c50900130b01075899201101c02459544100340f400401e81d16000d60f12030818001050003006c0b81d1580c03030089005100ba5030701a00380031900404011500003d007201101c08582d11410b000000d258100072044200c0c4d4007683c0401c1e00c0540741c0182c1680c0200007281e403616010003107814090686050050a2000f000051000411141c44a5081ca010301403405003408040180105424400c4c09500108204111143c603a109860801020b481d41c20440c40746402500c00d40310b10f0010040d031403003410400c81540c5094200640792050030781c00d6490443c9002c1d5803020341e04131100080c0c07501d43d10750600040c10f51500030038402d4419200c1c200079a80c2d00008040d03641e4699206880c5005045000c3d0034100c0080c400d8480d00e100c04020f0f1881340c585000c2e010300c6607410308000c850305490040049206417001a1040c280e4203003414035881e071802c01464031903c15005241d40 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 530787895 1250 530786645 530786647
    0x20c010e0303090304030b090c06180d02090921090a1e030501050406240b031f03050a0524010302031504060e011a010f020f0303070c0c0e010608040b06120a0201050c03 74
    0x48000d801000118400c0108101035030700c5900350702d4642c10840d00070300700340b5195100c00d0000303c65a40304821962440c88140c00c6000a024040c04580c02c8001420041d5000c100300013009807422011945545100159002d43c4020300a803003010007e000c2c08048175000848804140580300ca1001e42c0c2c50366503d00100a08140d590780d8425080d81d4003114203c50680e200d801d480b00c690380781060b40c141801540407608800d4100a0300300d13803a0000901004c84028074a111080ca06101a080c3c405540c000d0290f8400c206541841c5036100b1030921007414602072621500c902210050328181617907801006041c1c0c00700c1c00d001050b24448050b00c00d50f0515a1200c900181400921401d4816881c4101c40030070744000c04009403482c02000f025109640206e20080b5000e8070100450740d0000c80c60502060315880c5003024056078580e5006464804807031000410019040b00806200324411039100040342e4800381813100c1d800c9100ca03028000d07400005030307000542c0607901030400b022100040f2 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 530789145 1250 530787895 530787911
    0x40f0528021509011718031201080d0816121b030509060a06060921080c2b050306040e0309030a03120f0203071209020402040509072705030a020103020c01 68
    0x86400284895010200d0200c0002001181418108200c020030142003041c01c0162910010f082c80712820502c000080318800000c50054007481041e142e50003490841b911010450042c80c0d05450a000e400c2045c4140803034051080d200d0103c1d240301e400c01d080d0140080081c02d40544041c6a1200030004440d200c403500c400310354030700c990000c0050182d5400b02d414140300041130b08251000c0c00903040d542c1445824410f0307581003050b440880c0c0d6111104080884003151749114a88407034402450303c01c00142441e58544001407510071605122566499400880503151011440ca103000c000300da0305100080c1d25180c140c0c0003490a9009000b520700c4c10803042e0009007880381d10007080300450190315400c5090202d610414282258024045143d403c0c245400303800d101040920f0307050592219040811929035405440043c400501124464205480054602da0b0380240702c1c0b006a86020860300c5401801684804454014000e840079607581d8004501035030040842ca643d0759219624 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 530790395 1250 530789145 530789173
    0x3051603052115030303072c0303030108030d0f0603020d1209080601121505090601170f01020a11190b06061e0a0c0317071209140f0c0f01050f03040f05 67
    0x180e0442c40707000c0d4044002e8604080c07544090030114428034040c0d44140704002000740c0106c0e002c01006c190000d52074184441c034000c07040c200000821241c050002000000b55420000050218418500420300128520000c41c1d41111b41c5480b001c0d501c8464108000702003488800c09041060072803030403c52290703c4030415841c05000303074055100b100c8043c908509000d070559203440c0e1070404c03000070302031402c0c4803030b05541d42c02040c001d126580c24601d051380c0c8440002c0281d20f2000c440d0000039510780242c2e910107001240c01d50080003103070042a80341d058102ea01800c13409403680c014002c440e680c0302c3e68180003464004244100703d104000394216100182007028200c2d0100c190b0320513007000018a8020850110307825030700101c92440b010b1100d005e4001040c2d04a034000c04c00c0024044c81c0c582080c503031070341e504c02c2400001e01903031090b49030040003c43c60511741c43d401d4405500615010004481911a07003074074151004060002c600000d5040c40d55030040780c090000c580c070760212005 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 530791645 1250 530790395 530790427
    0x20c0115180606030605090f060d060c0305160f09090b1309060f14010605030a0f1805060a1d030f39100b0f041d0f0304140301090305160305 62
    0xd44a0446038030341c00305494040c0100c1e000351000745402c0c0320a5140c40c0100303030350003406080022211300100c0001c00a803180d00980c451603420150034088540300b100007030020002941c560301d0302850107004018450040c051549041c1c003503604c4010141c07030600c0b044020305444141d90380c400344c00c400f21a45482d2070300031184503034010382d0000345c09284804030004a816410700758114640c92001000066084029a688100c0c0c03100d010400d6035208184500a0102c0c5006038500400e200854050020000b2414410202d2310380030084100a20803a00d40000da82c000c40049500c2006481d018055050182402c40000070407011007aa20710113a0400d5503034581400000307101d108000344000010410306100c0c4084050807c10307007440001058652901c1c214040c0250303290001e010020360b41000038807000003150143ca513003909040c200c42c0c490703002e845050452146640090a0382c0f03818815042e01c980e00d9240c2d2441c4c1000c00b045411091000741081d024004203211002134041009 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 530792895 1250 530791645 530791649
    0x30b011d1906021b0d050d0e0604030b010605030a050a0510060c051c0c051501030b0106260108030714150106080a020c01020412150510120809150301080d020a05030409020c0115 78
    0x34002d05090650803c01300c140200108020f440784a8503054030f03000c03560100d50b101201d0f0f00380c40c0290102d8118004102a48140c1d4401880d0190080000800c0b41e80003000e14003a080b004000c0c0034544494110400781c450036114155840140c1c4002c101c0d460080d42c2c811b154900ca0419124103400016403003142001440130b00340810030301f401041c1004820700c0603a00540303400481821030b5055071a5009540b205024000900580030720318040202814000700c08940c9100c0b4104142d0303164503016807250081d0f601100d0712403c0640c034420001d8003040b01e4032620143e4891604581c6425411250001301411424901da405c0100402001d020300091001c0c141d104011040c141e05481c5c07000d5071042000c01c620340145440180000201d501d40c10808444a4501c1ca49401c005800e1500f038030b12502c0d01e003560081d100140400401e02050140d8101d410080079620029002c040a1b03885111a480081980e08104001d22401d11030354090314505012400001781290319401000702c9052903 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 530794145 1250 530792895 530792897
    0x180f0e06061c0c06050c0c030601060e041401030206090409080d0e061806060102070501030b01030e010f0e010605120a03120e060702010f0b19030809010215150a06030b011d1906 78
    0x4004208440c24100c12640d0481140100b40950b05195110b03545910528007662007006070002d11074054200800c021240c0403c01400d50f808d95a444030083c10254190b18480d0040d4100324614103610b000f040214100c0c0c0c2c003d05030340d161072420010000200905103045032488003e0009403010b2401344144420303a0002c0d0000d210604140c040328085204007140c0c0440c5500c4101004038999012515408681c004c3c00d020800e00b00210059008c2c0507140d410f001d99621381114150840d140c0c0e008030080e160218000c1140c0c2c1d842e002401503034034900200b141d95502040308980041e10500c4240d010310b24030300700011400d500c81d015030300b0501c0039244800142e446281070303100c81500740300b4800f4001084a030240041d4540340b01c080445100e2101610000c00840c5a0344240d00034001d03202c1e21000101c0c000d40c54070700820100501d041704400c00f4010f0004803030101da000d009104204000005854050301141d80c01c41914100380303c06c420982110210940c11400c10110720001d000d4081 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 530795395 1250 530794145 530794153
    0x1201080102032203170c040b16021e10141e19030b2d0303040b07060c0509130902040b15040801050906161107050d060e06130b01180f0e 60
    0x202c0c1d202c82100703c1d0035440000040c0d030045154400280c02c444240c04c0c005020301c010302940e913a2140854a401150300403041c400000580c801308001304d0b801c1c511124821a030403104043d40021410301a4445100c0f1604410f012200d044458001d400c40e0110420304040d8034900700c5c00b08211a04021801075040b591080072a4544c40c1c50b003030b074160700f400315078900c0c0411040712040d0006020081141d4126045000d25070380907026012004401e150b0740020702201e5485035680d800c0d11007540203000075500149085040711a00d489041299400304000b070016101d18941c01001000309442d0710200e81c8140c3d5180c1c40f050303980f40d911055020481d034040f03c6465500d4000d0042c29070307900070304101e4160040003c000340104014030b008034401d11494070741c40c2a850060114500707110350700082e88c0102400c260400b00b0400d604a40d200d09134200541d00f25071a60380700a0003550700100700400b40e103803800045c080c141100d410407000c1c02001d0004100045134541e550b0403250744076014422900 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 530796645 1250 530795395 530795401
    0x50102190507030818030d090302030c0d0c2f10020c0901030b0a2d0b120601031527030f1701030507050901050d0b060d150c020d020d1d15120108010203 67
    0x180112130594001500703050f440b40d440485070595141d11440c41518902541d52031014203040c42081550000100c0c10215000040c00315406000b0b5080d0342c0302102d0311009444440e504000a03a4402182010040160030501b005802c00c1400080c0001040843c4116003041c2403e07071301c5003043c0e40214000e07015445c96043c21481007064900c070a03000e1100d0384030807201170012020f070308414038440c52851001411410120001d52030300c2240e01058941d104590000c0103122181064040380304402800700102a0381c11a00a0480d642910501522400f031340c4140110340514600c40c044200c92800c0b0115008090814048400030b0b0010384203035000c41070a0050b42012441c1a0140004880310b5204a1455a070801c17441002002140500c81c032216520400c0640500e044441c480101c0a00a101070540029500e035030602c0c903840103120304406081c0040c0994444803501c0141020f5030700f0391030050300b400403100c0c00c1000400d1003002000309800780e141150002d03001e401e800c000076a6900b = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 530797895 1250 530796645 530796647
    0x6071d060a121b0f02031c05100b07120e010e1f020705030102040b091516080702030c06121006090f09021b0708241012060b101107080601080c090405010219050703 72
    0x74504d603a0b60030b5500802050904110400b402614813802c02c40106950b80c5649400095680c10351000d1a5800040790314403c20240d04007110380d80180d03684900e40c911851004448003041c0e00b0003e9002000c0700140c2d400d41c080300f0003040d205040c900444080d6a65600403908a0340305a2000b408038401013902d50503480c102e01c5842c0b42c4100d5a401c5810580031081c82070714413803500401814540001091002c64034244079a0340e403510000c00d0280c913645420307802e100e014021901c00040034458500464132500403800700f401c0e80c2201d02000803041c10001d29800a40c84510701c0340c01d42901c12001140828104403000c050f010311005403004d00d618040071400c40d0894142c0c5580002d100040040090042d02178038201c40d50f2142d101c91a06003420102d00500e00641d0305908189407100c0c1000c495001900c601c100c1c1031400c12507851681d00c15000c1e440301002e0041140c243c11130140000f00d490b18445894129002e50001441e11301001c2d039010040308500d0982d408900b01003803880c245 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 530799145 1250 530797895 530797907
    0x91c09050a09020a02072105060a060519061b0f0b04080703020601080a080d050a021c0c02070806092e060602160501050a09051c0503040b040806071d060a121b 70
    0x200100030b425420320401080c0a500c03140c490095081911030420002c9480001c1c031010402140c114096414504190341c880001c2e151500846001e0703820524641139420030320042c0b400329500b680c0d0304010502901c0c25000d80750940c0b01e00b61521640141d50b0408602280407044c0554414440030340c3c0c800c428035020382407030760590000206802131403200001c6510902110340345414104001001e540d01c604050090141c400d048000402408110000302c00310343c440c446110080d001c03210000d0780c030089291b5a0208441100d1315410842c0c20781045900c08180500f807400041c03410384010b0250000e030301213030718640c0710360010381c440c0b412090500084e03913091001d0003003840e081c2e103001d45055000c2c3c0440780b144183c90041241030003c070780741c06094662414043c3e00c1015255641e546441c1d03e00683c105000310490760194002050816011b40c403040d0120303400c030210901410354941008199000102e40c00700740401d21210b403942800701d204e40700800041c45400c100d1511140c000400c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 530800395 1250 530799145 530799149
    0xa090e060603010b2407170d0b01120b1c110916140712080c090301061205060601030204051c060212011502071e1205010207050106030c1d041505091c09050a 69
    0x21324010080743c690441a80c0103050b40301ca0780350000d9903140245005840c0c07e6406010414881010610751002c1c4903c0d0811032602100340e881c441c034182800c280030200d5005401d104c0e4001e2010201c0010000162840800d145c0140001c070801e00d280e2010070740380d030801c030786445200311406c400c84800e507001440b0384840e4550b00300c1603050908540d121491700340d0648441003800340d0280000d900610001c1141c04021003c1d009205076907550b0707281c44109001400460340c5000f40b0340001c40b50351107071081ea411594014402480314804400516100c10320400035541303030b07808106107454803400071300503030082c0410340c0704017821028014024109005c0390000701d00d03421424165034201c00390000074001e858011a020344003c0092510368028410501c00410550902c44008103200341c1007100400c07a40c111a03105103c0342100e00b140306030b5000300c81c010022081010850b030170309055400641d01191079802c4801444001d03900d0300c40004c0d042e0700c0c4000141442818000c0f81801451040 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 530801645 1250 530800395 530800399
    0xf090c0207030b0609060a0810090c09151e0e0c03010305100b06030627010f08070b120a09060902130f0b040608071521150e040302060103110a090e060603010b 70
    0x260700303030039556030711070840c005004c1d40e103d2032840000c14256521101680001d007407a8003203030b4280705a482208090003010364180e8100481c5100020040d02c0360052940d0701d0325000f980e0b41918103100380b41b003e084c0715001404039400c4440c0080740c2202100000e0340100002025941c90b0340c9140b4216140c1a4482c2c400e50322903040524844d03094031044180c83e005181200c4c0c2a0003e00a0503018000600501039031103500c0c071580002819a1380c01100c00e0503200e8807000c2e43d05843c0c45040d110b0003489141c2c1c140b44000c81100006102d040e0950000215501ca030301c012501c1038107a000281001c140082d10083c080e60381c00c4a440c041c501e8407aa15004005840c280000c0e0300c3d28a0581c0c4401607071150320311864010540c602910302c41d80e650b011404e9209030f00d524241e10100c02e14010006402c0c2c1e41c1940c110400045401e81e00707018194030072507065004203810313802e541c0c800340d081916103005038200d400c0c08008144114a800358000740c481c03000090103103140420400d400c1d00d91850382c00f4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 530802895 1250 530801645 530801653
    0x2040807050915210a081b0106170d1d030d09091d0c0402030c071a0403022b0f1e0201050f010e01060f030525020c091825050303040f090c02 62
    0xb50716482d901c0c1a48407100c131400d15200c00c1a80010b070a090b05500020710b0008001021000d01000109840d0742000b84802040000d8031060107255a40c034501c41210203a21000c07000c0410340c4102c01d00e05451909821100c1d4225030000032914007540843c4610214032000c3d018000d04d0725a1107050303203068a0800c50314a600090748080d444054500c2e00c9805190000001484414040115600381d03038841c822650541100b80c103810768200640b4214014043e0402e40d824401c1c41590b007444114440500d03402a03c00010b090700e801400510820500145c2c1f200c0c8040c441008003c04030f035030400c0e0000301d154a05043e8261040005800c481c1a95180302d0040c002194045030b504c0144038039040c0000c1a480313000040040030910060429600305903010300311020360106986899210545080481ea1200c1d003a000010000b0040c0f42d00590003203180e0601c0e52949240c42d0014001d81031104605a200c1c00420708641c46a0081c14601803007000c00c00178008103115603c207014040c4050 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 530804145 1250 530802895 530802931
    0xa0903031b1b0c05060f0720130506030f030301090c0801090c0f0c140a0f0201080609061c080c03040924150507050c090a1a0117011710020408070509 66
    0x507022800c444034000d00302040c00605803c01141c80b8000303025182c0207001c6526000c000d1200c1030240d1002504a80b20300b00420700c4403610410100e500400c1d480205042940c0550f244040c00400c002031106600d881810807400c079580e014001507010300100c410119078424186005001d071101a4030002c1000d01e44104081001d5002c500d42407444068a4003085000c8907052014450344454000c00260140301e61200411400d2182c4645180c400e07202e50003140d0f603a00c200300d543c1c802103c2c401e8001c0c401c4141d00401181e120b2105581920a0b03040c1410701031028840c40c034607007003074000d45000b950f00c0804500368400307079202c1a002e19030520501d5559090002c00300560440342058001d12202003408030402006010f180b020b5400034011440e103281c07404201c07020302002103e12140d1001800420160751003003039050002c030350410a00407640d1800c03a8840d154030014820311010b024a540d030884040316400248002d0442d14010020740b400c1104110654901030700c2c4210940c1c0d89481d07 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 530805395 1250 530804145 530804147
    0x9070515070605060a081b0a0b030f0412030f02070f0b0603030a090b0306040f0903031e06030b0118020c12040e0c030601020604140304120803100b040501020a060209180a0903031b 79
    0x40720111580400301003819160180480c40c0c84419801050650282c210a050f4000d51102100841e90040b2000544169190300301e0349188400c2c1c031001d0844940d400054042414a52020b004044c0361038005800000d02c05810102d8201300800c9540003582e0324050709000d000c00407203400000890182d85018000c000180c400310840c80342040380b6001100186043d07403642d210901d003480040741840103506500e070080c0200110080c09050700501c0d81c00c88903a11031407284d0003d90b503001c0b2400910341d0a000d401c0003103241c12550012001e808204081d5400000d0100e0309242008101041e251810011603003041c550042c03143d001c008050040010301e03a030004045402c40c0e00190209a0412181c4a8a0640c801c0f030f0041002442c04007030820070001c044005601ca00c403980109101c45071950f501134900d100d94414140142e2041c0d18200124906500034917004000401401005540c4a1494600300045a20108d01507442000c0c00c1031581501450f00e0080c590002c6a0b0075100ca484 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 530806645 1250 530805395 530805397
    0x8031201030f0515010602030306041b17060d21140304120c02011806022811010503130b04140c010e03070b0a05040f0b04031b120b040204140a0509070515 68
    0x11010b0145140d110b01c2074140501800703001c0c00624050360b102c02e1036840c1c8001035500e90059070928010b40c13401013503000d49401c0390302e03214046600784c1c0d41c00f040043c44243e0820300003000e40600e910101d401000800250582042e0300080440840070200d008003c6000d807050700e00b02548042020f04100b004001006014103400080075402d005881c24440c0c00121004a4a600b80c42000814001c010030850703000034040c1c0c140100c90308a048140e24506800b600190384802c010140c02c400c51841c0020f60150014640c04410400035031192080798540700c52480e800e072010350700c134220901c0070fa1840da42408240e00c103075030030300f000b0720208207240c0841d6031101a440b521020034800f040500302e15114008803001060842200c01410b41c407005607a0080e4420320040391741d1401c40400005540742c062048c030848500510900c4240242d884110300b000000b0401c0b40e01a94680246603e881d1003449030b030081d00c40800014003031804810b010729000d0703203400c264890740032520a6612145040 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 530807895 1250 530806645 530806649
    0x3030306040e01091a010f090e10270320011a0906040e0105090705030609060f04030e0414270c090402040e010e07090c0306050d050c041a18090708031201 68
    0x1841c0010700c5103101c107009004020380680106480c1c03050142c900e02c1c4c004c00003254142c40e07106032280b00c601d40d01c07a030020807100321690f12081754000b81131580f0003102681c080047c11500011040c00b03c03402007101c58880c2d20105040b00861814541d101601a0f07051001035030710900402002000b0381100b600300e850710180340480c4148961030000c0d0880e15283c02034404507604400902c118207040c40c119407604800e015450003449001e0020342250b0002a8690155010508840582d2601d403011901142c404078096003140c2c0b00c0003050b41c5183d80350446845210900c8981c00303404051500002030046402c00021039512049a0303807690f03610070220301c0e00243e040342d0020304084800b0880b03000d0401e150795013003075004503180001c01e00255000308402004a5504000ca6500c0e0004c1004e400180c0305c1c084c0c640d5020002c2c1481504190b4401c0d107090003101503503800c43c44020b0010301103880c414499448a0303407030f00c180202110100003000c050041c3c0306c0903602304005050000c007106814 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 530809145 1250 530807895 530807899
    0xe060a03081c0608030f0403021801061422060503070908010c0f0c06060e1f0501020109030903060203041703070c03021207021c031724030a030f050a12020c1f0b03030306 75
    0x4540c02c100c08002c15880003000381062410b03031762a0501051001899005480160301a02404240e55840081c0201c0141070f82e809072103010f07090758558003000c0f154202e0720f02d10100c0071841c180200c092003000300050003408a990744503500d250034140201514203070303441001c15a0600326036840641e0811100c9012141603c2d00f1a485405418410f0152459512130b1420b144aa03050001281440e8110807844540d401d00301045a80c6000480c00c03500c42d0704010300001c000900502c00101a60000c54026008074162450509281c040341000c1e801030751141c02003035580321603904040c1c0504c40c1800b030700446800f0a04010180d00880e082e045030481c040c0d10380100c0309007081014001c0c00c468064404083e030702c2c01c0b145408080d44680c0d58051980440361810001040300c1890001220110158160781e49652122140f1050b9000e400c841502c0d8248030911510301c1062080d4405000015940710060a140d1024141801c1030751401c0d900b2500e090a042000c0c2c103546000044036044081 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 530810395 1250 530809145 530809177
    0xa080c060a090909030207050a0803120402010c050f12040911040f091d0706030501090b1c20030f1b0307120206070206070206120601030b030115050906210102040e060a0308 76
    0x401d408960040058006040c0b151038148603500349540003807203006580c81a1065000300d51160b025036903a01038511142c0c652100440007400551191b6400c41d6032502c2002200d10ba11101070105040c130480e89000401024089030400c404402405035000101303e00c2006480c03d070900c140900d410006015525000382c0301c210140708444c0c1c45400e80c600c03000d40030a4845c0c3c180c8504005026050a108035191282403a40904162400312520201c003003a0b10048040741d0003642d9a034050568002c10130b401842031000f185200c1c0c6091203404e403281c1c0e40b08040c2c104012050362032020421500031050107a440148188600400340340050300c3c041c1c0482d052a140c50040c070000e4442d201d0001c00079040180880c001e9825000840c41c580120000d0b00c0074464081400203160032a8001c16801400c072032152010405400c00c200280d8005502a0088640c0500580c0741d1481d05120a1034100ba613500007410403007609000c18564200008441d0b09552a207145c4499045001e0182c0040d14407034 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 530811645 1250 530810395 530810407
    0x702010b0a081902190b0306100318020f040b03010f020705070602070b040e0c04050d051c0311120a2007030801050114041e08070f0503070b070c03080d020f16020f0a080c06 76
    0x14503403005a00e254171030140320428649902e600d42c40c0b40c00603a000f0340505a0890840700c105d000b8018916450300c000c421500401c11502081003440d44158120707041540c503800e64000381c5080c000c00c2002c1c402002c0250341d072a443d00c0c299203040200e034031402c00c40d00018400d10030039007420100c1f82220503039084029541c603080d0031200310744101d501c92984210b005c2c610358104900400e650080b031141c41d800c80185480c48000741d00b90b81c07000c0020b0801a5080040c3e048181c020718400c3d4008040380000150031030b02004110320b8031410241481500300c0400c5d01400c056210044a025003c00c2c64201014855901a0645400b8600900c01c048036130301e41c2002620703506400d140050001c0b6049071811a03550181c1d01490545020f80f5019010322003000c1038040d00c500495002a60204034101d074607107142c03502c070901d801c96100c81d000780740c081042501448079607015001015680b0100c80c0c03a24803920400000300244a03006000c0c00b8800010040e82d01e0129030113500d07031000d60340c543c2d82d45 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 530812895 1250 530811645 530811649
    0xa02151b1c061211010f0e030c060f0d050c190504121415072a0507050d02150403060c030b010333030c0b030a150311060a03020f0309060702010b0a081902 68
    0xb0180b03400c0244070710030007843d120500c41554a2988a4a400e8981704041407980c00201c1d11170041b000800d070140c0c451100c11004d03003081001001e100301c1803a80070781018483c0301c1c801c05a800a499088142d0b0010031b0510310643c140015902c609441d04010307281c0351804165034002d210204014000070321101032590890028042810341e1016071010803058948108003411480703a43c00a001c500f40c60340203850302121700c00340313009141c0d4001000b000d01616010402005450404040b600701a4100d070660407022840c01034800341d072041c0d102113240c18501800400321901e2050700b50400d070600445580035901d0012100400011900c24407010030060303044528000c40703034001440400104800165840c4400c045c50082040000900680b00340c40e0584074684120302010b8100400d10b1802c281610f000b00c01043d000a040c203015007880b105240021580d0012900048150001410005001c0d420321581c143e50ba03044071003001e140d082109240da261990702c002519407038104400c1e0259 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 530814145 1250 530812895 530812901
    0x40b06060d1107030c060e010e0c2103070609050615011d01140c0a05061f0605030a0621032703061e0c0c030206060103050c160c0b0a02151b1c 63
    0x1440c1d40882e0199280032a24004060f01503d044c15181949000030b0361134100c0042c000d045560b4003080c000c0001141c2c0308101b001c8801d280c040511100803400344600c41c10b400b0300181c405140125800100c040941c14128182000103080a00c100074900200806da03800400d00e004401e8040800c030807800b00d403401610313a41000c3c050016610b00100d00c68054040005840c0b080d14825001e6601d03d84400c44c1c1410381480703840300f42440344031102007400301034422805035a203c400b04401007445541c2e415250307041c2c1c007500c0a00000c80c8080004400307164000e4016089200461100c3c2d50701c0140e9580e60b5051503180c00000c004079103504103104081040e40d240c109070101c60804001448913480090b00300310070320302c0c00c40c00b502031000081c51a6010b0b1283c1440f985020301132600e064080d1600100c1e401c800007007155800200c00003c55600100805072011800e11f4004104640c003071342c3c0c94103030307408000e003022000481724800c00d030070b81094826214a04900c03a0f50300d0701080036649070406 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 530815395 1250 530814145 530814161
    0x50d0f06050a121103060115260423060420060d050a09170c0607030e030712030509011a0a0b0901120e0c130e120903010207080c0f0d08040b06060d 65
    0x4800700d081000f02d4803071001c2d0000810903100e2507400c1a0032444000f0325440703130000d02c2100d2131020148080480717603000c0d201c00541d008112011b0307110609000c40950281d01c00b641d00b918828007811008140d00c005075043d04441c1c4241d0000c145c3d0780341c0360303030f40c5c0101c103c0c8071840300d0a16010000200054a422040d00c03540d0003410818020b601e000c2d0000c400602c0d43c8001911541c0703858512800a10101048614004c2d80501500255a03084000e9001d000b01071001400303444100004400f007044a04c500c4001c072034a03a00410a42401640242582d15841c50b40d030b204922407100c090f050365100208030845618810103501e8015080050325407903083c003800d00401d801c08201e089564408102e6680012084505111180740e0000b20803ca60150100602d84da1141c03140d48104910140035022403200100050f140140302e5940d00341e660008620214264402e050390404d04030117104488040400d80f611004174074240d21219419403001d42101d008800000d800b15420f5615005400 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 530816645 1250 530815395 530815399
    0x31107051c0b070f050f0a110a030207050a14210c03070b1e0c100b040f0e011b2307111807031a13150302090c0c010606020d050d0f0605 60
    0x403003aa010155680031408440842e4000340c0c40001800040c0503c6407400c0c520704030b55070342e420b0840700d000c0d44c08140e000c0b280440503c080424003540701d403010008030508030300c07036405005400e20386420b120000140342c0020a64002c54403c09100da03c070003840c508607002e180c0f038002900c10790459050800300300d008200d400d401524000304d00301c10b40d50b005144804008000e004100f1444090000500031540c10f94030710b03000100c03601c0c0e08040300e401600700c110703004000048441303400c941c440c01c0781c480a03030007106a51229581c501d13000c4000c40a070403080f00f60803c20000303484603821800c0503540c04205071162102043d144140300c44200910070454020b41081e08072034000c864602813070b01c1202c7d05000a810301034500c04000e050817140e01c01103005010750703c03240350085454025246421020519889044000001d0381e2100305460003a60704080300d80e95001314011031400d603a51900321400b50761008804401041d0b000741182c608080e407500005900b020740e01404080e02c069400350b9 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 530817895 1250 530816645 530816659
    0xa020d080a0b060412171303060b31060e060109050d140109060b10020c01020601060e041b0f02061003170708190e040f090c09021b0f01020a1b050a03110705 69
    0x82056420310172601c135654043c4d00100c001c5981c0d00035580c02441100404503c030a07070400700b0000a4000d40051060100091150340c0b82c01300c550100e03909481401d103061403005c0c90410f03800e041e00903109140c080d00d50402a50a07a140410028080400c24485c0b00d014030241d882c1141031004945d141c400c200d41d130130020b0140002038109500500050341466100305001035100c00303182d00000d1100610032068000d0724442c0e2a03d84284c0e070108103000b60641240e04e81206c1c0c240d0000c103040d2007102d60a184c84e10140b4002c82080286031810042610000411290301440400c0b0003101721100713071904a4029a032140306141c00302442c01010189548c02803003800e17110310160014188600000103540030019103100d0042c00c41625010040501903c0c2d03411030502182d10745800a003004a840c4d0440d81814181c0034035640b44c1414200010300d20303580491607440a541c0081c11000040c1c2c08115104060034585036141c50307080130322008050042c03840304460082c6050025600801c4020070b09 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 530819145 1250 530817895 530817899
    0x8160f050a110a0e0402030706110f1603120804080f03070c0f05060118290102010603150504060f0603020105120601030f0921050c030301030f06090c12060506060a020d080a0b0604 79
    0x100714406500480030b1050310f0124002c2010703000f003d202481260020300500900b4540507080e03551004c3c180d0464070902400001b205044003c1142d68812941c140001d00d0b450b03c0d50501c1c1540642c0305641d481001204000e00002c10260025680340442c412002540c2c0c1c1c59042d0b00340c0e1419010000104440402c0b103002c0c00344070006c2100ca04a641c2c1c9108510310303488000011f400c50b888a0b4401249180302c010210804000030030030607260b03106000016801c7e45035183c80d0300310740c00e00d00744038072168842d41080200004c07401143d5814081c110140305090a50740041c0c2103005013100c2070218081080001c4150707100c1c0e04010504441c08608220300041410450310508500108145400035460780e62a214401c1d0308590503484054003542c110b9086a0703c5000800105200b81c40c40354481780d201007c1180b01a6010062a1220224a05203214a401001e07217000a000b1031190605010444005401213600700c40e0140c18035007003440755145019440223126003403c240e0003040220380 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 530820395 1250 530819145 530819153
    0x10e0d060507030f0b0303071b090e07150c08030f0a110f0c1b01020c0d080408060a021c0902092701052e1202010503090c030607052508160f050a 64
    0x8054000c0e070b12a81c09002001081d1440425149080881a055401000040045401100081a42528500644143d80d91800d0707a200b541c0180c030b0301045940110404010f000450310300e418055400341040b80c154025519002c8032800010600900460480b002681c7c01030240c0c007150704805040340942d120f880202200e00b55400410030b01402e44540c2040040c01641082690031491381640100a00700605040c4117070030500810071981100140400301e803a110034032840d071242c0b14190700182c0707807020301c24031042d00c0c030300301001540003494aa850780160b01c407040030303551007056034030b11658011540c04416401860320844100e594606014003841120802b81c00440c1c1104000c002c0d1040789185120301c09010078410341c002c250781d01c2e00b114015405180a554807482040640d00309801070008242800c508607200c000050380010024510a041010010802e051407140c00c10f0000540d5800501d02c84c1401d00c0708003070314080008041040290b10248103030f605c03400352107030307a4100d02d0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 530821645 1250 530820395 530820401
    0x1d150f0702030a08210f0c0a0203072a0b0a170612060a09060501051504060c03050409051e01060f0806040b03010209060a0e031b09040f140d0c050c09011a09010e0d06 73
    0x4400e1740008214500e56070324082104803900502c3c000c034250860780c441036203882082e808104c1550650000303020307110100c0c03070805111821032000305456100c0c24035a480450305160940090f82002e00621081041e1940148024202c14400740c0000303180c2c031404001118440c500c0640c0009200e481c04103d070500f86030b0403044015210b1a82805103988032010440c1c0444000c525860964080c0010400207200f6505107246038000d040803231505464104190990701c0440d0910415800d440c80094151108907075280102240d01d032091811400d140010241c02001e40340f184036a4540c902e81ea840c2c0d030203504441280400030103480d80c1d04070030b22000c1c00c12214182a541300e401703100ac0c00350700e060301d114590f0031424004040c503030a544e0741d5994410102011030181c610180800555925440402131440f1115142c0c50350031000c405882c04030702d050001c1c40712602070042030004100d07454404071404003000054041c251200088801202c801c20b0180e403444c0d2200c0e62624000500c21b1680c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 530822895 1250 530821645 530821657
    0x110c0607110405010f1208130e01030305032433040e070f0801031104090f02040609151a091003020d0f06080609060c040918050a050606011d150f0702030a08 69
    0x2031002d00181e03aa0310f80e2a81405410711403450402d420518000004c7c034158010421900c8001d0b046025a45444062001d04400d8104901095000041c4080b01d44007840c07001500583e00b682c944880d250101140300d01c1d41c102c1e0b03800c100003086a80d801421850585400001046880742c644070740ea11040895142810f8030308401241070403040000d1184500071050582c0e411801c211201040d0ba41440020301c0140e006075500d000c07500c0400c00503a618000e0328000d00403080c0100e054944100034100c150510343c803c88150190001405445640308151080340604580f582580c0030018800d40107845124141c110140c40e20380e000f9126080c2da802001681c0d50181240c2c800c0c0e0722040041da4410302543c444912200a2000304031b03580081d0006007071605001c2d4519400000b1ba40c52516012108400b00d440d500700c03004010b5103581c00001200010518007450454a500c81c01051039100f070302401c0440d06a0000f090700c24806031108440c9600e6003e8202d0f03081c81183e05101441d07030880 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 530824145 1250 530822895 530822899
    0xe04090c0e0903130b030424020318061902070503041205150901021c020c01020c1209120a08030408090103180606080705011115130b0a0b01022407110c060711 70
    0xe507000c140110400402d480841145000d11520319041414041c1d070340d0001041161b44c03009090b03041103e82c0a010010040405103c40540c40b8100744441b8441da03c02119041150f510080801c0860341118201590300f03001e020300140c0e00d00381e0f824498111b12803500b02c1109000101850030400000103040614608074580841098070380401c028242d00c101460183d40002813425001303900c019600805080d0f15044c00180f070100d990b02034a060124240b0f1007085010701140b0221075091130510161803500340c602500349200c00396078000c0c042c000988040c10b9114045803081c00c0ba4046d910059104200b040c00380c0c600302030784c40c0c4140a84180c0c00343d42582e010301900040c00f5406103142c1d002040822020b040a03c02400c00b03540d031888010001841507000b24080c5001ca4001481d50b4080c0c10079920100d00c10350100006072800e0144070641604c13000301400280510714140c106904280b041c83c0156406581100c424a443c40040c001680f01000003044020003802e01601d240100007 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 530825395 1250 530824145 530824169
    0x150905060a021c0503240424050a050103020c06040803091536030409050a06050d080d05010509240427050c0a0321020a0c1203030b1f0509010e04090c 66
    0x1009030111602e000c2500c20400300c891b591040075014440d400402605031780504005025001d82d43c800d00205030107283c0710420074402100b404036084c120150303405002d003800c3c25403400704030b5507440e90740315001000500340e00d9004c0007144501405202400b01140280c4440703449d800c0c032000d824034404003084a400000d41c1c55150b40301d4018040000802e860701031010718145490301c468080500001031004031301c0c43e03841201280680e90460040701c0c02d400f4590854a0b801905503540032100c040e00554401d82d21141040384403010081b1105981d041d104c056072204469401140c081d10600682d02001c40410301600d00c858649541c0500300780c0140100c0d0900108501400305407151030201500405100707928000d0304841c07503101381501c82c071403049a600600640382c0d5042915a48c105540c4034103002c840005066040c000c0310030120088509091301000c0e00000030002004113600303010b00c41c000c103038901c5a0b8007408070325044542c0134000388200c00092070320b010101c023180503a48010340 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 530826645 1250 530825395 530825443
    0x809190e100302030d0e0301060807060203070b070201050c0913020d0906020c2b081008030703020312010504020a020d1107121115071e020f03010f0608010507110304150905060a02 79
    0xc1405200702142d401501030311098070010300031500902e542c50b0707480d01036480e4480000d08541c10042d0000030020380d80903540301c2c4140e180602c440d030800390010303085a0500301840102c088081c1141c03000c110484103000240d00e030010500180c00380ca54082003651520445005110490700100035031041c803420b544e8171001f151034009101800d03c0c1440e002b00c43c000320404040d030007a2219500b11840761100c00c10035640305941e610b1940900012001600085003000b201c208074120240509000c54003582081e02c54000250383d101004054010000d4410306c2c0c89070141c060000c08081c1c02c3c0c4110340110b00c49141400e0354540c1c0e0071044140244a18a42e03200d40e6a10f0a0640300c0e00e540c0000c40c018404500310072859555403000050f42d000c20ba00d0080c800b281d800f4801c1800c103400c186d1010400754a0905030508640c1c00500030300a00000d040d440000c00c04c007000711000d582e04240044003011881d5400c40d2409226080641c00a000040c0001070b1500054190b0b10300658030600c2c890300d2 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 530827895 1250 530826645 530826661
    0x60a0e0f07120b101710200d05071112071505040f060504081207022d031e07050102040f140f1309050c0303030a0b0a05060c0d0c0809190e 61
    0x158162045445003a030b2002d00364006106921116044030752642020511500c0e103030001c030052003101d8080e016510030103440301002180e0151441048030403403400030b1400d4044084c05584034828820f18000e50780c1000070300890084144a0402171071004a504101c200481c0c0c00307850f401a0000e4866820920540000320818050701c2e00c03031588030342102d4500d480c540c1c81c1c0d0080e002c041c100726046003003481044111404003080d81d214518560040801c1500001c52101c09116041d8140c2080005020910003090000441e070300d080d8034284850000342c0b001101c0c2c819015428005105500014000407545200310340300d000e4960f965003400c0c4a000c0300c01000080c00c0c1d40d024450b00203400d25040f04000105038022100c0f68000d0003a10410f00410000a00b5644111039045803030742d950000550504021006001600041d900e02d4603114820000980e07813540300325548104180c4440d0340040244004c245c40ea0460060007000f001809003140c02c1011030326000b048000918000003070302c00 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 530829145 1250 530827895 530827903
    0x614090333180304120c090513060c09081f0905030f0a091707030b070203120a0509150405030403110a03060501151103270a180b040c1706010e010c05060a0e0f 70
    0x40c2c014500440c9064607001c5461014080404181c46003000d11000140c4101507000b82071040c6174009885003070002178900b01e8221000b44085908014088005000d0001c0c00144c01e41e14119508140040c00c0303110040101400280c5001405800042a4000c02020b10400380003010349546030440e110340c4a5401407001c69000c2a41116070b400b1340c000f040031030303500c45411f0341200c400c0c419280b6042280c06004604601503800b00020390b07680701000600d00062002561101c02030210f200142815111a0356a00a50001505410594100c54a00e07503803c080c3c5002141c0c422424000d0750b03943d07107a44c014181403a801901003503400d0038504c04080040100d401c50300c1101004004552020070386010100401e4400d50080c4842501007004c107000d01750303114040941c44000c6070b00c0940100f0302c829964200c10400611400c00c25071603d0206030aa10b950040003807034460100241c020040700d0181015001401e030f409280c0c18002421030b582c010303040144070941181e00e1160f40d410b1141d0380b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 530830395 1250 530829145 530829181
    0x10050105120d0f0306170d03060902040608010311011b050127031e09122f150d1d060907061d010302130f080a0c09060614090333 57
    0x5207801c45114400d0759400f0301c0440c0f00101d100e10b00001c0d8036895281940403042d207954a0100399020034001140b1541c1806110090008030703c095090615281e4050441c59040c040184104038090039641288d00ca21281481e0208604030158207051070b0510600070700103e40031494a04410161030300c0c120f4a00b0211081d07603450350b10032903d40322105d0740d503032a2aa000140000c000381442c0c0020002d007503070003040da1540a420381c0010100e80c49194503140c0c4134510342e440a000203c107155401e40d501014000c81c2090a05400d5131410303020b5458001300761054101c040e82c580c0c01e091160b9000d0008605207e1550807003101d01084c0c035610142d4100015001d030f15565881240350584070b521a402030f080681d05425045d003807540f5030241103082b0101d82c101c581a9030081424201384104a003800e00280900e0000300b01e501d0034048000c000810440900d068440001103822040e141003000038042d01d038550713000c80015081540320410b070411461076060101d80e00d01041203504812180740c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 530831645 1250 530830395 530830429
    0x304030828170621010e0f010605150d090602040b070203060a05150d0c082413020109050f0607020a06080a0b03031206010f090b0d020a120b03060f090f01020c10050105 74
    0x384240b5088001c040d6440c001c0103aa0042c02c04c02180c11049105035040b1000004240081510140f04c10510b19040c50031861820300e0381050010406901c8451020001140c0c84a1207951148003641c5000070b06880c04004100901c00034002070400381c4071015000403882202a2100c90301e50207c102e0070380e001a1f50401081003030310f02e120380500c0c01c8040d403000c02e4403078148140c103145c4d6041d1190038402c01c40d040100c001e18030300d02480042005a510340d40000d0601c800c403c498082d0300001d00e8541c45014950044501d0041800c0310f944081c19240116030040c03180104546070b04009100384070a0360114102400c10704800301e10304d400720540d0322000c8100c12402c02d070ba482000440d03010300070141080501c442b400c8049501140743c0002d013141040f16130056079036914440c000b040300210307400404235a40742617080300e0165004070740590005042008024140c4030f0186442c10010500d2650704150310000310300580c0c0501040c1d1130b14040c50b04d0420440ea0f0b80c0c4205000c58800c10800c004 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 530832895 1250 530831645 530831657
    0x70c061d061b030c10240e0709090c0c0b010b040308030417070803040c050f040e060730050109050604110d05040c230907050f04030f05010b030304030828 68
    0x35424203141d0003805021402a108100c0c00d408199068159800341d94011540c2d005a1441c0000c0c41860080586042120142210103082c5282951915141e40100d4500c8402040030031411132003850300304090300b441003003081032182511010300310a20005088540460760070001803058480d0095900320790304442c0381440c551b19661000040140380d9040c0b00d450100b801880702080601c00a5803049100d42c0560a04a0800d410400010714a403086c0d88070f142003040800b410a40810718030340040f050b0030800d075a444030901541c9000719012070303220580c422524090641400d500054102c40032020100202c2e115401800251090703203134020800b8004000b149100011588130300e078000e003d40d000c1e03810303141c45c1c1c4131418901040c1c0d84005405455811039030805c0c0b5003058000d42051060421502c1c0140e031750030000044c00b030743c8409004c131403000c1d44807070900c202034000000c2c8240040c141e0f0b88c0c0701c1d16840d00c04810b81201c111003c1440f2103013030103c2c610140c0030706060420920b03100c01d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 530834145 1250 530832895 530832947
    0x313030e040522080f1201090b040b060912120d060501121b050d090804031208090d02120d0f050108012309030324040507260f042a030503070c06 64
    0x2200f0440e440681240d40e080d0410940b82d00c030702c654019000700e6141c030f112001e0a514007003140d8251403030402c8451085240400c1d011240c0d03a4802140c08038103007a94560651405c4640c07190904840d0001031081c0d510018601d11800c00d164401c805550090300c0c1d22010411011414044a03564600084284144541c0c01c5456004802810b5081c40f416400304840060703959143c4c1942255108076925010b0703860100b403003a00410307400d40c03004070a402003040800b1404c00958420880d5028619540000f035440c004519540042d024581000428091355075034550141c024494140f8162a06850312080303241e480b00c070300700b4902800c9810000c50454842d4403c04103007a04c029100420b214070b10b403450a00d0340f203a00601d489182c054643c0c01660300119803038194400f02c14021440c03032203994100849084c0140b00d294000350040c4282e220300c1c60660f50314143c5485640803030a903246000c400410418004000d0148078410380c415100320b40d5500341030760200000c0c000040c41d0407840c80340f = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 530835395 1250 530834145 530834191
    0x518070b03041703090313090207030e0d020307170307021903260a080604020903011a0103110f12040302030702030f2109130905071509080f1207060e0a080313030e0405 74
    0x5107030000f0001d410b1b2407600903080c560b000c00c00310342d0b804101c0c6a50003040040c189070b001500300c050a80103031002d50b0104100d500181d110751045c024001c45e01030441d9012004541081501c414030b5000c0c040702d0b004554400280340320042d51004a0340301c40e85442101c5000395042c04509081200d01506091080141042c0c0e40390754010900d5030003e07400c5c0050182e645c0e09008000c051411440800c44820f0010001002e58102024000c1c1d5118104240818400800300729000c0c0742d6407008515513500c452400700e00314403880c00042e47c50300c0b603c5035040001c10003207080c1782d0901d1040541d94441103aa00024a140140ca02c2942e11542c044803004a60a0a40100f01e61510078002d03158001c0d00d0705100c0003020780e441302e540001881d090040c00b00310420480d02081000840c02803003031101001300c411b090b2190180081003161a078840c14844581006a10081540200015260f00d045801503005c000f1406043c2c002404041c000400c41c14070348a03040c003031414891070032002040050 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 530836645 1250 530835395 530835397
    0xc021c03050402030a0c032012102f03010e0a0b0d0219081c1b050703030516080f0d140603100c0e030625020c010905040905010905010518070b030417 66
    0x2080c1d80501031806510001008000801c010b10f2244110060031490050160040710b8018049401440c0e40401e086010b64001944004484004004250305e00792f102030b40385d08a50101d0080030411340c420039050010003a00a9410381c2c110480c12102555100c03c0c100903600e240302c480c0e4200305038101e00300c00f6081030503e12000496954200034055a54044d0926050681c071940400c054080e24415426500082041c01440103044840d0607001580383c041d20f50700c0711f100c01070a1100c0040c44150034076a11715a60034164024014a0f12a820341030300c40d406602c45144076404c0f41c07a08403000000050140ca203806a800075000300700303662042500400402107007105000344900c60702020880c0d903080101d28400c042e0400114103106010746104a011000010f21040d0f4004114902050364458244012244119000700d2001c80c85d0400d940101590840a4040d50810040242401c40ba06401400f058030030116900d085d0347c0e01c04a902400241c03801041101803440e40032255964030 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 530837895 1250 530836645 530836651
    0xc0506090415030b160809100b0a0b04120b1f030206030603030d091b0609060f1803050102120f0c211b030702070f0603020301060210050903041d01090c021c0305 71
    0x141c0002008449403607600b500c01459031040311414114000c00c000c0b00f050401ca400c501030581410b41030390600301c030215100c5884844035031215658145905043c0c2d42d502e82a001003117131581e12980c1c2c9442d4580d5164071400a242554800c0d0024089074185022901408450007403000701c1c000741c1e05550030007680364800b0382150780c188402d1000c1c01c48401d0b0751064503a428070480d1960588007032000201c40520403540042d0501c4810070003003240ba6000a0302140003202454105400650101e25038a00f12203500050525840421110b6a00540310b038050b0040890602c85080d640e950b05254445108100305210380e403110041e090074424101120980001c1c0000609888076070007002111207400449802c001603002e6001082510343c0e0074850005000c0c41e28044d843c540c103041001e56240c2e21004000b0401da61400000c501c00303018400d51b005820080c01c188070040d8043e2401c01e18031028040d88400c3c614020f804800c0c01d00000d03030f124480d9440001858144032028003640100401 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 530839145 1250 530837895 530837899
    0x91b03060103090204240515190c051005090a021f0903020603130803091e060105090c18040c02010903030f0c0c02100c020d080409050f072115060309051002070c050609 74
    0x1b2030724080c07102000a44508201e2148840d00f01c4217180c0000c01c81c00b0068801c0c507190a1404006201f42001040c4500106c0101402c142c0813940041c98807503d010040120074a0f01440c0c507040c807102e00d0780860301046c154001c9807400c44c0c85140500400050f2001003080303001c21803a180400050901ca0003860f8081307802c01034403800211940300d1040c0b99100315004540e6810690b8005018840d1000500c0610100c0d001031400c1e40c10503000c22080e120140c80f180b80042c000c606c400130342c8003800d070903040141c02810502481050910181c0603100e03502007140400e00f05002d050407414544100c0c000110150340e103403480c03403a5030280070441c0fa11441c03910400181203258000340e02c4410080704d28510400d0034542e03035803600b4003020454401030b003001e40000106051250b010390010340a07885201c0e8444002e82c0c0200c10402030001c0c10700100030b80c0703210b600810000d04c1d10380543c001031620340039005035403002a000d0351032801ca10801400500303059403103a042c4510304164002d014103603c0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 530840395 1250 530839145 530839151
    0x909030207091a010909060e071202090409111003020306030703061d030a0525020306040b07020106030209090721080a0804230109032304170712030905091b03060103090204 76
    0x40d100b202003070718148030041008008140d120041d07540e0016800005200716202000158200804040960006440d40c010032112403a51890140d4560480d001c280e00180204601011450800748561800c0400c0703100d900303007103e241030060080c0220791007600018080c0004508540d50b40b0000c10302c42c0740701c01588100d012140305e00e01040001304140c41541e2103803034582c00c0744890100c0d040c41040aa05e29403490185c904010388000400581045d444911601980d480c103000300d0043c141640b0180d40b2003001c2042c0241b0110116190b000d40394451000189088490342030480580c500200400303403c000c02c115604079200304c000c01d030014401c03580c0c0ca50081c280d038402400c1040702d540614907039545144000415070041035100c81e00300400b94011840002000c0c0040d54003c034818004c0325484500420203000e03061000001500030031315000b0812006003001807002c05c080c00b070f0318050340d144000304417000103001d550910781003c0d070b41c11751442d61389200442c0a025000f9003280c0140d1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 530841645 1250 530840395 530840399
    0x90c09090f02090904080d14012d151101021611031b03070303030509010b040c17101202090903040e1e0915010b0c0c12010c2604080a0c080a0e01020c0411040909030207 74
    0x4008c8002c01d00030b220306080c0d03544161203884522208008024031a8403200641c104005800b45110181d401e4009030a051800310460301c0028007a00c21201e5900340c10f4942013045c4200105200300c0454002c06404803540d884240c528000c501940f03401c07035541503000d2941000084d01c20303000940c5c8414043c0001c280954101c01150a0300c000302039a001190030782955509081d195000c0f264411a01c52036083d81c03500e001c003907030b411207014040a8091107a26000800b0414200101c03001440c800d00910224900350742d0804002e480c03600d01ca80c4550000c0c001c20280800010320354680c908075012007126900c2d206071842c1c680d0045525240301c0c02903035420745141c2c0c1c410160b103040300c640310000300b2055074400c00101100c880d11421195924065558030744100b107005882d81c0701d40d2048a1a5441c402a07905484848500b000180420400145034000c40c0d4094407032104220f0a800721044816401d00300710a451401c1d41d4004c1c1c00e04140710402c00000303da00000c003258007034016551156 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 530842895 1250 530841645 530841671
    0x702060420100807030c021209010f030e060408190c11060c010b120d02010c1b060b190906060801051c031b151b0504140f0109090c09090f02090904080d 67
    0x2d81040010010841c0c50b410440303855014082c0b102010302a03c00f4000240d00c0d240500c806019101640b410007500181505c03809001b0344c0400701030951002140c041d4a000e2910325441d9000311200700c00d5036107100f0225492030040300268041c41e80081c1310b514081000042c80300a0300f00403510b500355920758111071010b80b14444d0501c840302d0808080c0c150341b0a030020103825185141c4400c0e042080c82d0783e4003805115041c0046003810303400040030845519420000d0155072107501882010841c2800c00188011550b1001084521310f40b10054640e030f8030b20030070880c002801e420388011060140110000303031107507220841c0c1da50101200344e400030700394440d054803180840c0d4069001d43d41d07111071414030a2040000e0300c4190f65141c00c0c1d02d40760804241581040445040500034400980c00840584c083e410903000341000c1041081f00c00d602d180020240d07012885215803852401c10340c0300c5600014001c90700518000742200580e40c0b16580c40310f51b00c1e840324200031401075682e100d11000f0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 530844145 1250 530842895 530842909
    0x50a0f08190c03020d0e01090e18030c0304090614130f020d140402190807140406032f0f300102120103140318040e010f06080718050702060420 63
    0x201c5591420300d400c0c91880d01915216a008240c030a018801d405119940c2c1d000003540d055540c2d900425600f526029070480440c1044031201c00c950001080a40d00014000041c00450710118030038414107035202d01d804a040c120714a0f803504a0801c0c2032124900450b50040224a440a280103250922110710141107400d03019801d210051120207210551270407030420a000c141f1070251449040c50189550707500d1502d80304813410038044514410959a075540813000844d044821f404c030107805404058040d00c1000d1040c0184002c1d80c480303101a0070810043c5030a890b002d0400360b6031143c007800f582a0144403c5450016080d686498240510700307001900c0c0091401c2960300b074030350451411900411540d115030505038014005a09072108040c0e9080b604031040c0c0e80040c040280c0201c1601401c6112050040035003001d1000401110014072202180c180e0030300c280701902c1c81301580d002c0e61019070303083c0c00682c00075000c500400c40c00ea100e070300e510344001c0300694184908004103500c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 530845395 1250 530844145 530844187
    0x9090c0810060311090f061e090c0c100e071a0d0627050c0702040b03030c120301090b04020405150a1b08030a0f0b01080c030601090e010b07020102010b0a03050a0f08 73
    0x641c2c494404000708607110400440400d000c50b040112460108146900c404000b040c1620400c00e00c4084448589001d0301501d000402038601c00c82c0d480e05181540d150780c070820440300c0b00d1045003461080e0140ca0b01c148200f05007a60003800c03089103044813104185515070410305002030204500071501ca0648510801064103c0340040020100002c109445144124040d10b185c200000c0040041c41e9400707d0380c105d0342c110340000d0700880303a00100b8076600841440c000c00f407059061002400701c000c00614100e40c4603840a0141210010601040e4019072251903003101c0244402c1c0030300d8507110f011b40440440c51500c25540c0c052015118640c42e500d50040c0d410b440000207100c05041c550260071020702109409000440c3c945d40001d150400042103441101d9021011601e183e1164500b20000c0401c05c40300900303941c47d0389045c464ae500410040b40590701c0c04200118505000c405102165000f002511001c005500c403000c1c045070304642258040410404007150103071507512012 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 530846645 1250 530845395 530845423
    0x1b0f09130903080601230f0408030d060503070819060209010c02060a050711060315011218061a010c23030f030403021011030c0706020c0f070e16050a080109090c08 72
    0x180c8100908020b0810180031301014104007101020006040645041000340c090340640e0543e2094400d6000c1d801d80100e0f00080f00500000940d440d2000807a080f08050711022010350f814030b56900480d0740e8030403894030b403511000c0f000401c14010400c1399000d081c4448060510a40b1084158001001940101d0200c0d003c80c5000c174844050083c40300450700203200594205247d810004aa0035005c101126118108444401c0e800039402064100003000402d000342c04e070043d051442e04002604c603a0741303070fa8101c0090312072800580d0b00c120341c03505850743c2020014902d02405c903c40011084640160302e0320344070800000a0002c5c0c0400154400c5001c1c1e030250132080c0952070b01e5410f4032100e0001d460000018002d00540407801d60131240c3c12a4080001a55401c005d81000d0038040031101c0d03c1000d0040307242c002418200072400511a01640031782e658100c0c00c0f000182c81b580a114400c00000b8040401404400e035158000495140503055062806a0301c102c0c2c0c6281019800d4044 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 530847895 1250 530846645 530846651
    0x21090b09030d0e0c010509240c0c0f03010b100815090f0a0e0a0b16090308070503041d220203030d060b0d0b120c0405040f17211b0f0913 60
    0x303018010510564110040c2d43c8081c1410360340201c0001d010b4060500a6031103003900c401102e45a284428014070101804415162110340c08a100c644801c984500c3c54090b40c2c445002d0b08071442c0620407040341d000020700003c114103104001f00e544980080c400f01804100c01c8100e502c40c0c0e81e00d44250b1091b41490940d6117146880c038031603000d4654080704400e00b03903c01662140002d000d45c0c0c8160b440394015454140402d03550b20110b54103001e0740e002070841c1000141601c10b02c68040f00500a64104014014800251124003a5942012504850951700f1850312201089a0b0080400c0890000741181c1c1070140f400b00d01703402c13034004da07100e500702c440c00140d0985004524020b0700800841141d0f0202d100310101031441c0c1700c6e407408a00c1ba10903a550000034040041407070019981540020b031000e0300d180d006089406640c01804184209205005140e00d080b402a007a03034843e084502d00840600c126031215001ca410010425210b80c1052100040c0d0b078030f030004900700d2001c85142c04 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 530849145 1250 530847895 530847907
    0xb16030c081c06120b0703051f080304080c1909020304111009080f030703080117070806041109010512030a1404080d090f09050f0c0a050d0203041103010c05090121090b0903 76
    0x5070044070f2055009880c132501c0c940151001c1781580c4c0010ba03000d0513605000c141c130364619030a80e40c81480074501c071407503241e1101c1c08a0341320b9000000d0826074003400111041040d000c41000110000113860240c01c404c1c00109009221aa030069908036200c0ca00c41a1200e10101c0011508007514404000294180004101081040090f24404803004001d1131410506850050100c2d1050040e10180004070080ca240d921081019400904444065980c0c0342020310b80303402d8182d000600035103e24407900000c104c929004003104114490035005500d441c040707200c251800b01290b012000e64032018040016040c0c410300650452002641e521603085041c51640509000c190b00109000b503d44020005003034036101020350000f40488178036403982d902d40e0084a9510841144008550000c02440200070560001403040728080700203000d5200c450034211540e016003e030482c0060100180100102800c0750414540303588a0004036400a00d91100d0141c00000d542d0012241e00008034 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 530850395 1250 530849145 530849197
    0x12050a050f011403030702120304030c060207081006120b0601030905030d09140109030c03080a020c0d0c06140403090603020c030903010207050607110a030c12030f090302030915040b16030c08 84
    0x10901410f18401001e0001d080d01020a960307001c1d00c02d00070b019800ca0b43c0c1d5041c02030303410416180110703401040010880d407580c00094a82c6c80f50320581c030042c811200e0300303e203409860003010f080c0e170080340544003c0d40c540d8a541d441c240f4013400281c14036030b0b00c1c1c41c14008107406200500111150310303000301d818a4a40703001c0c0102c40d005050030640c0d1345080c004c200001e5212200216594051504280588580d0f5508009208000300320040348a80307911503002c02d07000350748448054014402002810386044016883d142c08a40040016010820522030180254090031854040c041180d00340080400800d08907070100314103884550144082215065200f0b113030340c0f4820b50000c0544100302c010703600078184104091006190a00314180103828a2180d408440c81500009051060100c2820040c0d00c0fa07210f00b004a000720752209591140150705000c44040350745108400b441e1260b41120103070846038030202141040411580b00003c184031002034000000ba107003a00400c0107140303403 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 530851645 1250 530850395 530850421
    0x5121504061514040806131e031805010305071e11010504050705120a050d0c1e0c180c02031603030b09040803010e06010e061903060b1201140604150c020112050a05 72
    0x404841143d0040006200604000c40d0090304110300d5030415091521a107000340300c81c481810030781c0403202c450340072105140e44001e8201c600c0007071110040d04261240011004e030713942101c80401040ca6005180560480c3c44500c2c124445d20b071900410705c401c1c000030300342510f000369020b44641d0b01204c02401985012005050340e807824a00a004d6000a95a6107031038104280d0260140281401c0340404e02082c02c6c0c02d2280032840c6504115184003520348901c0324883c9009008101c1c80324140740c461200544201031202c003064000314185814400c10b9072072000102c2d0114100b540307810000026880303040ca01d5028030320030100151250b05010405c600c0c1c02004216a04011140010211070703110002180e6140c00203c9807880c0901c4460803e90150a00da804403403200d0300058440c0a1010070101c9038141c502000000c425040300104202a5000e140a104050035101044443c0f10380551402c40346103106043c054002070b410500e0404442e41103400c02070040d1918204441450361300 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 530852895 1250 530851645 530851667
    0x1201060314060c070308040f030c082701030507140c160f080d021f02070f0803150f10022e060b040302030c0904080d0f0209060a03060e0c0901051215040615 69
    0x150b50f0350420f503003074400411785c220140000e01424618451002070611410101007480d400040f010b036242c407140320811203071541c4000d1310380040341e041c4402d040c0d600c240144d40c041c0201e9500c64014a078640c1180849505c00c0142c11894031403035400d42400300c00c8085d400000c0003170041d42c001c4c43e840d0000040c1044407492100342150808440507078282041e101307080120440c201d0058880c50681790164107004400c00c090302c3d00401008100c05126108031411358904150703175001005440f0070034402c40400c68091000903811507079900410b6404441d620350a8114a40c41c07420ba021800c004004035142e030381003101c9802e8006002c1c07080d41410811254202c00542e0807003641d03d00b030388585503103010703001c1c000c401143c45201403601500c850301502c1a40f10020031075a40d07007000c900094014007007071003910590700900340007480b40310441083d0b401120060f140d8502d007603855282007288180041c03640050b0303811065800340c0b94856100e50380c00b50280038006a403843c800000a04002070003 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 530854145 1250 530852895 530852911
    0xc06180905101205011409030d0605040e0703060b0a0905151f14131d010305150912160f140106090e03090405040c0e0405060a051501021b120106031406 67
    0x5820301880100e0521200112100b81c9010f8103000c1c0301d031030158050303d00070f902e284007074180005001c52200003000500e14120500d42c20021140d440c020b000646100c205100c078540c22020081001c14100d4200c880360b031740300a202000c0c058071030450703c0c1120000c0d15041c1c540820030403810b1041c20680084a1041c910b800c0540794100030200050100c0000b032611801c01c80045904002c90000a03840b9000d8080d581c0824916644d0701c0304c1007001394007480241e41910580102c07070f014034040340c8228060b038460406400b0300f035518001c441040e0322510509071118100c00303090340071402042c8201030b814810341e070103c000c0e9071590351242500e21135004035032000e242091032040310000100300c4d0741d000410b41e001300703543da11802c14202d09600317030340802440d0404204106c2005008620244a00d60b180000c004540300e2041809008010258250143c0d00011018485090488900d40140001465050204140c14000d0300759821603000321040e504010400e030410105200300355004082d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 530855395 1250 530854145 530854151
    0x31a04060c0503151201110f09030709060f030b090a0b0106020a0201020c0301060807090f020d02070302100c0206010e01090e07051905030c0603061503070c1a010303081003020618010201090c061809 87
    0x700980304d203030824031403da481408950410b20403400c003034003c0020b90302000700c0b07039440e007080c01401100e96101c442a54824010014003060f01803481c0711380c03016150550411001da1781160360b201e100e103d02400c0305a003849420b08171030006031085440c43c00f13800d5a5000d403540766928070019140080c1040e01c288642d041680903c240400094200101c403189500440d6030314201d4000d00c02889180341100340c0e50700002d46001859000121609020142c040401c818800550100d0300c0e00000e0003070311061420000104040b00a40d0031000308542c6070416a42c025598800107984007000c1c24011303132401c0706048100144d21b030a104c019007141c0c0c02d9030114a140340c014009034501080c0c3c1c49100700e2441c017101007104948034440c16902c10754410603030101e401169007009084c034002d10085000491440000d05100ca0940c03c0e03500b107940c00b6154030705141e501292080c1d1400c00300d210314115940c0d0007a04000c11a1112890010601a156072180150b4000c00c8600304038030741c10072545142 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 530856645 1250 530855395 530855401
    0x40e09060f190209030106060504030308100f09110d1406131e02070c0f082a01090e06150304080901140c071e18050108070f050312030709031a04060c0503 68
    0x3204241298440c1c1201c400d0090042c011040c0c0000380212404140c2640c03a16001080d110703004030050003928001d844100d590b5a0b041d2a0384e8202400c0d00a031240402c1101c010001680c00b0741005e0380c140030b4100d035141002d813264500c10443c0c0780c510b0300c0501d2803130b0341d0140030b101c0c2000828103195414554050000d0020a00101c0300030310385107000c128456001602000b4019080c41c140c02410a07915502c01040d91001203039995000c24082000300300300c143e51280d40702d010015082c440203041e1a0500881e14100265425900042800381c1007030400801c1040b080c0000d000314030541c411500c01d501c131814000010b10300380d496088178030303982c0c0d04000403010b41200180d40c0b01118854608101842c490803c4e60a070401203600c03080c02618a055031808841e00e0740c1003d810303181c5e2001204e68607540e88540304a19551845281c2c0c05400180c1e01c140303002c01c00c1c001594170a900303003040b20855582c0e40d1303010382c030852483c0d030003448810701002c0c041041b4031030040a650000514010b03095007 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 530857895 1250 530856645 530856661
    0x60201091709060721020606010f0e09070311070f050c01050f0d0f0b120d0f02030a2001090203030a02070306060506070c050405070c23191a15030703030302040e0906 73
    0x24852003004441d40c880031581e00e20355500c0398101c0348416405041076850758100058000c085c81c15000a6026009800001704c0a51060504c000920180d0b592201c909000c2c0d81401031142010b0304200c01c15480f11089840d15919900400780a1701c245605a0514014185103042200602009041000402075640c8540810382030710540c288409000401140382081c240c010400008281d4214501c1d80308116900404a000504400c0907114403148100e010012600c9202e401411404a90f004201c50400307000e40c2d00b50062032144200000301c0c0c02150f000245580c001101060060b03010380401d0080203640c1c080d4500810041e601c460820119903030720300d46403182d801140e0181d0398480003c0c110300d1162019004594000b051820070903160304905865258210b41f00e0003911482940024403030b684030311041d450385c004901c160840300d8200003c22848000d030280811003941d00c030580c1c82e40e50500020004605c00d031001aa074524286000c0000c94000f4990030403500083c003005506 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 530859145 1250 530857895 530857913
    0x9010605090c130302090103110f010e01050307030902010c05060c04150c030e060c01150305030a2a02040504020d0812160f170a020f120609240108040c17100606020109 74
    0x300c4004034203900d0300c80d00300801d000f1481d00c0c2e002942c80080b43c0f0001080c404a0140181180801c0d100f0044c03101e20840152041c0e1031030044540010f0080002680d2a4030a900c001462481454101c0c0400d2140c2c960910340312007521501441500020108401280c4c000502070082c590704004100c40358079140075101195602c903881c0107060000e019010100c0039407040d401c0d0406008100300d0b698690500c0c40d81d81e007100e81410049859115124003400c90201440025600507034a180e607901c1d664280000f40030080e208a802c92421040100007511702409002d1240c280106140d29180101c203d4601e8800c038540d01050000003a00300e6480c1394080a030300c404400100040e02541c84407085003000744500000c04c4090a8003051032210440a2100a4003801e0100c2e07211705103880b40134030318440ca04104680c03c06072129141c101c1c40da500918090343d22a00032020208420f50740d4010702c00d54018080390403156040512416076212403442000003501c6a880204440c0b03039290349810b10 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 530860395 1250 530859145 530859151
    0x40b0d06050a061227060e01060b07020a0b07050c10020105100e0c1e091c0528110f120d110708070911041205160504020906040b09010309060c020309090901060509 72
    0x10350300e4000500703880030304080b070488080c03585611800400c521b00b0600c0080c40003ca0707102540d400d2a10005862289800362081941c0050043c414146004c03481a655131100004035114040d179601034150755500744920784445019000440c1500d014032580204c082c440e044883d14144110510621202c48420b44810310300e0320319079070f080055207030303a402040c064500d0840d80300300121034003441ca642052034110300070701c00c8044130f003603100b0b940c02c00c01c5070001c8800c115640340601d0b041001103622000c02c45185040542001d0600c0e410f280810118003000f080002668000c0421509135a880380d144c608222002c005010200e05001d15282c441d900c520410842648502d082d40a200b141e50460b002001004034042c0815030ba46000ca4446680003241c040400314480001104c1c101802150300391400280068600307414401e90407420f800c035402d0541050360390181440003402c2c1d44224130441c0c20b16001183c548410300100714100d10014031785012030b41020002c2210fa1610f09030607030 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 530861645 1250 530860395 530860427
    0x9030f030705030717010f060e090402011e0c080409091406090c10021507090812040f09020a110f0f01151a09010203071a0604060506120601140d02040b0d06050a06 72
    0x258940381c01d04c0481c2d11108890030132019a034000b000294440911140008540c460b0710b800340c40c1c0ca25441009104041100c01a01048005842d0403092002c04120b14800030541846660b40080307440760440703a0410b0b0082ea0300c556071681d520082c001d0b40c0d000c5e5503152000c10002c103000d16210400d02d8981e072401d40014000c5d542d80081c80f41039402404082d0311080090780ca0f0300e0302c2c40d003104010190f60051098800600800080341c900340f000c1000c503000e0764016540312824a02e0107894000941c01020341e80100843c0042c0c401800c401804290f407200204002084500799002c0860b08444900c0c091320343c26003040004008008504103440e48081c80c00c58942d4891400030010703410f41c80342e8140102075100c0751f2034003441502e42010040c000c44065500b00175007074943d42401050300c1101586000d03c64400e0004149603c80c843c10a007030008000242d040c00c40c04054030050b60002c4c1c204400100f0045040a0043e1071442038000030f180403514064901c0c80c00340050214802000050 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 530862895 1250 530861645 530861647
    0xd020f01050f03040f02010806090903190903120201060905060111060a0e0319090609090603031b050c041103190908040e0c04050904051c020c0a060320130e09030f030705 75
    0x24a50380208192211010085181c6540380f4080c5414407005045c110201d0104486d030307003c24440e08000e51164801c18810004516101c10101c4000c51003160350440c0c0100150f40e00080f000410b403001210440d03845070008268241080c12110940c1c800500c45410041c1f1440c00300703034200002404a4106010070400035130796210714411829481140c0c500950000620085104240e110070308a0440e04103507900d0103010b0729041045c0a6074418031020f030026410300300820543d00c00c0309110038018403840885405002d2903000c0341c03d90300b0580300c2d104101300100410200c40031401c001146c0111001c0100720b10540c1342c0d100310440c05217000c0d035001c41110340000360300b08150004407806001c00801e80d41d80f6107007a10702141d0300d00c2c00e407099151a6003075000f00c2100350b00011306006000130040040140c5c03070403c0302c11001412148209000303400f01d0f5a0542c0101030300d4000301107180d003004450400a08180d003010302164050b0100c0010351007040001d0442c050602a00d0700a02285401 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 530864145 1250 530862895 530862919
    0x200c01050a0b0910050d08120c03010905010605030403050901081e0705130b070308070f1202070c240e0d060207060f02070c081501170c0406060e01020d03060506040b2b0c09090b0d02 80
    0x2103406400307001c3d40d00c0008c4601c0700a10a01800c450065030407100d541034184150f0780c0322103086801b4002034030001c02084007407005c201c0c150300030070342a82d002881100c1c024050400c818040c0d0045820303036080000c141c001484807862038100d0000e00141c186800114501041540c00500d8158010040300810072500c1ca440d10340f0b442a451800300684244065403a042c140c1421000c41c1c2d01d51160601c010303c2ca110601c2801903101e00803000400603181c80704003503101d07001d00420512a0f80c00707c4800b9402c2000d08006211f0784100303010544113400c01600c510142c54400381019050300903810592103401d003510403e00840c4000e056480254001164101400788107182800c0303840103c2d0b1084c00c00d4000f24640f640f18129403a041c0b0b090342114000c524a26054013120384034026180c0140d0704000500600e88210020030920702d13440e5803a079614070204013018140c091071495031941600c4280468050350b000600c1c5d4094a20b0f05420450140e4200020303d0040b400003000780158401140 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 530865395 1250 530864145 530864153
    0xa1e0f1d0307090c1b0305091e090f150414060f01090b0301061404090c0c06060f0e040b040203030412151a030606040b0a0812090301052206200c01050a0b0910050d 72
    0x410340170128407a0520f000305158900641190003580509003e900440aa2170801009480e10003503210042c0c00d007055038850002c1c010304910010040c2d02158205800c91055440d40d01c116114040c0b140f0b4140e007542040401c2000c41000c079000c2a04111f100039084c01596401411241180c60900340703116443ca0240751a011805154810b40701d135403411000c8210140c201c021000660700c6100200802c64454441c041124a02c0c06015a04128000003900154203010426001400103007140d05141c0d54190380c28010929181c120387e0720344644d8441d240200c080c003500c3c130201c01120b01000010b103030304080395a42c0c00c000d0089108580300e4620307410607100c022006014184900c1a500c040c40040c0001105510004c4414060362808000401000521000e125040d07003114094007440c146403140400391074000340200018502502d4910340201d21402054026180030001ca020b01c1c0c0420140c00321005021064040c1e007003901046030030209808860103994046a03490355507600303418 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 530866645 1250 530865395 530865407
    0x30f12041a0403050c0f160303030f0f05160e010e0904080d0f0c032301060e06030901020f07240b0a0b1e0d0912140f0a1e0f1d0307090c 60
    0xe100200707200ca000501080c59403000c001c20541c2012070407202c000180034800c544e1340b5400700111010f0200c00d002800080c0c0300e5082030f043c80d121039402155940c1c40c130600c1d804840065414485090440a00540c950b4001a4050740c011090801082503501d45020400000c0e00503c000c16441c00042e5444149010ba440360b400ca0200103002c100c1c403000800c014004000102c5502c00321851803030a10404600c0c405118162151982d40359000044103046c05580d401c0504600361554090000d44003041e42c00000c2c100c2d980c09030010f807a4034400070300046c9600f82b603850a045002c3c00d2544d0284e00b13841d400c19200c1261401d504496490141c0540d0500207422098201c44a000008500c0c2e4820036039040005a030303026070500e03a560409120290340b899900110702c110020140003001d00a09248054000a0841d0503c9200c0512440300c3d00d0f10a9040d2090101042020313103130b014590b03400500940308502049000c2e400c0341ca610006590391019100d03d1901903250703120f00c0c148501c100 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 530867895 1250 530866645 530866673
    0x102061503030a0f030e0708010507021203250c05120d06080a02030c220e031b07061e05070203061807080106060512060f03120a030f09030f0c0203190c0512030f1204 73
    0x6c1c05642e040e070303100c891940c06040291940300040c46803119000c0b8154009040700e010b81d03107040e145080c140c806014551103144800c201410710241d940c2c8080400c0051200e0b103100c0c01c1c05000d0700d036641d070f5801e000b1040b220503030056000c2d030b444040c6010040e2800540a2500b190840381d203c540850b00c9003241c104403a101100d40c0c00c2c0d00380586800070040c0000a801070b071229801013840c0d45c0d403904115645603894420400003651031000070b901d4a940009442c5124000e203001490310001c1c3d00842d16100054507036018442c1c0040384041e4095040c8030201c00340c100300b0004e00c040c6251100040281c0a032043d40b080c2c141d0140003040c000d90b00d80c98280904680039041d40c17000d000000c0d0350034142e003110040b0030201c2d0800561000c104d407d403142d20141541900d8460741400981c1040360f030384450030001c076094030402117180f6010724040c80f804240c61280b10a8847c1c0c50420742030107952030182284007465801409849211007403803054802040440d01d12007100d40c1c5505001c01249599 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 530869145 1250 530867895 530867921
    0x150d02030f0d031d0c041515020a051002070b0f0702070306021902010f060b09130e01061509080114071107051f18030c150c08030a020d0e12030a0b04020d1a0102061503030a0f03 78
    0x100040302d16401160307030307809035015030255155040cc40402805a22818400804501403072000a090854524119400801c10301c125850303d03480c0d03902c0702c0481c1d01000080030701050403041020204d90900409490514080d0107003e0765242070718500040c001c0f074110900c100100c45904458036126441000c01483c5603009200069541c08078034400b210350b1691400050068902050901e014064149224014034603404960345015044070080c104020702c5c10385014042c3c001400340da8000551101805000403030005540d03000c40a004404180034040c1203050340242000410400403a01e401c0b40c410321403400c80b0b40c42001c0c04442a44060340001c00d0202d000c000d200f0200c00940c05000c000400540403c40107803102d0070f10340d540c1807000c8140e0142c00104006121041160400385803a14060800f60030903041c00100b506580f00500000502541c1d0880480d907980c0c10809107820011a892418100b10241d012036220b1140c00c1c501030a0020b40074109210031312079804810080d042d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 530870395 1250 530869145 530869169
    0x20708070b010f03020108090706020a031209020d0308011e0b040522020f090901080105041110031e0e060c0a02100c0c020d060f0606020312150d02030f0d031d0c0415 73
    0x1600150f031600f00c1c403400142d00041e401d1000603031162000540b403080c1c80241e00203019070200ea80c1d0031210f01007003007a0a91450740794481c110060b2184050782d44c000c1d22a445180720b540c108186101030306811442a110b1141199041041c100301004a0301603074019103c1c0010b1006091001c5054050401403283c0207100184c041d00e050381440107070554a100702e42003c000d903070301d040080c281e0306c0075100541406030740e01c1004d100d450000500312001240c6e0401182505030044511042c0f81b603480e00f104080e444806082d5000d0050290540c080c6000354081c1c00e0018a410003907803401d02140207112641d13121040c1409500904030740c801da95004003030b1104040280b82081c0904640ea0090700060b04101d404207140340003100350784401866103841c81103903036210300d5680088850303003902c1e40216841118001584080c49440106040d81c1c00910f0820103001c4000c0403114103c400841c0317002060360080c0109400300301e03000602001c9170003252008032451031200303002040c2e00000d860700d1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 530871645 1250 530870395 530870399
    0x101a07260417010c0201060501170a05042f09060d0f08070501060b0304121d060f0f040b030c0a0809030304020a030b071101020a020c0405150906060d09050a03090e091f020708070b01 80
    0x2c0c150403402e071002540d07009001940e0303130344010f441002d14801d80e04007081c00480007425080160348005d501601986410050040c03500d99000c1181401c0c00361032010f070304488101103d04102040a070040000d0b00d104a00d0800307910350626140041200031715070280012103009120003504a180504030001c032040d5641001e1901c680160200a5403001241c40340b0200f00e550782150445550180d80584814500103010461600542c000c13080d805444100340310118103050541c0186200b1840c0898403075841c81c0d1000c0242115000a0812425a104004100040e290a01d8920031a079020000d08000d0309d40f510195101e407041c0c51551384a40c400300703a421400c0da00241740169500c00780c80403c2030303480b20032180c1c080407200844e803900810300c200492440d040c5140200b40d095041000001d980000744d44890400b000d20400340c1c0050080e40c0d051082e000540c9505400160420003401001d9000502100080302607a000c590f069000c43d0341003e2049410846198035030100c0607005641e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 530872895 1250 530871645 530871689
    0x521010e070f0306140609060706090b100e161209050a261608090319080403031101050f16120e010510210f020f09101a072604 56
    0x80303021075200c0005034485440202d07007402881190141e03200714800e003010140e0401440709990001c00819004030003081603a0104074a4800e1055003403140442c2c00d0b060400f40007074801030740346d9042148000701c51404c0c003070804c444499032640d1201505020035040b5503041c0302001080000406412805200404020001086c01d010300c0b0b80440180708004210007030010145000d048410b5113525404841c0f00e0210b81400060419410028100c822402c43c07090900c14140c0091000c46140c040030909104143d040369105410209140081085191080325451482e0b809000f0441c0060540040c2025030721817022695250300941062007900e240020040c001c00044801084442c0000c0010072000c500b01000001b41900c403d5400d81a02151941c4d035004011400890b07210030207601d000451b481750084140708075840021542d940c1d20380300c000d441c01c034114000040b504404201c0040002c4807000e4409000c611421070042038844182c440c81d8921031a00b20031001480c401e02e246103a = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 530874145 1250 530872895 530872919
    0xc190309060507090b031f1802041d06010e04050a0f0c0c1101020c090703050703150b0c0706141606020d1d0c2209050a0213020406170402030c01052101 67
    0x1a510581c020000b60b43ca0b01d030b00b1a0203c507580200c540e019820000302e921a00004c81401800891541d000c601660f540d01007000d00d82d064140c041c400340c01040c20006040c0d064130701c4851001c1072422607140c0c900000001d100d800c1c2540c0701031081f55220041620404281c0c401e01c542c1d280031a080003036001ca8000034046058100301129100b102801d008007135403001c1040c0c01c1d4048080c26030240d40e114040180e002d000010702e114201a560212082690000028140242030555202e136665440412072810013040307802c14424080601c00005000c50114100c0700c03a010705400d1080280035a162403400307031150300e1254034450304010021141a243d2404c40c03600c04205002c4420700040072040c8103480c02e03c100e0044e0900c0c2d0400c0c0d50b2800c0f82198125805d40d6218001b524450030b12079000a03400d4541d80c8003680e030703158081800e00a4a41140d82d003000000ea2250b00e000314078150380003982e01d10b05011720301d04100001c07408896810fa818860355400c01a100f214940c0c1da103400c001c03844 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 530875395 1250 530874145 530874161
    0x7031a09071107050a141e2106060f0102070911040b070c0f0914160c170306010f030e03092103040305030304110d0c0e060d080c0102130e1e0c1903 65
    0x5940144003002a0620b490928602140e0545c02ea540a49078144200400034003040f109005078400361f00983c1e02d690b00c071a072032010300302050409181d00a40e140c1803403410000800c1180900d0208034021816a00041c0c3c00301107440d100d00104044000c810b0300045c070701680c0e0107407010203c0414000208161129074006035104035a42c9404241c7d10861003098030080200f0401d043c00795008204070b03151004060040c41c2050814440d000d10711b40d03e03040c0003030315001d024004007404400e218443d81c0c00305020400c00024135040c0501003041c41015164440c3d040018810906021544031000c0584c0741c4844041c0391106881c4c03211780c0e034104540c41ea402250f08480b03400000480700c203a4903048032100c945540000303c680c0b20505010b1001e1030048080d14a55001100100981c000750704040100fa0b00f2180800158850400a602c0c1e8490103840d008071021400220805c030104404410015140f5150010ba400d070340c40741d500076031482c07040c2c540d110a04010680c6100d1950f13055000083c03 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 530876645 1250 530875395 530875427
    0x314010e0a06020c060c1303080306040b1309031d01082205070b07021c050c041d070609030c050103051b09040f020304050a1a0c1b0f1e010c031407031a0907 69
    0x121664030001c17495000d20031f9104061f442d10010006102268006014540c00301000d0400203402404100181c410b40100c003005144039200d03011141010b0b840703285052440c2c0c5070312003500c600100b40c00103862018001c0c044e81c1441020301c841c60010701c1810803035848541180584003040c1c6c440307a01041b1580403900590081c140b01c0c40034981c1c0068032000084081d0040f000d008403600440070080a4010030501c40c2845041c078201c40e080c000300b406588001c240c0394071010b0010303285280038100190f0030342c0102c0c14585840100f06810a074100c0c01c030b000454040c00700e0b59072406040024020171200c081c400740c9034400b10030402003042c00500b407101c16000e500e0001303002880c00c840c0702e03010b501103545948085c01401146003851000412807411400310081d150709a10180072949022002842d0032a103454100c40744074149000c0c07040807019a0646001d2044a10700301400907008000b4280704205555001041e0505800e90000e0302c124000a060106c3e508080700006d24034a48000520 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 530877895 1250 530876645 530876653
    0x308040b10050607021c060609090506061c0f030203070c1502010515220609050702060420030c09071106100f0f05030c061c0203090a060c0314010314010e0a06020c 72
    0x1185054007002200455000a055a18001c09a400e028007642da180340d2048114071000d000c0c00140d458021800940303818540014141c03058100301d4a0088007034140f5000b45035254401d484a140c0300ca0b80414036070444078403048000c0500d0224a0341c400c108001d02000240074010504800c0894980d54405055000b440b0700d407580c46824a0086014620a42c80402c500c5001c19181401c0d0501e0070b11024084c0c002480ea039078650100640e50120307030701d48c0140c12000c1080200901c5441c0e070002c0240f0740e80710410403007030040404da83c0c4030075042440c404c6580100051000d44149525640004e9130f906580c05801c09404400354200342d0300501c0c41c01a082c4801140d000542d00032a421100001e00510404140c40300340500d82e40184480400d403000d003001c44d14040d10b9400118060340241c4001c0100c0200d5044c2103084681d0000d40c0000c050819014000d0a100321340281d0650b60466903484100701c4d0342000b54010464011410014011400a50709001040d8060640489640282d03 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 530879145 1250 530877895 530877901
    0xb010c0b071d030f1b06070f05150f0114010c080702040219080105061c0f0b06040e0f0f0c07060c030608120405030d0e060f07020103060b16060c020d02190204180308040b 75
    0x5886807904012132055030300c80c08805481c0d1440034040340c59200701918030b5190903519210382400540301d81c4141ea20354041c1c40b0740d5540448400c2c1540d403100d0100100282c0b54101041c40e21500707040300b00301c1c3c10440c0c1d005103c001d01c01c01404580b0103680c01402155030303160038007503464030a209441c00c00c081a8038500004190400c0003c580c410111103100586844051a8000c001e000c1d0040441d4035076a03404061000d1b07118600100090f01100e07024601c00d14080c1901200d0a50003010b440501c220407007030003c2c100e0200706075004c1c43e07031001002c61200503c032030440003400e907940120708038840c62000442144400000780262003054096501c00e4181c20000d43e80355907820020fa8001d001005000712181c482006046010310524011a01c81d50781d4441d0350440d04043c00200020b20f560070302e00c040289520545241e034410340054540d04070983c20184d01c03030b1400f20640811070106a841011541c1e29844106821110101800c9003609400c00030301c40351003210115207244280001c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 530880395 1250 530879145 530879149
    0x20310020316080405070f0303020f071e03030c0212010c0c02090f0919030908031b010e060f010b0c0f0109050606030f012703030b220b06030c07060b010c0b071d 71
    0x3281e2042d4002c2c011901009481c6404603070b0480c004005071442c0c0240300011440c4000e0604140040d402940280406c00303076980c645080603000d82c08591207801841c15041c4400e2089a01022079030107040404480c0c00c41c1c00070070f064a000100d80c00701e40d40f034107c0c3c0c000510380085240600318000c2d1482916503482c0d070a0040501c1c829036050b10960302c5400401c02400301100015041d40c8070785840c10061b59520040c52950700042022400c1648103000ca00c0e4813402481a4415058203200a000b982003900844c1030030b231410700908080e0341c00080c24284180003003041c07082c0035803000000c00094202d424440d4884500782c624512a00901c3d9090b559560140204c0e4040c0c100c100c0c02003580ca0700b48140c89075103080360401b02d003810b85031522034a240d61850340c007c1c40c1c0890b0f240f803490200c06040d44401200c00a03000540b04404c184140540c08000006032805a60f102400240fa4040440103840d09801c021005044000d2031080010b003660100c044a079040300d10200c51168040c00701 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 530881645 1250 530880395 530880397
    0x60905091203060d14030f070309031703070905040203060103060803040b1e0f03310f0605180c0d060908160b070c020306060f0a0b040303090e011e030b090102131202031002 76
    0x1d4544d60001a042071074010802e4042c100010000e0a42120f01e40305800f1781003034960300081c2040d00841d400d10410420300004848446110580b80c06151440c900100302501040141c001e0b94041e0f680071001804590081d803116024001040860b9111599002c074801c0590010240340160307548950708100600e0f1807819110340054451415040d5654800362403140d45541c07455510a440c01d1400c0352020002c4e42da120141d03800b40c801000c80300400d087c00340945401800103508007240a5020864240100d07000003101c0301190045803020850030602c01805031104046c4c650000000c1c0414400795520303400403100d100f81c910321403c1d981e8010039184e000300d8800194064010b04001622850701c1d80c0000030420300100304044043e1965882604c94003c0e80049000c500c000500307209841e00e14a0240c010425440b62007c40c40d24035050b440c00e01c003d40f100030000c01720341e008505101405c0d0103a07582c0c104480c5c00c021040c0d5603407034524000003880e903059000e8000d40020041a440c0c0340 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 530882895 1250 530881645 530881651
    0x4020901080403030c031b1e050c0a0f1a0705180108010308030403031d03030a090b090601060f1101021c1a010f050415120504110307060c021f05090301060905091203 73
    0x61a400030039034031503d05402500e80540c45030100360342d405590360502070b646601c45800190b03540703098224925802441e006540c0e0441c25043c42011f00031050410070010343e0700c003031a80c04140c020980d585481d108034035035909616455030007604410060080d9105002d0032a08401c40e22007011401e240c001525200003e01001c1c0006c4020400640801c0c045e0308909840c5840e44180340d640e880c4030b10070720300350b400c142c446444268503401a00c0601c04d500c8002d45c0c1241914000c3c1500e54908070b005840c04e01c034951110180510000c049090f240d0a5055907245000c12880a14407000c200c96140102510544d20701e854258052542c43c0303510900100c01c80c0c2c030700358440340e1900303003000100d08443d9000c24444c41003000100145090070117500500780180e00c9594803018102440c0c04250030044507400443c10424424003000150350b03007184100f885040f079002d40c810001002d0003101c8078031511081d03507010b42c2040000280d1b010103902c0103214070300200030b907101c6002c4400f84480d01e200503 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 530884145 1250 530882895 530882897
    0x150705030705090105090406180605041401060311040f08070504050a021206061c02040b0c01051305100902010903050a050a05070501090506040e2d100621090203100204080106050f04020901 83
    0xc0c000140d16074091402040001014103082c0e0822800c0d01c0010f068800e9504414074281c01c081065208201ca0300841003e4602200d0610282c510b80d0300c07481c4a400148214030826403202001609018154119006001140715003103280d82c90b60300840d0354104601c655802103140070009240b610440c42540e2002e20240d19900054940104000c001d401080020600301044e2004200004861008200401491240340d40342c1118800701d40c01c40303900510038030500340e4500002002a10101d010702811050040014a1200d140012282080705420003000c07480303506045010f000c400aa2004454405d030215a940c680310001142c102e1010311032590812002e10050260072041912030ba80203005c045810580b010511400201030303c5842d010300101010000d001800044018250103041795040403030003030303005030307125680403084540d61580305984440c4101155400d009180c241c02420100395195522000c841e8000c14091040e18800e070b08a69141c1c101e414640265803c140f01 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 530885395 1250 530884145 530884147
    0x1d0c030103031e120606030b0f0105190516021002010509010515012f01020a0c03030e0a08030c0310170c0102280b09070909031116081c051209010509150705 69
    0x1840c0f442201520320344450003800842c0f007030303441200d401e48621801480c0640c0d01040318074440003404042011050b40604004080114004a1481e59a65840032145240c003c1d56410404000013111507a124001d500c030754000d80609405505410603800303400b004001f046a80c4802022116074100c0748600781c00b00f4004d0038000c1480b40244c80d682000307111200325910300b400707142d0714502b26072000600c5404904e0080c0c01409045e8584540e805d0f00301004020440f15075191544034203030100802c900c8000d500040001c0f44000031901c000d00078010b031200020000d080f4100c0c1601c8611000c061401031103004c8032500302e00c101506401540d8110042c80e00c001501d61108040d1413002000c400c05c6204150300002e01e0011842480d0601303029030380d42503000e5008111079040040a5144c00910459450188001007010880703c407039140c03090f0440c0441f144464143c5013401103144860700c046646040080401041d040710703100b4601c2c9010313503500d500610711030040114191044000104 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 530886645 1250 530885395 530885417
    0x200307061b0602071a04030f0e030307060207050f2b030501030206090405040c1203080411010804050d050a0201090209010906052407120e0d3c11010302131d0c03010303 74
    0xa0507158079100e00d400b50102615080e525202d00d00820084040210039640075010401899400f40c0110781c4c1240340e1400036854010000042d650740076160000d04501c0e4009003580c1000420000c0071303200205078041e1915a00c1c80d41448011204541c45180000207030b2813460200c44c42841502e041e20750041c00d0034240034411003030000918000b0000c4410103011600803668003013498094484a00c40d076580c415a1a01e89002c40040d40d0103070900d41442404010300000460209040032916001e142044c0c803544481c0040b40580400b5501a4112000308004030310343d0059040340c01594420340b40300b180c0da444038110391100d040680075110540018032a080010702d042c1170b00245501a46404840d6901c1c0e08001120242041012100215485509113504104203a50149030310b09441281004050740c5054880303075055007000704079036010711288219038065810f480c1d2044950303c1008145171035203520703071a400010400300c20200003030000131140700040044a0589905a40304100e0403 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 530887895 1250 530886645 530886677
    0x1e05011b020a0317040e0f04030906090321050f27010c0b0a020901030b180f070504051008061f05120c090f06160b07090303090f030302030306150d020720030706 71
    0x501000040d403003108002c001850601c0c0c200e25401540140302041f190306051402400d07108050380030100b4400ca00400b000070651b00c0200c589400c40300c400204804003500030844052141203020000301ca8082081d03007100701c0464409850109030042e40c0690040180150b072601a4201c008042c2e1454500084001c045a005000c4845041c103002c01e8071840c800010b0100703002440c0e28813001502d10b00304903c1c510a010001e0f00202c079800c00c5850300b030801d0041845400b5070030110060200304004141c2648810b801a0443e84c041070742c50305500c104c0d40c0c0017041d9900100c03c007001075180c2070101d41d00c00520000c0b2030b44080010070042043c00e5a006000641e00a954130008030b64002c98a5004030308500f840600ca064190b590928450451401030144d4032a5004100ba40106803001c0c400607800000b10790f0045d508650040e40c1020110020a583c82014686050345001149010070004906074031024074030762080d280410072503001803555680076481144000fa4030803c0d01d034908 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 530889145 1250 530887895 530887913
    0x30a0506150a090b211c030b04140610052808040b070806030a0f03032a110604150506060403080f0d0b10140f04030501050103050606010201110301060f05090a1e05011b020a03 77
    0x441c5c0100240c0724451004414510032040c5111110003280c0c81d02c03c141c020f40380c01c1c401c010f03440c894201c070a161814240c0115444074400340b0103005020000543c1605c003070f40c0c040003241500520b450040b41e03203446130005111142c05c2c1c1d021101c899803900450b020305d002e42d104603c11b482c090010044d24002d505c48038601411020283c0a142e515481c1100c11140d510708000860f480858440740c400454500801c041c0e131501c1c0c8500b1541150080c000010300b240c80000400038040303408243c5498481c0000c0322480350340d00042c0b0f401c1001400c260f002d0042c501900001c418000108900500702d03060110322210340d42c0280024414600ba041149040700151488140c0c12220ba0300303240d129520349007101c0c020303001034845601610401c01151390900880e00c20702805103403a415545032440260400850801603401d00a001c1110040758a95980403001810010201503000c000c0d00320308919140c040c01014002114101446451510b200d08031030300036409880b4644091554a40f0908 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 530890395 1250 530889145 530889199
    0x111280305280e0301090201080402150f0c07031106040312120e070f1806080d0f210b030f1b0d0602090a031505150105030114030a0506150a090b 64
    0x5005003440720001c52680403442c54003a04a0103152840b454500d00040d011101108506110b40c2c109581100182d038800401901306a05407941e4540e00c202c046020758a01039048455009040070070950503003400000c6070b0b01224001d03080784000110490038001c00e445280800b801380440c27040700c4180d040c81079800f9020303003900800015094401c00801030808040384d11151012100c0b00042c0700e81d05030300c1c02503c0f080960410410031240761108507500c80c1c00e01c440070f4041c800d28510306117006000f10341303d506501031b006405400e1185200344800801e01c0804841c002d01c07511900e0540c40c840090007460442420710022a80c20f54902048401085900122551602400030f200e564588455100185102e540101c0f0810b89003400d090071140020010250b80b8140c50043d1040d9801808490542d8034810500f10240940c50120349000050b0400801501c035800c00c0081c000b01c3e200e11040c19010894910304190b80d106020400d5031a030507030441e40448006210708100b120000c0b1809 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 530891645 1250 530890395 530890397
    0x4030509180901060f0504021e0a1b0f120e1c0203030913200f030a091b031415010f0e060102120c060601120203070806061605030304050a0201112803 66
    0x9459550924120700340c0c1c005996881490f07444220501114001000c11405402e098404504101c0c0a8500c074043d0b04c80c000040b82e08900c001303902d0303c109210391105100b2050012410611554900c0d101e5030440300b01d80d00b945c0740e868102c4880c00c118410002441a40c0e0000d1500824011600880c40108001c1d030040b42e05110410500d03c05440329900b41044013402d0a001503800c0d44c2c40c0f183e450f5140304084103420360004018590580e030000069941000030244001041080352030b03c00f1425071005011040003c068078000f041003081c0c40400d6085d00a03c0603140004803400b4013076400c05d428041e0303261a11b00701200b8000490703032451080d803000c0148101c0d002164081202d51256010030f45448503600910104403a950704031032074880398240d03840e08529501c1c10803801070260102824403841103c0000b035100b0b000b44020002c441464000041d61f42c1c80c240b501c0c015079140d02c065022804a04080c281d00d203c45004903000f0b22010301000c0b55030b80b03000714840c100b00080060101b14 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 530892895 1250 530891645 530891659
    0x80411040612110a0510170c040b130513090f060509030909160e1210050601020f1209090a05070c060902030106150513080607020d2a030c1b0b0304030509 68
    0x240b0031141200303041a14012145103243c1600d48083c04400101c81c2c201e81d0003110f15501c07030390322140c0c042c400303030001c2000d01007541c400d071580a00011540710356800401c0e100b00114020380f02d488202e9080e0300b1100129610b900300b422002400301914034410010301800078040303115000c222607801c0305078052402402c4d20300d051106c000140b1401f0742070b140d000198000c030100c144115040300214000d94070031101d002d1028000300c1155903d440c0450750446141e1242c001c995280d0080040b020321303441900035a080c49690408032141500a00341440c840c86111020541c441428070620f4011200307540c503400801a05d8440c10302400da1000100d80540d65081e0000311142004040100f502c034594526550301070607850410208444e402011007504140140034480e5000501d0901031942c50038005410501041c83c80700c5501d0003440d820414080b00c03420400c141d8440446044e183c41200321501c010b05801d01c0c0352400303105015910070780d58100041000700c1d0103030b00600000003009000d4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 530894145 1250 530892895 530892899
    0x120c0306080c09040c0f03050303101a0412050a05030a050c0c04020403122a0c0509100806011a13060c1b080a020f030a0f050105060a08010b0904022403100905060f010804110406 78
    0x2004818210364012340781030b00044107001540c24220618002000e040b03020303022101f580700d0344a141c1d00ca80d00c03801c2c03600c102d112880401c000051011030099900007068a40341c2c88010009130041d8070491482c0183d0080403400705680c03402c2c0c030940c3d0540390005100031100f0403404090741c4000c50140d03070b00c413810000c480c1004921a10800038842c01e119171b0107151103510340403d002e03100700301419524050f210b40b1030030f01c070700100060910304540400301070003c10040951500441c0c490030301290b43c0d40c0e103101004074105130003c08041e90544900c18400140e0601c2045071541010340c003c014190300300f04102ea01524042c5004544040e0017815100d010000390307114440c40d8010402108c10303944403804c0180c00d11344690348400922529000340407052050002402c0010001c00084c426004a40880405100018618003131700b00e04c1500b030395a0030b14212825841e5180e105041400d82480002005401c01c0e046102c001c150613111030046466664a5006082c40070a082d50880e580b0840 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 530895395 1250 530894145 530894159
    0xf030106030b060c1f0f0504150b130e070303080601050a0e060f0f0a021f0903020a0209071b0804030219050303190e13051b0c330106120c0306080c09040c 68
    0x2c0d81200401c00c40100510800017981141907406200750000300318600803c200101d000351804440200c0348203400105403000714000340c0b401c2c29558100010515011090311502000601182947d010341c80c0d58002da40d59400445161050301100c10000f4079190035108c4500b4403001504841040e0f18544e418070480b08803c0145400c21140c0c400107900080041005041300c0b26050340c003111001e410300600107291006907940d40c0d8090000d004400040001c0c2c0064411690f0029140010a44881004590801860540007800281e00c80c2904045804241882d81818400c940016001d5820841b84200c1c8040381c0c0c1a01490100703000d490fa000c2040750741c0743c820300352095a40d40c100083e141030040040c0b400c128007048104044200304134518842c40e0000b580c002420449011104941081030f03284402c2e1100315010014030030b00d000114529400020400c12507645820412815402034000c4050703c0041c4201e1040780c02014108400307082c030301203c1c0e6110f40034560000800d562020 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 530896645 1250 530895395 530895403
    0x30307110d14031e090d0f0f05070608090d0206040c06210c09140303070203121b03073801090c11030f0c061308040e060310110901090602030f030106030b060c 70
    0x50190b0640d040000c2c2603920959110000c2e408555500d4100d040095550110352084504040900707040081c003411001c005000c0c5c20440b000fa40001526080c658072000030389070f05020380b048200b50041c4008001c1c081d100003085441183c0005959051610380740043d217100c04000b400d40c0b6102d803822514074200f2103e000c2d40c200200213680e0340035210718003c2804440031140050398881d4004211080c05a5000282c6944021101440d0ba56511941c0685003c0242d60b500058841c080402d03503109000000c211141107079010000e0101031803d5110b01401200c0207005c0c503070100685001884414003070781c08807598102d035040142007443c040c4459440c5030400c805250b40c1f41000501140c1c100014803c8903000000c2d01000d10216620756966251400b0368000d034401d2074038030303400642240d408000c80c001c0c800a85108021540f80110440090f9103d1002140481c003070150000e0304070720000072907192401c0e148034681164200241100680010810355520040c02d0223045e1600d94144 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 530897895 1250 530896645 530896673
    0xe0405070e1305010f0509071809060321080708180604050a03140a0e100c150504020f03030f0f0a11060a06060201050109090f030e0103180c1404050402030307110d 72
    0xa1142211541001c040110540d103510b09121141d0405004110310380780c410543d01030b542d0481d82c40c0b0856988010072996401e9414413034188048244c40068210200d40c0a4000d4030700400300345210341401844000780759505010000003600c0c1000080e00d9500c00c0403c1368010200c50001d101761854241e005107403000c1135074181c0300351300145802800c260304092146c1000010401d450300307007c04508040e1021603545d0070203001d154483c5190b0409481000981601580807859600c0c00a0084035100100307002c5808078004d8000d0401203a00d807400000fa82d2440d0044100c082c6043d8408080c003009410001001003841041400030041050500038180304044c074810024080307190400090940d42e060788002c80482c90414201c001c181d8804c55509800d4040c2080c4100200000040307005002414001072a0f050b07000c51903040044511156048500d010116076068919200f0003040301c0041d1030080d85940300700200f0000403003000000d85645401450f0f013800c90304903103d00c80ca131480340e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 530899145 1250 530897895 530897897
    0xe01140c1b0a0609120213180201020c090c0717070602040b1309110403020405100b030705070201020c0a1d07020a06020a0503061801080d051303020a08010b0a0605070c0b0a0e040507 80
    0x4894424450405000d1440c945841150300401452501001612104590242d420b101749924001400d64807481c0b15008080c15042040100c0100b80d640e5944140c2200812030041c01000c14400451615a010318010008250f1191900c074050303855a4032840c240d00b4128600d01c0034007000d000700e042d0744080d000500c80c0c2c040150760341c101190401e0301d04106800800c0e02500d42201115920300d0101610207803681a600000c43ea100d070713221074111030340c0d035072044000c20310000c2006403055002c4d0162820f00c0c0300382c0132101e50010355800c20a0460550042d1600d00c00c03410001c2001055400c07000760004490300603100d40c0d520644906040e03a003d21114008070700008180083e07400c1a0240d65008411303880c038071007594180300c0180d8031480d8030340030401040320108d0800c3d180441001010001c50f4010302d40d0201c95070351918076001e171602c40a594420b804081c800074066008500f2507003000e0303200c064a03010328204619880a078010522190401813519540440c54441d0302c00c1c94040d001d1 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 530900395 1250 530899145 530899153
    0x20301061b0519020607020910081b281805011701020a0c02090a0b0a1502060f070504030201140405060d0603120c020306010e0903090a14010801090209060a0e01140c 73
    0x1800c0e0007400070800e0700c4070300511103020005440800c0307001c910700c0032154505441280b03205850001816034000c1d204c000c1d41c410907010500404186031660300e4201c6410380d0550f45d400e400160540300f0302446e40895900080201e4032111002c1c1d51301c0704140f625040c0720074901c4413a2501c039035480316024000021080d5640700e0040c4041c00d500d007003003c03522103104020f500c0c04850b00001401c1c0c40d480e0400034098200680412001e04003500a44040d020180c00078140315941d0380c0004d034031070a2800c800098040d43c1d02060b103101c0c03207007102c5104117100d0700c50500e02861540111030000000120400400d0309201c00318281e541d01c001080d01001541002c00c8083c218142485080a1f490003402400000b00e401c00c0161008602c2604485c5034582d040c0865442c3c03c0d82038118451044c950b940f04003640c8001c034102050281c181400134007a0b0310602241c6e00c90011108a1050b0124690701840911009083c1445842c200042c408103250075000c000050b4104070300b0750005541d5031840d0700 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 530901645 1250 530900395 530900399
    0x30618050103030e0951011e03020409020c10060801060f0902070f08030f010e131505060406081605040506240c0a0804060801060f0305040302061305120d020301 71
    0x1041854481080048504109551440c1e0b07024110340c0111007480e00885000d000200e0300002500c014800043d61810680740e0f28103240b8a440c201840f0546001c0007102c544000c1001c4007003011074042405c113840780002020480c1032010801d0a440980341095000c00011030034200c1d5001800705400540005c048410010004000ba50025000100b803a894444c042220648040b074000803034485900041e907802050a045408689002010b8401900002030200c0490007414450403154046400081520354080010480116100140080f212a03121140001080d407003190800001040052680d999010160901c0c14040c207407105400111010015402c05018150744510211210020f03204490035015080a400440008040b80032400311800a01009034201d90341d0080368194445555050090900c0300900802d4009043c9000c1400301038000e000b800c0c011a89038000c1c10f030b107540f1140c400350b5603e00720f40d0540b505e11a1a00e8111118101c100034844180200405a5258 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 530902895 1250 530901645 530901659
    0x80d02090a060f11010c1d0f032509050c090105180d050715031503080913050a0204180e0a1716060203010e130f02010e270f0601050405220905030a0306 67
    0x6881031100145a03410580002000c80e8405001f42450108281c41c150700f480d10400700d600341c560003039010f81503c18104005141881600e6043c4040520303002e929800f51a40e821038241c40041d00c5204241c20140f0000000f58004d8001e008001a002014045400160001040001e11311800d41e0305070080f4000744100c1030741c0048074082c031030302e03090621007404129480c10311481d562001400c1c900c00071488040585c0d86201151500040640501040c1819021075001f0341c40b92050381500040620301403401e03500b900402130011490700141440440079192080000d00401205660500402003600143c3c0700c02941d002850280d84016100d42c14552003550b003000240890b0120b03a0925042000a540c00010050711503081c42d0042c0c1084842010480c0742d001226400b01d1092082c0001c0e100c40d0003070841d07070301c1568020b100315680e40b81c0e20015141d6100b00c1c040c05402280088001405214a605180d03130390711140400200b2803482d0b00c1e0702d400d42d001900c3c1e500002c4d8075032100708211 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 530904145 1250 530902895 530902907
    0x30a0315050d0c05150c100204080d0c08070b0c0c0d0e0a0608090a06020a0203070f050f07090e0d1b23061b04062f0a0b0f06010c080d02090a060f 64
    0x90002a6040c0c02004801d4680300743d0407100b81310f0580300e85c0088640c071030400c0001d0180c4070140840000c9844080c0c40103c41c101942090213803425520a04007a8024184104994802281c0206895152400d183c07101030812200401d141d480d81c008010003144d06500f000324049a00060713446880361410390b0104118100c042d8800010004050b003400144400032030701820080d0300003001607580500300e81c142c0c214010074a018085040c01400c0c0810700a01103401044081c20b036040d50001611000383c0310482d0740070f18050100740d20007000802603600404c11f0040d100c05e03036440640448501d03964035085100f031a40700746000c0d040d0855154100401c005040d0008900066020030025102c801650341c000c52107140200442c9410303456800b80400b64101940b82c3e00480048000c40500443da070350600383c1c40c1103c0550840c4001440c2220b401c001c0d90240ca016941d003c0c1c41c0c0b01d0b603203501c10590030003424607190a07401c01c000c014654410080400800c1035441d08041081304000103005 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 530905395 1250 530904145 530904149
    0x106030b0109153c0e0106050d0e1218030a0605130201080c09010c0609020d0b0c03090d0302090906060714070f05100203031302011211161407060507080714030a0315 73
    0x425040ca410020144500c01d40041000c413484410f200340b4491180b105070020742e1a40300780c81000a07071001207003a41e400801850200c0140306e041c0700414290306001c1d0346048499111802100a00c91400400c0081c0e0024000303c43c01405c49070200190388030901210340c02d0329100034105440072031000310758021555a6110070100d10190500f29203c002800070640b19000800c0c00d50390f0303060788045640315070503080c000c0e4215010040390f1903ca8032405442e0b005440702e112a1092454042c1c40612a00843e00840c401500c070350300079101c0b20f0500486400200d8226014016004030040d00d24040140304014910b064110701441d1808090190940f084014041190400c008000c0d00340c5540400f103000c1039080c41c1c803201c060044100c4034024450400e01040c0b0030400124484051440001002050301401c90003014003001d440c515a1400c4503c606808518140000360124003544050f2a03441c0c06039945c2c0650040780b01d00c2500f5948043c0c10304000c40d030b40b02c0d107400e00f44401020b0000 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 530906645 1250 530905395 530905409
    0x3030a06061701031e0f050a0506040302060c091f030617010504110d110d031e080117010917090a0504140f0109020a09270c0c0b0703061401110106030b010915 70
    0x8420750440d164400703410b0940c00c10100d01c1205480400c200700c0441e0f4000046c0d50003005507804000300c1d1070701913140c1c0d00945042c0c00520401c40416240400d0208480e5030307180003424150440700404441e050b111a42002d101851b03541d03940014041401c000b82d51814100000018051400d403511503528141c3d0b2460798011655119503000040030702407440c540b000201c86144024000f880c044a140c400c1c1c42c05c13056503c0c60b5101d1515915004808141030750a880300b4480d030540c03c444000e00300e03020b001c8040c00400045642c0304000031100c00a0010f40006020154106d489901080545039014202c21400d034076402001158101c90720054090b101c507410035450300301085401440c890003401030401c100031f101c02130146030020110110003885914420f0001e1564040f02030080c41c2040e805842506000c2c1c0001c40c1944030303105d41d90645140e03240e50090050154011a0880b0040c40050350a40d41c945001c8040f0341d601320014000d042d00780700455400512804408615015800780b0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 530907895 1250 530906645 530906687
    0x40b070f020c13090c030c150801090203060108130305222d1509030b01080f061f030b0402120f010515010509061204080d09120306050d0c2603030a0606 67
    0x160180d450003106203480d0365400f40441ca02c0c9107030030005108450f90303100900d102d003503610009840c090040840740441c0750b40c40740c000680e6a8800e15080c1d120445400b4001600e0000040c5130f41c4403428407400c1e2601a113041400c120078001c0310034180300f42e08030584c918061442c08000320741c00d484a0402c902c0070620170444c025480354040d00b1003038003030180e01801c0400e540801c002610942180000b1900410298029695501040e8071040740c074030100c490340660000540603841c10000c2c110040c040b0b4900c0c204044c9140c640e1804100050300c101d91110000c41c0360051000100040500c00a0b420000521400d103140c1c03001c944d010309a00241840820312542c0383c2c2e43c0d0390b00c4c180d5220380702a8801d00e203a96a103161548440c0f082500c44410746182450290600050261085002e441a1801c000c2aa1141b00b0840d24003043c54000b05845900784040c8030340602200c0980c105542c0541400c00302020001050868008844000d4440e50b84c500820100350701510010040180d0700081e = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 530909145 1250 530907895 530907913
    0x33020703020f22020c0c0310050604060b0708071707060e071e030b0105060a09030812190204080c15160318091104090218040204060e0405060405070c06090203010e06040b070f02 78
    0x60a500301c0303420301c44001c441e40854102d001c82c00500590140c1c860087c180c1e51070890249505006102c103445040c003c500c0c0c01804126091100f08a8041d640c00c0800c56080604a80d00d941c1003410184002c82c441c2014003014001031054000d40445c00b42c1c42d4080c052050411725102c0c0c1c10080744c04100c0d1034400b01c00d0200049007941c00c40c0c905560f01a9a821355448041c84c0a0b2405210340c2d0000748181c00c0003941c3c5081c001000c0b21103010b04011040c020a12104041c2c150584c0114061038040d40c016121072202450840c40b50300207010402456410900102c4040800b01c2e0010010350210308071803110480f68103400d0080015003c03980040007a103002c003120544500490007404000341d4006600000740780c030001010100c400043c000e5603510340304c040080c11000a81c06081c0540d080401044480c40d080c042c0c2403044000e681da40d0000c1f28181c440354050310740d502003a0303015540c404110301c0c02981403107041d2050307000e191840311600f03000b00024881000500e000046400c50054 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 530910395 1250 530909145 530909179
    0x50d060509060c1918080618010b0f090a0218090c0c0105060301020304030c0f030306091515020f0d0302090d0c090e0d09030f0201030f0f0e160503150133020703020f 73
    0x420304d180f160301d00d081c1c40f2400b54001384002603045508400614882e0108009814000c01c1e0f0055980c40000024080d403071886c03042c000b44048512110758400e200f900050032540e0944c2c003908909036015000c2580744c803000041428080c06031044455200001010205150b00340a901e8111030300717600851031480e05484c0109a000c0c0014014052352030008000f05041c402c0c2c00c020094011140108030320700070010039028500da5446000ca00b5415402c10450560001c951501c00883c3c07013025020815484200303e0096014030725180e131090f004400d50020600360603034030010300000c4200207144100d0910769881c00d5100081b400030030034070110910014003400800701c102c56080c01e002c12890152201348019200b2005c00c00e01e0b50f803802c0c9954217090030001e51100094104074447c1d030103a48030414183c480560a8400c03000e040402c0041000c04450702c0c82c044181103110502d0400600c0710520749036030782c20700c2411006903c14a401c2c019441c1080c2c0d001c2c000c3d0130840300d294071101d00c511 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 530911645 1250 530910395 530910427
    0x110f0702060c0f0102030f040c05040c0f0e0103090b130b0637030b07090611011103150a0b0f0705060f01061b060b0d051606080714070c050d060509060c 67
    0x30301038180410082c5404030100b2500800f4400720009646a141164a61400000441d01601e5070f004a21000411b0f007072074451201a0781d001c3d40d4405800c0c40300307101039030700e0000f84503494105560350140760085170f81c000f2090301805c010b1140c0031900f1500e00342400d07400da01400444c82141c0e03502180180c8102054017004070344031554441048a800210404d40d00060346c005805820781030204140d060303010480d0070980301c0325100c5a00034541440e40c41e08071203160300c074804d010004101150301e4800083d41d02505c104010700140e412030312200c0341550b9801040301a0001c050200e050300070810107000040e0b100e4003002012100358900388004015001d01d90600d1000b041c000410418002c03150042c04a24070701030480c040c07454480c5480c695a161210f144495a40100310100da03252040c0c1c0098002d0a8071f07901d5224640c400c509561440d440030f18200d80c801c14901d4000345540b030780704000442c0e0b40184c400292500e0b1003848103041c03400041c41504c9414082101c1d02094040d80 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 530912895 1250 530911645 530911657
    0x5010f0b0a0e150f12090d140904110f030108100519050a500412020c030d2c09011a0f0c030306150c0607080c070606030c0603110f 58
    0x1ca400340701018502d001c10080001c040314002004000900328486001c1000200b802c41d088020700200741e0749000c41c03e40c480700c51a1144c07000030b40990b21148052101000780c29140801003000409035098660040c42d64402041031020440210040202d07800034410068070003c0000306201900d0b11207000b2104518555041c2c03245a40c0c0e0005c14a205002d81c00480c401c030040300c0403021451410a00f48402c1703a07801001c001c1030650502c21481c201d100396102c6d002015044950482d0b11a507036410340b80b02004880808500c0344042c40007480e9400c0042e07040001850312250444025540200c80c00c034034600c58040c0e506110b43c003102150320f60010441c11030f44540b041c001400343d05004030b0312500c1220034400d01202d01064101d4507510200c0218041c000444040c042140b900c0d1111440d0300401e1503400441d001940082c5881d03025060382035012148018403441e05080ea0f40714011a02a508156a0707035203550310510890340c043c400c080c0440e058000c0b090401415a007650903600c600 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 530914145 1250 530912895 530912897
    0x507050d0504050102120a020d0f0e07030305210c0327070603020901180905090f060c160f1a0405160b0d0b011b0f02010215060d0b190903050c0105010f0b0a 69
    0x7410018007484000e41c1920740c900002d40d4410803506001031580d000c1e4101c403ca04260501c1c01804180703494041c450748a84150041c05040014a10348081e10180c02c2020541e00108402880f10484170354803c0d001d10502115030950740341d0920f60113654500780d1120000c0c25141111004502c1040001600e50803070b0761a00d80580d031000c0200049500c5c103d10381d0301692032140d42001082904894008a01c81c1103030004884501c8415000c09540b15002d68078000041070800030200e011b000c8188546115000b8100355034100c0ea2540e4150180302e01c85c0a07142c0e4800f0b002c05100400c03401744000321003a40c151321a650144d05061009500b4455404031040d00780d610401402e4070f0b401404001c0a07010082d4a07400d9a1046061401d124861403074220300502a52880070b91411407801158004c240c068451104880b0704da07200b90031000c0250040307603200c419000301200c6c229540507807002e00c3e22070341d1000d403685841090142901c1b0182c000c110031030600c14084c80f46104500c142c03050300806e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 530915395 1250 530914145 530914151
    0x6090d1d1003020c0d021e0c0904060b06070b15090108060114061c02030711010e010204030803060f01030f020d0903030b1c03080a2004061709070611150f07120507050d 74
    0x7080400c0c2e00070310620100b22214000d0f80034420309650003003a101d4140444050f00701c242402d03a08026181d40e06080720552160703464000c60041401940840c5181c20090002e40c83c1402c01d80f11200f040d00c08454508660742c03c06100e5a180c104401424010100000204820350420200042850f440c0107060b00030040441c03c04643c0d8400c16910410440c103100455903800d100d02d00610f44000141603120960a008102000380030520860b4200c6e500100d9003815a1641400c210050000b22001340c101511134286242d00a114401010100310310703400010865031524001e01a60714000810744264400031600c0c1d00003154007041e1700c000b50f061504002e2692a082c0d5507000307000d1480340502088800c000c404201035844c00034810760b1010788075215205000401c20300d01d40d07401c6510300c2254200036420094075018210840300c1074202425034004041900c0c250007541011118040100158001e0142080d04107040e40f0000f809120148100e2401e40070150080c410728082d5030509076 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 530916645 1250 530915395 530915419
    0x203090f1f0906020d17010303030b030f150108070f05090a090219060c0b0609070207050f0f04140f0112030f08040213020307020d090b0901140702010c05060906090d1d 74
    0x107034054095080e0321460882640071000e124008141da019805520054402c0741d1200b1117a41c011011801001d49400e0281816030035a0380c110090712215026607094030928401c8880c020301441140310080c91003001c0200ca42c9000c40c9107140102c10703806504400c0890b81d00388290384801e200c3c00c0d4003003060f1130082030008452000c01c5200341101c0300800700e002818004285198840403c002140c0607100310007040d2540c0c0200080769206881c0034025a0010300e04224078144284c14110004000f8403550307000003200c2c085419120007803040b59105043e2000c01112603511050301c0d000d00700402581c0002c801c16a00a844003038400c034010140b044c0100001c04560307408024014a1480007020764170ba081448019640d030b281c4000c42c0c0003180502c040458106601420303100e040e50140e4400c81d59401d08003e07120140d10541c002e9040000d084242400726104102080c06840360f07100401d074a00c0e007152030b80e0915810001d8a010028003c2031604400c3c52143d601031041d0040340c54690700d00d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 530917895 1250 530916645 530916649
    0x30809031920010f0e01110106050604030c090e0d0c1b15050a030608031c050912130f090203010b03070806032a13141303020f01110d0b0a0302010203090f 68
    0x10003680c03040e000d45924a20440410070308003080000c1d80b601c50111428030480c680107444000940a40000065030114004000c4d8410034030280180c0d44500001405916600807903030a60140c0c2054520900302d090030400300e81d6501c240d076030212601001c0c00210700740c07460041001c07aa400d03002e07240101030303441c0c80c60b11038005101100030500024505805003580c08041d00d42d40044600d036011030300e03110001035000c07c0071080319a0900380020048002d40d180b0300384c07802001c020300012401d1260b001c8580441c0c80341c0c001000510054054083c4192924040800540c07445c2c2019040c0760060004200d140161019640c0052450900400503130b200004680340c129a95180b000d200881d0301501001c582c0307061a2404100252045401d0a0503003583c0000da980458400e43c070003405500144822a582e8485031400340b091050701c10400142407402d0955494641c2d401d0f8004000038000c40d8000984184020b808040d25608600ca00e180c001035200d0141c1150300b07010b0400401203020076 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 530919145 1250 530917895 530917903
    0x210c0717040503070e1f0503060a0e0109080325140703211a040b0409050c15120c03070e030a0b06102a0203010b01020f0a080d020d051801111303080903 67
    0x9040c014048400b50307640e9200c0200101e2013500d0b01c5252030303001440c80986d8440035900c001a19005001440c1d9074070b0304200351004006c0701c0001c0c0404d558494202c8005542040194007681c10340c2d8101e00c85200201c1c00c90780803404c0200c45001c0c08548800309500b004100d040e5045150942065a8242141042d0a00c0c802181070b00052040c50700301403a868480340794200d031005600340c0d820481e418544042c4012148d20010180c8240c1c8050a04031030b9182601404043c448054940c45c2045980b9030742030110041504c0070b00d1601408010001420b07030008084409036000c400401c24000e9640740c0341040030016001901498004c60464034080c010001c2c16480c9901d800c2c403100544c042c1c885620220170b01d1804038440d50820517407150962000908501c1c090b1360001804e4900410b6903400c005a02c52041040300725001d02841003001101d1040c0d620401d5820f0348503c1100c001034200d801c54035140b40d1044c410405019440c0800703140e600702d106407644840030795552124040040d00e0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 530920395 1250 530919145 530919149
    0x102010b01020a0c1a370c02060f07051c030e120f0d110c07030b150d05030d05041a041b1707121a190f0b100c0c051005210c071704 58
    0x115111041d030301b41e402411240354140c074152a1500c0348200004084915810540002c1c0d4002e009004229401007910300500006106400b104d04419844020092447c0324042c100082940e658024010300340c24032031703428010086c8514518040c0c00402030314450013845064031009a6605007014592051804c031113200a00e00100c1d81d50382c0d520300d0301c0311403414200d900d20040714001701c00d9500750402503102c1c1c12581e8004080c506180d40344030300380010b0000800507a1801003a84540701ea604400d0140f9004e40d000340703040103012040c034001901050b0360760b011896201c10165a403242c0c890200d400020b072212041c0f4006824000c1c2060340312100d050416284409452080c040d00300038905031540b42d1808d0500a101c00400c032000c440803034040d62070507034108154a00600007a84140700c107441451064031041c96040c0c0701c1000c21000304070700035044003041002480001064601c0c202c1d80d40b4070503a441040051514080e414000d005134075000345071070068000840e035540901c041e140 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 530921645 1250 530920395 530920417
    0x61f0c050601180b03010b010507080a140d090b06180106030902030c04020426011503020402090103140c04051905030c01140d050906100b2b021e03060102010b01020a0c1a 75
    0x40d5503110b2882d030300f54a280b0b1940450303091911100c04601d00341801b03504070701c0c20141c45a81c10440d0fa6180c40807150310808005040000e0303004520400c0c4080400f41420015406001414511521b0000700225001d80b415124092291820310418040c80045040d1011858082000410380c80424600703441081a55400b078000300300441c1c8117400300d202e10100040140000c00d10076184030711600b20b83d072603200c0c585000920107040c4094101500140300543d01890001000e50100840c1c0c04820340c289d035462064440000d042040e490903201d41c003041c119003003242591510307007000241c2c0d40d0384180b09181031002c1c04c100308903040441c0c03041c0c8010b000e4a2506100f44e15043c1c8249445042c01c55010346125886640801d03000c448a003500c4013900c4c6000ca00c440b5041000380d0000005441c91a4040c0c607408100491595150766000108040580d800940760308041001a0035600030044d003d0440d40842c200707402040b10491110200d91400008800030342620250a80b20b10480e48401 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 530922895 1250 530921645 530921653
    0xf071b1202151c05190507140301030b070507060f060f0b040b04180b120c1504081b2701091808071719170a0501142101110403060c08061f0c05 63
    0x200605d010b4100d0032131119040040b82e84404081d01c0403001032904c44d050a07014401440041e40701407440c6c1d008012307401c085041c0a0707a0380c0c0c0d01301500d50540c0c410f080940c030751800700005000724401d00302501c02e050341d01c1d0520f81400e1846415000314483c0e040204013040414402d054103a01510b801c3c60090184442040350000c0607544d80c1000b190217010798800c80490700d207490300405035000d6401d848080e107a6030036111102c04600c1d10b0705400170750001a9080d1a112002205039049a100d8141903086503903240007440c004840340c1d02924002c1d640d0703043c1712000045907501100c502c0d641c410302003801502d14130794490b814000d5019500002c2040c1406c4081c00d90448a8052040305074030b070924460380c0b05c60200d01034410030310802c2c5060140b45200e402314504070318004c802d01e00300c00050303812071114004103080d00c200808800070300d140042c1c140b0901c0400c1c0035a000f2000603040088541c20900007007518a6281c80840045203255100b12039002d1240410807643c5400000712 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 530924145 1250 530922895 530922901
    0xc06091e0a170a050715080103031115101a0a0507080d0b06030a050a050703200d140a0510060e031b060d0f021306080f06010c0302030f071b1202151c05 67
    0x4150303075403c24803064909200d0028000707142c07a00241c14901780c0900d507582107016480c680e41a140a480352124494500401a640c50821150f1140d2445143c0c0301c20040c0500345800d030803107520510010a07001c1315000f0040744080a41000440f01800d910a603e16a5403141c01020343c01400c1da5600f0950003280007003071112000894000c0c1780200b00700e21042041b5140e50750240d00316001a0300582c1040052420a08411168006054413490315080401c9003004804c03c9029601c044070030a018594600520504070501d00c290000b5080390708144510f5621907002039035403100c2001003071850300c0c000f007000440c0c1c0780c4400752144850100300078011074110001001c083c0d00007051401c05052034040000c0c055200b81111409404648210f401c80c1e11201c00441f90844401400c0c2c003503105c1040071a40404281000b465a140030b071003e52030100140c28084a0600141d12090541e03200b00456405030391640c00825496211514055440ca003c404510040d40a02c070a070048504c1c2c5020 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 530925395 1250 530924145 530924189
    0x602030106030c0c120305060f1306060f0f050d181a012907140a1a09101109040902010207080a08030a061d0406021621020c06091e0a 59
    0x6503060326216101400301c100c010b94200d943d00b0b5844005418010a01e4126004a000c0d0340080e404c420041c04030443c5860820108081d501085c502202c419560a010021254404602c510060403458005d001c0b03040000010100c2c040d0940040650355282c144c480080710100f14603020b00e61180d0360b20700543c040d100c40ca071103403007d00c602c2d000b080941c09503207088604e0a1807054074042840c04c0504218103034417014000310345006605642d101c1c44003c4000300d0021070101c07910310004030b07050025140c8084243e080220010601140a00302aa030b15085c08418041d19542e0100303a40001e14180b42d400101d10340141a0b00100e41401450134000522001e036000310721a60110409111140d43e4803208400f09841480000060601d100441e0004203150020100d4203541941e0b600c14210a4403800381c003c28404080d8000d601c510040c40d001da405101e0080005011900781d4105915403021a210501e00c01024078441d0000511110760380d102c0540c2c001a20796000700300101070034440 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 530926645 1250 530925395 530925397
    0x30302090108090120180319051501050f060307030f1803031a090613060e010b030402030d030905060c0708040803160209010f050d02060f0c0f010f0b090f01031205040308070602 78
    0x20351035000400d803030000380301e12505000e00c0c100341440c4400e14000800042c801c08040c0c00a203294046c01600c03500fa0071300c0b83d804001c405101d0250060542c0c480441c1c2c900103240011142031107070200d40703082c01008141c0e6406001d0801003020b0b40c03155501e5032140c0c0110001c00f1149111281c2c10701e0b080d50300000c001c4680f51060224401d8801b0000780405c0007000c550002080c00a691000402d00003600301d01302800001500494500b002c10050f49480c0300c4100c0306426003000702080e00100c100001e40c901040803141c1065603050401c102c80040d102c0c141c907100c0040c6420425040060083c04112040c0103d90081c1900001c1c2c07a00c03510307403522100c144011804264840e028000020a01c400d1400d8240700701d6000810708492001360780d0130b0042d513400600740c00c40348074428400f011082d101441034a1051008000001e558603510742d15801300d400e603240c00c5019030140402c0198010400c0261f60569130049205208080d481c00101d40300d10803030b04000c2c035a0350085080d0b02040502d030 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 530927895 1250 530926645 530926657
    0xf0f0606022b03020912070e0f130f02060a09080f0d11070602060a180209040b09010507020106030201080c030a111b1018030e030c1e2404170a0f030302 67
    0x75003980e51841c0c50103408030700e00489010b20142d92180c01c4608208501030350041860440142c110b4150300e480c05605800d201d032940c009680c3c10a4181003000900c8241e00d40b1381c0c00055500345441101d0349440746051500c140c88000e004240000e554071040d8018000440105400400c03511841350a407122522034550026010125007500c3c00006030a9000c60036005541c0b07540d000340b81c140d444241005c090b0405200c103152181c2552124000341e151055050b20503405181041900c1c204191100c2c21514020302c0e150440e45001130500040c0e0748a91441d410505c83c80d1740b2501d94940f452548010242c0c3d00c80480c00c8440021205028041c5c0b1080700401e900c4502554522440b0b40040405c1d1124005d285070524083ca6008000a0160300780758003600000d01140c0000e010354010608440420091405508040c100d5814a00d010301140804c1076072860400282c050041c811601130049006650001d00d400c3e40d007962042c000c1002c1c551407900302c04c0400c00e0344c105080c090000d40c000 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 530929145 1250 530927895 530927897
    0x10c150204081f051e04170a020a02102c03032a01140601140304140f0c0a080a02010c0b0705090301020f09120f101d012301240c060f0f0606 62
    0xf03100450b10b040280f2079288200580e20074085e1400400c0d8460154000040c0101d900d820b0103e03015a10007c0c0c1b074003a00c240340c5182c0042c5101c1c0f44d075004002c0e01c040303a4038060041203a02c0b600f00e00d94411801c8541c0400030903232043c2d0080c10800c40040d00f90701644080c94041c60100b010014186455a6000000c000340e00080011101754135480441d01d4007110003034080f41c20942070215440d00340c4021541300c0d0040c95078440e00b05003502ca50b030a10038001800011603001c0d698039281403801d4940007000700140d0703009144510441c2d00203020090f00c400058108030280b03000034030302d0b0301800486401c000010f00841d034944088200e404d0f2904201c01c424010300e0007543c840728030403002a120201d11076800040000011170314207d000380c41c202600c001d100311555003d00e0a42c00c01d01585403500405041a1020700c40c1094003820703a00e050303110310340740d200b0414502c2e00307614054ac10002d110f01510b440301440b80030303081071000b9040b5000401c4400785072010b548502d02241d1b010005030b500c2 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 530930395 1250 530929145 530929183
    0xc0b07060b0a0e01140112020c06090d0336020d06020d15050d050a150e070308030103050c01020a0305120709170c040c0c02130903020a0203030c0313051e010c15020408 74
    0x7550050f0f80106400d02841042c80114840c542e02903008506555a54000c0d400241ca40f2240c0c140d0541849419502d0118690054241e030403070035018018406080103441f401c140041d5261010040b40e041c0070310b4003140c2000200c230b40307095440b04011b8510361604100103643d5041d0070702c1504014042c840b04003280c51003424004c80c0a103018440a130741c0e1604000203190042903611008c404044104003125107075a5510b200080070340a111401c0110301640e1500c6d169850360800a0402003501c005604540110400d140003e40110035520500840c80c0c840005547e0b01d036054138029840e400034000000681465175641c84000341d80084d0078401c0d1800d00030349070380840544402d944203200940c040382c0c0c103810b140400f02a41c0304078041070103441141c0103420f1030740220703085500c03004440c242c5402c0062018902c03182110f850006003416210030703000003100f40c2c0c0102064614030034641088801c00030401800840c1e44451200003100c10210341c1c40f0350301c50880e507071220440e0a4401c4214 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 530931645 1250 530930395 530930399
    0xa02040c090e04022b06090212010c120504030516060b1306060504050d0503090d050303011d01050d2a0b0a0909060302030d0819020403060902090a05220c0b07060b0a 73
    0x11003408501e0845a000c0380072409521264200042d42e5a03038480f0688007009000801c507200c0300c4414050001307019000009040003203005000b1055480300400415a042001411071650300141400b103c0702c0841c00042c840e140e5240440da1841060624003c0070f4100840a0604c03000341d21420150208039480090410001001d0b015194070f4843c8002007141030000b0011420001e840310081881130003aa46840d10740700001300380707010082c0300361403581c0040010303c0418000d0742c0790240415440f02c081595850680000c0ba10b02c0d441074000d10049012082d03083c0380c40c070455114a8400780d558060403140d00c684107016290000c020a03000958402000507140713400b413280b00150398020b4098503102555503415980c01f10060143c029282525818028221862000d04051841448007040c0070843d801008012070000c0c02d810842071400b010700c000c1515140e41005100d20454842c64007921504000c580e11400c0e5004001d0114005034100400095034000c54054004585014220b9 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 530932895 1250 530931645 530931647
    0x161a040c1503110406111002040e0f0c0c0a140a1403190c050703030f021f14060612010e0603030408061006110d020303010b130815040506150d0b060a08030c0a02040c 73
    0x6007055100c40f810081c00c10051000310320604001c0440b02e440d8045400050a4007205000c0368041c0c6d001c0e01005c0c1da030100b0300580540346c61003260000345001440703080140342294984c03103103401c10009022402c0064460a0540c00f40076640c0d03081e8000d000d6610342c00e04440da10b6100d9012001c61000500c000400c07910490084507040c98040d0084002c1c01c856081d039a0a4513003079010310080d020740c400c240c100d0f0415082142c03145000d071038141e400700e00d10180c0c1841000441d0701034025031003100248541c0c0d90349540007a07401d044174400c0f2001c102c981c541c000440d066100b00d130852915400382c4010848d80800c07810507401210804e60315504000005950f082d01d52a0002d12500140c0040004025034144c8802421071800503403050071040d55104100d40c54901502544020025207108103c2806014000c842d441420207020f01810aa4400020642c50541c0c0006090402c01808181c0300d13110720303580b0b0300909070070320072a5620060202d020307949109805040344641e042070001840a = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 530934145 1250 530932895 530932901
    0xd050603060702150a05040317150312041d07090512070519060c03050a20100f0b031018020301050f1f030b06010f020a06150f05060a05161a040c1503 66
    0x601050701303040c203180c9690103c900500006001942001402c5003161080300740c0b800e0b4107000c1c0d5003001d44c80425041020602d410229810740c000c000c0e085c10f100401c240c0c00e000b4180f901030003915006048660b522481607418181e650801a00000340b051066840000001c541041c3c8908444a0302407090f40041c04692140b54020000000c00800601c8002409000604450300607070910703c0c00702c188182d8002010024100c5460f19503c8004641c18082c0c0c140719801c40c0e0704519005210801209003c42e6480c080c2c2040c90103010b54500c1c051420f80700d082e10007652654014001c0c000c2d810305107090240c1501c1659003c40d4030466548031642c0f035050f60003003001c40741e0105400495655810054031341411000361001036004520031840010802e204084084d101604c4600c426030030b00080d070890101c2d68110030b01901c0f0070400354181640080076641668020603000741825601e1034180d1544202c02c00c005020400e0900f071108210812552600341c07030001d00350f0350041c441d0034811025 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 530935251 1106 530934145 530934163
    0xb16050f0a080a0f020604021e1305040b01050108010b0307080114120d0207080d050403050309040b0d050106030309091107020a051201060308040e04050706051e09150d050603060702 80
    0xa0751341104008101c000584003c00e000e2030107a010078611143c3c0d6454280048100b4065401583d0351202d0308210740304503d0030300450400d403a113051040350030700803030340440c5c149030022607450010805d89100b92034035940c03072081c5d034a481007042d946649502c00c40c0c4c2040c41443c181075200c00811400c40084240d0303006000c241d00d040002818501402150420040200000c001040c4000241d9142c0c42c802c036800210941c0c10350000740c0c2407504040007411542000310000601d6002201c080c22525041c80901150108100d5240c0606c02c868000790301c03040841d130601c49420a400c44c1d82d4140000c4000182d40d03500c981300c1080ca5005a4400030000701d00004100c01c0290501100c1c0003840c803410014103003000018a5090402c2110000740420760118004403c3d50341d00780540c5103030380b090340307074a54800410f014a8081c0c03100310f41450191040e4404a01050b20024941203 = true := by decide +kernel

theorem cover : BRFrame.Cov 530755395 530935251 := by
  have h0 := BRFrame.cov_init 530755395
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530755395 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 530755395 ≤ n) (h2 : n < 530935251) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
