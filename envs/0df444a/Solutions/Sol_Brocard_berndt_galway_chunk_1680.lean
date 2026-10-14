-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1680
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:11:59.535045+00:00
-- url     : https://prove2.me/submissions/657095bb-66b5-4edd-a5a5-4ea43f3c6394

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 301978417 ≤ n < 302158273 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 301979667 1250 301978417 301978451
    0x4050a060f0207050c0f1f051303050a03020d0e0d020d05030d0f1b050712051c020403030905041406030c010807110f0a030818030301030f020d1b090c05040315 70
    0x5850381101040c000381c5111040c1e00001d40c00403000301c602c0d2003215081d81c424144944c030f4044002006010b0005503070400342c04220b19802c031a03020100030341007041c2e612280c0001d41d10006540200001d00307001100d8500645010599400035040c480c0e070030309070301c1d0f02e5503a244001c402503419202d001e60110315281c4075103140501c0e103201c1081405e141c2402d6801c05d19500104e040030707000b40c405071190781c3c544c0305640521500c48040c0c40180000c089480c00b40c0900c004007025044600c14510144259944008907005034104a000031058402080303a860070b070007400050b103404105001b403801c04400080c0d440c14003c0000d03050010031400250f203580248035150780c0703d11b8201550440c0d191800b100ba2150019402100410140d8001c2038196400380b02a65400c080a001076103036074216110080743c0161800103c1c0d2180c00c4071016000503080000c4883e1010261401c2c078a801c2c18020030000740c88c055213204041010500c01040030404020005031420921500041c1c0000c1090388204 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 301980917 1250 301979667 301979683
    0x903012a0e0303040b070602180603040501090b010b0a0e0405091f0213050a060e091f08011b020d02060c280f1202031b030a06051c03030e12071b090c0e01020c060310030b0405 77
    0x5404ac1003c0104014040c041d044600c0c0326101e5048510181c0e02c0300048006c074011403800e07078001020107602d0b10950500b07a1255070002d41384e40031104102c11000b071002114611401d43e10046402044848040010203610006010100d8000303042c2421b26000034210303100e245156115092000115804030643e1524007118031400304150013440d29054030f24040d0502c0745160a4582d01e43d590304107000d01c045290a84502c0c1d507030241030039440e036852a038640d410030082e040b592141075540d54000111043c1d020000c02c00d54858082003400d01e900a40049003404590b10681e004100304488124020408030312003d50001e000d84030b803078000c82c9200400c80d40d0005904802c0d60003540c16042441c0103081540d034802c2c1e506101e1440c01c000106d881c0c2072210021159003005210110006100c5440d0300d040d11040d040e0900e55070760752100c401c240c0c2c04240005002c0390250181d42c019503414070841d149424141c501502d9420f10302d040030311f00c24503484041c0000180c0008507003001410b000d02c41c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 301982167 1250 301980917 301980919
    0x2071a090d050304230406030803010e1e2d0103080a0c1104050f01030209130312110903011418010e030901030902012304050f030a02090a020903012a0e0303040b07060218 75
    0x3030f04d1301d40b284a80d42034002041c400041d500c1c414a110826442d05015030010380c3e40c1b1070541800e42c1d1034018030b2103441c180a02500407002c202200202e40b0441e40036264465006015a4000118a0306e0fa1601d102c3d04520f100310001c41090051000c00c05440450300e65944600c1c1040c045030403400c4c54641044010000740d40681410103001141301e0f5400c19a05882c001c0f2920202c075281c5140011040c0703649003004021070a900c9204100400c0c0394842c00003243c104141030314010041c00081c2c21607002d0a41d50449148020600c007200c2900000c02c004010301800800441d80d584d01095624041c01101c0c50405844440302c000f1a40b103410202c0039554003681c60785100042030072001060300940101801000740001000480c03400040325880306801409106107500e49030317812400703513211a014a1f050b41d21008036060a01d038899510038550140306801c0c1c41d04421100052040b2205402c00d442a072050000b80800310300001142d4820340c2c0000016550182c0300213228401d0a05440a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 301983417 1250 301982167 301982173
    0x1a04050909010501051504060e010e040209040e0109060506060c0c06092106061e1c020301061502060a0c08062112030c0a0212031005090a0b041e0c02071a090d05 71
    0x80050007005421144c145c0380e0031a0410845824504011403500a0348600170008003440c8250209501802429504002c0684003503e010040307400b080c1519560400286503079500c1c1148410f101c8036100b02908104122074061400700f8540d200e90741e9819009079544128800540c20149075100486c0c0d907022444480b40078640861240e4250300e40000710345550041c8031024100e101d40015040c0c54024030002422003d020040c03a1070454000c81040b001c80e0551350342c21000c00c24080e000300610380b180385a03005100616004040d14281c4600100c554140190312060000d42c2da02c80401d0602c403407a002e500c2007000380c04400e9914005603e0030440c0103038000000d0104e0440c14400800e0800e07100c0e002ca03411211029080541488100c903101203000451030b003030010f843c160002e40d0300070400c020040781003050500043c00f1541c29500350b04010610008044603031142c1d008419a5103007900141c45481d18060050071b0b40d1013880b0701000000790000d4010020341c4e0301898400055088421 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 301984667 1250 301983417 301983421
    0x3020c0f010507020a12022802010c0b0a09031707020303011703040e040b06040c080907060507060609060e0103021903030f12140702010203010f08070b0702062a030702040609151a040509 82
    0xf0194460820a43c11b40b0040300d5000c03940030711400080c00758150410400004141881c0448002523040c0c040c80882c1000f0458440e00007142c2c14000040c00380e0f10790b500c001240d02907480d010b40a00804018101400702c94020000c03a01d801100390380c110740c032140200320f141d612500c0c41801e40c03065030041c00004510105100038031516108152240d0805d0f1410800d680d1036060031b5a040c40704844a03d8180c3c00100244000780c0f0510103001c0d0755100310000308459403284d4481040d107085820002007840e05000410035490405424688100c0c0344214040007411601c0c001c00b14256800c05005108070384841001501190303005102d8540d010142d003d060425200081c040c0d0f000307106d000c3d03070681b24001c046582e0601180410440700041c25413450643c0a500b4009142c00c000a000c43e80c000000d2080707102c004000a16000789141c0002d140d583c880e0b8410001104c0316900540b117004d18104c0909841180c0105103826503005281154100400c444046081d20507074104070303041420801 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 301985917 1250 301984667 301984681
    0x90b04120c122006060a0302060d0f020c0a06110f03010e0c07140a05010c020706020a02091b03150a0f0e06040f0e011107050c100507060e0a02060c0f0d0e03030403020103020c0f0105 80
    0x180f00700e02c10807020315240300318040c5103042e560740e81c1940c65903404810b040c002c100501d0039000401108494100c00b15030070208002d024120381000c101208590807000e100300822500d4032401610107402c100050824000089a006030b002c14040c2c2458202c4003c0440c5039180004150b4881c10340c01030403104240386407004180c4500440318215255800d04850402541c0081000016103186500500301a03030b981d0200040d440c4050100d14041102e01c1c1541120105a0015031180010301c40703440d0340d12001d20a00c5454009a4840702421408400500120325204090381c1c120404a5011503a0500800a40014411076900d88820f41c44c1103050500156140003900583d03001d0f5050712a05840709040c068000c05590545001400400c4060005907250340001c40b0803484000b150141ca90550108080764000c40e02e1407180e40c420807501d8185003041000c201c4079462403509031070900440010a0752400703140802410305402142860303002c042006100e14101c0500000d01113030034619 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 301987167 1250 301985917 301985927
    0xc080406180503060c0a0c110901060207080f12032d07030e011116030807030e19150c051b030904110405031e0c091503010515011101090b04120c12 65
    0x1018240c824007618000401d4034000c84c50500c180e2800c140c581ca000d062880856031720014200c1221001500e1070314490075110880300c98040c0c0301ca50018803140c0d003040d40440c035007215180760a0180c1e1003101603011504401040d00d40204845000e180c07a001040b04031080071a090703e5404c04400340304108150203515400c01a40d40c03040320020003440ca5454000f8105209109070400c04030a41000103000910031228a50301100616000510001001480c0d0a0280040021558095003040302e0107000c25010000500c1c0f008107402c001172200070724042c1483c003411b0b006562049009030710140300502481141d030480c000401c00c1000b50741c0d001040c0c2090b0024050903000b481210094040c002c040c239205108040341c3d03001004184000c1d020007100540051018184101d0071710541400e440900407075014540d10200c005440382d64800042400c0c0400c501c0140c3d580c103000006000c5094080010340240c0c0241c010400d5502d0048291800c0f041e00d40000d01c5090b90881d64403a2503441 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 301988417 1250 301987167 301987187
    0x32d01050c04060906050903060708090a05060403021605011b0b1b0309010c020706080c070b0703060918021f05121008030a12050c04080c09180109030306030506090d05040e06010c080406 82
    0x42d203a4160417500c0f550122400d00038201500d805600460202c0d0b0740c24041c946aa03403001d002811180041c105548071400d1450a82e82107001d0b03030002000d001500251414140503090a181c0703e004480208502030000400c080c02a12071461400880e1010302840545400d60b103070720303e1007a5281003240321b1600a00308000c01600600815030003052052248080500800324500c03075606003842612003c60081e40a41642d062564446001a10b90030901680c41420b0001142c404800a00d00600406d02c40c00d41c2820031100c4011414460346030001c1c02d44e01d500090204507510365540007182e065030a03d907004011148008500c4011707943d400a40160459a0590305101d90388810900200d503015501858030243c0140541c40024104a41712035070002c0d41d540400801021940403038212400c00a0940010351515018000c0c01002c005e04c40d0030114110082c080ba5042c41c600074128000c9008035545003c085000c122030380e200307495080c940c1740c005400d0b0759160744d00e28000e0003036201 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 301989667 1250 301988417 301988429
    0xe01061e0509090c03121804060303080a0e01061a090a03080f070c230402070629040506030a0b1602100525030605090601030908070605180f010209032d01050c04 71
    0x2040003e200ea500495080041e910290003807900b20206d051007002e50b00f003101c09080740d000940300d1072150f541c0d90203400019400307602c0b841041c1c10841c1504080c1c5044100c2c0b5407041e0304102c410007901c0d01208050030703c8810101c00c4ca456180032000513281044550014100c07000204910a05400040003450000e01c01d075180d4062aa0764200d090641e0034a00b840d000b102000c4000c5005400e04c1d80042140c82e21844001481417210b8054480320484513074065690b42d80340c0f0300e9000d2401c240c442d00780c0280c02200140301001890b9900200d0354801040e004c403e4603a20f003a000154020441503c0e18000c0400c00d002c01d2920310500011500c00b903070a80e0310348050a07400400740380240300344c10035240040c044201c541d40340001900507081308003048880107400c0102202003251072041d980a03030410b00414503100342c1e100e411450001d0000010035181d01c100321468569130001920090300050806050100000d00c10b001005602ca802d680c1503942003104004491700303c1c40007401030380ca03 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 301990917 1250 301989667 301989679
    0xc1002090a0f05060d05040302010e0d02070501020d180302041107050d050304061413060222091a1206070f050c03160302210f030907030c06121a01080601030e01061e05 74
    0x40d59100107a5042c10a202d1560031410030010914001550703007180e68440c1c000c4c000400c40e0110f0310b4076a8a0038002550020042c1c1202e40140015a4103001a455045182c50a04d2000c4449400210403c0051100a2089039280680e0410904a0040d01c21796a00f003400e0703c03401d41c4a2400940f00ba0f10444003207134503516280020f000140ba01008038021183c00c0706174180046242d4443c0000d5002407181103040e050f041c44080700306406d040600160220120100c1e4004d07500c3c1c9000d40341084c08031018443c0b0415036616000e040009109507100100d403802c3c91100c08038980655140c419013500d08810700001414000013480007101c4d4058601c42d0b401c44081410105a02480c08040c01c807210103040c04005140020040e8005180c102e0014819605407036035075075070465a20b40c1c1d030b03008902241005680001d02900c0d8824110010f0600b10f40914103000c8034002440600000c10403030506645000c884060202580038002811465000a022151071750b8078880482840c414175100308 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 301992167 1250 301990917 301990919
    0x307030923190201231c0501050618010302070f080712050f07030e030304120302060f0a09171606020307030b04180515071206090e0f0703020306060607080c1002090a 73
    0x107141500400310804620007a00c00c410312000b440c900e80307850060913410016600044a151200504082495080d40c0130069403900e07074003400c3d9000c0301c0ea118001c03a414508001005242c80b8003044a038044041034500da1080340050059000340907801016004139003c0043ca030402035064000c060107805800f260014883e000011030b00b52289000120403440d040c844140000c2c0950f89042c0700c06402010b80313040a031200381d01000c6141d4118190016403106050003c107126420f03901e9003004c85010b050140c05070b180c452202c05200d400310b00441c01c2000500c2d050100c0711500c040b91040e40508199540c2c1081c00008000c0d203000307610544990320b0050914181240003400900c8258450b0290005182105203600401310050064050114002080285840911611011300400e46002030103070800e0f04280d1804000c03410000c6c040c0c6c030405040c030242c0e40010b01103600c4482110390b642e8401c90740c030b0101410b00900000310302c1c5100740c81e5401d503031340050f401030700030a407081d58060b44032 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 301993417 1250 301992167 301992203
    0x3161b1706100321091d22050d08091006090209040605060412261615022b0b030105010f1a0304200612250e1c110603070309 55
    0x5005880020318084032820759210207100030010300841c004d14245003c0341942c80c428141c00c0405954034010034044401004515096188402d69803200503100e4007030304c9555a40e00c0d5503500c04c81c1554051098500005480f001c1c104a00c00d0307000c500000900040c2d6480b200c41e000303504220702c01446641449000300d21030420034240e07011190600c40e84c031100c20003034030380d03a090381c802e218988601020242c0407003604820000034604c450350607c101c001e0070034500702146041950030325403c2d020700400141c50500f80300e101280c1c40b02000001d84200d08060165140201180c01d8002c1d05542008000030303481a20a0740101158a05581404a0700840591412500c021100101441c1c80903074151038410603401c030b40340c40709400f0740349a01e0204c0081480500b501c0803501351203000c01d01c000b07844020501503194268400c003400e04100704003540001802c500e0030381c82188283c5540c1d500c00414003d0009d02c0c2c40d00820045c160699a082c1440c00602414000d00c090710030040c40f042903039023 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 301994667 1250 301993417 301993441
    0x804111201062103390b07080a29061b16050319110d020904080307020c040204050a060c15020c0609161203031e02040909020307050f010203161b1706 66
    0x42c0341e00d507441100072502c40c035185017444a10000001e188a40800e00d18036614045100c04201d8054589410185000d00c0d0003001010010450011141090403e205445030842d032101025400164105554410008038907507000e06681044544201036501c07403c01004600c41681048040414490980f160b0605580300c404030384044850003204180b07000700d03100180101080900130103580107c485a00042c116000c1583c05171000807000040c007042ea42c042000300c1d003815040e0340c1541000d281100060400c0b034a231103050140100781a080007001a84800080c461015030300c11503ca002a905c0d8541d82e000407921100c1c00c4c8649203682c40400b0b14404c40c2e20032940100d582003150f00560754100d01504009505404910010b00d000a40502c54000780025100d100e40c0001c801219004141c03a0506079405540280880070745d94280742d90100854022042881400e00d490640f0300e0700380142c0c092194521428840d030440482c00c8050804e69249054400d030440c0e402e070702e441c010108 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 301995917 1250 301994667 301994729
    0x110f0406030b0f091603020405150a030c0815010c06020f0a0e0909060415020a050c010606020c1806030a110a030b0403180b0a0905040b04090215070507061b03080411120106 76
    0x60b100c50814000384c03103403d0b05885e4480100b0645005801d060f6160003043c00c582e42c7c0e203060600c0c001c0105984500a82c5446181e0503003401d490b142d480317418500d0141084c0700c015a01d25040081112050042c002142c0480d842c8c841543c0302a5500c00c20342c200240402c4161100034850300904002c1440b0724400146d0500440d0003004003140c03804a08031006c000c1d1322002e50482030180a0020110901080c45540024034150700a040c0800012081200f44800c3c0a03158859456140c140111610001110440d1641c0450041c103810b116000141d03019241e6030009206c43c0e54641000308040c2c0c01000148041186611525820b84804540c01e0b1400744100403000201d803864208090320f041d402840410502500c00160b41d0300540229080b0b005805c0340d00b461070ba001850300c00304141003291400074a028504050030612001298411501030100501000f85001c049000d010b048440c07a8100302d00182141000f01d0142c6c102400b03030009100f94102d410041008500d904075003c1940 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 301997167 1250 301995917 301995919
    0xe0610020601060f0e0d03110c040c0516080403050a061e02040302032508010f0b030d0806090a0522030e0a05010e030d1805060a091403070506090f04110f0406030b0f 73
    0x108490f0b080140031a16545540382c1641008511074081c90325031200f4844409842c003a54500300007500a000540c540000c40d41d6190203240f0f08010f500d040d680c010151401c0b0744011062482c201c0d41814403212a00070381d00003800740d00420b072060701003204035404a188022052481c00305002590ba0100403030050b44400381d01138024004845c198907071241e10100055460030101c501030740303904d40300d42150070103101c81001c0d0780d5588001d0182e15040195280c452004c0c034083e0010f140c0040845c00c020304c003a101d13030300064a9002081d060021115140c0b2210441d02211064403803038240103105288003944d05000314850140825130b544a2801a912120040c00801c410550074104a54201d4140c5840c1d41c41c60007801e01003195078502c0001c1c111a642c0b50303070b02c26007641444800604848100304c040d00c45c0d480036604020f66140c04003950070700203084401103c803010180104002d03100692000c103403090005941d0b100d0103c0100544203842e5241e904108540820050080c030303040c035075945 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 301998417 1250 301997167 301997173
    0xb03101e09050105090c090609010333121e060e0303040804180501051c080d0e03040612020a0804080919030606080d0507050a0f1b081c020307020d080d02120901060e061002 76
    0x47c25541828402059040700602d0700142c0c44081e052100c002e250000b09144035400130741481054406c540c0700c00303005404071226040ca0040c15680d50b1040154442c00c0e880d1011401402000307101d03107548180007404a82e0b055a82d00c0c506031500c142d05034010300405290ba24644101a90040140700302416550080d06540d500b00624040c8210442030540c1119102010002140346c0101401103001420030400110f0310795061443c050414821811883c410500c140060160706a010004540060b0084a03150380c0342400c00104107042030252a007441407100020000030000300d0341c00030f406ca8220343c0035103a510405203012180d5108941c0c014103079034807512101d00824040d008000a0714420180e500034000c070a80c2e0120905020740c01644282c01414111241002c803c4100052200740d1011358a40401c0d40c1c00154000307a600c00c06850404003248851000445504450008020b01c40621061a00c80e80442c0a070000e4021700c0e2042100c0004101c0c80c1c20f050f4280c2c0c008440c19005 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 301999667 1250 301998417 301998427
    0xe0604030509040b120c090c0310031104090803070c0302010c0903020d0209060a0e040f0c060819091104020f0d06061701090902010e130c030507050f040b03101e09050105090c 77
    0xc4032140c020701a4103034019030781c500d03442d0145d070b50400c050000c02982020300729081842c01000400d090080020500500800801925200f00312030001070780d600c42c803283e03401c510070b40100c3c005200f0910010500c44e030000a00000da034111f0900e0302d10300d200b90300a0114402103482283d40000c28800250002a40440d0030018641524229032215018010242d060b030b54501148c1014019501510b900600c0508001403200fa5210400680310504140160b41040e0601401a040d001101e010007550b51901c2410800c0e1801031a0344100028401d5440c0c0800043d108c0f501c2e4000c80000f14051718020001403054029040955107200500f0940440c3c1e203000e211101811a6074030407410004504802040c60703541015514140c0c50580000821102800340542292000382c154014041c0500442916020340b0007200d017520500619592245c0f28900e0715003440d14250085550b685180d0748407207020060242007012141e801c4401e2100c4d90780c9000740038480405076000c582441003041 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 302000917 1250 301999667 301999673
    0x60a0b0d020d020705030f03100e0412050903070302090c090405010e070c0f03020c04020d1d070503030306100318030c0309060305150f1908070807090b130903170702150a0e0604 78
    0x201078100c20850b1600549070400a41e41d03e8195400786850a42e022804003e014907080c41a0480014221060010200341001c1c0c5882034030480b8001c4a030300300240002c1084a9071001e002402c01142d010303107908042c3c200045200c1890304082409400742e4603202c00010749603a40c5180340d01408598407551040c04160b240c0b10100c22003030f00181c0c150b100e03151856005450381c0c40101540c8903d4080020030311140c040180400085100c1d64940e984501c50501c420358004c401c4a410070012103c0045444100304198080c084410740b0440b500000c1203c1401e060704088041000c610903915282c000da01c0344c5003070782203031015625840d600100300710b0041d13142450400c0c5881010f00816450010b41e155903440c0a50420f6045a501500081420000000f080261001400c01c0b00824004041d202c004a8a80203031036040100c0341d07450390f0220301850b010b068003540c91040b1043e103100900d0101c074041c3d585d02c44201d82007030300064000021031000546c81010142c0794000060425611151 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 302002167 1250 302000917 302000921
    0xd02030306180405030408030a050a0e0d1205210c21070c0204021c0903030c0e04090b13020d120203090a350709090b0105040b0d0b01061d0d0f0506060a0b0d 69
    0xe001311030b548020032011440c042d080014111901341680d035503680e42c0c0004802013080d04c4260389036014060024503100010b84145041c1602c003110b142c03150b2583c1f0742c00140c840c0aa9000c40d8a088805018184421084290014000d510f1110900d07040380303044007540c007400f400440b60200001d06060b8881c00500e01030700100310a61044400c0044800f010740742c4000c403200204e0031400300f681d498205840c2900407a021135000310446041007500c4081c0c5540080c1c060007050f800454036401c018400f19581ca0038006803060304029a02c1580000c21006552944030003074281c412003203860000340038011011408100c4558000050720b5020780d0611602c0b4505030114071405002c3d01740c0c0402d44100302d1041b82c444a0180790003d03841d500d40400c1c8021034440c0c49405005881e10361001011840500015045078007074070b4180403041c80c81c01d208002c48005c642a03980705081610801c00e102c8460f050b420740a009206840c010340354207040028055140c843c200c407a01c41488581d800710300036 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 302003417 1250 302002167 302002171
    0x3080409022208101a010c02060c15190e07230a0806090d1706010e011d04050f07030c1812020102100905030a090906230103020c0a050f0d0203030618 66
    0x6510807480703280d201e0303034401d010b241d1030381040c65240e00c00c42e025400e2002900030841c06410051911031809505400281107500d40703200640a2030000584000072141045072440b5284201043e408d1401c191610701e0790068500c8800c10540c0c03c001c284408000049401e40c1251007a40704c0c440082c00d446006c46683c50240702d00d82c9d11181d00c2e0000a0382034400e00066206082c8a0003a007602400b10f24054895604405180c40100c443c1c0200001a604500f08040c030800c01d003400c04070030705002040050741c0c031480c0f60190860300b444144504003150b992841e0041d407031510300b0720182d411010125444200044089280007401c9420851351810b005801c51040c01031040d500b0080d5082000f1090f41e0032440c046034190300005406044507804040c0b4005030041003000d010b44c5142148031031030a080540c05424030b0071041c80507465a0301a40c12551558004401e968124100b410129295440d0402001d40c03405080541020544040304503449030000070308100740a802028a10a00200 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 302004667 1250 302003417 302003437
    0x810051e01081c03090f0201080c0c030c0703030816080412020304080604110a0b030903030a05070c14011514030a0807050c0d0b070e0d0b0f07120e0717070308040902 73
    0x5800581480002080320007406400158010103221422584200c1c40c08000900c0404040c07402d1990ba000541180240e001c00b0380901c4e1000d03041e117032102d6420407440b03134400c100c884e0711002405070001c010114154045074026121211290f980c042c0701002040241030410000b600f0030f000030b0008503421049000c580261040302e090030307220080903103440340507101500c524015489510ba2481c009542c60003501c0d0011300b182c1581084006a5600d0001814240d502501d03030002032034152183c501c0303246150304206d6101c030f002e60b0f040300c0c9402021082041e8507a0401c000c8040707040140c080c0d0082c030459001d4020031343c021543c3c07a400140c1d00110402c0f07603240030b0401800c915a46019000d0031945c0540150500c608011038054001c0c020300030310070702503e107410110300404c680202c919407003203c800c0340031001c1da074020048a2a482888031064074924003202140e0f14000091903005a460904503c407001100301203195488400388401080c0e01c3c0100401e015076000d41d00527000c900f43e = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 302005917 1250 302004667 302004691
    0x8070608161d0d06060302090c0a1b1b03030503090f0f0a03030f1404120201051f0302010309020d05010e01140a0908190c170903010507230f0705010c0207080f07081005 74
    0x1081c8400510950420f05040d00d907507882d00800e206614140320b03425008040c41132800e19017152800040c0c40244140010514210060060024440c81040c0c50481c2e000702d400c41460030f5100e01c3d01811070341054402103c10310540407a0344c540344000822010f400c02910042c60f000c10f10303a50031805000003c1c0c28148050b19103200052000366104828007540c896900064010b407250002400c5407401420700c1d10107080b0081501801d0640c4100c5410340ba0203181c0418501800d0003c83c0340c50000050041c0f00c6d40c645404040b6180040d8010010b02c1400c8a00c08059140c5401d80380603500100406000c0e410100410581c0d005003003499154080c4508215020705910307200c10341c0302500740486041d400c03000502c503c90742c0307020f115165102e210340c01c2000440c05900b0544030030481c1081c01e054504400502d07400f0400404050f9a03850364003100078084c2510070030b4025103540c5544070b440c0051141d48800803050402142000c02c1c0c4180f5802415100c030086045d0000e007002414410b807200c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 302007167 1250 302005917 302005967
    0x12070b04090c2c2106092a0f040e0a0203121e040e0c0a0c06020706060311010c11220608071a0a05160206040b0a030b0901090207020a050d0501060503160807060816 72
    0x4d4820f03c43e0034070594043c405859004410360303002d078014081e42006800b84038040c030a80244e649414102d0150300d0291000034440c2807090400e1724014078000069403501c2091001442c0d219160000d00030400702c02860841c4c54018040000719001d24002c0c8245401d041c40002c00d501120300c040d1145c0e1485d440c0000c2c0302e4405440740e43c100d070b01c01601076490584070308050050204081c520502ca40d0203103080b0b001c0303900d651102d155646018500900c03610002c1d4450022461620050300441c41e0500200704e155944e001c69030b500d0720184650f610f010300306458001e900107008160395500b81203803a586d2801200d24100c00c0d0003c46400c049904c420180804214007a4060107007034911126100090040514405c004030b818059000f80860303401044401c0040e1a00412103089510648031000c003c01d8601d07013907001d4100768120981600c0f03440c8020403021041e8901400305d90400f001c2e1816507032142401c40703104504075240c82c09060010f803090031403440748200050314008400403075551 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 302008417 1250 302007167 302007229
    0x1020c09010b0a1704050a034e0b1e180108010212091c0e06070b100e06010504060e01080403020a06020408010618150512070b04090c2c 60
    0x300e0080e00592200c0d0004100341c03580300d410044603408100f000c03410a01e585419942c240c2e480c0c45600300117080105d03011010f4600495000f070074241c10640c2c03e10802500c0303401c02c1042c0b1151021407031540300c0d1040d510422051040d11a078042d400003d0200182c41521610740c10700301c8044600340b50401d555104500d04291800a5940a01403080016985007041d240240903200060203800094100320185e15600203083c0341703072242c21400e00309072038902070400014109002c2d4805c040c1c100c034506401c00141c100002034181c01d03501a0f0204010310b480310401100c05005601408000c603400c0141140c86602641241c0da0261080c81194145c0d00703150382e80c50603a041030340844c80326034560340180400101c0714800a84050003507001c010401100d903200703851f000b071441558024560024250251441803103041c028140419040380d9a40e1f4904c2860020440400c003d030001e80c0b0300f80c0c61011040d0007110b164552551a6064441a24800c2002121440f0301625500d036604040d920441c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 302009667 1250 302008417 302008429
    0x414010b07051218040b090c0406030c03090503040608060109091802010815210706021209101209080315030a020a090209030309090f010806011d190207060914120406020309040b01020c 81
    0x114a202104c0f41d010180880c18030054810320026648100c0782c5a040001c9010b0b40c3c0140c404a60240c50041840c0700b0155040d801050038580c040d0107400f00080110b05a50018446800f030102aa50841d80d40e80d40d4a20004885500c41500100d4a444280c403015612404401c0e42000141c00b81c001c040803000001002c00042450381d0018407900c42d400001480180301075402000f00f0b0018100760b007243e000e0a40d480c0709992449220f50000c4285a03480c3e88100030403428048c4100007007090140c181080043c1c1d0700100d41c0c1298810043c2e0300710007103090114001503031a902034074010265050108a80c00323500030410b500d0b098070044c4580202d5585000d00140514020740c01c0342410350400d0300950400c00e05800c1044980b0306c10144100400ca5007030200c1d40700b548044144e4102c184808000040e201d6280c000d015141041b0030101032010180c840c0182c807241d40229600d101450030202ea8500551103140c000d0b0b00140043c0e03815042c00d4000c9444030710144103403446504085c0000b05 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 302010917 1250 302009667 302009677
    0x60503070e0d150b010e010206010306180f050105061005090112050c0f0a081801020a020a08070312020408010f0b0108090d050c07090c0f0f170703090c050405070216050414010b070512 81
    0x1554449000303c0a205220910a50600a07800e03c2d0104c18131048030000b035550403040c40014402640c4d50304030301d01c0300250304c3d03411545540030103000d84d100f0381030802c98040c0805a85140c801e240301c3c0940c80281e4011001c44d60590410303103859a4903030000300c100b40100360003000720340d8584040210038100702454000385024446515240c040d800d00a414000300040628800d000741e2040040e160103940001340b00800692119039a81d6501d100c5c6000c81d2039041c01c080d00c071b980f14000309000c55003003019080103074030440007101003044000300c0c001141d110800391403c0e0070541210007000106c620502c01000192560012510043c0c1d40b01c1500c0101d030415a28100041c2811462400003940081501a6005145402040f80b44101a810703040c0074064204400d00d65164008020000615402402048020010001391400300c03001307525450084a0350b080302c00110000310f003514051040c10003060303000080031001d030708241c0050020340c4541015540d40c8103000300d103000e4014040081c0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 302012167 1250 302010917 302010923
    0xc080a0302010522020d11130b030c0102010917090613060801050109231c0507061806080c0706020f0403050102040617160e04050a06051201050702060115020304060503070e0d 77
    0x20950464604009003101c5010b071020f0400b024000184c030543c10345080c485040383d0115210350880c050303480c14000c07181d0502c2c41141c00444052620441022551006681d108180d007076030390000020b0012400c0320300b807203002045100f944803108940107020700644003880d00606218074200c0d90300d2800b43c0e141060341c02900010750400c01170100d540c1c0319081c60010260351108800714503c10080007910890103600030700516101d007100da10505080c0500f1032960b040002c1d500000c3e12420b0007400c1c02d1481320709c0d030048011f07200001344040c814000a41309102c50000e40b030030820540d9688003c0e5000c5001c00500c81814000480850000c1c4002c3c0002c0c98030761110908000c02300405040903000800320750003c42407880760f0310201d8024240185000040f1000141c2c1d03500c0b502c0e1500100600d81040b038014a000030f510210420560040c4d014054540803a0400e0b80d8403150301611980e800041070050700180001c200860240018580041030f49c20094440c0c603a10011406c0210500b40035 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 302013417 1250 302012167 302012173
    0x161407150222030c05010305151e0f0f1806010201090b0f0411090f15030319050304051905030a080406061a0703030b1912020f030303040f0b0c130b030907030c08 71
    0x304603059114a0003400703a040742c910109018a540c0318400000214401c0da8141500d450000e01643d50b042d040700c1c1120310081180c440f5078507410291015003d103000981c015640a4006440780c9041e600c01d000643c401005c0b42c00e00540c40c692540104000b80c2490705564a4170401c1d070000d46100a814415060b1502c510a585030505010801a0700003500c2c03070050400c0c3c2c091140314044202d440340c0c4001e403029900b000e60010008a86188138628000e003c0000009500619030752110003540607502440c200c6002c13600a2006203c41c0c0701141000701150b01c100107030816903002d00181584240100f90006040341d40d18200361800700c0035086652141000940201050b405111f503a580d070806a9040c00d031a56180341030660318169006401c015190030808204568401e00c09800160002d016242c690409280c88590b92050303040c12601a441d410004000c401c0080075180c5c500d0355004580403251400c6c3e0000c82c0ca03032026203251514056804040041140e186621004110080c01 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 302014667 1250 302013417 302013427
    0xc0d15060605162607120f030c1d0109032906040203011212090801060f0503480315160f0824030a0804060e060712030c0512090d1202031614071502 65
    0x100619041007001c0340c405040c9400341c20270701c00340e00030400a0800d61f05004007079840701c0c02c401a6440f0005030300007046a20320300303071782c1c40301c80d04d00391801e200b60134405803d240c50380b5410200800d0740000d00a21140b050041e4100c0013095040d8110304030185141400036100380c40720000384c01d440d095088100f220301201820410f90408200c21203c096030610707604d40c6142284c06402c140301d20580070201118015001414103c0b081c0055180018001d0403203104807031a6811a04c8040111f607028001c2c658110f1000426010b09600207002d0840d0b640c0d41c440f50b0780d0b95000c3e05a02422503503403407007010a6541c44003d4504204d4242c0c2103000d0103155031914945a0700810091070010450b009141c140803220010b003c1d844002c0900302942804035002100e103c0c1150707640a2080300c006400c2441051000024004c1000c103003220144e0340f83d01c0c0f28844074611506a00c41a9801c460f152407640090348042c3c803460498100c0350041441c0c030310b4004075464107500104c4501c03201c0c50040d80024 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 302015917 1250 302014667 302014703
    0x609081312021c020f01050a02010f060e01030501180804120c080604150509070503030f0f1317060c07021806060d09081305190e06030c0d15060605162607 68
    0x203c5100c00081402241e00400b03025400305045130603481d60a418464046520842c00b4000e4006058141181300c3c2000340319503445585800301e400f07120a881a518040d0800c0c8001140c040c00020702e504649120301d8203143c01d52402c0c0350039135502c055a24550054003c2090007052007041e001b54060b920014050200d07120704012900c1c060540400d81c1d008100412042d20040107484000003413040c02d64494503100810001440b980c0401401c3c0c007068440420034895001018400d03180030b5048038495551348406040501c140c000282d80030094203050900043e54222203648000c0c05442a410190b1042e40c02007501c0b135a1004413079001010481d01c05000055000720000c10040315801858007198203610058809402900329003944c180009040f0746017040990b420350400303001c0b42014041400c080c03428007100070b42e514030142804800506681300304152915400084407100c250501c07642c90308607038421444034882d5210100100b8010601c118058800c15002d00300a54900c400341c4 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 302017167 1250 302015917 302015929
    0xb0307110c03070e04020402070f050a0c090203100306090302010e0d0e130203060d1e0c060f020f120409090611041409011a040e04050c0d0c060e0d050a060908131202 73
    0x1540c034440d65021040000c0399503000600041103d4060080d400700c1d40352800031501a200e900300140c06070300110103440c20400005281160a0b0040c00c20712481c544a14a50040e4072065540120007184510141701040250f0701041d103880c402d000008a416020422a0800d05e800c0716031004100710420149580c2803e5908050703c01d080002140f41d80b5112002a182d0121444007078260a1360440480c8200b503041504401140c10101201381c47d130b9600d00c0144419031980d40b00006000e4089181010000040d00703900c3c00f040380504038102401c051a1a000b00011030003038445584810414920765201c200410107003a009060080d0526411300340840048180e20030074a4000d480c0c541c0c104d04001d04165001d4850461200c0542e40311410414a840b680c13490301076010710003002650401c040105104c0440b91241c403100080351041040001c0180102c8001e00190420071040000400303c1d8481c002403482601d80c1401c00d120445520b044440390b030000c1c0b0742055209450b01c213524040c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 302018417 1250 302017167 302017187
    0x8071e21050f0c0903030c010f0b0112091a0702100203040609111008040807030504091811060702010203041e1703030103020405060609030d0309020411120f0703090819090509010b0307 81
    0x1000e01444a41425100c40ca40040010304000d210500031810404560f820302c202c80c0c003800c03a030f0001d00c8207071050010003000b0102d00303c1e52408182c4200141c90881c1c6113000f04d41c0c0442e00440003040c413007081d1081740c039442c40042480045000300c480c082e50912561000d540683d000c1e11b00094041d0700f43c03500c2c800a140141449110b5920869010b01d1664007406442c0d00c194828146900c4500518054680e030103241c04c40e40d1414107120603043c400604034400003006028100c11172900440e107007480490310030858043c0c01a00700b00821b0141b0640881d4214040c0c3d40b000c02800307501d55695003400203d440072640c079907517000000108107510f068024550084c104441152801e0b02030000241d540802210220926498564120a5544580c0702c090010490000580c0e41d41c80000484084002140d60308000290003001c100000d00c20310440040303903804040d81e8500101d81510b44442c0c06518440d504106440c2c01c007040c56183c0040f02802441d5a901490303c0b4101800054124808 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 302019667 1250 302018417 302018477
    0x40f03081b191e06020d0207170a0c0206090a03140a050c01050f120709050901090609180305270d0605071d1005091c05030c1005010501090608071e 65
    0xa405542001d07581e058010b07504640c420f2007a42215040901d95280c0301940101900d8603202103007007195450540c0083c04d65a100b0b000c1003005000141c00350343c85001f2008424005244c03900d110005041c844010300b941c45005156007845982d9654840340c505040410322182c1c0c126118441c1003000c204881c80c45002c4c00d090040c10241070841c0a00d950040074141000352440e4008241c03201d006010720009032001601000b810f60711000160080c000521405003600e11b04040d0780b140c3e01902d4211181340b41e0541d101440d0400d8034107044c000641100d4015142c6140d51070350400da070b43e078507600c4000314400c10020405280202018040e45031941008480350200310700d112039580c0d29018200d00f903000d82449078031203500303102280f075400010f80000341d003001c2c901000c001e019001016050354107010040300e1100c079400c01c1c4e80056690070f1082c1c41c08100654030601605004211050b409009454211258410f00f450100306582e0010480041001d00e20040290001d401e522401d801d6 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 302020917 1250 302019667 302019673
    0x80711150a1b022803051c0c0906260402130905103207020a08040305030409062709030c080a0801060e041103010b03060d05060a050a050a0b13090206040f03081b 71
    0x841c064400a002c4492204c286450000b4605401094041c10985500c1e02c0c00d107000c60b07124880b141d4144000d050000300000031424050002908500c10320700d800c4030000c00344490310b080301e81d00c5001a03080780181c8100e038040151801280409054414030360a140240e0003010303841c219840181c1203500b4900002e08000b001c000003460019442c00e01c150401e00010032840c90369a44504a00b000e880c0e0031f00130510340000a0000c00e114000000e00191a12018104003440d951806000e82003050114610702c41ca030115500c4460f2000d0b445400b40f18060704008548083d103a4480e070b1079a11910b92400469142c00041c07040b030760302000c603070007030030b4161810001c1c01d0701400911030a0005100c0c415580da00040000d6003900d5142825110940c01000c07108282031540480340a00012911011081d00c0c010000700b1200040c059141d03116005440c40b0360310f0f907482c030030340300601281b0f2401e0760407410401c0002a070344204040e603801140145401c07078646a1040366032600c461084000100307a4 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 302022167 1250 302020917 302020933
    0xf0a05012007080a0c03110a03021e0d0206030a02030703050a05090316050f010c050a03051b04090c030b0a0b0705100603110d2d02030f010903080711150a1b02 70
    0x66003103551581c2401c01c02081190090300303900060715141083d00242454081c140041c420002c0f02051402524450f5000d640c078418018140035100c20f6a10020b035000800400000c0344041c00c030002c0701d20364070240c42e1802002103600450b581784d00030303158940c040d07500208000c12030b80e26100700c41c4c05c0440ca010071710082c149021071540d00c4c018910158078551220070103908200c0e0410001040031054070007800903c0c081c40c009041d0342c000703c240c5000302c0c1c2441c0008a500110b640c58154203450100f0050815051009002c014a162943c480500d40e4074041469155260070600004041a03c1d80607a2408540340ca142070010442070b03c031005041c0b1909100098140031a018820000c0c1e902c11511501c80c10419000c4503070002100a0070382111a144c8149501170790007020754025001c50b000b070703d0030b250b00d54200c40d1440b001074006017a4001140406114405400801140710202c604400da0038021104001c404e4858107600b60b41c400201c8841900c880a111031221036001500e041 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 302023417 1250 302022167 302022169
    0x120f05010b040b1803161a0901080f06010203070c08010c1706150c03130e01050a0b03091213031b06080606040b030c0d060e07020706030e1f020901030204180b0f0a05 73
    0x3038021401502660540800c04050f0748004d0350880300d03c10300013401c54400c180303c44469501c00c5d00038050402d50880d039904c6440304044a1b000c54a4079103060790b07010341e682e60f0744100540c0420041c1481341180005c01c483d90200e820066004044c208000002074890f50140300681500095031081141d440d08104200c4180d070380d404a1018139051404407030b80d07803450915650641c031405507a0002d056070b442012564440d03112009050317640070b64441c0403840d11030407042d00742e02044401c40d180e5030007202c0f103010100b01400501000728164440f10b206648940c0d440c40b0b854a81c2c071042400d400403100400c02d0a03440b0180d99004801070343c9040c03030305043ca0000852172000810111900c10005403039946407086911000c0100051555500d003402c1c0300800946800b480e129110000b41010051841981c0100302100d40080306003240d00707000c05040da0b0710080d4110341c076030300c1c1403690a110002e013000d240300c50195466114034000492526807001c000402c0f1952403001c0c040d170f025040510803 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 302024667 1250 302023417 302023439
    0x80c03010b0f090c220e0105010302070f020d0345060c0609230d02060603070807180906020418060e1303030e070314010f0e060f010b0d021603120f0501 67
    0x4019016100700c0200d66407407400c15424812052034120204002e1000c2820303419142401c41503c415006c600301b2646e030340c00114241c1c058207002600c2001c000c0791001c010300c1c1c8a450410311314420308001030030360f0303113800f841c52026444800c0d880c003044020441080d9031040c038418841d400da40006452800e0400c0c800400c04444175800508036582c13003801c5014010030459100401c41a0b13074003041c0000516080b00c0d120010a00303210050722521000c40c40b60300d000310f4200d0035600070400500c14248ac161400c0c9107940c000c140f01c0455555200894040342e42400104041d000c00030f42415240074003550381d01154116803290911004400912001c021801c411a88007a01407a0101c2d010161020180c18000b65034002007490445000280c560766064100c82c02c41590080d0801c5101e03122003145441308030840e0368681d00b8412070010300c9403c0d43c03a809041c8068a4a000609020f4070006140352444e000c503094020403c10034194440755800e006652011201c0072040c00b00754503007944003007 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 302025917 1250 302024667 302024689
    0x10510091a07121110051b1b030a091a120105011215060206010501030f06080705100c05010e060a0e031e1803070b0d0c080708060d060b09070801080c03010b 69
    0x9201004000300c54800740c1040503241c605070407201e408001040b20001811801c080080840ca9009445603400b102a0f188941ca1050b1104452400f42c8800d0381e184030110b034002c0803a81d194a06249160110390303420009415603000300e80311465264100007240d8a10702e0340030141c41c01c1007403c1040c5501c01d4000824030381120420308103840d60399070750600440a00604501001c0c0c01a4903600002c4081d0b000466504032102a2000c001c880458041d20090724024007803041540e000d08410080c03420004031044c803580a5180c00764074000c5030350b5114255180a40c05420b0742d44140c0a02502610074032032481c0c0c00079100011450f2407010070b111140001c14a0311031241800111300c84911016000c01400c140784001c0a4502141c2c543c1c8043c2d6058101d120010300292411040c4072084e402010a1030082c50300341c513094883c0d80c40303a007008103100c6000e404850f100e440b100b2146540e1200f101403801707140a40ca4040c1c40d50304000c6071600d08032040079070603ca83e040c107012180545402910907 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 302027167 1250 302025917 302025929
    0x60507030e0604110108060112090308010f1703040315140108010c020d080603060403080402040f0c0c061505150f04090603110301050a05010f030f05192103020a08010b030901090b07050a02010501051009 89
    0x481c080e91501f00590303444109808480d00703942401d00c24400c00d640a08060f0513035aa880d2000c001a0f1035214540c0307002030325090076040f81d20405c01800072032104811174031303c00301c40000803e00c058585440c0225034002c0c0d0083c803d42e91034079445503203590140300700c1c01c0070040b07840c1c11500c61814100107969031001401c0a0b00344918607001c0703415034403103030000c01c0c480c0c0110001740090703c81810014a401c580308400d0fa0720f2072500d1404003504025042d01c50441d01b0003030100c9011120040f80d465554081084940460001c20002441c1c0d40315000d03080080d400780d01c8004500421000345400d50720002d0441e55414500340050004107032400c0c0e032a09030fa40018900f154103005240c180c0c41c0a01d102c0d0030741d800070607035010501040200d502c41c1c4200704509a1a2041c8042202c0a800764043c003003c0c4004038884c407006104449000001d5607119035408008140710701640c40d4040c00100544100c00010000280030304080d07024003e0b0360042100341c5d001ea4410f404c84000510f0035003180100 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 302028417 1250 302027167 302027177
    0xf051312060f020313030e03060903030c030a020903070905040b100b0f0c0c0a0806010f09061401031109090a05100b0f09060901020f030c1506040b10230403060507030e06041101 78
    0xc02804180d900420144228038802c6540f420540c0e00200a1039280c14224002580707070101c00c0403401d000c180c8500540b2800021410b6071103099002c82c1d1034200a005160140e8207200a00c8030781d03001c001c41b4004060040c0005800c2c1014207100b1580e000007011180c04124075602009001c070388504031003000c00301d850442c1e04c032141031251a05000001201513844204001c000c42c080c00d020415070f040383d444c1140510f210350fa0b443c884054030304601c1203130b06024080e103103030045500a40044c80d004040e2105986041070010000c0e28598064a00884041e5200708000184e100700003a9809028000ca0560801c2e5206400780d0341c41c8203003074032940280c0b40400c0300032561f4020081e911940c0648000c0d80d0f1200c1c1000540c55580b140e80009031280e105c080085003060800784240a00e4220144c03000c2c104803003000d816610f0406d4030178881d480c01143c6081840c245510800380c00514810f960116050910003001000d5035451801c103d0203070064018400050200510703428411000c0c244 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 302029667 1250 302028417 302028449
    0x12031802092a0408010204091811010e0a08030c16060e030a1e02060412020405131505280f050a0623010905100e0a080d0c06050606190f0f0513 63
    0x7180866030109030080d10b0910224000c00c0130362041d0090700555590403c00c03c50088461040b284409030003802031300b28810503103100398551094014560100c4050150140d10f0364480c111441c0da03000541e82a00b42c1c00105801183d0075a26800000500103031620b0101540c40c040029140c0800210051550850b882c454211440042c8400325464000f4519030b156030342d074015031008611099089201e5440c00b0b0002e02207080860003c0021900f016288a0500300c2070000e034000e0501a18018188100e10011101001c00502e2100c0b0b03036068007008905040f07103405503420b0307a9000e018802102d0504c40240540904203c00070010011903982c034445844020050300c5e84481d80c2c000c990852034008908070754540104580101084c16200030b83d40b0b994800d011912410300a8580c00010101c02c20007000c2125034100c02c1d0801e40041c0340c9807a0006008100404224420a0382c02061000400a0406412500c1c05100c1031060420302d2802501082c0003142c11044c0c02900b00c0c140924034 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 302030917 1250 302029667 302029711
    0x15070801060f20071806050301020a08010509090a060c0504030201180501050702150d02030f01031209050f063001081204030f02130b0d0b1b12010303030e0f07031203180209 76
    0x1010106161a00241e89030a0744442c0418142612168100c0005d0304218000805040520031a1004409562030740456402e14003006012540606114081c0c8500c901481c003054442c8543c0554044c10b071a42c81e983da246100140928852040f01c0c407007032401100401003a6004012100d4883d03044400b00010403008100c0d030060f004660081ca00e003413021003000103280100303803018185c90140c21819105003401004451640c211301581c0d8000c0106440e403442802c0440191103002d84c2d0800e16960f07442402c0d0b49904400c4030440d4013061500707400042151341001e10915890b4052005994030302801c54036008030348600054028042c003000c010842d082c00065004001007440200061000d2002c2e00b01003844440c16110621814030034030440061481c400d04a80040014500c038034003ea01c1c1da1001e50060281c04000c0049005e180c18051010390103125140103103204030711848403502d02c241e004044a8072120700500035898210550007503030784d401c108d940c0802c1266581c448444010 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 302032167 1250 302030917 302030957
    0x603040c0e010801051816053d030b0108070804080a03060506031006080606120117010b1011060c03090a060c02030d020a080f0a02130b0a0c1415070801060f 69
    0x903224045400041c1c00201d411001900080e0007400c2e04181712005001c000b64054640941c070402811181402208101038244078400e89080c000303404040b4004092000458111850070f4040f503000b49060001405513a0140b18000080700c081c648900340703180080015000f650083d0010b44210b0000c10303c9100340707201f034000c01c3c09800c0242c20329490303003422201b2090700c0e02c0342c1c0070b01008600c0001c0001e416060200944102c0840c000b04003a190b441d00050015003050301c41034090a54984003444140d80b50156410550689a0344214141489199050070080b010b4046a540c1c2010810b1100162001401d03690407a04410000341200d00350106038a54402c44034001495800800c8001c54660009045031094001e020004507d59a400881e0124821403d1310a15044248400c1c050701200c103014001d600440d00345424118101d484410045211120b5090725070300840041c0c101100c0d42c001c05030403000506110403154141071018000025180307480742001071a44c0c0b1520110004 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 302033417 1250 302032167 302032169
    0x93303040b090a0c06032f271c150501180606020309300d020a0b010e0c0708030a2009100c05030405040e0c04050c0909100e13020d120201020306120f0c0603040c 71
    0x640340d40c0c00e40712440103d020103800c502c200c0c02600c81d050281001d00f207523080e055060610b008001e42c1841c40c0c0440840d241b041d00c03510035540a054032119003810b10061040131302900d480e050268845058800300002e84103160400411500b003841503400795103c1c280039440c295480c444a100860007001c0c014851441e4450349035880c070a0b856000c41954010641101c4240210049115680c0b01c1054544240c01950034404480c2c0030040040411804d40245410480d0301501090715464280e020b24150034903408003c0c0202c0024419043d49172180c081284a0245c3c00c050308007111588401d034890146128150240341c442d580d950301c418092004600ca02402803080116060042c3d20b014030390064a031250080b243c5001182e24404006c406400b02c8039441351450b5182c1e40c001c00b411006602280490300481c40d60b03d41c0c1700007106003640b01001d4030142e00041e200e1800c48104400a02484a040350315007240e090308405060205110b00c90a500380c900b182d80351610700c1d0094840d549 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 302034667 1250 302033417 302033471
    0xb090a1a091510090803070f051903020c01090501030c091503090503180a080f1c090b0d0b011b0b0f040302030c070e04050601050a0605093303040b090a0c0603 70
    0x100c9820000300034501d21000d150b841d0b0680d4040f2207041120300a0303643d48854000c1c1e5105178420b2041c0d030700185800005544003403254040c0d43d400302920300c100c007000c3d620400c01c80c0540c20079150720070213581c400920001808246001d100201c0700d0807000c0d080e44018024409009403155813580300300d010f500040382c2e580d88141140d83d142e2502d122030345404c00c2184000e206501d40e00c000501e40c140000e0501501081502400039082050b8091492070308207075400c1c1c24401c04000015002d4503c1e0b000c0c0411022803c0d003c643e0400c4207000502c0314645004100d034109200802d440810f2072103d44035480080aa40c94495880d14107040c1d207180201e803241d51081c400c0100105410b4408c0801500507480740c011122147d0b00e60042040b442454010302c030018a00381300302841c03071401040301d140c8201070195134607155448048c0440203220320886080c0421000003407204004500ca4806c0c0d100041074068000741010341d552940c581103a1141c03a00b0561554080c003030f00810320b00c9101144076 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 302035917 1250 302034667 302034679
    0x13030c02190b030604060e0910020703030b060403080d0606050408281b080105010e1504180b010801061809020a031506050a0f030b0702070e070f0908030c03030103150b090a1a 77
    0x41e0ba400881a01e5100f140c00502450074802c000a91610022169000301403d101030a41a4800210f0500079049682d050f810903031900c2d5015005d40342c14008001450041005035960050500f5210075694240e001808000c0c080008008442c404601c0f03004095007201803a0000c6001858205469000310000d800040400b15040030b040b80c144c64282101c0720040241309582c0c2c1ea541108103002c08840154105260f9001c055240c9420744c01240307887e081c4145101c280c0c20507250305c00000000d8000704a01d0b9900c420911105400301600204e10600400034004075080f5408280001c61500c0300800c818550259031403a040d40d5005000580009040d40c9038060392540410365400440c0b109803034201e01c000121b01a00c0c80401c0710307825100301195046041d10b80103011258a09103c482d036080005200340441d60b6541400248408420080219141c4d411802c10f420301d0000005104201480c142c4010000c0e181d8501407607002c003035003600050383c10318108a4482484122070342a07010b4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 302037167 1250 302035917 302035919
    0x1501090c0908100e06090d1209020102030d050c03091219080c04170a1e0f1103011107050106051801060807030506011b0501051f030201050301030209040503070215031e13030c0219 79
    0x300c019440300440400328421219180c5550381b07810707181c5403203d0703400b8000f50f60000004480c1c41d158100101491041c0304503031601c035050f1081011604180d0b81e02e0002d0500005101480604200068002d240940c20350704e094140200c0c0e022084043c0350741d005003c618800650307240e03032810558000b0803c200100400790080d290880c1c4a0341c02c00401c840a0650400e4145c1c1c90034a506ea185115610019000103481c05483c0d030181c0e4865460a154150b481e060480002803084000c0d20049210703100100d0002e0410082180c0011074030580c40000b41400010080d03182c1c0503443d590400f1003070074006010313115840101d6180c1844054200d140350300c401c481041100540c001d900c59030a000d00c01d03c4480404114900b0a1010f101c040d000a0051005001618040710740a030403c1c41041120300c3c0810340d0380400d0281c1e004042c1256000008410000040945110030f0244e0041c0d5120118901e40414405074200000c1d03005030030000c0340384100045446032410002c00403400201c1d942c400d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 302038417 1250 302037167 302037193
    0x120109050a1505070503041a06030c040914011109090f0442150306182f09220201020708060c040801060b0306092a030103030512091501090c0908 64
    0x1009902e150360403040d140c1000107100b18440d0090f05d0003103501c121089680f5090001c010b041d0300014190302c0d41809004020030003503507144501c1212070720691704000c0903507486040c6800c450070020416114501042360711047c0e1380c0c07444503662019155040b0b00094a940c282900c11000d182a00b07592440520300e095034541411109504182502c01c03003482031030544545000792803402504c4180e60b40035440034000200c90750404501c0c03118448021035520045d8071b40e008803130148840100b1210640c510341d42c3c1da80b80303445c00c09001c0d00709940980041c2024112424409041c50100380c090070790004410031a031003801500000c25440c0211081420700700084000e80d0b11501c81c080080d0300e0440c00160301e4840c034003503a100da40010300d450368580d01c0c806082e0651008101c1300c15040700032010103905070404000f842c042d60081d629075881d41c0303111021110b0700c0d01c052b00c0d03085580c1c04898040b07808880c0c0c005a50640d8044170000c20100030f80b00c03007604c142c0c0d99a000503426009807018801d00c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 302039667 1250 302038417 302038433
    0x4090f05060405070f082701090b06030717070b1c0f0b011101050c0f0a12050408120c031b0c010f0e0c1005030907140f0315010807091109120109050a 66
    0x7070101140d00304181e8440c00015150300c001e01c140c11022030050800213904086092025402d000c840301103018454050340b40d1400c540c22110100e800c0d0003294103000c050700f4100103031070142924902c420110412420308694402107446602c4242c1000640c140703403640305061466181503150420b000119600a064020300b0600c440070740012408a03407801d02c0441405064041d00c0c402d01114a4164038008030710490348132815441c00c5c40200d694000c0000d0b418414607100780d000c0c0e4030064850b00060b00c0711200c0403001c2d203102c503950700920a000b4a509c44410540c210400f90014540d103400100006000d80340c242d040c803032120701e8001222013a40012500c0101c5d06401c403032840101c20352103003e5405010a990010450740250004d0021211500309a1000d45005240381e42040300e0400003482c00890300d00100f1030a20b01d000403c034142c01040044064540035009029020030b00301d074000d80d40240b000c1c00e44154400c3c0302c6410012020f41c440c0b00c1c0d076074209054401242d00b5091900c0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 302040917 1250 302039667 302039671
    0x906010c140a020f0d020112050c16030216062a0212100207020f1c15020f041410020c2b0b041a060102070b0f032e030c051816030204090f05 62
    0x1025007400c0c0c2900381e0518141170b640000690584130005119001079840d00205001001e086c4061400c2255104007000c420700e01750071034801e5006080e030848070b0301f80c2c0500f03000682c404024000b146500c41c142c034550b4000007564100d20801a81416031a000094070300340c030203400c14028043e4011446c4d800e0b403690001c1003440e000380c41800d075800880c0c080c00800007000080c1c1403017800d0014640c001400301d090003071150246080140c1040c1e1440c0200d10702d82d115511159440e42c011a000d034a50410605982e000103c50024040d914456030100782c4000c03520801d441c000103188072a844030040c2ca840190071903006050713500189850f183c83c002d03210070344144141704904400059400d40c070014024007900e8007034800c40c0c10241c40c00c03001c0c00d4540020300b8020041030b00310b407105801c02802c4008207184040c0002c9400441c0396080100d240589900058020003842010106060f4641482604402c07058240318035580c108008038001e005a401c00700416080c905441c00503079017508072038 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 302042167 1250 302040917 302040919
    0x10605060f13170a021201090209070323010806010603020924040e090d090312050910090f0608060f1c0f06090c080c130509010b0d060207060506031b0906010c140a02 73
    0x5041e10341c44002e11600030020a0718410943d00144801300142000018800d4400702d0b20000308010100703500141e1540310031101000000d5a980310b40c040e540d4a512078103070001c0341104011440d41444400e0b61240c2c0c050003071605150300000d0b01c4407181ca4400c5442e403c607940c039541c15040d1209041c804440e900510500d40c0b0445910041540c2402c00f09600c80c001c46e00d0346440a500b031a65807600702c0c0381250701c00030302400018481d07400c6503110312490b0074520040f56030700d0500d10f0400a81c2c3c200301001c0d401510411219004000303031a1a20380d845900c616080b5840e24691407114a11144040321100040c0010b00e940d03100020441d50781c000194503881401101061074030742c0000e55030ac14100d0310095105064802c4082441429841aa005134000d00041200d409450124a00382c2502c0d204950040c2d0022300780c0c0502140b80302d02c582200c030460241001c8450500d115502620b810141032007441010085100740c3c0c02000c402c841594410741198424455061240d203070340c032144050b = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 302043417 1250 302042167 302042197
    0x9080d050105060a051206040608060708010504150e130f080c01051014060702090a0b0303041e080d050307030f06090e031e0412063207030606020705060403080c010605060f 76
    0x82003e141c2a0140c50040356103503203803410900e01200c418001400034150f16080f0359107003008200c0c2d86c41030140c0c511803c12620340d50103551400d803c1c40200c0c0d0b00410f02e0f6044280c51142485042e9020b0b40c01900301c0c40e07031411036450158900b0400a40c14204500401401e0006080d0f101a00190030040c817a10042e10444c05050780d99108000e0000301145071980003208000c45401850496541904500051000150301400ea8082880c1d98815080f80d55035840c1841400000c1c0c0903c5454005403a8207005880012200d0402421030302000d0310743c00a15403980406060354110360700c400c005000b41c5500780860401404001e03140da0010340d01150000408d01503501e00c06d188003c0303c007200c01e008c2c01c1e00742018a603290400100641100c20031691644904a6143c0034904e030400071028403d509005103050036000a0101c4c1d085034841000d64208403c01c110075610581607030201c90700610030503a5521855400c03401424503402c0b80741d0001010442d6a16a1042005000390b0840c400314 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 302044667 1250 302043417 302043419
    0xf0303040f060f08010e06091503101409031206011101090606031101031d03040911040f261908220b0a0e0102010b0f1c08070516150c0b06031009080d0501 68
    0x1089421400c24020b0300031302c05031a40440c1c1f9900b03209101070303405607040b0100c0001d0700203000081c6c201100131021110040d21805940030410341e03404ca142d005403103100150b00e0202841c4007a1448040205900c0c1030020b2401c0144e0200c1c801e41180c0d00c800e81c0000104040358580c030381407900d0300481403407900103480c00003401c0a41c1a1911518120344000004606061802101c58090881e6511104079a1000d01c0001011911054048007514160359440d481084110840721003048458601910b94085e41c0342d004000d0b07080316540f620a4005024681e10b203c400c0ca0f001c078100c1060b2041c4000c58040400007028802d2078050a41c0b01ba0a40e1100002c80301d1400481c00d1f90b040d01c10085e03100d01e042c100301c01c841c40c0900114007190030012400402d22200d44031500b03e41c110600030350b05500119403600852001441d944080c00c0c480f91801104050340c03400038480940303100300800300380c440008100300307941c100283d6407903520444007440001118036001480e50003180001c0141401c2c000 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 302045917 1250 302044667 302044697
    0x30c030a110a091703040905090607020f03070b060d060e0d030b01030e010b03120a0912080c070f061d0a12062c030307080c1e071205030606070f020f0303040f06 71
    0x308891810300d8554841481c181000960301c0d400d58104c0007080544410040001c82c40524095213200300c000e0307809072150f49413210000c0d081908004040410750800c0000300c0010700c070201340c03a0700030805550003003412101d407504a00501200e81d00301e400f072181c0045081c0042e81600000051a001e0303800b44a4081c0f104220b038203aa000c110031544c1030b04101000110b081100024124140443c603254039a00d69407030000301c0d1050141402e5800160014220889220410a490082210740c0c0200350341313072030718a00406103101c1d280e00d80005400d01e039410020b07517600604580609812109594500034501c0c005004151451220030100c0e00d0806d02c44088040c1c9075074604816041001d18610342c1c0c3c05404903030501005052123000c04c002c0c404a01007201d850700c4070b890f10064020003682d07907645003001015402d006101004001040081014988400c000c0d901c100303074070020b811000241440000c54918400c0300c46501444040f60009044c101c00300a42e044511075140d111001003642 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 302047167 1250 302045917 302045951
    0x204031a180f030d020d1506050705060c0f030406090201090f0b04170303160f2a11040b0f0d02040f09051608030a0215220b0907060e13021c02030c030a 67
    0x61010382c8150401c1c0300d0070200146540040210034101c031000100040060110003000440341c01c03450002d5070118802007080000c001c103c2d00840b40310445814014070b510700008901c0000c0005003039a4036030040d6021640134003a441d020f4152050380d4507019440c4d2652800c0b542191092070203468040c450b140302e00001001f00ca02506845c0c00000e000824000d05482141034030007a603040100100c07540b94021143c204c2d40d1107400c1900c503002881e01c076a080c420201e00840c02c4c4640304030f18040d080e00b46552907100c0030301501800e8070b602c0c02c801d0207400042c004105400356410060300705070a036810400042406002d40340403188240311541c4451042e56039008100141d00541c2c810050003201b0b42c034420350554030032010504458681c4842480e42c0d00c03485664411200448a4414045c11680c00c0c0300c8203029003d00c1c500041e245c0e00c00d100041d460103d903030a40d1401540007e00b905c60030b60400390507459840e0340320259940d03304502c082080703034011a9200010f034604100004506448 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 302048417 1250 302047167 302047183
    0x1103160b0c070f1503110c01060305030927040b090c0a0308040317070b1b0c190501200706050606210a0c1d12032208071505040b0d0204031a18 63
    0x16401da0050b041140741178008200807005401045024407403c601c2007400d024030006944110040d688940104081c006800f03510744401048481c110303001c180c00d00001e4662640260080c140c4265a114640300300d08000e480400e094101d0f85c1101c0c00700c14082e40303c2c000c2003200d1003000c81000c00e24100030b440c080386c0030f42400108100102d4000c18040b080b400a0240d1a14801c0149440c108001800078503016a03140301d86840b094111038036061000a205486455010845101c0035601d1401003242d00d1051035130050000d075640380031802c0b42c2c858000342d4500c80b034503600110740800d4600300c204102e036080302d0040c8114101454a4041c43c46041007551011640c1c40700310780702104608016070003100e580f040b0301d581b0003480380c2c0114000080c41200180340c8032981c400c009051000c0141000c0258021112070000d0180c075500d0302c0d40c4a8111001c90b103000301200c0e11250f4241c6104068071495102030b281800b0075428200d000482c0d400e0b6401401c1028141e03101c40155031001d900c6082c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 302049667 1250 302048417 302048429
    0x2040608040f020118180506030303160318140604150216030c0302100f0e010e0f03190c05060a0e0f12040909240c020d02010b0306041103160b0c070f 66
    0x50300880c00107000c022840c0102481418401200341c86460540301c032100030ba010007549035a940c11043c40d40b02610a0030f0f081075042d4040d62071442d2044003c4401034281c417007001010340da0f10f040070701d24a4100a22000d503602001d06024480008080d9a48640c00d941c183c5025144a035030640a925520031250600c10400c00d1282c00e00032610241d55072286050f003a0258028a804038081d18214440c104002c1c4902c080000c00c4000d21642608444204182c01c10a42c01901e000380c8418000042d104401040c0460055441c2e80207011120b0050f03008000705241305550500204d0b10305600002c03060603031007003101c120380d000c1e41c3d04690b134801c4c4810810442c03501300320030302841546400c5070510a00600415018850b5881044c00b02c6000007008140d45c1c2e61250608009507051001c103030fa024051000b480844440000a900ca0601a200510310f4100c0c640c405c0541d20240040010301043d1520303901c036242d48000d4a070866002e907403808014002c000e030100c0c0595500b012030042e600 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 302050917 1250 302049667 302049677
    0x10050406141602120c19030f022503020913051504060c0e090a05130515100b04080601050d060e0d0806090a200906070813231f05090a030503040513020406 68
    0x360b11100000307500190105550780141800e102c01c4c031801c1140c102a04d84a42d680a923603650031a8028203115110b440300b0846010040106607010807209810203498045640035600d4480040c1396040814900000703110f40034011200700100006220a4032a0b40034070014800c02c0c252440849060100206460348402c0d0748001c941250101c0e802194000e40381c600e4942c070350146450341860948501c46144041c00700ca81009810b0a00110b4100200f0061150504050401c6407803615280140540350141d0706809801e000d11206030800c40502408400755200081000d100510b4030380104c031420300400341000400c08080b102d00c074401c0452080c000b003c0c090050303e07002d2501c640c800e203504c641c018002d02040c808281018020301111802c0401803103458905034203258040852031a010800c400314035203111a445100700500a10140502c0c0510524418003e64450048030100354012915107c08010040008010005e43c1e80c11a1705400c1d001070300445a09901c194028800020 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 302052167 1250 302050917 302050933
    0x60c060a0c020c03030f030a0f02030c0a050703050d1b09170d030b0f0a1716060c0206031312030902030c0405040f170d151e0e0601050c10050406141602 67
    0x91401da11004101c0060b10582d0800c00c15100040d256411044000c0240c007000400c0c081034903c58801c0c1001e981d05031384113505503c3c02c00195600c07406002e80714410321070002061410540b10740100d0380d5101100f90700b04041c1242d0745045030340001c207540c080c2c080303411810046424000b01250390302c2221510005c12500043c0c0508a002e4024100400e801c584c111102e500d807507407841c0e0200042d01098407032003404840310702130b60304d002050211510291201030081c07080540c000c000b64413064040c0e50b125174944484640d208801e80242c800791042c404000440e0f420347c0c2c180c03c41c440071070080f130031210a8041901080103e0f401540d0060024030400c40c4200082c44007603d450305450101409401c1101800200302640c8149010b00c8001d502c01d4000c0c410300c280340103000451a06504445d42c1710741020104920030748c1c041d01850600c08007081e240c545003000c005051842c3c01d800010f00c00c90415180c201d024042c1301c00781559070300081000079612002e40303c901044c00e0541d4014141c00d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 302053417 1250 302052167 302052181
    0x3120d020f0405040c0c2d0305180a08010c0e0f0306220506010e0712020a0e01180b07050304050111060906010303030f1d070501020105010b12160203070f031d060c06 73
    0x207612004440c65032800c140b1001885503913600c10344501c0c0241e520707280f03422026860b003503c0c2c034102c07030300502a140200c1e400c00d44003803104c1c4460720700d955240c18241d40d60300031400100d44203802c000c907a80d030023a013900c004200b185040d0050401242c15881c0d0746d241680780010803a0300e044038503840703406030311003070000388210950071412418119660881410354041d032220380c24034009030845403000c0400c1d0180000c3c160300560358400110391481c21420604491001400314905450441c108444686102400307004140200010b03d2446165503603162140b616940343d800031302ca1300e40400c50f14001149545404030703d652080000401506035a0300b035543c140c00070b150002e84070314007683e100c0021007554000d049200c4140040d80040c80080c0c80e0000080c01d560050704400d080d20000e002c1d00441c1c00e20a48407a030005143c03030b20180c0c45c0c0c2400303004070b16600404c40050450314642e4108018035030000304480044c20100540411301003240c050150320f01c10109500038990029001070f0034 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 302054667 1250 302053417 302053421
    0x10e0c130902040b0603040b040506010b0a080f07141b0f01060b040e1308040311030c011b0f0807170409061a160c030819081305071211030601060c050c03120d 70
    0x3507074802400003a10401d0310003c10200c0c0c000700c07000c503040c480004c2400b061003010402c080c0100706480c155803030010f600c80f000307080b40303030140401e504100b002780403c11542c09410b00c188900b990312611900d0310b05010383e10709918032069408103140100480c00709200010700915040e603207281d0001e86007031724000304410b1503080180740c2c110b1241c45401c02c10008101e60020002140602c040c07085507c100400c042c00c144030711503d2814007041010a00c03c0640c071158803952950459040d0981c86e0039404d118440b4407031040001c000c5940d2039030000380099607001a00030780394410000c105141d226180481c2101c030003800c014400000784900c0010002c0c4007120603d15105101d00c8028950700d0351441c03155042a4440e041c05e46036030080c4183e00b5440780c1419070226408102e80001c600f40d4030768580b40c0700580903111780c070400540304200b842000326200b01d0403507001d012501c441d83d41c0d0100034250050f1060480c1c40f80107011250300c0350b03d030014081042d10324248105107020072402c40040 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 302055917 1250 302054667 302054681
    0xa05030328021c0905090a051b0d02070f0303060303140a0203090f03011b0210110711090c0c0f0a0201031a090106030e21030f0f040b0406050411190305010e0c13 71
    0x308501c00d04a1203c02e4900220740c00740c680403540c880840481c14002080180400186032500d42e514140400204c001d150741c0e0524507202100c003056070b074140c030402c490280c450002e02412484108020404240e41540102c044078065620780b001c1440340e0501400612032414080b0059005101003030f800e20b001210039606080040001581d00c0a40c5038100b1345013401c4d00407101607040700f1440d80b001d848074080c00c104000002c840700d1401c01d89586129801006030f41442c021403004001441c401303a0003080310a18070035038040b0b0b00300d0411514169641d400f0b02900f28000f0b070801607513800c0071003048100f8a01d9603004003c0344080e800c08004900074100032810481600c0741c0154008020003445030030b18181c203c5c4141944e00d2a25585000000e10043c01d4002040405000c02011075840000380381c0042e401a004602a1640d081c88940011340c40d070901d60081c00d804079080c1c2c54004490303180842e84070348000c3c81060b5a4031840d54036008401d10590b0018251000f12403a55000d901c049 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 302057167 1250 302055917 302055997
    0x130b0a05041421060105030c06130b030403050403020a030b0739051e031b0705010c141006080d09060815040e030f0304030c06050a02070f06020a2c0a050303 69
    0x80203000b0980c8008110f4480c1e01c0e03000324a82c0100c001800141814460b41e4601d540c1512114034160314269072900e503a0b003a01c18941c1c03903031340880498101407080040f1401035070000c01803032200762030b07007400c070f040210030f96052000c034000710910881945428440c2c24020840c2c010279190348190007071280c006050850031130301c0d40986551042820b4825401d1401c1d044030b000151345884070303c46a000d91039448100700c050303648041001c003e81d80e4056050510350f90b000c03d41c2c603003400f20400140c1c81c0061a4001110366400e14a000c80c01b44c100090a01d82041c166498009899440708152807088045e030301702015455400c003800060138582c110811405d61001203a180c07400b0703c6041c001580042c0d500b2000100c3c0c405003c41400880d0143c0ca0308031600000c210b10300910b9650b0b0790841c0c0d280e504014031371900869156255801481103c214183d0b11074001c001c104980d9001e1a005684401c1d9485022085808a1582400016036903410b0040c078948060004051851101080e001c1c142 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 302058417 1250 302057167 302057179
    0xa0308040501110a0605090c151e0c0c04060605090415030b0a0209060c0d08190b09070c2f040609060302060901050912071e080102030601020a0b06011211130b0a050414 74
    0x603000400506ca0304c1d02c141115800f40414442d0342d42013007083d1a448083d6a2446810b005d02501c1b00c4100480513003502c1202c40c0c003039865000f11202030800200f401d550b60b000c0d190074000a603e64200b0001d02180344101d804204402904111030060000c03404040c1441000d8000102c4244260b402400e00020080a05081592007203040d03203031126401c202000107084109100b40c1010010099504204840b002d00c00d581e0020045620040000d060004015110b070304401880314144001c40700c1c20300340c6a00080100a80c001c0008280c01041a5001c0c80c40c010700040c14182ea40b207144241c075402008245024102401100c95810005419900040320702c2e10705000c01c000c104550013015410340d000041c4003034103100c4086259550245280741d00400401459a03404181c410940340d2245000c20076440d500300480d5640c1c000940d4100e480d21f044941c2c52042c0107c0041c02c80f183d20304101c8400107032500c1c4100a035000300221400494000d22051185020030680003410701c1e405488 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 302059667 1250 302058417 302058433
    0x6080919030f1b0f030806010f021c091503050402030d0201020a020a020f1504060f1e020d030914070b1b150406020c011404110a0f05060403030503090a02100908010b0a030804050111 80
    0x3468000c450b5183d0803101c05040490307050825420681160703022a00f42030104070300b100352401a461314400b2114400c202c14005400c01614040c101d08070203411141214000072a0080c2c0140007400180c806920a00c910502024018030500842c1c20528195004d0075403c00c40c3e40c28000840403c40405500400e0b241c81200f2411461000c4c0004100c5a07984803481044000080c0051400f042042a4030381800b1a504c603190700010100d48903d10391030001910b98881c00c2400c5c440010f02401150f60060007000114140302c00003929405207060764021862007a4041c099884581d20440c4c0390590300400010081026940030701007585e200800402d12400d83d20080e030019008640881c0c001000c81185881801c228441401501900d01114050b908007000549a8001e40c400181003110010002d14202070a01084800680c007800492000314803083c081d1030300e2054001c401c40d43d0310300703501e060f180e10701008420100c90b00401e90fa0b150604241c0116210013071601545941c0c4111a1 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 302060917 1250 302059667 302059697
    0x50909010f090f0606140a03021921031707200304031b03060b011d040b010e030303010305010c0f0804020a061214010f0f0b070b01060813060f020406080919030f 71
    0x1140d160603c5400d01d140c03809410715110003181d200f41c112030b0000040f07203013a1605072a11001041542c0e0119800708a8079040d080d42a012005074024040030101075040400d0a209501c00d87c0d4242d12a40340c01d0000015440359610040044450b0000610203180958107041240c0709400114003100a0701d02d09a10798aa00100b1140c000d20003d03124813010080091004a100354480ea110034680042c100e0400702d900802944d030300b16020711490740d0300b0520f501c0360b01032042c4002c6200c0140030b4a8072582c1d40d0401d40d0082c02e1400204d4041504225400c1c02c8a20030781c0141d100b5a801041c003a00c2e5400c166007290000c141d07181d54404659100c0d90540003100e003030304090080c082542c40e01441d070305021240012484561114000c50703014040440040c0111001038103503200752400e45041e070b82d4881c001c0518a103032400588020300d0014400741d0010740d90010010340d69152210f0001e40c45003c2103a0381c900c2545015404105480e2035500001c0c450311710703155040c91a144c10659900016 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 302062167 1250 302060917 302060921
    0x2030f010e0304060f0206040b0720060415140106020601060c0c12060e07050a0501080103120201020f12010602190201081b0d06090b09010f0f1406070606081e0313050909010f 77
    0x1e00032a41d40003190400c5800e9001c417001815240c2071001c0d101c070b81000e03502c035424240043d1410051003035049000d150745a1a210b1005118401e900700c4111b4101400d040008101844403295554105075260210520f030440042c101d801c20f41c000e2039035a103005003c54001c0303110352040301c03d14600c1800140142040d845005c005000d200002044101440410710300f07440c0782e00090044007458010000c90780c102c0308a40c1141d8002000710010304040741d0072402840784004041d2038030300218070040d5100e428034005061315000c1d000c5031070101d105003001e88843c100100080c0080c281030300150f13449122510991400c031125400c1070a107041540180240c54140d002002219510b110714049843d044d644c0f640104140350380c0892036804d0504842c1e218460303001e050425181002c0c907204913119001107039103980e0000b07010030540e51038030b01298480340004654003003080c61540000030010040f046803802405901c00c210aa41303444180300d01110020005411550307680c51a00030111070f8 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 302063417 1250 302062167 302062181
    0x1b071e0f0b060301050f10051903020d0311010c090b0f2101080a0b06090402010903031b1709040c0305091b030f060a0b090711070e04061506090602190c03020d02030f01 74
    0x5101c802198600207041c18210f0382c00410803400018082d040c00755500103045c1c644295241641c00344807042d40b41c4a00604200b447d40001e40006640108000740b60388440c100c0071148000009002c00d4102c5202111403803a1400b80c9401c2040810505040704010790042410022804040d400c1003520003113004242002d900c949959040301400d85c080100001c400740e4812011542116942410b4000078481d101c81e000080a0003198001442a114803000102d4060790112040d20b00e59007440c07900b021500310740d413018000c0b4140348094007494086d025842c800c00d141001050300c840c03a40d160310b04184030744146035014060500742c42041c040c24804503104207a441804200c481d00c41081c0701d0b58900082500c0c042110340c0002d5046448080f42d00030889200700150b0ba0742e6129820b06000610300c0345108203615100c4500000c4660300b000b80a0111400742c0c0030380300c0c243c07084810029003c02c029401441400b22040c180010b103440d02e10300f035603540040c00f164a4215007000d01400c407038603 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 302064667 1250 302063417 302063423
    0x50603011803111006030804031b15020a020a060c0f0221031201060f0503040305040b1e18090601050711100e0a120c0504060e070c150f0204030b1b071e0f 68
    0x3d00703103200881600b0803841d81003190690040025925603107a18006005900004041a0820310044190b0810115480c060200c12030312a404100d0300201035915011410101e000c4c600034940002d0150080710820f83c1c040c0c11051400a0003015030810041e54088550085010b180d0036004803540e030100b01a0112020700703164403c0d01c0d4105100944100118103106040007401c104100000741e000096408940b203001c0c0762038640108005502d0b03c2c034a581900554031001042d0400ea054841115040015007035071001241d4491b00c00441c0d01b8420481c02405001c03d8040038100b0b420300031840c1c500ca03840b87c40d1131912103503540000f0f50410019406151040001c01e6404144854102184002c041c00c44040142d40c2c03600310361020303440c80144908103103c2090300785020301021416210143c08100070400c0f0081a643d42c0200a41081c0000d44034000311000281035070a100000c00003149645107602d0414000396034010141050b480034514148503514070b000000d46500ca22201d41344 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 302065917 1250 302064667 302064677
    0x60815040e100b1503060d060e12160c090c0207030206090a0f0806041505060f191a0c06010b0702090c0a0c06020403140c010201060302010f1101020c0609010509070e06010f03050603011803 83
    0x281c507001304100d99004514444151404000340302d000d81da0010300e006102c2c1d028401043c060100f0030500d0610000b4810b03015203010010707508000e10745152040c4501c80c13050440c41c242303680300d031340080480e9440b800610144e07000e410140094a0f080001e040c040e440200101c00d02038940c28008040400c5501410482c0c1c03040b82404100a00d2007092010b03245400c2c801c00113403800b00c00280341080008074003400740444c1c0c80080403407025840c1e038102604511064941e01242403514400740c0c1d00012506039917020f00000460103074043c00c101d03000b003034004242010035200c0403841145503200143c41e0040c011120140f03400070702d80d4000381c00214042c0c0551100d2030301031452141000903400040c2d045914088007400181c0c0c015810b2003415403d4500788034405500f40740325009210b001c20604a034492241040310f002015040944201c14601c00d503070185a59003185612070320156042404603c40c1507284580610036405a64030500090011401000400c41100c001c141240c055000034 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 302067167 1250 302065917 302065931
    0x315090f060e090c060301030b090c04090803010f080610060e01091503020a0e0103020c100f0e0f0a0201090605130b09011413030224041208091522060815040e10 71
    0x1040b07a40c006039203c009040607110080c00000020300c42e1005000c024244102c010100e094880100140c00d900040074104000408907030a0020b02600248140b840450110070085182e00001c600729005060b1741501c1c41203142821010307030b50184aa04818108103220000140c8103035560035428204d1a030303442c0140c0c1c66002e400c00409007450396500d10706060042288502010700003881441042c081c010014641038200c20070300103003449601e00a103a02c0b0305941030362200c2c0040b0300381001500c00d884569000d9a03844041e60300d802610002d4011040f191010445092280d0040c00e11140524112240d40224100d0b1180c43d04074201c0b00034603020500c800c0c0110300303003810001c8500c42c4e800201d1592001107a4591002c0c03055006000c03028112002d00000c019004066410700c14000705003003051228030301804403c1d00101105114109607025801040d0752042e80c141c10f84840341e844a003141c0c4d901c45048020b9102d022101d070426944c1e030207841c40901c203000806600d6900e0001088107 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 302068417 1250 302067167 302067179
    0xe01180602121302030a0609030201021c05011701152c040b09010b12070306020d020702030304060507120e01081f0306050907170f0c1203070206030f040b070207150315090f06 77
    0xc2003000b804216020f28150520b405a03a00080400c07009601c410007068a494601d4100d000e8090086401c0c0c4070f201d01003007401040ba0580207541030b10a600310502030550b45541140c2a1440000c0262003940100360512014451a4403000350000c4c2104c584c010611002c4048a0001c0440741665035054800500504c100280034280600108031450f40e11001802d0302c171a284c0300f280c80700401c580d60001d803002c2980d480340c06651400360004d003074a0300c80e0764072480a0802d0303110900840302e1858801c450000c003400b81a19800c1c004043c0d680c82c0c1541e54814014003107012440c241c0201105031513001001802502945100c0c0340000090300d11180340003580b1034207007400030b607500e079030340141d2464210300700001211402c2402c12180e9040f00140c4111141c29445400c0000c0e400c03210000c00c01c0012000c1000e641e008600c0f42001c06603540e07400800300c0e2244442d00031140075601150358001024480d03001080041510a09003032456900d00d07000003260388402c40c4c00580d0f80c0700e100030000c0d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 302069667 1250 302068417 302068447
    0x905090403120509071a0c010e030a03020301030b0a050c07030f051c0b010f14090402030c0c0a06060302130c08010506030a060e09100509070f0b0d02040b0d1406180a0e01180602 78
    0x15403001403411505100340c0078502d1b00c0c501c81241c10400081255040d04100350407450400d0b80403c252580c641c80c028005010b588240070a40b600e00c0b1304000b10340c01d020584111446020004102400c00f05280d40c1110070803503e8020710100b240a115045145d100301d60a8860882c000c080005c5680d2548000f500c400b10440c4900c041c00081610b040300b6070b400ea011545082001c40c1d0059895580c032038200c00500500703008200c03910602c500f03c0208407099028000340c80c02215401c80a1641c1c10990058842000d0740b90001665030004125a0800002840d0003407440900480c60035120b0040181e4000b080303c2c81155948824942c0c20701041c5482056081030641010b8000a0b00302141c0d0104000382e40b2903180041c400180b45034880c41e8070790589001e05801070f5100c0da502e007043c441c000940042c1858440c40040200400d4052810040f08455102003101c880300780d41d558550700000b820080407442043d501c640360442103601414801403224840c070310050b16001c01e100980c00c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 302070917 1250 302069667 302069671
    0x20904020715150510020703021002030c0d03050108010b0604060c031805060a051818070f02030f040b0a030b090915040206040803370804020423010b070215130e040309050904031205 80
    0x1c01011440002c1d4140da5002c41d01205232a015949402c442c5c4180408903e18450403c0d940e0050181ca07460908041d816003140c1c0c101c0e00680028004c1e202d060701001400e00c01c602c00e42000c100c0013544500024002c0d10044194020b20310000c90a60381c070380104445502030f440c00e02c00500c00260324200c5400014405580c00800d8800d102102d035100000350038030802821450900240800c0c411519108004441c5002448101c090f103c035919203201c0c000341c205500e4036012900740340f140f808a003000d2541134860010394004000c500700c000700d621682c050140099802000400c00850a0001040107100b070106440301841c00b4168105041c0500e9074009800700b08a6209910f0807207194001c00003a0000d80485002076002804d003d096500403031100340ca807e00c0307400c030700000f04004514080c2171994020348120b0b4141000345003481c110301c41d02a800c2e001d003119500034803005425050860380305101e410304032155915480000c401c003e0031030f411030004580505442c5085028080c082d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 302072167 1250 302070917 302070919
    0xc0c09010e0903041206022106031e030307030e100203011401090806011202010e04090209010b0d0f050112171c021b011b050c15010806011707060e040209040207151505 74
    0x80a281040240c0b1920f0b4800d070320407601d003107940018250078044980d040300c01484001c10204180803108090700061041203600d248240500054002514081380d955140d03c4408005145140d4406009030001d044485889c505407081741e000e0003001410303200641c041c1002281c046010075000300010080007090300100b8843d040480100300c02112601711840e85a42400c09080f1155000e004c18010302c00048085d5009544000020b2200040380003408070030950002071000301e03110340040040d2402880313644840203079040c807040401c0c40324250f0403e0840b04a540b5140044196640c0c0c483c1c100034800b980c1d15580051480030206a42204040303022a040090003000e20403080a56801c03400d6001000344680040d00c11000a030a00403501e8080d020143c00391b09503115510203035212070900402c00700603030040901d064a07a002506c01c085429590f036121462110009002c0070350450045290495024070900e070004d0804004c968200c880c401000a440c100d0540c01c0a4082c0f01ea4049 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 302073417 1250 302072167 302072189
    0x309070803070f030e12010c0e01112a01021f060501090f0b031f1205060901050a0525180603091b0506090402030603070512070303090f0b03040b060d080c0c0901 71
    0x240300041c81004503500c6030ba010b085c81c50005c100c40000c00d0f2920403221110006510308500381c50300380c0d00003c0c126000c3c1c200303030b841c01304031074815011035030703644403440c201445042c1c00c180560128103543c4000515101032041e1528244c07484400b041400300e09200c0c480d0592145004e100303d580c40f031000e400400055210070392841c42c02c0101c1c0007510001d0302c1c0300c0c98480114070340c1c0400d003114004a00104001b01008a1861460401c0c0b80ca0300e1054aa0341003650070030011900c2884d040c00341c50300480210003090040718550000c9990b03074111551140c18011409001032201139100e0b03184005080b00d880101d030056403841d001c0c001c0301810040d0021440041c9c01070055031101004c1c0c500110090301d005030b498aa03040024505682c5a10055000507000420580003201242c081d045030312a890b90303a003850b11541020190406802003500c0d080c0e0a01c000390100d03403008101134010340090701c0f0640700d47d242d444a0f160fa40c05000750320141e0b48400c02c124000d041c200c0300280100146040c1d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 302074667 1250 302073417 302073427
    0x7020f010c1707031103090c010e0904030f0c14071205011b08190e011d0d050c060a0222150908010209030d030234020f06030603061f05030709020309070803 69
    0x4040c150702c0140341c2c054014042000040d190501951210b08040e900c80da58545910b400c070311240e40c0d01d040d800f03000e001641113491514030703080c9103419602031640340d1500680090102021202c1c00c4007a14296085600720854404100e0148036602c054000641291408010390400b9403d5600800c00ba07550102c1c240481d20a0940c481445500105410300401162000c49043d80c003030681400101840c0d4a009510302e614411000318081e00c203255000d81d841e0031507030b000688180c02a00105030040d0032004c0019024902070b401400d40f08907040034507e0400e58900458800001c9800803905072940d8000d601c45944c00030110401041d501001307605c3c0c00030142c0400d4451040d81400c005154002c6907802c208008171030030140c5884007003143c0c1c01ea1108c084103165002d400d100164000e00308080b450070b060401c41c080b00d02c59000030300140380380c4e03c44031903004128450301100c0c22480c01d0305c0f40214542c1e0b030074000d2030002d14070b10070056101e04284a140d07040200c07075400040c8a501c1040 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 302075917 1250 302074667 302074691
    0xd18080d0906110c060c090a18050106090609081510030b13060609060f05060a0e120c040c050403200a08030a020a14070303080109050a1104081b09010503070e0c13030b07020f01 78
    0x40c0d25544a101c0345044d603181c060100201d0032300130903038100b460041c090304008462509140c0c450f50490b000d554550000c81d95031a8150342016240c02940b0568106882d81d10200700c80000d11908104481d03954555a5a2078407958901e240541e11071001003c041208010b101c800e01401c00504007048042110340e19107100f0750604c1c140c52107000c0c0940c030b0208501e90403500600d02000f00c100054400400d11144000407130b1244c00198116200f01d00d00800c40d1141c0f48118195010b0348d074015a00024800d0b1120440d441d07080c00700d03480794051400c000106160310207101030a40081c90b80c0003890500b043e40741603122000815000f9200e030340300720010004240c0c040603103411100322610020b855120400c0c42406030031046110841100002000600d000e40006c0c1410154004804801070200b9282045105074081c4030b120f0303141d8031101c0144102c128500249400000d0445c07041d1912201080a40700d010040e0710548201e1039410800809640501010321041d411000810201c03212031 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 302077167 1250 302075917 302075923
    0x506010504090504061404080d0c030c09271a0a0b0a08160c0c0e0114030a023106080d020d02010c050d0902120f010506010f0c080d18080d0906110c 65
    0x7110b040d0a8540380c6000c1011701c4a554440d49108242c042103007158030381803c102a00e90302c89205444054031301140c68104500c28810181071150311354400056038034040d0000680b503200c00c0041075108400084c882e4100302840b40c400310008506403689081400820000c003141c1550081c8141d40782041a6a00990700120300e45d805007100c901e02d002d40128100c100c1e62030301010b41c02041d801082d580450310020855480c0d0403a10740182220a9240b000c00789070700c403103030980c0083d042440908501d542943c15480700940503821140d080402c00810554000e1310415440404560026450700c140180c0c140848007480c02d03c1d00007404a410500e02c001e0141c481d000c01c050729695510440e071308560b54408a00691610b160442e1341d6502e407298098020281542c0c0b0034080b075105c91002da8414041d10000440e039070001809800d010200f0008005084824081c503910b481300c109200001c6d0389100071784040310a05000050244103840c00340c04544440e54102c115150030311840c10120000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 302078417 1250 302077167 302077169
    0x1050609090c070b04030e130c080f070e04020f0d0b0612150d05030307030f051003201c0b0601021501080613060e070303020f15070207060f050f03010306050a06090506010504 77
    0x195207400d06a9a001800c1906000d40d48000702120440350a02090592080f9070038203481044861031819a5031960440407118a444407002041e4410005110182e030209595444221424580742c9141d401c4c0c0002c049901c180029280308101180350080c42d400fa200380c41e2550805d0f41c54901c0d042c1c10031580c0c080c58100420601c0c244003000800e41e500e0325030b80c0b0002c00e8a07500004898490a2590300034000c1d0050580d061412031414000800401e00104804100d94103c04040d0101c074034959408000c034030715150316030070072242014400c00004440411a816000ba4a80d505038200000024105440302d4a40b1000c1c1c0d5203070005028450020880540054031110030402d20300300d5240543c0600000003034810a802150000000c1c145c011906580000301c42050b59007000000f10000c0c001c1e0760954000c8016488040c052110901500c10b00790381d201755041c414100b081c44440c0d108143d00981044410319100c0c824070144004500441002d01402c20040c0315918103080024003a00407 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 302079667 1250 302078417 302078419
    0x30406020903010209041802030c01021c081f08031c05010f090506030a0c12051005090303011203050f03010303030c030c0c050606010f18030b04170a0903020d061b03050601090e01050609 82
    0x800181e040c1c06507402d5040b01e03070b410740280040c0642c61200030508500c40c0b0106003079020707008800300021035610109081402011000c902140c4286a030b80c01c0b42d0040001b0306001d5442c010f440a4a100c1103e801202c1c010304402008543c1d031440504da25800403510018100d105003407030014490350681c000304d001502d03416080019103603203001c0060b1600b00e40d0903010b4501100b035140401c001141c2a04180610301441c1111258902c0c030454504444048400d400c05801c20b000601c000c2081e03060401650b4040d01d040e03824081c1501d140000343d407080c0d008401095441640103507158040c00f44400b0354503141890443c00311151120f5859850041810381000329802d02c00e14424010036160384010300000c8100e10702c039221300d000040e070b0805580a48880c118080b07102c02c0810740e2401c44801203a01c0d40d40d8200c45140d83d00b0b2103080f40360804110762840d251503103c0c201400810b13020502c05100d66010505041c40320025081800039004003e00c0a20000140481d4403000e04450040e08 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 302080917 1250 302079667 302079671
    0x10b090c030903091002011d0a0c090c05040e070801030c060c122a052512031202070602070b070e0d0c170a0f030309030e1807030509070518180111030406 68
    0x42d455030880e0543c855007003201d501c43c01d469624032180b907056109003860301c00014241c0d4140c50021084d035881624240003881c41c20628024803d41d801508031065152241c2065814030781c0b5101c0c480c0c4207200455005c800203804800400a010f81241418024001c5041c854a49031480e1964912118844241c60a02000404c07501d842c0b6886001000d598030541d5a10100300740383c1c54170780e403504041002074603444036102850070204140300301340c0121000c44a41340035004042c0e4040d58245503c25071424480c0e070a21141010801c240000c01382c03148144860380492511700c50103041059404c0c540383c052510541407100007015075001000f07075541c8003c0741902c2504c2c00700b4a454481c007204002c140d0401c41c00c00d201019019081040784604c0307074488402080d00103081c4040c580030254801c41941d5a803000c01e240074001da0265401c100800c00b0b48200e6034445000c200c0c9411000030701c0c03900801802c100161104940e50f003840e0103007a44000c2c80301501144160700c00f404082d00180c0159 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 302082167 1250 302080917 302080921
    0x14010501060c030c23030409150b03090709090f06020316030509030a120b030f03070b011a0901050a0e130203090304060e030f070e130b0f0106180b041a040305030c03071202010b090c03 81
    0x480101c400081c0781803405d044a56550300c880801002d402d10880b200340e603010b10900840c08010040a40e031040040c04020580c1600d0030300c241000d001e00f642c042d14056166051354010651900095110b500c10307950f031000c068802d5200504681c002040d90b03103560014443c0040b8594401c0e481a4000d110720f00204940084100281c145511800714000074400002d54204110101c41024100d9405040d0380281c0713840c40b410410280301d82c6130f030b850020300d041199803016402400461495040a0114505c402c51420603004070b80c020340b0440b100b80d00c00708003000015801441d6032030942c010780141c1100c0502c408519540c140900035071514800700e00002d2000420700800811151300305101a000d82040b1b840c05c90807034401e0043ca000284032031540d445c8008a075440b18110741644019a01e402d103083c030300003070b0480e42000080000c1003c12001020420800181c035201c82402d010303560300d00141c03030003800714a407030040b420948e410000007502c1356071791828055200c1c40d90400c8035a25 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 302083417 1250 302082167 302082203
    0x32803020c04090605010e0705070503040b0d09150615030b090103031b060c0c030e0d030206010e060406090203040c092f071104090b0601091d04020f15030414010501060c030c 77
    0x4101c1d0341041e0424a840b00f51002e110701e980100d4101c54080710840315a032525641140c00f4402c1d58000b812076442044204403003000200100080d804e038a100280c1403040d6030391101003250003004c0402603030b02c0341010700c101d0001d43d001c05001c2c44281001c01401440b00040354455070144070150a104070b254000300340c11581c034400c00000380d1060041144c800d074071401a01300c43c141d80090300010650080c50748541490905a0b8205406800800c0d50380e290024000101100510090700300d0f4075a01c0c0010050114006580210310809404454500b0f0405150031102494040320b04c0181c5804420002c3d82c0c1c0b244281c95642d18a101e00c0e40d2540319080c094200c0c04500145500546000f80d0708044c000d016a0b10350050500740d030f034018010795035020a00080c1d01140180300103016000454014688000d61a500060240845440140204464045420840e019a022341038002034042d00c802c20302c9601c0c003401d200d0508100c51103a41e100104010b11526009200e2200440342d0b401d0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 302084667 1250 302083417 302083423
    0x603060f090a0608060612030313050705061c0507050703231207030c0e0402030709052e180e13030e040902030d020a0203061605072409080a0e03280302 67
    0x8288001c1e0842040c1c0c201600000c00038075040c4a4505240151404a1840d14000b124005002c0c1c03d000290704544890f1401999040000ca04460611030900d00282907120000a01404951310242c1901c0c220801007960580d46d00811802c1080001c0220000080d017040412072030004542208444100c03503095942e1900c100079105120390318010811040c40d42c1030700a1003010540740c7e6400c1c440c04601052105038082903401a02051050505110700d080100110b140c0c000314801200c041180822140503400100c481a80024203040d03003410f40e0140d90842341c0051800b54442c60303c070700d0241c1c0415030701000c0200040402c034031600350004a40d1590440c4134001d40080a455000c3c07100c0c00082d50b10f80c3e1000e002c03070103801114001802488203070b411000c01a010b031941894050315580b200300c040d8504840d41d01902041c80812480c4001d03120303100c0e0003403042400ca41c0c0c2e4030010802400ba100c406404d2031080e400800303121700c03001240131154040042141140701e225210310b42607007 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 302085917 1250 302084667 302084689
    0x81513140f100902010e0405250509040204060306030515010b0409090602131509240f090e0103080306010809030307020703020f040209030111030a2a08040c2c070201060f0302060306 80
    0x1015102e074803214074049034a0750040300040e200342c980c46019002c0000780410340d0000c031015004146c000703041c51520300742a91101e101c204a480d15034600340c140400901203800a80042d0000ba580380d81c00e00420004000700c901c004d8038648040b540c0d40c9090842003180c481c50044061007030301c44000f20b00704003254058400d078100840d00c41c0340090315042c0110340d5100066822001078516440052402c00007070004500130b0341ea01c40d0480c00c0d41080420750300c010021446c201002681c501c0001c2181c00d8800707290296118003a91581e90400d00c000512000c0c015207920820b0304100140001145c0014050301282e0b4195a280d04100003540082d000b4082e0440e856015400e102d004150f141500c8021440781c0700c019001c002201014503a08440000741d2546010b041240030070a80290150090903842486940c2203d6015201c4481d10796448500c144129070681001c424010880804c0c846588440c245c40204407051404864030010600d0b8030010380151000404207913544ca0300f9200700 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 302087167 1250 302085917 302085943
    0x20f010c080a02010b010f050c0312060d020d0807060b06032202062208011b082206180b06100905011101020417240114040e010e0d0908151314 63
    0x20b4545215400181c080e00ba2084800d0015a84002a9810f0390268060b55a00c0100c2c000942c01c00081966655014070081d01d4940d000420020000050f500c4150702091640b00d00445519420586080000e40e0002d510040c461401407040104e4041c0f0055030080042c28100080c020039110700200e20345100c0c107004070059110300808004407207001a00c1808850380c81008002e00b1a07080030031804040d0600d04900010b40490114840c864100120b14142c07003101c841c044151790030b0380d80d071007101c1c2c01c0c150038040380c8490340c60442800307401e410655000c3c409940c020f4034041e03c00801800c10001c1d00039107040c80003000182c2c04402d4254183c4000d0002e500001c80405036000c5440e658210000340b0b0148541503400c004540d025400b0100e040311008404006584000803c101c090301c03010113100010740d0380c4d8031107406001c01000249014906038946941050504100c0c2c0e040c07c80c0d1419000117002014140905108409038415155800c007054402503c2c2100c41c06040c1a1108400 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 302088417 1250 302087167 302087183
    0x51801020a020109020f0a0e011203050d06032003010b030d0c0305070c030b09120c19030210060b030610030b031902031203010b0d2711010c0f0804210f020f010c 71
    0x12a450b0701540103900c114006c443c164600355210041160b140160f005500c0c0010200340100b018541360b04400140ca84030307043c114140180780d41c02c2c00448031254001d460710040804144402d0680d178904109003c0705030002d0084109810103c1e07681c00c03944102c002000003030046041414410001c3d2035600b5400f08207010200e58074144800402800d407101110307801207540307041c8406200001c070341605180710040e14a95030140150b0003441e01c500802e03029030054019034501c1c3c80340c0f8070805003d003da070f948664403818000c052140300d00d602602c0c242818a041c1c10010103550000300c0a640114a04c0d920035140100e1007ca41050507512090709151000300004c103045a40d03201604c00613982c65010040364034082d403072410050303202054021146640c82180e0100e10081c101084c10780d0107050400c2031020f00d80e41d002540b0b42a16065a02c1d030390125041c04500845420b5012016143c003140c0e440020035151249441b09984000384100c0c440751801035264000d44010386099080700003 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 302089667 1250 302088417 302088427
    0x140906070c090203010504050c0301120f02181f06050918100803030c09030129040e030c07080f010507090506190905090a0b100212040911040f0b0a08060906100305180102 75
    0x1241000c1c4d003080c06454804c1342081d0010700c680070402c068a048030722101d04181101d04a482d4000606101c2e003043e45c10042c43c1c1c0198024068450480d801080080bc03254013200c3d080010007081a0590850001c10900f005510b2099580b800812000c0c1d1400000c0d000c0c0b42c851100e083c40501240c8d102c0010345c0030200800080c071031030801030005c0b1941600280807520710080120708600f403810110a4624001988000d0341c00e00e94000f1307280a0310582142e02d845140c01e00d451030000150721500319035000309160406010f0a0213510f4001e005414400007590400e80021050b02806403020301d404007070704050100e0740c410a0418000e21010301416401d003003100d24200a4000601c2c550302a0f141001d0076410b4034070004800040d4088404040d00705400c11019401402003074a40280900c818071020480000f00e000910003410f030350361742075600d044104001c1d040f650001c14a17403290000d942004100e440340194a0b11440461a0028051b60341160544508003004c02c042415840403174 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 302090917 1250 302089667 302089679
    0x330907060e0f0319200603040209010303030b0102010605120d02120c0d2105100e0708011a070512120417090a0b221401020c041b03090c120b0f06010f140906070c 71
    0xc2485c0e01507802c9110f20030f0002c0c2c440600505102c00c1c1c90081d0058080320040010074482d074071031494050148008152281e07640d0009015420010700940306e50401d002c2c41c03d00c02d4041054444001d01c0300203050030701e4070395490662240e141c004010140012070003a414504c94000211440c4075101401300b009041c585541c08580400e4080c0003c03062500022441c0d0303e00811000d8101d03404520900984040600d0281c05500544c000304c82c01e100e60700d600248280103074040c201c22800070b50702564034031f450305141d140101d080307000908480080050ac2c1c01030301ca41c0401d00a541d1200c501070b42e41e6110350405083c81034401810b444485482501264200d020103a03a980024241d00f01d40100991204000032680c00e01486c42619440d0a00c81440300d0080e0031485001e8000c1d601500420b0b901c100814044c032803140100c600c41440001c22640c00c00242085030000028601001c0340c407244c1001600c403200400c001c51034201c010a10f002d0641d0307070404075100340d179100d8000703004169100 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 302092167 1250 302090917 302090933
    0x30c02011e120f0e0d11071703030a060e160302071403030901060326030f0912030f070206010b070b07231b0706050c03070311330907060e0f0319 64
    0x1882815001d0078110040f071204800d000c0c0500c0b030310029001c2c02020f6070b0041c00307643c10030b02e241d00340c1300320f00443c43c0001d1004144059124405420340103555a403400c560444c0469069170800064030345880c0c00d0013260cc200010030300c80000a410016600c04050502c5070100306c5804810b0810b200000801c842c141c2c041d000501201d01c40c101c00d151520030758804600f46420402c007480c0800013440050b1014a4606440d038000b01d840064031052001c1420710041d0b603104452074840181d000d030520004550400c120383c0141b42040311503003030202075601d00c40041300281003181084000038528580031804400310b210103142e07000e4547c1d280448160048100300401e0850b909000303050000400f5030181007294000c0c031008004e0761a007459550265680d00c40c4095484081c8036011140481c403650705034186102c40c000301002c406400300303c409607074031a00130704032501504114002c010346904102e40d0044a00c2c00c89000740102c00c040041f903e072064481c6200d80030083ca0110b14203221001d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 302093417 1250 302092167 302092187
    0x112051305060106031a01030f110703052d0f03100509090a03030615020c06030c070605250c030e12030d06060809060109020717030a02090925080112030c02011e 71
    0x145042d503105a0b03a48005500701d50000b4a0150003069520b806907031507120b03501501200b2900000052007400c440c10340b4015401554046000c140001144100d8040c94460340c051000421340c441103200000103400094007800b90355208216011010554508100228002a11000d454910a0b1400000c080d661b540010020b5012034038210b4041819a050070700304480000540003045806100b90500c4004e42c00100b00b09200c500034041c03c000546d2900466001d8620300c031410000c05034140b01004140c1d80d080300e10f030600c202a540180040c1e000800c510207144100c90f87c15a90082d8200141507120f00f002c8941510f02d42940800c0103500f2452440c000e80a04c000c98a80c0d80c0c80d58020003ca00c00d0712005020703805000e1414965000c0c0704002e41d80f011501c10058185044180030401c000c2d0250ba80412003c61200c0d070b90244520301101074080e22880c60702c44e4695140040a102d06c0400b2407000e010000081d12010540e40607111141c10031460f60409c2d0008082298010981012 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 302094667 1250 302093417 302093423
    0x20c010f0f0b030705030c1011030c03090109050d031e260f0601080103050a17070515010602061003020f09040503070b040b070e04020c150910020a020106030b1807060c0201120513 79
    0x42c100007640c4504000076180152540600107148132281034040104507551943c81d03e04001d40000803882c002414001340038421100402980ca90482c0c50003d00360089a8100074001e8081196000110b07500500410a142c01c1c2d14503801050144841182e4480b50100c5086c00c0c0c640d141000142d200c00c1030804c1d4451800d00f07400040c43d40301c8030011995907800303100203041e0703501c1030600d0008900c00d00da80d5078508a52510042c54518107039035031414800324002458203004040c004024654040c86504da111001c01d4002c04160b0460380018035034084c0350300180c0610010000602000402c00c1100c91441c1c0208070403149252074030346151184c00840ba400000742d91103c1c0c3c0d0f02d56007003d0090310a801e06142c00381c244204410000c140e9040020310311807452080d4501c403202d05a0520080201800c00ea0020600e20304600b00304030102c40140049007030311118001c40c9003c0f0000b04020090781d5062500c3d181000503400107d070641a10402e412f070903442c01c4144400a07520708010781020384 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 302095917 1250 302094667 302094671
    0x60906150e060f03010203060d152a080a18062c03040f0501020303100e1009150503120a14130503030a080a0b09040b061c080d051e06180a020c010f0f 66
    0x43c1c08403d142c01e07404180d8034a82c0008025810500264460071002c502c400610130004000805080c694140b2a496071032215001c0601d00303110b51950b021000e107920042401042c0904e00c14000610400121801f0213010f07076030383e9603003c7e035102805070550036400c000087c603440840c0e000441c5901c0754071034840e022030001003c40000e910350001c4203407446001444140c502aa242c035541e5034542c20b0080c03030300d00000da01c0ea1020956484078880c8201b881c00800c460321600d4200418149030401c651005083c0101c144550303130099600100c1c0c841d01003c203011294aa905400070101404401d0700200c1d031500000c919120800da102c14240c1c4580c03524101072003240720a4081c801c0d8084143e4019082d000380d80000f0b41c450030070583c1942940032001d103580700300c90aa240e00d815a00302c0ca2115100320384070b40a202003000b00c0c402c45a00b42c1c0c4400101401c50038003100042c240304601800100141d0b0400000f4800b80e540d07815919200e031020024850b11088142c000000c080640802003c0f42c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 302097167 1250 302095917 302095939
    0x30105191806320d1509080301090606170115021006030809091e0106080603100207060e0d1103030a0f0902061303020114040305060604050c1603051903050f04060906150e06 76
    0x407aa40c030440702143c02004890089203845014450203940d25402903500f500841200d4030540c03024030601d4a12402040499107070350400650805480107640300c3c40400c85410001d00107005109850ba044401320801120381c2d0107000d02c141e0400400c40d4140006900e80040003040c80184001407011036022070b21880c0b1507039030002c80b4502100d1000c00804051586005200081c003130b1440c16041000101128804410b51030f40e041660700c015021943c141d102c952954502c441004403403a1b640b56801c000768000401c00d111740d0380e4040105103034841c581b03410100070120803641c04459542d401030311055130385029001000051003d440300701c3c000b605c1c006c6c0c60180c20071a1b205031025240d0201c064145615148200000f41001905e90406480300704106801502c0d00500e5086e0306109445090b101d160f00c0302502d036000c1c40c1c04404828035080c5070802868078822500543e0041c0c0c003003000903c0346080e007001d10042680d522701c41081c0880303000110349a0f10105c0310a10440d42210704031215 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 302098417 1250 302097167 302097209
    0x7050a09050108010810050903040b07050a060c020303430512010807060e040504060605101e0315060c0f060c020c030f032515050f0a0f0c05030105191806 68
    0x25000c241704265103904112030f010704c1401942c01550300804000100d030300707164842840010b1075105540840d80c9234030035160b440410016014055610581c0c0c000b40d400c51820300b1500c4207a50000d034000840102e5580e0f0580d01c00c104100c0ea125180c0344070111020b404c0c907440050b040b50310103080c01c80c240041c0000028640c0300051240c041d10b00b199100900080c11201b40006408003070821502c0f5500c0d40004112a11000741c50003052409507030344041a86941070710085125400e001e04201410b00354011641c41e1a01c10840c01c0310581d14122a1042e0303e4107102d8102420b01c0310060441d401d004490f07209a03400115243d01c14412010b4810000b111540c0c15924441c14000302a4010340310360048a00080d2180c0e1110a030082095030428800c4150b01300031104200d49030884641d0500503c50305084502c00c5529211281300200505864110302078514001481030910036400804030602c004002c0c503082009088442081a1103038198074802c001c0c1c00c2d90b01034803680d904134500103050 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 302099667 1250 302098417 302098427
    0x150512060405122d04060909060e0103082b1d030310090e10140708091516030207050712061b0c030f0c02060307090f050f1309021807050a090501 64
    0xc42e480340062540724112155401c198020403a02007541e0400c0042c1160800240c4400c1c00c0311003484802d0b5030f29414880d000e024a00c054208110700341c90540113011040048564506580c0c0041c8001e403158580d1840344202c1160040c07808030f5030852202641c407481030340c01c00941c0c12101104404d0300000b40319101e40e240000c82d55042030584180703082082c903810b42e210031b0300350001200381c0c0c3c0301c00d10741c3c00f0250a9030002c0d260300c81500104010042c0d01c0340d1140380103411000603000340500212140b000d1585920180c07010f000541e807412004866070180d41207070203240c2d006013030310307545540d4400020b200c80000c04141c0d055402c1605440c094240c000c1000700c484069210943d83c1c0e40d080e18102c4201c0c0078035039050180111856008003580c3c40342c0181d84a00040c2e62500c50903400c0c0400c5816203082644814014112010203802175900c0401c910060b107210304002544e44a50700014060b240341300b1004d0301d404480b005100e8000e500000410001e089900c60ba9602c0c1e035550300440b2 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 302100917 1250 302099667 302099671
    0x70501020c1818070b0901020c010f08070e0613032006040602071a040b0c0d020d0207050303070f020f0a030807140a0321110301090e0f0102030618040c080115051206 73
    0x35126195035002c48500700848400c60f04010074000118081520340201881e240035a004942010000300700e500c0c256a040042d00d90503030080c41c040e40001001c5501501c860005000c2405000d08040c02d500e00d0b458030000c0e91521384242e00c04041455032030130101d1030342594003003d0725814284100302d000c2c0c1c00c1041c211022124658002c0204510b081039903034500e100d00500c5020018100710014216001201808400328100003130842a00103040181c5460070a0001c1c1042d500800010041e5a81c00301c00c0e0340d41030340c01a082140c005c3c510320004d82c21130028502e1940c043c450501c04828068508080c00945120300c03800b000c8901e20860341c0f540d500d46d850000f40018440310301013009000d00005401c0c0030f0150800440c48911190155400c2d030400d80101040e9583e0b404601c0342c0c0c0904000b07010500b10010700071807850801c9404a080500032000c0b041500685201047c00c02c1a030510310b00003848094000c00c40c030a0101014007500d68248070b501c0c4507800440a443d800756020403014 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 302102167 1250 302100917 302100919
    0x30c0405060604050603070c1b0602101a010e0103020c010c031508031e0901051315140310051002070b18040c1b060c0c021201060312020303010b04050904240b03070501020c 76
    0x1400c0a140034100503da501c0105010100300d010403c8230005040861042d1144d00d00300c00c0103c501e81490802450f0010140100340024100440c00c2070710910382c4103209110200b860f0002580c801c1c0c10058001c0e1154070f00e001c100350b18000d1720360201030b8135078012007101065084540c1859a20380704107a03203010f201d80c1030003c403003118480d40723030035845800400c0c000d041030401a040100488041c1c6250000ea40444660300e805410707401d90651001000c40440404440141541404030701c0f443c4507106405400c0c01070894200d50100e10703000b00081e4004051158025545400d4095545101d04140c4a884e0156050034500c51045005040c0d15448070b90b2031081c074901c10b10a80720100902249910481803280c440b0718000962035400d6010107441c3c840c1c0000c0b4009280d4078203401c4141460305044110340042c0014400c43c10072804880858030215074820668599041444a01100c1000c2509900307821481c507004100c690460343c14a0070440545038903e6480005a89507240d8a043c1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 302103417 1250 302102167 302102179
    0x10516090b0f03041505040b090105091902090903130f090f1103060d020a080102040e0906060d0b0f04030302120420010503011d13021512150105040e18030a0905030c040506 76
    0x408480d40000c014591103805011844c61a6207050070840485d11b0644061b517a00880c0700400034021424090540c20002400061800002c100740103110302000000091041c0400d41c0461907145e000c03c20780380782042d0030009102142e0769001d950310702c110314071480c81c03c14202140b20745130941e24400c0f285061001a140b51a584c0c2d21800c104003480240412030f40011090800718a04400b44098006003070113451441190a00d0801640340c0311005000510545000a550b0002242d480e800c030b0700105902030700d9410b519a460f040c0d01034020100355013400b0846408020078412000b0b40040e0042c081e554007507001595100440d5035100c240a5400301803a07450382c40d0004144840615404080d04000401c001e41c1540080c468600c00715800340c0c0d69601041c080000142111050381010454242e8100c00d034610300060214001c5204070001c014141c00060801c1d28440306030194442c4000a407a0b4071905da40c2d020b0320324210340c004d55000b4810440420081d04091040e01d02400d001084 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 302104667 1250 302103417 302103427
    0x2300f0d0e1909060f03030801090603080a11010204030b10030b070201060509180f15041502120c0a0c0515090f1902090718090207030f020a0f060506060702060705010516090b 77
    0xc0c090712544003680b4000040c00c4110000346100c6600c42e84014080d1060486031403850360400034450703034060300a24119440c1090400024041004451030b6011300e0404941c1c02010301c0401d0300900a0350f00142c40f07440c0c80c104010540b00c214190b0002ea13846480051095181d6020032400ca401368019644c104192070301054031081c2e1130480207450203841c2d003141d822045010b08542821811a01140c40b0217402c1c0c144010000402100100c42c41002130860421a900041000d04100503126075101c1000060800d665072190103001c001c0c5400c9800c8402104030009064061003040715861628000c0c02c0500c041c03480081171004100c0784260745c02c0f4132000f01d0703000c0002c00b1030082c0c143e0701403054101d48044902281003020006106100005031a0640c42c200584a042c620030b4080c02c54002ea20010005489400c0c0300f0102e507001078000555603a0f010101c1c0551155420196011501040f8002046815000340d0702c101c0d280312686812a003062001d40d49031096018182c810602400 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 302105917 1250 302104667 302104669
    0x230f07030308060303072003120c15040c0803160501061202130e150a09021509010c240e070305070e010b0a030b030c0402070605040303061a0f0702300f0d0e 69
    0x84203641003c001025a0700d41020740e515181c017070712a50340f40c17000c444084090360214038051004098100c100240e49203000740c000c145507180c000392418040000000710208060050b20200b5102800c020011255904007201c50341c107036000c003e00121041d6080c68404100c102100b0012000140d0207001507070108103219020300500f03141810083c0c0d41c41501400c04100500b0b5110500034003c00c4800104a400c0c2c0c0148942d03202c402503100c541c103a0800c03034001280d90003400c00c808641c001d24a40b91829403078503c1c800007003003a4240e21945003000b2015080500104925089920801c2140e4606507034a4040d0202a801d10885100c2e8500b48401d1705c0c141e020703400600c1c602c00010140c0308012a03030710020342280c02900085d100070381c0e288100800c0541600c2010054000180c1c4146901d08442140d9680c1c4a02c008100100310085014070031900c882d1000f212003030440c0c40000240c44c56044184070403050381c13180f03039107031041507100fa61014021501000039030a030f540382012400240 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 302107167 1250 302105917 302105927
    0x40c020c13090209070f0201140609010501050a1211040f14030a02091b0d1a150906070201020c060c06070f080c0409052e0501020c011b06110d09230f070303 69
    0x3111040705498100d004010b07540c4004643c0b092140d900c0d001000500c00c0c40003400c540c80c0252122010741d98505006040d5508124941115070910f042c56403001c490710216590112103104400702810858003c0c1101c46410107001030b60400542941d0142ea00c001d09a1301d2011900d501e0f1f0542c010016200240c24420400d661020442c807801c510300e2010711700c180d400da10423095070003c1c940c2d400407040b0250300c0038912120020b0480b9601c4107000c10300e0f40292103100d1007a0440c8104070002d07012085900030300010840400040c90742e915034408203a40c03511910125550800030303800c5101c0007100c90003400428010b1280e46460b504280c10708200300000c00010b0401e844102154100c01c100e0f018858280115050149405600034942800640b800010030b00c00c03814080300144110701c01004403030340601d9a4018501165203040c80b00c25078114171034070240401041c01d20070130000307104104442c102c203106550020798445440030354980d100c2480108a0700550055441040070078820 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 302108417 1250 302107167 302107189
    0x140708060303071401091a06132d020403030e15030105060d02040e04050c0a1d041713170d031a040e10020703020105100801060b0301060503090717100b040c020c 71
    0x14045918101030b139201e5120032000c11003020582c1e034560b00504c04020b4440c03200315124011070040030719170800500042e500c0e48002803280305c4075505c8040c000e204904c00c8001c60307000303035501287c900c054661110030003175030140c041500400e07808032134255281840101030160031800a941400d5900f1314080110550203609015000e0760284000314404512401d40c601544c410002411100d1904d0244484510700ea8003003806103200d11405481160b0080358554030640c071148080500803024100c0741c580c01070b9444049511100c1102103040001d103403500d5000f4091004640e034001604004805485a880042144c3c0b505d1100350507103410550811038000f41200c0c20380709681c40c0b0140400c12600081d1083d0f006079100d0003400004941d01d103241c4098202e0400038421182401e400100f2444184200810810b00200185984505100c9030000c0c2600d4800894010000100743d43c2c2d80d080e03c00030301d28984c50403442c11058a014440d128108405802600c5151910010003050a0075 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 302109667 1250 302108417 302108419
    0x10e0f010303110a02041d0105090607050a11011103040b070e0f01050405011b060f140f0618041b170f07080601060f051209010203180a1a040807050f0318010314070806 74
    0x40d852044c0040c1d480d8000c0760003181b4980130031110340710b14007029400e494000d088081e80713800c2441482207156100049507048409401d000384034101005a40c0d0040091928050743d01c9004400d2004101c0212205400742d03407940e4805892004020811240c148070054043c0452000c010400c1b041d405540e0f410908454001a001c004209403a84010356802c0c40050f41d03126600c020403c6000d07111404550040740c007620000441c6400d130f020a02100320030017142d041c0001c1500103030410403003190306207000c40c5c828a084042c960702d020300c00403001e00f0840784915000300d1950040000b000500001203900c44001020325901e03142c4250b0301a00e29880303544c10814104500300320008041d102c00d0091040b0000165213161a85200c00301410300c0082030090f80202040720085102e40140b0400071200c0c002e43c07441c544940c6000d00c0341c0e2203907103001002400b036400e0420103081c011002d446407040d510710750b0130b03c0901b5800450441f2076428403000c0f40000d41002c288003d1140150f640d01c440 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 302110917 1250 302109667 302109673
    0x3180c0901171204030f1b080f03040303030c18150905150d06060504120201030506060c012405011112070611040807090b0d020913020307050d0803010509010e0f01030311 75
    0x40003040c56260240c101c001410341c072035150b8280c984100040c80340314000c040c5040c1443e040d5507619420944281016105802008034803000c1b1080c040540004c2028004440081a80c548811303101e0300a880240c0c042403501030303440ca01501038294000600540500c140207a810a1512800500101c0c807d8040140709034010520f900c0d038060314840808007502c3d6580700c0991100100540351150803c508105003440100205040c14200e081000d40c24207020038a903a5400c04100240980c840b294025800e200c07421400c01610040022121a40300602c0d41c0c683d22000190b0b10016901c05003049503000000d00c841034400c0c0b1010f0010710344240008940e050000c1071030030280d0083d800038444ea80004608100b184020f02c40d00d5030802c02a40c80c40c410700c02640001e00d0307011005120b640f41e0000c2410380300855405003c65400b41034004e001d4002d8070600e0401000c9500240900b5000301c45890004c81c1d14104140003e106507200703a12100c3c0340e070039030b9001c84080d611900c030070300144 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 302112167 1250 302110917 302110933
    0x7020d140f01090b06100210050c07020a03120809030f1803070b0a080a0506030d1403060103141611060411010507050a0501020a030b040b0108010b04141f110f120318 73
    0x30405100001e03940c0d240030000700b0241d00c9401c2c800014140030305100d01c6800210514100107030007042c4002d5087c000c1130700003001e5451600e4000284100500250702480182c008000c01c007200c0351460009203203588100c07180e07480125583e0340388120306a07100d5154080c484034400d6010450640200400641a105010380d1030030b058405400040007080810149002c118440c0e440e4441e9030b501c00022030050140207036441010348140320007460903091010000c00500a40d00a400403401c00e0081040712101d40f4040d03071005040d0b1440b1484000244000c001c0f600710507000550030780115003203044119105030840066583c1da101400880f058043d4084020100d8004c1c809445a050300c0c5d1030205103202c0d00010401241c1610710700d14180603032003006006c10034114080d141030b5001501c410a1900344140022010345e40409152a4624544512554260302502d111052a5440111481c00b0340b00b401c050388801c0700301d06006c40e0140034000141c100884071026403203002240b003920250 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 302113417 1250 302112167 302112203
    0x10030b040507020105071103120103110402070c08011506181203020a050303010e0403090504090c05120102120a0f05010f060f081005030d0c02150408060112050313142407020d 77
    0x40d071011514440540d550303108121010f900140c0440c0c5480900c0c02540c580200a0034114040d14180400f42562206000401040d19a94111642140c1101c81e0040701d40e070342c1110b01d029007401c205a240105003200001040c138060101c020801640d16a0b89000d9030400b8200e090004003c0419400c43c0305a41054011980c240003d50281419039141c0e0031074909070502500841a0703611203030249103030035091004603441509610650f40c08641c4403625400c10942c2e2406030046066604401c0707105001e010790b800c500c0d44283d0035002102e500740416a6600c1c0b0f4050383c404688141c1000c602d40c2440010701500ca4000580d1041789603401c7c07064252508040b900d060300410107080403c040140346801e62410101d0740340e0f0100038030310783c40c94a402c02c030905032648010310a501141845a03140c40c1005024410394000104240c010072805a0710280009101d00040080f0702600b80c050700c000303105241c80000329200502442b624501100b40e424400154440716044d2910428001c0311208 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 302114667 1250 302113417 302113421
    0x4020c071802210601020c0d030e101107050402090306040b0a18050d0210330306141f03171c02030a1d0724090b0d020703020c190510030b04 62
    0x1010800110042c3c488240720f11041074a29481081c0d0440341400c81003140700c3c1e0b030000386450350480c15035401c0c14030122860180d030030b0345401400e550f00101c4000c28403000c0d42d0124004600b10207060850341c0441e6604207000c01c920030550b81680603003003140001c000c5040d07041400d80201c40c5a50001c1c652220300610b07000c040c400c0c842101da80e0042e00400a6403981001001800281072004012622021810071110180144409a0000300405100c00c544241307604000441d00101e060162800340c02085c0b4400000b03c8842c205070410321104a44007240742c040ca01900d911071316600d00349000399504041c41d0020607107411a20b4030031112010610700b40c00914090780d4010404070341c0b4211100e203051910401041c400c0310b035101c0c3c40200501050590905105003c204400754950154042250410440c0d089a1114071000628540014581e4010b1000e50300a03802d8540c144005001c000312490481060b6071401d05c005400d00041c41c0a211882210105060000d1905104000b04003 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 302115917 1250 302114667 302114699
    0xd020a060f1b060c022a1c0501060801050603060106020106080c0d1b030b0a0b0603040f0b04050313060e04050106110703020103020a0c0c090509060708130b060f0d0506010306110a0c0204020c07 85
    0x40d800d07440704c1881e60303c41d80402051816138808050b003500d403800d45031031400c090745100c00d5510803102d00c0d00c00070800040b040c0c1c000210350044000d11081d07848107880e41c00ba0074159a10360080c401d130000090b0451041c401c04055400c0c00001d0140413920504001150329402d42c2aa000c80c5007400800d04240e1040d81007004503c61a81071110349803440d09a400c0f55084100c02c1d0141c4010020032000411290001001c1079201c0000c501c40e07140da0409a1441c0a072028048241c903001d2070228089401010142480000701c8092005a80f642c404071004d4111810080840c0c1c080c507c1400158002d4007e401c2007202454112451001502c0c3c0c940c40d03150640c0202500c1c0da8410078010700c840103100c020343c01107550a100c17400c1d042c0540c0103405000034075005014001520045541951130914000701c8150090500345400343ea41015502c4601c04e00c000c070342c01440c011240c4010348021059587c514510f4440101d121090740904c006903110703012404250061369000700c1d01c0b01c00464285 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 302117167 1250 302115917 302115923
    0x9080d03050709080c0102061603241e03050c010f02030c071e050405010e01060302031302090901051504051e0a110a17071b020f01031b0f08060d020a060f1b 69
    0x41640c2c101200301030020f08060f00010030507080b16203040140e0b600068925008107044e07800401d10705140c03004800030300d0030f5810a0140108800b4034140c15110081010507031b413000c501e1280c05940c0b81e400400401007488001d100760001200d0044960082425040081a80c0107803482c085215481c10300b0440950080d00300c0e00700e0000e090281c102c041c8400d601400302594100a03c1d418034071041000c04052240800f01500000024515403070040c400420a90150038010a420030b82075850291104444c3d20b03201c0d0402da082e1040b00d00d000e01403240159085c100130450354103071a4a0081d40c100c020007496050341c854002c54030f408200c00c002e100150b0f8995035a014203800712900f42c0b400030301401110821840301903981040340005911aa441d50407601113175000444001039004d844016000da48255910b0302841c01ca46d0841e009511205042e0b8030306295945020800480c2c0f15010b01c0a500048058814000b0f14042c07020010724178043d05042549000c281c80d01581c03190404021 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 302118417 1250 302117167 302117171
    0x109020331050c0603040803131a270c01050405100306050d050309030f0106230d170301090f110a08091606090f120201020a24020c0123220309080d03 66
    0x1000600c04180002c3c654200700300c50252440c10591140075450002030041c022031414620b184080000500c201c046494290003610410724040c411145130640d0800b02c000c110b4070040704801e2602010074a010394400585485040609203004d1284480f0358480c0d01c014140e030350310085400d5aa20701180c0b0f94510400007545e03500011000d042c01c000085488410316030404809000c2c101020b0b540c1c4d070900428041c0c0c0d0000030b01d03903c005050b11b526410007904152011854219540b40306000318182c6540001c1072003c0ca03403d42c0c8003421038000100030814108244a50200903205030742094106000008407114141001b8000f012800c0f0b5500c000c0128001c8507040166800401c803100007081c1d000b00c542039440d850f8002075140c032035801000306046600c01801084065000c4132001c8044012011074a0b40f0a082066000380149041140e0308124543c61101d05441c81d039401d845051801500705040100f1441102e507100b100500f20705001034880041000c140070004000d030042c0b15900 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 302119667 1250 302118417 302118511
    0x3030302090609031b10020a031b030507120207080c190b031302100e090121060c0908010905011a0607080d09170a030203040303050105010905061c0f0c0f170f01090203 74
    0x41040106c461003c2005540150039444041382d04040d421032810458500c1644c10f03000703480d04503980e114441e0000d1080c0c0c030000c9241010b660005010080d5403c01044074090b82c516402c1081082d400c2c07511110101c00040b09106c004452406180c208540390380e840d8161400c0da0000f20b00152165040c00040c6001c4015003043c0340c0442c00600401e088001040450940d14500180c2e400c80e1401411440d200d2000101d502d101d05443c5004210440080044503640d15200b03029103c909084040d91031400302020f0700340761007000c60b0942940300b510246450549250b44c00581f0300c004040c1c1d5115044210203622603030280091502c9d003801c0da00140c0d42d203410300c1c1c0a03086036810f812003810040500e109000d19280da40460711a40525060b00303407031103d0310001c2c80260100107074509050b410328021105d4550080300d00c030603100c05500d825100e03103035034049548540e1080b031303101c0c1941500d4001004009400d50095800c40d68102441e2150b0302120000c09000e8986038500e0744044880079 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 302120917 1250 302119667 302119669
    0x204120b040605060a240c0203010e0f06150d02010c03030212041109090106080c0d0f0c03140f01020a020a1707140601090e0303040210030e070e15040606020a020a03030302090609031b 81
    0x41010381c400000c0b40d00c40e00c03207421b00c01e81a440d03040d084607000c46070043e01c40031501e40b0f008003158940140d006000707010890000f040c9948452408031200001c0c45400040341101e551121105560080a00151247d000980045546604030032064089c19802c01c0a500255000e89820380f00e0781c06180001d406e41c04070014085042401030590801d41d25149042c843c10301c02044280e803400c0304032480c0d0f9200d241070600581a2854100c01096010084800800c02603030340c2c2c0f21300038040c0c40c1c4141d0f40303042c0610105500380c1c0705958403000160001405840000c0083d6840d5a0900c249000385050060603680c1c075501075400080703046035a0202c801001181c01500507405071140f00e0002d141942415404a10050300c0741e203180040c5519130401300901c01c0100000401000c0154100006041c41c4a80d400d828044842207800b0303e0078800d02050403800020814140c96018180c10101031554504030002c0d040400c01943c061001c10242510366401c01a003203603c440750798101840c2002c50 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 302122167 1250 302120917 302120921
    0x30606060a200a021305040c03060f0f0614190e01030f0c050910150207050a03080702010e13091b080303041104020405030709230402090c0d11070b040b100b1c0204120b0406 76
    0x380380e030b1491b81403d003040001040110804107c9074090302c082810f0f00c1c800f000e02c0c06440383c2c2403002000c80c540800043c120455110000f078001003900c520108600340300302c2448041c481e0040f0701c8425640d500400005005200b1554181e00031020625019120f00c000b4075440020340321408036030f0341000d061102e00c00485903c521481140000c0205900c0d0601044516415200203440c00750045266402d5901030050319100340001440343c0442d0601440f00340040510080648082288000601c404240704400c0400da50360b041c029400c40d07860340d490550403110364040300d40007502404000340039101000800050f0408a6000c200107845203107416030b19451003c181400c0c50312405110160302c69800c425040000040b183d82c0d903014502600b000f406c120b00c180072082d40005018401d0080000e41d03580241d10503207030b507203072a2107807034001400c4120740c01070b80601a020000d20b15180500100c181c060110740c031015041c035035165017044038407000707203000d9800240800030001000b40394 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 302123417 1250 302122167 302122189
    0x130203010c1805010c020a0906030b010305011b0e0f0301110c0d1403061f020102091f0807080c19110a03210c0c03051c09151505030606060a200a02 65
    0x15240040b420100340380200341007111480b4890611843e00050b405545419032040d01400e944103080c04075130b641e4074008691030380034803056816520304100220b004403040c00b40c0300c2c018015902c03140a50200420001051140301c00503034559602d400440003400d5000c09800000d5014000c0e220019200101400e5200c1c00c4008500510007041008410740d14449480620180b818500701c40741d003101c009034024400c0c81845640044c0c0e20115007650210034804010030800c0c3d5490740c03415118408203864500d0145c6e564600c80754140450445d400c05840541080c440d0761522030704c0b2100b14142641042c1a03858243e00140c0781740d078401d071900c824001c0386140990107881004500c0c00700c24001d2814011550003020003500203101c4c0888040c2443e10500d540d031421041280030094a13106400c0603840202a201070308266600c1e003a120030329030b0f1408484001c0c02500e080e5991108200382c66201c481044280540140480103c11600c0c00409000c1c24000041c00f603c01e0301d0041003500b00c1e00e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 302124667 1250 302123417 302123441
    0xb0c0c030c0d06020c030d02030c0a14090114160602030a060305070b0c0d0e040b061303032a14030f0408071409160f03110a0201090b0109090803041b0302040513020301 74
    0x1c0510031200c55250501001607068100d0b20041e111550822142c1c194401c00060b07400da9030021090102a0501c28000c0c084820346840f42034604428052103280c42c0601d081c1640030402ca20034140030b03e00c06034002e10101e04000c1203071080da6883e59542c0100c0e00705403a082406590384100703008104040040308050034003074040f00c0c10b082c548065140d0b224010560b10040044442072900e03543c845410403015440002c0000e5100d052002c03e440c2d465100d44420384c00182005d045101178158400c07012a51029508402c0d81355101781c075900d41100d419038205003584820854409001020005000070308400c1000e000360794540280464035100303810701c2e2072041c4184401d01c502070411300100c1d0070318440c60408a04150000b6000d078010080c3d551288440d0400050b0820392a5040d440087c9440c4110301c1c0b81c0550740c8500420302164054440240441c80c2040071802142076150446801c0d000450500c2002e520395001c5001e5400580d03e2a65034440782c4030400c21480c0a002d0b82d0a1550 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 302125917 1250 302124667 302124673
    0x2120703060e15180403080405070e01050d08030903120108070e0a110702010f1806030e060a090b070c0c0302100c0201020105070c03081b070b010b03071b08030c0c03090a0b0c0c03 79
    0x402c0002240150070040c01c030150b000e001074040101a2114100c034001455a82882c403100d00d01410050300415080b40d00f2583c500501801040341e420700f0081b80d0580300050a40700302c407480d40d41c5101e896403010301100540d120501c188031141544644030380c080c0c050070001d80b9501d445c006103d082c43e040608080c03c5607003000000c400c0e03240d4280035522550f070240380c900704007501800c06503507000312681002c0c004410202d000c5800d03601500506c9440140000300d50b0750340d603105c40c00c2c0101c0d00465001821488607002040d22a41302d407000724595401502c40140403542d9500080d140d40101502c0d501161020560710259a020b20519900074040c1c1001c204a180030b035001814403c00900c080d0303800054040110348011100c0994907a694800b0f504045c558640c10b802c007407500200c0710300e000a000708050350070680030110800d103c1540404034600319222504144526000400051000d100600074030403282d47d4240c1107002040040c590507546c2500414103420100841007841c0254 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 302127167 1250 302125917 302125919
    0x6051b0708010b1e01050d0209010e09182e02030711070f0911070203100e2a28050108070c150605041805030f0304030c0b01080d080a0b03060a09061e0212070306 71
    0x10342c219084036003001007c100141c0d0b0300710180040e00d503404140840c64000000804001101c60a48020040f55960200b03e80450500e0440341d804007032210080003807a40310705552102c0740100c0d005103410200a050200304a847c3e80034680c6440e0883d4008502c1c0001c400041000c1c0580c1d01c511035260803003180952070701000d900825070718602002030524072070751211040c50487e01403198807040003e01023505281841d5805100a004400c0c50f07035841012003102450003c08034000f503094014a510380051082c0c038040c01510300600090910050089070340045000400c01c13100c60091b0080c04400041d06402d00061004071200000d00c0e4006400402c44003000c924000b041d149000e614042c003594955480c9411560840300a500414421900f00040f400305070108183c40701d010b19a0341e151440e6200800c00d070a460128180540540000006c981200c010360841c1200500403a804034501c3d40c1040911102946201207241c1c032030b8080b4445401c0100300130b1740c98100c0107038903080c4a91 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 302128417 1250 302127167 302127169
    0x12071a04050c010c08040b13051206061e0f062d0a0504090f060509010b041503140103020f0312030c0403060f0504050c0909100204120501140c030106051b0708010b1e 73
    0x142d44035400035418040041e81034001c0003e00000c4801805480440e6600c8015801c0503102d941040e01a140c80343d2009110344407407040c0001c046d80304410040a10760311800c0c0d201016105c00000789902c1d004641800300c5941ca8503004008c0446400d1b030002e1081c442d40f0f01d0700c46c5141c01e403942501e14080b8000c001910256a002044d43e0035102c3c0c8040000f05080010300b01c00003800c450380480d400c01801c80000400340c00c150050400c494051000e549001e04415046044034a001444001d16102800500150505401c28006e1080c058112184e0413442103d092194000b00c5a8400c000d800003802e00c2007004500404130300c00391441d07081c007690510317954068031030a0140c55180600d901c0000100540010414602000e0311204215078071511040080034540e031b060340039078541d0308220700c01c000001c0e50850580b01ea000024a10b003142d09100048030241c0c41143c10390007010500b80c0c0294555028081503004000c40b1000203200d10a90080c00405ca5403034500038a01c40b0b0f00c802004071 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 302129667 1250 302128417 302128423
    0x4141507111606030b0604030f0b07090b0702030303010b09041415100804080405040b0a0909060f1a010f03020a050408010608060901060f08072601140901050108071208160512071a0405 81
    0x2640c0c401c2c04c0102d62403140b070380801c0040c000d0794005009005110314600c240201002c3d05405440e00341d60b5601415220740002400e071058800082d0154000c200421189a080300600b0142d01c0003003010415082d40105203101c49001d540034a200b110201240d00d840c60f11510300045840303981045e40040c546034a40c22114055445001d00450302c4e0001e03043c142d503c000440000d0503000700100055246d41c00c1880041140405203040340303160506d0307a8010030603a02807032100702c01651011840c502100040700030350409041031301403110901001c40c054600307001e101e001d8852400100b030b40b4500f103003c050039207025611121300f820952109001c0c072040480d10400f034a001c000c92226490b00c400b8405960380c00701d90301303030295482c001d0212011441981c440d0702a0b980c02000b8022644c8418506850704410f02c505941c41d2a03445098000503529070160410342d000c80b040c40c8119046441c3c0382d08050480750003020340b0314002080020000e800441a901d80c02c10031400d500c600d0107550b0295 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 302130917 1250 302129667 302129669
    0x90a0c0e03010b0d1704081006091109130c0504050607060504021302090d300507020a0b03070c03030e0f0303090d02061005060f18031212012309041415071116 70
    0x11504000017905c401580c0140c3c00c98008003103010440c0c18294942000c03000403d41801081e800c2410030591459101d4100c05403900a1030080103401c403400c1c7d01c94003800408000b50ba80d0f040c0041808009080c1e9176500181110324001d1300c0202e501d18191040001402e094a41034411768814007c41c01c03a82c4500c0e01d9420b000c0e83c420036803140d00b0903040e842648660540740400c1030390700411840c0c0a01c0d82c00303001b03085214800c0c4c45c00b03841e03207803a800e401d01c42c1c0c003040b14903200180d03d00901c1c0c004a07229821040c1c1610700744d0144d1f0004e103c605000e9046610440d5001d42c81d030b100f100b00710900d507410050564441048544003c419040a00003105d6228051040d000840e0210315080000142c113004002c003e4001e04032100140d45121001881e0801d001410a150174000000740ca03407402d101d01c5816403245c00c203101e00004d114003088440744000c0d10070f13100101801c44c903ca9001007000311045420b17071807003041c5040ca03001710020b0448008400e4409181c06c00010240c4050210719064 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 302132167 1250 302130917 302130923
    0x2070b0309150c07020a0f05010e03070303050f0a050c0a080a110a020d0f050c0405090d09090501050d1b030c0b12090312040b130203030304150b0102120901030b0a05090a0c0e03010b0d 81
    0x82c0c21030702d81c48607480050084c40f00c0a503100d003240b24001213000c59107a0032000c80d2004e0705c402c94190848010582c8800d41888064003007071080003026151032003c001003090321135134241030f410819202d00b414904041d850049981c41c1c8001131009035a5004044000d081640c0b400804207041035a000c581c0b02010441c00900c0b046c00015500d00b000014031414080002c094030404c202d107040c183c07081c0c4c1e41c0e084080380000302d46103020220328800715005041c1178a4010740003040d0f00400d0b50b90701039441a4800c24480000300514080300142810005600406518407045c1d181d80d083c00d443d001240000c0e00d40da0450f07004100c0700000a004034240c50340075800100d403580c55a58014004030701b2500303110003035042c0000810001000200b50740d4880448404001708140754a0000590380c600300e14270410032130002030008001561181d00200300d40000507200707030710456645000c10000038082c0c42d0000c0064540040305421503024058034281c4604800034019030000501140011109990203 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 302133417 1250 302132167 302132203
    0x120117072709060c031b020601140d0b0702010603020a060f1d3601060c0312050a180303020705060c090f06160f2303070818040e100c02070b0309 64
    0x808401e00301d20a140400540c62100b800142002e1412100800c46184400003192a2415268024401d5030980b03240110b260018005642403580506102c0c084410350f90303004200300050000100ba08005900894072500003191140c1544100300c24215290001e200704941400ca50445c25030003045e4041d403000140400782040c003540049100004081d50042644005182c900d07902d00d83e100c00d41c928200d401c404041c081e600c0740300c1101d11002a0f40058001f036409083c1c0091511654400c2d500400352010000364146038032611405003201400a034042a80031500505100c0107020269014403180c0c03840740340040b580c0005507200d15901106001c2e0b10301041024092081813020b9001c10380291403900703907560f0391501141c0b4450144048944080c1c00c072208001880010580701d00640c010300c0c10f400c2a0402e2658903085640d000c85550240d1155040280500f090009042d5611940004a01d000c840b0601a01d40502ca41c429011810100704100c1c03175000104205240c041c0807418 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 302134667 1250 302133417 302133449
    0x112401060206250f031409070501030b031519091a040501050a0c120b010201020c06010e01031505060607080c010b0a0329090c01050703050d1407030b0603060901061803051212011707 80
    0x401c4000301b10140e1800701c1c2c07000b803030244001c800c0b00162440407500c007603070305110400c0381400713054841100b8801400d4010306800400c0b4030070508140b030581c203840240c000440511a48500c85410a041d040313110741d800d100d0510050107401c0c010240e105441d0501401a914600d0006040c05e01c03143c40c040305103544141c6945560b101790105e83d250b4014200315281961107420b0000b8414003840200c400101001d980b54007503816000b2284107500c002d10260404906841d2040c2e40d9004015200d0170355681c58207880c0b55078652040d100074501032403107501c2a03044a5a41440c044444502c40d000e2112041040054040002d030030400c02c2e405c4c03034001c3d2964002c2c0703000e072030901502c03421000860034240314000070111100624403c1640e66014402c1028143c188061888159182d542007a903440040c00b003180552400c0280002502800d0032442e9261a4a802c1030607000000c20490b40015000d074054032800030450140c2a00d040018110782e900190b15030f00e443ca4031900030840b0b06880 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 302135917 1250 302134667 302134697
    0x140f040b0702120d0203060f0306010803031f090c02010903030c030b061e0405120a03120504081801121404020f01020606030a031b06140f0f011511240106020625 71
    0x107184090900540f815032070341c0035802c00502941084407041d004074040380d205003262800180340c6040700c291201a43c42c545940c501740090622800104084007100000003031061014851844da5410f103074000544100745182c0182070760714034074000d02010b00740001c1e440d080e51010704407003001115001d0006060b41d2656a00071502541e0b100b0740d4083da40342d41c0485403110200b0103602e043e2003680c428440b1420114030344c00b00c80040e03602a00008003802000200144181d00c031070521014182000c0704040840d43d1320070b40d40c2001c4010700d41d4480074203000031800c1c419402c030904c0d40b09002404091500740c000c00d582c2d0860303580140401c410074202103a20751610603020720081c1c001405201044280d0b11026036504259000300360211007000007601400d401e0219030503a140d0100c000c0d107a040b600c10884084000004590450045840040005440980085100e014156940c28a40c1341000c003904111000302414030f0410138400d0701040c0b504108441c600d0300000c1c00c00e00d0700d00e100d0382 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 302137167 1250 302135917 302135923
    0x304020a12080c060c2a0a1704030506060406050f0108150a0312020d1d0f03031b010606080106030b01020309041d060405030903010b06040305190f0c060504050103140f040b0702 78
    0x1d8440c5200d244100306440500240000030952500300314204c68039502d4080c410300302c0f80f003240c0c45800720105440f00b080f1643c1600744c00c180c012a10000300e07026801140c40f20f0209045001a82010500009041040100c01d002d21588400308850412400b0b1030301000c51040044104c0c100c1c108038100001481e010302140d521101142c0190500382c28030344071315042c03030200103001c500809841100b0b0050000b911440598a015803500c900c082480802403d20070070002c440715196241c0424003c50a00100138455480b10441d428008242203107820380182c6180410f8000d00100b40c1420030300000f0780d800004840d4040000d030b800041a8441d0760341c1c40c1a02d90301381800c5001d801000180020b00400101501c43c800c8120020800c8110000800c104c5100da071100034559040300a10080745442c1c60368800e1740c1030196083d44c001d84543d80e103403100003c2c0e540200000c2280424140060350b80b43c4555030007004010712121041c249810034081d9084010310041400d044400050b84261080c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 302138417 1250 302137167 302137169
    0xf0303060d21080f060405100e1801020310050a05010807080c090a03050a0506061f0c080a021f0c020601141806010e06040801051b07170708090603010303261501050304020a 76
    0x112900101402c071048004140403015207059104020700c402040980c0307482d10410b406410f043ca94035001c24680180d610002c90014141c0d240301d80c4280e25004155020700080d44948201c4040e1086075040c0005c01a07a16641d812050400c0440000c200d003032600411402d0b002601141c805890300040000103000084a410040050140910782000c00000066042c018a8125900103001800001011721205c07002102400281c000213034401007031110006107400034503441903483c1c88040e8804014034a03136a44810072607681c0c502d42a00d6481d1f05008003405854140d1200710310a0340540003400c100d65202d1188110b4091002281590703005040c81610742d6406014261243d07611000640203180449a0b4401e8600f001400720b40b0052881c1121340080d4408501c00d2400d508940380012900044022200741c042001900175569420002d0742c0214401e80c3d41c49002d80d44e60001003504100300f88407480a080070800e0160070045051030025104003807920985039500d84c00003812140c41 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 302139667 1250 302138417 302138453
    0x8070c091103220c0e09010507020c1c0f020d15050c070809060904090b0a1a030f1e1006180c030e060c0f0904050c0703080f060a0302012006180f0f0303060d 69
    0x454000045e964281e545040c0c4103a91241c001c11240c1d40c0c1c0030b0140d03114045103002c1e40c0d10288c030300c1030952131021440f0750060b224060428424056042d601091f906174030440282c5103000c999000c15107100c220f00030180d1005030031031401d040c40341e6661091f400d40a8208500c0c41030300041801c10031a183c5611881d4aa41c00c0240c00100e42045440f0900414400016040012000c01a0340c62400e0005108807140f01c010010240c9083c981000348040f01000c0c00e00c4010f0086c0341018801c1c40250050304042c0c01d20350154104824144600c10884881c00b505105042c00c14400d01282ca2012488950100510018950701d00714002412010b21400c01e645610a2800c3c050141030360000f0040c200340d51094944142c0c680354410710f050a6079089440e00c0e032101d01d0a1081c0b00651280070040c1501081d80d050b0380111041c1001d09080c0b40b0201c0c0c00040000000900008050007004244031402841005d400050180e1410980341c0c030004009071b0154a116046008010000030000e00c0851 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 302140917 1250 302139667 302139683
    0x10e07020f10020a11010908030a020c0a0f08210412140405030114062d010c08070609061a01090b030a05090f03040b04060909060506070b10050a0308070c09110322 72
    0x4807100b4084000d4000350100c4000841d141000d5030070130030500c5880e00e06504035101c2c41c1140c1c0d440fa1400007030740c4140d804403598000da4940307000190014034034500107440341c010340d52514034440c0490081ca052441c01402c488032041030001280e05c82600640d0340b041482c008140c214164141d00c0b2600c113603844030790158a000752850000d1051480c0c24040c1d80101c40400064a42d80c1080203d0f9000d00c5582183c420390180c040e4296018035905104c8034840d01e0000e08011070f40c1c0340ca0080b03c401c0305080e00c0c40780d00c55000e800803100b40c3c8030504e40d40b03c09007401c041c02400c000c1c4800d00c0380401800e8201d040d6551010138100e9400f000f50305484c0c0584022079030b0b12600c0325004c0b0400e800c5841001c001c40c1e03000b4030105550115000725400e490740a01200c0c1021056298100e01403009842d0143c101103c0101092a0302c03040c01d081d01840c094001d0075030718105c0b440d0551a1810302d5110b02c5113140390081554250500350101da07040220000301c250907080564408c04917a05076240144003074 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 302142167 1250 302140917 302140933
    0x6050d030c031416060c110304170a081c1103091902190f0e010603020a05030a0203040c0308030112031d01022104080304060c060f0c09063207021e0306010e07020f 72
    0x3041544c540c850041c4181010310032000383c1d210603034034504080314800c0300b0740050100f40303c64084014080209061402140c1022040351070b00310f40c1c1c1c1e2142c807110058911001103c9000034650065945401405000c1c80c50340c078100e600c1c107072204004142641640343c404c0e684401c0d9900d0105d8011101103031100900400c0d50f07001d503158540014440e40c49a03103407400c00001c00718041c4c400d0390716180035034640d2461030307035011140402035000400890302c111b8090404404144020051400703090f07030106500c100484c41c100544102c6403821400313400c4610000a251304d03640424913410490005103200351000044544a03203038001d17034010920512002c280000c0d4140c2c00310b00c0941e01401108204140026940100c00f074841c0054180c001c101c0384081008024480c5101070341c890340d0b50400c00c3c41200307818180c06520513002081107030f41102091402c103500d01101514104429070140e104c0086642c4c01080d15040c05202d0321620320b14000c0000c051500030300503404102d5443c0140c460305 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 302143417 1250 302142167 302142187
    0x5040306020a050702100507170306031906020309070f0f060516080d0c0806010314161803080304060608070303080f1312020a03031a0d08070c0b070c030b070306050d030c0314 77
    0x11342051070281d2007460f030000766a00080c000e004481400350410311180144655862041c0981d002800486e054030074842a0500c01d00200036140055124040142c0c0d2030400d01407480c600001604030b2603062080b20710420200d06a00481d108407807071418007580f1031055085401215880b9940946000f000007040e0b1001d022a07444680c0c0e1000b2501d40e04965101c0c0c8004500310392021056442d071000400c041281880d6a4004c2c541100d141d1818000100560307010040380c030456403080342c00b11000701c14081004601d004403000f030030466006140151131924020807403a000f5061490304111103011505922110302910030541d0040c0080092210b030880080d610b0b80b60001c203400003480d150030040c04070500c6185480c200002040b10341d64000c0e9480d0812507070310024080f6481e000b4a5000606220b9a50240002c00e0054112428261960810a40d40d1000511076420076244c80340506c00d56540b0702c4032009103500b514103c400c03d2498a41075802c81b12103c9100359100c0040344881c00 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 302144667 1250 302143417 302143427
    0x1a04140d210c18090902090f06091b0d060311030606040c050f07020a0906061e030501060f11101b0e0301090209040f060b0604140f04060b030408130f0b0711030718020a05040306020a 80
    0x208134806e441d6440e47e43e80b0900d0040c505007050351400e0384880804041031200e408101040a001401240589041e40c00d01700a4100c542542c000c8401c0d51154a502c0d500c0e1506000f510f500000c165401d120720070351420014000d21600c0109040d084001c0b918206545810107100098180310400304525620743c0005080c03902440b80c4c1c040c0d1420040284002c81d8403e000341e41c1207841a40b110f0381040c080c0e88094502404020301c0181301e1050443c0c1208000250151070b2000c03a03400ca640c112210002402010b9500025100303001c2e0781000510401a203030010000c0c2c0c0300360040d40f0307011941031034500007010305202d200b003aa002001040c0421400e02500b62181290f0b01203400c81030f100c01d07480620064035403910841c0040c000500005001c100b03208003c05107207550002420350320392a05492048000e40340c0095107000b40104005040103040144282940800c40003080307201c3c54a500344018410405010b0321054002c0399004101380602c0694000c0d41e80310350150745804c004040289 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 302145917 1250 302144667 302144681
    0x50c2a0708011112060d0c0b07080c0313060908010e0d030504030e1f03060806010305071413050c121e0a0b042c0613050c0103091a04140d210c1809 65
    0x150200031001240b20b91415640403006c1d19800b80d10044521b140c00315075142900100410f40e005c1c2c1c1c040042248500060000389400c8010f00156450305080c0340e4000c014007003a070082d0f13070160f25250079048030710300018899060044501c1d020a15039140d2904070784291000b0721032500200c5400c0307103035080e5005800044100ca065541000328903556030b1400c0d035071070003840040c0070340d00410310501100e40c12080034080c102c40070300a10031a41c5002c4020007201c0007240c3e215940c42e40400e08103042c215a04d5043d40144450020459600d41c0c00e04000c00880090915043c407543c64058a500d600e90340c0058201102d00d20b040d80081030381011403608019000840b0140d0700505d4002828501000b996222490702301c1d00400b20401c41000650080985036020303680442a45030702c09a5851540d0214400e92141c004840c0111500c14102d14144c200c120ae4018001001e0200102d2006000240840842c880010440c60020102640c00d00d2821543d10784000850304042040000340c0c00c010 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 302147167 1250 302145917 302145937
    0x90905070207050f0f060702060307030207020604171603020315060a0801020c0625050703180504051501021005070c0b0a14240603041a0901060806090a0501050c2a07080111 76
    0x84d40c0e11415408001200b50b0600303040e54000424090030b40581498000b80d60702002c41d040051401c00103400080064000358044121600400528524104148001740000702d034903601103c80c2d81194002500c070000600c086041e1400f407400122580d880405110042c6000c100855032200d49404607a2144401c65020341000e40a048000b040100342040002c0340c070960355801c0c03c01d011b540c0e049410080182a84482961107000071501e55500d00c951400b4072035503a49207011058a00019041c0070107a4004507031946040108820740da00011a07644190b032005410034150f803410f0009005103040c0700400440e20651040000c5004182d54803600038201c40e580314a104945410040300b44000c9070010403010000012aa1406003058001d4100d2041ca00104034a516150031500c0c1042c100d58841c10382d4001c546503000e01c5828480e0b9038100742c006c882c003440c0071102c201c074401c2c421a14200d6001000d04541e00311440205110b414042c0010300000e204862505104201d50f4004050f01 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 302148417 1250 302147167 302147179
    0xc19090f0f05070903032d0c0c090f1a03060702060610110f0309090a110702120a0f230105160c030c05060f0403030c030b1e06070212010204150203070506010e060109090507020705 79
    0x81e111503460885d0501107802980307641c0007ca80314007411114030544500c121507502e0010000301d00c00b1060f000e244846812035000003a050310318411070038030400c001d0160f402030b0001c1c0706000c20503902040b81360f40204180c1d6142e5500d40e4000c0115268840340182d400113005040c0e140101e2600400146444201142c1448507074860009142c01c9a256080391192240104016401410100841c40300601c8040c1600c503a05002e40350555110351050007220b00c417039154007034000e01c54a003448001c42c00600c8020001c03454401c12001040114220301014030180411080070184030f450a1031803641d00030207460841c10030700c0c030511031600140c5080b00400d080041968929100c2e10440c40c034a000101400c0c0c1070302c101116024000300151509030448401c019040241c0c80b1120040b940140300310006a80310300d404c2812000304400820344003150810085200807c1c0000717441410342e5108108501c0e5602d596006840c000303000e512104400707060104124002d81c010400004460f816030300 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 302149667 1250 302148417 302148437
    0x72106050f070e01080115201606030e0c0108040807080c030408100b0d12210c050702180129040e040f030806010f050f09040204080a140c19090f0f0507090303 70
    0x5617104d24090040c52101d4001002c101d0036144902c0803255110300341e0341041240aa6000c1c003a080c51041c081da80905002c2c2c000030416658540300f040071003641040a020214003a4000810503031001c1d1000e0034060000c5022010f2080400072180344502d21412070380e95917900c0c0505501e4090342000b01140711316040d0a000706080076911011501d5002801154214161809a4004641c141c003001c000044043d4030707034454854442c20120b50140e841d07081e2920124810410700142d4040b615030f40c016003030010000e6414010040b0140260780d030b0900c1c0e480310101c1c5010201d010340c0e40802000e620325000c0c0000d1089050400c280140a07568024142da02c1d0b40065a005440900100000d9000c02c403801d141c2c50481c008e40088000180058070703181d5182580e502e8907019210075075030b601d504440e40c07605080030403405082c403505845403482490040407003144c074400c0f4852041c101c0c1d12290400341840d4260300082101d28482740802060401d408010892042030200f10042101404 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 302150917 1250 302149667 302149669
    0x9060301030f1b0e070305100e011e0f0605031311030a030302071a0601050a0c02040e0a05030408061f030308091009050c011209082b0f050709050111072106050f070e 73
    0x4540801c0c0c1d00840314110742031704c031024100e0040030010520b98030340520403c04220313080914040d9000305280e0010369000310226121031048451503106420302d8803007920800100307402005480c0d106001c4407028407981c0007400e044000c0300310001d5442e4140a03001c0d80d4820583c040e800360000f580660310f480c10008681150b070341d11070019541c50f4007040092040c04083d81c42201108082c51010300003007103085502c81c000c0e10301480e00f0008c4925800c00b04007444900010044035502060790340540d000c0b000000310780c0481004c0c9001c090108070640d40025020101005400039620311400c0030402c544e024144aa115440c3c2c0c4c140d9800141841d031760800160b80c40c05142603041e040601c283c80c1c81103103203140b02030010848181c01458800c0d000702080d801c5a2140704094070060001159502d01841e000700700d20380d40c1e00024148903580500c078051860004400d0269100800c0c6c69203509000d0307140b25180270810b08010031560611040003040000d5040321802482e80740c481c4450310940788 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 302152167 1250 302150917 302150963
    0x42a06121424040524091006030f18150b0a1a03040f0512030f1b030f0a0f0603060e0d05160803060d020915030d050408030a03050a0209060301030f 65
    0x2090701d200c109035500100d0348400c0c0c22008204061500310980d8054104800420140c607070032150018a0200d070840803115001032030a03c20320003401c68810740e95140c8011001d41445440c01220308156481c40e040d103049032550300c00c501808202c0c40046281490785420318200b0000440342e40b41c0c034103201c2103c80e076040451f490016900041081080c80000c02c080160a810050096504400301c03450305020034014440c1c11548200b06050f6952450040c1c17a491403520702038410440ca1214000c40303414000c0c0c510a80c0c2e0058213041d907007041d640325105140e0280c034007a042e224840d8a040000070403c10a9445505020b040d40165230741c1504d0380400f607869015480e22409025a8041900005064a001141c3c00407000704451000020303034001c5070020108030742d110100c9602d480e03910000d1804000200c40384000f407820b64545400d00038596141c2c0030f4403801030185034444001c10f0740c0c101d142d01034501ca0b100181c1039036180d60752802c1080d0020301002c0c0664081440c05514650040a6 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 302153417 1250 302152167 302152181
    0x4050a05011109010f050c0715050d0c050703050d09030905060d15090204080304030213060902030112151b0c02030312070e0118050d2003100b030c0f0d0b042a0612 72
    0x503181d05ca140c24a9040541e0241d00415104105004090b401304005c40078071001c0340409242c1d0740f4181c544a00d0081c00d02100d07800f15103041440410f0010744002503000044a6032401ca45401217050100341c582a40d62010a0700100d9121001140740315201354150304c0038800c1c00404004001c150b6945400c0012071040707009111058000704020f00c054200340360054210f40c2a107000107a45960b420f0b007102260801e800001803540d40300e000006016440c44020010807081504200107801c4800440c494107101a00301d0912104402d00015943d0501c1960541c810400c40f802041c50700b1880103100710303214000c25001c600c0d032850494100058840c180c007070350310190031003139120b505807a40ca0041035800d03c0348211250726210807141e82c6081c4a840d0780e1405030480800c40780c05520415041101001d0084d004503040010383c0420742e2004004c1e00341c01e401041100c0140c9442c10885030280d401c1250081c202070440700d905501c0000d01445044072010355841e444010b80d102142c0a8681c0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 302154667 1250 302153417 302153419
    0xa082a0304090908041a0a030f15050f15070b01050109060f020709021e22090902030606091302031e0d050301081506040e1002271e0d060504050a05011109 68
    0x60000384070b100c003181d01c03800b10b45003c3d41207581440d642d9400ca81140c01c5880711000d40d44404540c0e8500550540101048440c42c20402d1113000c0640c21800385001c441d2181c0c030310a10f180c050360a0151034401140200c002402c400c1e56440350941400e0108480130711079580050764840c1d0000d0302d03611510402c188070007140e0290502c1e502c0c090b80c54029404c160500400c00100b4130405c070001c10b50000038514520000301d681e91000d603640c3c00e101c1c0481d407588a44034960a04103100c006940100c0c8465210f1821240d075a20754544032000e070140818060000d41600c42c01001414050303c80800e4540e4582600454880c4150310608035003500080c070898905038020100710402c009864400c0c0c0d404807024000207007060703040d880103290070f14000707400c0e201d240c1c00a130310070207a10544207034801c90303040c2c240d000e00c0600e590002ca40050719003201ca10401c5c0d8200c00c0c03881f0b00d44d5029044891035801101c180201d003824100161920200c91003110b01390b00e06007181e01416a40c0d400c0e0341c05000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 302155917 1250 302154667 302154673
    0x32412030a0c0b09060f04300f0305010603020f16060204050a12110f1c11060d1410031208070302070516080609010510050f0604091b14030903090f0d050a082a 70
    0x211a6504510030050346420031401c0852340b0410040048450500001d05040d0390752500101d110700003604403507060f04103908050041001400101c448000c44205403890104c0d4215140b890525030003e001d103070002e40e03000c0702561000a4200d0082c064542d1103015110110501c141001040064030030092450b801a2401d800d15424042c1e40b20140c3c00719014043c01c400c480c04510005000e5401040007400c2c061386d40051445620001341000e078000102d81e10304020a0039621101e0811f400e50480d502002036500c0010100392007901a10f101c181d214084900440700000e000da0b902c5e40c140603030040c51142c10001180141c0c14002c95001e007070058509020142020280518850002d40340380c0c2081041100042a940b94070807040341c1380c0e0341460703943d46400e0688020000c00400321008038a003024010301040c500040704444060f401260b04103402d103c680045240d03004000006085809415200d0050041e480b000b064041c070b03c100400c0c1f0080900e202c000344880c5401c0900c4051f8 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 302157167 1250 302155917 302155921
    0x70e100b07060e0a03180f0305030f0a110703081206010e09150607050a0f260a030f0f0c02011a0a06170a0b03061006090605032412030a0c0b09060f 65
    0xa4003000081410600910000c150141014a080c0ca005141d81003280000c04403c0d5a140c008030080496000d4042200c00100c00343c41c5480c2c40e5900e00502103241800000010f0500840d401151b089045540b00403d5480c616500c0c140114960001c1e860742c11919254000501e10758483d80ca500b00855004002c140300307446904010071500c0d01c0080903a0840010001c000114500b000780e0300821703200b285000c4912816160a003000d080780c0c050391308100309801e244069280010160b44241250303180019000000b09240000782650b640d00d0041c16240c0381c6440c4026906400401e0030103415544410314010b03100070703c002071106201c4c2c0c030000b0350b00701c49584562000b4520700c3d402003010b001c046081458000000d09050303080e00e2449078031f404140b04018482d081810b1030300401c0320f414158203525101c2c2203002e02400da5482000101c4c907603801c0c034061b6550390b10340a0002100c80e04413a115100c1f40e10103000d0300b180c91410361300342102200041524000080462044101d41140c80e00d913 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 302158273 1106 302157167 302157179
    0xc091803110c19031a06060403060b03031308030c2107060513060e1e060f01060806120601060e030c09010303020d0804051011032a03070c0c0504060b0c070e10 70
    0x103120f85c001040419a25001640d0803203070459004104484080006801e521031300407448450f560100380030070b80350000000342c01d441088900701c83e21981d0700611a025038200c0000310f140350074200f101400041031600203d421441d06072010054030baa503510349003560342c00d000502d03c50f4000031004145103551603914a03d003101034003803c614284041c000d54035640501528007071100c0900030030b203152100307143d014161910200b80c40b400c0d40c480800411420803008098464400e00d03072110501d15001030424102c4e645500100a5800c696906803407002c4000c0064941d409405007115100b00309000310b2404030ba405c10039941e40e1801c0d0400f00048007002401010500b900c03040b0002c44a1600c089a03004052420710b040482910325003039254500c1a040f05400c81c3c01c0007070000c0c00030480b030090108140003500b51542c0d181c40d204a0001058210744141110f10641010010 = true := by decide +kernel

theorem cover : BRFrame.Cov 301978417 302158273 := by
  have h0 := BRFrame.cov_init 301978417
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301978417 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 301978417 ≤ n) (h2 : n < 302158273) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
