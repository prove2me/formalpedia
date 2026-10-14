-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1778
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:38:32.437169+00:00
-- url     : https://prove2.me/submissions/8f4ff230-9a0a-4989-ac1b-fad0d5c468d4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 319604316 ≤ n < 319784172 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 319605566 1250 319604316 319604323
    0x705040606030e120a020c060924040810020412021908101d030705061b090d0807030e0f01080105060705070512030a020d05040308030a0b041d03041409060d03030b060c 74
    0x40c409408aa1654040f51508500384202101c02501c540c03000e041c0220954003e644241620009000385070002d08050030b90350f520f2502c011a103030f54a0040d8085070f0400d4480c19070300030740b10b110709622a81128200f8a50503009a50566188860302c6400081c00d40821040020411305000034114030710010842440c103020542c0d0050100c000441c4c600082e000000c02140c40000041c02c54000b4054a00011000300e02c03950400040140caa103480070381541c5240910945101950085418450754100301070320001c0c100d0346001c0d8454080841046050086007034107940034600141c82e600051101d45801806440158020800ca40980b1b4480c0003040f102036402a1800495001050580010b581045541c01e549481c3c90464202850350382d030b1b8440703400007a22590402e900d61004030241c5d10386511110035103208980544290441403900b907240e5120780030b4074110403070003032240206081c2400542e0241038007a016243c01c0e24561402c82c001d0a160755043d40c40310b8100049036401c0713802c1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 319606816 1250 319605566 319605569
    0x30606070606140a0e010e15011e0f200a02090705120f010e011a03190e1f050907050d060b031204030b010801050105120a06050601050d11040e090c1f0207050406 71
    0x1043e80641d1010344104034160450b644407142d0030b0107280050208041510710280c2011010b0207400303120000e030006079164075400105588440c10a103d02580581c0610150310f0320105d516162004c1e4546000d01d040740680c6408444290700c0807281600504003103130010fa00154501d0305d2070900011041e84c03203c2c55020b40701c00300340442c41d000612107006c012105038018400b2011100300c903c0c94000840c01c03800020500e1134000c541c03511851040d4903507041050b001c451401135540c0301d01c600d1038168403142100c0d40d6440040c0f4140004011003400115542981c000501c02039410290341e4568020b01800001c3c0d907010301407140c08d040e03681040340241c000b451048005060039810311540e9400c54005a00c0759125201110880c000c0c854003244409080d03401070750110747c594609006950601c520320249501d9850100c820740714501c80b0307028005030768000310804095103030038542d960382d911040c3c6503980c00010300107010045416500841c14071000c60040c0d85480d650313980020203d5143c2e = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 319608066 1250 319606816 319606829
    0x3040b0c160305031806040c1404020d33230a0b07050303070f18060f0201110301090e010605030a03090b0a0c021011250b0c030405040207052107080708030606070606 73
    0x20040c80f1750a042c2c100244010222031008003103914203078131100c49040141c0305000440c009052444129251030f01240c0004000d9030301400055241c044207201e006011188407c4507442580381d04040085000310300c11209000d00a0340c2d030071030041c02c046401c0748841c280e562001c0c2134800061148580005020064025400380d9180d1500c1e0001412148048243c02d003040b500c0720701c08608125001c002003d80b45585440e0321901c0381642c042c0d004003c0100041c0c40c0c9070001c000000c00065507080001d505280d80d00038421070b41e594082c10b640c0c00706410020049458241c043c4666034160001c0d1100d5413051400302690b00c4150041a000711107a24001c0000e8040105100ca0000c2000008903000000d0b0b004200440100c201882241440c01703076550041002035801d51144040003aa0060311000b8001c641d21002032402c255144200f8034411780280c1541044c01c0140f2010f025149032540101100c3d1612255a5803403c99601c000d244540c80302d401c2c0181c10214400c0e201f500d010b0002e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 319609316 1250 319608066 319608077
    0x1020d120b060d0f02120c0708070b0403030b040e0c0103060f140d0206120106030f05060d0b0c03060102010e03040f030b07180b0f0412060902090a0e03040e040503070b0705180409020603040b0c1603 87
    0x320341e106c50003220010281d001c8980c080041e0342c000f4242c90200e604040e00b003002c2c041983c68070714045010f4086458210f51003070a20b030307480700000008540300d0303440359003602c1c2080099520700c24003050103641e1080e000013039400040241c180c1408807010311098401032260307141c000000105070b0441e0302a001080080c0e50b41c1c004c1c8411840c0fa106280e04610204c1d841e052040d02640c641e01003290050840a0a40000c0040350980c0d0007500201c0c0102d520000340c0e52220b440301d030045903650780d1f403000355000c0200f03c001c2024a4010081420501d03c07480c10310035514180b6803404850ba00410401086240402c00003031140c0300050a030300410700c80d00010845810b10700400c4500e100140070341582034900045031004030380000031503080394052058810283d46a0400c0c80c1540600726020b4143c103049800c00c81d1150b0700100410b040c90915185c0c40bc0d101c034860a2004640c14820005e400c1036041001c00c000c10307008410103074000c514840d1689007c0903036440e400c18440c000c00480c0801c0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 319610566 1250 319609316 319609327
    0x10201232d0712061206090c0801060b28050304061505041e14060f1c1a0103030201060b03010b0a0e030703150e0622080705010b031b0f01020d120b060d0f02 69
    0x10380c02003880b0840401004140081820710480020904490000401c101d0350703240141c040101100c000e600134840d68008004bd983d541002c0d0009601c0300d009000c00521000340d590540302144c0b20080d00f5801d0307590301411542d6a5641200411810b503000c1e082a5150030300085c903685a024a00c0440307002071901041500151500d015603054403404882101c3d25800c0000585603c4001c0340303052421034896140600c0c01035440d0986080c04805002c0140201a298213080d20b00c26090403203100c0da00030801e8036510003599006010038091b001980c94100004070700c03c1d12070048400c0185c4020b041e01d44060781d9999031030030380074000810400c0f55100c921010074480c040c0f09199110712512454408048000e0030b02c01c2892440000038501b050100303e075001d01a0950000c112014040c0840b0070020080140c00340020300700d000a8880c039100d001d2400d00f944041155030540c003035500c41071503c42c1c09407250300250500c04480c0ea040700040c030804034483c855003c1d00c600301804c2d010060b42d60 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 319611816 1250 319610566 319610581
    0x1050d0207170a11070e16090f122d1202010b090103050f0c0108040c0303050a12050910050a020c15070212040b0c0f0304060203030a021b0a03030515010201232d 71
    0x603810113140380711030381214a0400050341c60001c0b86a0011101103a083c03460109074090b51352088517009041c0390521032001240c00c283c3c114a040d100ca001e0800c0c0e80c0c1002005c1b0502c2c10040c0c411048521501014200300e00140700e060310714001c2c10b007074000480e04120200200d005900c09a0003039072194440028120b40300814060f80f40071850030b1808284030b02d066201c00c0407035800342c40000d04100340058a0500684200090441441007440500480c240001403a40d91828000d605019500d0000410b005400e14404c807030f4101e60711406881071003098a01d08201c0701009080784191f000d229555000c1071644001400500394000740c503911071107810b408520307125a50040c0d9989030300410040c86440c0e000401e030382e0b0180714014050b82e568071407451710300e100308203030342c588c19078410001004101905600014414003001918a01616405004a081e10000d180289030aa070715500824001d00411800f54002d2103501900000c81045081680304086e48000f102d20b02180c80034008603 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 319613066 1250 319611816 319611827
    0x30307060515010e09010b1803060a0b0405010909030e0d030509060f070b01120f06050a0216030c020306060a230f030f1c090f05061b0d020102180a030b0601050d0207170a 75
    0x1090280390024450b1180d001180011780180a030300b4001303d003c00c01100c100040000c4002850300901510070718101140b20401078214044031911507030601002007004d07010f602c14201403903016500c41084002c200c2c1405801b0090789016810050200010350b9240c807600010b00d4015449a1030f2540e07130046040c48824140181c00000010781e4504a681c04107941d1a00042041e800c07050002c0c681d00c8480e40f0301d0003071050040848801c1c000c1c0c00940240f6403c00b84004201c0d0098054401541e124070412004428034062031445503142c1406480d00240120426030340d42003e00070300014101c03080000c0c0740140400800c0c0140d8004504140580141c3c09015034514590404a425904050030b031201d640060042d90300403000800c6030a11000146041c070401d240307000607100c4248004400a02079400109a440c2130200b005800b00076081400c040011290014244402c585940d00111200d6201b07003810081d054081c0141d802260b4100104444580d06c06070065650180300f001404 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 319614316 1250 319613066 319613101
    0xc48060e0d0c051e06061905150d0506010c051209040b060d020301170102070818030c09071107120b01090b1203030705040302041112040323040f0603060b0307020304230303070605 79
    0x100300070101303040916184001000da82081040710103445420207000740f501c801201d07510031680045000c1506580b204160004d24900c11880402c2c0705980c1c0d8100103448501504200800f1030b880580380c440c0c0120710001404040000500100d00d0702071100000e25581c1091016443e01540040100414034010030881c1c80304d0002e200950900c1050b8950300168001c200030320202d0b0400c1c441000095138117011645c92558010708000d8142080503000f040110380030040403052190b01c3c00801e203031001c1c041d181c01807540241070350100d07800d09140d40d014001203520a0f0700100007420400480600b0300180d80320f8900c07551035030f85a03403135801001f00f9030b90030501409114008011911341c488056909581c05070f0182401c940b0895440983c4030054150750742042507010208005c207011903504100c0b03044031920380e001e010640d00d600c2e501c29684000e540e0880540e208020802c2440200120400b820313400e071040200c01c07003010020a0466104403000c551482e130303480c100940f071042c4600912 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 319615566 1250 319614316 319614343
    0xa090c030509060103030c02090a06090507020a06060b0708180301090c060c0506060f0315070203090303071b06140d0e0a0602040608070306080102040f0302060705100c48060e0d0c05 80
    0x2103a5407451b20047d1180340030500c040c0c069a200800680000100d0300050010010301100b085145000300700203448100090045814605000c00043c1078072000d801c1d2050290048040351400c121079003c0c1455030481c3c12003c0e01135403030780d002001141c1e10b0752216000b095031380ca4501817408285009070034444001c0c0920b03c6410780c1580e55613103450000d41d52040d418800152086515003110503442d50045d990516814400020800100505603490a41c074107501000310b0b0b480380c2c5038003064440364080c8500c65520403050096940f05030040d00200304110070142550303c94032103516000160b1784a6000b12000c91101010700c444250300d0b2287d000213084080c000c42c1010708200d225608013401e0300c00030380725000c08906e80c410300c0001d000c52569401c0c0c1200800c440d400c0309201421100c6409100d4140540c0005204000c041000d840c6480b400d80b01000034040030340900c03840788045418410b607105a95035045202990042082d0141c0101d180c8403d03170b600c0903e1a02625090840810341d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 319616816 1250 319615566 319615573
    0x1518010201050c07110a0302120706080c0c0d140c010c05041e05010e010c061b0c030f08010e0705210702010b12010605060405011b151e0911040c05090a090c030509 72
    0x21401c080102503890b000c0e44202e41c103481e101064001006c030010307608060351062411050440c4510009001012105651505142641d0b000082052805817284203107068000c1008120031030f11800017250148646c180b1142000006000f0034216100c1461200104100103014081015403114640e441c0d51b401e0407103034800f41001c000a06082c0e1011740103050000708819001040459000865085080e00505d03030100c00118004002d8021081c054010401584032550001c3c400c1280506031088041c0c04800c07030300d0b01c03601140c240c0d100441d8030740d00207603500718181a5107000758445e0168501d940080b407941c200104216401d45c0007a14503d9a80c58841e0801c256210a0192422a102400c0030f060841e0403d8100e003640d0701c0100d008000300d490a60f0b140c00741e809944070000c101c0e0000c02000d00d8203450400c0c0f43c100e8410000c090010b40f01010f40c0804d501e001e8004054882c030a01e0101e040049450100d180400c0e1600009543e0b034540b003800704001e5041c41074650016140005 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 319618066 1250 319616816 319616821
    0x305100b031b030c0412060204090c090e070f1b050c0307050a18020708040b0d05040b1e13020103201902011e0b010e151902010608032502151801020105 67
    0xc0c140d04030804a00b07080b0002c040000740c50240a01c00b80c90084c41c2640d4109a0441203180c41d1009500030301904100384d1410030240d41c030303d00c07030421802541c2c03c54030303c0d0031a6250500b06880203070182c0c2820040080b40f000e80c40901012650922084e80b1440041c104190850101414041039030000341c000c1010318020405268000b480c0400780128540c016074542d4a03041c06002ca20030b80c3c106002813200003c84a240ca4501d510051045001d1842c001c103a8680b0000d842c511001c403842ca5600e07003a418040f900301c142e40400810840e205050014404c1c804890300e180810300e43c1754140c0d6410001c01c410200912240c1c40f4560140140300800118046805114501171020f07101c5100380d6844000c43c82d140d0081d5a4422a81d0340180301e01a2880d2401c1c01c0089035002e56032030344404260180000000340140102d009503401c02003d1410844c075560b100301c1d2000010f460580c070950b1a900803000d03842d05e20302e020f004505001071980d10f9040102e0100714203c401c01d020304580c5000304 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 319619316 1250 319618066 319618081
    0x1103060a051e1c05060f0708090a03080103030e040b0a06020d030b1c080310091515021203010909020a0b0304050105060925030207030201020c06090f01060e0c040e07120c0305100b03 80
    0x42d00c81200c1c104407400c8000951000220f80214880000188684240400d010445500b54100c82c403600d40c1c1e55400505907a4019004d0700c580704200c008000c202403000520009000f064084000b4401900009a80401200149110110354030290150f080070f112200500d90502405540c40030076074000440c1141c1a4403002034010001000d4040352000c008150f04112040c120702c01031071308031414400d032401401951602180c42c07141e21181118401401c001743d002090655003500004901411607182c60200c6024042c140c80c200c1e482003108601040e050b1200c00503500880c09003000041c24a00a4203010400d10058005a5814190081c12640c2c2c1e600c40c071407104044070b5180150702c5035050f01e81640039001c0c0c250f02d4902401402e0400c41001c0c000141111900d00c220300a2040d55503680299000b81d1040c5c0d86501c0700f003000c0200f40304072950004015045465403400d080000200c0da0581e007261031600351000042c2d102d805002e05070600714604405440c00c00501c2d0700c0c1d41000c80 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 319620566 1250 319619316 319619359
    0x100c120603081e07050a110909010507080f0705090604090902090903070c0b18310b0a2c070306030b010e07120b1504030605040b090303070c030e0604091103060a05 72
    0xe81d040503405800143d242c00c030b103600050358845903000080301c00079640741c03504443e00000952024007850b50b400004030b9503c0c1c14040d850107100305403981921501e03040211508401c0050045051000400c408072154a48600400083c1010000014010040e1041104500019001c00b145510174451140814034105001007140d603003240a0b5a55082081c1e0512103c103814902540b116071905c4045078040400c8040140e05c408015040405020007403240403602c2d0303010800d40000e000b02080c4a03940303212003a500028042070005030b0b030401e40c510408002c041120708100084c1c448104004010b00d0320581c0740940081201d110452030456070050155120080310103030b46440345101c43d00e9071103002025000e06030301c1526a81ea03641300d0400c500504802e45044070b0282d03c000021b4004032021060741d0080009607111b030854810350324100e6200c61100702032a801202084001262311044c0300c0c0341c200201881c52540c5a00c0d180c800c2000e00017240d8000380c06500488852122985820b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 319621816 1250 319620566 319620577
    0x90c0903070b160204060603020a27030f06020d050c07030e010c03050f070f05010606181202090f100f0f03021003060e010504020d390f1706030c03100c12060308 71
    0x1080310b240c855101c84403405403040901c0380690040d00d01400480d00603850740040109101907213500002d141c0f04512603441d07007150070070505040407a000510018114801900710540201400350500030790010400c2101e00503281c1d40711a8038001240c5041642140c15030f40c0f21407090078510303003198940e10090100d100c2c16403251004400040d90360708001c400039446848d15003100c000c00503962603c0c40580803000c06040094540b90801c230018500c841800c07d82c1c85254050009100342d102c1003500c8507212005066119000052040440d01140a004110007440410380d0b92818519600601100ea00c0f40820380e0101420490107001040300300c0509c40c1103840980d0b006a41d00041081d48000304543c070044130480050340c542990504142c0d1407540074120144220165151401c0b00b6a0800011a006400310b0544c62450080c4861079181da640300001805588984c0483e03070009013040014600740d80c2443d9200d400c40301d48c550107001c00d01c80408046007040344034110b843e00601402079 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 319623066 1250 319621816 319621829
    0x91a10050f0103180b010f0e090304060c0c03060c201518010f1d0105010b0a020d051e13231c0503091206060301111602010c0c0b07060b090c090307 65
    0x4a070048291648a81c4c042100d4038400a0380f40d807524290300c2d2200d003031002840b03003080000d00c191001c1800303180460b00724060781d040340041d481c4c603103400e80075642030307100c0300b03080d6864a000080040492000e009011f5481000c3daa80101008000c001c135000d01d0300d01140220711350017502c000441904000155404c001405c000c024203603540482c0d02d003d842c148101c52440340c10030000712964400303100801d9809038200021f00180e03880f0a03548032580070742024080141c0c0001c00702c0d050305006400402c451030a000703044142d42581e200e415810b5003c0914840800300c16603003005000d4140602c046600305c064501044028810f002504a013903e01d001c4141500b008140c100b080f104108660380031402600000b25098800b02c140d460354000c4610798002c1d400c0040d486800e50136202147d410119509204540c0c1d665030700110351030b034080c400032184240500808500c1d01840c0c00074000c80c600c100c0380814150004070500c40104405050041007002c14001103000c1e607804111201a02d91 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 319624316 1250 319623066 319623079
    0x20304030c11210c12030313062c0d03060501090b0d020c161e080a0206030c0702180c130f12080c0106090c03020304050118150b0d0203030d091a1005 66
    0x120b00c40050b000724004501005000600f81040c4102c02c80840d0030301101c0e6088840d40c4090400c40d0380c2d9500e91100b1295840c0c0694440802000100c46501c840452003c95a0226019806a141000d0132105010750025903208010403000e16605004200240c00c0a207807043c9054074100c031007115405040f200c010300980124a0440f018000c0090800b40304032511150803465031968100d040000c6240080d50b040381d6008089020700c0005400000c035a805401b00d40765030740e584002503aa40000380c00300d82c4050b06003000000911412200c60003030121158207651605c0310003080320071410a620400070340306003403005c100c41041c4064400c10705401c2041d660340c503444000d0705401082103802c4075021350314154a41c101940d259000c0d40c0314070b2141c030080108100d10108802c0644507000700500300202c078002c00070802d040340c0000c24040e001401c40502035185072300003400d507041080700c1203015664640c50018050410720410003000c40d0010170b8264104600030700d030308941c2402454020701 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 319625566 1250 319624316 319624343
    0x9042f090103020c070303080106080a02030609040f14060403052502090606031308030103060c0906030207150c1209050609061b071b0308191e12180c120312020304030c 74
    0xb40a50112030040c4204400c2e12000c60f101e19001d08444c03400e0049000080b81500040d43e1401c482c42180d000700001800c42d2429692980c1d00d00d1030026a810441e41701c5d2402400c0700a220382000001c0c0200e2194a485407103103e02007415010050000b05e1142c143c003440803540150301c400f900301d5040b0740e003a00d5466072a40c3d0303802c02d2011107a01420040c40c0d458008000020300c040c0398002600381603256161031441d640c50004600341c1c003981e0304c0030b030049201c4010760448070200d0f4007c054a01048c10300304850710201100000300c03400c9035000d48054002100b00201a041840030551092419103070180340d040c442c108504600510700003c1410000505440422408091080007150310031905690750f6402581880d400e40c0781e1032840003007090388401800c0385500e21ba22100c6804c05030344440081a81160140280c503000c0a6819002422090f8901280304841810041d08105d0110742a58065140c0141100140d000c44000c03644140180b00009078401d81c01140141c01c40506c58042 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 319626816 1250 319625566 319625569
    0x1404020f070209040b09010f050c2d07030201090b06090c04090203040c2309060109080a08160c0806190204053303011413050408030106110703020303070809042f09 72
    0x1d10490001950000c0d011007003004211460809a10030342c80d0310000e10242c8402c441c00c20907140281ca965014400034465510224000c1e003080c0c9101c04618000050340300030120380c0e103140d80890000d40050751076031007103401d00100c003c155811070005d90f02c040107491b120b59a0340302c6004501a00c03800030b40020102c3c0620141c142c0a5000d0801088000800c1d44014a070f00108881d10500d540946050000120a58001c0609008032003061001d04004030b165a1441829803105e410265056045850500440c01405442c4094401040201140d0800e14001c980284001c0d849516a03401000140465281c0c03480401487d441c0a002404500b8500c5c00380401c104811b217509004c4030301200008214201c015a58280300c0259681c10050701003440d4201662000c0f940030341060010001008298403c0c0c09011a0340317541b000b81c03000c1d982c89900080c02c0d039000c514196810740002c41d4010f5030b842c05120742840d0001c80d1103030a02490030002d20401c4030003c2000802d44000c04110041c41d07 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 319628066 1250 319626816 319626847
    0x10c0c0f09020d050703113f07020f011806090602120c090f18070c0812040c051002010b0a030209100506041503110301060c0f0212060a0603030e0a140402 68
    0x5440c082654245041c0c603444050001c0d0000400820701074241004600002e010341304419402c1c804202d40c41c036086010110303803a882c00c110740b4661003002a0b0480480c0c0c0301410002c8240151569121030305003040b1274020300c0c02c4504070f28004943d140c032844010801fa0003003000b24040e840346004c04c025040e41030120081c0241c11164020b809607400f0000000546001000c4400d012220711962868210900c1003208a0701501180031441c0c3c40401c41c4640503000d15502c0d0382c400c5004500e496140e00c041c1c0350440050b50212810407203403005005030300e00480c80714108500c030710003004050220030005900c2203084c80040e0140c2e200700d01140003516000c140202920700034114658030f5580703001c049040c0740c4a00820000070714100c0c41e6550340724020112812201c050b81ea1282601030b54684210341032030807d0491740880707404003103035000c2c800384040e511440034800002241171035400e014045001d44507526120b04c0c8540401e002010600d01c0c412100401036900507100c02400000410 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 319629316 1250 319628066 319628069
    0x12030a030504080906160c090c200c120c01020106170d0e2103071a1b03150d05060601122d063215162a050103050906090c010c0c 57
    0x2002480040c1207084a880b034201c0301ca0f018814066600443e0765001071704122655102c49c0d20020702907203602c00c290500102c0c1d044039032880d80c040c4d811000743c4100250040726100d401c000e0035004640d0465941d80c0a105400080c031600d81000d807000c403900d5034107448003c004405802c2c44050074040020362290054002c092440d01201c1005103940d010880d640d4009a5080f01d42400f26804501000c8115603480e0081047c403031090040c04402c40510841c1e00028031703200c2211060000351945640311042d81c1034580c000d00250030306082083c001090314880c0310610646034184a2400907440d025190702292421500045040c0f001600041016050b1944464521041c03000d20954004a2001e10b11594444031446129400f00b0002d011684c071441c0c2c080914188140150b01400c82100403c2e18100e214001030100c0d050520585079515600400b101c40c0c8164121040c04607503018403d041c4c0000013400141a9403805c01d1004c0d83c1e8103401d071603060420542e0445030003040b0807100ca400 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 319630566 1250 319629316 319629319
    0xd090606180603060513021c03180308070b15011e090506040e01080d0903120c031110020306010f0e031b2b0204110c060a0209031501121112030a0305040809 69
    0x10108505026404054802c6010540f201c1d4a0600480e00304942c0c0c6002004055024050206c0f14070682c0f114040d80c0c802e041c056051100c6800718800408456007284080c42c0300d408901c1d1644182c1c280030a05010003044451403442400380d18009030380140002c40042c03241102c18140032182c0000702e40341001540500d8010b03002140103d0b2440359443c0d800c0c1a1401c201c11290340070900c0c40221040b100da4031000e40084100824040c55500c00c2440450140c020b042c01c1c113103052070604c0c040c1307800009003031201c03c0d42c2d020041c004a9a804040001203180a1a10103031004c5407400003038440f8010300504004464009950120780c07103819041c22100481c140002241022500700189240002e1040717114528220490458600d01410350300304082141c010510ba0703888281e460004e44c0b04c45402d80d4941b09520039403014000102a85d0b02a00061580c4140302c4138500e0025280b0141c4030205102c1c4901c0d42c0c030f00c41c1304500002a242c0c1812a07240104843e1142d040111712031180c0303960701e03 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 319631816 1250 319630566 319630589
    0x30501020f07020f0307060c060b01091502060103060b0a2117030703050114040204080c0f0303041e090e03040510050a03020729090303090c0d1506170706140d090606 73
    0x41000e04140301500b406402a034001c40300b01254400c05454071601e004d1000441c51802403c000700301554041d02894a040c1409002103881701c04d01004814450152070050f44218014400c1001c507001d040c4207503005650000302d00c0c2c01e2417100c0b602d1203c1046108120144103900b0428081c0d207004600071407503100c12a17503580c104400000c02030700c1d00b4010640901540502840607007042e1084808035600d00c2d000c0c00031301507034900700010855018001c41c4e02d440300b80320100300c070702441c01e00d0300c88009484169910646050038800c140c41400d188000150014041040369031103c0110b1180c1014601e08280d8645100703c0030360080c00b4082c406010712040340200f24440c041c0000b641c0c00228440d103100119a22118095038034402110851340503042100c0b42c0342581032883c40f1012261050b5228040c00c0e1008604c3c4085440035400801c004544007c06043c084090216401074003503850051100c0c409011001010300c9003801c2c00c43c107250350b501404180314955002c04042d260f1040303031 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 319633066 1250 319631816 319631827
    0x60602070519120b1510090504230114090a1a0108070c050709060825060c050106080d0e1e0a0e0a0b13020d0c0206090607080912160605091911040603050102 69
    0x81c4104c100849403c040035943d10542c0100d03260224040064403003650f5178000d51400c2c003040c40040c0010040e41c0e071181e0801c45000503003140b5120050701902c0c06008401a40541902b00680c2ca03034050021b5401138500604a51031203040c04800e441c5c1442030a00341c20b1601c903048212000642070364054454020741601090345e14003500f2010844004104884450010155078407003461070040d548000c0380b1300d4a0801006004985020456014800018455544004107400c0c00303503c2d18401c0c0003810405603500e45d45030000072001144203170860068141082004604454000d0141c0c0001501c00c0d0001002400c0e243c04c140b00f10880504200148020b05004d0b001a4000d10000c00b942410f000e1810310a40c400141c8034468402e0b50300512041c1c40b5414282c032110405070110055000e4050040d224480c0107000b020950180620303641000340908001c82161009017240c005030708500d000e181d400000003803c07001180c2200d41682007c000c180028000e0520340d000030015400441d6 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 319634316 1250 319633066 319633073
    0x705090d08040f091103060a030209190204030506010e070c05060714070206120a0609020f180f03120703081b090f060913020304060c02010903020d0e0f060d0507030f06060207051912 80
    0x800740484c0c0004806200403c04640e4268032800200ea2468106408403030810162400f0555507411070003280c0d41240303450003055000c2c144d034420b420030f031410760101004118040b07824518590110b07580ca08011558500d90b60750740c80da0400340c082c40c02c02041030032120302201400c00b22903050740d00030203040d41e40c2086000011510411680c0e64036262034030400082e84101d40c000c039400028055011464001509080e00030207201084a03a04039000814140c9151410440d0960f000d401145c11600ea00c26454014564600141280c05000d07583c104a1190802c0b001607030f403100300031aa08642c0032180408180c0502070180300580c0610144034a40d1940119802540140d00541045c8080802440142d080e11243d42c4002d006130311103840750000520480070700c039038100c00402c1a04400c0300c64000030050b4200401248059a90b40300348205c081e010f1081d054200360907581130095914164029495100c140320b901e0103404400d402c05800d840031710400024252203d01007000c48074a08 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 319635566 1250 319634316 319634339
    0x16170307080901050901020f0f07081b03071202010b31150602010f020f0702011b0501020f030f060d081605030405030102070303020a120b0913050114150102010b180705090d0804 78
    0x8442c032010354a040c0200c0c02d10754060080304d02c000d0040595510b001c405200d00754040e4088901900c44603001d01c02c80184800804c2c4c050012082200103588034800d0741405601c40680c40c401e07100390f80c980030302a01692503098031042404010082d40124041803e040c0c2c0450030f051001009031441d00038030b0380d401803a0869240070b54110380e00802c80710002d11500d604030310401050005107041801400d005621800c1000f403880b45002c2c0c104541e41c0d02e41c1c1d504e0700366000224004c4410030f0100400404103141c0082d80e0b0b00003002c40b0301003071522250b11000f00310320400803109101031000c0c2c07904051100400840d002000302400071035580c501d41c00c0040081d0011052400000c86030305100c0d540500b1402540c804e00001050320303050752603a90741d0401c8215451011540c1c4e54a0b90303540503504aa000390300e0310400d00962419038070b0038040c00080c01c6900c1424810312800f20b503210b50901c6464040d074282d0104150414540d60071030301c00055038000301c00030018820b580010b0301040786420354 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 319636816 1250 319635566 319635571
    0x2a0a0602011a0315010506030c0408011a09150a090218190807060801080606010309060f09060b090a0c08040807050109020306090f0610030206122d011d07051617030708 74
    0x2c00100350031101e8141015264014800020380000f0504014001403406500464100741017245052400f5500c2c201c103420f40f082508a08408662000702c125507042c502c1e0038540c02041c05810a0300320100c003000800f0448180103501e03905901280c00405656039000180b6000c01c014801070350003c45100940c3c0315a1940203446a80c0545400081c00d20b00600115050340c9801015040d156100c81c01180101010303c02030314016202d8140f6406403003039100310115a8000d40d801f080e41c84006090142041d40980b50070840343c50b2201e940c0c0803d52000034540c201d035100c42001d9540e582030820074050040e404000c0c0d4580520000c6c800384800008024914108130029100c1642c0c0303107185000c81c12051b01c00a50055010044450b03102066400f565004c8501246072104030800882d440c1c44401d0400807000f0002c001005000342d0040407118020101c0c136010b603894500e40103031700078094001d14200001c024003102c0145d003040110f4000803200728088814030b0f1a0f142a07040204603480a = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 319638066 1250 319636816 319636841
    0x506060c161502010c080c0a140d0203100e092e05070c061b0c08071b080f0c0f18070908030d05070818030f0c1608010c1209052a0a060201 61
    0x200782c0071890700e8018003496109540075100c452040d80d07408001c4549500215800f010004c41d0011094142d0200005c1e0071260f55000d4010b03140e280801e401d548521141e0020314400450030100100032100041503000034820305071202600762081840c41203046851090310034103080ca401c10401550003a041d24100c6d014582c1032003081c41890380b100240f8185944440059512001e0740046503c031402480c0051040300c210200c480c450800409480cd503400a2540e60402035441c0f111000c104480e0910381011125014801000e80c00aa0610628040e02d0030320003840000900c098007a84a68001b404403405807507131a81408114001850101c88000205022001082c01031401c1529401840740d0a070003586011907580c0b07180c2081c4c124200b206814810748001e0300180340351030940170040c4024800032030290310210001d0400c641740300011034024513001c001004202c0002c0c2e0800d0f200c3e00c10ba000c440e0b00500c405045107040700c442c5810b401c40c400d16000900c8030b5056000100b00f14a = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 319639316 1250 319638066 319638089
    0x30d150e010609051011011a01020d030605030c0f010203041a1e03070c03120902060c010504230304030f0204091a010905060f0d020424060e010806220506060c16 71
    0x469440003400c611082c01044001055514244428140010014148921400c200240c2000c203000142940d91101100490100500b204015941c04014000c0003240c203080a00189041c038001c03c0d0344100c14110a8882c0c80300580d003440e181d00903c110f4001d042000e401c0c0740e00403d45c07100410280d100a80020210a05a440c0b8800b11842000d6a001c0c80c441d0323484c09031044468a0407a88a101c040248e021143c2d2600d4010060781c031540104803641e84800041524a40760508203520402941c0010044a081d001d001c00d10340b00ac4101d4081e079500c056010344003d110700200c3d0042a403060001e100b900703c412a403100c4134004040d039049401e40c0106214650b0780da014844800210303549542c00842414031180180380c250841d4481484d03000301c1d08440c1c3c0b120414010f10b802d155003d0004603105a41948031941d200c56a940d0240094a111002011b003801608070b407907442000940e1681e4550102d026079079070800721440200c0c0c1008564050710380742400258201d01d44034a600303082d07 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 319640566 1250 319639316 319639319
    0xa1d0d140a2102150406110a020f010b01020705030601030b0903160602090a08070b040e0a0905061e070905061207090b0c0f100b06030f0406090c0e040308070908031911030d15 77
    0x9150303507105101c0601d0f6001c1c20042d900300b0307040d09a022014008984090703d400100d440080c13604050b00e400c17207a590042c41c0c0c140113003030081e013114a07152410341150400c44c03090000307031000034450381100d07442184954142c0d620300249086d40585d1040c03004003955481c0042c01e012082c1c0190144060441c2e9481d412035480c400a079560b1024402e01c40343c0b940510080098803000302c22139070321001401c000316500840303599440c24048111894a0892000b031440107125100c1c480b400e500450b58205202c0c01801c25000810390b01400e010039080400c00400143c0c0f89100c1d14016004042d104141034a5415181031603407103004002034582c0601c6440c2480b08900c509004c1e550a00078090710681c0303151203880078045800d800174801c4c0c801d991500310020000c0d000c0003840c0010a0341c40307101400d07070400745401000120040d001c0e008200c139089081c000c0420200c11201002440403400c07012070980d04040d281d0740c00e001c01c01d0450340404a50300030240c0c22504030400c41b1040a00c560400c5 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 319641816 1250 319640566 319640603
    0x302070b250206090d030902060405060a0c0507080a03020309040b0f03100204090f020306060f0702061e070b011d0106030c0e0405040606050913030813030e130b0102060702030a1d0d140a 82
    0xfa070048540d201c0b5540580c20b06000540207600c038806141c0043e015038641a00c030404109590b00112111001851115070341040c0041401640e02901144d4013600c1c0080340d6483c002d58038001c001d441449142e0710f0021a01959910074200c090b0300001c0c0980b0501b18801c1080002904544070381d42c0c015007001211038000c00c540c0300312480780c40d00500d183d0400303070046411030080c2c000b004100e8000d2400c0004090803080300d510707a807039020901e0719990750f4071032880d02c042c0c0e00c24183c0c41a003102d5403c0741940070b071b00000301100341520003600e4001000f214008085418803110711905812034509410301050001d550032000a607801a11203a855480340c40410aa0700424140540020713903900101d0000c52011907110b103424003d28240001e0300c9043c0024640c1519510075020044d90360b0f110101c42e580502c015035200480340003640c100728003200c000e050242110ba4075004071031901c00d02016546c665006004007034110270071036402c0c014070000307541c0c030303040401d0660b100c1200c0346001404 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 319643066 1250 319641816 319641823
    0x605090d020c04060b04091a06160515061f051608071b060206040809150c030a0e060423041506020601030b010b040605090d06061e06200703120302070b2502 69
    0x171180d01520443c0703458648883e5030010117505100d0354804406d40e0f91003034a6a41c0b040600400d0411414488601a607071420b6031900340800d11568a91510408010459485003010800c4022403103241101d6504144101c480e0f120b07081418200f00b0440803103a0a015041d006001054841c000030040300701c2c95244508140e603284240001070b8444000100020040006000c004001174400d81101d0004820080f064001c05500f200d107905c041207a800aa43c4042104006c46c1c0a032002403809040c003801000c0760a51082d80c03c581c215180300e003100380c0c4580c2d10601e520703c00f400669100a488020080d04c85000303100c2903402c2611000003041d4243d6850803102110b21f0354541918111050f001d10460b910071440988840765a010b00240e90300c070785565490544144551095041d081c00e102405540315441c0f0f5409040e40002e001101000009801e002d81e90000312582107140c06160880107449031403402008040b079001070240308004016014038014440142103502c01e00c020b4100e98 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 319644316 1250 319643066 319643069
    0x9020307050a0f2619051516031b02071205030405150903060106170601140c152205031e070c08030706050604020705070303050901020a0812090118110108130605090d020c0406 77
    0x80c10b40000066070304085d00b80b8510310520344a02c054031940c00102880c8410010704541d0303101c001c5522a10185010f80c103215589041014000d0348180c500074241c0295107001a0144030110392020100f1010b210b800c10940303008000060951a00341d9030b9041d05442d50300f2000030b10b800f07403080300d001160903401403980306c80394290342851036055540c1d10011101540302003101040036900700002120140305202001c445500b041c003440840c104000c2184c81c402c8040003001d01321982d0700300140005c40c084100c843c000840c1d02e8010320800d0350291101e01c0c0c451510700400b110039030540000d80c1000031015004990003000100406e03a602018801a8420800002d00701c0d02301c003900380700090051000d0f05d031b00f00c810710481e80206901d9940d00c266500c05000c881091003240300300030700c0c10b100b40501410700041c4a100c090413000355a520940704100480b1034180003030000001d29010840b0342551420390042d00c10700160810f100c80940358a10047d20314014054641d00400d20705242c0164030 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 319645566 1250 319644316 319644389
    0xf1c1101020c0c040b03150c090127060e031203010b2203050105060102070b2802010b0a03060b1009080d0507110d03080708240108060303070c08030301061d1309020307050a0f 77
    0x10b031669550610030300b40d0361014000711706020b2103e10000c0303030f1101d1029400c900c1d804004124040e5051336009000d441180003024420b5102c000341c881100101c2c0c05582c112001412856140d4014aa8141640c10195130329240c0301240500001884015044507000b46400e80a5402c0c564607214134502c0707440780044009015940f801148030000695105030152031035880005a076034440c40000311031814035401666501d86a495503c414640841800160031017810100c1501349091122a01c9600401100c02070040c040766079000d01031100e0032408000c10040c901c0507030700310528019140d000103540b9070300000d0404001640d104c0d445540f868800d10f2010b5031511010f5900d00458201c14028040303500742c00180130407030008041e0000f00c4013410650004e035071258103102d0010300080650160a25001d200c04024100782c9568031004ca051038040c00c04691030016002003841c03c0540c0d80425040341791158001012209600110706460980455403e40382c6421b540c8030000d4522003480 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 319646816 1250 319645566 319645603
    0x80304050609091315020702010905060a02070510120507030501090b0a27140c0301080d2a0501090c080304150c050c01050c1002030109050406050106020f1c1101020c0c040b03 77
    0x49050b4640309115a9000e20204c80c0300822062035a07a401107804041c50307280b00c241d00410b00e8011507030000c82050281c042035030424107200702450000e50f901f04501c41c560080721080d0807400c05e0b9110701c43c84055094104002d10940c02c000c00010010602481010030b41454003240302c1451800e40411000c450820515030011104580000b2860f101c0003032528104e41d40740d82c42d03160401d488000610410340d070740c034907a180d40c94588040c0c02d1014444d40081046440d000e02c001049000c805501840964260041d01100700d10300356006207851000580a48084100050000000802441500e1880c6503000810011030001d4800303218400c0000c1217a0041001d00d00b1551260001d03020048901c0100c030b800300352000c0e003501264400e03080200071507184c00c108414850b803401607600400031072008003c8203104070341098503030801d1020101c0380744409100d80310f11841001a070b03004020740d10003155900c000030a802c0c0e4032005816424080c504180d14080c1601e40424202c0316414080e008 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 319648066 1250 319646816 319646827
    0x50d0c0611030405030f010e010b060f07110d06180210030c020c06090303070b0106050909130b0f0c0d1404050f07060c0323070b040516081506041407090603060803040506 75
    0x2607440d40e1601d100000345100c10301c8002140d50701040700e503549220150002484880400009080d5070729441031a00071501004905090315007d01210174058000c404c80450750500000524213411040e0054456428a0721211103410f000051016042c030890340d032002c580440409400b0360306203548800241c3c00406111703209003042c2009180914004095034139111080c2d8955a03281c00a8001e10700040001c5800c5c0c0aa050550740d0300d4004500d82c3e03c0e40115800342d0750f42800b90600410403100e00321400c020030380c03082820050b40c41d55801c1c10b005003c031241d8a600110010300444094a10b07205202165a1050022402c6401d0364407540c1c800800d01e0a5031406e6480350a080019030001e9014000c0504986580002d03004043c42403020003e20308081c18005e2034032250381611010814161400c200312200021900700360b02e0000d80c1d6064960341c5500043c01408501c200492140001d4100304c1c01c6541b02500100750f44094404100b503d46441c0b06941d03c2c0624064950081c404011 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 319649316 1250 319648066 319648079
    0xc09080f0c0906060c030310060807140301120609060e0a0516050a061103120112021807050306270c03041b06050403030309050102160501020a03060e040218190e060103020406050d0c 80
    0x10581d500480c013034256444d0032882003002c1c1c9141d100329448486a4007150081c40034582c440300180d0800268a030684c400c15811090070f49912040c070901884034481d80c0e03074004200068100944c43e5400005c100300c4010701c9080b0503140c3d4220202101c0501035004511855080501c448055030030240c0505130303a906040d07003503c0080e48a02074121f18802070000070b44000700402080e0180050700040400081d443c818800c0303061084100c842500320321300420116980c0715042c0c0c0c2e806039040f40c56a00c01c0710404941c20340c03108030b40c1d4403c0b1b00c075001b0010071080c00c5020b03004500580c40780411002c0d01c1354400448244000781e00903440082c104210400109119800807600e403030041c3d0005242040d01801850342c810105012070f42e80e5000302d104100190180300d0040240b8610418001902c3d10761700060329407151402c02c8111615003c007268502c000c0070346000d5008220132040004000341400c4c2541d82d0402d06c400c907caa0301f4401c002c0380c1800c00c0c04001c079020744d200f59405002400d150 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 319650566 1250 319649316 319649329
    0x108010b0304060203042102070e0f070e09180601030b1b07050a060209040e0f0609070801060608010b070507030503072a05010f0e030c061c06080c060a050d0f020d0c09080f0c 77
    0x1041134480c40c01c0c22080c91203400000341d6884c2c100714141c00038a50304ac94020000c400c80d000600c800c0f250a102803c11454581001c40342c00103180854422207640d95042001a4060508003409a28410031001004001110035041d029a840003140004c0340e10a1007400b83c50700c5940d800030300a400040110300004c1d040e402414014100034000300d0713800a541070303c0749070074540c0b000300050780d02910501116040c1813006031301074141440240034441c09c0c018041d00c0e4090610800452510002d110001d11005215400256600809407561070805003000c03407080031042c5586500d684202d20b00d00203000006452000c070b5206031a102c1c41c0704900300c8281c910502e142c40741d613018000e901c81504c140e80c91a0041605118100e1032a140c401c100721040226000da4002000c0c9500203402e240b040d40d1b80c5800d43e0036031807084c9021941c41d00c0e80c3c1204000b8116100145131818008560035843e11a0307508800300810981c0d6880b881030b0303582c03031a85030307140c01039882c900c00307900319070364411250402c031 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 319651816 1250 319650566 319650571
    0x60803070c03080f09041a041407202113060306030b0402120a0501050a1a030d05041e0b04031208070207030809040b010c29010806010e010b03070e1302180108010b0304060203 77
    0x1250704070f0034a400702c0c01040503100145140c0340c0c59a611911901c07c0c0c03034540b003a03141c1006c3c0000812041d00c0c05e18000f07024040d0f0200113078510001406000721044041244c0b2060b0310415155485079582c4e600c15000030b402c80310032203210300040100440c1840c480d1241808480e04240c0100c43d6403500d4082c41403030380c040285041c9901407041c8060124409015660040381103200004008085070320a9201d05903140c0d07100d1081e0441c8080c9003c2c1039120040d1015a981241301807a40d54549c11003140344885580880004e0b44042130001c18084c800703c0c9500c0350500c070b484020351961003100403601e4031014080141403200134081811541010340c0800d140800c181400c00c0d0116854481050801d600850194807800c040421f04003031015003004c41c01841c11000920081d41441440c214284050064400a00c03001c400904801e01c05d45500402110250005039041050020340d07001e540700b24480d56550740014003104e0154401c1040f14104c0301b405280702d0440d1643d07541c00c00a907001 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 319653066 1250 319651816 319651837
    0x9071802070501060f2904140a03050a0807150b13150503071214061608040f12090603051302241c1a01050306061617040602010f060803070c0308 64
    0x2408400c001030401d12400c0041e02c0c1c51100000305c10300d4111201c8840b40e00d482840101203041303403c00b815141a0040d50252809a00400404d442c1c0e600400c044e41c1b05ca0340b000c2c106103d80b014607020b010b070780380081007064082c2c0786012114100e80c0070b100035203241d100c0c0180c011004040440455802d54004000e10038035031904441581d484c00002d14000c00741e000501c0c1c800800c1030110400c101794020741001d100c0080a0900c0e440c0200010102070743d19881c10f400d04c8000b600160412146240074031066620003042c40b076030800c00b60020045c806074000e60010130714000100c5c44481d200d00031070a100b0b6006002d984614a07044a401c90b82c0030030b0720211004030302400001d51181c0001071240d81c002c0154000641160150307064681058224089418000c0410501116071a41c42c100d440454004d0001c0721082400e140122102c809210b401c090a44007140209000783d041d0801d13011600040b0051000c5501e610a1070b480c0c1c03041100c02054108659001c00004d2030502c0a844a040c0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 319654316 1250 319653066 319653071
    0x140d03020c2e05090a15090b070203010923010c1d062119060e010e0114010c050610031703091c03020c010c0906121116140a2405090718 60
    0x2248511481d41d0300b5601e4201156020030004c256080241e1194014408508055035451000c18064407080284c001d2003806140015103905646003500f1900c1c03140c1d03201141c020900820036250098079401c110010701c035400c0c8090511860310a000c410990845401e032a10004071610812205901c400c400121244d8020700f001d0b9051042d685183c450201c0010801c1da0064110416044032000d8110f1040b442030710006008810b041154141540e031914841c0201c5480603005841c1034240c40401089072041c44100401c0500d00602642264410401c0c0c220700700302c2448980480c042150140400d030f10096a81c01884980d0400601f41e1119003401860002100d44050a643d0807030031000c045035054004200ca07a9010801d07013090f520900040107080341c50a1014220303c15940301009514040501034240442e10b41045902d01c0840102d07206250180341c80100300b800020032031454007003029244c1e421840e138010755200c0c0c2d10620240000c03500340060240000032200038040d0f41c40c0e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 319655566 1250 319654316 319654369
    0xe010e0309100917060405070b0a020a11030312010f0f0b191b0c03061d030a0e0105090102070909140f06090d080415020307090f05040e07090b1c030504140d03020c 72
    0x392201403204c04290000a484240f030541003051a10240c0d034440460b16404104000c4603c0c1d010032503510160340480f6900642a04000092940c0103600701245803030b50940000030b448801000c02c004440744024491103455540203810418020120288a20b0307117440c03003035920030348030f00490300722b00d401d04100c9800511075890f98132051000d07400032142190b0712010741c28050100000c0c1103203a007070f110082d4501103a040008010350380c2050a581440804078034502e05a000740084402790142040c02c000014103410491424009078592102c50b00660310001000b81c00801d141e841031050b10020300c1071004400c1b048500c0c40b001841640c040380e4034003d041c2d01210a000441c010f078480e642c0d20728120300f4105e0246502e030300e6501c5580704034a4403a003150317200c4012504004440c0110800201010f060300490601d03101e0a24650040c030300903080c03001301504030f40644103481e0464000100c0028801c180690381005a40150169100401032070382498074041c0244103400e00c428000d40f51 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 319656816 1250 319655566 319655579
    0x10e031602190905150d0f03120609021303140105060108011a1b0d030501080303190b03030d0e0d12060f210203062a0f0f030408070b0703020a030e010e03091009 71
    0x103820b41c3c0c0112020545032810305c86400f40031070700e400400f030044603040c41401169894159681c04107000405018605496208492880e8481801414844001d640d20181c6c501640380010713042c003084490300200280540310900c1485083d210702c0e810303150004242d080a98980000c0e6a00212089080081280405035480c1c66014a900c0f03600c00b000342000c11035100b0290a4800c140c224601c2f0390b1062017040f00012852071000800070200b000040e400c4940c1c3d01180c1148203641c03041c1d090a081030240761949100049074448840507a491a901c408d500d03403160207803005807013884503418940c8401e012100814400d83d04a03d2901109480b85801303501103402d0000c06c031030b40030122011035030400c9041044582c80c0c10700c500001c4680d03c2c00300c941104521501030140e40c1c2c0c04c1c101c80480010700f080740c1d482c11150300d43c5d00603050710b00307030b1400c4100100658040880100002e0905144c48140c4005000e40341030401480301543c1080a854184460b071609980d00380c080000d10140080c04 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 319658066 1250 319656816 319656859
    0x3040501231c05060907030902030c040b01090b040611061005030709020306010c06060f170307050303011205120d020a0306050612061009090614010216030c0509040821090f010e031602 81
    0x41110b404400702d000e01d0280100440390360700a00001c1807609068401c001a900800c4202c1d01b00b1040b18000f03900c0c100c0b480100d074800c02d5034200c88070b102c01c00140402c017981c014003030381009250401203031181d0b034601c00b15140c4d440240c440d1a800d64411a014000d00640350060341c1d002a041c90a0103002c51640c4406058030001d5100500c40791400c002480b4000450b1180b280440c000002946045410b039901551b0703100500c9400c102409a01e000c8042080a01c00880e01002034403819468070040901c6900a5001c081e5000209162401c00100c13414034009a401800840005494541c1c0f00018000380e201692588000c00440743c00114500c0110701c29100a003030392410680c00706e0301c16000649010000502070b108030654910030400103100700f0041c0291481628030101c203840718a0702135414003070001c2c6000c00f120a02079091280307803c1081030748504034002c00c5410080c116201f05080360761515501016800030010060070411400340383c100c5d14400381015807103984031000100e8 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 319659316 1250 319658066 319658107
    0x2130b03060414100b06120c0405030a030215130302100c0e060c2515050c0a06020703020607020c04110a0509030a1430030f09071a07030801080304050123 68
    0x51002c000d0000144188040204200d44c0582200c00c00c803600c1914000f800782e001c2c2c0398101c2004940c1c007000070201840c40301a40c00906010702219002c107c940780c003940354481d000402014008060001d82d00c00583c82410700c0081c1c05070041c00410003000e07a110042e001c12850304050040c14201021070340c480c2801040082d080f14040c000c0481000c41c011024041e15a4001c2064042407080c89404100982c045c0d4000300d41c1065603444291301c07101c5041081248024082c1e81c0301068440c18160007103201d5200b42c50990949820042c00e204100403144c1e1421040504007003408004190381c0500300400180c000102200c0c41c0310800e030b6804d03024800c4405610a0fa070003256503112400d810b1030f80d42c2e180341162403540b502040d100b41c0c00200c900000744003210300910603000c60b200120620002000c0d00d103405606844400990460724945d1000c441100040c1020000049501c2c01106460540300c0507500c0e42d400d640070b00e02d000c5440035915618180907004105407507807034207103080100 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 319660566 1250 319659316 319659323
    0x30105012109140a14010e0c0d0f0b1303170907090b031c02070e010602030403050d030f0e16150e0306130201110303160f1e0516021e0f1206010302130b030604 70
    0x540b84d0924014078040c0030702c800070403681c2c1403903100c01e4501008650400c0c0c80100f0303100c0403101011400d01c40c03003003024620003030002c500c0c603001d00140d4802c5400d1451454020340380c0d103650a0000c1015440401c0444044002c1d40080744180144010b81d08605060040102102e0400000901f5081404117039911880540d000c02002c000140c01d0154150040c026030002c0e40c20300340703152034854403945159164000c0560304e20218450104560110f4448240202210286040101c1d40c180d000402d0040801c5001c1c1480e031404010301c01c9000c000b80c42c0015012b02103640ba505403c1800b420f42d007200302e062011802d10307181107010800140d1f10610f5406211a920084580c0c0685000d1140c807844080119201c0c191004503040360000c2159030346481c003550340c0c1a168025526545942d40c00a500c4124400400b5103004209203c40007075004440d94503000038220f0811800107160146c05010b030304010010800343c507000c01d10b11449080007102240c0f00c2d918100180c2080070841d4100c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 319661816 1250 319660566 319660573
    0x621100306150608060312030718081605010206061c060c05090d030801030b010b030408120c1902010203010e0924060f040e061b090a120212010920010503010501210914 74
    0x3c1000c1c990242c0f000c0c0c0c10100590182144581c0000719a000e03201c0100983c7c1480030941c020348001031341c000c00e00000d060346000d07100b039081407180c02d5085120740d10443d030052042101282551070b18000c0c0d1766086004c01c0c10000f180c0015a61100501f107003030070080501006020030f40c0b50b6240c1400c4007440900c05d640706101c541c1585000c0922a02c1030300004440d201c00e204110007c4c0091045600d0381c14802c81c184050740d103404501c4a00c1c850400d1a5442c902d01c8e00c8081c0180c2c0d0150041c0d4180d441041000403540e550100e81544d41c582c000c5420860180b40070b422400380d0348610700c0c9400c00d402410414006d070020000c64240c8030342c504461010313800501044602581c0400ca03c6403402c18511399881c1101c1c00000610f404140c0c011070030070180c0c05030700004551b00c0004c1c1e5183c0740c01440080c4043c0415007044006010400705040341c554802901d80641d42c4079004880c160703003050b181e60b280042c81007090030511504e403030b18204c1e103036585020744c0101f189240c40f42210724112004 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 319663066 1250 319661816 319661819
    0x130c0f08100b0d1b080709020d05092404170f0415080f22060507030621021302070501180b0709090e060a020c1c09050f062110030615 59
    0x5207260518084000d00071a18040c401e89580d542e03410100d030705030307000750005100c84960b10701035002e04480da10036410f85c4100700f00095400405d4001d402601081d0000300060b80c1c5880100361202560222002c101c000d40c2c02c4c04800c0c013112040142c0180c0103510900c00c54000711074540c00f6a200000311204084085820405840c0019181051400c00c2c604503840381800424010020409031800c10700d0240940d0100c0726000083c1d0004e40b56030003507005d000b41e04000f84042c0c01000c160051421043c410020a4484401504024035035940a0004040281107080e60720094110110455055480c3d00c9480605414941043d20450040d40c03d03643c28108994040c100180359840a140b260406035101c59081001c0703022903115884c010007603600c803481d0920300e060a40707411460301500c00710300f14008403036409140002520001d03900b80710030300b40760002c0082a0103841c64444403410801c1c45030360a10401070540390000352046480c1c100c0d0b91a580c0351019144400802c68415408000 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 319664316 1250 319663066 319663079
    0x5070905130804181805210d0501121b030809060d0e03191206080c0f010e03121201270b011e05070204110301150c0201090e0a0e010509030c1005130c0f 67
    0x41440455010142c805640003542d103040d12640046140104400000032001e22100c00101b100c880140c203080401983d132f11454541102c10705104140c030014412141d00b081e61100303401c590300342c980250115040c929104208869503100b101d10101a68480c0e1065403469810005806000c01e00c1e070002400301011000100700d801550411f1465a041c0700b810044400c010441c9407030702d803094503003060660880c001603c907290b079041210703010300c5905980c402e0500400c001e0000000000b51620036640d90362030800404517600581942549041c8903c000c502c0c1c0782d40302007070000c410704180e0040300d089230313002c140568002c40a002280380003e1800c11882d1920031401000502e401c40350030f40d41070101d40108100c1c01e128250500444146040c103680c040d881d801c00500d0f41e1550f40c0140d01c1c01c949914050007440461391003941c00c00c000300d02c11440100984442d501f000005001145007910703500f0180001610b907483c13900e144804a801300d85520000009080504031142c1303913610307122 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 319665566 1250 319664316 319664321
    0x160905061201110f070204060506070b04110d0b010b032e061101140403051b030d0b03010c0309110d063b0105010f030803040218090115050307030507090513080418 72
    0x105503405a0f4549012101c0f601c184406032242d0034802e0703000700d8030380b283d86c40850001c1031300f9040b5a17030240010410a04203c4041500c03882548906200c07007113018840140490003c84000c028a00c4250700c006000d460f000c1d43c040c0d030b07000460900c51114440f510500c402c9120004044149100314520144210f5403ca80c0040c02c100440000300b100700000c000c10741c03c1003806040102040380000d0808840c0a44619140400309103005072035840f454610b150005101501f507190082d42081905940b00c0d000c2c3c0b2620308465040710740700d140300100604008031101c440c038044030002d6642d525280740204030b2690804152141c21040d14401150010301819000b1400240941c0c1c10032006012140a8080c800304a0394004a03807522902e9a10010303005506002522103076060800402020b044150031104038070411070401745100da00e41c000c2c15124139044c0000b174441da02244003042048040c2d0300450f0701c040e4441042d58165070960310303000e8540c4241d0041d400807031000155050200d452 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 319666816 1250 319665566 319665589
    0x702011515090509010e070c030c0c06020606040e03030609040605060a1d1b0c03040612060e151507030c0f0327080105010b2a0309041518020c070905070216090506 72
    0x440d071340c440030b41c0341030305001400710020100020800c0d0003c0350700c01c0500034075a003801658000542601c41c1d80b40d0038000d42d1000119145031140d42404005242010003000b02e0340a880007800c0040c0684d217580f0340e80e002d0080a4040b50300310b20300b6440068001d02e1441c03a44110006030b5807800b1213081403c07048103041803000c140e8480301010041035011810001c02c5a084074580d040048100c80c002525800502860b80a450360350300a07400c022100030901044150a017007212800381300070062141003503902070ac01004003c184804000c170b001c030350311030b03d4100454820b14100250407503a80c1d48071039400c0c0441001c0e45058240710f061208400c2800b5860151140714681403c0c14181001500301da0800c44040544800d4150078000d414424800c8540401000d401403120003082c0300d000010a00922030b0100c5900f0f403102c0b92984139440c1c000c0f180103419820040850501340070114004160142a083c00c0d40302c0e0a0344454003080e9005400000c1548080000d2a45002014025046500e = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 319668066 1250 319666816 319666819
    0xc050d11030906011517070816020708210405060c030c011b05070204020309070b0313110a240207031203091101020c010504140d080711030d0503040807030807020115150905 76
    0x41c010000c844600240c0c05044882c85607a40381c442c65281016aa90021154034240e0a0b1204003040706484d00002c07038902550404045601e03040d080801240c03114030b64001c900503500020039081c4100c1a46040030110345001c43d1861906d50380c1c50000b86941d20803d4051038941010440741c414407401c0c85110090f600054100c4098210366000a00610072a0390003840780380c0c04808034803d65070810102d0064100078601e40d940303041c11021400d007050803d00c103e9281e09130201644107410700030a11807c5a00c0036a1402c103440440c0300c8046181ca40c060314000714802d040c4000b01007140155202510151518001008015420501c2c05400c04080b20f42c1590b10156274a1000d0f6442005c80d001c441c0d1040c03030405032198000c00500355614042c1c0140248101094600a00405c2c01e240d454442044044424510842c1c10580351800100d4024000b12000c2c04044046402030309107960001141c400002c43c21301d5107900e4120440c15401c285d0441140c0300c410800c01707070800143d0025050 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 319669316 1250 319668066 319668101
    0x3020c0112020f04030215120106120e0c030a060b0d0f2d02010f05090a0e09031305013f0905060609130b0615041a190509012f010c050d 60
    0x210050f40d4966885540310090048141d00502c0704064104001c0d035031012001107424034103513074032440104081d180200744c0306854a0301034460000200026585089440500945024103072900d4080040840041c000d81140840d510351000031200a00e0500705c0740b14030303070a070407403001d4100039103008452840300c105000d550170000d000341c2e03040100390680071460f00c0c0c040e640d940107034003041d0b06a0580d0300034041c0c080100c09100c184500800944a103030820b0710750070095907882c0d0045400d90b603c141103400f4103c0b00c080103203600041001401c000580c031020b0103440d04080c0b01d01b0084030003261050741c654000f1028031903071340f80800c4040e030000513030804d40349680009d40f11442085c0024100394030070303400114071a004003081025680180b40005040300c0c2c0c410803440e103800d981c1c80040c4400001c00003445042d80c46019105541c81000e043c0d5802d400140c1402c0020810041c1c03440101c00004041100b140510003405202c007078466aa4a0b5600e0b07812182d16074058030108440c40240704c1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 319670566 1250 319669316 319669327
    0x20705010606032c011b0c052103070f140304120807020309062a0d0909060803070317250e0405061212030415050a0614090c030106030b03011803020c011202 69
    0x1864645501c220101c1d40e0791582201203400c044d401461070f130002d12500c880b50888050039603000145081514080e10985501080c03c2602d14880f4924050700c120503042800440c2c5814401d04200d4130105160801c08249002e02e041c2104940046034215800c0b00c0d04017546480c990b120031240d8000009000070f41c00c0c2045070001030440c1c003e481220617220344401c04034001d2404104000c201c10303020010748003101900803008240d408103000d044141c60030000001400c1900104892811b90140c0e9900e152520940340c0b201e1410340501210020801000129015017146d101c0c0704591080d61201050002c82c1003d110551b60010222403181071102c104500c0b121011400400840000c1101070b640e913030b1032420451802103840040440c0345080c3c200f200c0810b9540c04442666050344170b10600b2030f441c00c10052103100456101600c8170044c0010402540203410030004614024000305407c80c182d0f5800d00030740c8180b4010307401a07000300900034007075810401d8030a400c0d90060080d0700c0d00 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 319671816 1250 319670566 319670591
    0x30f1205120114010315051c11151207020604021507030e090a050709050303130e0403051b150105030a031706060c061915081b0402120708010306051608010302100915020102070501060603 82
    0x195070071005200240104810108004271409807a1151900406510010050384442c0255800004501c1c85003480311011409040c000500d0900c560340c0101910720403584c0341e8004419811512084060204e0002280e10355031300c3da445648524003d2800080c00c1c80d1465000740242c2c603d0307200500a4108101d01e403220801d0740078581c02d03120a011042007a41741c030310341220b151103500c0071100b92000c188845040418003180c007807003000f804090103003103980310310801d40c0310b021134a40240403510744010140c02c202201b1600750301400041906003060f55009000741030500444840b52400c542107800030f80803d5034420030911103680c0303c2a01c4071500f042c1c04541c1d181c2d9200141c1070783c1d010600f9844401d560700d40495100c517940c070600c060907050084024010440c02e0100302c2e0303001d040400017464076500d0100700700d0284403503885100b00c0c4d1030341e024454000c880181e41410045500340104d40c6544680e004029001c5035400140d44131140e0502600312819070b040031040508001380740551 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 319673066 1250 319671816 319671829
    0x402040f18080f0405190905070f05030a050405070810020309010c0c080724060801020a0f1d040e030d05180f01140f0a090501151e030f120512011401031505 69
    0x803503500c4002d16680b03a910300c400c0d81913400b4903444182d00000b075079110192000e04407a24000c4948040c0c05000f1a16095002e482a03041c0b009654002072007071001404049041d00800d82103400b0307000f56100c0303c0e12404080e0a015000301208410384c0c0000500041c50424840c94144208903c0d101e011920640c0d104030031403090340009410030b0b15000b201c10700300f82d032040e0202c040300c03c500081000940c1c80c000d0b58040c1d00801403000c0800c0003443c0c503407801400703a10802d070007a80541c50b00d91201c200f102004010084241240950300c41403055200c021103e109840c002c1004400302c243c031800c0701140c68074000207030301c0e42e030116414442c0008140f041c842d0f48035000701014036820101d640701e4002400802d408000600a036003004a07158960054080301d00c261040401015035049844c1100c0024420610000302020f0042107084040307080d045004030040e605240851618180e2800c030b8508136001c0c4c00551902c0040b0144003803568040c40b80d5952800c1e200710602c8560b00d000001181d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 319674316 1250 319673066 319673111
    0x1090b010e13060b03041406070311220504020c1507181401020c03100c09140303030a0207080412110906030a03020a030e030718050702070501052514150402040f 71
    0xc03214500c141c03a1025036038000c14050506100c2594813460b10f801c1000503130041d0000306841d030264230701141d0154464040c2d11040300010800364907140e664201011141012401e46c92078403c80e403c040703556910340c00200b0164884c04001e1203c000c00318a814107034503000d0010b0f01403003000c4d13041910f66154541c00808460741c48001200f1450f10500507400c080e110300c04c03198035000729998851402e03255400268000c2c0d1598946804c07540350410411a0b003941088258142c0c0140b0015131540303015001081000d2081000346c3c10240d5a10030f0001200d41d01c9411600744511824100c0c403402c006000a071301c00d804600a106212968402175282d02824401504000d107125241b003003900c040210900501c00521200041803241405500801041d40e40d40c0041c0551240011f00c0c1d880340382617507421070046001c04031142001d01e0501c82c10300309005c11581c030300429010200c0307040d0030f00040c8421103100040342c0c0f1902e0b0510401040382c025400c2c0d110348a2070005580c961144400c41d104 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 319675566 1250 319674316 319674319
    0xf050a0509010e0a02030c090d0309080d02030f19021207080c0d030b061c0b100305151503071112070f21170411030109080a17070507080a0309020310060e01090b010e 73
    0x10b0346ca03258501c0d106494403502e01119000070480f40090304155004c80c0070303400c075812001511201050034400301e84030302c121803000a40075001d20a0781544407007900346012a008031300403209030403a101d10b100c0490300302000540740d088010914007000c107001d20001c900014945000c06c920615500024401e0080f0f078032003003440486c1d10a4601c20001035101c075400d03040060a0034001c440c1c000303008000c0c000c01c4031800076845050031150300320b04100d03a4445110052031071281c250343d1602c0302200d0071414809050040e10440c12402d4500c803032200148081c50148503c0070041903142041a510403244814101c80309120440c0340c102a4400d07416105806010022310850722182440d0526010101c1c186501d0351800180804002c480401031419480a448035000b0741c0780042e00e1700200104031225070108030204044030004800e44010210711039182800201015a0380109113441606c00b03440c02c040c0d41c1c405c001e01101e100d1403001401400307040024008071860100080034010b00c8000c00707 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 319676816 1250 319675566 319675571
    0xa0c0f050a060c03030b150711061908090309040c1d0d0804120c090609021c180b0a020d0e01151a0708030c1c090218040c0e09070f0f050a0509010e0a 66
    0xc20513102c0e806c030f080ba4100c01000002e10404114a50300c039580b2030304048038080c0c241540302d04141000010381d4502401038002d055a07220009094445540007000c2d003081b40010001103903556501c0c803c48001d661250b6a49820003104c00c4800c3d00020400c4070248102c40e010106400a031003e4219001c3d91404010007038120305a181c050000700c030640140503e00e0402e000410806110b601401d802140503d503a035480048804060071240f1128000404001d21650580070400350041940c001042590042c50566000c031000c0890300c07180100f243d2a51114806009061195440f0020701a0001381900801c08190310318105c0c401c2e40c02c000c291031408400501010561000d0f140c1d1034441411005440c010a81e0b05801861502e9040748568a070b00514403030341e4000c88081348150342c40310f007511800c0d04050502004980c0103140352203138800e4003000310b031034841000c41c00d005001008500d02814204806c112a0322010380000c0d000c6c240480040203000d100d5100190800002c0400 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 319678066 1250 319676816 319676837
    0x5060a0e03070602190806010504120215121303090816090c0e0a14090f0603061305030c070311040c0315060302070c05040203130203010606021b01080a0b09090a0c0f050a06 76
    0x100c0342140640a0040d00b41c1e0b1011130111000440306a04070051a050342d40c512440c0d46050055581d40035500402003045813005181c001410107a0443d02100011030305141000650720741d9401c00c50081f902862914414910b580801d900004180080c1c11400d010b400c0800400c040011000105d1050001c80c81d150305011941ca4007584803421044030140c0300000c40d07a00d032411800c00310881c0c0e642c20300405180c0c00242102a0314000c031401448000d0103002d00742c03034071100358002c00c0702070205541d1030004010700401da80341002003c006510510070a0032040140003000102c0f540000301500745414041d80f5041e403a4035203120010340d54542401610303120386040225400c0001d4011036000703440002072056040e10300c403000b946113200300c00030b00800741c072620100e031100ea0b002ea491415a002020701d03203640d0302410340a41c4c450316000b000699980c030080080c81c2440285c411048540001c000941030100c00105440a480c00c0f030400e5044910749008035080014602c06d01d003c00800b5540c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 319679316 1250 319678066 319678091
    0x703080c07050105040506100603110403060f0e0106060f2a23100f0e0c0a120204090501050103030e210c0d030e0405180106061403060d020303040306020f03041202060405060a 77
    0x6407601103030000001c10051a00c0d240c141e40d01c840554120381c01510100000440901c00c0c010a100e0650158109080c6460f60761844050040c0d81c50030007505860ba240119500f1091241e030004110690b075500341082181405040c0340e10a001000300d030904803000d9521070305001290b160044c0e21110101001e035407002030700150480303000244c0e20382c0039902d9040c090103141c0e0010000c0a100f00e07820440ea404140b0b160340c0d102e0340100c6554100d0b207040d10401141000038040f0a156001070000b0914035020340d203070360031108260802c4010030000c0110100d00d040132013448000d20070000c050240c180d01884000d9403802001d40ca184164030210a00007098841e0003540e44e2548003410610070307030500c204542120701011350b00c10000d610b0501d0016495101d001003da480c0361600455145071104403d200d54a604280140c1e0540710801000002440341d2004100100016a4040e1241400c2c500080540802034901046500c40c20900c0045800814440d8105182601c001400d0420b40c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 319680566 1250 319679316 319679341
    0x1202030c0a0c15020406030606140c062802030c070b130b0a05060d021c060e16150903050a0b010801050601030204030503030a0b150c01020c01060f060c1101050f161412070308 77
    0x1401c9100c3c0340003050014203950550001000d0742e00c25210241c00c0d00142c4182900d5029920b8a00010340c01103010402c124206054820244940c00c0e044880c5010801c0f60300c00c1c1d80c42518070202a100c00100501440901003915400420000002e50440c040c0e80b00c08000f010081c0150f0350a9941d80c0100d00c0c180d544250349002c20384d01030724030003103440ca01034801001d040c440c0098079040d0801969098811b070201e450171000d803a58500130382c203a09240e000c000306020409000240042a030000c80800c90422100b10302c0c82c4038903404240c640c10004e1250039210f0180c011414140113000500002e00c0101c141c9078001e07294440021054140c40025a00310741e401e118a141080c00074001064a0040d00200b10900010b0024091070b135855a440485c0b00c001d00c242d01c00170f40032403024000035444a50380c046c882814900305003040e005094400305a84141075402c40e010306000d1182c1000485401c0700f401c480300b0303009440c5880e1070191910051007500c90040402071800000350a500403131 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 319681816 1250 319680566 319680593
    0x1c05100c050d0609050f0601050301061b0f06020f03090c0402030103030f0e03010b040e28020303040e07030605030316020117010501120213030b0a14090f070b03180d0509011202030c0a0c 82
    0xb220038000c2c155a00042c070014035090f9014004d51035114001000b82d40610100da0403542e10359912262034200500080c0c0c1c50a81c030310100c805150b54808600071801500240c0310148450b0749051340d174103050318003034270b8809111a01409140140010401b00f40c000c64102c0244010341800a00c001a01000038010b002c28450039900629200400442c03d00c0040d000e200b0b650741c560703001c42942241881038289222107038002e600d50310401c820700c501140c0390003480d08100c3e54200403e4803510350b4000381c1075030000011104002440c258501c20356900110b4010f041d10a421003402550410000a180496504041d0041078001540c014601000e0f0220401142c00003141c0300c1c0ca080241d44100502108900c030f800c01c41c091004240f44070000314012012a07640001030591926180e10164103404c01405891200e50041001c060503c0c1400642c80458440e070341e50750f44010090000d0084048020200080b0b8030602c01c015110310358004844000280781071000422103185410301e650040f0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 319683066 1250 319681816 319681837
    0x1201050a1e05040f1b0201050118050103080714280b011d06060a0509060315030d021507080a0608060403030c1209020f060313080f04080706080405150408040b0403030801051c05100c05 81
    0x360018174095039410350005040e10080400c00b041c8103040c08049040c0d82081c000a48003d0041015100083e07540c0c0303a200f4040d1074002a03504c4000c081008107a2084501000d003405640d6001c54000c221380304030224094418039035441280c20011054002500c0000c040c2406001e0008e10300d41d00310700400c02e0b6542008020900f5950303242000b210840c803c44140407074001c3c441c5030488403071140045514119210003da5032200d41c0c1e10f001c8110380e404409447c109030705580d85070118080c0018005141b050780692004140305030002c4008281c6202903003041480ca180c1100c800040c0e030740304201e11710048119040e540380d0326120040c10410183e0a002061400000380900544030448081e004403580c030001d40c1c0e0030a90b2114140e0350345d10100c400a10a80003560300b040891072031002d507504580a540c10030304090300c807002112590b10a4000b0340208040030010801854083c480001d51803030342c00b0414103524079036615035448851800d00c800440c0c46201c00b5403500e20a00554500720380 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 319684316 1250 319683066 319683101
    0xc0506060108092a13020708070f02040b060412020a1710331712090d140f07080c1512070c060920010305041e060209061201050a1e05040f 61
    0xf80d030604018004c0d0110080c0c042c0e40c1e440f00f055aa850b42c3c0c400d8030001c0380c0001035685840c00c25502c504509a000c8402c0380d00030341c1c071840450070303480d131101070000f4100c0742ca0718200c40d458078010000a89110342c409144a005055454800b0b8004281c1780c83c0030b04035100c089600d03c008280e02030884801120500408880544405501c824101100880d00860300000c61284075840b19515141e040c0c0004550f80401c000c00d0005042421622003054080d0110021030312482d1800da04105421107032100503030145c1c07410f014440301800040324240d400c840100f1030032076528250300c580c00355500c2070051200242c0003401e9039000d0000c031304140c0d5018030100903100b210b1034005807001701c0d03641000b080d6540c0000c07043d480d406072150343d024980100c006500306c0c82071080b0a0b013000701c00d1412038055400340510801d54403001d01404100d680d4551074003036581044103004a0103095802130740e01312295540c0c2d003855030750710484c4c0040d68800c2d2004a402c900003490100070f0050800c98031030440c0e = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 319685566 1250 319684316 319684363
    0x509090907061202030601080601050c0c03060a0b041109130207020a08030d0914010507020a0b06010c061b020d020307080414010c020d1203050c0a0516020109151106070c050606010809 81
    0x110041111410b692140d00c46002108842c0340d00c0080780021202d141c045500c0c44041801347d0701850140112895250440e080f00c8008000f20f07051480c01d0760303c104001e841c1e20060380c2d40c0c5868001c0b01e0f10307a50b403200d0443c285944a8005000c03a85400c500850081d40014200c0564417241c8a0b14007406c6c010040302c1d07440c40c40c6032800b401006001701c2a00d186482c440114034125060003078900406c030035030003080030140d2030b100c0078040358001d8260381c140f11002005100098107806042031440c103100c0500d0b94079400c104080d08107a002c0100300110b4004112041c0042c05003411307201030710b0031307550140c901d100d580b001606c0c803440400d800380d40107020407625020440d06031078812619025a80c18001c0d41c40d4a40c400f6420f000320700384000070030340500140040c0001c0c01c6024004038014505407461950b00d00030a00f40364000078007072000511051960030440000c110075170308442c071441c007070400c0e040d15100c0a40707894025104a04202d110804645200020061000c070411000625031054 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 319686816 1250 319685566 319685581
    0x142104080d0b0f100f022107050d1814030717030d0606050405010c0b0c1902030c070b1608090103090c060e0a09020408061303030905060c04030639050909 68
    0x150007203503100101074100015000301e41801e00c1a1008075a02500c110001511404103550031006000280304501c40c0051141c0ca2185d100c21880380c0401401e107c03030762668941011414010030407801c00610904406d08948149121810b0f4125603440c0507925000306c58500280c10290142d00178411443c4070fa40d030311030b209004801030460303081e03942c0d040080030380e5458143c0d1a40110300c00c60b40441e441d040c00e68041768011150a5000c0094015549009014102d201d0705086002846005038404600c0ca08024000c000302d101410044416608009655003071441e4001c84450050810801003034480059010f500300300e240c1d07a44401d02c0d00280f62244c8008103c0501c0e50360f003603c6000c4c000c10000c2c00601c3e9200b2901501c0b14074018000c903695518405c0c41021000d070040b030825664400741d20214100384043c50094064503041560b5901c0c40c1040029640d040c200c000e001404070301e40000104a44200010921038030f0a00ca0188450f0700c401d6601e8012000c0e01074000020701d0800c03000 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 319688066 1250 319686816 319686833
    0x30a03050109231306060f060503160810090f0b1305090c0f0f04110706020c030301090605031902010f03020c0a05060f0718030209182a0d03142104 65
    0x68500b000703020400581c41c045a00722151210011050720381d02d05010410050458010003401c4d40501c1c3c001c80c24a039592000020301603280c2c002400a0400b00030b0106490700141c070b0752941291860700c002503040030244400813241074070840e208a56a404030a4452806400c00820381ea401001c10006030442c46100c1d024050440e444029405002d40d101b42034502005002c442100191600003652529824000140080c100800c1034200902426001601900042400301b00a0014686951500000c03c0c2500d0491308460702c25001030605203650413130b003c0c84959054091a1411001001503002d40080c401e4000b008850b02078000c20f002444000102e0302d00030011a41403000540d11000110f0700b03100400028400780c3c00f2140100003514020508580000c0703c0680e5825181c0d410a00600d4240c1281d1080c40e44189149e00c1c2514001c1c00c100c0c6041400203407038800b2800400e40d001080241c003000e011400160206028450400c40800c02e1503078100310341d040155082c0703030816905 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 319689316 1250 319688066 319688069
    0x9021c06080a0314030c0403021c030212030105060a0806040225020901140a0b0a020c090106020105070e0405150d0606030210020a0c08010209090403110a0203010606110708010e06040f030c05030a030501 89
    0x605060440c0081e2680000516900e850b8269640710380c50780042c2c486044030703071001e05201d03090041484040056910b25500c4202078626081a00342c03820300d172038041c5c1007800e41d8100d1040c1c3d007802d0004101c1038854a0031030765440d0300d9287c08100f50f960100028000d000700c4144101210f5513042907000040c0c00f41404841c02c0c022100d170aa140ea0340c0f28000d1241c04c0d05c0807019000280340c2403c2040e80f20000180082103803900680307080a45290200d61901d00c242d0000380184c3d140d5040c072200301c0c0c0244500c03021020554060102e480d01c9038841e10001a1076401e10700500f61181c0c2002840150344c03122000c0e650007040602c4502c480c04c2c00a683d0121003000380c4c1d0b80f003200b1000041c1c0d01014800c07101c176400003400a550586ea0354600784c469111ba02e98140c11030180021a500695080c0b2541001d410503072030b160000c0d20301942c2f191500d0059002082c0341c2c0c0c940040103024810004400741c0c816031007003a1340e08650644c541100c0485031208020054400818a003000740e400d60401070 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 319690566 1250 319689316 319689367
    0x52208060720030a0917100f0c030b040903020319180b0901020d02010c0e060a0c02030106060201020d0b0d02090c0912010614011b03080103030e0a05130c0305090a0b0613060902 78
    0x4440c25081d84425031603128544c0040049003000700200141100024028003004900b0162a180e60b03480209900b654001100b1038551692407205480d882d4151298002494054508000710486540c01139520711804141040307c0c0c129080c0b2550040c45003591404400b441180e8085e240d030750341030300b81242e000340d1111409401003483c0c4040e428414880c5090103210799546a1110404900780201e561180300c80d0010050400c03041405614240901e10040c0001d07400180d480c45c4403000b40382182e203500d00340d9110300380c8414600c0241c0c2d0345200c42c50300003098242d041da4502c2c480c40090207803041c4100561302542811000200c440d100b0b0303205c1110070710a8071070300d0648030209080c0c00c141040040007001302d55001c00500c0071078420801a00000c10190260000c0364640c40010b10840e10541c0c074919880e03c849a92400c15414001c0703940100103403000384aa6000c650b41c110110300020103480c064a5202c1e4a0b000b00c411540000c4003c04200f03000315551840411800f124402801000c0c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 319691816 1250 319690566 319690607
    0xf2607060b0103061a070b131a040c061b02060d0b09011710020703050a0c0204020c030d0605040e06270c040e060901200f0c0c03071d0c03070522080607 67
    0x80c8503006400c48175000b5140c811450b160800b40da580c12014500605400945040034000d00c00080718001983d50710056604110300030b00d818074205500d494181c101c003041010b02e400001d4a40d402c0800d01c580258122203460304d81c503100c04a400148041c02c51a5882290071000090403103a0141c40002384071100140ea03402c01c1094941010307441030f82002070001d00100114100caa11031402c1c04590ba1000380050f292511407001e240ca1070300072800b6040d049648003810031045c50117125a910340039803240984034914000100b1900710b40c94904c20700c0310100184a0f0300b40b45e9002e1010b80b40100c4010410048908401140d540d1040c0c110748800156181448051503240000070504821901e55815032805008045035149900201a51b400314820010504600e5905121401c050481103a031540d586101000103125548046c007d0380703a2910030030038811100c1d405002c451889032001c0c02c0c130644080180140601502c243d102200500558003401615540400c0d10041c028240d0101c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 319693066 1250 319691816 319691819
    0x906460305010b09090a05041502040f08010f0c0516080c060414010b012c122b03050103030203070215090406060f180506190210020708040518040f2607060b010306 72
    0x20f00c0140d02c5410070403980f02c215000011081c807a5500010362040c452480e10522006522040701641c009420080800308615018041a1400d100f0608054440c920503c0820f5501001424501c2100101c52042e04031400d40001e0091460488505003401400c4501358641170809104800308a12207601c69420308001b80e00940c07040c0c0f41c2200d112010044251420307809841c020070101c1c04400d258200031501903000d0345400600003010390005280f00382041503030f2408920a03800038003110000f4580340000500101b9400010b03a9210382e410360300c100d400780800c00c140907075004402941d42e00074101701000c11200d9211040444141054880c0e170741204c070031150550011f045020f4643c1120050110401800700000ba882a00000e40180e4625403000da58840c1640c2c8403520507202e280000a0810050030f200c00c40b00114148a001f8504509180d13840001c1c0c5800d0081c081c0c09181d80401c071001208186050300320003280410510358401d41860810081d03d0182e44850200c2e1a0000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 319694316 1250 319693066 319693079
    0x402090a021215010c1b05010f02070f051516030e09090309010c021504121109100803071b080307060509060a0506031c0e0a0303050310080102090646030501 69
    0x380d814003031400c00315010b503584444154010788884001c80c1e0400030300444034004181c0c0310791000e40c1b84d446010f900d80c0d06400c1a001508000d41c1056550443d4031109040080349031501103c0e05480040303e500c00458152490103502d402400504001c510456001804143d00440143c0d4090015600f404890750b89543c0c80b52240100c45e09a03000c0f43c070180b110001807034500765941c5507010f08012141000d0300c600c003c0ca080c030001d090445003c422001e4000c2e092400b0201194002d0024074007894060918803034603140c1c001c40e0401000041d42d101000b918170040180140540f9a08080b2505c1e0001c0f403c1c01400381c0f200f41d0703540a984c090400840d2848500c0e0084610680028004100b58140c1410080c0c40001020200c000c0244001d012104d0342c1d2503404281c015400b03503594540724280301030303040340c1d43c3c0071030b071100c22103030310411102c0702c503440700c10503102100780c01d034014600c103024005400c1001101d44c001820800510700101510340c82854954040c4000355420001c1d0307a200da1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 319695566 1250 319694316 319694321
    0x30d0908030d050c0403060e030c0c0a060f081b161509020604030201050c0a060f2c0d0f11030f04030302060702031608070501180b090c031f050720060402090a 70
    0x1450034550010000034840c265140c1103aa0000310901c1000e01c2c250340d94407640115406d405198229400c00200038100c0704082243c80c0d86c00008943c54800076217040f41c00783c07981404402c00000e01c084400019442d9910450188000091114990307075030301801e901c810740305402801154080702c2401c180031030082600c22007a80355030203488a0316180c115001501c00340c014811004d8140309200c0b0f00000281c450059071343c600b40c00c07540400d0907440400c4002d0f403c1c0c2c20002410055503113940d6901c0203640000c00840c000b40c0740c10810800c501d0070904548840c241009140c0703a100000c0d007100c4500c00d01d0001c1040300c0c043d80c2981c240d030b107a40400b01e840e48110220f5002c50030030207130444080740000300241102c0d403080c800020440c0c40e01c0405580f40300c0b045001d58019410300304102c1d0181c818403281d00811421400343c6041055003055132403000e443c44010b075a19070344a000498003809841041c2c000c6050521540c40e001a100c0000c0d620b0004a0342203000d01c480b000407400c40990f90 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 319696816 1250 319695566 319695569
    0x905190e0706200714031e01150905101a07020301050f012d05011d0910030b0601050c03030a0b030a05070324060501020a06090303110c0102210c0415050706050702010506030d09 78
    0x400c050040d581c85d0504000110131785138481540347c0502007a8080002c000300c0707803540e08561280003050040388503030300703904210050b880040d44074140010801082d0704624403c0580344103030410420144440e0001929008a110084d050b43c0b805c0c060200c3c440e009220141240c0d00041645044c82003e5185404900d6501e0f103001c00552480381032000707600400d81020f4459074071400325114140400043c07100c0b030082c0d0b20380030307640d072807007001d105004500842552140c428240285001c0c2809002503403880700034140c1654650703a5920b060036980070f0000c041c403217030840203c0348a980c0340d040c480a4840c00080c035118010140780121185222800b89404a56058000c0d028030455900c80a000c0c1c404403008904244d55180490070303040c00c10000e8088000c412000680380c040d0600140d0040c80b51901d21a035000d0142c040050381c00e130160494054a04424251500c3c924400381500d20707000385440180224140340400589a5055110602c82c0344124202d60521510f00d00039226070744e00c0e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 319698066 1250 319696816 319696877
    0x60e010e1e040803040503071a090706030e070302010305060a1508240a0b1e030c1b010b0d080a021218030c090613020a0c0c0306050103020306010902090a0905190e0706 74
    0x1801c001800305142a0181d0750050050041d00e18188540d40d480c4011a034200002c1014000c010503c8a060340410074040a41440c0c14200038410468000075520f00031880020304143c1c03503100040068580c40c002400602020a02c4082901201030103070044a007141e10a00440610100d1780000c20003808440e07a4502c044c101d080c1031410321400d903101d82d20014800041440000c5138085007011140210302c01c001034004c0c1500e0302921120007442c1c3e080c04241441503170415400c0c0d403266481000f40b03004560301140d910b5484903404001e90610303039402000c0c0c1c0c0c1048046014501e41146990941d140e400880550b03512040c0b12041003440704007601e04980002c1c1d60481002914016070060100f0302036420802118000f50f0344440c030325151508101d605030f80700c400410450504001c980e014007514441903050501c0d110118406427064407072020016115004283d0725200c1004d03d1030700d010308010500401840e0030425903036218500c40d40002919000611821b003484100c02e0ba10080d5 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 319699316 1250 319698066 319698121
    0x110102160308061212040503120f0a0302161b05090a0e0a120e031606020c01050a17062704050c120705090601170925050d06110d060e010e 61
    0x189a00c00b00c92041d001805190000241024010035a008016101485c0000411250349501b00310506051000c2007056030f5540d81e06102e200f2000421000b5240d11040074500182c881142c070206400c00901044090f082c1c07400d80410f0a020115030402109a50b011b441880441d100e54650340c0444d0b00300c0c00b100300b0640180c0c0c0310200050315031220025200d01842c0090301c0030305000010b401e1040001c00380d1182c1c40c030840e0401c0055018090001c03080e03801d003046030402d000b03103d01600c0e42002812401c64001d103280000e0180c1e641032200035407490360700010f244952402d0000860802c0c29a0300ba1420300c04c42102004030b02e02500310440c034031000800343c400b8500e008240482c0701300191940b814080310b09555513010514108040c42085d031003008207250107a402d1070200000416401e0210b51107095814806512201040d41c021580040f0002b80880d00c01d0000313203140502c1070186086030610000003403011044804a040e00c02d410500300d0281c0300d0b12a10401c004c81c1681401c203416 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 319700566 1250 319699316 319699357
    0x3120c1e0206030a0f0617010e07080f03040308070c0b040b0c0105010503010204063e1c05043203070f03031805030d050c010e0613030e010c150b06041701060303110102 74
    0x225260030007041c8505e903801c003203101c584551600600c812000174038031060391340d800c61340c41214007005160010107402002d401e404000f1001640c032071046000282144800199034410000715035100e00c0280341302102d06880703a41f58803003007043d5448070110102941c05c0c1800400c051038180700703d400310380054031191f0340c000303d0706d007003955100030700d8034022801000b40000b410882084d0706da0540fa1000101030800c1d18441001106010840520f00e0200181803000380490341e0320401005840c140c5050007216880c02c2c444104400e45603070000d940600850300c000507040c0e06540c3c03600030750384251201294050b400380d4000f05100340b0700c5140e505a00c040c0d54001c0c0c0d80d0084008100311a004400803802c081c1417410346103441342c00e0b034a989842c0904442201410303400f0b800fa004a10091800d01c650803c01e031200c1c203103400340c00c0014180030760b07945600050340e030341100f12002814043c01403130380e07c4808a0000d008185500c805d40c0819034980380c0b5031a0141c18401c84400b080d07024070100d49030 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 319701816 1250 319700566 319700581
    0x703050f010f060f0c0c03030314090c060f1b0a03090906120521040e041109071803020108190e070501020f07030f03080a0225110d02090c0703030603120c1e020603 72
    0x11a130510b03404007400040311007074020a1800c010903011714026140854030304c004181d82002c4100041101410760003041d40500181e443c2d0b0304807401042107007c21903c481041b040003d0420011041500d07510403400500105900305803100e040f100c0d010410000785503600f01940509851039030051060b0000507141b130b403189640e101c230b04010b2104c9000c0e9091035110351240707090400c00d66003130760740c0076140640000c203191070a42d00343c0c000e109103000071000c00044440104200d130340c00b0081c140908800021025000a0043c06e603112019505202505d00400300603129181c500030030b4018062000301075410200001da50b42142d900c020000c903640c0d0142c5040300c41e140080d2080320030a4081081805035008052850b01c800182c0c4030590230a401c1c2d16080f584100c07080074441c06485514055000b5a41b180c085c283d01054035142e0683c1d0340441c2c40c0481c0102540e40000780040c0700c402039a14010381c0413010754020341c492084940300d41031030b003032522070000c00300e4000354000c0c020070016044 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 319703066 1250 319701816 319701827
    0x1080f0319181d0c071a0a1e0e0606030304030510021303020a0602030a12050105030709050915070c0506130818010201090b07050d050105060c070b0f090a0e0703050f010f06 76
    0x8612a207403005041d00b4042060318440035542c490b0228500211082035200c070701600035a00008001a1245810310584e45d00031a40710101c806807900c44d110000442141c8540c201c02c4110034031140460003800ca128a0340b00902014a918078544201c5000844c5410b000085500796134200000b0161001d22104280c003a5008100d04032511424080002c010307103a656450014080a401554480c0040c810040541c400d640380894610f0511004010507240400e000c0c080d01c0c0c17528004904d503641c0d24036040c5010341c1d003807481c00010720790410010400d45c4840000c107014811029078580f91103038500441580032440000d00038130400c0000545000a002e0480f010b0041800086090100350f101c401156404442d1200416400200d520b0200120f11070580908000c4642c2070a09101c05000d0b07a9401d410f0280340e006640000b01805007118002c140d8000c900001e00d6280d0b030646944400300a018181e8100f00030900344070210320480c0001c0c8480b4166a804a100d050303039880c06130119907 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 319704316 1250 319703066 319703107
    0x806090a0e120c010c030501060e010f0c0b0c040e0117060f041109041407060912060209010903080301091b0206040210180b0408070302011b0305030c1b100b0901080f03 74
    0x100e295200c6503512420000d108105612003168200c5880342c000d58110350035120210b201c0300c10145000018842150450104200140203107403c601030f000c0084162030700d1200c290f010384070039030050800040303410030390090080e02c000d00581e1b030a90340e030703248126030701e0b4040c0103000c0d00c0c0d4100e00c00050800760403050095000780100040030158200b4004100d42c900292410344a80708030700031100c0b10b0b11042001000400d11440c009000510341410100b020403070000061103e83c000615001c982c0c801c904181c041c68022642964959443c0d01c80002001d92a00c00001200f1500780260901c0c00422541e220f150041c181000c03006142404032251180c910301d154890540580114010403098041c101030503621004101490460002500b070500c0440000e80148980e03880c1c40000750310001303403a04140c0c184959030300c50101e0320b040340045000c541414041c2c403521540714550380242d00000304800d03040d21a400b042c0d0b00d1700e98058550590700003003021580200900016a84211020714 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 319705566 1250 319704316 319704331
    0xb04030807021f02070504110406020601090f0b030f0c0a0e06060d050403051c0506090a09080414010c2009160e091003061107150b0a0302010e03070807060c150b01080609 75
    0x520403500011070503c1c042001002d00016400500b051115042078030621100000c9400764034102031402e60002d41e00c40050080008060301d03030680d005c210170035400c4542d00380302c0141645c03030058490305080da5900440b00d4891094541032000a80340343d040c4c030320b40d0003844007602c1c041c601007181d64810080c2801030300843c200300080000c142c020309160341414411481d64008511414407100b04148000d001d0240c140c694905140038000a5014040314111004110300e0303804210b1b0b000050300c0482044201502c0008200300801240144290101400104580000d144c0d1242e00124107003421031000d90005c20780c103186030046464140140e540c8210a425644011512941d58009803823450200e0350481030081040d03010802c002104c0445c103e407010b8104600b00d0a000061070070b811030711020341401080a02e0b201c140c0c0f024408803000e01032120494202c0340d6900d00003040c0c50600f04040d80c8115441450085450003030150b24401c1034165070380302044d21000d0400c030364084040e2519 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 319706816 1250 319705566 319705579
    0x8070303050601090e011206060b131208120c0a1211030718030f030806090f0f04080901021c021b010e031b0d0f05100b04090222020c0106031b0e010b0403080702 71
    0x3d40e1400142c405d5010300641c9102151102041ca444000e0b42c030150009900384000703224151603030310b5041410085500702d0101010302001130518000601c2400b402c94180030b0280c04001d10014030b900105072018880e0b4a240a0b20030850080b4100c4061440640500e442040820f400c82e1080c5480302d1201c0c200304603071030019a650340722481280001003c50100c0c0d00c84040082034a40b60f20025440071040c880b4210a20b0000c901e088101c0c401000206051400314581006920800c0300c071200281d0032980d00f01c0180d08484c060364403207105400700710424220706098510f5128000d20f40c1c0180b005401026088204011f801109640c4d031001c541000354118140e000c640c4241460f240f09000f00043e141d04502d0204600c161452014118000c604041400e001a21a20880384100804208842c41d0480110101d0081c5c801c84c01c1141e695070030811301006000030400200c10002c03032064160302139039036552950790100091055884a00342448200081780307260b03000300f0809100030087d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 319708066 1250 319706816 319706819
    0xd0b07030f0e06072303070311070b090c191a030408070803100f0e010b07150b0d050c030d082401180605031005040b0303250803070c060b0a030807030305060109 71
    0x3411503881c0c2c0034480c2e040e84080280520b890308981032445100120041103040902005549074900c000740c083c03002c0555440c0e00600c0c00800d901a9903469500943d298100c2c203000c8070301661540d9020280e13104885181c589411902900d1801044961400f0090311055000c040200c55420003041514161400c124080000b6030941c025441414405000b400319800d00c2002c0740d11050030382214440c0c6580200600c580c3d01a0340c20781da1041c0d48800d000c20901d68001e154006004442650b581151016100740100400802c40311034181d41070f02204c4400b042e901040b15180000c0c2e801d81d01e8080040c550049014068100d400410011304021038280c0d010411140389035030325804040011004410310200b049000103507401090200e40602000e001d07100001d48921507003002c861451300354945943c60380a0a0200700b0b055411194458992920410150940012a400300d400510702131465040c0e20f000030152040c1c070b401107032003410002d1580e82500100740107010b2505101c0100750 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 319709316 1250 319708066 319708091
    0xf20010f2a1409041401080c030c0109030209060123040305190308040201050307110601090f2405040e070f0e06010807080c0d1e0501060306080c1503040b1905040804170a020d0b0703 80
    0x104404061100c0000e01170751f140000840c01c01d0341108440384203811016050403203aa10000001c2940d40484d154500d50b154000140c0d40c4409041014460740b140d08164108a004034001d401140d0003607048c2d880307070854013082c4c2c3da200002d028020b000c5003803c804100554070820255a00c41d110b8100000d151103035034846454000241c0c0b0642d8241c1d01c0740c02d044c1d41441d003802015032283d81861030f29003490040d00000d840200c940103c0380520790303800c0da80c245120100030000c020300082e1001141180c403401c240350040d904561140c0450401408228080d1140c01c00c00d100780f10b5041141d00b084020103401024080342c40c844644407100c2103264000385c01750311441d4000c1005407000905503203016809030500168026280c401d118a44100017114072410403a54030a40c09000c24030503584522034524031548120380b68410503d814100820452140000c00503a0302800310038004100d241c3c0700039921008000d0080d0801001e5179100c3c000746044140a40126090401081036696801d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 319710566 1250 319709316 319709321
    0x80615030c070c0806100b0a171506030a0507090e040506070509040e1603060e030405010905040f06081209090109090f02090402010e060f04030b010e090d0f20010f2a140904 76
    0x82028580340c0141051201414403540041b008082c820546414028007000261100b402c0d10440303100400240d001807103a50681ca003149115000400194590074114122070041c9400c40d110808100d5843c0040381c85010740810741c0c0308940c0880101007655074034104a80c5034104500300b80e0003e80310841c030207039600240000c00f61410020032628a551460500b8002c0d6071a410002c87c09030001c003c244000c0e40d101d680041562070565000c80d4034201c001415001b4503d42c1c0c031060650182041c821005c40c013a80003019003000886850a099072144086411a08200c500030076000d0600d0309c070001070802c00399041e41b02d0b00504121400c46900c40100307085911002840c814108009010700c1085075900055000d4034080c00d0869040c074009082c2a5604501c402c0b80c424854810403002c4010702c500c40702c1981c4284c94000030041c41a0b5031404c1c0c0070309a580031121340e0905018504c131241207000382a406001000715194490200c916054482841c2e485004185180c2080082641d40703460 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 319711816 1250 319710566 319710569
    0x60d090609020d0b060f120c0906032401060e03010b01200c060406020309090a060602060c03040611070602040e0901050601050415030e0114160206070210020906070f030f020d080615030c070c 84
    0x1101252250b01d08001001690342819070301b03d20902e8400c00d50743c03543d24005001103069030260b0f02500075880d1540001e1410782418842601c10000740342c0d4201d03004001030141c0c102c51190301d81d40b110440507001c1509032001d0400c440c1c00944003030740068064005800c4a00c2c0204a502561502e46a18020840c41da1164114102607031002440c0c0c6490b082040c01507a10460398001002a2400c0020080d2200000b4008080e003410110202c0c051001b00c3c3e0000340685003609135150345041600e0030b6006500540300340411016420001409110107028652113407005030340c4d0902d818207156880c155a8035505504042654a002018064209100d03444034842544240492840c2110340c000c40d03000420500c000715000881807098071a0000340746110703203050706009601c84c900940840c4441c003c01e840075168500503640441803682042100c100000c150707003a03510702e18803220195006001501c00c9034100344501d0912000140c02e02c040d42d00020055101450080795850707010030300045 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 319713066 1250 319711816 319711823
    0x6090b070e0a0905060f06070510061202010f0509012003091c05071d070f171311040b0604050603060307030c091a010f1224080c040c03020702060d090609020d 70
    0x4500101007a8600109224018001d804043c030140c07811034081015500b120340191b01511001c68001e04010b028846100d10101c107460810000b66141001c0c10300c6207000600b45d020032204038810340003d108070211101e0f4003068440714a40c0e43c1170f43d00b0004503c4024850340d8140001c0c0701040c419500e046001c04803d03444002004c0706481411b009003014403581c480300d042452a1120300314803003080c610690120f1907040c03180411b580f02c80181d412903100d44502d560f00070240308001c4070340889500cbd4a01540142c0d901000007203600240b000300e0f25140c045580c031200a0004020350b00d03100c07004540c050400713010386072265aa5070326030f5160541a00006110358071100d26020300122250031009080f402d00e40a0100c500c00040030b44182c00d140c0101a4040e144c01c44201c100380d030004080e04510304c06424000702d6039185200e540780c0000f01403d40c81203081045402c101446030080d5940260000c0c942464814012907020050084241c2152056140e1500001683d504802144410300 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 319714316 1250 319713066 319713077
    0x1d06011e181418040c0e010b130e130f05010605060c030a0f0503070801050d0201140f070501110909071b020316030605060414072105101503020c0d0c06090b07 70
    0x40d62100d000705607041e0380008030400c1004000c1000e0ba41c4501e02c096185004214444141c1c0700d508010a94010a401079498842a078000042403240003000b0301008a2508074984e82c1510b90369081c1d1211015aa000307032a0004051160102e1b6800100c0300074240724000009410b85e468010480980101c80c00d1200f58101150000d00d1540150262200318682d1421928500c2c202074080e0840358107008030742c00340d10001c03484011a4095920f0510f010148030810343c662008034903025481d40200c8048806500f070081e1034100c0c00015003950301c1008020041081c0360f5030f040007110400d025035040500e9440824039000035890512122501d0307210000340b0301e0002d0071400e09006903000900494081c80c50407081c0020030705002c6c4540d81100c1c140c5422512080c100d001040ca42c5109004d10308001c0ca0316003072242d499020550001101c0004200011050741064140c00301d00849031000d2081e00100b120f22801442401684400c6108030b400094500d11030300ca145014504a030702402103007 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 319715566 1250 319714316 319714337
    0x222140102060703060621090629060705030a11070f06051225030b0301090b010807090b011d091008060f0108012909040f020303030a0b040b01091d06011e 68
    0x140d040c081e0b00e500045a050900c08645441d000500942c002c2880d40103819503c113401082c2a6160440412030780c00080c144130400b605a101040c1c4c482c1031500100141c904101c0c802c0c10b08141e400c0d600f01940000c05503040c1203110704240c0d0007262416003006180104140840c22128071000a005003109544964440248100101001b41c002c0c0000300c0040300d892102c1403c081d80341c0000f048103201e2401191005100011a0242c40100c0c0024807a000d450004201c105c0001006011147c0421041c42291012001514101d088825040c3d0050065140c03141900309621116000000c05100d0002c0c0e0382d40316001800e00801ba9080e050140c0c0d04c00040140f44802d020b0004110803440c190700c2c114450918107040c0d00c4048041500600c0154009001e10001250084203250003809503660f078504010484002d00b5400719061041e4039000580019500c00c1e561241a40c840114043c040980e00c10308101102d001814541044000040d1001206d100310501002003d81d454092950 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 319716816 1250 319715566 319715569
    0x15050f040504080f1902071d070f111009050d0f0c080906120c071b06020d08150409030903030305010608100504050604110d09140a120804110d0b010914011404022214 73
    0x180694071540740356000c0000423a10603403490320590400c00d0ba061110040c9050030041e5808414140c00030114080c019001e001004c054014042c0c1c94440c00948a1030901007000759003c4040c0c0c0d40181c00602110305000004904000400c480d0030010300745401e00301c5507010000741000c2281c01814001011440404005000c00f4146100c5440002041c006042c910004d5031102d000103210300b0002288041b50403c980407901610b00c440240040c0035460b11402e0142640e042d5100460000f031800d000095503500c2141c3c030382d004040030411204850714100801004d000040c108641c0266254040ea5050020344d008040f19680c0840100d00380290742003118481940446446054101101210008100311110724000c0c2690410f41c0d440d0301c1364104800d1542e00c607044150400c40c0f0034102ca060013240c940c490304a07100072100b0300c500c00c0401c60403201d904003880381070400d0b0f44540080b80745292680141142e445249148a450015110310700343d070182c0342e4411000c040741c89e0520000d6 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 319718066 1250 319716816 319716823
    0x21070c060c0201062315072102010509071205010212150f0303070503070b1b070510060506070c0b0f1c0203071407050a030f0306150201060915050f040504080f1902 72
    0x20071254002001000d01d00720641d03521300e5403480c0c1040394514280101d05039580700341c1d10548594000b03407140d4450344c6c1c510f00344819840ca03a101401b5190f521a2414155105014540c490407800c8080c1541619068170161502540442110295000d0100c0642148514403da20a2501170a1010411004028060110a2091124080d030020016040807800000c101c80380c4650144003103107595107580c0d110780c40f440c0c201459682d0326000a401001e01600207000340042142d500e042041d150b03200c0c1040100c0c418400300602c6152030000410810f62081c002d0311407480176400e240c1c81c1083c20060700e082903000603c0c03103c501d503000c4140310b45164030a82102e00080702070300c41490301d241c1e40c0f18a59101078034100101081071900142c070780188a81c004c0d40051004a04a02c0c0c1c40c034514002a001c3d282034000c101c0761614217191401681180c0c00b03041c0c1192070281c0341009450b090800d00001d010014825520880d040004000034041c1d000100301107107020800010020b2150b0b4000e05 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 319719316 1250 319718066 319718081
    0x606050112020f040302061305030f030c01110307020d0e040204050a080109060c09050618040906050103200a060f05071e0c14151903090506090d03060e07020a0821070c06 75
    0x401c1d00c1405100490710302c1c0c3c0226070503207404882c0c150f100c0040c40d41d5500c0030005a0000c0350140111915205101c1c0d000001c1c2003410504c4001781314440c0e02003120020b500007200e40b80300680c05a19100c1410f0f00441109241038070260001d49806c2d1610040b4005144561100d90560355401e030010070301045105d6201045440d1801094407458240003a07010701494641d501600001051490940c0e0b45900100c2c03100e40c8140c0c1444103603901d061030b410036054480104a0b801d60751000c05403a203411200d010a071001511020402c84100f44200c501781c0001d001210100d0411308000400300310360020914482c420160080106d08108089902c071480b02000d60044417182a4500c460452005681d6019001508800040501081100688400e070000361003400340070b09000c502000030a101e250580d640d2020702456544800c12a05000b040b11326030300582042c0003200024804400a00a405480820030800e203003d00702010114000c0c0c41040114500c8014002009268042c244 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 319720566 1250 319719316 319719347
    0x10110c0303070c060f0c1e05100e06220807050d02070801020c0a030e04091b140303041409090f0303091c080907030308130818040501290304060f0906060501 69
    0x5040501c0d0b651000780c040124003075038050020001100c00080e115914900010350420040030500000d600c47c0d00d0503844002041e1003c0c0101c0c050001c211085009052400c459080107045542e40c1c403101c4503040c42031035062101d180c0c0160491001c2448000a0070b02e0354040e60203021303403250042d406031510801e0741c0040c0e001d034014400101c0c011070200e0390103040c07900360808071056007044001400030700f07a00c07500628081410070ba6908480c5041c0340201524202d00c02d40d4044050750b0109a0742c0d00031840744124400080075021440e00b80000f455410001d800122070340d54042e880890b045410884082c2040d902199182d8240c000c034800315000e200307ca00b410480d600b010035815460ba111404013074244002c89010800c130699600e84805030541010490751224402003000c0204414043c17500c2c815418000003180404c1d921841e0b40c1c010810a011140d08544105c842c0d0309074000800580311655100d03001c5984504034001e01c038a041c411140011070a00301000034010036140f01002 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 319721816 1250 319720566 319720573
    0x8030609012c1503030a030e0c0a08061b070503120910060308091207050d050601260a06052a0310090203070c0212161e051818010b10110c03 62
    0x60b25010032031a441d00068216034001042030382c034042c0c2c0d41c02c6425500e03070740f6401d80b200243c802d50f515890303400009800320304402c0d5840d056602040003e202701900038040113801c10408558a1a030000401d0a100000c0b9031160410110752076540c11608040b090400c50100141002030030a41440411002d410342d0000300f00413401c546a0705003600541000394082c075400280206411400c00040d002000d00514059410302103142c01521400203215265080c40030300c1400341c141c1c941178102d1080360600001002c60000903100c850181c000034000e400a0b4030107500c2c0045140314907548143c07403598031b080c0c00c0da41d062078121000484c00320340c804400584180288290f140c2e218200050342c5404443c505458800d4400031801c0850f1401110744111540b0b1000502000c5905100c486030200c070700c41036029690780188281d12140c03024508940381040c0020301c82c50031440e840201e2901400001404641c80800305d00456000300c0c1030008291044003101d041c0e1804c010440c121031095018 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 319723066 1250 319721816 319721849
    0x7050601050405040c140109030606141c05030a0c080904060303080f160806060c0102041e0303140c0303220b0406020c07060e0f120f0109080403110f0d02040f0204030f0803060901 79
    0x4550140740c0d02e004205041102d14101000780c1c2c46059082301035500008100200780d900c0c0d0209080d04c0001c0300040c01030288540050b40c10403218070b40c0d065240c1040c051458000d10080843c1c910100c0141142d010100740300381421a1a54401c9074061842500d0324422410000ca0205030010001d020ba048500ea1f0b6040c1142258020440b580040090707640d140c41703211140311b1174064052a089410000c2c10401c92610300e05200090504907030090f11aa2022001c0c0080440a4030410010003c181d0080011445045040780500d05136200004521804205a600c1d00d581000035902960342c0c0d40c000c58036a448001c01c0c02220300178603460138280b1982c44000e021030105440031b804148101444000d4003004030050050180c40c2d1481c02c02000400d100d8030b401c101a030440d0100f5900003032200284480760500103003039002c18800a0580c044555503a00708005000d05200d03494049800f031000200284d0f5006004404511070300c01240c9078a0008240034617428164000c500a4115201 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 319724316 1250 319723066 319723073
    0x1b03130602150a18020f04180f030e0603040507050906010e060d09063605011803020a032307200406090204090b0108010302060a0315170a060605011e0516170705060105040504 77
    0x44c0d06407241e050710703810403141c18940010010b00f04120401e242600a813190000c004440c1e200385800351086d2a00345402001c602404024007003280c0c02052a0700411041c00b0030b02d0117400041e441481454206480314042c1c001c540660000c070070b42040b00c0d80761466030b4200013190095002c0e00800c01440c01c0d014446040d4a030f06000000e841a109141e0040c1080c00c1c81001c0d000700d0342080c4800c00c002400849460029500d99502c0d005900196104040001100b00040380c140041600c01c079050402e051500ca8490741100283c8081e24500305405002454886008420043c101c20800603101d900c0d064508081d41e0b0f48200c040d0400141c10014401a9585c900395600525945400a80e00101c03550000014107290803120785007605240810760075100203000c0e105584900410f05c600c40d07079500191248003050134003000c12854a010044013904c502d015005880d00c608081c040408907803508180c0e5040980d6043c0c080c00009040d070b09002c070410405004010036101080903140070344 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 319725566 1250 319724316 319724351
    0xd0b13020a05070f080f030702061b12040311070e15030c1507080d06050a0b1c0908031315113a0c23031503030304081b03130602150a 59
    0x107038014849204c0c810000d0a0200140980c1d130703401d4583da0b802e80d9a0506280280d55414112500590303034030710506041c5100494401d03036100c0e0001c5260310380683c5882d81c00b640c4418000e01c0b051050711074044001603800c0908030b1640190780c8817a05000100140007498204003414400c580101c4024400f04511640b0b08110341150303030048881074407034001c0c4604c44098640d0742c0c0700700c0d8030113213194011510311101c00c010003c0c10000303a403484964240d00401c0c019562441c4014100032800e10000d59460b0f002100da001891156212010402d100107507802101c1d1f161144200e80034000c24a21451040300c0c000400003501c02d0250104c049104a00d0403681c0491444001144d40b5004a4141c2078040e1004507010790001c4c400d0740807000d41414903035094008a511800c03c100c4174264107154100441141d0090350013201e09271514040e0000116220382c043d56603a4184400c003c101c10380316241180e140900b00541c05409486002e00c00c20815810180c0010b1109117082000c0c11881c2148 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 319726816 1250 319725566 319725577
    0x30108060601110a0c0609230112181403030604140f0103081803010f0504021c0308131704080303090d090b0733060518060108040b04170d0b13020a05 66
    0x74603200103040f03440702400b81080040c00e0028440058214041b417000c0e004803e40341990380060a03500c1e071640001c01d85c5542d1401650141c0400d031403645004003d44150440c441348045c0c61440d101c10b0f000382d515074070840402c040c00c600c20340001c410f01610b46003034001c0c02031510310600c0c0303441c050a240411581e03201c1c0600c00180f14803000a0041100c2100d04821124034030000c0003003007850300e81410b5030050329040700c080b40704421202d001c100e0030740e00000f100740e9a90142e80b10369440c3d5840b41c0c6140d0000f40000161a07103c0b00705444041420000020720140444030051516405c2505a00d80b42900d901c50f40707014421040743c20302c4880b101d4010b54500039002400d1b41544113259501103600d14000100168101041d441c4105102c255049001118400d59406108003040c0e0035205005509650302800500c94001040125600018403600180503591000862069071000c0c00c241d8000240d03280d01c15100c861a80c05031034a41c0080090040701e220943c504003032940010071078484e8 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 319728066 1250 319726816 319726819
    0x90105061e0301140f0a150f03060504080f1b0105011a030606131502010209030f010506091f12030309031e0f050d0204030f0f020a21021002010b0a14150301080606 72
    0x3180e40e8004507030b400d422039144003443c500000e41e1410005800214003a0845108054604128080415030b01c0310114104503500009a0080a82196508005400054410307100314105204003a031260001e001001d0001d861440d4600d40c03800303000c030b132402c3d40c005030300c505040e0256050b64480da00c0c01004403980318000719042c40da02c0d030581e04007100341034407900400440c03071809420385001c503015801014514400c80c22034040744110009030742600d000f150b1803908003403403001140c1e8002c0c3c030100745800c49100d0031007068603d40340c1151050708001c1203401d40000b030311610b0b00c0e028190441810a861104981d0151400020480c06080488521441c10070003800251362186402c032541910041c1d0742c04403000c0129611170600324030250240c14140d105190052001503d40c40f0300c13800d6400c649000c07a1000301c0c0030480e001c0060b0440c2045106041d07548813150004141c2d100b14803000a0039040c4141541c0ca1003500a0100c00c2e1100020444201004c000500155800040c420f500040 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 319729316 1250 319728066 319728109
    0x5070c020901080c1c020112091b0b1305010c030c05120d060b07050606010f02010e06010e150a0311060901030204170604110102011e05040302071d061509060304031220040e09010506 80
    0x9286c40121041000607024143d098905407501d000c1210001d80e4544e54005450555000d1381c80d40080c01c0c152041c12403026501e010044c0800495000780e11415055000e818102c1f2981e2094071030505041c03c014000a02040020b544c001084d4584642005005101c2d074440c14480349594041d0740c0c1001804c441d040c808036080d107011191003504400d038090642c4081d1246941c0d2030b107880800000a485429005c07105c404070b0061810800050710480c0d4015800c5a02c0e6050f40b0203000450b4001012141010b40130080401c8209201d0749440012085e50010070084c0b80500b01941d62030300100c0da140c11641061004003044101c6c410b096004c10b0300ca0800a0b45480c0c0346410b92130071055500c1107400440c0800801c14507a40302004501c640d2040c1c078090340b800005260b007521740c4240b4010943c0300609001050219100d541c0c0340040320304405000542e550042e200780c101c00c00d64410f4001d40200042c061160b4541140c852b504800810002e00c0a8140300340010980d80407000c0e0b030041a103 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 319730566 1250 319729316 319729369
    0xe0f07140c0c04050901021603080402040c0e091819050a03140313060f06120503030916030b0a05070225091104030c120503070b0106030608190c0b0a05040905070c020901080c 77
    0x14007c0d811150380c98840220101c55100710318000d4500003045400780d1085e8900f849012030340b4000c012042903400000d00e003840f01e40d5003050b81c00e0006207680000c1396610421071062141003001c1044031180e405080203110603800d07403400822000004101c84003143c030501c18000b03000b10700d45511581d940e00000c0844c5a10300800d142e0010907281d40601c0141d80500d420b40f00b4090b0120045005440b0601500c00840103507003249118841c80c4801030002c80c5080001e507904c040b61b440550855400d105584800b0184408110405220302a00000c12040d40040003420380900c204a0021301924449007402d2440d2a8040c010000c0c0c441c4058800002000710b040210510480e18400da00096000295864000c002d00074251409180928440c1540304001800d0a1200c10009907000f101c4001c00750401400200c55041050504240038003440049961909801181c1c4038548a560710f00d50200c403401003080144043c0d201e0340640e0462210740c11076031070310b90a148680e0461440070801d103 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 319731816 1250 319730566 319730581
    0xe090601110109050a0c03021014031321050a18030213090f1502040906090e070311030a080c011b0906050406081005120d02010509010b01170601090e0f07140c0c0405 73
    0x400c02002c1c02401805107104034000c001e00034926100b52802900d0380c9e101d0360601c1c1010b490340303980500b0300541418180005440a0410581355204901c41e2000e03800802010903000a10032000b00c10a000c00c0d00031542810141d406184203024902c400d038900540342c559008606c1d402200700c5456207060f11281c02c4010300c2030f4042c4ca038007070396405405079489042c980d0f03420009410a000f60701115040c0280000c1c448054042e080d4403003c40b101812000340f466450703070142c1440e9482c068141c022680408003042c000c40244c461032140038004036545040c01030404003000c0d441c904d2020301900c07074018402c455200003594203450031030030710200a0b12100316000070446a42c0c000303503210381100c1105203160b201058a01042045030000c1c0b11036240e68200d83c0c00ea6000c141315500180b1100c00c10050b004182440d2600b01e00c06040600c0040d40f1042d107100c07205411150b8a400d02240c3d014030941540c4481480340b040f40103d5614200b46003d0409500c51490144503841242c40c1d80104100 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 319733066 1250 319731816 319731821
    0x2c011109150c16031b180c120f0b03120703080a1e0c0e030607090b090919020a0c0c05090c040e04020a0806070201060f09091a070c02030109030507120e0906011101 72
    0x18800803400c0f00c1034448843c03a0040c84403c580030898a00101d060003407910740e1700000d100180d030700044641c06d6042c00001d45800900407120403900300000101407040c44041c600c44c52010340100c41000c62880190307001d0603c1d02405824aa0112004219000129503c5040d070798201080c4000425131200f9007518501c4180349103e00c6e02000e207050242505150000440c1321880b00c00c1d0305030f4505507074403a41a40c440c00c03e80304861011004210000301441e00d41c294a13402244000a1ba49003030781d00c0704510482e04022260004a202000e030b850a000d4954a030724000c080403915860149446c50301200540190b100b424281141c0c4c5000c5001c6649421408010700b5101c41100c44615102100034040c003918451424075400c210710206020360240201099641c0000c501c40201d0703100e1a071041401c0d4020324203002c0103600d0034500300583e800c0c044d0480752400b95031000d8a910341350400d4260107000003126014010400300a00c0ca0b41c035400d4140d0b80c0003909084c041c00250400c3c0c00c0ca8003 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 319734316 1250 319733066 319733077
    0x318030503030703060303020607030615030b0102030d1104061407020d0230060703241217070602181c03082e080f06041119092c01110915 61
    0x920701022040040c10390b07255101c001140d00a034210703100c5485008040d02162128000c070704545a42594000c0450f0003908007000000040c81124909407a298a9000300c0b02040c40c41d01210f0b10009041007000c0d03108270201c0c0d01c2d00000e8180c501e0079005900245c00480d00c640028025110100ca0314924100b000d0450052000171401d1029000d1014406440e050115a0000824500130200462003140800d06050448030081d11401c503041031540029440c194404960030300c1d00000200305000303c400984642c0c5d10521015840304d002111096501610701e44030750140c0700044900180110b01c00e0b00c002c2c44d81d014101500203844524403900b0805005140044024401c16404210b51302e001040080b40c00344030036a0003070f84941794800d450b100c059030090094032200300512820700d400c448100740d0080c04120300883c0e81e51440e848066909107200c02d910500717900300c0c90141c00040101000640c4104008101501ea04104480c26000d84581607000742d00003035001000307941400c1200c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 319735566 1250 319734316 319734323
    0x5040f0209100303030e0f0a081602190f050d05061b0910020604110d03021e07170d1d0a18020d06080304080d020606060f07050a02130f0e060f04031803 67
    0x41d12032030652030081d00c14140e88801c4000a00d09002c5ca400c3c404041003050b2580c05a4000e840c01d04500e4448480541110b020501e240a01f02c01d20401a501c011545e070380d4600c0c1102010909140031030703841040000303500090042003024100e00000c2d00100e03040ba0700101600f022103100100700d401c00c0807070050000560b08001060100d016954001404503c2107101d41285808c201e400f20a01c220001c00701d10040140e4442d443c0006824100489805074843c00021910303400c0c0e075004075044450300d50781015000c0c2c02850a2002d0340740e120f0040b01c188078801c1846c9110549290101d884400248199181d80d105070201074a40c00c0c080e012292200c0e82608140005621144459100d40c402d1240d8071052090700001d03002070b400410340c2c510071240207000b982010b03004008992540d0001100b143c007030107000789440041e91070070314070040201d19007800104aa018a40802100c006981c44c9503603501aa0400180012901c585c41e80207625150540203101c101c8152090241d141c5c2005 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 319736816 1250 319735566 319735579
    0x71809090c0302060d091412030609090a0f060218031204090213051809060f04030f1b0b010b0c010e01090b04020d231501090b090a150b0414040b060f03060405040f02 73
    0xa18594a09401c40d4046d10300807c4c4010080742100c00056072000d200e0341100381a003007032001440c00d107007146a0701d41c841c1e0640f042d07034210005952040d03c0054042c0702200d40c9580866070b001c0c0415100c2107407881000940c01807041e01c6c96030700d141606002d00d2207150050382d000180181d41c0f26500d20050020310707001d4008840c0f016480303103010b10640121103c4090303100314400148032050518003e4052501500c40c030f0284a035011007141e0400940c4400031814031004210b400203038050304020300900700301204588403201150220709407007181c0d508150684c1000908404544800c100540259044076004464070482c81d018401642d4a080001307000911070001301c0354071010800c02628208800004000e0380c8505e040406ca607000c00b0490b070000440000541000c0065014103c414501111018021f550320035035012a0700076040410b10405042c1540c8031810715000c0e846000340c049603d0303410519402c09212041c00300600035403007691580d0100307080c05046a802801d0310b8001e40032 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 319738066 1250 319736816 319736827
    0x21303080726030f060405060103090f0b090606010302070507140118031203060b0c06071103090a03050307051209060711041b1d040c020c04090c120f0605071809090c030206 76
    0x10707030000c2d80942c5000000508881d0654551038002e0200c91140d600b800340d090a030384603641071000418000349181e062698850100c1c000c1a012402c10404a1103104880c541d407404031401e6040440280045044c98018046540010008640301007074950f01383c08001d0850001c801210107245000c0c0304580d14003440404401e00c041d0310311203e0b004410307031400c2c01110f6035034404a843c0e00c212000d1640c00e81109010548242c0300d140103c8001d00690102c80c1084403090010300381d0030b400e9008555690000804104010007032001d00035814415507001c5c03d00c06088089155403194000040c00300d0a4107900840da80d4030381d4041040da040c0d0700c42c020380d00410340340094498002074200002540803084a48034901c2d09024448004055602034110800c01c4c400784405018043c01c01c8440c8280c5100100d0a4003c49901203500c3e4000d66051950104d40d051200840b580504080208050380203050000c07018040140d00b00c0301880000a0000035034141082144442d80009600690003d04c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 319739316 1250 319738066 319738073
    0x80d020f0408190b07080a0906050112051506030c0907020a050105010f170f1e0a0203010509010c090e0c09101106070504140f150705070b030403051305060c0a060213030807 76
    0x5801641e0801049699503803501412180301c44030800300a262107000fa00240e017107441403500580203000c1000204182c1000d0b039421050365000d800c4003950385030800c10701c000d0040800400d00c02543d141c100640504100011030303220742e100d2074034034006d6200d0008551842d1003040004845a00708000300000c0d43c40b261032a101a2581c0305144071600c43e400603c240300d4000c1104412100124010003c18003005160306000c640304200d6007a03406042c5a41016072420b02481d4400c0c54244000900c00f403c508010300101c6064004810850b90081007003a01c51b00103040b100d0105040303617280e040740c1c034070081180c0c0070710304101000c440c0c0181e000380184150400040d2007070720803204501d4041c13407016091090b43c400000e06141d116845580c4070703c0d400007440060440602a40541e070b171643d1102000c800760b9005a80480008030000340304400e450300200510054a000c81d80d80e482c2004a0001c541c1e550801640501010340c00140c0400da0104030361203500071a40b0031507064070b51080e0304 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 319740566 1250 319739316 319739347
    0x302010c1101230a06091503020a08120f03060a09091127060d060209091e0a05060d1203150303050c07080601150507020409170340080d02 61
    0x204010120320021241d18116406004214100552100e400c2c3c010701e01c1d10b41c0c0c8840f0781000d00101c2c030440e41c81c840800c010010b0f02030701c2042c41c110700040314021320b54414001c00300b40a91240d0515001450800f40100a01085600000d00c00c003042c0c1e22510b8404c00608031640320340c001440c440c940401c0400300311810103124506a4111940c410b0a10741440005a181c0e0341e1519894038440103001600c03d15140c0004000503026100040c03c191107000810306500701540c14403144103070401035022110101e6440c0303038807203d40a01072085040c01e5001c1440300801c0100107110550701020300c2501c9120f6482040003564450901706001c0c0d5904001e0701070b90007011102e1090080701804a19081e0004055040702d425106085001510b100103c805800800301240d205450702001e102051072410240703260407014103243c0d640d0030040080c000000c246a6450f0090f01e855080440c2084841401c100c042904401d00d4222003071751404030503a01c078280390940c1503840800c0010f084041807 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 319741816 1250 319740566 319740581
    0x32a0311090f16050c010e061810020703121805030a0c03080609010302010c03120204081e1b01081302060c0102310b0409020a0e15090102100912051b0109030201 71
    0x688541c10349440308030100c100d030b610072900c4407140102c00300303181c0c0e60b1032181d07004003c140c400c08000141140513091090a190050754908a04000c992040ca0210800c0c0920034440010220840c80c03e607550307401501c064013400304e03103950b10781c0c41d00304504da01404041c50841c541e200041ea030b03442c12100302c0600103940100302500040e401a0010b005414005001c6050b07c1d01615001c11205040e50b0440300e440c000000041c50340d40920000910034420007a00c00c1c8400710100b04c9540c0194141240c0c43c01903010450380e43d00341a900d401e560760760800155a00a00032065104aa50b440d00120343d481c0f103085855001c640c4000381d032070080250000386d003458240d40c480e08141d050710b40d0401c511030300300d50140002101042004206040e941c0d0300074180304907182440301001b0f44403030000d0303e03581207508400e4545c500040e10420a42e8140306960341403520b082e0410151200fa01d48070140b8400040340380902c0000074518000c5502034410300c158129550080c00200792516000b4041c0c0050b = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 319743066 1250 319741816 319741819
    0x6010210050108011505121c090e0124030c140c0102040f29030f06040c0314040b0106030e0106060909020a03091e030801050108070f03050c0f22050f030304032a0311 73
    0x170390710085a0303440c00a8a0000c1c0d840e500008015485820b910481c41403501181902030080c04900050104514002d05000342886030000e010700d070306447c00c00250101a020700c000c00d8981100d0303a1003290404100310a520305030f00340d0307511501c81401607402031060360040d01c0c500070308038400590030003415503414948003692207050b81300d12401d04ca030a480c0000d80b040c1491a24150019480c0e040940c060880f003540c0d49004035000c0550348551001c4c4209840540300034145000500010307405004030001c600c1584000c10141c0e2a2520042c1005c111380190034089030001000001c0ca40b1a030841c03848550000314400501d00014885d040d00f1640200407000b050303506000180c04d40c0941500780c81400c00e40c445447c140b8005a0407002014028601c001c0c0c00f03410f1160150884d01c04001d00142110541042c3c86c000e113088104106080359800702e031140040e40b4071424035490102c2900d0031282c0c81400000d0080d40820b0710070346914980c00c68800704010003400400d102c030309190700082400 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 319744316 1250 319743066 319743101
    0x60e01151a0406050703030b0303120a1b02070b0901110313080a0308130b010b0a0917031b060108031c09060c080f07080c16060b0d0b0601020f03040e0606030601021005010801 77
    0x20056003290a0203036100e25000314034140305c1c003004640039400c0320740e04071401000c0d40e1804c14204034402a40f0001d541500303050350341d500305800b42e11200351100121005070000340021450003405100c988143c4406604200c0c0c5400d1074640e860b003c10595500d1096010f144945989544c401903807180000c07000d900103201c0c48042140126405518030010b9086a441d651980c01c040801c101039000080d240e040000b01c0400243c109691940c519048500e08099035641a01d0700450305200b4a030303140707050f1580001004000c400800412902c100001c0c8404a08a6841e418110014640190054a443d00f800c401c0d83c0001d030302070000f0b07100e102c0c0d1000e5022292a2014100c50001e42203503015a42401004021003c4d84128000c050291140f079002c0741e80b40c0c8000115152000030f6008a9820700158240715440da0140503003034180f02c2c0300d4000d40c2014a886510010442c01600d043d002d0180000030034041e074801d00600b58001c5207140140199692000070b68001c0c552010405050700 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 319745566 1250 319744316 319744349
    0x2d1a060114030f130305120c04051801080307030c1a1603050c0a0207061d06210903030709150909150f1d16051209030c0606040506100804060e0115 65
    0x100782405a90044465410500540d6105840c4e11101d204007030301901440018406030b2490400390700400d10803099142c60b103488615000500007621170141300860b11440c100010300c01248000140c1e80495012300e080c0760380303200300d06085054a10001c1642d00842c0c03030601b0070001c0c05000d00c10080075111950104202e6482044040e5540a00300609005030014141048650711480d0f1281c240d00402c8101c4888503a40c10014075150300c1110032305e003441d41d540c1d0401d1740040b1906260341d00480b81c101452071032070302c050001c05822440c01200c2005042034903445030244030350f804a0192240c2d6604110010760082c80e500181224420309e601d502405034041001641780025609141c44a00780b1811038907a0b900e619688440d84a40c1020460300b44000b508917030200358640d01070320403280519039500e0400c03001d505204005120b54001d9080c2000c2c4038040e1581210b01403114400d00e00800d06490f14030f0503801410a8001a030031075802c24400f600c0400800b00034000b107583d209865145103 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 319746816 1250 319745566 319745597
    0x3070501140a1107020d0314070f0b0f06090a050a0f050c0306240a110c0303070f030305011212030902121b0108060406080c0d0606050402040902030a0510032d1a0601 73
    0x165600c1d600340c3c80030b91003400781d03000506261065182c1070b071180c14000e615076106403420784643c203c001d050300d044c404000c441d81401185c00e00c0ba0f1304136240a140c400686400000f0455840c1d018003050f05282d0344000050342001070303502c80c1803049a00e85043c016820510201c4ad0a6002995031920503001c4400380400c05403d24844149080e1085805041c0055040d043d940144d40301c0401c603035405402c0c00440c880d941071004080451064000c4011640030f414001c0454071305801500369600418002d0300490104001c2c0b0542c54607510300828160242d10102e112031000f203060844510405035030b491402c10302c0740c5610000c0030a9039640b200303589041c20001030fa4810b1042180070780091180c50000d04051110540c0c030b6008031004101e151352500461300320792144d80702007503ea60210920207900054040c4540203500c03030a9030144103085d40c642c502001c02541824804820409000d80d03540000c542c0e00d1501900440c0201e03444035104e103584581041203502c280042c1d01040519180e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 319748066 1250 319746816 319746821
    0x506030705010e131b0c0311070609211a0702010b0316060309050a0c0b0405010915080a05060d06060b090117070e0114040b0325110a110406050303070501140a 70
    0x101c4005a55012034414900240918907610030f114200c600c0e100c9001c2d10040e40c0c520400e07170a0554035a01c5c955451003a041c01018800d11088681c1070390003c25040080a600002c80c5059500130140380304c018941e9442c1c0c00c51444200750044c4171142d0300d80081000140540c0742845415103070001d00606082204040d19501c140b404080411032076081403200d540309a1103441ca86d0f00c5101200c241d010507490324802498241e1011118640010701401256800324048006158107c0d07003800801c0768410213040203000504090145945000060b0b40b6036130b0403011200250015802c000345a2946c80810941d88440c01d0b00b0b011a001148510380481100d03000c0b0f00c50342070b40e501c9080c040d0b4207000465800da030510202c24200d1082c040803070300300071100046001d25811100a80c80b1034802c0c01848000203550a0f41b41400038004041400e01000705807034802640c0000c0103003420f088000010f006020300d80106400d0311001c14600d0030044154031040c4601c101c6480f10b5105e5942c4500d0707409 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 319749316 1250 319748066 319748069
    0x121f080a0c23030307050f070b030f070305070e04151a040503060f040204090818010f030e030406030f02070b040f0b0604090206090103090620090a14010813080702030601090f05060307 81
    0x503600750107600300406160700101d45020310340e02c040940c00514510000b0300d550444a03040d2010340010280407a80e40c010008500100134844201d8154034120000c400c0c000c1d00100b9038001d150710350000804c0301c0e1142e41071021501d0010001c0108181016400c1c50305100e034002d44810303858048070090f40c00000400d842c00c40f40d0040080c19140da03400c0d00c0f442000d41c003510880c0c00507261041d640000b4001d5000d040000c803c42c0c020b455180501000618540d110000340c0c00b030524061490301075000120480742900c0103401c0204680d9403001e5070b203000744510302c1e002d03116042441c10321041200aa020044460041c01c0142481e12140100b000729015000000c0d4411000c0080741800d50081e0005000340f030040c0780015210343d54034031050036000910310395074108400052001080c94513020410203003941c80050560b515542e40060721140014001c10004540d0a441c1d07020803c8600855000903405401c1c6c50695941d0901240602000d40e1480c007001e040400040460400184000 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 319750566 1250 319749316 319749323
    0x11040f0e0c031312050904060314011a030606101101050403180605040807050f0d0c060e030f01060302090c2206020d0e011718030909240102060408040317121f080a 72
    0x118420580d40704d251465400b0400800d0040611014445980b540b044400942c0500201e801d00401c16116500b107400600301032084480c010403214043e10002100d591010b416558078080382e49203c42580c200410208010f01503003020100400c041e40300020828030203a543e00301802c113454004c16203460149000d805101c2c0e00c040c1c000c00092400240000d44040040c180070000480c07603e81c1014200b40781c00000215034024205e40c21810308100c0c40c3d8440c0640d000800071641981d002404940000d005208107041c0840c6441000c0809060000e004044400d2601b24039034034800030b07464896604050f000301e003c403504841d00354091703007071101000304103603034800a6610b15060030060112121500214131041c00003224507140c5046107400381605034034007200710740604842444040c24105450454000e0720902c00021002e500b41c07401e0301c1d840810302c208941480b201c00c03210300134014103204828400301030102c04a4400000303040650309070641c4106c0303a10b5000640c6d50b000c08800c000d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 319751816 1250 319750566 319750591
    0x30a0b0a051b0a020705010e0f210f0d27140d05071d15030d05030103031b0204090f0c061b140f0105250305070f050a0311040f0e0c03 59
    0x14090040d1580241d42c412941c0e074403031001c00c0010501010710b4000c04003210240c0e1040310305101c3c0c0e40c1c011401308103000303045a03207100d941f140001042000f14403d540d041ca5040301080c0401098003481030709606a02e800448092011841d0001c01030001c5200c100d0554202d070780d07109a0f0b84010f44550003980c0c8552408100355014074140718904d80081c07020307141e6000700000425151900d03203030600b2508510040c1c920b11f00b025400b8465200d1045d05061082e4840e04c592035405802c0001c0e40c0c112a05070070451444086c04101d00003c40d54850025409845e00c0c10400401032601d61345064907015a20b12100c075925a54140ca10030716026440c0340303200010300e4003000204131000c5205400d00386400c0d40c41e001e56001c00079094803025100350301c0001404403000b0f640481d150184040800390b1400380107604040c0406401e44035600b090300200107001500003132040c0690082000111410b414558490343d0f0394181c4402d0010f40181c00d011000d04000c01ca0314104002500c1c015400b01590 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 319753066 1250 319751816 319751821
    0x10e04020d02190335090306070c060905060c030108060601111906021b0f0f010b010c06090809211e06010603020c15010906300b091905031305030a0b 66
    0x810000f0552115483c001e4000040301000042c0c0f076200840030070005040c8040100642c000c2c00d50340728210009655681d505001040e03a07a900028083e17040136403801d02040c00411424000041c0024440243c070621801c03050041d2100214021170403500ea078815241192150001140d1110100000a501c0e03403002a4803144980020007900303040d4070503540103140403003019030030362503100d1001d240190b40c01880c074141016005215000040ba0319400802150300e1200c000780c140400341d84041c00040d0b44070b040301c0802c4400401c0b1650702d1030041410f45500c4500c40c102c1507002c054030b609241d5000d10f1128440185900b80842a003600030405406c00d03138207041c001c4009401c4107036825164403402c444100c60210003206079002e041030070000b02c1e030315080040c152600e075610684c01481c02140c11401c110740140d42c20141c2015803003244cd803125218400140c2c40c00400e02850240080782075941010450004000e05103003003a0400c0890302d550f41c600701912403400b030001901d8820020700 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 319754316 1250 319753066 319753069
    0x20f010216032d080a0902190509010b0a020d0c0602040b0c161401090b07020307030210020f1b030a060f02130e180f12031e040506041106040620011d03070308010e04020d02 76
    0x4075181d005d16a14400070f502c4080e50002103841090000010032644074030300521190512100344ae024002800c04076140660400c03009645881102c200c00030099200f40080802a841e01110300602d0401c11550316188081c581d03985030100b03481880d500400041c8005440d00c402c6074005800c61050312449500391602c2c8181c80680d00001d412a0700d406403003030110040e1f43c1d0401ca00c1414041d58020f091100700450b501d0f00e8090080b00803201c8000f9100847c4107591700042181c01c440d4040c0000c50002c100c44118006801003c001d5201140460008920100480310a61003540e102880303074010108041000d44030000100c91503150b800c0100300c840d800c0102401560031a2811207032500c40c0c554120484c20001c03046d00d003214260040300034402800381100042110110484500e0300d407030f240c2000600241c4001800c800114400c45c0c907228080020b503c044a042500e0b141c40b25131560303003002a03450340d00040b011008149000c0021032550822141c042c0700356405400311031030700183d80 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 319755566 1250 319754316 319754327
    0x5030c01080402060d05090303161b02010e01020a060501080a05190c0501110705040f050a0f050903041a0409181412040b07020303070f05030301090b011103041401020f010216032d 79
    0x820a0741c02200400402d1780006440c1720b8503101e501214041c40c1c41303044c50008020380b4015410414104000d80078500c0c09528007864124660b582400c04542024404005034240b2a03801d0000c0c0103107140c0400000c0d03c40c00070505480c001e00c40c10548203200d904800040a07030710400300c003816101a05005024550252165001c907101c2c3c9400c480e00c05640b0b10000f0240c0e028018100011603c0300280f01e0401c541e406040c4140d1034224080c4100e21308020116601d009134030491a88000d440e4440c0946800031041300d000d041820030a20500e900032000d00560540000220345080300780c000a55401d00c0410300c00420000f400a10340307081c1c03420228900b03c0d00028801d07079040c007040100f2030000750046616806a4402d03809941c40e51300d05031002d001c6070141d4640a05100c41502d10031003082003c000c03038060790f0b040c017040580442410b0040b07150859590301071800b98400200c8000c200304504020340c19a103e9920700c808070109907401d600195152045001c0300000c07043c940d03e01070041 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 319756816 1250 319755566 319755571
    0xd0e1506100c1e0c080304090903080105040b280e010e070f021b0f15070b01080d020309060f070c0305030d141b070b04030203270f06090303160515010306140603010605030c0108 78
    0x2903611a0740304d40c45100c4207042d03921550001030155901c11140040580042842d40100b070308a0302004002562004135412801d808655000610f01d000c00c040c403200420401c1024013030f4540d03603100700c5da11105001d400380c00542c0d0070808541442c03903100f200c6200280e81000c20024540d49445105901e091004010240300c2d540e5001c52041c40d618800e04803240502a003d01a000d0001294900340030309040901d44000c034821034200700034000507615141c2c21120404049030800d9507411041c1400d9052504a801c0184540800640503404a01640280b10340d00c5880707100f6a02d5460704081d0b101d0320045400c482cce100134030a000850218502911b1550700c2402401681e142c4002d4014007582c59810300c0c1030100340403c10800c000c00b818907104201c20a0302c141c2d1054070f8005140002540c9020f81c10800d0060b1210b40c010f0010800c0c14042c09600f1110040501c4a5586929081003d490620400200301d41424005240351905005440440f000074010740054289040111480c4000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 319758066 1250 319756816 319756823
    0x170306060f0a020303071106010602300703050c0106060804020a051003150605040905010906030b010e040c05040c0806030c0910091a031b031905120d0e1506100c1e 72
    0x40c01801e050718460310003032407403425981c040d541d0392514480181000f20004071440d0194041001800b40c150009107008550400290111140656254850800c650b540000300b1028010071003104140e002000b0308000c0750084000d0080544401c402c03610200101d030080c7d030220070a00204a1810801a140c0c0e10a2480c43c01107280300700704030340280103a21648900c0025100280410920303030395105090262081c03100c02d00440b451501d4070a8544010301403c0c1c0603c2d1214080340c100b11038405110003c001c060400c0c4401c50891201074522142221031500a000380088401b0601e488910b4601c260f041d40c0c0d105484500b0991040c00130110b03401d00d207180c142a01120b80241d82d040220095450140f5030041400d07045005044c148200310001c11011105846002c0020b50007040075961f080b4582d01c202d4603940c040504002610384c1288415541c0100c01c0041001075461148601c41c40c020f0742c882c1281c104860b411036804a42a60103000a030030403507045145102403c040101500 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 319759316 1250 319758066 319758079
    0xd020306131e0f020f090609120a030c0c0501080405151e010305070303020c090c040501080c09040e01140105100503040210170901020306101e08191503020319170306 73
    0x903041100100d441c948544040c04004009400300c01c1c101e4000e031185044604415405c0020815221465004070300c442031244c40046141001030303e400c3c486000301003002c001c542c198201070030091304041080401303480c42540b2000200d1154061100f04e4081c980c810003c26000c035590308070707414440025080d90751006600d800c83e24100103400a042c00781d8007810180005070b2031840c000c0d1800d95401500c6000c2c11054080103080f80c0d240701682c0813980c00382007825850395127901c0e0500d184915980240d02030302e030090030001320805500020310940c08100900306641c84504020340200c01e02c00210020390b0400000c0c0040c1030071060340440715400e080c02002c84040c0c01011002c604102c802d12081c0c0c2d03021007080000d00d44101e01c141070120600749880880700c900318804c0440b9550180c0e6080c0840c40b00820782c40560307240d000c01c49606011040006003010480d4048140043c4003c0c0e01c82d1113a540910090b6103040584640c141c3e204076022010548466a0492500000c0c00c45a00c82f5 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 319760566 1250 319759316 319759339
    0x604060f0827030c070609060c0f1e050a0c06020718150e1f050607081206150c0106061d03060403120209060714370602091c15110d020306 61
    0x302c500c0d191086010965003e1078483c2032010344945001e046920010400000600c208201604a0f508424968004401c2c00612003a8200041c0a40303d281c3e07074040f845030046010381405404102c8504c0c50344105a180c0410369155812a40c0e00200c1c080c4085c08002090b41003448100d41e807000418a8031000100040c0b07a44040d00040700f101140c21502c0b41e2005041100c402840c3c81381a00607200c2128101e040445039103801d8401c0c000c503081055008129804501940c0c0ca4512190500460204441d5128410301d800e0340600341600c42c800115500b40840c0f1440120785c3d44441e8180c00c003a00a141c595216202225544550041500d949500304400324540d11410000d00d203983c001c441d0711182c110841080c5141469403440b19282d00030240da2080001003100c01c6c00e109004120841541c100d00b8100080244203800b003455011101c03040c004002c0d1400c5512450340c6020f05101901600c1d85908841542c44003000c01c1038050007000381500c803081c5640595048100030744182c1490 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 319761816 1250 319760566 319760611
    0x16030e120c07031203020c0d03140a0509010e100e0d020106030f0f1a0408030f0c18150d0f0b030f0d090b0d060b0a0c020405090705030a0809060c100507030b0604060f08 74
    0x130040040c4800000b074000035011030a820400c1040d80d14840303850104a070341000da11415400c54040d2001c1c5800da16140480c089034825003100403021580425100c0300810030350080000c220343c401390a03544c0075124460420500600c6000c0440340c108101012495960361340a10b1001508812605400e0500c0d8640c10507031000b00c854415881403120a5032814074000d0829242002001c2d1422a00d00704068400c0f015030786d44610f0303a50f0303041c3c80740700a0340559001042107004d911443c004a42ca020725000300c00d005500800004141541910301001303500c3d091503110301c0d5284407000803401042e401c0004000200003046548a201e000203006519080c0c403000030b9000d42000307000200034201110a51034203108203900304c1c00420080c11100c0c602804251180342020000d0659071707001c581c0d002d1944641c41224a4000b064040d19054001d0080c100f0040c0402e4410700d00007840c020100a003410161b007114251744054440015600f91048111228000240b40c031000c0c85888481c074168 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 319763066 1250 319761816 319761833
    0x706020613230106050301111c0c030b0301090f02040506060a0215070e04020d020d05010e0108070603020c10020304050f07090c0e1c021201090204050f0708010b0a02070f0e16030e120c0703 83
    0x108000c07030b400402c80d54038100c1054252051070b80d81c40d1702d444040200c007081212001100c04401500e11001ca09880f000707009070010080323220381035055420302d881c0301e0400c42ca4003151084548202c0d0100b181d031304c42400b48005400307112000405071303201c008007904410074000f945038002001d1070030440e043ca8410200c3c040c2d810281003201c510f5004143d41e0910744050242d5805800210100040e03589810b0740190340301094801d00c4281076000072407907444d0000784120a00c1c06e00201083d0741e28102440c14941d21113000411030b086000c2c0300c6002c680ca40150088101120083e502e80075000d0f1450101300801c0c084240c8600b0400881540d41300503101c0032600101303c10b01c0303800016031555600521080e601d005000c001d24a8018040100031500414164150342080190646682c1c0303004041c0d1800c0340c141c0007000e000342c0030b0710005600c1c12040c0f060361103002034074030001c00d440300058103400751085240e2110090b0000c8180e80c400b104108060140151000308507031609940744c03100c00d031 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 319764316 1250 319763066 319763123
    0x402091b040905150f100507060609060803070506010911190c0b010308090a05010504080709020f070830090607140d020c030702010201060f0e0606030a0209040f09020108090706020613 81
    0x2d443d101e808200400300f0300c49161580c6101a54030b0444003038000d00068042c028078405d0000d0050100e654028068680e00c248040d01124908101e0306031281015070781c03500034400c2100c10f1301c9030100200e50301c0b04601408001e8101400c00600346829015440303005d050783e40d40c071010084c0161002002c00c00c40e02415000b98010a04191b803928a84207010b540c2d01960030507814058208001c1080d20400180402201c001550050f1940381328060415648900766016060b42804141c004107405403004118222000544100c5802c000c1400040e00c820111b684100a800020000d0390b800d01807158161648045607174240b0349910340b8015412604452492080c60b48003050740000c65030240708030405005250504909985014444000420700901d0140282c4c400302c0402d14a00541d010388011440081c000d105d00d4141e14010001801079910582c0002d03140b8002c1071103002c010030b2103001c1e50416406030085a444030540e0b2540200c1d10b504980341c4921304180b2227440c054648440 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 319765566 1250 319764316 319764329
    0xb0403090608070c021305090304050d05030406021603081b031b010516140a0c020105070606080c040f0c0f030b060c07081c020309012a02090a020903010501090903080402091b04 78
    0x500e050800030000e080340070062442060201c0c19440c1c001503903452482101c61009400085010b5548111150441c09540e01c4942c12505038a0f5582c20000080060300075260b180c0d0031141305a08040242d42901c6891102800b032030000c20008008240c4110746021103484102102d1421854012800140e07102e0348000036665901c00030701c00c1c00d0100300040d040a480d186400e10403070012400b001128815404c0e590309100307803951400116402141660641034104804000300c0e580c0c2c60416486003d00002584154940b5014000c100e6903449500c80d0b210559031991034100c0d04280a5004041400400b54010703818044a80149410801000034100070f01c081d04002c01d9a600d11406803004048000640d002030001c501581d0344020701c10003080740803001040240c014040360700d0b040c850503006901b00244c01d0030000f9248031a0020580040c042d4000c011a81c1e8170801001201c085400040c0090007100201d4090718001c02000d03040703000030001c00080e01c44048802035a511551100 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 319766816 1250 319765566 319765577
    0xf01030e16080c040e010e070e070e0307090c030c1e050a030209030613150209010e010c021210020a090e0405461a060f060d0f0e030d0e07140d0f0b0403 67
    0xa40305044c00c0c0180007000240070000d0010b4040c51034000e880d89541d0258050080c00074000403d00d80c0716045c0d074019010050107440480e5155020400034003200602d030703008031b401e10f001c003400b0302d1141010401c481000c1110100c131200c55030040741c05611a031001d80030541c0902510746d03903075410b00c01e55000d15402ca4405102c0001c0c1c1c90041c1d04d1040d8040041c42c0184148490101a41c0004481c00c00c1c0c4000d29001210304101c2c4000348040c00c661500306118451a00c0c0c503404c0080c45e900400303015a0300d803240c0303500070340e04c0c1d4441ca0401d41c110b900408513006400842c1c0c91600e00070321000c188074008605c0e05001029807880040c5074820010b6001d1000302a826418008101d1018826024201c4c0c00c0304e00386441000318840095050915010320300008900709190502d40c05079a10034a402811f0110b180340c06070080c0e4a0300300300d0014903410302e0000d1103290a44d000031144101c0c1c10500c80c0c2c04944a41400300281c028940c5001c0c0c40d03000416400000141b50541c90501c82c2e03100b920344 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 319768066 1250 319766816 319766833
    0x60506161211060415020706090b010519030507051c0506070f030b06071e111c020a0f05100e0f04020406031a0405390a120506030102090f01030e1608 66
    0x900daa441030081d00c0c40030b01081c4002042840e2000c651140c4c02074100103040c941856186000b0000e10078080084c1487d131500d003a00c000c111030442142d04031002210400031040c00700d000c1c4080341010703110040855000038410442402e108075624100100198510100c10442c0c4401c2d081c540111002e0000035a4590410702c415014850480203043c03da44082c00c1141c02da40b00b19440a00901b012610750710300c0801000c0101c8452011006000039000105003003052a003400c0d00d121007c0200d00c1183c0c0c0d07290208005507803480010480e00d00600c002c0901000340c0b03042d03501000384030b08550001110385508074192201d0000f03000401d20740d6800602d443d16095800317034480030304442d02d03c00c9080c2014050b111081c06910180801400300420040d202000822840a49a5a8442d00354408102803041580107031410110160540303043c015542e0b94801c1508074803803040b0f5194802030320084890705511950109210384075000c110741e10700d895011002421071480c0c5c0b104000c0d50150700d1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 319769316 1250 319768066 319768073
    0x31d10020f06091b0d150606020c011b03090b0d0204030c0b04081c09060e0415030b0601020715080714120903090a05010507020a0306020310030f0605010608070203091e0406050616 79
    0x4520381c03008003c0c014010403050002400ba21070030248041d4032a4050340311070780a00000540c450301c4108961070400a40b0750350140651580000c3c004e11b400b041942041c0704891403020340c08011247d05035a903080490824903a0081c9401c4910900c2a0030303401e10001c0000b403512038042018200040486031038074a084803081c52b00b00580725400c02c1490380d891f2951002c0d002a0000e050741d070301d814910384056036500031500a10040d0075581103c5000d540c00806d0007580400783d801401e080e0300761440283c81c0c20301058101e0b001801c2c03000090011001440b00c0d0300ca02100482001180141f42c541070482000c03103900b0b2015a08100d4030307000007440c1c60280ca0452105002084203007003070760070054581c00085114103544005444030b40c0000003d0b0707890080c650f5110165510689100c0c507101c0b282044401030a09009440204030508042407520b400082138035250f03400140040b440e42524049020040c079205801908940c0724900031811f5501e0034080d12031aa180c483c1200c400200e0704 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 319770566 1250 319769316 319769323
    0x5010213031202032d0f030c0d0b060301120308071e090e070e010e0f03190f050631050708120d051003050a08033607050f01050403031d10020f 63
    0x100340b58190360040100c407000c00b040c2c070300c0303041450081c0415622143e010918200e940c4103c1004c0c035034541c6c0000c10049200f0300903010b0290850707110004c11080b2040400c0c042988028050105400084810840040c0c0f20b0703030460760301400d5490081c0c8121025540b90040d14408902070021070b4000006003c1c09240240d03440c0d01400600d03000701e03442c00c40c0001034810001c0170061401080f100780b0420042e2002c000040c07800144082000c0d02c2c0a6905016044148100c4102c0d6540100740c0441e070b000c5082031040303a0104800c0c401203806e0700f1038907030741890001d80c0d90212011302030b059000035031171000c3c0300307031900c00601c11301c40369851016500303800840c1c0f0028504a015010f100c000e102003400040d03407009456001c5165035590b100c41043c43c000f0701108040300010405450008903114201e0100113001c1c891900321001d158840c020010802c00d02c048640c009503043c0410804a0711481a100e220490103a503903412840c00030216100000c001c00c8000560310030350004200703c1c1c080 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 319771816 1250 319770566 319770593
    0xa0b0a1401180602100c08150d2909070905010506041e030c0602011e0603050d121b0509030607030c05190e03010906150608010303020a2a0602010515060f030109090f0501021303 78
    0x146040005032410240744030365103210001d014011303109e80900c00d04001118001690050030517400aa420388241b20100c035281c402c50307150300c04e4000c401001480100b41c1c0180d40c184d8100810750750616091007204000045d86044044020304103c40c00804909030240c0ca102802c490360010440241d0907101d00d143c921582e03142c0b0a16460400d0030004118082756002c00d8407618600040e40e024401541c80103081800c0d403480d46611045099151290800011b0039408404d4003615030b16034582000390100d5035010351040114000b08054800000454080030810702075050034480980448042421078001c00305c115a103550f5040711400300304c251a401d0008107500d01d41820b0300c0d070546d50f00075260b4100040042041043d40c1030b51401d00d0100340c55001d05607070076011007441940c41d074000b0301a04055400701e018074501106140b082c00c1010417120300700d00c100c1d01e4030f1441e41791200c0540180300304601900c41c0c8a110107140e0015000b0f000410f0072407541c00e4800410760850925600301c01c1030307 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 319773066 1250 319771816 319771841
    0xf0601091a07120c1b151b02010e0d0c0e0f24060d0b090f070e01050703201203040804080601050409052a03030a0201020c01050a0b0a140118060210 65
    0x203101180c4074950007001240e01095010020040030340c04244250b4500203c40d0008054100c40b005152008010040010454011400015800d0f20102080e100b80340000503d00d1512005983e41016501a186109180b02c0142128803201c0642c2c440441d04902a005410311009840a0209120907030300c0c01d6400c08120307545950407410382c0c3d8003052200c40652a00c1c0c0212404181c841c18602d4a902ca0f100d451006440000030f440d00710382000e00720350111000c201042d040d2040d000154800c5094a0744241c2c584c542d034108120100035401400720300200700314980718021f2140d1002d210a8003841c0030f1449482c4e40d684072400c1148541c109a030580006000c0c0f071070628103801003400096000c4100c0140c0e400e480310341556640070780c81d20f020310018139010b00c800608400c085034158000c100c07810048008110b01e44403082c46d4015913010200744c40d03100c03130003000501411211019126958005040c0040311102440f00c580c1442c1c1c01d0f07484140960030a40e404030b608036040c0130f1f8600c074081 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 319774316 1250 319773066 319773089
    0x60e1602070b0301140d0b040b040302010c081b030a020c010e100e0105130f0501092102010b0d0209010e07020102040503010c1101150b1e0d02040e0402010215042001170f060109 78
    0x10442e414100c0d020500c14448244108102c3c241241c0790b0000074820107030840d00f280c4080c84d250600d102609819502180103620f024020304035684620340d03640c003070000301c014242420038502545280c1e030000380c210a945a070070003a082221100740701e0f04046813003070009401060f803049801c030102c41100c050410070382d040c10100102209030082c1c00d05515400b90302c103242405036003009401031801c00d500030001000490100e00d001041440c6100e001c0c0b650380248510303d0150103009103889803007402034010107602c00500120b610421591b91100a40c4001420310b0754400c0040d0a42e03090440d65004240404094150030b0000e0140040d8500812600c2c00d45e40e141c04448402441826000c12030b1150541072641040070000450f0031500000c1e4056442d6900d885422504030360035034049015200c0e5040154400304000ca42c50721668000c031400c070444c4da00140b00c030035105049900781d04001011458224201004401a004001c20324200e1924035012002500d2201b00303401050000d00d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 319775566 1250 319774316 319774319
    0x804081b09071d01050703030905120904200703050c0a0b0103080a0f081509190501090506120a030519090b0c0609060a09170a031805100b010c11010c021201060e160207 74
    0x31000d290034442041c20b1a01c5c2c1d540c0ea0060804500404c01e84030700070102d014001c1e1191a12501401415251908440c00c102580c1c145a84000d511341c81c0056540034201030203001c01084c01900a4520380f40302c10150b4209500e2035036200f4804800741c000f21490300c404503404010a034030201e1094846801d040015607428541900d60399120715000d0a8429144180000c801100480309413140c0007152401307000c607585400ca000080d00003210454001d01e9994805c40080c40005092400700d07400d5100c0138a050721003241d2180c03001e1800d2104040c405141d400240c5140c904e001840b0041242019190505104845900307010028100c0d0500d80d0600423038101203070600107060a070391007500103603135901840001900680740d0095070310400d080401c0d9080611502140581c00b081c1c421004001007845500107540480301090003405500311a036854010354068030010904d00d00041c4107007144d503d5000c0315800d64a864000764006081c8d41c05000741c0c3d80400301da4130b5070321500f80090503145 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 319776816 1250 319775566 319775597
    0x15030f0c0d26040b0a0f1b06111e04030b090d080115200a020102150c040b0310050a241707121b020a020a0b0a080610050c0304091a0a0308030105010c0804081b0907 72
    0x500c0c0710000b0b00840d44d1446040b04c01c010380701c1243c80b806040341c800ac88000c8121101d2200390060f200c25260640c0b0310000540040f004110035503440a1903c90f2601359080440b40c440744240321440000340000d003620111104920312016501c640500010701003800180300080c1050780321100c800c0c882d1078000a2244440316502500c065410ba000d00329105e070303600004110030b9080c0d41c0c0705680102e0541d001241060310300f1050045043e80309103000b954000c4c40b004441c2c44031221000c0302d85150840104044030310072003054650360000580070030140d1a10b6950004072850165240c0541c2c002088402142420032001006014500c0464205011150058100c51300105403d1142c0c0081d2041c240d84c1780220140d4440040c16021240c6603529255010001c101d21002131240000d182200c070b8051804103190001d0300d41c0807800506591901c001902e400308520741c00c90300d4100a1101241d400740400c442140d42d080d8032024201c2074081c0f41072100d501009013041c41088011300340c9c00e100 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 319778066 1250 319776816 319776857
    0xe040c03120e060906090d170c0d0206010311120a0212030901090b120105010e010507060603030504090b03010219081815040209130f02010c06020d020315030f0c0d26040b0a0f 77
    0x951083d01c001d656403500f90000741160301207d42c01802c0c213640c0444ea428400001000e821100e0518040310708801030074106a9070b4045c01d102c0104540034101e42040c0500304101c0044c1c4d001c4070101202d040c65510350000e520700d900d28001d001c040c0c0c4042001d5601e5a44091998000d00c038a41c80c0d40d1500380358004040d04400705002d49030500c800c9210381c204130b911540854101c1034000070308200305510703032030300511540c05449004030341c90801001c0c4d03100e0328041c402c45103000b40110700b8121928010b901950b0040004206400b101e5001400118071503061044d10502d1040303408603401c038941740c410000603450250014140c4d1000c4080203000030192100c012020b030b02420201e481034400d203071040c003074403d002280040a0000c014800c0514044491a03640002102501c480d0240e0901e910f50360300d28886880d90280c403c00c0c0c2d4201088400e4000c070310060a00c0c192009820f26141940000c1c4e000768440c01c000303200001e4403200c0c6507004440d404a42c0b014a0a00f641d018007443c0d5958 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 319779316 1250 319778066 319778077
    0x309050a0b09090405120a09030c05150304110303040b0a030b10030509122b09050c150d020d09050a0b07031505180a0609060605070302120c190501060e040c03120e06 73
    0x9600f4440c0404c0034040c0800200074001034101c100d554420000c0c50050403030002d031104450755205207201051501e803101e9814142041d40b07140504541d00c82d10b98254161a000003590103010402c800704010319240c1c01010303100b200d41c5010581d002410b00388904100e2007005d1004041ca4541840107a00011821110098248444640341c0143d46d0141d07100c0c0301c11401c01c1d82120402c00240c08448174641000d04154003c4040c1c1e44040448014044100f00c80c880c1118101420824640318100e56809460402c65100c13000030000a1680c0712487c007030300b0171800d40b0140c00203020441543d03494059002080c00f0001c104185038903200c0400c00f1103c041d004100b00d00c2c0740900096030000380c1e510080c0100361219040c07248036501c20001c4e10b03613488140d06800600490402d40800480038044a0001c103060004102d5440d040940d042c0500c50104126925504c80c240000d091001c151464000c0d17005846140400c1e2551801c551681210000801072012005286c3c800750b4070701040c0d40 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 319780566 1250 319779316 319779319
    0x102130b03040302030d0617061302101b021009081006120803250f0e010306030c12140609010b040b040e070302060d06120b06010201061215021e0a0c0309050a0b09 72
    0x241c0301d032210314080e429400356517a800a1586420f500040140e500c0840c2c01081d680c1e4010341c1d00305c1d01c80b0b4030307070340c07441c02408001031740040e88100400e81d054031a0a00e0703040f220441c07001d0300d0500020303400601594058480340001076405541072150040501121616125000041000ca460702da040c50514100c4075000e0071180300840040c03c10403407101100d09010040101c4000206503e0018108682440d191030004850880c0131100354082e201d82c1c410741b600040004222031170f0101c44250002e0580044444110048443d40e030043c080101c41d0140c00024004580c0742d2202043c0400c64030080f400d43d102c0e0303081000012401d240418500160381e019100315607500c005003003c0015201c154411110220243c03520004d204074545c50300d0261000740c2c0248030640c1e44000300010b1a4400201414191601e05c0b540707500d21007070340200031103078500c014028031042d252042c10040d08241081c1020520b140621820903a20842c5400500780844d881021141020504403090140b0700c0c005 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 319781816 1250 319780566 319780589
    0x70506030f0a150513150504090f060207080c031612030c1b020a05030d0c060518060a1e050106120501091509020d0b0604030c08070e160c030905130c11010213 70
    0x240c1c1c0c120521510040602001707054002c4801e5404030541c01411007041c0c03085400341c0001c0200b441d2070940150140203030040d000115801e069200d84009520040044408480400c41d1024148082c07018100803d480c1400300c1c48090281400300d240000924103004151601d0b2400b403000b074000304001140402480c030400b101c411440070910040c265082142c0c036100f4245080b00850f4880d1010342d08901c141d006009070f49510550605040f82da094403071550300321200041e51680141c0c0000c11400b15041c08140c50048103a0034401c8a100ba0081b400146041d408800340c00744074001c5600401c210002005007940c2c40b1150040b040c0705024464031f840d000100c000ca515030507086644000001400103544507561700d00850007500354410204603008640c03000444180c074070f07125403003000f45152560082218520854041800300d604a00380f00b010a004940791b11440000d10380182c45083c0043e05104518000d45800a01054001a80e004020020b02d5000e201200c03c02c0300d01d0060304 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 319783066 1250 319781816 319781831
    0x8030f090a050105010f1e06270f03060b091501020d050a0302043b10030b1906092412230a050d090b18060a030f0510030203070506030f0a 61
    0x112420020080000b0700650300f454008030300410388400c203500b165407041003001c81020b070710240303603500d60b403480769801148000800b03440302d2040200002030258098003c007083ca03207031402d000310405207800943c0c0856803001c01c130703d03d41001c1c0207403500010042c22031524039900f080000d603030f10b04180741c0200300303c3e004c9442c0300103034001e806a40242c030311264803c007480c1010340801d03c149402d041105514280310202100016650100f80c0900038904004401c6805c40d02e904445800107440905891520076013415020300c0c0e8403c84000c0d0552840208554080d03076107500e01907a58070511074460f808100d04000007180310b00c04801c03d960000e00d400f02d5a0162400424091090750391412900521744990200040402e02200304c0000c2d84642c900310b6142c0f50910f195000d84492075490014404904c2840e00e0000c003d07209850745842c01040c0120945003080075940c0a44096600307008082c000d10441c6414029038000d014107030303011800e5262404034156600d1001d0001e551040d9a00f46c0c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 319784172 1106 319783066 319783081
    0xa051e13140c030411040209121b011404060c0b04021f18090507120f020f0f0304110409051c0e0a06050c0c01080106050a050c100905060a0509010908030f 68
    0xf103000b81c9110802400029408550b1482d80400275031501e0800c8902000403122052001185410003442540013518040720510521400d5600340014800c0d16030281d8180407080d044141518a501c44c0c1c004504a110020005000b07009095050310041d034010b4101070007005000300c800b00031643c9400c03400895070180e440a0000d505610680b2442526800c01254240c3c41400185024047c003050030090340400008040e215012040104ac0501040094080704c0f00744c8081c00b078a5029542c403503c0d02d00c0d07079080b50001054401e4102109100300000c80049801824450403d178851901400c5500314046e0041c60707105030000c502e165480f0341242e6048500d0740d2070380d9061000b40c40b4140e45a801c4411200e000e480b43c6008140f45052074016143ea00f40501301400480c1402121401500e200411a000b10382c145141c0c500080c007a001144e80c85940d11080441035201d860 = true := by decide +kernel

theorem cover : BRFrame.Cov 319604316 319784172 := by
  have h0 := BRFrame.cov_init 319604316
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319604316 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 319604316 ≤ n) (h2 : n < 319784172) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
