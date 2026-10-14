-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1612
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:51:52.851842+00:00
-- url     : https://prove2.me/submissions/aba5ce56-b679-4c17-9544-d20711841f8d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 289748201 ≤ n < 289928057 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 289749451 1250 289748201 289748209
    0x4090209012a0f231005010918020909030717030609130f11030c030d0e040c031b0804110a0e0f0702070602030f030603030409060e0411030616030c1806020313090209030613030c02 79
    0xb102040a844c2d800c80340c800e440e00642400740d94050700d10008100610318070985201484060828001c0c061a102d07030000d0400030341881038520b007640110040714500c00364048100a0350080716200d00c04c145501c0442c4003d0184520091482c2d0b200c01c01c4405a40030361030720401080046001a0700d03210360030002949031000e00100d010354400791505814126114100302c10b43d80f080d03407070104051600503065954891180300c9905029141040d580300e4445081440040c100d5241c010381010100030001a019400e85525100c2e0080380e0040c850340d241e4000c100e84481c960b104a02c01a8401e002c42074803402c404c0c00450f00302400604480c5000d695010520655505074041c3c01e2020200003040144100200c6201480404801a01507440d01d00108044140d80000c40010141c0c3c0d0403044812a016a510504c5540d804081c60341a641d1800d00a589a0100b034410a250b480c44800040000380d07402a25504580100a000d0640d00c40e40612050301c42c081e001d6013040300f070f43d25000150b21 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 289750701 1250 289749451 289749503
    0x1a031306110408010f1a03151b030c0703030b030114180703020a09060503070605090117070c050a0b16030902030c100c0b010603020a0e01180303110309040204090209012a0f 76
    0x51043d0020500184480590003100d81281c00f007110300c4805500c2489a55000c030f100c0d10041103107281d90035907132508204101d00d60242980300d83c20f03810010601a021001401a10701640301c0c2c0e07070034070451f5801c805050a03202e0440c10b140c925030b45540800c2d0b040c000b13070b8040c007803002e405000c60300c126035031360009241004035038040032006640f00b1051081f81020300c0041c1c060010307400e2451500150400091040025408070281c000286000c80d00d02480380410f403200e203800c6411141e02140908040000030340544201581034200203502c0b804078000c0c00380c20320094004001d01441080c0b401404000001c100d40380c420021a1f004170800203405402d114041d0000360b07030068650811040141416000724030590510400807c0844c0e60a0f000c030340441a250703d407030008240d80000386014918041d40e0b042c0c5502900206d804a105642a405080c2c0c0180980e20301c802075002604000008420b0b110800d202ca1000080794046546c1d81d200101f1207200e8500740400502d40001042205 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 289751951 1250 289750701 289750709
    0xe01090c080c030a23040b0c07080a0e040f0c020c030105070e0f090402120a1a0a050405061b09041e0614030706110c0a0623030105030a020409050102220f1a0313061104 74
    0x6030321201b030000380100f0710f0301158481680c0003850300e01080fa445464943c010301c901c060421082d541c0c202c0d0f26031a1078014400340e0582c0e02040c0303c0c000c00d5080180d120412984280d000e9840e000000e509140f050170280e800c1e190140042d600c2c5602e0b4070a00000c0007000b002a60000da41940c0c0042c3c5140400c010320710300e4066440103040015441c0154100c5101402001805051400340800b20304086010354001c40c4648a800843d02c030f11015604a01641c4016070f40140381450502241d422008020702d4080f18850410401e9101c06411088000c2c10310070303a826a100300c10620016000ea50280080b4400604070740c048400b800000d62f241800d608041c0004054504004100c0740003460902d00f9803040c20034505660501d0040f0381e8440d103200001c2d00c51501c3e900301006000c003e40c1228110700c2c0700c1407022840f80003511810610150380c40b4043c240c140c8444009400c036250140b6a0544110b5412940703141c4805803e40703034072401c9203000d641146e03480082110a003240c10040c4014 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 289753201 1250 289751951 289752011
    0x9092003040c030c050603150f0f12030a0207080a21270510020706022e0f050103021201020702151809041220030405061309020706060e01090c080c030a 67
    0xc90642c078002104c03071844d600031401940c05201341315134003505070500c246d41c2000f601c1c41c1c0c1884600e000010640e9160805468210b444500341e0301450340d001c0700401c1402d0040e0225030440d0342d01d01131980c0d5442c3e00345001d000100083e181c440f541d4968162800d05903054a480c440c00c0ca008a5002c010007003144105070f030303001034460030005400c1c0b000076025001858005440c15070300d8290301030340311105203420300440301c0b85400d92541000c02c452000310017142060204240058200d0b40001040c080c0001d81c42a03c0703403065100560b1050003250030b2240e0152188210a0741c407404001e01e900540d800c03a040f0300b00029529103a4480b402e07010b00c0741d030190166480b10b8241600c040c140e6005000072040044c0c80441c1c1c2019a18000200c82c00c98105540040d83d0301204010341d03a08131019080b2007109400010500140001c0341c00103c203940c040c030051031035030f660340b82d80380c0803207005929100100e12741400042c1c1010014014550040301402c011403240c805822040c05a40c00000c01404 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 289754451 1250 289753201 289753223
    0x20d020d0c05030f06010f020f010e070e010807060906080a0b06031014060f0708031f0b0c010c0f0815060c032208060c030a0e01090f030507030806010305070909200304 74
    0x22103646020708940701009007003081c0396040c07030340152008140041c00345040c070045060201c0000c2c4200000c05c00c506842c030007000505083c448070741d11603a692250619080f68040040b411400108a20341251f02c55213408601e5460410244c9209000410a000440c2d07500301e040e00d80c0e11014000c500c10f104240d03d07802c046040000d01c040428000709141e0140f48140500c05508003254210b810702c03500603100949a2340c901c481c00312852100c01901c13050b0740c800352000078a4042c40014090300f540800007802041501d0804079598a10880503c0c00500b10b200444c401c0340341881d588a000718041c0020f4609202d03410b05070b24513400701188055401c0241e0603180d08610007103450010f0420480500303045e0501c0c0d01a5180c40c080506070304000c6507a07009002c00004258021030500f5480b4000448215280c20040c0568011803000d0f008510080001003203584680302d100e00c034401030344542c00d045d810603400d84010442c100b00c0208940c1d00c0000c140d082e00c0c1000203984a6071017504800c40d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 289755701 1250 289754451 289754467
    0x1b0a0b0403050c10061a0706020714060138090a0335040501020304180912170a0c0203040b07080f0309030403120815090a14070504080c030a0206030a0e030d020d02 72
    0x45000d0704c0104450205107421014860b440650540740e07030b082c2d4100b0300c540c1c60b9030305070420300001d200300760000340002603003e45407102e69000708503a8120782c00c052aa9056281c4a860161110740e901244094081c040c110500380307089001c0500510900545900085070b1603564074458603040c000d0a074003031761200100c813248084000340a80c884881107041c034206860f080010303649008501802c543e0001c00200b038801d061007a800300307034116040080d50b4880c0c000e290000e004050303401c4a50090009850006403040003030300561001c1909680103503e054a05a0154426080f40c00100d40c448010402c00f4000d0010f90082c5000d40e00384009155103030714500e00030032800310300c00c0d182051045150802c04000400c40915030140390a50350f440c001d564003410440141000c4e2201402d183d4200d062011480c0d00a001d8800c1e117050404450783da50b0030200301542c1c0e00180d407009610010400010340d4400b030542111100c01000d400300c0e41400c0c206808542607030000a01d075030303030030754040f400302 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 289756951 1250 289755701 289755703
    0x9060705010209030a0c15031b0302030402060c033603070e090312010b0904061a07120509060a110106080102160f24021c02070f0303090206040b07050303060f10051b0a0b0403050c 79
    0xb41c80b0707911f50300b030030002850703040b04242c0c074400001c90040606a0101c005030640d00c4180c03c590b8001012000d6982da512400003101306141e04410420001c40d506410300315a1450506c2d140c9144401001003182d1880d1514035030440780000c0107a603280c081808125900d0f81078050a6010701030182c01140c40740238000c14001141e003d544040208640781b4080a245904074044541b120381200d200c004140903c40709032100e110741409240c000400042103000c6680c0865482c00e0844140001d002c21503940d085203090380101c60003c012401c0c5101901d001030b0010361056069482510010305440e21605410301102c821032008600c503800299540304000d07550828124009000011420302e519510f590445140d4240014180344daa01c0352030b015595500152002440c140d2501c035981c00e503d1400a0f204d80040e44c01c0350185c0b203031a4150f052441c11040d0200c1861040e03860a082044040f00e5182810840d2280910342c00303041d10700004150035030710440c4240c0c06511100d0b500d9459030001 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 289758201 1250 289756951 289756979
    0x601090c050301060c260309100c030c020c060d0e0303090a1a010308040612060e07030c0e040501140d110d0602071b060504180216050705131109060705010209030a0c 73
    0x340c81082800c200510405402c1210201d18603000300c00720400052a880c6001001d1501d100d51010741d801204001c4d00c401d00144101d203000003114103101424121030150140c480030132009016801800c0d1488a50038100b0141c0310840c154180495107003410402c5134150b620540d4030b0351207908445003901c00d101e00394014001004910201040a62460307c0d41e685c103009a0250108109000c14112111a06504030802400440309281500d04086202038010035590500c00c01103551001807148514282c45454100d4841c610b9503509040c1403020045070b00040041120010000714080010741c480804080c0010b1003242b005030746400ba814065441c0a0b0448442411807800c075040c0000c0364000c040e1800c5440c4000c0000b04000385e03600359400784c010340701c019001100c2c504c1c501052000002c0d001c070403a0001d40d00c001c2100f100002c08015240c041d00c20306098002049001c4107401c11200034111217010310001800c0649040019040191031401641c2200e2442000c0c400044d01c650300c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 289759451 1250 289758201 289758221
    0x409021503041403090604030209090a0615052d0d02030a08030a020d11031608070201060506120106031512080d0f3b060402040b0d082215022517060109 67
    0xc60a100e50071000420920407808024001e1350f1608c00300d882f00c08108420046941d101c1b80501038200840142c1d900003400344141841a5100302c400021502c4001c2031000c1c61403070510031001c000480007403001141c0540c6080380c0611846010f0008590850059401000140d80159883c4458120300701a02c16030800000d000008000b4804003411444031605400c5032420308103c00d903103059081e401080c4542c17280c2d401038000200542101820300c0b909050300d0302e03900e080020840602200c9002e80c01801107000f006044103a81011400c1903020340100b082c007210106141d20300892003c16614010302e40c147c24200311002100e01c20b0090a03004158050308210881d5851040d0060f46e83ea41c0179102a0082c1da4400d810030300f541b07402000150240c0c00c0540e5075592074040455408040651010554900c00c85801050700180384d01c1c3d00d55140c8a82d0300918800e9200001c5a038005c9110180c084009540b000006000d07407201c0702e0628040c49100507010540c900071620007600c0200030 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 289760701 1250 289759451 289759453
    0x2061908010302210303071805040c0c020a0e06030d0c050106050604120210182106090c0603060b0a0f0e03010603060f020a0201111e0a0c0b2514090f04090215030414 73
    0x2d00813401c44c00016a075100d0080d1802c4425084984008801002182c202c50b070000c3c241320031451260340207820000d03060b200307a0b82455102c0d501d80b041291028140d801a43c950450151170f41c8091050f9460311016020b04000105951382d54001809580564000780326082e42191a400703501c3d0410096200e24201d082c07001c0d403400a808026400059405241401200894908c40c030000000398800d1085c0d00040402030070300c41d0b0404d11441d4207580b02d9030000905020001c83c00140320800d075113501c01e9507110a1800480c1c075a050341c1100d12442c03680c0d0507659480f4000085130381d5000b0400c00754680e800060352032824100007802e41c0c604074280300503908c04000c00c1104403508011280103603054610140c5804c0d40041c1242c00b8070110310090982104071080c00718030b41c2020b510586981e204114102d02003007105090b14400a01600d0800740c14003405024080e06010b0003081c20b04000800004e860b07502580040c84034024a0803030382c0350413000300c1008100203e140585694101c810 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 289761951 1250 289760701 289760749
    0x501030b04021207152102030c1905040503030909040515010b040f09063006050a0c080703090f110307120b010f0609080c150f071203050a020c060c030402061908010302 74
    0x1c5c90074a151505010504100f041c0709490380a4028401041808044100b5056549041042503011103400c0f101449125058607002001c4050140c400c482c1190700180c065800d000c0040c080215181c0e0042090b211030150661401003001c0c0d0400c61406030046d90320707054643c0d060940d0428100d11540152500600e4240d041c000010003442072000d00c00d864105040c10341504682c1000c40b00101c1008180c2c1d810481446400c0c13110350485030000706981d45038002540c400504409a82e150b00010303103809a08242400440c1d5042c240d408803880240850300d042d6a604c40d03451907561201400e8841c04100b40040c400c0040c1000c03254010b020510340300a20501381564588c44400d505945031040250b000a11140c0400c003060381d107140040c0700015158440d60600c009060f02c6010f1004c0001d25120004907840094825922468107003002024141c1d249031490019500c00782007a0380c040c0c0300b8071524501411514030454030806582c0c07140129403541c41409821014144181144000e40c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 289763201 1250 289761951 289761959
    0x1008010c031406030a0b061e100f030b060a05070210030e03120907060e060316090f2304050112030507050a0212150a020a080f060112020a0e21120318010501030b04021207 75
    0x52081034200700c023110f0000000101c20b1280f40c40c01070050f0b245400a201000651040da0000300060085449880a1242d25110310811000c0e01caa284114041141409828050f090a891990f502d154500300003030148100558680380d034002050401ca280d034550300b00a41a80180302000013044c6500f05101f13018124400a25a40002401c2c040061041c607895100644201ea0f44801803211210000507540c80b2100d0825110140c0b103a08840400480a00064103051080c24122040051515005455950201d400c0d0340505e00590315803085401c10009a61000100c0d5000c09c0840c001f0a0b003021611040c0c0e00501e401007903010901c0c4140305140ba040d812106030f41d40310260100142c0c181c0d0b034100050f40c45008000d10421403070b02c040380611020760801050010104202c8059003010421002051032240020032507030300d44c001c880c41200941000b0040c540081c0a0340c2c2902d0b803265014000c2d0b0840d00243d1017651a01202428001907003000b64078418580c0c00700c40680070301824 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 289764451 1250 289763201 289763213
    0x3180c0a21030212041d06010f1b08070206030c04150c050c0f120601090b01140c0d030902060c010c030f05091614130e01050106090b0715051008010c031406030a 71
    0x540d010341d48a508aa048041058428001031064654812065454a803160a10308440d07040350100a000e031107040101d50258028880c2501c045450341d5100725a40030710318640201801c01e0b034200d0300394909010000059440002440c481e00404036065101d614104404c01c0b0a1000d10a12081c030a441c0004130201d0740200710704907900310640780f2140348644040031640e05a00b4402041da580203d2001040c0c40403160401500715001f40d030384511b4181804540074035885141c100781b410394040000b04415602940001094030b000500042c281140d15050600b590118002c0300c00280d80c4880580034001c0e41c0c403070f040e00048000010107150405881000b02400980204144c030010300083c9100399540c5c102141032100d000c42c00b8041c0b01e2a401825000c0d00080c0a2200400c00c9900003140002200d41526140d980145c00f65000d6140c142d102001000c004c0d00c07508900d20144d00105503076a09008a014100007550f0001d0485540c4240c5001d10001030210f0348603402030441c48020800d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 289765701 1250 289764451 289764479
    0x301030807170d050f0a060f08031b010b060c0a020a061704020f03030c0f06010e0c032503110a020607090801020306010f1407060c080702120405090a020c0a060203180c0a 75
    0x40e1101e14048014038242c2c5051642c0100040907112504041c100210306246401d0540540d40411050040079101c2605405050380c1d80a0180540e005000301e002e4128001d1307002114042020002902c0c1100c0300105d134946e40700c4c1580c140a07034003004a28085041640520004013100d141980d403d4880f494200781980c00500080c9c404c0c0b03245000500540c0c0c051003141ca09151000803a101c500c08010004d454560900c54a685001d00ba0700261081c01d940b021284135402d15500b100540e45508a4034550384901410481011364418043c49109003110091504680f00d4000b02070900e46130030020140c81f140d400c500107990050082c00000c0e6040050003880e1600b60a020705540720480ca0742080d4000c491010b4542e500303107207041001e5604040700900580030740d403e03200040c410310b0359403420b03100700d1152580001c104c0000030790b14452580600b9100782d00b4426590038241a444443c1070f03810980e41c4403400c0700d0742400359140d070400308040d244d041401e440d41840245040005207040c9 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 289766951 1250 289765701 289765703
    0x40302011115090a0303050a1a01110c04050703290f0f010513060801080d020106120f14070e01090609050405030a0513080703030807030c02010923010b04180c06050301030807 77
    0x2828100049090300c14424200c0c40c1e8182e00031200a403400003403456498400403c00e078042450003000c260803a0303980c050403066140404912413403c410000454242c00d6112090f403050094128110403039449000c4c2d140104440d5402140b6004c543d401292a0290014054066254846071010745e0300e031401c0c2c0746000325040700c020351020120340040e9140e1084d055032080e4030f0740e02c4c400810a1608a440306050316456800c40e004005044020b0307003216407500510030903100301001e0100164600d248040d9807071149001501c10a010040325240040980042c4400303110100144040c3c4a50711441c0024010000240540c0c106074403908d0701d0344900364981c001c01800080740c074102d0103800d401c9801401000c0803034034417a940382001042c640c0141d803c900064100080400d4403441409102c401c290803c00e50024401c100300141e5075032481e4001c07520b441d503c82400d000d190b03031107108080412040c0d805449402ea000d00e494803090002e50000e200b8880140011700100780f59100350741d155 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 289768201 1250 289766951 289766957
    0x108070513031502090a0807031a010e160507080304140c030109110d050a0b071d0f011d040608120403020909030a0207120503090405010603020c33060f100c0309120804030201 77
    0x101d641c80003c80082d00c00c4c459810340180005800003404200066000c00316802000b4641d0b03445800e00341c841c581142032042007504030f6904045880c4500078a500112017946c0e040080c94501c259448074441d4208036401d4910b90203203441103605260610400da0341e01011002044254001d94407040a0148254214000c401190040b8100b160400c1002a00c640000180c0304514000800804100042807070740034240e41078120440600707006010a45c1c079181615022454060b201300290503800f800c003966407040d2680f00000350070718240f0000f851480a0f10042d1b039107030304500610401c040c2c0544107800c5a401040440390f4649d001c00c42c0c1c0181d55030028080200d100d942401482d40c0600481d0a90140c6010000035030a501a401000c407001000c058070702000700100c40e01e40500c000d12500044403240010900f0a0360741141b907561192000384440304d803840742c0c00420162030307000006c01d0202d180d890100b001e2581042844004118440140e541c0421554402d43d241c000e600c070003418 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 289769451 1250 289768201 289768223
    0x1b170c031c020d0e03102d060b040e04020a030b0907081e150405012405030c01080106271d0f010e09030703031109031c1206121b15080402010807051303 67
    0x20301e980c140202506542c0c080002e00c100600c100102e55065484007d403507091448103102e17220308503680690b00c221894441c2690901b460206c00384504c0200030401c80c1d002208a10120004d50b004000e640982d80400080c090a4248201e15282400740030000c2000c21401006d0030340d20000040c0100c0e41440d1040c0800c10b51201d01d003290150a805c0b00080d0758210101c06100c000c07900b10b020404403a002c0701190982c081c0300c00199180e0000b0f00814000441108030900c13880d00c1d40082140d000c040406182c41c0c19500c4d030425080940e131103907880c003005074101408040068100c0c01400341a40c00e2130324040d8241801000d54900c40c0300401002d254590003a000c419102c04213031412940301400b40d421103a0051300b1a1b40100b805610440422001c80a100c03150119110344410703140b0f02c10b030b40b5682d100c40b901c0321800442d050700301e80b0780300405450200d1b080904042c02600c0251545800c55282003910015042c0b46004045130b041280910080110031403004a0380102d03900040101c5ca = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 289770701 1250 289769451 289769477
    0x2162d080a0f02240f06010c05060a020a0c140106030215160201210e060907060302090604092706061811030a0902030c0316150f0c1b170c031c020d 65
    0x10a01c0845558251800c030088060401c400c4c04e000c07054072074045810307441900e9840c40015100300540e4200500f055210000048842c0f0b400e500031300400d041410000c201c00a0b640c0c9010191030303d01c80c201c0071651200030800c00c60400e01940b5101025081c64681082b2001001d00e82000300301a019040003400c1c490301c4650031100c008a900c04c0c0c400103040c007000300304040407950f43d1800d550707042d801d214080c00064a60303ca403003680c500346402454545400d1030140310402804c2549403821803c0742071084070703041c140f02907e0008900c1c890b000119a81c3d1500811166059500e58031040f4a41009844419180c81004503544a82040c070001666100d50011a161000840a0f59054820900103100d5000c10b01519070031036960841d06040d42010000407201c2c80d614801d0500841c3d60b0203803540002d03058410702d006000b10003c2e40312445a45005043d00c00c1e1081c00c107e0010b070002c690f00d201904090000300c403500114011032400e1145800000d541d541740200c00c1042180c03c03207a4034 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 289771951 1250 289770701 289770703
    0x70b0a06050607050312152206150f1205100e13050601080c09010503010b0603011a1c02040603361e050105071106010303090e0a02162d080a0f02 64
    0x4000742501030301140d00d51882c0d240c03090b600c0c0c1c041c5c103025003d034a030900007485840c1351a9000100d044040d040e000340340244003101d411440030165032954181c42d1200498030803920700c920315640b9016a1001c00c2d444e440c08010f018207420300d06001e0540d05040c1082814001c09580c1411915004504800703969030320340e078070304040c0c0f84000108180075540001406020019070180120b404076039400b51340e43e031841098200c490240d20079420120a10041084c3d10030b17038202042000c121440c5c40d1a010b01c80452102151107010340c00c10b019804141403015503450f00c59503880c028218000d15591001c5c2201019036295201c5400d400084484d60b02c08021260800c1d983c0401101070300d600110483c03810f08c1c040d200803101c03900068034404458880ca500000d4090480741c041d140c100005040014040042a008107419140b039000c0220001c400001c07602180c42034000d02045204101190803054001070000d10b004894029440640c08196800201c50596605061418a00256010617 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 289773201 1250 289771951 289771961
    0x1120309140d05060907170a0b01051c0c030b101d01090c110709050114010c15090c05031e06010f0303120f110f030105040501060c050c0d020105090a0902270303070b0a 74
    0x400c60b0040c50140701012178001005c0e02580d01031115100d1f20800405004c1d80c4010302c02024050094400040065042051100720001c840100e40180e208040e1100304007900c140d8421900480c81100b0040c010400c2d903522005071403401401c550158481981030007001e81030242c0141e035640c400c40b070754005003d81c1024040d40401360654030519994072920006041c02d00c51103c80c000007824140003988680600c140b42680540d4402000b40c00403100401402e00c02d0701141c444e4060880402c00c1c2d6010480c0440c600b9084000c0c40c0100031001c680307170800360180d00c6890000f481a4003400020342118005034502c0c9100d8000480a00400980303000d00703010403100581600c00035580002000e00380095061b544152401c0c05940d0ba164021a11904004409849a046000205400d103040400100710900514059080500400001da41d2002551021110741e50001e543e4645004d052104c84c020005824440301040d80c0c032001c00d40341c3c81070715001014400b604000510003100c9600ca = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 289774451 1250 289773201 289773203
    0xd050d111c030b0307050604060801061206090e1b030d090504021809161812020904051e07080708240a0f1401030510050108120a1106040507030b01120309140d 70
    0x607103581452800340041111103d8603020340142007011a0f1424007408503000c0782d40a6407030302c5150f807800008440031403014a2a0b01810784034103000400348041e008100c1e0003181c48020300414103030000860400346c8030205c081c2c001d810205c00a80c0c0c0b0b0b41c20904d0700c0308440c4284c0b80941e440851083c2c0403110003261881c5603106107401c041c0300b0300f81400500d80c0c2519200e44c5414582c24080c00c0c4201168141d0b00ca0a4500d00c10b17000e840006042480700e254003e4892000c41d181004a640408501d2031449a10750841d4044079040102440400c141d500401401000d040c000560000c0001d4010300103078581c00e48a10b036030214020b00556440805c0440c0750210400140030042c003243c1e240c0c2e03c21321040e1307058070500400620414062003124101c6040c030b0300400c0321950030984161300c0c2e0802104201886884a5400d00501c01441181e1003184030b040a040864114034001c140c28006030000c25100704107100c21000650041007003030903030781001d511000c00080800080c5a051780480 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 289775701 1250 289774451 289774483
    0x30f180e010e090708060c040611010902030d0e0307060801031205030402150324010f09090c0201092004143112030b0103050a110403020d0309050901060c050c0d050d11 74
    0x10140c1440320a140154100c0064071130320b554501c0844d507aa5020f84d22106000e808002c00c00443d405550041100e8415500114010a068000130b040484107000350000c40c1c0398800d0b43c0d015140922661001e4140750500c1c1d01d5a505544406103800f00107800003080c00b4002021400b03643c0c0c4c407007030383d5051003034095602d03913900e02200981040c11516440b800c200070350b080c030f20030203601600524582d50f4181e40e80480c21413078628224054040182c24a00f50f5682d000d0034804203040c4c04010000d0111003807607000402215080c0300440710304008e2107004445d0a4107225040d41c81c03900b0740c107141810422140196813242c4661505d4614550010700c002c1d88906c1100e14950190440e41c00240240c80400035680c900d68500c040c0c0c0d030b01d403421300c840303200400c07007440189030009074405c6040c007914010401c107840d00c0100e00408401c3c2c000703001141c14030340848208401000740782991701003038851390074030703160741e580c40399120000303d00003044c010900d0501c005000104840058401e01071 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 289776951 1250 289775701 289775729
    0x80c03040f120509031006030f2a060302190c0317040201120906050a0509031c240b03091213090c030905010c0c0c090203070e130b030a080d1503030f18 67
    0x100c4050070030744c4030b002e040340240291405001c52100f40d101e02c40481b500710f840b900c2140701550302e480711840280c1194400c0c123034000c1d00900c0700107c00001d001503c410b4070010780c2c46824400500e41c030030f020039a220420414021100000b50710521180180c03040d40000c081c0342d1154401660b2080740d601551540e02d1900070000c06000c07103a00b00c280256018041000302e41c48084020380c0360f100c1e422050040032849000071404080e00d03804006c120b030b61054180c00034401c00d0300b03880d40d240d020390040c00070354408820b0000e10007040c000d21008030140074000785040c000c071703100c0c06000140d032203081c0c4825903075010848103601980000350110780c000004c00008104000241c0f6807007009100740c0d48003041c454049030f0a00d092084074060391185e02c034105c0c0d9021010410011030070f00e4a103d01c0803601c50b805901d0540f0200075042110344984505034861040c4400d4104580c6d102d00300d40c1c410011220f0800210b60445441a4040440d10700320f0001d038038569210302c1900d1142e1101c018080c0e80 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 289778201 1250 289776951 289776983
    0x1317030d09031e020601032d0b01060206190504031407020607060609020301080c06030c0412140703030e011e080105090a18050307030818072603030f15040903080c03040f 75
    0x141c3d0348103045802e4004041c100b01c19802c030380c3c40ca070034000204800c111210082c4200e070207400d901c2c0801669401414022210b41c1c46003800c1f8400e900a80c05030f84203001b4445013540c21200d10000d103041e584200950f140c01d880007802d1480d451459400c00b1000504d80040d5110303041240c801c80e400401c24400103a80d082918003d40c030074881d82c205405150895a400d1401000301c9014600d0040e07030b0b03401c1c00c1c1000c40a00035000c040100b00c40e080544076410070300300340c14041900154040c0d00d070f0a200d0280c98001520741c280301c1100c5502c110410031201074082c0c0150010703054030404e0341d010203560354840c1d4440090003070b0041d860921101c3c00508003001000001080d46a11965500e140b54507585042400d030041802020795581100c2024421030f5a21040d0803181503003c0100c031070210360040c03110b045a0003601d0890310f40c0d0f00b000c20844129107800388a080c020040d10b040080d040c44d6140101000e10241c0081c42d6100e0000205041c0010071300c1c0c9580294001e410700c02d05583d5 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 289779451 1250 289778201 289778207
    0x50301050420010c020604211202010204030b0f010510031d0a0c03060b0103060308031b09100e010e0102030f0a03020919080d0905030a0b0a020d200901030f021317030d0903 76
    0x2d5460707098001c2840444000e55541300d154611805a8040c007003070309050401c900c0790041d00c0d6121490031020010189400400e11180c1042041e62841e000141e40f00e040d802d0107001d41e00d00500c8140c0280b01e5000401560311801e0840a0344c4c28607280000b0f109520344000fa20510300411110100d1140818410074803080d412043c1c00c481c4036000402055903030000540a5402e20720014292001c03c0c40000d00c1e0200030448004c154517141d040f5031501080d030b00011039420314161550f0010b09041c0e00d002441d6001016490341d010240021406c1152105040c2d580d88150840282010340115103242d03192121a540000000c0c003d562045044c0c036000300c4d44d515849003155100040800c0c40000742070402041216800c0e030040d24040351a500c4803c4000a0350081c04003000140d600c0d00540c5014101840601883c03401514a82d03442d46031200040544004140410035a4410841040bd204400801d00c04844103840d443c00000101c003402070a6004145480607250f00f8071650b2810164 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 289780701 1250 289779451 289779473
    0x60e0a05071d0f01061b03020307020402030406020909061207050f0109050402030c1207170106051c1b0314130b071202030906100815190213140f0913060203040c0503010504 76
    0x410782c0414090303035440030b402c0304102d4284105408901080c80190b1024000441228554000d004880c5080c040b940841c00b07d0380220340681c1c020b0b82c0850b60b951b0130700e41020700c0ba030030040c200c44151407280740100c041e803515481d203d820b20038010041e20000c603900514419004000041085480b481c0200d072016555010031910340b01e900e05100091001030040c840c03d10445007903100140d49a00b02502518640c1c01103903140c03440302c1ca00c1e1141000440030301907405030002d004201c0800c1011020060b094400000e50355504240390700030803d2140000319101d0b007558029039000541d071598281900d030282c440b0381c2c03209202d00002c01c00250100000340640580c5a03001c00f281400c0e41c6e0314401c0c0d1100b0140e0110b0f41d0105902c1c001c1503a2003030501000702c2101c01381500618054001380007032800308061303120180c0200516070240482c41c1c10042c1034441e480c143da0001d05840c0c20300380030354001070560006180a07400300201d003d002d5070700002409008007400030071480c2030070300340108040 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 289781951 1250 289780701 289780739
    0xd0c0312020303070c060b15270a050904080d0e07060305011a03070e09090f030d0501091506081602031318050907050f060c03070606030311121204060e0a0507 70
    0x400241504800603100004a92080f852030751540b40c0000305d5525080a4034541200c81e6100300001804000c1c0034802004000750014020240c04c8124100a424152101107078031910400d4510b2040026481da006883d90060748894000d50701d034a90300300d610003403001c0001d82c8d0b118410980c0200e40300303802d940000c4c165507000c04100004000200c0c01c100d43e1100311802000120003520a41c600d05000400c107422108040984188041c0103281350302d190059a24400c03a581c4910042044481d984203038405010313511012600320b418200041c0c405200a030803038206c809642c0108500b00d20a00a6840b815049000d102c141a510b0440c0318040400c0c020712a8940d1803c000325a800900080c9007048440142040d0b40794400c4004201194003c80e5000d882404104100310025001e48911000343d0300c6a00c40c40da5a01400e450b41d49000300010030071419a001b0805510300d04440d070a00f5902561046005c1070440b200107426050000260f4001d1451060401c041580b030034810007040d501c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 289783201 1250 289781951 289781963
    0x8010509010c0f08090a021f09090209030703020d0c05090a1a0108010e070e060436060305030d09150515040c02062a2506050c03060a15020a020d0c03 66
    0x2a803594101242212a441d040b1804249607030454001039001d0503140d82d00201c0082070720104d0b481034000c596900220103444000c09a5140360465942c0c02060340c2d409032003104801c5003420122008a560303002d142c0406072003a140d811800c0c04000c407609408000d008082d0450441741802d01014020301414507141c00080c0c499036000040354070642089048903042082078005444140c01500c0c50003c40510a40040e000c01000c076400c00704508101c4c0800121200905004001500c054503518040403070400b141807140800201c0c0000065640c4d04600850001741407880e884d001d200b00b80181d13484030403182458108185915000c02d0303060b0034202a2028021207890090407030311040b044919004488034041250f14200f800148841400e0440c240180b402400341c1066100e810554403001030280c01c00b000000300001d03030003002e4201d64043d6080d419403d00000003446c1a10902a00e0481899030032070280310b51007000900d00c4560041c1800461642e0340c10a000302d00d029000660f10 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 289784451 1250 289783201 289783211
    0xf0618060204080703060506061216050d020c0703140d0206010e060604170106050405010b0a0c060e0106050d0b090115050f0f010306180b0f010503040b0a020d140f0702160503030405010c060f05010b040801 90
    0x107030402d2001c507112032010700c42c0210544d2f120607440c007410b4564980e100070013100f0311010304410300300e200500d0081800d000500d00e40b80b071451b182c0c00c1c0c3c81d030001c81d01490386c00588001003866000074801c3d05607035400910846640d40c50021840501480c1d10500c1c0e0016200100c146a4806600043c140c03a410366041c045c5a80745c01c1001c140f0b1168248250010344000980b00104100380d02024100b40c10340c0002c506d00b07130b035400010042c50000c1e1080d074016900318240060520240f0401190311881c0b904114040d14103070002c1c50f51003940c54068010310307943c0d540785100e0313210340c1c0b10790b018010030581c0f1111207102c60307071182c01031400d03a00503401090305c45440303030701d6601442c203a030b11032540040c4075410740d40c5043c039100203500403000d40040561241d441060141c40005064412884417980354a03500e0641c000270300d0005005041e80c0b0380707070460005100c6a01c008c000c0314103a42c028201103065641d545880c9008040d8100317100d4915103400d0001c00d40e04101c01c02481200e0384a0005e00c030f = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 289785701 1250 289784451 289784461
    0xa030e06120f270d05030a0e070f061814010c060e0f030a17060a051309120e040516080a1e09030201060f082a060d05040b01051504030f06180602040807030605 70
    0xb02040e41200d26068940c46183e0803610148100011039000036811000b02d04014141c828914040d515001103001400c500ac003800341584c8925140315010ba0724031000300c80c1c1e15040300020f14000e680081410418404403c3c014000c5a410801c0700c2641c0204440c802002d00425030b8a036005003400000281700c180800d4010b0310f07000380349809090f0050860003c0b41c9801d0800151340e04070a45203000a885101a101140f0710a5204ea2081f40a80301e81d10724101800802049820042002d450030050350820340ca135607803002c0c0440d0711140c69540061180c544184d6981c03241c4071a0b60b8113003258246001c00c7c04150b030640000089810418140700316a80b0fa00400c3d0702c0d5000c00040e400c0320350762204400c0c1000d110340710070320b804c03a4090112450126180a20826201c086509641617510580100410b0a050035001d994008001c82c0034182070450380c40c40d1034068041c038042d040310b40342d5500c4c904405240d03034401d81d05503000d81300b15501d540d0340601540b078820714407003a282a450500021 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 289786951 1250 289785701 289785751
    0x1150302030412030905150408040303090b0c06040201050315030609150709080309010e180a0e0c03030a0503161103070f05192406180617010b030a030e06120f 70
    0x3a005643c031007079580e00d40410b00c074110b00600c2000c1c02905d0318803a8511a00384a031181d444180514020400507a0712070460501411007216035101081b000000c0004000700c2d0780c0440c0c0641c0055092030301582d03a44801032aa02850f80a110840d41800781409011b1403240010b08042c3d0401016602d61180d40c99050589405006215910154108120b40302071036214101c0c16006000042c04640074042c010100b02d0643c0702201c00311a210f6803101c0c0004490070401150102e01c40441c002c5147c012030b560003d200b400b01400c0041c1100c4049070310070031180101c0425460341c00e541d04407501e400d01c508002e00301c42070300603060f58030340640e03609042c1d40820024403100701c2c0e810801d001420480d20007580440400c00c141c01c41c020355642c601040303842e0380c2860450100c0c0c2113580030400301d0501e4180380d00c0000b50090f48005030724142c02400291004240e240c1d800303401d428030203800c1031010003041c6944a680c01c400069506a01040030702070000071064054000030a080290403074500e811 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 289788201 1250 289786951 289786957
    0x3060c031b0503040206040905090604020a080c0d03030b040603050a0f030e04060e0f040c050a060513050a0e061504051005190e0105250c03050a030f030203040c03120302070209040b01150302 84
    0x4510003145480407244a10b019000464010348050052807500c0c0e50780402c00102c070819103000d8038070b4000106100542c50500100c20252504801401c1c10494440001d0100e0741000d0000301416240e03800010a655154800c00003180c001040d9400448540f814000000d5042811008030f03100e01403400703142c02c081c4289000c3d10714501502065131280380d881600c00b80d00a200b194048151300010440307840d80d851400c010070700ca854a584034a51008aa00400c459821141c000d0788102c1c7c041203c0c940007005a9040702c1d06036042001007c0f00300441c84540320315004990011740c04104103440300d0b48000141022508051040e4008800d140300b15481c1c000c0d8104180040c00130f201e8442490703500307403850b000019000e0704d4101e00c04031642c410342c2d900c1e0f00d13600983d003a07000106800c0c241500305048810405503407601f10310314501550780c00c03020b40103804081c00c03441a8070000c4044500a82c125003100d070f0000c000c02c0c1079160520301800600c070b090058080f8000c0031a6040c19407406030080d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 289789451 1250 289788201 289788221
    0x1061703040b070609050c03150603120906092101061d0106260702011d1e0604050703060c17100503011b0c0b0912040b0c07050a0b071218080703060c03 67
    0x42d14a000c0880e122940a000036882c20340e4240a101c4c1c142c02075076410403002c900d0f0105051709c54100e04d810810541007a40d01c0d2820000c407041088408515583e2004a9078013041c1100c1951700c40041c0d522040400c0700314415800c41c0c2d86080300101d07003214a089024400b0481d03a4403450182e88601044a5070ba0700038014221454035200341c0c40c00124070b030102ea40d101c1e040b032000203000b0301250300c0d1724441141c126a00030540c020f50000c10111142c101c640d946001814010a0b0341d041640d6040e035070394051310000d80169501d02d00d20b54014401c070704201580242004035800c904001c0d003044040340036881000d21035860480044080d4810f021118081040390b101d21020150396110031341400c500601001103406200d02030404881c011000c0c0000d4141c0000103611480c81c20f480b24585111900004d02c1104085020458403400e041201c2000e5030000c3d02c00005c1150322000d454008088280c010b40407100c81c00800c4030b90001030b2a10440780103200034022501d04103001e904890400c62 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 289790701 1250 289789451 289789469
    0x30804060c2d1511040608091005010812030a0f0908130f2306041d01030b070c020d03050a030b041b030b040605060a0c03020a05030a031a0118092004080106170304 72
    0x1900110303141d9192580c0c3c0182078080030840fa614030900c0c0005034001e41000011590304814807c0e5440204070a25517148492001c01a03135041c04074130fa0352680b960a00902e40c4800000040c040e242ca40c100c2c1d41c1341881b8401c02d00c2529010319200c03940c6c0d0808500105140c0094600140d650192103180044440c0d0043c1500103003118820001544241e074051034100d101000002180c181120041d072002031340f084240e540354198a0705a84406015007403074104001d95000c4809a940e05507a2143c065260400c01d5480803041001e5000e48440705625074410325045804294900e54504000c0c050442d940c00c00002242e0b00802c4115691402619003080e8180700380782000c0e00542da07141c1d0007030280c0116005c041c40d5a94140ca0740c0c1c060300081002a864100c0220380040a48441100135404d0078141d8060f00c0c08103a0400c219100c1c031521680e01d8580c920300c080e20009004548592031800c1c406030b0380b41d0729803951030301a10941c0714180c0400c10061180d410240e012058406442c031100c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 289791951 1250 289790701 289790783
    0x301052809020f03150f07030603050d050309012a12061a0f04030807060c090e19110409020309031206150a030506011214010e0a090201020c100207030804060c 70
    0x126008000305a5900c04030303080001055103e400340ea08009428043c00003c1d006021032800e078101007110000641403000389410083c0500c0010004100b11190489600e0038944a51382d0316805400750550640351040001d458101008040d0303420036482c11090b458440c00024500e00ca0408121110741c03050407011845903810070011241c40008028440b110608a4100b584903150f82c546036011000c02c40c2c0741030fa40c4031300d01c10054001d000b0100900e00114412030600c6c00c40403804103500420b10302400c0e80e5860103890f451800d114192000340051510440d144d20b800c4000340d980b503106416001c0c104516900007111890042c40c600403050300e25500724284044508240c000c1c10002d01801c1c18490f484860003070b4270b181da104d65612210050040e55541d4034081c80c4144540000e401ca0300d1103403d244901c0d01507600066840e15482040d03404240ea00c0201d1403ca0502c48203805c014100c4100003400210f42d60f12240403400320b0300440c800380f5009245113002150b140c0140b86060740710001 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 289793201 1250 289791951 289792021
    0xc030e1924062408011a03040b09120c06090114090d140403120c0201030c050c03040e091203130b010807060906030c3f0504021507060f0606080105030105 68
    0x380840d40a00744803079011616584502c501c003000040380c9110240503032460324443c1440d9104014900401169800129441126240c0312041c0702c010400307082d21050f0400301d0041c0400704140161843d00c450065152100a40640c1e01e40f0b0080d58011507035030801019100c0301e402d12103154011440080188510000d030101510381c80e42d52a1180c01d02e94043c0000404074600c035a844407100140d40d03a820300711819100140849a100318244100803050004040c900800030844050301c1040c40c90440039901d5080d10b61914003e0070710001031400c0401032010404c0d441c0240342e0128451801d40003541e88888007079039a21118030690340001d1045070304000c0c480c005d6110442203000c034640b50500304c0c0403451001583e000c001d60640000180c1c0c0c07040007401c800003003004417190a04020702c00d2742010380000307210042c4816041007400000600d0820440190700c55550b0301c502010502c081951000068800030092050300d000c0e50030b00b000160f005c8110141044501aa5541c9000c10411 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 289794451 1250 289793201 289793243
    0x1240f0e070c1b03080d0510080c131d012306010203040608151011121908060a08070807060f0e0a14041e051803040803070204050a06090c030e19 64
    0x6000710030f4420459200c1a00300441a103030b0039402550040d1001c1d6038542c40314a0741070440d0402002031644640161003400300020204000c1258070084442082200c102100702004118003607204513180c007403030f011442c8541c040d000342450700b841e0308610401204d00c0c11940c00000040300c05c540103030400c0109000345409020f400d90010a1805048030120000c0e000c0394004550408180205126410a0f0880074040100b20000401e0703900b0700d42015204680107080d0440000a030042c00854000200300d41c9908080c0001400e034141200d81d03240c3c1d2070910a881c0d402e14041c4400080003242c0b00b183d868092490740882060145c00141c2c80c0d483e000b070109903030300303900c0066501c262901c08800b8000c80c038000b241c080a1140d100002c0e00d00300580010800b0514540c0401c15410a10082200e10004016520b86903015503002c11a07640d0310b0100740c010a00b40c1c02404440703103000030f02e14040c0c0e03140d0300884000103031a0484016209200d48001001031301c81c0010305040300300c0214201100 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 289795701 1250 289794451 289794467
    0xe030304060801210f060e0610030b010e1f060503070e09090d0c1110021f0903080114011403070c0201110c0d03050c0a021203030406050718060302070309030501240f0e07 75
    0x20000401281d0713242d03182e440c3c1115030f00380e50041c4c03000350b2542c02541d13802030f0070303c415500020594448229580b440e540d0840b80101489200c541c49860f4000a808040741ca4002444821094803409081c0c3c882901038607503002503078000300082410300e10402a00309203095900500c000b070000c2030b1545618008070b6030000c03a8001203ca5004004040e02d4030388400c0c0d126040000c132038001d840910304101c0800c20010b40031065030354503404d0a07902c00109030446152415950000040d03061200700c1c0f40107845181c00c20341c000044400c00010405003a5000d540380707030914400d03030f03445100c580e40c48141130f6601082094a80c2c0020174004410010380508010800c1d03d01c0f0f00c068490100f0284c0015250300140451022140c0000080104100c400e219240e03000549042c5510041007030f00c80b10444078128012881070550014501003494040d402007402503174018024805000b16010411480d403000e40c0c8144451841c403000706202108102d80030955510020480155554208c1125400c2c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 289796951 1250 289795701 289795739
    0x30f0b2809020c01020c0f03071a040c0506040b04140103060602060c0a1107030b04050f1c0e120d03020d111806030613090803042a1a0c01090609030e030304060801 72
    0x4004010014101c0c00740e0001d0440384000c000010388840c0948200c03810110142900302668008000c039200107442a02d411582c0b850144100d00c4079540c1c5d140029030a101a0003440e8004408600082d00702d0b00c040c010701c00d56941080303860903940c1c034800640030340307003940602d4000d6000740001928030030120000c1c0411074000d140c04058410070000c100d0030100e468000751007074030f03090741000140142042188251199403008040750a409c66480b003600b6802e101590070096100b40302402551003012411481a4000a580d80050020000340c002e5100401d50401c2030f01b01441e0502c4a80c285040c3c2d900c3c6110480700071101010003003080031603400108070a5000068012140b000c541c14403c44c0700240c0308030121b0b5503e0170941071201070359084100d0300c5d10958100c00e41e0300e0800b1804410034211481d5442c645100b5206007689c501c5070140ca60601c0d11980303041170200c24040300b81c11413a0301c58000c1d103864000030010303002e064591290317001e582d002c00c80000042201c0c07814950480006 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 289798201 1250 289796951 289797019
    0xf10091502011508060901060e01080a02130f0c17070203130e0c0403080301080105150901140d110d0320030a0f0c020d081206042913060b0a0807030f0b 67
    0x843c02c41c201c03079010702d640c2c1c1c10070600c030383c0301c070040002d161024070403e8054035803c00c900c0c2c0c29601d05900d56945c3c0550400c02801400c03062280002d0702c103a50808024505140d2007407180c8030b4a030328001c01c080d134081500462030400c0c10204d01494004011240c2441003074040300700322418900c0400d0801006000c0282000040200002240316039001d90302070650040089082d040c01c0e1a06e510304241d06004500c1083c0490042210032051100e880010343c0a0b80c0354012a041c4d4241007001d42d043c8403009400070500081b00041503403000003104c02035a50400f01c520100d001010541c3c0307001d9850210f0114081c00d11640300c460003008031100c41c920042c8112958025075035600002d4100c6007082c10345019800c14030640f40307401c5c000c850380c01d90044204038401c0c1310705035082c0c5208071441d6941c0c06544245110102100c11707400007009804601c00c096504c4866900080c9200011100c010010b442c1009031540300d100c80c040c50b0001c0d24021300808130100000c1c040c00341d0fa01080c00170288 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 289799451 1250 289798201 289798211
    0x916080c07020d0c14031c1206030212010b03121201051c061b030c03090203030406030222032103060509010504020d0f05070216080a020607060903022503020f1009150201 75
    0x590342c581c10b0540440c858107084d8851480c0000c0350009090b05016288a50000c41e25028146000116100c003541545421065145405500e42c02040303540c101a41212202260b40841481504403034080002a03003181c40391100000c82075440e0042d01041c070f079041009401001030f8a00224015080d007481130410204500680d01c0c03004858031102ca41c10f848078240201d20245806100d500c00240329070900b0302c01e0400c250f0000780c81744183d0144505041d4042050891000e8291108188400d04d101164049459003010400c3c03509035820440d00c0c64000001c03039509407290003000c04030382d00946900696420103007080007a420100303030098400d80d00d5150b00c4901c41e0038050240500e8140c2c014102640107003000400c98601504039210075440b0220701030040c0c9070003080741e9005400c854001810201446c0480c10036030100041040000075450300392082000000300402c5078800c98040000368a10b03c00e1000c092110030500c40821941c400410603003d810003200c0c9100301c0d85c800064 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 289800701 1250 289799451 289799453
    0x80108060c0906220626180c09040807020901051207030f2f03060717011203050f0a080126060403030507091a18030708031b0712060203060406050916080c07 69
    0x4820804e030301d42d030900c000b00f030200b024582141d213070344070240500320741d0038035503d4102441242d180180c46040c140c034408069181c140c0080c002d4055561005000d1341403420241000c55003034025060a91198400f0310000882c2c0c502a107500f801003413a6400740c0000c17869600e5580700b0301e2107000e0a5885407036458560741c5507030452030100c0c140402a88845a0140c44105040c50312200601c10402d200b00342001d01400000741c07c04d1411a1900807603030015403c0c1d45812a1a030041d1010800080000310311700a5080e0040c0c0b04505861401900010b000c880d01e50440404031a0083c45c2e506070484400300c0c020034844d82080c1d84c00340322414400340099075955001c086607000350541c0c0b000e51000c80e0308140500f4048520904200441c0144031217401c0140c6103489100e24078092000b01ca4003141c0415200003401507600a18110740821104066421b204010794011074070b180c0714130302e401c0c004942443e10590840c010078070440c41300d407071080c041c1040d2a1101d014041035441d9409000c200 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 289801951 1250 289800701 289800727
    0x90302060304030305040b060108070c020603041406011503140408041202123f0405060a27060f0906050415020a1403070c1514090103091401021306080108060c0906 72
    0x14020b903c240e9002a4a16150a0107070340c04002a02d0141013080401c04c0c4030b9a40d500494003000d0980485083e0b41d243c403149485042d00200054221250007a80e00001e0108a403e10407111a803c1d500d0a010040da45000455203000440d801824084240b10a2040302103540880810a10281108508081c000d881e00c0c601070342d0085081c10a41004000301c1c14060003044180400c0314078105401c0c00e85d0030301441c0030360700407801190b00818020940c00b803068402c000c1c810301031800d0b10017a444000141c41d0050300b44054010346010840c06244d6400d054814900d09080350b8241d0b03940c0703007864148400f01401e94111200b00f0114400c80c007215003c100c84105901495000000031a03445590345000d094075a2640d0184090060b140300603070f02541c100d0300d001255600080c4050b65900c0c808010b8008100c5c2d0100940b56060880845120b40380c150300800c11520f040491a080950b5040e04450645007401030500300c1c3c000354041206460f522003d06500c40006010505149007a1401 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 289803201 1250 289801951 289801957
    0x30210021c03050c130f0906050303031009090f0605010806060915010c02040f0605060f22140603250c05010b0d11040b04110708120c16020906060d1505030c03011e050709030206 78
    0xa42d1999240041001f207210341d48079250040200364051400e40ca482c01c0022000d9402e841098100e90b03e401e400000c00641c90035181a80c2d178440801c03c56961142e84180e640c81d4200d034454010607040303010960000c9a180e4030104140160f480040307508285e801c2c0405004541c0800406c01d80f40d106c00308242e0340d0440a04038411701181e1440d200c079803130000004c7e0303058200090045500350010622001c8400c0b0000c401307940c0305071a03443da40d07102c8400b0700b4103032124004101c12600c0389200886c0074030b6100d5011004580290024007100780002c00b000144c002005000b4030000712483c500d00c0504081e0403209841400800015032503145450030340c042c0e03000d0b03e0100c4804a0001d03404c01a40105810300c0c1c0c0140048260328105069860051003501c500200a445104044005882a0750311310031038903402202c5034180304e1041d82103030b0328040b0801c80c0111407090058100203c1030b400c0510840e40101c4e24142e005441d0000101290010303d4050072234030410407500000700140c0c5410b001 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 289804451 1250 289803201 289803209
    0x308040204050f0f1b040837020112021e0307020109150c050901030510171e1207020f120f011d1c052520090c0301230a0e01030210021c03050c13 64
    0x1440d40130310f07109045002140c5610100c2c8111800008d94080983d80c00f00d03410140034181080140c1d07607451302580b10b030001c41420115030004c000008203c51a0340c1074100710900c1d07101e5000c10400c010f2a0140405881c401c1c00c1840006005101030381d07166100c0d4003c2c0b5042043d80c241d00001d182c6071270142403154050103204000e43c0c000340d4801c1c0d0084010b140c2e1003900c1c1200700076107001d400101e00f40c1c4e050711400d00064450049104006040e645454403607501042c1d180c05c8036154005000c056018101c0901c01e024808044440b129064001292a210800b20940184441ca007142c000307032265001407103024111a80d40141001d480803082c0c007040c01710f004454000541c0a4442d00219480602070907074001e086400c24450000f42e400c050301c1c1901d0920b1030100520800c2036440d0000c00d4081d03101c5038807441038003000580d00140081d150507a8026141a604c402c5c0c40e010503aa201030100d040c12960010b0740843c0d403124030070350106030481a0544002d18001007101516200201900 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 289805701 1250 289804451 289804483
    0x40c110d18080c0a090915090c05210a0308040309030b04030206101707030308070311040b03150105030c1206010905060a0305070e0406031a070c020d0308040204050f0f1b0408 77
    0x110080d100036a00108000a18800b0010000d101c0d6400104200d1051403040c0700c41503444200440070007510685c1d00c1e5070903900e510104080102400c1c0900740d14518401c0ea400341d01c6003108405260502158030314025484002000004181d070b03400c40e29003c1c014801d40400c03015600200005059038003060240703020340c0c010105e03400c1c95580c901c1d07522a6a0b00684401100406074031032480040340b907034201e80c0c140c102041c0c9903490b003009170003424283d02d88a4021000181c00b14032549484040c0d03000b5100d000c904000003403034200551712848290b60700300c4000e4042c0902001d80f40345a42083c2d10004c1803609400711691140483c8642d00074105c80c50210f6107803001c01804c640e0264009c0d10303850382143d00b48512132542d1200440c6915000700900007184200009070700b00d002e01d0a00c1c09555024100094000503401e00400c9003805039801c0303100b1410032021820502001007000e006548005103a84c15403076600000349005240b020410160030107010000b200d600c28170000701e9442e6610 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 289806951 1250 289805701 289805717
    0xc0f1b0b070209070c030c060903020f030c0a05010506010c02090a1a04020309010b0906030613060e07050a15120911010e1f09080c09100e13060207030306050f03010603030e040c110d 80
    0x40b041110441d0002c10510800c000104040b02283e40003201d505403d8100c000000c8007002400c00300e080104242c2c0120041c800020351500034080000d01c0c000c100d000710003c000c03036128240115140094210007030f6110380c58001180110a00c2e03032014625910384142a05131140f81c101180070b9800803601e1002507595282c99045030700340071016682c40740b012030240c8864500355690b6400c6d00c2c00080d0140031260340e242103c031b400504008035405000018406a40269921001c000c0180c080080303100280300c0242d01c520104090160aa03c0d5900002418006c0c00000044544030b5602d60540d0b440310b01180c081c0100e128052101080d6600c0d95103541d0716508100c0a03619040400c25103500403c0c2d140c0812a1004d40c10708488140d0340300110718009901c8900303410f80f043c0400207000c2c0502d840000c040d0209505030780b0440440b44141c8400c40124109000c1600f00c80c150f110140100704501c48011a0349080d9010060f402c41071b00b00510281d244022091811030038004140210304030f1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 289808201 1250 289806951 289806953
    0xb030706051b0a0302030a0c17030103060c1209030915021f15120c05040902010210050a0c030b030309150901030204030c0306020403030215011a090d0516030618030c0f1b0b07 77
    0x250b410042c482102d40208440c200c1581c0080d0349200e8020a0401c10000214440801c4082c000f220b49030850380e4407454803544c40e0b040c80e2008100b048014404502039013850f003910801c5018070744400707800d81c41d009606458004001c0f507061041d09900114000c2c8040c1d4070500e0000b1008240b5000c180f030000840114a00d4910080c05036600440e030000409001b480004046442c0d5100350749041d0b0380828080014401031f442c6c8075000305c5d61044107047c03404000710060700740d00081c20301c01140ea00f400408414424140c491290581041c2c0100c8000308055814912000030080c8c24818940149419503a03203d0704e4504285070000c480682d0002001c000345581008060003006582c64400801e514144203142c80d01040c00502060600c00b0271fa206203035860700c11000c2c40035000030540c0c04108203101d600200b03d841e8041100c01c0742c80c20109041d0301054007002085140d042d11141955015520342410840c0010002c030340b29400808030a211614040c090070061010034a501d84600d00e17 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 289809451 1250 289808201 289808227
    0x904050a0b040b0f22060b0a0e0f01080402030d030c050d090f060b0109050d0b071412060102070605041406090f03010603030c0c050409080304110d02040c020a15050105030d050d0b03070605 83
    0xf110541d20303c03404444400140c585c1c0c61184484008035071303141841c40d10107440f860348041c3c01250f00c40c006d800c3c804102e0b0003490b44c011544001320740e021211100720141040040d00d182c030f404e4a01a4145c0d104041c0258950300960002201c292982885420403043c8542c43d01640e0203214201d910304001c009560070406103003c1e10303041c98400d081850190f82482c000c02d0181c0c0c1408406404d0084d0503000c12049802001003180010040c1c0103281c0d1107142c030202007440307001501d5480c01031042e0b03000003407414851420f8030141d601c4050b100d04c0040c100c0b820844c81c4e4120700e101d5544070b101c07041e80c0b141c165130901c10000103501c2919010110407841c140014020407951003203000c0c0c2c0c10b1400d500006400317242241d51041c3d02210004100402c000401d05d01c0609000080d040b628140d48002e5182d000220116100d2188909078003001d4141040000c2e60741c02c0c0300d12a0154440c5400b481400e000344050301c0000801d40c800201040c0c1c001c002840e20105600c05800305c1e000050000d11011 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 289810701 1250 289809451 289809461
    0x80307020706110321040305040b0301091e05071209080d02040602010e0d0f02061b070c08060a0b1906270e0a0f1803030209030a0203120316020a050d030207080904050a0b04 76
    0x2903c0c003540c10321074200300801e014004c0f92812a000c101201c006020940078109403000f4203017800d1065180d41e10b07034050300020440101c10590850100e003c1c5904001c450003a148500d150303030390b4894041002c0c04448041c0050403012102280300748007102c2c681a052000d00001c100c142c0c000704941c91448a1a800c10744509030420421031941f541d10446078001514603000b004921400b04100c1114031001707010301580030000e1820841c1c0000050300400000c1d018000c1c0618441000799046003000c0005c403283d00009078004089074601080300502404c00d0f2078003941c039145020741040b0064940300e00310310b0310740002a40301d40c2c440070301400048034030030b85401108a043c00c005c4841014103d03021a44041002010113800103800d10b020f44050101d0781c00154042c0403035a81c501009003011380c0c0c1d0011555943c1300b49221740d174003d8a81c0f001850500094001003e000c840802c00d02c110b01940c080c1e001038800807803c01c11200c0c5521f5234400d2038800d00c0c1510000440715401030070003050725 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 289811951 1250 289810701 289810727
    0xe1005280b04032d0f0c0503010f1a0f12190308060103060605160206212208070308090c100c020103050c0f040501211e050c2113080307020706 63
    0x85060106000040103c44c4076070103010b00a0718074485900c070030218009000d034100000c01041128420604000040c8207110666904800a210004621b620001118002c0030300c58620300910140520b1400c0c00006c2140c222005016004400800c4440c90f24101c46021800600740d200d940c68000e055104418581000007403034140710305851700800420f24084c0c070308040c40103548540d0b01d208640c6c07510300702c4014406d00c800840d0f0700b40c4001400e000c1024120360110303c99480038034070101c0f8a0303105e042c0500c3c00e5100c105ca03428040c0c2a2005c407042100100152490b11841a82c10700c5580c4145100c6001760542ea1404a101500d01c00142650703409090022018018401d01e51810024070640d82541c000307281c40cdc02c0040000c4100140620000303241c4204502e03003c0440324042009400340e5074040790020030700464440104550715440f074004500c1303401313294641c00440c01000111441e00803800c3c07003056141154588500200340d109442c1d220260f0b020304070800c1001c3d04a1000034000f = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 289813201 1250 289811951 289811969
    0xf011a0a0f03150e10260a1502042301170403081b07060218281403030903010509010f0f1427010c030903080a150e100528 54
    0xc94140200581845250900d0900b41a26000380700b40755080404100c0040c00d5000c50241c41d0b0410924036010f800880c040c4130000c00701000c2c043c0180f150042102458a1100010138988403980c40307118105403120035450701c45408000010b0440300c0e035510110311840b070300101d0280c0c207c81c0001515110707080e21030000e11881c00c0308110100e6002004164401c0c3c82948031b004002d061401c070a0a881074110080c4040d101080c20014210003000c413141900c020f072419100200e200bc4104203243d00c441c41d90300c0e182e2054100340f2841c85861800b01b240d003005411207080c108414002400c1d0380c2d049419510582d56070350b24172502c0782c15004100d00c9040b61642000707422215117800407a040010f1072900c6241100c800740b40200c03e401910002240c0e047c00800c00000e151400501504140400303070006000310380400c0d0407440a200d801070ba038020f4030745c2c1c544e001d240c0650b0081c000070040624210700e10101d000102c2ea01d07850382040381c041303140700d20002c41310032000c606101c440306800c40408 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 289814451 1250 289813201 289813207
    0x709050604050613051b12060a05030604110d02060c06130c2106020c0c0a08072402100f110d020c0712030804080304020f120102071101050313060e0c04050f011a 71
    0x810786900e013020070041c000c54004100c5903940800074402001c00006440440c1c00052944088240b000405014450480340200c04a030754034205070b03031548140c601070032480c4104142065480c10300e002203a102c0c4050445414403004c00c006504261003258804000480105100d0400c9001c90008024160014800d1000e5842c584696821400000003c04e01c42e400588032108080411100f60102c0b4001d2055029584803240d072500c5429074401c468000010091076144011303214100201480c42c2d50007084c802030031122880140516180a10752955a40042c162941c00c0a00a040720804a540542e030b8030000c00246180c001503a200314030143d160050070000075440005150846d400c0500c076522a102c1e400020281010038847c1540005211070b6420180320640291444034010000b11800c0c00640f401501c6501c4101c0e07000c40e211075a208042c00181c4150320200100c03480c0c908a0f200c030301d071038408034084800a4804034030620101004000341ca092a00b0b12002ea000c610150341 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 289815701 1250 289814451 289814461
    0xe030a080301090b040c180905040218160201150e060904060e0d0c02030c0d030507140f0a1a060307050307050d0302010b042f0403031e02010b130e2112090717070905060405 76
    0x488017a4502800788d003291244089000e41d0348801096080d103094089013049030030300c2c5c00429082400d01403558059400c22541d50400c0850380d0040003199050300c600c818617981c40c0100054014001d0040b01c040381c0d1200e01602c0c0d4401004803070598041074540316003005160040500d850820140144100d51541700740000a600ca010380d0156640b206201801051850596080480e0070241c6041d034400c000c406800c0c005911440010103c0210740e030b8010b0f44418041c1515040d01d40140d603090380c404401040075043c07034401055228024800010300001010004080d034145002c272041d400a241421304000203031307440102060641040c0203103464950359014080c00e0b0701000e00500d895081e031024038114000e410000060000406041d0307247e44844a210003011079201044d041d102c0c1c80d01108504c03200480e4a21080000d2030460f0801c509030701c10301e10300c49008048200901400c600001c43c034454201c00100300d01c07810302401465003403001e103401300d400c018030141c411070034241030003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 289816951 1250 289815701 289815737
    0x9050d11160f260111030f0901020705070b211e1602060a020a090e04060e0601080d1b061503050304080105160c0201030f15030b0121020604060e030a080301090b040c 73
    0xd001c4400c99583c14010906401c00e4040c0c085500402c41c2c40c5509003499070395100c126400440c490f00c45550440207589482c00010308030300820340c1c0201194828001800044d10683c040c08540e128006444121040d0115803000c00c0e409540301660340c0914004840d100d00300d00645a800151132495010041540d0700007541e0701009058069a10390020348581d1583c8940c41580c0908000c24014101e0b08080c0380c04001010381c00713541c203600e000341c00011940120124604021261582d1242200b100316240c0001d0b003814400201d4a803039a07160f101005e00316100d0404000c500910140da01d817440c2040740c40c02e481005104129049030b982d8200700c0302c6c0c0c03c0500018021340a00c2e001903900300c0e40c001d590080c40c8811031902984020034000041040300003115040c0d540742c103a140490244c01c116085d1030f0502503402580f00c60240b0042c80118882c451120142d90020101e414043c502d4a5140b150350082e0082c4801d140c540c0110000d07030416001d076052111080c5000c2d1144402000d0314 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 289818201 1250 289816951 289816979
    0x1401030b040204090c061206060206070504060e12061602100510060f181707082d010b060a050408010c020705090a0c020c060f0306011b020607020d0609050d1116 71
    0x8009030506008107055450b03550180e080780d03500c05841070748240c4500c0003410041c03c0150301c45400341000c0c07000c0713107040c40410170301d01504040c0c9901c1e0070542450403d8500c3e040341c0c65042d42092114442982003038040110178000ca441002c4080503114880c00242041074100e4402401d46c100b005001c0ba968075401e203501120410321780400040000d181c2207446007042445a505088002804521007a80751480a07070401c0c003104888005030388100042d00d540c40b801e51105005400b072541c0c1c0100d07843d8520071682405800c00025443d00b08000a1180c0e04240c40c4800010000304050040010912814100000c1800140561890440020f0010100a040c251b04a49604900180310300822590040d048010801d0f07840e00007a401c104c0c1282c00880e14a80012001c0e03040309280c115810513503000b16005409140ba000d415000e00c14400c0610070121045035494040b100820300500c01d07428401c101e17030758240115514600403842c041d05483c1c10511807080c1c0c80d040024841a50750 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 289819451 1250 289818201 289818203
    0x103020105070f032006061207080709090c0b03010f0f0b0705280507080319050309100513150c0807020c09010909020303070507080304080105100509070c0821040510140103 76
    0x1d00c0c4801c5185284c00c0320803180c005090780c41440f900110401c008808564030b442241c00303503190151200d401c0d43c0380c4d40e1034080b0f200e0242282c1061030140f0020220342c01000f4407a02a0340c04000e555613a00d01d42140c0e40c000d0303003d020798480300d40701804620b00c16268440200080d0240c1418201c0d1a140c40d6101c000d4540551070907590062540c00c0c2034098644070141c6500711040c0c3d00a560345400c030680700d40c0584030f038007100d00c61640c00c134041900880950b030040712000010f04500b040d50380c030b041c000c040240030b41000f01ca20014040028125205120855044000201c2c0110004201601c914409003401d0203540014040400a4480b101101c0c110303901d00c82c01007054959400030a0035403140e0f050213800b5018804011460703e01c000018001c44100038004c00c0740b42c0d6110080b2500c15080d01a15500200c10380108500510501140442e64001c00303106207440c03201003501806041d8200d400806d009042c0811061080520a6009900000b0801e1211103110001800e44441c1400 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 289820701 1250 289819451 289819463
    0x1d13050604060803070f060b0301050103050d03020f040f03030507060e010b010c0611040509090303070219020603010627080708150c0304030809010f15150c0305030109091113020918010302010507 86
    0x1000402940e200d80004005103a81c00c1a13941d544520300f0500c1780f40e02e800100781d482d5030078644e00c016182014490a8101ea03004005011050304a900c21006580204a0000c5014061101007480451040e00c1c000452182d121280e903100a1301d002c2058508191014100d030b4503204003480d8617600000001140c0340c2c0b081c00041d410000002d072000e1030189805c44c6802003503039020400c03800310001c01580034003540d400b00c984071503904082141c0e4201c1460000d4000c034040c070040110500800c5807103126514a00240c461035804e0341c14960047c02907011121661002c4420800c480c401c1c00100d4540b0504030408001e8a0848034291161201800040800031020001000c0c5082036200000382000c480e010301c01051480159807107c05c0740c2c05070800c0d111003e034800061030301403c00f24102c0da6140d1103c501f16072804c0141b01c014018135030b0558079907803440160700c5180e1781c260500010340f400d064016140c070090014046448100e2000201d170075042001440581e810105803486954056 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 289821951 1250 289820701 289820711
    0xe0607171506190507120c0b0c07020d03030209031e0304170c03030a0807090f0e0411030105060f04202809031a0a0609020a2d09030b090a08040f061d13 67
    0x10408131014415050080c2003103400e0b0903070419182c0d104045403040b50050499501d81c0d220340c8110031192040410080d8411266500180028000c5e00640b4045000070160f6023030807540120020080b0150304001ca0a130030020f4140449142001d1042c402c0803c000100840401e110200f5980e1040b0003085060018560004a556105415040261400c4001048002d0381c03100d45080d1084159412a0190ba010080c0202c9050500c00c0c20b204060003401c000782c0f100074a00307001c01410701c81c5811285411603083d03261030800540007407564414000c04a000c6a5000c3e00b01e000a0400701c1c1440e0801120390802c201081500d26000e81505551000c41410b459410441e0020040c0c2d905c5050164004101054107a4112001803030301c161b000402e417a808440c1c800041111520304a200208100c200c0c00c0c800700c0d0315a180d640e8842d20101c101d03080c840d01e64507865070f035400039031040942c2102d8080074025540e1012081d0588455031100311108100320000540003002c0e44074078210f9990755 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 289823201 1250 289821951 289821997
    0x80604060213051002010c12090305120702010e0a0f02150403021f2a020f010918090f1a041101020706050a05070627030806030303070e01120e0607171506 68
    0x1007500c1500800f0300426203101c01004c200081d010b0082d031203e490100d00c01c088000b100c80030b1805007480081c0c1c580c0c0d6441c980705c01c5000407464040054064411990f071a00800c95568003008482001c0d0b0143c07584c0700c0740c0c0e411032041001c41c0130219415603c007842400f0030070060f2030350134541c0e450303042c2d04a20f2240ca00b10000304071606190b9241d2074407402d2a424a8007110000f5049401d0503034001d840000003142c2c4000192031400386441003000a00340700300d414901e500603601280072030340b041c8851000e41c41151140345980100b0442c040f610700600c018401000b1070032559420300381e02130028040075450a0005000f9010307849407181403050004000003042034503441091a418031002e00b00390200400304158035418201030490205803164007007001c2d403400000303a0744180c000b55145010b04110200440308c160780d403600421101c0d110b41c614400620144881442201c69075036200750414034441e005107081e8041d006400c0320400744003107051078403090f00302c1c2c4a41440c003078407011043c95 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 289824451 1250 289823201 289823227
    0x150302030a030f0c080d0207060b040603080d020c010b060f0406020712050a11060903010e07090f110708130906082a0a05190f090b0f0102070e0609040807060f0912090806040602 78
    0x2210754005d2191300006a03207410201d0a17806420800c0c0200001c0100305144070501c01118902d00014040340000e00a241000c000c6800614000700c8034000030440c2c040400210303406401959090714104008a0103024050381044120020529080c00414a00e01da469060310b4403560034000d03104400d000c041d11101c0c0c549500f00d038165407000e8020010b40c02d4030602a51660864010003c0b980d0400d006440280050b000d902c00404003110724619041035591900e046612001180ca04000708a4002540c80414444d4074000c0110314003814035402c2a800c044611070407031381075091000a80080c0c000360345498128405946090740c090284203d1140035154a40c6542d00c00e00c0c4203507500b40080740b00a400d4200b801142020b44040200361010300c010398031242680148413061032240300080852801246107034000c0d00a44145e4a8560b032504c807041034030121080303000219115401c14080240c0ca0500345403010991070820140c41c01d28501c2a11060041c1003c0c103070640105404c00f400e5a = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 289825701 1250 289824451 289824467
    0x6091012082203030f0c08040e0702010b0d11040b010809030d090201030b03251d16050708160b060402090109030f050118031e0503011223011e150302030a030f 70
    0x120342615101640e0b00c2546041c00c0141ea40000c13030000302c800103141c001901805c0044001c581c0440501d0800b8141551050305800040202c0704664032810b000c0c01603210040c0240050f4025002c0c9041d4030303020400c0c841954210040a81045030034010000d47c1e610101c04c0e2414101980c17000b068a9025000413405003400f80d01079945805a1803610356409030f8500080400104402d81c0250590380340204041041c50909000c12460f2000c00500e010308001185000706034107082c06070510344c050716140a150403e901101d42c901c2d00a0724641070103040140c050b40007000302c1d410341c40c0880a40c0002c5c02c1c51b20500c1300401500c0f84400c140d08111742034100c0f001c0402040c2541020360350a060007402581038043c46d80700c105c0c1c00c4545411162107001140d060f40c0c4e45142000f02e4003030716960307040c07900302c0001e01d4000c50a086001884c120001e0040c0100c001000b44055a04001804010112002c2c4117032100c11411703446040005840c0416880c070300e030780c060400450700300341c03010b00f647c200c1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 289826951 1250 289825701 289825717
    0x90204020f0d060e1003140a0b040602040503011505030319090302100509091305060f13121e08010e06061e0708130602010b01020c0405070e040e070e0609101208 71
    0x500108070900e900d10308501030401c2500304242030007482c0e66001c0340301c00c13248261454040507650110601c04102d82c5089031001c6800d4104031a00640c5035100e92000a5090340c1c100c4003642c00003030030080303842c00340140d903401c1c00b02c00068699540392a0020780d40344900e506000e03000310700004e008080c9004d0701c980f000a54010704410749070725409000800719402841c00ca8030400041000c81c4000224041c2c0b21040c0380d000008140f170751038540440c85100001030503103a130110004840c200080303490034204000745003501c0310751100c0780c01302202d02e4100f42d03981c0a00411003290010081140c1b194061500880700b0789040f69161141500300c526080e02625828400c8400a80c07a03042040e01c000505100c001151109041900c0722406c0b826140c4401c2440c1c0180d12051221855140c1603000e0b58000d00300c1d05107840e400011801140a0b036011b08450802504490401c005030480d05a0f425070209040b00d006005146c8040c4100040c83d16014540040b50810155003c0100e030604450b03100c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 289828201 1250 289826951 289826959
    0x11220b0102071205060604180506010302041d0a0308040b0108010c120908091512011d18070f03030c051002090604031e0c1e050301061413150602030a1719050a0902 72
    0xf0b03146810525035680040e9040c50040d45400c07006822161303060035425500d50b00401030100c691854017000043c00381d14241d8400c002a4000c2c8400c001020400042c1c0d06110741c89820103490f250400080c0580140e0040c2c0285c1d041c20003140889900170100180020440cc00050400a900303141c3d000b80a446169604207421919403403d4030740003006048903240424000c115a0f8071070036042020659101c3c211140854240424103040c03000c01202002d828040840300d0040d0348860303012440440e42e200350003107244c4000c90f90511900b07100920064903440001c1d4a41b500c0c49000c906284554030000d0b003890386407c0004013003120a02144403054104426525044d1a01c88545405800029510785000d0740394002841d4141801002c0c02c9a400040c0d6140c41403180d0144035408011802c40810b896440c0d000005400880002c040580f460b58003c40d260000034101600c141c2244000c800e0410026080107440100c00e03650040d451040c0c0f5011840d0340f1500f50031000f0300220f00c0c000b580 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 289829451 1250 289828201 289828229
    0x4080f040f091109010504051309050d030c14210403022a01020120091e0a090b030609061b0c01020c060106030c02070b090a0b0705100c03050411220b010207 69
    0x260310025032481c81a90340012041002c411054203007100c601ca0a26500c0c00704106120821851410416280c104c51050307501085947c2240c4d00d140c1800070b8400c00c007003c659110040c82d842503019800003845002d40d0b01c0b0710701d08580000c7e01d51001e0000602d1021850070080007c00b007610a00c100d4414225801040440700710700f0b42d640c000c8a0002580714019840c02581200344200a0380d504042924403640d02d140c03d200409110354400c541070a5408400d07005036058042c0c6030080240024500643d0000368584100c3c201400c080004d00b601c801039105905109462400482a00300c40c21420511965401000301490280c055a03580030218000c4100024081d501030b044115011004d500b03486c502a2180e1400d10503000d0005c45980028140c8018403501408100421510f4014011036082c100700c0c02607442680c00c1038503084002074031041440f0400040300440e5441c0d107130854880d89404100480d9012486a00010070401505c0b007c01e1240c590003031090314003078072030101c12400c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 289830701 1250 289829451 289829459
    0x50604210b010306090212011a06031e0901050402091008030d0c1709070501030c1803150608030a0c0203010f05011410030b10080915011a0c010204090203041202120306060d0504080f04 81
    0xc02400c5e40780d4180d0180a4468114641420600c1031400120400140340180d00070b4000303009558100502e00c980782400881354800081c20034243d80e228203060800484d4a20300b80c0b06004280c10b02400c02c3c0d80400344507400740110403021003030306d050300c101180001e030030b6800d0300c012a04094480719000800081d03401b030244d0380002140000681e0380a80b422303c81c03180320082c00c8480c03c011481d6000034608180c4180001040d0044801860301c5032140410403e40315111135040d948410410008905035941c01c0b801c50070280a0740220312079a0b2001c0161703600d801c1d075180002100d8400c061161036a94023000c5854020741c42041c0b91600a000005414544003000c0e0010300d064030130240354800c400f20055911200034045040e00c0b8402129810681d140c03800c40403580000c0e54503d1255000d00010a041000c0c0c80070314402c5008105d403035644800d10001030300b072481d00c00d1072203d603c2c02001081005d0721508200d4078404001500000d2540d20b41c1001000c601810900505801002500207 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 289831951 1250 289830701 289830713
    0x150b03041709010207030308040516081c05120703051f0602030a020f0c060405060309071e140301050417070c090507021c09030b0a0e011509020a090609050604210b0103 74
    0x510440c032070039024070512401c4140900300d004140c1414010f910407141400040d200b0300da142d070428410700c221407a8001040c26055101c0c1c0c00d40055030340c3d43c0590100c10f806d400901c420910900d207070412034940307001004918040e4a00070b01c4072042c1074503074000c15801070300198840c90720340b0b40320782c10700c906070b10785800a459074000082000103200d00b642880c64600003085180c162403006040915283c80c040901c11241c000030180503090007241c600140305040d03a0290f40c0740050900198440c0741c00d046c4070555160303181e0540da000381e140004000008008205030020300206016140e02e4100034a8001e0568070590445040e40f0709003824402d00e26000100c01c088401140c8280001d071110600860300d80600740300140010007408041840000f0360750201c0c03061000c51002081c0c00149103080300e5100e11543c00000c40c2c507030008038084480c0d44060664064092890306a803d41c9c505000900507010300c1c01003012160b0f007000c241442c0c040134284080d010354451120348007583d5a007000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 289833201 1250 289831951 289831957
    0x4090b07030b0618090402011b0506010e0f070c08090d0611040806060303070b06040b04060305061306060b0f0403060b03070e0a06080c060f031305030c030c210909010b030604150b 79
    0x10a0800341d48003402e00c1c000d8280c034654500d00348291310010b03030041000607000d0080c03c06c2e0706100d526000070b003400304440c091402c5540100002c084a503d040e00c030b140303a91b1005000401c509440001c5c069041d51100401410310340142889880c2c0301c483d4005a550000000001c0c40c4602d0068500510074841c0f001d041262402c50a6521030354807041419103030b200300326000700648010000540b0034a002d5102c00541003010303200003001e0703481356030365464060284c41c5045d0025407003600301c04000241c0140701c090711013500c4d81c506002c01001c04045034011400001c00c110380f902c51041482e00d040050300c00a0641040300b5480e410700c19002d100516150080d84400d008101e41030303810342002c0f41215905040303038000301d146179105a0b000c240c0d200b111600b111180000c1141c0d100020041015040d8050620050194800c2c549011005a44010a580045003041c400d020260b52071a000038116004040d140f40d4a0b61070000242c0244941401000c0004002001041804100d03004d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 289834451 1250 289833201 289833211
    0x2040e06190b0a210203070509030618031b010209031212060a060903061d010f0b091303020d0807020c0d0807061802030c06090d0503040e0601021002040f170a0204090b 74
    0x1240540c0120501c50188144034002c1c0e900c06501040309680ba207101c1c1c0c50911000344204070051840c10b6080304c0c441039a009554020014801180a10035481c00348100c503006110614001c103d01031400d43c10b5185d008881040c05003104551b401030b03400d1020340480d00c611000800b40c40100171f1440148450b40c01030749800c200f0440f564002070311401c2407008201030f501c098070303186002d0340f4541e2540c02034008940704200c8400140c401d0261038609000300079000001600108a16880a007400141c0800507c142c031500111029000440e40116441a2020700c82ca400c180c0b0713554200c801e900e408150031503542c02450311b941071001e104205000e8030000d84141002d002c1c2100d101c1005002c66114400039501d50000001c0b14042c0c5031803070052001d010007505040e01240561125800c1d80c000c0c1c0c4c043c04075040c200c010081c0070345c0e0510030801c1c41c04250f08118106410003004410045e81401503c0510b910b24400350021980ac0040400035503004105002641d035515014070203107420750f0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 289835701 1250 289834451 289834459
    0x115080708060c0c07150509090106271211011b0b040b06010f0906050c0a020d1a060303131a0d020703200a050309210609010504030e0103020c150901060902040e06 72
    0xb01084800d01204101c1e450b440704e20b00188811360615000003954003180002d10103010003042014102d07200c03082540c0c020007441c0c44461400c41003030060551204141c0b46151448040c90b405d114240b18294462803241c1c110405282d050b0701d20340188d6241c0c08100d03044282400c09901c0208000954241c51b2146124034055616500c6000064440841404000c40800c0c1c2d920741c28003100d8880d80103821621840300c1111604e40e6181c000c103101c4442c40400352035014010300e00341e140c0c40030000d42d507410200c01d0740214502000390801800360955401030501c1007c1076484590f01c11700c032074103403004d0240104085540f50024500a0070601c00010306110300380003226900748040001c60104469900480950300c3e1040301810407116125580090b4207488515241c04070080c020001a841441101d000007824203046c01c002c0d1010070815a101c0c105801008040400d6a020829541071885407904c400340c1d44480807010b0240205030440074000b4130104000419100c0803a4440c00f0342001c0d1 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 289836951 1250 289835701 289835713
    0x406050c07240f0902010e040c0203190203090f0d02090a090206091f0e030f031b031b0601081519090204241404050c0a08040807080d0606030f2a020115080708 70
    0x1031050944041c04c03006400304581a241030300500340f0340c104151100e668410780c1c0c9011020700701103032601d1201081c08010ba101144180c02810054a40069110704649800d00482c841c0e0000b4142d006c020700b450540e6446490000840d1168000c5d2610301000030903034030815400850b00d1003104021082d0400260040300e90171020700300883c2c1c0002d280c10341d4014529140352102d041c40b140e00c8109943c1524030040240c08035030118000c0380c41c4030302c41040180045516021049140c00c1da1642c1078108554400284814a440100386046203440700601280110b142c2c00000e004001199400b0444154584030301441c1f0784062411003503642080c0002e81000b030710744c01c1c00200c410444484040c17140820000c207000d400790300100e5200f80b14079401c0c9e1410106039101c00154101c203440000e925114070007486000d03018000c819084202c104100604501569400c0c1c0d08400a03020080a0f5007540342082c1c418800e402411200d11191031455021b0b51394500c2c05d50b038040314400c060381c0d40511 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 289838201 1250 289836951 289836971
    0x9020306070804050607050c120d050f07020309010504050108091f230c030a05061f0206010e01120c061b0f080910181404091208060316050105030406050c0724 70
    0xd10441d80030301d40000040c0190307a903910043c0c074654014509800701d403003803278210303582e44400c1c030010801300b403102c45c01151508000126401c45907004d412401590010300240310300340d80c05000d0b40c1c21100246031a8502d9116001d000d418a00b03442e01034072014140140e5520001404d8000503211015840c08140e8850f5003200709074061803d0b00c500c2c03c1d101040000c1040c5107000d4001d81e0300410003c0c000c007400e40c10301e20a0705546062800d46000b60300088010003264920f0b01d49240141101a180d4000003025a103070b10130440c00307018040901a0000303c081030030340300203603208542d0341c0201c901040d40840c2c2000c800c190400d9050034411540d40d14856070a900c688290b042e032034184440b01004a051070040101c03907503003129043d045580e0340034a00c0800c8102011315800f2002c1c0d254042d480c2412003e06051551500b01200b049c00981e508201903603000c0c00b01d80c1e010b40c21160000d203544a010700c00c08280b0603040058820b0b00180c03003101c041c0c48110517501020301c44903800c00407a009 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 289839451 1250 289838201 289838207
    0x1020c040605130b120303070801080d050712181a040e0109091a060301020d0c0e0f0307080c01030e03130b030a06120206040e060d12050c0624060a0219060902030607 73
    0x18024643c020303d00c00e078035600860340c2d034200d0707404e00d0002003481181c1c0850b0752130170740b41d07420480e46100001d0303945004001d840f00c14071601130515200d241c03c904c0d014a07070b16640301c0003941c00d904004109003c4801d80741c0b1030300401c001c4064049003035034183c544100b00302004160414020094244007a40000507200214480c1d110300b1503004003d95020795001060000410004104a1309075400300301c902d0300407c00784100c0c40c48821b00d031240c26504800c001440028070080448174020341c0000c405110303803040029400d0582000b4a804904c3d044c10321001c50560099000410300c404034500e02083c841048006944078021200d41080003e0362115494106c1d00b14042c040d400c450100030038041c0d0f10503006220741c4901c019240401403500f907035035105000742c030842c0c4030000380c400704604103601c20912004d50810f00036010804102904003130b04462083c0610b546d481500000341c0007402a0003070002800704208031080c108515907900708038015143c41c1d00101d12034061140010341043c0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 289840701 1250 289839451 289839461
    0x8010b090127030b01090c0e09060a090c050714072309130320010218040207171b03040803132c060a0302030109050a020108090f030a050a0e040504050c01020c04 71
    0x142d44180d82c000e020703421001118180c128003040c109510401101064219000b58024040381030002840100b0440003000301c8110001ca600c5580c91788180001a92010311410030743d11901800a0758040c4210261018070441c84020441e40d002c1071205483c04012807898100e0b07014aa2079040f48070441e4803440d4210b004414a81d1010314480461021000d0f1a440c141451003803c1c21010340f4600c034994103c41d165240d114140703a4000420103080030140102800300402554254204030a0b503544003c0ea034619410ba10f0654000306031036940505000c1070400242c0d0030015241c0c0c07541c48a80d940d8403980004100300d4170384840903000540c400491203545071f0095428000e024100346810f0a011004050582d5601c0100300c8404800340e9428030515025034441c50040200044510000d082070b8401005640300f90401c070703c2c0c110400c01c0030085072081c0b52140780144e510365420b074094070900c00c1078441a810914090402007004400140c402c284003098085600341081e0104020030b0324 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 289841951 1250 289840701 289840717
    0xf0102030a052209151503020c060109050a02070b011d0705180103050601210902121c0503060406031a040b01150c02120f0a150c0512180109050706050a08010b 70
    0xea42040034403a0315011030040005004250514000f40765107012503000e8865943d407850f8004818541008003011903c1c0d80ca002440314141941000304040140707443d000140f04600c03000e40c41703400245d9000b49070741c121041030307510544440e1556141d0144403045032520030b03130032402108c1202040e00301b406034050f00e5a8a0103407148940c03e40843c40110301074480075001d0707818080011a4107071700c0000c00e04524a852149000003d130f282a03401000380445100c1403070405c40d08003140344038040304545030041c84c2080c0c2e4200640d880e110200030a00428070340c0d1026103170a1142e011804540104040c4501550151804040b50b07622603640e0006101c48500e00b4004c40d48808132a0010b003402074491240201c840c0559107003005101c5c5050401240200c21100100022100e0414160701d1007600a90171062514a00b04032840711100b0741d200c8054100280842920030081505009400c00041958040142d07000203641d0900a003150300554440404907402000120701911390f00203a41d007032 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 289843201 1250 289841951 289841957
    0x30809060c04050f030f0105160905060f0a0c2f09070305060a050112020712030209120604020616051e0d09051c170f0703050904060b12060f0604031505060f0102030a 73
    0x102c0d1500080012070f810b1903008607054025200405076403202803180600c40c1032000202c01c01c0c0c0c2c01d0b48100500d9051b00350032040c482d203028020603000d011500c00340c2d143c00c8a142000321008040f42044c1480d1032200700081800b00c112403400702c032240c89081d004150030050b18007038001d860700017040d000da4030106c40c100d811030308024003085998031a440d0b10380804202ea900600e40203040d2500c490348010f201042000c01d400043c00c41c503c3c1020005046030b50040e901400c55400d040d4000360762803060301812041d44140d510705005109043c0f05002d805440c200b5107031400f145160310f40c0c1d00c606c107440e007590201d07009000c0000d080c00d2450490f4a51007210b80c407160342038100c1d561080a060300c0708070600710803018030000401c595181c0040221034001e03102c05454100b4101004103aa01c035400c22405000d0034020801510151f010894020310f0840d0744540203c4038001040c8980500c0e80054002d8000042444003940030780c3c04640206015113401c200c0c000c007040117a980b407061228034000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 289844451 1250 289843201 289843207
    0x1d15130b07140a031509051b160f0b09070b0406021c030b03060412030b030a0302060604050a060305071d0a06080c011d0a0906090606090b0d0b0406050a06170a0c050403110d06020c030304030809060c 87
    0x4408548002d0049948411401100100a86804c0b0300140c0c040421542f40b917410050090034a801c12030080140419203150740f51078100036000f500c84011441000314882c5110040200d14083d40101e08030703600180485680346468141003064403012400207010030300d0030301902d2031400d0110325a03100070b401d81c0040907691074440a1100828004245138450340c4c3e915408400503009000d05001000741e8a6940c0c0c02684655415078000c40c060b00c281c610390329043c030070401c060b03002c10b802602d403100f424040c00d00b864800310b00300e001820040301c55111140010101d4140401d030f1000b421346103404420040251603070001d46003080d55005440c5001e005004000900c000c130307040341d89003090140c8007242482d6100007040b440ca4050b01710001144da5150340581004504158590007920054148600700c241070740580148103600010b000a0381004101c05c2584403295003511460b484807046540f05403580001d0740305d820568049002400b8003022502480c800100315003c0c12100f075403549 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 289845701 1250 289844451 289844491
    0x14090c06071707060212041b060c0f0312050c0408120a0203070b100e0a02071b0501050301062319110723030109061d15130b07140a03150905 62
    0x115460450300c4a1034021030800450f00010018000b8054041a248405d40d00d81000e203010b02e0641c009000035000ba00203007800700314596101b845186801d400820241c00b007107003810126440250800ca42c1025410b20090148071500e8800170f00c222404030003580c000f204028100301c541e1242150400c0103030b209011400201c0c8604200641140342d200c01c183e01140e4550184142150403a20f502071160702040031010b000c0d010030264a01c2d41907160700740086080100291481c00103009041c00c2006207183c002285442c940c5404800c03010b9a441526480e410b03034003051030030b5280c003100005421207540d55846580000c5010035699410340d0540d00d0154280741071620103032818410b0703056403107108a0022170780d107101c2c201c40c82c00b0303c95040e40788a004903907841c41d1a15900c251407140961000700b00f5201a0b0034171700903425920099406154584050444030703100c0f040c204d9142c11f14009504130b801901a03210120345240300081c101402c0d5114524001c841d011503002a40c002d9007140300d9 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 289846951 1250 289845701 289845713
    0x6040b0306221103010521100203070302120c0d0c05190507020a0b03190518060c0d060b0f030106090b07200a0b0d06030215030910180f050114090c0607 67
    0x1c00360340310701030b0002494940d800941d01640d07509000c152400000000501c82d908000070030844c202040c00c0c1281200c14152440d40c2c1e42e182c1d030381e00800b500b030780400840c4900303100f60111024081d02c402c4042d11400d001d0700840850b03002c00c403480ba081d86802c6440f036409001d1800c0d01d46080b400c001d440c0c0b07800010f070000d81d01d0342d2106000f01e074000101007020444143c4400514019194130b06242c01c120788028000048a0b00545110340c07000070107031109040c981c001101c2da40400000d84031501c07a0345051401000c1d10498021100c4900302244942001c1c440d04040c43c1224906d50329194120b95441e80c4d600310348240d14001d0708030026500231040849060000322100c0c000074048001d003a07501d82c8000c52a40050301500b2105032a90020420b51130610002d800e041c0310600c0c02480c50803c00c0120741d680c400701000c0100c5c2c640b80d40e95840d01c0380c034440d1348840c45034001000d147c541c1500d2501038028583c4182f805140032021020070704451001400400540028005c5d6140c085552910 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 289848201 1250 289846951 289846969
    0x206070c030201020d020d1e11040501050904150605030403090608040809040c0908071403010b0303090a1a04092333040b0604090917030405030318030d1d0c06040b0306 74
    0x5600b599001c0080343c0c0250b10b5803000f400385c13400c0d4003c0052143d024480000100c3c0030340329401840750500306a081050500000c0b140bc695090902c665030311807507804200038110300c8080d0b00040d603242d00c00240d007903046001188118865036135071080e540c5402d011742d00103009440c05840b01600f800050300c00e0400b0790094184800e1410420422a07507401070754a0311040d9080100c0001d01c564964100342001d000c3c071203001c001200a1030400300004080340c88000d0511400c0001880c40c5641110100b0300001c030b0b000b82104001c14851041c0e501c82e51541908000340070001c0c030720784800103850f00414500308070000700b0052520340d140c41d0741850540100400b0b003070142d00540c1c0c1c20340440c003030b0743e1a40244002d00c1c008a002c120f110250601d40800b520110200000e490b00b0010000010b40100890758403031800b020034158501c0340381aa6246010303112107007c00034500360b9075040d9500c054400c60030a0f2410000c592240d4414824040180514400d40484910074400b04030b1600c0c0182c04 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 289849451 1250 289848201 289848203
    0x6090c0405040615060f030f050f070e150a1805040c270e090706030e12040905041e060e010f09050714030f071d100302131e29100206070c 61
    0xf011440420a4420040180c11544074401250481c02c00c0f0780402e8060003804015141d808081007145410700c0340e441c22000c000c1a220070080700b001903074040d580d0108008c0d00d5541148007540c07584c034851000350000c2d420700d80101c06ca610301d1400044914040c02650170807d2a59186800c5003015403404062141078520501c403e280d1001c04500d03211402c0504e403054840e84024200149003d002a08132904258240100c0d00401d0341d50b181e0599102c2180d081b10a4000c001405944504251141c08003940411180d459840203a1003403000b990800310141580100800031102c0462401084898003d0024429000501c04110310310b510501c005040c08098140c800e4000e001090341d09046c0e89420071441c4840120348944c8c0c03038541c465460b91000c090304110420314111b4002603144072520512011803138852010504541c2e05101e092040e42120005011220072050f09444e10441d00352000e6032100d084403144ca407460002400c070019012900a440c0c180c840240480d10240c10344c41c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 289850701 1250 289849451 289849463
    0x70204110f120f0604063209130c06031806020904020f0304050304030b06032a031204090603060513020604030b07140a0815010807021009051c0801030c0806090c040504 74
    0x32048503846008010b00000d409607903441c856240a689000b030303490b00984020701407890228280300c44c500700d0728480c002d04413001301c01c400c0e150001890512240c0042c580e41d004550001400000036880320380145480c0b2a0351f428002d5501c80c00220100d685542462880404010385040482c030554020008008040c1025140041d8080e10f131007903900545084500da40001010001c0c071049060351608030400710050802e030400c00c46044074a28030f00c0321096603103001ca145e02003a541c0c00c105410502c010407925586450352000c1d500e00602c6188010741da503a007040b0000b00c140c0c0c007211044456541c018500c03400c050850312400351060004080c1c000380080c1ca030441c41566a0300000d46400c245a41d9046594039040e4141074111820008040c1400034410600440580206007880d0301500381c1d00014403c416820f2461912144c81100200406440c001c400426405040d04c1d068900484a1020240e0780e264243e58800d021108000795030040806280a0310f442d8008681242c000c030 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 289851951 1250 289850701 289850707
    0x16050f0f07030e0306070305040302030f0903010b0306280b0315062407030306060c0c090506210102040609060f1202030c04091802190e040237030c0902030103020607020411 76
    0x2040c524441d800304000350701051581800d040c1601c2e0400217203900c00710b0351406001c603007807980c0e001e5540c3c0540c0840116201010480004940f8254004000088e009007250020304200b40ca80700301d19414501202200010034523504070f000d4a004e400e0740c0c40000360040ca05620201000360b881280070300b0041d4014400d109201c21441d9560102008502e61100a641c0d09824603012301100c00961081381400303000004c040c04284110b002404a603c1d000300070400ba91140f00295080c0c0b100344440f80300f0002d03440021045201540a802035699a481d118522501c42200f03031184c01501007200d0004140706042d040c1280e80e80c02940c0c0200d40c0020181c1010389038841c190640d52508ac15211012078014100c0c15403410a9111001580d044d05601a0504145801d451440d0041000e4000c0d0182e49200b01d440b1716840307010140c003110000c001244010b00c203402c0e06040503484103070307407402c0603050102d80d40c8014030071681202d5002704064600b000d07a509220123003018041041c1504070074 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 289853201 1250 289851951 289851967
    0x40e0c0310021810170414010c0801051503060901230d050105070311040f050d2109140306071220040803040303080109060308030105130609150302010f02010516050f 73
    0x10420420503103185940503807a20b1000780b0303140c0128161003003107121380101280300b001a90066810740002882c4ca02007020341e522801c104080300c3c03100c001c50781d2940c60041c0d60b81045500400041c141c0b00d0031140c103410540d031a8296069400282e030402e60101442c00100400307180c500100fa41c030401e80005c3e86601d061034001035008040500d040c0c07820b94441d01000300e07a030341c94424107104e01c0c00260312909103400c10303e94200d1903c407401511300400c2100400818400c49800b0300240c8104981107900300340c0e82072802000400188207482511001c4408402545400304641d403150405945141e1415500b03040c5101030002000310009404c6080d9040480036500300040c03000d8107200c801550389a1851400419100d4168016551a440c12005000180c001400c03030b8110345040301c400c00071906000001000b815180c0c4504016072402e80120319010b6420300ca001124000d8882c42c424001c4410241d0a8035001c5902d2200f0621990a000c80b25000700b0284c201c1c1040c003480c0318144446 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 289854451 1250 289853201 289853203
    0x2310030b100314060403140904060e10030507061b0b151503060319020a0501080c0d05070e040b240a030207050f16080d08040204050c0702091503070504060b09040e0c03 74
    0x400d036510307440c03650301040c140203000c03038105001c003c0b040400042c40756103450388004100010300c0410b2058101e0010702d580403035a81d508a1400340100ea41c0011183c2003a041c190003901241c40b080307c03240101840094894002c44202800c00801e220428100f9507a0340c4000b1010300080400304581100403100e100d075118801c0c8100c2252032009000d81c0c9007005010540703491031081c2c5c00e16461403c0082c01d00162920040d00701202d2082c24284401e45890b01d02c00700c5409403850131030b045461300c8100140c03194031044d8840c000304d054030200300307038502c076018464010546944411034903d8560001d0b641040c03800108500d0081d45001402c180041d0354440c05d0500317041400c00383d903210078400413070004080124401844140000c102c141d050b05400340001d0802000607118654880001b4140140b00d0100c4000c568000e0004c0a2480c2001880f1100e11000000c28001c1c8200c00300803541c3d0902d807040c1025101348a07005402c004184c0100310150081c0310401c00d1501032408802c400da10 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 289855701 1250 289854451 289854473
    0xa050c0303040b181609020a02011e0203060f0901050f100509130b0a0b03091b031006030303150f050f21010e0307060e010b060f1602030d170a231003 66
    0x3c440c41c040100b5080019058410b21310710301207446a034000400b00341c0d0f8400d14004640848445400c05a2500000d200a90041a18030008101005e08580030b071056100b65000754031503c411120504a0f8445000740209800c09010700c5400c41c2e03508030135400e14546440b00c0e20f951401c2c0d1a00500e4207070302c034001c614498403090525091a0710783c0d8000e82e41d0b180c89401d020182080f900003138110302e0540c4078560b440d40060a0750051031038008000710161018030501d40c554141d81814816035a40b85001802030165880404005130310503c049400810043d502c812210002c0102541e002c0c07207020000d05c0701000c0251a0740c20410403180c1100d041c01c0c011001010f4100d400b95880d01d201d4100101035034221030006843d07034500b9110702041e5482c84240d0b002c0c1e005995000d0b071a038551140f900c0110101b104040c0d45440703001e404201559020040f000c1c4496018011025511018428002c1c0c0b25142400206c540d4040c1502220540411000d81d20444061000132a00d0303582d01c0e0400608 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 289856951 1250 289855701 289855703
    0x90b060a032429160b090f0703030f110a02100f0302070c0906081c4505010908031303140327040e0c010212180402040f050103051f0b0a050c030304 65
    0x99031140d000070001c85091840d10416201d143c00614043d640f00b40d0b13054010501d04010180d01840d80400e8082004200714010210b9035402c90321107503140d040107420b00d9060b1a503100051101200a0340b8940c005ca2000030003030303020301408442421514103540000803583c02c030f801c0580c28045800406d205520060041840104c0028014181410141270004594070030b00d00c0d0352000404101380307500c03045181112010501000040e850309280c491402c0b0f0408210018250201d410003650064140c050100d59090303c071244103950750384540303449005103080031803210400b46042000ca0407401114480c14100b006503481c0c1311101840d181000e0050301544004061401d2608880c01d05103e0624980ca58a00030b04611401d41c000075a68280c500c2c0c881c04154021a02c4146a50441c0901204000041c819500c03251221080d903105d2030b062040c1800281132002003181095081c000d0780094907041c0d4002c06c01d90400d41d41d000c44e40d010304460302c20400e00704514000200240040c600807 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 289858201 1250 289856951 289856969
    0xb0d080301090605010c1101050706020702030f1b12030d020d0603080309010c0e06030603060a0b04320f0907030303020705121c1a0d03031a060c0a0c090b060a0324 72
    0x654142101c0a00f203610ba6008681441030042c50b490109904042001d000780d801d02e01503660700b03650b02c0c14001038000c4000094044c400d0380d00c0c04022040c040781e000103000484004003c0150300104121590010040800c4290000c0001c010880101e8000b001480c80304400410950360fa40e507141e90507031044500010a035036031448500d04a038410f078100c0c88100101c0d040d074114182400040d0b2225005098521050307541c0b80c06420715162078106651007540b43c80720783c20811040c41c0020a45e05220f03c0007840119080000d03010504209005000d0641d00c002455414195a4107600a500c44401918203100d51600c0220720710481005100e000c0da05044115602c074828158025a000b0441d64200e80d41484002c510940340c1950240c0e5141d01494041001c4008182d0701c426200b2442c003840d00310b1000103802000c508000350b0080801d105542100c40705039a81c452808940c0e1a100d00c95100e0740401c80607240702c0c801d8100f008602a456036030084046881509114419543d104141d0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 289859451 1250 289858201 289858207
    0x306031b0612060f150a1107150f09030b07030b190f120602070804060504051f050904091103030408010b1305060a03080a020c090916121a07050c060f0103060b010f080703020d0b0d08 80
    0x607540c5d00860a8000d050781c2c1f8001c252103414004100c6c5444281003d1004011340200464011482404910000e64000b01902c0c09800d06450090281c003515001a002d109803407404c000400e0006504400c80da103410070301410508041d0f07503407000301e00c0c444160f030b13421307000d02c850380200c1e0740030303005000400f41912625559894503081c072a118208801c0402038400800031000e0141d007010407180c041104880000e078080341c40c80d108000030906001c441e01032201280206038880158000c2d4881c940840d1800245240c8140b00402d0b240c0403101a5041540360310200001400c540c00b41146503141c0c015501d4540303030340c004602c140d0003c940d410b03141da1042a20b680c1810741440d04034081c0c0001c0c400d12281080035110700f40d52012108006d104841d4100014126078450001d80342111100c0058032001e05104580e0348843c0e2080c00b0595100b0710b0058060f02544c000c50201c0c03103a20b882c0d25400c0c0142d44100081c1c00035000846070007509910340c48541101ea0f1440002141d8900c280c4500361 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 289860701 1250 289859451 289859467
    0x705090106020105040b160212070602030619080a1704080d0f0305151e010318030801080601050405130f14160806090d12020a120609020306031b0612060f15 69
    0x24149069018030300b507914241c10300c00801d0b0300700c642c2a4840d01e0480a240c103521341e040100d1400c070040b451040c5141c1c010408004205032500118003441e000c0703a0000f98141100c03880001d031001c41c0b0170106154410008003000419144407003c046410000300ca0409542d10b10f9107061201380f40d113500c0020088400182c0050b010f05c900c58000100d401a400101064000700d20f03060150082002c403458a07025900300c9030f110307030010504a036043d8041c20300314003d49000f40c1034480c00c0c000e84085004087c00030505042c00d210f031610802e0300a0f040d2118071195158548050464003040d121600d40f940c5103500032004002c0b4820010400820150310b40ca018042e9081000207400700190b038001440800046034051079a200d0b1001200d80140c0d01d40c000202520482d64205001c491941015000649c1402c1c6a0103981f0544040d025100040882d010388054800c0f0701c0a4558007013014885014911140103025a018902401c01091110240b00162486000a001c140560000180c2003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 289861951 1250 289860701 289860709
    0xa150305010209031204050a06081b040806150915040e070b030c12011205070522050c0a02010c030501210c05090c03040c1208030403030c1e050a02120f04140316080705 74
    0x40c0340f0300f025a1028140750421000400500d0b291140c03000700000d1001060034107013040004003000d082c03002f816648950382c0c241c032038440d2030481d0640384100300644c0d4200282090682107202e0101d40c4000749080701c030b0b2000c000041c101d180a00311503206404010480f105840d00544c001c0c20000c6400d80c581504013561509030605802c4101407411340c4c0c00c0c000000d034000a003071003640c1045507040607801480300510342d0000c00c40100040765007880c051016a021080c02030100f40040d5000f440103d20202c003d81c151003080c42069410030700320900d4840301c680c2d415074540f490700c14801c04586030381e80c0002481101050740c02c4040b80038000107101c1007213040b110030ac0003030403020035541e900f410945511980d0700000700040d0a05071512401007807a403041c009454803c1e4040d2141a1101d03810100624070780190010f40c0c090300c1010500000040204103a80301301c283c0610f10751515044c098080e003d4805c2648440c2c040c410007072030034961b800b0200150042c00a510041c03408a141000700 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 289863201 1250 289861951 289861963
    0x5150a08210702030c01110312100302010906020115260102073f05031005030f010608010f06080703112409130e0a12090b04030503030a0501050102030a090e0a15030501020903 77
    0x9400d103288100a010b0050300c02003100d40f44030710f090820100c000342001c0d2043c00c6114220201d005200200d08002c43c0340000074440381503034000c0e40c401d07060b139480e50300503802c9842e00c0440408591440c04204203110a080741c030300c405100340042079010f000c1c580b07400d82681c101080c201e03044000000308102221094140039000d0721440144614005c145107600140c5540b000c0c501c08008001002820580440030641700403c00501140c0070214005c02890080002d4010b800c03465080829001c038404882c00740500392044c1c0c00203808818079540d44c110064004001158200122000c03403195000111422505850011210b0b541d0390090010410000c0054141000c1c00c1d01d000d00344e0040c240c0001702c0c18a007642c09021460a80060301c006d03646400d00d603000c90720140b00040d01004201d8080081c1d402150000ca05101507601c80f0010390b180c2c0200162800043d41c2000200104581880010381102d0300d100700281c01c01070002e1700c11003009190801d541c16034002800e0701103400c04200c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 289864451 1250 289863201 289863253
    0x250306150501050a0c0f02090112030306050405071b140123070f0c0f061e060806090606010c031b0206040b0403020f22110c0d0c03020d05180405150a08 67
    0x10000c058180350001c0d0a50103040500c508100180240c2c0d01002408450068210f40007051144150395441d28030b48000c50b445001c800103402c0400c0010241418003d00c0d0007400142c903a44250210030640121010407550290b48503c400d68654144400c01c3c401e800121041088010000d02400a4417401d004003a119004008403481c2c100c00007503000070200305040d0300800340700523039580f030800001924500011070603d900f0749115400e82c00640d80034a01716010780303003902d0351903490051660320349104540c030b00e000ca2080e1031504002842060b01b07569480d134200e41c000c4100d801d42c02003481a08150803401150800060510075442c00e00c1d01c824014070101e82425100740b02c0a0120b00302d031040c07015038840e030f0b4640e0b01c01c5901071444001c0d05e2407140c11070200c40d103104807178000420003200742400f903015000b09030b50000810700c01c80031901c0c0742003e0080c0b00701501141c01400014074005007190b840044040c4100c2c05545c1d401c030200020300c2d4079001001200340c0c2d45490100380701e11034a = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 289865701 1250 289864451 289864481
    0x203061602030403080702010314010b03010f0e0c0a030504170a050301030311010c0c15060b0c03030a110a1d0604151e020102040807180612030302180d020d14250306 73
    0x400c44a18070381c00002c48041c0c0c0d82c001d1840303803500210700c0181d002c2c2c0503017483c0151142000e000801d08da04004003960403110040c1000c25055680c502e140d956070b00c180c5e001d804501c4c0401ca20300e4024000d4000b990098450800d0010b100a01a0050070035084000110002000000100185680590700b111008100030080050504054014046042c03031000104190125540c00d0a15041544501c1c014001400f02e40da544010f45116601e13548100c90305508a8134051080f050f100182c42501d20180300c58681600e2003091041c0000304e07107403944103158099000c00c0b0202e40c141c0f015013024005180c0f030301c80d040d1541c2c00c03030381800b0500b9442d045081160300c180410009440d00083c800c0c112004002500514420261090007500d0700c0d40116002c0c2280008420070581d2580c001c003660051960410000482002004200c0d104101c020b0347c41190315080c100429144070301c04254485010032500f070803030303401070300c00000124000305c45d82c131403104604105003c0540030708003603240d140b0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 289866951 1250 289865701 289865731
    0xc070518040b280209040e0606060d05090a0f060516021f05090319020a03090905060906010806010e0a090608070f0b0a050c010b040203280608032b090f020306 70
    0x2442440e9962004002801591100c8003140210403140340c480e803108004480940c008408001d0040a540005403a5018a00d40700070511000004203289000d03039001001c0c0c5182414080c061000350001400175841d070f014040c080350014140b01c10640d446482072102040d6484c00c192500d400b400728032010015904254804018041c030381c200361000014040300004c00740c1302d081a1525600500da10280d010050b4140b06d844503800064401c1e402e8070950f609886980c40e007241400b82c0f0001c0d5220380d000603404012030f82560003143e209902240601d8a804141c0000000030300d40403655214600040d0b03201024000c051050101d20098034541c8000b42030f43d4075019440101d803285822850401c640494032042c0c0803800c2d080b002201d0340c020000d640700e091010304501c0c1900141d01c018414089118801c04014860040e00f0448403400003031070030a40100d15541e03052045c206030702e002240e00e64246c03441d20140d11462480a01903d020a1041314034410300d442d02402401d0150b00308009 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 289868201 1250 289866951 289866979
    0x501150513020a030b030a030908120a0207030602210a0f060b03040503040e09030706140f01050118090b0f0a030f03030b191401262208090405040f02030a05030c0705 73
    0x5032600503040303981c00001039949071025000c4005000e441d040031742c5409030038040010305034411090815a40030000380e5420705500142c9400ba8850a0307400030168200000c100045449607020341181408403081074940420100140c0b8104801c56500d4805643c070030800ca80c040c2c8903c140e0000d892040ba1141ca50300380360319595074a01551050274017620150001850049007401580c00850788500248144404501344c3d4402c10001c6410510300d80c24907000107000c6d0311038005440d007140288007240e80f01d41492023002c00b0b00405902d4a40050b00070701c008040f0b407038034124180118002d0a031050300c0043e6203401402d4030202626144240f9081402046004ce400a11411150303003c0b201e49403400c9803001a94200c4003092403015003040994208104002001194400d0130541c3d000760310100034194031800c0040d4400042e04209045c405440c140c03d0039800190001d02441106880c880c3c40da0001e441c7c04c007034074022601078001140070146e0b4001000300c0c0740038000c102d406450350114 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 289869451 1250 289868201 289868209
    0x3040206090a0e04030c030f050f03041209180608010b060c0718270201170106050f03060a03020411040906080114070f0306050a0b0406120b21190f05011505 69
    0x540068840e02001034001400d564807485240280201030081000e807401d801c0181ca400800300c5e003500032816403131140740b2003803003407080b11900c120002019055403104d480d016080302c0021a00c1051090400c00810405c0122030020443c103164030740800c602e411311070715500352110320080724020701c0240710b102a480c8020070070030141c60307043d40386d503580c0d001400018000e0510500083c25241c4040c0200400b1100480d80d01c4040d4000c2c8c881d46481aa100d003040e109400034401c11000072010b100101107048500c0c000c0d5007000e8020003d500c3c96031640c000400f180e840b82215044807800003404c21010044c1d0242400030b11a1400800001d4245441034507404070040104042168021407041214081c1c0c1c840c1001d840d000d84001802e903110080e4600d00e174081d0003a40003058000301c1e50048102c02e4015014140e0010b810100340150040341003c1c103d03802110b075003481c0102055039000050500320802810b002d94500d01c1141800d0811900310745000740f940100711581c200a102c1070712 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 289870701 1250 289869451 289869457
    0x70306181106030a02090a0f03060b010c08031302120f071e0501050a0c0206070609080306010e060c1c11060a0504020a0501030b010e060306060c07080f0c1002120a140705150714 78
    0x80300350b4209540781e4544091400a02c40e100300f0503806510400b011a0284440c24030b1019240f02e200108182045403006640c60030003070000038407250041001540200c03008121922061024080103070042c014070a4038180040760391030200070b03403010f4000c000f02080c00c85034905881d0602001c5084e2030501000810074440c201009080c86040c101110454582c10111003c113500031004104100b03e40c40c0120f03042c0c0c019290240014206074180038645009001c44804143e06001081314880e11151002040d1008104409120006100140c90201881910b205110f0103c00145915041c410051401c01035000303141090324240800c0c240c0c0c1d070880080031000750202c0e0380644031341d00c1800040c1d04d03108103030003000b1034043c844001542c0980001d504101c06205030545d41ca104104040c0442c0a00482114c2e0060f44420b4103c580000180000c05241c556403030903c1c8a0030340c0356100c9000d07a0180104813996030010324508040500c040803203420288504e001c4818400300194040240 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 289871951 1250 289870701 289870733
    0x60010617010e10030602190206010618090b1203070f0b160f080c131206060801230c1303032106060207030311010204050409030909050609070f0c02040b0303030907030618 75
    0xb0540b0012a100740d02e050b071084001d5500440541d07540c006012041c0013404030b00c440d000580704071000814500c1c0500c0c0003c1086010020580040d45401c040001500c03440440a8101c0240d0078001840c09040c4000d02c00b5600514420205109070328005491501c01000007102078094403401c2c080550000f09824200f400703141410660300e519405c8690745c80384c1d81d05070101d20103c140c00510a6080c448040c0c015000308020045542c1c1c81d40818207989003460b040540700318801003400350310408880c6a409c804144545410302c86841d600c1c1c10074900b2034000741c0219801c0800c403400c0f2010300a500486280c00c840511609181c140c01940d03411a03400001d0600010001e19000e813002581941c1c01050010170510641e15182130140094440d070050410700f5080200103486c40c1820b24505000d88403965801c6000d1480d0071046a0280000c1d0303040703a001c0d441d0024410140d03000c1002d54062402100600041e034039502d000707800c40304d080c001c01c8940481103100030049009003601442075 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 289873201 1250 289871951 289871969
    0x110c0c0f060a030b120303150108010911070305071502030f06040b0103060303091a0d0f05070f050a080703090515011403071d0c220b070b0105036001061701 69
    0x282c601600000d50841a4003080161762201000708061007041821040000000307032114005030742c80351201c4080c2c0d00380da17150440d140d008001e40c10002e0300c038000510105002d0744c901122480c1002c0c3c11401d0ba88142d580e0301610f072159050000c6ca15091150f00244002400c003085168510340d00904454a1445034184002007602c4505000300d014080307230902c5044c1c00c02003004082144080004100503159000010f000b22100198035000f28102e0f9901c180c0c540311000039640d805003c5000c0d0100079401c407150701508444603070b056800312185002c0c00d244450350011540110505240060960003100715000300300f11048080822020380d6000038a4007c09035132440c2c444442c11815035041d1b13030b00500070119000020405414005429118811011101542d90f950b081603643d81000002c013907c2000310701405071000340440f14060240b00035202c26412804d038a40345031602c86010b5102416000004c030700040421401c0e000d40940120304000e120644607610540d06090140038007498 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 289874451 1250 289873201 289873211
    0x303050703090203030d0603030806031225020d0302061b041a0c0304510e042c0d09080d05090117010303020a03081b0d051306110c0c0f060a03 63
    0x5524440d0b0420002c5503009001c03290745e6041625803100801103480154001161080480c04918001c5006500c8160000d541401c0c070ba9803001c000c0c1000d0b502d0400990700c114107420280140c9503102c00c03400f030300c0c002d8000d03202c40d240044002c40307940360000003588140404c000c1440106c1400c0d80081d108104064410b0311071450001e06491031156801c003001c0d13560040392100410700c43e04085500c0e6160100c035138543c1241250300c030720360002c0c0303000c85682c07900105502c0d400c0c0c070b2045584036002e0f9802480811140304400344101c031000e0040714038503480480e0207130364140b110400c850042c14665140c9000a070f031509540946600000c00602c08204002031000b01686c401c5555102c107046111060701e003542c1d00e20300a559181b0458049010a000301d00048014004a030442c1408409290300c23071800b003181c3c1c410401071200410028040014503200360124080c0d108950440b040c0040715581c87c3c000540203450030001e281c2c514400d1400c0800c419a60300c1d104203176020340f481d134103001c20 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 289875701 1250 289874451 289874461
    0xa090603090c0302061201080f0c0f010e030109150903030e060c16080d050106030c110c06040924030501141b070204180f0c060318050a17040b0a020303161b030305 72
    0x10b0700b00365a01c06984541d012498584207034000d00d0b018100c6869a044440c0440380c00c0400c2d40701c4070b411041e560b000b013400803070400329401000c9521504400400004c4c4e101240d0380c0e0164801d06610f07171154603540e00ca14100401d900b51003000c0001468034000c0155117014040b24025102e20003091002d00d460300203440c100000c540940303400f5250520180b20541e1103c03001402400054400d41c0002c038102d00c41415800701003010b0408210190070a444d03c1d042044040141c0070311340c0000c902190402a070500e010119a0303074406035220f980003259074403511a404038484006844c6006040d840500c01820042070f50444076010b0307050b20701142d443c1d036100d580c1c407100e18403040151078504494004010030021507165400d40e4031607201040108030800c2c113150000c0c0d64039401441540b0410602c0c0204095940070194500400e800600e426144d8402d0301c1d29030001e07811380c00035a20220505c0703051039946c441c516041c0300a141c0b0103400886403114250101905101405060b91900822 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 289876951 1250 289875701 289875713
    0x70506130305060915010504050403080609070504050d0503030a1116240203041b080304031e11031002070519020609040c051314030d020c010c060c12060e0a050c0a09060309 76
    0xd00210340203010b990061038018400b54a9442011410040140c0000003191a00e000c0c0b050758051901507540e04041c2c0d90700790901c24210005424101400020300002a15aa0701c000b20b045007072061010b1a00d82c1040c1c450039054130700707204159808800500c10107407440e100c07948000b8110b801060038544442480d1b0300039031074543c141e410341c2e00a00000401c001e1180d0404400c2c040f403003c03052407110555130709140c3d449000b9400014074070841c038620030040080c400b07901c110840c094400142d1644c40c07400003e25005042d81070104882e004100350701800f405008110150707242031002e0300b1403880c1e50b0002d0014482c000026100d0b079070f0f6031200600b0380e10600c10384500c0481103400d0541c0c2e03602c030200c02180c1c80c40b044080b8403900ca0301003d440c2c01071000c151407100020603190304a40403000d595000180081d1106c1c4010840112256404000240142030042c00b40d46015881401c1c649054002e642009225404610003004021200380e030103004401201c0082c940002d200c0c5840c5021 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 289878201 1250 289876951 289876987
    0x130b09070c210915050903161a0304060b04020a0216080115030b090c0307060e03122805210a140105011d04060308070303020a26010504020903100c0809100608070506 73
    0x500070101e00599480d5480d0410000d1940020460450f190f00c1588000001e00840394014064040b00c649d0741c0690a41001c806160400d2081320701180b04001c1300b01080481c3c001d01c8483c0c0042c1d11104449201140047c40c9002034130500c2c0082c0f04014000302d918049071500d200003021900c04100142040d032040c0200d821440707000381034407203e44d42c814008004c07220b030307168903442401a540c8600c01241494122a03098002c07410300c100c5000903140c2d0a08201c400964103040c4102082510f010042a8480c0720003425070248010890605140c40c030708070383c8011903030150441042d005200f183e8200c0c20701c803240c02500401c030b480079501101040140089901c002e049840120310141010317015006040300142c299181781070707180780080300024180b81510016100201800621050400703400802c040000541110381010608550710308459402c442c80001900380030610082810520020510515015090240b80d003000d05054488a41d4030440740319420001e82080121030103002 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 289879451 1250 289878201 289878209
    0xf150c0201050909040803061017060f060f0301260f10051e24010503010f150c080c010605040605040b010801150e0d1a0c12070804020f130b09070c2109 67
    0x41c40e1800d007481c1070b01c1b10340c0040d15101d10442d581c0d40032244181c85914030b80303800442561101d01946036603041c00001d01041d510650080001c20a500f82e0030714000045000300b100300c4d620100816880200050065030444041043e000005039a0715070800084ca100d691034004000262500c40c000400c4801940340c00d081811022801000300f01000e400803d8000f50101e110a540c00400d03d00440b01403100b4007038841542c407840010721240d42807100414070500d07242401840c102003910307006030981210083c09a203a44501c0c040c807040c10180950301c020641660f09200c03090b86880040d10200050051032303200b07107600c07140c0120540b0482c446001c04c0809010900300314000d040c955096200320760260070a0320030b03030085140646e264044031003003a5640d4803160700d0b0b205c8108c125224a40681b05130b911050070340d540042a65503040350001c06440280000d84c0c4004a410701408641c014100c10902440c45c802c1c00108038807d0000f0300e089074410200404c911584002e640000c07003600 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 289880701 1250 289879451 289879459
    0x3c09091a01080105010e07180b070f021005041206021614060109050108030403120e0a080f0a050111030c07170c070906031505040c1502030f03150a0f150c02010509 72
    0x1009000d869445040c00054424851180360b89500800303099070000e106050081103500d000590b00c0e40701e5080300541c0c201c00e002c0c8c0089607951b1441030301036400810040c3ca041d00050b0501045103405c0400210504050030100d00700f17031400d501503e407845110009010540c000410f595082c42c1d11407000c0301c103a8418410041d0303e410504455490800340a002d0140345030400100f4071a03000001c0d02c0490360710812941d5400b17144003084822800780d111054101c5c0004d1004282810240203240484101c070300100b000080030300301142940e04200d10469060382c03c000380b084401100c0100c9803601e40048031091403031200c0141419511404c0c0d20407016000345080440e24100369004501101c0c014140074041071b5100c000c2000f214800d4400400b0f0b4042120104039021401c0d99004803008140196801d0010014840c011a8001c96800c4805600000844941d29107480c880018160204085820314280b507000460340031105060300a00c00c002001c2001c580c071500071502503850144c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 289881951 1250 289880701 289880711
    0x207020604030c0e100b07200a0303080702010b010503060a0306020a0c06051f2c0c0c0a050105070324060c020a08011a01021911090a0603080c03133c09 67
    0x300b0410810340c82d0307005607144014a00c0c003117000250722556130350540c6e484401e03c51402150740d90f40b0b503492403403c42032408100d00e80d403001b82075541d002040000398000d8032440054941400000c0c00c4070140341e00241070142c00e1082c4048e03030300c89801807015a0341c030120059840c1111038091750014250b840007000282842d04010a620384403a05200f135035003031020300f02071540b40c0000035410102022000e8980070030128010302038032605001c64022103071203200d9240040d54240f8506040010006450a0303440388140304040384c3c10f100c1c00c00756600e240892207811510fa1500e800b2020280700d26010001c4450350070080d03664941e0000010b1071807500070411301042090700004262101455030160041d6440700000320703c0d00500f6502550f025244810703044015007041015807000d8010b02c2032a9807004084000785140e402051301d038100f13070b008584030480c00302c48210860103500f01d0b09002c9141047c0607500e03096a62503500310400c8421601d00110300e40220b083e42c030340c140c1c0f00458032411f003 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 289883201 1250 289881951 289881953
    0x110607020c030d03020a0c020d020a090218090f04030c150b0a06020a03080c0328090206070311070812030604020913050a0618140c18100f020607020105240103020702060403 76
    0x2429100303245090b0161a044421060150100d0003032031031520110702824400700040c901102515800c61000b01520791264032018000205c1c0c000d587e06008081c9040189213480ca404a030b400d0340410403203c00601844c0c103070350081034034884800007464050400342d034060310300c2160490755090b00040e01d00b03c406903541900a54400c0400d0b130a8001c00c0007103000c21409501c1d001103078426501c00c2039038039044600041d00d40d42642840010241d20b07545445100c0140d0710b200080518a0080da40e1480a0455091560600610750f001d400e90307a1041e00c01c3d40c261000e1106596105004550060311420300d90040b44428030f80301c104926a500d03100070021030b01e2441e4001410384e8400000d111100c3c8030102c0f4102142d512004c4100b40564040002d00d00a0040c8004d003800250204280701030484003000ca84403022108118000c0b68030f10b03044052281e81001082ea004d0058802841581011103a40740c00000010408010300812641c0400d030745d0103078044034062a4060003481c0d039a0b41e6 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 289884451 1250 289883201 289883203
    0x501060e01121e063821010b301605120403031b0c021c080d020408010605090a0504020906060a09180203251202130e04030e130c0509060a11060702 65
    0x3501aa0001c0481306a01000305c10505180304400640860300a10a001007103a820b07140d001511050400c07821030400c20080041c1c40a80b5001740801a055900c624003910811125240003040444000c440c0d485102c40d4503401c4d508a0700700d003080c000d80c0880d030a0140304445a100d89040100002c00a500303100415506038018150001040c0b4100030081d88a9800c40c0e6801290102075400340f1101b0f039500c00304291401c034103056442040b0480c80c2c01e50300e407000e005030f0f041a845400180d556500030841810545107240c0e100812400801881c540380c2d0008a07655005080c59000b40c40219800d200e481c01007607a4400f40c58050004064034600d40b1500c80070758070856800042d080282110b480c01942606558000030040e00d07401e01c16030740104800001c2d00015000c0c500b00900500000380310702402c0c2d60301d01860080d03482d200001c228109001000d9100f0b0060180071780340005e440074840d406020b0350f511090882e1000d41e1002c40362400c03117220000d4510070805014103000d004c24250 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 289885701 1250 289884451 289884461
    0xb0612100503010e030715050a09050d050406090e160e01030209060d0504140715030b030129010e060301050d02120106080118060606080106080604021c2d0501060e01121e 75
    0x54210b0080c4104140c0741c110b19241d005110004000300d05007642602800d6454019590115008000146581150301e130140340c040c444c440030002c01e0740050140010703a401160071014000c006000301d428106401c842a042045030081307000c01004a0980100c2e0303100b074048841d0f5000062016488983c080f800300010281618100c0f00c2e01d8046c04540c4503654007141a80c121405080a54041e000c134034000e402404660f1502c03941550380342c401818240c0000351544a85030740b49807140310f0440c1c840001d003000303406640e87d0748544810700c0100905e642d4140c1d14109c469040d42d00085c62a11000100c0c05813105d5080f00203103508112000e1325407040d0110050308540038441c240159903481c50282c906207401e01a000015150900140300360600da0020711a080070b10310100716160360001d9030000c131906100c101038485160890304c0042c4400e00040c42146200040800107549021310162402400c03901c1141400f114990140007140c85d0384c0841304992201d4211082c03021800b803408004c007 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 289886951 1250 289885701 289885709
    0x5060f0c070e2a090a0b0301181a240705010516110607050702031501060302030a1413030819020c01020304060c031803080c04090e010905010b0319060b061210 70
    0x480340344000039031801108207090080320308500040383c2c1d410301443e40c0c1d0804030f9103000500340c9004000c04021500e0b088840b5008040100d0455100e5042242c00c3c040408a5140900740505003812080720b9020140c00e03a6240408035450076091214074100c28096200ba004151503003004a0444244071f019004103214150b08000003041044040c4180d51040c016020000306912041c00224118040d10061003024001811070312152032140304803103054001d070484400650003101307106241c0c1180c0a4000b94281c02003a04246240c08a011100100b0300e00014041004080118007080201425807014841030b61041d1360701c82c81c0100080c040d61080c0d808540300b5160200002c1581d100348102041c0d0b2800360254954003089440859002c00c018180c400000c13020040003900800c14031a00500c401d20b44004501e26140307051403403c50380d015031103030301a811208418019900b8848403007400d03079201d840040c810f810503010485a016005c000c1420000010900c40d0321010030724407800715 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 289888201 1250 289886951 289886953
    0x907140a09060e0f0f090a020d2a0302151c02030a140a0606080f040f1b080f1609060503060a020c0a0609060b0915010f0e030c100804200a03150605060f0c 68
    0x5a01c4d1140c1c05044044100d1b0030b9452500550903070760040c078291000c1030b0304601035000b11442d20402004101000240c00035000c591508003010811418032040c0080c01c041042c16581c101000c42c2041c45191007021004545140e0000c00100941e6142d802841e1600030812a0f40180c40e00e1003501004140e140101c1003c071f10b040d000544c00030081c00d1440c0c4074991044060450035003d40d5044800004805240340c0241003030301c0400da5010822000c1c02804004006150280601e07000c4204624280c01400311a070400d40c007030109407400500c207500211041c80040e41d48020030125800e101e02900000c0160341807140d51400d01913160002c1d8150b2804460b60b0482c0e0319030b203100ca40c6d5407603840072a50101d140994010002d6000d41095481c4d0720018041d03644001c6800b00207000c2103200d000e0500400c2030401413000f03200000400010043d00f00603580c849400716000103003c4e07140746c8001041d6025084c015401e210098000600504000c0d0045850f007a2414900105030401011840c0d6 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 289889451 1250 289888201 289888231
    0x90203070b27031609020315100210110a090605130801020f0c1e1b031c05030711070305100e100e0c0f0306041509030c0f080409140907140a09060e 65
    0x910302c0c001c610404c0540c0218044d0841928140c03140c0040d40008200100c5a03a6243c4030b01d006446028000380c0e4034032203a001e45540950050054101c4501c181460380c030740828031024548d82c2d0481e00707001c103492140c01c09649034031800c85400a01001343d000337110780d940041804034115180a014004002c00e131015034150034404144003060020401159202d036000f000d06401c242e142c48096400280c002d000d5401094800420f094560403842c030740e1000460020070000c0d80c6a11030700041440c1c07403070406050a10b1845c0c13101641e442208043c03041c003d40c2c6182145441c141000f80c4085100303800350512400c0703441c6a40301e844281505495005041042501000d80341c003242c254426075201601000701e4022501100c001c00c0413000c21000d102d06259071001140300c80c1000031715035120b08022541c86041054000984840b8050b011441240d2001d0251084020400340c0503901c0b809110b906140310b81001600c0c0110701d500842c40b440c904107004c00c0a40108036043d2042d0407a45034084 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 289890701 1250 289889451 289889527
    0x281e020907170c130509011404140412030f020702040c020703060e0c060708070302151302150c0307030e190605030a0501050306010b0d050705070602031305010c031509090203070b 79
    0x100702d1104031000d0342001c20355001801045030700d8003402d03940702c030350b0045403145869002040d071740700c002c0e0400c8408054082c502520b52500f40030f0111065003800042003030781015961860b042800303904031428151111100f823103032011035043e02c000b1500200184074045103030780041c0d00c0340c48500042e24070700d040140e038001c5080c0000b8802d0600002030a001c0c54100e454039042c0da03075040a0011011400350110950004034005800342c0903041030070b000710b0a02094810000d100ca184001080c10a106201907907010704c01109948200340c2608001000e803659400048581580b0b035821280292007403c081040d66200c13020b94850072208104125590b00c400402d55640006d10a4100c6240700f003080c1204020b4680049401c654103040a90412240c0d54602051760011180421400e00c030512000c01d02009009000c0840f1441c10104101110840c2000003401e650003122695500c4180600131510f0400840c0021b001510945445400545005007003201e20150f1503003070808182096 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 289891951 1250 289890701 289890707
    0x30b030f06090a020108061305010f1d0105060d0f151401021605060306060a09121a060a030305040b0c1c020105090d0f08042019051908281e020907 65
    0x640184260401080b102d0880d500458046c4030042c022a04084009045026001c103401601c0c0600100900b119100d801d1091458880b04160114500030340004010401170700c8041c201d49401354a5100480e103400e05121203805450494041c429003000c09000081e210382e14091200d007500300341d09452407071440680e030307068020b59402a56444042040443c140d85407010080041480604024004076668080d4a6104002c8001600c01c2d030750200f5680580340d400f130745543e030005040b00c3c1c1d03201c400d04545006195000c1c17801ba54000c0400000e00d2100a941000b06001d45041c1c0e119a5504c1c911841d1f00070701910f410303140d29146210f40501a060303034dc010f8808221803040d0342e450407226034490b2140003a4000215a054200803017149080054031000250312a80099403044120329182105000c0121034060780c00c9581101000b0034803602c00049004100f6500360181c0503400352200d102030558551424004000c56081c404961643c2c8600750403403007041c0211030301055a900c0c27080075 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 289893201 1250 289891951 289891963
    0x512030117070e010e100801050910062103050d020c0316020405180319031b1106010b040f0b0a180306050f0708040506070c050c04020f03061c03081302010e040606030b030f 76
    0x1084441850100600085071700145c40e5038044401c2064555450781e40c80c400c0d0850f00242c0300100c89801000b549200d1001e04c2c00340200420003101c18107140151100c910001c0f00709c00c1001806c100001841294061058040e10080540c2205880e41c600ea25561100e43c503140700e0b0224040e9051600091841c3c49a80c001d24030700c00c1d10405589002410784909460080021060b0306141d5a0508540c265811800500300480d00d0b442d4124170641d0400030901d4104142c1c86000f8228082205100300312607010040c04035a081d10f00c054481c0d600c1c0740140c409071001503606080305420303030001040c0035094000794000c840c00c4100c4011900c440394101c54040341264054540d901420116540310300c5240094070507030003907041d01e20704081000002c007a6440800d0007005100c0c08000c0c402e6a15014411042c0080710300060055114540e4000c2c10140000301100055210b50202000356406101750030380c180b10060041007410744880014008000884c056802031060050103143e81c580000c0c4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 289894451 1250 289893201 289893209
    0x20c01061d13170d0c030614030c1e060304030f090504061406030405072705010e040201021f0e0a0605040303050a1406150909100617040b06090603010207051203011707 74
    0x4407241541d90050703510949000b04821543c0103101c020303159116101d0005000706002e60a0003040781e00c2c56201c0281034900a8000b5030440720740441030b4003569000680611026000d071403c0e00007140c615054208070300c01160603034001800000704010503034419441c0f1924046074991802158a8000340001ca030321038000c1c40010f01c0d902da4402c220345041006036910602c81d40448070b619480c0c0c81c00c01000319800120340c00000a19001205400343e500441d4050f280036171a091352860541c0000390b0711042c00102c02021003480000c88801d800b40d4100c0020040c0c00c900b1500036106ca4508200240400c0b281500003920301804151008410301440c01140c107a100303d000d550b100c050800825149280e00030240741e000300642802501c41207078083c4106d000c03c0510f84850724102020b8a0101d585600e4041003050004000008a0940202d50011000c1c2c03400c40c110364603032000c05e00a2140d9500988140305801c2c3e40d02c0c003050b0200c000d50603a81015010140e40d04901920743d40c0d42410f000f = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 289895701 1250 289894451 289894499
    0x603030c0203061513110c01060308040503010c05120604090c0e0f150102010504020f06220801060f15020304031727010e0d0503030406180c03150c090324020f0d020c0106 75
    0x417035907820309508254a002401160b81e03141550000c049400c42d1030f55031007140d02c000042402c0249250038800c88101141908005241003100e540307075840210020100c91140340e6a0f03a842c003e00181010803809088503140c103407a94204181d0f911a4080708482c15084817180845581d2a540b044c09100e0085a001d41321017072203038441040110540101c2c940810380a0b0742d0b0000411240f0885581004004041c000a04c240c1003004421140318a40c2280601178404444840100e82c000f0803203086a4102d5580d246049070a105180d261250310001c0144e181308443c10101c1e050342180c2510820026299059422049002e124102c000b00401500d6a0403d000003404030380c0e16040200c0c0006d000c0c0d034180d00d8014607501e003110800d00b5002540d040907015041d00c110070607445209a6800c10742031001460b46165a0202c01c0f818100210706120b252601d403070074004168042d078085209042da0380d0388030344c0c0e101c43c0341d07000b500689100525907003007107000910803242196611194640c030b0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 289896951 1250 289895701 289895719
    0x40516030f170f0a0e03070902030c04030f03020109020409050d02060105090126120a08040c060c02100302160209070f080a020703091e0e0103060504030806120d03110903010603030c02030615 84
    0xc0ca8600000405180d4000e100108000440702c3c200020001c24070030800c0e455a41148642100707140c034007403683c0c01c070f00d25291040080c805d000c450344041e581140d6105029480c001030914049004d0210004025040f50415034203004002020a9001d6021100e40c01c42d08030b0b80c0d0310340410001c030314280701d6a44ca1070340b04011080444200000c0b160034054280403111402c03030308140d140c1d481d44880140740020f4041c4007800200464000c40e5801401149044410100d098000444007000001038000745130f07001480e803c00c1019503a94250031030300149190301510301800060020180c058444001844100c002030160314181b00b0f840906806686a07070301203040c1811644600c5604040e00d80c1d0015542c000510391512066081c00b8501c80c400209160030f251402820142015115a10410f1743c183c40c15195000040d14801d510301614010610680c0b811054005108118581f601035080500c08010b140e04103242081aa2007074084030303240d917181101104071012a0000d41d0b4420881 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 289898201 1250 289896951 289896953
    0x10e060d080a110c060c0601080708010905030f0c0109020d05160b0c280b0403030f0b0d030206060103020d020906041205060f040533150a090c050f16120206040516030f 74
    0x1c1c00408000203050340840f08004100f40011391780c0d402c0b41391a800306501607001801a54401d0010070000d0184d08001c0c8492a41070b5504c0c0d0b00ca0017007484800003c0008a144101d81070250807031240c81340c02401c7c440341d111240c1002074855400d4182000b81c440101d030f001680d074940c030701250300ba2a0040003500200180e50b101c07051440c0107035040c0201c01503400c030410214200c07540c0036000303a00c03030349000030f074105103452900075140107201041c401d40159050001207034001c00c00702e602c44401d10700160350304454503001c0000e000f601c80240d0400c0000c680421601c05040707a024120340242d08842c00340e035401ca01c1c11107556040f00c1c01002e507080b85140c4881c6e1070441400c6800305039421b02c00c0700d80320b400c41103050103844c085481c411164030680310350147d8101585208003600b07480105000d41072000d80041c0452292864901d180c080000708058492107000390b88071410f1384800d407144000da0940f4020b66405003078409441c140100c0007a4140c054443c45100200c03580401e200e440305c111 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 289899451 1250 289898201 289898207
    0xe0d02090f060d023d0507110406120602070209010e010323030d0525030509030405010809100c020601030312060e0c0c010608060c040602150f0105120a02040c08010e060d080a 77
    0x70207030050341c1156600702c0410040c0c0e200e071088408102220211481629041e00400c0e541c512031009a00e498045010720110941c000221003099420490100c10720200ba004600107085580c42a03007402e841c82814000c00c01284c008100a900844020185980399800c24201d20002c1c4001043e54a01e03805c05903d45c1c070b100580c43d40e80101a01900e05244111510740d0680d50f04650b24480e03007224041012180d101e03444286c9000d90035150401491070040300d0320380c0d00d10070b0f40a041d05215180340002c0134800700704040318103d0351000c0c00b4001000c0c1c210010395580020b0000300e02084240d907400486002d284100021a0b0000c07910603040e4072000350002141e4407020b100c3e0f0b125501c3d9400481c402d1010000a80103a203101c50081d511482c1c50002810080c500ca9202c54002280081c010180c051041550549000306d9101401c1210340000524221702030030025005410a4101c11445400c141100d0480340c0c0d04010703d42a640f4082000b403e8243d4142c0100004801e01002c0380c00e0344 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 289900701 1250 289899451 289899481
    0xa09080106082107240c0e0906011d1302030106021b0306070c0f0606180f05130318181505091e060a03020d06050901140705070609030327030e0d0209 66
    0x7100c0d60790901e043d49035121704480104a03000c006100e600c00101a0b90000035125010700a0100e01c0c00502c07030100c510010f040944003422450410840440583d100f200e0a4018070341044002c103000840000624054040d400074800c8501600038030ba0405030710000c01141c41d150072001406000395a030b51480907980303420305030000e03103c0740c2904400360b0016009101c0d14000d40041e65a104c03101544038003a80980d015142822065400c01041c40104240c40307001314003e0b07505082a20034002002090b00410010380e001c1c110300944040c809071504200d41c00109142101300c11a003249442c1c4e000d1212001b0259800c0d90060410704103400c48007403c00b6080d0304440010320f07049040380d581e0002840c005c100142030b07038540c0e543d800f4000303c5032092040d60364040341d622001760645000344024109000c2d4080180c403403900c8200000c00c2510951100c900202200d0005403814041c102080346512804011000b007410014090207525145d00504241540100001641d84c1c41c550703520340c1c41d8 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 289901951 1250 289900701 289900753
    0xb09090a210507020303070c030c06050c0a0206160c2d0b19120906050a1a060708090607020409080d0c0206090304061206050603130c0b0304030804060509070b0c030a0908010608 78
    0x100b414880600185d070180000e007030303032400340c031452a0031421410803002d0203160340d000200741304040009510740b2201050b4466100d0f01101e020743ca034140100c84402c10189518000c0682001c0c44000c140080d1004180014540d102c0c0000f000c64106240032100c8000e0b40500d40c82d007101401011500708155012513411030840c81c05a1121a010880780191a00c29500300c03601c989601c01c000d65400580704032501c440038040300019000c4442c01060341c503c154403010305402d10000c2d9440d060785901701111034860303000d00200101401820041580e8014042d039a580c07505096a1380030880c80040c1a500402145014506d4286406c070152140744800010b002580d8460000148940e90325014604c0350310101140c0b50711000619106002054030b8200c1e5028810500c02d00c00846e6206000b10740c0154000300c00511a150800708500d40100381c1d0040101c844002040802e40802001409103c07845031561460315032a4a48e2500707a800a000780202540500190020351311b101400c800f0003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 289903201 1250 289901951 289901957
    0x210020705040f0b010219030e09040f0507031103063117040f030311060f06010305090a020307150e010908030d051e0a0207030f020c09040b0702070b030a0b09090a21 73
    0x303140c1c0c5501280a5840d8180841c12195640b101500319580603c0320001c106020681d00c521201c4541d0050040300b101a2018041e805080018040044415900413102e03003110440301a2562031030310354603a41108208500a00501010440408110542c1d40f00f003000c8c10080e41d43c9101d001800d40f40404141d0b01941c0e016400c82660013900c0d00100244042c05c80409044040fa0031414050001a002195001c032a4000c8040011070900641101e03042602403070082010740740c0c8807026140000303907003000c0c1d414015180009260440424140d04410403912840348955496005403100d030750b288a405100d4004100c02e0035080b0745584200d5210310325401041031030544198629103944100c5440110701e6000a1610070b140d0454140d100e8454544002c2800e050300030042414400042d1000b001c0d800207170086288103000b8054a0054100c8010050301c9282440601c0044c10243c80c405004000c0d080c081007102c0340104480d4007198112821000d10000504100d0070407100700b10500c10 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 289904451 1250 289903201 289903213
    0x1020109020607061508150a2a0207030309050a0e04110102280203121903091115071205040b0304030804031704060510052719050c0a0305060301021303021002 70
    0x50740e950000c2c000c0c03107000d1880005d070304800d800d20301410115078000c49031030752080501000090720700d01725903480300c040d0070b0102d2444a00282502d002050501103543c110f41074050094250f400142402100c1c0696105150b06540c1c105100c0d030740286010754510b00f1440000200480c220070241300ea40c600600c100c07140100204821007140d03581c094121840300b1020b160205620341004010300814540405503d00440541c07808442035084c21020300749500c40ba0070400f404101d029040004c2000742c40e444885004050364883e5611240040b95101e1030300010410030f41c415802d55050300d51600880341b440e1030700d0318241c510440041c0114100300045c00324003e0341c82d0414100f4003e0340701300e1001c0386c141401c100f000c1e0442002d400181c0200c0741e504600c824079000703042c40da03644440308410380c2080d1582c0000c42e0301d44804185040300c4608000c28025201d8054008204841d885c0d81d040286450340c0701010300341d100d402e4041140c000c640364140003510305480303000c42d11a818011241 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 289905701 1250 289904451 289904453
    0x60507050c0c0a063002070c0608100e0112020310050a02130e060901180609090b160f05030c070c080303090c01022103011a07050f0f011d0304090216212010050601020109 75
    0x11b030780c040c4008031054803980c0c40400c00315400504c4150040704190100801c40e041c40ca10005480051180c0855a40d8440d00d803415034906000c08103545a49500a0009240c041480b001035030000c01d0051028039001300006120b071080c040742d8000c80c0001d14042e01d5910301003142d10018109416004220740e030f0440001d6041c0070748910081e0500c54002d101ea14901b0f604c8481c10b0302c0e6111500e0080c040004203095443d5070240850b0350080da030702483d5880d24a90705012000e5070194000074250301c00041403203030000f400900b020302c10350240d0848807040c400784109031281e09501c010307100c00201030006110f84010020400c12481d03030040d2050030881c094603090703d0f048100384240b203581c202030800b1500356030a000c0c180d1101c0320100071201e040001d0f080107540c0e124a102e0400b40c154080f41800000c51040442e47e0201c1d0006400c9601059203c1e6100943d240e000001011030900200001401c815900801e0720003d40b601600c054100850010f01810008010b541195641c9454034 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 289906951 1250 289905701 289905797
    0x301020c07060c170d290a170f010608061b1e0a030e0a0606080c0303090f040905010608150a0c03051909020105040f08011b0201020c030304140a060507050c0c0a06 72
    0x600501e40803004108420700505140001d001b000d800c4100712050038040d5032503201c9081e80d800b1504056100000c2d03040c403268290400341840080061542400d1000034002c500042442c003441400b0101d040740c6c40c102c0c1c6540700c14810086024086402c0c04031509000804c017002c1c00700c040300ca0070080703036607400d00006030704240007074004807001941c03564107004204c0308104192007040c096001b14074033091500042c09104000300110710858880c1b2680c010000290056802084c6180032203a12600341010610410005c6803040030080c0307410580c3c861680700380200346c060102d4401e04c900e186d01407442d13180a803409030020f90500004020003d0b41100e16841306c0010051a00005021608040d0307011049800b070074600110381c018090343c2c4007400080126608654801c00039403690b000801c1c22403c20000343c00141c031003803401c0100001d00d44c1200081c030043d2110020340f01d00301d81c483c007000084010386c015200050040d03444207400c01a051104400540b00040c85514000e03c01644 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 289908201 1250 289906951 289906957
    0x8071b080a080a06080601120f02030c0a032915060a03061703130f0e0609090a080d0f05181c03320f13082505010c0e0301020c07060c17 60
    0x40d000141d84001080160000c3d4802d8001401104015080d1035140c05041d85a49110800c060300ea1140d02d08000304540d410040c144124001420603134a0554904000e00d844e106a080501c1c48418100d4550500c140d0703041d40b034030851007100210440107202041c0403040d00140d85001c1415500c9001003460111841c3e84400545600e000355540d4000703024040b0b8041c00c0350f00000d80c40000d0314060010321400c0c8140b0358000c034250341390011343d580c4498807450441c0020015101c2d041c0018843c042e03079050b410000d07281074484818015502d580c85070641812180810308001e8212404400da081444042141b03079081c035190100300d41100300032a10180c104540d248402c21070301079a000a009180c400d007075010700d12960202c024030744481c0d00306d0311002400e4000c00590700044c40c44c2c02d040351001304c41d0b400172008081410b06682131500c503008008920040e00401c00401c00141079280500840310003c0c049405081414680402034515540045003107400c01c3c05c079502046102a0388001d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 289909451 1250 289908201 289908217
    0x20a020a15090f08040816080304030206250b0105121506090a230a0605100e0904081b06090f03090a150e060c060601080a0c1b020a050604091d0106030308071b08 71
    0x1d8213507291b240c400840e141082d200605100744071903200821a040b8003000f910101d80e0192221a56034810102e1411401e408541d1002d0190041ea01c2e0310a10884070f01040c160350042e40d20034600303042490404d40c0c4600c00c03000000c00d0a52100041c0740303801e00f8a50349412107200c007004214000030b0b107140b104440c116000180b15102c2541081386080c00c034000e00f00182015203d032030400140c40d00040014000045d40f50023001710030702140c208440c05040b284000ca64210f40b820424604220903129401a034113001542b00744402080d0249021048882c00c043c0100400450391800d002e290f284001c40c5403580500c1069445107001d5211040141a1b03620144041e1000d0710300321001401440c7c01402e0b620503545000100314010f0b801441028500452074100c0e80c0c40125440002c040d030340140c005641140022034006007001d4540c101034001e025140e03c0e05500f01d01d4a40160894802c3c1c0710150010711b0300c10214014500841d01040d140c024485140e01418040d128103500b6400286 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 289910701 1250 289909451 289909463
    0x305010b0a031d0307031713170a14071103010c0203032202040f020c030a030c090302090c0309011b090306050604110f030a02090301060f0302030606030609100c05040302130915020a020a15090f 85
    0x80034801c110740b600c02e10350b1149132414440c64071806611032407004270310751500803000e1a0009040060741c1c007840400e813100c108060001e0f80c580c2246040d040110010013880d00039030802801c110054000b100b030724483c0700c442c2c411270140340d840c2e121081c1da008413100a0703800c19a51415807280b040f07280024508241460029595000e01003030050440b241e8210039070400141c0d000c24001a03a50050450308a486000b006850380c56004081d401003468000040d52002c11414003582c003a00182400101c900440d0104900c0d40d40d041070000382c884079127011241d80000c0040032161840300d005180c100302900070041c1880c3c3c114011030708594580c0c120042600d508036013041189020401a98000001c0e0054015402d0880016a84024205070700c0c0004d9100c0405841c414410415100155002031a00a0440d10503006a004007140c2a041e01d000c0d000740501109102140201c4031120071903802002c4a00303003138480d4540070960315a0744c0b107110b4482d40c030b00d8041000c540d40080391f680911 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 289911951 1250 289910701 289910717
    0x105160e10110727050705090907030b0d030f020d020a0f0b040c09020301080c0a080115060f020a02090c0c071d0106031104170c0f0406031a0907080f01020d0c0305010b0a031d030703 80
    0x40b00d400030010131001080030503042500b0000c0e00f40d413002c00d903003031140d00f41c0b007880c010785915900341d0260421088840d0081c0141c81c3c070b8800d16520855a1010010311303000c1e02c0801403500004c0780c0790303200e031720000c0d00c0c0b83c80c002000000a5040118203034840d0044035001101622110b00360240d0b4400e030700402c51584114600096803402d200c0100003403c41c3e10080014458505d17400a5444c001d1148109202c1e103009449215030080c0084c0c0e440300da00600310344880ca0807502e00d450a402c00c0c010f1110a105207200410340c52000464076241c560031a1a0003401d0b8038042e002ca01403c00341c40b0200c0100d0045c0320000e400b84e11034030b0000035008090051301d86d00303117801c0912110f26804509144614181401080130407005800c2040580004081c05d82c0c6a0381c40070002c4c41e044d1141e00c0750215109904d004400720f2419409031035400d200807414000c00b020038000724140c0b40d0078050107042d40c42c1004088895402940003010200c82c00c0d19110038480f00186260940d0050001540860015 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 289913201 1250 289911951 289911989
    0x503090306160f0305130605060f060a121b1205131a0708060118090b03010908040816050603010f09050402010314010f061b0302060c03100e07050a020105160e101107 73
    0x4401c01d0f81d14040e840d08000070300c0c10401038010001210009400f1642c2c0c0d201180722a101c6032421a00c4450241142d075685c0b00840005000940b100642c05009150900c040761601040c2002429a84c2a42c0c40424429a13103a01c50000c0034050071116401d40701c9101a400114240188810448112043c51013440c1545000d0003800c0003d000130304000348101180788100300088044103a54036100c00185030400c0304007013401008002e41c06456041c02150008500c0400102d00c0d00301c5142c44488100c490342d030014032130540400e003d90114420311000a0141ca9060ba2281d41e000d4014540410500a007110a20b0322081c00c0c0c204006400c501007003401510b810184031000ca14050340c81e5101c101c20f0361002903c50b20050b10100c120301000000ca10455202da41c04809048408545072a60404c1107000e0950b0f0b00140040303000d94200400100500c07600c00f0306810021294840d07440144205041198a080c2c0c080c9400c24040c03002d00711070203214200300071400307000d600180f080c540786a = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 289914451 1250 289913201 289913207
    0xd0e0a1a09071a070201030902090a0c110c0102060a180606150e0312180105040e0903090907050c0a080a1413051f050f160501020a080a0c0c080313050309030616 71
    0x4000e080d030980e81c0c800300c2e0810000e18207845600c145048640c109881e2046403004034003030014464080c1d4003035030a00500201c040700d940001070320b015035100c540003030b22881645900d0b401c0655489015030000c1f00000c81e080360540010b1658412050300c4900e0180b10f070365420444016400030204c45140d105e40d48441c0f50441008114480210001d104080b040c601040c1d083c4900e01501d502280300c0c140220a0743d014a058601500754a0f00c4416035181403c007140d5a60800d07200d4a100c0e40c26500401d107400d020308125490b5246801c050540000640c0758404035a00c0100c254042042c044d1242610b80c203110080d02504501000c41203840b464181000403009425007860007a0590f1060360001030b03000000c030703061103130b002c0d20490715901091040413144400c040090065400061180c21155000403802c1c89034075401400c103c05121403004a030b60101e40c910080042408101089405004001d0907c141303201e01d04403407405400c040400e003800410b6840309e80e00100c210801c805560 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 289915701 1250 289914451 289914503
    0x40f1419060612020306160e03030706051909080904090311010c020c12030f12060a03141f050106020a0807020307051005070b1b03010909210e090a060b0f0d0e0a 71
    0x720948003c3d0001882e0000303074482402070b205110346102c078981d1465140c0520035500c045640242941e80301c000f2404c0030030250034103c03802c01515030400e00d0300340f4043d00c5104940d4180d410809071401c140240c014800113116814060b0280100f40d01d141503038040034068140c044030aa40945940200b20040c007030b061140381c80d594020740003031000340c1c82500c1102c03c1d50a1507841600100d130907240c06011464041c09504058210300340e00364002c901103c00030380d0504500650f8070300f0941c01d03a4071202070201c4e1420702640c40160400850900864080000784c801c9034001002c2e10380c2d8940c0c400001e21600f800c0e103003140200d03602042550600808403090fa0384a0780040d49079100b11b850301554900c2c4d1105003d18030b0004d613501081414000280f18a040b6503420403103550115200c0078028040d1034400112900c6042c5100001e07000c0c045a0141504030f5514007a09410410301107400c1142d074004420301c081690b6210344140c9222f00030410a4601400ba4950031008480800c041c4078442c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 289916951 1250 289915701 289915709
    0xf1c020d0b090a02070506040f0c0801060f080c0117060d020604050d0b0f071d060a0215070306080706020c030d080402060705120702090a0c140a0306090e0c0406080d08040f14190606 80
    0x11300c10301110020078004940f60b94095400381541202d5070540c5400d641120864004540c41d600c1e010b0b011a510103604000d8048d1103143c0c088481040b1403d004480f030744210f00504208141004c0440c01904021000c01c0d080c620040c1007905164460002c1039090400600917155520305200b40000b9a100720032454008a01d8070381814044001d06000e480c80c141910028011000025061082403082c050340800140c0b02c0c40c00361260030801d40050192482d8001c5900303500556a002500f01d00000380e082180d08090003a0000d08107414080c1c60500f0001e00c00d03604490708002d0320b0000b41b418037a0060092506d58100d880340418014841028001081c046110307290408051800350000710081c580036104000540c0d42002e01c0d0700704e0241c001603000d01040750900c2d807140840c0c03c0101c3c91314042e03181a2010002586d8841141c1c0e0b962640410800100300514003240104034401000c01d04070f805101c400680c403c2e12074541d46000821501c480301010400c180100300b1640e405004014 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 289918201 1250 289916951 289916971
    0x13051f110111121501082517041a0106110627030304050106030c170307060c030b1009180605060a0f0e090c13140f060c0c060a0c11150f1c020d0b09 65
    0x240b03804c0e145224034002d0441c048003494000c049848005105001005008410b0340424085052520740440600138001e0b420340d0ac4a650400491074510800e5140e5182c030742c4800914403500d800d240c0c0481d550007045021141050b109031080030034000c100441c0901d05c68000020040d103503003002d400540c6240c1101c00c146020b04d0884120a0000068541d2680c10407000907800d59403500603802400320036000c2e034114420321604a0001c0e0800d01c0541212020385803c50f041100040020440d200341c040d441d4000814030a816055201ba0403403091190310341004d040030446a00000e040000881d054000050000380d0121044080c001d000010b2240c1400c48201d408510006003c8003200603c80b0301070f0b0000301f50ba0000d8142008540c8000c2400f0780360300d50320054840003c0c0100b102510980c2c031010b10b02da03940e0300d0742051030402c4444142020800d040826051207804168032152018201c0181d03c9030303060817040700b48001d1008280d2500000740224404041c0003014800500c030002e0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 289919451 1250 289918201 289918217
    0xb0a021b01050a1b151a0409030c170c01111c050106020303010b070c0b0412261902100f0605040e07030209040f08190513051f110111121501 62
    0x19981000030744116003444d080145003003080d114007213601a100c0700094502ca401c06a8441900401e40c032071005040340090450026151800b40002da843d0620000e0020301c0d448182c001117190f94400032410401c80c85c0c810300d49a00c0c041c9903030035502044c50351030f55103200207051840c02101c101d003140c0010f00c051003448558540f4a0282d141e0005110780f101400000900c00200310b00207a201000e4452188015100c03a11001d08010340040544110350004010481445aa40c03880004906d05100d0b11118613100d17180b111010004d0000f00e60804bd0310a04588203001001070084a0074035104500014a251070b1400300310540e40d41c1101d280d0300b900680002e10260700c81038426980917401004022840620340b0b0300c00610702c2074002034000300841120540401e54001c00034101c000c0b10700c100e07103e13458a5908204c1c00042c0c0b105861030919000300d0700c5070f003180070700030480302421903100014144d000001c081c1a59130194441d91001210401004540802d51200d40c4a96a080c60301c3c03c4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 289920701 1250 289919451 289919503
    0x1511150109020c0304080a110109120b010302041107020306070f0f0e240f0301030c08010f0c021e070b07050601032003100519060801020705060a0b0f010e12070b0a02 73
    0x181440060055189060700090282c100b25401c0007160014131012040f01c1c8050542d0610700c02e2620018190360014000c00400101d4180d03c200c01607806d600f120b408901a4659400c01c0300525030b0709000705d00c84030188503d00c0560f43c1404200c3c441c11581c1c507250000c402400c070040041a4541400b414003404483c5c40c10251101008418094100381d4005441101050001064010f00310b942c400040000004000c00c4100e070440d8084035240c0000f80074940e42000c0030029105800030050059114449480740c075086070907a50204000e90050707580c95500e4076a1480c0d154410b107001d441c03641c0704000410411000640c07209001038409120b1200031008800a51200d1a1843d04c820454951300030405445658035011020541d8140c100082596402e195000c2d40040e44140c5550240000081058079030b80500140c2d00c000500300c46035102344400648002c0742d49654280c0041d01d07005507a17450704c400c00001c0c010b021101e454680710140c1410080c83d01480070b0000350315481c2c44440b81 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 289921951 1250 289920701 289920733
    0x140d0206070f0e0d061b02071d06060d0209040605272a070501020c060a1d0a0b16090b07030306030c0b0903030a110c180105031b0d0b0702030d061511 66
    0xc1c80040d0100c4400004c0340d4103052240140c5610000c0c12070244101d1040c114030742c0c00141d541c048070b01650340c0c20003240d0008110a04034004440350340e000a0108600011b01031580c4c000e0221290040000031080d880780e001c64282007000c50050f9003020000307a4906030042110303810364400408145e140c644a0003103641c045007140c02d10362031244072010a1800402000b03406540481c48000d044034214034045841034043d058a00c03299541621000f0201c3c03100d00042103822149812112404054a030304985426011030300302e0200c101b20910002246241d52000100500e500a0b035003c1074403030660400341c0d5a01c07155070050509a07801c010400d51501c0110503183c500009080c00e10595602c81402410000d50f4114540d00142c03401503540490500c0d000d95058030740070b508980d00240d14403d20b10500b0420343c90340c0c0e03105c1142c0040500203229a04005d51250700d80c41500d0510403813001c007405442c2c5d1508412201e80144115091940d803007484501f02c04003c000070002030385414041 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 289923201 1250 289921951 289921967
    0x15090604050907020703050111091810050105090a080106031a0c0a0806040504060b0607030201050414071a0c030f040f051309020d02281404050106090803030a0c0903140d0206070f 79
    0x14042e980c200b0000b00d40d54001d200780c10043da0804000c0c010380b1440c1d100585a0350180703207110701c0f4220544210070401c420013181803241c048a00708011290915005664035089004601c3d0301c2100c07a0740128152034207000f01c10046108515000d1031000340d00041480040080000724030103000d122103010307141c0c0719135840c1e0800425503000030b491b00d503801c0c414050500c904025410240006448003015815407049202c2c5003d040c1002d240d50300400340a440e10036038820031860070107200095284851030390080440c4540402101d00e010b00b4007855000780c3e08a54040045821559005c10450420001c20718203022490810400c094459000983d03102d04d04801900481c6d025481200003600c4500b41c03a901da60303589002c0d1800d40d6802e60350480c0c00403e01c0c0180102c2c01c140002400c0c40c02080208152030000001e1811a07491b41208801400c45059035800c101031184000085070718280314a0701ea090442c05805a01c4030000c0c06450b000000d00031404101c0c220a8480e541c6174000a0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 289924451 1250 289923201 289923209
    0x6123003090615150304080c070e1003060525050406021c0c060c0225030203190507061d10080402011b020609014506030c0203030112080c100b15090604 67
    0xa0f00d014881100c0100301c0e00350010400c80c580da03030000107100502688001801c000c07030002048481c0640c5a020104001c1415a6981000c6003024028000604141c101c0c81d4801d9810071065040039070451052940c0003c220070801180b00050203000f419030500c0285480103d101c1c0710f00103804100070043c0b58940b8003d0142501c0d03555011001114820710811126034060500c02c1040300380c01010065000c030310700c4102d100f13200f1030442910b052400e60384207003003640000181620600c1c09000b502c401242d4440d00300b54405044558415545404e2021000551940c1b40d20f00381c6000d1002510120440700c1014040300303100c55141c01a0394450449101e1182817a111b100c48505c900d6941c400d000302e4107030000c110722007031104002c0d40d00705d450403908137045030010350026925901582155507813180100140c20810040c03003c2000510690900340c0714a0f00c180c500f107600d40040b410012200100e08003251111803070400d40c94182d0404940c000c6141840c3e141404110010315140f01310b04c5 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 289925701 1250 289924451 289924471
    0xa032f030706030f0e0706110d0c02090a18050d050a0801080a050d0e0a050409080a0201061d0123220507030b060412080c12030a0f0b010e09061230030906 68
    0x88004c1e14801a0b4201103c041c00300821540855240c40010300010301816494090784a02c08600b2422407155a40346003481c2c01405150342078031410020006001d240401890042451085000290040100610100c0659585900c58541c54030040468006034008078407680401071342004100c000c200145141032605101d1614440303c0c01041e000d0400d90f01c0960b21519203a003060038003a46900030b100400d1640c0c02080940c0d1a64215650320703040c50960382072146404014801c100e40e0b4190502044c0c1142280800060207000041c4a004070b04d110050030300c21915034030400202806041c0d0814401c0c142403101c5040c0c01d0110300ba81c000c0c0e21441c4000c0b9480e0034410180083c80044800460000c3c05a4001c90410240c00300305500603103082d60303060328058803035540031a584129040c84405a50705505441b8142c00c000804d000070309880e6000244d20b11007000d64408000008881794514000010203441824216001504a400d000c0c588010020000ca0356004546107510400c418 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 289926951 1250 289925701 289925711
    0x705151603090507080a03020f0d03091a0601120c030c09080715180510020d090b070206121b040909030e0306041115070f08030a05090d050f0703020c0a032f03070603 73
    0x2050442c070b4013803070b070348800342c9400f8040e0010709040e40810001c2d09041800c08445034250011070480869040280180500c80c50303103050103107940903002164100b54149030030b043c02c0c0ea00781540e0040306d509c00d2501d000320380c0d5501800109a0000014001405148050181c4620301070268000020050500040100050402034417442102002d40608009440190034080300580a540d40c1900084c1c54013007070040d203000860842aa04403012540c0c00386c005800c010381414000c0010501801b0402219604014071a8007207220740500300404040102140309a0a8140034000000f0b8403140c90080c0c10071f008100105140300c1007142007007001d0b14030141640900d03181d280c0c0b9002d41030b002400361848041e10401c0c4481c48000e103001d0b0f002c5020800c2151561819540d039014203880d007401103403003804500d0202c00c1c40c1001d1701c0c030640240182c0d4528041b41000508030740c0070390000c8407101d00312864110383c00c0c2081c05811011200c44d408100b018090700009035105414400c032000c01d40c880c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 289928057 1106 289926951 289926953
    0x602070f140f04022122020d110105070501020403050c0109060f02070306050c0d1103041106251a090f010e0304030206070215040308030a02070515160309 68
    0x8441400040d1208140844900310b90a40e40d4059800c1c000c40c40d060180c0c440316160310f02d100c440c09111385454480ba170500c4600d00541003041e080c0b05410310050f1281d035141c0207015007081d00401601c40c0100100d0b035600c1441401485540042030000401c1400035105524280c00d81720702000f551a40012148000d0540e0351100591081ca0704002041041d13002c1c90300704c01c0100c550380c5020070740050310058603554500d5001c800350001c20842404210a0341c0038440c4012103c2518020780a84040800006c031075205c20040c804003c04e000f00f02100d529454004100d00c12030041d0300d0b00300c0f0000e0b1190000c811002c401d50030161801c0f80103801008660940380e001f080d0381c0c206007141c1c003400807a886041150103442c500300008000f2030280000703140f00798544c61016039503105502e01941410074512042140b54125000c0c09149802203602c3d03008694a4500050035560b5 = true := by decide +kernel

theorem cover : BRFrame.Cov 289748201 289928057 := by
  have h0 := BRFrame.cov_init 289748201
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289748201 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 289748201 ≤ n) (h2 : n < 289928057) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
