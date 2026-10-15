-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5504
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T16:05:02.345866+00:00
-- url     : https://prove2.me/submissions/40e714cd-8745-4591-8008-0a5751c93e9d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 989748201 ≤ n < 989928057 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 989749451 1250 989748201 989748203
    0x50102030a21060b1b150408090a0f0609060e010e0d061509020304060b03060106090308030112060209040507031e2717070c0501030605011e03051005030d0309020907030e0a 76
    0x100304802d441207006240041414030000c440c1c00d15080b000310b044111000a01500d03480070703800c400c11001c0c5911480c1c0d0b03240411142d8020128480000d00040c030220300030b040880014001d0f012090b1341d8848014144129013141c00400c06a1000348859a40108213a43c10f4409181200000c040d01010400081e00e0403006000103072142903001d40000042c8900b030081c1a4010300715900c0c501420050010b140210040d41709004050001a559214502260560303401188c543d1942c0d10b044e032031140e46604000d003107408603000c1c082c840c02540c4501c01c551080d00641c501054a403d0550004c9100504841d03c0207c01e140c81004241d40c0f5405146081c11300e04811003014000c20380c00c101101181a4080803140900010b481080140f6840d003501100c0c2d00ba01d0600403070341c4910041da00b00f1000d01c1c642924001d81c81850fa246ea20903040300d42c01c0b4036441208450302d81c40f90042410154025150004a0b071a00c000a0440c02e296102c41d520100074a81089003044d240c10640d281e8504880c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 989750701 1250 989749451 989749457
    0x60d1b3f0b01050f0a1d0a0806010e0703060302101e030507050a050c030f04032901060c02010f0e101d090408120714070b220201080610021510080d09050102030a 71
    0x110a070490340541e003140d0b1001601000240c603011000d100514080360108022500f090682e81c0d40c1046c1840010ba10949900e00c0142280740e0904210b01d480100040408040503101d402c0000581c645141300b1f0b03103400700d55448403550302c65013142034021140b0754a241c04040c601800c001610794000203613050010246005560f81c1c014462051a60140301300c6206660b000050000c01c0004200740031f800c584503000c03040054005052200e2282c40248503500114025804c403070015032041c0409507051035541020690300750008003054811801c0c20f040d40100312991030030302c4401c0101600e000120b100700d40b1110a4542039860310740c1800341c4d04a602c03e00000c1c1010911490251140509040c030b42c440b15500c074403007400c20b50180e200980e80083d84e514410301c0000b8960440000da00e40d03d4040e1142c1400341c450605002c0043e200845c49030850040d0001d09059144552819004450044e40c4c039008500307004116040c09501e840080600016541c1000180d03008400e5500d20300141c2 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 989751951 1250 989750701 989750711
    0x71202010c180b0c0a0516180e150a140114010e0a15030203090f0f030a0e0d1a0901110d02071101050c0601090209131b030c0e030606060d1b3f 63
    0x40340c02458054402002407450003039003040c40c6a40702584000d41290340c008510310f1655503203000b07141140c100e6a0103030002e0300500314030315540980380003c80d008110f51200040c0201840303a0543320090a806c0106d1800483c400381c0c00c1503074022140204950200d49a20380b441c40d00340c08002c901280f09581062540100000d101c0708000e0002d81a185140d0065400300400c61a4464407a0b100000c0d890114114000440080c1486018611003d0b40031260900c2800b0707520340c6503d14440200481c103070390b40341c4941d071107900384050107011304001d41036016803a054540f80010440c9185c182c0c00341000014009844086000914181181c800e2240141d8440742800403910358014054002006400c180c4850b480d440c24142081420041d03a0301045191b4400400f1154042400802c3d60b041d842400401c10b18900341c0000e1080d2600000006448101d0200a0601c0810703504203001182984400041c00501401c000c110400211507102500c0685079455840c1440301d00d0080105680d8 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 989753201 1250 989751951 989751967
    0x2a030117010902100804030909110d0f020405040603150e0312040303180c06080406060b03060d032a0b0a0506030102120f10080601150e0301141b04030206071202010c180b 75
    0x81d40302d040b1203500a4040b050030408401c011741356072000e440c103c3c00200ea007031001030f8561551061034840751014084030304c4c0030360502c46800a0401203080768100303642000001503036070755881080f004500c1010414244600000c14070200c4000c181e81c0100d94008020200c4240309000216074800e5040c1070000e0001c0512034035003040c821001004105c0d0b40461404540c0741d4024040c24840ca114840a12101e51030300e11542c1c6501040d150340e0b41180f10603910000185c020b00302004c00304c612034103030240240000301c240684010a181911096039400600206001b05c0c022181e00c66020741c025450101010301001940d0390007891201000c480c140407482d001c002c500001e0040c002e100464016584819281400031042c850501c08106000b490039510b06042c001d40f84500d010302c00303e0b40c45545026040d00d040d078080074280088a003c0002100607074030380024215141c003d44c10304007220f000200c042d01311103241c20a44140070403010000c0c0c0c600c0c0051040300544500b20105078985d008 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 989754451 1250 989753201 989753203
    0x2250e0f1302090c090405090c10260406061706190209040e01141e040506040303020f043f020f010e040e0f0607080112050309100c0f0b2a030117 64
    0x1040000a501a243d81c00340040f001001020708058081101e04010546500d0032060b40c03189050084c540010700e0100d1044e50134096404652440e19121842e810003486050b5900f02600c129800c542165440409100d0450b410940030007040c103500003031840342028079400c694650030041001e400d91f000200c01945407141e030810202c482491000b4040d0581001c0030018210049841d1a45180049000000c411060050900840e0000040c0071541c4030b80e00c1c200d001e98000018503802074000c000000700903000b0340e4608060310314540003003d200d46031055414030f845601d4141280504840c0c049002da50340380c100c0b13084a9802d08001449030340361400b140242000c01c01000c1070b4002c104603450001310100d0600c0c49100c0c19940c100c1d0a07a00c0c0c03146021080c1501c0f001130304075030045c041d5840b00d0a00080d0380740e07408058282180d512140d80e0b0360f40e00740d02c04048210b50a0141c601408903042c5060340b030704070201c4111120540c1c0500d07000700c042580814410440c11003004c000800c00e1080c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 989755701 1250 989754451 989754481
    0x106090308133201030b060f0d0b0d08030a05060d0809040b01020c04090c1d1003060b150c0f06060a140906041b05040303020607030204060804020909160602250e0f 72
    0x601c803d01011000350740c40b03903a03e04410340702c00c002c4990061040003101d0340c4030380716800420000405107400c10b0300c42c50aa520301d0b0400d03601c80003110354990400c1207607621121000c2490788546201d581c0c070718041d85034009854000d80494050503c062031040000c181c1710507a01005001d0390001111039840340100c2c6403a03c48116640c01c103140004c0c1c0010701c220b5002d0342c03054940190f40200c04070200d80c240340760303c00100c5141d000c400290a003400003540507002600e1600c401811294100c42c03174107000d2120761010708903440550020b1004058600148000c0b9032000c021681450780d90f282c803030002940080781450910881034140000c41036a22544030225040004c502c100c14581d00180103040caa105002c10b8001d40309140020b10305034800d008032004c0d42c00c1c0b681d66075030648483e800d00c8050304c0060b103140450300983c0f030b125018940e51a00c0340c00900d542d03401049035000e4805000242181808032280c034281c04031082c0b103c1040c284865800520201030300ba0156034030039100111030 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 989756951 1250 989755701 989755709
    0x50307030f063803010b06090a0e15191e0308030c251b0e060f0103020d020c2d0703050d0c0302120f120603160608070207090518070e010609030813 65
    0x400e10541e00040503e0fa0f007407079081503000300203420038001042014001d03038003030580c8a09042420300182c644110381c181c01c0f0300c0380708040c007400703407481c0006504510102600205071b40e503100400c10420b0782180d0907046203a108a0200890460301c0316a41031000414194480000145910440d0ba09001c800301c0c5c031461210a500e50f5201d4501016440b99003040c050075502c1900010400391040081180100c1c401022507503091410b0005502940211202101c915400e1081a074041c41c00e108508010480c0c44441440210654603051890803042c921410382d0300c004402e000040c0000796040700d511150500f0300c4000c03294030301213151498000c00c0c41c5e1102d80228420350740101c024087c0018912822a035120f95030340501340342c0e5030041d880e0204000160342500b081403500500ea601e82180684c416174400b0b82d11044440b0690f501582da00c0176000b00920b0002d50401d0038003094000e4072030716581400c07a51408900406c100c5003400b000e00300c0e4200041c0e480c100180d425501c0018 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 989758201 1250 989756951 989757011
    0xf2007120501052a0904090c170106030510090213110f0408061006140307030915060e010305010b0d0302150924071101050601050a050915040e10050307030f06 70
    0x40c905280030703043c240c6003000b02c811a4800b208001c2c0180c1e10040c040d01145080c80c0c10b19401d803040002400100500360341d500c40004e0007258550b0f01c020840210613102d000428600e1541ca4028a42002d041d09090198a002c0c40c00b40140d981caa000c46041c54040300c040782c02c3d178440400754800d00c111a407442c0041c03000900010340b49804900d140c8100301071010380300d8039662a58151003103079001c91071240f200c0c41040060310b0b4030301039444044810700135001480088040200c0724100d07985a0451b08182840380c0c010410043c0074041c0c4200c42c07070140c504203529400340ea00a0368070404100b15000700700c0003500045947d0801c2154680ca44c01548034120000700240310324a4801c0180c48a00000d840308a240500d100e05000b1540140410b81d80e003481c0c07404145d0120f800b42c00c030501c519444458210048031520350f40024101034500b9940445a909080c40b41c014510b80c203500050003500040d01c10404500c91811005e45140c200001085141c090054000100d65030b018266407 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 989759451 1250 989758201 989758229
    0x1808030a140415061e0b0d110a091a09030c01050304030e13091211250b030f0f10080604141908030714040e04060902010504080a1104050105010f2007 66
    0x5000101c0c00c03107054a1083c0204020040d280c1e6002e2180b54040140700200503260001082400428001060302010400c0c000075400d444018143c40e45c0d110602c02000108000750610032150112000c8280b4103220010f42c1c502050400030a80341d2085444032070500c480403000500b49800340e000040c860000400030707040144103017443d000416199005580300e0103a161641c102c1806881d840034a034403540020a50417140d81d107801c50b000c00e4003101c0403580d00c1c4d052001886c9140c0c4c101550198400c0d201c0d1416502d0a04060b0185080c0200000e0440040007010414070402068050700581c0001d8408940702e90642a1442c00c00514802c1040c4076040c0468418400350402440c0107100755a26100360090004403140140614010440c440003807001040003c0c0903540840c80d500d1043c103013682000c0d5220b100a0034100c0d10301d0142e65001000d4000704092600d0311445001d00000d00340503011200108000703251075807020000f809d80034403441c150300409040100b036000b050084e24a00d0307 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 989760701 1250 989759451 989759453
    0x705071712030a020a09080d091505120a0f0c02070f152d0216230a170304060e0a03120e03010e10290d0326150907031808030a1404 58
    0xc029172000d1031010029604900119441c80082075400f4900201d070341d00f0120a0800512001c49400c0c5e0f00300fa820300008001498014003008240c40c1f00700d402d0342001410515003d0400d00356800841140119040b2007002e000d10941d0040c03044c29103910944028250140c2c90b4181c03034822400c192505600e07a0000f0355146690007684030100e287c043ea084c1d54248645032450400c01d2258051032401641d00d900144200c4681801c40e040350b6801803484100c1c0d66500c01c00c20a04030030003490605600001018803440350420741080400c0b009442c00c010140c0b55032110900440b00c5040001004140d000c24030b080d42e001d4120040c1030a101d02920064204101500000d00100200448001c0340d910040c03800f40380041e102d0351001002d403520f0545000750354101c5403c40c2c0c070241c0d004640e10b800100d180c141c03800f51145118130b04884460844200401c100086490020022010181009008403015052100b5a21031940c002d40d400c0d260748660b8045000342075801903840c40d031100d01003004 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 989761951 1250 989760701 989760721
    0xa200c060706021309020f04060c020f040905340e0613020f0a080105030102040f0e090a050a08120f0106140a0201020706020708121b1213052e02070507171203 70
    0x21000003e000134040003d80c0e116909030980c0981c440300e02421600f848200400c3c0e0289400c05103452008102c42503120440340040c08560b10b00f441950a54001d175803400514807011103003c00b12240100014001a1001c2c00301c802c0c55581c001d07000c10310035090108240340c4603c040e180c10a02200c405645030011482040019001014900d0025281d1800003072030342018401c840a80713400081111050f81481d001c2103034054040c142030054400c02319203001140c2e0074444220000e12481080c4d98808000c545162b4542c00642001d80c40d10b00740c40108415504404603000142140c1e0040b81ca951041e00107130300902480c0c801070030180c000160001000340f10b00082c40c803240501c000d082640c940310045005110b140d0843c03400c404007041000844003009003425840141d00108101e9410160349541c18a1406540e05000c0032009002c40b800d0380c48101018114110b5120460a04001c0c1c0c03a0680d54001030720902e01c1520096503600c840480c240100c642d001040b8040554a060018183c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 989763201 1250 989761951 989761957
    0x90907020c040605011e030209120a0309140103050906011802041707031707050a081c090b07020c01210c050421030201060b0304022d041814030a200c06070602 70
    0x102e100d1881c00002090b258001d01a04590500e00d14603900140b05441c0c1c260001e52126055640c80b000c451000d8500000801c4902e41c0c2e60300c0f035239440ea45e551418040488502c00300121074141410710040241c0c41c0000904c250456001d80c064040b00360781d10706000c0c0288038a811849514880310351070611940c0000f40407040f41e12a194404001ca014108011a0b008118008000303801c482034502c085281c0c9070191038445503000e031200b0038130310a0103860215100e0000803560031161808002119070144a0211441c0087c00d0003c6820314240441d29880d1170b040c00c8100b0565182d42d0810801d1181c401e560241030400740d40920095000c003441911310150344110700540c00d00d80081000c2119400340c90103503501410f032002c10b01d5000084100b41c0103140c0c150746a4141011090055070f1140241c2074410440c14101541580e1814010561403001d080d030351507940200118400154400007a004081010740604c7d01e84e6260f9140504100540e00d4582d030001012802c40c09000c025401 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 989764451 1250 989763201 989763223
    0xc09041b0603150915060e1302040603050420060904052a071b1a0c0f1911090106170a0603050601180e0106031716080c06040507060503060d03031109090702 69
    0x2035102d0084d6200c02c43c60070740c0d44005050350252004282080385500483d81d003004039000420351601c00c65032501401c101e0f00540d0000c0000f0303884105001c103205d5000081829000203903034491807918000040740d500e00c110402c00e8003c560b610000f4010300f020324050403140307200c4984105540e4010384022441d41140b9026920f0024900c081550006000440c00071509518121000c203401c074000740149410400030f10016000c2c0c010700201001040c00f100c51050202c10440f103000c0c0c26421700c0c0d01110482441d43d40107080c11401032050715007141600700b42441404082c286903803071840000181210703a10042c0b641c4240c4002060716034544402d03180605000108014140d1219016400e07118a48809050a91080e1403a6400741d0742d8002482c04241c0e07481c682026050036901c2a0503980002010381840e0000020300c0200403007440458010089860850704508020b0001541440c0320a030007014150765000c0090002c88690a4807040310006010074402c0ca440314010f0344520010348 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 989765701 1250 989764451 989764481
    0x30506041403040609030b063c06121f030f050606040b0d0b0f1513020c160617101806030c0611100c020309060f1314030c09041b0603 59
    0x140a040702000019141120b20315500d4080b120703c1c54950014561000e0241508600d050701c00004004d0440318200703014030702d590426582004d0515000d20009004034540c4110b07800c0003808112003110f46019007055501d24520003003400ea00101400d80c01941c40107041c0400c2e01500e200b840400300d101072080b04207907010302a0480d0a0100140200c40e100c0013000d103e901c00100340c04101c401007050f800a52801e00c80301c01c00101c00014500700c200c64141100c25000212104072407418820a41060070b081141d415080c11304102a0083c000f500300742050007880e40002e407113091001103000091480306441d101c50242d240018014124502003601d90008101000a9403486880080742050b0a41c0240c42d802040d101c0e40d40c040d003180810304046200c1800042d8030356407440000d08840000705161580d071041c10f40c00c4048400c150f4080016500c0c41400048182c0b00820745030002c407070131030b50301c501c5549925042c1012000d500d1406002c461001002c501c154050388100090302280d2 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 989766951 1250 989765701 989765723
    0x421050609010f050a14130303020c01090503190503060a090902030709090809040b030d2a1e050f030304030903030e030a0819080c0a051603050f0d38130f0603050604 73
    0x7245d2400d50300d181c0e02405210b0300d84000103041c0600c0c0000300d09098171a20b405868109002d46003070958000c00703801c1e40c2c2c42d000040d03042450031902c81c1c0440340c2d15803030900c84c1c00c610b030160006520820610440e101161110f40c04401c555052100c1005410345080802903656281001550b80d081301c038005000300e1404a0050040c80c0000303981159000c1a034a603003a0001800d108410b1501c160440101803849214440c001030084218156101e000c0191280781030315420031500d86034102c0c1107003009030000c00a1001003a88414640250313038150a000f8840d11880c00803d14128460300054000c00010651400f0602000f0a414004c481503859a1041d01c078808100c0b0390b8444d103040000400ca081040103684020b5400b981070340e070700038189141841450591458a58001c408100003e1798035440707406081080c200d6410360b000020006222642a1250501c450340e8001d00315201d40f00d440e030b03c1042d05100d80c014050f600780c008400e000c0b0990740d16100d640c801041d05e04031b82c0c01140d0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 989768201 1250 989766951 989766961
    0x212010f0f021903050f0c0f09040f020306011704050307290a0b040b1c022e03051e090601180e070807060201110309031606090602030907050f060a050421050609010f05 74
    0x74002d40c0e0081507149038000d03980c7c881d070030a0800340d0301150b18a202c00109002003c040d44d05c81c45104c034074021805000d40d40b480c0a0b030004155400ca040508050903000d010300c00420800802d55080070751221500da8602c03a030101e201c0a1310b0214080f4810400380c1010840e000d9941d0300b02d849000411390f414085200c1d03507002c00c0383c03030110313105a0b0101c94030362031070100549042143c1402c1140315243d1f0714450003440c0c040b0040b80e8040c0840c0c0001c6034441d41403105079825607540d1844204200f04207601410b112040c3c030f4640c501031040c0700e031040c01c13203100c2c0b8480d040a40c002503829500408444281d0b6554510704d880c2c0101d03101d940055480e0050111f4000607901c2200d05c0760b01d04801461a18041e1000240b802051301d0013a1109540c80741041d000074900d100071030107403081d20000c04503589080200409e0200750324029014410900c0130700308083c0c0090a0b0340c10b84070b4441c3c207645841e04c5101c85011030051000041c10351b20414081c40100311040d406040260a41c1d06d0500c2150f40e0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 989769451 1250 989768201 989768207
    0x30f070608070f120b04090b07030e070b1206010e030106081911010f09170a0c030f0501050610090603051e010e011802090f010521070509190f030212010f0f0219 71
    0x15100440300881d13011800c51014040383e6104180e03401004000150340002070303e40070f0040c40200d0b480001302c1c6d52907200540c1c0e040108030541c000c00400032a1450800b5440342d0650f40032025080b241441072603001881c3e06e607400e41001000d011548202d0f0010100e1b2140200b503848450400c0d11400035038400072172154840c00b01042c8080e6541c80e034025040c502000400b101041c4241c68045001f600403450004201c0c0c2c907031a00860080101f55402d1609081c41d90840d500941041d01c6071007100b05118882e074021782090204c50341401c00003032550704c014030003403900034409195040d190403070700200b08800601c20042c16100012121004025103103407000c101c0c46800406903003c282c041c1e92944540c4150300030320124008030f00b8040c070602007490300d0b2555007050710464027107400454629501c0c200340500b070350b13a000c816002c1040e9a14004617035a2200c02400007900560090b01c40440d144000d411004400c42c03100f204011200540c0c000710000d41040310500c00c1d5401b5480c054082601c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 989770701 1250 989769451 989769467
    0x1914040506010b071b062607120b060706110712020609030f09060705010e0c0102011a0a0b071b060c031101050403020607081515090103050108060c09040b010e030f07060807 76
    0x948000109071a90800e5080c045940009000b2108004c1034040c80c0301104080d40c1000044c40c1d151100c180000610b59142006100380000c501d001602000300001158800782c00b9002002d9548001174840c2c4d48008a007261081c601e0144c038082c100090341c2c4405071801c00034080e2a0090b0300184510b01940f00498407100183c85542003640207000b00c19046552000030320020000a14951401540c0d90b41c003400e4955020706508a90482d003110249560207010705d18a01c0d030b4190760303810002191400140340822501480701e40790804a00201080203052440610750400c40444007a940d4591004003505220501100052040700c920b900751581402840d000d154150040d0400307603101e803401c490703238500201411a0345405a01d200c1c03c0707440c1e500800440c1c040f00742800b0741d140c1c000d00004d4252681a80241e01640c00001080f00d1141c60078140c80070030340708680210703003500d405004841d08485501c1c01503050088d04400680710301c1c0001c00324100d8406855a118680e00c564094407007034 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 989771951 1250 989770701 989770703
    0x20904090828140703050306040b030a0303140105010c0222020f1315031107020d05071d0912070c0e0402150307020c10093501022d03062b0b191404 65
    0x1c0d1050104c840004d01038409190300c00c2d0090b07c000360000810002a20f0300300c9265064010968565541d0750b02c00641c00c0d40e42c09000d0078281802c00d030030180e000c00d003105041030550511020b0504800098085501107448803400c01001a80f525500c0b0f140505c510303080c0c42054004413101c9003a03084140030f80101d204100d51032800d14103060040d000e01440070401d003401c6615003d90038010841c0380114091141c110306c02c0350011102d150008807149003110303061910004481c144159800504030b8850001610171410842046031650310102e45108c900601c01c03860058040108400545e0015168414035421210a03d11518220040d5006502c034001e800e82030000e00002404036808042c00c034003818103201c660500745041c0b07898500b26004009941d1410205221613215910040b440076840c01820000906e0350600c072000035464003440045464000888010910000c02801d00c84502d80d008103007011285071000418801d02102408c254059107006002e0079600700340c1000c24465 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 989773201 1250 989771951 989771987
    0x903050d050f01031112010e011503231f110d02070510050c04170f01060305071d0f0604050c0913051e0f0c1c0e0601090c020d0e0103020904090828 65
    0xd0705610040c0241c0c0034051480c1541b5640701c410040c6400c40910666000f403220012001a40c0d0441c6040c56801080844141000842e03c9008145044c003003241b1070448041c20070329822081e90380c030480c0034040c0940564a03981010a143c061805203070003e00b0000e01c6442550b0303c402c1440241400c441c000d645100082e08248010310141e154600c2c81013402d50b1040403104049864100d05003560915001100c4036008440100114000c48140d543c0d4038264408002d520b203060080c22403c5a001443e562059807154042017008000c0002c42d4120345d8007600d0312280d0409441250003804064940300000d2540c0600b040b202104a0301d0f00d40105c80e540f0704040d0944400c40c0c081d906801c14003851100609424a80c640d13200d0314810340380d04600407409044c496141410f071000301d80c00d001024003550407000708400d469600c02c0844501d80000d003001600c44540002003070040c910b91030010010400025900a040c40c0c40a4815601d4000c10403507092440f0010120b54402224030380c4121 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 989774451 1250 989773201 989773223
    0x40534060813140c090a06060f0c03050a0c02010e04020d050718030302030315040b030a1109060f030c101101240b0a020303010b031b0301180b010f0905061c0903050d050f0103 77
    0x64012064182203c07012080f240c14401810020f43e00080c26070308032150356912582005280c3e004160b114001905080c2130141c0300305900c0252951091740125000c00c00a490b0362821a80030b04284080390002410854882219586000003084141c5106010035071030f08030b0112104117031a69000303503075044d0301860440c0c4a0160000e0102c031040c0c45a036000e40c80315814403464a0800c501d122142c0515955003440030240103100d802c0724050180790140340b1805407500302c1d0320009130b580ca4019094070002d0360200400011144403a42010304a803035424600685400100480b030b002420900411842d400c07942e441004900788034201203c00076070010f200400c500401c04014550000892060060305108050404402ea00980041510252510b586850240140b0550401d50300070308022043d0100203201801a8103644034040c030404001555905203440008124145c401006091140750348601c1c0140c180c1d00580b911035029450600042d52810708050070504894001204000d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 989775701 1250 989774451 989774453
    0x5100f06050f1e0a0206010303120b09011701090206031e060904050705130603061419062d080a2901050607111804080408161d040534060813 62
    0x801e400c046010000c243c104440b1580d2008644000d058400780c03070380a4040d541c107502d805481d1000d0707106420646440c2400002a40d102c0c164454151001d000280d0f0400c4400d01d842030240c0f01c200e000035000b210203c18441000035200305086c004c07003802c00030450ba58030041444007450084030058519441080100068100305040c804034118409000c6422902c940340d210035682e4924168260700d5800d002c200d80c801c0108030703000729400790441c207000c1c26151843c0302000c8401d0380350f81d0381006c4025140041c00200c6402400061000c8000d845080e2a02e0401840c1d146990601d051802164014128200211000d15068400091809050440301d03101d4044603240540a590841220000d454140d004103910a02c40ca100702510790f500c0303042400017402d01c448045404201580750a0500140d00c100c2098100030181803c9e0001c1940c5605140349002c0c80c08440c641c0d8551050045040400003c1c60400f03d000c0c1080004849543c0d0300040315907107801c03107a02445610b0a59000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 989776951 1250 989775701 989775727
    0x605210c091f0b0d0f09050c1003021605010f0b060301080a03121d0706030e16031403210702010c0801030803060108042102030403020f03010603170d1404030305100f0605 75
    0x141c001da400c1d5425000680d9200c0000340c050240e40040803c03a1011610020109450107200132180307255405111001c0c280e540d02c1c1c0d035042d0344404548101c500740da400702200d200b6070681c3d000c2002c0070b0750302e14001c040c1d00f0000d00070540d040e8406140d03410011504070a044c40703401c50303048603500001001074109a84003190000042c0b80e602041c5c40c0c0301c44032a40006401340e86c55141d84c8203e03014001451810070045c04030749152407484400d4001024101c20300b000700000c40704490304130954442c41c036240d04000b030440c4a140c124115105180842600c2e041ca007102c0c1d50300c200d04640081003e0b441070441914100000d110080071000e0420008036194843c078840380d0410700c00c000c1c0035903100c1c540351814807400d4003da41c1c0005900101d410425450b01000a0700405010740c02003103030505545601c81200501605030322203d8001550603100c2090307520101600c1700350b4801900c10705140c5001400703080c1c15100c82e03000040c260008240e02c0d0500c60310f8000c80b4211f0700e445141840b040019 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 989778201 1250 989776951 989776969
    0x70326040b0a0e100e0d020f0f030a030e16030b0714090a210c1d1f230415140a05030606040903180801020703022118220605210c 57
    0x20861030159079401c80c0b0b1310300c25003d020702c914070b018050200c507190b2400c0246403040e51003070005e02d6440030407a03120000003c0b003210035a00306c138640410200c0802012524203d10742c0c48000f510b2000c2da01c0001807245401c140390080620740c1d81c0f51b007046500d00c0410a18001d1004466201c1221402042403a004a103401000f1010a06403030418049485a0141d06543d9000686100202d60020784480220070030750b0f84944043c0603441000c0490144a41e03000c51805044602000e80a4440010030000c1d604a941c400050051002025140403004407510342d228240300c0614100e0412007500e002a586404c0d03c1014000745419500c4c0010080a442200c80c10340c144104c1c01c030304200d10f81141250740c0241000e403001507518121860000d1030140311065448410042c60101141d40c41c21100320340d03078180c12071100d80341740841500181ca03101610040c040c10035039140c62400c0d10703102038200c441210300841da803900508580a21018403814503116030f500340c000c2100c1000c0da241040c00 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 989779451 1250 989778201 989778221
    0x27060503060409140f1e0c120a05060901090c06020c01171302030f0a02190602060c0f0d0c1107060f050304081b1f1802011205071103070326040b0a 65
    0x1140388942900e07813103135400d68600c2656860b081032100ca942c1c60010000c9031011400320288070360956075200242d446800d01c050283c8990214544012411020884003000e59004400e6404a0501041140c024250380c603003141c00c0075503040d0000303406002142c400171588060f1900c07800301c507091444403501c10b001000320452120803204400541c504110410b00ca142810007009000304900400c19000788020080100c441034440c01e22440340c1c0400e55641000d1074142a544454659100e03620500507d0101109145003080051269a11a9001d510f40c182a019100207030348070941102c169400b8610710010800400c041400202e40d400200012041449448040c8a10802d12820026212070007002207912000d081100c0005101e60920564401419941341d00c041d07001900c80c54000400060b469521070014280070b00508006c2400f400721403d90383d5415441ca80601280307c1101c007034140259050181a2918240296602898001d10710306232682d01c048158001e0300c00402 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 989780701 1250 989779451 989779459
    0x60e03120309150703110a08010509090a08070308040c03021f111614040b15220e0601050901171008010513030903172502040c020d0f030b010c0f03030b012706050306 73
    0x1d455004030081c2c405020f12102d59610080036500d060100310f0088bc01501c0b0501c16000a412180003c845404840c282c6505003004c89041e6114201005400000c2c0d101a401c81055124844010708040c0c1240011010303440e542d407080c0244c480c260307403004010f0002020035020318050040d000c005046811350400108003043d0021101e000c0307001618100e020f810030410100700d40700c10302480310007441c1d01d07d03c0030502448103107480344425080c03501502070360500100084014450740b01d2481400d98202c400d041b1415400c0542038684044003921580065518101c0822200403046001d420342c280c041c0d540350145402d586403903008070320100390304150a1040060111749450f141550440301030b01140744280e9403031030061005031442c04081c4801c640294000c40c000c1e541103007661090b100c40e40f8000424801440050750002c154000160204611050180406038160091480c000081c0e90700f848851700340c2014000c1c480ca03220380a100850149007402113a1042d006158030002c010 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 989781951 1250 989780701 989780711
    0x603070506091906030203180303060907260f160201050c070227011503061509150504081c0905060a05041406040b07051501050a1d060607080301060e03120309150703 73
    0x1a03d8006070010340e502c260046074001c0708201c2e400240d08000c001c0c0c6c040e5540654518909940003c46101340140028184180d40c680300b8480361421a8041420403d1503407a038860400c646602e2540d40115502850381c140c07100120720303a03803042c090705002e01c030390030400c1d41465001d500300305c800c00c0c4024140650f4100202540e07203612501031118001c01c2141c80100c001c0020090060039034120748c0054500304807003d030802d244d59015015008440400c1e030240c10040740a0030403940c0d80b0031503101c41a90700c07421f09501c080d1807000c1c890740c40241080d11074020071a9104c082c084180160185000822424801002401c4104401840d00380c0018400d5107090b440354500300141d0080f81c6e0540d110390023080600c480484104a2a002d403e048440c400e000b490001c40c4050342c245488080703820812000415059190702c0191407066501010303403600da41e19848000d04110b40000d541d031080c801c002091002e00190350840703010b10200d0001c1d02e0081d440342b03051100303402c000d000b1108241d42e030b0b = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 989783201 1250 989781951 989781979
    0x203040f0506130218010e06010c0203101103010e0105100c0b0a1506080403080601090506040506070f060e06150d0f120c120504050333040f0c030623060307050609 72
    0x51005901c5080303070200b000110380721401402800c0343c1c0042c1c50003010f05c500b00140300d085558010680d0046003403908051240580c0301007414244007103208202941040340c0c0e850240b44442c09107050b1104a4044241a130303030b03039007001040c0c103030b0800120200d0342c0000b002010270044c0c21a241e01080c075100100d070114203401c00080e511070540c00b4500003002041403100b00340e0310443c856000a42407030160380c61401d00000440302d1186229940c420640059100c003040b05200410041c20780111040007000000d0444640342c44085804d884400004100701070b080c6801c182d80c08489400c0001c1081e1000d00782c0d00d60745a02c01520140040c02281c1444000240801c0c14640250040b9944c10b500c4a14000505146c0003010001881a918005040965100d003803122815000c0e548a000030603100d50504100b4181c015002402c034450b6658040f0034404247c1118103c4281d04885442d1092509105403080c0e405131002581074001000030000c62070614050221203100410f180101822 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 989784451 1250 989783201 989783203
    0x50907080411150a030c091a0c120a091701140a0902030102070b36250f0306020322020a030305030c09030a060603110904080f03070c0f0b100b0a05030402040203040f05 74
    0x10f00b03104503c0784800020545030f0030743d15020340203841c4610706101c03c02504010345c011122034503440e07a40e00700310f01182990095001300107080d21f81400c1c0d404560b88503410100104820114051503440030045031008121a10520900c0c441c21241130074071915441d091311a02c00782600d50000d0341c2c0756400f4401c2c540422100c410701401079016910110142452030340b060317603070001c0010555540d40c0503110312010b4080402c624540161f0404c1040140450000303400380280e403500f112050034101007000c410019141d00440c01814505806803c0c201c0b0400741c1c0346041240c010003504048000c4040000a000c0c2001d0742e000b4a4010703907203061100810100e4034008441c0c03801d540543d281c0344200103200e404800065984801e981c421050702c0c0649500591f0304c502c04648050040000005400910466102000903400190710036410154202503600b11819200070450701401d00c400100e02d0707a29002c8840503401c03611b82c10700f99900c40d000c01000b504000d0055511280207503e01d030014030 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 989785701 1250 989784451 989784469
    0x5061e1602030105070509090604090f17073f2c040e010513031d040f1406040e0c0607020f0a06020d1205150d0609060e01091b050907080411 62
    0x60010200d030003411107004250941c0c001800b21010f10808010b10080c5407280e401c03050b801070081d140424600303a289040c0201c00394481018244c0000788138110390380c45a120091801038015100c0380d09070100880100d04005050b0030701c204142040503428400c00028080207a43c00040c01c248400e94503900307500710408050345550048412080e4200158034061040781e6490381c2000c0200824641800798005a03903d0300d20141c18482c071300300c060000105841da02d441a1801500a08c1840c00312481c40001c0c005d40c81090148950041c00034086003040d208520782c002040303008021503a129000d01100da40700e1403059810002403403045a064440b0b0115000500c00c84d8014090716210f41801410030b403019400c034038031034140024059180c0012840c0d2110403422a40300d00040d0092401c04001e1004072001083c050400b08182032148040d48035964990056a480e102c0100d0324807900e180116a0140c41c1d4000c40c1c810109001502c5501c440e0b5100d8800c1c3c81c40c1e80100318240016040c20 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 989786951 1250 989785701 989785717
    0x705040c09050405010b0703142808070f0c020102060a271a07051908061c0c080d02010e070e06030f010204120606090b24161b0b1305061e 61
    0x16103618010000c9091a10845005081c6291b415040c0601a43d008022460b21000c441c44094040762480305003021403580300c440c1c0c1c1e804042154465000b00064001d0204880c01001310b079003c1d8414060310b000b20300e1000c045074160b01801280d500c2e491007034010444248141c401416402148410155100c0f46c844114010621071409140c05103101e003c8440081c03045042110601610100c40c41c1c5032906100b0040e1810030501d035581d42c80205108110181002264241d145121002e02000c3d00f29501694000020380300c10042e103038006d0342a14142160343c1000c3c2e005190800c02030100b2861607800281c0103080c1d582e1000c0d0450003030309a030415000034421498401c0d48004020403071003190010400c2103018004141c061000074405d183c0c4608000351548452a0860202d104c0c10885502d02020044102d6440c0c00c2c0c10020381407445884011445001190049244804c010681c1d50f00651046072012042c2058148040741c0c00042c00b144040815002c0d181d88040d049010b80030350 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 989788201 1250 989786951 989786957
    0x6050a0e06191e1a01110a022713030e030127020f090f220827041a03010b010305090a0f020402120708070e0603060a140f1008090106081f0e0705040c 66
    0x90054071110665601d12070034258103208007402203418991b0041740218101d501280c883e403a142056002d5495040d500301752030307444803110003005054090b10b41c0c92803000d80a652003018018000051500b2100c00008a20000c400c40c210784621040c0552405201c9101070100c0c0b24881005000c942da22000369400501c0c1d40b001000c000410480c011a9089244111280e0b8124603050300c9245151003841e1000100001d0f181800c5d1140100c0329610710601c1d1b01900c10400c1c44141108000403c8200408902c65400d003a02940158030030b000e081d001d90107110142c20240e0f00c03075079204804440010202d8006d038081c00340c18103200d801240c05100c4c2c0c496444904117442d001a0060004561044842c400c80c0148144046901c50101283c16140740c51980d981803250200082c02000e0702d0074880354098074890b0b03240302480d440310500e80a05840e100038042c0301e495111b503c1c1c45a00349215200706051400780304c0c948445075040030594000000682d481342e80c07640007080c15100c1d51103491000c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 989789451 1250 989788201 989788211
    0x602091203121015050a200c040b0a0b090d030e030106030c0302030c030d02030418061223060f06133c1e020a050c070e0406050a0e06191e 61
    0x801104491540d000c0c500b502e030b40b0905410080c040d559164141149001c01401050f907000850080741e240c000301c026688441c43c13007d440004c8643e00c950704015503000d103040c130242c2246814031402c4507003580c0e843d00c81c0f581004210018040d400c4c0ca1104280e0070000782d0b02008047d03450a104e00313406580518420600c060071401418641248900346038040d5008641140010341c1c0401036400784c50346084d4501d00140000d2a08002d0551a0403000114580400380000c200c2520080c41504401181c00c0303103440451148951981e0040f035810301e80c106201e0006402e40b8104842400d00015000d0000d03000840c12241300b508080108a8240300080800e104240300b40b00c00315603d000025003040c8500c0c0c080720001016440441d04a00708070f900400c0f25213079540510252840550784100300c50a1545d50a480c2c86110010340c5c1c03e036145032815022410542081c010100c40c0d68549005003070640311071611074940401c4c1070350081c00075600d89150244409440003544003e40d80400410 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 989790701 1250 989789451 989789467
    0x180609050c040501050d02090f0702160f06020111130501030c09090f0515030c1c08041d010521031c0f090602030906070c020d080d0605040c020f060c030c070605040602091203 77
    0x2101d5040c0c0102c0c0c81952011040001aa40c41e8912340d8421072001000c01d0342d0311504400d03491320845018110000d40d038090042189020901c0190840d000d070f0b8000c0c40b9601038400710b88958072801c0c0e00c1c1c25003e401e0200070712165000c0c0c1c0250001d001d440c1ba09111866a660a0030200c0d400c240c0c503101c10700c1e12403007480700c84054400c0d0709614540440c082c00060440b1000202c003410ba1460303101c000e00044000e48288103075501628010140410340a5408120a80594608009001c0c0601c5401c60744c40560052400e00f10044900400320015032500321406000240030569020003844992501c039a010742c01424001c428081d0b10403500941c03039041000c1c4190a004006101508200400b115000507030750782d40901c4070070354104125582d245410040c80703001d003515412964200d81015103c1d06403c3d4006046880d4502c40750a40b13140351a41c3c41040305611087d948861000c50511000c4041002d030340c8130640040c40b4800041c42c100b07602d404503daa2014040e100716603000854841 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 989791951 1250 989790701 989790709
    0x20a0c06032408030a110a0501141602030715020c0c220509030a0c12020115060906031a030309100c050a0602070203102009032104060e06090d020103180609050c 71
    0x915406048589004090a0032080b42c4c0d40d020340c400b220104000b000134880c034500e0034800300c040117030840001c0c403407000302178807007180345d40c09965a09903802c017a003581000030704c0070003610140d942c040c1c2d11484511800c2c0c0042c01a41041c004d41105000f5030300c104e03115030b0380d0001c00502a4001c00c00810801750700c507000e00c00c946009024400c80c0c2c00401c241c18680d9404034501d031040b68400320006950b02d0f0248103c0c010300d2100300c200003804280c10086201504108039008407410b036582400030740314441a64000300c2d1a001c865806600c00e00c52603005240c0310b100c013400700c10640740c021004441c0f610741303e24014409500759a0254000380d41029400c4c24852880d401d90204d1060140c0c040d14000f184001c0956109030b0b00b200004280e1410603078051119034110a40403880d41800302d103843c258200d41c0d00c50b100701e001044a46007030f9042070030300e83c0035120115001011003030560b545070015000b400c10000e82c00c00c5038050f01d044400082d518030401c40e030f05025400410800f00440d00f0f00c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 989793201 1250 989791951 989791991
    0xf210c0402120c0f040b0301060306150318023d090f0b071502070506160905010e01090506071407030c0302090a2c0c030f0309210307060b01020a0c0603 67
    0xd000390300401c0004900c2c2500050903800c803000c01e0100f40d0300c402a000014650086401c840000000007000007505036241c1c0100059640002514031a070034400310643c110744000c6007030028050131421810251500ca20901a01c50551390300509421300c0350080c01812003c042c209072940c9601caa10400c440d2302c07029280180040100c856815030406100c1c0741da50089003001003030390b02e0454004d04454030940603104c2e255032103c00c80c4d4490400c0104080b03281e010440010024080502c0014250f1143c590901d8035803044c1c403042c481509050074088240d0180340305555590280c0c20300800008100b000300000c40c06040b0350002e490642c07041001c090000b07050304088600b070007201042d090000d8072007a40960700b0300340440f1018401016906120007403c0c0b4030741c10f00811403000f86010010004050280044401265200c3d0030180c0610f00c0e0004170300c002c3c07161b100740072400005080f07034440b0306039140c140103c4240405079a00c082e440c40d00da07080540000d07100c000d5225090103025a03 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 989794451 1250 989793201 989793223
    0x6030506180a1509020d170d0506100c0609020604050a080a0b241207211a150d0c0f0b12150f04020a03020d020f0702010207060c08030708060f21 64
    0x1602d20300072a512070a201c09604000c20507040c1d0703a03003c0300003155105017003e03905503440489180084c42c0740b19000c00c160000003c24002e0340c03c1400284030740c588000c6a0b0351550050f01d1fa0440581d65441e048024241034600303d800940c2000b02040d2a603484100718002c1c00c1c1c1c1d030001e1206120625208d14002c0001d00905041c208a4110102000005540c07040e0071605481c5000b07002c441e034000ea0318007101d651080c1c00e403010101450318020300312012126240e01a40100503c7c54442500480515045070300c500d4084603c0e00e0003a4902d01400130105517401150955211910744100c0d1b00c1c600c005600083e40001d000070b124040c42c845080c6d0560101c7c8000f42c1c0100c810b800004610108400792407203210300d0740012501d140d5402541580d0b5259135000045440c0c103a80141c03416039900c008428bd01510903a03000162541c4901500c1521a46c406070760340c11512251000d8a50900c0a05100e41c0300480030442c03880e64640c88098901e406071a041c081c0340016899026040c42030700c100c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 989795701 1250 989794451 989794453
    0x306130207210c0b010801050a180809010305090f030d02030a0e2b020f01051005181b0d060b0a0206040209061008041104090c0b0a0e0901050d0b190603050618 70
    0x200450100d05540d8044018a0007200c41c2c41607201203100c100c07503940142900400c03c0c00d0100000c030f2074000540c801407188800c00c004207c58101d00000c98003d240c5620010401c013010091a04194440d401180c0c010112008031551f180344084200d0454100d9032017040310b250b0100401807409240d00514004e245031401400400e550b00000d80348010300142c42c1200118241200c0305107510130440038410040c250000c100505001e212000441210f10400d0f01c60b03228503001c580d07003400ea0b0165038090b0169004507000c0e0084c2d1240302da103170381011103046101641d0700b800003012440c000003024501542d6014140a01e0700f841003120036400500044e010741082c8420350f040c00d80103180b00d40c020741c01c01d070800741c074604820004020b0035074a0740040291007401c0d0300141207019039015200101d4961508070b42e50008009001401c8001d00c45c059202c080540703540c0200c0c2041041542212846548100d0010300c2c500350015a00a603104031011ba00c81c01c100840d002044019000c5080020 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 989796951 1250 989795701 989795707
    0xe070f17070210051512030d0515030307060e010908030f0a0c0f02031c09050a0305070327090209010903140d120e0c150d1401060e01021c1d03030c010203061302 71
    0x604003e41d101d1100400c591031541d500040b40340c0b0600410300050100c00203045620070104018015102d0300010403401001c0c0c2058082220801014041c1307010752400b4000f1401c102071903d42d070000d811659107420482d540c4800d0f01c0e002c41d410500551250603070112480160620301005001c0301d840c43e80050401c4080c0214070b1541790301008650a00010902035a030014400c2200d40060141e0b94005101388111280e5008068100c0d000c1d00e0081c0c000c0d203c04002c0800300240c4a00c0320b00c1c10403100d00c618000c010030700500d80a580a04070140d01031408842913500d80da98000c00340801d9149891640c40300d480f0300c20f010b901403e1003104081c5040e0500c200e40003028640d9841c40388105161061500f803071940c01c0f603c185025901c0c4100903001c144800703440e070002110516402e000d02400900078101480441d400050f0030305140e104501c0740103601c81c90801c1200c0c070b8078101d80303d852801c19054020225641c200080d100e508460350006039241014820030211910403028001e104d4018 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 989798201 1250 989796951 989796961
    0x1060c150c020322050301020a080601110a02090112060b09010306061406091f0c0f0f170a02060f0711120903010525120f05090a03080a290a0e070f17 66
    0x4425650500308100421202132010160107840da202500956055803011400b0126542d016550600078003080e290012042200301230383d92038180e101c40c083d400000c681d0040240c08940450200c130140110030004001c0c0011f4002a00c0b540280c0c81600da007601c0320400d10291200001803610382e84100c03030240c64040b0080c0460022540c0800c21480201f0103504882014024180020010351107070350103003100c0c0c032072602400a40c0c035014140e0f000c012030410300380d146811000701c071000e00303d54000740003030b40d206030000d0381c804401002d5004010010003000c0b041c600402071000c0c90b5050004880e03c504081f4103040c00c503035008006021034111f84000740240c1180607001c00480885107043c0c44100c00f01e0a03203001504a02a0001c4014503000c200070860780080340050800d0b02c030b9980c2501c2500c0340076a1205603048424403180100008996031407a0015070b062882450010f454000065a03401c4040706003103003115403002240000e040000c6459102080b06454035511071081028102 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 989799451 1250 989798201 989798203
    0xc04030b091c09122d0c030605010b0a020c0f01030b1201061502070605071e1401050906070503190b0a0816170111030c090f0333040201020c010c061401060c150c02 72
    0x1380d440040c110200c159984020131164900c07070311001c01e40e5241c55180c1d0400740307010319001030644010380c1e030107160034000305e82403c0075021280510420740c01040d11004013001c001003400c0c07020f08141415134400d40c00c030194942510f100e4907070a11200000f0b13582d00d410200703211071400201070303c02c64100e002c007404140c2d000010340d81e00701d40000c980c514454020041e50440c1a103100302a1000140ca4245040c140f4150082445007603000107985031601d41850648a9000c280ca80005050780e1485884100302c2d594000156504000c0c00d03040d895640715038190030007441c0b421a044120811101341b1a8010034000e07050355201c0d0304000c0065001d401c281c50040d000140040b01880350000301c2c02995514542c1351507001c00010b0a0319582070401c6c0c40c1e003d0340f03448080d07014032041888000d54005010b020710039120325010303000313080300140d22001100c88183c10300c0211649a511500b00040c41da0305100c0b24040c4c43e01d62034548154025082c02c00c85440d114100710903503424503200c040324940c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 989800701 1250 989799451 989799479
    0x50105060d0c181e0c121103180a0b0f040c060e10080a1e0501150806060a050a210b15070c140a050603091b0d0c0b030c04030b091c09 59
    0x2401c003c40707100b115800c00c000740c04040e02c3d0740110394001c01000d038a26502c0c1e20040710140ba94031081c010007402c0c0c00c803000343c0708000021103051100740001a01c5060b81c11121441522220540d41040003d5032029407004003070701d00c5007038207031964104410800303440b0060014019904003a0b00b00040c2c44001102420541507100c20445080080340b1010741c6034000000c522501d41500c0d09002c04000003000030582449043c0345841c0d942c1030301070f5003400f074040a0302548010300668944041001d003070f1070560001c14041d08005912402c250680c420164504144000c03000c0801e031481171a042161008400c82c03000d0f950035042020800140c031540542c000c4602c084650050951000000b50250450307601803034001c400002004614200821303064608d490140d005101600b131041400880c1c007400c40010a070380d06180091101015100182d40d00210f00181c030391a103034890750703041c004410503191540c0b40e030b00c45c2110301308002c0c1c5e80825010508807890103a00c841d10b0b120003030b01269 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 989801951 1250 989800701 989800709
    0x915130311030d09060c050a05070204020702191409010b21040203030d0f02040e01080106061418040609020901020d050a0c0206160b070c110316060509130513050105060d0c 76
    0x12410501054054481c0c0c0303a44205040c140ca0311004401e0403c400752440c00700845101d4901181c00c0d0381c0500607020340e0800600c0d5541c40d81050525801e100003903001180c1030b41d02008210a0b0104d040f1000300d114090004140b042e00c0c542a10418041c0303440701a080b83e4003045050090315071144007858029001c50204140c400162114004a0b085201d50300c162101141001c545180032600b0340c00501c1140c13500780000c846603030398868440c2210024024240080d40882481070728180d0303a0081d081d2101068030090464141380e000504907000d580c04081020340110f1141c0c155a014028640301c01d566051661400540ba40c0040440340b2100c002031090070003003481d4800649400481407402d5120003280b900781040f24000e0411445120304880a07024058807004901700070a065206200d50b000741410340c0e04040080c2c4864011130300481e04002070444a4090a0003070040c0340c06110840c60188403400181801425034400400b024042d0304941c40d41d20004054203111011a = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 989803201 1250 989801951 989801971
    0x715020a0c1e030216122d0f2306010909050a050d180803040f09051503010f06090b090f010308130f1d090610060536090915 55
    0x2220104016561984000300181c203510b406007141d070302c8034001210010010b000b40c0841d040d101e5001c0605001a00742c0c0200c11025140340a00d40010302000780d81d42401d81c00341ca11806c07074a100d070760708540303003d10302e000791045440c108081c020710054520580d49143c00505140b00d0900c4c00100644d1040107216051505a03074035422028800180406076555901c6010360300030b442114002048034121090700c01c805400c0d04000941d0900010449080711601c0022910722407030200b082000303190007418586090314a104403c0b15030f500f17210301607210501c0d4000060250034003010b034040b22a00a1001e000c2c1c4550420700c000c84242030b24441c11280c1c08207039250307034000b05600300040e0040b0740c1c4000d441e03542c080c101042240c030140540c0e03101c04102000242c1552100300c040d50700d4400b61540e200b241100764003031120601c14030080c1404908442c241081800e02d8400c40402036650f19105202e292403040311b241440c059820a4001096600801d10140d520310b81d041000400ba11500e08 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 989804451 1250 989803201 989803207
    0xe0a020a020718020912071505070b0601080c0d380105070204090201031103090f120313030e030f030f031602070605041e05120c0909010c09052101020406050a03060b071502 76
    0x843c5404407103103464050103d0b00031031660b940301652000c50703028070b0103104020b000c040643d900c50000d0340c4000b500941059416259a00156042d580c00740000528641c100110380f61010030380142808212070840742003d42404031000c0031740003007123141c03620821074460180c6526030f03102c02030364580ba404031800140c3c00d08510041c0d001344000f03000001d20b2a004410460011000710f00e09104201d01c000340e4040600c042c498402501c4200c40002e40700a00d80c4400d40805d21a4420480fa081d004d000c88241d0703441d05407080d14507000031180154486000041001c401100c410080a802c001c0c001024000d05101d40a07100f80140d01030002e035140c13180d249540d51803001c0c02d144014180035000b4032441c0340c81d000080c0c480c802c00058038021100c0c2c01c04581a400140f240c0c42c04451207a452480d598103000c2005010707000140b140e418602e02004001c032040080c40240020f01003500d5066a27105210b4010381134810702e034428001c106050024901040702c00049010b40ca146d40d00050f6 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 989805701 1250 989804451 989804489
    0xf060d110f1008071b080a030b0414010f03030e0301020c070611010615050306120c1e030109050d0206010609090209011b05190303061e26190b010e0a020a0207 70
    0x10740040c441152542c010006100811903941281000c1e000c0ca0250317035410b41494000880071001515124010130b980340801c01345107514480d074841501407100804c04502c0105000302510101d50070b800503401d0100e81102001099001058010031300d400303400070360501100c6408180c42d517541d445040d040c03203130803014400308150a5004402503d0500c1e046080782141c0316000307241d0b0b00101c44282c000e224a030300041c103072500014a1001004020000f80c1c4841041c00c60101040c1c0012055070150340325821000014070034014151000141c0d0300601d155890070000902003030351a0310a00b191441004480c105903032003814525485240110050400c02a00d032051402c1d0480354501c0001000700400010140d0580140c0c00321808005903038801000e132000c8403c50340041c42154840a000ca08406803c6c040c1d9907440d50002d4000269102581c0316040030b0751080f42d10100700c2d550403e00c0d0051040071040c0010540158103c0700c1107007868891070b000f9540d42400c1c0200ac020f8608556580 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 989806951 1250 989805701 989805709
    0x5070215191e090501051902131517010b0304030e09040f1b0305100f0c0318020f0406050a0e1f08030a03110f1c0605030303041707031403150301050f060d11 69
    0x702c4200c510750803c00c090211401c2880c02042d0960304055640c8031a85550400c070541e009460342074a001e000184810307c2c04602091030108120701d1018405001c006141001220001500038102c5203c0301e41d5070301d072501c0c0c000d044400f0701d2109840755992a040c040410000c3c0003140c400c95021041d90000c40e10b0b84004524030410354001490780c425003201c1e1401444980145100000c410030900c14260103500940564603c50003c144e03400308401200c01501d0300064030030b00070b6005400002c446417107801041d0121f010381c000c8401031580c541070000752a5061210740020003140560840c11341881c9502d03440c1c0c403408680e03c003090f464424a1050300c945404688103601d041100d80d580d500780c00c041051031500414141801c0385000740000d007509001c403c5a114560200c2030307081000750882d101c5030a40040c0e405500b017110b04200d034586140310398001c40c010b4035014660b0484691842c00c0500b91035006043c0a411521041032200d551241c10382d007481241d10640ca011254400300101d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 989808201 1250 989806951 989806991
    0x40b0703050921010c0807020f0c01120f02040608010e100303170604060906080a0507090e1c03061e0302040c0e09070509220c200a08030403180305010507021519 71
    0x141c40e80014456400034a5030055200205450175502c030007060303554417002644c0307803101d003031000d00c1c213130841030317107858030798030803000012507a00c850700005510350b40c24441800c80c6c020340c1080340441c103007500602c004d00550404640c002c00c1204911441400c5a4005098480d20142c010b0a8401440410300d640e0345d680050f0003130903511608003d89962401d140e030740c48088140589407070207900c03800302d07131304105000302c10f5004010070080112000820641030000300041aa0007010b030b844001044d811840141020481c1e80307110300d00e1b15541940104030841e002407905406000342250380c511035440c0ca0420075413000c0a0309203a0744581e44100801d03018000d10b60031b040306400d1800160401500c41c0d003d100c50041e242c2c1c070321214180c140b08408004207071044480f900d41c8801e00360302c0001c10300ca00a41c3c1c005d100e0316001d5404400101c0030034803110300342c204036020394444d010451142d038100030603035080e0008000c0c3c007043d082c000003d428280c0341c02a030011103a02e07204000b411ba0400d10706 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 989809451 1250 989808201 989808229
    0x703050c0f03091e09070c0305070b0f06040b03010504020108150402070501020d050411030f0a061e0510080c030313090c0509060a0302090103062c0703060b041e060302040b07030509 80
    0x5840d2407001d0400c40688950110840307510480200620441e00444001c59400e84100a4040490351303d600e081610f420308600b0085040150070400d010004a41586850240340e20b00c0032103481d03050940030081503c20b14803102e0f000317030325107402c0002603039114050a40080d07804904590020031080410301a06c241200a001036000092001d07000d80755600a41c815401200d11661040e2030208041d11511451030382c24441c0d120000c40800710702240e0000c1c040d442220344c80c254545000b000f81c1c0545134102d929103000c8802d54010019020b0078881c100300598100d0145162014000e56200700b94054020607104e643e03070702a0351003c28015800c4403801c960041806407161500c0034018080c2d409020300d240000d0900b000002c8001b50b5a00b02e4460041ca240d0240e5040021014050340000c000c011004240d00c8420000301040314800801c05032903d550303110703c1009407001c0094400750507804002010b104001c1082690000c0007a2032071554145072940d501d4071034200081400d903003440 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 989810701 1250 989809451 989809453
    0xf0e041a090f010207051609090201080c0a1808030a02070906080d0c0602040306022a0a020603160215191a010f180e01180f05090d210c08011a0f0706020703050c 71
    0x3105c400740000051680700c0c84100d0510541125100c00312032041c0c500c0144000d000c100c0480200300101360302e00c0544100b09851810462070380c0030003520001c030f12503030b845080241c00010762940125070501c9010091b0084000500880d49442c2d400341ea08e40c1050400001c00c01180e100c0000c02c100790301200c0c01550400010b5407501d4046880c0c180510fa110300c02c04941c4009980c01c2140714010440d2001c0e59001440c05046940d19512041400300080d81c10046000d00e40644105002040c43c0a01070181d901a80c556904501d2502c0100c88291a0962031511011003401c101c2c5c0c1d0002090303600703580d51710b00781e504450650108250341c84c01d500b2420100c11880c002041c5044400041e40c4e003004501001d0100ca02d4401d166800c075070b019126407600750003100c0c02452450003600c903004c560001440207000c0d481e64420020450300303001c1e00000024615401080a10440c0c1d40c001e800343c9011070081d01d8000302d903030b900155110b42e1038001c20310ba401007200350034140520103aa1500c11084 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 989811951 1250 989810701 989810707
    0x20102190203040f120302060609130b010602101805071a16151a0a0b09030a0503070f12022a0a0b0a0c05100b060403060f09050a03090f0e041a090f0102 67
    0x80301035201d40280c0101942d601404000003403a143d441444c0640da60107030003900c840d803a40c1080c000c00550081400c4802d4040004410010b01c500e01168000c04440e806400d8400b40c44800340c0c20382c6d56110700201c0801c03148070100f01107203012502d44115141451b00000196452003011014003c1844003016951101618028041624140001000f802008100c140c03040031800441c901d8004009402c210300780d0051000540b058001e140c41e86004040f55195901a034030b5030704d1948840011105410b001440b1010084140d4110921a00c28000780079000d81010f001003401c0300003d1100505418080620038940f110810440940008280740366910312030300c80070b0445424510115402c1c8a02d00d11821324074450300c2100b811030030082c821403801f403039504c900b000f5010800560900c1591a54860001542004406c81d5035200f519588420381c44c0010f00b1032020510341c00014201001010000021294480c82c05901c1c620b81300c80d200e94541e0194070740790125a12050750158800 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 989813201 1250 989811951 989811997
    0x1e170403020a0513092004271401060b040b040305370f0f120806030105130605041e1a060108060105040501320c06010b19080703200901080a092001020102 68
    0x903041b40e5980c0050314244486041c0300b20003000301c402184c0c04a50030128552210000341c0001d420b0503a84443c400200300c040e160280c40d0446e900c29401803000d6140000c013002000400d12a400c0c152103801204024942c600e290040e004850400d00030105200305082001c0240c44650303005075075007207074000010070803a1800240c942d0380383d1000c00101c1c03c0540040e0603031405016140c802c50f1141140c0100c03c050342c1d00c1c0d40181c02c003d84102c9640b4242c1d0200340715002070000d80280903001e41001c0740c644800020070312a850020740340e00c1c100a02402081020b9810070210740072130308207103402102c414048218991030201000000b0f544040b00d030480034144c80b0500030b06135031101401984d00c942d80c5c900c0111003e1240c0e0042140d4003044003502c0d40c41c20b00540300154040f9107420089614106110030b41d90100034030008071050900483c0ca41a01d50707200c904c10781d00803403a0004100c0c0b04016116040c0300d48040c04600080f00d000f00a40015910039015a10511010f5441202581074 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 989814451 1250 989813201 989813243
    0x30209180d17100f1203030b06031f0906030803160c02040f020901020111041a0a051b0307060b041a04020d0f02040906150507031b0f1e170403020a051309 68
    0x954640e05014070b00780300491000122180030800f280e5000030746102d65403138042680c0c45a41084400d03010705680d080202da807902d8200c015442985854217100b070740c1150100745200202640c10820000d4607114041c0001000320080702e4200c03620140f5201c4500080c8001c40d0070028034a0000c1d042814200907a00a03403480e00580b8104101360004d0000403417070b5001400501441c4111680b040f01d0785070504100202800625207058680740140c908421103035880800f45440c4088001603000103100e5062140f0362159600c200d03005c1303a003403082c01507856a022000024500f154456a40003a010702c803088070b94480b0132085580e68065460b6590f80708140c004016a2050718141c00d40b00c044c0b044040d22031004c803001b140d03160f2101800110644410744408482410440340304192151349408a2210001460003d41d130810f40c6010419528000354a01204036214590a074240410710042c1e036002c00340e00c255034007980d8440c6800003c510f42030190114103409071101e010090b05c01c40c8003407 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 989815701 1250 989814451 989814467
    0x21060b21010e0109030c0212010b03030406110c1507031103090a0e181204230a090b040b03010c050703081e0702390108070207080d050d0b060307050301030209180d 72
    0x4003003008000c0d0141101c0420300f6101c40f9080200090707590325966005140c0100b10071405201e02d0000500090310740040b0745194002d400243c04566141c0701030741030312400c024001e01100141c400c280c03050310341716541c0c5240c001c0b0240101070001413104440800c204106440759580700500c0900d42c542d48209509120384103548080b5403162000800d62941000640714a4600715244114038052921000304100701c0c81c60038041300c00c210444050705560701d0034683c001801d0800780016010000208100403680e41d003500c24080c0e4146806ca0390303501c0d04281a10301050b0103080210302a030313407070400900840000b5411021652040706201b2640d0740000c0d41107240c03041001c004400e641101c001d801011400c043c1c100c400302151017100c0554071032500d45400070000e00445200d06d80340c4041e00c3c10043c100340060700041d0040740412881c01c040c05008a410015650749103141410780c1c0090280c0b005010290003034801c140031800301340c1062100142d6102030000d036602944041070040c1080 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 989816951 1250 989815701 989815759
    0x10509010c060e070b070b10060e0d060e01020f250b0117210405271b1902010e07060305160e03070801020d0606080f160e24070210020721060b 63
    0x81d450340011320400d1030580024149e1310103440fa000052041d40811290040061040310103075110100c4600540d002d0005d40305140d02500c0c01e90f241c200c0f083c0920828001001044403030130b01d0504c01404141040303030f600d0544145144648080304451840d901c1e10070480341d200d42c0b01d091000c034043c00035111000307042076030421211780c245040c0a600030941c144550b020b403051362501c0c5002ca010101d80d00a04010a054901038074280b114018001c20501c101303210200161b516540304d502006004c0c00844040c00c042c0c2010040c1e0f0500c2c020188090030201d00300402c0c0915801441015502000320600a14070a4002e558070b4202130340c1e0301c014003003034407071078000c10fa81d500498100a0b020704c889111300d07416401d042030341000702e0017181d0f400441c00074640c100d074060021820705081c03c094441d6504002c03c4064cda5044e81c41446000c15101101004640211105016480e085071103c1144003c0c10b62500c0740b566542860300003402c1c103a40955100003c0c549031803a4136030040c5040000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 989818201 1250 989816951 989816963
    0x100f02160e040c410603090105010612020a09050d020307080706020c0310111206060c0304060309050d050301150807120501080c04060503071a13031a0f0601030b010509010c060e070b07 81
    0x2803642c894800b4010310101030b40550603840210208101410156444c0848060350001800044002d000c0f600039401030380c01c0982e6035100d00c018884036030803c80320310b00414a034004518140d400000181501d0300c0340a8603204900c4081c01200707545d0104003a001074404682610502075490030080c0d607504044510340d000380035511480d8012040d80c03080f03c1c8102c0441e030100d498039800b928540301e807800c0107283c035600071800d01c14441213a0342040030700050250b50f04c001480c0e007d0760414a2070b0002e00007440c1d040101c2000140800c000c00d10350075920012074141102103031941c100585499402417801c16800b45481c000064042000464070019207040d1010401117031185d09040e26650940911010840815680c03943c0c0c04c00c200003007440f811440c8a030b0b0f03003403501c9580d0a000d100c2d43d810100c420240c01001d011101100740385540d0002824201004400036050000e0b010703001d40340d8540e05200500e4081428031449800003081010614103490b5015240c1c00001000d0300700303800660350 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 989819451 1250 989818201 989818223
    0x408030a0f031103040b190905030a0c0b1b0f1c0c1d0a0614180904052505210a0b07020601090f0b240d1a0f030606100f02160e04 57
    0x181c00d55000300d07806203401101c1b00c040d950304c20b0340864400000403014075180e80e03908901004141e051020b0a009001d6940e442c0d2040e01c1030400500b0428080c0c56a1200700580040280b406003003811521404000d0005986907000c4c041c2010190710070703003002a0410b09120258400c0e81d40701d00819a9011a401c221a161105805104190000b801044081081500491481f0a00d507003e4800d500c030b004542c80801c1e04c502e001c1101604107440480d4150b00640034071035000d40c6038011540c1014070f0104400305030324101c00501d84919509480c3c4c2d55010100d00c0c5041e4950a00c410113555820000c294190704101d84002d40d00d00003441441c43e46490046a01c032030503075138081d5440f0b00d80001c020a03020a510000c0c1c5c85005c1c5444a181d06c002d404100c031202042050040440d09801c03002c03555000d24196040c0a4401c0142101e14400d070410400c204103542c0e14030400b5405001031034000441888244103070301c2d02c0c090070a29041d030198200009006280c2ea00c4540c450780c03007403d10b815 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 989820701 1250 989819451 989819471
    0x3070f1b080c0901090b0d05030d05011a0c0d23030f090c040605090c0d06080f0c040b010314040b0603010b0604030516060f02060c0304050c0a0303110c1c02150408030a0f03 76
    0x40c980481c1582d25a00c0400c10004001c00340a513000700d2040100107200401c0002c0565560786175034403100140c1485502c590040021030b070000f4511002e840300300c1d8414a00b411078502107131280402100c05c82403080741350308c00c1400410880d21030741043c02d99401c2076590405102e03040c000e00d800c40e9100350034840ca00307a645880c01d29009103c1102c9003d00021159217a1000100550b04070070720110b8441c1d95101c0004d96900108103003480303400b12a0240201040040c24001520044004c4c541894102004150703005116500b4543c03141d0403004601460b11000002800341c400c02428941c0800003080102c2840004a0b03507802d0481c102c64201a080c0d40c402054441c0107400504c40056045200041c019850001c02507a120380300b01c5c00c0d1070443d07a2a90010341c4500d940d03002a1700180398043c8020058804016000506004403009483d8580030504168409429407009010b500c20440100041e110391094070094134680c4283c075210319800c0e00052508610040307100020303080c514000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 989821951 1250 989820701 989820703
    0x50603010b280e0328141222050105070308060405070c020603160305090a080909100e1611280602070506010303051e2a15040804141c1403070f1b08 65
    0x16588100042c2d0007030551190f529a206910f1280d11444c281d40140d00075084809400c1c0018076230003000407090b41d48140d60421030580404650065414884200b0111010a410031000c56020b10304032130210301903480002c00c841c0d000b440b41e0000c1d08503002100340815560359401c03010602440e0360f800c0196941c2c000700d903a1b13107240c01d51000d4812041003128410504103020300f5548807a403e00d003050000c3d0b60b170440740c460000440d00b032000d0305000504d00c0d00701c43c0e0100000c0d9140d01e0000c0144020b10500301c0f007041c0e032485800c1402041e0252201d00781080440e40540301840d41040c2640c0032903a6908015202d94054500d00c0c280e03040503122402904c91440623203000c440c9070102580c12070740d0f1034503039810010703451000d03202441810644102c030030068140510551043c1c0303010351541d10703051904203d104441085441034001c0201e001500420406a84801e9040034101603142c0070103a2013030552041d203201811003541107949e40144a2165900c03014000e4606214000da0741c0e0f07040107 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 989823201 1250 989821951 989821993
    0xc06070c060c020105190806010e1807050d24030c0e0f010b0706020c010207030f030501050a1809110a0807050306071b111c06050a05060a050603010b280e03 69
    0x410001039240309001d1079204003820900e207481810034034642655007084500f10745041310004009510002004400c1d40e0144400b040004150b580340f500307040e041200000714000425030001c001021929000d1982c00381c0202c691074600600a003070840003001e60303103c004201e000550709003080040c005410851003418912461280d904910780340d003010a03102c1c056100c04425640700d5005c0c0803090b0070120038070052280714400e488610b0030800340301014059440581c0654070604030b94100700500c104601e810341c0c0c007501380ca0002609034598901140c05048902c15070b6042a00d050010030449400207602040c0d400490440c1c14581c0c603440e040fa110214240e200c844c410000e01c0d00000a90010407a04c4000c400600b0080303020458030417810045002e070b1041e0340440d22a018000640c116200703e41e0003500903135102d0b1a190030000890450710040c0700380d140710400025010648105000b14015280c110b00f039240074011051001000c00e4a03243d403452080c0118181114048148010 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 989824451 1250 989823201 989823203
    0xf0c1d010801080607180b0301150e0405160302090a080f0304030b10050d153e07170717040b0c06070827031606090506092a0f0306180c0607 62
    0x140255680e209041b90510011000000d00d1542c1c0040400c1040002e806140600658174910480c2440501c0080c1900740300e540050282d032511050203214010304c14040c4041e906418090703640c5c2824008258450a42d41c4292560b0041c0809405600c82c0400148112402122503000d10b48a60080500840092040c0c951000c011802900040e1841b45500c1344c10101200c00074100e49071043c42c0d40384010f40c083d0f0740f4404c1040d800129005a8214024003119140300d40369092003500e1740c0782c48644202282d142d0351440040307000001c0003c0380c08240d8500400468058440b0b82c0e07a69140c08580041c110720480c1d00a03040010201403261078070790f00c1903013032580058020411605210031400345401c00c0182e03020400480304440070032204585454821200000c65026a0600c0350910b10058040082030f00700d500450f0441440595030b034408000d0107011028030401c040010800c00b112103490f03070140981400c2000c00104181001e040350608000e030b5240c0038110701084083e00c10980 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 989825701 1250 989824451 989824453
    0x80304181401050f0d050d050408100e0a0f080717070b0105180601030e0102040801060b0c010e0d0e061c090b040209070e0618040617010f1406030309090a0f0c1d01080108 75
    0x70042105151040ca00d1991800240001d06010300a0b200c540c02c0071314011040f00402c40000c1c0030440e000b0100481c2d446c103628000d04009508400310680d40720220107402a241002c40c07406174091200d42d808a50b280c41c2e205103034940c0400c00096101c540d0300200d000b61060320361880005000d0400c01402d4100400600900e64255a1400158014010055514925942480041075108003481030001030000c21000d56103540002d92018255614141c000d80c083e04902414405c860b0000b1b503190540740c00311201600e810081c41e90405c408500030102103000d0910312801d05000359100601d001d90300a541c3c1013056a1810b00079103102000d10000c0e500118100903820100001078580091600d0041c404a5420364680020711042c0380844800c2c41070755038110140752100d4a1007404041c06000707a64240300c4c0750200004e0344a001d1803010b203028021140000300030450561080f00da400000c1420005c01101d02c00003080c040c880002000701c400d981c0d8080546601420f065070498980030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 989826951 1250 989825701 989825741
    0x117090c0111010f1d1e030d0c1806080603070e070e091b13090b0a0f0b161b030c080109050d0c1b0b1c1415061308030418 54
    0x80c00440c2d4406942c031001000303550342c45801036049582d004d1320625110500760000c4d0190b0f880b41d11070500e00401c1d003c0e00c2460498040d1562001c0200543c0c0100803c03010020745465040e50039211211000f9115141404080d004100c00382c0184645004582c00d41c21a100c550302c410741c0141c40181030b01d1100108200d2100141c10b45400c68585a00548400080350b40c8048a512141260014104844140c00304142072004040510404540b03190451b0712600b528079140070710509000a00030901011130020786010503109641081440c15800006007156240b528008034000080d40011030310041c0840c80040c401a050044841043d0403501400340d480300c1034815a05841c4104003100c00c843c1040c980e91042007a0788904008046242a00355a0304443c0c4184101054001403217025610745101c0c010744000c005003091303000c804034124800300100e038000110680603441c000703086040c1083c40440c61110100251049401c13102c101ca2101800c1120001500c0703100b0151903c3c00402 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 989828201 1250 989826951 989826973
    0x7060b0102060613020c030702030d080603061b030f042301020415020a170912010c021b010224070e0409060606030b090c120604090b1e10061b0c080307060506011709 73
    0x103034006c0102e280807400302c0c0c1ca4040390380e010034142407402c0101c40120303d0300001c1004504040c402c182d440401c541800c00b0898000d02410440d00000c0c0803c03c3c1c03610320500080c01c01c2200520261409031180301c5040c04051109440d0217940140a00350361815106030340c00381d660001a80c10f50880c0e00180070a03009141806000d01c940012200d103500c507003070519000c2025400c0c070908840c0400d1364080c00c03561064404601c4041e0071894082d046601103017880b140c0800003034000307000e004207020301c03015a01c50074811640b0300d0007066450342c0030780f401c10f2040070020191302440449985440600205400304100709058108484502e4411410000520a4a100f0810a40c0010000c1c4001400c003890f440707801804504aa046114101128129400520121455502154940c41205d0b40707030400b840104580d44584a07495860000480c0508120b072800746c00000d08100005c0343d88031102c600f0006c014080642d0030501080143c09041c2040050721600f61141540310000d01183d010 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 989829451 1250 989828201 989828239
    0x13061b0503061e1908060117060a0b030f070905090f060c04141809061b03090a0f0510020c03190f0c030e0d020303181201050106020a08071a0106030207060b01020606 73
    0x1c0000350007030118500390400903039680c00c0810801400440784009064217200c0d60916012060308406000189035010840d41c00c0001062503201c403443d03101140080c0a00c000c00d16000345100d9036101030040c20408154031480d948200d2140382d0300b40858118144910301036440749001c1e0340301c5501100400c0240010080e01d80b0b42204108043c012041440d403c400b9003902034000da4084e4404c1c3c01c00428080140c01d4842c035903100d9032039903902e540381d4205a038400360795500705600100101910040030080c40000c2c05045154808820150f5840f40e84003d155140c0d0311070200c45440000c400d030b45004040c0700d1144500c040c00f8649620b210103505803029038941c160f0030300382a80f200c40c007444640161010720103071020919928800b0104a0385404210082600750f80620705603152a00402c0902da00003400c5c05007640000c14103503034018900304142840c1e484040c001e400940603000040740741c1d06074001d00c400e0f40900070801c20240000d00490304c5020645160b907100c80d4000d12034500c40b507 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 989830701 1250 989829451 989829469
    0x40c05030708100803070f0303140709171014070801080607123803070b0c06010e04050f03031003110d0c0513020409090c060305060d0c06030b06070b13061b050306 72
    0x3d01d078106510060741d614510f403860b40441000c461003002e405411003059014000c483d5128102c82243c0c403507290040c801080c0100d03a2041d910014010800441604402d002064614010384014445520750005010103032000341c50342000a00e110000143c24000400d04902541c1d040d61030f500300e1203a619050016007444101c0743e20f01b02d401d00c0c000c12a03d40e1140c08001c944007012085d00d5a41c0f090301003604049a03a841074123040020414543d54034030200f14207042d6204041c00340c0f4070b5242c508040d4605a4280b201c0005032000100384209a1700c3c003d40d520840e0300c200d0083c1c0c40240c0c000d0070b115444030b05c14002008001b4107003061000f4501422a94080c0c0302c4c500b00142401e030f4a00151065a040d0001510748602c844800c1c00030719814000e895110704280d91401c0109642d942c1c24084201600c07800341090b5940801c40740543d5968100c5010030b1b0070515003d07043c20540c50702c0324000318424048030713035514080c09003c0c16180046041f11102c0350fa2036072420f56980c0e80c03e07c00800303 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 989831951 1250 989830701 989830711
    0x712050a0b0a11070312181a0408040f030b0a0606030b060d0e100204030b01090b010203040612020d150b0a0305152202190f0906081504090f0b090d0e040c05030708 72
    0xb68652569604040007500a0000c15000707070381308441110004007960895807221040c3c2c4011815034419408100190920503034240d180441d1040c655850600070b046000c0d540143c0d040b85c900b8100002800f1080861038010202e055040003001d0f542c040070f6044640180001f074004070244078140c02d0781e40d51750001420710401c00541d5014050205080200d82c000d4100712b0f1000c01c004014000c02003d441b41980c0e0030002c2c0004c502d01820f00c00090301d665410440c0444035900001e01e4410440903801c995400001300002d0308195403074400741c0c581504074011400005c2c0c07070140010718011602d011310415080103015846914507015400c4220000100c64420705030702005400400c114034a078002d41078900740c0e195075014410900082800c07407a80e001c1c1e01004001c00c14000640c4403100314450a900450700010548441d10300b02d1551490040007034030f00c0d00c81408100f001100850140000b01e800e6480006000e60310003084100d401c03960b40c5000245050001480d400e00500550341c00c0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 989833201 1250 989831951 989831971
    0x10905060a05130f0b03030f0301030b130204020d05060f0a030804052103030412020d031104170109020405070509040f09050c0103050c0c120d0e060906061009030618050712050a0b 79
    0x2582c071040820203520001d1a10b044403a40c0e00e14034008080725100b00786842c14201d015601d46058070f218840c080c0010700000d0540428500030911203020400098540380c3c8c007800642d11050049500d2000b843c003141d40d036020723060380031083c2903600d09142c0c00c1017542c0e40300c0b401c03600b4581860f0a006444031001c0c0c00c0c006812500d0041c2010390001c2026603c584e105040c15641c4c5041c0c1c0d0002820528085c1c00d4100385401e001d607068096441c40e05a07000d5a030075100000241c210142818007404401b00301079042880c10017405101d96108009040d5210151020f001d10b40002d2610700454070251405071058024200c095203035880b80d040107821005c00100541800c007004040343c1010a14000b102c4189000124144003400781d020740068052050301404003458101c8165444007401045184039202c0c49029a411038090501305014580010041000c0300039100da00d60103880584d420b8540b44641c200000f030102c071040c00c0310400c5510602804052902e607a5041c070791803001d0101541 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 989834451 1250 989833201 989833219
    0xd05150114010e03120c1f020406030e150406050c0f0a1101110c121b120d110406021e160609050312030919150c0201051015050715020c1c0206010f0e01090506 70
    0x5800200340d0315000f1400503840041c0e5271454250064112001c642d0140500d0b0400d03203c174a100c003540074075540d02076003161020626980c1c0c820a11580c4c801c040c0c04c1d6001600114242c501d040e030112214040d190054002c122000079071304841c003540100c20702026158881d5500da044100444081c0c44a100031410381e01200c20403c40c1a410710b40d60303d46000c0d103400080380b060704a43c49402054014440010703681d00d814104900251202e054012991503c40788c0940c19500700000c01494000220088440c90032584801005151405522034148280725a02d0301010b080c0c0d65000700c900400b000f4000300001c80c00c4881101c02d1500304007003030361444480080401d0302c440d180a522200b288681c0001505d01d0180d40d40c206c801111b422400c00348492800038030049030071408a4400f10307003120007400804d140c0754400000c0e02c40d11140031602d00902190a8455110045c41e68061540303809485c2d0030381e00d03000002c1c50110340f4030610710784901c2070b00100022615540b1a0b900442d016203001d01e = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 989835701 1250 989834451 989834473
    0x3120603020d080d150b0d0c17070306050f0907020d0815060f2502060313061508070315020a1b06200c0106050f1e0d05150114010e03120c 61
    0x144101e002c1c0350607140d030b800014000340c3c03412071072080d1300040720b4101400f00300d1410a0f07100b805070f0090280340943c01e40c0c0c5d840011181400364030901e250503d4001d21014928200400a01a048500ca0140181054103003d50384d468903000040c40b60021394000c00410900300812984000040d007901d040c03100c1e09409118a40315080100300c88290b0070701c043ea03203401f03900e0100c90400001e02e580c200e4020b14034440c401681c0346d0084030340005092640d04108541030424100500d5104480010a041d01d04001b82444000c5003035401c41380280c890780103d180c694800c509034461510290000b0344507014521040010901052015000b040f001448013401d14031441c01c02c000c02000484118041640d901240c400d0151a000d01010b59414402000200214428010b035030084a428000d60f803000080c0d45a000c4168480e1760800111060000c4850b03190002c090280100e50390401d807110640d0143d4050705114101400c003800402c03000c951419002d0300d42d04480c41d15916406003200d150 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 989836951 1250 989835701 989835709
    0x11a030606130506011b0302031c0903092709050f0d0c0c05240a0207090e0a05060105121207060b010e0a0806060409080f0f0d051302011d04020d020d0f0c1b0312060302 74
    0xc010305202c8d40045503a0010b1083c001049a50b2154402100382880340043c0001c2c1d212103800704481000e41800b094083c581d0709030001c074540340c0c0304410481ca00f0103490103100c00043c0b03d9240c5480102503518100140000b115410440c000160415001d0310040056003060305110441c85000c00b4111034201038001055080d0380312251820050780f014070103100441040c40f0303d0751416091380040c400300c82c3d26510b071034a4103414841c26104d00b480990f0001180e1003031141070303414032000e078405035514168a040c0004041103940300340001e642c220030405d00c0c02c3c860400b00695101500900b066560401004060420082d0481d004a41441500644461400500b080c0c40c0c0c410000d41e00c8401071005901103c5c0014800403c00b000c10550002507608205271010055241d00003101a00003e400304020b8882d2402e980065031001a0201034101d540e4014807016150400c00d1182105070036007160144414a5441c2c112a809140c09000900522a20007141002c800100e05c4584e240c00007 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 989838201 1250 989836951 989836997
    0x106080604020f030f0f1f0902070809030a03020a060e030a1e090509100e0c03070509062104060519060501020d1d030f010e06131205030406020714011a03060613050601 74
    0x8000c081d00807020f010800d11401640e0342d1051030111847d140c0a130000b091001e032840c43c03007202d034519400282c1c1402e0052180c01c40b0100c54026040320306059403860000d40d41c0e000300d40b09980d524a031078910405c0314004001c560101000c0d6a49a082d03401c1c4443e000b4a00c95a03481d4142444102000002c854440002d02ca12407806801031945181c904800f002d4038400052410808801c2040dc004502d90410103894420700c05681880e10b5981560780383d540324881e414000b81c40c10794a02004100001600028815480005a402e1a1440080c4442500c00ca801501c0c0560803110500d040301c0d200752a140022408084000381450140300842d0525036084145032150b51205220140100c04029a9810149043d209884401a5100d0301c0b00f810008204004000000004c1814400e55405075500c603a0400390601c940c8060095050013001b022600391512140309024030900c0c42c010480911604029044118805000384144024800105a50b050100d4482804550b50007000e036 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 989839451 1250 989838201 989838211
    0x50c03101e0f090c03060e01150503150612010609020d060b13090f090204020334022505120703020307060e152a030304020405010f18200a080f0a140106080604020f03 73
    0x80012400702c2104564296030484007442c5010044400410ac103860006012400301c0129002800c10b403100b1002034008030545081310001e40c00d041c8007003a06900b5a004041501303100d4410403c3d1a0fa4034401c0c04a80600018100c42c06d00400c01080900320070340203a4400c3c401c050f000a800c40640c2c3c0040c0880c2c10035281c100d120b100e19181e40700c1d17aa07950111610082c8240511b410080d00300c9500960700c106502084c100d00050110b00711a82040c42c00c0d00001c0c020041604841404100b07125554072280d12059100c1c1c400c100d40001c5450066195207404c40001d031100004101018600b103c0b64003058158141c483c1c0d481c201006018040c0c81e4414106400019680d05c0c1030500400041d264183c0040004900c0c0400030000d034844080c40b00ca4a8550400126602d0000340c1686a481619013295040300707000241d80c1811a84900c115114042c49034240b61240c40321480602102e032801105103105401c2d000602c5040e000e030000c164031190080c07000d482c1c8402c4030b0000b21281c00c01c0d43d07 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 989840701 1250 989839451 989839463
    0x12150c130b09040b0a0e0403210608151006050706020f040f0e010e0901050f0f0a200703020105090a0f0201050d0915020415030504050c101704050c03101e0f090c03 72
    0x810190030703d040c2c010000f000004132001c516803402c140f5040101840030f04001c00703100c40c141e078481a43c101c048481c01140b83d8844104211a580d004964440e9884e095980c040100800060944024400054184c0b000ca607a0203040440654501009501c12685c0c2d400448060100181d100410000c0301d01401e401c0300c040096514085a4820b01080644500e006904250404c03a0403a40e44100c0d0760b001c0c0408054582c00e48030a8182c400501d10001c14003548502c0c0c10601c15031980320781c010010641300e1350007044107035603405180c0c2d00c82c141203000405d400014202c1c01c0141d807140b40a0504862200c1000071400d125546a070711404e00c02d9031680c945500800c080088203500c3c5443c0700c03003559609082c0060714250f5610b0f40c5a8013000a150700ca056020a00f4048500c0355111440c0c0c81850a030541c86414141441c030341e00d01c04044040d20910070050049440070140c060408403d40300e82140a48826400230070f0090b0010722554110039a403600c250002c91a20308a110003075020320 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 989841951 1250 989840701 989840707
    0x6010f0305190503091e12030c0f061b221203090803091305091e060115020a0305040b03154f1d030403030e0f12150c130b 54
    0x450242c0c01c0062204442112600003910003001c6200401140c00403d41101c3e03d0550300381d04400c03249030052070b544035604003003400c0882008100000082000e00c1c1603c003114485050746a03904d503030b450203d42e4041c10100060036084030640e03100c05071460001c0301004942c41301511040c1d02859615610000303000c402c4020303080515401203600c201802c644030145181041020101c5d003444980c5101c1d0400c10b6680c00054003400c414003007074030382072803a4141002a84d5540380030b543d900020702511a80b032402a80e040b071418000920b051003d0b6268440ba41860b1078040440c50507040100510449410300480018a50329210407000c2c1040404003070b0591100101b060803206082c0d0113120f580c02840132142901e10003a40c05651708000b084010034540d01d11080c02511465a000c14401440045000b10030140c2000892030304850984240300140803800030450140040f60400f209030700801da0143c03240c0b100040669016512100161030100101a22550907030180d01407207404d0404 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 989843201 1250 989841951 989841953
    0x9090c02150915010e06010c020d02011806090f06050901080c030a06051002061902040501120216060501170f0c0f0418050d0504090e010b090708040c0f0b030f1e07050a1106010f03 79
    0x43c0b00b03280903005019640e0054a40200080c245981c0c400005e031203160f1005180003160f20921100400004141e12003542555402c1d000d0a11405402044103444003000049042889082541d0391403905075900d00454480300d4a540444e80040c0003843c00d9a121a00070a664482981c08103507036003564020000fa1404190b520860343c600c0418041c154010802000380380c2c0d01000d500c180010782000182c0d6000040f21824074030714200001042c1a00300400090000085c2c3c03841c04c454030301501580c8288000f9504c280d00c460255403115800304100d01004040d09050b44440d115171901102050180141d846003072134000360f000c65a000030000074090000d0102030080008110103d0b000703006038664a400642c11240040161040089040005044c8201c16036000000d001110010751070743c0e201c0c00e6544041d4811030710b5041c2c42003044081a501c0c001a5001e54500020703076a001c2641c1c0301e801e0308840701e901c4500c0700380401500c01e0807210300030824450b242c02480c6620704c0032003192071 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 989844451 1250 989843201 989843233
    0x1b0c060703200a021518100201020a080a092d17091206010308070803190606030c03110309120c030d06080a050c030d090608060d06140114030d09090c021509 69
    0x1400c100d60007681c0042030f600d00140c882c441c2900006011418107078581d020011081e0030b00c400c0c0858240c2c86440300c000003c440340c0643c000c0c05480c4e513641d03a102d415031f2405500f83c00c2d1810b803003006000441c0c01c10385a01a001800d40d035031001034840c54814440701241c9506104802c000c000f040715440015034140d41c0c5c6010214220906643d00180c10b00d980f460300c5600c0790740a000d40280414a0010025030701410790800d444030070a103c8420004907840b40c60080c014201c55103004046441c2000c0364805501c994142c0e03200d00e5000340103088d1600d24402c14940e07030700542e1510b039445c4014800071070207516500840000d021100300078a11441c443c10302a2034607040030020741c000e4201c1080c5401d00c42d48461440c1c01c0c0c98550500c00040d4503148042600004400d00c050807041c503182503e0914038001d446a0304034ad200320503500b0078981c203400f05074592894003000004611250802c100c08401500004141c922600555404005800221f00b00c0b48045440c1080754111040500041c44 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 989845701 1250 989844451 989844497
    0x30e010f0b120c0102060a0207060902090106090e39090d1b12020303041202241b0715080a0908040e01031502070b010e0912040f05041d031b0c060703 66
    0x88000501c1c86000300c0d000170352504005802a0315254002503542c1c184003c0d50040e00750154064441040c0e03680d00c03c1c000305200b40500801d041c003404000030074101405020f0f000501c10b0b41048110300301d03041c00c650094400e8a03140c4031980550074880c4e1480f0b542e0f03000f00c250310140a1340607058103074103180024040781082d80022002411200901000da1000420b0780c0685800c0781041d0512805800000da483c10340751085608800000d06800c4092051005442d04a0030840b00310a407450b00b4000390f40714441c074083da0711179108600180c1c4c0c400e48581e10441c1c00070580702e00006c400741d50340c8800350781d64400c3e004607160803070000041082107662040040680800c100c21410007419941e48000040188200d011a00b482c40c041109804241b089030030400d450428603503200c0c4e454104030014909071040500c541d00d0302210321201400c2240d20001b588070301e80510700c2e1064581055400d001900750082d05445100c0140c0240e8507085d0082007003a00130785426000429111098034600 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 989846951 1250 989845701 989845729
    0x4120201021c050319090f060212060109051e04150602030405011b0507031103010e01240801060e0604090c0e0c031518011a0c060408281e030e010f0b 66
    0x699000c1c8005035043c2d00205480e00701d100d242800185a4680705554003920514402800841c407514595080142d241e00402d400018040c00c096241d030344100664140741680f1490360440a207848416203040c00010030b210142c1d000f000020070414203880c1e1100341c10560400005640000303020305c1503680005903e180f80f41042540031244160307640341d03078440000348801010f220082e02600c440b56401e4011402010160008010390b0742e4110000c0c540d801e4984a5151441e405070000c07420b004c0600800e8181e03104001321501c1034071a001404020220084161580c41c001d15001c078041e00c0d0232000306c7c082d039607626400d0b4a034100200d000ca840100f03101d80c07910864a014a0f10f03082c5c4c0700016003034112402d041d880340f503203109100000b689104000584005006d010100420000303400c0c0035080d4964a120303404250051450740f044124400051f80010441c0f502c0c80d1800f46d0781106c901c20321420760789170100300516044000c0d130a4030342c0e89802e01c1906494000400043c00e009186104003 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 989848201 1250 989846951 989846983
    0x29040807060632221a010f1d1504030503040501030605061809060609061c0e0109051507021e0f0f071202041104240206010f06080621030412020102 65
    0x40c0e03088000c54005542948280d490240d95500c10a00380d9132450720840e058603441842c807102d82d41c00d00d8100014505107120f8400038600e1002a800340d4410710451000704610340b0385428040d40c40c0e903c50600e0884840191340306d0740078101a81120b4120000d0401144190015501e0303078240f80c0003400781d44035130700810b000301e0060200e080070340c1d21101045074802050f5101e45031b980306d9201041942c410047c01c9138000e400051110060000e501d5101e41c0b6642901c410080032404d803802c42d080c4d80d40780c14050312a40c0500e440e02010342c40354004c0340c1c000358140126420219120750380ca100c40785204a01d010ba4115100c2041c5010041c4407065444035820041d000c19820480ca40812903864680640600d594080c11301038880d0742400c8070060000303101c0c03110202d0058411401d03105002d0f030681d40180600380001071801c56404405d019282c11307441d1200955580001e020741c8101c081c1c4030022207074642c00049444035040c00240058070800350030a0898040740006072070940300c144100b6403 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 989849451 1250 989848201 989848229
    0x20307051c0c03050a0c061104091d070510030b0a060f0e0301060303091703090301020310031703090c0d060f051801060b192010060f080c010c290408070606 69
    0x15401201c1c50704580c1d03d400d140b9110401401c00300c0755046040001070540d8900301c3c00880080746400540300b100c003d02424850900c5441c000b200754200c02441200c1e503032107540700340040d00c1c1100c60f18441e100e00b0b20340012080c11160000e02c1c070708a145d01c1340c000704100045a1270700c1c41d4010a0b118210780309030001d00c00103240d9600188030300d401d841104a9040700d0b8200424002003442243c2c03030410002c3c0259207a05065501008d1940c0038441203500700501c1e401604141d201000b83d920480704000904800e841c0031050000383c8282c502c089420954400400001201c1846010f010701c050115031520203440d0352040d42181c0c9140c12000000800740010310b220405e002e0703400c40b5214249041d6441c40703003401c00c80000c039420002c90100c50180200801e080d90080c0c3c00f0340101c2d11448500800269180d92458461616200d203e0006610b040b20b0f41c0030440c04d014200d0041072401002c22102c9500420f01050b00f0190f81c201c03100c003400a4000c050200d10b0103504080e0404510300c0003 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 989850701 1250 989849451 989849503
    0x1302030f0a18020d12050403200a27020706020c0f0606030123010b090102120f030714030403020a0308060a0b07060b2803151103090d030c0e06040519031202030705 72
    0x1400072841e00903d400c1c00c005c030250035280304405490003903603c8000200c2140d80441c103200303684001c82c1940d001e48407042c0b00003500e404980590348140440ca0010344a442d800d910030029602040054070030a40800031071090500c10403180140c03403298009031046050020806080d1000740160b003003032091300b5201205000d205860780d03046030b5142c4400e6684110040050341051150000d60110243c0812052030202101c0c4c0110f215081582c1d07218880a881c0a5089180c0000e44014005038882d60a00300001d01610016811010082001c551240d5840e0206420740c0800e20864805441c0c1c9180c4456043c000042d03080d91260310707500d203200608078103070581600540c44007401540c0c5007900d005443e80f03140e000301400843c0d12007030b66503441c0603641140d4509c100f4150000091a12802105440c0b0412031502640e4000381050b103000d181504000128000340102070501c40d000000000003120070241518004082d00a5510b400c8241003207802c11505000c2c8034048009841414 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 989851951 1250 989850701 989850709
    0x20315060310020d1b0c030809030304120503180303011d090a0f120509102616030b1c0606150219031b02090910110f0906091302030f0a1802 62
    0xc0b801c1c0c102100058461000c2040780c00500b2030b41409110400c4842070a000329a4000740c80c0f00b8041c00b030b48400307085856003600076030b0b85c0c8022640a80760030060070821906902c43c000840c0c110340303400f003400409811400124255442030b440503075600c4400402018907500966155070020041d0003400132000651038003a10504400c1c00104103081000244000341d003e030080e81c941c0180a4a46140c05c02c0c03004028100d480e0212100d030134060202c5c040703445241e00401003445105203a2038000d0300e040740e00041d4064910035007040d40c00710315003000700030010014400746540e0307005110215066162030005103214003103403001c1d021900b01c40700c080e09001000f140c0ba090303a940352510304190003245414001c3c111303a90a0081d80860003e05202032420000303001400300e15003280800c0031060304042032400e84281d040240101d142413140d4039051800c3c0010381000140580a101c0c0181d4040311502245e104580581c15191000300784003001c141446404600030a40d01e405c1003008035a0002 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 989853201 1250 989851951 989851963
    0xc10030e100c090e0c0d050f070e010e01033305100912150c120501050a03030207231909050a051512010e0d0903050c030c060403062d090203150603 65
    0x18101e034039858861081441050814020800002d840c2440c0c20030410100072603000c591443c405074140340201d000018692408c0e40904080d4035190f00c08403900c8015212268503c200b41c0c1815501d051130b0070401254210007a4814851580c0030f080d05210442c0d2052030b10b2070b000540200c11040c281d8410b42d0f004051a4240c410340c102500304419035140903440b502e8528009102c0034100342c1440354142d0130404110366000d80090030300c800ea0b20340f81803240d9000b292001500603402403c041000e0b058824092054105810007500030705240350200300c20790780700302c040001ca100300c000070041e1141521515401803600e200a00450070209603d818080c1d82c0d41403d8400c0c02c0f20b0501044115007540040e031031003043e00a84e81140b551034000350181270340c4e200a4500e80035800005104c2c1c90081621006040000c01c138500301030544d150a001029001200c484130300c80010b0000750307001901071034149088590b0300030400d801d5a00c14941007d40000703030100cce12a454410f21400303035000306007 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 989854451 1250 989853201 989853223
    0x2b030e070e040c03200103050105042c030705060c04170106180e07090f060f0902040819060b0307090507030c020f0c011805040203040f03080f07090504091b080c10030e 74
    0x140400316102c9081510482a00380d000801c01110760450000d02107441c1c107101c458202c01d0b01c0030001c0d41c0e610014001134aa04c40300800c402985010241d01d2103020b180082c0d41502032008683c20007007240d484d541750420a4810104210020600704070010365250100c2c0b45034041d000a01a0520340b1580d80c40001080046800c941d8880e201149441c0d003c101c150010035a0712001e01551b0303400b0b0381d5000201a140290510005080d80c0411280054001ca80c1165130220003480303080b81342070914612150800342292266125154128684d8040103001c000d4001806e0010b4181007165020b0111041400c5038015500f01112281d4407a10100301072001800078205541c0c040740e440c041844180036604252b80c01803020041c44280101d46200c0700f0514840d4949030210b48600f040381300002c1c01144c58400142c1100d206004e54102600525006445900b900c3c20442d2060b070008032174034554101c005154005400541d203071030003503055500c090741400c1c03c1000c0d64000c03019507101c60310600 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 989855701 1250 989854451 989854469
    0x21020909010c140906130e150f031e0a050303010315050609060a0e150a091b0c0f060b06070605070c1704051e0f222a0c142b030e07 58
    0x13926100e030b03480e01c608807285908040901ca0782c1c1c540350710b10011002410b558440103040c030103d0351480c034180b511a0241000e030081c010030656180c2c501d20082c0d030395801035a07105809044e01c0d03140001e0041002d5406188600004440e205000314480d00701c0301b00400c503910401d44103003270000c191a80204001a1b80c207042c2101340d0340d41e41241040089001100d4650049400c0800040c0740b0707915030200342600c444900c0c682040c650104111a620301c5400054881c481c13108a038000904150300162103a90068000303402c0442a44810f4203d88084030f0b1800400d1440e0030003002c1141c80c0310304405106414080d41e040c42c0c1030001003a080030848101c0700e0000c0a264071007009903210f82e076018450300e006210501202c1c41c0c2c0068803244030944941103440d0b04201b503607074840103040f502c0010080704804030401d005400c81d00310340080e550340701601d20001d038100350000468140300c0060b10086001135205640c03c002d0555414150408040b010107213000403080542d00e010450000301c6007402 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 989856951 1250 989855701 989855707
    0x120204051806040b33030f1801060909080c060a020a0e0103050402040902280609050d06091a0916080c0f10020312070306090c0903020f1921020909010c14 68
    0x240116000703150242415600c400500844032002000c1c82e108102002185c03100c06494003803801c41605404299224421044c001e4002440e0500c600403c0b00b00701c00460000c02d1440e9140300340b90071951404c800355002d45001684100030101000034039042512020b0444c50029280402042c210059035903504258980011605568aa400840c1c103c0c1c3c0040c1090804179000046070000d615028000d04900300f5034100041c450b0003540114101d8070040c0402e0b4540e0020356811005280c04001125603030038009411543d1210209518414001c3e58001c240e0000c85400c0740c40344003a29803181403160b22000003403915480c0e0b003890812850f000c0d100036000680ca40d02c1070b410340c0101d44034010305502c40e804000480b64180c1080044444072442000b10201c006005c990040407030002a4005409030000209800d00040089100d00a5001400c03540d071540410100603800107851500018030f4034110b0705501d401c810311a0480400f41c001c000358450154050802c0a48540d24001c1c10804 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 989858201 1250 989856951 989856961
    0x1a220b1b07060f020c060a060305030d24031b0909020f101103130e0906070f080606160c09050c030411040c0309020607050d020d05040e150109030f050604031202040518 74
    0x20016220280d602c080140b062401c6200b00d01e0007900807180d01411842204c000c41c03844051131040c00c041c0c03504400607615015101c44110090044000350101e0a03032007507404040d00601e1501e4002a61103401d0380c41d800e0305540c03074008140e00280c00040356189840c08801c0180e4442c611350700414401c0e03c0c214040d1803054400c0d1089190b500c100c207140d010000f40256005442e030080020f42c1c0002c00b5596958a80b841d0b0741d0b030380322400c42c1d00710046121502900380c81809450711981c0141c0081c2000d1401280180e009030550440008480d40412803400344203200ca94018030343c0c003410303c0124a085d494203407900000d80c04032940480c060f5948022590725184a50020071206c0c0e0068201d40c0e803005503241003a610742d800004900140942c1d240c034049184542c041300c0c112120f00703050646a40781c020550f4100c01024468505120315100d00100040c0403051500241e401140a840a40350609010788920440d6840c080340c94410002801035980d02d903a59084030216076240d491590714 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 989859451 1250 989858201 989858251
    0x311010c0b15030105070806010c0f0507050d060e0d050c0a030c0503040f0e06040606030c0917150c1206010e09070c060f1104031502070b01031e1a220b 67
    0x1990000d040000c0400420100d0b0710880d905209040050340200140d41c0c507100100da082000769840c1d800904008401d0000c01d00c070690060145000b403060380c1206589500050703440c11914003c0711481d40fa81516004180103010200c54080a800c00078035041c2ca482d651501c034426084000c1c140200c3d44100c0003404010000d03a409490034022600da44c507111a51303154495412210326104600b001000306266209020303400040e01e01d6205e9464241c00c06810310b20181d00740c030200c1c80900c180280a03142e0701180340c0d0b1740c2c0914261840b650340c6103105400c0030080310008050724148550040000740301d481e40b50b0840e501041c2868440010156844c08401400c0c1481c0c00f100c180f41013110351611b0403506002002142d1041103448151070f5030851040c240c0c020540c000d0040c00341d0100400200d41081c180914810b1308104035008070445590706104500803500421240c0400c1c1d0800c0341d030382a15904070b071082b18100a55806010103903a2041440c2000300f00d0825240036481c98001014 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 989860701 1250 989859451 989859467
    0x140c04180204050a060501120c03110304080403120906171f0602070f1d0a050601051c230f07050d09060608010203151804030f0905030d0c200a031101 66
    0x11004100344003026100c445603444400006050780704501e01004076001a445206050480b041070b161180d01d803400e0310303080c0001c1241c0719805080c551900d9100e2007894602c401540f18900c200881500c0328154108449600ca00300345071014004c095a040c0285904040e91203c41c1680c02c400c0c0020307540303142c40381c02e40300c4c107140400c800080e0f211004914150040b5042050714800c900c119007442d0340314024100400d0300a14030b00150200d81c0450324540e042d40010340d006206041c040d180203801c05c1501c0d1010a020440b0701060703076850f00300d240c00d81200d0072840b0418141c40146094208106604640c2c103019040c3c500b0703c0000504640c04a006401090b49990018410800b00355174409660203980211002c5e00c50065007180c000c450710709640502d81803014205201001d0307840383d40c103450840c00c130383c85407042c454415070000d01941c0c204915030050324159940300940d001d0303180082340f01c00000e548034400060100d0341102034550080500480307400030282d000180601c00140c416103 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 989861951 1250 989860701 989860723
    0x115061e26010905062223040807030806011409010c2102060603100905070b0a18030807140d140f12090313050a1a030603100e15090d050714 62
    0x4149641d62400454508604031049400140407554a41d0704100c0441c040c640340d5a5a44c005002030050540300b60712000300c55818604a203003516001c4904038141c802141c0480f500c5c0e00010303400040641c8003508542048081c2045094215096040b504902072120b807941007020081c00e078014840c50000c0c2845004075000550080e4001d40c400079100c03001103030098021f10400700c0310403641e092849a080084d40010240240030309000c030310310203940a440c0d49020030100c01e1140014861080030074005510810015943c1c1180e480c20400801040c160f0007090341140801c10349450300803021a02d40d107104941907950340c44d0014150401d01440071400e051910f4041048501000040100301050010380d8441c5400d0f84c52080001001d0700b8040c1d50380c884001d80301505048010405550410b200400303680d01c52519080a00444101e64411005580806940310608400805680c0c20001410142c0002a81401c0c00303021442040401449440000000c0704a0f044c1031103403403440 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 989863201 1250 989861951 989861987
    0x3020c04020a03140f090d050a210c260a020a1b0b040302100203090c040f0e30090a120c0807031a010803120c0a0c0203010603060603050115061e 64
    0x1120080d40080061213981c2202c50b0319400d48000c24000014507402503c0707141c800006001600b00540115171a030481c1155605104c10400000781403859a625018401e03800701c400074143d25141d00081c0f091144040061465401101c951a9242c003181c5c01da81c00804e40d03c025a50b071034046011a921913400103040d100602c045000000c002d6000f0406028500035801c443c1000d10000c2d51004a200542c1c5d038010720303808820080d00c503090175003042e00c010880071000903100c2d1a29180500700b4400c0c80c0c1e100d480c6980c002244000403e40c500b5000c9882c11b021000b07003021109404a00ca0741d40a0160341c81c030303030501040f0030100441426101c010b0001801695034a65070381c070f0271244104c480e40e0303210310703041c9850300101c3c0400000090782d518811144811540f40c65031560110b0350f61000c5c00c03850401141c540b214002d0b8a013405004000c6104000001340c0a140d400c0032400c4a0b078407e600b120b400780190f400c000e03d40d8424109022101c83c3d41014104241500c070503220342140b03c1d03005c0a0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 989864451 1250 989863201 989863207
    0xb21091018020a080c0a15080402010c030c0f1511070c0306111b0609011a09060112061e0810020c0303191808090f040b0a03230f0d02160e060d03020c0402 68
    0x112400109400c941805c0680c5c886041e0754486107008004880c0d02c14460006640c900040d02561103488100001402810b08410312011503d60343c802c0e4401200c16940e1015080c1c2d0100011140c0c869100f8403901503480341d0030100a603950b03044900c1148006001c50341c849201c0200323210864122038500c42c00440c0d00324030188848005451301c1d01114040c615519203403151107a2038819030740141900c0018901c0311150f603950019a503c0c2c02c900401e40d0616a688408914401400c248101c6000070110507000c0d580307040082071030418180224a503160060000800c007840010540e0303080b41580491000e007100340f643c5c9000501982d07982c0d07156801c0c103603201010b2040718001800c1c1c8442c141c48e0445101e4041050206440001f000c03076070041c0800c68204081a0440311100045985550000b046c04903c00868a4054240385540c0c1a404c115003c0740b0281e01042071700040115007086180c1c0c107160152229440400910160181ca40c002001007014030070301c03402d03400650003401152 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 989865701 1250 989864451 989864459
    0xa05220b0f1f02060109090807020103090f0203010204140913030906050c160b0a0806150d02070203010603020d080c0706020c010504170a0b0c090a1202090414070806010b21091018020a 81
    0x801c2c00c05058198090301aa00010503068050b018400c0b5207508088020701c3d10001d940110300402500201b903074103002d0180b1030f07001a502030004000500040700e04a460844010070001415070150034208120700031000d4038000780e0022195070032202241402921103030100749080c2040c42c1c4421400081d404a180422a0307201c6401408618120795680c07030050750f0f0310080c031414011802c040000c441003444004801c1c180c580091044600c007400129000780d42c0d03808207400c0c01008608880c1c1d0700000c00c40f01007544003000b00070000e009610042070300c034081000280040c031850190000355003115541040406042050352000e6038004c100403010700d80b4076207201c015048040d40c2c0e4801c0321800400140100e418400b040b80740d80080c003e03401600c4941d81c08920100340da80d403107128090507030009004013041c00894000c0c081041e62684c1d9242e00095004400d0f560f100740c5c414480090144001d8800010304240200c1d49400d00255030301d201910300440e00880b40d0b0082d80100c0410002c1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 989866951 1250 989865701 989865739
    0x4120c05101e0b01030209030a120c020414010303020111030114060a0c05061006090512032205130c1e080a0e0c0a030c030b100b0f09060409020a0203090a05220b0f 72
    0x150710b498208205a411810044059201d1900881d82c10350000c610000070900901085620341d00350b081000c00e9032200e6000c10240c43c1035085c1c00321242007800040046c160207003c0d09140b2030b0019403843c91503042030300300308810200b88a01c502442c4045951107080d03020f8440d54514030b40210403581c0d6440d04a609842251980c0076400000d24400800602c0d42004030540d07441c0b20800b00654180328002c50f03015040c500300031040e007015078403110026040d00d410041d9580001c00c40d00101d400200706c0d0010704045d0ba170302041c120800d44001d440038020381c40354200d40c00c801541008145140f8a48170740c0e16114000108a0303100b004070b000001048080101601120310485000710141e54824200c041d480d098810280b64410800040888841c1c8000814019100a180c90308144e2600a200304a0700880300001c0541e10008501009107044030300c0400410040750b07411814003005d12000000d4100700d40c10803180380c949419605070f640b1096900802c01003c1c01c1110740030080302d004 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 989868201 1250 989866951 989866991
    0x15070834020f12070b0c160e10150f0c05012912030f040312120c0908010b0a050102030f13050613061403061815040f0c09080604120c0510 61
    0x200c0c800c40c072441c0c2c2c400d801d0510302c10000040d40e000380a800e00328a42082012107901c00c081490903400740d14044454030141d211100040c04000500303069901e040144200b0b0780741190001028a604900045080e0340d003d054441140818500f00c05603462505d003080c0500400b501442d550741001d00e8141ca225680c452640c4a0002142d2081d103182645903600c1c2c40c0e00c00c030400720f030341900d08010a102041c6074009048407100750340b07083d504100034400036100319484000e00d18005010000c040184140c240100405800c044402e44059850078001030b40d01c1c0300b1024a015001c0000c43c01d0b400401c80f41407504000c01c0f001d0f10300780d91080d20fd804609000c13183e009020119699000300d4541000c0c07281a24455070024000d07000c060140300980f08084002072506081c0001b00341d010000352694051458200ea036444040b5941c40d2820f40130f803000130650850003199000d40300f000089120719055600c3c55420b41440840b81503141042030034041103055100c0042e080c540003d40c61203202d501 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 989869451 1250 989868201 989868203
    0x90414040308061801030c0b0a0210022205040c09060e040221040515010f120809030f0106080f0114010b070204020f031e1522021605011a15070834 65
    0xf10a4103625014813403922420280000b82860008940c14440003070b001c0001c1c00d485105004070781e8441c007035a0540059074002030120b9244c0c46025102ca01d18090395a002d405050304a034140302c3c00900480090040700280706207402c20501844580b159160755040b94100c9000c8411702e14507612175155440640f5003920f040b10035200341d0903221104c107421041e16058481459001c0300b800d15001c1c40c06013441a5210607200d0050401c0403d549a130200700900402c0d00800010940b07034030342040b06050035001080c852450b4104100c04072680c500c4a00c040c15109000031060301e031700d22400407800034000c080481049420000034004003140c030b16000b02a645003130803030a4040e80d924003070003010100803000b103801c422840e2090741d030380c41080c0d40038260401c9507000600f413020350a0505030100c401d20303058405943d20851030800d620080c0c010040b5000680c0c800500301c20011090184c1d10031464080c112000224030042d80000c0380550607412120f0340c2981c00b1441c200404107031400d00b0450 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 989870701 1250 989869451 989869459
    0x50c0d0c11060c0312060411190224040308070203040f032d1a0106091a160c060f0908060108070308070305040b04030b06130e101d01060902121308090609041404030806 74
    0x40029604e2404d40541403880801d09913160600400310f09d0381c1c4980040010160a5014a6500c4c0103410208a95061f1400619800c080c0e5400c06040c00380800074050540c1e01150400c000070300440c04c0111008007141e50107013002ea400c0714441c41403440c0307007020442142e401a00300940710501103200d094031840004680c00c40c0391640d0b038032815a14098944158203680e18a0020a102c103107460300644031006019070410001981580d0b02e0280c3d481d10381242d80450a10045022555403044010002e455010006c0155504066540e80d903801c6600c801011031100092800806100c0c1d0140d8000384681092140c5480e1a86080b420045040700c96600500100030000000c0c00340d4061100c80e150346002400c50200c517010f07668003a004100e690b0700b02c218080b01c03040e004102441120000d00c10248010380340ca0301103004100c050b00240800d880840b6044028020440020886414001c00c540481d5650f00c1100820302400c885442c220010030070703030b0420051507049480180f155008039 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 989871951 1250 989870701 989870737
    0x1201091b0309030806010806030a020a080619090b062b061d010b0d0b0703060e040506160c030801140a080f0715230d0b0916020c01050c0d0c11060c03 66
    0x300840458541c4500940003807404004035500394010f4000c0c40d00020003070140c0b08504240d80200c4c400d41d046520002681d84010204a0f80740c600040c2d160280280320740a00c144111030f204c0b06003194001e0003017442070500300034801104c03003d120900808400e00d1f1000c4902880c0f82002402811026a50016504110303401c403000001032003980000c50008103140440c80450f25143d845950003400c0344245960f6030b07400b0481d5414400c2c401d00c1035206600500c02c030b01e410f50b00800c01c101140c24940900a05200b91000640c10441440c15030342340d101a2240b64004000041d07060b200740d44402082c0c01041054201e10001046200503900107440c1c4400408611508a0340c0c08240b0021a1402070380800c2075140c007517038000410b01029020000f00e00c1180b40310020301f4207841a030380c030480070442c01c0d040841c85405001c0c4080a0b002400d0041c00c06603a03203849901c0d00018040c490130007600062090030814a094961000107015000f00c1d00c403000007019556940c407984141081103086 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 989873201 1250 989871951 989872001
    0x160e07050f0a0e01030b2206051f030c020109020603010303050a11071d04110604080a050105070305070f110a05100c0e0a0303142110060e01171506120109 68
    0x4104440d100181510024070b03044103944121824214034441604042d01c4403240d40050356101c50f0002440301d600c0110a0400318000c1c2c0c00c003210880e50110740a081c040134102040c1044109046040b04c060030080340102d040e110490042007070b860001c0d031241c0e02000110034035601c00090518400503840d128501186250020740e02c424600c00e101da9420030005844020084604103501f20713200343d040d0039851503068001045500140c012405a034018401c480031701101740100c0d5000061030408100d1414076810080081d44030b00200c000303020580780079042c841c44c2041b030307080303025000001e6a40fa148000c100e030001c0d0640000c410b0004240f4051080c041c9000802c580c1100d9045c2c80e4443c0c140300c0c1464200c0a030700f10007d001154100d030407515441d400c40030001e903c64215001d10060075420460054040401c450307019040190081c102c41c4201700258909801c02c4d060b8042120074480030740062040d02c10310070f50419101801000040c1090b85400018020b140d02a400046a0712 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 989874451 1250 989873201 989873207
    0x13093008040510020a11100b090a0203060d0f02060d0f0f0c0203161e06020a0206040215090a06050f09040f0603020909120a05180d240c0215060a08160e07 68
    0x340c80180c543d401c01c0200184128040e4018071006a040c14440403c0c400a1800390411483c400000d16513a25860440200d180aa0309030307510244c040c0085045042c807101107002d03d15200070003802006031481e00300556440c101036a4408525000511014064000390f4002c1c116882095a40e17500f00703503a0020a500201c1551522541c10114580c608010384421400c079a030280b40001da60140718840b4041200c500041081c80c415400500351800e10303105110005546283d01440c0e84424400d0b0f00b40b5030303038501589046810510f4110789424001c65030380f07164441c0c0c12941c2d038014079211101c02c0c10350759900000c00302c81c000c030b0390541507030f03a188100781d2150380c043c4a829108400304000050349005401070003014840414041071000c0d0100450001224040c00b5100b01c44030480b101c203040c01154000402000e407a02c18043d440d01c012000c1e645142041c0b610b1340d01300003040001e440c1e0315100308042c0107010384c1c3c0440d5043c41101000000e1a00c940c081c1c011030840120000d100180 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 989875701 1250 989874451 989874467
    0x3041a010503031608030703090f0818090412080601030b060d1406010f05120c07152405060f030a0b060301030305190206060a1206060801291e130930 66
    0x10420b00c203da010b00311343d9129640707a48001c00600c141652200301502246100510034201c42c0f00c0c44106541e01c4000860082c0480b0440d4840e2103140207508100001e4202808003a41a01900f010945a01d03050700580181c40ba15818680201010940c0d104841720b94220080c81010305030780005944a6900450301101540b4200b404500c007001145c0c0b442402640c03090b4040c5c40340c0c03c120b060501580d44c0025807074110144035225600c40e00c07894000010480051200d811101040c610649000c1c0459143c0c01141802c007501240480000d011940c0b0340c1080300c10990042c80c00d541c80d81c41c0e24025020b0303009071040c8a40c440074a2081c0005030f00000e50540189801840690501d140042446030700a030800708940c0741713132215000a810741c002d00603c0210100400e002c0e500600031701c0c288214800d400c0d0002d02c038401d403180084030700c0001401612018025130f00c2c041c1e0710300d0454a00c0c0160424210003000c01c03050382c9104200f10f0500100c2c6d0000c81405902d804040350440048410f24 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 989876951 1250 989875701 989875717
    0x90b011d06090a06080a060b120d1224060302040303090609050a030b0a021b1f0911060c0f1504021c05101806330b030a1e0203041a01050303 62
    0xe84500881e240c1d10b0304030042d5038808000000414a1502c072603d40f810728441c00c00c102d4403e074450740507403410300e17010240380007030031031640141601c140c00c20008003d4880c1c01040c00740300d0354a441c86a1090a08a43c000b002ca1103114100b01039a81c3e040b005001307601c103201c19400991111070218003c0e200e031001c001103490041c60100344070300356200c458000e20064a403005c81c42c3d007000070b408d14104040c0c078124140c1007580940700b00340390304020301d002440b19850030f05921308c0d1282c50301c00295180095110309409a4610351501d02c900011481d080344d0b041c0c043c034103100c0c541403031305182003a00844d4403640c4260380d0101d0344102c002c900282403100020092494200400d031141240599120034001c2803e2100342002002640341c00f002c458516250801c1901103001c10100e8001c02220703a0360f00f0507911040d41d0300c00c0c501a1200d100f80809800b805111392600c103040e5040d6840d0b801400c4850801f201195203003024034184464215125000f0f0044503078100006d09803401205542641c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 989878201 1250 989876951 989876999
    0x903300206160f030923010b010c02011707020f060a0b1903110f04021e0705010c170718170307060c0905060909180f03070c090c1e021c03090b01 64
    0x781001c05050f20f0100c00b04815504241d40ca003078450103d250035100d801803000c1e04c103c18040018240c2000d0079280040c1b1800c0c14400a0725140300141d0b40611111003400d88100a412191107141040b42080407034841d00e1500d20620f4240310140616a0105038204000c85032841c45541980d01c42e10590070902c4090b02d0fa40d8584414041410051a502807268000304010724014801c1c0e01c05a01000c00c14410085030800301c0c9000400500348140c2900402c0b5080c560b0006052810003150010700619060400954191130000d08020030304c04809048001c82032030100840c0b502d4580d8070f030021203080d500d41d420407082080742801500202c2c255000034043e140350040c510700340044c5584c064640c41103103444031091100304c1424820505a994858095580d812031800c01c40c0c40d0034040c2d004013030414505070a0540340b9400903c24516980c07035030400040a030000740181d060140000c07081c3e4801c58a10869181150b056000944207071148184041a03626100c08070035402140e40c0c00508 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 989879451 1250 989878201 989878231
    0x80315030628060b0d060503060a060305030a050a0c0b2d0405061303090504092906010c0303050405101a031005090d0e030a060603150609090b06060a0903300206 71
    0x1084148015141d900c003042c400101d4059650720807820264004100760b41a9507449106001c50724043c020039401900c01c0500f480312608645038141c0b248101c2d01c0550078071400082040140d030017045175141c1e0a0f00001d0104007460b1100d052003011648800c0c2010603406c0340d6918003840300c07100500380215004001007100d82c2e42c3e0882011111441c502c01e4041c040c14020000e26541c680c0601d8a42d640f1a595404d0580da034901c04148100303030440d00b40d54019035641000041e0f6440a1400901a01441c02240903116401c002e41424850b10402c542c090900000c000001850481080c041006804075082c82c0f00e603041d00c0d000c1744c40641b0030f05030070340040340c10301d8540f8864940711203108801000c0d034510558581c0c4a808a8130300343c2c0708403500140014180004003841c07044100501c4901c00c00c1c08003280964130070359515001800c8502c2101c003c02d40b0110980328941c880082c42d440202da0b00081d0002040c0034050042d441d8a0425141c03c1940001203840480c0c0140203865060f11070075 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 989880701 1250 989879451 989879491
    0x6060b0a0f2f0a021f08061c0605041104090c031b0302010c0b042306150a15030f11041202130c0f0507150606050a030b09010f05210a0803150306 64
    0x9a0400b500c40b0b120540314442d0000d001d603850814000c280c01c9407070005865160785c10350240400368018400780c0304031400e0290703200307500ca0384445001c040d60101d00005d443e0f9645c43c1c03500441a04406240d000f030301d4142510200200818560241d03070140c0c00d4078820311244d0001c1c050749805800020f0005000b4070003540090080c0004c540c1280c410040035000240050b0881c041014110b06035523250f00c40b105220240014001c030900380e21b000c1e104916007a0070002171540d0b81c070310b003020070307013015503e8009821424695000c42102075100c035069546607a5241244083c027034001e81644540341403140d10761015074610030f5241c240a00d488075018501c085005884035040060192207000401c418460801d01034810351018003050b0300c07400d03195180084010202c071044103034140194180401441076901c800710402c1103800886503030740c5902c61000642119000e0b1805058184501c0b1900020000680040d40c80b81a5803031047d40071001140426550315403d445c4410024039080d1440 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 989881951 1250 989880701 989880767
    0x207030909061a0906190f2309060a12050702030a090902180918060f01090e0610050f031002040b071b0e06041d0a03031a030610091806060b0a0f 64
    0x2c0c00313180080c202c0d4100b04c07128210310700a1240310081c100003049410300050b0740b50400000d418000107010008607501c1080041c0d0001e21410385014401c00000c103450900701c1c0f01c3e400e907102d4441c6600c020300c1203007072004003e5529046040c2840225940c0c28010892603610300c2030710b11a0f0900c0d18110002c000350414001031b114041d02085c0100d0b42c10483c070000c60030821101d07000781c4001400c4c50a40d894103d001080b10422107280ba001d8020005200e288600303251811b0a6400071600c1003120008030700042c1c0391540790280310b0340b45070011078001105a1004080c11807503000e8010744e00c0741042030003100d0740c808981c025121040340c00d00c041740c021f0529500c44c01c001c080b95020f030580452041e841ca8900f904900007100060780303034900342c1902c01090695851503078040e00240301c2e90a000c0d2078098006014054060400d640e00035408043c8110700c1c02c103c030079810940811113103480f03000c54445680503404803008a40c038810410180b620400c00c0088807007101101000c80e1005d01162 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 989883201 1250 989881951 989881957
    0x121503080306011215061b0308041106040f0f050316061409040e1c2307060203270c090606040524040513050a060b09030601031509080d0207030909061a 67
    0x1080c100070041a401d141d812242c840d0024200c0394521710803c252410800609a11440300e6924034880f03051880c400007500000d00c15000382c3d001e4603482110350300078041100e6028903401021014030b810000640504540c0045081d581c06505460740c0b00c03600001807080c2c510b5803051b0f0002074404c00c28107411407450805071415000040004c107004020b0b8420300d01c2c213244800b044e02024824400104e807560850501240c207508e6203107201c0c0100c80003a450425015841020748140d0300040040c151201d604800040310994099142840d14081c030392a03078460440096501a5000c880401d4983c07a00009450455000900090304410720701c8118034032581200c4824098030b010310003c526556043c0c900c414650f64880000341924003088a0016180725503c44986a4410882c0e03400540b401700d0b00c1c03030560741c000048050400b00b1038801401000603280107421010040740c13607002050950004d00c0054003c5d91008880c64450480d442161407030303c1861301d2588900f9008501171200c3e406 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 989884451 1250 989883201 989883211
    0x309200415030602090a080721050712030207030614060603130f0602161e02060912150c07051e1b130603060b1f0c0b130606060f1215030803 62
    0x400e5800c460000c0075801001c9400031030701d1603000301d504003c42c280108160000c099000080025501e0809602a881c204003084040840001ca200c000e1100030441c0c0e2000380380805104031080040d00f0000d441e020903000c2100c081d0304000c20079072103c00d00d045d00d0340607003001003503036240d13031601c0c2e60202ca151940b18085404a004040007001314419102030410941c104076047d0b8440800d00d0b107166080e860030340010884045032040409601c5603002d44400d07420a0b207000c0002030005024520b03118244104c02c84807404401045400d42e1010042c2190038424401c541e1b254084000380b420b20412641c45510541c442482000c00c50004684e1070440000581a08000d0008503108800e0352400c3c0c0058a8050301e41c0440c01203802c0c002840e03495607002d8060508504a41d60b0000d1220280c4840a01500640000704410a1780100e0391006907500490400a0681e0b800c40608240f00c41000040441e001c61110101c0c2c00c0b02e40500000b0707500c0d050b24224420301b15a01d05405400241c2 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 989885701 1250 989884451 989884459
    0xb07020705120c1509120724051303080708040b0d290108161403040c03031103070b0a1109041a15130314011b05300a09020310090c080d030920 63
    0x1000410303c04e05000410140030b40114440c00c0300c5046854440100040f100d0342c027080410401c0000004450782541c0507268080c80083d41c1e41d00c5818080300c0da00a0342c0000a28000001d00d5002e034009a60105102810110000719681000d10884c50315a0140c17070124086014040099150044039100c061039003014206400700c0f00c444001ca542c2d5800c102d80403901414060000c0c024140c0040c0e0412510314944020f41c5000d0b035030358500452840107000f00342950340f95080000502c1100d4261030543c0c80241c010004484201c00c01c120034050b04201d20b000701c040e540088040c11a5004503215125a07283d5008454550f0780c13403241440c0c2042c0703580c0340e9550300d064001100c041120300c09000c0000e60780e103980300c1c566140070a000030140a0000303e003c120b00941c06501103100b25007544130507054000105481d40b400440d040020480610081c50700c1c2200020400c0840c1480c0002d9403465000c0703c3d01e00f648040c0950440321400780c040c2c2200401200410f0042040c0140d80b86104050 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 989886951 1250 989885701 989885719
    0x1031505090f010c051e040b070f0321091a060d030509190b04090b0102010b15030601021006090e1e2802030601090e010513080406050f04030b07020705120c1509 71
    0x1000c281e003107441096904c000114000340c82c0d841c0c00b0510800000c110300303204003030f4076003480e02c00b20007183d1150540080004141602c40800e1500481ea460851008090080060920080250700800e9010030844844030a1481d030345001e1030f004807051164034080d10007610b0b0340450703c4c255069000f000ac2e1a0340244080380354040380c02d40081c000000c05128042c0c90301d45050904100c141c5480e0507000381168900920b149460360f8420070b200300b40072484002982d0307488000040b4107044072145601845070402c00e0016118007184c0c442e145950007941030741d50416040c80c2c000f840316041207014840b544000c400310130f01c940d90400d05030180220124241d180140b980840d0500000740e0005055603920011881041070030301402c1d40c0180342d15400ca103090f61980c1c4141c2030b4040e07809680101b000100d0300649010040342150301440d0410700801c03e41c901820001d51322801da008207130046018002103d20b84034002254101408020402d1a00015075142d400c52600302280f040c0d4000042d03 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 989888201 1250 989886951 989886973
    0x902030a0f031b080301063c0e030606130b0604030f0b06120d080c0d0902130f0621020609010e10020f160305070b07060e030301060201230103150509 66
    0x10019040300c24070411641914903018140030740500048400c5440030341507140c0c00f000084000085a05440d000e0501e18040180303004003021102050108001510103110450384900784102c1c2c10001000550b01e03042841c90100034151501810307512035801641c1e62040c809450419080601c14410140c880c50074250b59891701e5a05040d04d80c400e8650719804c40505c110f508144030521083c0b00d10310002d203000200d0340c0d8014640c0c8001010028103542c00f1442100450461704403982a98008040c2d0f001c840b40081081c009100c2040589410382c6014000910700d02800480c1e00c00c4041c1491650004005400340a0f40d075100c4441141080a1120180c070150348811006481d110a80d00801c3c65100b240d24051420b071031420004003140c0100420030028400050010554a6544c0d0075501d400381460188043d0042042544c1d03036003c040f0000c00c07a2541540510302d0911f2086424041c600705490521018070701780000b07001600c084447c180904c806402c4107810440c80d1048403801c84807 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 989889451 1250 989888201 989888203
    0x509030a0311010f020403030c020d031b05010e010b01090803040905070e04090503130b03101a1e13060302091518130b01030506030601120311100c03091202070806010612090203 78
    0x403095045020039011403042801007004d00c129411091110011880c04c0d0654802030081d000c44e0134000e00c01d19040220500b094828007504040b0100d00141c03010004080c54814040c082d01d00e84001c0a6180030380d80401d5600c03c1d10f00800306e82c000c3c00994542401c000072040034140040c41d0000340120030341c600c075481d11907110713074103081d4003907006903840d4844808120509602070384010b509003014420300900922460080d021140400c040700c0c4a840000d071011030714081d8030052500400084040008403502030001c01010900c400c433016016240e01c1c0942c201d000382c17258144c114001c5501140e040f8016030050a61104a9100280500546e40021000f43d082c3c208107030665107a4048503180e58042c010300e90400d6044000d05819030410501c2d02c81c80a0320f01c400ba0406c1400081c0b000310700c0c0c05124890300038103000350901a4480382c80d8080d0152400342d80c02c6902d404201ea110b0b04841c4003144000039076140e440600030f41d9180c40001c8500381120210080300c09e5076005100b0040e60 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 989890701 1250 989889451 989889463
    0xe1e010f2a0f060506100e04021605030c06010302010807020d1706010c02120f0c01081303141201120210210b033c060903190e0d03020601050406091109040b01050903 73
    0x1224907601c5a601102e4503011058a1000e0903680c054040c11404c43e01c0c641d048841e6030803112069a0040c1c0720b101404920300c0e10340110001078040e010004180003080d4010601030b0584e4004c1e203601c89035441e075210490b5903040340012080000d141d1304107024408a0842c0c03080d00030f08145440c07c8080713081c0d000039100201e19442c141850b80301340c43c0052019818130410304078080c242011480703490300700e1024008801304607004082150041c00030701c998103220f00b079071604c04103407002c04500d603107402585490200007039040e449100700301100580700d40f049000320080c01526206803028444560300c00050425103072140d0f8980140741540e60400300041c500b9062211200c48420420b0300b20108801d0301007601c49880305c075001401040030710040082120318840303098000410036240350398202c4040700c811079001da10590035440e20b8141540010180e06a074422101001510b80d079800880445405090a00c840310082c00101103510b001d60000101c032106043c0646007100c40380000381070203 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 989891951 1250 989890701 989890703
    0x20d02120f07150f050d110f0c030706200a080411030a05031810170a06150809010e03131205160f060e01020c0f060702150a0e1e010f2a 60
    0x182c008078040008107515407611031290b01d01d062150943d62400e900034800d00c42c20410002d404c2e01c0b110344280140742c2d10201d50901002d4614a5220b03600031a03040d480b6404203000f620704a0a002000d003200d00c0d00c031020901510b1040e02d9030b2900c00d0340a000d03078003400d004000750b601c00d00c0c20f0010803a0b03031028011021400e101d58082c5a07201400140302d005c42e480c00bd45030b80101c4c2c00102110110340c22070002c411041185035034030000da07034880311540581050b07080282004c0302d00200400381354103d0481e038050b9034502c0082c400a8402400d0603564001d100e00000c95907015030f020000500340d5884038148a0140c020340b4050601100d00a110403000c0e03000341030f0554180410492168004040c0c1038600b02403010700482100d881c00140317030111400d00c3e41d110300000a641e00071903940d200c40c4e00742281c882d9400c548400d0780030400781051109548240c0680c200d965612043d90b000300d50001200d205840701c000c24400403000700c81c207580f404044c0501c50141041b0000e404112035500d240a = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 989893201 1250 989891951 989891953
    0x204050a06050418020303031f030c03081c0902151e0a02160f0602150612060c041a041d09100608030301170303090d050a0212040b041a04080307020d02120f 69
    0x80ca1520b014402214039002112426800f25454000180c0e0003101300c82c1c0002030111038884503403401c0501b40101c50140c3c8000c0400c4414880002000fa0401c040c0413401c070307003032140e0112010559024050b03c005490007035200c5144651420040c43c540050001c441c80810203071030b5065081c03070107081588140c075941c0150740200c8241c0d1181c801d54043e040501404041c20480304d14181000c0d50b10228595520301c0219500c0001c8c00c01c4d00d40d070141c2855039600307508840340750602c0310fa0100107a2050048040340046913180501c210018421074040303466060928031402ea2403440c20a5862003e0004c00090007440b081d0b00c02c04115000381c001804800f03001e55035951406c4030780740e50812164440d00d800d030000e0040040180340031400c01c09030711072410255510f000800049041105a1600c00184540444c02103000c150100280064821500c007410154003016004403a50159100c1c440300d6a00410140005003000c0788001c0b4071501c054007c0200c11600d090080c1400308028a0030f400d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 989894451 1250 989893201 989893211
    0xa021c02210304111206011202010e0618011b0b011a0c070605040806070327050304090c0809010b0301140403030e0106180b0306012405030c1905040810180b10030204050a 75
    0x14007400c520f041038813110403104041c1e082d544100c0c0949490381445507a011210300d000070303425640151803442452100900f050f9130b504005010040d0740b81c0c0d84462a002039009a07182c440340110a030b030800001d0f04040090120f0b885c180c503200241110000c55000410103201c8000d0100082000e203024040a494554036241050324a07460020028a01020142008044402340d1004101425001c5030310a2100885d440d49c1030140c50342c41a5841003895524102214544030b61141989000348101d00083c42640b22103000c140c2603400b0114244001030503000070400181c0641d100140360b440000c00418180c0c1d1300c00e031000e0300c00e074440611400c064844030121050300c2d040c00103e000d4660381c9500f80202c040340011b2a21291001607210500c00008040f41d0400170388000d9484812020142807400500c03120300a00581151298400034484d103400301c441c01807039001d00a41d54180114091844440d502d843c03481200140c40c03000e9440b5040804009a10b136401903e10031041e809001ca0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 989895701 1250 989894451 989894453
    0x1f1104180b060f032205030a021e0d0509090717130b18060c0a0306050319051203090d03111210050307090b1509011e180b0a021c02210304 61
    0x76145180304051040d4030400140c601c0c02ca00105030b90b0480808070300c0d120a848000c1200401882086020380140300224000c81030b20f900207003060b148442c80b04449000c1d180c1d0401e0903503c00030858510f01103402480a00982e04110b01e0707065000c4076a00d407501680741e80d61150007001105850000e00300351030f01803802c248110f640100f60025204c90000e0001d12040100b00e480380c002400c0b0f82800100043c01c112050b01c660041005000c009080d110f00d24204251694460309100080300d140c0654043e83c18a0a85582030302d10a08582d8041c110010081c20210024110401000418001070064400c0c0d0000d110a0500c907030451124649400d0821040528040b507035800105a01e0a10402000684070303034080c0f1b00200d080b20b00260303d60384400700584040040d01c03420150440c01c42c8c0040f0400e503114115000c07a00928070070301c24030f0b522003a100102d07224040c04000035a0020800040e442079214580c04640850b1058603640035064420005018034520011440d038004400c0c08 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 989896951 1250 989895701 989895749
    0x12040813120c0608060409020301060f031a1302371e030206070221030c0303040312090812042102160504050105180411041b0908060105031f1104 64
    0x2001030880591104040c07003182d920401d1581c210b003e540100840344001c10310741d071141e130090348000d580100284030113038645040c1003128800d0307c41510810440383c00701d03407004042c0b0407040c05501e8110781d41104060a4003401100c42030310200c41701039000710230074892042c140f10200f030f03c640b050100405c0f03440c90445080c2c40706100307423030000c000d141c0041c0400c010b80d02c10b402c9400080e4143e5103840c0d02e410003c1c00708102c45c0e07140c0200c019400b00190f0012629000b0000354459032181c1c40b0480c0340c8800320040821100c2c800da0090600c04104100b0034001441031900e64014881d040140050101900090029150800d01000340c0c0c4414028220814041003a070060901075400b00280e40c54040042c40d01200854010500740b80c040c040307000c4c003208142105902c04040c00c1404064802d40e6242d84041081e02c4201c0012025180445d040e800401c0060480b0030090003400d44102d102940203183c01410808003034150b907800700ba100801104054001044001c16903140c07407594100704 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 989898201 1250 989896951 989896987
    0x63727060516110709091109040f031d09040b04050a120f08011421010e010603030c0b0f1b0a091d0414010504030c060902131a0a1409011a120408 64
    0x90803c0c000310110f203060b60200002d059044070805040070401071800e040c01d4000d120301c04481508410b80300100400c1c2312289110080f030714400c0d903401c603200421640803407030b041800456a0303121800c1c10110307012500740a0f01d40d40040c0504181c80d544406980c03080140318194031201c0100d0b0340c100701f100d603458100d48080d0040801810301160720820000041031802c0000315102e4540381c084564103003c2c82540203a1490f004000200a416201d0401411100510404480000c1e00c0800111420090b43c1558029044a030320705048106959200c800364000511000400003880350000ba1889003d140c030030010549043d000c81030034141001e0319003285004140785c3d0f5a0600c000e010000340e21000e10a000c80d0416000642d0700c1c0e09100080e03003d28690440a241810031152002c0320b40000c01f144681082150320024003952603074400c00d014600510150b001c0c890000410000d03854850420150700103008040c9000f508070103c2080b010161030035149100081148503101d0945441 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 989899451 1250 989898201 989898241
    0x370302030105180903040305030c060a0b0103021207030b0f132f04031506150e010909060e150d021c050d08061f050c0a050637270605 59
    0x1503103903605090210701040d41002c00344400c50541d00008201400500c00d4034050755000d401d0340e070707a40514200301d5903c450507a40d01d04035924003144500550b000303100321401c0348180c41c8681c40e1a9200d8100760003c3c03c002c0c0c0c27a07640100c03100282901d10340da140024491155180c10014101d884611101b40c0120f075040c40c0c0d22410b21001003010916802d00548049035881f10741510084032040a50000d40720300d51009500c0350074684078000068003e4000103240c1c074217a030740c078030040d988104a0042d51914070a4401500006000c9074000e640f0081421307a56402425400084069038086540c4200b0900c0f00034035043c044410204203e800c0c031000011210505d452102414407200158985590a00c4201d004480c4164001c0d414010001e44075413800c04400c0c0c8117160114104035448007000c0351801903081c03210141c0c9c001004601b074a04090540c04208e856034011061603036004010101f1082c01d00c581c0c20500070700381e620003141400b132640f1940c000316503400c0001302004180019aa = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 989900701 1250 989899451 989899457
    0x30c050f01090b03061807020d020f011b031805060c13050604032a080601060504081203011a0703020c06030c1803010c08060d23010c0f0914060f37 65
    0x240035459070b03a00c40a060141e0701c041264907500e461300c1c0c000501440a004416616041d80d00c02c110f41c80760041007825411a281d0251070020300c4030680301d401c8589164251200030422014506214420f6000b07064810390101d15800300459078a0742441d005c41207a480400d07800014100c02041c0c210140b15006001c191402401e2505503501c5402240442004d044081030360286840144c0c2d000099400030444002590020358403207a0007412030303001d40101c40d00c9101700d08069a10341d82d110101c9040b10248188540701d00c0444013044456442120154114800c0e80d0f2028080c4d90741d9001580030300c20030400581c2d03a1010128607106810150801ca1107a4902030400541b0354100310340b0b42d4400e404898068205000b0701d0420f1240540003001018645464503004030b00405500c458200c200d191a010912200d000e012108080316010300d8000408540d1542031505098001d0440006602e02c1c0d03030f0604c10380000d035030000394019072080510520307056400000c0d2040160307071404100f01c0c5 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 989901951 1250 989900701 989900719
    0x15090209010906110c09180f0703020609060a090f0b0403140303071202160f0803070306270507110102070b010923180f0613050c0d0b0601080615040f030c05 69
    0x940080e21040d40b610484062001c0c1d0034510141d1242401080700c03a0100070117080460400080d440d0059040c004542c1c4c01d40300c4c40f040d0b1000720100054400c112a401000d262070144203001307100d0720b43c001000b0001800b000382d0010466180354842680a000d080228985407461400d103886040b404d0602600070b50401c00500541580c03246004098401000000d0307500c42c040519145103590448001d04183c0d007040f480010440390070001c0d801403000780e070b0600c003864030380b6803003070803100800000306009841403c40224015242c01c080d500c5001070402d10f04582d460401c090990380702e000101d600d001c0b50700041c0901602031041d00c4000c01c01360710000c0080703080a0941404240034041016103a801003d440040c2001c002d0b080c01030042c0029182581008010310807015140030044dd181d00840d0303e441502e040400d08110f516410543d4900d2517190b1100641c0c02e803c0151900303401034055850300c00c03500079540c01800281503000d611038600b491070510300f609419503001540700c0c000720 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 989903201 1250 989901951 989901967
    0x90c130614041d0718050c0408060403030e1e0a06150b0702061324030c03140703090f0605270705090402090a0902040f1a010f1b020411030109150902 66
    0x7081145100400903500061900241e0a6410001c1215041120075205a40d008a00700402c81c68a041045030b1042c203209a07240c103296141e01c0d0045000b2005547c1c803010004010070300c01d401c40102514050103890b1588070744102d01940c3c14805003c400c6950080600c031302003290610034000303502c40da040d0b041c000900b0300003400014031039060003078400c0f14003180088011244550b08001003101c18040142c1c3c40e110040711606030b800301808804680b9010171248160b000340154650304142c800d20074240d0780c1c1c0103000e0b002003141034025142240035800d0b071000203c0718403e040c064443c8440003020f004004402c0070000b47d50300c09a11030740c1c210480030000e030380310158541d420a45c1150b20304c1813641d80b0035035a0010582d410010b0352190074128120700e01e00d110750182600c4445403481c0d1a50b284841e00641c1d0760200d5181040003d0342803507040c5d8003902d0f0030b020f0805445c03004001080403e08101c0b80700f5250001e8100c0c2c00460703074039a2910100c00030b40c1000c00051403162402e50410100c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 989904451 1250 989903201 989903219
    0x106210c09050d051005040302010c14040f05060a1b1b0501020f030d0c050c151006030b090712020d23100311010c14061f05030f0a0215040509090c1306 67
    0x4038481c580c001c203c003030342000c1000300c284011000200951002c0020b4030303050400034007a000980b4400041541450030b44141d05090080360260365041302c41d903100703e103884148912640140001001c001c1174240e40781c80e05600554000c02c46015140c40900320020048643c50404194025815035101d000f16440c0d480020095070140000b007680065508460841a035183c803681d4851a0325001c1c0240e40031005c8010300c512402079030144005440d485d154182502210501904c2d40d900a100c40c00042803036105501c01107221640c50005410624980449000d1720038100c100010401040c20302188001074a0105034003010070100c91860501e10b8960007110f428020300e1504100404a80f0703001c5c00002181c0d00100840b1004485480c90000c7c91500f100c9142d203c1e607901840d400d00000341a240014041c540044401c4c007030070607000d243c0c1c01c1141c0d02918000c0140720140601000440b582e070700c03240d1031042030410040c00c901c940d40000c000c0c0c401c0318800c1081310545442c0040c4035044c2c07 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 989905701 1250 989904451 989904467
    0x10e190807020307050d03030903030b0906030316030e04090c0e07020606180603150c0306030714010e2b030c0317011202010503092107050708010e0a0b0c0c01050106210c 75
    0x9004803040d5a0740c019800441d050002c00d07001642c0044000f8204401c0540c194030408445009a034100001d001c00700810103001000d036030b4940e1662041c040348507203503041c01148107200c0c481d042074441d04d0b0070840840c06486081d0401d0f94a080e01d5501049140500e4101d10760240061000c1c0c02c0c9441c3c41030004d43c2c410041c2002c0900c481d0104005103864408000e250f09182c0240d17595042443c22000703010ba5a441100c60038001c2c0245080098000130001d54141c1d81c1c181611203048230924141485001124074103595001007080d082d1a445804001185d61201d0181c0da4510640300302c0d0a001d0070a000d6021400008006d50004104204607801d101c1c84050b03091070840d44c2da856030f034603c52908400c510107128140c0b88846420300d030f2149400601c04144600190f0b0005c642d2019140d080390020740f000c0d5200d402c070382d100400180ca20b55070035601c40304607108103007030482105200342190002d070404008a100701612511541c0108000f514926401000340001d44807103e000780a0700c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 989906951 1250 989905701 989905703
    0xa06050a030542040908090123033c0601081008060f0712050108070614031b09010908030406020601090b1915020102090409080307031422020d06020d0e010e19 70
    0x81c40c0188540c4440050070710340760032000043c0103011821a1b800d000364681d1140480300c0c04034451440500d40d05540d034150201c10664602024210744d01d101200d00e03040014101e03030411140060820041c0320408404403011424001582d2071490003d0014001c0751010340710b4005030f8503605040060303d40000d012507001441126a000b66103070b8040903640035007034042440b62281883d002180c1e00320009800e40c03c441c47c0c3d0b9a00540e05416503c0e1a02522064541c1c041c11426200401d1071080c41000030440b00006240400d40c1c0342d502d0b0110f50640c2c00c04e402030001a00710070010420240c0038040c04400a134201c801c294030048004a6080b103000911a032755611540d0360303500b100700e8003c0d41a5410420003810501461100e490b1000c1c05a01c00c0300c03403e002c41e00d0840142100c1d001c0d4409144200c01d000c440c0f40c00b070300705c81d00302007a00034100c1d1049a1110480d0b00880000d401c5001400e000c17038144034046018111890914290755100317030701348000e0740554040210000c025004030552 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 989908201 1250 989906951 989907031
    0x10206160315170a0303051806060904050309090903030105041a010206040213021306080609250813080c0109050106060e0a140f060301030b0f25080a0b0a06050a0305 73
    0x2588049044003002e0b0b09035110980d0620141c000a241d090080b412944281c400d42c0c0403c829510035045030343d040f42007001003406a00c0203001030103038206802c0542d00580104103c23810420020300286084e8001c079911143c0760000701c010021410180a091300c0b5900920f98403500e9481078000035038a0381c2c0140040e104000000e48030012010640c1121200459039901404841d20b80034003030080e031401c4d501c240c0185010400252001c181619000ea01038403294480b4029041440032079662102a001003501603c10801d6800070740c02400402203414080c0000c2151700060401600715040e55126100b071100048040c28a0b550700c4d0301890654006c0c10b00c0400c0441c2007030103d40f202c2c85074182160807120000000c814480116aa907106114440541446130307251a60700c5101c5076504500307102c44540014000949001301140c0358040340d10840003690392030a000040148405511100105500284814030698540682d50b40590101181d244540c1c00701e1101c500107e13580440c404c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 989909451 1250 989908201 989908211
    0xf2107060c090f0f0f0b2107020312010e160c030906051305042d060308090108070513030308071d150f0c0a1b090b01080a0f15030501020301140102061603 68
    0x3018014444000640005422000c85a0302e5545404d00000702d40180f0403045506100062a241c96404840c080305080e41e40c50000100c00c2400851603a010701190301754003092145240c0c04203030300041130003000c06040d00700407410702c04c00d90400011004a040200541d0014203c04290070640c0b0b4402c45929141041c3d84002d0007104510000c181c0d000341d42c1c81401c0031400d80040002d420007119442080090301c146582020b16070040b95824030005142000034802c0700050b602070f4111340e6001c01c090030302c00d191400321300d0749500f030f4041c98108901265002040c8044282d114091300500340121400d840c588030001d0008181c2e0f1500e010341c01b50700383c000881000c0d400340c0205403029249404102c1d01c0000e03040c0ba100d41c1d05d044040d02311201d24801071000400f0812401a843c0041040e100c040182c5c5400004030f02610030140840031280c1c036100d00655100e05029030340700940c000c80c001a1a5410306140d0070700b038818024aa0b045600003810320036103158075003003503110007498100026 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 989910701 1250 989909451 989909471
    0x30609150a12082802190201031d0703051605011403040c080d0203190c02010815040b0d0f060501060207062c060307050711030d0e0d150e0f210706 65
    0x5621082c0e040345012800341918a010020444060501c890500302c691900c1c1e0f4604048412150240c20000010703401807484824640f58a42d10074103090040c50f000c5010500b0108190b1031071740c508000426030340085010002d001060100c10300e4142501c0410420038a0000000c110031203030081c4680b24040080407604200c0e01c0781c1c9c42d100601505040c2c507080b00e61a90042e40341d8005000406e41d504945184d003094a20231410700740d00c980e0585a0845548842901101c01002040190380040d42e914451105c1d0742d820510440d90752040a0a0038140c1c4c039450544282d0303030181d2100041d54001c40042c403d00760807011680615a05003049a1499130046425003040441621103170891400024014400d5100780241010390091038064072825641c000d0641c0d034180d403056900004c3e0454100e0006141c0001c440041501509104a494000da86440c2c2100c48c0116040c0f4682d121000c0c14902410a014105040002c40042003644803622207031050b0340304004000705100d5560519070 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 989911951 1250 989910701 989910709
    0xf010f110901080901090c120c1203171e13110a0f0b0d06031209151806120e030a0c050d030e150604140103080c011a060702010c151a0a0b03060915 65
    0x11071160402e20103541f031a607030b100f00f005031840c0d054280d4010301c0c0400e0201e10b201214600c0b0000c00e50690b14030041d203004603900380390030401410110b001c030500c01621030b01c0c0d00e4036000c0d5802201c0300404030003038a905140001c0e01d841400c600038003c06410404114106075503042d10304130740e480030340180c1e01d0516158a40082c40940c00040c0340c484000303462030841e64400b081000b030b1401c41e580902500c0d0f42c200243c41e8505a441c110f1507039400d5101c1480034900c1000660b1100d4038802c00800e2240c03656082d00d0550300a210b4103130014800c0e100700001e000c03080180150701812800c0c00c1200c203040c00142502c074145d0001c41c6203124242c00106001e612540d10102a2004541650001c0d50312842c1903d0194418440200c00358240303481c02010703c000c0c441c100c000140042c0064034000f1140d0040da64003480c0801582e103412881a0344081901034054000910220f03c070f0b00030720020120400c0002d001e44c3d000320514000c01d004108076a200c002841d90032502c809600d007100c0240100103 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 989913201 1250 989911951 989911961
    0xb0604050c1c0204090f02070215160606090b010315060c0609020d02210d030b0307380a03060e24040b03010906060504060e09070e07140a020f010f110901080901 71
    0xc00c02c9401001d482c014030b0101c641c06002980c8000c2000d00c07441e100b1821410a1b8003603104080e42c01044450101c4141003d4001801c0c40850518510440c4010b529a60f045138400d0744034000e200c1d200c4240c220903682c14071030840c1d145031560510340b8103801c00e24002c1034a00894001007034140d03900e0820044d5a41c1521000d110759004101509035124056100220010115050b5042c481e0b103c00c03000c024024010036101b40302c080d004240c02c43c9400c01d9506004018051600042d407001200d400805c10341d039507800590b1086010039551402008010100d54550b03021890320201681480482c4034080400103004040040380c2e180d107014000050000c03c404003105a00d5031034038011104000d242e42158080b10021107040003081d41d030349003c2c0202c140c101c48140980c2c1021105028540304010800e40014452405031108014041070200a620000341d00d00564006400b0f00c80583d024000c406000c1c40c1c610042c40740d0800c100c044115801001c00341c60500c90f40e080000c00d640000d40c01 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 989914451 1250 989913201 989913217
    0x3032a080a0e0a0605070f12061a30180312061908100f06080106032f19030605090f120a1b0b0609090c03060105040c050705010e030c16030b0604050c 66
    0x1042103040c4461301031f03d01452407070700001196110f80c2e80d194420451084408940014a104500c1c110140c001c2c1020743c02490342c02c64410085610500360209041284402d0480c01c000040710701702500314440003000d020700103825600c100010700d0640100c0400036048041502d040b007011490811040c101d60103900651024800e4492016504096030081e02414030109400c118080d29a802c03a404d8407040d000c0500901402070221112018924240c2113916031a20301e011028503240c00200ca980e01501a80250f480c8143c0074014085a0320503150442041c01c01071034070b01c00c0e4200c2c1070348424181403a06007405010884100c11070084c0a91101c00c0140c65105410450510700940480c10965200307006043c01000912200400a8071000707030300005000b003245a1801c070070400980071a03c0100100101400031a00250003405260040c0300d40ca000356844901d58500d4a00d040c0b241032140c1e44414002200701b0101e14100d00150b0484d400340c0e4041030546e82e501a201c003e10030445 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 989915701 1250 989914451 989914463
    0x40f0c0203042103024309060b13060c05030f040602061e092104081603050c010c0b01050d08120f0f150d060e16091a01030b0303180f03030703032a080a0e0a 69
    0x60a942c101d80080720341080c7d0301803e40422402c0c0c0c82d6090500a401030314110144256581d42c2031182e18040c4003000c4e41d00d0301c00d030202d9107001460b403a60181e0781c20550103c0d000d1381c0100140070181007545d544402122100c0070000d080e15006030034554448190107001c4140e144102c01300440e12000c0c040350041c009400c126062610428003d5210510612081d100c074091030301d41001e2580b189a4400c100c5401103411410f0340d080100f0807040f2004540121400e13a0100200043c1c0041080301510501a10761141c00c1480e010740321260241000302407a030800c5503110744a107143d42e42c40c16162200e401031030000792803800030304040c85c01080e5418040c2c076058518002500100b15000740e545062080007041c40854000019030580703007046d03100d96060300244060307d1241429082082185001840d00140034510404241541c0c00441c091b00041c0e03c07081e14100c1150410016a2120701c0307501440b654880703100004005800c003401d00e845039619205810513030101000070a070000e405c14 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 989916951 1250 989915701 989915803
    0x50409151e060b0d0c09051e01031e0b030d020f0d050706060b03010305030414041503030f031509060e15010c020904080c03040b0d051b04090b040f0c020304210302 72
    0x460050102d070001310394445107604244148928501c00c1e40c00704c04407400034100008045134070386800b1180520b61004c504056a0704d071081c114104080003109810041d6000292108d642d000341400e00b00560f00720801d40d03100c1c034840e025200000a400484150510f002c68540c0000d10742100540126031050000076400300000c420f0010100081c003c581004a920080d40200030034401960000801c0880554004100300301190107401500c02d006c0301444d0028a0410800304400c0701d4410760031141d01665640428403484e240c406400c0d4011502c45410300741031144a000920180284500901030201d50011500f040035543c00c0e0740e1015400c0c42560785460712070404059035088410301c2d4034018144004269000e84480b42e8591469002004601d0035060950120180115540e803540261343c0e212400c11004040c0304241d907510480d8061661540781007840345e005141c4919a02c0c0000e55601414002a00005e440c00701541035001400c0d0380c01843e21640e0546840c529551895200c1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 989918201 1250 989916951 989916959
    0xe0d0606030f0326251209140709090b0127050a0207031b0b010323030f09030c090c0301050108040303180344041103070816050409151e06 61
    0x1080c2c8000500c00b1461900b0b14466284c402e00794500196285500049614203c058811004000111800315810a0145500c4a20080e0101e0300300d1710003980d00c80c0802940858000d0180001c40050203109418001d403800c0b92100b0010003030602c1680c4082560052001c0400003040ca0300311101000762040110385072950003a006503002075022030000d000c51008609424084000d514200d4008010400c00c1e8259614090700c241000c021840324030804442c504d03228420230080003010f0414995588403840344e8180b5251100913120640303e89900c104000051900c0403d1300c0c112807003440d06005644460405600520301d41070921804e205001c0038400345504010005065803000c190b26403008810012010500d82e06d18400c40320503182a069443c0001c05817400340c10501604280d0104010032000138a071202c55071020300140c10040090306413003440c2c00f103e0010901a10f0a0010440da69114480c8a2481c001180216aa10340f4441c0300008508032554080440d4001c1100d80d481e = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 989919451 1250 989918201 989918207
    0x10303030603050106050a180e0f071701140103080a080a0f021603020c1e01031e0903020f0d050913200c0109020411070b040b132f030705010e0d0606030f03 69
    0x41408159003130340c24200c0000c3c00c2d0030f00c110b19004652000d004070f624400080035031406003c00300b82c87c49132441078070101d45201005211507402000651414400340d10100712040c2541c440811030034900d84a00300402c00f00e1a10401c0f10440c4856141c0411650350300ca20000c014041c0ca003440424034804a120348000501000f02c03481c0c24001e0b000c640085403940e08004223100c15460015210092010810341c41d4025001030200640c0c101010a00d000600d80400845240c0700c400d50040e4403020501c0c010110602004542940f00d1400c41c0c07030084000041142c50703410b8100191001c0e03541a016a055141a4080e000c400041421550758074818804601902140509078425460728140401c0750040c00115079202d54070100200c641e544d6601ca864610f9401080001100c03c001d11560001d4804c01002404500300c7c003402c1c240c00841d50401c1d02401051482901980c0b002c0d1041c0070f940e820042c80c114046d01152084a00c182c90b02d4610054942540002e01704948500c01c0410103070 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 989920701 1250 989919451 989919461
    0x607180807061e27171612060b04051e070c021f020a1502040906060e102609070f0e100e0c070503120402041808090603072c100f05040b0a03060b0301030303 69
    0x7480c0c1424130305d100ca400d4849901c5c0c0f2810030041e5045024a10100000d1000440304911346010340c00004082d038a0b0b10215060350380441d40c1003048070340650b00b21507200203132030402e8105549141c0324124078640d030301042d0711905904202c840d01e40d800381c0d1005800e108212920340181c0c0032201503030100300440150040c1d001800381d50300c03a03410300b01d002c54075a00c140d11000c0549030040090842c2c0c06601000e0b22100ca8114981c007500b80a0070303240a200703514000f0789000318215002000710341d1810100ba40ea8028a412050255541c0d1060229031500b400360b10007030341c1980320360100c1902d58584500700d03841141c038018801e000c041500b121a41c0b281214500c9203000fa941404071003c3c07003042110031140031a004041c55024400403a1504054010b0350303124420b824907031a0201c8512001030f1800149281c0c0118502c1d5000441d15070401c10050400c40f86030b42411801c8010340e00020300103000f01c0c0260250306402085100f00184260841d100900c0c84000d41d56480d6101c2c100100944 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 989921951 1250 989920701 989920709
    0xd0509060601030b03100207020a0506040b0913020f07020f01020309040e0105010906090b01090b0304030c020409050d1d180604090b09030417070e0601120b030607180807061e27 78
    0xc011500001c005500900800001d9800280503007070340354100034004003e400044040ea00114800800b169a4079000010b00282c01c100001e20384910083e401c10400381010648455491f005100b03421110b91300b002504d10f02c13507040714005c507c2c00b040ea00403891030080810701c0761302a0401d8400c1640310810b6000a041e500c05801c01d028094407400300c0e0083d5020311100600084840000b00314040c204009160024800d00c1c1828980000d90006405d0391003003c400c0e9150f030401c45107062400c1c2c000310400d103260a45c010002485c00b0b05c0c00003034a00f543d150301682c4410003000001c4e41c00e54442d4040b82d071195000c00c40c1c00450401580c5203a403a00940a1a407400c894240740d014200800140c86d0300b115042c6040b400700b540d0780320045440c01c040124003144c041c0c958040414681d411301c00d85120b00701c180c3d0383d1389525903100c56982024219901540040d0400350041c400180c0c820174900018004a1208201c86900b9604589124410f8241d504194140c50481d48880150031400121 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 989923201 1250 989921951 989921953
    0x30f19020909030c0a1b05100807020118020f040908120f060310060f15020109050f0d12020f070b06030a05012c06070206010504180807081905070510150b0d0509 71
    0x180e682c0c40541c543d2482041070b004055884080520001000c4c4055002d044074201c1405c40c42c03981e5240840d070300080317007401d00e0b0100701c43d64104006550309200d141d5042400c40c49007200464150041058103806031500741c000c0741c03244504400d00040408651a81260040c03003440c41c0782903e035102c146501614018400d01803545089052560360140c44290f61280701843c056070718205406210350319a000a04c290f540f80c840701c1010480074402d1a41044e1404041c0c625604d403400010a005010b4200041c21441070004150040b800401d44000640c130090070030540e01e41d100000d140828080f80242030b03600f0300b41d154500806800031441d85030340d6143c400700d15844040c0d0003522058200e0341c07903005030b203c100100f0180c901500402e43c41e1000040c042c1003040346440c3d41d0069445a00300703450342c41c4000381101903104850340f0f020fa591080c5c5080d03402c00c0a160b40316038590181002c6c0400c02c94562000c41d201490406640009001740c0c4911681e4405001e0600081d1004030b40c000d0003 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 989924451 1250 989923201 989923219
    0x405150d0507020307030827011509110c0705130b091810090b370b030709090f03030504170304051b010230040b04061701050409150b030f1902 63
    0x25543c00041641c901c20350507140c1e900156a0066910041400040450443d00ca040d2084c0348410b000e07c100341b030341910a48400c0000382030605e1030055414601007485000410005559808801f050300030903550304030f030011055620141c0540103449101d41c07959006054a091120000c2070103403da039001001000d1741c0d4002824074011089900101d406440c2c44d41e81070006840e000e080c0e22218064200c640308400b4040c00000d00d000703c01c0c0c04503c101681d5035a0444115500e02000304000610b209070f814030202480740c0d2414540281600300600703044e250000301d4104440c980c85605050545e0400e2512481d00e130a119947e0021242c40d50a14500088020701a51003c28105903411000c08000240518100d030b070280c1918900c03103503a0fa55400c2c0408541c112610000340b004001998030a0542c8028071442c01c58014180c3c0524810303407404800400003501c0d8403091034001810740f0000713100880000440d04001380c1e6542c60066002e0700d155881b04e03c0d410304540c3c10140c0244e83d0100 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 989925701 1250 989924451 989924461
    0x203100306155907021b1f050a050403081303021305061509040b040e0309010809010b15070201020a0b07030e1501030809060a0c080c03071e03230405150d05 69
    0x200d11849082d180c40a10320708190b00c00043d4039460000515210300103d2280c000d68541c418100581950007100507048258405072000c2c0b40700c1408070444044482181d0b81504001c0030340c3d80c90135040f8200c14031a0209803503105c0c502a80681e8015031700403243c03542d640384000700c58512a003c3e02040740b05030612104441c40c00e1192042034881c00e0701522000150000c1000040380d60401c241e5550304c9600c0d032042c0000e076143e40c09401c02d0350300c00f40000c50b00d5a01c10340015020140c0240040c00583c5840401c0342d40d562800650003000354050350040c4e8800302c500040b0b062080800014280004030800d00c80035a90550051100301d0707041c415621100070800304402c4421080c400940212402e0000b03401c1403074280b005160625050500394444c46140d43c580c0e200d5000044145055000400c80e0020310600310f03d1000d500c82c4c414101220608595000f4104000d4580c95100c06141a4186500e02403804121009010000e124068220301d210007011164480f0203001115070905000c14 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 989926951 1250 989925701 989925749
    0xb21060f091b0103050c0c16150206100303122408070b130504180b010b030613050103080d0c0e060c0f0c041e0c12110705010e12040306020310030615 66
    0x202904410030b824060034105000440c05010003816200300c010381000144028601045010a000340704442c00003000d280c40310003074102d1040101c01c07065400000401c00d40c0c2d085032001c0300c04d0303d9040c2404140c1074040c0445000400f06240741850710050829841c1280100e100414211905401111401d644400900c41c4500400200c0b90303047d49200b2062141c2e107050b400c041404100400d0481e010a00368658507034000c8283d0100c0641c010000502215081640e41440183c001d180140700ba549182d89410b028498001140b0695a4511954507928460400440c100c40d00400f959100c40d00442159103501e1810b80545681c030a1001c50782d001d00f0540540a1003c44051a941e440082e02c2c0340c24010346019000b0b2002c00020030320000c442e04191090700d40d0b000051142c25107030400352510a086590f0424041026801045020f1505600c074003200e042d25842800540c032500c642c842c00c0c0740d8038010b40000304074600b0848240800c0443c85041d50031036440030044200030038002c0b802 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 989928057 1106 989926951 989926963
    0x103030f0809060103120f1211040f0e09030712170c12250f0c14030c1b0310020a02033601020105060303030a0b21060f09 54
    0xe0380080d9030001e1030740e50208882e0010102541940c994000111804140c1e008210700e4a4482100038400c2040350340c50701652000f40980e07010825400031342d8015015525545162010000d4205d06403030005018144080146142a00ca625150103540d410b5000384140b00000529103c15005488503510501c900c085071901c64940960610b20414054202460007030300000c00d015421a1a86105103035005040034403000220f83c405881c06070a10102a0400e000720301601008070002c8000d181c5041040107135095100b07100d4152003030074006690160103500424415810512035401040320740d106004582c00c0403080c9080302c0190792050150440403030000c1900d0223260341d4940c0d2141550382400240500d117400004030380d407400010701c046844c81c0c483c9900a5141c0f251544801400705401a00211400d0349002560b13078001503554a103402c03c04000245800c3d004602 = true := by decide +kernel

theorem cover : BRFrame.Cov 989748201 989928057 := by
  have h0 := BRFrame.cov_init 989748201
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989748201 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 989748201 ≤ n) (h2 : n < 989928057) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
