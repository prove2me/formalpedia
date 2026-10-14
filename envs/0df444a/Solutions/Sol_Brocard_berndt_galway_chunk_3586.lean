-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3586
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:05:27.305688+00:00
-- url     : https://prove2.me/submissions/94e46159-d2b4-464c-8333-831d49c0bc7c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 644784172 ≤ n < 644964028 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 644785422 1250 644784172 644784181
    0x203060a0303110a140a0b0703023c040b030621070e040f050d0e03070914061306050a030c092007030e032d010f020708070803131505041703 62
    0x2044046207100007418040007980c3c2a2080a061080a00c55a00181c552161100c5001c52a8403002d0080d4100c50007050036001039512030182c0b080d278039078941e03078001c11040c46454038444403003101d40f0100d4076040c00101c8460f480004914028000f03440350100c0240c0300d06020003440444401c81640c1c542c28035464449081060b00050b01008a501c9060359602c03a4451341400c81e10b0f900d50102c06840c0340101c1d800004501d4004210382d840d001c0c20340442d2112955500c00d2012500e04031a0b0f507180301912404184107150020724418001d6092800041c042d82d2000024038001c80e80d44100c030300b10025101005a80614442d09000c0030070212204801c0c40308864400040c844c002001301031002e0340c03213484141d40303003041807920051b06943c1d2051004610700e00312000c00d0420002d04800d6013412140155000103000380c038074035907020220360f040604c25610140d02e40c000500080090b41414120b82c0410006003403403101c489080d90000340303424541490007548060078103410840c0c4040080c803 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 644786672 1250 644785422 644785429
    0x409060f06020a03031a060307020a0506070201020306010e0d06020d050f180105040222060b0d090507140a170f01110a030b19090b040204050d030e10020f0a03030506120106090b0310020306 83
    0x340b0f04950315285c005800c01e0110820b40311000200441c40e040000802042190b9400160035182c49004030100e40b540c1e0f545600803820f07848202c0e801ca00152854468810506081030035454440c4203803409030a008012200d1001c840048400d480c20710240c80504c01c04082100d803000d81030740c1ca8402486186000c0e00802e00d000d01040c0200501c064103503050204901580c4082c029240101290380e840c4c0d140e40200020b008100d4082c8c64601817a0360008003842003480e200270000014104500c41803810360802c0b4201b12030060319000f8000d00301440c2c942d030000c2c45203150003e084080c0648680e44180004c04a501c201c081a014625850200395202c10103140750b800c0703030f610100100c2c0440d41c90b03000c9400782c0525808031380c105c0c80d1441c0c0d1000305500140103226035142a14642c00e665039801d000c0780d83c0c8000c425000c02c40d811413030681d00400e20030342001e90300a40c003420ba07282d054010310300b145c216032a5034000c40c440c0f66036003140123561405022003d00c41500d01001c1d4194100361002 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 644787922 1250 644786672 644786683
    0x506040318030c151205011404150e0109020a020708150106120c020c040e24180307080304080a03060519150c1109040303240f12050a120e06040801020409060f0602 72
    0x201d24107144003240c400c0c0c039144640340010340a01d031700000340481d5a58844903661911072004040c400c5081c217000c100c4000d00c0c0092a400c0320450145403207144d20740380e0704400a6000c50f0144045004135080840c24103001c11490078803401200c0c43d03261541c13401c1002409001c2030607a601c031050501d034948002590025544c10254821180021034610301000189420080c1e44180415048010305410007070181890303038451080382e00900e103068050021240c5038801e442c0004c0800318107001107408540b1680c0a0540001f40d07040004005807644000342100c0601d0307101016400002c5000c0c8901c40e5441c2042d40d624999040100c4041c01036a40d0002c000703030402640740502c9806002609141c4079411450b21410040e01003035047e448048141d001411500401c152074900300340c00208a41000d24440f2400d03004800340c901891140d07a0441c01c40100c2c2410010404000c042c549903603180e0f0700078001804060001070741ca03807402d0140f005481a0390b024503200312100d4030401086801042 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 644789172 1250 644787922 644787929
    0x6090708061504180b030c01020a0b0c0d020f04080303070909060602030724060803070b1308250b0903040816030302120309030f0d050105011b080910020c0306040506040318030c 78
    0x180c41244040c4140012030900030ba600891307000c00000321410600e03003140c0c405150944164255100e00300440300590740c032440c080000342401210380020b4951320350788002e481884d1f4a45005031610f0040c05058800350019004092241c10000c1400001a007040304600100402e01080c0302c0946040b201a40320b0041240c0641100f07181002854825055620b19022684410042021685409429a5070f40022604449411400b008a4900c82c0c1d120b10000c0001d0b481202145051460212003040d0b040c10403040040c25030384508180001c4c0300f0320f0402e1044201400a5442d28a056105454141c80c0c030b0800c403440c0e21140c0103101107680814002c040c1184da0f14420fa580e16400c0402d840c522030420825a600004100387c07003030350025002141211000d07070310100100c0d2042140110b1510059000b0410030b010444002c0a09001d0907070381c48544140151080c1c424a100845d05150040f6000c460642040d4104400c0507040200b401c442200300c0c0d440c50400c1c0c116070f01c02c2c0c0c40b140e0030300 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 644790422 1250 644789172 644789179
    0x91d07090c03060e091606020303010e0a020c19110f0103091104090c030c0303050a0806011b110402121302091602062202101d06090604181d06010e0609070806 70
    0x469112550302a810140c001c000342003aa08485c50a102815154181c0b100100c0300400020700c00542c141c4000196030581da040d6000400644620004800950020030280a1030203172003044c0d004040c0380312101c05039602031020208a0f500402c100b0011030300e1801400d0506150004076008207a581c13041c4840110140c60000d040e50103420a007031070300b003590b1008021601494001c0304056110000d00b03004010707a00d03200120745030a001960310078000c104212142d00320b00304c4000850001c5e0864445440301a20052908a203034079030078a4030710f046883c3c0c1030105940710038004609050401c5030b031012001d1107038182c80880314002520b546026215000c030318800410070b8480140d4a0469207000d90081100c2450b08400d80e000c2d1581c03806074640010340c07502058000c3c040c2407038022989402c400030b24403480e00e0f050401d40d4025140c1c074041200380f0f0b5038503184d0240d00031014080d4810b9240b020300a1010390324000440400d200c00030101802641d5107000c0c03291003600541c04c0ca400c40000c8 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 644791672 1250 644790422 644790431
    0x5092709070b0a0c08130803072f010503130c09020a1805012109080d021903050610210b150d1104030b04060b0d081b06060316050d03020c0301020d06091d0709 70
    0x182000e81c6c2c02c0b425030000b000c04e001c005020420491020030881e0031180c2e034815001c0900703001404842c80042d000c0010702080c4100300141818800c1001821014030591004103042d4403030000e802281c018407420000300e43c2400d0b10710365048150303001c0e00080c1800d11781110b40107068008250814907406040a04980348c407011801c0060300720503940c4007000c0382021902c8400d194a100400c070780c04140c0902082c40d002c0400d880e82000b58200c0545403c0c0d03222890076041c42d0302c481c074404450360002d030b069039a500624011130f90307465503003112885c1f02101c5036111608103030188212640132040644242d400c020420008046446507640300343c0041c400100c40369100b0201c0c401c00f480c070100424440e40010003281100c04101c44102c0100202d085403604d540e00020303d0f9440c00d000c0e00c0c142041c403080108000511300151410b078032901c00d2060740d81c44118a00400e0981e008603041c8400c40d40c64031010f006c5070000b446902c1808a40c1504051103000800d0144d480d129a4090030307080350b884 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 644792922 1250 644791672 644791687
    0x1050a02010618050a23150d1e030f080412080c090405010306050a06090b0a03111f20010b0108150d05120c121905092709070b0a0c08 59
    0x394030010040c0719000c822a50b04070381410a83c01064112410000940352410300b0710059500348103101d45165020a02e4001d0f01e5610744901400c07842d100050f4800310b9483c9600010365054240248d0060a8503540c03248084d5140c0a07081c001000d4228080085034400c000104d18014005280460179007031410a070340300c06480c80c1c01d5214030024942c20078101800003040092507400300340f146101281c100402c1d51141001c1b000c3d01d09603000c003070b031043c8014424408103107152603403060070000420300c0710011180b06400390f5120b45030403000c0c007094488a4007110050f55a2002c041c0000c0c2c4d400800c2405a4003001914402d0060141e0011040480100d041c540310900c0d81c0010640080480d1407071215034100641c5a0f00500d05903c00d4000c01c051032076442d000000b0740343d0307e403001641c1c0c60a0f112015022207498100400b00c070342c082d81d00f0440c00c403046100072603010100f01217174400900e850822108c921300721083c0d000300200c2500300081d20f06a9030050b64101126884005503036140718 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 644794172 1250 644792922 644792927
    0x4030c0f0c0b2a010908030a11070f081201150c060c020f1005010510050c10020309031303120e0307060e0409020f0306190b030304050d120c0b0114090a021801050a 72
    0x18a0300300180c00da90006440c000c0b01d00e00381c08031645202c1640c40060f4a01107840650907510103000c010640d060500214041c0445130b000000907092200c035103820500c950301d841e07901d60742c07041003a240500c00050080050074812215809040c0d00244180160f050101c000d2020084a1000e043c1d07564036014010618030a11214410744404421a07141d00710700381050006000078403030300d03102d0f4404207060801c0718020019240034011180190010402c040c1c80200079500c024801d42050008010310583c070340ca4000e0300d40c09580100c41c40c4c0c07102c01d500d46000d00311184425115110741d100e41010441b55a1203035440c140e0a009841c0402c1c91500d40c400300d50f440c507400e0010740d410f010b90710070042081c0c802a212410240500320078082003448600b49034492046018044d0814005400b50010801052443c1006003903494000c0c010050382e00c6580d0541c000b03804c0040b5109040340302d0b41c0349180c2a40016004a190340c021860046585240090701440a0450741842404200148500d0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 644795422 1250 644794172 644794193
    0x110103092d0b070909050108010e03091909110a172505070609080901120c0503240a1502010f020c0604121101020c03030a0f0e1f06051804120804030c0f 67
    0xb40c0c001c1c000140b41c1803404000c1d241205500500360102d20300000010740e10700502400003004844006945494101c40031b000c54454145008001d540f00301c030000511184604c070364610a482d03c05555144c80081c1c6009084007811403840128400180c140070b0020711504404a1602c445010491030000304038081d15140590352002d8081840c001c900401c1c040d4010040c1000c64003680d60390507514210f0116400c0340c904010f04000640d0a1000904c00c42b06101c02142071030005a811501026030000039200f9407040d0084c07260b00f0a012080e903d090b80902444890404565066042c102030800340e075694000104040c00d51a10020f0f60280d007030040d5070060022aa201c001d65036160124080c6a403580181c0303420100e9490f0503155050908988180059001c0283c0645054580480f4072030304004010780309162190388280000d03641d0348134a404003480400301c1c0781003030503c0c00b418000088008581e10205101102007000006544100e0441882d548400e5141d450810303403c1200504 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 644796672 1250 644795422 644795513
    0x31205190f0501030b0f07270312110c120c060306010c0507031a0a02071101030f02040b160c0816030b0916030f14071202060c0114070c11010309 64
    0x80c9426a04424074200340c10481c1a41d0041480c1c045586501140c80300c0204216400d1001401d1a4201c080d00e02000d15440386014528003091210798403500c901100260018108001c280381700e85080700020103010081c0440300c129602040d4800e9003003020f4462040b000c030144541c00002c0041c2c2c1c0d0340c3c02203180d03210b416004822114440c0d00c034507002c2450342606d065181e08007210b800103268140140220b9480a60004c0303050050702c40071006402505000100c01e0000c0d40134040400c0d003101140107000c1c2d1507444044140050729030b0a01c04408502d54116100c0c1d42c01070303059030102e02988100c020489503c00c8501d005640c8964505041a01003024850b03a040140000024014a16079060306540180d84001140c00009002c50791840e280c031481a0b001440e0640300050301e03000001d043c9a810003000441c0c2406003050303072003d00c00304481880110345001410404e22074500c22664801c2400e00f001c00c20001070752185c54186546914105115603d440b0004564903c0016810403 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 644797922 1250 644796672 644796721
    0x40f08030f070906030c1407051e16120305071b09050703060e060a05030303060112020f1602040509010522050a08030a060f06051c090f0b0a020c0c03011119020f0d030902040c020a031205 82
    0x510718020b04c54bc0c44100f14610010341588203103012503a00940c500030720300700350300d600e4161a002c0540e881602c030407044d003000946100c5911000402e0480c2e13018180c403c01841c0e034001905401d00690b40685140a85107030b00416035034200740500d4070b00108880d0000d10909000c5022100c445800c00a03100e1107150001782c400103d0081d18070300504503a0001c25100b11010f2110743c0e10304035418200d030703c115104044966180c60f031050003901055060519800703541500d5a507002c0d9120303031109510036100b0308105c65603000100620040080804041e1203c0d1400c1450600c006241c0181070107038020089480703071f8813060803040100c40c0ca1403241d9198400a028041e1800710000340003034000f84c0d4001c1c02c1c2d02480d40e00c180c0516040c41a19600c03504880c03000e003482c0d281d9038074a5100c09003106040c00d6101c3c10040302580082000841da502e50305990200d400100c51060000307481040b00d06805542c07001445100203608107030405c0e140c801584002500e503a8031442455143d101c0050380c0396 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 644799172 1250 644797922 644797963
    0x17070b03061c030810050108040c0303030b0103090204051512060103170a0e03060403020c0a080d0207150302090a0b03250f03090303020915090301050f010e040308040f08030f070906030c140705 85
    0x100354100821600c520320105c3c180307000a9070351005444240703084800400c00750380ca03501400068069440121418010300d8005045079040d0302060440c0e205807400706222004a02c0980c21b0700e82800d884400c118143c003e04065495551004410a964411688200408148030520750712078040e00c01c41010080841d03902c0d0a00c2c0c2400303511020114900f9000e40c94104011403c500c00003070224048681d6802422628548100010507403130119440c410184c00300929441c5640b00c0362100e0140101000c01d56403410310500d0030081000c0360044c8064888108800512035810103041003202c4524203000c070b00c031074542c9004c6009100c0c0d520b003564400c5000328000d102c406560042c0084410942c020001511254090014600244220400509500d0004000920a0341d17500c1c0c1091044400c0044070041c0d03910004e5680007180c5421441c05004104820310354801a0b4400404a60408028101c6280c038000c107480602403090020344400a20307074040050400800c46281d003031043c01403 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 644800422 1250 644799172 644799229
    0x100903030203090d021f0f02090307030c0617132a182f0c030412030807030b010e0a06030207110d03030606091e05091305160f17070b0306 61
    0x1002500199840d0f02a40701c1e40d1101507907140005014440c1c50109070211440300b51204a0b500a0712158000c003001d15000d2220700c280d52010824a0b001d54030412a50440d40d040410082099090b07003284411610503130300b4030813003c0042c545851a96001914a81011a909031011150104031500b4100d1030000500042e000b000701d01414105041020a0200c1c003c1707501440e198441000d20010600c80761040701c006021018001d00024445000740c038200359070f030940300c0810500f150b02500031070940010491060742c58880c8607035610007424402c450f5132085000c101e868040340038140500d58001040c00078040328011140915100510b624142c1e0158503008024014034802d80d80807800390f210100f07026900003611080c0c0c00d5440001c100c406c0c07070074003005090600503045000d81c070501c8050b4400310380d0030721030030042d60404084040c0c014648200c2c0644445285d009503485000c01c250204031f10400310b030101c01c03102000840d40c1c4940302e00c00080c1c038050211400c04202c1001600c00d1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 644801672 1250 644800422 644800427
    0xd0204090f2a0807060c0f0c060309030e060a08010317120415050f2802070203030a17060a0b0d0c200a11010f051b070b04030b090c010f20100903 64
    0x32420401c1c08040320b5840741168122004461400303031070816006101e044c005a40310b0b070f60340c10010b40030317010b00e0703668880644442c0c1215460790042000207881d0482c034028103422501520b18150140c64070b915107828108010720714401804000d08240f480c0141615044039481035806040005113120b41c14140352a04845201d800c461030005c06050000192404181c403a005124400d00f4125a00590101c5d0401da803900e104e05003a041541d0074048031000d62410006401540140c0d160040440448000125040802006148140d042c4041448050307004816a00b6003c1da048000c00c1c050341c501da080e113203940b803003000c02060070020010440216000482003121405407400024540030107004594900400d01518003107a03080040d01c1d605000c840a90340c2411124041c2da81d45030325800003401070b41c1301d5030041c0d64a031f07810018443c0c40c8109010010100800742844402a044503202403c00d05800359060243c29212540c001c0001007070080007080b80d080d0000304806176091401 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 644802922 1250 644801672 644801693
    0xc04150507020316030f120c0b0a05040203100c020c060705120705030d0f050f070f230a02100b180a0906020d0e19051f02070c060804030f0905060304020d0204090f 72
    0x42e8800e104500441e282c000e00301c25084c0990750001e1510740010500d440e240c40794a4142c90800c100171101a40301b0104032402a62801000c5800303002c0f425003003c1c01051b161a42c0041000480c9103414100300005030000358122003010300b83c030703480c0d01d550343c3d4100141401e00c1384180054528000400404000001c4001c01e4125900a4200050314000c000c6004441044a105c00c0707501145e0041021103010382c0006a4100040c07a11310341d0f0540701c08501c6021400000140702100001c141148510f4050041d50041c1050b50001c004003441d040c0000d10031140c0707120448181948801192040c100364001120003900000c0640d0b0701c0d41c19217020001032406001c00c0001c5d01860416008254040822900c0240c00ca401070003e9642c9a281d0619014148408070103d503003081000300040d81540814010403e6403280ea010b480c1906018013440700850060040003030602052059540d80c60a40e40c0140d01510707028103000e85840403070014610aa0090312911041229008000b8900b00 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 644804172 1250 644802922 644802937
    0x70c06080a0506010f03020904331d011a0706020301060806270c0a0c0f05010606030501050a150f09330c05031e0f0d020a030b22050c041505 62
    0x35910040c0d91031a03803007411984281c4611380050440e1045800380c600c41e8004c1d11341c0c80c0303009100143c0781c01c8582140c01c258403560300c00d44140e2020040c500d812590055800024001c200154180b4508a4041e0075071400501500005946405522803605003003c251882254071000440d9656181c480160201e00100c8100d44104007621000c6090385100140c1e03280f944110362854441e8a9010111030103420840380e09081021082c0f01c44046a250701032031540034020400055010300b0010000c0035500c05030803080c01441409410441801a501c054506904503d09a13070308640c1c180d0100c034044442d9004030680400100e0506c40960b0080598040c1f0061103800c940444008000f55035681c0c1241c000780c20741e04280312564000d01d4207d240301c9200c20b004c0da081e19000008680745040c0d0010403440c050a0b50100364240720302d8142c0b168600b0305808940083d1805058002c24250a0960354500585a115804070b0b2582c034070300040e039014080e80002d82c01151510800100315820070f24 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 644805422 1250 644804172 644804177
    0x1a01061805010903020310050414010f0b180c030103030f0201110307050d06050a0b04090905030f0c0a110109030221071521140f1b0304140c0312190201060506070c06 73
    0xc0002685602800c030349800c580d40500607080d032030546e1400000510340100f090710540502e100700e000c00710f03081c8100e640c0103842040c00074000105005224106003510f25810384080980c00780510b20020b541540c1c1104e40c5132400c41c010b40f2040340c0c103c1c013600c110104448050303008000d0080c80c6070014042e0042c500386001c10024541e13034400300b140f0199035104100185d50304010500c0740000ca41c0000075494015000c030391070280400643d007200d0340000380049842d00510107420400411110f0301075109400d19000b1501c5086030002021120010070b1414226180c1c2c2c0c010300000c4003072051400400012072210500044240d02402900c0741300408609800c041d2000e55090960348101205140d208854480a50f541204042c5001025042030800058049800902411600250300c9075108101c505031207110340e5070052900e81d0700d0040030301c00d4010200703080c910110070064400e20040c50041303500020149c04244d006000c3c5800c01600248002206014440c211900c1c00840d6500c0c2d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 644806672 1250 644805422 644805467
    0x71a13120201260c0a050f030f040c1403060f0619061e261308180a080c09070e011106160908030418090804053003071109041a0106 58
    0x70f0b088441010380403806039060210250109080080000142c060700e805410143d03d840e0b030304005800242c00843d40012040103c80410003000585c0c001c0030010440c0380d900703921303540c048000652100d1000308040c280c2100000001c0c42617817114043d401054070342c103424540c5512840010408800b0705051001c482102038103040c4135100d542481f1000c070700304600748110400b620001000c103c001e008080ca5900c403910041c00310341c0100050105a170ac50800203810008442030101c10403180e84106e925800407692200d060729010f42d80c2c2c0c5d02985626000007000b0310040162050300705128502624070407901000003c502d40c00b140c01462440ba100c4000145ea00c101e055a00e2256008000400d00514410720040f601508880c3c02280714541d4103080c40d407181c010071400d501302c5110000c184042c0d8120801040b0381c9030b07042804601000990328000c1c1b991070701c0c0c4d11010202c00703031400360f040307076000a0134081800100c4c040c05020504412035540e581100134140c0a04010440903003803070 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 644807922 1250 644806672 644806697
    0x2060a020616020a0503043305091806180402210a02150a090311010201110c0a2a0e0c0d02040e090d030606090e060f03060709060e12071a13120201 65
    0x2100514558445c000310b10f454103141e801d03080c800e01045102c2100c44d0708200c03034035180c244024010b6094a40d944650b2244008410843e050710090890800280070209102e1140c981501c0d90000e20120501c055298031248040f500c99141c45125994480d000e1441001c0c00f40040386c07642c02c42d03000b2584d0140f9043c2100150701da622901c002c410102e564181c080001401401180d0000300701400001280c0103814000c0030140c0c4091030492164002d00d03150070030084050000080640003801d4004401120a4401c00307084090241030303101143c840000e11660500c00480e10004a096001d5490390f689810f0003101741d200307542408030742c003c0001c0940e40c20312a01c2604111111a69a0614140760000310910403201924181e00a8518030740340b01e441d01c0030801e242c01450565214180140340190007807201c09040328a0b4800c40c1b0703007070303845580400010b40d400a80314281c458040001800950004521070746101c0400400c46000001e500c074410b40c00c4d2222103000ba25144e911f03600 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 644809172 1250 644807922 644807927
    0x209071805040605090f040309080a0c03060c08060f01030e0a02040218011704020607060903050d141005031b0907120504030206240328050616020d08090706081302060a020616 77
    0x3c44c041c0e240c220440340d00056520206550450b0400c1c000e0622000242e1903000103400c2584140040d41c240c10949001c004204030f500c541c0302100036504d44a8118200040010720020b050355245040540f00c04c95120007120500c129240c280e4010400c40d90364001d120300c007400030030305c855040c04140f100994038440011540680c0c86a40c2c001c0101d441d03d100c1d0390303c00b401080c6194042e01001801c0c81491204401e40c8180510b0b044418a803420620b45000500401100d0790021802038000030184506002c8550701c100342c0d29003c0743c803c8500d650717060b03080701d0b001c0d00291035400c81818081404241a000b05800740641c1e00b41d031900d0f090110204e05140b400070480c03032164056100d070815009012100082411701d071484445610f2003100d51302c85030310b00141a035080050540862003941e0303031a01000600100040c60800c3c130041d2600d20a220344406083c8078903410700a1050000300c00900349509600641c0d40104505d0b22940b131341400075035512007103503500503401d0446c982829150 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 644810422 1250 644809172 644809181
    0x2e0f080106290301030b040c031505011505040501020601030602093705010309020f0f01030b10030b03061303091413050109051b0c0d110a0210021f020a0516030c020907180504 77
    0x61260b0b16540f950b4a55a44c102d480d200c000d00a99800c40c94480100004502500011040950103070218140d410529424100340000d140305e018000704200c20015640c01040e850704494000304016155231036400414508070002011442d521810103075205c03070001b2181c0b0350071034841240340003959a449500560894044c0710010f940605002d403020414605034912025402041c58085210b64089001c5502100161748110210ba07ca0b14030043d04c1c20704111056010000980c1100e06041c10741740039145c80003134016881200440c00c4080e138951144010318281d10041c2408110560b0340351990f1004110a41d1002d82405802d20500f0060390050183c5880c05071860207840c010f600c208042c0d614001d1540d440c03071030780a20505c01000d640c0720f41d205040d9001580142121110621f00000011901012100030500c1445601d00342c540c04016110b4506074130041030404482410f080d01c0030783c8a510001d40c08005001001911030780b0040b4684038074881a4000c042c151200704200aa4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 644811672 1250 644810422 644810489
    0x1206060f05010c060f0902092409070c0318150512060109060905042c030a020d080f06010c0203160f0503010b030102120a05060a0305010908130503062e0f080106 71
    0xa404403500340701241310369021040040b0001000a62502c041d8080382210200b21484103207601212030182c400c0711400104da420980450b01d0300d240349130000018011803080b170750180c100040c45d411a1499a2060345050240c0b88d8402c40e98141c02e06a24001e105600840e0300030040100d04010491a501800c039210503131707446417070380b80e191030400080c48003d10001000200b00482c0d54495040c0d081140383c0c0040c07440003130000d56520001c1c644040e1812007140c1d480b104010f2508100425a900d039040075410190034603120502501c0c500000349401c04075022030b5003542403c0400a0442c4044e501c0000702c401c01d070006d00084102c0e40405080340600301550790748050708030001c0c2106a4540c0020760008008160009280e00d81c0c48042c00c58a00840c11181d400d000500305103a00da00d080c1c050005c2504600400c814a0050394103164580b0750003004030700910640c90010008200600348018001a184030500d95958440c0d45002e0842ea00ca07880c402c5480c0411100c2c1d2008590f82030112 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 644812922 1250 644811672 644811677
    0x207120c150b061b0115050a27020f03070801080d020102040803030f0406060807080a0c0504020f09010e0111150115020601060936020c0d08161107030203071206060f0501 75
    0xc69007100600c1016100707500441c0d9003c5020498032525481440c0030300d24030340b104000060204084200030442c0c20346070300b20760300c201c1d115a41080508a1201000b41031401c82241ca00d43c00d41001c211400f0740100e01e40007002c2c00d404002c00403070b10340c401c41c0700b230496158004582c4000302c0084184c0c201d2186e4000c03000c4d1070b0810000240001e202812181d046840391038001002c030340e6521268141110ba8010b85003d0304040800014401c1e004510000b81004039000c505d4410100188038191040120450502040d0075510341c0980c047c00039110340510714400d0360201e50407c601c40900b440240035822213840c11070443d0040318070002e0046e043e5041902d0703645041e4140a8404195140a011010101d01c40e40d54440c0150580b060020b410b014014096220f130394041d201801d200a45680300d081110f10020000300c00c1c407402c5c01e5140300c8541d04000026202a00a10742488003503000a50940305512001900140b0b18802d030401901500003003080d035485032000c107142505482a00d00 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 644814172 1250 644812922 644812943
    0x70b0106140d09020f0d081206010f081306060e0901091b06080105240a030c021903050f070c0302031e0d030905060a0f0f09050c010f0e090103080307020f0a060207120c 74
    0x104400c5500c6005820b00045c4001c0d4000080c1001402c442c8101100303c52002000c1589510b01c2c515121140c1c000c00b01f42004d200a81440c3c00c005c20b482002000c0103d54940c445080007480b00f25401130001e04201442c0e00b09030300d05809500e001c0e2480300d070b00329004600000c00005807440d40700540150f80342c1d565441c060b6481e0100b08a10f148006207220062280580c01092510b4020020300e4001a035880c045081c024149000e41003110401c4004ea01500c07080c4a500041d5000048400307210300c032480c99898030f02394101b0480f0082c140d000290140700c1c126401a8800c22640a0681015800d04945031034203803074401c600b0307940d604400411951140011804045084d001a00038200740240040c181d41105951001d0747c0916900740e8507900000c0305c95415581c00700c0032441c0281c00703040c9914a188000c011506500381440042c040c0480400450380c403034424440707030882046402c200c89490400d03052140081d400300a00300c4000c507440c941c00c14694000c02a500d81581c00030390021 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 644815422 1250 644814172 644814187
    0x9090709021b010603440c0118060501091b021009021c0f031206080703060908130b030a14012301021204061110090c0b09040b15070b010614 62
    0x5000c0e4101154099420300012242c01d030b100401d11400b002540a01c0310204075000801800c40c071022082c41e00e00c58078888116120144403d004c00c40100b0510081c410340d6499401c0307859005002c0582c11040c214800035101c0d09102540e0401416654840010400301c652245016104c11545100d03c000d81c000300c541d020300c42042d5202e4201140040d0461200e010002040c0701a58031100b400ca54008540c07504a0034035a10110b0304500d14a001010071030f1500b00100f07250384048910005140c02e40351044181040000c0040d41c2da0f8134020641907800070b884104070001504211a0ba0102c40d10306055206070100e00c81c143c234100c81003242c000d00d02d500c16501100103c00c0c0d07850300505600c030780a422084034032444000d0005007400c1e90754074050601a10384504021004502c0542d15007484101e20128200b501550101e50b00300075480c1d03480d584100890007500120000641c044403420300d180c1c2001d09071004160b258400c1d14040d00d141e032940d83c1524545440d510410b00080103020701c0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 644816672 1250 644815422 644815439
    0x206090406060306170f060408031005090a050906221704090c02060a150b09120c03030c0d03180308060603090f010510210c05120a060c030c090f15030f090f120905090907 75
    0x29030301f00c41103150b8110002e0f216008103240cdc1909448004190b40d8a50030458100010320200341c1122410106840d45240d91703400c44140300050001a041808841c9200603011004040310002c28805000b44842220f181001c0c2d10b810040b08c1c1c001515040c0080744030031303040401001d425104c5044507142080d60b50424000024002102140e6900c2410b818100c40e0b982000a40f101a414030014650701c401c802c0e00405480d243d040c509540d98001c00844000790704052034640c0118140e5055460307039150654a4a08940540107941039441e000c184480b8404503001c040c151049500c091040b480081c1c0b1819015100c403401030080303001c1c0e00c0c040c003052a2801031050b01c00900c60442d2003006450302c50b02c044a03880c5c03d071080429501d10350a81e0550b000b40b0322200400b600f140060b180e519211001400f0a00100050105540ca0021089016080d4032a00301d281d04201d015002485914002c06940d40003000ca001041c2d074900c0000b03441c9041603c4520031030406018180c4249070035880c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 644817922 1250 644816672 644816677
    0x112020409060e01020a030f09120c051603030903030f110c06090d06060f03060c0507031241060406050a0e090c06070606030b0a020f160206090406060306170f060408 73
    0x12a4080d86907255000407038568020000e000300c001000503a5840444d00160032606800400105070303007811150400b103005c0f0819084c0404040c10801c1d0711350750314039206041440c1d2203400841841550400300602da03100d2002001d60307111b9180d600b80f640403e00c00751b070540c034880c802c5101d540c00707a0882d80403800d1190151000000140141094000c0c564583d0706803040c1d078220581c00c0524000070005d00c406409070030b20031119400d00e6440d1800039103004211102c0b004a030301c18103803628010b580f43c03041481110701a070010329072850008016180011101c13a40120508140070308000710700d0720314040c4114000c4850042c1640c4c029440d21420010f201c0c070082c2000601d00071030360200d005071200d4008198051140400040850441c5860749800002400d0001e03101d20511203070000c03904040445080c00824100820712200a10010326944103c00803250850300b007032400150303290980c02100580da50b9104280702c1900c5508010b5440d030703221810040795030180d808640880c404400 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 644819172 1250 644817922 644817959
    0x2706041401020c030d1a0103090c06080606190c050f0f1509030f1603031406010801050d0620040303020f0c060a120204091a040c21020a020c04060807030c15050301 72
    0x5410301c09020780d950f04541100d80c451000c3c5440301b80c4140862000340b80703400344d5003003400c0401c4110000c0c0c45056152040e4020b1030240050078010072425a1250141e52070000c042001e030649000e0090014544850004c045940d0310981400c0104100302065143e41261000001c08401c0700003c40310341030040c05415200b05000030000b600041200a00401c010000402000f52041c000e10b0011f0442d800071305006c2c02c01d164001440711076a40110f241d0304480d0f088a0720031008042c0e0500320010010003e0220410b0a01300c036404900f1140f0380500101c90007502955031140d0f0303203904981ca82c0302c55049598810420041784020b6400744a40c0c0c00c0704103400c0d20050a00352500c2c5044100c03200401074410201d0715425103082450103004103519040145003000c0549001501282d900d9a010032141107990085040031806100700800207000780c000340240700e0701d5910b030106900e0307000303a0205a43c2904410404141a1500001562030003d80e98401e1b1460f860884c50307100c114074914 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 644820422 1250 644819172 644819213
    0xe030a0e011106100806010e01050a17010e070e1b0309060f1b03010305010219230d02130b0a03060e16030902120a0506060901050a03200d0c0608270604 67
    0xe02c01900c07801c0c200030f400e00c640d1540c000c0b8401c19003480041450100142d011021224a480040c0429210032990400311148100760380701880d071540740a0701402503225010b059110386100000d000c15162066402450029031115600d1350200e215009840708884012036a80310b00f021a011030b802c0c40215521049400380c0d202207c020369507142c2c480d84280e00c2a5600d070340200741d1104801340c61000301072b0300c1c1e043d0400d03803003d0413440c1d1802a010b4101c91589294640401c122000d240d003501100c980c95246200c0c1d80400b6129580c1781c426030050421100068601007010914142c13a4100d24010040119090103902d5850740490240c026807000b260403585003074400d40d040303a0400621041c244500048e040c1c601c0e0103028460030140c140e002070301c2415070400030400700702445001d943d10301021001c00560414280410f40300ca1908000500c0152816000221540d01580c0c0a02880145101d1107540008849182c101c021001c1010300540149002c2000110040c907100c0944500c030 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 644821672 1250 644820422 644820437
    0x615070f02280902180d020108040b04080421050f030f03220f0501050a050f060d060216020a0314070b04050f10032a170c09060f070210030b090a0e030a0e01 69
    0x2d078005450208540c400307100580c0104015201440464a0540d89071060310040710369480d81d00024090a00900081c081c800c0c2000407400b408550000c941c0031305844807510200005040c440044000503070015645405241c00e40c044c40440030048640e6a00c8180b06182181c40764009501220b681c03030082c03290000d90051030300010b40c103910402041805117000090740d14100201d4002d074ad44c000c040100b101082010002d03d03545116440d140160448001615200c0c804007012501e500300c20060f600ca0b0840c0c1c0300008020444022009407400141500c0840382d482c80c030940395006500450b60b01011500003050582040c8900c00461080c0b85004200d111005040c010045000c411141d00409d0b811000c1b4140c6800020034820b06808140700d03500d07481c10981403100c0d4028031420718451100001e4124006020805480c22580c000745061401d55521388081c0003090b004e0102405051303208000380c0002c081d1300c100e0010aa508000d0343c03400603001ca0442d034458002c00024103220740c6 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 644822922 1250 644821672 644821729
    0xe0121050a060311030105061c020f03060c0309120f0724050903040503070501050906070314190909060902090a0e1008011506030516090b09040f0c0201050615070f02 73
    0x5009003400340340c85000c0064400c3c2541030000c580b03000c0c40b982e18001d82c10300043c454941c1303d4011000f644030b0b901e840d0f4911003180313100103100d0820440065501d44612418002d0300f00240c0015400f4862031802c079024039408420504103400b410b00c10500f404418400000450640d420000c00c141c403100f80c40c45a100340c80c1e00341c2e0171a081034944603034645c80440c1c00d10403800c0c00c0081f24041c02003401c1190400c1c44000015002d8800c0020040c200010541c80c0c00c4809841c1c0180e03400b00003220500081014400001410b20060344191000d65040c440c0015080440d0f100b100c10208002d4030418029007449040c4c1080c10300038240c540c0c2c080503545d0000b00c2400a11500c07a0f03000001c0a554096442e0800040507150060070040860030244404041c2a402a160f074044a201c03100c119112004d04001070014031000b05032000e118200811030301c0b440c0d0b041d8001c512801007103800610910301c51100409a00074108001d1801c1c241209202c054640040c0c0e0a0300d026581d10302400c41e808 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 644824172 1250 644822922 644822987
    0x110105030c1b100f0b0d110a03120201050901060605040501051912180203070f2102010311070b10090e0d03050c070812040b06060f07020607050a02030f030a080a0605010e01 76
    0x2940c0b00500540203540450081d00c42c2d070007403140b41100301c141440310014140004403140b486c10310042c09071029000e44103260b185c0c00c0b4810001e54003c80200e028610f1400c0190180c00210341c03085455280c5580403c003507000c0d130300b0740d000d4581c1a034035a03080400c203610710b0449000c8600400d041c0032040d46910340e0300740e031401240100180c00165584d420582e1040c9890840c0300c1c2c004040880010500340500040350b001041070000c039030654221380d603c81c001a0002c0042c0c40002201d00300c0050b040c4207104550030101c3c095101c80d03850b60f104070740c0e030b400c5503040b00c407094440041600482101d9202e90300c82d4001c0794016900c40d80452403e141a0341d43d8406034030107681c40b40e10700a48030821050010803012a50700c0f02d41521080d00d0310300f94801160043c0b06a2000921801c00840e141c4c0a1010400c413031a44030f54081e04031441c00c185580b4866481e08800200b800064440000440300b4850b03000710000c890060b12481e211035084001960038004845c40510700c403920680410700c020 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 644825422 1250 644824172 644824207
    0x50403200f161d041a0703180807034d0a110114040e04021c0c06050d0b041413052401060905030d0c110301020d0501031a09060103110105030c 63
    0x18405250b00300c94074141c40a46808082c4590154454a91041101091910080741540f5480400e491920341c1c40c030b030056009000100c010b0010101d85000c0b403082100100c0204802d600a0700c9140240c0060352164202e60701e12510003d40c42201d10600040062006641d01515020788022080107520444a03240905000041c1c03040152540740364902e5030003212010300783c03100003106898581000d00c507811101020b00b0080c01010f00205901020000900d007090031035001444000c0076984400007445a0000041560701c14580640c8809519061091020101c0080d0040310165104032005040858542e000d03251409482d1240100881940c0c0041a4100d10703134036506d139941400720040c511f00e40c40e004207001e40d011464038280f06070401217071081964840b8114002c0e9904c14040b81c003a0040341c000082c1a03081a0000c000c000b00c030607800c0300700e14210072244080d541d0505016510078007803102078907190417414401030380c0d4414002984c0c000402c1542030b10340820b501035003102a = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 644826672 1250 644825422 644825443
    0x6070c120207121104110c0723210d0e1311210f01060c11120c0607050c0f0406240315030b0f15011202090a0308030c120703050403200f 60
    0x164aa181304c401103113094401c144c0c0c0b418580718414208114004585da07a01c03024016002d8060101d0011800c0c1c0102000142089002070108002c045c440359030050120076145d2586142d00a800010341c00d24071805070b109100d41d0080805082988072003c5c0c800810018500003800c043c02c00c218643c1503100300200d400c12032601075090140ca01201925030042c0b042c0c00c0300003084040014003000c2101000d042e03070b2280003100c4111461020705a03484c0790042c680d41d01131301702102060140a01030040340004901100761040300140140008220031104240a6520655040070140440829914104048881c64140084ca20203810702c00001d44289a00071030b86101951700308176048a400c00c042e900700b8412002c0e8010501c051001800c1c4401e44030440081c01ea003c04c02003555135409132242c009540190300540d0f2402c08100099040d4445503100c50003100080108040034420320401d8465034055403100000108004e450f8903044a294030035289100340103225180305020300501881 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 644827922 1250 644826672 644826683
    0x60409061d06010e090601200d03020d11130e040323030a150807050f04110307022a0105070b0c091305060f010206090c04090302030f1c050906070c12020712 69
    0x10401d42903030190000402080386042001c9803810000588446000d2500514242001d80c2c01c85c244260301c84d00d40c480d20102840780e105094100705480d4150f4018204412244401d002140f04410381103200d2003410504044480161802c00800040ca04140c3d0014800c1ca0901e02100c0d003130034411f280750600c12121150040000a10183e880c09102d4140e08100986180b064945402c08098640200d4803680740503035842c80d10715849a03500ea200c480310281c10b42015480b0f0500c448005d55440300e000041c02407100550201c0045800e100e105054604140d5403c1d01e802000e6a541250310405406824584003d222915140c0e4076000c2000c1d06d004480782c0043c00d0310304032042014280710743c03500b181550401001c0c44640c0101150020704914280c8002c0b400d9255403504924602c22050351411184002c180281c01c14020a400203a101840381d00348426221800b03c1900c484040d101c28000c40d02d4401f2100001e0081c000c49201c003d20390054844071a035440784280310409100044a5 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 644829172 1250 644827922 644827949
    0x1412070303170f10030201030e15040c05010225180902090f0601090f0e04060209011e0e0109060327030e03010c20060412050306041e05090d1805060906040906 70
    0x3141c1c2e41500070ba4001c501440d549140d08284841c0600b480785400040d0401d5111003e0030900300c130810101b5103184002803003106038600341c2820881c1040314050240107004400d68001450308044020240120350b084003101d4514001c0c403190306185281d500341a441c0c946c00b10b500036036606201070f48200d5000c1581161440c0000004201c07c047d900f00307207910402c000f42405101ba88420341e992103a80004010303521046280140c0f50b80d06006e1200c0c0c08840902a80781e0360307940c000c5100100c550207880b07200550303403505025030036503000d8003c03142d0790b40200d02c840019250307103200ea1507550b0003800c1064039507002d40d01083c25201d0340103007800030401c5400344589143c00f598410509d2501d0740040c04540c245907035410500191461600c00300030001c000318a19550f154413200160f40280390f800c0e4142c80003d800c80207842c003141e104040c1e000d604d403120407241c0108240424044001490900181440c3c1001020b03040075035103d0b0003c40a100c0807507400e0035071245c1e1000c1c0c00c0114040d00f = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 644830422 1250 644829172 644829197
    0xa120c150e0f1e15060a08160618050904030c020a030c0f03031b08030708040c05041404020108061509041a090a150b040e0a02070206090316150e06041412070303 71
    0x7890a00355400915003d04691911079040301c01048641801410b580f0300d80981d2102e20016541d003a040d000000103000b02843c0c03444200411106408662007070b1103642140034104541d01c1c0b0f80d5a688605600020340d440081d0000b4440c550354041c061005140708681600ca40f02d9075038140d4207402c001c00e41c41c1480802e105243d040044822a10908044100c24030040e07a01c41c0c22a010251103101440500008103003081800f52a480103010041c00400450a0700498450810429141680440e00c1000821a50304000303498114a80000c1071440c0307001469018800200054030580407440038403008000150781306a009409510001300c0850112080454440c4a007041d501031003182c04104000c00c00c5e44c21007a1020b6000c6c50726440140c44803140d0020a14a20841c0c0165625000b1014090941032803074005ea4142c6503c0648410035144a803001e542d80c600c0354400139400682400b003008034526042144e000302c0000f80040401000640c0c070186000405d400440108041c01300f0030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 644831672 1250 644830422 644830453
    0x6071a010501350915090c1e0d020f01020712141e10110403080d0f0501090b150a090e1e0609010b0d0b061b010603020307080a120c150e 60
    0x10703041283d640600f107501c08141003000004822518a800b0502c103258000742a400c0144940190070381d120712240958603011100301d4441140c8240c0a204120503605070f9128042c44413001e00c00c000103000a03050704050340800030070b55000b5184134114421a00301140606075811a295a603206210404900d0000e82045043c031110780303071002c820080d4103801d9560000c00503403810441906000090141c200310311420091249400c050030000c07000031071500c039601d079901c0398080c1c8800c000d0403c5182d80310100c0d402035036071188845501060251503031440701c1e019401003150140c181445901d040d601c0500d0448074000310364840c10403d13141e55466482c820820030591100d0121005a041d6060038000c2000780075403006014815600c4c1200c004644a1004480500900000080c1908401001c2c075020f00142d0008078000e001c2c908001410640003d59200c00c103500844161106035245000c850f1840c804a042c1d50f00190000044074580c0c09100d0160b1003280c0b60090a250500420325 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 644832922 1250 644831672 644831687
    0xf06110c03010213150210110304020f090910050618040b0a050609010e01030b041704090b19120b09010f0c03090203010507020706020714030f070902042c0c070206071a010501 77
    0x2032074042c0e4010460364940c080b2001e1000152000c2c2020341400295004089240c040c1c40c04400c03515030702d08031501100c10751000156210303070301c2110922041ea00e04001d01c04c0703080041d030b0f00035216071240300c5180300c0c0385003504401ea12910290100043e80160b805003102002c0607541076810000d00c0050005070784035070041645c420741c00d884501e2a9458030078041c840d440c0511016200d100240040340c10404c00f07101c003c10002800038001d03180d5444d4040c940c01007008038142442018203861151140c0580c03a1100200c902403001e4500d80082600c031200f600c00003e2459000f550f0303078010320206c002e85105a6100440715540000d0900e030910500d401c40c0c5010703040c90155401041c040000707580c000303407401c240c404e240c100d00c400d440084040307458000c0203002c1d05818041c041006c1030211955000d08215a00354001c034604014003c0b14071241000d90441d800b1081103000001c1a04030004020500030344050229440c00d1455151828081e488032640c01d08404044010002c07503900548 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 644834172 1250 644832922 644832943
    0xf1401020a020309100203090d210207080d18030605040809041a150a0c0209131b060507020415030803041b0801021c111c020909070306050105070605100f0611 70
    0xc6180c0200c0e0640a9500d010300c00c6a2445140d1145480034403d20078010b5810f188001343c10905810524900801100321001918003410840700c004116140b00081d00e000302c44424002e41580700c40040c00310742c018106000003841e144103041c00000a441c41c82810312a5014804158444002100b00410303100170090b100c1c40d06036061508a116a2600407142100000300800707952652a10030944042c1c107581d00283d4001c02250800411b80b8110200c0180c140c482c01707202e0441c6004546859030320300da9001b2000080c0042c0700781801420316901c40140c4240007080c0c04041c503581ea42d580840c4d03104440c111105601d80030752026030382c0c00d00d00d02c90140421300029400e1031941007001403a603519101c070405641d243c00080402d90300d10000c0310302d0710140c4142c0c07800c00100814008d019500c42008580210007a10000c0c0a4074424450801540c80c141e4500d0300d04816522007002804024040c00c10003a2000c0740001c0c03020000c1504002000b0b00d45a5080e00c802200d0b4450030521300c1070 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 644835422 1250 644834172 644834213
    0x8060f0703110f1209120a0210050601110a06020309100e031207030b0d02061c09080408070f0b0d020c070b040602010b041a09011512020a110f0a0b010513090c030f 72
    0x3c51640032a902005540f249084c00d058566543d581d0a04c031481c000d8601e0711007804540006400041e5640800e040e160340b11020002d02c80d44d01e464004442030445104070345c65503003280c1050340001c1c0e4160021038002c54004111540640b408004004442c0100e1030032480303900004505d03407002c40da61060f990012150408001c001d0070880443d081048010300244650f900062441214905c401d130700c091800b120104110341d00452510f1506984103018003803e904c87c5000010315140020801c10039282007200b03035400d000380c07110404042e400c001003c50f00c9000d1000e012566200c14800760000b000140d00118801c00328009020449a040c52803010b01803ca80d0469055120700741d00c01e04503003072140c041b00c20000480048031001c410050408420340000b80841066a2200c0008100d00b03c100c180e8681c0c3e060b003000da96032002e20f13340c02422250010010083c1e464600300754005200001000b140703c10b501c1d5140350003940b4a8008562003003240e5800001d00201c1c03114482c0100403503 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 644836672 1250 644835422 644835427
    0x60708031f211505012103020106121112030a020d08060f0904031d030321070207170706080c030f042d0803011418010302060f09042a0201021201050d020a08060f070311 74
    0x3d01741c01b070b00442d2842c60344030390b40c541c010040503c01d6206000034401c0c151488684421072601144950059032010b200b01007002c2c01220074840801182d2240119030014003d12090610903651075000504a980c480c40c6003202400d00c0d16000109803086100341d440390090180104010012244180d005010307600c14010000c0d99641c90a0b06440c04142486c1c41e001603079100c1c3d040345080025003200030302a0958030105951800018143c00307a0f05140c41c0da07907407651100400d03c4180401c8940760442c0c4000000b003404182d0b181a80034100080c003a0240c4092500038034603482d240600c504176080d03c80000100a0703581e404000c2076480000b280d40898031900c000101c4100350041c000a84500400a0b040704514038003400c80d0a035035405401408211900f5941c40001180c019400e54174114400c150100c880c8103108a0f0300c1255a9074144a5607428981800000d121002040303800c00381303403000420060020031420307104454002c50401d41d8540844000d00756907100746104013240b410b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 644837922 1250 644836672 644836679
    0x6080a060504141f1515050c073c051c1a040f03031a0a080307330b030f191401050408090d0303061a0414060708031f21150501 56
    0x343c074a02c2c00304e000003601203111a010b2600d026110300ba039000620211100d0b118070f40d240d82010141941150380c1081d50140341d51503030240004440075140c0c140070310603406038031814012204024030f09940ca280040103a81c49070041000038219044000302850403500030303820800301c0c8038406e0300507511418501240c2815074540341650302c811402014951600a19240c005c4040d00203000c03038200411071060907a64003212900ca5001c40700c02d648580820084102440d250030300c0c540303003c1c1032030300503420441e6209529000f8070360344811036414060ba0a004030948020040110b24a05210005036011030514041c029041e0001e400c10240c0d06003001c0201144090058070311000e41070392003031030344561071904400910658014580c00040b9031410300002c0034880140c0103988046040090000c401400c103d01070040800091003410300b040050f007045c540c103d500e09682104102c404015445858011150100d84d440d441502045040c0d142801040303e8000d08900000f00c04002e01e504 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 644839172 1250 644837922 644837953
    0x70503030408031807030309080c1f1107050411030f070e011d06070b1602071d010b0a051c0203160513030b19020327071508060406080a06050414 64
    0x501c0680720b440040001a980c3c1d006180030292101c4030816181c0641d201d1901800800042c002c1044c00d2080e03002c0c07044c181c100b40c0b403400f141070031942d081400c080c19004100c5802d03d00700304440050048042c0041c55403500d0046060040c0300c45c40103600c030b190124110350103143c0241804200814a0b1140106036001288505000d11524482c22a0524103010a6080c865840001c0080d03490a0401840c80c1c2071407440d81c00c00700e19a00b0740750001c0d0340300e990100301050b410303d00d007038200d540300104010300709000109880319440c24003505100040c00802c0c1a86c40801000c07010940001c00c0201203075a600b5222041c810904025040140780c00c0f40f0f010000d42400010803d0801401007928020f081c04079045440880070255a2890000c0d00380e804c20030b22400c4026030915003c0080b0022801141e858140c6403841c403031000a4081e16000c07900e8100107002190407564481011032018424040040414015040841c1c58105460203808500700f200402d84680c006240340d0f0342120 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 644840422 1250 644839172 644839177
    0x80a02010b150306060a050408160e3301020c120714040e0a0609060e010c03091e080a030f02090402040303050919120b04060b2101060b0901050706090309091a0411070503 75
    0x94090305c0058503030380004002e131014407072a00301c09250b2160714046089000841c404500340d07500504242816150441010020031031810080c03041303806509202e1080702250a402250b080520445c1c00030001080403500c003c05d044140c9203960841a01480038030815191031160390019503040001c191403640454440d402050002c003000d440d42151401c1c0f140c903400007198100c400c0001c00c40c14a12000242c014610b000d800c032480d085c0880055500540b0842d1441d07016001041c40e460300182c144214001e010a00307078450110b50912030303281035444a06c05000550305c01d40b030b60350b40c40b0861010006050305000d241305400e200443c090080c1182c0d0707d03004600e07030b034003034181d100e203480300d05e0702c2400b810b00d420b0b0560304409100102c0040300145159a50103041280081090b582c5403114004c0d513108515106000c00c000300704c0e1600144c01503002d00540781c003e28002c0078090b2610b46020a40b108801240d078400700d10240700039507143c14494000e14200e10f29060b445c00701c2640d25141c4a0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 644841672 1250 644840422 644840431
    0x20d0c020d020a0314010b090a0203070516210f030e0a080a030f0f050424020307140d14010b090f0a05090a0902061207030c030e01090f14010b0d080a02010b1503 71
    0x1191200280307411502e8215140000d03662040c24001c00b0801c410007079008140f80a0198450320409010a01642880c401c43c0d0091189680e00c9190113064120000c00c081108022a0304960b03000b00c140c0103072880803401400414559800890407695030000b0152518401220b180350001c085200c00244910112880c030260b60038040f0f00000d0644c5001c0003010300340610740045041000f00b004105111410a18403415034800499205624115000700d00080315850081180785040084524104020706241d0044980124803944010701c11052a01c0130707804100c42020114a00d481841d000191034000c100c1959142c40c0c6502e004000b0307866520203098515101d039240350107001e54442d941281d080344003c50106101e4144610010014202d001d0306800103441e1020000000906000d0710495a42011a092000b1070503201c071010510400c3e8001c0c0e0f1503607980b0720481e035600c450603043c0016014185e01a00c40903080000781c00e40310300360f00c0503209150491001d0070442202080d81d401 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 644842922 1250 644841672 644841679
    0x9010903150605040f05012c010b090d1b030213020708030a09060b15090a0b0a08150a080a030207030b100b030c0c071802030a0b010f02030f030402031518010507020d0c02 75
    0x703060030801d072001802d00d508030642007410030030704003440d03c0580c10450407500c01100315610403820281081400750403d19002002c4001c40041100c0c22529014241d1f05070b0051284c141408155201c45464008440506441068000030015450445140204840c00c03010540c542001c0341e507500524031004000c0112190756181900c140311566000c1d684036900a41007409520401c1041d45103504803580041c0300711003401010620230100030135919404100d40303844d800b40d2680c20300c03051070407400e904054200e1030314000041c9115042004488880c020340180a4242c11401d01e0b0342d1440c0f00915015058580b080b08020400400301120750140611403080e0f01c583c080100242008641e80c800e10794900b210007280c00050240d0700035070040322000e4040000c174192100542c1e0710880940305202581080c001201056400c0b0000c6a00a10007803e42b034003008103800840651109a504569030640ca0380d000a015209110b9241c004c40b440c0000c026529540b440108010b6141000030700 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 644844172 1250 644842922 644842943
    0x120815150409020a080f0601030209060a0518031f11040f0e07091d0114040b0303040909140102032d01151101020d110903013803120a050d0501050609010903 69
    0x100c0c0c064500c241c4000d0000100c0565469250307820040000c5801e0750600440f00742c850101d004c640c001e10803101100750181080741000e0480b0416a01c035003240080c15180641c21180c0555683c1c180b244460141c2503a12103c501012040e00c4411a0720f400441c00681d00d00b08002e00c038002c8a110440101c0b81303c044420328035540c0140440741070300c0ea5800b140c4002031100300140859424068075041e42c0e000301c0ea0441000100040200303a980f040303070310b9405410400007070220030b41c2c0e60091042c00c1d010701581034410404a12890891b403080322683d00030030600e007040b03104500515100140c2e140d0305039400e2095040c907484903074840c02d840071007040c00361400300180315200c03e4050f40c0c8015601c1000b009000418450b07603a26503c512240313403095190007860000003045144074070640c0714403101120303540c3d0702080c610b0942502c0600582d052062400760340a04802a000704088040da03540e0540715080d80580c3e2003950410f800942c4034210032f0022843c281d03440200441203a8000c042e920 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 644845422 1250 644844172 644844199
    0x21201050607140703030f11010213210c0e15030601060207120f12020703150204240903080310030218071d0a210c1e0627080604120815 60
    0x3c140003400862810310740140348000080c95081102924910b02079102e50f151034240d10010b508034421407068042d05040e0394010700c91080c0d24110390003040380414180000361034607210a0348041c0e0a0788180340740007100c000c010758004404400142d4020981c02080194140140a5140e0350b480c0181e10340c865140c0391034820300c0b85214544481a401c02e2650504d0109058002e4031100103010503110300e02244144140280f89200720340480d00c194110850b94446200e4004540f16000201c1040242c00c802c0880440c503010000c5020313980814803242441e1446c414010030420a1200741c580c86120010040820f4202c2007844101190000310300d400002e140004141d880360303401c40d44003e014030610801089580c0c100b0750310706024880d92403d150741e8040e02010079040e1241c0b4420f401d0315280405c540b900440031282180381c0d80a4510b0b004c588051044202c00180d400810142e000105002c24000e40c40401249100d107480c1c40c0f9410b00e009040303180d4612480c0c0300203000d040c0c5034102c1c1 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 644846672 1250 644845422 644845433
    0x6040c020c0117062704031d010c11031015030519030e3c21030a120f1b11210a090e0c1201060207030222090c060503010f050103021201050607 63
    0x40d00700c8a6201e20700524410030383d40e03014121701200c0481c007045283c41c803060395100080a40c1d2030100140d54801a401b1103a40301c01c03200c044c2e070034503941601c075800b242100b070b001c0380c090f400509040c0340801c00f09078910b0511900e401812440c4085540f0303400070203c04640e2002002c88005819252000046101e141c0c07900301040740c04402d80c0c00e80c21084080341920b1085031620000608491080e82c10101c200445400172401c08500311540c8100200c4400d1801502c202030801401900001e9850701c149014043d1080c044420749000c610403e20120542c11107040500c0c4c04840e4024620480368400030a082000d844c0302e60009a00440e0034182503200e0110000507064140c1441058140440d05c0c40c0d00b0f4002001000c0c0f003032251030001c5041840007410201b207e400921810001d0101c3c032426114403030703002000c14225125520b00f0041160344030901300520680e91000d9581d85040b44860190380607400060415004004007030304500b00c07480050640e182102c2c1c5507612622890038 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 644847922 1250 644846672 644846689
    0x10909110307060207090b060309030d0b0604080d2606090103031b0501020f07120819090201031d0604030908031e0904091505010e0a02090d0b060a05060409020306040c020c011706 79
    0x5003503051082c074030082059036020408904a903c4c2d690203101074103000c01001418001150090b69503401808071000b140169001007051140c041c19442c81d2503290300e40581004e54400e201408608062185214410602c1c14803036a45980c002d02d4460b0b0070070200281c180101888050108407440004d00202c5440c1c151075414a07138800003c55071a40800c05d82c0306550011801607031005207441c0061b058a008004591041054801c14208110040c50480081000d000c00783d04240d5500440310b4452900c038844420703280b0010044c101441d151a00500c914616080550700c0e030070038050751407441c04121054141d0110700c0801501e441c0020040340c014142a0b6028118400c48005204504c0301580414148e076100045c480391a41c90404403020392040255054002c00c0080300d0300d003c103000910480d0010401018900e545548200040750750300a034100c0e03034ad000c0d4000148012850b1074841c00c5512103060002c0c1c1440007000c0d00180c003100b140541c841e00140740d2000200107650f0600b5 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 644849172 1250 644847922 644847953
    0x16020918190303150906050a090e06040f050705150309100b06070311010b06040b12070903030c0b060f120714240c01020f071a0609090c01030e010b060408010b18040506010909 77
    0x114142426a103015038400303010181b0500b40035907040c807004249c080b0213010304191501204020005038031503586694004041c10000c3da154002c40002054a64070303120044c0c030106c0038604280d02d900b05074008504004121201614140c506002000f803038480f001900c07040394150800108403115030000f40e014101145480d90f11000004011030100100001340445820350b800c044801c2d43c80f08400d0320090400d00004e00803070314031803000740028802d4610560182025200f4480222400040352102000c0c0c103c15100381c2141d8001d12a080b4403050510406c0c2d0b0403105da2103041540075075501403000e0f405064414010001c0c0f21544041d00750100d4015401020401d44d480c550381c2841c60784603140da030400c0300020034000496a2403030003649050203818440007400c0200101e0005400401c0c15025000c15552140085141350755150301400c0101900f000100e41d05454008100450880340541410514041e0038800810030010303c03141500c5003942d0000e080b0640e801c000101264625 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 644850422 1250 644849172 644849201
    0x902030114040f0c06021b0d11030601030c050414150402070302071703040f08010e120c0a02090103120f050f030703090804030b160212090d1b0b16020918190303 71
    0x81c002007003c5101a032940600402050740041e4035220120707114030341141d000d8000d00200507001c025280c4074111040841c440c20302ca90010701801e001c00d00300002640295201c4c284041d08101d281010301034020078010b040f11260790762800203010040c1140d00b0040a00946d03020600804140c003c001410191001455003440048001c0e035540d5a0360040c01148138940c181040082d100c84140a90b51080300c18002406d20f8002c0c80c40b403182e8070742000e50743c1c2030b0034458250344d440940ca171a00b406010394003400c4100107280d1004d41c00f90140b03101c45042010001c2c1003010b0164490f11b001925080500c91502041e4844c01b81001d10803070080382c001401401d02041404500480700484810702c2c9a290240c50864030004c0c44402d060040070747c4a900030070f4250701e0800045110b5580781c0262082055001020748030710000c3d91a40100a007804030320380000c5400254680400b40f113a00407602989010703200c0c2c154139090703140c51101c908242c806d0f05020400041500981140c1c11150042 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 644851672 1250 644850422 644850461
    0x2a031d0a0b04060b1c020139051c030608070506030c0d0c121e0606230c0708070308040816121101031b0e01080f0c1905120709180902100309020301 65
    0x109840420f04100c0001b213000c6801000340e0120641030581001102d01207180540944030041c2c041350b2400c070b4441003107030301f8040d2084e0415800c0070241710490074480c0da9000584242030038009444c1c00c07507982000c3c0c80380001f4010884440021002c48180340c066400208200003010002c8e9508244140698046400d2440080c4018580e0f038400f4174912520000380a4981e03543c00030b0700c0040300c800394510484040b0792042107040c8d540340204107003071280084804169844a01c1030410710f036500304583c0000d001504100d002030410032941c20501100c480d490355840d01d25411080c140000004162800840034000503a00a60014680301505080101c00304100f400041c045d120b01f4000c0c90208204c0004140304000c0c0003c03d500c5450341000407445c00c50310080ca07101d0118404007040030000204201203001030319004c00390042d079842d25400f10082c109100340c0d4400712584100a991450400d1920240c1d03500b40303003103521034031500f00001c000c00b05002080c007400e1007010307488860095 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 644852922 1250 644851672 644851699
    0x3120204031505090c01030603020f120a12030204080d030b030c1c06050f01080f010e0331090b0a05010c1a0709170604050c09010e0106122a031d0a0b04060b 69
    0x4030f803c240e11990314042036a1090742590015400c42d50140400380d0058540c0d980c00100b0306141c000303000c80c45412411201c224417a0b03640c003101800107084080009802040c01c0082403420410b002c88c42800c1d0506009200320a000f0030307940d2243c2c00030719210701480d100a002228400019444458104100303000130300c0c0000188400240030f00c99030591348540240e9a00256040c86800240001c5401841c540345500080c1c04900c001d0260384203042ca034040031440300e43d201c903d00100a1581c400041103e040500c20000c058040e80c1c400d60620a1041200c400280b030180e003141d8240700c001c130201c6903803140e01d002c48002c0850780050310124400003912040e03c9c8001041d9100720310840c201c4074000100710038004180801e10810140700705010040c81218080d40044c409544602c1c00003c00c0250794100040000c00011a51141c410031044080180ea04d8000c3c9240f03010140308502908408028007956080b01c20406001030780003801180c104542e94001214410000f040c010b251044d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 644854172 1250 644852922 644852963
    0x804050a030c391e032d05060a1b0f1413140306060619030b03011107060c140309102310180603020109182a030e070b0301030312020403 60
    0x1010100c00d958092980c000948013034a40300c1800c880043d9004184051965548807603800c2c010070382000c2c2c802d400202686013140310364038841d454001d000030300041c241610404102ca454103200e42080402d104203886031a000903c48481c10864a0002482004902a2949405a4044d1107a50350142800240c50a8013206841c1e4200046045c1e03400e54545074200051071152603052415030400c0d0b411107800700d01070f50020102030340203800404c020413010f5040200b640022011120b440d650302e0540701869006890303901d00d240c90aa500e1075810105038a03a533400c043c041596040f038650a0b01262070740c80031140038140110a002c801030303050101004481501c14016010951150300c000c10131011223000d00421660103071552401e00342481c10616080c2884211005015280ca5100010105141060200741c0c80072808280f40c0c40b035907100070203458590921f640190300c0780909020302e04526003124112076250908991204d418044080030f4060395001406541c1000c0b40c4a08608 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 644855422 1250 644854172 644854253
    0xf0703030206060906010e130213030f060c0804150b06281b0309030f1103061006030c0503040512030907080303010b070201030b030d0c030e040e0307120f0804050a030c 74
    0x38425000d80d00142e881c04244000c0040843e401400200d503900581a50b08007040c5102603030140381000b5242c400640814900b00d503803540b00b02c13050b010400540c1c041c0215441600c81d100c90925107002c0d1030030651200807400314940c1d540307810b059072108010000c0ea41c883c1201c8500c460741020310ba070656407085080e494201165000c01092a00c00711491000c00d900003034017038030b5042e114001c5060643e00c661030410b420220440c0c402c1445150300740703d0341e01003156500c03440c0344030003040002e401c100005058038221200328040c480c0900a0200280000c0fa101a2005440c842551656a0900d12602e480d8031035000d05500e0000100200304a8404c0340140300c0b80c0e000380c0b01130000500c290103041c0d880c4521144d00000502103020302001034131602d81e407601030b28018404a82c11410310a014115801000300300c4080311860203126010750016800c8141c61030900b481c2c1200d00d0a515100d4442c005130030020100050380c060340c41080322200c0760402030542002c50316070b0450103804013030400 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 644856672 1250 644855422 644855429
    0x70302120105010e070c0506040b28060501020c0a1d06210106150503070509040c0e040e10110405030a030f02011d0a031d131a041514030304051f0903050f07 69
    0x203503200b100003102c0b540544189815194400012318803903585488a4107524005450712101503a401e62020008a04140c01c030103014811000003826458000007900d00755003100301c41c3c0a11800c0d82d040191643e50755955600441c0044002841d80e521b5001800c403102e400c94000740034008091118818605521820540341004078ac0c191000218230180e0f40b5000844010000900811040d4818103003070300b280a00a81500341041018282c6002030199213404445038100c3d40803003c0b10484100768003480440c0074159201070b2a00342030001090701c0340c0002c0005030078010022101c282940c070035400107451642542c0c9109031817494810751510340b00700000c181d000030203c42c1c041101c403565030b180700000d16009210b2002c0c03800141146000c1c048603007080400d0848403c904003540c8540c01402c19407010034565240c200d0a01c3c40c0c41c2020b00652100d40d0090f80184810311640d02c40e1081111a5001000d8080ba009040d80003140d00300f803542c00040403401440b8406200c0c04000a080c1c065 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 644857922 1250 644856672 644856689
    0xb220e0f0903090901062706050c01050c18011404051c0320061b0d0c030b0a080102040e01060309050109050708010209010e120312100f030c051008060f040e07030212010501 76
    0x150710303800d200316541e01540000c107a2040c900f00040091500a00082c0300d4030100712042000440f0f011402070416042d07600140100d02c000a608080b283d00f031007001ea02c0820041c09500b03000440404200c81c40e88400050305102040028000910085041d40e0052900401080040034503108804900c5142c00c0106d01084200c22100d02c07007412514442041503019004041a698504905035041c1d010b5000c00c1f10390000300115480c004003402041800e46840e100813407109401c03007c1c060f0903400b541c010b440607403040c4028414142c412130300504480151901041e1000030382011401841c0e00d0100a0803441001e90000c2c0c90309040d0042c01c61001e09888825100d0700703010500844804a0001c07070f1702d5030070400158106e0450700c04029003041e2410200000c00d80c98411044910020350803c0e0f54050184004110303a203862191103d401740f0710700e0028114181440401d80c010040030b44907102d40e4580001003c2d51400300000c0d401507070020f00b030901606800c02c0c8180241b00a0044004 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 644859172 1250 644857922 644857951
    0x711060705010c05180609180a092901061106060405070e06031f050303070f0807031e080a05010b090d0f031e08010305070501020c150313080c0d080f09070b220e 71
    0x66182020585150901c060b00d880c0742014100c0407510400401042d0070119681c1d41480004548039a545007164bd40d411615000400c5140c0400c0203140141c1c010410044080744002c000500400e550341c101c903080e900401c090325003680948100300c140f080990002c801004001488464200101302c0c0741c52001d0a0381a180c640040c15280d200c0c0710001b5110f04044840b4800040481c0c0003404a076009103000c144080ca41c02c05554030003125280f8000261041050040b02010b5214407030052440002491822030000045504042010400f40c40c150390034840c08181405503010100c1101c4001c0ea444c024810403201405940003804107072514412a03202040325400018141c04078080148004240c0c00039030b506030900e0b4401040b6211481030103020b000040c800c440600303d40e00b540c1001d041d010f0507500d0002c1c250040107101040c01c0e0848000d00c5151000810312905035601291280e0380c6a1002041e60705603114041003031508040d000c00000c10031b000c07000035070040340c0c104401c08 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 644860422 1250 644859172 644859217
    0x920010504060e010c15020a02031215010e010806120d1d0a0305121602030303011818081e0c030403061d0327011106071e0c05030711060705010c05 65
    0x54003400707039006080201d142c2c980c3c0520300d50301850890015034032450340c80d0f00d1020700b850350609076044000c442015a201007020226508802880e6511078010b00c058414000520002003240146000782410701a00b00081600c81d2101401350300b43c1c0c40701c0400c070365640c4940b800c01001114104600358110f41c0c0c070b000c140b40340e103400c000c1441100d40040007011034101598601540707510201044444803082e420510041e2400c2c00030714001c0c00b201409413a5003184070743c00700c00d540304036089901c0118030603864800149103200342e40d040c0500100740b40700e16140b01799800051280e075203100c0c00c1e032101090000400c80660400e45060460708041c03041d000c104a081952030084d910700b0003a0400c204a85102081109140d40d0509814500f40c1380d2480030007900c50520005a856000003000e02010450551164102420f002042d141501e0b1042c003603203030240c890103003a400404001154502040c3c7d40d41d4001926085030b0024000c01990340d185001500aa1110901d41c0d1005d18400515 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 644861672 1250 644860422 644860427
    0x19020d090614040b090a1d190504030f08090703060612032304030f0809060a03091e0f06021b03030f010602010f05040f0b0c0d1805060a180321092001 66
    0x410302c0721001459503040c2070410724900182e0f006030448a4001000308400034a00424040061303102040003103d10f041d0070a138815003074030a407142021100034201018400040e43c8000d660545842a15081d6070359150f0050007802c01e20f0503800900b20390b0400002041c0030503840486054a48283c44601d022482c10724001100305451012880188090200b0000319020107082d00b070252143c41c10528040c13540b40021007680010100c0c2000a0366000e0345d400700400600d68111034180e00090600004440e0b030b641c5e01c43c1171700c400c0c0204a55008900d101c040c4030f60754101001c00040f441038139200e18003041e00180b220301c2441844015030900403961000325580c495a03003d40c1e002480348528031403070703180d1082d0403070007501c201e0720600208440540000b940c0319a1965071503849609a003026036041c07442c0750503405041802ea8610b80585000c60149030081582443d80c10b0030b00038034030070300740c08541181c011b4105510485d41c10207408a04211a245d0080441781043c1031070100c0e00c1454004 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 644862922 1250 644861672 644861687
    0x3080315030607020a08160b0a0b100201050c040b070c12120207090c05030604020a020c1203070c09050705040302130e0d05040e07020a0c061b0218040c090207080307080601020319020d0906 83
    0xba0400341c5c01116450780031030740700c0d030081003140d180300e1008400c2c4a176503403201490541102d0203000c0c5655140310a40504d0403207086840191644024019820320790100c0d0301038802c51281e10300340c80f4006185420041324504101c0200b0b00e1900300c507684019800c054840c40401600140103000b18100492084494403645203d1129a0348030313820355540c141404020741c407109400080d1f101d24401548555207900301040c500d42e0f020042c40d00c1f04d681d8034000c40d40c891540c20003800e0301e0402c400c12040c1039000c03082d41d0840b0f0b01104c0c602c20803da2942c00c0b100914410702e0222450141029920740780350040c0043c0f044402c1008811602d64030365404070b0b1603441d03628004120007180c800411140303124031f82c0203001c0e40c0c81017011441508a98000743d460101a10b0020440c00341c00200014003050b181040000d00c1034a0307042d841c2803c2c03641c03001c00a10000f0845014007a001001c00c032140d20030800c0e54102c060001c00302000020410000c0d41d00c0c80100c24080010f0321303118012804603c514003 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 644864172 1250 644862922 644862931
    0x30115150908072c010303050909070e090415150b07020607150626030712030e12190e19030b1308030a090209010506250201050f1b010c0c050c19050307030803150306 73
    0x88d0a401c1c0181d074410085003580140c0382d9000c1200002800070310345d44403d81c05003d0b6100301000c1c1d8140401d0f0350240d0030394400c031141d0304802189040411140802e42d04903410958111580c030346c4c4110914000c901a1455070a045019180c10b0010800c0c40d01c011000c0b9500301d0740324007502596040e101c81d59036841003800042800314140d2400d01090300039004048000090001e5520156260010f60500c0d01f1110207070f6081a01c619055480b5a04a10140c00c500700680d0203500001440b05002000c0300c040c440141048418030003c0c0180310443c83d02058958000103281c0d03139052416005018204201c0181d2058101400014141c030700b00f03044911412504995040d6080920310070000c41030242e2042c1d044c42001c01040d903182c0081d20003886400203105a804e080e140b140051821105580b0b2600140043c24105034017142d0009800106400c048903100810710030300d0085200f101c4240d110070380510a070100802000440005184030b0003818800c165080086c5080660310f407003d03907 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 644865422 1250 644864172 644864177
    0x70e0112050415052802090a0e070f0c031b03030c080105041e0e031e030a0606140d050711030c010608061312050a021504140c030115150908072c010303 67
    0x80300c0c00084403450b0003d0382e1050310144030346040c1700c01001141031407100103203e10a296001451103482e140035107107440586064424541c0d649003001010f040640c0460750700003032101100080e0105071013403005001004c91800d59038404006860050082d240750105800070500e04000890581414841c918582c104a001c0001080d001d1224000030071442c04403244d03500040003002021050090103040c1d020342c47c8207048e602c1c98a10610800c41d00b454028038200200c85880e1020402140d05071001c150740000009955100c0319002d5072604c000207109203540c00040741046180d80d040d0f1000c400c60f040e200903100d00d55503005003c40200b280310401007440880e880c0a01201d8803e034041e0070601c0da10f00441e444c0781a100c241c110340c600100c4080307402060461842610312011300600241c2174040d40280400808a000b41d100d40d00c09004440310041b150301402601c5105007a080010400c0e903042d1b808590b1540003180c10146412101a400711641c52a02003004144940a040340d4155 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 644866672 1250 644865422 644865443
    0x30a0c0e01091202030a05010c0512090102030f040213140405010e150c120c0d11040302040c110a0308060a0b030f0f0606040317160212010c0f0207050135070e01120504 74
    0x2088410843e1000141c2c2c1600c20200c40742d0001344244162000c4120940380d032502d448407044014005900100b1144d96079005005208144034036126075604907504032074901c211301041c040c0e04014999040100c1c49880c804081c04184a03040d84032419210703041c0c0998601900801084a030301c3c41c141c41c004002d0800300b02420511203800d5806406c00d0200075440e180c000070079048000e850035000c0041103200009410021854217114041000080c1d0030a020950030190352561100008100a0144940d84001507400e54803c20700f800500801d52900c0d480342840c6540f0760300140c01321110b1140450710f0001c14043c0c83c0c181c044e05c00b00d0b070b8442c08006c09036080101d040c2150b0440070f40007003034032071204504c0010394811000000103401400000fa0308a24220300400d000c074440403143c1990007080c801c1c050359034042101c144006050f03120041c416441c580c02002c49442d41d180c0c6010300c03055000e0011a035030000484080c2042642c540c8910010b807112882152025100100352001c0c6 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 644867922 1250 644866672 644866679
    0x18020103050a0b1c140708070e0627071b05240f07030f0603020d1a0a0b030a0201110a0b07020a0c050a0e0f040c0911040f0b0703020604020d050f070308030a0c0e0109 73
    0xb0480b4504d86244102480000310f20740c0c0203218906400b907009203145030407020052225843c1c80c070300e1039841041129024504a8844c81e4224000c4246594182801a4034000b9003982d01442841c6904041e117080c0c04092081820002c2d151103003001c0042ea00c1c5102d030081300e6224144801680645010a4840120b440d001c0003980104035415291400e140c07207030400009a5228032070f21800b140540c002c0070621a800c1004020404d000f0481100c1514012090145440c0010354540059081c00c0c01c140d224191041c492070987c014000502e031800000c20400581e6020812040883c440c0e9007544840f911601048540c2086020346801c843c801000034454289810645420034051072503900f4180d1210110f0703041e100c101721099800000001d00b00f01c2c40001c0c9541600500340340031014200052a64001c0d1501c1c030103000070b4824500b4500070002d220050001d5940061880304032a4071070364a28009045130803c549280d4800c2c6400e051a95031802080000c582c0c0301c05a4403250038505 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 644869172 1250 644867922 644867959
    0x180d0c03052406040b2b0f1203180c0909111509090c1207081806010806220b16050d020315040b04150611010e03040807080d02030a1d06070618020103050a0b 69
    0x1c04445510084054610902248400140720101406810f29502305640e00101078240c1c0d5158004441d100c002400c0d42010501501c440e1054451510001c1025070107070420690101002c0e00480c2d100c60015003c0c01e20088071030007011400819134500c4400d41d0fa8098a0740c0718094440d00c00801e5803010001184141324070f02c01ca92010568400b61800903041412600c0c10501b6045a00194402c2d4148641515170781e0640d0801c403255082400345648913981d0101800025000780c61400d2202483c1c4210741c000d4082c1c488030341c0d220a003103450345400b1000c2ea0f04402880c02d00c501443c545a040d42c4103090038040d00d803200e1500812101800d217028011280640202e9560006541e145003104400c0000e1000380000d148450080a1880c00c15400c1c500b01140340c1e480340305641c0b040250028003074111095500b10307025551681c0c10070403004d0100d5440d01c04e425009182624001e654081308528404281c450b500031b98040043d40d5954101004842e00e9030031055004540d01703000c20715240c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 644870422 1250 644869172 644869219
    0x1f0e091f1d0c0d0204120b06030f030a091503060503030a05030a0c0935010204080a021207150804080702090403120b090c0904020304140109051c05180d0c03052406040b 74
    0x4002d28001403170706507110000340500301c0862084400310680820b010141c9000c000f400c918804d640040c601c1e20030792040150890040c0e114078030701100d03880002ea45890003540094010800034007640d5442405441c0105254811030300d41080c02c1c0b50040b100012482482c003002502d00004154103440811658403015080803030002d0400f805418403004a60428000340004080e841c005100c905420300c1001280214405c6031040d5501440c410404029071800010380700b8054100013203252240c0c140800c0070f12941c0f8029402c1001d030414001003507846807516a0940c0b140320708002502001c0d0410156440640700d580c003810f82800711341d00d80d152541c025a002440b07503010034810743c0c0e8103038180c0c20744a01c07030b10680c0e2507040514602808034822400d054800e4083c40c1443c85c0c0200e090311404c0c17103020140003a019100d029040c1d010402c1c2103410304065504182128403070084032030721800110000c0d4403004140c40d14000308915080038041c82400700300040c140e000040d100c801c0444150f = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 644871672 1250 644870422 644870437
    0x91208070203010b19050a0902031302011d030a0c0503013801111b0909070503061504090615090b0d020d03051c05040f0c05030604021f0e091f1d0c 65
    0x555035140e00013000d607620b8688124016094122501051409007080744007469a409003208500410400c1b1382d009003925004849942404c0500c00290304985506821010055103501407003204141c80c03d00c021422305d04200c0d1022002440560804c91a0380d03980c1600c020058103500c0d03c040300d210f00301d01c00c900f501061181890306485a43d0f90640c4945002c0d92a196144949403884000c000c90800d204010780c450400c000070300e0340300c0c03078640844d80d5410014490388841003000280d003510b50313540e006101580c0d080541400740842c1c90103c80340842485c480d5610840c035060300c011403070900041d0440010740040001c05040400c2c0ca042c8d546600c000d040c00c8004c4000e03612818145524860603024500407010761068141a107061a004589500700b40e01c02d41c040f000704030059441e00b1500c4408214030302103100d03005d800d22064400b0050102003d920502c50001c1080c000b81036a0080091520559061245655a100c608208010051007403061200d0300c0007450001c0c0040080092 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 644872922 1250 644871672 644871679
    0x120c15020309190f0609030b0109110903010f05010e010501020106081507030b0907020109032003190e031b030d050a020a080901020a06020d0b0907050405060901081e04050a0302010c0912080702 85
    0x14420b000e00001c1d4410fa800401c2c0400d40b99885041c09044580c2803100060a0903040007034015046840c0c0110004052080c020b10765207400b03a0f5a001c4801500f83c3d01d0030340d0042c2c024810b01c1d29078945100505000d02489108402a0000051070345c414083c0c0c4c01211420b002400d0701ca00c8590f150040240c0007070010b001c1c5a20b5220310b640c0c544400358078500c20392540e8000a213040452500400304040d04880005c000d40c03060b6904000c000100450744c5880328010391017a4042280004e40d6000c10021103d0740c0350040d682444c00050310003040c444401c4007201640c40c80d00c5011000e8440d4060b541400e001680118001d4002441d50700007041054014011140c600c21550381c0d020983c1e100d030f0008a00c4d03030f494024007449400c01c2d00105412400c80d0905600345410440403a50500517804158100904040070880913000e1254201c5801c140f055810280c2c5060301b0010f030340d00504d0000310015880d14107004103551003290203c06403a64070007024007042a81e2107502007a04030000980c3d2 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 644874172 1250 644872922 644872927
    0x6060102160e0c1207090f0b0906030a090f0602030108012004140108090a0501051302180f0a0906060803070f050d0c0c09050a1d0d0905090105060d0c110a050115120c150203 76
    0x9140400c1120307502c1051550340c0e0300102400d0031408400c0c41f1003940701641c441000c1c4003485281e600c00f000d03240d1041e00c902e4001150a06418128204540404082c00c903600c00000481e8200e41034101540c5401110554460704060010204151085215805030201d100011385d01943c410344400f0381140900c0211b8926050070b407201400c603101940c2c02c001c1c0c03880c607015010440c203000d10600508100343d072032481a498046040700c401074008002446c80c40d41c81a00c40c0801c00c0302c0e808607028225460483c0d0b20b460851030a5010340001000550b1640f04020f0b130a1602e5208058082109600c200000302051511911001901c0007a151580280d1a000c12071400d4042020005002281000070100b0031207400c40035182200c1c5070001400b940300301e001400303644c45410444c1d0b100d0003c200300080d100041e4000310381c6501450301125a50250101003018000150409a01c50406007018225555100c9800f1140c2c03580300c20041c0031004002040042002d902c101e012142000d006692 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 644875422 1250 644874172 644874187
    0x209070210020a0c031b0c0501050d1503080918101a0c0d09050109063615030519060810090c05060703021f09030203040b09031207050307030206060102160e0c 70
    0x50fa0003c9042c000000d86006100b018150321042100100c00c5001d0100c2c00c1e80041d88031345d083c105042c0103d90621500040404941c8075581c800006400c91840d4071518a4880c9080000b43e8050340712144210700072007040f070a1a81c0c0d080c00d00d000320403d08038554800c0c03400100c00310030050b5080c584494071061159201c900300501404100e0015035540703000460a140015001c08400e8129004000002c142d8020304406542c44032004060803840034403000140140b14039040d00c80d0041c90300030940340244d1024981580046000b050000030007200301400140003000c0340c1443c41280c14590140691405000d00c55014030303603540c0141c0d071101c100c9072a080450b503180c2c4032903c00c500587c000e102c10940c0700210210008841030310482400fa0b0b07000398600039500d0080f40a081a0042c0001e0301d201241d508110580c4942c0c0350820342920b4445a00f0082d840e41c00004081c0c016000d0100094519840070a8070544212444019604541001c500e085050401808108040d20800c07014 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 644876672 1250 644875422 644875453
    0x4030c060f0e01020306010f02190312060306110a1b0b01050910050402270406050a05061c06030c090c080123030a0b040606031a0609010315091b0f0b030108030702090702 75
    0x59002c40142c00542c0d6420014001045611040701080454110340c0e01c18031044c0c10000342116a640500d42240410700c0203e00c1c030010035070b542c0002d2803c0d01e0190750340d011800c1040541001a11516203610140ea41403003e04440106140200100300e01c40041c04540350103521035800ca60a02c0c0a0050b403903c4d04041400c07a400220f1300031402c048000c16229200300d503a8451480b03881994284003091801000c62081401401803034441c400104070b0034102070345510000007908100c601800312a6403820300d403a00000074010b021500341006c00000c01d6500901c5454101ea80720300d1140c0360281d204001c50400152201c0499050254030060004034500308101405140252000101d007465803801c1104001d4405104d480102284100521a5520325856045a400c0042440390180c070f001910020448203a00400c60313000d4040c0100c441c020307041c02d081030383d4041600b001d1187e200c9044040f01c1c00300b4414007249900c108403800041c1806112242c03c01c0c40c0d401110a041c0700400038 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 644877922 1250 644876672 644876681
    0x70612050c0c010e1e1209010f020307051f050a020909150a0302030102040915121205160206030415051b070f030302071401020a0e04020c0d030c0e0a06020c040c020f030304030c060f 80
    0x107801080d48000000c0d0490f80110404040d508014401421b40d51220100f0715200c0c040e02d000f071418081c200b8070920416000f442100c01140e40581a10705541b0040d4540f08a01411446410b1140c03400b00080c6402803507100b184c4c51b000d00101220640d90382c04030b04041c60000c04000300d400c00c02c8110000b0050b1001d00282c0050010b0352001700d052403c048240441202c20703800000100441203d0b17038007040303800741d650202c00c44505e041c9a07550443c6040140445085500942000c0c0001c1000180160b04034421565240090306200729290301410801d0702c40c880c0140750404008001940c0014100b220144003e482402c2c00350401c41241c03101c200b00410545120741c207035000240000307441d92085c880100000112400c41c10b00500c084601c0c0d0300d031031f00703d00303c3c05056955050405450103401401e522200003494403100c3c0703881b00030003900c4401c52812940541d06000d030803811603001094414004182e04011415542caa0b04c0880703200712034000c25a0840e603140c079a20750001c080d024 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 644879172 1250 644877922 644877941
    0x61003060b1206040f051306020c010b100305061206060a0501030207110a06090801050606040b0301150903051204090e034b03060f090405030f0f1908040b0108070612050c0c01 77
    0x14010503c0c42c1200c01d10094460001d0b440c103240340f40c5410001516403400080b04e4954101e000161100c201031001401411412140d82c0c0c4504521801c501c06507042c1c000780d01c07441044e07980d5615415805100e981d500e8060b40c0041e44000d01c840700f441107510a90140a05ea4028003004001c807481002194076464950007420015440260910244009004913504000140d031014989460100c1c10299400103001300505000300f03941e1500780a11403180c03403014681081c281c4014000201031091143d100d4800d03d4811400e05c009840c0081d07010054410142001900b4440c40d040b4642010901244442c03814070505019200c10145003c901480203005005282c0d540d81d00741002000030300d54207150828405c2c040002008005440841902c2c540e810002a207900c0f0400381030b1002c210301900400e1060710014503440c0c0c003e01da0040c0703030340e008a000352021000c030b07601d461200340c461289008007804510301c400d00d07004103a4158000c070340c0880b8909130b181c10540364025442c29a80c04c0309 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 644880422 1250 644879172 644879197
    0x905010e04030f08090c010f020a0b1f09090f0204181b090e0303250c020405131101021b0f0120072301022503080a020d02060c030f061003060b 63
    0xc040004058000c0c0743c0c111000303002d003807030301840c81e21140d184d03510074051ba101810440e4090000500500800c6114409035200701032003502c0c5009814000b80d42d8070402c6d1392100c194001400104090148507103002c20703402c052215801d6015400b400003130318090404806400c6240e085501050a19003200c80400c000c0619040c3c171454440b00343e082d54411101c4050381d8004000f03001c000701c600000888102d40c00d1f030400c0c541880c2102d00761164003420b08080d40142c1060104100f12304000f5203108007503c1000c0d03e0310455404001242e035072003048a054175500314040c1504031403804610114102c1030514280b1400c04120002401002c005032014202e5444000c0c14450050010031105154030078038041e80c3c2c1e03072000c80c0000399155200890b03500d00160b070990380c000c824010b14003000999004503041d6501c81c100c00c002940e034420202a0300c014083c0c103011944102059045074002c010310740031213520f40c41302000c1000700e42500740b1b80c0d001d1591b02d10380014490582800703807010f0210003 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 644881672 1250 644880422 644880449
    0x41a030619030b2a0703032d0605030609010c090b03060a05150d0c261f080d17132012010c080606070b0f0c0d0f0605040e0604020f010513090501 64
    0x20540e907140c401c134140c204480c0315443c90f510306a410010950380341c05d03018600800c2c030350040d03010440305490240a50701b007610490306c050703032120385a04880704840e415011640c8654541170300a080b20000315003480043c580c3c080410941040c40041c5800100042c5522982aa46c0c400103200011100c0c034039440390000300f081c1403480d007030703224186020105060001c041034628481e641032800000828903040d02000105444101d00e0805503410070304250900041a1607048003691014011070301750005507000580d008440c0c690305c4080c0500b0354800d10a6107403059980344845002c01c0194001c00782a1440000119600c03240000140143c04000240b0000c190704010203182c8010841400b450b0b0801007a070005500c20701e065032101c00f1814944aa840d010b5076111144114007080507105d0805606401d1b5a5240e800341d4101d035800c980410480102c80c1e01240c84240c02c0300c001c1e50000380104000d6055020758001c109072985084101d19035602c80a0341800c0341c42c281c100102c408601c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 644882922 1250 644881672 644881681
    0x13061e0605030c0306040b160e150417071a0a0203090d0b070e09160c02120a152306150903120306030127020d0c0918050c0402041a030619030b 63
    0x9010850b40c0d0f0009401820851502d51503400c2c1080015000101c107042044560311268071944056444042c0109070719424810440c980303905070858007072907021400c1e01c0e004112560000079400304130b80910b90811030b080c4440c940c60715560014101042503000411580105507249083d0031006e5105281600680c01c00c9040203040d080710202e128040e5864506100b840700ca1038860554082151501460f055014130214681e03411a0150700700c144103401c3d1031020041002c403c00c248050081007004160440030082450844d07500e26030b100198800045030060500c021203407071044101122078038000140e00820314000034054007240c0e0356004424800709203020b014443d8590400b40d60100801400085182d4555880300300a00c600000b036200c10070443c1c03407181c0e40b0083c819501c0c10802c3c031100540080c098030500c0811102130194444083d80c2e450075100303680684210f82c0d00c41005201415600e20541e01c05010715621141da601c900c50009007a201c02d00155200b040c3c40700d0302d03090 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 644884172 1250 644882922 644882929
    0x918010e071e050a0b0a0318200a0b180316090f0501050a0302100509040f051305070512030d09020a0e07051e04180b0406150e15030601050313061e0605 67
    0x71441d140602c8101d04520400c00395503402c00580c1610320b40344e60b0310f0ba0740c00106410340c01040c140c410b2600214034507041c0320500c40039074808180e15217a1540055802032103004c000c08809980208088242c090103080d4036100880f0181c0d400c910090300315449002d03c1074120580c60340d0f07984100310702500c0781c400b14640c0e02180292801000141c8219114a0039940000c045060700300109080010106280ca526542c030f03000900c1280351040d00700200d04001d42800702803400d0540690b498840d41400003403c3c1811030038155008602c001540c201750007026072401030000da000603030780070b0400303140419015010320710680078204070f407200d541e00ea510100041404106450701c0b0810a0140810401c00d215078040c980000340020340055242c02d43e6001030014102504140c0c140b60030021501c1c00f90341c001070044c0c1a110102c5184200c1200b4003501d4035548801c0703031441c0c0000c405001181c0c181e1840c00085d01550305c180c1c000318620400551760748a01884c0d24070b00070b040783c83e00d404210906 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 644885422 1250 644884172 644884199
    0x180a12030e1f200a23041a040302120d120e0f06091f0c090e07030905100203090118020307060e0d0b070f0f2c031518010b0a030c050918010e07 63
    0x10b404602c0d02c1c0c10720b59244c2014003500400c01c200d00e003500100040807018003034a000c96000d8070a00c0503006050203031000012480c1c015000c02c07800340c0b0214600030b04840c0c00044c4c0d03a84455240e83c44d440e0455031003400070050001c80c054402c080c807444030b45142d6040d050018a100301c248500604489501142c094030601b501181c070050103145c004040503190f440319040e419140c18a100c0e45940e15a600201c00a215030740002e80903004100030444040e52a40056005035081c038002d00420400b034540032a006000e580080d459442010100503050140c40c00320b091400c028042c0c3e00786030a54440c100000300071102e81c00007840880c4a00401c1d5003003040601e10032020700d00f184601e01e5045000c201c040d6800c0c031502c03405880d4034103140300d5641041070740b80302111020404868100b4803a2002c4840040d0441d007002c0d428540c1c141d5040c20013080c2030003102d070006203006c1c4103031824080c00340e10f031341c0605030207458000c03000145441708090080c00c0f040000e050003821000d15000410903400d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 644886672 1250 644885422 644885471
    0x21e1b0c10050301140111030a0903030833010215010608010303080c03070203390105100803130306020d02070b0f091b13020d0605031203180a12030e1f 67
    0x11000290307101542680708041c0e80c15209140000c141d00031500006880c84580d001c40c001d17861000203031480c0880e600411071340469209840704d02081d2220005a400f0803101c01403000410020b0000d100303a004404a445800c21040c0180c885503481100741c90b990080c00d800c2800400d428030010001c1550103208251b00003807000843c1d0540c00d0105001303441c0d105082c001101901200c4103041050501c04480107a00035411100c0d1141002147c510301801045070f48690038a502c40d0005035040d03010041b42d0300b146005024820036425541c2e000002e4101c02e034104203166003402202c1c00140408201409400c58615a41d203501d81504c3d1540340500900d1010001035030300340702600740c0c1c40f042640142d00c01d070103d00ada2205140001c54000f032055a03c12035243c0f28100d10155104524801036000381190b800400b025040c50900e56a00c002000b401048030226217013181c1810700c603520011020116000740d81400d845c40c9111031083e00c05420781035a00e43d035800400301e0814042c202d40d112 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 644887922 1250 644886672 644886679
    0x3180c010212090d0228081c050a080c07170304020f040605010e06161509030f14041421160e09030d0e0f1c0305010803030415021e1b0c 60
    0x51810000b810041e000300601c0600811035a007406045503114403068400259045c2d1840300360300341241da14000030451044000b10f00981414118a40194094024201e21621501d141c01400801140d000030f0041008074016002d001010010f07500411076000490581c2803c0e889060a00400c11080a1150124852850300d03508020f00c0c1d0300820400e881c0441201d1094580c0c0180d807aa4038082030f125402015041c00341500c20b4281c0c07140d80700380d5800d03009543d0040070920b2080180d503441a070030000d040381002408100718082c41022000780004025040406803000503010130365580206508030a660400c4682080c02c209055000d4001d00040e800c8064038181030110701d03140d200d000520765841d41c40300e11407140f2542c00c01029030956400400c60b00d807408490040b031480601e0440a0700068242400001d0050000003a00e0003075405c100b000103000506614080203501100d4603c50303130001c414140700c00c107204501420680f1020407100380300140800600b810b080d50404600c3c030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 644889172 1250 644887922 644887933
    0x5010b0f01081009051305060405060411063c03040c0923040611070506010f050109090e0c010f2f06061203031306061a0c0f07151803060203180c0102 66
    0x10f541c88241110300440e801c004000039941c0310844134014465000c20041d00c94403070303202804200032000442c02d2041d401040d01400300e086000403c4200e00ca4040c1d008101c400d01c1c0c040c0202446140302448010034840c16000c9502c035601058212500104d4003501c1180300507804102c40c03c514014600c0c050184160801260040030547c1a04440500054001e43c0d030740b00c03030342e03070703070300240e0101c60030150007000b19000381d07944000741c80100c034003400703881d00040e2600800a040c20490041108030400000074002411081004542c04440d5841d80b1040000da803140454110f829900c0000d4907104021600c40804015001898400c4c00340000303000360042031039800000000700c00d60380c00c0848220050b43c0d26130a13040c00300c06401d141d0014480c400f10403040c000311030080f00040000d2842a401c0d5150074042c800d030b5a49032003152003407050b01890412505046445810400b241c03102c005244900c40c0d03243d841d078104a81084a0302e04000d4901c40480b074509804101124110707000b44010003 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 644890422 1250 644889172 644889181
    0x50d0b0a0324051b040308090a0503070b0403121e2d0306030302120309060601051b07140906030706020d0f050c0706050903070e130b130b0705090f0a032604090905010b0f0108 77
    0x1681340318074400a8420000410b40c1841c41c1d44262740040107042c01030031500c115844005d925001d501c030b480116000000001c2000840b406400150b04401c00c1e0880c00281c403d128005850310442d4114502922240c25101100900154000c682c0021943d42c0058084e0551402030b2415404840e810312080c800c0c0104003001000246441e84140e0a180081d121132080b00000024683d116250b0303040e0103a0351010865201d5414084080c420480b4100f0058031610149074a803080c6024100c0142c03c01e4040002d00e9006601c6008601c115180031407a040c40c481d213903410180150000c03400035600280c4c2645901e01000000040e00200404c0111428246280c0f040d904002c280240009154000141c2680b00c21080c1d02e4003d0b00311f0103c4015113410f250060660340032040c0d40344111b5030003008012505140380c008082d21381c041900400c46101034840004100c4019116a5411041001051944060154509081c4140f00201d02030707803000100807580e10181484d5040007007850801 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 644891672 1250 644890422 644890471
    0xb16140301290a03201303020405190e0616090f0603090c121a0114010e0409171306080705070210030e0c0a0b070c080d050d0b0a032405 60
    0x1641150b844521051810100030000342d15a0281c050702c07218000c01003191054241c054004e099010402001d00c0c024210074154805103000e114994a26040750200c14001030a103a80700310f4101a9000b407403c1d0f04a041855481075600350090b92075030750000010f0052014180545824182c030a00f0100e003041e0510300d07500030030405841000e00301038503201030105002100700302c04017031b04081ca4800700e404020b0410300c001540c407920f6000180964800018580c0403c100c064070600142d41c0e2000344000c101c1000041c010202d41a6043c81c00d90703070300c0300039540000c004103224401062030443c1700c0d03e016405040300b80d00070041c5081c00020031040d00103a9a00320b641d100f1100c1ca040c0001e942a552420b14940000c9404407508000b00c031402084128043c2e01500809200f283c007004a1a110328039683c9545a4051400c0810001d000c0e09001801c3da40041031031000c06440d031443c0580da0303110807425a10500108120303031055050045d4030b160500840794802d4840260309040696180c50 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 644892922 1250 644891672 644891677
    0xc0f0f07060f05160825020604110616060b120d0809010506010806090703150e070504030c0902040e061002010905060a02040312020c01140901180e2d0411011206030b1614 75
    0x110b50421022070b00040540030b050b400c01d00c1c0080200b51086e507800702600065038a140507607007601c102c0880f100800861070050100c50409441c0005403221241c1d0395a014007038001200b00d01d81c040310354051444000c0080165070324a80b096514011241428084982150805044181041031840400c80952138222800d0780100c143c3c03800050421210f030b5103200d50b00480d0442e01201c00b00030305010440d80e000300644203032030141d002c2110403503540005204a103e584036181e21603603184000b5003540380c40da054070f00744001800042454100b0f559107a007041e200711450381c0100d0303001ca001d02c1030010a821144400b040340c00105000a030482c0060718210030400c42c0003024100140ba00f0081e485103110800140d1109420b280b070540b08c0d4180c2c03510324012104c0e20b10b01c041d502d800000010520480705806c02c800031b8a1641601c440c0c0390807402103080303111503041c007003074649002e00e00c600f40c070a01008500a00c00305c940d90030f0144100103101c840c00004010031021008414082100108 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 644894172 1250 644892922 644892961
    0xd02071805090316080705060705130605041202060703020a0602040315060603020c1b010c021f030e06070c0b060d1e020a14132705030d110712080c0f0f07060f05 71
    0x16140301c210130340741000310b030320403031400511500640c02400051038000c0d0181c86141c0340201c400039215118201110303503010703512442c24103001d001c10350f60140c20b0081c000d15000340648196290b080072520ba11050303034400d40c400c4402a4803807640c4201c85200e03126017000740000d89019450300038110710300d071783e1070f0704880e42e51040300e11680c8841c0c1c85030b0140384900140340c0e001d00206000155180840c00890414000c203020902305001d1040154003c90700c5485004c46803504008440a5241d6030070150300240203d40006a120b240c1c004200c024044240d030703ca035004403040080c01841440565001035200700b5900c1055031110003542d031140d80401c407101c02010006246048040b698071180508510004441c1e007101004040c000080f004280e2070300d041006014101d0300b41401c81a610500901800007030840300090311080c072501d00150000c03000e00c00c0c641000444410346c032480d03101084010350440002009410004c44d80030344d800e051044101080070b4900485c0d404c2c3d00c0140500c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 644895422 1250 644894172 644894197
    0x1081209090402041505040906150e01050307060c031716030b0915060d0902060c0f0c0612220203011b032307050705030c1c0824060a030e0d020718050903 68
    0x29905c841e507050403000c0d04d005001c024401d20a50000d8209503006100c1c000d0080302008414202051810001941c14101c440280007880003038500302c411909441c10090480400004602641e004940011403c0c004d450301038440d50710501800020742168101d0003c0c2d8003c0040c80100310020070705039100452901c3c04d0321015580c929250f00000200007400c0025840751002c0352042c1901c2300044c84643c10780294046550007001401042800c0c02603c1441c40305600810006032410000b032121882a00c0d410940d00102034981d0009096a23203007800c80441000c80d1a001c0c81055041c0510078140203a0400c81c030400088103086589100014600010b02500060701010040104110780020341c5c1304056910441e20f0314245100075480c21008000500705401003140c000074400000c0d1003844680f1889000d107121001e01c41590414692002030607a00c040340c6c10150014000100103081b2036018003071050900c50f8241540014003825218245440d04201180800000b1a1907881190 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 644896672 1250 644895422 644895431
    0x101d0105031e06010b09040f1406030f060115030b04151e0f030f02060705150a0207020405060609010c140a0b0f06150712080c0403050102070308070e1008010311180f0108120909040204 81
    0x1440424007030230884140c1d401041c6095500516480c00c0d450550003036a0440c1568501d510000c207040d82c81c0720030300680350b40144540351498074a001e80e11220007180302500100755100c90500e159801e000551003041c2049140b01c5010340d0541c0c2c180200050702c1000075801ca440c2c110740f10f6840798501c854000b8000c0c100082c0034403e1150410205401032071102c0307107840d20700e001c890500c0650003800c400c0780114200000b090351864030506607151a1810383d5000c42e1050030b034607010400e42052600c8a040e01034070004402140030340b070b403051184081c4911281c541c00e01e0402e201d40f9a071a20001c04c4501020300c0300c100061042d12214135a0032040c40c2482d115107610051070780d030f427259610040c0075600c005040402c042e00900e03002c1c49008141c84080f44402d0741703000d1103402420302d0340d000006034a1070014000150300a0b4900300c10000a40a0f000d41d8200103504130858405813402c00d0505181401041b201000300f00607071001d4028070312141000f8140c40841e02d014405040240b01c3d6884 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 644897922 1250 644896672 644896687
    0x1020d1407020a390807030303060b09090f04020402270906032103092b0207090240080a1e0b060d020f040f06060813080a0503101d0105031e06010b 65
    0x24401d05402142e0704e11078040780301d55604807117590b449951004030301180c01c04000040c003a6806066a03110b000c0984840c895554081010440410080080380d01990a2200c2c0d500c258a8075460300c052820200301803110b610050401501c0c440040079103105c0c1e40160440c01100240801c480d400c41802c130051600e076201d0407000760821801c1d880f966a0402c042c1c003218403810701505000202d02c640c0e000d0750401511640c5c9030040e0b00c6000003841c0700e00c401014180f2221020401c9500c040043c0402d01c440030b11000c48000303162300f81c1d400351b41c1c00d078000c4c400d20f41480144444581c1c03102e10784600c06200780142d603d0507000300300209014810070241c450201036480d0850080e11000700200204181d000303011038040244014040c1c3c0000a1402c4002510254502044030000d60801c0146090052001c8100e07010f9100910420b802e5004610003d900000801d401c0180c03049502c036621035605002c28107103880d40d0030307904a8800001111000507800041151419076030b106605a86d9201d0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 644899172 1250 644897922 644897993
    0x509130b0a11070f0b07030603170c030702040615090e090622120f11030705120901170f0411040219050c0325030f08040803061e0301020d1407020a 65
    0xd0108076401039010003e0100300b0440d003101c800d00120f01c9490380ea0001c1d11201c004400b11070582c080200740d0710810240d40e40c0092814050f000a9102c0f01c102e038905040395010a040e03d4a6910042231000d02881c5140304a411205280240c10304104520003890110442d583c0d400c0f010305009004040b1a001c0b000c103003043c82030b0f1007005800c1201d688035401c502100410001170f500d00940080c42c4100f641d481a4000f0049030302e0550001c0040241c01c41d082c20f4681c0075400401981d05020003c80da80c0c210810602206110744e114408107822072a0509010082d80d0541e22243e2145104110140741c2004580300340c1c0766010f036481d106440e0140011000e29510881c01c5102d14180c1a000300340a000d481003804d078596202e80c0d00c01c2e0890702e19810640701e2103000e6500500c000000d100048045c05c05100c1c101c03100300c1c0c8102002205403c100031a00f240d20072070300f4482d4030362503900205c00c1d40410101c45801c00071038030042091040ea41c40f054a001f0b581c0160025907400701030b468140700c2 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 644900422 1250 644899172 644899181
    0x1b080d02121302100903030804140316140705090606072303130311030708060109020715090302060414030406090b030c280f1b060b121207020a0509130b0a 68
    0xd1030074580c96440c0c2420040380b007885100da030301244248003200360012080d00c00c000c4c48040f260f00d07441b0901a034460707541340c255404407017460898901c014032491b130110600400d030034610360107100c40031841c002040c1e0072410320340c80790013060041031074006100172600c8078400c80752060f0704144001c0380701810b0a46030121003d032040340c10aa2202048010300d2429000c0c0c1c040449203d85541c01880310342d1028580c407101c184c45031803400e8000c83c0041042071701c2c41d0000c2034000d02c200c400c00d03990103505002c00101d5010041c1507006911440c204020051405100d040241481d402541442e2500300d0091080c2d075280100d02c00c841011000c58444403030441691a162846100b402840000b0000759540011a5006800150060003039415090041440c8850a41c070f40307420340402281c0c0c2e03d40354003500d070a041c03158118500b884046503246040c0320081da1100041c1545503600761600410218001a420540c86442c001051100d0307e003030f50301c032500300c241e001070002c500ba40e403605041d0050 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 644901672 1250 644900422 644900437
    0x40209130e101e0b03060609061e13061e0b09040f09140f060717280c030b011205100303031d06070807121407030e010b030714030105071b080d02 64
    0x440c100500012408009901c10a0000c098082013081d80300d00c100f01984c8240c240c034500e80061959000c5461030804c940d00e034034042c62482d517030705419140001040032100b00e0030101c009141d1b64081400074250601410b140ca15204481c486090304050300b00400340f007040d200d6441a0713a112510950000903801c94020740c0d03001580d40188040c0000c00c162210142d808161040c09040001206a070180d00285451721a03020403c08643d00e0604208001d0311661003542170400305400d03801581954021554503a200d03507800b0948000d1440050000c00000d1810061141040f081150590303c5a1884040703c0c0c2500d03002c2400c0400800020b240c82055040c16980e0295100304540c0c26000710156000e0901566030043c1c031082d800c0c1c500100c0e06d0303a9408603c0000243d0101d030718079101e90000701c40500c511000048200c0b4034800680b801c0d0092f0b2000070800f0540569a880d03180170f1080503880301a1741400d403034040c000b645014502c0d403044001043d0007000300f05501940910342c1030302e006 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 644902922 1250 644901672 644901703
    0x30702150a0221030f0708100302090c191809060b0f0307090b0301090b090a02030c070f031107120c08010b03100906060312050d06060905060d0518061e06040209130e 73
    0x102c100f090b61020030741e07108469481c411744912000c6841c81e807245140b58460072402045000d203608550802242e044060407141058806011b00d600a414500840745240e01d1502e500030310b1491a03502d802810507690103010954544107082207000c04403400c4401d000c1065032025601d544010040d2544601034111b038002ca10044008140380c0100c0e845000a0f0400b140d84540d65a02e1140c404140d100071661b44c541c0c1442449004005440084561420380c4070341001c042c032150301c0344801d2030400140c1c042e5450f01d4102d440007050207962501d0801800e5920300912146500741c01003036965128071665500c142d603403240340c000e010803640720b4405150701040c41c058080d2007113401803064010807112401c0d60300d01200002c00038010035039102111400341035a0f040070f28941c800401420000c2101401c2c494000820080c9001449518030078100046501e16540c4000700640d481c1200606a40c01988100300002a56803a60000c0c211001015800708a002c507040000e8240300450f07400070390303 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 644904172 1250 644902922 644902963
    0xa0e09180717010e0a03120b180901090b0919030c050a0b010f06021519090f080c010c0f031e0518011a010f18050603061c030c0c08030702150a02 64
    0x220550a08820302d02c204200009005540041c00c0e4a501c0c2c910011008000c10001035664400301d020740c12414229000038a00003802248000040a141d42180d2030205655100d1a00d01080120f81600d03801c400a0300050102e110101920b03045402c0d0080c01805010700e803000c501c1040001c2103444280343e80501922040d59548018160031080703809000050b010b02d141501c0910114140244201c5101c150001c2504050103140000d000c1880140c0d40054821903410100702d150005110080e40d590002440c8581c0904c000c0c850a041e035140401c140c02c003070162140d61701c80008014801e4a115000072285c440306031400300c4075180c101d00c41040d401c7c040700426040b1001d00c00504000d003a00c4034109119808000c41d014a40d0f01d02c401c000800344e0078103102c1418008003450b80014080c04442c00c00211704840f1502850b0320908800280308a0005c0007085000140c9000606146c001103060000a600240c140c0403a6880d042c050540403d4042c1054400c00c8411058155101c4403031 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 644905422 1250 644904172 644904179
    0x309030c070617090a030206180c120304060305060a030507060318020306100306050a0b1c0807051e010b01030225050c0a06050408010b1c0308040c0f081606050a0e091807 75
    0x7001a0a41c2c03c030719050709110000035103100e202045600f40303076a1550248c201036a5074101c41c402c180034040351820364460b03010504420307100d60013203031141841c9000450301c40d4585000141680c2c80281081d000d0b29030704c1ca0030400114001003807010758141c0d003400b2802043c04807403501e001070302c090081c0d40740c8281b8003481200983e041c031090079640600c01c00c1c080d40d9241000001680c40b0401030340c2c1c0107028845c3e0311a183e59010480342110b0700c102d601c2445d05249072a401e1800d8107801501450064003000e0304013101003440707400520340003070a040d8208040c000c0c0400050320303407641c07250034070088107c56400c110b400e01011600030350040c015074115031a0840180140c00034010794010f5840c150000d805031422144168112a500003000c916881d2582d049032806405001100e2106080702c02090b0030244e010b4020107003e5850080c4050009502405c2c012015588030b0410300c0b104008040700d01e50300c505000b001c1e41c0c003903440f84c07925110400c02142d40300e50b0581c07a0303450307028910010 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 644906672 1250 644905422 644905427
    0x1b0702100509030607031803080c19020607090806100b09150f1c180f0303020d09083001050d020f0d121d011d010c020307080303060a09050402090c0309030c0706 71
    0x20b26207408294115a41540c2d2800141d0460702c80c40d0b0510311003c03070035080b600001d2180c1d0281c5c1d440a4401032460034a00d07110001429080e03000950800341c2c108204101c000c540c032181c0d0344010300422005007440d0901911031070702d80b02c082c02000259a00050710380032a803200700f100b1206500380c80c8159690000241d04900c5500310416400700d2030251103c2c1007107143c0500400260f21701000c201503108907166104540401c1c16072048041c5030b004d001c1108840620700c03d88030154040c82d111a0354007145103401c180100441c0589400c680c0341c254055070800c1207128241521016940c1c68540d031440c0c000201c03807a070350303008007684640394403054010021510f488441c840b440f510303036507000750030b1100044502c0c081d807103c280000c890f512b2070300502c404a120315007440418180685a204107401017070804e411904034448a5000100748902c03400c001c403200005000128040015060684c002824070401130f001040d0f1240c007002007000500248203e80b0341c2c00309241200c0d482503442501 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 644907922 1250 644906672 644906677
    0x30b0904060b12010b1018030b0f0f010b03070e0f06040806040804050a080601061209022b030210110405060d0612050606150315090c0c0a03050409050a0e061b07021005 74
    0x519004540c000780f0380c07544402c140981d1400d440001c040b015540320a2804984d1044100340c401070755030054800002003185112020f0180c00d6085c5982140d10b0160b00752650b9007010303030103a4950003041013008074095001411800898041390a03407644840d01c40020098003032078001c007089029500500c0104800f503001031044a5083d43d00d8403085941e840501d032910424402c0601107803c0c1d0b03058050b107103c90381c800c4030160310051101c0f003040a00000d80c03410960f40d010f0b4100d80c20003607030807800341501004444e403070340d04049042c81410a01e109000f1b4500031481503500079400491802a28500c981007003001d0050302c400b014002440f4200140d403042c0585d0024010b002c45060070a030182d0440450348100a40f000c0a0741040901081c0000d08500030420308044505018506481d0030600c04c13080403900a5403125200c0e4200f0394010f00f200d40140501c14540c1c60189c10070a101c10120344258801026104c820710340100d528403143d50f2003a008002e500c034880612a80700741ea0001c01 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 644909172 1250 644907922 644907941
    0x90406020c25080a020a12150905100509071401030213080303190b0d171309020a0903060b0d030c120507170c06181b0102011404030c0b090313060807030b090406 71
    0x814601c034a42c0d80003e261103104000b0080d40009011006100924100c8816056988201c5541c0300040f124202c1d5002c0710700203801207905404c4128280034074405c0303000c0d10341c100c2520006400b1300e41c41d08294010b401c04022805050540101c4c41d00042d034080e00340e140c0100000b1054035520310705030f5082105200020b01d00d0086520704034003002c0d10b0500070400d02c807544d03000d03c681c80d0700d00f4520300912164000030300709030300d000d03000e1400301e22a0f0185c009071140401c0c0c0e40365440101e055241036001d803109a01002d00484904a590010a41c0052146070164011141820550308040d040314140700b04c0d08058002c000c1c004188100703564020040440f0011581641c000d52200900d107442c4221040020002e6408003000000c0340d00702060030000036205000010340902000105403020a08981c10740101e240c1078501c00074040c9185121b684462910081c42c5042c900086400728030300c1034080d0350200300f258400a804a40280e05c05072070200020250149407506140c990050400c280 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 644910422 1250 644909172 644909233
    0x903020708160503030901030f0b04061404060503030909161b030206041515030b06040213090b0a051009090b0f1e010306090b011d1c1101020d0c0f02090406020c 71
    0x2960300c032403000700650b03000e4840c0100614a440c6610303004401506040c00c2950451b5540c0c0c02400160703503984118030007420411003d0020100070710030001142c2040d84500e009820801c0806420383e6503064442e0300a10181016034031142076007089403111440318000518001d04a1407906142d000078840384254801e400421180500032440d01c15205119a10201c2e1119242e0034000102491040c40d84080e01a00042c2086060765a0401c001c40c0c076032220310013943e1259041d42c1c0b401c1170310000e40600807e0f1750306000080b00306ea009004c4403c1e48907910000c1e94a411428080d507a0f030300c81c4426594001c001035400702280002d82c0c003c0030984d207800e0100b8a0200300041601c110301036903101e400140c54800061003200c081410781c4850201c100c2d07200b0030307001c441d141020740c0c540c0322400240034100c1c691034802202d00280c07414203c49110018000340f120104001069102d64102881d0705641c0491692501c0c9440e1000c1c2c0203041a40800e401a140408151858400070000059582 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 644911672 1250 644910422 644910433
    0x30a021b010f120e031c15090b0604091503060c0e01031427010f0c0f0305060108102304020415090f03031b0c03020d03050a0e0907120c020708010903020708 69
    0x4030010b445105000a19001044500c002c1891030561a03021505110f1071500303480c41c4c090302040341d103140d8103141c3c14000201e0751150b0401241440440400140c41481000c00140841800140182c00ba074407410512948640d115400140c4840c10180115401001800440b0500d54094208140c44560a002030b160111103a517076104a8001070007500000280038010404110103400d20150040c1400b02d50740300c00042109401e24402c5a042d01c0103661040d4481c00f003450300500b03a8501400b11750401141d04103000759814440408011203d4140005003a20501001030340240c1c8050078081e0b000b80301081c0054050707501040e0b980e40f80040e55a41c0c031425155001000c0c00c00250002030005400c0380c101c84140d048207042d090146015140144030941c0d00e600207140c0c11481001100024004214a078015810a40000c0089411640500e1500c2e00d45401040d1102041c031103800c4680700d540340c00f9064024040742000c0e141c0d0701c0c003d0010020b5410003a689000c2d62042c0843e52044 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 644912922 1250 644911672 644911723
    0x3031204020f01090b030c0d060e0103060e0d0207030515130606240201050c03060909100603060c0e0d0f080a180f0305060c0a020a03080a0e0607020109060c02010b031906020c030a02 80
    0x1030340354603055a500e10000760854480c1c0c860681e47c1c0d0440c0210b204c5c0103540b09000302d000c0091416060007184903a20101e44403011080050420711442c8025055600040003440010700101d80300c1c40b80e4400c603070321403010313669260704141c070714032412010f032402d8036080c0007003007400440428910840c07011406162b414540e0400f00d00701d0790202d035100c24400e020b201140040c50f00e0300040380c00408400440d442c51603e9081c000858856500444d0180d56443c014428541c00c900c1c03941062070121242ca400e0f41c103645030000e207001c040d28001e0603400001b0f40070400d580911000c084199140781d582d03148949406001400c0c0c1180c0c0010f070fa140c401c480024500100c8038049440020056000d45041880781c2d40c16200282d001c1d145c0101d5035110b0000700c2181400b0051a803040045900200300d01c41242060b000b2101010707060070869040020000c0d4a84000450200d592805101040714995500b8180300034011a1141112800001614a00d1a60009600407080c1c0034401c0c03200d10540 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 644914172 1250 644912922 644912927
    0x2010b12031201092d09210c110301020d090606050a090219143708101413090f0b0a0203010e1503010f0519050f0609130302010b03031204020f01 64
    0x41c002c110088940b0035801802002c04641020020a140c443c03902c40c1c0b844003c4200c2d07404900c24595641031642c0d80c88180c18424002d5075071b51442d1281407071800d0001e140400425858003036501070503a40c0c0fa008280d025840943c100d882180310143c0800c5a00410324005003c2d00319485081d00c03400044402291401300c80c400c440c803c60026100340984a44148184d80d0280b40035021802d60005000400c0c1e0000300040d600070b80d110b405601411449141107840c801400f6072220010000180100f2103c4420310303103428113480c00100d041038448072110000b005600f0031440c140c0d00ca400c5c1400d0104115039402d01d40300c16446902021015600c0c242d041049000034402d14640074040f10201c1c404882910b1000700c44000a00045400c0386a40d150310261041603802c030b16451075a9451402d1080d07903106183d0425030281d43c0e007015082081c0020790110014028a845145004d403a40400d4000d43c002c2c60300c4400030701503d84031000481020b0414030221400e034003528410410700245e61 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 644915422 1250 644914172 644914177
    0xf03250b031510091a070b0f090304092406020610210f030e0a0b04050f09160f0216060c020111060618060f040f0902030f0a0f030518040c02010b1203 66
    0x321405144000d6640600030091003c0740c1040c0c64003482011200890445010800c1d0111000c41040265482c4010b00d40f0100244000340742d9010b60083c0000c1c042d0032200442142d00712030503428045254174980c1c5c1c60b0245800610f414206151b401d03d40001c0032500855502d2042000010340b10500d0303500e003100441c1090444802040d041d6280503080002d045031009006507000f8504401f400980b40d0104109100d0350300000010a80440c0030841d6250540381c05030158819640c0040d2424001c0d07003c01040d510a00030414080c05514220406208002050a18400040b1f030071589640d400c0203805c110b8000d50580c00201290701d85840c0160010ba40c500450024015061091226402403100c0d40082c0c103407a40042e0320010703151241d41e54054503881407010540011001224810949805081c2d0351014890304146003a20124900c0181207100d5a05400d240c0c0d0365108903501e83c03891260030041c071540107142200c100350b03050b4158400d511494042e0b415007400f00c0b0030301c00f481d641d0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 644916672 1250 644915422 644915431
    0x1e0f0e010305062802280311090f1512010602120307050901120b0a081e0d120b01030204030204180201120b1516020301020318011103040209070c020f03250b03 70
    0x181e2054020039151102802440441d20300c4200780428044a0a000350699011807604c0d084509920034280801c000311b617a2480c0040e031810200b020800c00b980c00101d078000c0c98686841070220070f40900142d155404440e25242155907400c0c0d41782c43c8030a00609d40c0300b00780554401031241c008050180707a111011030340902c0d4942c64640c03c0140b94001107070600c03089061600d815490340350504d12515211240e4024281030030207040501001c000210304069003a9074803c0c268440f546155120750040c1300d6010190000c0c80206051480e000181d019124a41c0002d402500c0c00a400d104e100c198004100320768800da947d00e41c0580c0d039240d5201030303800c0705c49250b034407540741100003000d00540c600a000c0381c07510744400e01c2c0b166199000207003203130011a100c41000300304000b45900c0003801e00c0b40a181000400c030703c1d41107003006d8020a0500400403c8a42807020842401c4150f40e80e21140d03000c1040010100e514035192490220580480c0110400c40032900038008160411801c0559104 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 644917922 1250 644916672 644916683
    0xc030705040512100219180f05210d08220314161b060f140d02031305060a0b01020c030105060d240203070207210c0902030903041e0f0e0103 62
    0x3003500301801c1101c81c02d003001c60410b00b40300e84ca120040002840c005000d490f22007620703418640110070000340501c0b0b00c004a5000e0070801290501c00c10360751a08960039180d058402c01d41d41040030362606a41107807140c00c040c0f10320907500450070203544900c20b98841c0c0050b04540103404400c000340410101c0c442d03c0200422001c40d42c00d02404041009058443d20400c40170001c04c00544481090804d07000c2c0003591032440c403005000850700520031032004140c0b03241c2190014010005181180211103100d104142c0010114000c050704a1884081c0c0d6042000d035419400c100f0b02c628000d042d0030039410b002d8014518407101c146410b01c070b214407540018224502000296440b0300d41c441c01e40035810340c4080116801801c03080b40d4400345100d50320a800170070a450409200c07268401c255420f501d041100d0810b4840010b0b46201100100c0e20640d030003589a41303401001c5030841c01541c01c448540c1c90300050020b81d034140003802c001200c150750b442d20303003698955201d03400044d001d00002d0503 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 644919172 1250 644917922 644917927
    0x1a0a0c1b0201120212040c080f12090405070903122001021608070503070b010311130513110102030d020d0f050c04060c1103160303050a030506030f070603050c220305060c030705 78
    0x140d4040c1807508400800f40d4001481c5c880090440d158140c0e0542d0280c0d403a001c050005e00c0209420440145400f000c40000e1007607840011031a842840748503482c034010390722103002c10400390264841c04051030f4084401859031405100040000043d1071085140c601d0340c0e466004051010320845410045018440b5070328151601d0b200403903801030700115098481009400086400390070b01c6c82c041c40c0705480154010000c0d100f04582d02c404940c0612481c2c0c606414840c031070340410422072585910116440d03201c08103100517800d5008006030120814000114490398200a40c082e00104111441c1001107880d001000040f074084c138002e400c041803204803400c010544000908181180040465482101c450707007040030059280c3c012004642c1c085546001d0a4141c05070b150302c03000660003007001c5810002c00c0c90b5241504d101e01d100340b61b541e1002c1900c1c0c041d201c08888003c0748111003102031482d120300d041120310719403205640d280640c4010400784040c40040b24020100d55941ea030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 644920422 1250 644919172 644919227
    0xc0f040606020d0804081306120c08131104090b090a05070f0f030b0c0f04060e03010b010305070503130501021e070507292a0606010f05090303030c161a0a0c 69
    0x43d5801009170040d901254180002c0d07810300141345c501005001c080c1c1c0d6100e50180c0c0c0e00f4407481540c0b030b06410202449600020000c2049181c1c2d0341010560700940344107210055003002c1001400d240e4009010b1000020400c80c681100041e544810b0344a1400c60742541d076261804400322180c0d005200450140c2d06040003c25091540c0e15003200b405420316242400481d52000360f07500550204000c6100c20b00101d0a5140078801c1034407000c4207090070301003450100c40003451307444010b01c00d801d501c2d00d042d1b41e8414050b0960684181c045540d6521050024600c0400c0c681e41005a00700c80c94401c560000c910b0540401482560000c2001000000e202030125913a07280c1150b211404e009400b820703c002c0402c0b00d1111000709803a28409031000303080c10000100a40c140c3c115440c00c1c44800c0103440788a0300c0000c1204c1c3e02071210103405449400c500080301c0300c1c009424015007238802001000c508020314040c124060741d1040d004001d5040d00400a42d105502c031021040d21a500a4818 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 644921672 1250 644920422 644920427
    0x30d0c050c010f1b031206141513170703120504080309040207110306071101050c041d1f090204180c1e0323010f06030b0a061407140c0f040606020d 65
    0x1100e0300320fa03e00706407228010400130038800803034408040c0c0000381d10b81c40e00308600d510751040c1d0018001415482080300c1c1d50102042c40108c111038071941300d600003c2c00c09810b0548004010182450341071301c06404418441103540d902c028001079484400080c03a0703413030081c0120100d1b4122001d0f0300141d401c4c0180c01c4c0810000750040e0209480d613401d000080c0c40d965a05003c5a48141755036180c203e4404c454030445801c440f0000c0040782c114000700801e1200c3e110011500451154a100500b42951800b1502040b091750304400c2d1034000c008800466020b80e550042e1081c1c8119194440c021403155014605803184081a48003042d2144000901c8104aa81000c404580c82c14003041c030240030b12a862071050910a40c04098082d00018049034806030364242c000c15451500788a00c1000d00002402c4546e40c1c41960b043c40459016190b03810210020b0b00c0321a81c000c58120300900312410303030719100e00c110190305214204840c10a401032405111310801d85486a0003043c0040d0010b805 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 644922922 1250 644921672 644921687
    0x61d1801051b0a033e0301180f0605040c0804060f110409021b0f0a0201030b030606060f0703030b031b01020d181e051003060305060106050f07020d11090103060506030d0c050c01 78
    0xd036030030107480c1d0003941800c849903941020031011517003000220050614011240744c44c00c641900c40d4060070001000055281250401070301b855190000c2e04050500062008000700d52250303070403600b01704081c0561b03904080386503c19801a14184034501841c158602143e0400b00040715094040c0803d00111085902600e40a44011941488155580302d49031405081d11551145030340301c0f0305500c0031940c0c140541e14045105074003c0086040000001d141805031503410011100c01052460605200381c012076005070020b0b0545142100040304000e0301c00c40781101030701500c5212845a11705224100e00802126000c21070040142450030000700103009299441648004503804601070781c69000c1030031840d4280e200010050b1039854200c0c00c0820590040c030500c0014031400203400303041812583c00d40d50441e0b07540e2000310a071803c19620b52403480302c1a00f25503c1e200200421503c0d5000301c0c01038208504490184c0510f8000f00d5100181c00304c001d1940d004058440c0701540900310 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 644924172 1250 644922922 644922937
    0x706140903030c010510180605241303060f1407170702070305030309030d05010f060c26130303110d0e0d030215100504050c07050d0e04061d1801051b 66
    0xb52032614080000320790035580203503084405244822800c00158400b0035100070030600c00b1800b409070070f2400000130900668508986448084030400f0200807124104403485110098840040c258490030803c004000405d0090091898004401802c1d51901c0c40c440c402c403030319540c440102d0758420714031040c140042d020b1000c0d0b10442002200250301800518824403d070001035442d41340d91a03006007580d1040e4070090f440404101c3c00e01843d940f045000d0582600a021881d84200c0c240380941030b80103207405001c604402003150704542801105c4881101d009964440014540041543d2651200c40032040405c013036070710b114954181b500b10086494001d0040d1a418103210984000038641148e0800d000c030f01ca071400340040d18051141a4006583d03014040c14520700340d482e82e0b9541000703940b02e8280a0000d210703902e1170f692034114001501c403155006004850010f2610403141050300c414aa8400995110310282014801d0394071440032070004210301d64a40b28140ca195200c0b05 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 644925422 1250 644924172 644924179
    0x111090d020f03120705060f1312080417181201052412120a09080a2a03021905011b0507030f1106040e09210d020f041703041707061409 60
    0x141c040c40c404413688040c1440c41e0064010701920b01d494119102d42c15401804d0000c000c6001c128403000c5150f00310390050ba40c440781003145450315142052030001d000c469212502da940041c49078210560861022401c2c002558011011120700488a00782c50f800c591030f40c48081501240410004092115090440c02a0445584c155090b000904002c0b0ba42c408494046000400d50106540405408010600800a0003500102d0781e100c3d45d20442454810001c0c1a040364480200da0a10000400841e8000c200d0710a124031304801c6844005a0301c100e43c0420100e041c803840c0031004622108070260b0100260640301c0c111b50360010300c0d0074500340a80f1201554401032005403a002c0060010384448100f030241850a59869841c02800c82502e0400a036400304110078058a4010340d642020000c0000d600c51100305a0414540035603841f002c802c0b014a03c0c01f5612090200041c801d42d0030705a0510f14441140400f5a50381113180301c5c000006050074441c0d15002d498501403c080c030b0008 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 644926672 1250 644925422 644925433
    0x11b031a0405011d07030e1e0c130c141c0915020c2d100b010c150e01061e060f03020403080304050105060301180218072a050111090d020f03 62
    0x5801203001c4810903041650400c261400140100250704e403c294002014541400804009000301d41c640c40300d070060b8039052001da400c1542011044c07110b00d440d25800703484110000340b2504500040c040010600c008211741c42081460411550100c4200d01b02002d0034202406164403030341d000f02160f81d070986140740d0781c0d8030501c4c58900600007410b8911581006000d64181096004d080f003100c0c08042204540b801020080c980e0040b408440c0da60100e8070014200d282d80006a805052030340008002c048000800b000d45203ea6200342900300b4403800070003a4a45604c8032440d501d0842d04d1000b80d4070711400040001340e2089145404c0110185005428180d0780c0e07a401096030801d82c3c0407a80c60f51034078208891030900344144040e00c011001d02140311b405c0354020806a21034074514400000305540001c144e68080e1041800745541c0b100340348502010003149490030001d142d0100c8855007002d403070b03d08205584046d503a081c0310003481200742501036400c11481050201d40c1030b03058041c0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 644927922 1250 644926672 644926721
    0x303050f0a050423131a0d06020c0a06020c011113030b060303160302010e1b06040e060409021206160c0314072d060b0d03051c0f0606050405040c02011b03 68
    0x404510207980b4610241d0910b84019040801482e00c0102d14244412458602e01301e20321003020401c2c03150070100303035a1141c1401f030301e05000010b4425044074142c6482000c04202c10424103074024014600888000c102d441ca0000d408c520754410306148110825907400300b4004240c41041c3c0a8121070f00038100c82c41c020b54032090303070781d1008051020b4015075900c41c1101c0e03440409102501060300388500c4c80171854001343c0014000d0045026008040701c040d4001a40342d1501d0b40414442074008021208005d801110b1541d98401280d40e602c0500045181c0451a40a081d60219041d03140d01c1d03524103105240080c2c02d1a0304040001c0d142000541c81080135242d403141081c01802144a4980c40143c4a0030b01e030f81039500c5072141c0740c013400340217a0b054003180e032120507905070165201e01c039a010b00d41502c02d0720107004c84402a891841c030340000080c03003e41141c02001103440c1507030103004014994070107070f00721510310307a0301e41045031501084010a44258011a5400c010311101c143d8001e4 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 644929172 1250 644927922 644927939
    0x1060f0306020a020115080d0309020f06030c0702010f1d010c031e0504170c1819020f0304120f0e090709030b0a060302120d0c02090a0b2e02070303050f0a0504 70
    0x10a94816540e4950000b5060466039080c00740a017103021050f00340e88210310b460085599065101d490303508142c2e0311013a00007190740c0c0e08041031300c14a00a107902d8890800d504d1100c160350103600124085050b107400b030648207004130420030058100c1c0a841000c140a00e0040d03c541080750700c120300f000b64030f00c1419032625411509100c01641e80e80c0340c42c0c5a5040c5806c0701c40511002c0a041410b40c0704030500c002d40e5070359a40507039042101040700c481030b4548507054800b4101c10100c050180d0b0021850101d02107585001c1d5105500a103803040c01e00d20280003d0340c244042c11800c100107003c20100102c0e0741008020140c0010302454910081c941d640c8421042d50700c2079407114195915642d0030030079444c0000b00030407011507580250a1078400103401078850440741e90020300071403d050014120b09900d91102c83c030300030064501c1003035140000c14080315500481410849040c011300007a0b2035480003d2031029039926440305807404901209950040d003017590f0032401c001c010040480c0118 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 644930422 1250 644929172 644929199
    0xf0b21090c0906030c060304060f0608030c03030601030b1c061a1207080607030e03030f04030c08030c03040318150e060403062c060c0a050a17070c1e050309120106 72
    0x440480c0a444401d409104122140324040c0c07035103202c0d90007452603002c29512501126001a0300c1480080c04170310041040b006481d2076031280c0e4940c000842e040e1802c5c0004030056102d03500c01d0742c1c20040040710b54200302c2d01510a55041f03600c10798650607200007c0603a4000e541840901a034503011301441030008200c070041d5250421190442c460030024040108440d42e0840040c1c02c3c2401100c0c0740c81c02242d902d00000b8450007030321f911400850141030042100440d070300d41141c40e2946ea450403440c022041c0c2d01c00c1d107003100000c0d01d8940c29110411501e02000655004011209160b1501c4030300312a0a80031201d820b41c0000d042000000007074462003140042e66125110803144d4800c0c4003900003089694122911a40045082090341e040c04e10858000b81c04a08041e61a810301003400c841140300c00c00000010352551061181d004e401c02401d0350150300c94042900300b120089070709010000c800000410743c0d4000e00030400e0500d01840078820000301c903000065003655900c000c00b45c44 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 644931672 1250 644930422 644930431
    0x1a09010f0806060d1101230d0b011805150a110102070303060302090f060f01200609060a1a0a0e09160b1c05060102060c1b0a1101030c02070f0b21 64
    0x1500c50020030008080309119a07030340210101d41c075486554080d20340b103242100e250503550402031b190130881c07000d9800f041403020610321000090303100e00c4580012001040c8890b611804600300d44c42e001600500f0b4020002616800740c480380321002c1c1d01c001152280c0000c400b00d02804000200e008610a09202070001c0e1400b0307580114041d440e600500c03181503809015440360b01002c008021080d241c41c0c003940d2400800b031070680305000315002c2d904074070f0540e42c030000103900400007070040d02c500006200d0f001c5d003501e90b420000d010440404552030740c209507030035130007425494080210b04d682c05142544221990103480301d113040d421303034103021018030b4200101c2e040c000310302514928000c2c000b040c01d9a0b1420403c00c40c80c20180c0010355699401040e101d9454400116111f01852001c4114550b105202c21505804840e15001c030346144401c900c030f030002c0e16184500c11914800220001140d8059050012a43c03c1a102d000c9552002134801c1c0350107954040c04440018114070380e17208 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 644932922 1250 644931672 644931689
    0x50c0a0b270f120a02010305010506031302010f27050f01031e02030601021606020102130f06020616120c020f0f06070c110a03021005090a0504020f0a0809070e04030804060e0307080d1a0901 83
    0x4070134052001404942d01a000f2500800080c41045000c003182c031a030013016130b02424503c1095213209011241a001d069001ca51012000b4805030a14141d10440054400071103858180a01420045048407003600382c4c100100c0c40c0710501d81405401d6401144c10442c1071056170072540500c038040551103629404500140e500069403d5180c3c001c099683c050041c540501e40850300c0c25030002d55800014081684031030030035612001442c02104014803003403001006011091403000d01944856280c0c040c482240240f00b48810703640c4001c940c05104000c3d40c1c480c0c012a284588410400011420b449900308021507008000750341d84845049908d0362940e0381654568091082c400110a1640224000c600502c414800c0800303400c26141c0c019883d103024100c0e81e40d0450310501e4000c1c80c1d444084a00051410701c070505620100c0140308901a40c028440e0802e4000081d54a1042400140100d0390900540711008900d80040240c00c4d030369115102d050800c40c00040c2d44800c2a40030086 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 644934172 1250 644932922 644932933
    0x9050601181104050405130b09070e0f061005030a0608030d0b01030b03010603080a0c05100f020310150509090403030f050a1a030721021c050c0a0b270f12 68
    0x4001d075503881c80401c0900030000e100c181e00e2034a101c00580140e000340c0784035a440384001051605428150a800c9801c40320400742e900f4001d840907220302c014010510300003482c20018180201010304103010303520280c00a90740300c0100030120307459003000d88101e241a45031140020048402c2002d000001500e034000100401d051002400b00c03584400d4031400f0340d040103002c101080c000025127403841154106071100b903901e0310b800707403c140608a00d45061403070712801c90003640d01a40a5071041111501043c4180d0701c0381d00c54010004100c42c5040010070400444006090000015400c2840b0b4103005c90f211103002061001d90700105c5496030110740d0740c80906c60140d510424031101389025805440900d0070305081c888012000c1120301301400c2c001a40c407045486140030383c60a1040c43c5e00f01031428540740361498139601540320b0030703104690001d0086424420a0201e0328902c49404100300884402e01a85250041d0000307020340c001d440503828003d03502e50591039401c280d9000050302 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 644935422 1250 644934172 644934179
    0xf06110709020a053915010b300a05060d052d010e0607020706030b0a150903080409140f06010c03080a060b0a0908160302010c03180b0408010b0a0503030f0717040909050601 76
    0x101083d0616900c010300d540014607101b18400d9801c1c2850544071f054820b19035460300840d00b080c860803c01448a0f20008590a020a03401c0c036152603402891080f07014042500c508041001c076545102d4043d0054010b50341c41410181e2030f00141d20481840c0368480c210204000d251401c480c0c009180e903400e0b422071410011900d5042c44a45c001d41100d0400304294403c0700c0c08512500140d00039848500490394190340004d001d007a441c00210b5211907150350725034541c140c0c100508113801043c1145002200414409201d80000c24410001a5a501c1c500103a1fa01e0484580070f0140c4810a903542e80c100c0444c5801880d0300501503003400c0c0c0c8843c030000d4030f044003452a0401c180407100e18000049814001030780d10040c041c0d003e90f01840c01070360840074045501d00d48541030340102c0002000013000a01e500e4103401c032120f00340044a441880704e0f550b50a1503101e228011220b64500800c004a0000482011408040499114000b41020f0300c8080d848100c0311041400e860320b40c080760040 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 644936672 1250 644935422 644935507
    0x1809040f11040e15060a080d020a060608011107020d020a0306321005010f0302040506030a0f05060a0522110307032a05030a0e010e0a0602040f06110709020a05 70
    0x200c400ca00305072020020710700d509901e95110000c07211004411310107413001c40c00565414440c20080c4c0008000e44540d11110540a9900c2011000c06c0381c4607400e000c1e0000c1c8901e010b01c82c90515802e00c2c07500d82d241080d980c0c00c00000e004200c0341242d020b081d210000c000f145c01441070901c1c11447d24601e054050b200303201e030110382c01000071610f001d080752400c00c0040b107030b240500030803940700303007000d0500d150201000e40103809142c0203550040c030007000300002440385400000d140c811034641000903446080c01c0c0041c1101c54000e40ba0090a0320761080c91040404c02d40d92a20304102c400000c840318603050b615040d900a031184400030741c4405420015105030764404801810440340c1000c41c3c0242d0798068040d00009156501040d0344d0801e1152071a400c0d0030143c440d403821010340d880013001c0e15041000b50003d014005280b003c480700441c07524010442d500070300d450400100411032805501e5801783d0b12108006041001c21f1000d4059a4a210b64050040460b00501c121110380038124 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 644937922 1250 644936672 644936693
    0x1c0f091b1403070b07080c1c03060b0a080601050c010f1a0f091b0d060506130e06010e061b0a02090c0a1b020d14120c031201080703020a0b1809040f 65
    0x280081c240214620240e690001580012140009011522890907081900c514041c07410700544d2030240b080c203607501d440b040c1d060b99006601600c04100460f154900400503002c0c811000012070070500107d580b540c010009040e21448103130000c00e44410312035800341542c0b18010003940100d102d0a0180e154582144000c40b051825a021007081c40c05060340703140c040401544881c541c00009844032031000c01d070000006082e000d400f0320b0b62014502c5aa030380301030ba02d220300d42a600030403010135003543c440c0040e800314034402030403241005c4030607510140b80d4101c0208208644107031494140180c690014184c0309000c1c221100c0c1d2240c960030005400103854101807900c2c42051900003006a40e04003029031815002119032129010010f881450300358102c0140ba482803000c60282c0c0344a4000006148080600540ca074040c0d0741c80f01880e542d00c01c14003009500042100003400603a40810251900c03101d03c16140b04010028004107002c240c003564191241c2001c24007a03414880404038 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 644939172 1250 644937922 644937929
    0x20c0102040302030d080f220b010602030a0201050a060807030b091c110105060f0d0b182a09060303070b130804090207110a032001050c012301060809031c0f091b 71
    0x80407400b904d000180e159a034407000703080480102401052803030340741d00c0700232520f4a181e00c1401501c0e19615000c02075500d4000490040056007000b002600b000d003d80103000440d05000014244c03113082d1b545020b40040c005028203903034416100c60b880b90f0320300e1258910188285450380d000c1100c01040c02800d4580040c18140a5010f0000d05003440d119404c0c80003555400580343c0700703035440301e1007503104c40102100c20b601e4910a4091900d0f0a00d80203003c220034101640a0b0b00401c8580b0040c0803800b003007151290342c540c00610005020450750141c00c0d81c00f40a44241c104174030300e180d41d02c181a0300290091a00c103940843c07110100880031903c100c00c034a040302c055419072b00d59983c1200d1000710603416118060441100c9403140d015070b080c0c0f648402074900030b00110005121002000f00706021903c0001c41d2080000b41c22070180c0e45190069682e039001e10b242c00007130003410704040d811000e8041c18a42d101c004040001a900c14000d5081c0726100c000d030145420706200e508800582c1 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 644940422 1250 644939172 644939177
    0x70806190b1603020a020406090b121c0f020a080706090b0a0504021003020d0b0d0b070206060108190b0a050d050706020c0f0d020d030309050a0803040614060d0f050709020c0102040302030d 83
    0x10301506541c202600c1200541c00c010340245021403a08904207040074200940103400c04101003040704007034005001c03000090301e40d044031840c8030340e495507100c20902412402c1d0180f9140e00400030701c10039a03030305868030300d00403107010385055619007a07254403015041c4c0e100c80d85c0303564517002c000f0000549a048100f00701d0038450342c14a0740000f121000042c080609140e07000079442c0140b6010b030082d80305c0e094014418042d1501c542010803144000b150320301e00500940300095081e41c0150002400b64224030a044011169540030310002e100080c2c1c500e600c000d11000008450392105803040e649881070010304042850458007a280a14181180348540c61038984581240c89600e08144916011980d0320214011030070190020f2421080142c81409416201c0c0180000d00004600980c403818080145c04240c44d103c2d811044c064404990101001000308040b4070b221000c041c50320301035000e40d40144c0d980c0e10504100d9110b9145001c050750007240810961400744002c0e03a400c500b60 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 644941672 1250 644940422 644940469
    0x9010f0309050d0804060b03010c0c0c081203130f0609050a0201020f210f04030c060c0c0e010e0411031203010f030b0a02030f0601050d060f0b1812060601030b0315070806 75
    0x550702c0d1902c9030b98240300c10040100b800d00250600c40b65420100d58080003900070007034104c50040c010559840c01e5400c0c1c800c41c590113000600e070400066403c061745030000310340d0b096849a181140354a040d00100f50b80c0918156056000b280c494071070610014481c5008000c540b40a01c006810040c1c0860100101d42040c207280d40c0c104c00ca4442d0311100058081e00b980da03074510b0300e081c0b100341c012908081c1c0000c0c8402d01c0410503d80008004907054003402480304060b54a203a00490b0203c240515404142540c000c1800902801807244100c0c0005051319a01d40c4803095044042d04242c0c014070000381c006d0410028020350104980c0c0040112405500d549001500700d07184c2403003e41940d040040000301941a408d0b00c1c2c0c40300340130781451146903050f15980c0812194a8000d8200d4006041c00040e112056180c04101400d020902e6809001c4640e207850041d0010704101c04201d4050103100350822011444020042c41f416032a03c801e9241d040060901043c018440c0800030700f8200c8 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 644942922 1250 644941672 644941691
    0x20915060306062b23010602070506090102150a0501090e03030c120c12070e011b020d060b0406180218030a030206040f020a0b030a2708031504021201080309010f03 72
    0x18030040365404002502c0c0c1e107a880e4940c4c05a8414000040064001c0d9134581000040001d5103400c4000610500801c80d040d000d60221340094002c0300307102d03074005070f80100402c01aa041007170103400c03904014010386070118012101c0200d030920443e01701d68041c0e503c50060203007a120744540351005032813600440c21803910b0006000d1500c01c1800200c00c80041c04000340c1344000000c22107209402604503001d00c1e003403106000c0c2500f01d80508070b50100c2e20302c0051010b102d07094501030a0080d001002142c0268554075481c1c003c000b880702c19030700b05880e00c20200d01d800402c40d00620001f40c02c640140d9841840200e5580003c0c0314210500c40c0c0c10000951b4007090b40081c2568100341c200e03203400d0580d4461703c00204040307036952140300420740c0402001910206580004810700582d4401031046071988502080030000c080700602d480002c2c40030130301154400c0900000010007410051070f00c44846074800d0300303041c01d90080103d580006000400e0356808910b04c103413030140d0300301407285440 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 644944172 1250 644942922 644942929
    0x8070203130e0411031b0406050919051504060303020703020907050f07110d021305070807051912020f0708030109060f061202090a1502102703050a050f03070507020915 74
    0x625201d4000b0a0b52480049002d2000503864482040401801c8494600c11080704907580d0700c400036014070442c0703007400005103805d0105813144510350210584c0c240300e0b1040040c000910015141c0300e540700c0e101e289840252114840c80010358081e40082c021180703144100030302224014441c2c07040100034043c00b8040b00228083d0380309182d00c03907096042440303150082031000702c000398084d42c401c0749001d640640b038540c1d60180d4007d101740d40c0c8003001c036a280081a0f41e03d20552100707515030490318011084980c41070a001d44882c20f4150054901110b1200030142c54000400a507039100d800401044007001d14480e440c000c0c04441d1800444619048000c1c00010034042030000382500000d9484142d40d6142c0d189020700000c207141ca980020501001790703111a0101001d025600c1c0806640c1c1803035000ca15201d0440303405026001c0d800e00da5400306c1e902c0d04449080000d00c04240103003031300c5110320b0024610a450342d540da692074117518010030104143c0a410052030000742c500b100d181d5103 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 644945422 1250 644944172 644944207
    0xa0b0d060b04030f02091e0103061b020607050306010e13021b07080a0305030a051503070605090111070f05011b0506090307060b04021602060906040b030910050f0702060a09170309010c08070203 85
    0x1703404a0320000f5035a51400380d65403843e108207014031614071700c3c400401082155805004101d241c2003a80d400b07034070b0f030340b0044e41e480d10242e5040c00421380920004e40d6541c0b103045a03003d401d10141c040e9040e00030308040a006c1e40c00c191511690341c0c1240d103074244150010008031001344041c40003841000090345010300244800b8017088074403929180065004001a044c05405000c09011629440c2d03480030300400c2a08480307113550001d450303001d20240c1e84200103460000c0d610203203180040c4501e00001903d040c1150000e0381c1c815000550003801080082c08031703d10038190203015540e030324030910340342c8202c031442d00c19144034600c1072203400640b41c600756124840c40e505130b440540d240440303c0060624041e035407094101c0c1a00004200d0080400b14040c80c42a6070120306000c2c640741c40300000c0d258142258002c005034894400624004230a42011070114060381840c1c1080141760420303032650740101c0d207511050391600c40c98000554004a40c1d64041a1407001d54144070402c00742c044190b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 644946672 1250 644945422 644945453
    0x1050108120301060c230d030c02190b0109050402031606020a0506310c05031f14070f0e0f040c180f0b070201030e16120c0603110306010f0e0a0b0d060b0403 69
    0x49680d42204400e8400d000303e20f0401b1503140204c6001000307581c030080113010141001c1c0c005018444c5c161440d110a6a0501007865101300c0300d2003140c1c24514070a0040c40000c0c03003aa0b142c4038070710b25600a9010a08a603024100e80c1e406492070007045d081c01490100080c101c0c0c0c2c0e0040e1201c1680702c50b0340c00310303c030381c45a058064918502d00c2c641b420f00180d02070964111035414025103c0030b10071070080700c4801688482c003c0c0d007031000c40450700100071301410031030b100c1000c50030801281800910902403407003c0707007005003980c8098039004080f4085620443c400d0010170840075181e594058540310120080401c5030080504e681004444540e0380200c80c4000c0c10715031a07002e65442c00909100a04240400e2114403d0060b41e40b0b1084200c81c1c8021b070f0550707603034402200201e25103209001b4001807501c1200b42e54959150302d001102e2408810444408106402c03040d44034903a603584030b1800a04c02803c0e8107481e00788108031001200e0743c503403040d820340c1d404100c1000020300c1c0d502900902c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 644947922 1250 644946672 644946683
    0x218010f151d030c10020f0c0415260d08150d02240f0c03070201141303030e0409051e0114060a05060f040b071b0b090109090b011b0501050108120301060c 68
    0x75200b000000c02d2800800c1e00c8240d60040c2c501c29028036030307640081d0041340305522400311135001035808207000c2202c4d00580d0304a0341090900e42840a1580804850501c0800c404d0040000407503114050415549504880006005506003d03080c2020240684400e004039400e002000c0349030700044143d0003084072820b124000740d545400c0880442e09440761140d040b52101d6423030001261031501ca50145400f01d002c150329901583c490007030403083c2c0d049005000c50304807170107046840c02e4500001c618096940b254860081c01e0010b1414484020401504140c108045040c01007803401c0d609400504942044c004042020301c1c0d48603451601140c83c140c50259491200b4242e6640a00c40da401c00f80d44882c0025120007000881158109528080c01c0c841c4191a1108070101c003600c44c41070344500184105000f48550741c850b038040340d401e6905042c040c0c0c6070021001910141a01080140d80d10f03591400100b01d00d540034800e58001c110b43e408818a15030400724064080704180001412 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 644949172 1250 644947922 644947967
    0x30206040b180c0418051009050601060801080705010305150402070309051f0203090d031107030f02042306151903240305150901150b03040302070807080a08070206070218010f15 78
    0x5040705c401010b00507007a0418142d1314040d80d221a0071020700f602d0b21046440c1d200f21400050380318803406216050343d4001c07010f050780500c0e100044000c3c1502504241134020360080d044240d039a244014591213211381c0319440802c1c82c0c0340411108450880c00c81c100718008101a1038095404000c40741c04200807107125180301d000b41000c44081e0316858243d0038a02c0382182c00f00901c280800201000c5200325800c2c0980345540d42282c0c40c5824038144600900e5803140071070701c1c6e4504403203805071000290411504000c2d0200640540140d4024180042951b940e044401a007500901550802024420328081032440c0c0d149559082c030000d03041e40245203817003c28121002904110409400d0204010080c2e880e1320140f0410b600a0b40d0403405882041c0b40010718003804251001294166000782a61a00300d40702c62841d580506000c0383d103c10700704903c500590307500111000c803041100d140e450319130400b41c5017124220a500079041502520581b9000e030399200300308146241141200c0c01 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 644950422 1250 644949172 644949191
    0xb01140714030c06010915030b04080a140a0504051215060118030204090b0a0507032f0405090a060303020d05041a0705010212040b1b09060403030809030c0a030206040b180c04 77
    0x310800301c901c0a95150000003a9200c00c8400015042c0c1a00e95840d000c01c03040c0c0503104403a20504071380c40001e081020000005010070503060251074250000e0805100d0000c820f28112803651010a0120106030089001d0003241004030803491440301c58001020050b019a4916080b49001004103040007184035170703200100190701d202002507a020b4418042d181ea68506170004500441e41d00320303454a803800050115129000f1807a240d00d0084105180143c16402412541022514016032000c02c0000142e80d0301c2d002000e910a140c1d62000060742d44c01c41c500207043c1102c1c0312185c020080c0500c014485a101200480130340b42960920755901e088074900039029014039003400c180c40e16200c04210078000070340c191510456a403000c984030200c9110f00107505004c0d110380385420a40034403051002a0082d91121341051a120442c0d04081005654514004004000b100160007031818032040080c41410150070094001803d0052240c84d07400079912a050003046204075154044403 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 644951672 1250 644950422 644950433
    0x207050a2a0b160c0f0f03140307030918020909010806040c0b03090d0c0218070908190512030603011d0709060e070c0b060616111c02090a050c16140606040b011407 72
    0x25008140c0e00ba0525245c996a45551541c4c842c0c51205442c008154905070f48500400b00072200c0309a40754507a166002e0804114144005001c2001392003582d01f0410b10b0010b980d2094094002d2801e84003c1544e440c05281941c0e007036005600240c20f80b0401c1c0184030142030041003841044001c5d192035268072825000164084442b200c07440360140e000d03000d22140d194410f80c2c59003a074020724100d0b0f00310304550804800003140c0c500060301036085a2094440054080011900200d00400110b8081c61455007a04241e15550355400142d0104e0000c0010910700d01a190041c480700c0802e04551074086409044941c40e018020545032180000a9190f9201c07401c3c0d4020604110619101d050240741c4904806c615178090307440380c4801d980480415051740c12021145602500e0240d41391074110640c406003c0280107040145010300ca401c0380010200040d00e185401800c4001e030314000340f6070003400c01c0c0025050601940c100a1071380d1041c0d800640f0304180c108040305165030341c406070800707 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 644952922 1250 644951672 644951693
    0x220603110303120103110324060a150f080c0f04061710050d030f11060a14090138060313020934090b070b0115030e0d080a0207050a2a0b16 61
    0x1000c041043c00700c00305184481c230070001072151310b06880c814a5035458802035401248054034000009010243c500c10f641d100da89000d8101000d00320460402d5543c00700352485c0e0b0000d40000d40003615000d010410204c107000c1c00d0760031000384130815070060b0811011601d079032041d600103414005400c0c215581c1c82c2c89426038020310030300d01040d600c0c0307070804405040c00341043d5010002c0f00c034103e40214900e40018850126054002d00c5a01002000c0319059640441d05400101002a2486c541c03800c64440384020b510581e441d100207104200035104010300c20074042c200c0a0200f41003502c41c110410381c846450661580c0c04440c0c03940c0013004d071044840c0b51842d0400c202c0044041103440070401c196035150705035a8092000185040d1800b8100c04499592411481030f40c001d50038081181d00401482c1e400038030380709015103403102076202c0c14a0641030560840b07070444100351000d11281e200d1038801c40e86110300301c910015032510425500a015250f104040248141c03c08820000100103 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 644954172 1250 644952922 644952943
    0x242703111f0f0f030b03030915120403030506040507231b03070503070b160e040c092c06030102180918070b0c0615030303070e2206031103031201031103 67
    0x407000d00203a0069801849420a80c20580104800028a070000d07400380c041d00b4040f61024000703504210301785081201c0d040342505c1004040c50b0030060000400300756003680c0e100328002c1e24045103034105001848115080117100c20204003c0f0741c0062b141c19000c8441c0c05003c1007910106849000e01c0064014100c4d10754240c0c446031100103110810418080081c007d102c8c00f42612502998903400c030705511040c41803200001512110884c50b161a15034450341015903103240c40621681c0707031018501443c0c4560140c09080810340030080d10100c0454180d50f0000040e80207600704030072031350b0b4031444440b14489544150b603010f0011b0700c0440b07840c041c12902c2c503243d0b08580131140d880081a445a11900b000240c90296200207090504e441c0034156810401500440c91035981c8042107507640b14030786510f50b010721900d04221110394084240e1060314074018000990034510f1422034410030701441203d0207600207014000381c1c2e51500506d1b0341140d4011000c000f060102c1c000080c01e0040004 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 644955422 1250 644954172 644954209
    0x801151409040c0810080c060307030515150706110901140c1002031e0603060123120d05040503010506040b0919020c06070f080f0c04090e030424270311 67
    0x303d51038120740e0081d003941c000e0f40c04260800c1d07515150485661568420b81c1481e4000302e041000c40d1480e44a035200310350000f207040b228000d90f0f0800c1c001030300c05035203014a04440100800c6586c18406148108080c5070f446150b12460034040c0000070f00790300444050703205c03000400f0891260117502030103100001c1540301000c5649107002c80f441218110072164906d401c8076508000f45040c10001074181c181d0380301d0284101c0d900008843c0d401109102a1460b81200d01561180070484040004805d483c0ca02d80b02d4903250341c00c0c00c042c9400c440008084a100d5824440072050546843c1d03104c80e000110049440703200c030304901c0c4484c080e200304c5001003004c1c0300e00f504004113542d02c20a003004218503075583c14041c0d1103a90b031051807440c0c10795408d00050401c00082020440650152240f034046000b6a41825907600c08200380119080f9070070341c0d1008034a40b20f942c25a02000c40301d492014031031030034030b4204c00f0414000c11101c01d0100805c20100340030720507441d6481038580302d02d081c0c910 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 644956672 1250 644955422 644955431
    0x403111b2e18090b09220c08031b010504020d02091b07050714300a1a010512030406090b03060d06020c0d0311071121030c0d020d080115140904 63
    0x80009142d0190404518072038044200003207003c040ea40181104460000c00003c410303200c051400c00d503101030580c942110405401d054001440c030502c5040100340000c06940c03154614844001031034018051890264548820000113958001021110344c0c0c058580c140c45698220b40d040003407000c280101024a400310b200d408020700000c641c001d44200c030b2580d4683c12030920900036600b001d921003011043d00901308205c01d40c2e4160069480440c68011120b10611a840d840240d0748000d060001b000d4400c1c00500c21030800c2c080720324600d49140000c500c1c0c070b4075203440140808403900540d00a410000085181030759440403080080381c1100d030466035041030300446644d501c1001303425004a420311a11100b408060804e81e00c80541100250103031000350420802c4004214490014041c14041d00b0400721004201134160000c44000403d00e041da42400030789484142c009220802506100500c11610b11000c4d0f124452400e081000150164949004580c0107007508203402a280 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 644957922 1250 644956672 644956759
    0xa0b0316051003020a0509090603120f0c0f03040503030a0e010201061d04020924040906110301121a0c040e13140c040501080607020c09180d080403111b 67
    0x203003600c100490304100c2c1e80d00320040708410b040e003d81c0074506882c40420018800515a810940f412550000e4003d090303541d44281d5030a900c00a03084880c5c4074403404c0c0d000c00d503680c24000c1009400c0d036940c00d03940110b0419240000195592185004036410084c3c102c14160b0b0b5039000350444030103400380c200c850340d0800c1400d0b00c1242c13810044400360b110b8841076000c0b6200495a1a500e0364101d40c200c3c420310800240c1051101601c1c450008980c000d581d180904214070713410b00907601a2600081d0601c03407000a040c401000d0098891042c071501e542c0c0d00780319954400c0750841e41103e1008501551503a942c0c0d881d0300031610f0302207024255640e00341692840401c04502c810408a04035010051640c807808126a600422102040941d01940c0c2c20388a500e00300000a40c000c1440e10751244105c0980c0001d0700b8001e02180d00004141c004040c8820140c101e0003001c140303072029000b0710900d581c0e04400e40795008802c40060050700310492494281400f807000883c14200e403a1084807401d207 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 644959172 1250 644957922 644957953
    0x20c330a0504150603080f1606051e0c0c0c0405060f03010906020a030c05120403030926040e090109120e010c06021c0e0304080703030302133614010e0a0b03 69
    0x10115411245010615000048619540704030f0b015250080b800a0802c00c0007c014002980710f0440442d9144100121000058075409180d02c41c3c4103222803201d652400c03c0011040c000090071180c0c1c08038040c00011a82c1500292001c1d02d520100c1c0e0120b220740301c0c0c2010940200300044420740550906482c40107200c01038000717250340b54481e60304200d0f89800e000c1c100c420340610425942e10050140124003c24480e4000102e034500030a80b0000c043c1c60910705802d195019010b4102c80c160110b4204404652200c4040d8000003200080c0850516543c0313401a08c030300780711404240a1400c00c4500186d00c28894028003d5002d00d007190f803074020403002094018042c5607019580d0600000e603000b03550200640d01102c1c4510000c0c01d0280c01c580c1d0a03400780d000b034800c8040e0b0b50402c480c0000c0000a03030b1680b0400708108041c000c440c0d040709107462070226101411039011418a8001d40d48501c01030030b00c80c11202103007032131000c6403113400380780001d0920304848035072510607101d4007a40c228 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 644960422 1250 644959172 644959181
    0xc090402090609041d0d021207080f040b1219060305060601080912041202130c0f0318020a0e190506030d050d0f0e0709061401080c090f060412020310020c330a 70
    0x34602c0125040143d1b0b004d002c03603483e01500042d801c424014800580050412130141401c0c80c1c08209007030509454590103100b81d00644014071420400364140105003048010702c5030b440000e86814003c150071501e03850368582025100d00d04005034040003c02c1080c082c490000c10410f214501503841d40e5504090221407580001644a4011003510301d81c405102e106079040c22515032169003624980b40000d5000f03128008418800c02050340c180c1c0010383d9000c1c40d40001c1c101040919500e03040002c441002c0b89400824022845d103000240103260350b0020306080d080d40d40f46007080c2e0f40d05c8442440b0f00030b40030b482c031640e4000d401d21a440e0500c503008108001681c022010030400d03a5595411a04401c40c03a102c400d0225010201044441d0240c00041c41c0d440340c040d0001c1184600003002c2036a6500c41d900424490501440342d0307085103018048400f06c031501c07e10540c00c0a601c405441d071150300d8465040782076541000c1e5121106001044420300810b49034400640d407400d014401d0190 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 644961672 1250 644960422 644960471
    0x5040f020d0f0c170705070f060516020a03140702040e010606170901020702100806030f101a0915040905100203130605061008040b0703060b041403150c09040209060904 74
    0x320b080407200d010504062180510b000499904c400c42c3c5500401207114850001e04203004100003000003001064400180c20b40991045100151601c0d15402c801e02140c0d00200090071904145802070111b540700b09490000c0c904410b600e039a40c0703420710000c1d0040c40c000b080b100441d42040030000352a6040860780d103140120040da00300c1c1d9520010014200d106400c0000d5010a10002c9103203010700c981c5c502503114502a04540d40d81d00140c65580c6409854000788003400e445440752100412042c4040c4003401c03065601c42003a040c50100b494003620036000e001e02850340d03800001d0512208028039103070300e0b0122008655074180b50301040e480c185085416503c46051801284860400d041c401000300c4c01ca42c1c0392006034846554114001e00064540d02c04c0540310030700401d10680980003880181715000c82055112a9042850b00f8054400d00410005640704100312009401e0b008a40240004440069840842e200050b040b17004414103250404c0c0741c10701c0d0940b410680c00540800 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 644962922 1250 644961672 644961697
    0x8060603010b150301231f110102040602150406060506031f0b0f0a03090302210405130608030301180f0c11120f070f110d3f051305040f02 61
    0x42c400e182c140708020284160419a1038001c1004200d01840c4804006080781000f6a60300d4075600030340010341243d22501024582e50504000106903a000034200f0301008080c0000d42c2403516240000e501e5042400b078801d194011000060304000726030707001e040500001003602d40c883c00d14030b001955117002c0c0d0000c9510080c80d0280403581c0071080301a200d911007a0000c0600c4c00701d0f0350341d04074080d0036850750440942c0701d4081802900001d602010f001148911041501e482c60941000500890111051081031402800780031085011003201d0655030940100c0e07004079031310740c4424002c00441c009030315558500414001e000fa4451801203820f13000d50100d5486034062403100400c1c0c41400b00301080000c0801c0b01000140c0c1400d08203e0b041c9c0030b12180d100e80c80080c1d0106204160111044580e985007044040b803641400d03400904c819074030b09104020101c19642030441a024521101c01c3c02300119000c040c42d04040d2042024090140003030214000c80c024400280d0007109404d90b0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 644964028 1106 644962922 644962931
    0x414060a0c1e0627081606060909030315062102040902070501050f0708040b0a020f09220b09060609120a0f03230903061f0305070806060301 62
    0xd042c84155240c19040301580b50907030454044224a809680c0c1d44902019181203410800f06480e52141c40240e95031100d40d1038a10026000000801c030500713100c0003140742c9523942c00840206202c0d031400d1081c21042d2001001c0c603099401050002001c0c46030401140f61010740512181c0c07524440185819100c441860680c1c0c84031106444070380d191404d00205031035450340709900c44183d1409502606150b1355040d81c40718040d00109045401050017040e441c0004d003104c4040b003005120050709404250f448189a031502c007043d484501e03150000310741e4105040114480c4c0d2008094610307045a40c820484180300454000c2c08a00c0780406620004986500c0c03103841034000d446a6004002003c7d04054000380301201c0303113201c40280800c2c8641d890004000fa049408140c01e42c03a02c01c0f403250001c01c0c404d003a500c0907004e8410b4113000111400c0108040340510001d400901 = true := by decide +kernel

theorem cover : BRFrame.Cov 644784172 644964028 := by
  have h0 := BRFrame.cov_init 644784172
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644784172 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 644784172 ≤ n) (h2 : n < 644964028) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
