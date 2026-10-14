-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1303
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:16:17.668986+00:00
-- url     : https://prove2.me/submissions/40eb480e-b84c-4357-9bd6-d00c29e93c30

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 234172661 ≤ n < 234352517 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 234173911 1250 234172661 234172691
    0x12030a0216171b0d02040501140a0f0b16140d080a060905061503070215010305060901151d072d0e060c031e0f130612060b07060504170c0a0501 63
    0x1116100140140c03c4100c1110072002c0303041c03d08208580c3c82825060540007580702c03842154003a02d600200a0b54900704601040402080b50340064000905103000b13000148201c01a5110741d248000308010a08183c9090a03800300d440810080c0e034415411a0201315a01c002014040e800c160010403a10761102845425541c0485055401c02819150000c0944901000b0750384500a407041d030b4010880d844002c100c100e8280d000b0380d0681d10375001d01c44050300a00c5a00d440169081d8802c1c8080e02e05554001d00d5000000c41c20745948400c8006243c0c1401948954900400040711484001c01070800a0071214401f43c41e5001450803c02c402c80e60a00000b118800a507d400640c1030940070410800c030141411005590f00e281802005101100b01007c4c0c4941d44500811020440c1801002040c008200601d000303103500b008410051088284211504660003140204141d07580d400c06842600c3d40c0b1420302107440f400116920740410102d10503e003a88640002d10110000b00307101e03 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 234175161 1250 234173911 234173939
    0x11e09290601111c03090c0807180e100501121101051305040b04020f0c1533010324030309050906100507050109020d060b0f0a0f050f12030a0216 64
    0xd01504904a00030984a602904004100c00b00d030008075080310b08160b4a00ca1000407902040002c2a04c42c1510743c00c202c01d20300c12030084c26403c0002c0c0005864031480498100b1078400c0107500a50b1007000a61004040c0280c40001e0940a010b10940d6550070302044070301d1503400140d0303007070108042043d5550321860486810340000d00344540c550781040300700720003020310308615503116508202104d241a081e5000d02038040f0702d81c0140111020500c528031001700002c0401091841d0044c1643d100004903280720461401515201d1041c045440168010107000c00b90105036241c8510800745080c0c18030101e01903921070f94882078542d945001b0700c43c08440a0381c2090340050020350f42d00d9114410f01c003074060580070f00c0000c82c4900c1a0740210705030a240b19010754031641c41c0c2e5160411408c1c01290510b034107009030b42418103940b500724000400c14150141502c101e1140001078079a5999000b000054540c400a4a0f650041c2c1038010b0751320812800440486502e00790001440b400003000303 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 234176411 1250 234175161 234175223
    0x103030f080f180309041104051203030f040b06010e0d140f0118060b01091d150d0b01060e1201020f040806280507091805180a020109030206030603011e09 68
    0x90904240c40f0b0220f503d0340d51800020740c402900c001c1c0144429590b950003159140b1034144001d6a90310700303000610500c8004a64150801c0e4010400d01c50919224103190764015048180303101903840d8800125900300508c1c40c11507105010003e41414400304006041c03c06070310a08680c2c4040081210500f62440c4140c0c00e800700e201d50442c00003003a019000041c9420b0b051502d03485203501d691103451560310900400400d15003000400c0a1000010210300844004a9212286812a0f95046044001402007400300032910644602c0c9441d0040a10344901e4003100070340d1500e01c050054402c1d604a031165400703e10600780410840b14800c00881c140c8289200003120b5100c0090a0710003506c8003801c030204029014000040d903210991161a40545080303001c1014100002c1910709016102210603031a0400040040141c0e08601050101c13903060b03d0103516030391804006030042c01e201401041c0c40c1710400010711418816130055510600c541e40103d08042d000c80201c1080c3c0c038000c6 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 234177661 1250 234176411 234176431
    0x1401030803040c08030703020709050a020906091909020d090b0606070819050403021002160512030418090c0303020a0c06020318040f1d070e06040b030303010501180e07080103030f08 80
    0x1800410100002180d005015944080c0071a43c1c42c1c1e81070385590300c140d8058006070400340013440f44440344e0040a82103100128150305118242000a803d80b103540505403040e0340c1141d01070559020001d20500030840c0000442d214005042030b00d0242040c0700c0e0031a1395805030320000744a8a411401e0b2100950032095445c01c0810700301c1c0803002c05545080742000c3c404244030000059480078031b0801c581d40c0a5001e0b068810b801c00b2040e2044e18076400c01407055510b0102c21031890800400d4504a6182c100301242c2c0300051500032004100110000c0c10340401d54002209140d000031307201d41e605100f809240b0529551300e10403a164081c081e0b0855510108130b4004d02246429006031221103141c91001404018031640c20300000c1c0104400300281e040a031307003080300001d40903920350b120030f0554061112203910000aa10391205004a506000b100b10300860403240c030105007400360011042a00c811306043c00084c0c1400c009100403000142d02c10a48000c02d481262914010b9615132 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 234178911 1250 234177661 234177701
    0x11060f1303050a0c080403060905060907060f03150302041802010f03020a05090409031701060e0f011d040908041206050105040c05120f0c130e011e0b0702010c0f12020f0c04 76
    0x1c0e070101c50a40c401d030351100401541038942c1c0701140d441d100520040d03208940000e020400e40c603005040420081c88200d0b19000444108400d0703422196a008442113032400040ca108040e1554841201d6900060f40203441c000b28a802e007035011104943c1139000b62201c52500c82c1210040b000d85c8034001d400000210103008600007418035421000307002d80303c1d05100f007442004c0b10842400795002d0f400390300003a050603129442030420350905e940d0755030301707180240034268640310079000c1400000c0c075039001c1c81d82e030710030003003409022800e64000c1e1000b068001c2171481603040c12030141c1000e002d164400d81c070b814581d03203005014004507200306500c7c0f40b200090b0350b40d5543c250124000180710f076000a1040005d00e62034401c40684002411030014101e600f54102001e032460401030000410101110344014480d403581d43c01620074031542480e011030311042030b107014a002040c030040140207052014804200e25000315210007038112100480c1d45141030031003040266088114040041c40801c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 234180161 1250 234178911 234178913
    0xe07061b0f060207020607050d0306090501082a010e060a030c080a060806060d080903010f0629190e0607060504031103090a12060902090c030f011e050112140711060f13 74
    0x43d4000d4890705000030a140d041c10707626200c042c00c148080e00d6000009a84231414000d8041c0c038402c00e405005228000c1c0340b0b003240003a04070040c103030f0032130350000814250440301c0310b13603210314100b48070401c001e80900d03140d4007281c00280113000301c02c00710070110304604005043d0b10300d28456102100e410314010602605c4540501951380118070003518a21000c0059488544003405401d10210030300d0400944540742907103980181124030800d86011b01202d22070300103102020150340442c008044000b5442c018142d0560703800c140d4940b00340e080701c0040b45880c01d00440f9446144184c6c029280c071005802d2141815450344504050b03203610001c890390a0002034041d54404048a10901002903090825000a401c08204440c2500c0d502000410001240b0743c004219004242888440da80b060540700341c1640c80300c060040c00c0c10001c1d14000807a8a040581101c1110321503602c0540003401c0200c4014100d8036951406074a0780329550105c2d9003c980364545900c20707103089000e40c10710009 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 234181411 1250 234180161 234180173
    0xf0503090c0a0807180c052b050a02191403011412070b03161805060304150f0b031506060906030c19050a2a02090c04090e07061b0f 58
    0x586040c81910804080074455215071848001400098005008a038039000300700c241c106054100c245428144035694400c2134001042d1903c0c1b9800011800c0400c0c2400e040703450071650384031800d100074140f000340000e104a0754018524022903512041182e01c40322410781e49a200c05d0383c011071442c009c0004000d403072000c4580035403503100100b486844c5586000481c0c90305402c0e4106a40c1c42d00004240700d034403a44511090040641420510901100d443c075004070b8056078424940175010000016003040b100c0c0d0103040b954845120b00700000c02c0d0380c090001c000d00401000c2402441441d544200b030b20100110b440c0f0400001309050315010881050060741d0300042c1c00002008414403104503425001c03a0725040c01203043c0e490a8941200050003420031542201104651b900050b004500e105212022010241c050381d4000310360701c42960805007449641d01202c02e8510306212821450340c04101c40327045801e1541d814001f59078481c1503c01c0c8030540c0c0f07002484d1802a100130341c00105 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 234182661 1250 234181411 234181417
    0x150f01060f0c020a0b090406051926060105040f020702030f011a0303071509030302190203031e010e041211070b04030b0f06010807030b040612060f0e010c0e120f070b0c0705040b010f05 81
    0x183c041c0010442276624408a00e0b41800550000ca000080d183c0070311040e01100c005281c45c03c0000311800d58900000c4082d030f02c5a0040c02924040d0743c0310104041c4080d100e40407900c540b40d002d0b00711800000b07820b41c00c50003400050300e82c2c0f03103980c02c07060011070310300e4000b082d1a00d01d500141c00c0c880071910303588003e00502e2200422818942c003840000800300c03d004901082c814075401075640ca140030098880d1006524910300d07034102c0c0f0f030700061158151184000d540700d5840181c0c0003410318544000c2c1c440040c1540b00f03452502c118500421448c801c4009041203a1103039260442546400302d40c4204410116507050024490000150165100750010f69010101400007c0c12a854400046c00316000301801d996054a914070740181c03c0da0b038400c5011440c124402000f00d0001a40001d1030344009091451140030704c100c80b055001c0c814070042e0408205002102c1d24555a00201362158004010300c43c102e014081d00004c6504090282d0504000140d40380002c0c1244007009440700c0e0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 234183911 1250 234182661 234182677
    0x50903151801050423120403030c060b1002030403030806061206150c0303071110050c090d080f0c0c0901080c060a0f110d0e0301240e040203150f01060f0c020a0b 71
    0x6009640001900e5000c0c450305020758000d030100d5039900240c0d40d000d4441d017044164210907600c070661a211000c650429503003035a074180f41c640c0d0f17421014240440508001407001d81e04c280070303500d29030006070004000e00440c0e1103500c2e264080d0b81c0309400c00c4803a0040c031031508200202c02c03002a20303515005c01503000004204442c00e0404112144d9146581c00440300000800c0d140009500410802c21218943c1c6031801d800b40b007149806003034000350b401400400d6015641c10808041080304070000d0751a03903100c4207103050715144000308042c0c1e512070170150303e40250603110000c04d01c0c40b0045008100340304e0280810b840c055115900301c541d00705004d1041c0802c10003030300c4040130400034029000301191540d24240c407004040109400c6602d64444007820504440a105001e016901100115550040c3c000a20b64407400030030f06109841c03c40c1d114800c494400c0008035031060000d10705903062583c4a50f100c04515509840686040c0b001943c003603259601080040e11560040440d4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 234185161 1250 234183911 234183931
    0x3030901031e020307020a0c0806070e060904020f0705250b041e030506070807020d0905010206010b0702120607120c0305060916090b04170f0c150c010b0901120303050705090315 78
    0x200002c000501c201c0c0c00507200c450040e003040d1550307410312000b0400340025000c0103004d07240e00d007071070407010f80a10781d02c015060296074049024500d81d52075905441c041040002c4242e0307500300e10701d8040c0c0c07101950440c00b0388400c0c1042180c0c8605613070010790025540d81502c02032615040100c40303d0700c50302424840d0442d01c14007038084001007003030140502815054036001181d00300b1500c040d041400e9007901504005600500700403076030340000d29604481da0003100c650794003038070f0002c21000070840030700211070f10440d403c1c004880d91204d038240c001a0f4200c4204210082a20211309844013a901d2a501c049514003007030740c508051404c510036050a0034525111680d9454030201500070340d0001003c40000f007601a1400d07000d22070418018030740000303440d11408500c0064801507034520b0022000c40c01040400b030203042540401c041400c028030460803581e4822035500c07404401a401c0300040c1c2802d020485450041c0d00b920707592407004010b0035003041d0031000b009510740003e0010250b = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 234186411 1250 234185161 234185201
    0x8010c14162405070807022404060212070809160302150d0b1003020d0b150f030901020f0d0902010e03070b180102150a090b10120308090a02040c0807021006050303090103 75
    0x190400705000c002d9a1100080c0800c2518101102420b0f01c60010094001c0d500415608409540624101070009031100e2070a031f807a40703036070815600a00410802100f02c100c0c080c1401000b50300100d04034840c00310306003103c1b00742049a11121020701188002504121202801c0c00c0700d0000034050100318048850000b036202a0303c00184108140703603100c1c0c0100c0d41c0050a40c546110900030030340b201c130003560041e100070803184c1420b040f0710071590361141881c408000310f24800402c1d0101d6899104841e2034130f0301c0d0405080c9a80c010202018124007081c01c0031003078001750030041034060445010120f1242003201c50644100302c40d20000392581140190030200d080c404103a00020300a0404001c0050709139200d11f41006c0c800300140030218520280c0d1800c2111300365040381e403100d0340d901d46000c0d4100c3d02d0341d8120500d00030750000000c1d4020300305900d00c1c10050380111000d00c10030b8290300301ca481d40b8411500302c0843d000c5000301c607015081000112025402900030380712084c280b0442020b = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 234187661 1250 234186411 234186443
    0x9020c010f050103230f0a02060901050c0106031a18060606090f1507051e100c1106071710031e0215030c0703020705090601020d1d061308010c1416 65
    0x104541d0700360030171104c0c101d4400040034108044803000300004045402848005002001c242e074030409102d000341b00d5080000c9025050340f0440548052000c10002480000d0320ba1900c0f102200f118103040d0461140600003642800702545800c2050407040042c017006d032103000c00c2c00f0319175200e410501c0d001400c45680101903141d01a8580d000010382d5141500e65010345410f0b401c2140d0b1141010b0041c0e02d01c0c00c1300202010100d48030b150390080c00740c00100d00c0c600000030b44900c8a00701003e440c90007120308102001e41c000100601c3c2c031109002950740ca50310f60452890700f007030398040038081c20401d4450f00e001900c1488221a8a0300080004143c40380342c0c084040c41e90b01c22540685205404602c0d9010550100701c2035000e4401107403c61018a4643c000139612100804020f080080900d81c5a1070710b10078000d200ca202e400940955910003081c08181c1c1d000c59541726800c0d2070762074080402441b0344140400d100002124410078500b9140319641d001e00c02a03400160303018032921003005 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 234188911 1250 234187661 234187691
    0x15010806010c170f0d0b01110d1b060c02033a051b04230d030e0f0a0810020901020601080a0c270207031d0103110d11070b040501050108100c0909020c01 67
    0x12615a4100750103031703591050071085400b91080d03d200703a03052000c0100c400c0f10139803011809485500d05850024012015807240c801015010b04000c0c20203494064040103040e03001c802000120046a04105901460f1022041ca9a460011000c0d1801c44c4041b8880c400049e0b080150004502101c0d61544807245110050303e510560008151081c081c0000c03e42c2d0341540070300401440121b4107003d65a581d900c020b4001c00c94100910b115045c90300c00f2100c16610368a0803405410000201c501c4d680c0919010002503004440203805441100000a001c100c0000c1900a01361700043c2c000b5200d1800b44004030000e50029a4218104000311401c074079181c910243c40c405000e03a41c1c2d42203500310704401c3d800c5211f04c4480329040605012004081c105098221442c0103080000040c074019030301410300c170500038003c0040c4030030410000c0c4402c9c050150065410390b9050019198901080c801c60030880b4191041e801c045080410204810711340c40d8081c190401c3c21800200e04885030902030 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 234190161 1250 234188911 234188917
    0xf031d061003051b0f0f0102010e0706091415160512161101050c0703020909120c101b120c050408010e07061e050306040c05130e070815010806010c17 66
    0x40d4500392000d40810912008000184c1000e0f6404510001c070b20101c004150135030030000c0c1d0070f40507014485c0f40c050310307910035400034403121041d4080e18211911180010800b036114031a041407284c0019a07200703245080c032501120400007c11481c60064040d00c10b00c5c81181441040e121801030b040d1042c003028036240102032058094000d030140540303030b207801c510a6416050480c10080c050002d01880080040d604050f01d80481d041c80b944d0f0f845018440c075006440103440301c0c4c0600805c0c0220240390004440300c20a441200c14000c4402c618401c020404275600e8400018840000403110300c2e000b40d01180c1c5525441c03928130700d0144c451750306500356a4680800505544001e004020299000c1d40400801e1003650f00800030501d0030074005c019000c060201f51249036502111f4880c01e0086044643e40b01210165168007a5503091040c401c8804841003004a01c0080000340406006400800d080314161251420b6449140044075124a00342c4212100007003001d02111910031f42d005 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 234191411 1250 234190161 234190171
    0x10212151c030c0303060603060312031a0a1d0112080315030114040803040309060f050f09040603051608060a0504020d14120d3201050904050111070602040311100f031d06 75
    0x40d0380c080100b40c90000d044131b0340c9a00940801d0719081092000405409541030104001d140c041105805031050050000c000310001c1da101d290b83c900000c0781c600604181c052480c1203926809140c0c1d9074007003c00c03028120100248020000c0001896003c42c0704084030a002c4064000510030110804d075801e558400d0310150342035070f000300c00c0004040c2d00c0b40c3c0703a80280125141c404c90140c5a080090f0160060320008494464041002d01c095180d035408400110782107000c46521100002c1429002c014500524005015080001f044404c02c0e005041c06154081e00f4810a8803640d01c800304c2d0584504901e1100f40a440054407090b0002c4002d001d0704400f50400086640c10030168000000c02e0408507480700815200c0c900e4a10441180d01741103c7e02660b04118035070f80e905d41070380144004a1406480c05000c500f20080c40342e107030701030b0060b00e1040c0c00421802e1408000c010344079541500d8400020150b0166140061180c0c1041840007240d40814541b881d00c0101c05041c00402c8803 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 234192661 1250 234191411 234191417
    0x1a070203030402060c0c0306070504080c0a05031b0301090c0b0705100b01020a08030703020d0f06080c030c030d030504020607060212100b070b041101090e041511070b0103080a12051303020d02010212151c03 90
    0xe003448040014094dc2c02e403544210b035094042d80c64000030a4036900e6180706d104d444040001d0200c0130b5102900b080c1446a4040a5010144d84618501c0d1040d0090001556288142e0003414002c09907441040010ba505800416507044c496440013401ea100414070320415070203000c40e0040f060035010b0b14681d05004c82d008268541403181d0249040044040d0034031940c00703196200c580c2c1d00c0c0030421001c1405503181c0031955654500210f00c1d02d100e2a80f00030f01d060320000f83d5220183c40b0400150007869405030110203150b41ea500b0004a00424101130300080000e4041800a6400d04071450315040c1810300c44003007561003406e050550740480b0140c600c10032420707116111400c00d10508080340790700601141480300e16240d0f98040d07181400002d08040c3d00140d0f99001c6801150344a1000304c1d00c4c2024412803400d1449815030990390081240584100b4044039070740b40c010b000341c904403c40c0701c445140070b41c0d902c401c0002d08001220160b801c800315140c40c00030001003111803c004c6020752 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 234193911 1250 234192661 234192667
    0x12061c080d0f0219081515030c21060f06030403050a180f0902031905271204060201200307120911040203040b1b040f06050a0908191a070203030402060c0c03060705 72
    0x2041c0504145001401c6e940c101c0c100200505a80d6580e171000c1e4148135022072415102e580314100001a4401d42030800801c400c1001618110050641e03403510504094a00800502089083c1714841c04142c0700103001c5801405080032180c86203c094180c606110700e1040700e25500c0800e0550820341e030300f0080c032545c0c0000c00c0003c5a81041140d280e60340c0c001e20100014036140400317041c0300710058650260722404400d0540c942c041001064031300070314503440741d5840350340c2e01010b802020000341201d016204000190b030b10b5400302056070b200c2c100d0f40d15015250900c1d680d02c06c000b8014420b0403111404100d000c02070300c3d1260f1024503c686d00c01c14a218441c1030001d007496880b00c0c1e0280715003503000c08010a004071080746502c0402c40ea0582842c07511140d0803130041d1442d4015420405152145c44009031240040000390b840842c050720b400303100052041000c20751100700729042401350b0300030408180141000001840f88051503c156050b2110404c0042e041a2081da229800a6404 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 234195161 1250 234193911 234193957
    0x303060114160b0a0f110901140a1713050d1403011e0e0408040f08010606020d0e1804050d030b0a0302090402010f120501060302030106120b0a06110a08030c12061c080d0f02 76
    0x84c80750380c2c904100342c0c0c0e1185c2440020000240710131500d0040468924002c140d0040c0700b8066100c44560b070744194081e821914114145903303112820000b5030b40ca10552800c01c890714003958200d00304080ca61215441e40e803c0070000c2020000154001c0420803222a001800152403980540118802c04e034003691985807200c1107001070030580110400d80d25102040018540020304802c500000b030600c2810551400c0004038806407070701c100d074a244c0e18007080000300040414004108051600e04002014000c010f1100c18103860000940280c15000840c0142d8000c0c2d0883c1c1454460342b901404450515504e4019a6802c0e401940469004001441007582200445512490400b0208415403000001031038182c2c0c240700b04403c0c40044180c1c20403014050082c107180e240c120041d19981c1c01c00c800442526072240d41042440360401c2c022441034900000f0360582c180b01d800025500e0301007511019095404100f0344c8a0150327844264444000c910300240560071060550703405403041e0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 234196411 1250 234195161 234195191
    0xc0f0f030e01020601080a241406030d030e0705090604020906160201081303120506120a050a020f03120f0d0f0507020a020a15050d090206070204060e16020303060114160b0a 76
    0x607140341415500410014046c10f8800186c159000341c010301031880c001441441c03004024509001c16035403606010139815a20284c081c5140262070550480d600443d40440450031034803107010103040d5412070303402000f5070304d41a03003510f4020100810051034404140c000440641c048441020b08440052501007075682000071030354040710048001c041d000b01550000c0c2004da44186481149559101048103a01d44901035030842004c00701700d540036002d908010341d03220302c400d000700d05c00d62003c0092003260401090381071907400c01040c15402c1440880790711210760800846841c07036903a9400c850305a03003030500540303004078042d4000d4017003a00a0300600200c0c0981c0c1d0490345042d107008260100c0e05501404540b0043d508070000504450207200040701d920840038065485400e041012940310300f500c0d9041c2c001d03030604031300b400c4c3e0f4040c0d118140d0700e070f000841d8420301081e14103120902c0b1030300700c0d40184025040d0181e4000b2110072556608841d000030b031400c4405a81d100004d034071006c4 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 234197661 1250 234196411 234196427
    0x504050f1518131a07120501080102040807180e0d090302010305070e03060114040917130f06020d0507140703060b040605030c1020030703120b0f011e0c0f0f03 70
    0x4030540d4404103100708448004298180a003450f0703507404a0111810030310000d00414000f24882540b001c8050801480c001c1041598004000140780b914000041d4154144222411030b103001020740b030761034901244014080c100e0340c0301d0302d2247d49485d050700c20900140a1070049640c2519642c040c43e040d4000141120700042072001405054039000e4255034001550a04640c0301e06401c1071a00208070202d0098131b0180030082208006541503a00c10407048090284541004242040599110f20100c50101c40d0700c5468056040310210f100d50b14030600c028090035005d510000050503103003001c0351400b0501d038010340740300c1e07920b101d60364203480c040c044c20b001400114014078020010100191200b541e0760122000e025080320200200055000d0589401011000f500c4d1a40c1d400e080c054041e19900d004204480d01d0314807c010a49440084001000030603910203803074081a040d80e0b0401c0010550349000d001c030f5030120400282a41e080462060301c2415000b680705080c2c540034001741 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 234198911 1250 234197661 234197701
    0x60914070314010e090109020901031406160504180902090a0614040b0303030a050a09050a050a17040b07060e0c0d1a06010504030f08180907021b10020d0c06060504050f 74
    0x9410b100c00c507038964032904009410359141d4000d0344200e440b240710312401444140381c025000302c10080004103102c02d0100e101d03645210503041e9151079984860344232506140c8150304010030000c2c0000d002c08800c00503070080d2041c103100d002402d58610380005040040454280300a0790700d9440034062984032110324003901000b9030302804a0302c80c0c000041d4503800006d0240b50265030b03440c0040c0e880400c0e42c000081d0703c2e802009a4884081d541043d0740c55500f00302041d5200d91304402d40e58040072140342140c007112410aa03040c1010071a58600014240b80007817000c080c030400611402d42d41e00e01c124200400c3c4100c4851500c460003c1c031030505d10b8001008681409814030082001c940d1a17074220307040c681c1c40424a41e84c0c00016081038270182d00720603603682010400c0d00b0040160307000502c5207019550341601410750110081080550b4802501207c0142c002c7c201c4960000e00800c03440840b2440b40f0700200345240c5400100c5c046a42c07c031100b0221108603010302a10780000d020703580f0b8003 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 234200161 1250 234198911 234198917
    0x8060f040b041b080f0c100f03150f0e0708090d1403070207080f0705031e0d111c05092e1815050a080702060f0c09040902040e011a01051207030209030f0106091407 72
    0x310f080003e02501054000c501308e4149501c5181c51004400004c04010280200c44020080799880780c1216080c88001c40d24800407460040210f403110364005040d41c410103450383c1d01d50b1040c08402007900c054001030641c406510581a010030000e4003809080d8080d81400010007102c1c1c03401040502c3c003001c0000346d4203260071940d80c0300d0008501003128003602420381042d0f040c400b094199180f0782001c102512a08182021081c080c16a000000b442050011110032880d0040c01102030a0042d0001d807401d02070321005001d4400038080d00c04041c54007a054026882903a494440a1911000d00300c45070000c0c01c00510100101e0304050750316001030701807004003c039107010740750a0000310003d00300100d40f9001141c80002d41e66a50449800b50380d01a006004462180ea901c0d40a40184004005040d1207910000e500e940b040041e289218105000c10100b40c4406070250025800740340066094080d0748641c2001141c240102c10040103a2000003030007203949102c00c4000f8602414040c10 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 234201411 1250 234200161 234200179
    0x70501080405210c0d03050604050609100303030c0201020c0124170a030507080f0a0c11040e030f031510050a02070501081302040e0120030105090108060f040b041b080f0c 75
    0xb0500004542100c2010030f6080d04031100071209203c414010100600c1035441811105410954141c00003405100f0942c3c0a00031900d41b6410401c010700d04455400240511050030004070344640c008040340070b61800018a007039800288242941c010110700c041d012388859500744400c9002800300c0c0101b204500015003000c0c44d072019911804950030141c2080310108a060074420050110780c020100f5003072070703680d42580714806007000c1f40070038098418145001d2401e603a400c01c1e0050748030824024001e545044940c070209041c640000e0305001d06070406440d04c031410b031075035440030b0710500d45900c1e015166100f000c070092401900d42c10480c10003080074103005090b02202c03441c4a140c0d82c1181e0101d0a51064a1640c3c01800640007010012001d051030b0305254281030021030503182c00b5203000c00301d0781e00c03180c07019034030701041e207000b50007850300c0b000200882c4482ea200b03034000d840f81340f900091041c14101c20107088134581048010390001d40c082050802c0403c01852805010b80340c00d40 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 234202661 1250 234201411 234201413
    0xc1501080a080c1204061806050322060b0402120415060501050f0307030b0306100f05030a0b060907050c1b090906070f030f0207080403050106050901090615050f071505090705010804 80
    0x38071101c00400c000c0000d10007140c212100c15083c8a01c0181d04c00704c00c06552600d0b40d0b0381c0c0042c503440048150b0a200c100c0c0d84004203440c0e100b501101d100300b1031f4454070107074400501017404400d01485400d481c13aa41d1800c140e0b0417035880340014030f650441041c07144854246030a1001d81005c007011130030031040c0740030310401840e600a41510240110b642400d0340f07030340c5e0f500b03816809000c03020703c13034be07403500400382008400c1060010340320645591001c014402074447c000d25980d41d1a02d54080d2085041400080c824501084441e0388100350740707442801c00e50075103000c524080045890195209500d10016000e05210b06813551000c51b2100500041c202080d0107000f000c0c5030781c48503040603150b01050344184450340407070b081141d11221a44d9101d64908000303008007aa40107051103030b030003500001002c400d2030141c003043d990180d20440e462419107909aa07039900c01c01c40b1441c049010702041000c107000030140206204030131008100d40c0f410014203420b01e210707070b0080c1c0d043c402d0640a100c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 234203911 1250 234202661 234202663
    0x3010302190821130303180e060604030f170f03060f0303160303020a0c140604140303010b040e040c090207050604020a0b071505070507051b0f0a05060702090424020c150108 76
    0x2034510042c900f24144001c0c10341c01244082d00c1000701c100c1c00e001400c1000001c05500003400d21620010308002c1034401c8e1244040800a83c050b5455944400e003407100f4004691800c2a84103460b20078900350750783ca800d4401140254104421200503964080300b045400c0c00e0600b0200440350084025600d484001c0a20215440e40e08001900301070340860248041c81c010800034500c81d030002000703c5150008002142d41d42c10440b000ca50604000c10800c030807140c008241c0c1e050b28001446603044c40e051600441503104018429103038409000400244540380340b004160042c003460240000349418014400580e51356404202c807101d041040d1b01c00700c0d081600c3e6400e880349c00302000c240768035064011540c42c00340100c00b03410b50182c40c42c503002c6d190781c207000f0b070074204400c1e60200c41000c2100c4c10401c00e2261071042c81d4210030104500c0005280c40d400b1903600c00d02c10101c590490f07020349064601440003111f80344190f41d001032070344180030041104205042569102d4181c660400080b5 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 234205161 1250 234203911 234203923
    0x40314010b041404080a120209120105090d080402030703030c05010b041d0111181309060510030b06060f040306020307031122050405090a0f060207050102070c05100309050705060703021203040305030103021908 92
    0xf04090240807d21000d8035030101c41e0034420003041c1d546a884401714003802021b054901c00e04520505140e40c6c0d44a0140c42d4061103590006e014100903483c50710151100c64407030000315140c2d540c800541c0f045685078854081c405900c0f440500b2a20300170542d4908603000740c141100b03503c1c41800700311809604801004018903054500301502d04008035444040c0ca000000180041d05001c10015510002a11042200c3c0100780302000b5807101001e01c0b0710740c440c200000d80910030400c0f007407021a1140d00110341210103440d00182000095010031080d400101c407601d01421000010240d05042103a0040038201c212410040340c00d00701c02591307880d648520001c100040d1064204e040c0704042c1c0c1034500007900007000b90741d50b200030700d0031580c6a406400381610403212141d03401c0b00144a44031f80d0400907484001041404d0030316080040c07035085054200e046220b00e003810100404403c000d5801940710352070b4035407203505504c10040c03d041c4c0b992115411031030400c001c1003002e03000101 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 234206411 1250 234205161 234205177
    0x3080a0b031906090203030d02070b15090708072006090d05040f05120721030f0c0b0609060a03020a0f080c12060601080a060503010212011532040314010b04140408 72
    0x148902c100c2460080040d240920b4040d5040c0004900c802e170082184d00280061440360a81004039601c02c0380c080b1541c0256403401e44c0290380c10b0b0008418501035281c95410040b1810070080e6030840c81e40704108207401080c240c1141d0058410702668071802c10507107962140c00c1c1000e40c102402d00544010041e41c41c42168428982000f0200d61408107020400203002c000e04011511340b290483c05000910902c1c046001a00f01c0f56205000352107400c080f00840c1c2e001c08030519507100c0c0410408480005042191b001c41d1030100000140da40348031f0800144001c0900d240854a440001810140400803d5015456000100400000201e00142d104109091a180c2c40d201c02610000030010350b000b154240d03100148481d020840050b01a040f6841604805441048010212170326501c0300300519202c01e50503200c4450b040710241c8802800d0b00c20020908040e902e480c0e440c40e0034118403000c5803995540078400032504060140800910090041c44c25509041d610b4a03078602c02c4c451 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 234207661 1250 234206411 234206443
    0x20601050a0524090d0809101d042007030c0c0b21090c120f010b0105040b040e0903091017060607030e01030b0a03060501060504060905180c0d090605011203080a0b03 73
    0x41c2c100710809115094488158026190200c05c45a41c40c0c41001640030812641c07080d00c0410a0000c06032003010542d8070201d003800908000d1052406000c05401d550300162080482680031400c200c2c00040076151540c060f41d2401c0a03000780b401c010212181c107400108182c0c500f00860700203440322090000c06800c80c040f07240c3e1269030310041d170307420302c011400c51a61080d200c006003207030b0000001d2009002ca254078000c00c08003640b40c9c01921144254854030101c102c00303200410040071070311859540b100c442d0301601e103810031030000900201c501d01407050202d039501d05507000d021150ba0007140d21071415200c25181c29071135107000d03002000c05648035040603100c001011080e01d517000240015035010009120ba56104d02021b4483c0e0401d005560024035040c0e00080d181c0350040b4203d00703801701a6000c84680d00c1d99001e2103400c5c0e112203401d405a0791181031a43c001441c03442602d000b4070340b1840d003401903c3c1900c1d00900881000d080a600241003480320342300740e0703800704594400c0d101d861 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 234208911 1250 234207661 234207709
    0x1020c09040f050304090c17060a0b1e0309060103030206070806010206011202060d0e06090111131208040b070c090e0f071502070305060a1508030f0406030209060403150b01020601050a05 82
    0x86000d146402c1c440500409500001c02d0000b400380f20f03a045002c1c0d40c062504e5031802e0b500a1030000586042c112092a400711040c0c1080107030501d0b00006150048810460036014011070300343c1491039105079100c1200c0c0d40824010010725506120850f000411841e050303000d8140480000c0d581d5070180a84103294501e0a010811980c4801c11520010380a5805005a91169200740d0301c400c4202d91604641d400c0c841c0d52400ca403242c4044034000c28110f800e1500090415500c44d2a034411041c0450740c44100f0803002c20b1844403003001c1d006181c0300c1e954101000b4100016007054031003480700c450055000c0c1030702c1140140013060b0305d0281c03105504101c03210501c1d02c0080b0f240022a1384040c1250240c0c4061000a102c203822007001c010088040c03841140d51503900503a284030310007484506000500c02801014840c0c2c00410742100000c008030b04003130b100d4841034001e40000c8106220342da40c03055415034035601400348a0041038215403100c45d044c43c2c07901007649845005000c1001c80104 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 234210161 1250 234208911 234208913
    0x4110f0409020a0309120309031803050303150303071401090c0905041109060613030c05190b0a0c0f0c0b0d05060a05010504050931030201150f06030216050105270601030201020c0904 80
    0x203a2100ba100ca4006c1c28240c45411a040080c00815035440c00368000754541c400341059107108500c00d811030f90b1180055145540c0d44070b6911401c01c0004845d0b034540410000400855181c0c240800d0824801c0b00010380c2030250301e0700661a07500303680882e081d10705007420031000c20321640498a00500c1501c2068880d070f10380c40000d4035071086141c0030078035814009000c010311100400210555000b80c0d22f0381e0588821103441c11141f503041c450000103200810121100c180300d0704440464a120f03003001c01e2200c02d40e90328503030581800e40094201c040046210b10401c403541c061a6004001030ba01d034030f1401d0410b0002021442a40213540c060300a06000c07400b40c0100c04e0307524009100000411030190381103441826001200c4400780e00540c00c005000032115110b2030b1200c121907a5000c2880081e01d0f01c0c000360003a400c91a11242d180d1080b4400c45d0110760300b8043c0c140b0075030011013820004820110145829451145940940d9212500500060360005032008030f000701110500345650715 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 234211411 1250 234210161 234210167
    0x91202010e0907092303010e1b120c0301050a0c0305060a0f0b0703050c0607031d010203130201111f020316050c0a0b04140a03031e090209012d031104110f0409020a 72
    0x5a5200d1150b4200c02036181c50040a04070085c1512601207009011154400d0382a86c0d0b540400c096508000420550380705040c6080c044852118680d8400c2e01d00416078800020700b10780c030403030381c0881240d02c41d001400e020b42d00d442a198800c104440c0a001c490600c103440494403050300070840c9500001480d681454025820350789419001c0c02151124a041d20b4010003400f84590740740f0900e010703007501c940c4190040c001d4a104a41a1013041c1e0780c1032041d0011100880a015042120701a46120312004690b40303400c4000f00c442c240b40581c0d45c3c2080c8078104c03e184481d90060b4200b03c000d216141c0d00060108544540c1c41e0090900840b50321141801030b000108071342010040c1c401c143e036040400d501a041a4400d80d0100d50410102d0741039801e4500f50782c0c450000a62010a00d00144581c0e1205445900311060605c0d07000c01800300200191401006c903002a2016036040300c011071203241600a40b0503110564443d00d09283c41292050035034000c0d130280c200400d4002c02c1d00c0403007501c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 234212661 1250 234211411 234211427
    0x20c0106050d080c12040b030402010c080f1912150b0705010b0a181a0f1203041d061207050d0303020a05090a06030f05060a2105011506020706091202010e0907 70
    0x8000300100d804244900e0540500e030321040c018184d500410001e0b11032214040c09850445010640070351942c0e650358011201811884401c58541c1c00a1043c03801100750300c0e01900100c0d18200c00c4040c0e202d6101c1c3d02501661051818201035418108440d982500108440c000c0381c141f6442036440742110324000c1c0c0541807910f00c15030480841c0d0400100226420700c85003402a2010b01000300c81d080241d80024804030851041e00480102c40342101030805c20022008031080605a03418141c03650140560035900040380c80410884009014451030107909000c685422000140a206c0ca40400b2818600c901c020103000c1c0f686c01308140503054090021605054002440c1500054548034094004c050a000b040b00891401c00090a68104403402e4016288115000c1c2180000608441e0751072241d40c4040310340755215220900380c040210010409012581c004e4509141000d0004001c59504d03484105400644819000581d8101c3c0240504110680d0a84950b0740c81e002c003501d5501c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 234213911 1250 234212661 234212669
    0xb041e051005090702100605010207060f0503100315092a0314030403050115090b09090c04020903010b040501060206060102100510050d03110a030f02010e0a0c14010908010c050304030905061c020c0106 88
    0x5034404204031300d5404240e40c00d9008840c50200582038030303000120380d01c0030b003801810003207000302200841090180014651003820b02141180700c0340c0740d0791045845205903071848806901c400070310702000700d05040e030070b0b0043d000b001c491145481c00645050105603480058119144c40103074052009050040341c0c0650b401900034401065244007a4028107824442c3d036007010b141c59900c081920301202042c0c090540c2da8000c041c440d24640c1000020f40c042130929070305650b100b4009000b91214000d10b4002d0503280c01030215450501c0c00603041c0454803400b1000039117054100042800c40d8404141074a0042c0d480b001c0d601501e2a00f5594214902e007580d01c24400d00000204050b40210034800d151096802884544800900c01d9912003420070b000380740398181e800620007860b40c84403403485988145071a070030440d943d0f100c2a086500d002c2e20940010400810030080c160082021002410f007600c91078034140c0080c01082240320150916100241c00040c1032421f12000d420a201074 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 234215161 1250 234213911 234213919
    0x2090612040c03020f040c0801060f020703150209010305091f09080d0e0627070302060c192d080a0e040b1c06150f060f091a0703030b041e051005 64
    0x60500741466141502184802c91084555210180460505000c0d90b2405d402e251502c03032003a42041025a01001300c0f52032f00045100b418000008111040e103211a464003510740140d44182010004050717680c018507401141d8070000340030910080c684103c0540143c11140010f0660540c078080a12303120f6210404041420421180803a210200c0c21380d00809000002503032280ea4094080700b81417804024110715048a101080542050384c01800040032107000e88160003103039054624883e21002c02640e2504020b0817604001c400001150f0001d07070701030310035900d1615503518a00b05104411103c004c0104840c0d20440c2902c982d0400c0126201c01402541005c04040d0340c0036a034911010141c61f003908141084070340ea81e030f00c0300321410348007a903034403401003400c00c1c0040c7c0305c9940440b000700411a04d004000354817403400080150850300d80f21000d44c3c58030a402c0c010240c0f0360130602c5500c82c501d05440c1c80a062503c0c2d4600699200c01076000c075241d6159503500c401020700d40c0c000c0f604 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 234216411 1250 234215161 234215197
    0x311010909020c1b010f09270c050c010b0d0f200a12020a05041b050715060906030302011a0a05040f0f0c0206040317040203060c090d020301060834030303020906 71
    0x24403800402c1152181520b0416160010031413001110036500b40f6140d507000c0340700d081080c40702c0d411410316240301d8140440440305409400d40710360112245404040300140011400d4159420217018940e66204201c0740e00c44c00307c0007030310794602a8a000800804807044140401c43d04101ca0b6a50741003100c00821020303250783d0301e01c400703541c0c1c00d10801d080b40318601c00940454186030501c200009840003071505210304501c05070684540c0e011481c1a030b220310341e035109952603016030302460028021041c0c002c143c180c83e43c9006825101040f400003000801001d401c4820345604d84c04a01300d42045a000ca444508141c0340001405203400260165003003400302c0d001c0b240c00043c4c141c0960710030340c1c0d090320801c110a03010a25202c02d8600a506d9001070740410200040c1001800c800080100a1403202d00c2580c000b90840d801c9a100a206401004c10300705110442001030104036107440803040040f41510701d0140c4c50b41d03039001c02800d02d0b40c041150806500d40000f40c0d40784510180c05000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 234217661 1250 234216411 234216427
    0x190f03091523040501020405010e06070804120c09060303020c0a060f0e130f14060316030812040212030d090c050f0a0b0c1509010e0715080f063111070804031101090902 74
    0x17010b940540100e602158101c518450503080600440d81c85982120f411401d15041058406030055503100c1690010301e0070401090b00502441800000e41c42078000740b805c05116000e002689400d40d1040085c811444111000c9c1600f140d001c0c01e0400307089411199500c01c10140c01d000703201506041881a2030a0000d00010150328444c0b0b000344000c804031000c0412a4a000c203136140c0c0707400010b000000500c000d041402c0c0103c00c06400c0752000740640e07000000800c000b440c64004500d884001c60711680740c4030512603220720b02c0010300707810303580e50b2019065071300420030004a5102d001c180404c0090507400d01c80060200003549401400720020ba42840c806660281140a440c0c943c80e000c1c5505c00102c07030009024480314102c00e900c0d01803060703031450800990040d009007000d404c142e1101d9004903651308411070080c07450303281e0f10b45003800448a907541e04540c00080d040802c07800c10850600803c10100582e0200c80e444100c0030000c00404004a40c0007410340d100c00304007030000c81c001c0c1c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 234218911 1250 234217661 234217663
    0x51f120608010911090714030408040b12070f11030a080c090a03030c0309080d0e09060f090c1b060601080c1e07060b03060a0501050603060402090102010b06190f030915230405 77
    0x500c285024138000d1404001d0b5608110b2115000e69810000c1107000b24545180024500603590103402030002c2802d01e82c1d208018411036200c00710710004040700a0410a405800a039258502d00552400d682d01c2d0790300c00c59442c2d03070380b240345000d109200340207000900301409501141d00d80c0c9005450712b040d0702e0f079900c0c01a140307520b0140210085100504c0101d20b8050008824444d0190f80c0c1e9207881c1041720005014420320050855a00103510f051100c6450b1900500c5501900b43ea044d12035450303240207070040e0007010000d42d01820341c1080d0140103143c0c0e0700c10b5041e81c02c80d81a41409035180b000010000c0e10b01c4070341810000c09180800d444090042951104006207400d809407031080c1e41c1c0d00c1322101118003d000345940b000c000d0020800364286a0f020b0280080103000001d804401d0310000340c030a40095804000d8081910020041241d1080350806021014181402150650b5980b185501c44190544070001c0d80c80d41001580104401c00d4020b0b003c0000b07030741e41281402c3c2001 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 234220161 1250 234218911 234218921
    0x10e07150f0203090d0602160b0718050a0e0a2301150908010b030a080c031303080306040c020d0912080409020c07060201051006050409050c040506131806051f12060801 74
    0x103101040c5000090900203001104680301002e00034061421704c0000d80c0d42c200290030404508072201e03400200d000029030201710290044200f901d9420804c820014a03020510064129a01030b540d862403c20034070704018112a0014034040d8085034400c4080c008441d21201244001640840d0030300004140c40c00003000300311201141d40321052030341c9031080c0c24281c1d16080070554155000d88880e001082004014100030f9048200340e034903041c0581030040c4c0d00c880940040c2e60844000040c00340902d014030544012260078000340030051205c0300040c1500e0294480c40d810070b207008128904004201d422a1301408281c3d0b0210b4a40d0301c04400750b03030354070940e008402c090342c41c080214500c8111030f0705103c100c4030b5656402e844c00d0b00b041d009402401d00584421035400080c0001720300d650780d24000d0b007501034580d070758040720500e017040e0401740c945403400e00c810403031410500744181c0d00c84210b80d001c40c9504840894807106180b800b101c0060120050302c250324a44480410060019004 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 234221411 1250 234220161 234220199
    0x120f160203160b07061506020c090705130609080d0206011206050408120a0e0105011a0711030a080f03041b0e01030b07110f010b090c0424020307080f0901180609050d05010e07 77
    0xb0800c03105010111b00120801c1034054000503a20500281c0010b103010010198000c20506d0581e082c20b1820584201d403c246400540114968000c240040039042007010302d0900300e0f200806095161600c9407072444440d020140111752100300017814008200c007140e401d011041d0001c1c4003854440002001400300030355044403542000c0c00055400b8400502d0648100b2a01100f45844040d07510342000f0350039250102c0e05400b40380040e80124410401030420681c5040010340d0300c2c9418600620111598499061181d08000c401d0040c400000181da06403035000051003e5611140c805861b0504a83d410111520a10743d07004040401900081d11080c2d0a480d034145a884034628440c95000703a00405100800d1003401000001c3c1030702050002d0503d5005480c509a100d454001c0300d0350240804a521284c0026800d0705035078004550301c40c040f0160310040100307040582c014045492842007610802d1208101d40c140300081d0700070070400851b401210032050b6030b500030406488103921 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 234222661 1250 234221411 234221423
    0x80403050c0f060d090f050601240219030c081204050c0f010e030606010f1704060b01080903180621010906051801120807030309080a03050603120f160203160b07 71
    0x42107080382e080c01c0e8409004280300902140c1030814083d07842e030051081c07000036140001c0007060080421820720055000c1c3c280b0528043c5000602501a5401c42002494000310b500813000c514006680d9042c4804a070341c5032519400709540e600b41801c05029120381051032600da14140020400d00250f0740031281c0d01a11000440151007006403081040c50078200c1d016003000d40001c4856200e000060000102ca08040d540c25420844041c1040822101194441d030f44101a500e250380210110b0ba102c0d00ba203004500e8038607040c07105000c0161511280340070f44004580d9140d20490b06220800d41841021039a07003540e903401651001e080c480c418140070b800907203215000c20281c021001e058800f440c480e0803070740c010380c0d0b91100180c1c8204000d42c101990b40201c4e200041564009240c0c07a14555000300b03080c02c101d802c15046c000c003407c1c42042a0420070200e0300040801061706c503980d16188002c100c07034800d400420b00b4644200303400d510064150f4000324220701003001a282c0280616 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 234223911 1250 234222661 234222673
    0x902180621010801090c030807020a0b21130302030711130c0e100302070b010b0a0c060c0e0109080f100b030c0406180506061c0207030909050c0d0e01050f0610051608040305 76
    0x2800b4070b08840345d05401405040304600188042015003004000044c405003810070030507582e100f003001035009a841000c00c26541d01c0e80c250030880301c0c20300d203810000082c0b10a14810195034060f680b8414036500815100c5444544034140d1358020034006c801c20040401e102000c542c40000302045c0c51071244a120700c0c018400aa0b140380320303200750b45402d941300c0ea5860040c0d0800c565102c0300c1e0170544100d000c20880e14500c1002038403c0c010703090170240d25191054a003240f0f2001402102941d040060241d2141d800450400c80005803609199010f4800041e60066100031a0070710b001144c030290028200740c40003c200114252100f54450760034070421681c1c5a034820843d03148910141624025021559485400312a9000303003403c07481303800d0100c41c440e6107080c4542a500300b152803840c00e610120740030b0f1907002517020b0924941348441c020031582c6001040820a600e000c0c000034010b14103070030100e0215004204070740c46445c01071043c0740c1c00e01c52482c10b07140680c80b60000b101d03540145 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 234225161 1250 234223911 234223919
    0xb0709030618020d0201050f1606020309060f161b0b042303160308130614150a0e010e1806090d0909090201080103060b03030906071103060115020601090218062101 72
    0xb18070804a02d0b078020a003460408035900115500e0f00002e5420307000100800c2440741400c0101080e504440c42404050b88030f20703241c0e0509003004001481e20100c0b5900a00b080b00342c0d140c502402c10500e07a0707801c001d0058421fa503640600c10344100d100400d10b400320402d01040c071040e00702203c07440b401004506c104014014450b91680a80030780c24001103202e810020000340101c035680c0d0301c5400345100c2080c548c81a202d42050b030380e03c8207410003d40010340a004c1c140100c6030070100d00720407d94200403c98a000b09110240405100b082c116148610106d5004010310002c2c40c51107402000300d40341c5080555819440704580c40c100b001140204100194008260141c030307042d60380503103c5070704070380c60358841e50058044131a10f140d050200b040200a80da842c00b01800750036020301c23244480300e05c4080605141c400180c002c0300f00201d0413500040050390000e0004c0c10b5a400400c00750320f418480b654070090101c00f0484585c4110b011403960b1000c0301e0800700a540f41e00c0e100c2c212101303036a5 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 234226411 1250 234225161 234225191
    0x2090d080d270b100e160c021008190e032703030301140307060305190b0a0b0408060a0608280305040909030c06151202010e031908130e130209130b07090306 69
    0x1603c25500c80c0d080e4800068001041e400c02986d0b034500c2402c1401540406600103505400c200110a0101d8901400c0c89400743d0704003904100c207941d0803c10015240045040d41c2d0300d020700004002c0d88400c04050886000f10a600000404009401c0300e469584a50924241c440c900c0032481c0a031048002c0060ba01d880b03070040342d02820fa040790305140988014415006031008441d02070f003054001c0e82c0002c03105140e0b00140020030301740c0094a40307418410428002e0710f8140c0c1c0035590690010a84045025460000742d10b03125080000d0054200b45207020f68082c0140d600402d1a00c0c030340361806003815000044181d52901c6184c0070003c00703c050382c1c403a0307040348103004028406403818460b01c01540226040305450b10010216900020f4a00c0c03c0b81000c0c24003001110080c50103d42954001e10384c20090f0043c0c031080c02260503900c1c1c103a0304860804a2071030068440c0c88410302040c5410020001d08176001d03001034103900d8034036011030040e0465659120441e0740c0c5203040e2410301c19480c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 234227661 1250 234226411 234226441
    0x3040b09060f100303031d03030a0c08010b0906090910031e031206061b0804090f15090b01050f0d140114010f020c0603070f020f030309070e0a02090d080d270b 70
    0x40d000c3c1c0e21085032421901c04600420030581010000104152013910401c3c0400140d0302c9041e007000081a03000c40c0c6000145a580181c0c01180110418008503200d980c0e11001d495801c0fa081d00c141c807541d9681c145005400486a10241000f003c0002ea07094851710901e04502ca00d02030b8840e031070720015154480c02120300f1481502c00050394a02100c512007c0301440228003030045003074900b001c2e11040ac0c0001c6800301d107448800c0c030790740c0e80071481502c558004aa0003441101002c0103418000e80010f07082c0d118401c0c0860188400282c1200f002c00103501c1004207045c90025100741e0f40c3c54418649a0070350380c21060340450030385185910b10700d1001840c00200700d4054180c40c01e5440306801a200f11410003106410b600801d80504203034001040510300c84c600040050004a1401c0d18105c41e1180141c10040400c2c0100a407100a03110400104490341c0c1c024111603484810581042c010000044110015240c125141003d006e00780e50044443e401642d690815407100111041c15007 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 234228911 1250 234227661 234227671
    0x108040f080a0509040e0c15120c1e1809010b0a0207090c0203040e04030f0f17130503090604030b090c03030405090c030702070b0f1902070b040e091203040b09060f 72
    0x100380c4508640010495009401c103002c150800b1414001c1036000102603414040f010710b00e507405400400310070300d0a0344400e100700c0c880c903607924500301c07013075a5840d003102c00208070760011381d400900b00c01c0351440401103400c2008080703500c03030700d801443c0341680341001c1c0201c00c2882010441e0003c5a91040041190f0820b41c00780c00038040d40c1d29010025024002c08540c06c0c05500090000180d4100314841041c03049110b9554003001075034540c009007885541d6500c401c10080160141c0000b03404050045400031030700d103092161b2000c07a00c1c1c05031962107810b00007078020801040010410901c0c0d00e40b03500641703104003501c0d811030a1500303050790380c029441440d41c08854400441e0b030403c0254021600078001d4410769403525180d03000d040072548050306076141c00c100060350003425050140079481c01030841c4082e01c0420725051051215019600405106141c11404288148010040c1003680b9428045068891070982003504a07034030b0456088003580214400101d46220071200c0a104e0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 234230161 1250 234228911 234228923
    0xa06080a0318170304150801050f19150509011b02030d0809030f040b0706050604140c0a1806020f070603111206040b0d0c05030c0d050706030c02100e0d0e010804 71
    0x414401e440c121a4511070441400800c0401c840c0410034895092000d11540b002c000150354442c645025040381c44411401482008130b46001404241d03070302503442d100054101c4005a1040e01003814120a8400e5481060105c40c5d440b103000e003203504080601000300091f05c0f81c02010070308581c49595054200e01c000d5150300f102c0c407641000c90282e104641c00049203070841c0e0a001d0ba46a04041d03e40c0b1503084a408000b01003184001c22040340502680040c3c00d6074140030b00d9072075400716210a480074015010b8100017003031241d8075030f205110160252514020b0f0740e88259403120041e464071500084113411303000c0d1031400304801d4041d001d541e4080d181741c0b0143e03203414a40c51201c82c40300400752500760311035242c4451b01465070710b80304034490300e90042c210540306920346020140341883c00010386004000c2424450007140c0003041040403140f440c14041030707106011030120309003003501a034000081d20301500a01d480a0002d4002d06100b5913407501351407811031500540c1d0b031120496006240c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 234231411 1250 234230161 234230173
    0x1020d0c09150314070c0807060203040b0a06090212010b0d090c0308030601180605090d150f050f1e06040f060503060c03100e04020f1504050d0f05010f0516030b0f0d05010507080a0608 81
    0x10034032543e51b074000d0f40c3c0030b038860074244a5aa03031104140c0e4810340c2e050714504c03404401c1c49030a09a41c4160801442c480c14214504207074040d8440300170720148a080320160300841d1201d0a0a46504186440b81d030100c1110700c038035200d1030480c01036001641d61034001001c0b4808900f0300380c1e0b02c0043c0c138156080f41c1c44d00b9041071072050400604113103018040324103411070b0910a03548040703030013011040b003580c1c0c901080344c1c81c000a0a207034881004122242c40801201c0c2481070860958103d60040405d550100c2c60b00020890000a8880d56000d69018850041048121980c24020b14040d12860355411101565401507000c40901518041e50165210300044881c0c0390007078460100c01504012107082a81d05d50005d80000d44418055410150070046601086420300c503403103024010306000c00090514041da203181c6950dc0d0300403401d042e074480068800e55542c0480710b0b044003005240400000b0945441d5000e001e040e141100401c070000041044d03402c40e4010312041e50004001058 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 234232661 1250 234231411 234231421
    0x1524030a0b0702121b011a010c0605060303120106050d1a0918010609020406020d0908030301030c0506030907031b03030e15220b04060305061e090c0c01020d0c09150314 74
    0x40e103a4010b445001544074001c0703480103005441c0f02801644210803a05114520691a0b0381d094441744496841c0240341d43d00319035220b80e0002e44501c00941c010600003425565240420b00e1441242140c032030030304a000002441a5000c40240307204d0451440c180b2407404100c081e0610354450645596000c08660006512683d11072109400030b40305c1d10000c608182d40d81e1110041307a115030000b0005070030442c01602d8454000030104000c01c000c074011865507145031100c80a0030380c02e000e010b100d01c03000404038a00f201e04010760000345800602c0c10b0b110402800c06110201c16602c0100c020902c129005426072030090445034640503a00802c038608030100b0402d49804040a94800d030f8041401408212407074445e01600150415450008007801c1100c2040360b14041e03040e4038240a403140c0460400c0d6110b0548594010a681e1f048580b00c0c00c00c02d80d050301a001d2032012001c024034080c4480e0640342c2c800c0d9184219007002117921205401403e044060b10500d15202c00c03192401804a1 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 234233911 1250 234232661 234232673
    0x9080a12050307020a1b0f08060f1503030d02030a0203040b13030f12140906012111040c0504090f14220f030212030412020d0509012f1524030a 63
    0x558040100d03c1a42d050340c0c07095031440b034190140b00500d190644c078030b2020300041001d20940005850301072300600103891301084030002003200038150324100d000d0710044c0445031070070401d480e503404180000759100c2c544211848000d40086405807182102140450560022024015451a0107695600394040c41d05030640356054462003140801d0f50f40c0c04009040a203c0404038095400c90000d88000e500d062000c018081c6e111001302d4251051661080004093341800090941d0554022030700f0003102c1e0341a0b41c070703010f1503205840050a2000d0809121a540d10078400810360b0b40e4250101e03154203240c13204140a03485804c64004401c20300c540411421204404694801e00c12039242a40001c4111166041503800f1665070400003030207010700b50140101c140c40725803840d149050a5a0800081058540b45208100c4001d500c0c0c0d0840b00380407019419030800c0089044452002d500c0b03000581a01044401d01003140501c3c0e0941d00454400b440728109100c014010200e03c81e5035100d107 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 234235161 1250 234233911 234233917
    0x9070e130911120106060503010e040c0923010905061309050f250605030403050703080a2d0b191512060e01060e040e120c07050603010308030709080a1205 68
    0x540c0d4002410088851414101d001d90524588681001d03050620484207002900014000c0402c0c1641030020600256600c00e00341e0381100d11440c8911a1038459007401e45600311950402e1603101e0400425a0600c80c40b0614015803401280042a003a0b90b02d011034800c0b00c00654165034461000b1881c1442c2c1700180e0800040b07203000d0000e840f103801540d940140380c50b0304400d10038008581203681d4001c5010f2245100010100ca0610314507500d055900202507104245c0003d06014900c000305207204d049900075148411030290443c000040300000c040031a0340700d48080713509401c1020008240c2410401070035420070440075040103038200191601c622103100e100408200071200604804840c0f40641001010326400c0c40085504101c3c000300096881c00f21280924140801c0c4076085100141501c01034030321081d0141c54140e410b02450406942c0d9000c268010008000403003400380d000700840c09510b0a48407085801c3d525807005441d04031303031000942528101c44082e03031881c1c020740003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 234236411 1250 234235161 234235187
    0x3020304080304031a090303040807121b03030203101e12170f13080607080403030c0903020301060f0e1003050c011d040f0605041d0c0628180906050907 67
    0x15a030a1540707490103945140c202d5842540e01a40e41c031440c25a0142c01150303140c0011101000d1031452901d034896008501c103d81e001028000c4540c01349920303070300c1180c8920411005042c00b83d16101e250800401a40058540d90316070b10360858001040d1256042054000c0008894401c41d140707403d01440c180841054103580762130b048086070f909000340000030041122400c01c0350340c0fa092a03101d6090841d502350004052070f440340040c0000e064100f0070385688035a00d0715000c9030115450000325000b0880c1c1e03200179055800c01d41c000c80c1e591000a41101518030100742522960b541c90a6128460b4440c403001e0041c0e003001442030115446003010200c03c0e01c0c1806807000f280b03000c8c1c01180480f8115082200101c2c1e5410091040f882c19004015010b8044030b40001c01481d072006c810788840110384a0b0b807044800040079a000d035000158110400d810398807a0102c4009440081d0a07800180e0406007800d07010b0201290b040079600c60b80c410307900c0280125590341d6410358280c0f0640c00c440c80d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 234237661 1250 234236411 234236413
    0xc120c05090a060903050d05030f13060b0d06021e1e0904020403021003050703050c0903030a0809010e1507090501021b0904050709060909110a0e04031d0306250f0e010c0302 76
    0x20010307192078095501c00200025941c41c1d120b640740d03083c40c03814805005412400c11108105100307400d1030507980541c0002e05544241451505450310380b00500890f0b041d0742d00000e414041900b40811640940900100400d02d50b18003054109204002e21841c00d408403400c1001642201e00c030312140140c808100041c0006251580301d030001000a0308d0340c0111000070340c440041101c0d0f036030b042c081c040d0451741441100d070038008240c000070348900a00f40010108520b4800181d03c402e000d4000c800c69641500a5940c443c2c0c0300c01103003000c2007088500c040404c151910000351540300191082000401d444078480d0000d00c4420001e2240002c0c0082c0c5040c4155440401c003400e991042c48020b0000380d0000500248074500303145400035510700a44100340001e0100aa040900100c1d03030303c198546050380c0000002e084400050b0200c250080d014401c036810411059018480821a00c90722400d03ca0400015101110180504d4450f980040c0c81c512405800d0350148030b60050040c8280 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 234238911 1250 234237661 234237667
    0x309071a0a02100912030e1011040e090d05030114030c0307060513090e03090405061503012709050d121d0a060b180c0d0905010e0a02040608010c120c05 67
    0x900e840091001103110054140800103a40d00d181e80c041100e01d5030340341020428801020207459440954444808490905440d40307058850204288030410000390280b0041180341c4100d11740000941150103515013280d05107000c1140581d0004145e840182c142c0d8525141d03a00b40140d01502da411001d00c00c0d050f120b03403490505282d071b00340f000d400608480d039105c90b110850940a40968a0a644420007040c0381c4201c00742e02490100460340c0441c0d042e1004145611484046400203001242210000d00c2c04030011a60f1031544060513181e07000b48103241106c144da0781d410003c0f1034000c0f50091840c2d02c42d80c04c05983c85d000d01440013410200190000d003000e4134181c424100d000c240b0f0260703a180c002d81000b0040081511900d000c2070310079114040c080c00181707421140c1c100c02424550005102003040c2c0328a0307104e600543c90003503210000384490344a21841c84e507900350b00c1030102d2042d070600002068446051092100d08415550f58140d455061080000282464020340081000030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 234240161 1250 234238911 234238919
    0xc040f0308070804170105090d050c0601030b15060a08010302030706090b19020319230c060106120f02070f060501080c0d02011b050114010f0f14190315020706050a0b010212030907 79
    0x181001000085c00704008611850040c055604124400311072400b030003002e00c2000019040011114192a40000720070035985400501d13140e5020501c120f150310410000710b03c20724540c8160018101c91080e000c5031307040d0780c48500131b9070110480d0190b08403400d03080c0f201d82c1d03d210341c500c55206e900c030843c0166450801201075109245d400b0a401501051028041e4510f0801d01c1c0c401c2e503495101101d625040c07540f11001a0380f590818412035040110994000240154540c06441000128203007155500f01c01d14285c0c0c00203099610944001e807070180000f54016011900340000300004045c61406905030380152055000c204d50401c0c1c204100f0100f000050b42480380c4d110490b0410600807681d80340940e114040311303254002c0030103640400f40402c807010b01044d504907000740841e1707500f10008001002c949465200e40c409800c0c5000103070310b00c036030030b406a0091224901803c0244040d1307803050414000e0f03410b6285901d0040c0c7c41000300c0d0303040b451440c0246812035021f0050790030705a59 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 234241411 1250 234240161 234240179
    0xf010e012a12060f0f171c02030405040501030308190902010e0103020d020405030106030b0f0c0403020108040f1b1710060e0109180501020d0b0414060a1503020c0609070303080c040f0308070804 85
    0xc1138000e50100d5828190034000b11104100980042c20180034003020080b450168030b45800801c24a40d03d8004075140c0000b0043c003d10588000d0100504100301070340c0c0d64180148585019036512010502c4104401e001c10880d0080c00e80954040e1260ba10145030302004500179444510f548604d564284000b00b401c4e5405e02400380114041c410a21079824001d071400202c2c2c0d000307003000800e20010801040141d070040c1c44d40ba4000d802c64801d501400160510078100d90105402c280388407502c03500031401c0d1941e0104d4414480304942207800303080c1c070004000204c0d4024095581d2031034580004001c0d17020a0b810020303002400510803002258950390369400da03000044542129519003240101500b003903c20264001d4084d40c003c421403c142001c00c021031114003642c000f0454800d2030312007003400b1790112060940707104205d4565161aa005030385440d120301041340001d040b40040f8101500c00419a002da881010907040c2c03551441d5a141e0072540000c2088a070f042c01400002541d0f11 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 234242661 1250 234241411 234241421
    0x6080c0403150207290705070215030703060f06030e0606150c07030302150604050606030a05040507081506040c0503010f1203120606030b0907020f0d0e03070b0a020f010e012a12 78
    0x32014201588600135803601c4200440003074603102d04107006500d101c0140000c01200c603002400d0b418000d0795010680041a400b14030044c4603204008000140001c513589544544101c504030448091420307101c1d18110b0035500a40e060b101954021004030b000362070954020394581c40f000c0032840c42c01c20081c05035801c21000c0e0740140c001d0381150b140251600c6011044030341c400700858041081d40307003010019046000150402018036503400014040090401856000d007100c0812120709403051601c503614240f040b929140114144034606c401240100c2c10b40c0d050359030030380d51201180d051440c580c0759a07103581c1c02682000761061b0310b0044071304070b4822400903059079500854044911004d2020000002c1d08a004550001c0c00f054900100850304144000141c0703003481c2d1601e08200004d21b855900d80140038a507800041003200c9940025a56030b0030014034000344a8035008100030303401c07241070030443c040c02e072a528605e00140241d14150342c080042410100301030400036100400b121 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 234243911 1250 234242661 234242693
    0x15030627030906030606020c0924120d02011103070804080c03040f0b03010311100504050103150801020d0213170a03080a0e06010b1b0a080412020d061b14120106080c0403 75
    0xa50645018401d0030750500072200079001b140002c2440441c007034085403070410020b01c2041542c40c1031101030038400c040d10f0080075128008040e5141e5001c80c6050300c0d11170810002440240d0320342400e03075250381c1e070700c10070340340f2a0940e40c9806a5603510703a11118a1507001d80d02a400d580000c00004c01c4208405030604083c0c00c1c010111307a200d60641c580f6182c12105003162a200d5070f182c010f420f0700305501c8404c66042d5142881c02090520442c00d1a8010f100e164005050035400814a0356041c1d1b0280c0c040e14100042c01c0c00f440220756501d500036103d041e1418582180c0c0c01200200340424020110300b0341140e07004c0400115110b40c13413031150511a0a03000030141c10000150a484585400d0702c240d0030350552405001207070055502c80e0218401c0d0701c60302100d0805c0d00491030a560b1401031003081140c005405000301e207202c41003c441c010107503621710302044800c2c094264800040c0142c80c0003506038081546182d0030201c041d04c03103910080c01103000e1002003102100141d00303501d8459420f = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 234245161 1250 234243911 234243917
    0x1410020d09031215090b011701030f1110022805060f010f1a0304060906090206160c0603060501081302041d0313050d150b0102010605060712080702011503062703 71
    0x3400051600410034880107400604990074507503072820510740e580c6840c040303c07001e50001801c2c1b610100180c400e680d6151880408a50080000050100321502c8482d814415082c1500c0b5a00c46410072800044482c5034a00691154010844940c0700c02191000c014104c000110a03519aa551501c0c020084910f8204c0098880041102c01808101d8002900300396080d1160900915403107417090000410150209884202c1d8005102c2c084c1c3c080c0c00d500b900680000c0c1d440381c5907005030b8000d40c2010412501400003190020740503120340300f001c0c203170740c81617490070a26100d004038142c0c01e540e030040599100340e8820754600309403803a46d0300240f8110644040c5440b5078220510f60164172841d4030080c0642c440a000000140051180c0039007020010000180400760800407401480140c00694202c100068802c2c14031801c04410000380d0661360b80c45445a0310b0700d504a00780d415101c0f81c42101c000710202070001903015004a01c50140c0004910b01c40021001101c062136101d1f4001c1d004 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 234246411 1250 234245161 234245171
    0xa06180b030f07060e22060b0a1b0b060402030a060e0703090308060a030203060105060a051213110a060e040c030b04050f061009030506010e06061e031e01030507031410020d 76
    0x2060400344601e00c010501400a8540d80d403130110007034446100a0501441980003c0451280e0841c3d512800942403000d4401c10000761070f4070700142c01e540080c0c1a100801d21043d001d0414241070080102080e900c0300e00c0601c56120041408080d400140c180718205440340400300d600d42403078042c10b2003462503981c003040858090070081c01c80b880142c212800781060000510160b1000a20107044600903180580d644040810403a900c0c041d179181d414101e039500050001809581c1038a8280500401424815182c03100070000241c1d5a4071a200c04034503415040685458560312603a20207400c1e04010510072003883c001400c80ea030849507529840c03903103014015a403c0180c240c0d540c0a019007000740c2420305689815544c0c401c14412541a54075600000d14a0707112041912204403443e403409281c0907a1007062081600200e80d0081c2c0c5420040754410840a4203401c0c9040300c1c0c0020203040c840d400c640b07904010303648845c4040181e11601440340132812103440200541a810107000403 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 234247661 1250 234246411 234246431
    0x1e150507030f150302060405060901050c010923061006030b0a080a0605091e03030604020a0e0306040f050f01230a14010905100b0304021828060f05060a08040b0a0618 73
    0x2202c10707000e94900d46258a20f014001602c07000200c509441d0110707003094035540325100407202e80c8076000d03415a03654204110a000c0000e0745030144c074071307480d00300803003589050010f0304070380c2c41c03008480f0301c3c0c0c060309140e004102c5140264880300317070240d010f013080903429190300006203004250102261810b90714810010b40d50700134021401d190389581c40d001d00071701c50150407555a003c06000d113842181c0c001580507807540691003018a002c005400d45010b46064100400b13a01603401040e00c0c18000c03000d00104010040c4211301c20141c815494001c00b034a01c02d040c00c07510301d0080001c0005955010100161741100c61444d000701801038002c610f611b4042004549440e0030350211104040900c140001607484032604000e96080041d00071460740d40380503001c20700000c011a4001380e1007a801817406c0341107a8201c1c00a50740043d000d45c515039990000d000491140ca074801d030000e82003102007000548082e58840e0007034102a0042120b940303401e050800e5250039100d081e0713003c0c0d65881540c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 234248911 1250 234247661 234247691
    0x60b040b031e011203051602040501080c03070f060c20090c070c14010e04020a03110c03090f060304050307080a020c0310020d0c0804021f14030a05010e09010203041e15050703 77
    0x207030002c0c102070321200554502001243d0121000318000e082c00008500140855000303503091141d1038000f0700601007541d40d004400c0d00c1d03215201500d40280031345c0402143d001d12181d014821121681d95150980d8516201c016004901030440386080c2c0b0380f50390050141c1d6951103018051311209002c070356038402c5851303d64a040096800b441c02c584100c00d0000480c2c2e00044406e51100b810780c0c016a1390b1181110840061408030308028803104042100c01c14440004041c152604098036801802c04440f400c10825000031200141a5803040010313800190420000d410302c06401c0c0100ca00c5a420400000d09004c18400c0044a055011848198001740da00500d090000c850070400000e04013070f008242460754080c182080c3d26101000c10032414842d2248244030300f00007501d90b84a0815801e000c010f4034080c4920035081c9070001c041114500c040c402c82e4015540701d00c50340c44c50180901a840380203a080f5050321400c0c1d010f0448080558030707003d060b11070400b030758000034401c0300c5540f14 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 234250161 1250 234248911 234248941
    0x60c020c090a1a0d03020c2e090e070c0c0e07080a0c0804020d02010e0d020901080106030b01060f0c0b070c050604052b021b0a030c0603050a0c031404030e04060b040b03 74
    0xb4016141410303440510b0072031444030110b0403801a201001000540c0c1000ea2800c184901c000750010000000c0c40800e942c4244248160081c010800b8000003220504443d0204036010300780360b80c0080c0b800b1501d41409001c51ba031405214800442c043c40c1d139281003103074881c42280d0300c0000c90203140404c4218030a1380314607100031005040a000900342a00801c1060b4042c00009040c0103a0010103001a41e88000203104942e00500d036000d10760312407403044d0181c64213200444018200b070002080c814016800c00700c1403900d5985080d0b0055583d01e980c1c15151002c0e084505011034036a1200c00705a050106502c601c2c0150024080c0071400301180c600c0c007040008081c40e0092015800d9420359011820200b4480c002100c51801e04400000418072036166100a01180d1000000a038254140d000700e4414074102c901041100800441034056803111761032070f101c01c0c843e40c000030000307801914100e0004102070000148191030302c0105030749910640106070250340210800402da0350090b94 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 234251411 1250 234250161 234250171
    0x20a08071e052719020a050405120102030606031303090512010209010f02070810240303110c04050c04050913081813020c07180b04060303031d06091b030a060c020c09 73
    0x80d000354007010202540701d2105020180a50300700100461400f80c20b01c02828404c8080c40c404542d14228a04043d01590203407040e58001e842e08031048068210610035648984000340140c0c0c80e5982e02d41c03200d024042c2201040302840318018020445440700c202400300c907092100010380d40c2102000162011501d61000d034115030040342c0601010101042d41c0c04140805000400c204265030742040d8008640010311310000003201002041c103500220a0704c0040308042a291210746070001d0005942040f074500c4101041003000308161b09044100075444900e044c0b00f1410518195103025150b40440f483c2c4510000b84503011000345006410039600b9000014118507000601c03522a03240c06a07403045500c2401c407080c00780f01440843c0c10040c0302d41801041081943e443c0d190242c010240d510038241d20300c21015500000d0400042c809005450100050034000d5035042022140201d003039040d0307054041d6400c180d001580703038001c0300c2e02c7c6010b5401420380d03101d820041c031601c103c0040c9 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 234252661 1250 234251411 234251419
    0x2070510091b0b0906070501180605010e0c0403080912210d1811150c01020406030507090501030902090f0703020c190201020606011e0c020a0b16290112020a08071e05 73
    0x7000c0040b44201d0b000c440c0e862000780e0701203403540303407e080207801807510f402c266404001c0004840e082116582c0014180c030603c09000744544c60300b4052000d64025800020034080041003828080e150500b40d0010301c40800088500780400300144885400300d80350f0303030360865001081008032003100c0d001c1d07c20083c0c0c503052a9041240262542001101d105a03598011405154140e900c1074000c021078030a071540c0f00086d036596607200c000400409003101c50301c002488240011989620034050340302401c1c2c00a00740c224035250008840d50040e0f0240441040c95400c20410070210024021901c21204299612070000014000641843c8005050b01d041042c988117601070016540b0b0010410291450b2103000b8110f24800314602400a400c0310000920104003201a251414498091184601c8110000d0081e083c100348905035140480001300100d6401880842d81c014004041c50380010100100c0326601c00310b01e810410203401841c50503400181c681c0b141c010300503c2070000c1100761 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 234253911 1250 234252661 234252713
    0x41d031c29060c0c031b0f0d0b040b1504060f030c0e040803010312050714010911121b0a0f08070303080903041a0a091707080616050901120207051009 66
    0x802850300344a200390004502440c504400f0460301c40c410703001400f11204c07041e517481107a00c2045415200347c403402d46200c19400070f01703010150044e56680324049100645580d6a80c00c87c104005029450754014424100007988d2a8003a01000301185580e4004c00750541c10b100710041203941141d8807084005d414080040d0540c1d0880b4112600907005040d001c0304030508070703400e210f4410003070a008615410b500702c000040d406034603403078030500841000108038024003c1413a048040c0d05500c0c1c200f1482c42101c0c0003030503c13140701c070400140507248440c0c54007c03500700f00c4c00a4100c0f040943c8a10f8060042540085a4940145000c0000e43c01c01b86040c01640095419501c080d10110020801603003039400340c84800080c1010046510310420050311543c0d40d100c283c4100c2a061107907001081020710b511864840d65511551842c2c41e043c140360040d15408400200d901017941c5c200581000b02302c1c10705c520301c2504e02044000c1050b54881c1803401a03000021050000c0004132 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 234255161 1250 234253911 234253961
    0x7110f1512160504060f0903023a02060d0b0d02040f020309060705040e040204020a1814010f2604020a150e0a05030f10050a0e010203130204060602070b0702041d031c 73
    0x1ca01a10201c85d00d501c0c0c502244442c5800c03c4410010980c00250000e50121011203540d0403042143d152200c610110504541012180340c075000107140083d411003820030400701c222049402000d00084007501d920303d00717006036001c1801c460380c59056100f86030f804024000c1002c018801503800404503d00705003803e0400c60300090200d4080c1000f8031031540000d034013004138011a6107124401a070007001d00841d80e1024102050303844100142d00090300b254081c1d441600800b141c160501e54a07688604198112071302080030040500240d9220000c0400000c00080040caa410015403980e1119410700384d00c0180030580300030760003851194000d038400c0794130051300040300f440c40c00e49030300081440d46800c00c0300300040220380d0041015500010070041044040301d80d44150920980b4104480d50391400300300d864207101e0258a0500400b042070301d02520349500501407421914051028090f4001c0481d840c42d4001104036400b020f55280141a4600e60b1160000010210360036202190304 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 234256411 1250 234255161 234255167
    0xc010509070608010305101e0213180908030c0906071b051503070e0f0a08030414090c0c100536070f060f2001050c1903020f07110f151216 61
    0x8440c9544480c0b0342c2e6000f020080e23820600341c0c8240c080d0301e5031085690340c0c0d80488891681c202c074001d002d2190354160010800a03001c1c4078250445400140340f90840d16281d5000c0365503801030b03418582c410b1040c030160010a12510703040550038800349415180c140751905106903084212120814840148100409280c0180c0d0100c00c00030112800c10342441e80c0400200041e003241c00c0f120303c51201040108660b135074001004018402240c1e02e03a542da840241c130881d80d21070040c086500d500000c403800420140d030b4005a40001e001c070900b844041e2103141c2d007461101d10340504201c41c0c0301500071480146050000801401c00301c902c1e000000d0800c07401034880c56161140404010440c5030840c1c050b0181031b00d94503081002c030001d1000d41403101c030820840d0002c041031400c00c0c075040000316025000e442142d02840e4161820345c03c00c0d030641c40354034407207201c4903005410040903130034a2150703540d00340060b6906c0c0380d00d02100d8030344980f103038a00f82903038004002291009082c40303d200e1040e0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 234257661 1250 234256411 234256423
    0x5090f16020d1e090905070e121b0d06020d050a05040b09060601200304030c06020606120a0f0b060d020d030305070314060d1403040e0a09020f0f0d081e0c010509070608010305 77
    0x800e08080907000f80450700c111442e2010b075005c64600c91a080c24456082c0d1b1001c070402440e403048a840034a0794903046e916440d4601c240c042c0708100c0510100052506284415120240c0181001400c10004840ca00141c40040320b50284039503a4908000c100170884012980110b541c400404141c42e040001a01e208050034090781d400344a403090b48540c8004004440155a01c980d4510800340c0d120806503540c2000e0740d11520510f4400d01006241d440042d038841d003103401c017106400000c45a200e1040b01d10303020303240c650410717000018000541c58480b18035034030b18070a42c0c0c001002d1030f060314014111040e40d1480072680c0103102c10f002259455440c410803243e00551030844100e11200c00603d075101d1030f032000010f10013140404c4402e03009644140030441c000d0314083d244c04800300400000400f104896a0311001c03a80181011a00c1d83e40582103d001c00c05c00c2c2118440d5040385021716030081001405240c0d190010441d80c1c0e40148030160040c074490074189103a505642d10592104 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 234258911 1250 234257661 234257687
    0x9092a0306040b030f010b150310050d080d020c0a030e15031b09091006020d030e06131704090b0a09110708070534080c130b030705090f16020d 63
    0x60404000304929035074640c08014000f100404032162115503165940c041c0940f50121440b4400613135060059080d03c5041724800c034401001128164104410030242c4411242c00b915090070600c80c0030440500e034802445541c2411000304000c104c3c5c0e2400030100c010307c0303101a00442c0d5006a100c0d115440c481542c6d0440603002e42c000782504080d0406849008805043d58451415418400701003805030024095404039400d0341c410700315900040c0c0076a5100c5401e51071b9603103c14000340103044094040e0091902c2030291214032101d0840da0f02807900075412014856a40c2c50030341c403184c5444c1441e60014400148248100d84060010b0001c901030b130745000e00b048000080260410400f4854a030722000109504031040341242040302c2d1042e41c2c0180600742501c1d03008041205040000e800d108100014401c0460700780058105028001c02c510458140c800e103e004a055a141c036990b40c400d1504008038500d5142a90600781030045000850066400540d10703400782c00e0740040413003808 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 234260161 1250 234258911 234258991
    0x303111009150c14040e1f0e150904030903080c160b0913060e010605031806010303030c020610050306190e0a0f02030d050901050306040c0e040e0105070315050325030c0b0909 77
    0xa64458001100b80c080b51005280d02072007c0070040b40d12114007100c58041c00c0e207001070355160301c0d86200f0702c104a003003a00c0c06008140c85140c10000901100d000b8411001d4803c255610201a01310003250404a40c008007000c4401103070b42c0b411410705c0c000090841c101c6070020302c0300c0d524110740d01c1c50302c2c0b02c1070284d102001000400100b1720114508801c2da0b00744054220f80b081c2da50390030000d00420b6415400e000501455000c0350398081c8518900c0285e0f40000c001e0422503d499952031012104100060100354a032015190040c00a000410006000b4246100d810f042881010302b0038401d82d20326414032a0602880050340da009058942c8104242e400182e400720b03e900980f00c1400f0100c045070301a003001c800052401064102c02c3c000c0145880a11103841c603840010303c2c2c030219005082d0180d0201a0400e0449281107041d4100900c2d030820595803500d036110b9848010242e0002603a40c08002003107400c600741104a65800b64409102408428111000c05202090340c0ca5400344 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 234261411 1250 234260161 234260189
    0x6020d02012903030f03010902071505040203100c0224090d0f1b0f0203010504230a0f02092503060602070501050a02030901112401140d030503010303111009150c1404 73
    0x103d032020402c8039691403003158101c0e245d607500d01d1210080d5100e0030080740d400500d090b20303955010150103042d024590040103800310f20212202c250060019802c000210320500304600c0042c02d4002c032204a10a4201e0308074094500a00032510342400084220108016001207600c8190f201100054480e0080300911028440341061080d13440f0b039040c0a07504d03501c0c003403e1000304885070a030010305000b101c010850201724074109548036401c401d00680000310040100d00149482d8108650024001c0d08000018030165218203001003541812000b0036a80c0e9800d00209070100581d1005140034030300036140441551000303480740202d88109050211b0185501c0e840841404210342c00a500031107524401ca02c100c40c0400b81c1e02c284100b1181049c400c1e0400c050381840d00700c01c01b110350140c440600e140d20b56542265001c0c003801d484000303401001c21906410041e17009604425014102d9060491040c103452811150312141140c184000440902c07944618903040c1c8085601940c50400 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 234262661 1250 234261411 234261491
    0xf0801051e072102210610020304080d0503130f050a030306090b01091502102c071d0406090f08070b0f090601060302090105070c15120e0a060e012406020d0201 70
    0x80d009418030300081005d02074040b040320038080c1500e441000111640b100c03203444601c0c20707a184d21607801480a41c3d00035005055120703018400860300900c1442d10a9000c888544405400001c08581120f20380c02c050f5802d0245a03050042e20090140400d003000708202410000e0140019449501440e4555040740541b0500a001c02450680520014041e8001240400030040e400b20a03913082e55035400091045400d0005134441030703034030540d031079130082281860542c210b080041c8225480c94540c40c6410005400c43c50426000d8481c1142c4d54690000c0e241501d80114000c180300c0c3c0d94a4840100161040c00042c0c1f181100c90302e043c0165203140000c0100c03014420752034060000103418000040081d0031410700800e8509070390742c8030400b1800c5c500e280c080c0c139040440340c003166122076540c0010560b81c0e400b00300e0740c45007080000b400d03000c44800111014200030084440304035808040081d9a01400030854000d82403000300034290344900381144000705400c0d50b401c44184813a21903 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 234263911 1250 234262661 234262727
    0x901020a0c200405011502120910030e0307061a1305040320070806010e1e090307062d0f0f090c1403120403081306170a09020a0f0801051e07 62
    0x8a0002d0094414001980c40711032a555220440d08480010700c0f81c1c80e00c02c0c0748841d05034143c0e0401c0e01d004203c6240b540d000300c41107000c1c021500b00d41c800d40c04104505030010383c1c588154990344c5002c0d551030300084100410000090035031207860f481d0b14140f004020000c7e6004d03240c2c003c89554124007100f00008082034610341421600560420b100704800400c04400c2003c1c0d09108020416248414000000c041513140105640000b1594014013085000410a800240c80b900f11003009140219400e680321300c010204118140e011a55107005401702d4486000c1c80034207030700045080c0a5004aa580c0040ea0030040c42000403440264010748178540d030601468209000345160541c47d00d440e03040200072a0710035502c0c040b03560100c0c03000203211401540004a00c10401800d4585596180c840038007400c41f560089074411500c0307402103902e03400324240744c01901450b0000500e919004d10b1042c14081c1c11044015003103000c2c0200009168091000b850303461203040304249201c0310340114 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 234265161 1250 234263911 234263963
    0x82112090f0d02011409120703230a031a0a05130203060f03030309070602011a01140c0a06021b06010509010f05060f0d02180f0d110d050f010c080601080901020a0c 72
    0x9003401c0c0140400100342c2541504440381d095030006011004c0c0d00d680c00e5040ea21007106000318840d4106201d080042405124038600d000500109214445209403d030790150f80701c0f90b4001d000c6130761000b168440034010740c40100d0600041d109940c0da141088000b0340c0a1400c3c0309110071440d0000002642d81d03d070708085070f24010020341240d4582c200860350781d44407480350007070000640c41c2817808400302449002c1041e44040684540100100004002009900c0f0656480d254407582035101c00081c8244028200940b0003d80040d0240c9080b00303541c101031040e44400d10608210006000c01c1604e448007000f120b60403100695902c0342000307a043ca038040d000610203658404156540480452a105950090115211400c082c1e140040122480b50a44d002d0156940c1e03030311070311040c05c11117548003456005104607180041c040c5140b40c00e603010180c0c0c00313000a1951043c0700343c80d43c205074650741080403c00203508005c6030280044c2481419040500321003901000030040702000d11170 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 234266411 1250 234265161 234265183
    0x2c010b0108060d1a01091b020d20010b0907080a0f0905030901030504050a17070201110303091b01050c0105010906060e150306010c02040906091a0702071a03250908211209 75
    0x4038944c10369540c01c3c100d0040c81c5210b905685003111282170313685680701290b0548109a15115140030f154501e0080b40c60102c1c0d4520070115640c1d42810b050907a580c600e1040c864296556500802d00c0c11060940070b0728030b402036801c0161b003040c0035400002e4000c400d48410701020301c1c0028956031241041c078503002207140c014041101e04042c070041c0910190090038940c0c001e880c0c80c4e004081c0e5030074440d82e0348800c490305030f0980c1100c96074604040c0741800e403540903001450100c7c1002c1042050b5403c5030000e034040d607101c6075121000c10a440c0c11100918000300e08450000d1400411105d00c00a8880140380b5410004021944002c65039258404150107070002e90410034a9074501c0c0c5041005425407546040c010401d00094000780300080341c0054461000e0078a25904d03009001c0c0103141c002030080b00102058106003140440c003203400440d2400c0f155500001680303020b040c00e00381010955125120b0000c6a4101c516100086c11134045000d000c14010b01581c42c14017403401c0182d4518 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 234267661 1250 234266411 234266453
    0x271b050901060203070303140601050912070b0a0e120a050304030b1b0703030504021305010f0620030c070e100b0406050c011b03020a0813020d02060c0109062c010b0108060d 76
    0x2001046043d40040a00b012a200e13441c100240000414108440740c401c03522640051801c01c4828410f0801c2c0c6c0040221041042c2102e84142c0c940358480c0c1141c0000281000085025100010b545444040f550b484507511001d070650f00261740b94030b1307120b00c214040640000c1c02900401c592144a00503483c0c070384401344200d521040c4518000303000e0f20b0250f906034072800d0701d03c80c28141000300e841868125100101580076540c07402009036001503450703405000c00c108000c45200201024001001c032034065030b01a0405c24103018080c41d00042c0a080119242410032040c80850441401c480c140c0740d071400c0954a402d51240e105000d07290300c0c030809a41a90300d051004d030098140d0003070203100e0350a440300c0403c0e075a88103048000b09014032010350711020708040d880150801c1d100a040c1c906070000082120b440d640c50380030586101201c501c0f10b101c03004101d002d450486190307204809005030000d110161418000902c540c1c405000944107103041251401000018482d030803154401003 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 234268911 1250 234267661 234267679
    0x16020306070306032003100f06120c0612022104050f120306040f0e0307030302090a0b070f170c0c0f0d1403030106090f03030f08060f0d0b0901271b05 66
    0x4880107000d03000c40e200858403d01a410a500512000d2035500b80c19000031b802802020b801c481e00b40d001e040c00c80100e1856517520400881d85100c0c0c80702e01c1844c02d0044a1200c01d02c1e00d000701c02002c26800742041540c280c418801031140e600580541e0b44180c4005290b00490740301c1703041460821482e03131307801c0c0994402c0d002601d600741041400345104020407030301084042e562604179030580b08184003441d8613420800490740085d0190780900350810001e820300d02e0507602c070800304189071b01902003691585400000041000a00403208204480c0c680b01079040c03800303032984240e41d0000a49081d21a8240542e503040b56150058080c8407260004021180150b1441c030301d5849920030300a040009051007408034001e0082840c0400712581a07407008620140d07900d00b00e51041b4007503c9958808400354042c440380e07591008409000d40150111011410019050741c00c440341d600358005c1d124030488100301c82d00b803030110018055800150301c5201100300e0f80d080031914410740026030320803188 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 234270161 1250 234268911 234268921
    0x50913140f0609070f090306020d1503050a0507050109030b070309080903030a0801030b0708010e0a05040c0b041d01150207060c0206040302040c02031908150f0102010608030318010b150f16020306 86
    0x440150141d42e003610241d90988807800200c55000120441d4008144410420400550142c0c000d094490b00950005001c080d01d810410008000e41c0c01680d25074880d480c0c500500100307100103401450700342031105032a403665440c00d1004400500307907030a042c2da5003628824040000202e4152520040981303035102801000605000005c4c0410380b2040c030740d00c0005584e2406100140e0596130b0f03c01c40c0c241540d9414022001a0030024402c4843c4807910f00b000070600d04c081c01500181001006040e42e006048510091503c0140c1c050100310840c43e02240c3c0c81900032a0742c4040d64180d142c1901c1070283c40c0003003110b81c803950b40001d400910b040000f418207135001c005410803803146a06c071070051300000760440d00e040050342d144001440c104030709030081c40d1003415001040d00600010a65036039600e003180c20354008695011507100181400c1031040420300c60b41218200495428190701002c0ba40000380703000d02d60301809070f0180041c10b20502120040c48402282c0d004048590030310340 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 234271411 1250 234270161 234270181
    0x6050937020d0f0b030f1c0e03100209120a03051e1b01061503060609150c0614070908010504170906190e1003051302150c030705010e16030305091314 66
    0xc104481c10980c2c0c03070b203210100b86180110b0407546c404503d00043c4890342c2c0c04002c0d509030109601403d014007d050444050a4405110031000030031651401616080c010b02400304022503418010595080120f4480021790008150740145004488400180040d11814000e42c400d40d45038000e0f40c9051404104103480540098064502803001000e5000c075801c4203800303542e8136005400108030f001e030042c0a01401c103213199011184e54a00140e80c00310a0711420210307481030100491494041c01000442508622203070005c0080e0b800820561a054a4629480807014140c65043c80c0000301d030340150390b40780c00352001c0b5080d1032001c05002c5072030003000e05000344079800780c0c0c0180040e410085005002c1c2c440d0b28480e00ca441200c821200303080d0300b04501514245c451002034002800703501108001000600341041c03040d00001150320800040764074180b0101c1e20311015890200c024000a0b900805851242806480003800b08903100850b402404610b40d80344103120f02c21007000711b00c1c90 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 234272661 1250 234271411 234271421
    0xa08090406050a0b041211061303020918030d0f020c15010e010e090319110d11010e03040501020a080f09040519110301060f08041109040f0606050937020d 68
    0x104a80401103a50b40780c0a1010401180c86041c0c2d00079014401000701c000207a0140d654144030b8003100c040c14070014005201d42d004010064960b4040c8502803046040580d003e9420a440254410a41080034012640d0b0f100e0902600e2426484110788494580c0d590144c4040f84050015500032074075402c2c40200d9000244100d24154540a000180c0100b020600c035010700c1800024625080300c02c004800c030103e00d4a00c460802c80c548a03451005001405100c446013099550706030503a840031042c2d400c0d180d046114200c1a042044100090b81c3c000803000e00f02603010400540f20301225900f20014098102007a412500f40350420121645100c2840c0040001007002c1104040b007a80b4580305000134001c01c0007240d100300441452b64041c1d110240c0c4540300d0340c40302c0c0c0740c54150404070f0104d40e000c0d2821540441980b440038100800340c02020003808060794000a50b1420300001c0d4400f83c0c900e1038a10b40301c810300300c20110650074001d00d032445040da01c41c01d564071b004c40061400184 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 234273911 1250 234272661 234272677
    0x30f030412120b0a0501050912030a030f0b0f0d020d080706020417010e060702060712110a11070602010b0d0209070314010311010f090b0d02090303040e0705190804021e010309050a08 80
    0x51030309450541810101e120b490f0152501800b00001a8100310054a03a40d0101e00250761180584005c029208810030040082500c1c50b0b4000c60381d03403201141030302030320089011030b07124400f901310243c055180c001c00d9802d880d4048415208482190a081c00b280c172030404043c061a00014010415010000401150b5441d00307000f00141100072141544035101902e80b40c0040c1c0004010903082803084444901d143c0d00304c000000e64400b20207042445038410100d0201180801519004244042c4101e200a00700ea000034810760400d00f0011b4040d03001101e00074450f4108002084105229611215124901c1101d00c0703c15612030403c483d160311b0400056000580400180400c580b10741428801c6420a15015083c440d0580210340a500800c0200f80c01d0710080c080000d90049075014280202041d454150b40c4014000d58011101c08003103a035020b0203007000511005803901030081d90420001c0c2c0101c07002c0c004c1000100c01074600204c020b8014802c50760f100c4240709401000788884 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 234275161 1250 234273911 234273917
    0x306011e0206041a0f06010f051b070e090706080c13090509060412020309060d1107080304030801050306060609100e120a060e06010f051305190204030f0b0a05060d14030f030412 78
    0x7400090003135115120844d001e08100295101203812540510031003c9880282e00b00a424625005240302d606401031a200600c0c0e807100340100424813441c20065008050080542811403c100c40a40443c401070070b140d95090000501010180f81e045c420070103413261800510a9080c151846503543c542610142e40310090b802050f0401800002140d020030006486e550800103804403105c005d10468904150f003c40c1003140e031000900c0800150b02c154426100c1400550509043c9403800000400690080030302700f01030703030a59036001030b500d02c1c107003e03841d040990b45d071a1000300356064101a170150180c40303030802500070802503401c00c00640018070111aa2340c0c1c0d0f14180e40ca0104800c1c45103a0704054254200112a041c80e0011540b1880d5086080c03d1a121401128100d9005500c26500b095100074140d08003c90360140a0301b01404210600c010f08181000584601608800a080d410700702e0030080312620500503204a42681501349882c1e2400f800c2080c1020758104100e800 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 234276411 1250 234275161 234275183
    0x131a07030911060c0703030c0203010905030a020609010f27050709111b07062003040e0109060e061801123206180d0f1e110d0816050306011e020604 65
    0x45040ca0416a44039154040040902c1d071b1542c0c6050780c40c10068002641c00d5521012040042002000248001052030703000300a54500304c00c5050854000000c402e8403182042e040050764200034503c030424441a85c0b0a0f400d114140c40c201c0d00d050086e505c2011a682132184080521803000060001c1c02c0140304020401c03085000c070b40d41c590545000e442d010031341005a20040840ca00304415014030443c040341c0ca45034482400c2800302d2026481000500d0b142c03503050169012060090303400c440c0a580805480e0060703141c5c0c81c0040c005000d03156007003481c01c00076014403582c42081d8445000d40024141d00c000f142c1fa038285124080c0725142007a110300400303e6010901440da5442c8207c0c8c3d40c0c090003820010350b5040b16a60510945030040285c42c1c020100101d4046208600154144d12010251400b5204050a010000665806111004040025603200064081c401a0700c2d460407668079620000140c9611603250b00b17041050910b00c0c00e060307a160700026194081c900800d0100e407 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 234277661 1250 234276411 234276443
    0x604060509040b0c07031206331d0a1805090d050f090402030604060806180d031a0603130b04050f0714011b050c04021305100215131a070309 62
    0x81c41d85400d540c0140315000120000b410303515603901030000d040c86403500506280c030079004030054a140e030f040a442c014401c3c4540c1c02c00500d00d2100414070a010a0707540c003001c0404005072a051043e020b0b0500b0b00404c500c1c03410342d50b641c07882100141c54691030038400a0fa00e1014540142012100a0214072800c0808118a40a80152440c0781800d45805142400301003d001c0690000381c001a00325444400100f0000070070b1040c0791190003091040c1980903d4098000d142c000100d00000505150401078414080c00c0783c0c0a1b120524155003d50b07882e100d0000c0d914400181030030282c0341681c4107045c401009804901c0c90120f2400c40100c0b8551a11540d215107010750103a184d81c08910001c90020040c001d03c08441c0e0014002c0007a0703130010b1810300200e02a030f402600910341c0021b1022041c0b1991900c0d241115884241d840208a002c4014030380454101000e4840c40543c04451060801c00c40e14600a030140040d10060445a0074150806005072245403002c4400174140f0f1510a = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 234278911 1250 234277661 234277669
    0x103060c0504030210030b0d121101050a1505040509070803070f030e3703060f02070203160305060712110f030604050601031509020a050c030a021c110304062607030506040605 77
    0x141035130780080c03180c80c0680603054250000c1c00c00c0641c1d03641082d0607814100105e0811102c0036003040003600d403030151801400f410790840d01c1c02000110f10318070713002d00c9541e0000c400a0150a0783d0701510005050340f40c420001c1d1a0595a41c00110103110009241c02000701400580110a119072204000e0b0392082c4100852000c3c2c10a1004801128400180701c1c090106151021139980c0b81d001750701d5507165250761085e40d0041007400fa1154000480c40110f08040184c0e00401d41c045450b18149401e55450b142c80b00c102410b0101084048030b24a03a031061241d00a03411802e4407065540e440c01d0803560065075810489500d88034525010008a80394040d001b4000110300f0054403280c1c090800c1d0210000307400c05d01811041000502c10000400f02c01c01c010800400d1980042168000c900c070341814a07a0b00f0103800b0100700c20045a10f80302d080010988003611094100902c0700640b400242c800002958115a98003c1c4242400010b68050b405035000316403c0c1c0b0300303001c0c581e180d0b0148 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 234280161 1250 234278911 234278917
    0x1501080c090f13061802040c1d01030506030615030f030a080106090603090f0b07050403060e0304030506161d0f06030f10120c0e0714030a020306090a27021207080102030103060c05 79
    0x15450009203e8007800007141c07503001d91008481e880189201d81c40310303004036003240c0c00000f108000c910045a983d0320705c4c404c500030114444e02440c00348450320706200440e80310000504807146091050036185841d0b50f0074080001c10a01c04404c4a46078619240300503d1100288076041c0070620006000c15694802c1c002d0261280e0848046440c00103542d0395111002401001c410410900f07010201c00940035002c2d20300b500c060b01d0700440d02c480c25400c111781021030182c89803000c10b25080b180b0700015040103008500d920400c400090034203034400800d011902a41402e0f611090000400c8140604040c400c3e0180d6401408603420603107652001c012107088200186c44049411f20030040e500250301d03041d030300504504c0d1800030140300503600c0090382c00540d84041070540210400200d42030442c000f650040558405200b649500c21304064801ca0300f05c10020144000c40c844000c0d511051403c4c034200420381c0850b4401036407100303000e00039042030204548079410300b072104030723005d100c1c40075 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 234281411 1250 234280161 234280171
    0x11072f120307030c03120e0705030106150c11030a0210030f150605070b060316081506011404090f0e0d0c0309171218030109082107020606040b031501080c090f 70
    0x4601d8140b090324107a80d90410010704404008400305d038105001e020740214244e440c048402400c40c0341c1080c04060940e812500a036400556440780030b1180b513072105003486c1840c0c0002e9400030744004000440c1c01d0000040e07001e90000311380c58400140c168182d005102404d82c0c0f0310100220301c00c582d9684900211407085d000083e405011200214030200b00b15504141300070100ca407034440035003d007040c11070b16070b2150010b608601145031928004201e01940500240f03410b04540e007441c0041d509070700460041024459940544003003a103413581c0f1035800b240c4c00310112400e400d407007480100309100e00042240003803a19140080c0107801c00305500c0010240602800c041a98000300003915048010100a56004039900d40b440743c900b84501c0038400d01640c2c0850341d5000c1000d507503103110f001500754080300e10a1020403920715800300b03000d0f4011a080b0790209a039018040060b1a02d03907490031203147c0960800c0002403003800000c01242c44001620f601d03000ba660240183d042420443c4e0b = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 234282661 1250 234281411 234281413
    0xd0603200907020c0f1e030f06070801080a0c0b070503070c1e05040b0d0209040f0c03080424020604120e090c07020907080f01030206030a1d0619060501021011072f12 73
    0x10a002c9945081511b8010030904d08403041c1c800b0342e07018002440c0c03509503084481d007074101d90240560180d0019510703015042d41d50003820080106e03911216041064450b4038a88113010854208000e401d00c201c40d0420f811010340741c0e4283d1a43c3c5005251081c200a524144510041c00a0320341031a0040041501d07005111203481c07502c9409001410030700410840d4520628051540043c02d042c1c0d0b0707030010714000d02000d505c0b107007025403900e180d004000404088110b0380c1038890665900040381030380103520600043d82c0482462040d59840540c15140307910150a030100719000c031030080608070440c02214860800d85840310b069807403030b0b015111607100c900001d0050015040080045d900701c1e403000030001e038011f40d06240c0e195a80c0d040040000316004032090100b2035008840040c0f4030b602944c02046610b01d00b10000c1d6903102da0b807054220007910341b0005011051800103030b03001d054020508825000900d4200140010ba481d02c610100408a450f5805418519038041000303600c00 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 234283911 1250 234282661 234282679
    0x605090408030601020a0510020a09060903050a23030a0c0506010504060b030703090206090d03110c221a09040c1a0901080408030619080708010608010c080c0d0603200907020c 77
    0x1c0c6660000e0b030b00c000c10060542c4900506400051020044a00d070b013100000010780b1001c6940004289001544c050003c1212a0400740086440400d03001d10680d4010517448034100341c0b8194007100101518070580d18080410410b8000b03810083c00b204052190007607907990781e01c2d4010007084030414020780c0b00d504003e0001842c405e0082e40024038240c0002c261a007001040d41c0058074221a00308120009862403a8a0003003100402006e00c804404440b20580d0b580c200d2f400c10082c41004010809440d1545c00c0340701c1e107400ba40001310384103901400817041850329050089002810b07204044401c4480c0c0300c81405c0b10455420344460300d0b0160f6858070309850307544400150b0f4201400e1983d015503045031781c031059a4114a9179005082039005000024581204282120425842000760303034140701112010640c40800c030356100003424a10f07500c03011015001e400800709a00002d011204943c11720100310002c8249810003141152169415591070f54101d80707602015003101e0300100f6407 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 234285161 1250 234283911 234283913
    0x12011211101404090603021809060a1812030e070b040b07060b041d0609120c060c070309080d020a020a0603020a120b13110a0f170105090c28030605010306050904 71
    0x280c8691054205600d8882070007000100c01c80003d920552007050781c02d070340e22401c00c00c42c10440540340355001210104c0c182e40c540aa0f05035201c882c001c042c0c0003003d175502c4030010f400b40144200f008090700701c0020b4400325000e140140c000d0030b11040082907441142d100007500017501d81141c0075100c3c4244240d042100d1540d818015001002c80d4503805074542e00c07010b002c00306035a07944900400e090006d0103113040c030b145842e082c113a83c08188404101c0070003013208510070000b152500508103600c41641c41c2c245040483d41c928440d04541d0030313402a00c4459a401d580040c42c5550039008540b000c0941d43c3e101000e808900c200c08209010407002c20b41c3d100e4041495020940c00100070386000c8508401c03028030000c40f1010001c1c40c0d203055000c5011800250300c4040d000c00f400450500907c0079a500c40814418081481003510401149002a20181060040d20b05542c005040040780318280c00180c1c0809c003040b078078180002c2c80c0c001f00141e40c1d8401d000303030821a0400f80c03143c400354450b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 234286411 1250 234285161 234285169
    0x90d0c03051305030a210e0a03120e030a060507080c0406081b091302040311040501051507050a0c0e04020301050a11071704050d030908060c0a0e0105070204140c12011211 75
    0x1c60002d041540c502c0400000e0281c03001e000600040e8811032499070710700d901120646020440c88128810418002030103812900c0307664400b03064a400212001d800b81001d54119601500380d2201c2ea010b00480204504000060b0012743c0505070765120301c0302d250364915403c1010f01a42c8525800a01444086481c41d40740d501d42c0501d00759517030354492400115202280e90000c0c801c41c82c00c40d403540001d0400074800e20364100c02802008803024010f551600c00010180c8141d043c81841388503000462008103c820810002740d1a0320100c0c000400e81c0d1002a054540001c46041c2e009500f0400001c4030500075104d0400c2501d40014502c0c01c2403402d0f1100000010708208207614074404100c003040d5656441010752043d03200e035603150640c2d4201203586040c050060500e4003600024080804141d801030213030941da080070301e8010b031140c46500020b4041c05800251840803103c0034207010004080703000030104c0a000909030221030342c1c0d980f00c1030001544a0b001500700c50405019440702d01e4 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 234287661 1250 234286411 234286417
    0xc030a0513050d111b0607080a12092003011506050904090503031f060e0f090c120a02030601030c0c0812100f060f09090c08011e0b130302010206090d0c0305 69
    0xa0000030407003581d07000341d0300d103480c0c80c4034041d0710800308144402c0c06402e42c900b0051024510004404003083c002c00c0001300d0000e020701d41303000f003ca80c1d001c1105d0614600c0f03025414800010900148400b050a081c00c02410070300e40145c0015000810a030046810140515540000000e070404140c0740742c4202111710380c01c40100a54025210300300c41000c82e408201660180210f00d00890001c2e800c00c41195028140341c0c1714506021a00708408040c3c0e8a190400f18041c0096640c0c44c51985c8401d0025454400ca848244603c180c0b84148200d00b01242d000e94898102a2401c00a09da4105800c0e00d107070044407030060007482c040292030500080b00144a401240c5085151031640d1501848411109180c00650001e081c4507081d40c078080c1c2c480c03402401000c96200801000302035032070080c142641400b61803c41042941041180f1b5000c80c200c0c001000416071280d08c55014420002144045204c142e00510442001c035a0034a00803800b15480000d035280c0142287c01030f502076407150 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 234288911 1250 234287661 234287671
    0xa2106141e09090a060203040b2a0f0d0615080103020a0911090d0302070e090a02041a0306040609030203130b090307090501061b0f12031d06010810050a110403150c0201050c030a05 79
    0x1011310114a40003c0c03043c00a903014910580f0905080e1410b000e00030100300222401804030440b080c402d06180c000d5000f126191152507681640c2c0c0c0148040400140607603521424003454000541614075034084040c5058034400c880c154522569461030005560a44c1c40404503144104444201c0c0d02d4030340e00c141c081ca8440e00588034400d650341075240c0b444400700c903511341940206000c0300031890240f042907900b088100304101d1480103140481c0d95040c000300300601655807001e601092500800580c2e10409503000040c0d012900c40038200e003030350811b80c40c5502034414068046120501030240d141a61069030b10f1040d501203c0044050031002d01000340c4a2a05d045d14003404103604400c405250001e5840c08584001035268514198010303000d0001d5503007003c801400b4040000c00d41003d10311080f54040b5032610b60400c82070051100360f21810840303000007030001c20090130500c400a0361801d81c008000c540000e40c426420b03108100d03841d0b21a404200006400c0206640c40ba80d001 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 234290161 1250 234288911 234288913
    0xc040204060f0c0609050d0914090f01060f0309150e0106140609010804060b04020316020c0a050102100e10020a02010e060903070803010b0a1101090b06031e120a2106141e0909 77
    0x40c04c81d03440c6d5508180d074064864000403000b06040c08840744e0080d03d18105041640c2250079483c0c11001442c1b2601c042c000c400c20003d440551030381591194108418290300a10982c01c0401444180002848440b0440d241e0394200b80e000036207580f100282c610004800f4103054580b450034401168080c4004000f01d030f00c29500c603102034490712a48095482010445034482e240011708201901d40195075041c40d10801c9010800e100a176030120300710005169410740450545048a007860038440a260303500e603410310114482594590541040e82c6800500043e02c926031560500c05440e8400c0090180c0141030800c01080780b600c0180041400c0d2080d89000d40003440b08140c42170039209030300c1003655880341400c10f02407c0e14061003011412440200c46018140c408016103480318207042c0c0111811741d001c03440c1050b0a00a50b50110107090181c2072100c228401c0d01d2a20042c0b1841c0207100804485c4400e10503070b030038603180e804074148070546c0c40c400c250811020413212000007003c181e51 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 234291411 1250 234290161 234290171
    0x111b06071401060b030105010311210a0f0e0307030f020706020c060717120604060b070201021c0c35160609150e0303010302030f1606030b030a0c09020901020c040204060f0c06 77
    0x1520003031041070090b0132002502640c07075160600040649103583c160b1300d4002c60811405481c0507a0126001d0200c500c4150340c005a80c0d9007801c00300400c069400d45a8907170401840e880181c5001c00203107401e034400d44984503449541d80b004ca82c1c401d818003901d00540c0c040c0c1c00340c100030329080014212441c400c0f030010344805400a10020039810076a0103944d5201d1880030300145207818080d140c09000034407851420140b20b034000030360302c2c039101410740d004141981c22441c12a214940e40301c031458000110a0308403900003090190744044160a5a40e0940360041b045d00742ca10b5401c036402e42100c42e401301803130116601c548004010030b0340f04844854600342c1c01d0388200210b0050140b4200c506001d503440c2c3d8558014541410014100d561054001b60300c501d100626100325101a251b6618000507c01c0c10500801d10300000090098504080003200203126903060b0010303c0c0c200820b900b5200001c40c41403c0c0020703401140a00d07004074506c410301c005554400e20400c40154019840464 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 234292661 1250 234291411 234291443
    0x516090618031502090f09060f1e0603160305010504180201030f1407020d09080c0a0b13031a1608040203061501180306020406090e0103120f120615111b0607 69
    0xf0460106911146441c1c012414800da46011201d090302c220341584c00b1a1a0301e04840019402c0c800380d083c5903c12080b030380ca600c00005000300c0220310010003a1a1645c2c0341040e5002e0300e01101844980000a82000f0011500d4200b900401d03108003401d6102c03401c10340d01130380154003030a101c40c00403009031340d41e182d04c40000c4100380c1018003611041d000303000d448580c844010000d803c90380005e1211b0f071240c500e001ea9500d0b1022104d0480f800680ca03c1d0301d0b000c01d14907aa1510b241680301400703d03281400f072418000320480b000d0340a420500c2004000000075170341542d134080101c0b8003a5254204000050841080d5100b08980b41da051600c0c4022505120b02a00c506043d6002039900540c0450240481234000312180040c4c084002c4003a030b00d47c513617035030000e400c4401c0c5900c004101d0811030b0f44d0207480c0034108181c0c5444540c40c00b800071640b241603c1c05036090700c1c01e0101c001007901c10f4240ca0100c02054210b100c5441e140e18946030101c104c14000720b80c0c00501c04940300c00f20055189 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 234293911 1250 234292661 234292673
    0x100507050703081c0213061107031a01170a03023301030f0303050702060c07120504120516150e210307030306060311190311040b04090f051609061803 66
    0x100c061842140c000b42c40d0009100044c5112124040120700e0900c10040d61911142090000d81101c242c4e281040802c0700c4600706500303040c3c40307031310080046889040305201a0281c0103034038140c40c01c0d80c0c0c902503409031030000c140d5651442c2030050b0158000c02d0b555400b645030802e09035107402180584221407a04010030070f0528400364800e482a0500102d0001016850700400350007640038801810282400300d820070300303481034502c001c05d4035240c85108440da50040041d1130080a80c010f180780320000904029840d0100c0020b080001d40351601c003c5000d220300325016018000681d54030164901110074010300c400780640981a5560950808061401c20001400f60910a96001c0381700d034a012000b600380c1da44400e000f01240d02c03c3c44140f41c0308150343d40410b000b0751340d46404201c03a0044c8400e56036921480c0c010540c02480008c01290048007500041c15541b00c0c80410400c075035030940100802c00c11030b102100041c21451040204500c00d0f088980c2c031550540003114215500d54400c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 234295161 1250 234293911 234293923
    0x1611100201090203010c020706081311060f0904060801020f1b010902091801050c07170307092c0a0207240b030118030e01020f060105010c05190c0e10120210050705 72
    0x50b91254004011800e00303018038018004140010480b29050000290140800400b40d04032407009903807803018801445200c90b4100d20161101d99545491650a582503100e100010301860501c44001103c031814801c5407128014030034103504190911606110b1003200109210103592100d03e0310b4050380e01c44004a02400480b004001298030010549007513a42c018040e10819101b80107140102d6031881a1448000e20700c405c03980c0da9520004242c9501d04180c0003000e4050581c018401c030301490302801713220406a40c038a01042d9079500c21160a91250810041c0070100b262080c0454003262242410100580c16010412112410110342100c4000d0404042104803034010001e0607006100e840e2808070a10290022549001d40760b030b0384607c1803160310304100380c0084007820b12800f07100b071a00701e0104440c1e000d076013134413401c0070050100176002c0c07441000b6015001c41e10b0559515a00e43c21200201c3e4804002443d58080203131100c41c0c1d030708031070500804010180001d00280702c0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 234296411 1250 234295161 234295189
    0x1020c060a05040e01290a0c0f05030a1202042d1d15100c2918250b0f0f03100905100f03020609040e0d020d1b081611 52
    0x2a0070b8643d440c0820341108190180d000c90400303210022905100a8004c00000c41c210b551210142e880a40000485141c14500b00141c14050449400c80412a02000400004500341d45d1441040b03004ca4520080340300b1b070720a90200c181081d41205410f90038001c03901d14920030420703004555560f4001100800c1000a4645104e4003074403c102c0b2020064001e00480c841c16500d180425407403040c041c04050440c41c01802c42203e248a00c00f81041c020050001e0210260340f030707802c5040420801514895805000b5040c0c001e01c3d01024029005440f0039a00442001040745003500d01001418641c0c012001d101041c201045182c03803045d52400114003425507203642021035890070051104846001d0706400c5451000d150400503260101d42200c107482c0c040701e07015070314104036002800a041401b900503076805800c03090924150046111b0b50040944c2d1a1800c02d0390f000300b143c140c034402111004100c00c400b448041c072007603280101440b0a034401e403941981c0040303440018101d0404210 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 234297661 1250 234296411 234296417
    0x70f14040c14031e2202040b04060b280f0503011703090604080a020924060c03130e01030515041a04020a05090c0403060b03060103051203070e04180212120a05070201020c060a 77
    0x41c08943e0584c08501103a40081844210f220300066a000300c44aa881003c0291081d074030f612010306560f40f1544075100408110a005580310101c0b440c007568a010b8036070b810186800e00b600d000c00640134060140000c4155591503196a0030300c01c0100103c200c4100c038242e00d1000b481000642c3e2035420060000e40f42540041c800404c0f07520401c014403000a0110050301c01c0351400149110001c061884c81a204036941502e9940a03180e00d4039500a003074502e82d1102d000ca2000078103100b1420184c2c162801041500d40d01d00f4041e0203100581c8054800501643d980c01c83c604100040100b01a081071005107003100b265903440024908840558050105240000f0208108032461151810810096015200035851503c1c0c0580706c04141001c500d950701d001000862107482815450080f560003082000709002060845c0c10100c0c841c0c4040340510300800000246503800125040a0450030710500d2a040e90f51800b200d160700401c9007241540b0407240c40c0700c407550b101c102500c0380b20b40d01c4d5 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 234298911 1250 234297661 234297691
    0x806090a090b0f160f021b0415030f05120918041115090a0f03020603060616120203071502090f0f180a021306110c011409030f060405070f14040c1403 66
    0x2c20305042105213151100074060300c9040b0800d015008282c0380c51200780480c42c4840a001440854041c00c214410f40b002e010b2640004010007450b03038100354030280280200c400b40c4800e000310f90014803800c45d507180d05c224180c04040b03101c1d003403020180d842440b0381d0313292000c010120041090a40782c00c0c60120700c031a0204461508c2d0500780c00200050640c4544040740d5031550300498403921000c0d210783d00072880047c40d60100288102d0060300b090340003801500c2d007100c200e8000e480b90080c440840b61600c0e413884415111110f4020f441300188000c1a0300740803c0d05008102e545500b90650a800c42510303980d13010308030b5800700c40030b00c141221440541ea0f000302001900c00c0342d040d600401d081c45410089031a803510300007181c810b540c00070f00f04103882d40da0300403131010180100345c1c072281d02d881090420390700e46001013400d50090380b1a030700315000e694072400d2440c1020901d0140c0780d40c22003007480700e09031440c00303400c10a490b0f0b055040034040b81554141c0c03050198030448060b80480482c0c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 234300161 1250 234298911 234298921
    0xb0711060412031107021f05130303020d0305010b120a0b031c09030203060a0905150606190f081503031c06080a030503010e011a07020120010f0e01060909030806090a090b0f 76
    0x10b0181e016040401034004d0700d0884a503001811600507100f00b05803120003014007000603401b51088841513100007401500c4941d680c0380095032107888201460006e8109000024403412500c1a609100124084d001403075a910944a0041c0103084100d40c0c18450071403e01c1100440c0c03001d622265202c3c0c1c2c1c5181015080d8014149810800f03420001a54688541040441c01c0405c0b15107104200c8800400c1e00d440d80300008417603009000c100d035440140d9400100c80680c02043e0b116210503a40c54001041c1d4592034482420302d205000c040d05a0400c204503c0c85038004d03071386001c400000d0039001403119140c02074289000b108403022008550000018440007840b605214014131900d10103c0510a00040c1e1141601130010020305004a06180c00040307980700d80e515600d001c81e0030082007462900c1110101910300207850619a510785000410102c180d03000d1400c541d901525056140e480e00014014040b10091481c11695500c100310070000300c104400c14014410008001d2032414a = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 234301411 1250 234300161 234300167
    0x103151e022d030f0403080c0c01020a1d0a03050309011202070c03060b12160b0304080c0d1805010806030a03260109020a09080c0d230102070602040603060509130b0711060412 77
    0x34030b02605458082c010014590303903c80355954450b5042c94141034689071184107a406000300701801440d94008134640c0383c113603800386140702018141062000140e520b04217003d0301c400d003400041c0c4a6081080003010550041c11080144500088014608003d540b24420f103040d16400444403241c4072919068a4074000380c0c0116400308070f0000d041c07000001249805100c0d054070500c0b00f103c20110009003030000340c0c01030b03803810074841090310701c4440001801040b280c0314800b4000040d90102d00800e495108164a13880b80c0d13000340003040d503000070782c8007075070402604170b00b0030742188000300c0b1080441c202c501d02c1d500030a01c403580941c45031461407018114140c140c102003a1503214044100c25a92900e010300d401e076401110304082240c000300320701c00c0d01440e40c000321565800000c0c80402c03c500c41c2d0003003003194090364040000c50303116800c00041c0041911103501c166060000e200200b0900c0c401c0f1601300710503050045030348841041c0c85060250444007960314425524181c80300b250 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 234302661 1250 234301411 234301477
    0x212010902090123010c0f050d090608010605070818030c03030705010c031404112806120c172d13020306010504060506181809100c03050103151e02 65
    0x6140c034001c1021007585007140c031655004402c1320b410030406000800501440b10320311070340f10f0780000a882482c4010b1401070201040d40c4aa8800990042c0000a1035442030082d41c1080358410380e800e14024890208071100851900341070750601402c00c119405590030001030440c14030900010a00f022540c10180032946404030054400c010304d410070000074040071a494015a08440c1c5042440750031100400052100c00040c24a4141040102e002a0020880c19125070b8080b02400207410341001251155002109611290559000f1903004042c152880d83d1604490300192120044180503c40701c0c1005c0c0c4405a480509031070369010350071b0901215000d8070069405010f1503180c0404038180d03100d5807000706544c012264100c0d100785d944810600102e51025013808007410700703016031b9031101f6080c424039080d14a095460315a80c0c2c0240101070403203800c48200e90603000941030001c040c050380a08401c06500c007203150030901c4420701c00ba01c0440040450422402280301541210007 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 234303911 1250 234302661 234302669
    0xb12010212010e0601020d0f0f0e0604060903140a0c15022104030302010f05070207062105010608070f020f03030c030a020d0606210209090103110d060e0a0b011220010c02120109020901 81
    0x240041c030b11031f47c020303070409007109201085241450303604126181c11101d601d4a6151035603c40f80000300015034941c03040348442172b41d004071040c18214004020003a500d8946141c0203122140e6040700b0050580301c0751981002c5490360044c0d803401c0c640c80b14007040441c0c03910a0441011000300303051003071560900c00d1520540d01d16800308240e0920303c4c4c0c041c0d0b40320601d2007580304000b00c0984d00701c0846100303001e030421401d8042c0148001d50b111000900320400494160000400740225542643d01c005002c0c0790281e50741c1d000d145943c45c2c04009000652000340709135002e13a001c1040030840849482030390007c04007540c83e001c02c00c1c0201d52014550448006a203c40343c01801031844039aa100d0703c1504485c1d1020384075010104000c0031404c0e2040d19031024251314580603500c2c60442c0e001c41d200c0100352103003880c41c05d03680c2c131030303808183e040c4601401600020b1064150540449900d0345608481c10504040149101c60ba00280314849142c40f000388907512902ea032403c5092149a15002d0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 234305161 1250 234303911 234303913
    0x1d0603010c0207090f09080c010603061107030504050103112104061d100207030215010b0d060f0e07030c09080f0708070e06130c09030602040e090606100509040b12010212010e060102 80
    0x911101c000940e20303941401841ca645983d001000d02c5c0703110a07401144980d50054406403a0922284024020b01c91031000780c401b07e0401c1600441c0101900c01c0b10b540d83d5054403100c0c2868104001180100f154040c01880d04008010388680c03000400c45101c0001341d5a40c90384010303e85803400070180c44824040789101c07a2034600c00c880d42d034000f0510281c4404070400c01620340c209420100d00d00300c420398410700c104045600220b80b20b0102d500030880340707084840601c80740d0341c1c82ca035181c0d00c0d094610516000c80440b101054825111b90040485c000c1e06203080d2001035141c1181c9403d0202141d041d080381d51024008200c46801030102900a00684110980074903009001c1070414250964a01809650384041c00c44603000c1d03481c2d0030156411013400c644803511070340752a081150969000740e0b40d2040070005500e600d8013290847c001c40c442e40c0d45a0074043c1407018080074200141c2440e40c00f96426056104035802440a0b0078603036110200c20461b5494440400c19031180030b0051411 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 234306411 1250 234305161 234305171
    0x20a054006020a0b0915011814010506030414010f0c030209041a06030105011119060e0114060f040c050409050a0203182b0e1207090f021602090408070803011d060301 73
    0x501d0390046103a01c8200d4021007004503551710003241758282411490780070001c800d114004507401d0301000f04001e2284050b0740030420b07000d11003c42c1881d54800d1181c030f0752182c0c0410020340001d09481c200c481c0002d05500214080d040a0000c5050320980800c040000742d000c500b04806140c0780c0155030300050700754011001050240003040c1e147c481405482d0610030750745050452884104183c0b0410f45205040c1855a0040d2070070344094180d80fa41d9411039800e01d84100c40c44ca0202240c01e01420b0010521012041d4550030300c8083c00c2c0181a840a20006200c0060350f0065405031a01c11492258010781d070b0304c1d11011000090b01040c2c1c0d0200d00e6404090480746120f401d40f01001007450700200800385181d0424102c0b9501c010341400f6811051741100c40741e80316000184503081e070b1200f800a001c1090010549801c03400340c0d4958000380b1010250002c09410640c400301d4110b030051141500d411660746801100b54000e82c410401801c017010290444250700c4407403904900c04a00232300c6 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 234307661 1250 234306411 234306419
    0x90507030605090103080d1e090516080c09060126040c0f0e070509011d180103030210020f040b0304080909010b09150a2c220c0c020a09020a0540 64
    0x4643d010304100301042d0348e900d100e5018950040c0480c0c00540b40c2c44034042c400542c1c00d203801912203100082d507010602c1000408100c0b0480032600d444500c40c013520a80581d44c0380001121003500c41c4000400d42081d41292200e1141c020104500c00c50040001c5010185840d855030a542a1540701028480307561051203c07840d07001084500c2d010007480c00707807418914501c1c5c022900c2c0f05190102ea1014940021015480d0502089412039000b602039030200220001600140e200380302c44000b6540041105001c0022040090740d04a030041c4d03442420318986901081c481ea000381c01580d003000004c40c07a00342c07528001e01544100c08900304058113001020070083c160f000d810008402c4071446104c4004061042240c410101e40001c02d0000000c1d0800101407600140b440c0810003182001840034001e4008d4550201c05a405071400364814032701390025009401500407030742041010081d0001843e00c020048800100c42d40401c12403080e1460410800803030004070034089046003030100 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 234308911 1250 234307661 234307673
    0x10e0a021008010302100c150e0109110306011203120605040c021e15130609050303070e040525050307030204080106140102010f050603070b0906070203030a2a17070503090a090507030605090103 85
    0x41041000c0c140361f03014040c14500a8580d0f4000d6032021000d42c900890401440c030150403010980b8000d5072a698045044005d240d01c48609000c0c0c8910b480c20300c04014008bd101e9003014011000c1c0c0c120001d20f017612800000d081d9400a0108030044e07204121200e0a99030403080030108100410041c85013896007101e002c00c0280003081c0d55081c0745160301900a004894100c80003255004045e41d98a01d8850000780101004500c024061480c040c00111600b41803008440a11084040c0349031498a0540c100e03540d620040030107007019000d10000484950174003480014122064141c80000c211000080c01c440c1001040405a400c000501040703440125440c4203442d2184016035854094030040b454511581500079018030000800c0310189601031481340448490710b0070001d807129400500c2c00d10030b00701c49016081043c85058100d160350754400801b541c074441ca054034245000c2500055001c2c0c07055103d006483e8480b010441c840781c0c544520b4001d03200451f6040d1040d411031300c4003 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 234310161 1250 234308911 234308929
    0x8030a08040303110c1002031012050a0209040f12020307150504020d03030509010b060f031608090606091b0a02010f050901020403031407030306031b0311040e2d010e0a021008010302 80
    0x20b01810381d10350305140c20760040c404446400c3e2042c03044801480c92100300b14001d60048030309495015002c2c1012460390040c180200c4060b03001001040300f80c800740c01304950f0500c00382003225078070184188500004c0710b0440106400401e90060742c3c4690a0382090345c0c8515103110303084922440c2404020040c0d88408080340c5441e00341c82d00043c69a110000c05006003114120280e01a001060698003034101c50001d51007920010103180c80d40701d1185080e06c8e0804207460f03160b001d42008000034040d040001f081c591100341d0070342e14180c3e1600f18036050140d81c4051000030050b5110740b0f0381c03010280315000c0c5a802c45406030086281c00e141d0344005000300801c0383c44484a03080064410181882034000e02c0256030810f04059000e40740b0011644030042610046501000c07a03103808016180a1107401000d120010284c0301c181e40b950026010b091004482a11410b40701c200e15421107002d06c01c407440842101d0040c01c032400c441c010001c8044484a8100800180c00014001a00e4460341 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 234311411 1250 234310161 234310163
    0x6131413050402062d0d1b14040e101802091002193804030e0402070210030903020f19020f06031e0c0705060703061403071a0d090b07020703020a08030a0804 69
    0x6910602035880c585110341e10900d045d140c001e00c0840c24042c4442c3e02d034442c2c03510742182c070304040a10070100c0040d01c0a01a8030841400080b09200c20800d03a002103000e6503100e0007a11807a00483c0c1c55511194826015440c1043c549602045850341ca041403620201e48002600040000c43e03000d008502c2641c0f01e4040c000c0070700004680340c0c014201d00440c00c0c5440f000d6900455100380d412a2001b20441084905030001012224981c00a0911744211071442c0d13006440018030350201c40b400c1d4054294828101d04600c68000e86000c0058280050904000007551104d850446801000581c081c2e00c80498880c0a0410510030804011240c5882001074072626103500e07074448130640d0560150610183c01030285200304854940e02d5403028055800c181e1184440104450138199a002140110311200076030840310b02000e850340300074040c5500c20000100b04054503075500d04035920300ba684000540d20882090007103181c8a0940c10140000e44003c40c1049601ca000502019003e00 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 234312661 1250 234311411 234311437
    0x61e1409010c030201090f08070317010b090603040f02151917010312050408150106090602010c020c0f0f060f090906030f0c06030a060b0a090303091703070b060613141305040206 78
    0x81280403d03000f90048400b40b07030041d6003c510500ba905110407542d0100340d00708d0004c1c1408520708481d00c0610760366410384040c0070481d801d1281c2107040c86100d40c4054400d0316440b402c02c4010005a9500c0e001c1b20061006030344444d1541c11a0030500340303040c1020000c03011b01014240061401b803452401e01d0440350040302240c1c60001d4600305848074811a0400c4120740a000650200140150380c0300f812211695242d035405595060100d088940800c240030044e002501400000d20b44070200b2440400000d04100c418641c10340001d900c2d600002c800c1450000209121881e0324000101c41d0740004154090080c100c108200183c9803081204103a21030030021022443c0d0385c115030b10510141801014083e0307501c801c0e83d00a403084500d4402200058480310020501075807410008030142a0310004506003149642d40c02c000e50002003000340c110400b07010305030500e400d60010500a020320060a004020840c00380440c00542003080c02485041809010040e1210411201c000c8000b01c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 234313911 1250 234312661 234312677
    0x60a060302041a091329060a0609150f020106080f060103021903080d050a090b07020f07150f08130c0605040e010801050408040b0d09330b011b0c090204061e140901 72
    0x4a01140041078000c00039904000d00580410f00e85554030b41d05000e0345040780c0c08d0036069031303403031003103600320018014100303004900d88083c05564020b88806501065030700000c40c1b01a01c0c0e80d25145480015030308440d103584a04010010f6080c45e241e400b14040f0f050400504060854443e25070300d200722145131303243e02c0d038980000c0e0544145034410010954091690649410000c100075510000c1074103041c0d240c0101d0400140d0207c00551707022844045031a9104401c0c0d05250a43d5448402402030240c0440c1003011000140c15407501d0000e01110b489650b10b039030504048040d6a101604409880c0e0715000074000407880c3c000684048400151806550b9100c1c0a80500600408400144508110911030340c411089001c543c40070181000c00003040c00840001d14143c400442060f404524805415140c2a201888032070030b290003881d40c1031030030f503658442a080340e004d51305c03040020380d404e241d0102c920000d400710060045c1d203240c004641140e4001d22002c5100d40c08607036060220113 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 234315161 1250 234313911 234313913
    0x4020309030a300f0c08101205030d020304060e06070c240b090703020a030b0307120807050a050601080c011b0209011701060504060801020c01150608040201080414060a060302041a0913 81
    0x894100c2c2d0040040b0601ea04011580e0140c05002c0d00b1a13007555071019041c04030f24907525118000461061010200c281401c1d440d28203510080d09410324151a10b002c200f0034030f0220510b40c0021401644201030004042d8000294503003491805440c0c141004203c06000020420225401140407251003585103000b6200c508080100a80036003660440804820017101541603800740000305801d4170b0520440c00f41100301920380c00e241c05805500715150700410702040c40360018001e020f20075002c544901c0349a8a5040c540f24099102c00071170b51021010341e001c0e591004040c0d468845980c40b0a070507486941c001640c0e034074140203032a815201407007104a03801c002d4101500908000c2c00800400d501d642d40740e40070b9841030314102425820035054510102001c040c490440b141907070b8445a0362200c0c0d00460b0a207501a005513004d00f00c0d400616043e000134001d5030301030114000d0025141d031440c170500041e0758090903d42e15605a24811142540702d00c4259070748095500362004001d203035 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 234316411 1250 234315161 234315197
    0x806160309021002010504030e01090317030a0e03220501051c0c0509130b1512070c0204022116020c010c0f050715051201090b060d02181201091104020309030a 70
    0x3070300ea0040d6100c21612034404607160190b01c410b009500036030b115038880070030384015a07601c0924800108035150182d200c202010560b40a9504070b241581e02107000600303000c1c080c1c65a0094a140884102005019160022601c1c0e17900300038842800c01904080c07003070300d454180141d0b81059003007503a240c41000c00d000b44a60110b03441403000804a10f1070933034110380040280440c00309180203944a68101c03503003075a46429202d04107200d960001150b03480c3c0b80b04131010024110200c0e045502800546c0900c1c203500c9030303006034404054900fa0035180140b010313490076a4109690040d50480c1c161000d00c1d0760700c11243c100464012031080000c00781072910b03030f150400c10340c00341107081e03500d4592641e900c0d803250041c0701e1401d0501140f8001d0742c0b80e10210040300d4903451704c2075008104110032a40050190068078402c65506030600b56941c0200108414203000e071a03c00700c1da5510000d00b801c1081c0b8132860394001d9416a011821858502005d0b5902d1244840700b07402d20002400300401f031701c6 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 234317661 1250 234316411 234316421
    0x150105190f0b1b0a0b07140d0501030b07030b0d0507050f1909090213050c0403030e0d140f10180609080c0319090e04030903140a0501090b0709050a08061603 69
    0x1501c50300a16286680c2d00c404003032038200c3d0b0119110301e070390041e024011600000d085001c050700100741508540b030b4000181c84000c801c0c12030842e088002e03c44000002642d100c5d150082d4010b5103204028a40654000c3c00c4031001d90007240310b841800056800b00e000043c0e98025568281c030342000d50701079400010414100c9150000c0d602c0703040c090100c2c020006801801030244252a0490000c5800100310150b480072140c00c1a08a0144010008244500034a04031018003030701c144c40307a001a480700d103c0340780c140207448001c1c0d12213180520f60400800140c9590881e00d2001c001842000482404102450b84080c0c0016250002c80083c4180b18084a20506144040300d9407110082074511480c1e00e503c00e140c0118541110009000000640c218404c41d07040d9030b0415407504582d00e1014840c5014000e1788103205d100c0c041d05c00948244500c415160050f040074041740b8198a00800e07070700ea16084035000d003000301c908004e8400000781503034100340a64000001f00c000f959003100109 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 234318911 1250 234317661 234317669
    0x31403190203091504210207080d0f05070b2404020a081501020304080d08060a060807480c05010905030a0609030c020a03080a0e06092b02120706020c010215010519 72
    0x920010709005c104000c84a03090598124103103460b01604011000b640c4441c828400d01085400404590031307620320403c02d080c0d01500d01d0070200d0914130103031100800b02d5022103c06400848058000202218000c605000c09030216020b624014102c0402001c858000d8107148010b035111010740c250b60300a1007920060b0500904030f480d41884604014859202075810038010307070040d003000c00c01c1441200c8046c41202681c0751000701c009011040741104d016146000000900135000c40c02c1900c2c96800d441000f20000d4882e0b01214440c1000c44002420358001414049050401c1102d0b880100c0c0a0a5950300070600203429070044c1810b0354070024449009500082141c004010400c115029050000c100da076840c0015071031100344481482464106030303202d00c0590310109981035000c84080604550354a45007803032040e90200e8030300851030341e2048a0380c200c0001442601e0307040122018000092006100d00040082d40c0054040d060207841d0044012054401f110351000c00c3c401d00070 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 234320161 1250 234318911 234318943
    0x608060a12031d04050601140a03240603060f06020705011b0501050408030a14040201050d09030203040e0a060e090327010e1807110f071e09090b0403140319020309 72
    0x8400e039481c0040108034608500b0781c0d0802200f154082a00301842802e10035241a147d850340d4855100c402d030065000510618101900c5080010302c0394a5660f05800880940745c1240500781030010103001d440310341d0010031080420500800c2840c0d40028031300101d85003800d00801e24110210501500b42210300003400e15030034101844100316140c0c0080d4490b800c194010400341c40c1d50280318101c050261400307400208203102000900721140c1c481c01906200340120391901b9a50710805094110860300340c049540c2c1c0d92010814065510742c0c240d4030800340c4015514194100940001c481c4ca031420445c2c40c07000303038240030b0000d1340183e0900e14201402805000481000310b031151100404654200001c0d0600c140c4001807600000c008104510380d034080c0050700c0c181043c0510070107000244600800d03aa034800146050184184201503004014581c5203161500740682003010000d400c00f00c00c0b104104000c0c248541182080040c2410000903940340c4641c1845481c24000718084080 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 234321411 1250 234320161 234320189
    0xc0203071a04050901050607030c03050a0917060402040e06090a030302090f06072402070b0a0203070201110d0203070e0d03050a0c060f1d010b060306061602011b080a1d06040608060a 80
    0x20040e460002d081103480440d10300c6a560788400c14005a8000c44100402141c031380030300180001c2c064800380c40d00c2c60740e515000505a50b06e800441000a0f24180c1100a4010906000039030034030b400381c8a00441484014180c40c10804481a550140d40303030050101a8045012040d6a44520340400c21800050003551100103030b00b0003505e41c42c0d28600c030b290110b40c0603510118800302802a0fa540e2508002d400020340d0303e0710343c008080d500003041c0c00d00b1550b850705060140c0540c64050400b40411203401a01c1c0d1802030006044600207044091241411f14520300000358031501301c540740003080c0340ca02c0e030401c014070b8114007916105c1c1e440042e09041021518074006954110594104a1402408130344a104140b03c440e1006031000c0350804010000703002c08049280b000802d03c3c0c418035203496842c0300445c2040d00c075000d0006c11505442e000032410490b9a03c101c035540d81001d44000c44140c91684000550184520710518041c0225800020a12350301c1280d40c4000300003134624071003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 234322661 1250 234321411 234321449
    0x1020417010e0708010b06040501030b120304060f11120d0e1501082109011b030e04051e07080601051902010605121c110c040f0e010c0906230a0c020307 67
    0x40640400b20510289100e030190000d042d43d07050283d036281d80702c080d182d5480c0a05100045000c0d1041400712341d04031522290700304c0c1d100c008000800003090350ba42c0c1e2121000c82000010804600c4241c10341c075990003032034111045161a0b08445161041d14800903802c02c0203502a414201540b420000b072400203000064000301c04100074400c3d001c0c00712424036910320840b0b800c400740a041400c5002a40400713420941085a14001d12002d000e400c1c60340070302d80e02c14002400d486003103607410b2042d04e41d0030413410b07010341401c0340faa0098003a0400c000e00713260180c00203005010f0309040100703c0c540300480ca41c1c800e0007944210041e02002d407a0100c034485030020350350340f0503203d6410500d00910241d04442548210750f0303010380c481d1010140c040b0716080c0f41004054101031800c001c901d40d80b18510a4440403d11428a141040761154a44c1c10701e071200242c030030b02c48034121180c145044035407290455a4030342103560400d900c2c10200c040345c40310300100389043c0841d000b060f501c10340303106849 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 234323911 1250 234322661 234322663
    0x504050c180126070b09220b04060501051c02031008161d0c040b13050603040f03020f010902060904150503030403060531030e0f0418050123070c020301020417 70
    0xa058500c072403003404a0881010f9203602103c0e801c0002031040d0081c070030038010005007030010090004010030b40315400340b18042105490030020085600c0030351390003c00095041ca4001c0e14002c083c2420b0003420055005c00b0b40d16070552a05065220b2603002000880e030707066010130b5a01800303404049545614048010581d544030500841d4080081d007442c2c1c035400c08441104c40c0c4951010301c0c3c07060a0030718102c154140b540044c03200b00d80c0c1032422800400c0c1512a0f0014512407805428034500100322401c001c0c0c10300e0034640450326264100895200503032500000c8a030714001c10f441c0007a4812016401c140c01a005801c8a5414000003a0000500400e6000f06000fa081da40b001001c540c615503072803400c1c1c54007100c1d051901c25240c91710004640580044004404050008010b00b0391010000e0111008140d541809900805910051100c01d20a02198000012035001e255151818039840c41000600741c104102d0000921000c54800390180c400901c1070f44402c0c1d0401003080307005 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 234325161 1250 234323911 234323959
    0x140d06020f0c0c0f100c060c05162303040f0302090402120105101a07020a06030b031c03060f0b0c070e1305060708070807180b07020d0c060e09130201020c040504050c 73
    0x501d2044c0303030303a540b01050761030811280c1c000c904041d110b000040d011603541e0300c040c2101510b02010b002081c000e61004d4030007000b42c540c50390303c5030320704e00590210801c215451500002c00703031010343d2042c401401600c02c80c0c1100821b8030b40499544481d0740c3c69200088080c0103010b40c9034201c0d420f0205020340034240025243c02c3e21001d0f0404040355102500881c00b074040d00001035804402c5107810400580603601c2004040c8024090b500c0f40300300c4a0795210401c1158240da000240d07120400c2021040e403002d40e601074100c9daa11607240030760f042c03040781c0d07a0940ca0144110315901180400c000621f88000d50090740d902c03000b038503103925001d01d01912009080700c94801096001c40010010740c0301e40d8500c007039226240b83c03c108031410710817060388907003008400301d0f0454002404400440d220035469401022143d503004801c54148080c000c4020f00942070780640c15068403e200142e030082a25699040300703883c001495900c0d810041d18080c1001c6001d0b421600130340710124984110042c17 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 234326411 1250 234325161 234325183
    0xc0321010f0b0c0a02010e1f05040602070b04030818061b0c0a060302030601090905101805010504061d010e13120305010503010e07080a0b0601020106150302190504140d06020f0c 78
    0x10441c078180d60345081a103070f12981d42e981045410140d035402c01036000b03103030940f03404001420300500000035280d42400e641c049030098002c610041400c1210680c1000703120050400700400d00d00346451a0f0b50110301d405860805054051203440c0304802d0b8071110140c4540c0400050694107a03004551030548400c104002203010b005e1443c00485e01c14024000c40c0e000304010f9480c40d0f50341749000020001030101070180c0303c07261403641c4009101510300885840305040700c034000459514203800c000480380305610643d02085055011165030032011403650458442846541d43c4e03545025900c5a61b103030090000700100224840050340c00c1d850340c859030603680294020400070383e040703c0050b42e81440380b00307000300c2da44901081c000003600c00e001107422800600000c9602610f8503400000b5141c140b41001c0083d5021980050050007140381318419012410942e180c83d0404444100340d17030040d0f40507400303540c4075034603401004040e604031841146c4250886803116280c2e008251206000c410b = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 234327661 1250 234326411 234326429
    0x303030e060a0203070503040609021302070302010e0114070504060e0a0b0f030a05010b030c1c02130e16090b0909150306090d080a0204050f0108090a1e02280504020c032101 76
    0x4001202c0e818148200ca008a042e0b48601d03086503542d594840c0a48039002003241c2200e1030110702c40141c0c082c1c0c00500b007828881e4001140d5044011202c41c01c4580e000c000030701d20110101071119094100040382d007580c01c2841c10500c68403610012800144983d4030541005c00009244102c050142c00a1406251800e60502550b43c2e501050b1003180020303100d0842c0780c40101f0001481d180caa0b507614415026800c000741c01c140018050144c1c0c010103921012002c440030040000400b40c6440c41c80088206044c0222514109294040c56000e5545042d003cbd0040001080e8100610803628507458001411a0490303c1c200d2031560f1141c031090440070100c1c800402054040d5051700a640c01d071341c4080c1c04110045a2240115649103001d0007101280c042c2500c20780200322168059410014140f0070b00f440c1c904180705014100200e54a803091f0324181c0035000352504d20b2000c001c8115441100d015031900c0c030550b9007034114418601002d0710600c02c1410200402c003103030340041c102d61103a4 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 234328911 1250 234327661 234327673
    0xb040e0c0a0f0f02161d060d3c0812010b0a050301090e0a0c1710181b1e0320010f180b04080606030c030304030c03150e0a050114070905030c0d030e030303010303030e 73
    0x4011310220b0400490f000b8840727217890703801072451b90b264694284110344003020301075044c443c10202c0c4402400c3c0c01081d0f80d00d141c0000c2e0321000411100950f4010890889070625180c0a418018a00d02046c062607000c85e486400c2d24100b0a07081001c0501e544d003000c02015000d541d038a80c2c0107100f20703032402044603018200069950600600c100d102569070040c545070104000c0e0b4500211540f00040d0080b661042130003c907010710203100c408062101402405641419800c046002400b003d8550401180f803a50381c002c00c0c2d80c004002006204642440c1410301c0c0c4101c05030f0700f2094580c00c008074000300460f001401c0304000680f24011074080e030546500c948a0400e00d0349074891400040d0048103023880400010300151b80d200d03548045090009419506e010940342400090702c1c041e19641c2d100d9a0052488a40320709a50300b2000318200160040d00e0702000c40d0711120a1011184111040041c10007411301580c0e0081d500c1070001d081d00e0b620341c0c4a00e000b400816200c0310307554040c07040d1 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 234330161 1250 234328911 234328921
    0x80310180f0506060c030d0f020c07090203040b0a0605030a0b040627020a0b0f0f070f0b0a0c031b020d12090b2d25020c0a0b040e0c0a0f0f02161d 64
    0x1a02218800716170600518944680d100d40034000d0042a6082c0d280d19070f00b04071100c04008280100d1000d440b600c40f0150342ca04040c180040348090182600c081149403110400c03056800241c0c007400151300c4007503040715030344070700309030004080c1850b40e0b111071102c0100004207295140e101c0005680700311181c00d041c680ba070380745912900407160295900c440030024603007070380b07544001781c4400d600c035000c604150101951100c88481c03050304d80810690f203852102a006800d401411254121203400340c00b401041a0b00a6454942000b0302041c01444680006000a00d801c070b0849180c012011859030f041c00e80134083c802c2c200c02e0a25040d842056283c41407994038500d103030300401045002d00e00129030304036003c00d0108205c00c07803820351060348040001922858810310060a00e40d440e07030b0715949000840410088010030041a46000b00001c283c441e8002c11301003034003030b1a0b18207003c000c80794010691070304a040f0b01d03d20b443d034a45c1f0381c00a046504070040800440000c1c020140030303150 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 234331411 1250 234330161 234330169
    0x260c010207031b11013014060d02031c0309060203010e0603060702030403050d050a1110020c07050123030c0706090803040204060501171801061208090f01020d0c080310180f0506 78
    0x140f500103200f4035030308a01c0c0d01c241d84200003007095038a0610000300d585034440d19000f8403604000c05000801d03110b403142c40f0300a007400ca64513880716007501c00b9080681e0b580d0004c0c0e140d5014182034440070f1a869280240309109502280f6240d512070701c02c5589507100c100702403042408440d00d5200344108800622243c0c408002d9601b180e900000401d40c01c40302c504103817400d40010401c01e0800a01c084c826040c900b00f007041c00c4019502407401a07407400100a00c5080000c2504564188a0160901c03a80d490002202c0701c003221011180320f84075100c503c41a080d13845104000f40449042055842c248002d101c019030080e4822202042203d603200e0043d0b07450200385403040c644c3c100b4040010401d070940048540420208000000d09a4941c805110441c90700d038001c1d51a810089412030039414090b0425120302003d000820341000c4120004ac00720b1001c00004140c40c10210100308410a02e00401c03026001450100011400000b001c2004020b030621520000707040070701046450034 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 234332661 1250 234331411 234331457
    0xc0c081c060b1602040903050d05151005120604090311030304060f061505070f0503040914010e09030c190503041203120b01050c0a26030f040501050c1303260c01020703 74
    0x85074101c8a190f110ba580800006085034a01030341807110402115a070030140d8400c0c18403608a0742801c82c07132800d40c081444402c482c030005544c01e0203010000c00540038071213413504c3e51000080304e010619120a28003120b034024400140c89480c80084144000c00603107800ca00c3c00191014400c020ba66914036444840560052100011490403c108004603007400c0394003000c0c0780144212440c2c0782c1e076450307403000f11008040754054900c00c82c001402280e001d10b4100d0340003c181d40040d4241038101184030b45451403040903906001402c00210100402402554010458004003010315001821302420050741d442d83c0084452608641c4402d542c05041a04e4100b5241d00040032070103800d03903609854603840500000c2d0240404562405994aa0001c521440e0303140b010785000d042c41c1c45c1550a44e40301902a040088043c4485000da40c0c0000c4a034080301d0b00940319a62030050055049526900741354598024100096020000365054004080b010301c41d64903409008140307104111104 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 234333911 1250 234332661 234332677
    0xe222102031908180f0102120604050105100c05070f120501150608070e0a09090f03110a080306010f03150f14090c0426150403030b0316090c0c081c060b 67
    0x4001c4403a944401d0344076003c080d501c1455031180c04644108032184500d0000210442262690006042480100c16001042d000a4107840a03c02ca505240021308d10911b180c40200130490100310202c140042080690000d142100e808900152903050302101c290305410165401d42c2003012042d00d501448501d8004c0f540726595503e260346038010304481885190700c3c2e007a8004180000841c040c42a48216040180300c3e6012030141c00141c900608181419800c2c00150340295809402191540741120b80c03180302440c14034000b02c41603805400520490710103c5010000c5d490100300e19008200c100241c43c0407625141414070f0f01020070130000701c1120f983c03000a2003480704000e07400c11100c88800e002003d00c07088607800c602400f403900d170980184464824040030300a21083c150944902d02c41c0c44400e401070084007580149080100b10684284440e10356900310110b440d500c10409900d4555120011503500c1841c100c0f50150034440802003040c03903183c0900052181e602c0c5049500a03 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 234335161 1250 234333911 234333937
    0x11d1605040c110105010803070c0e0f0a11070501090c030615060203040506090102031204082101030803070804052112010e010f0e22200108060a0e22210203 69
    0x218202030900c40a0103055100e401400f050071681040c5003000c0c05280d01070308610000759180c032400c0c1030644c0a4925944502c50902d1450240143d481c0c0e80c5060380e038412200100881d2103941c807420101c9901c90158094a50352825038030004208200c041c000859001d884140103420122020340e400300c0c070314418400564401c0004001b81d0034000b01a102215050040c0c03030901c0046096502200d00c100c1d821070380500c0000354092921013a10040d0041030242c0b80805d003941c116540c0c0c034401e00c006080c42091042004c002070410004119000c0c0c0302074407138030401e40070940029101c8590406034822200e400b1030000801c0b148403080d4082e0403503403100d400002003858a140140450383c0582402c1c0307021001120040d00d5034840700c0c1c000c0c5941c070508224560859603c0e10580700040060300c581003140400c14040c0e203581d4140301000340c0b04142401400c90b212890042c40c0218070803280c00043c1071090700c1740c040c8004580c0b00c90507500c090040c1c0d401e14009140c220b0f2a44148441c41c410 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 234336411 1250 234335161 234335203
    0xe010c080601300c08010303141606150b04060c050105060f03060f0c13180b0a061215090c0c05060c031b090102030d0e0609010f0e0a02150d0905011d 66
    0x2c1803030112148440c5401d45000034000340020b02c03080c05682021308500003254084004104159102c1612802541211038041c20700e9108600c940900300b50709006003c050f282d01c000d001e2502d11030040f40042510280055a840d03a51030060501c0728403100030340f00ca510b06000504079007800c8100322030310030006000e001950b6401c2c0a1542c04107018010b44503803234052261341014980700030018081d1440d280110444a14001040b056075409510207005110b105020040e640c2c0040e004182500251030204108414100004070102ca60780010390f05c9007491020481c154000c0b00c1802d50718010350a96a4540d26030601480521050780e0700c5165006c0382c14007914081201c1c001e088005414030649103003e11743c4514070192000c14503a002150802c00601100c08024030a88038510707031299007032044051510100c0d8032030903e940c0c0a0b0049c03440d030130180300c100200c1d812074062401c01b400c00c000b80202030038424001c000000c8803900803c3c0001d140303402010001440856100b50340070141c5 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 234337661 1250 234336411 234336437
    0x20306010b0309070918020907020c1302180604090207120504140609040905100f0501081603021203120a0c020c0411030703090c080a080d0c050f0d24090e010c080601 73
    0x2641c4010504101c50082020104021505001b00710300c0b2401310400c00300803601030042041c10307030001d00f030b100175984609406649a02c0d4101c001c02c49060f00800140c0340c0d4081d421035203100244080299001100040c042070455595000e0f205060180f000555030000040041d1f0f2140700303c1c0a00405803481d480011842c0ca4030b00c00510400101810101b0b1900c0b581d0760741e134078000d02583c40300c9066072580c22604103c01580301300ba004000b50320042000390700180c8800c208260500019002c0c081e02e68407070490f0307641001220092440c01d0528034462038041544001403031006141d100500a00820701450718081c040d1124242c1c214401e90300d951035000b8143c00030003410400310355140703420400180f6200700f84070092149010300e50095841c4031806091044a4110542c881441000d2200004407030350ba03400d0358420078900500140e00382c041001c0d80400c0310301441400341c0940c8801e000c2044c00f000d800146000e12450001d02c43c1e481051800c1c0c800c1c1000320703541c60005075280695030f = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 234338911 1250 234337661 234337679
    0x16090c050405061c11070609020102010b04230a0617030c06100501080606030604060503120909060a0e01170a0609060e060a1b0c020409050312060a08060405060f04061b0905011b02030601 82
    0x300740300d52800000f4002803800402002c0d904130000c07d58509995006032020b651302802901a224000c41e0204001241d500202d040059659200d21465480400190b02e08080f50301400c06480084120204500418a203641d26031001c2c0025099009880100b0805500030415000fa0340b0140c50f00401c070340d211828048030b5080200030307039400345d151500000d9585040c85400c00c440c160546081d642c1c4440b02c280811010003400003030091450b000c0c01c100341400520010f06507555240e034031030b00300306070149140341120400300603064030300d400500c00c10006194030541504030400140d13800c542c0e80c040307804211039030025820240b0001c2090102d44030f00c80c0c011007003001e10051002495058035155603103550451766080d40042a1101032060302c1c60581c4140c0020301c0034000404451a140e0f640c0b980700d10b00540142c0c0c04021400100c0c1c1041035641198180030312010045007940c13909400140022928070505010a1014202c103032414010006c041280c4d4001c1c000b858039034a045542 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 234340161 1250 234338911 234338947
    0x11a0a0b040f030f021c1b141c02010908120d0b04021903050a020d0f050403021219080402010c0218060103061203080c090609060408010b040c0c0b04020d02060c16090c05040506 78
    0x103d134085604401b810007044c1c40c001c082c1c80f05024030106401c1e0740c51240c004460b05000e4011500c0107400d40314aa06950764903c0f92551301c06144400310b00c0e4a441c2c40161010200ba4200000d1030182e0211510140c59042c0a0207524824400900c141c000d0a02448101c1c402c1038001d06120350590365105805002c0e0300700e9600704080000052405807000b0040007111200c01c03034808041d84400501c0140360f81004180110820500d005180010402004885904040e9044148110840003506580c014101e80c0980c1e80c001c1c2c0305508008900c150301c10000d408a62050100b45014408281ca80320740b0300d4404000e034552220070840c2c0b650200303d4003036004045406e6220804000c1c04010b610b881000d0401008043c1c00894229202c904100c191100d4007400c20030040c2c60514600807428903029250026010b644c0328143c00d04a0011070194451a0000009486880603089610105042c1e4508544441c1d0040011461b480c000316220300c545e214059103e002440402040c3d1003401d01d07 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 234341411 1250 234340161 234340163
    0x10305071e091a040503073302071a0316080106050703140c070e0a110f07121107060c05070b0c06160306050904060b0f0909070603150305011a0a0b040f030f 69
    0x3100b00360310364544254544260841d10480e010720081070400c0325041c1044408050308050440348030311000300081014103654a009000e290b0103908080d12614003c0c01044d0103041041803403031114400000701c1c042680240d449440000d11000d40425480c842d0300400c0c140c8038a562180d203420309079142100d5449144000741c101410400140003d4042044558001e009086002d100d0313181034240c600868041260703200310080100002c9070000300050850b0300c19030b84150708013012220041c04451070320958245440701c0c41010404181240c1010302a96440e100700304072070405848403404010b6016000c645081076002c2070104e181500da04c0c182982c8006289800220a41d8030b02c002007024200b84e40c2aa445556800561035600b045000c0300603401c8151904c03074143c14513034410341e80e030605c6200d1801055550404100192041d0009034001d613009070081c0100c049611081e051085241e90302c9129510403000080c0b0702c1c010406442c203c032602c8007550000d900c0c580b01c08090115200c0c0c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 234342661 1250 234341411 234341417
    0x30103120c0308061924110115030204050a0207060509010506120c0f0909030c06010b1306180501140f0d02041e0e0c030c1210080f0304050a05120c060c0d02010b010305071e 76
    0x30201b003001000104916800410056000d60b4861a2002d012804540311114140c1d051002003100740b2002e24015041303a50640d000166542c4e100d40850090080e91401400f00341801d041c80b00000c1c0542040f4042c104c00c4410b8030003400380145840e650030f04988996005082d04555074450310300303c045183d01003066000e40b4a03208403087c1007030414070240c10422410380041041001c9915005803030010305840d00300031900c01038803002002d9a144134403810b4100300814040c2c181d054007400690302800000f50509880b02d00704061840a90041d009000d100d0543c1c4055000c150500201442212040b140b41580c6448620041c2d210307a10082000c9240380c1c040003025001d001280506120b611a2441022100c1c00e00d00294205031000440062a500500007804241d440308003020840d0002c03921600141d6001e40c2d40d50400450740300c0300350b1208011690500085001c60707445000310140d4002c0100e121504015004c4a00644801002814201c282c809007058a2811140d0380d03000c0c1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 234343911 1250 234342661 234342709
    0x105040509011b09060e090609041502040519090b06090d0803090a0c030f020a09151e0b040312090524091201060b0d0f020906071b03050a08030103120c030806 70
    0x210121200e0911045094006044e80c0070400005900c4141201c03070310000c0f25903041d1400c0040008034441030290025004220717581c0c91500e130308080d074101d40c01881c001d008802d09584182c8007000e40c080b00c0c82010155824010515200e1400f07104440d6034042c01031900d41444426181c000031500001c0050340c02e4410641c2c5da00210b814613100074001d52103808841800489841400020304169000080544c249140d071003100040028413070986030304440001e099038030714203041d034420281d07072005026140c00200407007400f01003106454504000c2d2543c8207016911014000041d020300d0540407102c0c4000a504000d07580701008103100880100100d0110b991040c0c42800c403101c5600c0b10801442c0011860b400c6415405120040b03513040a0850501804c0d0000c1102c500c0751030801040d121074862880ca511600c4a0900c001c1d42e007100880e4440300880c175000d03480750300a0105441846401500e0036905118890b081000382d41684d075000d5075240c1030140440303541c0000c40c900d410f407001 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 234345161 1250 234343911 234343931
    0x6060302060d0f0f0e030d11070f2f0306130303020d140916050f0907050c0f030406030b240c0106030215250c030b04080c06070e010e18010504050901 66
    0x70401401d80115140c0001800c00810500d007000c8a001841103420345090080e00b03500c121000c02620f4240401d0080815a450382028480040c4113110004000c0710f1000a000107200003840204084c80110a083d40000c00c48403e205520071500c101503816408200050020310f9400c00f00c01c4814424140542499010003124060b200161215a0400c11540c10845081000c10103034101007968103403603a68604000100e4100d042149090b4003c0c041b900110345000c2c0308008880045880ca82600c0040c2d611a0710303540c89500034860200040d083c403444e046e07030307291844034144c5801130420b560100c10340707680b01c40c1d032503402c410303200a4555a142d50020143c1c8412081e05000045c1d02189550303048030007144411640351012100c0e24900240814000800061004007900e40254124080d650759281c240d1041c0b207140306030017543c000e40050010789500500c0b50303d010b80d8240c03a2440d860442106000102c903011a4a078004151000100083e0416501032030300007401200104842c448 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 234346411 1250 234345161 234345169
    0xc030f01150e040e1b06120f090307020a0f0e240d080910030f0501091103040312090f050c03060f0c0d020c010905070e011e0e0c0a0e0a08341206060302 67
    0x40b1a102c6459900a0b480360351001020060080405c0811100c0600344075410f60f031140e01c0e03032000700600100c000345804641070742010419030b2800c4d0350003080d901c0c803030781c8800310f901d004041341c810082c3d109020750108100400c018040e8519000403034080400c40054420452110102030081d94840310400c1210507a880d500c003699030f03a48043e200801d0001601c020b0303404840d41640800c0c2481e10304040589030301c406004890b04150989000c4580380c0320036580d0002001c40240c002c04003004a022101048000b09210350201401c8054460543d51f400c412258103c007201c0d41c0c2da03404000c000e83d20300044507901070030801c0340c0b282c000a481031650742c0d414a0a882904518110f400c01001040815807018510005500d21902c40324a0751602d10014a96140504070103480c080c0400c55100c500d1044644559a0310014090348541d03594984490311600000086005c2c06034413035440e02c0390080000012089603400b1507010025180c0314500840c000072100c04c4464548400001000d656 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 234347661 1250 234346411 234346421
    0x10e12010c030c0206061221090a03201f0c05071d04021309030f03020d0b090711150c0403030305180307050318010e0906060a120f140c030f01150e04 66
    0x39200083c205042e9000a03140010080c212031044c1d030003400321102050040390043c10b4055023440801044501c4014400c0e078000c1901894002640520020900c070124500c1046c0c0180c81501280400350b4109201e00303100c9004072180c00040507180c85540c140b00d403000d000321138002d0007511403090301c40c04241c2c0ba000440c4610004440303100144015032401c2404070382540d800c52001c010002107582e018045210285800003031507030102d1042200da01c070707800c8400603040051000050f071070580d201500072610000011074a00c201c400040300c10502075040750003005909180780c100b6245039002c6000d00310061116540c2210451840c41c0d117072080015207105440748000d540c43c0c081d0f42103040515455405824100800300420000d6900d4a071042038102a05503101551a4565041562410030480c12080d00341d160001041032845585c1c00452019070301017003002039450b5141240c500b03010560700c0b007a0076000b0310f0040190b035246080c1ea1500900d10700704031004540307400008040324 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 234348911 1250 234347661 234347681
    0x509130b070c02030102121806092d01020d0903140408030405060a031503080408010f1b120b06070b0f0a0509100c0201060308041806060201020301080a06090f170409060806060f010e1201 82
    0x1301f6064240074151ba00c6035903101403c40810010165450407a4009a5400400503014200d81c80394000d03906480034491a0801028104025555111410744900c000c217011a070940015202c4100c035034110501904440480b50108000c0d17040900380401c11a40307034445100c803405d05a4507514840e071f407805100b01d44001c0d4003c880107901c4500d03260f5220700b520342031003407074522510300b82c0c20100c010300c151070124001545240c000c414603600d070100d000400300c070003100340d2040e0086680030401940b50503143c03203192160001462900d40c010040706441003502c204040d5004124142c000e0074295100c42078491040c4004111242d89403981c081d0740e4065003200045800100441c1c0350707410b482c0190380040c072151000314a15850000c03916100c0341e849000404541e110007552060014160700c080d1120b0300035080e40465004800d44029030342c010310607400380504011000501c0d00d000b0485510401d0050440c0036141c155800440d0706106100843d40d00510800344070b40c2e000d0092142c2400c0f9 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 234350161 1250 234348911 234348937
    0x3181902061b0607050c0f030403020a1502010906060f0513090302030406050c030403150f0c080108060109020c07090507020304030203070807051f12050702030310080715081911030a060509130b070c02030102 91
    0x41d000004100b400d000e0880c81f12552a40f003080b003080103848080308101201d00703103044083c4201109078101c0c0500302c00c038405030a003803d0039030101d860344400c10a101104d81c03c0720040b46000c03c9900c0d200640f0040003001d400b52300180000c0114a005030300800d81105503400352803400d522560380032060394105102c01c078200d5641c4007111201c221882414a40c00039420b050885624106d0b00f0360307035000140a00101140c010170341e80d07840f00c0c041051070b0203440c2c00e5000703001c3c0703240030f58000395aa0030501c400d0b4071a00c207440001071100400b2460001340c680c05048010182c070001f03036041025103007540140402c0601196500781c11198030175580100041c1d8080c60740e0341890824801d0048441d00b2600058100310300801c42c203402c186030b00c04018410304000a1a43e51212042000d00910710702d440a40c7c00c01c0160b05041d031000000754440c0d101040e003040011746413020b225035414100c0f0482050b403641c87e091800304400043c05035000720180380645807081c280c3d010a0a90300801c20302c00c11 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 234351411 1250 234350161 234350167
    0x50f0d1709010e0604060c030e1c08240d03050708070c0314030406080f070c0c090c03050a091505280f050105040221060112090803181902061b060705 66
    0x81900211215900594003070000c0c801000c3d030014850300c60101a00040000ba0b4828038580c00394040c3d0001814401690240c0d200200058030740440c5c05c88220700301002a4a0500203496010760b038070314005503612007400000603c080410f1101076950170745c0a8043c080d040c08414006207064004082c1c6511801d051035156240d440e200d049600a41004902600184018860194000c0c0c056078880b061440d11246929a240107540f80056024040d06400d1b0b0003501041c140e52035000004044241e9508020300ea9a400216049030080f4400800c0044948a0302d4500c040942050b074100c2001141c1540c04081c5200401d400e60450b480d00214544540703100e88101e086201d0b541c0105800d0380e05518240d20402d0200c1a003082112401d254400c40007c540c4591003130250305060f404400040203101c0380340c2005160740d0001c5494402c950710740030b540c0d1005030b03004c902801d0103540c4505884031030a8517400c00c41c41d500104c612601c2402603e01802010070100b0409000f80b4581c1c0b10943c0d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 234352517 1106 234351411 234351437
    0x1c051c1a030703080a09061d060c0c061908010b160b0a0e010c09050f0d020105030c0c0307020402131a030402101d0a0e01050f010206040c060507050f0d 67
    0x50540b02d006408800c0121103801030880d6101500d49030151030f50ba017004c89894070300803000031a051140040c0721703050401102402044001030151140741818201080b1035401c506038181038440c0200e0801203507900709000b64058a107000c0c60a14014500c0207250709803800100c010220203040001030a2000c66601074000c0102c1d90009001c0f5081c901c1000740003804a00a83e07210328004e00030b02ca85840c00804d8030b0340603541a1622030031907070340d1441c0003038981001c400c1040c580020048400180c2d40c5100402e20b8400c81c8502400e01410003040841c855586001021818010400d0101603604e108107400311407203600d4503940c1510219520303828088024400350700110182004151030301100c001505075101070b05c1b000c01115005004a03581c2005550142100744081c1092002038402c0300103114450140c02100c072454008440c0c2450150380710002000142e00110030f00c = true := by decide +kernel

theorem cover : BRFrame.Cov 234172661 234352517 := by
  have h0 := BRFrame.cov_init 234172661
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234172661 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 234172661 ≤ n) (h2 : n < 234352517) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
