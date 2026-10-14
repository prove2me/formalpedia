-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1724
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:26:35.91098+00:00
-- url     : https://prove2.me/submissions/c189151c-a0de-49d2-9e7f-a9eb2af54417

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 309892086 ≤ n < 310071942 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 309893336 1250 309892086 309892117
    0x40303051c0b1503150a03151d0d2c21190602133003030e0f0d030513150f020912030a09091404030c030504090f020d051605 55
    0x705007420895104440d016002030001c012100c42100782a0725800542e414440381c3c610395104002840c1541e218011294410400724500780603101e45001450320904019003844160740404081c50103100321403420303010b030310b030030209000024082004000e09203000e81801c210b40701c040d40d01e6540da407009001005089182d5100820305040c04d08005038403800c020354070b040030001d03802c12100d50041c00c0c00d14020b00004c0903103a41d410340078090078107003ca000603420450940b8002514244100d51010f400b80c18041004000c0700a02c80c901144100652480d8112998080140f985806403a070401c00322405001800c01e80d442e07400c481c2c65203000e5840811b03581c111090201545405079503811000400b003807403100c10040500e4503540011010b1000909010300440c02c1354851040d00081c0300309001500069072581e0f001d44011915100039024064144000504000d080c011007035503403500740c3d0242c2c507902d00b051079078150381c0041c0000a400501501100440354003070140c400c46441341c940c8 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 309894586 1250 309893336 309893377
    0xb0708011d07111516020604020a030303110708040b0306104401061805030a030e0613080f0a020a120b07050a05040506130e1509060d051207120f020304030305 70
    0x150340001c3c1005001c0520f00820001202d43c1007050b03070071845071810f0a01c0da614202c0448080387c85500c00c890096002c02c01078010310101e48a41d00007080e030b04500b8015840d144440c1c440750f165801c06e51051030307001800810020103090646034074003191050f04002d00c45484040300c81c40107288e02801c010514031021407a050039105001e20310010302141180f80143c0d44c591380c0040c41c6011380652108624514000000d0900380003070f041a100ea0103546d00c0415041c11402c20940754401c0075501c100c0e056010b07010540c03d4085c829102420840c000621070600644144000d0b00202c4c1c0c4001140803840d60060301045ca030b008400e5110304036250140d56840300350810b40c4c0034052504020f40088010500c1d8078000303003c02e1510261108001102ca17259103a0b141d0f400401590a49541c1040481010a002c1e007003400010550f03c2c400d406035070740324407030410400c415000014280d40f00900285c140000c02d0300410590203c094510140d450705041da14040c082e032059814010b100c8103000d00 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 309895836 1250 309894586 309894601
    0x60901031b021c090803071707051e0c0108040f0204020c0a0f0b0a060e04020f060a0201020f030a06090b062104030c051c080a020a09150507080403030c0b0708011d 72
    0x1c2004024450740d588115100c6001000350368000b10a0b040348100d180400100040b8003038000c0b1800c480c1c0400045180c050250b030387d42d01c400f907980301c4441c04000910451001034402e00010025030340c60303040ca00000f01c50210305440d0143e40b440c0c00e41482591801d200110b0104080e5081e540c1d01a5405030342c44241c048400e1810003a080e001c0d01da44240313601c42081007000364950303015480800b000e1040f6030721400745901d09076040d60020340c032038100c4603018024100704c8094000d801c8a8000181441890352100d04103500c00c0740d00b10543c5541d01800e200c08001c5d4070810000200540d8002e041424000c0f4007100440f01840807152902e440700020101442015941c1c40302e0750201c00e603006d400c1101001034601d103a007010301c1c01180100002410742d10720380c4251810f280e00303603403040059450480c03070011010f4200d0511040100802c200740c0815100c03001080110310a0b03590182d241d8081c203050181300000b50200b03041140d00c100410034100041d00650b881d00c00c40305081240e403120b92 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 309897086 1250 309895836 309895841
    0xa1125020d0506130c0e0613090c0b041e0801021201090e010b040e0309010f0f02030d0f09051507082202121501060903050c122503080f0307030b0a0f0506090103 71
    0x78000b07000b84520001c029a80004030074800c5000c0c400d83c45042c44a1b100c90a2801c03401d070403240c4a07009016040b0390800caa80d240c12901c1e855009040c810011915100b4013561944a50024000c40c0101c02d1038100390200c0b060700000400882000f1414a01c0090800048400c18411100d80b151201e054800c2c140d400c0d44407802241c3d0050080040c1c808400f54a030716500003000850202d4001407420344568041c0c50900d4203003860364003851404003442c420500514924442c001010380c2c030a854000114208615003610140307901c007011300d1500440040400c01c008056070b00c07400f000546500300d512110401222035a0454084a4100b0203180c0c251030145064171701c1c840c1084a10000503400d401900391000d481c0203009841d0890201014841c4c000e5100110040542c04025610704102c119190001108142090710070210f0303690f12100c103542c0049007250060000001401300054142c23294108264050310460b00c16881c0501c000f007076181030b12410b801784c0000201d2540580c070a6 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 309898336 1250 309897086 309897109
    0xc08070c171812010501030b0c0a0e0901090608120c070317090901030b01080708011b030b0111011517010e060f06010c02040501032105040e070e010909050703050a112502 75
    0x7401698840d281d092018000034698009140112500280c0d120043d406000c0c141c10780360096411684e61f151440004010386c0032030b00600401044c0d000490403583c2d03800034607000b44404000464900d08210342d1609060014020042c184020010b40000c1c0c500460b40004a94021603038040041000e500502c5601c141013100b980b07e075104002208105070b015816059900402c2103e8480b512214880e00300c078010050108689407030800500c41d940700340c001c0030803100c040c513150120140c000c00c41c0f42034403410100f03000f0409194005000c0340012201c0c00e006103118100a0003900c001f07201705a11144007406c0b0307c1014200b0400107406034062915415030310f074080c0041180f581d6030b040c4941814101450800c200204003140301300b0701d1140040c1c905076440380e0200300e0581c0743c7c14015211004201e150341e06200400c000020039024034861980300383e4513070310045110300c0d1611002c02160b141c100b60320142d42c01400340c00821886c11140354614004001020350400c01070001440700c1540 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 309899586 1250 309898336 309898373
    0xf2115040c030b12070311061204060209150a02070e070e060706050702010b0a0806010305120f0a1112220609150e120a0f0b0c0405010e09270705130c08070c 69
    0x40504014484d900019003030122401080252912001c0408100341072280c4458000517071001b60104002c034000354001d0a2920005080e141107100890a01c50160001079211016811442c0708011240e12100496404100b03441e10711001502680090014000c403a00640740d165a0b50000c0c4d0514001d41c03045600700c0d00100328007512030b074440c00c03c1d640f200d007404111013602070341c86201c00e0851100269107003002d50140e981e0915070140c13412140030580380c0481310107100b0b00c10100411050f0340010110751000b440d0b6018400d45920891941d503006900640411180102c01c0000c21350382c0c406041c0c2c10440385446014405410001111501080201d9101d0300988090704100f10200f1482105184102410001a81d80050a00003801507210b0b09001c2201c65004040d945044c1d241c4075400034a40300120420552007003c01807051000e0b00580803680411824892450450010712189013202d009000403210460000d043c1d00707001c0c011000740000070039440100030a407805400c4094a = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 309900836 1250 309899586 309899599
    0x605030304080304061101090201051204060b0a090203060f0909101503150b240405060f070501060f060e12190c0317040512010c0c150e030f2115040c030b 68
    0x8940c40ca082c3c4992042c403451000c2206581400e900ba4010701035180c0464058580700c0c2000e1408082a4690700000c2040b02d500c0d40c0c0340340c1c80440c3ea03a4050b5510280c100c03540c0050304d80c5020402d02030103240520603544540340d038100708034408600080c0c5120702a400314001c5443c20f040e60340c2c0da950030f1950b00f00400485130800f4000790214164084850080300726085c903542414459000740018141c1c3d01c545080d0002c100900546c14802c0043c9041c03442d06c5030941c03400c100c0b501c80c01d003120810340003115003041048082107815441903240032400d3b0304465407a008c158950f003959403070443d4401d4070784841380c02c1c07a41c4062240012030040190340202c0304111001600198122990260040d1441030101c00d88014a12a0510a1501805035922100c61010f401e4503a0307640d20001d640140d0500780c0b6041c4645455102f480500200103d122445848006800006561403410800000c8411007202000aa01c0503480703005007010088d0b03400140c4401221086002d80981c10003180c00c0745 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 309902086 1250 309900836 309900839
    0x50702030105130303051312030b010e04020c06060102010f14160c0b1e070c03080604050613021620060315030a061a030d020d09180b1009180204270605030304 70
    0x108103c8a480f00d54840c0e94100300d5503072181c50b56401d11040282c00380c4080120382c00030101c14080d60000442c00814140303d00c01080c038a002400b40c0e4444002240c040d000901030011558090240b400400b940590500801c0202201410850801089a00101614500d01c16002d020f044400e070200d41000841000b272400b03155001c400044001003c1c95201c1540005103003505c92150b00c80215856510301e1001c0d241c03001048050003020340640d03400b03203018090f00c07815147c40c8002e00c0590b0441800f01064042d60814111480007804003c0c1703082c004c00a200c0e4299158402c46c0c1e4003a0045800c10b03111080400424a031803082500144200c1c506a0124440e901a1a903411700010840c100d41c610842040700b00d072240c001081c200d0109255013414458109112503030076144da0304540000b00d04a044001500c4c0e010000c144c031011800f030440a00448102883d078840d04410500b05605c0c0518100001c07880c4441326a000400b1880700041428601290300f00074000c200060850707440d103 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 309903336 1250 309902086 309902101
    0xf0e03030115020d050405040b13050a1a06040503072112050c1c0f050a050f1803100c08040209040204020c01091b050a080c2403070c03030507020a150c050702030105 73
    0x30350081c0a140c1d00c0b111400d482c801280d00c005038024030112551344660502d4a0401800042d00310010015481822240e06101e2204e031445410300c20584002c000c130b0f000e0f40c003038500212218640c56250040d181003000384a9603c00103241800c40703e00c21201854441c4204011142e0725001c04018240102c0000b43d6103020b0f4048003402420101d070060305c0c000316030070040078803a04c1401010b401281020100c21800c034010300141c200c6100c0760806a1800290b001e0b03101c2954400780d084640400054489001801e08000e2024426141c0004107e140c010040150440200600007445400010002800c5480d2901580c00401d90708000380b014800c01d141c4845141901c02d410301e200e12043c4000101854905000411108114064101c1d6441802848486c2c00c1c910030040c0f084204840041040c035140c801180718086076079514820f103195180090548401400d18004c55120780307040c0021544d016114500c015100d4000580a41c030342c002500c0600481002a605500e00740c1002403d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 309904586 1250 309903336 309903343
    0x30406020c040609020702030709050c07050f010518030f030114010c12080601030b0d1515030b0403111c0e0112061a0d05090106150305070201090212100506060301060c0201120f0e 79
    0x801038121014040305444d85110750403405164006541548045c100300003800031988400c0e00181c0100f80e8070b282c901c2948030b0a2614010f0301400d00c00d69560020000e5000c0a1f9807140079100208024514084d0307c138002c5001404180101c1c251000d21007101e000c540e000d10000c0710f08652154000b0001d14400340301400030f59048500b140402c3c100580c440062a0208900034090f61001070071290a62648000009010680c20f56144100e82c1c0c1d008408150130001d21446140b080d40d400c02d030381c0248001035040a00085540602c2c1400c00c000e0141d0715081b0390080a407080a2034040c0000f948491110040c4c4034540c024502d42ca48070b2200303000b5890a0004164519031400103000310b807204200c1c94220303849413158203d841102614294224801d401c01504030300903100211b2a5203540d000544902d071400a5400a030384a130300740c11085840750050303035403148007141e18a0a540c58500d0140c11079400540c000e0401c0f00310400f403401501d580c2e225010002d0106c2e010800718642d0800c4d80d54 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 309905836 1250 309904586 309904603
    0x103050607031a0a0b070204020f0403050609120301050109050f01090b0415030e150601111c050a030506010206040206091504091107140a171b0105090c0a170d140c03040602 76
    0x908102000f043d0f0404040200704840024042d050180c1c5010f00207a010b40281100302e0b80203400700071003d001e030804400341000d140600d01400c01414030022003850101182d41107541c221042c8010000781e03030070035220000c50b941912030000031010200100ca900c0c0154002194600f00030030b01180fa450540c5407200703000901e031800c12015082c00700303095a8080d0f079580e08903011554000101a544201d08152074250944210340300301d0340302400c1c040c00c4400d5990b0003001401c04102c032045698940141c9801500030300203032115003880d4012510a1141000b25800760300c466042c071100b1441c4004440003007401040400c0100b0612400c0145640b04280954000502c40c1e0421021324001c590b02042d1179110205241541544202414541245030010b01d02c0c401c044c00c0b12005203007802024811000308002d4035444014508001c0d0001058000340714201d021040035403000800541000c0b610082d0038903585185101c45003180700c3c82106500d44580c04041000210550009940e00 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 309907086 1250 309905836 309905851
    0x4020a0315080607140f0426030a020a0308010e062404170715020304080c0409020d05030a1709010c021005040c050a0e040c09020a120c090f0f050406080d230d0501030506 75
    0x2c0c3c400c05043d8000190180b06c2d0084a6004104010030588000710101300c0e2240401c4a80910500000c1c078440c01c64004041460242e04200000010160b2102c44a400740c20000c4404005051200224100ca04110285409004112031001891a400c4107440013002c60a92204c4070403046c01c06030380c54001511846851450740300031440c42d18008001d030307420381e0911001440034040d04401c10010b0f0210b050b040e600311080c1d4007810007045040c001000c4032a03464441c003039081002c0703040034040c3c0d10082030902d09914007101040580c4d4049840088031400c1071012515071518107107840c10b043c04d5800240e000c9030b0344c3c2c00007403164521500148100c0c0070b84010000b55544095120a9101e40034040001442007150000b18a10319444441101d105c1d04e0140200b42e103408410111107020380200a8641c40d189080003189802d0103800080c00d03000000d800c01c0150b6401c0603210810b1444c400b00456544c0100d607500100b0300041c0d40054a013840103000950356410a55103460702550b003407 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 309908336 1250 309907086 309907097
    0x20c040609090503070b07091a07020f0a03050616050d020309010207051519020702060d02040e220b010e040309050603090c030c0d0218070c050a060c021b13110403053c0c04020a0315080607 83
    0x1f0b819441c00b000118122500323f40a403215550741408030300c15400048600042c000705000301011004d85101644c840e68807034000695a50041c1441071808051081d0704000708456003c00090401d07001e540c0f510361002040268890589100044460080d04c10074019644017140002e4103c62101c4074a000714100070a16269810080142d00c0315805108058100d1094000410250084030b5180380d000703000345813000c005a02c07080029469030040c0d51092941c0e00051065980c0d00e414820003c0c20001100d030060425400e074082a00046025107058080710b079100007a42c0140200d50403442943e0250599440e04401d282041c0140203d00c2c8560040c86131500c000004400c00004902c1d821008082240f03000d05400e02401400701c40031003204003107041c800040052000c011010783c00003402da40b4851602031800c60143c0e8210030074030782c0c0345041003400503006ea00d02007030804481c40140c402581d504155407040c2c01038598400c1d180b1000041c054009030f80a0086059400303150a95100f = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 309909586 1250 309908336 309908359
    0xf0906020d0617060105030d0e060d0e07050a06170106030c1803061a0607150b0f1203030f061c0201080c0403020d060605030c0f210c10020c040609090503070b07091a0702 75
    0xb183d84e40340240500303a0141d00c8005101100c60040c9103884c044880106400d1401c036114918106031802c044032100e050344811410312462912048240c0903100610300810104e8507110b15000d441411300c01c03001810b0b030ba039040c0c0d4181d0344030302042444030300c038501d071444101d0703803480d0140041100e604170540301001002c1d420140e1900804490b0300c0350300083c4444094401c01d22540081001564099000307446d00d5520b5407a44401e11a400341250741c90246880345800c901001040400400c0c0c070b40f0074000310b03030020109031442203488840c68080c605580304ad03543d220b07041000d1003550000b941c0305580762412810020590005401c0e160306405440140c5180424491070070300708511580c0c4440351544030b040c06030030031004003111310b8148111466614020b000c5040e212105003980010303004100a104141811b0140c00d004046c03001d01004440c00030348500d91a4001c1800040c035800342da9011605003841402c2c00e50107822100d04a82131480929054103a0f81d2241c071f402c07405035015951 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 309910836 1250 309909586 309909629
    0x1704061409090403031e0603150510050303030a0c0201021c1a010806130e19030c060506060906030408031b0d0f060509010b0f07062406110d02030901030f0906020d06 73
    0x1903551009002c0c00d020001e0311655425030207401c0002e00c3c1692540301c11a4000340c00c416000e8680114014410904041000e28a09080c0d40004202c0c080c80c9042e1901008251400000c0b02d900034454800000c10541200b0228064800c1540c0141c1c0c14000e00100ca046913125880344804002c00304400b80540c45520040d80d003808200c48555018440d0503100d030003c3d80d42d0300458454200302c401c2e10381e04081d0145203003444118040547c005070454802008204a80c4912500b0040c00c64a1904105044001444610008100078800302c40480440d9503a03c000490440740c0e4226006261900424003d0710b0003420000c80e20508a070405000040604141d100c0e02c4c1612440404180b07414541a21200150300c0241c04a8000750b4411060740001110040407007038145100a43e1501854290010810a031200c0c00d81c0007904000b42041407681c0000c2100c0c980c280030300b00481c445403811104002090585406000e25000194401061039103601403000c6e1412030242d03400c02c40110300b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 309912086 1250 309910836 309910877
    0x8040312111b100e190f1511060c0a020c1008090d1b0314161104050702061e06011403010b030a230411060c0316150c090b07050703170406 61
    0x5440750781042c10416a100c42c107201c0d208048500c0d8010b4651103000348400c4170380d202d03000e865000c090102c0c024a000c4c00502d400000005500340545440c0f07000052030080e03251203203800340030642c0080000071145d10950091048051b03004000300314078614800f00c80082c040c800100d455038040e01408880c03901540c01a8100904c407508480b0900c43c8840315a405da4600003610029803030121700788029210031012601801b000c510030b502514021100d9014001034440c064442002d41d00b00a04004004020071081d2072000c0b0170140842c41d58580318010381e1103500c0006091a9200c0000c00810030704050740046018121200c000c0100394111100c0700c4001410720560721090300c006e000714001c12a811b9000c00d401000400e09850501401100d510356808080001800030050980000388aa041419440c000c000b00f418021140090f4000b800d118190003900085180401c005050120401001307000c0e55101b00e0300c100000010300220402d0301b081c8118000511850250000e46c1d5024 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 309913336 1250 309912086 309912133
    0xb030f010e0c0603040302010b0d1104050f19050606040503030711090702070302091b090d0f0606090b0f090a0e03040816121e030c12050a120e12070804031211 70
    0x140d000d4250b000071202009460740c0f0290003501190340380c050300c80c0e8503503130000a6164240700e00c0c0b0300c0d0780f0007070312070240000e9a0008007100004a81c081c00c00840c0010710310103212511b02d107040019159903400004405002d07e8000980502c4040390403c10403a020302c0b142448003017101c4c0d0311656581d40c0c80890381e4034101d0000030b40050040c0040780161080f1104140b00740c149259043c20b00c03642e84041540030104400035100e84401001c14000c1c41410b100702c2e0003412405109011505100010600b600030020480e805480c0800014a40c0c80303041d441407481041c40000d481d6103990f5203800e0381d515640303025901d21022105800081c1c01700e003040340401c82503000d40819001408215401c1034140b500b401070b4280b0040c40c540c1340005a0745000302000540540340e0726100d0350a1400281511409001030210074582250301c0101440024034a82c0b9403c0385902560311240c07440c0820090046a000900000c002400c6244198000120050054002040303d103407101d0490140750f0803000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 309914586 1250 309913336 309913361
    0x140f0a030512070f08070821160c151505011d01090314030c06010e0a060807031110050408010c030603021017060f0109030c0b0904061d0a05180a060b030f01 69
    0x49240110002c0c00c40e4050003865002d621050449a056120a18150701068044031070540002d054144014412881ca8a0391a822030107081860300e04814110100350400034018002c103d081c0004000c0e0b40d80d290201c0380300c5008280000030016061149544250280c5804222071a4498507001038248100300c04120503529000494507549414003030307030804c140718103150204010919807003100300328040c001c0941c80b00c0301c000792824a001c082110b805802039209038024140801c080b59101144002e40401242d581d0000c3e20000c07029a81d40c0300ba07510101c038650a103507810b07503899056030000303003124002d031440c1743c0030f10f0030380402c44002829803041120614240c0125140b03080c4501101c01104040c1421061507031680c0b20741400101c543c1c4a02e0088000103602c91803414980600001000052440f0945065020080764400c070020302030100c10b6070b01c10000302c0d010401442854003805200640340c0004040c103021001d003170142011070081c421200c0c0f1100c0007105101e003280d43e044 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 309915836 1250 309914586 309914593
    0x32c07090e0d02062a0f0f180306090703050a060e01060810090b0a0513030e15131a0301080303011703071203150e13080706200705012403080901110304140f0a0305 72
    0x5020030080002d402055401b03094a4050086510828104000340181070011500c0382c60411802e04052609038010714846003034000384001c000013000040c0b03041e001c6a105c0e402003184012060503a005124942c401c600c0c900c5481c0c0c41c01c02040c281e903c1904201c1c01505244079070794480b080c0a040c0c1d5026181c10188240c80f19014002c03d10562661381d400c880113243d41d11031308900784400d0203078000b07403401c3c1c4c801da085081c03c01035103440c044014a11343c0c15940070760541d171529200a4580c001407103480340d40014038080c101e079000144100c584041c0d104004003801e1500100c010010f003502c400320303004003c058001040c040c910740480da104513554046400104002c1ea5010f0082d001400100c0740241c030b41001e0b1091030300014000e403808103c01c41c2c1036140d40c900e0812909540d4541d80300748041300c441a4040c4031050121034401680d42091403e179840300c030000100c9110f401d0024a50007400003041c0031071700211f901080000d0300300440d40382007005145410450131444030712004000340d0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 309917086 1250 309915836 309915901
    0x5070c090506010c0f030c140f07080d050703080c0c16050f01020708030405010c1e0305090114030717041a0a0e0f030910030b0307081002030a0507032c07090e0d0206 73
    0x5004164044006100f40340031900d510407550b231290b605a8021060202e604451a858108002001044005e0641c07900603c07a101c0d01c40e001034801d110f058000342c20007071048001145101d040080b2104120200e048034044409001500b45911003070241610600e00398844c61001d41c400505e601c2514001d10141d40303014a801e00548036059400021075855074204401d0007200700420001c5251800384d1502c82d43d44a6035400181340c0316800120617580c1d1024802c0c042203d90100300da20b501c01d2841540d4840c0d40f102d003001c1c40c8c803814949007080420b64600402c2107102a5400c4a800460840c0031950b03101d000d0040035031a07000d035142c60f6402680c0000e103c5101e07407007600881c05201000e800d4400c000e0321070345500e00303080c43c007000b00c500c09400000b400b084111601c80d050740702610385403c0001c6842c4000d507480c20503800b110b42c89548050880400074150501c030000c0100301103a02081144501c0b140740740c0b02c03050a02030710050f008075000074504c0498900902116803480a0249801 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 309918336 1250 309917086 309917093
    0xa06020a170402031c031e0b0312070b010b0a0e120d020601120b06101103030f070e09090d12020d14090d08010602060711070306110d0c020102090612040f020d0305070c090506010c 79
    0x2032850729041170425498040d0036415113458040c042080d0745c010004240ba040083c10b0502c0c00d21a01c1180080450410002020407800e46040303055035829120305135030319581d10080310a000a1990140d01c0f40030500c3d190300320785001880d00c0c800c040d90780907290240e030303907080000c625074a0100140c0403001905c00500d8030301c0d003110050350000c40c50030041180324a0340011450b50704200c800300e1614054505122030540c02444c8900510720403600a45c847ca0b240346100c2d1030341d1104c0e0301d01c404d000c407407007808121a0440d0181c1c4c60480000004000d00100c6620059507601d00703070f031440c003c0d000e40526282c3c0c0c640310305a200e068944540051040b0b440e00307207044590301d490310102030850046501c08000107103140920941c0303d05c0d03084c1041d180d2a0f4580341204892980c8013031025a0310401040c3d0312038030b4041c15070320805020094100b1940d0355040243c0c0f4044c00130700096100c90030070500320400d90032001802c90140240d4507942007540f1107000740102d480076100d00313011505503400720000 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 309919586 1250 309918336 309918373
    0x16150203090c2e090806060f18100302060f22080703080a090b04060c11040b010827060a050f0117070504020706020c0604080a03110f03010b0310080a06020a17040203 73
    0x6400c240f50f80c64006121001c0440700030020303c2c42000014280080810854004001e02500100211403044001110400041c0740300f01e13209035034001024100c0094203140c4682304a800541c0c02904059840420b0303001e64496500c14941200802d401100c1003952004401c0f05405507041003000300003860850700d81b01c150750400e012490800004410214004540d500588000e00d0b1b20748582c00b8210051034045410b0340705089040c01240390090301d505680e401070031a50000300310710080c03601944030400042030700003540d050076480c41540148221070b0b0085c0d025a10070b2152a04496890f40c854641000700c03160341d10307040c4840e0701c04c03c014091450721b07500a0043d644100780c0145031204d0154a24284003003203409440c1d0000200346981c00f036401d03002e84200807100c800410325102c840100c113840b500041c050551000b50100018001c54a10740c1e15502901402044130089401898058040d43c00541050000b4004144100845100b0f9107018001c82d8000c0c05001c2035881c1121503804e = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 309920836 1250 309919586 309919609
    0x8210301090e1204030309060905040203090d0806150304050a03030b19030b0c0c061503060a0608120d0b1e0f010905031b01021606020609010605060421051216150203090c 75
    0x1c0c003030442c4100c02d01c4603c8005000851180c0c9400d0021481c0c01c4000d0700d03120181d0300c0180228010001c103c408000819400490343c0e19042040e21a00c3d44004217115207441040d40c8a6028000140b2082c400c0000d04511002c0c804c1d602480b14a00c82014804110242001e5100300052080e0a2001454410510f503020580c0c01d0344ea814900074183d100e00c4c0900985000c10041012202c4040c9410705100d0207501c1412035109018280c40c10b200c26545a420340385280e50004040384423103551289800550b0410f030004d0840c4901101e00381e4000d400415400050311550141840d00c80720b50090804100301c580c020301034114104040d00d1011100c50085006045000e41c4100c8041c12501c0700800000d8100c6500030507041c03928000e45401c407869500524400c4200317000820661516050f500b100c0600414034000399680c1d45802031620602500c17400d9204030101d85128281d1a18000003038590003158405d01c91102020f940c012440f083d140e9031046d0300480c03540045030502d41803442 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 309922086 1250 309920836 309920861
    0x1e040305090f06030f041109130f02040f0203010b0a030f0902010e1908010e03071e21113a05190507060e060f0903030c070303050c0d150821030109 65
    0x105811001e0004031141d0048810040005e00503040c030080c801100f41c212850401900c0d1255103080a0554020b81040008020a4500c440c1488000c41d22a904003d03045640050103544030750311110b001000307801c9035526000181c60b10b0420303241082a4007401100d9034040e100d500302443e4132028803000201c00034910003da000c82c2d40c0003071543c0e4248218840c0c0328805000c1e5458881d10f1a003401095030340d0003103210541074000444003244070f440b41c40482e0340369810100301c0e00c1071240040d60480c106401c4068a40101110108401728458108200d00040c40c1d030090700c0c0d1515a00c1205481030b14020700d00007413003405030100b5158084a80d0650b5102c5017459030821603a55a074800350b03400c41c40e8002140e080501406202115800070300d4008001d0070240d070561400349421660360062120250406448034041200c07071001c40e04071008103000c284240409002980340030751584403445810f80301e1040300c400d00500d41c40c1d01d90821080004243d2940b4607480c1107504400341c000141180c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 309923336 1250 309922086 309922099
    0x903020309030703060501061403010e07081e040803190e06010501120f1a0a06110c01030b0a0b070b1f0302030c04020903010b120f010b090405100c1404030c08061e04030509 76
    0x1030a6940d010010f41d00110702c100c001082540c10441700819a900e4040b0780c0d042c0c090148010320561580d020b5060384041d640c80c1540c03441d51020080350805661900ca0010242c048007808140843c00d0015445081108100700303d10300840c65883c00c0700c00903000c14529402800c0140400d41c40f0310480e488a40241d0b4021580c48100a000d001703e900340111a40c0c6c0c1400c54030512124140b85451700014000c03030812010240303040f502070351201034480d50345042582d92090808940d40321030322107024120324180f03241c684505291160718410300743ca0303441844880024400002c0303030101414044e80d6001d400f804441b1ba040c410b00019421a44c2d120b07a00d55221681c8404e82d442c1d5464032500c1c1c42c4480c00800681100e0201c0d1800c4800c40e018042c001c0c01c000d0100808071f14000740d5688005480140000c01d9000c140c0212916464078000441808000070000244890301c44d40c03c041d50000015a5081e0b2107004041030400340700c0c0c0e200d2603221440d070002030209008601038601004007800d00c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 309924586 1250 309923336 309923347
    0x512070201021e0f0d020705150f041809200109140a030602030405010e061303030605090420011707050a02010e0601121716030302040305151b0c0c04090605073009030203 75
    0x1182049511403038170005070700c01801040b070b41c9404007285070303030281c2d22004505d80b00c41140d0380b00191050b4001c1d1b4000c0d40171065400410383d01e5038084c240740394000740304c00d1880c0c418006002c42c000c0343d40003540c00607240100118502100c032041c2544410010081c17000c0170b10716520354001c2d41005009407036555a50304801c1030b03101c00b48200c511541000003000541141031030701404444c455046540200703c00d00810000903400341107440e002c4680110821005242401211003e00760f400407642c0d01c0c881d2050006181c2c111014005d4403410780c00a0054000804095540e12824421020072503545000d04000c40c80c5214043e807102800e40801d1318002040a02405550301040205c0c00650700142c10010b000080c0803400c0714940e400c3c9013110f5401c004200d400e64002500c0b00e0805400000350031103202008018005030303908003400030f124030810f0303041100040c0760403550a00444d81040e1081f00203607000901020a0030303a040d41410070fa94080f0184010f00d0905812001e40c40100b0a = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 309925836 1250 309924586 309924613
    0x10c031101060f0e09030f03010b1b07033c0209040201140424020109150e0c04090f02040b01080c031f03150c0e040b13090c03080a05070512070201021e 67
    0x30a000f03030209100d010042c6142940344160841c0007070404000e03400921419021080070b200700c9046500700301038562a03103a06004240c20030b4060b031703411100d4441c2c3c0c04000b00308403440c003034580f410368400d480450714a00c6000ca007055044c1312107282182191590b1000052401008150700680189001c4a10f510000100c141071307845600880c052000c0c18617a000000280c1c0c1e08041850700e0751000703110f03610056071603542010315540105030181c1c881210002d4088208113503091864002d2050050a0f03c9041a00340010b069909900903403d0004441155001d8030300e4901402d00107414616640d108014400e00d8050b406d0030442001c030f800d0002001c108440550b050400e90000002600c00489102801c2c000c14404d4180c00f403400d1240300d104aa4440ca031300f011100d4941c601041525403442d081c0d95040381904000c251140c0400c1c0720198540c002d024090316445481103405244008503041c0c558082d20500a006a2107901a03042060104808181a101020488551964108 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 309927086 1250 309925836 309925841
    0x2031302060f0304200d0311010e0a0606080d0f0503011e1a0a030b0102070b0409050a0f150918020d0210020f010f0e0c0d05120a0c0209010f050405060f0a05010c031101 74
    0xd202c1e0402004000d11041c841c01c040c0b414101c0c001015605582c441a0000c01c00d11503102101405100f604542042e01120a40008400b038080c0d8003540d10f40c1026260046c0242042e01418582d880707403c2c4c8000c80742d4000c030410110300d0040e444982c1903071700c2d1080c5501c1143e91a00c11103506e03407072a40c000070018200800700740010b0118603039540307400003400000c0072180c05e40c0d00181154400c0208020103010340044034251280c142c00031a441d61414800b00190620700c04155560349012200c0d20303c156150001030540f1025a0305100800b0b4107070000c0d810a40b40303a03019603c200380740520310052401901112071060700b401514a00804c6100850854de00e500388400c03216204c0c0d90110544506004010304140d04030750224414685484050b0380303280c0002030800c14180000e1080702d00e406900c001c2e80303099000300115015a128001400480c03011300c100c5001e03d051202107440c1e4a4503d440c060501805000d80030382d02d08e084011240000448801c1d824000b40a01d2403203075200030f0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 309928336 1250 309927086 309927097
    0xa03150e18150a0e010b04110a0e01020c060a05070c0812091e1302040510260408070c03060b0901080c0d03081e010e010512030301120314040914070912030c02040203130206 76
    0x7910005441e03c0015051800d44001e01181d510a03881d080a230600c010011080c0c40500820385040402000e8200040c2e01d0818400308071a40420045664880150300078024210103115004184a20b84d0b02d4001660b00c4042183d1000300c40000d01480100381441e00d1155190514001d280604402040104a01c980d074620300c4030219400107814070203400d01240e0b05204000c0c074904883c010804a01318000c0c5660303d140c2140c5c0c203440801003000e00000354261440c4540001070021116a42e15120b8000c14025003c980070b944c4080001502c4040410310600d844005007048a562a039950200e0345410000c2400003850156851041d010340444c6c01030340a02044c0142d130700c07554104010070031a212000c0240c02030b50f004100501011104040900601d58182010300340c54130f554035030744100e000d250881507180f441c0c030141c0c0c0b115000020200380608207c1e1203000c0155103464110351104912440540400c80b40c0b0306020041c00c2c40e5001b154450b07400c44542100d0300301e40c0d00207101e0b680321 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 309929586 1250 309928336 309928351
    0x9130f05150a0b040308030610021e010c091202010f0f120e0a0501150b0706020d02090d060903090b03150105030405010e031c0f09150b0d06110a03150e1815 69
    0x2610798003050a2a2078a00701420010700d0701c5081ca865503072444043d21004003c00d01070034003044007003602030080080c060320115458050743e000840d0410140203140380000080000c00e0782c4800214542c010315143c02c03098041c3d5507203070555003d0f00e09030b0390880c03492900030410003961040b640f0780c800c5204901c0a091000044d2a200c010340c140390b42558039200d050809540c4a1508002200e00c0500f181c030559884040942c03185c44420080d0b000f4012005040d40013040c2c0b507a03400401001e9840001d4080c402d4440194a584408203200340d8041198609048507003001d0454007580510003540d8400e206a0002c640440a0040c00e0f0031500500001c400480d801054600d614059000714554400441000c12800c1419100c510408038074840c5868071381c1d0f41c0d44c151840d0340c075007200354213886402103000e0010380f010740361041b0700d03912104408001038900100350744001f44c030300748ac4002c41c0c810f0b6007850a01c0c0c07104c0c004100c01038241c280c03000700b510400d00039421608003a03249a00c282c80 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 309930836 1250 309929586 309929611
    0xa0e0a05090a0c2007150201091a0402031005060a120206160503120901020703090905040212150a0b090f040b091c02011512030f121103040b160f0509130f05 69
    0xb0b03e0151070180f2072508a502d01c0e0708804130b4141d5240015106044404103135124421502907038041e8010012500c0c0603241c0001120014005d01800a9290049209900700c400300124000407004442081c1c80096001c2c3c94494100b06151107014900340440c00140607030300d8581420080c905c0303c410360408807595000842c2a6005c209000c9a0342c0d88031203400003d610f0700c14540e400900c80d000a0080e82209a84c3d1000700b81551241c68200040180010884440354101c0549100400e002c58000385507a00304800e58595060196890f401505161421011900c030360707891460081000700604118402e1003400100381c03210f840005491a15500001030011300303e034800c075141c451500000c8202070154199400a84c0c0440c42001f100b4151411400c40c030741070710519018144035020503c1451000c006d0009010614003213501400314101c0500d900040041c0c142c0380d4036090160b50303010580620200710f00381000e00440f540003019200003d0b214018084403801c461040c0e5210f0003881 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 309932086 1250 309930836 309930851
    0x204080f0615180c0a050f1c05010b042603070807061b080108032a4e07030c0b01030f05060f100302060c07030209071d010503010501050a0e0a05090a 66
    0x2c0251000c001d0651080e501e4000c0303000501440340f607120010306900e999500003e03030f40e080e151140342568414484090b40c41d5542c020700a51003a03c4014184007444107140000028280c400380088604851900000c00c00a03141280c1e0070b111610a5511928a400104454000240c4100082900501c103800c00140c001c60705074a080c0030511860b0042c18005900010b2190ba034001003961500b8821011288140113041c440741c41c0666812000f4a0612030082810703001540300c2403080c014800302c004083c4600c5126484900001000d141000940ca0080758186102c0c0400061030703114001e0a091190603c590b03501c00070b98000343c0c8296021266110501d08201040c41507903000105202941900d09010b04e58548492080c40000e10914000614480c5482c0900000c1e004540081129034980791080002c0c1211704416010000d8420025441c805503001d001a00c1c140c64040e50348600f00b05800c50305640300541c00c405a58007031046140060203943d0401c0e00c1e0b01c2810f0000c4c0100b42030 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 309933336 1250 309932086 309932101
    0x130b070812010614030109090c150201290604150314150909010c0801060c020a170c0321030402090c07020406080c040b0103410103050309010f021911040204080f06 72
    0x4001a0000303c00c00c03044146001c1081c114100b80c0341528207400c80012001400d2800741c00c41801948a420ba0000f059035001350a40c042d481625541c0041d061400c07641100b40c0c3c2c1c01c202203911502a544074a0a120034050301411714850f150b1741313509080c00a8421040032035200311500480b0409003103203103011030800354141030444d43e401804510003070008048401c0043d2a204050041d48100052156000255618003001000400340c880c0d44854507010f5006e800c2d11410003a40d240e01034401e03a41c2608504507200345060700300502c0003056066468540c2082100383c0c003d804080a40f10611000c07015036110b20450000b00820740050001e241050180410b5400052000d4140340c5021805080660055050f0b080031103402982c0f11007406440307001e00c0264441c0d40c08090440d13101c00100c00c101c0e001004100007442629400c0d611114000300f00d92310310700f02840503d0705400c180360038005000c0d401000d600c884000c1001d400d00c1c0d29200100d15003405552507070820382c8900280a240c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 309934586 1250 309933336 309933367
    0x70911090406061803060b010302220f050a030b010e3315070312050408130807060201050c04060518030c03010906020415020c0607030e0d0b090f12090312130b0708 72
    0x10070803404c065286035214141c416440c1154032000d4000382e215040e851704c50b0700c2503040f00d1010f656187c031100080c4507004413004a0b4450302540d8980130000c84045154039081303444d14110380c0d01201410310b980c01d180da0301c035081754042d12107843c0c10f01200c00080c55040c0002615062815000d02c0181d0b00034a00c2000a50b1907902d10030641050200400ca01080e07110031000302c1c50081d0b8801255544607407500050368482c002c21324080c509031001c007040801010601c5021170780d890b8020320032a2241183c0030780f00d218611a481c04102c080014028850322415800c1605200800ba03686654484002c2400e5540c1c8450480d021a0f00103000c0c0b207081d0000454000b0220355100410300c1292403408100540710341003016041c40a8800b00c2001c590b00c1c050804680c035803191250004e4102810607903aa140502c0350a031542c0540295912004840000e40c0c0074444003c0041001080d043c1c40c540255118406001c0e8410380c004010035043c4000c070041c01c8141c82004010307500c1000e040780510 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 309935836 1250 309934586 309934589
    0xc05090a05040c0507020108060a0801110301150206271c031e05041a04060b131407020604050607031a04020703050406090605030112150b0d1202010b01050f070b09070911090406 78
    0x426440c10650b4102513034840c1c10340704680d0b4203003044407164070380700c0c005902500790b0b40c040c00701c2c0c0d800e080e10040d4001400300039504a441c20b092084403045101002d90f05c0350b408644c14030880083d21400e0038520705a040d40340380c1c4801070307040d05c40000f01c5840d4184042c450090f0400400d88070041c807245000c00d26204e04400740c00840801c054102903880c011680306544402880c0c08501002c036090021551229190440c002c10840e1035080340703000c90015201c0c0000711800340380c0700b1000880607400861020f01c03e40d0300ca00541056941d44000790010b040b200d4191000480303078440701c0c441f601c90b44000c051260094690a8555240c100010020000e5801010402106000420016520401c41c0c071800b0344c801c00719460415030079086801441c0002d915070307101d55005c44000a2103148860b54a03d40e0780b950080c020010a48015070360f620901c020791075440c00800c00c071004a2240c2c03c1054221004030181d0b0f204540d102192400d82d08001d41d51912030721300045410003868588100300 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 309937086 1250 309935836 309935839
    0x7050d0c05150a0930091d09070803040f051206041a0910060308040305011d0703150b03011410080a050a3002100606031841100912030c02030d0c05090a05 68
    0x2d00c407420201c59055180907480c1a41f1a007426801245010805200b08006803030710204507502c503a40c0e04030b009202c001070f108140c001e00800c600c60f444000701082187c4620340100c2c41050f01080c9510780307215140300a000c40d03420b00a020b00c5960290726030013840b00030f40c01350305032640380c0741541080b0703084442c0e4000b105030091000d00c0c14502c01c3c1c00440c01c40e0890b03403c1202f640400b0410303032401001c2c1040b500c856a040d403034441d220b044080c8034030595002c0d10b001c810705281c283d100c0c82c034595680e02a02c03010f0300325485100d084c1d0000311100d1240c22400d00040c14030b0032140d1a4464003103150504940c10000d03801490303030420400340310b2103680c0007041c10b0324051100c0c824035180f244115403c0b000190000080d000220640340307007445610b0808145c07505800340817010300c0d10650004071190740e1221600903520701c074038030f81080d0003031011440e04800c1c01c040c1400070441c15801000d03812010000c1d4041400b031605102000d12548012a0b107540f201651264104c1c10050406800d401070f5 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 309938336 1250 309937086 309937097
    0x1050610020a170a02010615120f050105060409021e070305270f12010e031303030e0303031506031810090201020d02070f06050c0c03010603060207050d0c05150a0930 73
    0x10300800d0914038400d00c0140b400c5103da90b12100b15108078050142d540140300c250489050710344040741e100d001c0d04c54040b107902c81000503202d608a01c006545023072081381c1d4000424041403124000715401060ec104040607560030a48031580e041d01190000711003035001c12404203411000e103102490008038580001524281c0c2908100010300395203140b5400d81c080d20301000c0c001c1080c00b09510000389100c0c21000c494540d0107041c00c203c0d40740850f020480c0064041e03240000c903410000180e901662090040c1e5050016260034410a500000d0940c2c8485140402e00a800303c001c1c0075201000c52582e03000715150f034144c0006880e00601c05408000c40d407001000b00800044000710741c00365001c51904a036501440215685403451151109605505e490b0000040114580c028101d1910440a482152880c400203480d082911340014285400900704522000c06040c034040e030000000100140c4040581c8502c154000030101da80100102006071101c8080c540c0041e540c0c404080c03070070 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 309939586 1250 309938336 309938353
    0x120102040602030d020c15190e03180402070305040b12041716030f0323090f0d090302130f0207050109020f0f0a1203110d09060306050406120b0601031107050105061002 74
    0x2e42d0f03449038007540c8886075400300d11140c10b01000d022880c031807000a4040c9030281400c801d4007201c0b01d4011900c0c0c24441c988042079864200100981d4070f510f4514140746000307403401003408040d40c0622800c80401c10b04100101e081c1d5040000703040501120145040c0078542890840e0b2025020b2060103160b00061100c40c0c0401d60401100191680c1440c003503031a0320400405138050329040c040c050701c101c42034003866980714a41c424030348240002821a18405400c0c44810346900c040d0581c100080c01c181400e02c0582011401800100d0358040001000c5400306003200403070300700703000807901a51980c0d00e403800e40c9064402608240c0302100c0d003c44c0c0122003030000b805090240b05c0c500242c0c10000307020003454000c028030030b244480001501c0d0400c0b85040c005000fa02d03a8021280407034580b010101d2030381050b10659040c5c610207581709404520a894103c83d60781c00620f00740c1010346501045420400501c00360030340c54891400491030b030401d00200181c4803400341d540811540070000 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 309940836 1250 309939586 309939599
    0x12060503030928080109050c0109050303070b071403010b190807200705030303070c0501150312030e010f020d1e05090606062212021f0206061509030106030b040212010204 75
    0x11034192040443da0704a0524280d072072404640c002c0200000c2001da1480000348202040d04801c00b042e10076001e540c80107001000664400303100d405140d07010391083c404440083c04040310ba17604000f0505244003c551141941d5002c0d0303000360403081486a010400008440104001444615890a044c862803601403802803010190780105110b0380321117221317040050300c24003003c0083c0c240a01942e54a10b001e0101070544006440d04586944c42c00800a80c2c816884a400c003c0e6030348003a9203000041144012005000c7e4ac2d107000382e07503550780d069402c059041807005045045415a02050000120106c010103550081076000103609000401508102c085502c56210b003045400c503031961001c80500912007480d072032402e11036070441c2003c500d0007034041240d00418400c44410600300c0804010480d0718007544258070140e803281011404914100b2080034003a140340c02c82905100740300380042d0079141a03900a482c03d013003c1c0c0078403055081440800761003400142c025407500303244c150f = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 309942086 1250 309940836 309940843
    0x1603150e0d0f030b0a050d03080118050f130218010906060e090907030204110f03010915060512010e0601050d0603060b01180b0d0c030615031d150135030301050112060503 75
    0xb41d80e030030142d80d13100e00c0240390303610031141c0090400542600a007807464074020b40901e400b80914402807280195118041c45540a098465240c01d01c0d400c40d030761224000b0782400300342c5640c1240e10034020500e40e0303d8045031420b164028192030101292640c070f4054041d18883c5103840e00f90040000d8800c2200d8108000740b81001c99506582c00645d42030030071107451481c0148403040651281c000b00000e0138030885d410102010f003040001d10050759864a0664052050a040c095080700c071100402c03451501d00240d551118060500914007030321003005404039800307600211001d50f5208901d02e29541e001e00c40b0a0b0005400481c0e07040306007807030006002ca000b441758204142c1d8960140520140c82074218100802d80551a040b007140740141c00390240c20307511440030030103445031500c1241a00000d05030144c0001070f104070540d6400d1201c015004000c0041110160036800076480250000c0320079100b03000804001780da01ca504102c001003804080c0c2266154450030030400340038650340407 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 309943336 1250 309942086 309942107
    0x30c090e0c040b03040302100b0a180e011b08090d08060102060c0309010f020c060604290f1215091204030308010918171e160308091603150e0d 63
    0x220005840d907a00c11940d40564400ca8101600c251000700602c01050f400081408808080e0700341403107075800c01018004100200d1140003203010344980e41850001041d80311a02d50854680041070342c43c011455107030340e140c00000c45400194200c04100301031409220107003a404103450500d842e4103000d00000d55072000604840d003405c0000020640018007544400c0104952800c203644503035411580585175202201e84501950400b01300001d00e881128090001110034407444550083c404140100240720050003900100000c00004400700104071029205d488900c01c5141c070300d0104510ba09000d05038088003107065007400240000303504441c219054414021001a41a100544054215581080c003030007103500007805403401c44115000f0815920710344e90620400c092071200c455540302c0c03510300d01c12101e00c14101d00c0000b44940c000c66000925a8205d8200c0c03500000c1d1400303841c41551080b02c0c2424003192101180300b427401002c0001c5000703c0608411a4062800760103142d02c4c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 309944586 1250 309943336 309943349
    0xa08161506060503160e150d2d020c01060b0301030b070219020a03030e0303070b010e06120708060f1905070215061008040b0c0705030301090b1906020307081303060e0c090601030c09 80
    0x114100d01d21900c02c042c6c42c03459110090400100b0394010801c0045940304014071550141050054a011100d001662148c4040c1030042410800c616034118020740110210200715501d0300c0c00080d810a440000c2c50203180114081001800d0603000a481c140c86020001c2d1050310a022001c05a65481c0842048076014140700200145580009040d03104c1c52500414800032072002007200ca0060342c040c0d2040c2c4058507083c0982e13003001070305a5500c81da0b2003410000d920850004541403c00001c56811680944e40d403005407100703604010a683c01141c4840040e403000300c080c0341000c8002d2401c0c2c2c0200382901d25590854008400801a01c4001d0000d00421280000f040114276030381d00301d6481a81000c01e403522542c4501d440c2d00074005285001d0711441505006256945210714074000b10ba2403900218582049690b442d0100d820801c050350858a00e8200040450035900412140051140203031410380300c480300704000104041c20050405240c82c00003540035402540010a071440c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 309945836 1250 309944586 309944611
    0x180b0702060702150d0b0906180408090a0b0403140d1713050c030a0c0f06050406023c010b1e0a0501080a0207020a0602031e090f0607050a08161506060503 68
    0x854000310340940d000c00d418104d200030006850940340d103d58001010780800301c0d4074020a4803103000b04212001001d0204903408040c5001c1000600071074010000f03880c0c094148505140d80b51b688400340d07049a4001d07501994800c1d08140c0c0c1450a21600010010311304103404151042800117040034001400007584c84181c003000d2081c0401040b032080415001411a80040b1061500c086040100d00c101009103059030004180107008030b094900387d0381203038002d005035000d829855400318000c070040c4a00d0000d00c80240407a140f44030501c0c40d802071600c000f045031002c0000b489a10340c18802a206440c56910a01a070342e981c0d158008101d032805d01c3e0002240d21000780540080c46402c50080d800205d03004002a010b4001c405000c3c50003074025010740c0b420500c1c0d01000e5521411501a502c0000d00341000c1c114a008406001c419000d0011681c130b00c0103e5450103110303404004501c06c12008490f0150070883c004007083c01542501100b400f0f80742c58103c01800c0c5020107040c1c0c036140c00 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 309947086 1250 309945836 309945847
    0x1606080a0603080f0d14062803020312031f0302010e130e0d020708060a0504030827070b03010918050604141006090c1205070915020c0d0c06180b070206 67
    0xc000d812210207541c01c61012941c0f4920304280e01d005900c05116100110306001c2d4204881c0290703150700d0b2290310094106594240b42d0440c44142c00380b558820240c918519901001503101080f180c1d68100049190503501d0038000b4200c0e280c1130002c00c02900507c2d58200510060741e0060000c054480c043d60122099541c00c04510003810501005003080d1040c40d600c0008250300240c0723082120313180019684945c444a92000580d0030454001c3d0110340000d0125255495181800d0201060011310b0b241d01c0d4410b5100340e0501300c0320707804403440700d0021006002410b100d03c54078848008914031741900c4081580c4098403000010000350001a00264190030f110b0b0a001c2d40c1e91110402404204c2c00303458100d208005c000c030456400001c2c1210b1210040c8860a1251034002e0308103803100c00c0311900d4020401e41862000c90140c085004a40042032242c5580c444542000d1140300c02140381401d2920003040c58182080351020038141d1601000a11801c00840d02055015114541d464 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 309948336 1250 309947086 309947101
    0x8190905060a0f0f030e1006030b0c1303030e130f050402030c0d11090a02072901091404020f01031d0a0b0f190e070b040e0406110309030901030b0a0e0c0c0105010602160608 76
    0x1c0418500809040c060740e0031942c0320981a48c4000203603885210341d209503842d43d091401207401840c1c540b4000140300300301403000c640642548400441e000301160303003030980561501c00751040f0300d10500c69103440304244800c40c5401c0c0003085440c1401d4600902d1003545444410701420b40303502d00c07402400c405000c5690b041c01501102e84ca540c214140441d00004090048411400c02114100c0400200004120f4111901030110b00149072a52030784a51900e40800a192030a0300c2614149907491075502502c8110101c43e00502000d08042c0c1000c64150034000402040100a4071841a40d0010002d281445038182d070305e015a19900081d40e02c40200142e8a02203040d0400d00c050320010030000380c4104940142c620131031007a2014814040001d0700394050f4041a0340806103500f0600c9041e4407035209a00844c5c48800040416440e1a6280b402c000e2240c42601c1001c0110700000311801250001d0142d90f004244a1004181c0340c14684030004201d109405054100b1a0650100c0c055 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 309949586 1250 309948336 309948341
    0x3050f06060a0c0c0302120709061d0a020d0603020316050906030102090a120516090b011b080412020604090c0c03080708040809120c090a0204140613090c050708190905060a0f0f03 79
    0x17440d03014007150600f00d080241240d0344c40c10f61052042d0340d4203019010400e0012000d10300c1000804902c0480c1c030381c5801c21040007a400011440090660341c0c4000000759404114040601e4000941c50318068100b40500140b85401409036004e03a004200d8440035440b02841002200c070340300c1c44405030030118a812401c1c41062181428560499000458804030326440109403541c240c03108420022240321a404911302c510001d0702e001c8040c403042192800e111001c80081c1c1c40201078506d4039481c0d00310b050444002d0400c0d000000c840c2d0351094101600701c001550841c200703040271445880c1694800c03540303204800750240208a0183d001c2e460b451308000314485039000400d900c10b985010704c580380080d0003501ca0719031008860b00c100c16407820039400725407070840c3d0064401036060034046014050407810300c410042042c100007440c045940e05025000700b68512002d40034000d0350b01c0d401084a5290f82056206010401410403116008000c4a055040909050f50041c071102c005030700 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 309950836 1250 309949586 309949589
    0x7020904051c1e0c0b06010807030609061202120a0f020d0819080603070605040806011a04080607050301090510180b0307080304090f0509010606050706020c21070303050f06060a0c0c 80
    0x1500b01e141849140341940000b003c148a41160600f850021641501215842140100501442484030114102d54420901507034401a5802d002ca07026a0355242c1e2801c41d820741e8088811202d1407042101103140c051a00424000300e00000c00d14075895498002650f41d08002c024030407030f907851480c400c0000500507500d0b20b00b070b20307450b54124000140300031b0103503481220000e209002d042c101007542402003040d6402c0c0c502d44002401e603030382072110540c0e442e074402c7c24a02c002c1805101c00191480c0400440c0d2180e0b036156103807916075140c5002041685d00140a940360304840340d405100d0020400c00107001440100004502c0f04082004a0700748461a00301d0450342c08002804100c0c076049800c91041c04019482c10000b50355010340080c01c86159009a0000030401c02200010640b079402820b554000241565140b1080c032480c480311510000840d16441d8001c0703010000c3c585c16110b1150700607203041c803000c02c0380340190016000748111401da0701400240d008900602414080c48170 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 309952086 1250 309950836 309950863
    0xc06100515180406141306060e1507211701030f08180907030e060603060403090b1e1801030c0f05091504030b040501270c180912030218090c0702090405 67
    0x2c6081e4803000744050100750b404c0400d000b0049035a1603100a1b1080c13240300b04481c00e65a800b00002c500340708000c3c904e2203103500241c400c4030510130040031031458605141114184908404900c1c682ca9002d44070464560f50340c0c4440910038010004a41c03400d10a50003140e0100700e03241d90361401140503601480e01c44007680c004807184100700e501501036005a5422900e034048a0203595007104241d40e40324100c800500064601e80700b0844c110070b00d8054060594031401c05800400564201d56041d00301610981008030140d504282c0340d60984910030100c2c2c02403400300130040702c156002d0030034469800c1407405014100000d0659400420545001c0d5a00010080d01c41c1003600b07240740a0521010303109540c0c04880c01080704900407214900c149030b4495a0441c5551034080c12904003c0c0e0002e41d0107015881e13481800024154102195a000103600c0058444080088108042a143c1c4442e03000b44600c03030500c4940c103801400c0d01e54a550403141c810f031540d25450400c1c1030031814404003 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 309953336 1250 309952086 309952091
    0x506011401170f18030414090603101404030f1b1104270b0f0f0a02210a09140a031704050a1b061205070e091503030a03020c061005151804 61
    0x30883c03084060540f40203640034454848081c81404100342c89115a1080c06801d00c3c083c00d81103400d0030144a00383c0e010030018144c500711072020f507101080e500c1c51902c6495a0048130100810950440d14010b210036141c54030b02104040409554a41c80789000c5c013501d45500d0f9000243d2943e616002610540c04001402d20000004410001030a82c80d01c400c0b21112401000201d84020702081244501c48200506515840d80b00c0000d000754806529214448001e031003403034141d220740748094040d1381841d10000d0805401d0411b0a00c07010380d210204201c0d0000311910001c030340c2c00342c1165a03000c800801e030552501d5500d082440c00d003c00500400b0b045514050000e01c2000390009802c840040d1182c58035012440d90391030450754116000d401003000320740070b10751b04c0c2002c245860b407001002c00b1005281d40070b00e002038651b800000c42035000030303000290182c0c04402400403540189640c00c480b80441c3c100000280e19181c26050440b02000105610440c9100356485015200014008 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 309954586 1250 309953336 309953341
    0x3030d0204121205030402031218040e0f07090b0f060c012018030d050708180303190e0d0b0118020d09030c021e0f061819031a04050601140117 63
    0x3904051002d180151018040b454a04500301d0150782264492076000300a086c2a40d00742d01c2c81481d680103081901541580d0007031481d06278880d44201410200124000e003d5800401100c52a10100f500901100d0f414405820b00c29100c075109010b0f420003c071040b81c1c86801c00c0301c5072401041d105200011811104041e1021031400070010668100200d40c0300000f019084107050f91220621034190004000300040c03004100000701501076108a140000c0c0d000140d000081d117941c10000c07007003003460b003030100c3c4001c6603411484440003208c0130f860403105141c4603202d58458030b00500c1a019854030a095804410380b00741e040711900d65141070200060445810300500000341341508a004451135120381003100c800d016140d4106000400c07030f607140c4c0721641c2808140e0b0458101c0c00c040604040502d10313a551341000120002d80c4003009a641180303503003001d00d180c4402c221980010042c240030b000210320301150043c191418100e4032406040c201d401209c1094001c040040502c401d41c06 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 309955836 1250 309954586 309954599
    0x1b010b040903090e180c010516060c050405030f070b1b070f030c14030115060513050a09020a030506180105010e1c05010c1d1e01140d09051009050d0e03030d0204 71
    0x10201c00b0781d41c00c07200e03020072035a502e40b16071304c0170b00444c0f20000203502035540901d41c0c0d8800e2001b404800450100c10380050300030b40c0c5140c15100044a034402082020505210303c3c20700b04181c0d100301e541c40c4014030365549003c000381c81c1072080c2d001405813001e0132055550004403c0000c0d0000b440340071015800e030765907402d0100403200d550180c443c3d42c60b0074023208640c0746014021070001e0401030030f648003800d180c404280c03010b5028008000c00c0d00c01c14070000443d540c86240920040c803d18101596581818200604442c00140b000380318103080301c055070504001d0080035040d141c0a0800f00e5440618500250074004c0802201c4014401000e4540408c101034021000219854482c1c581c90303202c011130580404d2003031140c0ba801110f4002c02c400c103001700d0010b5003003005040c100380110140003c1207180c50391154005030b20780340c2c881c02804104241041054100c4010039001c0160b20303040e580e481e4541c1c2990303003441c0401940210441e0560703000d104440c01001070710421551250707070f0034 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 309957086 1250 309955836 309955847
    0xb0c0706050105010309020f1002010b1002031306020102030408030411040902040c020a0302060108240a110406090608010603020f03012c070908190b010e0a060308030f0a0b151b010b040903 83
    0x110480380c45040c9800010a94042d0196006590b8000c0283c80c95081500900c140006500000345c119074035100c8000c0191540407224599206550103541c0e100302c9409450682c041907403052086a00c10400c00000c10303610401e480c1c10560040090582141c4040080c01500b60320402a62180ca0201c40083d01900000e10303400b10f034800c1d000e5484070317070343c0d040d42c00e40780e801443d154031001007040d48090700011007018066100c0e0749940002020301c0c080e07a0b2081c45801581014000c2001070806001c215040008a070044c41c0c64a030542c5485012441200340780418402e4152080e00ba048032070185640303250840c0c8800030008902010f00e003100c4002e24001081c032030300010380280c007842000c02010412007031000d60003002440560f4a803800320024140c0c01410062401d64511020000966801c01180a1070345a00000300f45e007403100d0521b04807112044180c0c4500700c401000307042020000c00b500e00e282e40350b030002c042c41403040c0ca0103401b400091200b254042d1800000c2000c240e0082c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 309958336 1250 309957086 309957097
    0xf0501051911071403060604060303020c1017011205150105100807260105040608010902030303150a08010504200303210c0412060606030c020601031a0c0d15090c0e012a0b0c 76
    0x1101210044c0e00c47c3c20a0204540c203600004d40141c00a50f410b0b005403c0c55090320100502900d41800b103d040c488001c1020442a0440c10350031010408a005124040200b81003080140c1c0d00f0503200d5150a0015491143d80c543c1c24040c04500e90000381c45501804015040303002441025055052009625a50300024084c0c0c40c0b14910f410300125035620140704d461860b0703901400861840c2c88151481800d00580300c040c1c2e0388150122004500c815081c01000d015920454840c030308055460031895902400d0042e0303034000e43c418071601c4c0740035082150140703010740c0c00040e4040c148c643c2400003281d40302c3da401510300050040c4540003045503c3e0311010448465680070059a1403661003203849101c20300c03018048611440da0086482001d4142c2030704003550380d00c203c0c9411400c41c555810b40d000e40c2501c02c010109064208200307079050007085070a2199150400075118080c0001e055441e40c1d240ca61504a5070001401b00d56106140d000c00072900141041c41034031b0700201e031512a5220 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 309959586 1250 309958336 309958339
    0x81e1806190c0f0c0b10170c0405070807080f090111070807060b0a03020a0e090c0a03030c050c03030a0f0309111c17030103030e0904150e030d05010f05010519110714 73
    0x38941030040c0e0a12511110030006516901c101a8858039250a0a0b901c0042c09491b182a16018006982e2210a5032101c06190741c50243c0300030304805081004445000b4484030600c90458100072580d540500780b0b55228040c51780307110a5440301c51b5141c0c010311001c1d14140d61309100180c10401c1c0702052014101e183d10840090100c0c4043c03d00307111120340700d44002504228409030902c107031002012032588c8540e0752011290008c200800060b24511140d0003030f40403401105101043c07000c203006440b00310905400561400302891001007401c120403500108165494403040100f10305807a0305603014900a121541d0941c00e050241c2d40300c1c0008074103c0e100d4102840c10311480c10a03a05a90480e0780584584528410307440034007180c2d01c0c3c010811100700091030b01c140262a02449114a1051020021619100c0b80001c003000c0b5003040c0c00444002d00e6400082109a0303015044801a10110140410343c50035680161341410700101c034902d0501561002244039228000d400340c1d03840c1c0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 309960836 1250 309959586 309959591
    0xf07030b010801061401110a02150405130903050a030c020c060301090c23190c05100b0f01031808070f05010e3304110307030f050d02070501081e180619 67
    0x9079a42c9039400c030741c00c40c0b081410903000d4883c201044c0d070141c48004d03145032000342035468002c3c140d40000c1c164a41c52406800740100480d080c8401d087c080842c131221010728004101a0722b0f80e840244c003d0280544502c10581c417075803020055031003409100300360200907210640302d5071141c8414015101c0c2d042003200003040c0ca0121201e0386401710110701000020f06145141c46a01c41d141c418614005820700d05200e44080040d00085080080000001940500040030021801040030030740741e01c0c1c0340e207040504040c60300c2c4d0500040c10050240691050503580c4d00d1b249450880413519011f01c01810552805607940b03900c201c0844c1c440881d1741200428015484080e4440401441c2c1d46120703050b0071000000200091540b02c43c89070440350007011983c12035540e54071460f9484038682c00b00c400f9040a83c0040d4495010011030b40509800d08020082c0e2401c10031940409406850ba00740c441c254030042014003500701e1511684000031010780b4080d24003507a00d50035443d0414840e17640c061 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 309962086 1250 309960836 309960839
    0x922061a041b0f0315030f03020609061005030309060a021c0e0f0904110d021c0503041805010305060415200a080c0a090b07110306070c0c06050f03060d060605030f07030b01 76
    0x6080700b200540400c09459510049040000c11001080020007081c0c010742600f1010000c10110801d1001380743c46035006040500e800c0041a00f004c00141c100e003c5a548103409002d15900071095401e0410240c078086e03204e00240c10304a02e04401100c44480000e807200704540001c0e88508007400c01c03002910340b004828028030030f1101120040703d02900c500300c00c04a000c0d044c50160024541e482c0014640d041c20700840c0804090003218090484956000041c100305000c000340100d42c10f4203148104211662540d01c1d10740d12010000e100820309020918440107007001b5a2000b6400406440034070501c21003111540c0890340140c481c01e002c00d4010f0006071444a034402107882c542190743c7c501c020b1034a421540d40b02c4d5009443c00f160078580c40c40c00c103d2076071000c0002c0b51050020340e6640c0041441420708030b116800c20b030408802c0000800003c0c1d6001d801d403045940000050307034191002082414000300400f100c0e08003035450b0060950104e056880040c101c41528015001030302d159 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 309963336 1250 309962086 309962111
    0x506030a0b04020d050a02060a170c040807120309090204060905030f07261e0303190605090612011b0203090a0608010e0a240f14030c0922061a04 64
    0x481445500410314001e4034005070050910b184000d02d0346114101b00c40c1405030342c0c0d000811035002580c18000042500d800c91789400680d2a001c0d41240e200f011003454107082040803900c8201034040d502d816141810340c0010540300b090031400070416180308540701c6480c0e800c01002c1d01424485c0743d00c41d110700000b04012501c003140100444401c6214100e4074000d00c82007074203001d030000903202c0385c0c0641d64a0250b81c070703d6800900818109017000d16520300e081c04408002404210a51030198070f0041c0c18041920341c404016000002100c151012420966840340540201040340d01000c15100030b400d0f03100d80000c0079100081c1d0403681c00f0006030321000b0498400009200d8a01800142008103080c80d030b407540300d04a1001c0740002c5d45081e01000510031b400d645541e200a020090080b401c01400060b03114282506200714090701c04402e0707036030000c3c6400002500c0c810400c2c00030000400d5403003a01e04c03850a099070100b818400c00349a1941002181041300081c2e0049080c0001301c00030 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 309964586 1250 309963336 309963343
    0x40b090f0106140702040e0d09060207060f140405180a0b040e070b0706200408062514040914010509010e040b040b040201020a0f081803030405010c0305030604020f0301120303050603 80
    0xa500000e8140c15580c60041c00716240c02c00080440749142c02041104090380726030044955201c4507000500c0c0741c0f0031426000b800d1407600d520040c11900029000c1c0f00c03183d80030071400ca01421910f0420303900341d8400c00d800b1485c401c2d50f0015600c19041014106014007640c040c5101703850030801001000700303a10921007994441040079007039400030b600c00d004003403240000c3d00d541c500440c0001120f08500303e1049a0034045444d0801004010031f00300100c3e4004c225081c0d11140200d40102072112060300705144003140c810b00d800b8407074404000320b044030709070040c1d03002170000002c18000200c4201603100121000e0040c81d010700200f9002090700c40d44032903060b0142c0c0d07101043c00300b05e40d0f454992009210340600704074114003409403010f0204020040003c0441d010780411641c40031006807044e01140e4490945020b600181300400590381c008584c039030310980606000d07940795201000640244205081c0c003418080110020929000042588804511079102080641c071003008041c1e4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 309965836 1250 309964586 309964591
    0x51b04060c260f03042a0302010806040f0507090503162106090c23010306050901060528020c1903020a180b030105042111030f03130c06020705040b09 66
    0x4603801c012804005064110001c03a03540700e4012040d151001d10341032622a501c150890f6020820100a010910030b40c00c03191070301c0078002c03020581c0348000000b80c04000c0801d480080e041c0300c1041c0018209841310f4000542021611320100420303e010100541030b1002401903901030b204142c01c10052041c0200c8040a840e110001c3c0380c10341c140e0610f03e0b4192041c1c01411903506d6200c0303a01c04c001804141104014008041c00f4080d6040d20355904000ca0203008082810981814803c00081d00c9580400381500d800d45415030342d940c4040400c107407501910880c2c504105040c030040f9225076012a00050700d10003161320700034004031950310741c001c0c803014040a5408032035900704000c198002c2000400c0ca24149501141c60340052000900315076045030152035081c0c000180c04e4451050344000110740b0914140600368034150a0303030035a6800b56803040840d04030b0020205130401c2a00c0b0b4225081c07a40304820144e441c1e282c0343c00946504940c8246c4c0d004605040d010b6000f89000000e951 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 309967086 1250 309965836 309965849
    0xa0602011a061314060705031303060e03090109050909070e040f0615080304180e030a090e06010906020a020405060103152c06010e010c150908031506031006030515090a051b04 77
    0xb100300e08001c90f01c4e007401002ca1055511010802c503c600041d410300c040d0510403031844001200c01e10b50b040c0030041e6050b14403001c2c0c041e0010010303406584c1e001803240040c1d030b00a5580c006690f42e0569058500b1040d90022510b000081040204026000003244001480b4180601c4111121121100c0313802960241030520f0b0011711003800520840100004440d5030340344003056803403652103243d0555100075a000d000645224041c4994018041200d40104003840e10461252030a18004d4480f002000024030541c0c403800482d080307038402c3c5c110303003d044070b071041201b1000d030354102002ca144456030110703045030740c7c07a0213541012070340c0c0803030610078041030b120324408546c3c0400440d1a2a51400c0403640400840120040080d851052860701445200181d9407810620240c00500303085000892240d1810010499184003803000301c0d040341c4490802042d2a00c400954020381280c440c0c120b0b0300100300d5000c00c50301400640041e401030710350042e48106540c495044030010b02c1240110b4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 309968336 1250 309967086 309967117
    0x506010308030a060b0301150311030c16060e0303070507060e0d141c020f04030209240d140613110a061d1c0c05012c010804030203090a0602011a06 65
    0x10008100720703500455100c4112100080c1860301c80c0a50030342034000380c0003012403a04c42d203141c1505607054440d42c000880010955800c5141008011245101e1062070030a101180f0200d4401c000c00c680001e1230401c88103050b0b0780c692414070f030020040d800590050b10720904000485045840103d9680444c0301701d41d4039642201952140711006074004503c40541c0400c072050b00a000c107292000d45608000c8117059592246180104600b800000e0001900c07040344604c00c10700c000d480044680344803025a00c00004081e50b080030754500000c400c0c2004113000d10700c2048580d0391403950b2a008548141c2890101c02101810f0207280c402a000700004078331a00500d6046000350981308908000003404400c03070b006d81703182c2d240109090503004c40d030380d0101e131100780010f680000c9110199408200071780c81280d28100f4110041b80d80b805500e05011003400494149442030084802e8039002414022085035102802802800748440c90500e00240ca19201e80b613142401c00c4400c0c0603c4441d08 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 309969586 1250 309968336 309968339
    0x130e06070305070c050109031e09120f05070f0e0a1d0d0302030a18050a030e0324190e06040b01090b0603010911070209011401091a0304030c11152104050601 69
    0x40c1e00030680030740480309000038880d0b0000010030900903000414030a5980c07041002101d25079482400d1443c00000600c0400e14042c040012a1054040b08079000801d4004250150500c0350811003503410290076084024000308080c01c040203154044c858285041040c0c1813900544904407510b18001d41060700001d901036000c074400d4014503003001c5544000603106410021000c5000c20035401103500341c1181c00200e0a06801006602802000350040d0103804000062015042581c1a0f0780c00700081440100351381c650b40d640e000c03400146280d0208840c09105444c41c1e070782c481c11141102c6110500d000070501e1513440c001c075800c00d8005450503085034203003168074000c0e219950600007a102c00344035044c01340c1d846c1c140280c001c01218244034040c0da00c0310001002851190050256007400150140c988040c04003182c0e4001d816203001101071b020b61604243c08000c00c0700b11a80540922441070080541070001c2c41d031182d000b01100700201003c50700f489e1f94601102d010f4501d0300003400 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 309970836 1250 309969586 309969601
    0xa020c1504080c090421030e0c0103060e0129161104021c09020f0d080c010c080402130b120111090307050f1804030c1505071803120e01090503100b130e06 68
    0x2150403611461100780035051b071070307020034600b8010308803171001079220002c00c00318a03024054070f1050300e001c0c60103012050800201c02507850041c13080743c1c0d00628170f00d502c20404070302d1080c50b00040503e41ca41580c0c1c9103003580446002d08441801e03140c6025950002c1c9a0303182c28030868481d0042c86282103a60002c6400f84001409652820b0b0381120080c2540c0c8620f507500182000c1c03c80c8582c0307000da147d180c040ca001342140d654125110070f0051503020704c4056991806d0810445501000c0450000640c0b4082200306880c1c0740300e00034a60921030b0101c00c044866000d404610300503400c8964107681e40007017040018810902c160450154081c00d040c070710203214401c0e8403501130305102140341003030703580e022400302c2c0e030066901c06e16076981c24480d0441d805000c000380301250008034011182141c450705010140350865106220580420100b10b074001d00042004010080a40c0d4120112648034000340002d281d00d079200300494607220a407412944500310048048c14000c3c0b01c80d645541 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 309972086 1250 309970836 309970849
    0x43606050f010f030e07170601092009010c150501061b08121f0e061302090f040c02070902123301030914030a020a0303231b07080a020c1504080c 64
    0x181c00f003c050302e401c80c595044004024420040004003089445000441403050138a881038000314001802e0100480c6249107402c102c01d00c03403444034080340da100c500da001690150380608000b0282a8043c40c11000340c15942d1111341203403c551070341c02c1064118003092072604c015500c010003104080c00940c40c028000070103583d20016202d800c0e00e000b210300340907120a011952201a80a0f810320030003560b4106611320050b980100e031401e509000c0d14078000b80300c81c8610b40d6880e001d180d9503600c1d0015103100300801001040483d504640d079460700160a03d003441308846804802801140e040401000e910024084041000c000d003040c00303070070004401500441c07c00b581c0320400b0380900c18806c1c00500080c43c010300300360003e05010040b4030f0040d060307071040301200b05814030381032042d005084002c48036640400c0340420180000c10b0000d20380700700d01440348064020480032600c1000680c0006402600c2030303045811f0f554500c140541e00d00b40d44114052171000750401c1007036407440d00b0900c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 309973336 1250 309972086 309972107
    0x30a020a030e100f0606050a0e0409030e15030405010e0c0a030b130204021206010207051507060506030a0f031106240f01030e030a03060320150307020102043606050f01 74
    0x7450003050101c0301255803807511014021003403856940f820f002207000c24500c6000010119800d141d410710015100290040d208034a940e802203071104003000c201485504105403102009000e0280ea004c91080d802c2d0700d40007168100c919628040e10801901d4000444c2e1442c203c00506158805046076201d5203001300142c600c3c400c8142912280f40140d07201d0018109050003280e0f210f40314903001000914012440d4401c501a50219021420729803d5008550b091500b0401c080f50a864480120745010b003619005421014001c2850040607848101151410300200444071162165460200c0111180304000748408041290070024180308480310078a20341410002000d029000015041d507201c20200f100103039841c0c0b41030040201c4290103120542110444080071110000850711010000000012a150102c0001c200b541300b50100c40103020043ca042d140940041d04e01060000d2000c0c8403c0034850825801460144a00c280e00865400425102c03003c48294015620000b85 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 309974586 1250 309973336 309973357
    0xc0402032d010b1b120304030804050d0e030319120204080c03060f13060b030a0c09060911070804060c020d05010204031a0f04020d0809040e0f030d0c08040c030816020d0303090b150105030a02 84
    0x203940105038845e40341d501651165000340c1740c00c1540d14183c0b91040c2003901160b241c0c3c0900c28402e1000f0720984000080d40c0d410100c0c14100c03c401d6050b408161816110308000c1400d440c0001804640c81801280305c01c1843c03002d408882040c2c03140ca0035601d140c4800c40d20031000c00c42281c0c0034002f02d20660020540307604041d090321908100b50700ca242000d07506400041000d51919400c00104195104891100019140b11820030350380ba910480c0301c0c400c9101c0c4204000300c00310500c0965840c91101d0b01c640b540040219034483d960f00c3c0c10101e0b080c81c03c2da802841c5a0b860001040400c62210083c41558020404070841d802075640720241d41024000030b400c681d03504020800003c0412101c01790294202c015501c80700001203420940b004c0013421010000282c05101c0018200d42190702600d40c0102d40d25140c00680d1150f0f000710f5096803000c2c0d0b1081e16108540d00381a00340d4001d43e510360092030342030466030b00d4110004134240c0010b110f60000b041000011188151a800b8000900340d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 309975836 1250 309974586 309974593
    0x8150a090504030306051f17060307080f100c0c02031c0513080109021017011514040b030a0501050306060105070f1a090d1e1d030c0402032d010b1b 65
    0x200d96540e00100d8004440440200303690360018010b500d03001c10036080034800d4080c090b100f003c800300010b0030b20394400c1d510814561080d010980c00c1c0d40034444103000d020307031200322500e00300c801c151140e0310012038000351400ca26100340100414400c1c01190aa1500907005148038182c1c04c46003040f10f910383c40018104142445070304c602c4c00e6101501070003043c03698004141c148180c010016852143c0c0350a8041c0030003070741201545000303035040d64115814a452801241c40d00041a90400c2650008080301000001c0c04280504980301840c000c1e816100f081000b0303a222000e16540702001da03400b6011400500c05c090014040c0210f26803e1403040400108401d0284011040110b003a0b80101c015004035140400705940300c3c4814520540c07084040740610915200502850180c01855076100b110168031201514108000391200307101501c21517aa10303145001040310011340040d017003855048a182c655175202d40300302c50f0695005568841c5050f0341052030420030254400c0c00c801500 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 309977086 1250 309975836 309975839
    0x4080a1b170c0a0c120501230f0903040807060906110a0305042303010509010c020607030911120a120e040f02040509060616120305060109080a05120d11211608150a 72
    0x381d002c407059006281003e110a400c1c0c0d0f446c80c00382d080d00e03102c0303106840c010f02e0b038600b901d0100d01070980240c101207400491072041d20341c01a86402d41c403490300a01a58800c460707002840c0c560145001f4115500356030742031a1310065400f01615181984005400140d06210078040541c00421800c0d656000303000022484003a800401d007996011201d0001c1e45c0d541d50307450821180c0507ca405c2c0c1c01015841c04201407503080ea10b03181c801180503801402801d044604004038032041220549140d0840c0131002c98104448006056400c40d00c0030a000300d0402c0801042c000640c000da8040e40d80081c0054000e0b512034081c4442600034003003610b08405245014030124003403811003655043d0940d4007140300c7c50400c1c005020580254007a681ca0740c03207124020040f40021903181e181c1c840e18501c041e84c0301110002c140140ca440c02c41c0740502d9a002507001112103524080d220a018000e50041302c950b9801c0f58046411100d01040700030031124000181c4e502c440c0c22a030070720a0401445041c1d520b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 309978336 1250 309977086 309977093
    0x3070302030f0708160f0303080601030b060d06060e010201090b1303051b0309090f0105030607180510110106060201020306010f050d0612080d060b0405130203061804080a1b170c0a 79
    0x10801c4544030b0620b0708010780500c0101c03c28029000101d2045007040e41d01307441c100007400135082c2d07440050208440c0101107403503a0301c01e820061a50303000804568071803040c41060720050150380320314000300303c040450b000c0c40d50040c09540301c8140c201c5400b0000b036480b139100c944a00c0040c04100d08015040010802c08204895042ea00c10071f1039000750345440ca14420305c0b03608000036000e458400c030f5000040145940c0069040e1340000c00b8a400ba8040001c2d92004110413400e40020b58881400410084401da200340601800080070009005c441e5035044144d08034401500c1e03560000701c0140e007083c4207502840081420b030a00d440000703001650340c040d000c4680810306048941c020005440819202c0f1805001c0c090007542813214506480c060000300540d0800042410b00c2da000300004070701e0f80d1004075180302d01410300010040d40c5004e01e002c04055101e5040c07180403640101c807009800445c01c0d548084c00c1e40c03002ca45041c01812800c500081d8110038502d00c0588990307000305000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 309979586 1250 309978336 309978343
    0xf1518030714060a0204030804051315060e0117060a210602030708090c030d09140604080a050f15010b030c03090c030f07063203060112021305010807020d020604110307030203 77
    0x714040c4019821103100c804010b4184000544042c103114010b00050010425550440e0f00b101c1081b075030014541c501c80080c001900009c03443c146141c003082000100180c0012640942c0e6074266604506041da0340c02e450107228040e202c450b04501c1c140d40900100c41080e940d103110a1102d044040b50100c90740e68441642d00031104080096416000e01002c08001c100300d1903855812000b40c442c071a20050700909200d0300d40710350061009103120b08001500c4103000c44001d00000d00c19220ba061a60801d183d88519194403184148502d030680b0103609000d600e4541a00d01c51035a042c51500c0c1c9000640c402d420180c1482540e00a401b2012400e903420044c800c5002e4056000c0c1414610389100500031400907941840b024428001030070740004120604180014045d6801d030f16900c0307100048031018001d00100400030b2002070f81d02c5285481036030b04001c41f2000d036940b0b201a0386c2c1101c220f84514a4648a9025a000c800801d000450504040d404000e01030b088841541d5240c0000b4036 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 309980836 1250 309979586 309979597
    0x50d0906090b0105030607020d081f0306020703090e040b011503180b011a0a0c020607050c0915090a1e050405010b180f060d0302120307030212040503120106020f151803 74
    0x564541e120808800c0001c002d02080c01041e04a000c4d040520f84818069111520048414100700b00e050005819003d020000045d001c90780c403600a1582d101d1400f18000d62046006a0126041c18030020b5005003011015100e55408411615140d28000c0040c030008034140c260818543c944c0102411001581c5054038058003d42520040394580340c05024a04e503803040070f40d00c04da0100000c064060f00301440072442da48c16601c03075548003074a080c42410001d540700b0560384500b000c001d2100743c001c4aa08015414011154070503292540400384003180d401c0358120841403000110340701e81e00b00d1940401d0b4841d00420000c12014241d0340040d840c0100424421510080001800f100052070002e540c4e00c4082a82c0c90124060b1b0703a14040d5503075800610880c00d9500000c0001d00240c0300e03406841501d40d1200b001019070804c1d151060701e80e000040c02c9408021140c0c0002450b40c80010b9488100030118040e000380c44202a5a01c8501320003489861510f2140c0907900c0b40060401c010103 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 309982086 1250 309980836 309980843
    0x6040605040524010906020a1410020f0417010b100309170309100b0405060d0b0406021201060f17060a0b0705010603021e030601080f0304090c11150a0b01090b0906070201050d09 78
    0x51804031103c3c8074102c0c0303140b28016a0401c145441c0500c9810b80010310848003e8205d400749882c1141000d100d4540150741000c414103c1c00441c40c0c19144032031001400c156a80042c2c07034031642910007111400c130b5140640440c0d00680d0f10001c8018030f4007a5101014180c0254404004600400078100880d4404e55442d0300541c4050420390786081c45114110f01c00408803420b2051b810510001221000c104d00060b200c2c0303100c00d020600700405907046481001c107601340c125003985d40b0303040035080c180f8040005002c2046030b4000c000d44034101001e244036041c010f003034011113400e00c11100c0541e000345904492544d622400840541c3c2d40f6002d03c40c0c0251144008016660300500741400e02d0010ba100300519407000500c1018580003000703440a940f86c044002420303001c00ca4045800e14038022102109024980c01070720610070290880703100d0008038809110300303031310f4034011185044c661040d44250441882425981d24181c40202082c50051501a0400e64520b0028040741d05c608401c4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 309983336 1250 309982086 309982111
    0xf010c050601062c0604170319020709271b050405010e0603070b030f04121e0c03020120070809061317070509430206010503010608010b100503060406050405 69
    0x40010840c40d00552902e404d01c1040c650040c2810003240190150740a82c80d40701a26811910040400b041610580b100c940408a29020509006500c1d80014010036812a051071920b0403101c0125032120880307840304a8003542c0080c141c0703406441481c081c07001c503181d0481c0704001070a0799450180c0d901812610102101c1400d0200030180361418503401304140a40502c1041810404551116806600001c203014901480c1c0070465000c4000407002d180f0280d88903801c07542c6503102c0c0c1c8400a89100341c00030450803213450321401c0c0c0091040b6000300002003c00547c40003801400c003034138109002505c60750401146410003041082580c01c0480b602006d01040381d030207034081060000030502500c1d81b880c5420480c103070410b452001440c0c03203003030414001c02d40042c00c2d10f0054264451041c0c1041400032020f542c00948803507080c419240301e9800c10308085242c02042c45600e0300494000c0091390314480e141c03c1528030390030040001c0d07407159803420000f425840c1c2d07010b2030744180c8900410 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 309984586 1250 309983336 309983357
    0x8090a03082a090307080d211d03030609011e0603230103051f1517100e03040906080f030316020715030b13051b07080f070b01082a0f010c05060106 65
    0x51600c5d00320b0700e40c059040c80d48030202c241c881c2e42e0040e2504400c80030414118121048415582e03010b0800144040d203004280400451100e4010004c1c5002e4a411583c02616980c1c03032252490304c0e1210082c07450381c0d0001c884100120f41c0070760300c000d00340507035003511965190308003208468030364090f07000380e403c0d81195544429103c0c00c10b40c400380340c80202401b04842004040d45071140305040c080c4d010038601d002501280c40744104401c510304542e05600340007180c518601552030f40c10038840e5074082814458081210f5101207031412100f10707540300940c2141d8075420b24518848648402c1e601b5409a00d00c081000348203647d42d408100402d403000315400d0b030404244802c40c003680110410301c51420b070a03c070080c0c0025a078110701a030804c05054440e121410189810b01c1078540c003d48404000a58030100110011081c1c125031544066031412178a04007505401310140980610408074910800d6907850f0480b003015200c001803500081900d00d40d591130703180a03000c0c0c00c80408140354044 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 309985836 1250 309984586 309984589
    0xd09030b0c030c0901050918010f090f020909070f20061909020d1202070504091208010503160504150909030e1306050901090b1504030605070e0108090a03082a09 71
    0x5a00e81c208045880c050320b07501d40101501c01c180034800c2a070f41001400901c1d01c680e640c40c1e050b0480d06040002d4407c0c415651000380c7c0c9406c000b079206809010f42808881c0a50703140d00d1080c0d850304040680300441560700c841c0d003200d1085071b006401040c8101d6a200c20704a030100200c00c82400802c90003003c250409440100d6030101a61400d52014100b00311100140c890141010110717600101c05ea41c00c94403450140d090822903003080790003900c1d0094517014401075410440c5a030001d6205c00480f0f90b0de4509240c0c4820842c4070213440f0044403481008a4200341d400480580c4610440440b82031701c6120800aa030500201a80042d41d10000c60704c10f03207485071081c482c080d000c0ba03041151a1030040400d02c6000c05219220410303607602c0004180e40c40701105a210ba0302e0000e5196900ea80340d02d000c034002c00d425501c040020381100e1a41900b0750140800c68015180d00000b8040c070350050754115140340008100b4006810342100c240d80c0010700b40e510b00f880039200a80e56440782d60b441c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 309987086 1250 309985836 309985853
    0x41407030b01080f210a0807050d0c0e0f04180807020a0b0d020d0605060a0212030a0204080f0d14090d1101122d02031e07050405100c03030e0a03050d090c03050d0903 73
    0x310822450280c03055210601d805c000c0444008a100e0f06201e200d5541d00101507500b0301401612020aa0030000e21b4146d007580203c130b2400c60f8108583c0203048407541c0c3c007400111200d025240001288c4060620081081340000e000260301c01482c1da02940c0d141e855601c101e07002101181c241540100c0c030300030b400b00c42d40151006850f0540d40142040401040207580e41c94180700041c02c1d81001020450f55401501103402500c48441101c2e219047e0490540da14010a15070500044c000402c040d001101c8900321a01c00600428848004556071507581c411851201524140f000c0080000c06038049405001c0c11907102103100c0d00886840808041e061280044d1a80c91034410420403034101801c1107000c071000305c0c410a66a0a6a60a0382500c240c82607411440e80040300500d0f9482c00c544c0944801c00c01c1340b09540c02d1052006070070409507151204080100800c0301402000100d800a500100c0c03618000c103403c2d1195aa00e88689007041c1c40012080002008450b0034405d010b03450 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 309988336 1250 309987086 309987103
    0x3040e041109072705030a03051209010207020d020f031e0304050a120b0a09030c0b090d0e0303070b06060d0f09050a060b0915060f0d1503020f0604030506041407030b01080f 76
    0x2e4990101d00d14003041c00070440c000c0320745000d4098949061902041030100c408901600019049804003821402d000e0450303088200164040c0d440d00000032210314040c020355000300c3c1e01420b5001956000d17420400708001c1d0090507609480b1343e0945000d14580000b07d492b0003800c5501075a5501d003400d05004000003150081100b0704442000b0200003000c10010507840203604400040401c011f1a00b15220019680054500c200c80d1081c0484140e01180450803c40c05071217021107026410306240d107a0159800291006880e0400121301b030428400920300c1710610310000490340f044030700d000219001d80200380d8456000312500c0c0e0400466100d0144038003401c903000b008038a420300c29000031425007240c00d4042c000111b0603281d84e6a0328000d481c0c014513082424000600c500081001140441c4020b07403003001d20030030404103030800108075000e885c0c001d00a0b00b02030340d40351504020100600d080101c18465581c0000c0030650382e5410030301801c08440680b500040c603506070791812142c6c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 309989586 1250 309988336 309988339
    0x11515050a05090d03170708160f170a0f020d0f0507050f03070f020102090a080a1b062a05010509152d060301090b0108070513050c0313080c03040e0411 67
    0x10032800d82402e4009060342d840c51000c030390148441c03941c2c1c0750490385038251450410743c1020003405d1000c096040354203a4800d074408030040d0100441e840c1c0c100c84e0f18038102801c1c0041041c1100c14804111002400f0b94010704c41600811851507010744002281d11241541c03a00381d50710300c8040422803440c05082d0b000760305c51800c1418085464401d0031540b0002d0b285a06118800c40c444502c14000c0d0103030741a5100c0205030810856881e000951110648001107a60742e02d0b0001604500c04100e4102c010750f40c6556900c004500303403244407403031081c40c52484810f040200c0305040000300c0900425206807210405426054000c5480801c14035002c0c03c0348145615840c110f00c0440740700444111b1050030280402415101c51011a00408503002d0141080d04da18001081d48080012083c0440d001176502c0660301c10003001d4038048a900303403081030505408002242500c001c0c0d610354101640501d52080c40d00e40c0d132040c82c51465026920801c06403011400700400d001241c1a41c1051100 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 309990836 1250 309989586 309989597
    0xb07060f0509030406050309070b031006022e15080a03020c090a060303120504060207150b13050114010807020f0105011806080c0a03140c0301021b07080f03030a0f020c011515 77
    0x41807600b10b520f034003881c0110800c02801000040407048108903a9005010070702e0500d5590410001014040391240910400f51040c13280a241e41c41404580c0070803008101d14011070500095180700c00b400c03071030804601d440b008001c042903001062001c114290311940051003501c00c80c50510007060300041600d10911718101080000c6501709440a5003410b480d080051250f40f640340c0600207005c0c07800d01402301c01c114110f40744504070726400050031920490b5040e02c000c01c2030b03240070190f4800340a003803032084030901805002c0d406400394540080141c011b1b00c6a850000112600f1a0b000742c0c040c0108550b0809007590206880c03054101800d0054042c1c180c0765400404100d1100603484000c010800030a01080700c030901b44100c40010b00300600a42d039800040c0c01100b1907003007004500c45680031b040030018581c600015a80009901070300030310b0030341ea1042c000300001c0c1424a003030741d40103030200001040201c00b84910301d0070b02e009400000900f070519104104890b100c0828205100 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 309992086 1250 309990836 309990841
    0x20108090708070b0307050f0d05040c2315121509010501091409090304080307030210060b07020d080c1606020d120605010905040b0d021023071e1109010b07060f05 72
    0xa5010840f002913130740c00d0302140c5d901d8a54510840d091310407100c01056229001c201c41e04e0491041e04258040c0c1d014468405100c4d440d0201c001c1e00080584080510390380102c807052030344c1450300c030300301103c980f800c1c00703900b0032000300c031402d841d0103084981c600c082d049211a4801d5141c545040740c05004213280c802c106d43e041409542c5510017400001d40f040f003980b00014202a020000c885c098901c800543c0c0c5c8a071500c0ca0003942d101b0001246051035400c104020030300d10059800d4481c0c9030740082040141d9001c40d2641203a59100180c401e01c00c2c000d00c6520041031210070a8403008100940c01440c0b402c0500c0401411f0300345080d01081039074146101040181c0c3c0c403420b440c040d2501110002001e0010740000340c056003007001b0017900240f00706607028030075400c00881d400800c3c5110040e2260704403188160214808c00b00e009054401481040c0f4041d042ca002c0e844045115200300140e100d00b2000007100054240c0c06414081c5000620b40c1c1000402e00030071190710f51a040030701460 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 309993336 1250 309992086 309992099
    0xe0109030c061d1c11010e030a1b05011103090c0f1e030a05070e040213050106020a0f02041d1c080c040501030903021002070804030308090a11120c060c010204030201080907 76
    0x80d01041d03018051640300e000c91140070010b800701a40c03400c1000200d910740106100c1000c001e0f02c220007038501107510998020340444c0f040c050280310740b550070080c0d803406044050507190080d1420301d4810302d4100c44d1400300010000d20440b41d002c4004c0d0300b170644900e030192040d45804c8412050038040c0e9401442c2c03100503100c403120001e500c3c1e1b10708154201030a29001180c0b8103000e0b044060001d12549400041c002d030a0300e1494041e5000b510000e140350410a03510013610028400c080050f80506000404601046442040d0038801440032400400c20065020f500e5029003a4803920b42060191804040010200d00303030809c0d042c00c201d151460070030108002405644540c505140d01c3c0c0701d501041600c280095800c1c809000720442d29107103581014100c0e0b40041c0011404102c1c2e040c0820061031001175500040d0740e200079108010110f840900c009181003030710940b404e08c18001c0b10f4500381d98071000703494001000b0000503241d6103540001040c02001600c4031070745802005081c07100 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 309994586 1250 309993336 309993347
    0x1f0b04021305010e0d1a0403020606061219090f0302010c0801090b0f13061a04050102070611030706150807090b03070b0316052805030702060703020306062b09080d0e010903 76
    0x111042424002954040f80000c10001c2174201001456111283c145e00300182c42c0904440c0594042e40c2140c1031952110248503030352040c4041502076204481c00141c034202e5000450308945604100494100d82d10340e2030400c80f103c1040d0450140c2d4507504041d40d215482580a401050311082c14850b17840c642c00800c17081e1601d501401c1c028020804c1044a4040c0d035046a0000c1c20350f40340e56921200306601001441e0040e000da036005000b4401c1c00207890b4070510000491038141005540381140030f55800380185408016844a0710204d01c0c00940113809000940003014500000708141c0300450030181000305d980c101400300e010138020f100b207078900218041c0710002d05041403655107182900d80b001c0183e20322400104c00060402650949030302c94091030280e035880e021a2070544a903d415420382c041207809642000b0203000035600a02081c038020590711442031a9040344541c40c0b01001550441c1006071994600019824005500d620407102e42c03c880b10000c0110400701c1e03400030039 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 309995836 1250 309994586 309994589
    0x110f18010f1b030c0206040302060a0507110102030301150e03010615030f180c0b13030803010332030904020d0e01060909120e2110090302070f0515040b13081f0b040213 74
    0x2c00c1413152500045454507000c56000d590000c0039581c8441900000420f1680401c80850f400c0882114000c00c0d54000025641640c0f294040c4084885004c0c000311003406180d00ca0990641d2a8200003c1600098841e030442080644c0c011404400c1243c217041600d83e2500c0b500003041819040700045010401100300f62503640005542d10200c4c0c42c12800c140c0e106410140048400000000400020203001e07192a4604c40e00036080350440200c0d806030300c3e5134040140b1260000c005600b5145013a5004151104103c1c50010381d4580e40c402181c02c5804503000651007590b00c0d687c0d9400e0015030341c1030140310102450030030315800c202c10200e503025280c0b03a00c40e03811492000c8d40541d103440c1448801d13101810480c00304100c03c0b160a0083d41c0d10058840e1200362034907070324041268140702560760b240c08000c091407440c091511004c584580c2c014413940320750301452200858041810310458102008030079082171402400c0180c103080b28085082c1900c0303a48104045078084540005000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 309997086 1250 309995836 309995843
    0x90209011403160f050607030c06050901022709010302040f090605040f170c0d050d14040c0906050406080a020f03010b0a0e010f0e01120314041703030108240a110f18010f1b 76
    0x3a111f1344249800e555000f06500d0041041d4101720070010200c2c41540502204080c0000e800c0d001c0310744190450042d20000001904444c0d00e200500240c2815080305d0004280c03110001aa0030050b100c0000700c91050394210f4900100d020305100f80115126a00e0703d4071844080c80c0c0ca404910030100390f4524031080c0500c18024082544140c0c24182e5003d158404c1004030f00001c2850180390541294100e401503031a40ca2400b0804035040c20a40f184800b644d10445c001c0841b08410b408201540140b5800154035640f1126a9000c039101d141e00c0c01d00801a283d031140081d41803070044541c403003c43d0003503d15a009800100541d801c1051003240c030b00d805003003ca0b846c0300d0b0400c0080c41351150341c115202200a5041c008101800040114100d4210205032445178032100c8841036004000041d058007403200c2d501080c0303980c138680d02424820002540091814504103d40d840d1900420140080401007106100040d40c1040103407804070580d01e03103440d030060101c0c1d001051150851018 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 309998336 1250 309997086 309997099
    0x51906081e072103140a121415010e1207031208070804081209100213140402130b0c010e06040309061b080a18030c0806040c140a0e0406090209011403160f05 69
    0x2000703042c0030350401e003800540d501200da40ca02e02d11b0740107081241c50042448144d45055048100c110011410301d0040d18548001c441e21034140b001103440031085c42507039612030041d6000c075401c0752082014500640c0709510b00c052140d010340d40078069400007481d02003808442d50801c00041c000004980d20220f54110403d8152100d21000c0d191140000c08a0340041c8005440b004d85019a01c01400729501030280d4440368006200303010a074014514a8161036011132400d1060400c0c1101820100c0c0b446000000e1114103030500c00d24004d002c3c1d60560124459010074082e0950141a03400070354080b18008121000603a9251820701c0b0b0a034804042000d84020045a280b58018580046030803c5242c2c502c151034002080e01d031082a00e08454001120000061110900c00303445d480d602c00401c41d0a01d54584502126014001001154650f40e94440c0b80c005a4405005a001c0c3c441d02504400c420004420f1611f8940104410552840f01e54010001c0c0710008100e401555000c0c1c03840c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 309999586 1250 309998336 309998399
    0x20c03090907020c150c070609081e030f03041104050c09010f031a0904050601060f0822030c020619030608011503140f03120709061b0204051906081e07 67
    0x100c1c2400342204c103941d40b2046050800042c8070806002c0d20313082090300c00351070315181c2d201790a442001d041d209154451b08001519481400f0207040035000c251b00e1000e0f00e180c6564100ea54071240d00c21281100d0f28404484008a030303081a124a591042c8001140e0780341c10445400a00003a240d001c04400709519120590304d40205440ac0c00321016019050401720b0030145862030303d8150900940c40029036200700440e00511131701200340107445020742ea1141e9845102040807110510a05074144102990404e0040c0c0f20000203110b40140001c41d03050100140744002c0654029a00c600300726810035076035030942c55908115004503940101c0e4111016100515903007400590440304000c1c0c08041859401c28a59801140c1300e0452551340d018a20b0312164190f694040d1645041c01c55101c00002d000181859849540c00143d1844000c11810248003030b2800e451064000c1c50090300801c2c2c0d02802102051240070305521940003401c917807402c00f013100d24507212103413420f4405640900c0b07 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 310000836 1250 309999586 309999601
    0x206090415120515100509070c0c0e16020c03010507050d0b040b06030f0114010c0c091802060a051804050405060714090301060e0402010e010207081b060909010f061101020c030909 79
    0x81c18001800c0d440210707100004903040440c0c40d03c9089035400200d995680c0080e03100d2038168100d40a8030310040c042509925004802c030b445405200003120012455a8082842581c4860702c0348621a41000d1201074115818000d062101045207a0700aa040c9014811200c0d0031606072120302802003400142183d0201c00100608003188445800000000502603d0109c0c0390000307050303c5180600c444000072030320045402a62440c40604040e10601041c80002059045601e0040511a007551900d549400044d40d80d4064800800441c20000340c40c0c14640e14260030184003101210104110700d01074558036115140201044100061100e0311500100502e06640842002400030040c0d5500d4070200d80407050241ea06034007041d113500300e481c0a03601c0001c2000035110000007901c03829010f00c00749079030032002e0701800b03510100610101406440b40d000c00e034000c003058017145a00e146480d10180c842c0682c0d806030f403d140d0040000c080c1001c0c000003201e03003829095442d2503e5a48410 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 310002086 1250 310000836 310000871
    0x30f0b04020f03040507080a0b070c05160e070207090e0309040b1c200607030c02040b0607020402120a0507020f0304060f030908030a09051608060c030406140c2502060904 75
    0x101a58000d00c0411014001141100a907108603c6102211034498031000d2499075500440c1c0b00910b601503030b1002440040c030941c01580c20394490b004462202c40701d840d0303002d4101200e4101310020108501000001e980c10044071000f802c0c80503041000d4419200745613124401c9404960066840b60030307a209686481d5119203411900e00410790324909a807502000e1914000d0141c07188104c00c203d00340042c83d000e0100d400070341e0f1640303c404400030076500307000141425003980d0350b000f081400300d840941c44600082060f482070b44503a03400751804006040450b08058408001c66004040784000c007800001117402703952080c00e000c0480f50100c80214060180e012008080030700200c1809502c41c42c6800ca40341f502c0c03041040d26000b900703d910146620305d940c815030102da40580e0104072041908001503400c24080d0001207208201d0107091551403605840503c406040014404025414001d524a03d103031195000c900300152074002501d14001d9001143c812a03903005ca9100d0000c0c81d2 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 310003336 1250 310002086 310002101
    0x40f09170f04051c150605130c020c040e0303011d04080307050d18080a0306050603061c02030c030a050703050705060f0409050703090b0112020a050a0302011413051908010e1507030f 80
    0xb05855100c1135062098500302c816041c00310780c00a25040a880e680f280b5005072401c0e60805018040100c80036410b15014018105410055015440340c50009480700e0042c408a98000f10085a4a5160000c1d0f00d80560700301500714050407840c400d0000060320314040b07070340005403407800c5030b02c80071001c41d03c02c000d1a4000800b0031132081c0e911000c0820984001074901c00c0440d407420085c1c80e640d2814451144411100349074810200d00099215101183c4580506400078085444107104070703022a2402c441e039070040e0b4155201400800c1084420010140603000170340d041420b05d150820880d007a409180502c209541e21803000139001071003540100145504440c60000c2544d4a90300340328140c00c2030000f40e010b4109840045803909221000d5000c6030381c1131359444aa03020518202030143c01110042002c00e030b83e05000161682e51040c00307240080003030340a150540c94000c0d007500319041c416581002d03400408042c0a003204044980f6407141c0c2506020650b610502189001080034 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 310004586 1250 310003336 310003339
    0x909041a0a0603110f0a0501120f0f05180d02060f090a02090a05070306051233100501110d0807110a1a010303030c110606150403021e040f09170f0405 66
    0x19038003080300c21040340d0031440c01c4900440615445140ea4018001c16070320801255422611a0764100301079441043d4260104180e004005010801c8405040030f46036102409440e4544500900854014080030440d6400400c1d0040000c0020a00003070f444070340003001c0344074400d03580c800a14405000d10100403507036401802d903284c6180c603d40f1407004000a44101c400607141c03042c01f0925007804003850764001ca600c00206207100c00801d028100130303c00da21000003d0402d4007825134080c07006401d07900519000c00c0c2601c0150070b00d0700060417411140381c099000da2082400a10320740e040309449401c0040c6281010900c460001c4461400c080c40a00800300020300b00810750703000307044030418144c9110b9035060010348112041100c20034100740f40c5e0b88980d0000d02c085102032919036413280d249002c0180c081e040503a60f400013042c04c030000d44c100e00030307a1000c48440074a00c0c0c28458030100306d072a01401c00104e0801c1d00c072983c0c1215034072003010b030040000038610145062072058030002e110 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 310005836 1250 310004586 310004633
    0xa03030c0b0403140d090b060607020a03120e060403030c03080f130327030327030312050403211d01060b0d1104030210120f14190f020d0213050306060105090904 71
    0x122001105d00602d554101a6400280d40c000b0907000e18200003120092500200788894440c2146c81d411400c04207000160180b1106100182280d11258042d000a501a4035610031814003820301808003907004100d1100034559074204242c483d41d04080d14203003a0540b80c07642111060006c003a030501d000741222b2008600c1c105002041551141e400c0d0360708640741b2644203112522083c0d200103001c1c00e000040201b5481c010005500c0c0190b44403950050280c40c2250007400c40c180d540c902c5c0705900c8080340c000c0d52220042034084095034135100d0b2070340365400200541c624141c86135005005005808409544a680449540541c503007682c0240d50010549410365800e54006000e0705481510000700c1810240340720b103c07080612941c0d6210070348a0800754155034074021144408422507042d105070b6521140c80030081030354070250030704600511005a40d407400c1c0c00850107608079540041e1280c2e0202080104503640102500d011042c0bd50b142c0300c0603200e0f40351001860a030120300c880406c4 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 310007086 1250 310005836 310005847
    0x190902030c060c07090b03060402031e100501090e0124051c050d05090316030f03080702010f060609051e03030f1b0f010c0306150206040305180405160207050a03030c0b040314 77
    0x40e07002ca50781c070031254101c0c0d0802501b2444818542c5441007290069416088176285100e01a04040104944e0070914103580c0444900e0520b07804031030003a000910907a03686e10785158224000d2050201c45110018448004c400700d00c0c460741d02e040310707000301c90042003103869640c586c1910031035a00031581c0c48004d4540c150340070715000302250807040d02241f20748601c00d0303400104c00110b2201404c1d80e40001850795001c505490a0303900d50006080f00045660340c1e10220740244c404d1061074044c10003981c90700601860641041034281000c4840c0b8030840d0340c00045802c2d0b03a00042110410306000c0b03407403601c0e80d40540c0342c400c42e216040e0041c0c071940079008004034107482c19401018583d1064800700896a06c81020084d44900390b544d400142c0e00010100300441c0c021030242c18021440d0100d00246841e00303010400b9600c0a0720003160914812002c41051038044c408280509025100c80052030301d1074600030040148048050024900040820305040c8288002500f80f41100c1040c1d5449 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 310008336 1250 310007086 310007107
    0xe1e1c060203040b100b0415141b2103060904020a05030d030605010914010206040b061914330f040914041109360f0607030b030105190902030c06 64
    0x1d500031281102c40080020028a00d075060181410966807400c660b503003020300b0288c1ca404011030098404090209101c0c07034507803501014004255107044101204400c0260b00316031443d05080404068011900c00c1103034007810a00020b07660311110480f03512b851601d480c004075003c1c4030f150f08817540601501071120105031701900654110f03002aa95882e00e00c0c1c0d200000300c02604642c0a05006822101c0858045800c651150f07400403c01082c1c086d40b030002d40782c09500305540f0303400000c1c22142100040900e00c0d12590010250308c0454200900322549410a9110860030000c0698078201050b9844142514010b941c09403074990410442003030061404400c100086504a40350101c0301042c1c900c50411100300c078026100c201586c0380048101c0c006407080130303000c0f102c0c034105d49100e0b410001c141000c0060f130150030020000f409441c00c0441c00141514a20360160380260704200c148611100310700d030340003040c100071003001844091034400282813121084500e58041070214010901 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 310009586 1250 310008336 310008341
    0xc050406060f0207080c0a0b0904060b031602120702010206012612030103050c03070506030a1806060b03060a06090e0402010f051b0d0f0215040609020a031502090f010e1e1c06 77
    0x4000c00b035021110520740c0c07401d03810354683c1403c0e030701508a55010300412407049003101070b0031240401070010074155100c1d00c4402c8107410488200f0850040c0d1445c01d20180d0b01841400b141013078128640d0318012041c6c0003c2c2d51007106201d240e003000120306040e5a003d10051950b110268071005440c00b660300344101e010035070000c1c0415565401006180c000c0c901e40060f0f1501103074009000d040c2940c0d40d4058010007083e03051005100d4400c2100d5000019085200b0100034021003c41d480d140c3c2040300030b01001103415008034041c81142d80d0248250b540e00d105c4268001c0e0b0920389001c2684400008030f5036070144e8a61168442503000c1414100031020400540240096580401c900c090040c01c076518503d040c00a01d00510f810041000316030150002040c050000d030016469030f50300d50350104201a10980c0f01d01c590790104501199162044004020380c109107400d01030100030704002100d0b90320004030020359003a40f40c0000354030303101c080d0301c2c1d1401d135075140200c009640581461400b = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 310010836 1250 310009586 310009607
    0x804030506010314010507080c0904060e100e0f0903090d0f1a07020105071407260706020405041811010c1e0609050606010f020d030903090b030103060902040f0b030c0d0c05040606 79
    0x810780d131081044500943e05110382032003410715660301482620341031a0401c840c0c0c004400b20740c0044d211034011030184500710b001e5000308040c0644007013840c60500b1034200c03000c020b0090750700450100d0a10203032040020990355408400c40780102c00c074055240031100c000314014000c1806409030350070003511a0180381c1c20300ca021190001c0c13019640c0c0780011118203d0310b50700300c051100c040c0300740300c00305460300c8102d550700308000440c92080343c10700f254860607000b80c202203521b241c00280a004504090040b1803034200c014201500004140c1d40310301e10341c80200d0480d41004602038000091141d902000300005059076403501c10340220f801c000014001d281001d541c20312440b000325219500c81c04032140403000c945c2c080c0c00703903600f1240c003100601007a0000707904201c0120b10114508040000450003940f1032480003078145403500c140802e9600451038084050b02d0030034820040d44012484c0d030441441251150962152403404001411040e04011303009450148041151171b0081c23071204 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 310012086 1250 310010836 310010843
    0xc042304050a0e0d1103040905100602070e0c07020405090c0a0b12060a030f021e060318061b09060c0109201c020a0308181807030605060306092208040305060103 71
    0x101da651000080401da5041080004195001c24142d000d0703540b02d4102502c1e6040400c0540b4503241e81c85802c80d081e100c0c150f444000111590008101050b01084500300801700d0740c80001c501d2804052140190007050300182c042c0f038440d0f000681c0b120060204c40ca802e8801403038010390341c2e1180750001c0c10b0781000b00401a58200315001c18560700d00307240c00cbc2c01100d80c0141d0200c2c103004c196090000a5111081a9100d2040b540440e5502c1d17480d00090341c4243c20720038900310f068a115060910704280030340741c07110711803484910741f9801544104031102c1c50000c3c1c81c0307990740d91240c3c107030540141280480903140c07034000004244903006d205441502074108880030481c0307104400c6192981070a54500075413100c02c040301000001c5a11000d05203010000c03061903000b0000d0000f00384010b101450124507100382c1401c0000315a0113204000c003034402070390418258a1303d074020036214200a42401058040c006a640000400b00c284c07a1040e5445038030aa00c85680e03140481d9249020f01040303 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 310013336 1250 310012086 310012091
    0x1e030d0f0e2d0105040507210605150103060b090307060f110709090b0702061312030b030303180f0d050d02070c05060409021905070308270d02060117010b01020d080c042304 76
    0x20702d805081406054025a00400504542031a08168421585e010b01a001c1060801086400851650720a0a100c0c110512602c03403603c444400040444e00e16070401c1c9a0300000740140001c541700081d48100307560044c100b101500300004000d40700801c4c0700030280010f100340007010515120319040b8840d0103101341c00881003500d801d4003e0340c072028200d50700c00006071102116008150002030160040109040010f4190144c0002c40c7c1141e20480710319109001900352200d43d4142000100300701c0303100074080c02404403400b0008080b4404c4958440f410340d008501682400841d2001400608004048661fa0350303850042002a4004032054946c80d003041e00489141c2e402101140d21b010741c9582d43e0000c0340d0300c20030764448291810f4030400000a11003411090076508002112048811f6001000113624118603500c08180041100b00c507a410701d8450f00c1d2503600040d01c0c50001c4c1032401d220885075561941a039080c003565008800e003030300c0c1c04000e6461150040209001e0301c0c00b034809 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 310014586 1250 310013336 310013413
    0xe030c0109110a0501170c04090204141206090c090a0b120d0305061c02100e1504080609030f04170c060a05030604150e060105070503091e031e030d0f0e 67
    0x800480f45018070420f0b010a030318110b00607088200034005a4007280b142030560030281c48242d4041241c000c1c3e04841900b4054a055084c1c2d49081002c031845040d102d80180b52518084908a03100c000004409003c2d01017580843d103107068581110500d1200541404401080c0ad80000e83d41c526482c14100400e00c2d210101d0b90707505002d00403012442d040b596040b500310b240d500740701e07a032480c40c115281003003450403560503550f45d00001404240000c1c0145a140d0b07081c100ba5600f4010041d1540056500410841e00003011030001d40c0d0841e8880c1d0002038a21300c0700103146042803421099180e00500001354031030350981003000395000c1c0100742c5040050320206848140d0f03419250060b20952406000000c3c0e06602c034000810301d82d80f05130b065038140081c400100d200b150f4141c40c0010004c00130312100d800c6050400048100300c2c9001c000e4040000c6291032952644500c41e90480d2140d100c0c000120542c3c51900f203003541d04002c208464104210850000082c0d140488417804000344064 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 310015836 1250 310014586 310014589
    0x1e09090f0601020d120915020405030c0418031803080c160909030c02040203130602040f24050409050c0408100509010e0304032d0f051f05010608060d03030e030c010911 74
    0x1200e611540c01a0014480a8030440f001d40d10503c00c02d281903a410b031a1220f40000039000c2e42e01c00d040031801840035807201c0c20602054100815239800e6800b4074a00390413071190151880d01052440d070541840051103086002ca03612540389500007400c464070005100580c40c0d00010000b2440344204d900003803180d11307a40c8080654140800150015407400b030304402500d01039005580107581d182a18080300c04603030710801a60001e40c8241050f009a180c01c000d08800d44004501c0d40310081007012444007401c10144c214040c900640c01180d80c0c40d00002c55007142d43d03045802400c0a4012601300d296140300704c3d0040d00d800c071414501d0b5401c00c684050740f080c00000340c0c2c0079260300800010741034848101d81003a00b42c3c100444500c190101001101207401540350529032402000901403031601d0110b00042c00444200c030501140c500340040051170b0f800720416411840c1214400351a0b06181411005011500a0503006000003d84242a034105520440d6898403032000490340004500 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 310017086 1250 310015836 310015861
    0x6050406062f0f0a1101020303100902070501060e0c09010e06030601090308030c1b03190c0c03120c02120c0a05040510050108180d050a0e0405090c01030c02031e0909 73
    0x128850101d00112002e00360079500c2000b165049000c00700100300100010440c0740341c24240c10803840160882c038107201c1486001d08915050755030030f000440c5036003403080e800395015003d03115a10516901003480e00401c030082d0007010041c105016610410305210154941c00e601c4566081c3c08101c00d810851803a007048000c0c5c0e40700d0401610742000491654889285650004190401d603c034108620158104c0600e000d002c40c81380d02004544900003400c00039903504141c1018400d000080e80341800180710b8070070000c15641e11100d5003003000c2c5007100560700c1c2039490100a6000103140440c500000c400500d102d00301d441101e50140507591841444102ca0060356a64040660321905001c15401422400d401c0401e001c80c805c07242e0440146e2500f08060264010001000005c41c03d000c01e9108100e003410107022102004107082202d03806076200ca8031101c1505043c3c071010b500784ac0701d0007801612040047e08999404422840f84860040c5d4400f0204c10b120314064004035141c9101c00 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 310018336 1250 310017086 310017089
    0xc0a0602030f0702120307060e10152315030601090603020f160503040b0403050709050105120c0f0a0801020313210f0c06110a0f030c020f0601050d170f0a0306050406 73
    0x10340141d803030030302c1c91040c1e052681d01060040c0d030041560240860340072401c00052811901821001402080220341d9509105010311074107801801c01ca51081da1004113a6280c0440700c28228041038060a0302c048511520000c0c00b40d54003918940c100b04500f0780d070380000c40c420b21003607a1700c0010a8945405808a009541c2c410300601814800c044060020990140c04140a1812a803c140d9a90540038855000e81c2084034143c01c510030800040d03140c1d000d514054601140c401e204c010f25403080c00e42daa0070074001c00788240ca6100927091244c848032a014050210b1100965a902c0c20850000503543e61140860300360400f81074020b200000100b1840b01e83c1c1c010b41d00c80f04c0c41440540c044800c0c80002c0d20683d4401c1e0768101c11103030b5400101c0105045000341c0c83e188400c01c0140c2d00a0100c61002468500350b40000ca0038121100d80810000d05481084035880021500340c00d191000006140007000c030060002422801804488003070040b05410383d8040c069075031104140400e46285 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 310019586 1250 310018336 310018349
    0x412031a0d03090e010b04030b16051c140f060d150f0f06180b03060118140103030c050d020f03091c1209230105030f15041a04140105010219030908011d0c0a 69
    0x9660204040380c4900404007250f40c0c00389800cbe400c114240d00310f0140400800c4020107140e581368100e007a40c5289540241d4820541c604100d490300d04200842c50b0b001045c0030080c00b0200881e81100780c04069407040380300c010840c4c800c01c407610b982c03070b10f9200500c02170062405446111459410205c2719010341c0180301c03406000b0f81580d03440c0901d038440c0041000c4401c410241c5802580125400c0c0170400d6000310301036510403201c00c8031401c0040c1000c140501542c115000094000c020342800070464040b11819910480c0b15017840c4030540e1040e0756084020a954241c10185281a503c0000d074020384078691022300d200a40b600821420184044038180450300600026990f0589010381580c07107101c01c4610500c80e4585000079085856161142c2d03144c140440e20034003507081c540f00e1454610314149040006505000010b5a1007080300126290842084c503100f01305442010301c000240b8140000780100483d0302c4904c003407000b40803180c00f21845041d500f040320b8940548180100e901 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 310020836 1250 310019586 310019603
    0x3050f100f0231051e0f0f09011211060310081009030207060c020f0306070f030b010305041e0305040b0f07290403120e120d050f0412031a0d03090e010b0403 69
    0x2076010445040400fa031403907603034105030400040c0549484000d5600b059400040118440013113040041c1c4009000002d07001d4a80c032600d011442d00c5c0c000760300c0c1c150340a42c2c9079080c0542651030414280704001c1c204a802c40804028003c249408412810699441c60165a0b0a0809141d00001c4030038488015006a10040c820000503000d038580e0340020f030024100c011103526040c040703032800320192003150010340107091500550f5414801c00602200910b030a00c87c90800d9124030541c010380300c0d00701c180101040411400c050203003003150b0080684000f511b48900c0c0e40c04e0100c40d15003120205079421000f110300c4c1d2102c140403c0100807100860325503c8030944880e101219000c054089256a00d0b80d01c20408100c003208104d4401d008407507214081c1c0e55060520301d5030a68001512001050160130207000014240f44c0707111580900324540041c1941c0103e2410300c0a68400d07036861b402192524110080c16803054040003502c0c001c4500b40b00b5642d032407a804405101e14400a400c441 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 310022086 1250 310020836 310020877
    0xf0c05120c180303070b070912020306010b0f2a1005071e0e04020f07110405160f0c0f0f0b01080c060a031805160f12021f0903050f100f02 61
    0x45001000d0451460b4404500041503911000f01c1d256a0016109450b10083e400030807072420750000403031020b8181c4624094144c4a41d40c086580c9041c1802190f81c80c0030301054040898180da130580300045003100d070040d03503a03504411031040150305403814480c80c01410b0540081d80c0c0c0c2802103500604c4176513126400d920411511a00c0e5040c048c100c0c00c10806402c42c20200c03030b61540041e0a80c80d0160003210340d10034036850840030f0300300360720840d0340a1428041001040c052013040c01190365000e0600704010198010300b120b0944a00100511018082c88503806119100c1c0c1c00808032407050f9207040080c0d80313a00034a9603034151841c1d850360250007000803070010792003a0401820360400c402c0c80000c040555a44508060010402100402d1580001c0001d0801015400010125001541c03402946a000706082c4110006d010b020300c01c080d03100941d040c1c070a144510081d034101e41a5540d00d50540042c6131a1a451020f0035900d50400c84c2d24410012103101300c420b401f408241201002c0c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 310023336 1250 310022086 310022101
    0xf0803040c15051801020703051006090e07030b0c07031106010608151206150409060f020a021b030706081305010c081e060310050405120a050d0c080601080109020c0307150f0c0512 79
    0x64130308071059045014031100000040d908200c0c140580d41402c5d80825050705119040742110f42c03034400c07070380d26510000c810030110701188242c1d5084130407048084d03038844581c02c0941d44407035052000c0c081c5100b00d1000043c0603074040c1100e409159455072042c2191906400c0040020048600c040f25802c1400411045404d44503001d05451001d1f00101d07140d81c003610360000700c4820480b00300d101a000030301143d44690600007d0055245242d00101d055021390101c0e580d49402c2c01050280000180807914070110304406031301d9680d2050082c484442000002005424280c940e40c44203010b01342c103034031040e000041242c850b1784e010380200644003801603103038041c0c82c026000307907810f014054a02541e02a0340008144000c0f00d61902c560342c50724901210220303034030000c2103400c101c000c0e02440407580e4402c1400341140c02401000d80c445290001c004c0c198800c55074001c0001c182070008900310011900300a414900c1c10000b0008500c41404c1507c8503c118464032060180030000140c1c103 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 310024586 1250 310023336 310023367
    0x6040b03070521060a060501020d090305031204140307050c0a0503071208070c0e07080601020d0e0303030a0c020f03161101030504080a1d1003021b0304300f0803040c1505 75
    0x141501c402d0900070840074120504000c020b035400c01d407176600c0b02c900380b0032540c041041d8032b40e6103010300c0d08943e424555110151280120343c9400b28a03080c560114041c410040411b03000a1010000c3c4c0c3e6aa405500c0e0195403402500b070801d000b130000c95000101441c01042030002c80b4003030382035294003511503a2500c101d507000280c111804d8014480104400a491548511490194a13014464100345001900c0c1c0040b200f011810412440040d6a40b61000b0050b6508481e081d000030460110005003070741408100182c0465900c4045140e115689d451941c4150b6240100d541c103082ea0260401142520400c940284c078411042010b540711038410202890340c450000c5050344854107400c005041704160007240c1c1c0000342c001c90100c10801c2c0e0135812201d04c051040c0110f03d0540341c40c00c501383c000140c1e50490280d608800c1e00c2d00030303145481c1c01c2030240d5a121070001201851490030300001e40041e90161180256482c0100301c0c034003003444a802c0260f0a803145400d0040c1d56034150385 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 310025836 1250 310024586 310024609
    0x12090d0e101b050303090312090109030e0d060e0102160c21020616080f0c0f0d210b04090804030c0b04030201050319020c0a081e1306050901021e03040e06040b030705 73
    0x4460358020002d03404244140043c60080d01c841014603900e0415114441d40f41c1170140103000d041e4580341040000070340108514800000a0321411000100c030f05203140101501803103a00107500014085501504400307003d001d40d44640004142c1545070030b4442e204c0c0031811a1007441e40c1a108255001d481c0c0301c000f41040c00c0c142200d454003480d25590342e00c4181c002c524503030000c0c54007084e000d21403c81445000d13030b0045030000074041502d04040c010021103c034000201d05200003416402c1140311504030040e0040301030011f0001454a00e4821081e0f441440255584c4450b49d6020882d2520700b0308450440350140d483c00c3c259142d03072000e000070700c001e88103041d401d5500f007060710660030003446607400780b0703002e901c0a6481e008103407032132044aa41059030328003506040060031440801c800103036080d00d070186401ca448008140040c1d01d010600d0348100d002c000d50b4560a0080b01c4000014130a0303e121000c0740d07040b0348a01b0140415a1000400280d16400004060046040c001c03032200e0b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 310027086 1250 310025836 310025867
    0x2061b03160809100c08070801081501051207030512090102160e010b090d050105040c031506050108040605041a09030a020706031a040509030d0609140106080403080103030e0a030812090d0e10 84
    0x301066101c3da641e80c12036a100201700c01041e00841000300c115044542e0702c0c010100312020b8030103030701e580d645280b4a0405015542c030525a2601c0030016020810501c2c026690083c100d80420000c04110551500a102070b80d00501c2a00150209041d02c10a04001c90f42d074a00d480759207034200b1a810740c0700d4201840040d00059000c01100200710240952402107000c4c000038848681182840452400ca803000c00036503d0401c9002c0015076800010285d02641026000800b81c441d45080c2565640012201ca052030100c0305010f5240d41c040300501c0c40ea0041d030201da2510350b440d08140d0039030b4020b060307443c840400212258442c0c1020b0700480d52101c04442503d10f448000c0e01ea40b4100c5010380c005806442e80c440f4840381d84c10f1164103e6014040605250303049207081d0b60300400010381400014208140300103118075588a50a410303020315840046140c90344c241001d102c546d0f5404403417030b414900c1a003600910a0307000d500705403a0001d000d01801102507041c42d0a03510b000e43e418580 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 310028336 1250 310027086 310027093
    0x6020c0f1b06121503120a0c030e0402030c0a12060b0a02030d060806130305130504020301081e060112140304150c050d0f0816020f0706030516090b070b0603030c0106030302061b03160809 82
    0x8080a201b00240441d58054944200710481401c000380300780c1e8240c0b80940110301c100248483d1858003000e5480310242807904a01d80455020070202901940d0301c440c14841010810a10164001c0041c00680000e101c007044034544c4e6900c00e50391383c0402d444403098080010f5030000402d02c40c1c4010f0441c11620440403000d650341d007010400700d074002d03440341a4a03040384000c070664007140403000c000d00c40300d5401880a94100381560b0303055a00a040200001c100e03251031074000c4814800d941c02002100d08280791807007003550107000c0c4007030724008440c5c90040c440312020190084004103100c0c40c440c0e460481c5683c650aa80503440d1001c102c1c1c00a6100711100c03004400020480d0a014148a96001c1900d04054000a10361514588250148054030b4000d0040304180c0c01074030540d03600b160281801d42c9070f807070120b41140300b1548484080d5080c4107010041c5a00056050b00405030300020482c620307054424091b05020075a9038850b000c09003052042c1c02d030b2003100102c0d00407640d40c0a4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 310029586 1250 310028336 310028353
    0x1c0308060103230c090406060e0901051017010b04090c03140609090f06090a03020d09140904020402070605040b150607030504090c050903060f0603070f030b040f06020c0f1b06121503 80
    0xc801d2003048031000c00a04c4001020034807400c0c54001d410081140f404d000d183c54030610002265460140a501c2c000c0d00340816000d1190710074000c841429542640301055940c5454032114140d00c10b02440310680e05005244070f482d4428810a07620114613502051a41c0713680c2c0411000ba00c0141541400d031140d40100d020559060220f83c1c05900c440d030052029020614029041c42c000062000c248028850200400d0381c120121814480d01180e1400700c699440c40010b00074001d1000140045141030300304810090112052030140881903481111840b02d1020003100b4480c1c40310080000b00140800c00000c421070f0840300000105050050170305404401213417501004440b0444420602e0050240324241030114902901e1401f545c424038500b9a1142107006c08082c000910741d24140d200300c0280100f0303905035400099084241c0c2e00b0320100025081c3d44520645003445001002c03280b81d0a10b2825104692400c00112950a10303540d40f001020540203a0000142e014020540d0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 310030836 1250 310029586 310029641
    0x1707111b01210f06140a050910030609030314070309030311090d0f06180c0e060a0e160e0406080106050316081f11120f0a0e071514030103111c0308060103 68
    0x61340d019007050a420402200ca030300030001518100c0d44141e000707841440c1840030480300c0c550780701d040e00e4221001090b4041e00d85000c900900c040c1c0c03400e030102c00086091017815a410340008408a00a070340030b21441c9800403118110b0710513081916485403d100c04000082c0108201c200c103c4d0080400140340200403000c0e450704002107004845000e080082401103078000c010301600410161100051a401e16140444810b00502410026600d409a40c062030744a10004038085102410601c03a090780c4c1d01882e40a844180a078a00c40d001d481ca4251510f20500c6092081b030384101c004140c0320b0401c14134041c000b11107030101c0202a485040c0d600d802c441c2039009100180b469500c501880ca491384010440d0000908800b900e141406000c1c1c14203100050302d00240d40e90f480b540c18079014413050560f042c1c42041d8008100e0308010000100340310214011031480001995146401c44080b1100d004c0d11650140c010042000c4d040820142d502c03d81c001c290003025181540c403110b01802 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 310032086 1250 310030836 310030841
    0x101209020d0b100602030c03160609050d1206060309120305100e0f0417070b150d021201020415020f030a030c0e030a060b03010e010207020306060603071707111b01210f 74
    0x168250394600c092003e01814800382c6210200425181c80a1410a6003c1488030b8480c031442500f03032825100368443c981444a03a90100c003003030f0ba2040407203540707440311800505042d071401e2000c45902d1072308100080e810b0081c000e01f00401e1b80420148100180d0140c207400614015002c030520000307242021072480c0700d105001c5e00551b2030f441082c0d010310b0b15107850120102200d2000c100d1400511445000440019800d43c000d008039103207a60064045012034020750402002a6000c04e000300000781a00066004005071103801164140052904800f0381c4d40e441840c0301850150320400650707100f14402c1d8130000d0b2805482c6880681d0390582d100003894201c0c0240e0540e03502d55200b4025400e4682485404262181c080007981008501d8001a407a400700401e1540078110000c0000c600d10b2207040c4603807002101e1107400306281002f51005016480c0010204880c0c4201f569403180200800d07455079501070144d4610404044031001032a0485504442108042c1c549a03901055141070 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 310033336 1250 310032086 310032109
    0xf06080f010204051f080402040e01020d02360109090c020c1003020903060a05010b07020f0418120207090203241807030b18070905011d0301060311040c0e10120902 72
    0xc0c0d0025840720b060400300800115840140250b030b040502ea500301040d0070105059101c1d0b01194001421141018480d01920801d107540f14440c0c400101e00d000904100e00c1102c00041200d11385175450b1350f00324400f402c4200c100d07440380843c021420412031a0110307000003002503102d106682480d080704001c985100f02e01c03000300010a4000c50944040d0400300310450348850710301d8040c8203551410210102c0c5200d00b400c040c3c041e1f0700c400c17160741543d203ca13000300e0904029041824003100c40f60a003043c04446001900780140100c060000320381d0310b18000d81e070140d0150112030100c14518441464031907900038055810000260311140e486411044142c0b00e50076a4401140fa1601401000b01d41002d07180310124a100314820701040b6a40300d032440b4243c030400c1c20142c0c1a2580c00c1c20102c1d52484003503070117a1541c2030160110410600c800c081d961010300303540a216a08000c0e1041e250142640f24860b004410456046001803040f0a1708003828818800021212840e40100e400074820 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 310034586 1250 310033336 310033363
    0x915090a080304150b0108010f17160803071406040302060a1e09050705030c03010212070c0c0f0306020a030518120a0c0b09071d0c030c0d0b040207060516030b130f0608 74
    0xc1048204c05032a014002c20004240390081c0c1c80d6041203106814001c01c9d004180b81000b4440350260080010041d50440062135200c104c01e440d56214000e99039840400708907607004010200c200d00d4030b000201c4501031b55243d0044e2159580301601040100250165001d440a80d50407641c0d9004540c81010105c502a0010f42455810035082c94a4124000840c80c02a80304100094124108490160f00b04030783c0c0c84d150740201d055003014920090700e50400800d8080c2640b00108005103036009186203020303070310240900c3c0e403829201050b0082e140a02055500106c00d41d501d609a25001404110040c2c104102d18a045803150002844c0480300600944d0101c64103101810507030950b0345610301da00001c0c50840c0750421825840c1d002c042d1040c8078144021450744980111500642100078010b0002c5440d95003a046c2240600007d458040d20030190340890710409109010303012107041c0103400020707005410303a0888010400041803104c0a41c1e03a2030045103444003408405a02c040 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 310035836 1250 310034586 310034603
    0xb0604051b16060b010e03060f0702010b1c0b180a02010c02150a090311030d0215070302040e04260306030304170f01090f2d060c0c020303040603230915090a080304 72
    0x100c1e140c0030b400c54080084040c1030104401d080c1c00260341c00540c05502141644d91b241e452b840e0102c05a0240c40c10307100c2c00303602030b05c1d8052002c001e2825440c0345000c0b40c00351840320500d4440c2c4e1032580204802c00051401d5401880030440554011030100306441d101604d00720400c0d00c100105005e80c8c010030701c5800002c40702e020030030034130181036061250740c4001c8018241c900100c01c0f010b903861084080ca032298031084000140280c2c000e0b41078034018601c0d8460a855032400e8907062425060341501e402d41410300e1a0b441c0d000c82480c1c000d4a01c86e44000d0000c4d85001e0810000e68101d019203034001109100340707135000710000c50030b0241c034000510652080d0200225441c2113440c448032580004440b40d02500310702090f002001400318255000500002d03511904c1c901200c5000c1c0702c1101a4240c407000800080e0310343c0c10383c05000d600040c041c019a212440e90550104000309a07580710007544000041144050000300755500000c00c0002c0300c6024270240c2c1d413079a40d074000321419101d190 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 310037086 1250 310035836 310035877
    0xf040e1006082d0a06060b0a02060703090201050a0c2604080d0c0309030807050f07180f02040b12090a1509140604020a0e07031104030c030c0f030b0604051b 69
    0x910340a02070142510201038118003101e611802800765849410190301220401c0006002400303002d241c00310350f04910288400c0e600e0f03101400c204c0d403080728584c00501c5500c00050a0790b2181c0304407000e65034141e4035146401e42c60380381160802c258410a8461041240c17003000350f48000021180104103400781152181d1600481d0350400581c901580107000d101400c0e0000660b00106402c103485c0d01141541e21101c06043c00352900c000c4680b102201e10842c07130081081c2807810411864956151024000c01c0f01d40304424042c0c1c041c0d485a01542c000500184600c64064051254040366150071070b03070b40039002d440301e05543d100307084141c142c0f40e6510300d50380c10f004030680c41c150b000c41404001c0c8a6401d040c0d02080540307101c2c0c0f054038220941d001c0032680c0340b48641c00042600f41c4001c00d890300c2c0e076101d04082084003001c0c4070844d18582c9004000801d03101c0c0d01d482204803500412125040d68400d011302c0050940203225008400a0b1843c0c1e80240c082070004e81a00c00001c01192a080c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 310038336 1250 310037086 310037113
    0x90315240509010515030406020d0b040c0801050901050a032616080409060f061d0f03011a04050109060f06030b03010213030809040f0e03220f060c031202070309050f0f040e 76
    0x8070410b0708020f000b4502c62442c81700d080380d41001c4a4100381d00000050351144680d4036a001042120180340c3d005043c14556803183ea489400103060711001c95071100d141e44c1e0303103040064501c2c1a01c40140000c9444a00441220100329915140b803050f11019240c040400b84840140d581d10000719180c3c500800d040c400250300b80b003090060900c90285500d0203081c440050509104901d0302400030070041b900d40b4864132807507107811020801500070320007020100711160b4541c1c852001c16005510b407100000300e20503680a031008540780b90719203080316810404100c001c0d1000f225140e0305903400301b2841003a5024020a0030065000702c6080380c503040c485c410082903d0101c020300103c035040c01181032400c0301c00f00440364110284460580400d541d54100c0204558075409030b22540e1000c4400101c0e00e8012504801f1548a59202c0c03840040c0e4800d424200c1c00b80013130140004e548a0b4040c0203904013556402000c103002050001c0bc0c1101000140c01d544040c50401079681095440a284 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 310039586 1250 310038336 310038349
    0xc010e01020708091e120717340b03011401120c0207050f0a030213050405160612050702011d07060f0302030c030408070309170a020f09070903152405 66
    0x209000100035441e208441c0c503420410702420500c24410302101111a044c0103104200d503511800252805003071841d1091810f4440100d4801c4500908400044661299000c01c4100908540c5443d0580700c003840e4002e0907034050000e40ea132290110714000407075401c820402840c001c20107241061519030205000404c007020982401f140241072460712080c0503000305041d004e8641c16113590010321420f900203002c0203000e500281d040105aa98803124040c550081440359000701c04640c071203034103d01c081c0c0c2c4644842c444e080c009549000390001c40c0803560040d5810468520022400800b2011a802d0a1300c406126541650142008005450300a050881c0304642c5080031804d5103844400840d2a100050008201c60340008151041600880c80c407405047c4005000151598040200b5a80c082e00c0d041a4400d03021030003c039a003854141c5145105801d40d5494ac02a10b01e15918100301800f0313024205030361034035080d1030b000307441200d95032102c40708000300c10341480340c6000c090240307 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 310040836 1250 310039586 310039601
    0x40b06180403090501030515090f0103020f100e01030b060c1c11070e18010e0d030204050a09110d15120501050f0f040c0612150e0712180f0c09020f0c01 67
    0xc05115140821000c00c1e048000714003107941c00e081c081456136072456105821040d00715501d03400000c3c10305002c030b0545640341d214141c078801e0340e80c81c3c07820948204001c580c000d800d041c41c0c00540c0b040d803174a00951107900907101c1300d02e02802d002e041821a070404d6003050f1040c20048001c000394480003410991010809802080d0704016004807424101000c011a0000b4843c81c180d0320700306000c6a0b426000d600c0303038040191b410156468083d90305002800b0350321500c9123a200b02d9880300089800ba4007445007420201c0000021480d00200c2a004009402100700c82506810300e10b00002d20301441055848600d44110b000040e9450400390100c4507410140850440030705000800000030640081e074000e6801600b00070120410b004074420203032280b14034088448088000009074190358a100c00d000b00303425200c0070340d040741e400d0001d030813244d8502039182c240760840c810101140002101d211014060000f900c202d5031503903d01c805070381c881c0c5508a9039010000b4041c1c039513407084c0b00b60354 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 310042086 1250 310040836 310040869
    0x60b0d200a050a03080903070e160f0e010f0c02030a1217010f05030a03140d020a0c05190b06130e01020307020717032d0c0109050601090f110f030c0c06040b06 70
    0x15206402c1501041121000340001041600001800362150341d080116100070325010280e107485140104020759103624411040001c00c07a030003400c5c04a24001e0140f1030341248181e560800480f1000e008441c5c00d101130300b090b80c160189500c81004a00c0701e51803880e03441815200c00003117002c3c204080b054040305034440407404000d41001d120f2030703070081482141c164240c234048e40b0419009001000a201385409040c1142c400100c1d103204c150000070b100c03481c81c0600140c070700103110221031161f601c0c00000003d01543c600c100056091910140e034101d803401001c0c000a502070200015822640300342c0b080d02c0580d000c2c0c84100480c40342e5284d10350f0314960340c601941c20165840d17458040380603810194150b0a104a0000100c14552015248001b0b0981c0084c0044502c9040c110340300d20084c0109001c1d03908145400e904000103010344a440908081000d00c0c1c00058220030310b09400c060302c0c41240702810000000e00c2801045103d0150f8001c0040384568200203041021040d00f144805 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 310043336 1250 310042086 310042099
    0xa1b0206060f0603090c100504090c022a0907120e01050103081305030a050307030e040902030307060603060e0f120702010c02090a060f050f060306010e13020f0c0106050105070b0112060b0d20 84
    0x4103a10049940e1031103201c2611f54005103c1d00300700030780c0d085c0100d400103a1040d10740070301250a2640003c90720103c10407110b09207407002901081c0e89a5400d59849103801000900104031000c0c404c03100d000c010605d1030000210b4206030420907003554403c0e40195a0b108011031031210700c80350701551800500c0c0403401410721301990365071181c690007481c0014080c4040b000000c0445e840d290000c02840fa80201a01d5840750540f030180010b216a002c1501d03131628007803503807104200000c5c00c1c020480001008207545400200d0070340182c3d1010b03008a0401209200d414010f0b2100014903005041400c0c0202c0c0090420920600512080d840035100700340b44031900c0902d407108005c0740d400160a18001c401070081001048040b9100240802c54510010b04075040921540142007000000002407000960b80d02c011681c900800c0006020104c6241c010001c0044c201403000e1064414800801c00c0d50480002404900c1610829502c074022001c10b44040348024040c0c644000046505 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 310044586 1250 310043336 310043341
    0xf0f03010f0905011518120302030d0506030609031c110703021015120209130512070b0f0408040e07020c040c050d0c03060b0d0b0112020a02010e070605040311090a1b0206060f0603 79
    0x1a608a1000480305c806002c854900d210049281d100e400c2c2c013401d01407200310000320642c50000c0d80ca0703120710580c000c058603210100d0342a203404109203004203100002035090000342c035a20240300050407400d480d4aa40c940c04c0c80c41c0002c1140c0a0301103580640c000c1c218007002000c03100281c41d0441c0c51500700c54a0201e051058007014061560800d40603200c84159580301c0b05107540d00540c0c81c9026146109480030101011940c00080040304d100b0b0408140360741f90303082e041582b0034050303400902e1030300d003071100380600d13264001403d030301207858030483d80390609040c0410112604100100001040013980c0c843d070145030301502c7c0105c032051804000785880c00e000d1149a02480c4480c46010ba1100c3c0740390f41682c82241c1c0c1e02c170f81d20a030040c11950ba04040d03202a001b4030010f094444a401003040000c1c1c60b50090007590201c0b03401038041003240e000d0904100c14110000c1049208668401c4031090841b0607043c0902c0b52011500200014180901006014003116003242d21400c0201304 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 310045836 1250 310044586 310044599
    0x30503040b25031e06171209061b070f08160e091b0406030c0902090a08060c070201031104090f0605030606030309180402120a06090b0a09020d020f060f0f03010f090501 74
    0xa000c40d800c94245000603044c034541c90580901030f022010f0304031040c1010b0000c0341c828403500c10320300344002c500215032107071012454001d0103000302008594444028030041c080d05d0b00c0d605942441813203644c2a505200d8640784029904c12550304400c84ca64001103c603012040b0284c840c030082c00710542c952606243c202e01081d80c1c2c80780040020f18038007591100746041e4445400c800080d50784005080787c000d0300c40070000001d40018010a104801140c00000c1441e00418144d0040d00c1002800f4504045500190003401d1600c100c840c48160030400006d405519100e40c411000150388045600c80c07400c005c051038407001405180c400e4004115009503651a049070112480070101104010358880c0001540c51701514138440440c010800c0e00410400a0380c8041070080c41071010a04a80700c0e0507100c41280c6005000070b400c861030f07a2030640585400300310b082604800810891819402081071940c0c0c0d04984181d03241e5480100c0148400721040c16110042c0c4501134003003000b03614190 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 310047086 1250 310045836 310045891
    0xa0308180604081c112a0a08010207050d140d0209011b050a0309241803120f020601060c021c05010f1503030e0328170a090e0901060608060f01090909030503040b 71
    0x6c0903a11403407100d18880c00189099a01d003409550041031807550641d9130a507103001c0c0d4131038003013120315016000c0c00c0c0030441e0050300d55040d000085400a030400c01a440007038029880704e040c00e414403000120315902240c500384c00447d03180c800c0b809011200f41915010304120300503001000400c03410030000301c6560510000002030f120310714202d42806521030102e10000290341010b041001000b1003104006d40221a1950301c100543c00c440e556a80c45004880c03288100c030000b5801500316034002081003401c08802c0e0311601075000003600c668030040d00300448243e00321070b02d80d965030301500b041407541001e03d82c0450b035010346c040e0030340402c015503038a07104055061709038000391051025000c0c4071458412164a0700c01c180100d5031546581d07405801e4903094412f041408680a0008007003801c10f0290b541100d405440f905550348481c3d040001c50440386446a0410014140010741c200c0d07180151182c0a000340c072419541d00301801d004404003001084e405000c03811080c0c40304180040c8 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 310048336 1250 310047086 310047103
    0x8060f060f010c030e0a090c270302040e0c120f0d031104171f06170a030f050f0f030109020304050c09012102010903051b0f010e0a0308180604081c11 66
    0x920b80f140058442d89402d440c15060350f150b10b90070044032600418195030541c0a00e000302c0c2d0540741da00c11509044803450940402070b41d410000b400c1e040080005007001d81102c080d01c07101c2015a451092103202050f41c0b0300c4080544070141d440120f03d05000101072110010004451400780440b100e502d5041e140361140384036111910826003281100c00701309014602c1007503202c0032620201b44035025850701400300ba0084542800241d1441005000e00160070868641c0c1601c2c0d01c1d911061819090f207290f00113002c1c0c4d41c81d104040200089104410700218060052a0b10068076810103003050391505400701c0040380107040a50040c48106c844103540c030381a0803000082c20200980d4401200c540d0880d40c0014994400c1c01018003058011403089449482e051703610110400d2030200450355541d0200c10700d03412440203002880820701d0743c001804c4034425681d281c0e0540c00c5d564040784540d80280e125060940082c4149026034070041c000c0704e14078000745014040c1d01d44c000701103900d40c44003 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 310049586 1250 310048336 310048339
    0x2011409121b03040e0f070f1e080a022208060109140a05091219120c0509040506040204030f0b041704150c020103060f06090617010e060d05011401060908060f060f 72
    0x124000b480e04030070810441e009010300e0400000b007810a22006008441c0955040000c20b140282c030f80300e02c5100300c03440483c00c00c4d8110815210203901d0b00595007204082c4c00070282d40e40170130181540c061240e019410548280c070f540ca11861500d502c46013081d0381030304494186410a00c0d25680c43c11061551034005100b407800213919141c10b0100c5252161083d080a0001401319402d1003d06101e03c850103240f074103440e1480d22a4011310700ba022560f28442da000821003e0111340c2c5141443d6214a901220141006240c01e49a032200246280c414500b200c2c884000700130401048a1f25039107000380070700017800a0606040010b1450609c80304041e0200304803140c2038150540e0720a811a40081c954000c5242e0000d03101e90000744002ca41d4050000450302001100c40351500500d1014101c685043d040c1d601d54561a0810400d00c0300f1750025a040c3d0340b41c0c403441000d03030301c2c5006040c02000076803207441d0301902d0041d01d1030428400070046e180d840404000c100b29a11044246080d5040 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 310050836 1250 310049586 310049617
    0xc0a0512090d02130b040f020307030c03050c0315130f020306010216060801030b040f0b0403050405120c2809060f1a1819080106090f050603060408040308280201140912 74
    0x8100c146130000b09580c104269006003000c42c0d04905056070742c000c1d03000e4045a902400700d11291903041d829200c1c01e07030350101280001c000284804240025520418900900514904800c40745410583c0c1c022004000d0305540042030000c1581c040104014024103074000340001481c0c01405401c1d04014030000c1c0550161100084c1013260011010010780d9000040d107400d8107180c180102103800a0190500030f00c07103881c3c07816100400103505040c1c0c110040000e802070707203581c080b8141360604c503841c1070014180c90000303e01075209001e0b40313000c0c0c1900c2070440b000c03511306062011b01b121000300400f4034200400100720101d09811502492841c00e9602e801205203c004107110350b007480c0c3c01a1850f502c0c0c90408590b003055500043d64940c1511401c0c0466100c400405881c4d4a0030b40740248590010481000080d50020103401c41e412858440c2036506201100781c00070781c9000c026000183d6440c03518180c030025110001782c000e0341c000700a01c1140100354150000e4170032101304010068 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 310052086 1250 310050836 310050859
    0x80601080108060126030a020f12070c1203020f2a100206070809070f0305070513050f0415020d0603050a02100203040506041806150c050607080403080711070b0c0a0512090d02 77
    0x1c5c4180312441030344408030101d9541300c840010094540054980d0803405000320700c04020a01c100c03405a55600390000b20b1030343c00a103481071003010500030081c100c9c19030050f45001080e0040c01c6c0034030502030311904200001f041280c0440702007a42d034440141e2140c2d54240b0220603a590000740381354000494104180280c546400306403070310965504c8010b40540c8008040100702010403d10200ca00641e641c614041c1303030300141400e40750111401440c0341d44035800074002c0b485c4555414181d00c50490f0051600340c8003103c08050b5000d94106031000e60003800c0d49021070810000c004412240c0788051403c03e400d10303000403e148104d22480b042c0c0401548000741c0e1a406a0102c001401e5a0001d940d42080b040303806445400003403070544981c0108000601840d00410b074075031046038195038220036551092400e07215040c03100020a01840303802004241c90718160000c00b0340300180c60061070a900c40e447d240740380c00a400e00c0e21031a0350081c003052416031280400d21045641c1100d0f6400500e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 310053336 1250 310052086 310052129
    0x3120f03191122030615080105100302221112010513060e070e0415091b050a0c061107020d0506060a09090b06040504081c02090406060813020f0f1f0806010801080601 73
    0x14580d0b04082e0950f807814030740340c02c40210078440c0d0b411265040001d1020b0780d910ae2000350008864440a508910741e1008418804a001c8402c90040702080c800580c000031404822082d13081955591132181ca600014402c904c8c0c00d5500c200c00303d40c85c0d001881554103014190703030410300240a080501850760600582551240c12150840038007114028159548480040251120300c89100c0c12010b000100c1da0798600c144101c0d4007a6001e602c1d210f9113400e42c6c1c1e0b103a00080083d1031050b01a00420701000340142d0701c4490034455180070320018035160070300c01c081294030070582e8004060305140401a000007604441c030030b0b90107401120005007076a218200000507124000d5036041810b000000c1e0381700022650b018100120054604104198031a00141e41a07001a038420440d2058958072500529051412010419010b8100d001d003405010102c0c1c460700400d09001d0b0454007000740c0a4110707500a2030560700650074607040c10705515000c2d0850f110041030081c54040d050f15090050071 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 310054586 1250 310053336 310053397
    0x60e040e1519020c01091703010b0415030204090509100608010c090b070c1508090d03021206100504050316030210020105072a0c0608040309050405060f0d0203120f031911 75
    0x101c6400c2d8150b54507071404c00214000c001c01c4804841c0444004600401081d09109480c1a1500c42101d1440c00b400c1c034840c0185218403c4002003019020040418205024000c1030300510224006010340342c071180b620002d42d5455006210741d81e1428400b401c1140d8440500003caa0890760f00d20340e114510709003d00804056040300b9403e0038404503008034541c1c0800a648030b181400281e9048550a0074214181d1082c0258402030002d50404900149003400060f40b8241003410010304e019990404a810210050229a080d82d5410410001e508111124103001c10b07561008000a141880000c1c040c0481100c5125011020441c01e061494007460040d4066402550204c000ca580d004014071521040310100c0c0001c040080000b080c0c106030040b02c1c09144014507a01c900c64040c03050142001041c04140e905102c0d52030b520401030300e40b50007002071b2450910a01c0c0d40e03140c03001d410066111a64048480c86140102e520328121030402a101090b8440f48003486002c102c00354144bc = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 310055836 1250 310054586 310054621
    0x3020306041116050105060a060804030e010c14010c0905030304030f0305070804030204060b030a14090d030e070504090c170312060409050109021306080708070b040902030910060f060e040e15 84
    0x1c8100b80000c41508403c01d0415005a0b188158000e00c51903944901f4012030000c684503000119415502080000340203c240403a0094107260501c540320090b141d00706145003491542d0a203955500c445003c1ca82e0001c840c00140106400441c82c16240d50703548500c00062507405000c128011560608002041c01114000c41d0024400c9c8010740e21034003124907541c000e03079841c4d0803503160840040260718005c804601c180030200160811642e05181600600f140c0300a000d403030b00400c180810507070740c0d030300c0b0301c520b418024054078002c981000c82e110461440320042210079802486001790344020b554000390b1050041e5004180900c0e1403034041d02500031210000c1d8407041c0d500c0341c3c880c6014154041000c8407500d000310386a8550302c40780070341c4810003070042103588401000107001010154000395000001c2c8011100090300c0642e215085500e0b680043ea1100c00c802410808207074010035140701464100e1b0b0400404c5440441d680d591951445103d00b4001c40100040404561218208 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 310057086 1250 310055836 310055861
    0x10515032a06030c0705070e0a0501120c0504020903070905010803070b0702070b07150902030307060e07060504030503030c03060307050a03080d0b060a02100c02011104031109010902120f04050a0c1d1b07030302030604 95
    0x1c250351340362002925082d0f4225004190327071f40b81200001e060070007800f8800d8281d40010260618a080409100c040d51045103401e070148540d410000783d0402030b210380307030082440c10301441e15103600789440603240c0000b511840031580314003414050704251404a44410754450908059400c400e11034401038256040003a42c5404049008020b00240f5000a12941c040d0360680c1d80050322101c087d9514001d501010b81a940188000f8500d50081401581c100713600500311080c09507a40e000814141141d0000c44018030b0101b440c0c28251042d00540c03c1c01c80301160072038200080208025560203401b0390503a01183c41e5415201340600030b5114400351140745140c00d684031b8503800c1c50030000140c035080900031569040000303600410f80c401e65002400b000d07030820468441c030220100c40880900107486501903240243c0005801e000c07098000c0001035040d8100c81d0022400a900d60401000c1002840808600d101c19001c41411a50005c1c0c2c1400d005840380c03245404a401000e881d43c405 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 310058336 1250 310057086 310057093
    0xa15140301140a17070302210d12050106030b1c0344060a030b180d0818070627080f0a050706050f0d09030c0203010515032a06030c0705 60
    0x1040615020502d81c801e844283c409841155588240030b405507110880103020780c2142c9414070051600c0310406403031515021280c3d080c1e003c4250701c50308240094642e034000c0740c0b4419403013841c80c8160141c0d600601550034104880d0480c040440c00720030300c0481c3c2e41d94070110702c0e10150070140035140c00c1d000c80701200740d10400300080001070523009940c900086d0829601480c8981d40540310302c034452040d14080c144c208014590764444010303000103050748a5100340e0031205684610100100c0c2c071004502e9882d40301c01d003421718102070245095150034190b6042100c09001c100d400c00e1030000b0fa100c00c4038015042e148210560000c010b02900300b100c05003d14000a01c141c14001440003405001c1d00680d1a040c1d6943c00540c2c4a02c920723202c945404205002c4001580c0307090380142e8005000741091400c05519500182c21120101c5402001089030042640740d4282000034200c5a10314003404201018403030902008081c9a010040c85581d0000c0010f2800c0310a600791090b450f4420201c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 310059586 1250 310058336 310058339
    0x204090b01060908070f0f050d021c08030a0b0d030f0e0103090803090d020c0306190504061e05100501111b0d0c0f061d4621020a15140301 61
    0x4005855501c5204c100344100c040215141c001d01210901b04c4200e107290381411440e0106000401c0b45500c4240c0c0c0c01650840130f009104030080c07e84d1109842694501c5da2441c12012201c02c07151a07440442c055404200c0020000741c012050110014580c100754400d4008040124040c111a0000130051180401400310f04140011a01d80b10112a002e82d070b12013000c403090503a00c1c4422035058440111001550030242d07020381c021500b2501072500450b03401104c01c140000c0101c048260350740641e0b074404201450f40b8103050360300039000929214070f9010403c000c07030760b0714480c41d90f00707074032810400130440c88543c0d44a11003443e040c0e0217036030b00c00265510300991044201c10300c54a0045060008071502c9c1801901481c02c41d400018460318403403018501c2c1c105041c1001300c40b04101c0003c1e081502c00350694109030121f484804207483c1040d810a5084007800201240403c2c100042c41070440050f55010101ca0555884282040d0f0100d419241251090300580d5400441c3ca4000300 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 310060836 1250 310059586 310059599
    0x30e030910020a0b07080c03160e040603050a1109060604051e03120a030605010806090f0a0f1107021306050d140c0a060e010e030601150302210726070215040204090b01 74
    0x1c0c5044036074001e004c80e080c01e6032406000d07190924101c0e200c2c20f16042c02c2000a1000745000901d44620130f55103404088020b810011804455154005a445612a00c1c82d01c0400003080b500d034480c0403068070041e0031410440041b84981c02680201e500c180c0481ca007140300a03465500c0380701c6003140107084030720340940245181003503030003031a50304000313800d091002c00d080d4058003006014040c090410720166850345180748002c90040c10000c0020748480c034a000c1651a401011101103100603030f240d860341b2503c1002041031000082c0c89509007041001c00c0701ea6618441c81080641142c2c0040c40e0315000c0040a0414116409659200d05a443c0218ad159407012882c40c8492082e20b4006050070f4500400d136a4034000d01c0f4080c07056200d442d520020b580720b40c020740f4540d000c1001e5480b10211314000c00801d81c00841e024000511810780344c3c0b2010541c108c080c032042c4100c150161440c1040ba100075260a8902406580f0201e81808103045440360341c0131800464011088111558441c1c9 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 310062086 1250 310060836 310060843
    0xe0d170d05100b0406080402040209031504061a010e0a09020a0c1502071109040203062e0b0a090b1620030607020d020f0d08010e040f0b13020a06091401030e03091002 73
    0x2c402c0ca0414410380804121094a24115000e4900d582c0f20f00b00d142c1d68503802c003c080d40c4016001600f60141c2e9600c0c8bc103441e1400030050050307110700c0d408190200d400806400c4a0401e81215040000e05260307007001e901c1d00e00d500c100b40c514804000d40d40300000700c42941e180c1070301031000303140305000c00140c513102c00e00b580601440361191091141c454107060402004000aa4019505030840c0300845d8044078011115420140c2d0021108000b102443d41e20150050b540c1c032550320300100045d181c01d20f0760b0081000c3c001c1d00200c03180038184640400c41c540d172911007100007440404903400a9042c507482d58031095141c2c500504880c550301d00408003d40303500f010000c21000d84150201c441013100085523400500030f155480d4003481c0c0ca40032806540d1000070b001601d0b0300e403440002c80c01080d01c03403410324495030502000700094651881402140c50080d031021040012015003844a61802c50080070b5916003440c0204902c503a180405041d48200355000d54841222092454100e4021 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 310063336 1250 310062086 310062091
    0x21140604051c140d0e010612060501030b090304120308060a090e032106030a030309060e01060f081516030e0718240b030f2a030105120d0e0d170d05 65
    0x2c6100d10042d500c0030b106561410503600e1000c40c0c0b801c203018aa24409240d44005c07101c0d10365900221310555a1826089101e00a4406440c12611381005205001b61201c3c150740000901006500e0075207020300f00c80c0c08402c0c03014000c4c2001b2160010a5190b42c03120070810181411060800c9070105030040c072a0742e030384403a0202440320600840d0300300d1840701652882c41210090054828560070356021030041034500011201c140d9100b000545d5803000b48900301c041c042d4165103103403450074640007a180950098002800700030744801c10403030f0440044602c100852608001c12640b0300701c4005405c01c2c1c1c641d088421207031004944106084c84903041222043c1000401d44c0303081940032100c0c80c41e04480c2c0211091f03c0d00810106100034407009940ba401021580c4010520484050074001d803848035100c0881c21501200500440c030f4a0300300e410120811130010301040d5608840a010740c4039001c1d07081d01c42c91101c0c11176014081800010b011074032280d03070b0550707540d400f03400d0480061105 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 310064586 1250 310063336 310063363
    0x30b070503041112030d0e0106030605040507030b010b190c110409080301140105091c1a070215070201090507061128050c0a0b0d1e020307120c0201062114060405 71
    0x8440c40e2003804d003000201a84075900c090099441d0010611141d4050701112000c80c40d2036503101c0001021410511610303000da8401c601800035140f55041500080390f068110100f90301c800c00c1056115003402e03510340c40b1500ea83c105942440c40a042c2143c0000d88841900c0c1c01a04020f89101000182e00045069400e401820b5210f6444c0c1001102c480c0107140d00b8a400c040c44c0244400c2c8042810220340101c1d204804180605500c8680703007240c03120646140e00541d1100c1844d420780481082c0065001c850ba01c02000714400703030340701c0595070210307032045400f03020f210240d0300c0c0c150701c05101d0000501c0d07880c5042c0782c442410710041328600d099014103032040e0041d000791440724642107035090304407a04400c2482c02c112007980c44070010100700c0f4a03121800c0290030707009040c0507180099803180c0751545074081d200c032a00c901403084d84c0505841d5021a450310005019495200c290034001011034103000e55007100600c3c1020608070140315091203485007008000401100084500c03840c01c1 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 310065836 1250 310064586 310064603
    0x130f06091415011e0b071b0b0c0d030c02010f06060c140111040e060406050409110a0905010510120204080f0303071211031522090506010e040206160c030b07050304 72
    0x403241074251611961211074084601400c010040c40c0b031040c510380b0b0004030401c08071203001e03580d0484011641c4070400403107612142d828021500b1245d0801000208400321055180c01203005046840e880c5215603c41450359441485296038804d511022429003619010000b441d00c404029111241110017180d0710280384108086040b4107004103207400324201429802c01d030500d20003c0d2803034001030070603030465900d010004050f51103000e4001c145000d482451420200e600c02d02c0858000790700b101c0e0706282010010041c640742c815926034014030390702e48004038561188803c0043d01c60380c3d100d80640c1c801c00758a141601d80c04001540920410303118020b100c50300081200544407228401c440d118000d0000035610303098004100660580103151002c0701803010509003c1004609801d500faa940e401c0c0e10040000410195000d0050690b011040e031500f47d00041c420b100e548088030484000d40c9034a410017018106410285610010030b10840ca000f080050240d00201c034150742860 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 310067086 1250 310065836 310065863
    0xc100e0f0f0d09060f050705060a0e06060d0b01050f01030204090207081b07050d020904050f010e010b01030c05040f090207020310060b1c1503080f090d05010b0f0109140405130f0609 80
    0x450000d49070320039100940300c50b40030131320b45241541e01001080c0e49000384a0b0800003200043d01c103103c4140703e00903501c4001940d60000b100c40e0301c0d0880007000303140a040c080310240041409114454110b801c200ca80c81c01c00062000101c020740a958000e80301940042801c5040012402c040c241c005a140141e0803422002c40c1e240b555410390b80b00d00f07034110f0944402c42003d400e040c0101688140110100c0c0c5007070080800903402c480401c851315000d40d44d140201101d969150042c0b03031444040c2e240050030f280c1082d0103500712440500c07400403095170009215045403000c3c445a0025083c5030000c02480340ea6481d503441300da1182c03040548012401e00d071251440c10390b01c51120080100e841211445045035a8a40c05a10004451a041d08184194440d0b90785a00116810340d10540020403008181814462121880d04169060208804c418019032810486640c0040d104880c049407a444d807102441650124400c041d16071340e03000900b4028480075401c5004803502c524043d52106 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 310068336 1250 310067086 310067113
    0x60c030c060c03101208070b0702010c090609030b011205010b09040f0c050a0b0702010e0609030f031b0c1302090a0506120f0105120d2003030f100801020f0409020c100e0f 75
    0x900c0300b02c400c030015100740c010030701c00c03031715403c0290400c50f00c5007142c5843e000c015103503440c180070202c601d100140c0d104c6003071124007a4081c1c40d100080c11075041c2f129005003076603561881c41030140504224080181911414402c0941009205070b4020713181d000c060415040160070401e19003005da8174003107299000140c6050a9811108440444c8607c600f003400c25401150725012044550b684204184202e1350320350b03010b1041385030f0943e00400440d43c0d0103c40100b921700101c0c41c52029007a4000d4490f01e010ba498a01c50042c400c2c921601c016500c03c100d0001940c503500580041ea0070100106038030011080b034120f000c0c0070324541440c21181f80c0c1c0e6030b0100020141002500e042d0703904010a481c065901951401c00b2840b48601c1756045200d08000c4646181c000b220251080451034003888900600295258041c05004009624203031030f000404c411407080d8410150126030024850403d200c083c401c640501e0007007001400b484559048140d600c1001402402c0745005900c400d6010 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 310069586 1250 310068336 310068361
    0x20a120522060b210f06090c0906010804170d05061f0f03021b1518010905120304051f0e1005010e010311010c0501091209060c05120306030c060c030c06 67
    0x10301c080c0c00306140c2800303540307400191010300324282d00035010314842414890140e03182c405040440f0300900700d1002d030303445843c9420f20241c0106841d0300080c80b515010384901452652120007801c00801c42e40b104d1031312005041c00201040c0b07400c940071555100d442425049140202411075804000d00003003091412410300090803080032901644d03942d00954003070380240040381d0074401e44440d011022022107003014007103c403038034420300180200140b4551000164442603100750081002c2e44a5079102c0c1d81e2843c0703440c51419800e20100000e401c00c0020008148901d1801e81c0701d24000c801d40c0000006081c40c004e8851041c0901d52200307405130154826a4102c800c1840c00d0210b50b46507490b0380504028000b5520304004220340c54001080d001d01541c04000d120b4940300c0b0602c0780000004281c00041e400a0040203400000200460f400061581d841816112002d42e01d0720354100007464604510780c2507412140204006c45418004030142190f003020206941e40f55480203502c0300d1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 310070836 1250 310069586 310069621
    0x14030309060f070306081c031103132d12081f2d0b030906070309030e0927010509070b04180b0301020d0603061e02032a0d020a1205 58
    0x909610000c0041c1d114a000d0194a42100290500095554560001b2801e040018292403104032620480e455a140e01d481040300b0391a141003d5411030510100c07003840d80c40070501c0584400110850400c1e4440c05404c0d0503454440c924a10310600039624004140d45002d040c02c0001c240b4060018102c101c0b00706a1040551108500c607441c0c1d8101a4103111071401041061044010440700d05104d0000c0385d11400030f4003072411159104d01e070a492140c5800c07401007543d401c050074010349031700003600140c5a680c15076045621a03416610014406041010160b884a0031524030b002c581c080c0106501a5000d060b54000365550161034218080b80c1d4802e0388034442d8012205560755200207d6540448020718006001600d050310004000055801035003042d203005070f56000780c080c6030a180202180b02d001904003507065140c16500502d21410707159808541c1c0641a180e084c5030180942119803980a50340c0854440c403150000400c40800c1800e80780c4103a2810000c10a4846044901d40 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 310071942 1106 310070836 310070851
    0x1e0a110106060512010506030415051f0e06030d050703020102040b040b04050103140417160204092d080d020a020f07082103060901030f080c0303090a140303 69
    0x2421514a03070b01090a1010800c00354060081c004240380c1180c00c100d803d2912a6114241440d1050100a404030118940001c00c640c02001800205000108400d00d50b01c082d01c0f07104100c0180c8054034120b5156100c007020100d407a102e4001030421600c02e200240c1486d40c1e40b02d07035249541241e04000c24202c0045024859075a246c4110a00850b0045131310080c2c2c200340c0c03140182c5003004c105031662140b0000c1e032410b000541280008003254003400c1002002d080b410f00f007400000c00501442409050407802c1d0100d00c240045064154010f0180d914191200c2e0400307009600824488095004c0c418540180d24400e10420300140340d044040c060395410643ca8001d02200e0250314449074009105028142c2c403941250360550f948605802e07544191808d01c0c400900984034054032900c400030070040c4103000841d020190610425120705001c4400c0d42164903400308950f40e9 = true := by decide +kernel

theorem cover : BRFrame.Cov 309892086 310071942 := by
  have h0 := BRFrame.cov_init 309892086
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309892086 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 309892086 ≤ n) (h2 : n < 310071942) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
