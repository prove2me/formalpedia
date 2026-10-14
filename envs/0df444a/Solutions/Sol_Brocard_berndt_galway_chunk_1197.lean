-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1197
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:42:54.465873+00:00
-- url     : https://prove2.me/submissions/cc5235dc-2552-4fc4-b131-0e349a6da1dd

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 215107913 ≤ n < 215287769 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 215109163 1250 215107913 215107931
    0x2010e130f0903030b01030b010e010f02030c06091b150a05091804210219120306080d12060501032307020f0a0b01030606050a06090e060a050d080a17010f09090204 72
    0xd01c1006100d400003030000a2045503428028111002004000d042c0761500e200546c41d6a041600c0000c03d03c82440c107006540b507102e8080781540a00c407043d114074072035001881980030000c10390744840d41440e2201c070a900701e40000c000e4402d003060b034084000303a010028940d20341c1c1700340c0040c0000d820251044048494194a40041d80012281034032410120107182c00c15208045600f06c144201e44000c012495440070040060528081d001300744070710852001d0405802604800000c00041041d1111800020744c003502112048105008062070130001090a41c0240304952001c80d0b00011016408a0f00d40080c2c00c0c42c9003e00800c080d1320810351003615280c410400046400d00c92141c1d081c1c40d501d1440c0040c02d440c201e40180e889000704c1d1405001c2c0a60000d551011204850122a00e64a0302c20101e0f80c44401a0402c54214845080c0041404100d60043c980c0c0603440c4d9a405952081c02640a0800d0080c007136213000700b84000c0b00b001090115000310440c0390000b0300010f50388038 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 215110413 1250 215109163 215109199
    0x11406070c031a01090209010504140d050609070905100605041e05030d0c050f0a1e0c03080a08070e030d121e02130f0b1206010804030c0606030b19020c0a02010e 71
    0x20082e4030465110700b8809000301d10201041200340184030744d4105504009000001808038003d5028845181e005151114119aa025000c650507034200080e124182401c41c0a1500c1d43e0090103450141400c004c0800c4610800d2041d0b08121146a55540d08103400c00c061405c0001131481c00003001d4007190380c04030b200d075010300c07040302608015241c0d10fa174034119280060501c2d82211110080341c11a421080200b41c00030718241d448012001403c90340714081c42d00c42c02c2d40780036030170103001f680010941c0102a900900c03502d008010544500040f415103100705584d0f180420341d40c1e4000740d60f00405a41d02d180c0c5070000604890011b9403503440a180b00d080c00100d810000141001d0b88000d8010414400070b054407601801000340e07914600107064a4030401d20b41d015041d03a0400050030002000e07d48204030140c07031182e100c1c505001c0d29a4074189204184000c1c3d901003d800260344055180300e801d0700c02c841061404c1809800040282d400560309001420344c0d0326001078542400c440980 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 215111663 1250 215110413 215110433
    0x1051807201e010507110c101112070f03030b032e0605041505090c04060512060d05060a0504020312070c1a160311010501090204030f1410061403060603011401140607 73
    0x2a40b0200002000e2070170000c0240907406030081c485840c4c014580110307407521464140c010303022035030900b0800c4d060184600340c40d003108000010140c80380400d4010800c05a11011400c0c140299800d10031107124400700758070f070885203c00c84020b040d1680030382da40d0141c0e81c5001d080301a42d808000b469560710004035003a92800414202407002807001400340e8503001680c0398000101079a024281030800c0000b81c100d1107078010b840720b606845000590503603140e17904220300940c8502514414108540c17018003800701594128464012040c001da80200644150b9034008d800100114010345000d03565020481040b145911141d010444031056402c1c071a071001186110fa503c1500551885e203445003152010b802103401c2034010082080482c950f41281e10016401c9110080600744400c00c7d00d140c44a900c0d11a14520700b0810005280d01100402607000d0034207a0076607a550342c0b00c0c07080600702c0c5c01c41032801d80c0d51803068006100c50059030704001c4510b00003400e49480d2200035201c0348090703 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 215112913 1250 215111663 215111713
    0x3040512100608030f0307111c0c23100b030717160501080c0409020307090e010f08010b0303031314070b0d0501090b0d0308060114040506030403080105180720 70
    0x980c0681c294070901103076482003400404810002e90700f4002070f100c0c010080d20001c1c01c1030b8104806501c8882030324205205400d9001410282c0c400b03050346d200000340c00b030003001405455002141d007070703d00c0309070345000c007220341503546009000d2229003d01882c0080c00ca101800b905485000004204052448519840188441c0042c10720603100c0c54490300c4c001041d00028104100042070040f4500818241e4060f03881c40040581c03280d856000403522042c00d07034007481e000001c07130000050125100000009070f80484000380700074118141419030f00e00c41a5a20100700b0542107205003c01c94a016207902d201640050f6011142d4584101c0c201b81c1042e031200098690f074a004128040341440785100e00c4006075090340c02e40c5060388018001c844020040307810b00c514841d03101c041100c02e100b120b000d0000103041685908041c10010f0505200b4000c40340140d100803040013188039450b2490b0b20a0b0041d9503165607408003808804040002140d1360401c83c03103611500441d500760110340e0120 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 215114163 1250 215112913 215112949
    0xb031e0a060e16060306030b010b07030516060e100213030210020304170c0901150f08070c1a0915040506130f1a090c010c170a0903120c110603010602030307030509030405 75
    0x9543d8034141042a006940000c0600d0302d0000200002217407015140c1c11070b0030200d48251601c0450400340d03a20710130201500041d02c0900c40e170400304903940d80045502040a411294021030118010f012845442c0d4907413518a1440c03c01c100614110114240c608150f1042d2810543c0d9199200e0427805005400c03c180c0c0c001f44200d0115050583c0d0050061030300c1003203454080d6050201409504804a0304d40402c2031000003d172900380070f04880c003400c580c024862040040e0b20343c90305d8000c820607903a1010f20300404184050f0f9141c1d6500c4540243d03040009481a41c80c0c49c00210501c4a90340740032640e10300c2d0b101c8040085400f0303412a03a48007502e0300800c9940e140c02d40166090081e2002400d05002e04003180c00301040c42c11000a280504990000d66074046440c0c00756148021540b0040c0721240591100481c6036018154042640c40381008200580c040401c00030640024040c00700103030702c144006001644240c00140d04084140e060ba80741c03a0322180440c130300d241d20000840b4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 215115413 1250 215114163 215114173
    0x1b0306050a0c050702010e040f06080d020331090905150112024209040c1e0906081f08010f0b030f0303150603041a0a0b01030f0b031e0a060e 62
    0x84070a224010307028001d00c00d1800c54540302d0b40703500107841c0302c0c0709044090049545110f482046074090313201c18094590308049891884807020000d5603a032240d0780504940c0f04c40181c00c4080701d507000e0758911200070311508007442e9041c510443c009185050080d1824401c2d11554501c140306034a145029240c1200c0300252103400c0d0060004243c42c4502408102c44044511a000900e941c50b80108105801020803104039049120996029580341c056000b450300303400e5280d0a4026034143c2007400e007440105e244150760316043d5182031592050b0b0010030700800024a45210001140398885540c080750000c0b903888140c517500312502c40140d0044151384000481e80340c6401c200d20f83d40141703500b008529510380016491000b80403201014000c40011003c01c0410482071245080b00440c558100c12501c0c28801e00e801504030080d000c3d001c41c0c134089248101d42c0e043d0080c2040024054020300742c03100c6100d2180101a5407240b010407501035040300a001412501030b40c1400424000142 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 215116663 1250 215115413 215115421
    0x708090f1005090d02121002041d07020a06020912161d0606040905190c03050f0702062509120c0e0c0307020709051302030613050f0c0312071b030605 66
    0xc03821030458140e00c0340c006618000c403560342c424102d43c0c410100390740103c280c2980d032000c5000c3d03d84200214045000c1c4c40000d02c0240d5650b40500221085241386281d00c0314000950503001e80e055800f080160030a40490f404510b054000b00503010340a06140141b070410b42100c2c0c1013071060107042c811190448020090503c040f2000500c014010800c05c0302c07414050b0004143d07200b903100705c0700901d803554002407014681902d003543c6000800018400960f4010b4010010441195503400112540d80800d02041c40002d001c0d00c51190030b1000303406803007072084e490f841d413019810344010092207600218080d01102003801c81c40744206040944a428a0791144e4255801841180f85040c180304014800b40e00140141c00c50381c10880c0090b4a07200c0c1c240080000030303112406501407154400b441103040b00440d039405014000d609485206030505c0420b40c075500d0032407125038540d0245444120781c034030300001009024442d00b51194150456401c400030303402d15500603122a55100200 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 215117913 1250 215116663 215116669
    0x5070306050402040f03020f0301021b071811070321020d02090a0603090507030f030e04050c12070504050d030e1906020a03030f09150f0906060803070c050a03080301060f0203090402070809 83
    0x44040c00080702d00703500349410b01100c1d061000c80d501c00030b480350203103072404901c03910203504486a90f4840ea040d203100d02400e1100c03aa440455108040721078000550325202001a0f100380030b40302650101c0726290140607141100c3c80e2118400c01420010308802c000074825080c4000c00070151711910158852005104102850380580d020f1420705082030352501c00100f02007081c1060300da0000800100009500b401c03950524242f0503160041d25200503c00317003984030741c00343c0b10f2199541b50b00c603410760703554504480c140110b1040c0390300002265407020002e401404075910681014240701203005444070a504d040f4500d501030005600840c54410502d030349401412099030354505e050100e8040d40c0d950780c2d040b08041c4040302d880c0c0d40d266030200303604800d5085000081d1300b0030f100340520303034454031056160390114008840c003401c0e4440024050400501e140200c075007100301c031811686060415101e1086001884d811400200443c1d506903442d840946086400b40d9420307501d8540b00014 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 215119163 1250 215117913 215117921
    0x311061503330c0c070f08010b040b03120703121b08010b03100b0901111506010905030109020f06032203020d17090a11010c24140c0d0528050703 64
    0x49070307541c0c1c40c00c2c0052030103100c079107220241582d688039600c2001d40d44100c01c045a500401e80080342070f000c0d00d0700003d000e0006482c0301e010303242000c000f00803154000041000f202c91460720150103410050302504d4220820010700031440c005e061205448003000c080a0132101018451000f00003020740c17a42581c0d80c090215130142c402c04c3e900600e1420704038071404c0c41042e10f101e90303014914006803188042e4828101c1420043c005021550609054404d420105074221403013130020320300000c00101854140078103c0c00c69006411100c0c404140b030280700b0345a0004160103900681c0709001c40c500b05056003132407c0280603a001e4074100503041310003403c401409800c0c00b40d05020906010074001c011600001c0a41c0c40341c2504503910050340140e5454110400240000c13022450301900d030810f101d43c5040c1e104039404100081042207442c03080b4500705881e80c020b1410184801c05200c1740320b50002e60840ba1003e02a41c140c4d02d0780b0401407503901603100a5905585031418400441e0309405 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 215120413 1250 215119163 215119183
    0x6120403030b0105031005040c1101020c0d120605010509040c0e0307030b0115090303020c0d0213020412060e030301030503030f22060207021806031002071a010308040e090303061302070311061503 86
    0x44c0107460350610180040490406009640c400d035565000000201d0240d480144003d0083c0d0096458042088007182c90b030440c403801a000c0b075008120707254180c6452140740159038050b1602420f00b800c410500c030007402648400000c0c080e40c1c200c006003540d004c000d080000d40c0714843e8491998140fa1156407480720720142007041c03140c462030a100081d0045080038818030b050390104107481c51400001c001d00900c0c6001d081003840040c0202e40b4056005502c40098060001413184644c2c2d100f125640c0c1c07009103c082c1aa03082400426139441c14041c40316048154400743c08032007070303514005a030700034080d04013200c2c0c4660006400085080c55034104402c00c1d41e9130032070845032404034003213612180408900840c560340000c21740f00304004800301e1040d601d6942e55001140d80c4074035207507006130310030b0240406460703043c2c0000d0b020a000100b00c902ca0400603001441100c20740540b00060f4000e02703070480520003502c00d40b41c5011410811688106280004056105402424141414400c0b8 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 215121663 1250 215120413 215120417
    0x15070302010f060e0606180a0609140d0503220803030a061404050402130b03010e0d020601031a060102031917101a0301030503071e15020a09080c010c02100306030206120403030b01 79
    0x180100110440201440d03444170741a80c0c010760311103490340600044004001c12a40c00782c03000310f0104419078050a9102522049211942004650400c0100101d10380ca0000c115a03c10843e078400ca101d9502013904c003400d5400c01e03444454903200f405045410403140a900b081e0390720800c00c100c040102910190b403070203440c108401d0505401180d0301c1040b90100c183d840740c070b6000c10310441d1000d5200300c04d440e25180c1030741c464458000e00251034030003c0c4001c2d06d140680c589010a02d6104100060180205070001d500d4401c03803411203c3c86080b110600030a101c0307101d00c000722429101c07801c5c900c99546a031100700341c1414010400c50034510100c42c0712000105000500000e60300200701ca00a03900180005145414001c08940007412080c00800e1540d443c803a20611131101e03005040401c4958660401d80c035160300200e40d0fa65a88240f1f01d0009000e0302030f880c0941454403a00c103031203040b49800f003036064aa4000c203440c0d030310014030500c0001c4280d040000f81079061061900d00e013424 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 215122913 1250 215121663 215121671
    0xc09020d1b02060c030606070b010e060102060c0a081504110d0b030d030c02190c0b07050c040b120d0f050c07060203070b09010c09150302090d0605040b0106090f1406040515070302010f 81
    0x14400003580e4203c000c02c200140d02c40040400c0041e0ba0305c800f5950020f6111180c4500e81d0b071210348407560410b040e11604d0145c4078640102d00c01c07401031403c0c1c800402440d500c0b90843d5444980314ac01d503821069005401c0b9581d0814038103000d00031310041040414140021072a0300708c000038545003070010b11848041514000201d08219408201e0002c0340c1c003002105c0024402e20300346144840c00ca940070081c50140014a2003c00c0000306440e90b10070740444003040440351490501415650192800e6801d41029002c402003a0103100d10b00045000c51410500f4400010956880c0c44226003000d0f003d0f07031000c1440700400450f44811030b800359050303009000c018040d000241240d070603409940e1680b070700742048152942c407a506603100b0b01c030008d01080da02030503810990700805c1e09803016101c10740300384000b288841c0100311a8081381c100300d81d04c070039241c60030154199620001e0b04107944030204000020b000e40e00c0840340e07006181d01800c0300b50380e03c02503d0b0290071030303401a41100d0200d040c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 215124163 1250 215122913 215122961
    0xe0a050603100b030a18151a0a09020c010b190e01091808070503091305041103060c0a03020c0f070b03090d0c02060a0c0f06140a060b070b04031b0c09020d 68
    0x2100c03803200201c0301d03243c030415101d4a541c0300320006072900c2d800c8094049041d144c04c1c0103100c000c030000c120b00020402c041218040500e00039481d0b010351512a50420f44903441005840d115078010200c81401c0342c00010714000e510006204e19001c100c1000c8082a0030b0400d00140c00c42180090051140c03110130410451001c182c00b03c56411407002500000001c00c0703480501001744101c600b980d10041c511030207000d0b0514002c0044c80d05890a03a0440120f01c2855158100011118000c0010300e9643d403c10444c0c070700c102e0203503004809640c07190041e4075035114101000c1245202414058a0490f26441e07c29001480d08521420190800c02440001009078945070200c0d48014054684030500c00c545007090442980e4420f8000e10313030743c608020517415201e042c59050082034005406d11103203564800724030a50241c01c0c0054801c2c580c1d100410f00003030242c0f02e40813101d11408000e60521065840307802c1041180d511440080d030f00000c00c0c50384e480151083d10305480827500c0600300212 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 215125413 1250 215124163 215124181
    0x30301150503091504140d0201020304150c09090506060706050108010b040c180603020a1e09170c130f06050306090f1e030d0f1b0504050a0b0918070c06020a0e0a050603 74
    0x140401034101661a40c0045818081e00405481b10307040c1071800c035100700f03e02c1c0314028000c1d441101c05032080c40200000d54801c003403134040d80c4080b0706a136503103821032820b00710208002c00c00a45817070b61020080000034001016401b615009213001c1000141c0c2d0007901741804195903c0e69449030800c554001641c00346440c0300070380402d90b240c40c0f03001a240c9043c00c006035113071485a282c6d101d001101c030f10558186580325680304286c030941200d10104230080014660f44001503140d05130b108a10182c465122038940c1e020a29100c03580d44007044556590000c00d060042c20b0b10340c0b1041d50048003901403d0101041104c42c3c50720103404145100000c4a41951280180c1c0c1d5541121038a0f14920307400d144840c2c021440740d526590002030302c01d80600010301150b2141c821716000e0f00b80d02a000a1031901407040d69990080a0441038a40724942907110034090001c011100340180398000e40c0200c0c45a20142a081300b01d07490300e02c4420094820842071a03401c2e4031140c4144000c00410190a03 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 215126663 1250 215125413 215125423
    0x1917010506040b16030207050409080a0207060306050109060c0204090b070903110303030c0d0b01030b090a140f0103020303040e100e04060c08060f0a120201120e03220608060904060906060803030115050309 90
    0x41c820002201e4600300c505d4220700300125036002d594080c1c1401c420405124240005140e0b012540d02100d801c00d5880205400f41d4101d841000e0101d008540c041004c1c0e405605c01c1d6039110301c0200006280491980c5405081e00e050f60032a001680c075503010300c1084407000303048200c0c2a0480040d03040d0300d00340c11034400f0341c403079603070450304072500c6d221040b0441c1d00980000b981e00d90024012403040c503024058800a1490304017400c01c03503005102059404080d6081c46040c1c9030042c002d503207003e0404245a01d40f0001500c0340307007110000000003445004e21105240241e02c01c0e103020401d107502d480000c0203c0c40180103284109900c21041800d5602c28a441040b0307449101c07403141401e03140c0010b8510750501400512110f08200c1825042d44010000f440c00c2400100158141c414050340c4110702506c6000c1c40300410514000b048003480d10843d42c0b0360151243e84d02080d401d00030b550f80c0d81910307180d40c4074080d00d82c40070005201d0000500c800b080d1414152621a00f18078003983c80e15510 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 215127913 1250 215126663 215126677
    0x601171c1d0306160e01080603030d0519020c010603030e1e040c02030c030f04050a06050c060406150308070506071b0215090d02090f010e070906080a0c051917010506040b 75
    0x4080c8480303100280841400c040c030180300c8000c0988040d0300e00000c0740029604d0030100c03c2c0009a4440c4030b07042540c003a4403814001c440c080c0040d41040c00f9107090748010302003d00710710a00400020341c000714a445000604052000500220b5898914030703003d8141240e8849091140b10351140b010040d061603c2c00713604a00046030b0102c0c10800f400000d900303510440185030101d01000803207240c00f455520003130040f82c0c001c0d11010100e50381d4910880c2e0341e01404107903448981004010501044060b003202c03020441c540c0b40c0d01929603590303a840005034044032044850360011000c10007038a03081042203c086642000c5403480e2001c6034001480c2c00070508c0f20028407000400c0c4040c0548428811024541d8090030303109250401d052004860328007440359040e030740c202a00080c00d2074826001d40e011201140c5400d5859241c0c0b000c000301405040b01410108007003400b200925410f03207110240f00c0304071520340c41a1901c0d80300c42c0ba03940c01e90507040940100e00c20002005401c0b0120115594 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 215129163 1250 215127913 215127917
    0x6070c02032b121509050f16050304030c02012a0314040b120c04030f0507080d02160303110f010f140a060503070b030a11070c15080402300304080601171c 68
    0x10302030f1038030114000f801070034070108100641c00800700d001d1041d5403001c1d0080307204001e0441150f41d500c850102000c50701030050300180051002c83c00090050000c1d00c0d14601c1414100d61504150301d03002c2c16801d40d03284002c80c4c280c000c2114028541c00c1680461040c60b01c010f060303e40360034441100c01500c1410000700d11514198001960001504140c1e80619408a2101d10030b481a007030481d41c482280c01006020f015149001da5418000940041104241020741d0040d0f4a50345041d00c0000e10746c80c801ba254000d6560f602d00b550001c0c411100d500c00c1c2c1000c0015020981c14401403015802080784c4c58452601c4414400ca640000b2220304a42486804d25543c0e910f0b070303110b200070345079404111200c0720707000c1040c8080106e0603e11806480c803051003403142d216040412110250143d40107500300002c03074089401484001c4031704401030314606095402ca4042c1c1009407450744140e100786086c1d0410302c01402101001c00054551f00365803c01454000401d02032111030b65071002c01802 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 215130413 1250 215129163 215129177
    0xd05030a0c060608101b020a021c0809090702071502060108030d0e030705160e060409120f0224040b06010908030f1c021603080c07030c080703020f06070c02032b 71
    0x100542c1d0380080d0060143c6209403421000d0302144c45000d0610400b607101441041c10584d1641e40c4000b614074580c0e5002800601ca80440d005040c0c440d4031206815610003c007080102403945811140e180515031644c010040716160030030507403100c0102e00030f800c115001500100a500000404d41d101d9014203a000a020803c0300d0105d0300d9881419001881c0340242c030451058619843c2059048600c00100c44d80207590741d10070482190542580148429414445d00b05407134804d180180501400340100d8002142011401400e80d14030f1a217050030140000c10841046803246410350411400c1c2004074a450800e000c0a4490258400800d0aa00c01203a01540c040002c400400004440b4004641d80c182007800070800490201003038000c10061004100030b410700c44212400c89401d40e0b40d008d0904100c1e521806107030b010200a41c01c500c665854150301c41c4061260700e0150240b902c0301100c0c40040e01c1494140b0b4a43e2441d02c1c0202280c0b5000350004c070386180704440381c0070a8a0261 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 215131663 1250 215130413 215130437
    0xe090a05060a0f060504061812110f0604030b15010201020a1b24020a0f020f0c060d0906051003030206060a060f0c0309031e0201090909020d03050706060305060c180d05030a 76
    0x281c42c03695942c44000340c0360b03805900085280c0c108008009440d20399503500d50802d00b241d0f25007041c0709244102240d0241007248070002c1001d4080350810007000610509480c4c0e501c40005910ba040307600292011100d80050182c840fa030703540c0d1705a50b8142030000354185403001e403004d4001d6401004223031122506e000e009042084e0803000071000b031369150f00008080e035448505c1009400000e4040d0205a46030000500c2a00004070301d02e02c42e14100041802c13107120028810950800e030512240c01e40c40c0c40c0d00000055607030003600d21421814840741d045070300e0760400074907080d0050151402502502c60a1085560003181000d243c501420880c020903160324040f1200b0750b00b94805002880240f225440200c50600346000d00b60007641c810451503201c0801100310345982c41d0003507102880f0080c120020380244058440540146400107071b03290703a600d030103040c1401250070309000c1a00084c240a000d0051125031000b51003524013041c2034a0710354815039030344240081c060600170121020b03 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 215132913 1250 215131663 215131669
    0x6022b090b0a020f0a0c0305160b190507060c030b03070e0c040e090c03060a0b270112080708030c032502060402040f0f060b0a08090d080c0f04210b01060e090a0506 72
    0x250b113128803c4012560300981c00e05017246030000ba4081100c0500030340560031403d503540344880095884104a0b24a40940b60040502608210110400f400420300800d00071480620454461450b680c42c0071a500345203508042c280043c5802200d50341140c542408440003620090b1425240050481a21030b16800416841c05110001640e414407403c01002500841d90f0860050810306a83c0f0301c1e02c4409032408004c903d41e100c0c00413004c0c0348060004106030b0030307050501d1703d4480c010326841d850000d05c2e4032698605c2d48203c595a503016000001c1c0100b01d80e40319203420800256540905001c01e202d000251150005407002c2d115503210195040e4084e2680d2000fa01404248e4007000b009940340000640381c1c000240707130000b0030381000008089403070104802c60b4082d80f5035180305056649280c8a41650418503074003642d2041840003051600411901104181c0e0030b010800c0d280106140416480105030411030800503074107039416160b03c07a07840b40b81e0880038001000c2920354404001c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 215134163 1250 215132913 215132923
    0x1510031416061d19180b01051e04050904030203030708010f05030d031d0717010506030c10180f08010506031e1b040f140a0c0f05040501080711030406022b090b0a02 72
    0x107895000d1545130381101d6120388840036000301c1d64010344000032071801d80c2410b002c99810620b035502045040008c04485041454840d01c21240481e074141016102c0c400304d201990202e5048015074400010b2144558000000318014040551230015642c1098040b1741c86400303810460b03040c5500c40c1415815004180e02c0d00c6209600725081b00e488541c0e900c4030082f42251556041400e51170071010580e181000306000e04201c4024121072229071050104403819001c400200360b009441140c003084441110400c500248020300c00400d00b402c01070201820b001e4000c0b4003a0054109800301c8034620404201483e143c0b03d0341ca000d000c03001040011a028000f0b100a404d642c0d840d005914100c0b9000d0002c40d8011080400c0c108284426481e050b541d0300800400b800200390b05006c104115841107640680c0700600d460801c40f00311002c91002c3c615081781c2c02400140e004140304e18403000f404150175402e03526055400407084983c0d64003401342d407014041e25000200000b0441c08050007048 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 215135413 1250 215134163 215134217
    0x30e0111011a040513050a0209041103010204060f110609070b18060403061509060501020709180506040b0601180b04051005070c0b04030b060108090c01050c151003141606 75
    0xd1000b880d50850442804507a01c0b050741c0f02e2840d04000c190012900c11700c01c0c44c2150700c40001c22844280b0380030400b0303200d00144125000100b20b410f07040ca40d1402c0c00a0001425130780c8404802c00e0039540301900074601e5081800c2c040d0b119008010b9071540000c0c508046a02052180b969404090f0b90000c0d2007c0c0024000c0d0412400903000040000c02d902a00f1440c0440a014404a855228220a940d018400e281c0182e00a00d03080c41f00442039030040940805a83c180000086030380d8606041a1080301e042d102d0841d00000c001c160750b084005083d21800b5a80880001e5051400c000c08a01980c0101400f0300700c07100c202e0304111700850031184843d4008100f95045980c4030720700d1090380d00501040700d240c007114011a01550040c0301c058012175807000942172114004004650320703004040381c60036901c9440e01c002107004180a80c1409103100883c6240400e09604081c140d60500300c907120426804101d040b100b110205840e44180c034041d28082c0074050184005c8102c8400000c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 215136663 1250 215135413 215135447
    0x70c06030518070b0c070b0a0804031d090f0a150617060a170303100e010b0d05190603060f0513030903080c0709020301090903080108070f0306180f0308040b0f010302010c030e01 78
    0x40040749028188000e002600490030441b13a0883e1141c11400070790041500e5580402c1d800030106002a004603034090904911001243c50b040100000400c548402c0e00c1c0807074400038034010322041941d14001c20400210307104e450303070b00c540c5460801003901503031a0b016183e540340480411429619010024010011210b03881104000c40ca50707103889034800c0c0e9550800304051840043c1945800c2541c0d412202c1d028815801c01d40108402c1002d0480100b201300c1202201c88a012040250310607000030303500402c000a1900d05030494041200c01c00703031441b07030010700000180000940c000310020660380e002d050640c660a04007041450003040e50042000a0b00110000c140035400780d10041c1420b000780d4034036045990f103841c05512018103016107000851901e20610105a803502700c0e0344c401107151100c0e403880b035460702c81c14541c40c0450400c5000541001c140030600c0b080d508469009124841c40281e40d514613070002e002080003050080c10300c105000e4801c410b81c0901ca541e52840900 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 215137913 1250 215136663 215136673
    0x9090c0303040e070e030a080a0f140307021b03060f13050c04090f02130e03090f010e1302040e071b06050a090b0405010c02121801050702220212010803070c06030518 73
    0x94000c809510004c46210b400109110b400b80320901c1d000a0032403080f50415000c5140c56626541240c065000101080900100b00c1480c003031292031030025840b80c0010360150100d400f92840f0380e840c82a0064403644030313030b0101084c0280c418102e01d1030354101c134a9800c07036594801c01d40750041c281582c98142c00d901524188000c0244410710510a418610858524100c01129142d10084400245800d01d4550091080441c1410114010041c85005040c160b2840303590100040325441012001c48020380c012404004041c41d1080325074001f0050b040c10039882490101500c8c440c4100c00d0080e00e807503201e402181c50a0310030780c490402503410406203100c41c0b40c5810442e02821180200100510600100d2043e07280e07050140e03075800d40d60388590740080d401c1c00300464407038014820a1740c0c0700c0000064002942030003008020b4400a410003d40c68942e440d60404003254140d0141000782c00401042c0000f40c02c101c0e135502611000d0400041c1500c40200c4000020450481e0890314490 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 215139163 1250 215137913 215137919
    0xe10030b0a0203012111060d0e011e15030305160c03050a03020105061003060303090e09070b0307020c010807050406051614010207050c0406060c12080910020708090f04061409090c030304 82
    0x703a0002c5042c1c511040c0d01c40c0c0784400c401d52001c1181d405103400352100000984031031283c94907000400d0b0041c5141c1021801600740203072642180e0b001180ea520f02d030104a000d0442d140d590044d014040324510b6046009891901c0240c49440307917040f058042010202c5407420443c0075070288002e1600481101d066401038039010340244029110720b40728402480d040a202c40c0f280c01a10180d03641030b40c03030035805454500400800b0a0240204007540540b010200f801098075001e140b0a900580c01000113180950000d0001c4401410090401400b040148201500101258410000500c2031070090115042144036070b4038007000301c1540d500014102c01807290024000301c08a82c2143c040000c2c1d560344000307035030b0040c41c180c000307000c1020003046180e0103000c2d14000354803040510a80d1500703ca2551440b0490307104840c200c41450010a8034661030800791209000f03081d0a80b0704000c03d03030500c0700004500303a400d1003052080038070354002284030b00d09004c4060400c0c0041c0c100ca8980303032 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 215140413 1250 215139163 215139181
    0x110d0302132d170d11031b030a03140105090c07060e0d110106081c050c0708070306020301090c11070911040e010902090102120304200609090103030807091403070e10030b 75
    0x1a8100e40810502c1c880403000c200c41520b140061550722144000700300701c10601c002030b208139400b0890b0010b0b40c0024062020121074441004480500100140d41d485d003000101504407120700ea44019a0400342c8010700964451821403074110542c01d01042d210081d41c600386015107541204040c241c081c482510110780e030440c0000803c564050001d0080c070b5101e0010958032170500302c0c005402148591000001170080004100024464085c0c940e581e07198054146449541d80c02214490f82c000010402c0324020f201e1041d0080d802d140c142c0c02d1150f01c0441c2d43d41c400d9240129081e4a5840710381003000046003040f02d00800072100162125a5074005410003034005100d214054002c00342c3d0740303210080c0300e001ca0344200d81c0301004007141410540d903014611715040403240c014200300400000b50762001c3d80f050003503110740d655207030a01d85404024000a00340c1d101c0f21405140240509242d40c0110340c2c2c000b500c0c2c11403021082c80d99070030315812880e1415803014121185110510030300305 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 215141663 1250 215140413 215140469
    0x90102130b04061709030a140d090b04031b0b0612010b0406170d09030305040905060a0e150103180213020d060b0a031401050a050d1101050c07080a12110d030213 71
    0xa040d13030711150b010100c084024032000c0b504031500c6655400030401008030f5402101e040003c14014600141004440046e400c12210048416104004000104000c040e4040a03811000035111070721041c4e0000366449401c2c500e030107400a0f224903160540160800d00950103000503410080081c0182d90742e602012a404d0340104000310070740601074280c90250700a141c3c034400c49925540d040e15051401500714000c01d80540015802544501e00099041e0031035850350040310b4000150451a41410006d000c44d4905124216907803511751099002d0303a41c01040040051740c842c00980d5540140c0e01c848014900c1d0740281c2c00d40342d8085260346e091581136000350120706c00c0b0303007038050700742d0302c43d81004045a210300c501c0b07070300c4080303450141c002070585400c6129401040c14800e0400541201507030604816401c0840e20f1350040013020144903c1a500c00b1441156013000b40741c000c0380800341c58440b15211648800d054000540c00f200c2d0f02c0e2046403000801148000982895400e98409030340 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 215142913 1250 215141663 215141669
    0x60b0306040f02090a1a0403150203100e06100305090f0604030908060f1003020103021c05091f0203220302100504060b040506100822020d03081806061008090102130b04 74
    0x4a2508101074030100b0507100b29071034254010014180b0307901d0241000c101440180008040c180144000000509101d440485901d4101c9015880b4030b008849000f04101640c0f00556000005007032003c1911040040e1a04100c641340100721603407040d00040c5000900d143c1d500403880b48d50308000a1513405041750013680c0e5247d058a43d941c0700c2151100c54408140d80c803002042d030304982000113601a9006207281c1c2c01c0e205600019080440462044440460b4050060780041c5200703c019044980c850700c45008040c0114258107103848a9000e644480201128070700302c10700b011b81818020031241c107441e1800d950500251a151038540c0151204040702406035080501283c0a441c1000103036600040c240da0340d601340d9941e0454944180441146c194050324000050000350b00c1d940205400c440c06070322048501d003050104045104030a04000807143c00000610001e95500d02002c4401a80c515000c8034644842081c01d0091098001c0c1c15100095540c00080542400c1c0242c021 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 215144163 1250 215142913 215142919
    0xf0e18070c0b0702060903090603041103102018090402031207030507030e010509010807050a0e030102070614010b120403050a030209120a02090a0e03091e030703060b1f0806091504060b0306 83
    0x419110303c072081c2e0b0303101001c2d02d0300c2d041c0c1d420030301c00341400e420844051503006009603c0e408040d01000003290a20f8080c03950720899686401c82885000c9001401444140c0c02400f050b180c100e14110014070b810410703030003612402e049000f203400e6507000c00454014540d06010079580316101c2c64080e0459003c208200c0209080e00c04081d0158002c8041e50104d1406031100c001c3e580d540c0000701c50903401000c120040c45400498028592000d102828480703104040000e0405001c002c00119540142d00c1303a0355040082084260000e1440600c5801683c10f013440b54a0311584071066010380101d1010701c0c3c01074660b0320520650080040c649110f00c0c0269249001c580382e8400340c130290b41116a0508450307000300240080345c202002d22012704c030f82c03512840c82c150540100090400d80107034000e0704c8442c3c680d40d82c00800c2c039000c5a400e4070b00340d00d0b45000921520f18400604004030060500b8868080c410000742e645040551603804100001d00c06c014007501c0d400c02501c10380094441c140 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 215145413 1250 215144163 215144183
    0x4090b0c0c0115140d031103070f0c0503010b060a0311070812040303050f06100c0c03020a0e01090c0905100305060f030624040b0a0b070c0306050a02070317070f0e18070c 75
    0x228912104010404d0b42c10b42c0400301558482101400303400341d0740610480c108007060408034000802440607080040c413496038a000440d0360b09004910044a82095119034500008401325a4840e17080b240640c040f8140440d28401d000213084c518055100041c1c100440050b0031400b0f00354460700b40b845075202e40c03400c200c0c944a88400f080305d048221507080d005241d41e110340d03000038000c5e00784000c2244181c01c400b540b9602c03035001c101e09545690280c0c0114540a00520410a96002e4401090b415141c07000c0894a014001401d051040b84803c0a040d41c4001290640e1110703101041026409422030b101e5081c0707035072034071003480a003101c1c150300020890002c031032481c240c090444420402002d0081407400d00641103090752040c141103498441c144800400100907004041c40b0340c80100006848800c40c3c100940a48007820b4074031010410101003111198001d089804102f0542c80c00303110088541006c90321001c80295001c1c6900c41e6030081110803640030000c54100391040c84000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 215146663 1250 215145413 215145431
    0x102010c08040c0b07060612050304080d111209060c07080c010f030911120f0109051b04051006030c02010204030f0510060803070b061323040c1403060a020904090b0c0c01 75
    0x11540702098030018a0b48507000c5003006581c2a81018050041c010000003032140c1d5210305012544140000488840d0800700d070401c02070105100300e8020803541d08040140c400c0800c0240e444010350340d40800030240c042269112500c03142e080c0e0b1001821082260030198443d110203175941d0902c5051800039415030480070480c0d00c82c1c06424040c07980452040c140c14803c0b02000b2881c40349181140c20b61150005c20340203103000340241e4080c0c038050005404e0301c1c4590420752181c3e5004400c446e0180742418284800c0c13041400c0c0010855055240000f41d190715000100e0180c4034680c0050074401d0100c0a200600034046001c60701d008112904000c0c0507a6541c4060300c90050b00c201814609803000003032a2401c1c20741b140010b9915540300010040c171100345040400041d041c0001a10140d98204410040c000f03810401528007828407560049a00c00001d40d520401444050010307000700fa00200303601c03181c0052401c0c03136000052181503d0f04104c0030040740c0003000080e84560800da020 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 215147913 1250 215146663 215146667
    0xf1b0e10050307170c130507090b1c09020a0504020a0806040506030a03050d09080405210114100620300f0313050708031b0601150206010e1f0b07020102010c 69
    0x2a011118090040d05840f860f00914080c000e44405060b01300e4000c420294140b03030381d03000c1400c0104400f20703400521401c2c6000001c01c0c151080e003100d03a030003200304000c40703071a80041819600d08050f5080400c07807295510114101d002d0b558440358220b8004510800b20703030380000260b0722801e02a102044595034500416540303405040c005000311b10304104105031619260011705402d40039901d200d207040c0e900d1000c90b032180816813840044401c070f03925100c1125002c0c050701c9181901440c0d00c0500c0c0c02c3c40002100c005040344030b403405000c46034002021040888016000001020094800300405d14480d041c1038058030318801e050000d4a4003400309212044281da00c5105c100b290f07a81140d42320b041440d202043ca4000380c0e114440c0c0040002c03403a000b0001040c81043c141c050900d680384111110b86010f2041e0000c500c05050404104885540003034810304484003d0315010303190300c420103100c9a2592907064004404420b810226141c9401c000900c09039200703038000c01038800c80b2740003 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 215149163 1250 215147913 215147941
    0xc010e0d05120703020c0d111504050c060d090b04031107240503041a0103050c04271209080607080417090307030210030e060f01050a0506030408160f1b0e 68
    0x300d404154203200c10107031060381c079254607440440360038018589400f0242d010300e000d40e400d8000c1d0001d400762500d0340c2d901c401400706240d24407515030201070b60300341956025180c45c84100c1c0d80d4025840404c4043e500e180c0d90300300b10324403034108002d210300b420242030044c071076411505001c1301c500c40d0030b1000503224050302a81710740b0a000a141031035101804030807035403644041d005550807803002c0348841c4202d007030b5400d89000718031900052991002680501c01694005962110b58400d0010041d0440e03003002d0700c3d80884c56000e5145400104503d00039246010150000002c0f07204450400c00c400340c0000000e13000701d0007032005110782049034421060610070b401035250950826241000103040c034012626541482d0b0501003891008003041c24a0f28200f22420802d0050480c01042141440c4c01c000303020f01801d444203891071400d40c454515500c14010300840c40e0030a0f185250500101090040d000c0c1c0c0d000c0150404905105034594612049004090708401d400d0081441023001e10a = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 215150413 1250 215149163 215149183
    0xd060204030b0c030f040204090819020f1903020318151206090c0703020d200f070f050d0209040b0901020f040b0304020a090e0c0909070e07020f010c0c08180103090204020a02030c010e 81
    0x201c02d02176545a9080c0000340c40300f9030007104c0d441d00501c6010350400300410980c0200c0e039540d005100d90002e41920501e40001e081d0304414040390354080c00c2c042036001c0101c891070f00d6480c144902c6d0b81d10080100380f400d1104020401d0581000c1070041400b0045175070795020785000c03030707186820380c460000c0c4045610403960002c004d6800400074151043c05150008031114095030030076a26507000041900b040c08024180c00f8540040d4000d0240c0900305071600063322003a1041d40c0c02c04555030102d0480c242c0a00054800304d4040300003480807074250120b0b405221140d415076142ea949003010355440d002074034201c1c4a1407030801c020501e0f800600c19030245900200050551100c05d009014460303a01911441a5001e01c0c0808140c0b40589210b00e402884c60358020b251495a0f070714524210341c10020b51108024400b0031203400b10b980c600c1a1502030044504485651444000680c020000c034000290418008900c20f0860741e0080064040c0c502200004d2181c1c1033b075091800e4440200742 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 215151663 1250 215150413 215150431
    0xa02030d0c05010b090124021606020a03091502031e0913060e160f14040306050408030103030801060807020d12020909040c154503050607121e020a020c0d060204030b0c03 75
    0x1011079281f200308080c2d6440c401c2d50301c0c0180c80c6021502560094802c24903040400507901015000c420140d10428110080040d00d10580e030070300c0c0501c0020340fa071041000902c6802e4800d400c05c09118034600455a80c180000d0036111081030194050000d05442d00c10f99904580c048000740110682102d0700d464482103a07180001484044016500310140300808489048140008030004030203104036809079006072001c1e41c50350324610f40101118016041a010800d580d002d00c03100c550001031348941005681022203c004809242200034001c0c03140a940c4105d00c542031005000c1c6035a48101a5a4071800903107207036a40420030f60f078401503582d5500c0d03e4808103660140b07031401480980740c0f400035240c01ca0a03085a4100d540041c800c503410a682a400647c2800740860300701645000803152040140200f4201c6406982c244034900f603180c00441d00041c852204510a0180d4108298002c2c440401c1140604041009410900045500d60060004036903401908000d0300e22032003080c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 215152913 1250 215151663 215151689
    0x20c090106050a110a05030d050603030c0a1227060306140f0d0c1203080a0f0b030d080a0f090c1406040308041403011d010e12030603100b030a02030d0c05010b0901 72
    0x1402c4940364011040d480401030b54801c00310449009105c0c4000c2e241c011002562540311040b030150848502601241c070980c01045036084806000c00d03030f403082c0d81e0032040c4880716010461050304c0c16a044a07018080c00c1c940c1c1481d10100300048040b0094581c599010818240c45049214503120002030341c960200003aa022a11880c0c0240201d030034901c21300c4030303c0b1003551301c502c030040e1031980c0d240483c08540d1000c2040701d280024030550001480e1200140999624140441d0325011580040b9040020400008240042030340006402d1401c03484100300c454140c3c1403603512071006004060210143e40c0542000d032900805903410340380c121040d94a0240740444c0c98102c14034507988282c165481e03d00c40b00310003440203484c2100400303050000c60035203d5205094145640304485840d800c2c814410321186031030000d84211400d41c400340c0000c0032034075000000e02d81040c2240003075242c811304103c3c16485a1101000070002d20810007031155002d4441001123002003402459008021 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 215154163 1250 215152913 215152919
    0x1b090c170405031b030421110613030b1503160e0105060d09060c05070506060406080c040b0a0f09020406021612020108040f0b0c0c0c0d02031005060102030408060403031b020c0901 79
    0x111141541e00306200d101200d140c5a80d030f50314681c2c2626100c161010541001c5410040001c6d50080c101c083d82c5201105030140c001c540c0c80d140304414280c032107805004007083d2141441d4422903007401468100345054428a448004500d0398a44101228001d0043e08125a688191165003209881e19902e00020a81c245414440980c0280380701082c0c45849803d000003107030340c522078540f0b200056980d042e541c90007410301038540040644007900551809404214071000458050f840900c1240c0100d21260140e0010740c05c1d400301e410100c10a1060305000400c0f0280f0341c01001168110380a6441091106003008070400700c920a42008000e8004808010b41c841d0a410742d10a10a0420301a810b945848003410703131500303d039a2901880c00045a183c00d4004210000250f80704440d40c8030b942c0f0482c0e0100380c50b94a2420814400ca82320303404038015071f0007441610081c007030340d80859409103441e08006001c1d103c503440708070914038813540b2241500c0c804514503c9800024003004050b0b40f0b = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 215155413 1250 215154163 215154197
    0x10e0132041719092117090a0e1302032e09030302041e080f030708120a140708061804021809120a0903020a0b09032a04020301031b090c 60
    0x50034501005a001044030001d1540301070315250f42c10a07a940c44030405410407400554001e644007000f051800c450b1010780010f140c0700e1411811a0301d4002131a29810b030800460007950007078001d02035903d4418100207002940071181811980202c0c01c41d001848805842700c50315040e680140b18205142c000344d0118050f542022000074401c2c94010700c0c1a6a8450030706c0d0b407800d0003400801c104000f010400141900304100a103080c09071010b07521304101583c0350103651180901c0b03040c0e140c01c524002034140241d40c0c403180e160054070380003081c0c601d0400300003400ba010031102d16100790317601106c805442d5403801c04244a254080e2115001034040c01c1800000400142210007900c2507015210140b000100907200b000740c00d8981207003050440c0304001000155400034041c01800384040b10040d82c0c000346040c00e80040c0c59502000107090940d0600d02178441c0680b5070001d00020000040090141000e08401e4259051420f0a5207407000c03c0c2c261884e041318080002c505080304480f40d1 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 215156663 1250 215155413 215155433
    0x1e120c02030c0a031b0b04061d0406150816080f04022817010612030e090a0623030114160f02100501032a0602060114060c010e013204 59
    0x140c00103044403a0308655600098010425400494018011008003500d41241c4c450f0346019000e032038011030a0604020000709600c08800d440101c050f2014400e101c5c64690340e1080d00501410784202d415840320b91000340403030301309587c1c08158410800d10118440e11801440d4080d42c40003800c40055101c603020041b0f0303c0d0b00c4140071400010ba81c1c0165080000e400092350041c161921250b0240e4484614a03084448039407007403220703070418040d12002a0740b010300c65200d240110341c01071441d01ea007001c101c01000b464000342c403520091f1683d281e0740d00c1040758099040004400034000c4d400d5101985450241c00d40f0010380d4800640140c944540c00740000c00c0b0305941c00d1040f02c0003400003910303207000d0f50300a074801d442c40d9144a1110002a400f90822005000c49201c0c0c00600307841c00394000d42e01d050511410a054612040c1c3c50030075501d1200315881d82c5034900c002c0c05281050315500380203261b60300403024010029580300300da680d021040194007600c8165824203030f035039a4807000750079 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 215157913 1250 215156663 215156687
    0x30e01020903250509040f02040507090906060210270204020f2b0e0304060f121b030609050a0e0a06020a0201110406020c031915090501020d0609091e12 67
    0x6540034040300c1d449403400c11048800d1030340000001c0f11681460005110aa0550000c1d4081d440d24401c00002c10a100c4400c1d0344554155030004250742e4481080f280206250002d008031800d000d400160f00c1c0d40042d03541058000300d10100b00598800402c0c0b0341d0100040000c1c122801c0001e0800c02510f4184e0103081341d540303a4a0050b25010408003040c80a10020100e4a101c040944003090155070f07034402c40307510711400c00056107064184000580703070034908004541002140360074074948540395048508a520559803a400e99602083d020340505802e0251121103485c001c0091600c45803405820b182c88d4100d005003810000395103646000c3d41c414540070041d9926029480c4c88030900c1d0001b80010034003a03003d0410210020201803e190243e901d00140c045045003003008030700460084901c0c00480381000a0602903403410902901506480001d81494090300180e040150b401604400303104440d41e403000a01040000e000000b0785a014100c40546200c41ca4268001e0f0303d00c1325a = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 215159163 1250 215157913 215157941
    0x15031b06040b130305060a0b011704050a08070f05010c03020f0913092f10050a030506011806021608030f040b0304060908040b0903010e010b100e041b0206010f060804020a0603 77
    0x38007a1201d80b02c900c141e109815049805200400800500070705102d12900b043c24202c05229622030100001e04580844249140100c0150081004c110041156400e5039610681c92a1550640d041140e04c0c812500001d07a8507509004008030707030074400c1c4200c40700c0442006070241400449070611a2800c1c50380c150250150b956042c45004c00c030100704141c007090605030402c2e201e11402c45c10001c0c402c107408215020300704140c1415919034103c03080c0c901c1ca40c42850300054a980f4103004958180a00c10003140c90203070b02c2004102e0713035400700e00f4a8209031001c40041c240c83c0e881d6100c941e6132054a112a0144005000c00d2005018007030003503400c01e00412002c140700a031510741c0035880e440b5901c5441458000107014983c0d0030300380075282c860b01540d002080503048920110b038800c44020500410015241d40c608140c2e5110b50000c81030715460620600c98800460020355078180c00e000d684030b099640c00000460601c01c04055200342c0c1c1c050403038020280703400d4054024080503541c4540c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 215160413 1250 215159163 215159167
    0x9210201060b1c0e0303090f15061c021c080406020d020303040506041407180b0a0e060306010b160b0f041e0c090207140d0207060806041a060702060c070308040501030515031b06 78
    0x18400400c0611f00030090038019107800c5a808100785d190040b0700ba004080d0700c0608081107203607a210140d1054529071609415400105880002e205071003000e5940090710400c1e2141040c884004084c000380d50b0f0300e40807aa100c4600c06810790740da0100b120028500d0b4008400036002031080c3c907512440c05000000c903000d041e03d40c0c03c40d4402c0035403501e0711001c56a980302400850700d03022280741d00070100510008600d0030180042074464405004074007074840f0018000700d50702407842d0f0840f1501c2c1c0016034000039041003861030300110415a02641d401d032443d0a4041e9201000703001d13a407442e41c40216418123038036040c1240003a400030708041c0c404103e0040318842d008800d00100c1d0441d41ca41e400307441e10a0a20602038401500940103d000714030b40680c0c0c080864841a1151000001702c42e155112500c0788002800d910400281c1c2090307020f0000700004029030840030b0400c1c0c50013601d040c402e03951004090481e520b40308003030f00e60660004040100117100180381e001940300c0038000e28 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 215161663 1250 215160413 215160431
    0x614040213080717060709080c04050601121508060604052401020316060506130606020309010e1c24050f04030806031507092103050915070609210201060b1c 69
    0xe41000f9140d84903101c40b480368a2094138100c000d000d000c0d4001c8050420088842c1000005a075480705420303001e00071903451000c54090380c082d1000c07944c1d10345428030074130074100074042c40c0020b1911403007107010910403840461828501802480d2140128805109541e400c0aa6440c0e628040c1010603056000c20404116042280b0b490030102901490001c1a0343c1401024003070200214003561032410b20f0548240021580817040716018942403920140c14044400021a00c810400c80240041071140d06030040200c1002c482192134030341103020f0595480c402181041c2c0da01210502c9a1400f00c0d800607002034094041141c000308080c1c11244240100e010501e07403100107031004400700c2ca403035a0400002e40542c0c00450004450844c0100701e5001c0d5a01030710500801f070030399109008170800d6030f07038081404050b40c0060760031a400340041386003070420841000003030395158404030344002600e22040c014051002101c00070000b042c500060003402100c183c1c1d001c0403c1209940300c000314 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 215162913 1250 215161663 215161679
    0x4021306031502042d14030313090c1b0c06110114100f06090e060f030f01060f060e0402090306190902030f0d2a0201030c0c050d0905090105040614040213 68
    0x1c442c03008010030010380c0c55042c002070000f4002c818400740f50084030032504485100e00400e9840886049045d112803c06220001038103500400c1279020f182401500000341c190510340080d01002c80d00e4950b080c0c4030141c15904c040d4007181440150980c0d5001e1030800055115400b440304000501c0c00009041030b03d0781038108024000c0d6045003010003a45000d12014444c00340100060046060030642a480c24454850519004141511a40c0f0300e103030102603030f10144900701d00012030f6002000705903100d42d40d05e03401001602420307000034078074030f56540a402d040c821240007440050040c0099070300c40c05840c462100c3c80300e0003585185c8803520440140c500300894006825083c000e4440c0c0300c45410000e1541c3c2070034018481640f03800b0304001d41413a6520304240e9a980a01e004a500d241119003500c442c021800010010322405516400080e444603500d41982d07812240703d41c080e603a83d800c00c400e035941f9003d1502d03000c08000d0491841c0c58581d0040a41081100e458400640d0f02da0340 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 215164163 1250 215162913 215162933
    0xe060f0403061a090105011b48050103060305060f040309080a0b0610081b0702012a1106030c0f0d0612030c0c0812030f070306050418030206130b0402130603 69
    0x203441d0040751443c3c2001401d00d01288030502402d02860320030401c05950143c1040030041140c05006a18070340c05001c3d00c0110a1100303800c030b0403500010700141044000c05900f480700c0d114102400d441200005c15117602c83d001303400450350040000c100d86d8403540d8041c0341031070010300203d0503c4070007400007410740401e20403880454051b041c03440751361800d271061281d403d03c4d4034424000c1084400070442103180030200058110840c412700b603241c94580c80140c071144030800c0c4403900c0340c2002644400013401141d20a5010380700d0403001040c031a00f02c0520a41d0b006c00e075070150301d8250034401d0300034815801014100301280d40303030082200d41c1c4c0c40790400e4035464192000d130300148801c14803000b8880c003451b054005054a2000b450790780f060008001d02030001905c8409032010002c045120300d440380c0c000c2006450000c0040003074a401184444200301001401c8001d0300801000403001444c071a131201032150030181041c910354940c0e0030000107072010021307406100d42e9080040081805940c0c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 215165413 1250 215164163 215164181
    0x604030e030c0612060d020415030605010506070c1502030c0102120610021606030b0d0c06090e090616050912010c02030a0207080f0c01030b0a0e0112061406100e03070506070804030c060f0e060f040306 88
    0x51202c81c8680ae41c14020103641b4142c10090081c2002c10030310001881c54070401d02151420894440740142080b801c80c2188603915804489600119800c0201418081018081d0408590007100e01c00322000030781e2226801814940d40d2440c100040000c2070094000903030180d4003d2180403a002c00381e581d5041d50340346401c00c5000548000040c0041320001c6a0240c01c1010440200881d10748507944000600c0b10685840401c0000328080225442d070482c40d11080949400034400030608101c02540c031340107035596100500c0340020029203001d011541d40010b06840024040002400c0f0040d00500038102c01a50042c0205500041c2121606000741c0a03152950019650400600300001960135034106030b8480a00d4400703115042c1e42d0390a10020038000c60030907041100000c0c0010342409034503886103030050b4002800004000820b8001c000350380c8149510f101c22916050201d030b940180110100100f0103078290103440b45045405803044201c02e5080c20300e41600c0790740705000d0b0344280c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 215166663 1250 215165413 215165441
    0xc09040e0c030f07300203010920100206040f05070308030903040f05010503010e04062705010b09010603140c0322050d0e041104030b06030705060a020604030e030c0612060d0204 78
    0x2a201005841e09003d681c200c0d00c3c210004002d42410f007420f01e01c1c042c5841141c0b045200035080e414281200d881900100c03d60018000c001640d03a44c280b80d011a511407841c2e9104000002d0340500514000b510f103d6a100c10354001c000d1540e0320b0741e070800d044062820580e03071845803070310001c00038100000035481508894040c2d03880c2c41c43c4c04945024103480b5001541485401d0005105c44400b001b0003d44c07041c0c06c400c0c082580b10391034203060002c5c100d5078a01c400314801c4603400700c140181500038004120301500d80142c030780e90b203101c110100c480c810300c003801c0c50a80c1c00100340c0c181100f0002c1c0da00101705102e6500f400300111100071041e1014001140d8540240f01c6071940203801c044111030a04082d9014860604901c4103a00a8030580c00003c0404050700d0115899071801c000d085c0c02b910000d402c55582e450a8200a5524042118220000340725009840c4c06402c0228461921403400381c01e460809a041c1200760340b09500801564011048080f086c1c0075070703100d01803464808006 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 215167913 1250 215166663 215166673
    0xf0603031701050315060118030b1003030806031c050a051303031115190c030f0c03060e1302060f2101260105090a06050c040e190e011b080c09040e 65
    0x6021141c094a5050384820700c80d4014080c0b100d02002442e074000e502a00900c2c081c800f81c0000c07090404141c0450f0405000e100c004010407010511000c004410799020380ca842445680700020541d88044007104d0340304c400b6070320700101c1603036000b000a40030100942c1402030070000940070301030803502c20b51f0060f400240d500c190040d0849043c080c5800075115504801094500030150701c208820700d4186031b01c8660303540c911028083c400d61200b0f40000315018103100c070019118008000d4246801407289414192000c91aa1903001003207031549680a8582400c00400c1030a041e034a40140003403003e5404c160340c600520100d00d004a601809146514002e02c8564100c0101d902800d448440e840343c0c508020f000489030b002610f05c01b03943d803088012415030307101c50744207065008941c40440c0c1800141d0a0201a50012611000c0025000000c2010380a0640c045007078079141451118855a6001d0707420b00284141c03a425804070728082c00300c0c0751914440106080315070080d00303c1e60716044 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 215169163 1250 215167913 215167937
    0x1050402090703020c0c011101020c0313080d0815060d141e09150408030405031204050c01030b2d0a08030d0506040c08040305041e032f120316060f060303 68
    0x215401e6040702c080c0c541141030000101c8096580c0c0d00c902081414040b4004503401286000d4048600c0c0540c8602602d80f42e20f00015081059070fa40e000e00714440c000d8800808500380b084010602c01c104110101d42100581c07001d105180c0e120320180003001d40c5850245400d0f0201c0440c030b41c09249680500501c01c3c2c4054210b0590240103000d004c81d9800005951007610b8a10035031580081d0403c403819034030b8480349400c6d45180302e0241244a00c0b10968100414064007050a603007484003030302c4c203102c00c04800d42000524062180e041007005c603000390b001c1c1081c01d00f1a50514410340a420344007400c0d103941041c1d181d038001d4003083c02069100c104200303460070b05e0700445001e0b0b10103083c00f40490070541d8018045006038080d50000c41503032809007134038150805c081002990400812f11150a01d529020250348914454160260100000414900307280e95955910030741c1401850a0540d640b80090b004080540305907100c0ea01d894075612044424450000198441d46030242d02080c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 215170413 1250 215169163 215169169
    0xc07020402190819050c120907080613050d030203070f110a02040216200d03050a0c0209010605030103030e1e0103090302010902040e010203040309090e0604030e0d0b07050c010b04060b19050c060901050402 90
    0x44041c01c01c3d200701d42040d090083c1c50750046c06031126510401254619590713000003041c9031550780c0e488540310307200e84002c2c000d4005801054039001409001610750103610420181e06a1000b912560700042c88442a072003268460706030307c03c801120f8000d80c3c01d043c07202d40009050760405d1424030a8514521746041c201f00f0082d040e4400006101341d00e580003c0d0100000364000c071601d030090244500041c28150651003a140c0d80290f0394020140344095840b41401000c90704240002c8002c94003482003244149410300541c0020006020403200c602028001100581104070045042d90b4880044900607907e0b0b010301d050030b540d03150006032207240a090082c411507903030b84050791007454480350102c048000f18004c0c5e40b050700340c24498070031081440492200d4502c44005464140207000327001c3c0d401c1c0c1c810000d00c420108440207100c4810440c003000100c541e580708801d5040320411843c01e0407225131561032130101c803a00f0300d14203086003200910b0415000f260707141c1c0107035035800405c001c5203 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 215171663 1250 215170413 215170441
    0xf13060c08090c01020604080304030e03030d0f02031005030c0a1502011805030a1e0503010b0304080405030607090302190b0d18020303040b0a2d08271b0301050f0c070204021908 78
    0x80f40910041a07a410151150200c42c8070241c0702404000d60040e4441e1551010030403500c100c0c0e0b20020400c12038110b00642c0d4029001510b1542100740c061000040d0b03031038000b44800c2e59000061503500614900728180c01c0c803074168a200d206554846500d078070141c2031072407003030340c098018400703540d450f90f02120052410050b28030107036041105014407a4040d500c0307015a41540c10910006642c0e4889051080b118012035000d107915100c1c2c0c2c03040002c00d56014546804070f034420741b094038860b010b0071902850301c1080c1c02560070040c001d000c3c10803403030b005420111001072b100c00b185016001d2500440d09580c0142c00120604500094000e2016032240f400301846140c001d160b020300c0000e164035108440900c407040104801100810405e00003001c85844404400c07014201e9044410704845d00c0e41d01c4140701c1c1d041c0403045030005d003090a041c003517684074407043c00c3c11141c140e50714882042e490b040240b00340d8026600b408010301c448030100300480585810703201e440e418034000014800340 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 215172913 1250 215171663 215171683
    0x15020303011206091a040609050c0102030307020d05070c03020306012403151404060b0d06060207141f050d050c0306041802130903030b060703030203070f02030705060f13060c0809 79
    0x198410401040b03014000511200410b502c0100440c01e440d16040c00b050030942c06041c065140c00080a0004100d0705500c140c0390341e449001a960701c0f40192006a0b201e00048440c0000341c2c100440b42c01046204000074201f4510509120031503d4503a00824a0a130007604103a809200a14900324005c0c11045100c08030b24261800780300c43d00108100540540003803140401c90750644129001c90b0b03540d40c111102620303510b81f0003600d80c0a20660100030f4003461180c1c42c09401040004209440300c145806108000a081c0b240a10382c10b9804110300c0c51080c0840e4100001840304501031a503030b0080c61f000d500324007503203074030707801d00c0010002282d0786c5440203041340c401c500802c0c0058540f039a090488044400300041d514010b800d05601400c04040d6240d03101900140c0c0307404240d0590b000d14040c10f00f980c3c40b056580311010041ea5244a80344014000c0d600071000200d00301c0380d0410031a801000101d0404403920155034034020794011820110209080c4010454681802c115140075 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 215174163 1250 215172913 215172917
    0x1150303030b1804031b030302270a050103050f0612030f0a1e020f0604140c220506120a11010e090a0e0d0309030522182009060a03050603010f09030915 67
    0x580c01c144d40c006d4418200048510300d401040c1020009050007a816526803880c1a181c02a81040e01c0103904120002d1000f0188900c041c40d6012403154804d1003902c0c810017181000ca11350380c48401c10490914540004943e4a200812180800c03400e200c0c040c0010b010140c44a00385550514003c03d030f0042d41481c5c00b01154050b00e08013521100c009065a04190040d02c0f0020baa0421982c0c00e040000c0319544980018500c50507081f8641e90542842007009094000c10254580c8401c10460780f666090154156000420103408143d190f0024a4200c9050400c1201c008034000400e8000030304a640c10015592001045000c540c10f1001e251196050303d0208104800c0e039a0160144c003c24203201000301c800c403079050004000740c4001c1c002c0e010f1805036402c8038040124036405407140300c0c1e05255102c0f03a003088070035030262001611150b140080280d41010f9524804400420004100c00e600d51340310705000c0c0c082542072196000c0680a59148019141444d00e00d18143c0503010480301 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 215175413 1250 215174163 215174209
    0x170606040216030f09050a0b030405060c070203070303031107060e0f2509050c0d020c0610120c120c0e09010f15050108041502040305010218010f080c03130501150303030b 75
    0x300c1101c501c8000003080c0c0e80f5003404101034280d48801c5451020b9130300010b0f0040720506001c252111440701071441359205508540d4a0b030307078820f180314030360007000d400941550002d1000c0c0006030194101c3c000344d481508045080085035100c00342510000e02c0401c0b40d0740c02052140780020414000881d541c42d03004c0d60035103d08a480c640c0721490299100d000700007607403200030614048204044656084010780b040d500c0700c0740100384d6619100155800000d01c4400e840020f8041d8001620703030743c0150400300d6482c02901d00040c0040304c960040d4103c0e1044034208002c1820705d1922070f81390003040003d0000845100000d2840d007252008215511030ba1700150040280382c0c0d22075407680d4015400b07400e003082107000c400c03c0070203030143e9040140103500100d140b92003a60080800080d8280076600c40103012303d285000e0311401c0080c0c0e0072084551040000a54181402121001c914821300001840c24007160200070420025001200003030b4549404000c9441d11a80380d940c42c1001108500b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 215176663 1250 215175413 215175427
    0x60e0102060c09060c0a12020106050a080c030d0806041b0f14030609010611100203040b040b0708040525091b080c03010f0905220b0106020609010204180b060708041706060402 77
    0x381c0500103800380b04c2d40c0005800c510030201131040c100c0c81a481001041d07c0d404804019010700461b00900d80035405200c1c0000b80203500146150681801401804181011b060120f03901c240040001c0d800c552900c40c646039a101c960120b0420f01c0d003e9031180485444160300421609072070159032a404000c0c428801d840c0e5454030590304407503c905000c4a08250201348905020700c41c2e194042d118800f1040005100e0307481803441c886c81c4241c20700142c60703a0b0b2080c1a1070b801400d07074001d082644940700c5240080350040350040c1903200c03a1820050140d1717800001c0141c4030440a040780c94103044100c02034440e00407115a070442a654501411136061203e00b41000c48188119100c81d6291400700d1014440c008100d5001e00d2083c00c0c0d40001044c504105540c61001c6c41080014401d080001e4000f42e01842600d060382e07004103241204100b0340e4800806400c0c1460b131540d120300100075000c001000800280018004400c0510300904000f880c1814650010541401103004001071 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 215177913 1250 215176663 215176681
    0xf03120501080f0c0607050a0209010306050a050c070503070b1008160f050109030302190f08070b040b090744060a0e0109030e01050d111b0f0109030c0209072106060e010206 76
    0x10fa00099170000d842d0b40c035900b040c91500f85018400317508012088004404d000040d08000c2c41501d07801018040c50311011038400103032080c0c0d1009081da8105221039000201004116a005a01441300084941c0c5420a013424441803800c109101c50504108201c0c051100320007600410b001d01700303030b4426417454401075154000311001e84e8085c03191680c050100015422a58091034025403900d403a2100380c903240300a08001d4505403091582c00b00058007102d0006040000d8403040c000310001c1c0000140d14007014103510b210041802c03521318403054481012481c800c010749072040100703058100303a0318460841e0702940040c00d031a410200c081c80820b4000185001c8003a003844c1031540c0b40d02c0701401c500240304510035451401d400068460b00559034100c120600026182640c8240e040b004140d8200e40a5210043c081803951014201600e4151070b030315030205a5082000d0b259071264010380344e01d000e2041c400000b0380d0700e60301840345541c02120080031480030300041840742469605 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 215179163 1250 215177913 215177923
    0x15090105090c1c0e0d050d0f05010317180909070501110f12070807020d120e0303130608100905042f030a02060f070b011706070503040308061c0f03120501080f 70
    0x180c41c120100700040c0c3c1074140d100c3c1d400051120f10384801d0b0f0f460515202c8004103581d000c1e0b40071600b041d06111143d40c2c00401c1c0e108580c12207a02000140082c1038001008005420010a1140149000752a40c8054803006015032142c80c0b80780280490070305020024121040c0d140080443c1d500c2a0050b210f42e0000003098a0100d422902e515160012440d101c40c103440b41c480002d400007a230750300450800c60319500049410384c503900c0d11b510b440700f01000d00d580c0c3c3c050103058a4400269180070828503000d90300c091b0708041f8001c8200b000b26100c0003400c040e41d405980032516000345010707080f41784d01002c02000559a60261004100d1581400a60f8400801d00f020380300d44000141000d030584c10604903596283c1c4030f0749109683d86d40d041100320460b0b040341c00c945140103410014544a208001712441250702d9254400300b5210041032100105513001c60603c0c501c6000144000300d0700c80c4400380700c500c1c030a66619071600e00140c01c150640303206a010003410b60010210302054880410 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 215180413 1250 215179163 215179177
    0x51203091005061201090317070c08120402040207050d020705090a0e060f060a0f0e09010c0c020109090b0f04090807050f010b010f03110d150936031715090105090c 72
    0x3040640314140090000116545212569072910495004168025402301c07403064200070a903c1d10380e0748c03410903699000c10b500028078a00c81044213080f040d260a1f4036035002030024000505001d0b15541e00f03803400c4002250fa80250348816010440740c9000d850056000c00080401d1101c0c002c448026030351150301820358140c640d91180011090340b80c81c0c90000042020110a400050303941c14030380d0118034261101c000f19400c041a010349140600c0b801c0e0980c580c1a51440360852601001c2e078001c0118003421540200803640b40341d06a0b40fa409103480850243d4139150ba60155032522030714091102c0c0300000c0590402c000024036a802c0000000444183d0a0100d000c40c1c0360041d0050a20803072200f07960980c6810301c0d6640c1000448030314410340d9051501000032200e10080c580c503040c00035440c941303100100306071500305003140344880369003c0c440e080c0709094062040d031002c5001c0d0102c0383c248230320113812040300c8589007094007180107001c00d42e908009400c01d1282c0c3e40061003002 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 215181663 1250 215180413 215180443
    0x10c080f0307030e160e0109050c030606160b0109020904140f01050f120706020703020a060201020f0406051809010311040c030203010b03040b1b0301120314030601020a03030c0c020a1205120309 85
    0x400003580c480d000b44c105101e6090b02c03d064604007828000c040301c801e00c0c4c600904016002840c0045100100780c41102d0245000310b40c01810365449104200c826407201e03480003115039039011080c0004000c0c0203124080d1034101e40150700c5004890900007101c0282d15485504c400e10024000c0c0d41071591000342c1520001c0d140540100000d40108556080e15281d0713064a1092850010b51580e0200d106802d4070f108803018000b040e40d9200c228241d0150b43d0800745800e00400c01008090f004030300800381e0f5241c4182c17020700390100800180040502740c0c400d5a5000e02440c1042c000d03c0c05101e10403444a01d070408500755414001c113420b80d804020300003015080e00d08082501080e0209401508103800c05007982c0d81d607111120074915204e40300c4210b0104024200e03040382c114441060705c0c8603242c1a402001030f061140c03800c81c0900a00c2c0110020f002c000e8442c2c1001d03855150044000e001c05089505410309149011031405034130781c001c060924014001e1003c4403801141d9440d08070250 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 215182913 1250 215181663 215181667
    0x7260601050a031d030901141e0306130e010b0f03030a05090402090303190336030311090a0f03052401030b0a02120f04020a06080105010c08030a0b0d0b0411010c080f 73
    0x4140c00da0040c10304a13007240f00903c2d40b88a0303801c050400002000310b1035007a6a6441c0340c40307280c203d00340300e4000c00c08880070404100c0004050790b0b00110145070300110007000c000f28203107000500b100b100c40100300700c03a69075111002e0801d9414400358052070b51806800440c5080301c072900082c50380c0100080c6a22031078001511148a590801c00c0d503c1012030759041c10340b142d00c1214080d0003021a0740403c65028001d8941c041c207007915a03031015110091003030000580d0a02ea9084005082800c0c40c0c3c1c16114041c070048000391503446646011b050206990421241581002850007250314030314140e9020000122140c10815007021f411240d0020038030a00d82c54030194000a4081e0350310141501c07c07450f00308011101210b003500c0c0190b000343c50440566880c2c02c000c45004d20b09004040c00719a00c0007602002400301e00007564001c0c0810400140d500007100004d250400200068400900700030520052020300701d030170710041c242420715406482c83c0340d84800107801100c3d00031489100c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 215184163 1250 215182913 215182927
    0x504060e210d05030f0109020405010c06090606170718050129070b0a0204030204050603061b070f051617030306010c0809030309150315030105100311130c080726060105 74
    0xa00c03100032519082801c2030b140000c00407800100b20f6002120158040041c0e07000000c0d00c3c0907148212000d407641a5108a0070945680703401008c0c02e08480c00304c588030b40d5040001003032400e15440c003507114403000240008a2410850041c000002c40203081154603080040000d61112860117a0700481c00d0300d118a6459801c41c0e5145c507010724074002d00300c242484108640901182d000f407055034800c031030030030503900c81d2401d00d552000220f80c081d041512000c410302c103114628000c3c22213240310780c10403881c4d01a240d81d581e00748140385640c1240315100314014010b068801200c8580c44210390011411803500e0b00009064014104015007249400103070103240707440c14000c039803518001402c0400206a99681251345601c202d0350201c2c4147c0c25000c81c15245010f000e100d001e01403c02801c000903046841c1c04140002c09210940c1c000d9240310000051010307400f070740e49c00b5841500c50324000c0c42e1030308001c2c18654071403e802410715600d0f101440702141410740a034010000f80b03040e9071164a = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 215185413 1250 215184163 215184199
    0x41209030b07030b0a090c021f02070203010f020c0118030f051b010207142802040b010302070f03030906180302150a0f090b0a15081027210504060e 65
    0x891034001400041d01c52041082064040d000905842c505907042c0b000d4582e5600c1d00800c9400c5211010016041034003000b074488a1902c40c0603109a40e2000140342030103e900086c21111103000400b03801d42c001c1208680043d0078800d142c0a040010410701d81607a03075580040c001000c3d14008000d000c03010070954402024818204480c030402802190340e03854174180151040ca61046100051190100325000d0400018803007104035004040c071150101290f0170040900303003080f040c9040560034401c64001c2214040101c0c00c40d8001d84002130480b92908041080d925200741004244884000c01c40000e5030010305030415082c80e00022600d52600c0d801800581484000840028100307140a001c1c00340b18203059002e080070006c10010035419a01703001d54008503104014454001070080080758440344c110103000c3c458030b0384910f048800d55802c01c0403031054100c00d94092810100e00d40322101c1c41d10b00c50321299243d040090900b0300d0000010520030075000050f0040d00e0003400503000340 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 215186663 1250 215185413 215185427
    0x51c05040504060e0a05010f180207060908041d010e0411042a09080c030105090c01140d050c030a05070e0321091e100c020f060901110f010c0f170412 66
    0x20074000c20910180d035403400341030000c21041d110503020f51301e007100000b80c80c04072903640c0c022912280060b00200385552401c20007034210020a440503601e541511001851820041015241e10900c900030004880038010f17060205803c0b000c3ca10402005000208104101a61150384d048070040b40c0000c0b0249000340c5119080c00121210f40401542010903402040c4942a03550b031808540700d84210070105803d0703400540310605940c200240c0001c081d403003000050347d550044020b541c50500011868822140200c9110b20342e42e4002c800d000c07510310b00c0d005080d000a040c6c40c0c41001405030000098887e15040202462100c014101580701c1d02c001065401c01d030402440301d85071519403020303445055408028180b2683c942c0b070341c0d05088e601810206401540252661a07030b00d041c0d900740720742a4000c0700c005050042170030074448460000c01003800084010300010500ba100c00f04003030312441140500800340510002d40010391007854002c10352054000c0c1020300419403161041d104a = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 215187913 1250 215186663 215186669
    0x4050a0207022224171606181401170709030204020c240f07140405120106081b0618010c0c03060c080106080c0a0e060d0f0906060b0403051c0504 64
    0x80c3c010b04401e094250b1040401034165120700040c05081c41010040340441640c566164103050800418030032100004281503010b502581140c000b80b200314038020b040106544900c0004091100d18114030181061840042aa44202c85c042502480001c0d00c114140d6000c48008140e103000141a144034145000040d074020b07000310f5441900c07007c400e40320b4100000500b900c0242003182240b40a6540149202d80c02d106c0d5080103945442400b1199074080c0305040d00b0080c0148008546035403041c4c00d180c070340f191240c00014028904201036007001007a0b83e0a0207502d1210030362040c151070f424210b079208810340e01c440324092900380059604070060700b00601100f907080c0c804802c20006a001100aa02540b1740441a03a1398101c101c6811204035498040340ca024084d4030000d6014000d5400364541c001e00841c240100410300d0320441d401c440e6980d9015071602844011301c10584030321b034054505040f204d4901400c58070f03116510b9503019075a00c0401000c103000c03a00d580c811000d80d005 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 215189163 1250 215187913 215187919
    0xd1704261b240304020f030706050a0f1e0309060b060c0d11101407030615051b0f030f09211f0609090606050f010c02010818030c030a0207180b060904050a020702 71
    0x600c40c81c40c0e03503102e0f801c01c0350304a000e40c8500062110030701e40020320714100c81140d607945143c0001d07444100d0b19050171080c1c0c03105000c154001c4140152401d03401400c0000e080d0b5000803617680504010081c0c901204405000daa07080012031030720140480e0000b0020010300700f0408030095480601d1420036111001c01c0041e20307020a207050f030b00540044c140500d0b406e507010b1084545850507404451000c0c801030380810420032415020303180100040702142c0d00c000c103403041c1c408800d051074216404aa81c0b56a0f010002460300903e103009450007401440010b200c080011541c01040c0c1c1d9180b241040c5064480950075284034089a03410100152900b06401e010f07801003890450060400340c080c80784a0010f2200301e290701d500c03a1410f82082601652580c2660b00c44001c00c1281070840064071000740001c10060550400030002000007581c6a40202400c03890142c0e401c07800d003008110a41c100f81004051186039446005640815800305c0c0d0000725622051a440001c0c4074203030b00250 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 215190413 1250 215189163 215189209
    0x408010906020a0207140d02041d010f1d0c1003180f030302070303230604021b19111806150403060507020a061a01140304020d1704261b 60
    0x20030442142c01401100e06103800321031000392110392509103610440145500500c845240070054a4550403a500c0307070440c0e5a044001c1482c0601e40d034251a00d820707658030810307201c10389205510004e11540e10070f48510009800d042d4000c2000400380818010003004042e1161603004117140c048440c15001c0b940400c0e070102e0442c0c28607010300030f50404c041c1a404203180081102c107822400034180020440d0310341a001d10390314001000000c2d0890a00d10b03158101c04414203098500130401e0f843c501c41c248510000c40310f01ca00e020600340328012210fa00035212442680d0300c51741c464a00c0380d0442e804880e0032205002501d5122564000c683c0080d040c5800c14041c01100d40d00411100700e101d00521080c004080340240b0700071442c0e001d00b01d0600090050044046540300b901c00b0b103402074070050135071400302a41e8030340d810701540403140d0110044000404000c00250f12003014008444050050655080b4100c483e440d0010045607200fa00200d0540915640d90303403104042602074028a10 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 215191663 1250 215190413 215190431
    0xb0a1514070516120303050112080a0305041502070507031104020702130b031203010914070e0303040501030b04021902030307020d0c0b01060503060a0e0a2c032710080f1b0d0c0203040801 82
    0x12550001310070b050300440d02c0c0c04008524a40200746000000d80c0110030f252800c000403100f10001c007c010410384aa4000d146810071505041c0020507101c0d02401c0103100c460f08600f80710406041d0013250398401c8d48100174420060f1102082024a041c0d11440050340044503c0840e00700840071503103000ea40800000415500300b40d901c407004142c210107041445030f544203001c7d00e1100c07a01d83c0042d410b17403050100300081e602c00c4c9c0008440d500084c1016041900c81d40d41840501400a0940c001d80c1010007000031055040110f150903410510f00022054813640302da0b031180310180600d40821000200142c1551161017040c00180340004050400d4070f0408500c0c0000d06a030030240612038910209410f03040310840015800d801c41901841c0343c80303c0780c1512a0604135000300000c101401e103000c90038030365400e01c252019440580f80c0c1c2c1c41a00c2e150026900004000340442104892501003c8000c01d103107042d100303510304200c1c0014080401c900d0503440d5025950100980f50b00b818030701 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 215192913 1250 215191663 215191679
    0x80c0c060a0f0206070e0a090b0a090c0f08100e0105060702030f0f07050a051f0c15051911070f1434060207080604060f021c0b0a1514070516 62
    0xb07200354071680c03c0d242140c803104011643d5000040c0b030294040c92041003801080d110b54400304400400070f0400c045155104a200f064032081034140c004205080320845240e9000031417203905c00300014440014a0410204d81c4c02880f041c001d45000c0c1e00081140000c54600708030032a840010341c804c88000300001d21045503520300c06d014450044180410010703003424245c008042c50b5401030211a03114440000440e1000b044020698051f503100161000152452090f039005d002d00c0d841c60361b0b0141d40d52562005854030300c0c01c60a0150b804210030408106811080d040301c0e41c0c08510100841c0344481198608000ea0540340d03000600c0805452075501250340c170900e52030805d903640202d25518103003a80c450041d4400e0000301d070050000200040c5182c0d20004800f002c5000040c240340250050b60010442240c04000440d69159003001500e49403032254014000c00c846900040d044c3c1d14001c0c80c08409541d840f013001c80101d030240c100302052001c50021402d400d0000e100940d00c2d111 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 215194163 1250 215192913 215192927
    0xb1003020a060314062404150806010e060901080c1903020c06090601080d050703030212180106090b010f0318170304030f0f0c0b10081209130207030c080c0c060a 71
    0x100c1c0325904506000072114001d00900300914800028081d03160340c0c1600b444545050b0040450000200b810843d04418400713000d400a0810851942030f039401800018084250140040b410700041500342d010a56942c000c07614031402c00e1031b1400701340d01c984200001e207014000f02c01582030f11b03a2003d118825495800781118401c0401194030503218000c10320f44408080c0100c0381c0c990802405861a180150014000c2921a180051400041c40301c40c11a4500558030900541610821806001c409028542c0038111851041025001c000b0003c2e20700340c01010381d08181612640e00e01d10507034407803030540e0301d06030010b800e0000b40300103060040c1e8543c021242200464040c07044034182d0340c1724a80d1841c1e20042d0341c41d20141c841860b01c80e070a2110700240b0002c60031108850200310780900f484082c056108506155031140c0c4148208a0200c40101015442620520407034000c66800f03110389006c142c2104101e652485480a21401c012880c42c88940141d00007412000c0c1d2544084 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 215195413 1250 215194163 215194169
    0x82a030a0e0604030c0501140f1801081b1e040519030b010b030603060601050d0e0106080715031401120203070305011a0901050105072004060533030108070b070602070b10 75
    0x1d110000c1405180c00c000703040c090340c003000e003001d40800810f01c040d5003d00008601102482030301820f020300306201c03441c1c80e0310503850013052004012a01e051960411589500940307501040c51a81c9450300b40a82c2c903010b241c880b010b4184042c5c4001800b0090f0104a401a00c009811446810503585200340f00c0003051008403070803072018000207079085a03142a80c1c0911001809001c1c0c80c0c60300342c01143d40b50041c250408440e503540442c5a034030b9800740300d8078000b054510050030850b4070300104900d2042e40400d4100c00d0600300640a113110002c6000681551005410f03001c007050300c0d001107803906160380c0005000b0744c6854002c0c540c0300c110f90035212007040b044900c502c0c3c5a8031000115038074041e6039802001c203241c1c0100c610418058611440301300002500c00110103580d4400030300317101540200d81d42801c8560100344003001401c3c0314881038a41606580340f465151100c40e81d600c3d4244c2c881c085d400702012410b6010461503404403003010b07801480035091400e103010341c00b400140c0c40c4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 215196663 1250 215195413 215195417
    0x209011d060d0b01290a0903050c01030606080f1e07020102090307050f01200f03070305090405011203140309030d0908190912020f040e061306050f06060304082a030a 73
    0xc0001440ca140c14002c540e0010762001003201940d01c3c0401c42c0310710044510b90400d9071002005445110181074010344188191542d43d01005441c500b4010b01f410b500c210303403904241c1041c90504c0816000410a17810031221030460341c1560f02d240c00d64296403841030910001c401403409210046078150050401c1c0041141a07581c220755900c10450040c16681683c0c0c00305407003010040e540c07400d0a4825410420791400d5403904003d1110080c1564005030703041700810400f08103080d45041502c9040d01500c0c05080d01c0307001c40b0b003944002d40341514440f60032101034400400244580414000d68848410094061058031100e10b4a46429040710204c0c240341140d01c2c10ba84403840c07041114108864030180040c095024540901810707041d1044601d0300280c030307041c0c60140b08104001b0944070314520130501e01395042c00d1510100792400903000c00b8102d0100e800b400303483d0b6110002c4940047c0d100310700541e00d001400540d85a480030507440310300483c4e01d85454525080200c010041c108050b = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 215197913 1250 215196663 215196719
    0x4060b120a0c06031b0302070c030516030b01080303041a040303240504140105010f050706140f09070b07241407210204032006130305070302010e040504030e090c07020901 75
    0x102000c074205d4013006507080c0111050050310350340ca0b001e98010444d0b64021140f100a142c1c698498510b4111580060720b1540f0a55000700284002481e07900e002d800c0b036501451850800d9190300c010003000319514503c403100e183c003040400d8001c2d880304100030040b0881d41400c0c04821200c128200080c0b081d18012424039042d45170099280c41c00364160b50303058681c20040aa0340340202e421f6046410200c803104da40d500508070603400290505c0c41140500107042492400c181101e041003515400480c0b0644c040c0300c00800503100b41105840b00030301c405081c00318030214140c2000351034500303102c022404000382448941c59106500c159136400d648280581d0302001e02c00d0004078461440007601d000a80400e041581c2c0c1888009940028000c00d160300b042d6002c8185601c00c801ca034021111544044420811960401d44c010a6484220703801c01692426480c09000b6491900f031030b41c49144064000b42d901a0404103583d03842c1d070080c00c80829907071a01540c03a0420480c00b120300620000c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 215199163 1250 215197913 215197919
    0x90e03091302031e07110708030301060318121803020d11030d02070305060c1305150d05060d0f02040c03020c0d0908060603030a0909051009020a0c020a0b130e04060b120a0c 76
    0x5035000b124004e01020125500141c91031050114608014080e0310410070403000007441100c1c204980809018890082c6039030354035002c0041c2c00c9031500f10915044d0880c040d04800441c00f030342d150680c036000d40e003001400303101c010b0b46c0301c0800c00c00c0d0340009600c85800c1008101780100116400901401682103030085031807110203a0b95203599100043c56503100d000011748242d8503601038a200400362407140d0b9100d444030005418800c00c030007002800348000c21300c410300103114000c864010100340c03100900c0c40701c079403102d0111b4000140042d015940710041000490300c641d0441d558600c0100a58a1000f02d15000504c071651500c142006407103800c0c049500d619002c406c43c0d403141c580e80c55411005140c100304102410700101002c00b41c00d010341000429000f81d000819101c00f00c2c0ea119511518180f0400220880940250300404024084ca0f400d001c03804c83c0d0350040d43c860705110062940d640c42d0000c0500304144001d600615140014087ca00c400141045c0b00e502c20030021402c10b032 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 215200413 1250 215199163 215199199
    0x14061005040513030e1c14011103060d0609150c0c0c1401020c090703090c0b03090d0f022a150301180b1c15060305060603241f090e0309 60
    0x280c140c503000329040707503549000d00090195035440d41c43d42000c2e00c00400b031814000800c4680d8000c030026126454240102d040c187e10070f106841c02029265002401d50600074080f4001107040400184015540c0001e801031140c4008048040c0c3e191440600405402e250f00510a801c9036004840c1707160b02c240041180d1029141c0701000c0034040c0d00400a107d25a405c00c03c0007140580704806240d581e89045010801c21a0610041d1401542c05075880c04c100550131b203048024000c1a0822041810b0310030142ea0225090001120018034020301c9111010030800002042d5002c036801501d127245c2d041080411000345041311340850060074403818130380100041d550447d0310a0b0380001170361410324145e011500c05020309405030f9036003403070440321040d040d04031340950b08140e955600890402a651030104000b0021100050070021544480d00d01c1005020004c0c1c0060200140112894000240ca209220050030010310522060110400b403540341d41c0240402c074080c207458908180307400 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 215201663 1250 215200413 215200421
    0xa060305010e040b040f060606020307230d081b0c100c0c030516110603150406050d0c0b030a020f040909030314091c351e070311071406100504 63
    0x440700c007602c2c2d809598a03039070195850300062048405100b581800400714109100c2c08019002d190000e5039204050704021a011f02c1d40100359002d14050352103c2c41d9060041a080710044940c1000081c41e101c8218140e0704142a00102c44424800b1031010340700f4800241da183c030a50500002c00900101e6101150a43c01c81c00010300403840400190600c00f00752600c03807039024080c0c0c00314824194403400207035551b80f040c3c414810041c44600c4010040c60b091042c0001001c04803070b5070701401c000c0c0e50b6804803500c0a10440d40444c0000c0005554608140c044503c0c504010b000555110748030083c8100070001e032001580042c0c07820200c965401d40e0107a00701d0184020000030402115401000c090003004400712500b04030040d124190314103030460904080c10b00c42e101d0301300c01d4400100c0d00c1e03819540050100104400081c1c8040c1106070b500704464024256183c04502180e40c150200411303c104580100810248011107056283c00f0841e41e0150940801d42c4d40c900d507480040200390303 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 215202913 1250 215201663 215201669
    0xd290f0411010903020603040605040203100e191a01170f070501090504020703020a0212210a08180c030a080a0806030f031602010c060c05040303110d091203020f0d09050a06030501 79
    0xa11698408140422a0414411a81081490105400d80d1a80d002c900990401e0343c0880d48940c07200c040c00708525041c8040402000104c00c00c012411003210415a10000118041106410510f000051118501c41d0f1b08040031204060189569104000391148111a203500c110b400f0f042d01010403503c000c01d0311400c07101c05a403410161420141000000e50003040c08805601c1500480710040e180c000b4030400824440c4090103a49803101300040c42074041c0c50380030201d07440401081200a410020b00c2c0c1e0030146001328104490242030304107250100c1130044607898803441512100f04800c400003802403400607650b1443c1503c400303085c169900c4408102e125076404c140f021104e4201001090711000d80149030605d41d41d109500c800741265404695180010b60000d82402070603008500b88038400079240041041e85c40d03c00004207181058052141d0300c0d4000220340303060601c00c10034100c009000509444001b103c0000c05440b400341441040c0c0500c415210004485020f40b04060403 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 215204163 1250 215202913 215202931
    0x18060c11090c0903160e040201030f021303150b01020303130b070c0f05030a1d01230409020412030e1203041a0c0f0105010807050301060e060d020a120503071109070c02010806010302090d29 83
    0x15202d6074012b5003d0441428410030480e400d1240300442c100b5000e14600460068090114124064808405851201941506550080092101208580410242094000c40303101703005e4680f905c044035000c649000141124420400d800c043c404044020070540006884010440c0901c8490304140c09002c0d5840d4042050140d80b114480040c2d400740d0081c10090340000d01d01525203c0c80700c02c80c0c000360098a180043c0120301010581c000d010031601180460302c0b450849040101155a44154000c02c0050503a4126146100c07800b1070660300111480707410f98185d000051013503402450244100c031024410b24000040d40e0030188141000e40b4444040c028444e070b43d034411700045940c0703200308030b0700168001c00000d1010080080034070501d103e21702440d40d032000d9003070041003501d414010a100c0e052403011300410941100d140000c0941c2800c3c40c01442e5104001a00280140b044540d00850300c400f4103020051641c3c86030500101c006400441d841d10f030304041c80041021903102c12 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 215205413 1250 215204163 215204189
    0x16080606090d0611070501060e07050720030102040b04030f0c090e07030b060607140607021015050d06060b03070c051b0a06050c0f0102040b04140118060c11090c090316 74
    0x140600b0300586201c0381e5030003007802107041001034404103090390242600b138400e44d64542d014840e100a442d0042d07004040c600e007003030800d102521100150f1446a0345c09030044200d000040b9103450a4064400500c0c2c0000d4043c0c40d1982e130300700404543c40480080312005003180c004100342001c2c0c0300d0340c0411a80f003001420b03204d04554410780c00181c050442039004000703200d0303400000e4000d08120384103040c8030094400e50400d110b02910702030055100410090403d000000308000f001902c500715641217171303a01c800402c04e0801400800440d00f006400d00800030400140325080001900312503c52230443c0c034403604e002c22584c403c519000106070310903611001003101d00c0c03068001c4e01e510748000c1c0a4403040c80b4403010060890307220f58080031180c40c003c0303000c11902000030650241c40c9400c1c20304440307600750200c5251111480b401014184094600302c0f03401d00071080440c22248c080a0301101803802e0500121549070041d9494034480e104003a03032840080a00002c400c04c80716030b421400 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 215206663 1250 215205413 215205427
    0x90c0806130804260f0c0907020d0815010e041406100903050601090b060d0207230307050601210209010330020a1e021c060c0914040b01050708040e16080606 69
    0x24040d604104d0414640c803c20244408040300180102c410a003181070040039420a8141070101c004402003c0e0340545d003040520021541d0010103080d40f0078030003814851911003190060324010030102c9000d42040c5070204004040b01c050300100c0c090181140c00c40e40401c1c40c0f004c11504048103001c01070498012000402c09201e05401040e104c4000604060500c426846118100d8007c5030303083d9403210b02c9003040300f0180d01080c00c40d4060700343c80c40550702c0d00040e5101d480d41d4410611810f84500c4110070751520880001c0303500b44105500400c0c0c0302413540c0d2410001e2070b040c41e5010419845c8910141d0640007041c040d4035000f449500d4028084114007070301e80d150704100042a880c0501c0061071003000681d0f51022900c80810004074030b081030f41c032a05204046801042e09541480f500c1d60050100d00c3c41e00e07441880001e8120307808249082e869004a400740203844004000c100c0c0800d02042002100c4d6145100712140c00502d5641d04582d0400c45012606541042d00100c0c10007081c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 215207913 1250 215206663 215206679
    0x1209023007140d0b06150f0306090618160e0a06050d0506030307030c0803100306090609060b0306010602070b0d060b03090a060c0302090f0105031008030a05091801030b2701090c0806130804 83
    0x1445c1d20100003031503252404100044041194050390011241c03810000810110f442c1c0200941c0d040001074a202c40004038020340003207102c0016006090440e9901d461014161065549500010014015110540d5544009046900700311a554025400e00c40040e4083c14004161035809800d9521008100f0300794845002d00d41c005011028030503222000440440c0701d601170310f0344182c822600007031154900d007010821124001081480380d001440100401d9034001182404d0741c021490b6191354158480c0e050b0001c02455000c075205d107002200308510142e02140c410350040c0168014049070503a01011003c80c0310316000b40e580b046500d800d0035141d501c0784020316400003c28a4602245031114030041c69030b04064194000039000050b20899800d100d25106081c84081003517600325415640c80454030b1400420080180d01d80c0348041d100c038092080c080300e4600d018002000044014100f0855281c0c1c1406100114860f00001c190f080a12141d1095015004102c8600341420f00c41c00b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 215209163 1250 215207913 215207933
    0x1103070906051602061606150302030304060f02240105010807030603080318160308041a090a0306020a0215090604061109220b0301020d02070b01060c031209023007140d 74
    0x108060004000e0307007180050300c0da903000784204c00c55501b103419603800e1071030440c0c03e46002d03e00b401e21911030007104000584001042c0c03800e8403420700b00040100840c50007207140c00c0d026160084880302045078007111149420b920b60680f0400c7c0e0f03d0380c0082d41e171000d00f80c040d40e419210080a0410810001d003820b1408464286040301d0b0809442c007d18030480f0080d045642a0010f4901800000702001140d410400c00300110f00030001c45410304210740001000c400c40c0344009042d40342c001802c1801a4800d0181000c85200511341030b841d4203108006503603401040380c04407600b510f0840c080b00b44c206039506030341c0707140c07401080680c0702d0010325540201405030074a40d500d807548448400c5425a000c0c0007a00d04541030041c0180c07182d1040c1004c8802041c10792044003444544e84550f00482d9002106003200100b5203401304000a60f44045200c031002010056005a1820302e045100c54124a51aa813a0f4215046420981d1202480100c1d050b4404419500c0300603003c0d100002004451 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 215210413 1250 215209163 215209177
    0x4050907050c06072106030f0b06120f150c03090d0c0201180816050d170f090a09090204060e0907060c080d020408030c07060c0803061306030212030706110307090605 73
    0x9001c0e4100180741110924000e000d07181301011500d2582c804103802041802c510110744030300414800300349141c88880d200440018017030413030b0003c200010b2480e140c0520310607149248104403600340318030503403050300e5651000d000424003410b400424080620700d0142c901850340e500280400181c032007002e403010880604120706200e0300c841c0c0d4030351015152102c81d000700402006400c030bc0d000020318800028054015a2290303a156030004081400341000c01c0e0060304070904d440d501d60b60540c1c5d5070018018140c0071a800b88040c140840c2510b840d0300407001c0c481c820f0342c050000580f1040040850101124112666031010038100052442102c4c0b10440c1402042083e10306051081070700140c0c1e201350080c0c003031784d40002a81880c0030750822414006024a04c0c3c00f200f04070050346e80710010b11018081d503124101c1410308010801903940440002c540c010090f51202500384090b988940120700c0c190303401f510304801510761a1059007283d00c80e00352640c07075031407903800c0c45019200c907040a5 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 215211663 1250 215210413 215210417
    0x204031a07210b010e0306010f060c03020f0604060b01030f0b010509010f0e180f0a05070e040b120d1101180b0f040f08210606091807030f06120b01060f0504050907 72
    0x1c81c0154042d5090075411000c1410b1402041202d1100005400b6050629884d406540804010400300b07040b9080c0320f058551310f02e4020340008690604902d00750044002c00807901401c000e001c1000610303403141e0360707400003a281403154101e48150103040b5888480c0b9103021907420032a19210790702c100400b030710081c3c050800e18201c0070746801141031180780c10a599403403d80030050029a69080803181c2d40303d000301c0c10500c0f035441c104100500390302071f404005010b65141c010010080c1d442e0305030424040c0c040e804441d06400c4c1c203000100340007003070001003d895107000f511075084092080070340c0c0425004243d0407000c4c0c5035030555150080c00100269a01c81c6500b6246000800c940c0042c4101c03140008007042c1542c508031200380e030010140103184550010080140d96840742d140300c00060440d24050002da80ea000c005801900d460002603a0186c41d2200218011aa00118480040c090103030b0542580e240c400c1601d50800085401d0082502030004000500e000201700c1c3e030042c4c1038 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 215212913 1250 215211663 215211677
    0xa0e150408030c0c041b020a1707050d02061824090703200109090b030d1d030102161101030b0904110307030f0b0601030b0105030c120c090613060e01030204031a07 72
    0x30469241141c00a510f800c825400c01c080c8032102c3d140c54040d000302c2c00110b150102c55603c03074000c003035519141102c000b4413403204160448405110034081d5400e640e0804161102010f410000a4583d44220b03140011108440f00050301e15a00051903030360050540ca9018511400c49512070092900410201d081e203d98800400003480e81c218950601003d4030004101403405e0002400440a0b0f4100b0012245025104203850f40c00003088420f1981505061a5131100c0d00c44121140d441110070300c1e0150300018159400306038a0544d089014020010900350700c0d1100011000d9420042e0503940c0151903c0204000c200c1c851814058540005c04480000e5034030b0352510034402c1501d90070f030b659090303142c1042401c1d600342c014071003584824640320b480e5152118a550b5a405441907050018681303200080b0004005011180c0110780101621740342d01c5420224401e04045000c0c07800007030708510640f00c207540240241c1e015254000c0781c0c0500407000e81c00c032000303001c0d00a102000304042 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 215214163 1250 215212913 215212919
    0xe0a0308040303052502011d0409060c0e04111204021002071a0415020606030d1b0212060405100b0607020409062306010e0d0c0e04081306120e01020a0e1504 69
    0x9031802407000318032903111241c880d107200c0044100d0b4060740402076800091031090100607030388031145290501c96080b00810303115000300828010300103290b006180510740840012000d0300641c2404c0f811508440600c104456504200b80c14000c010f2000e112280d001c000c00c00520b091240449070300414812600c4d1140d49515410140c0724036206000410720008040c820760a40c1e41800309804480e00041a0341e040543c0440e03500c900c2c0c43c42413001c0040250000e103a0512004011090a070020100124520200091600c501d41a075003101d142c070640f030702d03070130001c080c0c0c02103c00e0144000c05603801c104690f020301003e4807584070100d58040d0758000300490034003401c000203500709080300640c01a141000001d0305241c0d03403108252066141000440000d5014155001610920100c1038455180d80c9400c2216003c1c104d070403410600d030f500004c22483d60020500002030704d14507042c400092010b14070340c00c074820340c000c000000d040301007074041c40e003460107100c1e8109904503507062820307075 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 215215413 1250 215214163 215214173
    0x30305161b030201171302120118120f080405070302060d0b040912090b040f0510110f0303090606060708030a27080c10020909070e0d080304030305101707060e0a03 72
    0x600341c1246103a00e00c0c01d00900c19943d0001034a2840301801c00c1000355070900032407048615950743c0000b4410b021120300251101029048441e591032031001c5507221814502d0402001c00c90052081c5c00107011800164007980314041e10f038080c0707803c0800f802103203081d6024084540c1c08244e080841c45e0310b1301c0200001d52981d22695021600400100340314145020f0001c01c2800f99a018280c076450901c424041d607401492900121101280ea40c214801002c0e420746501c900c1100219290040c00441c0380040f00c080019403141c100e100a4500399a2032001b00103241c0940c0102034605601070000a1444030254403208031031074a150040303400c4e004108409503015840004807800c00001c240c1a20007902088600f40f05000840c0a5040c048070700e010908842000744410100401c0b206004940d85890801d0b50300703980c200414a60342d00c1e0a0030081d0141500791120f50700c03040b0342800000c2028110540001882c501400750032120b01e0080f0445030840c002000983c00b4411240000c0000d1b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 215216663 1250 215215413 215215433
    0x70302070c0b0d050f0106020d0c0c0801060f0f0509010b0a2607030c030605040e0d12021210060f021f0c140711010206011401120c030b19170102070b0103030516 71
    0x3102e402960789440c40c6800d441614006000b0407800c1e80701d0401031045036000f2501d07008410305450305d180c2c5071500d800c1080602c411640400344951a046000c03409070742d0200d10005840d1001e41c400c3d101b5564405002046500348034920609206210f01c0c0c40292181c144402034201c10703a1245046120700d13a0070030501d542560001e01082d600c018150001d034050040200170402181d0401288030507810454075101c560b8014410003054210014800c99aa0b0540d010b500e101c84201280b803400c1701c60000703a4a070702e00520300891821035000e54007070300c00188041456224040e00d8410880e46106902600d440b20f10a810320041300c001543d81208240a0050240198a801d172041180c0d00064107055040c1c101448980840c111951039903046061099181000280081d08034002d403405c600404100080301d07400394080300030310b2840c0e0b1026071050507540e00d1000c8a40c80e04015510342e0803031258480080a8096280040000c43d01071009090b601040b011450785103207850740c94403001 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 215217913 1250 215216663 215216669
    0x1b0606060503160306030b2e0303020d081f2106020d090c061704030f030209040207061b05040f0509070c050a0605090601050405040302030d0b010905030a06090212060105100503070302070c 83
    0x410200030032400c0c03d80c074100d84107842e4160900300900d44c215181c42104550041114801051041544480c240580c00c0c2c443c4085404154801160301c03850002c0d01c40c82c10400610000758a03902060354640c03405d6060000c10030003404c0000c114a0000418140401d6811809107240011200ea01282c0580010160029282e10024001825107030040d000582e80e01304004016240c0ba0030000040d040b20703c140c1198050505c0f180305410f1100c03c0b80079102d00300c201604180041044e40401105400034403082c41d00404c08406010340c59030807150340c05107100c1d2a09281c120070302040f0310704008902c0e0703410071154078113207580c103550392203240c40c01c010f448048600655a00800501200911480d80900000c46061106090070340340203650707001b5101d403d858130399665041c01450380214a428010003000e802c0d24100440fa0508038002c1c50524000e034020038520840419920010034114143d034001000d0140303903211007108a4094000400d1202810b5080048202007545103510b40e0003 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 215219163 1250 215217913 215217917
    0x203310f050405161d1906170703050606040909052d0609150f150a061101050c040605030705070c03061404050f060106020c0f06070b070c14030301080a031b060606 72
    0x103480c40c0c0310901c4100c0f14000e0040310f0704c101c0400d9103020070b0343c480148903110040340e080307540c8221030400241d01c0c569440003215203100080300001c1c0c5c160b04101400260090407001c000580e543c2d1a050342595411640c242d8001c404000c02e00c0062041d502500c4d206000b0011211241c215000d28a2480000b15070116054003842c000d10010008224403540011040c01901580e01e94aa400008120152540001c0304003107002402c0c107050b81310009410030b401007250075260f50701c1d100075020700b86180c60f00d0219404c007000100d005003008215002c4411594890389540d462502c01c4400303400190003204c40032002071001010075040d014586a06149801c460002c4c03c042c84c0c00d500d044c0d508500c19140f50005401006200d4003c182455820030607221503504070b030b08500040c10ae102e0810001c01c040031100c14428070343d80c81480024100e20800d2511082441c1038611a560300003449120300300d0f03018180d10f100286c0f01300019860111103002e00a4184055907403203040e40d401e03400c1500 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 215220413 1250 215219163 215219189
    0x21605010b0a0807050a0b4608040812100305120d0515030c040b030307080d05070e0901140409020616030e01031802030a062703050702010915020331 66
    0xc41d41c030300b4841c102c0080c50750302c000f03184039442c100204003000d8092045032503c0740302050102400c0e09035602e80100320440c580d40d0000c1c05040c0e2605619600c021107505040c1004543c1d00503030707030048001d58029500700d142c1d80c3c100742400d80b40020400000788150a0f00f101c5020000000d14200141344001044440c4180c44a28234240d2204540c00100508614211104101404c0d1004103d4075030360074007a10003003000900d11020a00d5481071210060000d00002060f142d01c60655103e00c1c026001c0340da8103110300d2062010001143d8081c0a6030390781d10044502c042d0f076861305500a001c024405070107641081c45071034018000020410050f00407a2210015400c0c135a803620502c820360258414000ca0f09025401180e0380c3c041444008002c0c9507241000d10034800010300708140c040000000c48403520b902c2c41c0c0204541c111807022804600c00340b0303010480c54000700320390700301c4c00c030b550300950a02040c090400040c1e000308c491801c03800c0400301c50400350000c040092000e03028040c5444 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 215221663 1250 215220413 215220431
    0x1110030204060e04020702060d0e011d06041509020108070e1906030b010801080106080c090402300105100312050a0909020a021f090b060108190c0309060b01020a0b160302160501 78
    0x36080780090700090741319620400c41000107a0310082078500280341000000360042c180c1011600402d039210000701c84503208481d500a0900000300c00d8819071213080361882e00d5000c505040161140400000c1c04608080b000500940c419a901d000d82c003030081c42ca82d248000c07000c0c3e5052418080d0003000004c1d0712181205200d580001c0c0d03180c014404c0704000c001c020302d8084115103644205988a1054200102007819907940424954202c1c0c001c7c060408029403000d010011201a011240340039420940011001e54203101c480d030032641c008542414542035800125010b030b1082151a003170200184010826030001c1c0301800043c84aa001032410301d1b40c4070f48030040024040041d070302d0142028007641c009110f41e19507940022003800c05003031640f5000103095441d181a00c191829601d00210103003000c1d130507003003c9070550280c0406c10241e80c00400480c1c03561a80304000c1c182d9020040814981020080f10b80d000203514a00141455070000681107074400c4400c0030707030f25607444007020 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 215222913 1250 215221663 215221667
    0x3020a0f02072411030d0e07120804060f020102070501050a0c020f0304150305330a0b0309060c0d02160807020307080601060c0f0f082b06080613111003020406 70
    0x4212401403070008107000d42c40c001c1001d441d08421200fa01000c071004403001a0706005100000340c4003003a07404d0700c0c1c40d201d82103598030040404000700441403140d02e0b4005222004044990300c9103402241c40e03486e040c00d141040d00d100ca0710068800c2159420440c01c40410420f102d000d0041005020104803842c82d04e100070704d0480000081449031f04100420803803180c0c00219040052003500b80030a1940c4c4038411481c1160700600380402c4880120300c086002c0d14000d0240390250000c440741006561a03001d205070b5400100c2c3c04125580c48100030601c007082c9071024040e0300040445c090301c2d20342c0843c01420b039015101d0044a03000350103d0000111f1509001c61401b03006048001d00d01c56140400040c025111100702405002c4002c810303200f80200e140207242029040000644d03580301d000302c502e00502514402d150030010304e11003441c4680c0b143c0150340844078550003d04580d05c88100340d071080c42911004a50940414409000ca525495500300351302c045514010b07143c1e40b81c8040 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 215224163 1250 215222913 215222927
    0xe0405190c0f050909060a0e09030406030c0c050c0904060e0102040e01050906061e160b010b1b010509070b090f0418050f0d051c110d060302120114010b0a091503020a 73
    0x20000602122003610b03909540e100c1c00741d40030380d8001c5801d150b09869000100f0010042c5400c400032401007402000704005001000b07204980855031300f00020341e1707001021241194481001401d60300040b0150b0041d2624a01d641c1d003007400742c000001e00a022421071422070b40541c0c4148280e91041c4010450b40c502150701a50160040da080c1d45081e10307102c00c01c00100850031103802500004951151500303051000703498400e40c032038001865940c4070400c403401a0090140c0c0c900c60b50500888809000c01030040320f000b080410018030100c0d051000942a503013262446541007250400146403e9455002c0e41c1c40140550850610108403400c116007843e586228450035540007403149801154000101c0c0c0c44102034503a80c0500c80071209d40d480260510303444002c4240000b00703204151035020f610280071a0300c2110380c07007408214140d101d1300765850390701d0040b03901003003500410444c80c1107030003040d000a80740703052400ca035102c2c03ea114965255644400000754045071065400340c00c900307 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 215225413 1250 215224163 215224181
    0xf0905060c0721080f03090a020a030b220b070c02060702090705091309080702013c0210050112020609030312010f091805100b030703020a0e250c02100e040519 70
    0x14460740d201e425074441440c61712a5082c03d030300300700c0c0000000c0e184c00d030305001c03641c0d0701ea0703000304809171490313580c248640394060554100b02c0241500010617225900308005ca400c441c1d00254031031291b907800d141650000d140f000141e8005000b084084c00680c2d9140809200e90078030b80342c450303c0b10b01c80030a00c84410a44030b03003070310390b20b02d0030114001081401c01525090f950928001110994204403c049000c8540c0b0710a20007200711114a56500392010200c002200350f400c842c681030440c0350103c182d40080c440e80c81e0020f07171514508003604090005140b1000003508582c0380246030102d082032020241e20400048005180c14801550580104206018001c0f003c2c14000210707216551030f50b802584000c0203554920440071140c0701880500000d540080042406943d9441e603220200700849101c0524158140607031400044030518509950459480c00070283c45642070210301c208000104043c8801d4002245480e961030046501c141d40c421543c064800a00f0228025180150 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 215226663 1250 215225413 215225459
    0x105091c170f0a06051207050d0f020409050c1203090108010e061801060e130207081c0e010c032301060c031437080106120911030a0803040c0f050603070f0905060c07 73
    0x102c00e44034103000000e0740d141039070030450314071510902524ac08500000041d8000707411900301001c1e0414010041180d0300c00d44000e0b100d034801d140001640503100d11448805901140b5101d006000b41c5441c00e404c540d10032005069481384414000039405140d89c26032140002544944003c0e4142c10040d030b0752411049941d0055040a00540d10f499085c0690030124850901000c0b1280001e00203401001000102d00020804c2c42c02003440200502850301c0c420206038040010042c10071a402c010904031a0241e956944405441d54200c0303030300501141540070070b8420f0002c41010604078103e00f0308402802060000c041e04072070300382800301040c017940050200c02d40042003c90b4001440e5002c2c0e20039400c000802014500d01a00100000c1d4107003074061007203130010400c20220000440c0164003440310504415503407081030017018124050b080e0801401d00115140c0b90103520000e050030f900b818084803051300c82d0702191243d0082e0b620b00c00146d000c1c80b400c104119a900035052041505 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 215227913 1250 215226663 215226679
    0xf010f09050c0f0a03060f06020c040b030304060c17120c0a170105090c16050105040b0405100506060a050d1d070609090b031c0c08030c07140105091c170f0a0605 71
    0x10101c40e21450040c8282803803283e00000d5100c0c00350f84241d01c00f0000d01003910008107003a40721200252781c0c280a12016016038586200c0b02900d2600005840c1222420350b03c8604c0d407405035444802010f000c407044189541d00384240c402d00000d11265078856005585003a4840c5031008004042c0308400c444a86a4990f00740140b10a48030303080410707402901d071401c9076940c0201c00843c503600c800501014207294a0308041c081003185214020703000324010000c0f110704202c6904070700226a015500c0701d6102c8010082e1003442401a00a004001c8202d18000b41c1154008001305280c40c1103030242285800c800414081c01b5000342c0682c000e03240d0901700700300b5101c1a00109545414080c0101108034a0680806019105a00c000b4441d50700841c180e81303c0c103120500b1070041e000076004a0b181500500710348001441440b81070b2190405c08010b0180002d16000c1c1d0308848030082045003000030307035514100904003410006002e8502c2c030b094500c581c40c100f50301800315405500028400c9d018 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 215229163 1250 215227913 215227921
    0x603030302030a0f14010302010f02120d05040c05090712050612100b100201062105070519030b01050d0305030402121207080408150702100c0309060c020f010f060503071214060f010f0905 82
    0x2030201170f981500e5080c2401000d03500010800d03890304198460642c2624000591601d08030025006a03020f5841041500103454079101081102d00b401c0780d46900140c2d041c490501d03070f1203058106a41201020380111000640000c04504180f480c01040c00540c0c2c80d030301029031605103150603e04007081c0f440200801c5083c00707860b8a4a1001c95444801d040680c040401840303410702060b0001d00b030003003c6e9000518100c50340ea003100d441e40305c15290300c0446000000c00d810070080008410781c1c1942d40034955944c941c02c02801c070040102c0d1040e1403040c5000050f48521103001414214080c01107a0340704c40c5008042484c082249144820760803c600910000302d40009510000983c0d000c004641941000705c128020456403401030002c03414370b1030440c05190049010300140040000a000c0748100294030020745415120301c9400d503008400402030190805074030500c0303034403d1450b20782000b200c0600501d4980143d0b0403651454508004020b1588030720000c100908400105100603d0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 215230413 1250 215229163 215229191
    0x27010f14150c06040308040c0602030414011110111c11031303030908070605150906011407030c0206030a0b010f0e030703110f0a060e010e0a03020d02060a0c060603030302030a0f 78
    0x55018031280280c070115000008080c04900ba21031629100c1c0498015260a09001701403420030b0700c090721820101d54011035032510200494081c0e800d00c2c040c1c03840b0351039107500441d5400b24107000fa0f0442d000b0003006039502512030080100500700b04201301d4071100365580309001100d140125121107031420305032101031440802641d41c0028030040b40c0c1a864158203064003d0b10603000020b0a91000043d02c1d41003183d40d80c4402d01891030300c100c5404041d521000d010500005450741804030303804044070703510800c0400040030014400c4c507000480d5100f036030104032103030000d0ba8070101994581c99840615648060050310205e06450500841c1c203186010075201c05140c080038100d000808d03034942e40751f00c52140d00080004050901c0824507a6060000e0164501c035801c0c0307000406e0303424803038010b2a0003036681c001d507600100b804812a82e130368204819070703100c02c54160511036195541c901144061180300300550103918056076903e8039518100c110f414100b02d2509031868054000d01c255 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 215231663 1250 215230413 215230439
    0x13060503060f3003040f061e08040b181006120201030b100e0f010e03030a0807020c010e010819060506120103021912020108040201122409020f030a0f06030227010f 72
    0x41143c110452000f07111000341540704030f400c200283d8484a00008545602404108903114404001c582141c50200c00725884132064401414a081501c045010090620000d040c84c0c0d039640103c0c0c200c542d4800b80d44040d0384183e03001d0540690f0201c1103000b0f558060003100c03461030048960299880c036020b006040500ca00c00c80a0040c1e466600f2503841c0e0f4014854403480c4000201241e480350001940200003d10440e0300380c0050091aa40e10502d50013820b19484400d016142c10017a035940d0015403e80301d201c0c401451541c1e8444000080b00c0d00c807800104402525071040060b03943c194018481000c14500780b0060301880c4202c02c0101165249554513520390910f081a800c2c0c8a03400120b85100c10f03441c2800240d89070038911000600380585c4681c00600000423021400d544600000881c040c032248420f50180030000600103104580c45074070001c001c00400181c442e01d175008a8000241c420b50141c00403516510b240304151050741c0070b0f00408005201141842c00d041400c0c03400 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 215232913 1250 215231663 215231719
    0x130303030b010c0602180f03120f030402040908161103160302040b130f06050103111809041505040b240604050118080f07061b030219060213060503060f 67
    0x1598410788054182e100303c00031001c40d50089010f40d210344c0c10030700310528540260202c44c8101d9640071203603d81d040118092008840c0350f2203840c00c00c90681c10095455100501c101d074080d51310002d0000080b4580c003e8421700c0d900d40d1016001a503223242810345a000320b40d500d07119500030030708200c0d203110480e10101580d0781aa0003040820b500b40100303841c044488030622001e410a4945010743e0000d50007a81118800d90303041c8260100b030090300b2018401c030308240e40d00c0385640c9440a20340c100650341a8102340300e0f0701204916000d114910b005c0340d4098500302c176400818024130010b080000012600c0140440c2180c1c511a1035000044080c41180300361130504c1002c0f402403c4100020038076030002d20380c2c1410307a031070321114400550300e42c0c11a006a0020032034035003c0400d4440d00506100c40d403941a0010510011900c012410b6502054170440d0815002c000c1c00414422021440c00140481c0d1102c60302d0341444001c0148008200b2001f50040c8041d0490341006d40010850382c0380 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 215234163 1250 215232913 215232917
    0x91407030f0b0405070f09050402031311010c0503070b01050f0f0a03030813050313030210110604110d02030d0201090309090e0c1003060b0f070b01230907091203170705130303 77
    0x2000c8600010740900002d11106901615050400c1582da0300074154030b480700b040795502c440d003075181c3c02000128002600c40c200301004c4800b4900000307100c1e6140c640c41e960b05050a1041076003036980c451460b807080b41d0803541c1c0c4200c10010045824200e9101182101c22102d10822040307640204e14240f580d07210180403c036040c000f01e48030502040c54801e007180c21a082e240d445c43c0015101034159079078807040303005030003109403180c1c0e40d031040100c1c4840c010400702518481d180d42c0c580c07003002e0b031f0300c54070255004c0300d143c4a05005a40c100610100c08200381c00101c0c60000504000c1c0c0154002d52021200c40e00b468074401d405540030520f000e101100316481d232035951207a072048005101503001140a070000261a5400d4003800014000c1140320b20007034000ca81c0c844203444d03880042c0703400020160855840b4051239240003203800307600010314900f111255903541c0e1707410304138200401c0540220300c00319180e100d00002848801c1c4d1004003814081e2a11358201012034213007020f48400b0741 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 215235413 1250 215234163 215234171
    0xc0510050712110a03170c04180207060b04020c06060901140105160f02090403170a0603030912240608010b0a03020102070510111219140901030b03150405030307080109140703 77
    0x782c40340503050480b41041c41400b2200300c040d5501c0c000d407480010200b1000368040341000280e104500310200d03402e445484099400207035601c40c9040c065040034408031035068440b050082942c03a10f101805004108600808280c101913080c41001e40e810f03000030307194160303801020007166042411030f81c1c02181002e0001d00841039003001042d40d1000c810007917100140a0900080c1544003041c0d00041481d0f00010341c10392078602034034040f0341c103a2200601007200000c3c00c000c2001030f01d6030668070900030440007840480800c1070151091031290315540540d5540c000740f200260034410405928000d50b00710a1640c00d580020350307580c91754840c05101d0355001c10340c8164075108002c00381c105500d22086420035500503148545a03088890244583e04010754907030303000b910a88026110a9040a01e20b1800320b05078011000350040110450700742c4540c0c145002e0344165000c80b04d01c07642c020130143d51203003020308004142c0741043c1d01100c41581442546010303480f044034a00c0c3c0015541c02d00003 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 215236663 1250 215235413 215235443
    0x5060703020c0d030203030403090e130b060d06060303050307170c0306090414030a0c0314070b0a05062125061b3f090e0402060903010e07030f0c05100507 68
    0x80c540b2141269042c1c12203400b410340e000f050b4000000e540600c2c841d844110b6207945550790380350402c80403030f81e1010309205c0007030610109812094503600804081c000e1a4800c1580d10368100781c4500d54011000034500008012104e640710140e100c44500300c4141100d1810041d07441c100500001e40703410b21500c0410701103800c0180020b601c1030b80074901010b80c2e031540990f0303001824101d00184c080d40810b0050302030700e00c9840c1c146c0c2290070841c2d2142400200d51079184040d401820000c04e00d80c5c1103902550f01c2801040c0d440b2102662171000401010034a070114000c001c000d001d0150010440a186000c8c001a0341004100320111000540d19142d10414181a6030400d840c0700850b0610124500900c00d848140080c03004001c1d5600100d182028034032030490340700c0345c0380c840c082440c44084040f40c010701e00743d8010a04142c004001107544006550101e013003034220f5008a55807405001d0000070007005014000080c80b046488207a880d50340380f4050100e01c25414002c04000380003500c4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 215237913 1250 215236663 215236667
    0x8010c0905031c021906020a0807111e1f02041401030b09040314120c12090f150a02071202030a121103070c0f080319050603061e150603130201081b0405060703 70
    0x1050752090176041d0f100c01c50b00d00d00b411300095014015031000900c07014001603840340a00ca49105c0020200010600102141011380b010410180000103a0040a801c1009208002200c08020b52003240040c2e8540c509181040c0c01018004c01c94181410040d01443c1590f80f8450b2950041d0107081048002120a480d15040c1c40780c005030460130007100701404a001c4518010304003403c0074012807031203a1600025140d488011070b42c00602503004550406a001c0c000303407e950400d224481c09818141195250340880d00308a4140005074404589a80810f610012068900d9100701c010800800c0d25481d420362848002c100c0d40c2841003c1c20b00c4010881183c0c80750809035004551561a410542d0000301072074400300e12807a02c1801c01000c00c415240c081919070240c8800101100c203000110611503a01100421030503803e465280e10b441a510340000840c41651490101600c2d0846403001401c000d00181038070548030b02c19444407810034104400c45040d44c404450040d2285124501 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 215239163 1250 215237913 215237923
    0x71502030d02070803040201020c0103150501031a03010c0201200a02030909070c0b10061805030616021507080a0c020d2304030c090b0312030f0601050d06030f0c08010c0905031c02 79
    0x2050351540d10010f540c030b00340200580554041da200743d09945840b103400e001101920f40440070686071300e0507017408003c0c0f503002e5400050b0900078050455001740440001a0071244113082140c0540d45a01d400000035041c050f2112645140e210418100703035154500941c0c80c010801100c1c018015034003c58000f90003454064100c43e80041ca0102da440c0003041c2100189091060401260f4038002804c00501c10300101c906603400600200441e41d1803001003400070f112400520194026506450041c86410b018540710710a5038540c09030328101404071004a443d80d13050a42150044800ca03d0103a03440240c4e10101920400e00140d8001ca60031015910b100d15403005014103e50400050500446c0d0010380d0784240c11010340c0e0392800070405c00800392200710303210400c010008001458541c0501c0c0546802c0180345400142140c0b41c4e80c0d0a81c01e01c907602420381d00039003501402c1088000c24000c81071081b06900d02074800a2900b40030940ea40700c8018068861012095840c080e28402c00c0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 215240413 1250 215239163 215239177
    0x330a03060c09090b03030a050f0318030a03020403020319020919020d0e0f07120b0f0c1603050c010b040e0a03031109040501060c060c02010b010c0f0f06050c040906120507150203 78
    0x24007080000301251016042404522840f02e00d41e091040707404441c80d02009a03071000b40c541d111140352103601c1c101d4101c81da1004020300a040c030042080400c01c6003c00c003900703511880351401681c0300d041d0b0041501d0600010308200300b0b0981851031600586600d400c030760b049007401005103018420300744440080c1c020801c04d18070717051409440c003078001c2000400d402e90300d0b00c0300300703484005e5190318a902901080d1400a01044840801310b5040030394011020b510842103100f050514158802200c0f92107402d030001c0d40055000305115454040a1140302c002182c2200c3c20072480c00803110f140d8481010100140c00d242d42c1e001d0610f101c03040c1c102103440f036100080c4100480e40e159880504641d00703540b8252040d07460102441c1401380148610503e10105840b02c040b1040300f0f54682016090300c0d0022141d00400c02940c1000482c00c0c0503e6001d07690500d03000b501d55042c00b22030001ca45169201c1040c0100714900d03607001c81c00214541f0300780d4550341000c0d03110350a18401a495841406 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 215241663 1250 215240413 215240423
    0xf110303090c09010b0f12040303020d140402010e0d031b03020c09011d010e010f03140a0b0c09040c0503040f1101020708030406031b11070b090301090c08010f05330a03 74
    0x10070018580008141860460b40465190070240d132141c102e100e95001e11130062800b0340e010051a1b00341485a03a0440d80b00d8807a107400740c5482e500c9071196081c1d4880a242081c461034503007d0008560300003c40700394100056030041c10030480d5480040081e00d00c0740380c040d10440c015580d1400d0500c24444039042c0703140034106841c5541d68412500701320090082c8903100340705980000c00d01c801c150171030a0480d51000428004241180c0703c464000118ad80c240c0d135548100b106020028842000c064401c60701c2920690301d5004040c203000c156580c6040b900100311040041000040040500c81c6c0e101c0d4002e8a11846a9031040060f440c0066941100740c5030700c00801c0000b145036142d0407407020951070f000b840075006100c500c06d440d180303000603a50145c2d812883c0706000e44424079014188606008002151018241e100c90078040804c2e082254036035110040013014014502074240c1059043c040b80c161190030b40388541e108007100200111b500c0c3d0280c411a00366070b0f24040300c00515084 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 215242913 1250 215241663 215241667
    0x303030b2b02091003051b01050705060a0e0d030c050d020c0304052107090504110411041707050306070207030209150427031d0d060506060f07080a03060e01050604060f1103 76
    0x741418070707514040d508220f20520700000056410854007002000701d036441001030240400303001940754034901807d45141048030a118840219404204090280c201c4000025001d4030109082d82459100c0e480c078002d0500300100c2882280c0e210048840e0348404240041c0c1310841440031605500c2958061030303000303400c00d910400e1900c40d90381001d00701181500326203d01e0740d41c01900d420b4540455010b4040b414012000c0440d083c0b642000250800307040c403151405407904507950000b800800551030710b9110703000030701c0b4030300f0304001c095008521400209519407030b50340054100a0000c00a4282c0039000c0c01c41c10183e1100d800c0900c64485a9003071090b5006400781c0c2081090342e240043d00010340341ca00c0312020010051424400c0c10001d80150f00800980c1c8a800141401802c131a800c69020000c064010b4401c0001c0e0150511584d0781a0352070510140041c15a1955044030440040f00c0d0b0040006554400450302120040d061a6105403507648090710345200880340c4503058080 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 215244163 1250 215242913 215242969
    0x414030a02060f060405041109040501090c06050a0201061e1e0510050d051006080a09020d080301090501030b011406040e0c0d06030b060a1a07110a08010e071a130303030b 75
    0x32501901c41d4908400c1002c3c255601000c000650b02c00359405420a031132a02240130b1400c10909190707019001d0313400418500c9603582c0744600c0d1005a80203500096000c5030807440258207024501c000c0281030707180210102002d2001c0c0c108035892080310036140f00040800b500f00c507002800300040c88014590303241e219260f0700181c903d83c011200301a1192a010000f03408081c07441c0110203540d200d9880c448984d9914040000510314407109a0344515142d190000281462008601130171100802060135451031411508080ac1030f04090740d0360f083d01c411502030b9281d07081030300c00f1200000e0300084243c5412601884a1160440752442e0501745100481400501000e450107214140c8000c064243d550311080d00a03190419490070154003001804041380420003008038410000703016003101e0ba42c4142142c211a030300000c16416400089041002c0000200503c45200722901058607015844030102403c02c814040202415a564030011890b280c205660988600944c00210341500b = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 215245413 1250 215244163 215244167
    0x803070302070c0821031b070f0201110708060f0720010914010b060405040c020f030d1a0604050907030e0f0a062c03070605070c0b180705030319080414030a 69
    0x11200ca4151000840c0e10320008010030006081281c0d117421341c660064185017600a500c1a91010f004010b401d0620a4003800711a01c20380100320076485044c2903401c08000c0c1c03001405400c202c0d0084902e60300001010070001d240850030b603501c002d44ca0340e800d0940e942c4060589000b002d0011240c801d400ca000e04080d160b90542c800d844650065500c18500c5070b07000d40160a84030042c0c1040d4102000740410006414690444544060940107a885800c3c40d84a81c5285403c180c1e071090419445800188914138200411801b009040d100d06245c2420100881d503440d0000e4600350070540d8170400c03855000b00a00c44000300c07956078016540640c0441c18031001500521450301d0180000d860349203d411001c400500060135000e018500b0b104598a859000304002444036042c007040d450380d4130000f6a00162a88540400d907900c00070884142d00d880e141c50481c1d08864043c3e8070030090030f841850030081607285881c4e1031400080541e900d180c01d14081e016a80001c03028030001c103010078103036 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 215246663 1250 215245413 215245417
    0x905010e01090b1809031209030903070b18101d060403031d0a08030f040e060a06091802070b01030c0e1f050409151b12150302100c020307090b030d05130b13030803070302 75
    0x110808507480d02c86e402c01a80742d02c038aca9507081c0c0c140c0c41408104030f00b040c00c1d4050700c2c02d600200162402c0d00301560104542d20900070542c00010502c1ca000e206108200901c42d0014600b62040c0b400d0038155035003d05092003020403c1801b800c03800a107004c9a6590388580050185001035907125038040311075a000b40c216005100c05110010001030f05800d22858400840740559181055a860144901484625050542001d0b5000c00c9031002062410280314000c40c41083d8104459140411180c1001b00c0070703100904003d0030148161100c3d4013a00c222094800441c2c0c0024400081d01d006a407915200d207403a00018108940301c8960511405001210f002075120f030040c0c655010100c4045880c040d1041c071181300704443c01d0002d03040c1180032400044440c02c140e4a04503103500000d02e01003103070703029210b0b082d02c50038048a241000c0c08801c00d00d4440f4181541000d594107109151110b403401031a020305c1d00454451306c4500c18401d100300658201040c180c0e03d0402110050181d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 215247913 1250 215246663 215246677
    0xd06080c10140301150207081605010807020303130212070315050f18120a110109121404030c03080d110c0604050c06070b06130b03070905060a0905010e01090b180903 73
    0xa01190300300751841500510660025558059071545583e08140b49125003100ca64110000c500c5210008201c0c0c500030841390b40050103049400c0c105600d454001000e844005010340c0864006100f03100302c2d0103030701026910348c2d6411900000300c0720100b0580c0c1d00d007160320b41c0003030201402070554038800101544000d00601140c90006250390340c0180f0780b5007940f10505052415809042c01c7c1070400341020103000040c4082c47c0c0121840811000c05095601807003041c0ea680c0c1612a5103102c60303810411280340c43d00c22034004e509207807840d06c0b10003803c000ca04c00070b00050000210042000d074541d00541300244030040c0162100307081c0c04819502c000446044036584515421000c0340d18003c029280c0e0039502400e1140c80e40e4030383c030a00c81c0019440f1456441e0b41d80303c418170000355505011100240200c1d080006003403800318104010100d03c0d60080380500d10704401403100f81006141c6505443c6040b00224507038800304041002042108507501140002801b417100742d541c084000c01a07 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 215249163 1250 215247913 215247919
    0xf01151e02100606030b040c0c0b040813050d031d01083d030b010320130e0705150d0b10051e040302130606120510060c05120f040612050c04030204050a020d06080c 72
    0x88c0724a094010b84140d01c1c1e94002400f00c104200001c7c000603a500b0040100d043c0304540c0140f419a90030203c0e00320f4070342d40030440c08203590b0000100008058070300d400348030109203400d610b0340c00d1500da614000b50300a0010018081003107150303d0710b1032600c01d2000070f00d80705040c21803000765203003000e0748642000e0008642c04409151000c400317850660b0400c51100c0000d0040c000d000f1a100103800401009008030268051035000089607034851403148040701899a103144d40f002402c0004080701e8551040740d03c42c10002c003900f147c4503800001d803060760300c0082c0c01c0c0402000f980000a580e00079540025408040380610b038544036005e030007010443d0305070b8480c3c4c21200c910844407801d4482c02c59148000303d503a00c0042008504c0303045803041180c010000e4459524421921210b513a010f80440c4240312000103040008a52160b0b00900c0312050b40c4042100341071101d8100c40718851072101a10032034550005c16410782c9283c0c111000d2448809040154603030b2400705948911103c401588 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 215250413 1250 215249163 215249171
    0x8010b090702010c05030109020903190602040614030c1803030f1908070c150507030e03031f05030a08030105040f021b10050c0c030d0507031401060203030f01151e02100606030b04 79
    0x7400c0303005005560012070580c991078156800c09a1590007034200402c029410b110b659610005c0401030b13891010f00d54001c00000d0b03511401c141d005401240200c60820b6906400c00c2000829003034501694910f21010f030300b0f404089420301c0060300c0c600070320908200075a4002500c0d60a0404403c00000881c0c2540700c2c02c0e0150740f08841941c102401000240280b0000126280c3c1c55040342d00c160750043c0b05050029a20f0b550028042c50764104840425070040700280c40d041d20483d40c0c220000400d4110000c200d00800380d1b4480c07103603000c10700c2201e000d6600e030106502c19400580503240412100d4641d10007091001c400f440d80ca42400c2c0351011250726203804103000c0d60385a400c4910101c083c030025481c0000381540b40b0020040280a81c0404ae41d82005820100810300d10b28000d01c4103500850b203d0600d00d080a19904042c0e101740300c070010026500c0c01d429088024006621001036018040f007509040036030400503002c0144030001c0c0747c00d1b004180c1a07003552001201c181d0030341c1d00704 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 215251663 1250 215250413 215250421
    0x5070f050301031131060810020c070608070207150e0111010b06040303050912070e07030c02010902010903033002070c1202090c031302150304050105130c0b2208010b09 74
    0xe562888207010181030301c04003940501440c100f80228400d445980500c148681850882c01400d00c048000c1d0103030500e40714203040080840c02c0196189110340c554085141c8200b01141c42c0d500c141c03512440c82032001c0d01001074100740c002c5c0801402895440a0700282c0d98080800801644c07100740468003083c0c50f10342c0070b4006441407054030200040a400b107071805095403416545a041821042d41c480c0c44140d03400b941d240c0c2440200c2c014040c01c0d400d684682080703540501a10030070740c99542160302d0000c0200140c0c0c1e1060000c001c99805050802c4030507610080f00d5400014102a04a03428207050482a040c1155000b007ca203802030160f810403d845043d441910200e1402c0a5030180e000d1000c41c0342042000c000307580100350341c540307070024001d1980071500034401260b100081120101c200320070b010003806140e134040c103046540340d2240c5240c3da03040d4003c120350040d001c1c0d41c44082100c2104044650103641c400308030007683c1e089503544200f014040c0c00e08460071400b40c0352680c045 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 215252913 1250 215251663 215251667
    0x140a0e0d050f09030f070303020a022409040207020118030302071403060c03010e180723030c0102120a0c060e21180f0109030822060e090402100e10020105070f 70
    0x240e92050256a502031918484603460039054004041c06a80342c050100f03030803078840042100100952194015000885d01ca00410100003140c4480c03001e0300408484081d0344440c03030800c9400615044070f005803240e00500048407625180103d5140007414610003200307241d00080c084007140c024103540c043c08a295024161108400d071000b080030307070041c00140f080014000185a121090f8808a2007290300c04042a1a0044680c0141210458408011007183c0b003140307a03840e0b0b007105800606030259401c0001b5542d207000d218113080c4e0000410500c0240340310700300440945800c000305002c004003a03c02c85468450707080d0307903058090f40120320000f00079004081d15460424039811108500605043c4001160740c55002810040c2904d004400500e40101410410200c40d0306814803d076003042102c49104103070080d100748803105c07000f98502e60b108070046c1e83c4650f050350700310000038600506980d0308940405495018020001252800b0f605600c528030411903507640030b40c540144001 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 215254163 1250 215252913 215252923
    0x1509020910081c09031115130503061003030804020411130f090b03010c0818030f0c030c010f0b060403031112040b031e13030309050c040c090305070e070c0f060906140a0e 75
    0x700003103003801a003080440c12406c1006403020000e0710f8409100302d50390802000b948160022200340051005c24041c42c1020001d0b20781c09a4800038010230241551005080380d60700034002841141c070342040b2001140094207a82d8600181415a6801c40d200c071200c440740d030964010600b072503140000f100001d103014040c0078108012922a1156905c81000340c06e0815000d50680d0110b1108100940500001100901c681c10b41c4201843c0c0703c1d800442c0c86401d43c0d02070441c4000c11800c25490710b00b2030382d440c82110126070f49801e112010140080c3c1481c28105400018510164003040c001059203802c0300551080421081c03950301002001240003d894098a05601030340c06400e038140040c1c02584100c41c1a0302940c226111202d036540081c0a44100783c10355800100c4809003001000070401540000d4085540329074454681034400920490103e080901040b001d20901c10612045030712803044540c12410500ca07407034444000e510700913010744130300700440d18008041c0054000411 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 215255413 1250 215254163 215254213
    0x111011e200a0f14070317060a030507050f0102010608030403050d120216081b0a050d090803031306200304080301030209060d1a090114090a050601060c0f150902091008 74
    0xd030140c00c2c02c511032800c55841a8040742e030018089000325080c0c0206911000d09800c030303c0ba0f0340e5503000300d44404161005841c06007000f4014520600103000041010030002c095603c16224442980c040e540100c0c05000c082d40000c0d100d000028000c0241f10340440d9046030044a40c031004a00c1017135000c94000c03481185012014007818150000001d400403008001d20042000c0307110280e20420352150415880e907008842550224200c5840c03507400c102d0450091590340003542c2035181c280d040c16105000300800501044d510030603885070a48101810300030003000150a80c4901c3e240c0b230504440d038028002030344584500400070b49246440401c1d0342c840c0d40d00c8001c5201d14000f81c0914040e005c0003801d280240c2d500d41c50085001898048114490f001c084c0060800c001d980c1415424100d06800c03c1d030402640d5004074001c81c608001c840300b41a80002004c2c080c440c1c40400c04018241458000e50059190050005500440700348405a401d403206540003040b43c0d500c03407218410180 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 215256663 1250 215255413 215255471
    0xb0105040e0606070204020c10060602010c02190b04050a0c0608060102012702090402120d0513050108040b010e040615080d080a020a0e04020c01020403021f08010b0a090b090111011e 80
    0x740000c1d80c0e41085000341011920140025040081c160b464505140c1000c2e0031400480d900d24040054603424086d0315080314484c000740252011340444040c07050750410b8003420a913900f030041030070020208000e60806403c1041c001c11a615200b0041100105440150041d07082000c81038051b40300040000808100700c2003a486582c10794280180000003e00999020000714100300004034240511003514039640d5400f540c461942615120011141d005281080328100800c070000c0c2d5180400b03815200420700000070b503595032611a015080f40302c40f81c0c1d000850004c00041c98080002d050075140226150341f072465480311042d404a000e1600140c0002e0b14249000c00c41d4141030380213103030556640d800949000d031a5000714400d40c40ca030307201c44440116007850080d00c6a100c0041c1d4050500d1444046c035005808000804603d043d0090461f000c0e400034001d11141e00991508082c9040400203008402c0e550b031202c903150000c4158000ba0703a0509a0a0020514142004200001e18 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 215257913 1250 215256663 215256689
    0xe0f100f27060c030e10020106030201080c03040309120809190608091c0c0c0e0c1909050120011506050d0b0105160b07050d06090203061c0c050906030c04090606090b010504 76
    0xb0b003080710949089001034090003490400e030a80313078486401c01641c00b80107070008654146540300040110400422034000a5028420300000a80c8080c8800495001e01944030203d04203080504c183d209401c1603a0340803820031200c5012030362926100c01100c86944840c051580d41d110460749841c0c0210342c0c141858610030382d140016000c0c401d90780705a40903054003403080352200500440ca0380e06071030840760b581001c03c0d040241c1648041a64400d0100d140070b0040610f4240041c0c5810218164603007005440002c50701894025031000f10380620090004005503a105409809980550090501e03103003824039500f100d50141b0100c0340d401036180880a80301d8081d8841406010001d4a001e081220401c6070b080300002d50302035400038150a150060ba40e003000420002a89041101d4142a81609041c80d0218182c00c003450112402926148610b60340c201c000b80c00c20701c1d904007296005e40392480c4101449070a51006040d600750600401010f410100103442c24001c5200d004409010 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 215259163 1250 215257913 215257919
    0x4030806060f0f0c0708010c0c0506070e12010507030b01110106030f02040c05122e320d0501291e0402071502031005010806100e0f100f27 61
    0x280d00030b142c0001c01555650400d14014109080c551100f22243c0081e884071405000301d010070711460828410034103001400f00480c2c0d985035201c00008000c41e00f48025040b035030f42c064845c80035072032011803600c008102514144801a00803c2414003180c00902c1841e41100c00740c0c0305105a5098907044012003800001d103900b0007028101281c006004c00205016007001704002d4024280211500120014034902014012501e03071490102010440b5601c4000c01070409034920b081015115030341035043d80300c11800b01005001d6107000b26600010366490b100c09100042d4080034902d50305503c5100c000074801441314035111200c00c155071158400002c1c0f001d803c004c3c540b10f000000060009801d1482079281c6150b80c880354400c81c07841980010820041d50030901c0f013107000d402c00b401c02802d0780c2004004610680f0002110400f40002030711985010f40d61050000300b0818020501c604044030780d00000c04020381c96071050b0100f046008050f0600b800b0012800d01c125140242400d5a0b107 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 215260413 1250 215259163 215259169
    0xe010b04030b0903120408041e0b0307050c010902130e060c030705160507080303010e070f08040804090c05040b04082107020108220609080a1416080f040f0e0402040f0504030806 78
    0x40064208083c51104100410b80340104000f05c0344214010700f00720340c4aa290090510891010f86e100e012404c50501c0144400d1450406a0b03070020545d00d00691200c1c0202d0483e0f0042c000030002079400025060381da5207201168201b40080c40d90241030300c01d40d480f500c0a031500e034003003039600601084c000d001c01d030740c80a1410031788054503000b20101c8046c01d660703600a604662080e01300114006c0c0700703820428015040420501d00e40c42d249010581452305403207800c3c00e4046c0b40185407140b07469003501301c092407203442514068411503503181e0b6103a5907100450303544c018403550402000c0281c000c241140c0c1c040e00685450513010f0712480041d90303541d041125240503810040c0201100110103001045180c4110307044540315070203140c0d55100c08170010344850104030403224020b80c03c1118500d0382d040c64940c00e4400e0f0740b24070b1322500c42008900220080c01141c00140880151240021b07892034881003041c010ba000b0f4400308908040c0302024400e45404a5003d00441c0260001c201941 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 215261663 1250 215260413 215260433
    0x60501080108031b031c02030a0b010c15020a0203130f0503010b2407030c080705100b060c0325021203041401030501080c1e060c060114010c030f030e01180f0c0e010b0403 75
    0x10503132905807403400c0000b680f81b6020030a00145204c80301d81c04410040c807a0351611032802150000d013404411903800b030f602e0314020201e80580c6910b40340c010510041545c000c0050724400c1c221074156192007512100800e0007800e041c46024800d40c2800003c0480342000354590114201e1048a0405000e44e0580c60140b039028a004404010701c010088010590790000340070100d00c01c502030160b55211990420035a9421140c26105003003c11409070791000010466424524084580e08003c07810719800d40c800a0807a40690485048a18044400700100003071054404088407004440101c400440c12a1302c01d005064507036020303180d001c1d0305140800380304000d03403501c2d00c801c2103407070078100403a4494201034500c3c2455402440180402502e182c0709601000080c40c0001024942d078500400012a1861603003d150b6551132200c0314000c20b4000f106000c0b004809000e030f546e07403841c180a0141c01d800c02a112101680d402207400d04001444078100c4460611350703801c00d801e54440341504 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 215262913 1250 215261663 215261707
    0x30a03020a0909060308090a060905032d0f5b0e031e0304020d03080403090905010b0901020f010e101104120609030f08060a0e040f1a01060306050108010803 69
    0x11002c81c0c200080c000d07039503006403c007a6214036541521803c4450601c4048496034004030b050068000c0f0601540e00c1c00508400714507842d80d07440d0f1b1042c2d00082003c2645690102804041c09600c1040040d5030001a80740f00307180081c404076242c4508101d40d034090042c0002c055030190382582440b00512201032015980007048a02440c901d420300c000307a4216101c0b0400c208082c0c1021034103e940042242e4101c51411211555070324504d415800120050041c1c08002c080c40300c44004181071620801d58030300a80b0211808002d03550b1038011030a0181c20203110750780103108440400142c2c4006028601e0340794001802000703c070300720703010441c041c2100400314214904107020000c1c0360054220b4030040207014120014a85007a070030028440c0d00b90201040074000c038030081c130450f61105c4880030300b1038441d1307540200551102d203403040f4074985415005c1e110301031a80c0000055980b40e4007250407983c650320200020303981d40006403030307030102442603032410342023030156142034440c0540507001 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 215264163 1250 215262913 215262917
    0x7060903060203092b020d17010b0a02121c0b060702031f0207150501080601210b041106070b06030706020d090b0304020d150c140405281502150a050603030a03020a 72
    0x2402d05c03411203000f5000c0344070000c14003143e42e8a9a200c1d014001480400c22038501000f01200054544103a04418403c000b001c0c0c00001c0d2902800e4428003001748100c082458455a996074010180c050400210942c100c00d4640b440a078118905101100c815641c0130300a480001d403a082e011841c04c0300c82d0310352040380d0340810641c000210481e1a01d205061481d40c0000c041d41028680c1d071600c101600800207d40d4042c004000182500140d108002d038440f000d1001030741ca1780782c840303048801030b0440b58120102003007640130810705c031103d00e101c4d003030a07402c03187c490b9030fa40003c9039100b40304d400741800b04441c014280900307007000009680c40f0380060030f800c030603882994660800007503901070900610b43d640c03c0c54a080d070780004801c0300e1418041c1003a080600304000104a50440b0000d2084a680094469a28901000d50200074140100c0da002070b01041c10703000e500c03250184400c030501030180707000900c112503902c02c041c003602d0084d00071401c05070003044c150000c0d4800550802 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 215265413 1250 215264163 215264173
    0x7080a0605030d08010e07022815061503050f070c0b0c070807030504090608011505091915061101021305090414010501060324060219060603020a0b0307110706090306020309 76
    0x41c668404010720f00c8a06030980d1090b00c99850165000b005000c0501140b08541000700c0846214501c20001403164000b0011000350303195910b8020544841d1504210032281042c00006076040303d03101604883c0e14030b4506014a030f54406000840b1802103800d00c0104541c2601100402c000500c130f294085400c0f00f4540c5419503a4070750107136607049508207c0010300c0c00281800b100b0551300551b07000f040c5801c028018192005414440e020b06802207501428000001894807807030420020340a2048001c10840d40d4005064612500198090140032502d1f08100c100210b005200f1118050742c40c000c52000b0606040400c103404901400681c0c5502050070000d0307500100f0302c1460300074042d035107000130840407298051030720b1380d0000182c0120302c8091204108940e0003044220405000c1d10840341d010b00f05180010040120307401c0a5080b01c2544000700c1d241b92001d0046006039943e4951f443c40d45030407078055942d00b68600980002608046040000800c0ca030083c507004400c5c0820340d0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 215266663 1250 215265413 215265419
    0xa170d0603051b1011030a0e0102030717180904080307050705030d0204090603151a0405060a080a15061e030f060219020a0212010228090b130801180b07080a06 70
    0x2510306030f10301d043d4668001d42412140f00f90700d41450300e401c1901c0a824007286042d03108003980d460740595110b074400e0100100030a07401da842442141d081c1c84e40310140c2106d0480010210016412400d00240003100e009841c07e030900c1c00d0020180300303035400108540745a403045400c0b60360342c00065044810307200a2000141048860010388050078980c41c0c00512180381d0701f80700b0305108071403500130074451803c01204900c034118003000012402c1610042042c0d00c902d0082800c0e200319a12070b5080d0700980800c0c1d001c00501c1f5100303054078101c9050500c092915070400381c2148590740101054461805820000202407518a02d113590003080010b0400700030400021000c5c1d15402c45100682002e20000c04500d800c4149608110301503000314103058602d0076402c1000c280c410204209941c40903481030b40d500c40c0740d2200103400c021003c1c07a11804144500c550803101402444515402c10b406c1c420480121f41c03403c200c19400c2000c00c841d944030528152401c400242c80d8612094030f441001c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 215267913 1250 215266663 215266673
    0xc11040f02040e091b06090303090f011101060902120a140103120309060203010605120a0c020d23040e09122b0b040203130309080c060717040f060e10020a170d0603 72
    0x80c420301d0f505014007207413000b00100010b100300d072403090351241a01f0f000e00780300358030000156001c00f0b40503141184002c0f101d00040e5403ca0380000d000255608048001c604190684c01419a042c500b24110700c0544a0900322070a4864104c201540d08900340010404100d800210324001e1146080001e40d4400c02e440300000da82c8242c001d4008184000b8050150302c110ba0b0001d5486005408100400c0400c010000e44821038212100d007008000310400d4485817003003d0344d0341d80004103440b456941d541c4449910480c0b07800c03030704400746001d541c0703844031503200e280d08407003240c1007031141c1c03c09840e038040c45d040c00d5000b00302400d0740d01541ca88203102c0c15203540c40110301942001d1040c100312551460010001c5403190445c200716003161003c0f1841d03481e044240c5600303651111003190101c40444030311109005540c0030918080e030314640001c8030754001c2c0b4441c1d404c400a0743d4440c0a2140c1581c1070741c0d1124003a400906d1091305080c4800045040c0f00900004070304020082800d40e40c039151 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 215269163 1250 215267913 215267939
    0x507030f05130609081e0c01050703020c0402030a1b0503010303021005280b0f0a05090106050a0203120106050a110c1f0c0204020706020c0c1002030304110d12080a0c0c11040f0204 79
    0x4500520303800d100500e42005812110944a0046c0c0604207200300040e48402c1020784031418010301240080130103000b48000002d21501410443d140d01e41800c80d4405080c500e0081d4035140354580c1d80c10324142c0305030704490680350036030002c0041181d20402c200081000030040c03480040728a035900b4250400c004504182d061000c40441c0f1103041c0410090504c14140750284a602c121000700034945031190307860304540083c07d003151a2078501c1c4041c1d0951081600158002303546d5000480c40e541c200307019141c06800e50b40ea8400107540c0c40c00c000d646000941d1091740c01210324842d07030580c80c620320300240c0c0140c052809400040ca6a4040f42c01c0e40c2020004440c13a5070007043c01d947c4c0601c20003600390004000c0300e0301d850034034024001035224400035002410709507050f204580b0603140c0c4e41c0a03504190340120482c2122501c204020b000b42800e8806600817410706503401000ea224800c40c5000343d40012103061f4020300c1804103c001d02c40280c0c00d00070746800f80000100c030080810 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 215270413 1250 215269163 215269169
    0x1120807020306090c040e0a1106160206031003030e04090f110301060906080a17072004021902030304030305090601080705010315080f0a0c05040204030803040f020301111602011e0507030f0513 85
    0x10a0038442c0e100c01c06c000d41e01e11085000190f4000108000418503051601c455542c064400580ea941c1711058040e81140c8400080d411510010504c0035640034106008210b07030180e952504650706020800c0b0070390302602806003088440c001d0010219510010f0446021030040000071155525090030050b0303211907010490a404c000648010320001865038200072044446403450160fa80c1d0385d60449040c2c14221010b200903101121840d0744450341119404e000c1c0e184248070701041e074a0001e642e40e100705c908900203820200442d038610000244281640d00e2000500001c50070200114000c05420f40030f0440401b448100090401c810b0118802e00001a40680751011503400c010b510a43d07a40d10581c02540b040008002050707154056a4200d64401c00e8140030382c0c403900000b030241400c045086540500001c40542c00031034503503804a624400e8880d0b108155207000c048036007120340c2c26881c1c0450010020007000038800c24514586160a041560030825415503964034009950 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 215271663 1250 215270413 215270431
    0x3150b16120207080f06010305070e09010f0906020d1b0504170a0605010e0609010e01050604090b03010b09070e040c030b030c0f010c1401050a14040f02010e04090b0f1503031201120807020306 84
    0x680a003c03140c021710040c2044102c50008044035495a903d0030f1340e81140d44a901103011b9540c0c08910803503800e4105901c06020400b084c061110703203003444002540a4940150f60034980907417464441ca400415410140c0d03142c07240c6080c185442e91703415420030007444900c40380c00703803e140310000b889900c02c80307010317000d25034100b61280760400a101c206a0107800c100054039205004025a079904800c0301e066424a56010880c00e150901003805012184c2c072450384460f080303080003c40703a44103400802444045805120382124004143c00325104010344503055000300c1c01c00181803c0444c40202d0f6040189014140881d050321000c505800042c0d681000c2d0b5101d03c00c0c4501d00c1010300600510100801001c000e50900e6592001c505111010082c144910460448420740d620b078840700181d41c200040c1412450202e1503490284800c48180b9132201d005c000550090034004103a600404100e080b0050a900f007260440110114050481707800720b0402405005850500c0801e000c0c0901c2 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 215272913 1250 215271663 215271673
    0xa0b090a0e060906130305090105070519061113050d260a020c1c12050408010e0109020a060203130e0a0b0d03230306130b0d061104140103150b161202 66
    0x40000d40c14420043c00c10109075002c03000784030300340c008003940498903036050815075621051f400050358180601a005051401070901c00e031445484050500c00c1a03205a204020780100c41c2d4881506001d0301000203140b00c00c10200b4030080c2010106070754528021302400c491040030b40e030030411040c004401101001da021400c0f1416a40420032a205440d04694050080c18940a4005070302030812016200c0d1286880c0e00e85a540201c0844020b00306800081c401d0070340a94949020b0401000f0490041c4030f0600d0009102c2d2012041d00c18080040b02909902c0f403410601d03050090000c2c1c10440001e5132043c401307501d41c3c1c1e00e40035010414845d4591001701d0003058001d9242d81a40264007080304030800401810355168850001c420588101c0042c0420628012070040c510b99040148114508810000400712240107002110400b596030074884680700c0c011800c0c2c0341003508000031541312540921500b07443c40e001d000764140d2100c0d00700a6030101c0d280d00003042205404500584c00c1 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 215274163 1250 215272913 215272931
    0x7030507030e09010302060702090a091202030a120b010912050c03030301030317130209161709160902070507090b0112060b0c07060333171501050d0b01050105030a0b090a 75
    0x104071002c5450304031004115580345801050f141d10903480d000307228611010019140001a030b003c4004607802c6801c1e4119501c00142c06035030b944c4149100d401045042d208081164564080c6810181c41a941e4607403003031920000d00d100d50050ba00c100d0b880e00400c0300407100c5840400143d80254041c1c0e880d40c420300245103000603041e4020300790800c4140303141245400350310343c0101d56810540e264045046243c10b0101100c42645040045204400f59000c2c060b40c01e80c001030300310110300f03000081042c159441d0010740881c400d00400410342d4100100c2003160741030f5a8040020820181416040404084551400c84405400c501e04040f0080f5403070081040c100451000f401090604000b41d0680e600d80100b00c18100d4180c284610201981e41030512282e40004020801c0614503a1030042c55500c0c2a100c488042c40032560070302c0d8a0000486103071000c0700403c0e650304a8021000340e42044011541680010704030500c2c1900e6902425203130300c80404081c07083c0341071306001451b0701e1 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 215275413 1250 215274163 215274167
    0x6150306220207021003141f091a040e061603021c0f06080106060201020901080c090a03051006060206070e100f03020c0a08040305010c1e080702010b100315060f1409030c060703050703 81
    0x30b650007604101841c101e040d205400aa40780948c0055965500070f00b0520210500d500c1c04c80541c0021a0540c1081d8100000400348421400d100308211414003003c0c4581e08030b035540e440c0480305802014007502d54500424060341c01841d0150160300c80c02503a8400301a0f00040d1030709106444841a550039041041c00b50a20070100a4800c602c000e6141003000c9000821142025200404d540d40014071522a030361082ca24000a60340041515040c070032034141c0c1e600070803c2e8460340001d80150030000f1107451190f500700c582140014601400d00407105400c032800c0e40c04d40749500c2415030030440b0500009040000014043c0308038105691641949007441c25100301038103071340500c1030811400d8400351207034101d00722224080c90115629525404201d02403e583c01c1101c1d000240005c0701d694143d4150407041c0f40411540c0782c4901c00d60b80300800c40b65142710342c000c1c2d00080c1241311160300050341ca100a1a80c01d01c01030031100c1001c1d1712000a8040d91101d4021008582c0000e45142016 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 215276663 1250 215275413 215275429
    0xb0d14010f02190e0307030204051e0114091603091e0302010b0402030601020c090406230106021e07050d080f040e0714130b0d1b030b03010b090615030622020702 71
    0x4081c101076080441d001101094207800c022201c2c24880d411a039002580c038100300b004002c0da001041881182403001740e4250310603003021411400356119001180583c280e0b820410f03030000180c8110201d6840c2966100354540200800e410140c031520202e000c00c0e90610a40340f00848440003481004640c540a400c403000c2e856154081d60061040042680e004500a00246130031b0b12891000d80e100d24029005000a240d00081d051050380d00f005130400c2400218142e4200e50211601d015a562494820030f50310b109240040e40648810301003810450900e10b9081d208510f005d0520b00480c419010680158000340811001a0b040004c1940c2c00300c40f08079000c0f04006480d10704a00035210b0701e102e00302e500410103600d50025100d0100c0034246d120220b02400f07040003c1080340880d10050181c1740e0000c409202c1e6081503010705452810311111070094800038911a00714035510318815164200510302c0c1e0340880c0380032440c980c201c84802c040200c00a900c03401a911441c1c0c1c41008454 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 215277913 1250 215276663 215276681
    0x9121f06050f09042d060b030610051e1c0611030c0d020a050903031c0f11091512040c051005072301021b060406180807150b0d1401 58
    0x41800d1110410072074891400c11000b000080c1c992000350b590f0350030030311902c0481c80e038040c000240840c1c0c120a088075240c440548944685420f00c54140c87d1001c16980761001c0d69400b214440d0900c08100710300d00840346030440003611040910081e10840060034040d90100d40d503e01a0515201d032040100901c562141d81c0e8400d150503055050105030703202c15001e1480c100d90700503400112030040b02e0003003082d259a10001001c40f0f584814200ca1313a540c0c8a03420409514a9041044482c82903c8900a40403540350400816040409900c10459200c100768014051100104200c0084039419000a40b00b580908060027400b031801c001d11040c0000c0f2900c40e82003090a1141100117007000e01d2504106605403012541612855103a900a00c03d08040701000320f851280d9021b81900410071a100c0d42c001e21040244040c1e025180c42031610310400245a40c40400940c0d00183d0000c083e1004c1d0700151100150160201c4045104070f02d00600580e0040030b01980086400001d006403617203 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 215279163 1250 215277913 215277973
    0xe0316061701050319060b030c130c090503030a1b020604030605090718020901080106081905151507020f01180f09050f070c0210140c1b03070b210603030912 69
    0x39640280ca5440c0b00207172511005041c1340d1070f203024030300d56070301008100750a200050564401c0304420141d4001025448034078004144290380028140c90003006036114485152641c3c015450610a41079014852400803a481a0103020220100b20303144a0b8030311802d01d00c03000f0403c2c00e0a000c0807800d41c186009214000600410031140c03030343da2010380c082c1100e06138200b00f00c090319407480c0c10141890642210700140d2600c0704010108842d10300d03600c107000099a4400201040c1c9100d28401d108071100690490210308502d07002c0c6d4465a204110340c29407d900d03444003910f945c0320a458103102d03070080f0710300c03611a401d1003c003000314010150444280d0400c0e000f00c10f029408500c04013560b801c2802403080e112102c0c400c100c40d1000300c6001050031070035a014440d84c004c03c59103182819181c94064400c40601041c200c1d480d0003103501c80b01001c0b103148440c20342481070141010f401005250980820700c5414402d8603001e061034480100700c0c0140180c6c1d40c03241d034000039282580c003501307030 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 215280413 1250 215279163 215279173
    0x50705071406040809040b0102210301050f09010503060403210e0d270e0703150806041109190f020903011506030513030905060706141806070e030d0e03160617010503 73
    0x10004124500705c4010000940e008554840c0d044010f0381010f40104062007820362080030340320f031a00346000650589008440c2050703113000e072800f4450f04050034090036070907600c0507002c10080790140c0071042c4003403034500c0d205a1030580b42d02d80505407402807c000710a03510989105071210f400c2003125801c10440600c5030302c2507060f0f64001308410907910a1000c2c00c2d00a03404101c07a144250040034a030110f401c00b003c400b82d56500c0b115500c40d0704503000c0d02c141c596810700c4d6003031f8501450a03500413448400c101c07407086101400c402c001c0040302c400d8410304da030030098a02c4c181c400703010f1551110110545a0003103860301c1070190a0b550010481e03c14409400a8600040e03040140b4209841003070b985180c441240e4504940181842c460301d8001c00008800c004440820b0b04040c444840d407d0140c440c1da4540507026658075240c107070081e9241c3c104071049440d0b203100302d071a1080d464004040314022100e5200c2800d000584d600320700005800c40d290680308480a00081d8010882980200 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 215281663 1250 215280413 215280421
    0x1802041805070f0e010509040f0b0405030f0427090c06081005090c03090705010f0c060902130516020d0305041703070c08031005031c05070318050a0e150306010b0913020d050705071406 81
    0x210400200e000020440d43c480ac0c0400e043c418104140e561705210080400d81e9552594046030416500174010848401100080b200d071710103900400351702c96803002c03103000781341e003031107001d80e0212001000301d5002000000000703420369821841038040c5450b451080d559050030310b00a03082c48140e4000034107000c0344200803c40940c0c009032100185c0d400c04000541880c0904c00500320740d0981c2401404079060800b40070403806c61400f080c10079109502100c4101403262010b9090710070803a005040d86161208400017030b000c0c14000c55005545107813a840d0703114140e880000b2504252110012031b0b001400c14070090804104414038603c04901091110201840042c0607225042d0000c0401c03510803448603900e540c5658a0000d008010301241400307131a02c2e0a49007500080702c9980074240c0200c1c2100300b6080205166042e680396658a0345042214400c0c000c1c2d20f000340d07401d032105550070490b2083e0540c21b0710445014040aa60b2655103020b10309007000c9038540002d640085403c00c00503c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 215282913 1250 215281663 215281673
    0x30105070302121302220f0f05011e050618010302071406100801110406110a0b0c03041a060a1e091406010f02070803031506040b1b101802041805070f0e01050904 71
    0x3091103040d85015884062420148000250000c0c06e00c100300039042c1088c01801000642243c0e0603103440c40d0807161140c131150240c40c1c000301540300e600d401c084100a032509504400b1001a11a02c040c1400751802540c0e50b10200151341c10114001c0035005601449408140500c20740300900c0050000e00542c45017440c500014401c0c0d204034414080c5001850070000701c18880842040e0b085030900d10300b403500c9a500a0645e00032070781102c00e4580c00c040340e040d207002c4605642c0120809400740030790f14100501d6551b00700d404504100043c070994800582c1480301d004074125245c040001404c00d040840015041070781c00e10402040d0b420504003446075000010940341d0003102c09241c103459061a0700401e03041e100d160040c510f041e60000322800790b41c2400f654136244022003800c40310159201580036003110146c0d4042e4a2002c4410300d8440540342640010341c4020034007500304a294001e40e40c040ca42002ca030f103e000241b83c1e1500c1042050381c0210014010f0005030b420004901d099075038 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 215284163 1250 215282913 215282929
    0xa1d01050409030905130501080d030908030403030b040e030708070605090303010819022d0f0907020a032006161205060907111c0c0c080703020a050d0809030105070302121302 77
    0x142070240e0360300c07030400b410b061103032000c1001014060000c05082205500c60710240c4400d01900c1001c0c400d00c1d0001e5400d0b0310911446410a400003e8141141c0711070350300302c2c05800c403810321a601c00e495901e00352a0300c605000a14101d44100440f40e90b940b03071450b0050507030358010285c030807581003800100a00301e4045620340801540003540560120790303100194410b51071502c0f00f03002d50043c1c0d0040b003489076058800800b24400302d44544026420030104a6003003c01c580c8100140c00090780c1500282c09590b209851401c030802105c1001c0c10502a2480c005040b96039404888503258003144d041d41140d50070a1600c10031109002514048000c10021040134101c141007002407509089480c000b408016040700d11501000246500794400402d03d0200c85420740344422075074000500c01a00107852000c582c1e0192020208a280c00e0030001682c1400308107940300b40003081a1045681c082c0310301ca01c40c5416440050310703414146000703078250b8001486080e1100403510420056036844032 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 215285413 1250 215284163 215284169
    0x50426060c030c070506010f08062401050d021e2208030322050f03190809330709170615040c11061e0f07120b040605090a0501050a1d01 60
    0x90041c0d681c0c444100c401c00368130502038058414011a400407032212422200342041b120f02030704032841529031000044061003810081010b80c1040718204030154050340241511345602c48006003440e000b46000041c050800c035444642020006901e850a1008280400800c800322284010745052415182c0d90b4480980200d12002584031002c21402901098280a80e072280a03103c3c08548180146c2d9243c00c0801140c104031600c52035680368503c14441d80e88100070b800d0040c80c000020701c90500c6013852145102d82411003014054060151845540d4011406542c40b0b4100c2860a41035100009a00201c0707125078110b8020b103d82d1803108807003900304810031600050304112104081e00d10016080c240600c40c081e1008210070441e1001c440110703603080fa08218900d90b145c40f01d05101ca0011909071000c50700c8900c00b60310f44403555200754610b000c050030001e0b510313444400140710707884c044038800181c6072900f00600160401d440c460340105091101c00c8200020b0082044c2e91100c140 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 215286663 1250 215285413 215285431
    0x3011104030312020f0f070b0a050601020a0b060904020315010e0a0f06031101081801090302011a1503010b030c090a08011d06100513020d09030207140f0a031401061505042606 77
    0x801e800404c445d01c00c00311515510380c0882c1e95690301c22841c01031001c08049840c101041d16110015a480d400401c1d80a1101c0e80080b02000641c0c1c0c0c40204036107404040d000742e8042c41503a928940818000250501800d80030b6181c1100b4034015070108143c8040e40e00070b04895040101c200001420110480c4402c1d5003420218001c0ea00c1141c4200c01c4103001159252940c24030b00e407803040c190194030210303001c042020a40840000e440520520302e6800983c1a800103003080100200d00754280a140c00103007400c0d041c0d2a00440c800001c1c2402c50fa508451030a0359600003c8510200c1c40520380d0514070142d020304038529001003030151001461003082d005204040c00342a40d106a54119424941041d800300076024160030f00039030b01c02c2c2074080c03240700200700f0720752403618130300b1020500c40346100410494180703043d580c440c1400f0f81d105582000e290340315003002c51404c160307110f120614684c41c0d40b526280d40c90101610940c2c0c09010300c0248035015200c2a040034076010403003a81c080700003 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 215287769 1106 215286663 215286667
    0x5030717010f031103010c09050d0503090a0e07180602100b120d08060306090309130c020a050a03180f180b0105040f08070311010203280e1302090301110403031202 72
    0x1500d0000315145040410003498441d68ae000d502d0f1080050b80d04000d00750004c91203500c01500082c01180103001000600b079401100740e804040550ba6038044203282c03210203034581c265410210038590b203d004007070054651881c6000315170199030454101143c0058010440d00058801c584240660000714500460000544680010003040141e1402020b0030880090140440100a5020f40342c24200411821701c0071264a9020742c80702d07070007440740050300c54010b0038580000c07482d14661134083c0700591721402c2d82002c00c0c0342c580e00040d003102c080005032000e00035076000c182a10a40400130502c5080450701e00101c9104848003040401c0708401aa128021250800b9043c49410000061040f19020f8040700450a080c013410140b00600400c10018520541c051f007250001122001402c091181410810f070311410941001d085070ba00802e081003a43d0351030381003900 = true := by decide +kernel

theorem cover : BRFrame.Cov 215107913 215287769 := by
  have h0 := BRFrame.cov_init 215107913
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215107913 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 215107913 ≤ n) (h2 : n < 215287769) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
