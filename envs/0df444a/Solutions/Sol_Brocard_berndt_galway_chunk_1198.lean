-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1198
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:42:55.175984+00:00
-- url     : https://prove2.me/submissions/b389a0a6-0b8c-4422-8bcb-fbf6d70d62e0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 215287769 ≤ n < 215467625 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 215289019 1250 215287769 215287781
    0x8010221160c060b040515040b150706020310050306040c06080f01140f040608030703050c160308030103110402040b0c011a0103021306050309120c060f06150a05030717010f03110301 80
    0xa95160105414041002102d220014a0080d00c2240e140c2103c8511512248a13050184010303d55082400c5d801d44103110685070b04c05111401034490040e400b24503c0c50f902501d240c41c0c0e0012005d6a60741350000c8841c1c01c81072580210780c0c580140810b001c10481002d1707031001204e040b5269000c503940c03107010310f000043c0240302e0030b0403e11000c1104c2c00301e843c0004070a2440e1900800004a0940701c100c5580395400a08048000c02d00000d4205040c40040150560503100310080030310f581d00b0342d556400280018030006020b1000940e400082e9502d9405036405802c0d41a107007925000c45820315800383c0b8003850711050801030a65103d10a520034000c44d041410f22210241c2401c0c03a10204482540c0000c185042d0340c0100110000044484401001a02000300042003141442400144a4400581385c148a81c0035410700c42180784400c419580b1490160401c02e86a81c1e4400c0b0658040c83c1d545820852034844a00200f82c50b54605120820351b40514548031091800c10181400c80349 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 215290269 1250 215289019 215289031
    0x10c0c05010c141602041118030708071401050c01090807200906061603021906020301030c0b160303050403180f0915030f021c060f090b0a14070806010201090c08010221 74
    0x3c0800103004008590701c582c0e0300a500c0a040007038490441c205038501500100740c519050051720b00104403603e4208a002e0180074034102400080d86420b001c04051583c100c00c85050107004a40c0010006003035002c2a40d0f00c1d0004070213a41c64215152030303212803001c40d9090348001c03581501503240c1d080090b030080c400d0b1006450b1500e00313048581c17081c41c0300c0c00c0380d401102107101d00740303a040c14018400b220401e2148100005600c0b541545442190394405801404032003405100550389294144210100c0c9a010f040006450320365041c2100d411789003000e04070042880d00700028042400c4c05604049a08007401000607844400410201c0001c0e44000381100340c2144c24400940f80901c0c1c00c20001d001c69403042001c40316a81e444066940000014485555030070301c510600403d0900c3d02d83c0301517649070821080d109484c0141c041c090240c42031040000b91000107000340d000354003501440f41c1000303107120640c0d030b5a030301c00c4d01075031250703007601002c25448890000601c08200d045020308 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 215291519 1250 215290269 215290307
    0x12030a0501140d031101020906040f030b060d030914060c01020a110106211202010b0d110102120705030315040e0a0c03021906120e0705090112140d12020c0f010c0c05010c 75
    0x40701c5840442d080c419150381d4581e06c0d58200701e948860360b9810002c00007841c01145c4c400720189541000c0640307010003021240902401c1e92501d0000303501000244c00d503480c014483c21040c01d884003007041801780111001c00b0b588009807600e10141c000d4000c1030065100c400a104040e00c660040881d80c0c0105c192604004205164000168101e5602444008288000161080b00d80c002900545d1500d109481905000030990b84a5a040c401c000c00100c801442514002856440c244e9030b1000030243c0120742c001072800701950b0713215001524401d040004880703a5860500703080000807106e2008034460a44114000f04100c41d01160b242211055140e81ca0101d14480c12100544485111f0100342d0103035030004911a81c032071a200340a0410058003110010b1546441102040c00c1800454598003c1e07583c1400c2e681e100c880034a00c03c404000250301d445907045640e1602140483d0303443d00f9400d0a03103010700b4590005101182c14020002440f00e081c16180541e8803182031030680fa010 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 215292769 1250 215291519 215291539
    0x140106080a1419140c090705040b030a0902090c04090501050f06030711070306020403080c010f0b03060621030a020607080c07020f0f01051201081e0105062b0512030a050114 76
    0x11400e2054001c1c5014514400d8543c80160b00b101d500003e01240c00132100360a04140d090000303042000507842c041410794409540d414010300c094a94016840780002c03428000001803200242500501c0095501501e80c0e4814105101c00002c00c1c3c0280c0a42805289044000039151030907440120409101400c101e140d612581021a050304003007001903950300c501c0ca0000b000440600c028802180200d8459407213400c050401c030700355072420728661500d50401000010641e80440c105800403c21103080004440d041c500300d2440d060310402000318000410012909074012034610b110303031420750741e2440540d1140115070880c0640d03c00650004240304266100b401c0c840784d080c0d40c2900c141046428507807030104a902d82034003604514440e80104119102c0a6200c680c05074441141100a001e40d01d084004180414000052410812180c038800e070204032100c02c65103000c680000585080314000300220b45e4550098803402101490640006100d00d140701034240942d50042809101f = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 215294019 1250 215292769 215292773
    0x10c020d0e060904150b19030b030309030d20071805010512060109020f09100906080603070e151504060504062003030a0b0303160302060103060c030606050a050d02090603070507140106080a 83
    0x103141040c80004501c17070085000c01d0301c0034901e020300820880804240c207601803019000f000d85044810550180d03000b40200a050356000c511851003180e60b1824000c90f903080010042104480c082601c6a400b6881011905d078400107001c920800d04042c09110f166621000d0044004042c084003c89400080050124500a400601c076203410208042d06002e200c2c00010074800c04d601200c000326000e400c04000c2c941e081a2180e0344602d04401525080749407060b014550f41c1c0050a500c1d240c0b00900280c0c0195076042e0320051400c82c2080540d0b04da607125040036103207511034050a070202c1c5071817211420300181a91820700d0000304201860840c3c40d000315220251a000f00c4141c0d060005000b954010540c061120110b80c0c000d80c01400d0035495410840c0c22070301d00341c3c0c01e2002c240c00e0603800d2216a40241c1140c1c000780340e514100c0d075074020314401d2400900130360010720350040c0c002082c001e50b01d501c40064002c1d280251440020241c04c04045422140d65200d075941a8110b544a800 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 215295269 1250 215294019 215294021
    0x10207060f020307060617060115020307230102031e09030f04030807021f031d0d0903030c06140f01090b0301060509060d110406080a051b0d08030702011508010c020d0e060904 77
    0x144400765030048a08203056039071400e0641e0355681040c051160007038500e40c4107a104014503401003400500d040ac0d040c549100094484c4100c8402812200502409200d280045413080c0002880d2400841d100d041c507481411410200d9441182c0e0b90554a01250740881c1c00300449418502e24240346187c98030b90350325440903401889050f41d2111825103961075221907000d03144d200d0481d030741e0005102d00001529960348030340d81301c52600c0ca500c01c011540246811110000030b0b40c0c0c045c1401603211041d4034040c0090b040d10020040d602907054280120310f880e00104506a40081c1414820b07612100c051600b04c8903148070b01a480b414003000714011b030402c51112262a17000300644200700b0b20381e0002c40c0c15142503610a07407a2341c1c0040400810b00c0000d10251740d0515014031480d072000c56150000d10080040400a00f00c0203000001c11250341c000d5000321482c40200b070071b00c44c000e40c1e45c50b6518002c0610500500260084c00c40c4100180e01c1a0f0119410172401000281000c0a0f201404 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 215296519 1250 215295269 215295287
    0x10f03061a040603151104080604080f0714010c11011a060a0908191110050306010e0103061205060108010e5a0d0e0904020405041b090617060601020706 67
    0x8201c014803000d556071651618015003016501034902c440b8440c0e5518089800c940d01c50501c55200d9406101c03e0103032400220382c09402c40d4001d04c3c0c0b00d03194202c1c0c02040000b4406c9000040c0800e005c4142c0314151441900982594080c40e1104140e4202d0141942c0c00e0340e180c1000a0051039000d20450400e1801501030507490b002484c002800c0703900c0e0070100b840c12001c81200160742c459900000c040100c03544a500369030500340d4034407000350720410000e403450001816543c184100b910007071265901c280c0c400ca0050451840da03408074217050820a450360403e0090703007499402c1010360240c0210005d104201c40017400300050b0300308903a207070f80c580580d0740c9643c1001e191141c1546049081156514682d00400d08200310910345000d00300030b140100d500000400d0181c0401c00609980c2d4481e101d03940300e501a140801d00f99101e18006e2800d8a06d0699281454805a80811503151990000041c0d55a2421100e8004d03600c00d1200c0d0340c0c100c1100d00703a006034800141400b416124001c00 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 215297769 1250 215296519 215296541
    0x20d030515030d080a05250516020907110d180e09120a02030a030c092102030a020406090f06080a0f140111040909150c05180105071a0f0f010f0306 65
    0x20003826109500068104015001e5881c0044d036800c2c03d002d4451014452990003002c034101503d03411069103014400c01c0c2e8100300d80010b2020115203003c0f2060160100c09505a0040c506c60036031800c000c0c081c0c5506a0700c0c40d036082da882451500080c05003d8048880d5101501c540c40d08401d140900c006030045c0018801d414a020305250a034a06061201030510f20b40349030040c6866202200b00101250441d254500401942d00810082c6088501c200d440e961b103d0010942c05400306c0c008246040031001c0c00070341040c82c1c41c00010b100c0c40568041d103a01606448140316a66584000c181d65a072122400360605100401d41c00004019550701c1c100d4007440c900209026001000c10003154005a225080840d240c88641c01080f07025001d03502104890042049541d00c680401010390180e240152000c40341c1c031880201c1680140c0075902040e41c0300c1c150f40d000e00b01038901516442c43c142c91402ea0907224801041d06000041d802906840b00c1104900030300d803840e100e91010300822405 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 215299019 1250 215297769 215297791
    0xa170c0f0d050c151027090b19110a0311092823010c031b050c04050109020a0f14130b0705010b01020303041509030e12150106050f04050d0c050901090609050f0601020d0305 76
    0x100c0341c04106c50b000c0d00c00d841d4003904102c801440e2290704a4160140d902e440c042091416600c810010130510603a030310401e040c50006440380e17051400c2c070007a114400a142e40400c110b0540905602c076040380e41c1880020001c1d0048181d134681c6a240001c03907030080c8115048002d088102154400c00c802101d09000b4942802400702c42400030044082c3c89000b56250b800c413001e0250781e82440c2c02080c0c0104903a4404514003132000100030000050320217002d041150010b0b00c242c2059543d42603075000d51307026503401c500c1c40d03442808a0042c0d20104080303400b5403c007521a1030540c0003005585c03040390000c4c441c02842a8100c00030004200c085021400c0c00340d1741c91040e515850b0400c1200040301004010421f11004140200c2a00e105074030040811404020700006007a480b000e036030803100c0940e0840e110000c07524001c2c00e6009241c02c0980c2000388940009800c10050b0401c401b2984405420080c5440da1540910001c5003101c07642c4c090b902446042d030079640b02e544030716407080c40141 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 215300269 1250 215299019 215299079
    0x30c03130b0403030203041a010509040b0a06090e0c0312040807090b031501060206040302060a0e071a0904090305180604030c170f010c0509040501080a170c0f0d050c1510 75
    0x14841d16103550588096000907408001c0004000054103429400804007039100391642c50900010050800280b00810300c2004d04003043c21b02c4d03a80c1c0c020801420341c17103406125141c4032200083e13076400e0850005200b846000c920700c1c0008484002c5405540ea1040a0954182450b030080043c0c400c100307070070b074051107955605042aa41d10030003e02a0a260b8060103d5082905000703141110152219200700d00d00b004031544100e0000d024030498000c0c8451408408119170340c20500e000301c600e03c030f8005040c440c90004041c2c0c0f110040107030038a4001b80c0b280d4481d02100f031200500550100038682d15401f102031207400c1c1e1412001d8240d0001c0000c030b58a07000303500707689400e4681c0e00000c0c1c000b244010a1810142c5000d008042c0074020b01c0004040d483c1b02911020720717000015250a1802c03000041040840780180100c04001e4441012144801a41c0500a00c03680c0084145c441c2800b541024024841c0048040f601800048108103810350030601c0c2006000355503146940f040000c20 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 215301519 1250 215300269 215300273
    0x80c0303011401030b04050907060e04061508040212010c020a03030207021f03050109060e1b091c050313050f01020703030305060301090b0901060611030a23040815010603061a030c0313 81
    0x11400b07440002c248000c040e46060001d815074100110082c8281c0c14101001038134080041d0007001c50791149002c001a0444c071006c1401010a1b421040d2400741c0320420380203c0ba00710100301d000c3c2c0e00c2650351030300c10b001502c0040c3c203c64240340100016003150340200003180c402d801500401d8002030600044030008046c071034000030b004c1510008240c84030b004002e00c00841c4145001440c2e125010b05041c500700c0000e010850801000000a100c003050885c95611900a01203120081c50900c050705426420480c2e0769400c070030038001c41192064004101804c0c00c8054403006041070700240360843c2540e800381c020b040c0060440ea0507640e5501d423100811003090039180103507540307000004c010b42000f0009085007080800030001e540304202102e10b07554440040c1d0180c501c0c00b0455404401c4100d44075100b807085500c14040e07846903400c500800f8bc0c04520660486030035032010056590349607800c44022200601c000d061290610029200c0700030800110b038000b14052071001000b50755 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 215302769 1250 215301519 215301523
    0x3080f18030d0c0f020a0f0204020304080f040801050405072301120e07032102070b12070309080d021902061b090a0503370c030f0302010902031903080105060c19080c 73
    0xa000903100b150300d80703e105400d00d4100a00440802c154405016500c18a840b500402c24100310001e018035800400101880840f100b656103172841c5100d01c0365600e94a0001c1800b03410146d8042c0d60f0b0f802169000134444c03040c9071811034010444600314408000442c01074400602c840301400c40542c6803002e003000314200303002c0003000e0341c801d600307a0300b207258042000c4001e020521040c1066511200341030103800402002d5440c0440707089101c00301592003202c1100079003031a2400610380c2130085500380c074280840d00a040347c8803050402460442041c01c049030b03aa9000d460405283c80100d50300080c0c0380100004050110014124034100e59546010030328000030f889000603241d058240b0715420030038a01980c18040c40d0340490995610300c1d40c41e01c140100c9c1c0fa101c020500380c04420b180e400c2500070741040f42000d4004050710186103440c0700700038504840407001ca000480d000d00100d641e00d012016680c13030303224400080c803104054940b1400407448100094a01c200e0500c1121031811003 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 215304019 1250 215302769 215302777
    0x306090c050a020111030106020c19030f030c0209060108010506093001060806150a05090a150f140301090515060a090203040503040f1401020d03110d02040902040602060f0403080f1803 81
    0x1075888607070310784403084001e007180c14440030a005203004200400400341e0005141c074049404a50364840940300c43c41e01d100754129a0300c0240403962141600061540000700b00c40300c60300075600c6e140241e45810044581140034040c055104c8000c0c0054061414108500d107810385440c20500407000d4142021901074803c0c02e01c41c040e41c0c2d1944424448008244541ca800c0038803e50340a080904140c006040a20140603143c0280d003c41d00081000480d90001203010b054115004100c907250446400300c1007050107503442c50404401d40500ba828140b03e0308040c2504100074240f413141c0d01c5440f6030f0590001d44010743c408500d1401007103900c409e10095028620940045a0b15442d00170314005012003580241c3c03a01003120708071456a40c02080c0c5200080041c81c0010780e414840809100038010510680041c910100340400d49901d207500a106031541502101d8407981c685550306e641c5601220000d00083e0080f011a0000305641c44840d088524441240c2800030851107145c40d50700 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 215305269 1250 215304019 215304041
    0x18060b0604170309040621081e030a0c030506032404060e0d08010f0e04030c03180f060831030c020f06160c0503070602070608040501020702041806270303020a030609 73
    0x40c0e1058a107002d100f43c0d0010247d000c07480401507007041c000714007400000e80160141c1800113042030b1140364280c00e940036034000d456180d200d00703100680d81d004000c504100c402191804010995030700c2c0000d5500740041c0280c141c3d07250505da901280300e2004000c0e10455240d501c5080d07440755902c0620607a880a12540c2c0e40c151158500005402c511840e40d01c80103c8065140074000841c1e40312010841841d01401c210403001cbc1204002d04420601d6400810300381600100850790640c0511050f0080142c020b46045038140c000480e07103d001c401c14056041d150555003d00000d000e03100c1154010b000814046000150101080841e407228140e01e46115801c4013240c02c104400c2280710261009800501e101801e000010350383d034016000d0082800100e00004003003010075011590781d568040c10a00540c04c85401d0540903410100d03045581c03d04041c000740c1546000007041002d102910f45a0b494440c0b0782c0c40c140c00a6200c112030750100b5485010201e88400301d0701405c0d503810 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 215306519 1250 215305269 215305273
    0x302040504210c0206030c0a1e030c030605030106050609100302040914041203110306040e0304080f0309030f030703050901030504060905060103050601050112050405340b030106110118060b060417 86
    0x2410340b051990842a0040ea0b060600143c0750b12000541c03902e805a03030380084081c140e181d80f080c001005441c0c2101c102c0d40d98030285603070007200c292564035030801100c04505440502c0015190f004141c00d903a01406560742050050240202500d0001682c03050481d003401c005203055160f01d042400d44442c80d018000c0c040651062104020210910900805403464100100c13180b0041440c1c04c0d10029003020f00c540e44a000b20b07410000140100d900030480f0f04211070b10294201031085c1c503038100c0300040d8030038003d10740b400000310400700881d4111030b4596142e914109000c00190f0003400042d000781c540c2961100d4150006a0821130140a14040d0006000643c907100004003131a025402c80c0124504140500001a40c0041d0b024034a0100e41900102e41581e201035605022001d01d071b822004009070000980644400011030603601180e580241c0300b800e1348002c0b426103212280c1500c0d0a005c103010000800d11503070000740c4034800206994546503403400103018144544500a50303139 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 215307769 1250 215306519 215306543
    0x17030c04060e040b0d0818060c0c01020c09040b010e070e0d0605060415030c030618020d030305071206081c030e010c090f0503190602030705090909160b040803091201060302040504 79
    0xc1d07030005840403200780d080750140034108601c00403890b41c0340303042c5c0010b1480d440860300849840d110ba80041458801503c0da9860b0114405044e41c0c410a40701298098050a80404403a040c41d40305c561107545c010810b00256440e028010803000e100408410801c400d400b910364450350fa0101c13084503a400b90802080a082150820049441c5400107100d8000310040800009910956070412607402000019425096205411590f18080300013135100786a0030444082607015032103d4029141559140d20540740c4601e05012100203001d84112030b4000d9030030000c000000030160f9184101d5240101d128050048100c2c02d603840c01e41c03018003045a0060600000541181d0720008002c110000c02c8040c0140180071021503000b071002e000150004001902ca5000c1c100311007009002400c000d1140ca840d080041d1900340ea02550108028a039030005680c0d03120300142c3d415515098069071402d942d410030004481c00d0b80d203841c0519501d031b00740040940c0e92840351070b202c1d90180008107030b0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 215309019 1250 215307769 215307779
    0x90a0903080702030a0c020d11090c04090507080c0912070b04080d020111190807030209060d0903020d080601080c07030c0506010f080d0206090a061a130f0605090108060c0717030c04 80
    0xc2a07000804040440d8424004134100c1640300c0b280b592500d4051715000c500c0715032800c180a500340c881d1070b0107401146000070300409048200050044440420040005072114101240c0184084c7d03664982d802d000c1c00240c0051420340d4200308203500980480740e0296640b0041c0101350019480f460f210740007146c2c00846550280119004041e4000c40c242c07034508801480e1554409035690101001001c00004148500950480b140408020300281e01d5402c041e00110241406000440050056041e05101c20b030107054090300806058441c1da54580c2c070f140c19010319800c4400190200328a030160300300401e000b4401d90380a8040b02c0e41802000382044404ca1400084040d15421580803604000c1c03100c0011170241c2902d07502540100e00015034000c080030600d45032052944c000d1441c200225030103501c1c2c1c051341c2c1c0b00030407040a10119035518100441000c0c02d20421109070480e000045d0041d4118008000d91403241c03000c81c0c3d844140c0d000700c0d88160001c80c1c190010030380024051103 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 215310269 1250 215309019 215309027
    0x8030a0c05030f0a020a021006030c0614030907140d060617060c070302070e070c0602120106030b040b0108010e0a0204082509020c0a170c160f3c05090a0903 69
    0x520002030500714558201003511503200c900c01806202c44541c040307074500c041c910074884c8d10030204c0c4400040c007826844c1c1c01c0c09480000e451260601145102e0085a0848001020f0b01d03c210b83d04806070007d14604043c800301c00c3c20850002e0745c440e0744070520900062542c451100503281e401b4022481c02c4600b0700f402c0c40e0800240c00031040c001d05220880001e580000c44d071080d940440300703100445c0c8a00105841c0071203560b00043c0464004039224011300100011107040300d006940500c42c1044003414042102c0e186520343e80010764100051001c150400e0840350031a601c07180040c81c2a40c1d5038111401c040044004e124000700d02110952808040b00ca04800b90618220031480d01840304191a520205080024900c0c009000e000f100034132024162035045c0d0355201540c05612072482c03840480c00080c011000e180d040a0804074030b910505010445002000c103080301c030001c880c103003c41c401d00006071444040d0078888021030291074448a641c059070031003074082909180c900d0003134 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 215311519 1250 215310269 215310281
    0x20909090309030a060b031906020c01050105040b1c02130606021b091311010210050108030c1b030705011b020d1110020c0907030f11280c021e0d050a08030a 69
    0xc40a64420b2240c8411954042030324507000e5404040090b81100340004207040440001d80301e80001c82090040b003d1100b80e40041410007800f4000b009140e0304c43e070400c01240c40da88010354220124140341c1c051401d2421490380b01600003410320100d0001207121506a4425801c05001078100744900c0c41f45003564590790700c801e9421142201503191140700002c0c500c03209107001e04101b0512017140d4540e4028000403007510403544092000d50f860724102a03403940b040d01190300c0c5100c1d08000042c03180030f029a98411070002400b0384055854a00115441208120b8613040183d20164050040c3c1d260fa10701540c203440b400110f2501240c4604001009420f10381340429504044419485030751200788403644480355040006604500184003001401c03136095645841e0400070384440381c40729a9608903000048080c860a0f0321a44107002c441c5c00342c0910000b5001441e1400383c03000380030017110010032000054044110420b0a8070b0300c51402074214010740d50f6020020500003524541d0040d8 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 215312769 1250 215311519 215311531
    0xb1315060504050d0312021b01050117030708040e04020612090109061d0d030e010e01060f030606240e01171503011a0303030a020304020a080601150e0103090302100c21020909 77
    0x880d08280c500307400f02e01342e14042103004041000c40175170500c0903040c07981a0f0301b0a000d508030515041c0980220503001740003c0c05641100480503500d0781e81110004112000c2ca684011030a0400c0c3c602140c211203000c01400403a03008900780301d04911000800807452244094500106e0680e07400d08103802122114240a0703145080684212841e40002524000d030030000e180c00a10801d00b00c0c05140140420404c007130b1079500306240060100090a062300689000d8142044416035a0420810fa15002042d80001031020000000510f0045e0702c3c00078884818105000101e100c0040640d008504942c541400c4002c0108408142002d10030202070801040604404031000b9001a6507404020401c0040c40d40000000c0c08540301c0b041d4600040020004544095840b181080382c480000c291a100103203c191100101c2c0d032007806013880b0181c06402801c2c00081d0a00204085d2444050780e100b8443c0d45010b601549024007a000202c00c0862401a00d0b02c0c0031008000c0d4810000e420 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 215314019 1250 215312769 215312777
    0x50c040314032d03151306080a06150305060f040302160b1e0a050f0c010902120604061401050d0b1005030712020307050a06080f100b070b0609070f050f0c010b131506 73
    0x40000c1c03c0110350440350031001800000c54142080f00000d00d80104018070086020f003010307400203a81d4800120707036101c1d49c4541e009010a000b074200303c0e08041070340e21000e8a42e038400400b08800364014102e00380c000c0c2c080c3c4152002900f034548812400251903010512070940081c41c210a0f40e00000040003103198020048c0c0f40401d000b1004003603001d0070203040c2003c0000107002c9004502540b1480025601030000000d044881858607200c0f10121002d448803420014080c2d148100b4031303d074a043e40d60007810b64062030965110300c000070900501014480e414090041503940d410030480c2c00034101c3c0c4440030041800c41c41410306045455220034001d50802e6410300080f031f0401403480d840b0b00c41c407481d2600399070b032140c802c4031048241e4441141c1c0840002c0b1401840400c4400a02ca010241c90340f00b5992140401100d1b5940340c0c518880000340c05102e2001c03440c1c00d0380010310203c940140041019610b140004154050920707401c0c04080d41c540d40041251642c03128180100000e040c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 215315269 1250 215314019 215314087
    0xa0e0108090a080a0e19120314040e0a0209010e0a0b0a140f030619120308041a04050606190512010507030c0203040605040501260f0601080115050706050c04031403 72
    0x1543c45403901a00500b1421310010041c030109644410540007030a02e445c000e0b1010f600c0e510021000b0910b02c5000039400110040d07607101200f204481120100d40b44000320515642e10f06038080c00a400403a01e060422543c041c00000d40d0b03440007001d00290001415146e03554078280c4000e001c18103440e20120100b0301c01d003c0700e201e4103c0030b0142d80c0e201c00191043ca642c180c800c400c11a80c40203a4000307240c1003001c90301082c1810b91150143c2c2c80f5a01c0b548100d000391300c000582000151044030024804c6c0d01c1980060a9401c10716100510200c03242c078440c108548910019810050424601880da0b40d0b4002304003000e5458020710585040d580003551410707092010080151056025140c10b00030380d6140c62020f020207100c1c84021031841511580381d030400f0410a603038a0000c1ea84180040da07103d0000c00c254003401c0b1402c40003a01b40d1246440d01a407540c403031000c1c000007001c03508054424840000402c105115140350007d2080c081c5031b0b221544c60425400c410400c80050b03000f61010b17 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 215316519 1250 215315269 215315273
    0xc06090609070321020307140a110d050a020111010b03030a030f0606080105030d0c0309170c030111131a0f0c030d0e0d09090f0b100905041107020f060307030b03030a0e0108090a 78
    0x81c204400081008040c1e81060143d00c030140c0c46c620551100030701084c154100980181000305200107010301c200702212003000b100b402c12548002010300a0510f8000301c2d8400c1c019802480c1c0b1600f070340002c2d03002240c50b00c82c40340040d06503000707007000c2004a911194482c0c03111045214650203080181088401941001c01003681e03642100512000d202c92003040100303140c003d941d1800100240301c04580080c0640d050151900c5007504074500039800d06030510030002503130056890a850740850794143d41d01d48406003003034504c1c0d0405880c5441c401c00420107a90030450043c40203a48040055543e221401800002c41d046548140007940241c1c0c1807040090f0300041da2011615107440c049096050080711800401c1071201441d4840b905107204040c0c030b034100d4070b0a4220f03581103a0030042045490714124040c41241d034000e50041890a0060003481c0040181d42c0094143c03a0000d0780890b05d034046840d6038050040440452122071a031850380d0b07402000d20303030f111500bc0e000d40030b40d158075 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 215317769 1250 215316519 215316533
    0x3001090209041d071a1201060509120606091308040e0f010e010906120201050306010e03060106020106180b0625060905010f06081603120513030b060a1215020f09060c060906090703 79
    0x80c007805c0308000e20b211222100b042c806003074459510849000c0b9900b035a40b50780107401584201d00307141c024042c0c038042d03da031044045916485040c014000c904560303105505100c100b10460800c95080b1401c2c800030410102040d0818807a5010516000840d41020305810b814841680071401003410080d0502c00d490b0f01c0d0740483c1c0080e07828203010740c5980342d21005841428400700c5030398062040c0000001c00310350541049044454009040480514070705c1000151000418240e81201e420403044100442c20080c40896200140c810480e1521030341e11002130343c005100c160340c16034551610721400052803041800510611004003c3c64500c1351401180201038403003e0305001000044045460048080720035245004601e55a819140d141010701402c0c155a0f96004411002010403241d9203294001d4683c0d4009800900c1445081e501c1c1c4065030064125504494007480802d601e07403209000717003108001034400740c00c0354a0314507545807a1450040410701d0f164005201003000c5100 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 215319019 1250 215317769 215317783
    0x30903080d02120f06010e030a082a0303010306060518010617040809060f0c060c070b0a150312030b0108070311040614090d03020f060601090b3001090209041d 70
    0x110000464841c40c01100c0e5600034042c461606005490310303030800607181c626041c0e0510504007600c401e08000d1400d81410341e40c8104120040144908021283d03855515001c6c48106100d81940116002441c1d02e103581190021307481140ca1540f140c00070b010318600181105d036511800a40e820596140900080c168102040035104d40c1359000046403c1c041008201da0f250340e000780c001c680e20703101880c0480c10383d4030148840d041409144003113101049501c04071100d07660003c000030403644800003100c004080420003402006540900000000c00030f02244009401a403400252400c2000000d4003001c0c004041800301031030141790f4406203110406903070682d1725903e0010f0701c100903d550020244035a10b401036000e11200007038800c00d0380c00146222120800700980300d50f501c0c3c81f0300543d102913150103103035081c040c01d01800745040c03203550360758000081c0900c4001070810030244418850500ba0032500100ba00080c1820280c1001d004020990b0210046246403038483c80203181c4641c8 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 215320269 1250 215319019 215319023
    0x80304050114160c0f020a06110f0d0c12020f161d07020d05070201050f220b0a0804120507020d0b0912090307090216052409060702060103080901090b030907050a0e04030903 76
    0x40c4600b43ca0080c0180e520f085c00f807030781d80603202d601501d0b142c01c0b018004403045100c043c00c5100f03d03102030254402c081103209004640b5100e654214041d90307601001c1103039030b9031040110710514140301d9015008104c83c0c0080c046a5004c0900a410905070704000b0045e01c0820352003601d00000d02c00096400581140c044046141141d00c400070b51004841034030030066400343c40e003070108580004c01d036200b035110700032404410080c0c8000c2e0348406080027801042601004160000d0028010a0043e0108004207255103800c80ca00b414a82c002058100b1415065400460f004200074907aa010051405c0b6407005104450405d480640004d90310344a40c003c4c00d48980c2c02091401c5644035401100d0f00301e940c03004c151640081c0404240c409030080d6403040b040c0c544c4903008103101c41c0010514501640c16540078021130ba0031034a0b50000c1d0f61241103401e041106806000400120311006180074000c00b01c05041840c2c50402004090600ba401480a0080541c140000660802c040c070080725 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 215321519 1250 215320269 215320277
    0x304140a0209190212010308090118030b04021017070201090c051c060e0c0616020901090203090d0c030e060c0106080d03022109100c0e1509060d022508030405011416 73
    0x285243d00314030190180400a1001601400001c000c0000c10304c06000078043c2a42e42d80c12038410303007541c810003880700d200107000c180c01e00c0003080160609032101f0081208034100300310204859200c01d45c010104650490050759216401010041d041a409004003000c42c2c6507559000d4443d01c021010b24980750003801c81d552a0054401c03120140244004420018402d40e106d4811001d85034000c0c4012004920030441000007151040c407034401d0368000c100d42c8004190103400000191944d503280b030070950501c008407204c0b01407580e0303100091107015071840020540c6468140f20600c0d0100607003104007414018407014140781c41440c0254205040071180c280c0c81e444520407507050807055441d40950070308100c40002e115030000882c031303012001503c0120318040061480b885500074010303201c2e4001400c0000706003100316900940418a800080c0103041c24018090420721542c184003140c400d4004001c100501a007841610205002c52480310f6452516210911400c2c0320514204188 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 215322769 1250 215321519 215321551
    0x9030c030f090a0b04080d080108010c090504090507091a1e1c0305120703050f0907150e01110105011401021006050d03050d0905070f09111903110d0f020304140a0209 73
    0x40e541c490f401c41c02801c240d84600d41e11601c1d00140780c0c4401e0307a8074225004c5020800000f542180522852402d41ba403642da03c64045c0c105070030400540785101003a200380c07040f200003080c0307186144142c915105071690325008074076440050001c40c0310f106011207031035148681540d206407180710100c829030300115901c0c81b60b80c947e490295032900601c202a25000304420400012941650040d8000c904541d83c01c2640c0d03584803541661000203001e082c4800d00070140a10a00d80030701e00300c00110b070381410182d180c14000203003182154400da1208500404900d00d85110f541c060000c0c211162550f00140b0080d418200452030034003900000804010000a05200e000c4d40da60184d083c0581c020281c681340d0340e95001c040030500e90350054003201480c010322401641c0c041c208513a143c0382400d014500d10542100250020a454441810040020410908007a08510500041c6052300e440107841c0c4c240380c1000c1407030940e41c0d00c150340340350301000d84030003d40d039071410036a80840340d29001c50320 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 215324019 1250 215322769 215322787
    0x6070f030c050a0804061b031e02190b040b01120b062b0506100f0806180f031c0f05060105071103031936140402090a03060f0509030c030f 61
    0x2680703205400980140110a0741d4030402080300300a1003210100c1e42c2d1880f103540c008100d107426407050726004001c154200f901c211450b4101ca00031280300e005005075082d8840e03e91000350202c00380601101e56007400c404000c2004007020005001d40b10010640450121641d500ba25460020b41810b100c0e0030310b01c2d044440d25400d41008002d584520284403400002840c00598440040c1ea0700b00d80c06002c00e03004508010042d40050440c0d5040000300a20b84524100e0030441c13411040f0024140284010122180402c0004020120800360b40744039103660040c1d08c0c804c8492944a00e0441da04100a00485a81c468203503180180c001020440c00d540410010780b8510504280b2070340c0c003462030203000f04a45c0159008151504015040041e001d44110090404800182050310200c0303190061103440703003a1548202002004d00010318040e00000010403100d01035004842c6607803640c500c40d410320303283e000300c2e604040840015410962140d000580f40d01a0342d000d410320f6540070804002c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 215325269 1250 215324019 215324027
    0x1f0e04080417030307020c09090a140a120207080c03150408030a090519050c120706050c07030606091a010c020a05040e010f09060e0f0a0f02010c14120a09080c06070f03 74
    0x5110408940100b02000340d2800e80341c1d00121032050250149100c601c080e400c005a40360f100d0894200500f0340205540d988520007400800810b200e8400c1c45e2483c800645105858003401040350010031680e8a000d05039450070500b130a2680c02038225161102e040c0715940215501b20380d001d0410ba0701c0350b0300d580d984401040b0000c00a0070030b100300c80003030007200340d841c01031031143e8000d1050301d0304c0c03101420501401d080400c0c1b4220080c0e0001d5010409144948098400440c0701001c3d074044540c1c036282d100a8900b56003110540c250354190030050b06511100c8058009000e083c0103031001c9450f00050700c8110503129480c040e43d142c0680000c041400e60052492082d160360800452034241404402402000e40412542c400c001d41d0045ca0400054000d404a41c012029841a00680d00446107802400f40c121380d075550301c0c00500c5e6000c1d014400c802c1e4100e070212203d41c40b1104000300401040042e0310002c0704e50001038000d0b101c0d0300c0d075031b0803540c07802e810034140d51084009240071a = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 215326519 1250 215325269 215325277
    0x2130506040b03121e09060a0c0f0b010608100e0403090b0a09050a0b040302011403010b09010e12010507020f12090d12020a1203050105090c030610030f060f08060f1f0e0408 76
    0xe034035002c4c035140c080410503000c0143c101c0301c45076481444c004020030031120480c0f2404858550110050010043c1c0e1407040021240c0d4a1023035560f119100d80c030307664103030300c800b420307003181001c603a0382010080c9034481442800000c20003800c0820841c186030300c0c013070a44101800307103000241c0c001503000c0300140034990f084014240a441001000e0f611180c41c03440742c202d8003007280041d46c0080061060b41111058034140d45519a9861924865400645d09206440d104940210801000581144081c0b00d502d100d03001a0300a00047c0010128450a040e03000c840e5960044090000d1f501c1781d00c907076950009660740614560900c541c91401a450714641c800010002580861051020341d41504214102c510541e12481c15881d103084500c820b0200307d88003a0810031440084100d80d200c2c0e0070200f012031300351400041ca05e0311002c900a80c000c2d207810503a135130382c00081032162a00c18200798503407080c0650208120f070a66003005565102852088900841d03000c0d02040a22255000b00e03 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 215327769 1250 215326519 215326541
    0x6240509010e030f1b090903090915010c020607050c031204140118030c12110103090b0708180102030109092001050406050714071d070311040515070609030305040507060207030213050604 82
    0xd03800c00c102c3c001d400c1301c1c48408881d281d014021b58008181c4088002080d0745194000503c4601503980c0d400c00c20302011401e9000a04005c0c102c600321002d61103001c0180b2032980108054150f07030412a0a0529110341c0e24004003041400700401c00014544a0900482440034605012201c00f11049102da0407120340020300004100c400c0020f41c40b4520000300042032180340020383d0541e450005504a400400010f040742000034005294103108600e03c0e64401c1508550240002c60f804130282203030003d0300314955103942e86c0c0720401440b104d0102071002201e08012018030a20420000302240074501c20b000030f03c4070200c2c11500b08502805028292181e82c4200d4408540e00d2505c8000c507124003815000980900c00800e00c0e1900c070b80a00906621805642850149410217000c07010302805240880e840c0d00380700e89000140140200c2030503d010b13540214841c00c1c1340c140a414418283e110a065510180007000180c956131004071625140d8000000c1540c0d401c00424041c05e02d4400b0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 215329019 1250 215327769 215327773
    0x9030212120708090d1d03030c06090303180f07060305100e0412030f0c1e0302070503040f08061014010302070c0e090a150b061c060e0a06240509010e030f 68
    0xc1400c0030321042240b4451082643ca000c800d403188035805458640d100041400100c0904100250100508200141540c05800c49140580f100c4020381480d03c00d03a818a081c4c0c01c0001072013901c00541c81d4035640105001c026149030344800c1c2d034150b9244941d115079014191950000740d85c1049940050000302000e00300c00b41d092a040ca40082d021815078405804249019410b001d0020148038640100c80c03552500307008984d401941100e402c882c0c80500c3c1c101034081021400207541403000d00000d11f690b40c8815012800c1c200d503903041940c002c1503814003064040d82040b00743c580c1399500340c6420b805e0900603518451410842180126030304401103182841c0b09000b94070000140c411182070244a402d681e0060b1180400186d400ea0f0118aa000a080c040700480305c07241c07202110882d401c004001009641c0f0b1070004c0050343c04841005582e40c0c2d6a5042080b50200f900d4049814900281980101040a8094540d0190032001410082404003400d016202081041091041201 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 215330269 1250 215329019 215329027
    0xe0d0303020306030d26061f090302120c0604030f17031e07030e100e0115240918050a0b06180f030601080a15021903240302060a0309030212 62
    0x4000c0c010394801e541c02030182c4203448910708081c2c030802a0480703a45403820f1003080c41800b2542e50a0310040505541da210351602920610201090034100c486010b54981000040c07450040108618410100d54003c1d081015690035690715841100c0030390b90f0056a00c42c504416040c400642d24042800c01c00021000003070000b4521080d40221003828400c1145605580310202107054989100480c500d0303a00c119506100302080b60404204052840d00020728044550201c0c03910610640c0710159141c24400e000d00c0513420041251810a001e04220003054070703007168003103120b905805101c88030340c0d16404200c44034610f400442c40701d00c0084c071260300d401d160f6070400183e8030b090628900c140d1800407400340d0303414040741030790484910101a0042260507100c8088051760041142c040030760070000c0c0d080094140c1e000d1285698140d5002802d445070b0780c640a0503c40603448400c5049940ba03007040141d448804444141a0a01c0c3c00b15000126203426460813410500701080048085 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 215331519 1250 215330269 215330273
    0x2041103010509090106060906120e010603120206010e370c11010b090402030c040c021903081503032701050702040504050a1e11011407061b120c120506010e0d 70
    0x10145060702c0003294520b00f03644400c5080340c00c032441880395001240824008104150041006200c1c81500c280e0202e45070391081c070440c0c2100c005800888503006070391200120543c3c1007003804d0151040c82450452410112140400000c211700d40220404030005000082c40c0e130010a500381c20340d60103007400316103540b00c40580141c400d02c15041c02c0d0342c0b81009018140c034000107854040e94000d0098411204480e0070301c0082e00509040005600c07607441107490405880ea00416010b0003070307540d030380c8074248402020b2902c030010074907900c01e520a000308444901201806a10a000010302c07000c4240000010780f0035020300d00c8081c1d44140f40600300003e003c800706e0512802c900c01c111511000101d20070a00ca500241d00c40a401e140c1c482c0f80b402c01550042ca400010072420561a9040c00000e0399841c007a21a40f03440380d00d02c50951700b0b01c807000ea078107c0c000c202920301200d070500018152400040c1240c84d024441c42c2500d4682020850b240d0090a2948403114040d2000403418228 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 215332769 1250 215331519 215331551
    0x30a0201050114030109170c01060b07030305091606200705030a030c120903030c080903120a0309030f050a14031b0a020a052803030504140d020f060f040c120f0204 72
    0x910411802d05590740510b02c0344d10301840f0f03500303e00c3d521a510049890108505122541041c0d20547e455961440b0206800d06958040c00001d03100340d90106d504c1c904180005c0c00c0450ba10858001420500424060103800501070014048a0046250540c0010702d00500c0c01400f030b804140c15008440e0040c090590004020b1700d0140100c1c041100c00b11000011610310751180300180c0002e485400301400511108010310b8070b0480117040b6592400303164500d421943c040c104c20004a80e49280f40010160000740f0000b00c2012402c105080484204000d8220850041d03002400c110010000d18600d210b5003144102e080321194058466142510180d62031017206c106031140d100d200c1002400c2280001c02e41442040080f031b480380c21501c0e96041d006410060320440c6c4128400c1501c044040f01003161600000d4103a00410410344d024170040c6c102200584101c040060010401002c14184002601114a00c03030707a144504000e030502d40d86054160400035406820b00700808403d80030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 215334019 1250 215332769 215332771
    0x20301060f0b0a09140a180b0301110705010e010605130c020a0c030c0608090d090e0c161b0504050c0901080702030d2412020d03080c04120503030a05072a080c030a020105 75
    0xf80c0d45420707403c5500d496540340d008001c2c50009600c001d9501d410302c503007250402d91420010107454081404040000000d0948010381414000c1c02400301e52041881801d003c0c00f42900e100c20001c00030780c0d0516002c20b102c160b5080c1c0e02d18003243c0b01c00c001ca8181c1d200304007410099800109206559450303140000c0c00307040364401c1200103042140400c41c8100045400c140307048050321210415031400c0c4401103659001004442c2e803400c24041a41e0a0000d00d030b440c039845100d03130f12103d0031007850720000c500b2406641000303009525250803c000d8401d528101c9190b8502400e0442050741c4600080303140d8416416003852072402c001d01c2c2e8148282c03d0507443e0000c203108805003070701901c1c0c6900307050031400810045d40c031405000a000c046806000107030740104681050a1401e80c031408092011401614210340c03541c0700000708030810030584034403500220b1904d032082a032050318102d0100c001c0d148030010901410241c84004101610b021614440480710a0326180c51600c0c80107802090 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 215335269 1250 215334019 215334037
    0x30e0706110c0a0b03250215040c12030f110309010801171903030905150603100506130c080103060606140307050a020a0209150108090d120e070512060403032405010309020301060f0b 80
    0x109017801021819106c4200101440c05500419443c08800a07503500b0b800301a0042e42d1000c0c1032000411603080032036000f070481f8001e45681102011b102c2d001041154620248100390300305100b108c40316a84414a5411a0301000a000000e50007040c407500b42890300303541c0e05420090800302c00030140c054025403000b5000b035054524080154284514450044131070039450380080f10250240c0b106540b0164000c41c02601c007019048420004d50125211000c240d00403c0d00f02004000300056070083d80007034411450111941100d0340000261400040e2204051200c080f031001000782c801c001084660b0740040c80551030b4140202400000c256034031340076001607050000907102c803200140030004c103400d96455005081408200c0001803280c42c05200e8a13000c0c1d20300004150790754040c082601c1e1003050181840d0304051038050101e031038514042e501030701107203642c031941e110740c0e522175080342c03400c2c2000300d044c030740c544006401030110342c100c00c210140c1010b0104880c40c074203010b08103500c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 215336519 1250 215335269 215335291
    0xb07030903061407120504051609020d050105030309010e06030c07081305040c0819090f020301090308071211120408161115120412090305011b0e01030e0706110c0a0b03 74
    0x2030303c0c002d10201401d408885980229042c41000d600303d110b60f43c0110742c018004d20035200e020700e1041e40852220352580c03140c40015000308180c044c42080381726280c0100340c12001140b0301801000085e29000340090b5181c490540400083c442400c184100e0b401c06074000382c001d80c0d07103a140301c0c000c281c40d210380a03050041d89030406950005029011480c0281461480310010740413a580c4e07580076204000080311403050750309415005880034000e10840910a0300d448180745400c0390002c103503a030300380d013030461450500102d03545000f241000c40300002d0fa039818410a075036a0341005000c6204610465030b131418110b00c041e06120825982c1452500c003201c03140b5003c03100e800307044124081c46184090032001d00d4081800607418204450040c1e426050601031541c1e1390300d80c107003142c072000c16510150540c1084200c0d90340e0700c03005501c50701d007003420300300f0241120f041199640e003c0b0b401447d00b440000183c0c0240d400e42000380b121034400051501c980192948501032980d001510030030080 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 215337769 1250 215336519 215336531
    0x41d0724020d0801051507080c060a0e06010e0a0c03061e0e0703020c102003150f04050108060f06010311040602101803050703080703090b01030b090601060206060f15040b0703090306 80
    0x16920108010a0b0716010790f88440c240e07424002000422544060100071103e400c00035100003d00705806041c50b4101c0402408540c544026224259034003c42031111035000540140095840641000c1e048070980d00001032906041a05030b0082583c0c2d0040044101c407004111321000251410391706940c600303040358526071103c400070b4080e402540b003415440c1e0440031290381a4280e96005c582c8070350741481000035011824030784000c2030380203513841e090314580d400e124816400c041d03003040e07200d074030646040125605d000e00d0350392100e1340500740001d0480b82c04080351250703200b80c000502940324400265070b03c1d075036400c01941c0d819050041007040f80c1070071480c200e00ca03219240c2041d44ea8041c1c595501e000b40c0703a9401c03034603075000611000a0695030b440c000701051510fa0301038040c610900b4441418200b0050840c40c1440c140e1165085500c00810444c0d070303440345500c282d5072100648410304640d02d0701404240d680a10b0300800d8003040c0c00b140c00710a2550007004442268002d001c20415 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 215339019 1250 215337769 215337839
    0x2030712060503030d090c0b04080708070b03220201090503030309030405031905030913060b030f0604050a0920061e0717072f040504050c010905041a041d07 69
    0x7554502e00ca441d52503001030103104040c0d512508000c44030b602c40d40c5c0b0441030301d071280c60354001c1e50001d41050f011a444001309110110303041000d50040e03c0c01c01103180c10362424002c209410f0b0103c80d01100c06540e0440c24008590140c624035020b8040241520f48925001c90b100380d0b0780e0841c0c070a2038820310451078922540040b0b500506581904200654a4840d6840c1880a64040ca00f44c814a40b5514940001c0c0240e130b039800341d17009007000c0400c80700d2420b00300100403d81e003002d442c01c0c02d124600341254000a00b00907000c4688000c142d141c2c50b2940c0e02400103151401420619003c424440320001290a000c2c8010041036200780e0716150300d070601d080000c00c240551400102030480d00810184000100218865294040c8141c0286420f01101050070785d0015201100c1503803081c80c2d00381c0c6070b41e00600070b08083c000645e000c11a481c0c0341c040c0100e01600c12403600c2d0003640e80d18401030321218143c4e402d28480c10018100d038501a5a100c02d40180101c25150405028a005002138 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 215340269 1250 215339019 215339021
    0x2505030108030712120c050301061412061215040507050306010e0403050d0203040816120905060705030d0b01021903080f0a020301060804020f03031309020c06010f06080c0a090b0d02030712 83
    0xc16904400c1c011410540c8036900d5585010b410086042800310301e880881c5e448841d801101d044481c0365584948a514102c0e02a00a5182d140a01c029420a01410003c4280c2c4002c160340640e0440c0c4803500d0900f001c25623400c12000c1405903041da11403004120610000081400860b58107404032031f41d5a81c0c40700001070342c10003910000c0c0002d408025506d10700d002500174640141c0540142d6280038000307030150000000401c01202c203610003000c80761103181c01c0000e800041000b607501d5441d0000a44d6520b46900c103803805540c1c526501c45498405034800c00c40c00c0c9a40001c404400c42142e81c03030402410944c006c54140541c0d2600c000026503040650090300e04965030303525a44000e4545908008040700d0944d507050309444180031281490607411004002003210031001079541182d0000c240c20418160801c2d941d883c680c01e020800319500c4109250b11070186514aa02c1d40080402220100c2d9a54000c2e08085e00102c0c00c291625203e500860095030141c6900a400c1d06180d0280 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 215341519 1250 215340269 215340271
    0xc150a09050a060c05161506090b0604060507081306051801090e060f0d0b2d010b0406080a060306050103080d05060103050c0f0a0e1e030d020a0b130812250503 70
    0x2007454020b285503100003042c035000340300449941e00b032190400070542c400d00c1d0048402a001d0f15092500066020603c61510405000d030510800600590f404a000b1038890303c15480382e035003006000600082480072410940724001d030f4801c45404110340d644002044c5400c1858030050041000407625003540c050728100b0225031902500300100e50f0341d403040104e8007440380384680d00300c0c103240c0e038400c009038212201c10310402c500c0300e4038486011a50f040800c820100e000500e101081880180300c40c0024500b920101c910034540b007500b550314a20100080d11030f603440200000d007480008020080010003400f055240e41c40108010307501c200044094400503215000c1e03420042207080c4050301400000c01c0444254104404155a0040030803003c5d020862040003400d10320719070a2151906000240d10a5154030007402ca00016803a03001c8002c4000e40049103654802005070200700441e810b81d00d0b10107400200e07205500c2d048000411030007044802e42500c080c4804299070b02c0c3e01610580b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 215342769 1250 215341519 215341523
    0x3201e250c0b0913020307120e06012909090c0f0f03061309030e041107300503010b2704050f090c010f020c040f0908030a0e011a1f030f020c150a09 65
    0x4e0318107840c03031501200030750002d0102d90801210409041d2444101c0c040e061345240640300a00c1703a5850b00d00125507514954a800c152440413816001c1c89090000658401c00c20499550410ba182d404941411784070b1440410342c074000c0451008084c803683d4000d1440f0703207020385130319031864001c2c440c140458070200402004592040743c11000c50519a026200500100c0c41c4030385003031580d46820210105091805401c140b16031701e408000e0419903c2d000003000d590500c142154141614802503000c0d045006101015900400310440009a8a00318101028100b00981c1c00e000c4658505500116060201486503046544d56540702d0865007640341050380c0031b85800a800802c000203019010700c0301005907103c1100001042031b800045010f414116400100001501d000b582565030b10010980a44160051100707aa11020301d52a0b6241c181419896103c84804099000300b5502c490a40320a20100307942118080000d4800c2c0101100c004184083d510320400d401601c0220b800 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 215344019 1250 215342769 215342779
    0x7060f080a0506041e0603060b090412140d020f07020307080c0d060917040b0a02010609060f03060c120f020a020705030304030c030b10090c09030303201e250c0b09 72
    0x4801072420b42c800c50704010000e00100d031a0648140b4269030108120107402d5040e528882003080005c0c030310444940007025596441a072910b40c072407417030028403c07900c0002e00c5500c8240310f0700185803508a45114040181c110349030240c0030490640c13174010b404102d02a1150610108803032500040c4807407903000c000c02c011480207107543c40e28003424808400300e45850341e501c3d03180c51031104580a417000d00034032110551a4004110002e0a40300c00d98011503916240c100c0900c64a1045a825020350350403480c08556403601100403100c0080070030030120030038503100c201e042d0125903400030010410690b08031800540c540d020103450348224800188540b40781d5508000242d202c1b45203580c03020f050381040422555071041070341954103a01500c400105200400c0c41055050312401c812a41c11007113144000c100500049120f2040e00ea039141044410000115070b11504d0041b10010030703c44503d115001c1c9202c0c070482800c144240c0072540c402c200e0101040007040361050314258540100703 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 215345269 1250 215344019 215344021
    0xb0103050d0201140a0c020f06090c0a0e0402100c0809180106090b04080601050f0307030c0b04030b010b1602091b16120816030209010e0603090f0f0c03030d051305070f050307060f08 80
    0x9044028418021b504040d80521126840e007420184255031090140401905038841c010040021545445d080a100017101d4020300000d41c403001c01c400c01141046c01c05414841141c01e00940d03a00a041045030700000300c1006001031007007007030664100d40c41a00d41e1041151180da00c3c0600c1e00441c082e071001a80520010000f52a03d41103011007468080c0555002585030780344e000f03400200303402810701268009030805c10422140c3c0c0041c010280004002d00349540854030f003000c041841030183c490241a40840c9602c041d1140b40c00110010f40c0c1195a035280d96000100d007a07188010942e0005803010100c500c80f8050b00080f40301c0c00c0311345007491180c6681c0200354003c3d0444800320741000020b010360500e40e00d400380158001c001c0c0800a108c0e0400c20b1504a16068090321900131a0304000030400701910008141c2d09181000c02000c10b4039a241c07c0d400640c0701e4140e6002c0c00300c1c414034100190040360a2543c000380c0e030054003503440c0c09407500016184188a0429180050001c034 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 215346519 1250 215345269 215345281
    0x10b010c08031f0b190309020102060a050a0f2c0a03050f0a14040909020a0b0a0c08030c07050109030504060801140a0e0604090c15080109180b0a180b0103050d020114 73
    0x10019980200d0107040c0580c082103540c8041c583e02074075001194030160014884a11342c4403501d1003001424545014070110b405580003d480d003001511758041c240d03c8502150105a81e41c00c030b20210f5011002c10880c507540402480c0441d140f01550482c045125141d11502581c04034032440b10a81540b201403812a20000b0220541c0c80582c0d81000c00c401d00c61000320400d08200100000d1507540408501045a4010040c400650f64000c601c80c00b800c016014800703402009403044607800c182103036143d50360904502e42510441c00000e000e0351030281003404040d04800a882030340c2043c1e46481c52a030f201da9140c00f02d41c0400c0703070082d03024141c1c00c400c0004d00130801c2d1260b0702c05005000820440716507611108403204980201140081003840803045a40c020842401030030141c10610071001c000f0f43e8001c0c11078400b00046c0140107080002194004aa0030031a000310b1040325082c000e03145e40c248624546000c2c04119042d02400740582d07a5584140943c0500b0081d03107065108035210701d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 215347769 1250 215346519 215346533
    0x90524010914010b3103031116090b0402070f030503100e0402030c0906120a0b07030b011b030c05120414010816200c06120601020c01050708030109090f12030b1002010b010c 76
    0x95802820180d5000030600804405c0c03901111081443c02490340166003145009800c020711800c1151203030380005560510f4460494584045a8203450300003440c10b0f13900007160192045040c00342540d04400300070002c040e4004000c44c81403035490703618010942c4548000030342002c10340c0c1c041e60660000480320000d107040f402c0c4c190070581c0113082e900f011541d044050305041c5411400c1e0b0740c201c0082e0030840c1d155018080d40317034014401d1a01c80c48003504046021fa030b40006110282c00c0000440d0410100102000045101004075503d10b8550b980c903c0c0a01c040100c1507241400074004c3c20115082686450030310003406c1161b102c0902180008440d814880ea5030703007000405200e09035440c04a901d40000411b2000041d41c4840d4451403c1000079240000f200c0d440340c100700041000001040107241543e0541362541404981c031101400c14164028041101400302104501901511501076200d201401004d8646801da01207017102a400c841d2850318a5000c1051100300c14001603107 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 215349019 1250 215347769 215347777
    0x8040f08090604050d060c020d0c0503190516150f0228052709060f030604030e0a0b19020106210201140c0102030f070221040e040501090524010914010b 67
    0x6042c1c01d003007a83e2100050030204040106540c0e00d542d900c0c2414000364107110718048041182002c00211130a9900e4aa13a0310802502d00c82120b808c0d440024018401c0007103501e030b400c80e07141032814541c40d401c1c4500360120840030000e03550718049800b48902024001d90f644564101410803011003104065070110610a00010802c0401c000803007040c1850b035041c415010b1803144510082d03000d00c1c148006800c0140c103882c4210b89a03401001c0942c0e0000751582d102d03500d3f18005c40c40400039004210440045c1d004582c038000081940d5079114241000e9002c02c0000354000e00c00b06558038003282c400500d0003500003400b203d0740040b4001d940502c1928003107010740d40300545050000700089013203030000e031021500340302034005104006604020b60204450070080c58544030b04020000d43c0a44540d2041c50031450301540002c0a006080d809581810741010580303800880e00300c80039803d550042c0c0c2c80941050608004100165141b01c0d07020413540800c90040f00c1d9007848046070007600 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 215350269 1250 215349019 215349037
    0x91404020702011101110d0e06010b032d041a1b042709060606020708120304030e030f01060b031b0c03041e12050106051302031303180902160c050108040f08 69
    0x22004e10402d58120f0244119000501c006002d1034950660b016200140d40c0001c0b0306251507842280103200c802e1082007105c0c0c01c9040041c80005d10001c44010341d000c1842c1d80360360030a180c60f070300403c402e002880c5030a200c9001c410081003015070b00c0062a050a412407500007107803040038030090180c0d00c00895166104020300b0724480110001d401c84406840aa5204503900f031740740e0104000068040044e540501840b5000e00800741402000400e0b50100070300160800540980c2032405031800d101642401c16514001c0c400d060302c1d088544810f13881034035061600050a000e004c083c44010090310074410180015600c0c003860000c00c04403518903240030900e0068103c10001c1d000103c114019811841400041200303480c4c02c04004151540780754085005004000b0000c28581c071000b103040c400d0303250500f0011804840f030003020009007074106101d12407001074003155101303c0120a00d441031150004032103441c2ca407401120380703000c15a00101818a41213840740041c140001a0030070b80 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 215351519 1250 215350269 215350277
    0x30118021018031b06020303130b100506030406060e0601050c07031202030c0706030b040b0405061f0210020a1e111b0619120501091b1215080609010c09140402070201 73
    0x14040030b0700210314602d5540203c844610007100400107800c00e1010304002d010701c0c0007441c20340c5485501d0b00d65954010310000e01090810001440d2031411007d40780251201400440c1c69103040e140c041d000b01b1090040300d0801c1c0e0410b000405642c8200c00b01ca10389001c1c41c1c0a400c1c001c0c03540e0b403886a640c0b60110780c68190300042c4021001001c081003000010881e0b40d0300465050b00c200d0070301045512440b00103000718146003c1041c5a2584040301c002e001644000410700b88800344101d0401e03500340c50b00842d071400000c0c0b1608140d44561400c000c00c10351440084001e1140e001910f005210710314800c203a40207502d0312801181082c0c0c0349601504054101e5250a100c0d070302d0803040344003054a0310b0120b038500c2205032000c038075440303698050907401d0820005500303108604540c203100b65000070204015002c1d04207042c103082e04042d001c0d40c84207841808440d00c802a0a4945604903005082c030745c60b01290350030151142d28940c08032104003040c12450001c640501000c3c0d409440c041e4144 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 215352769 1250 215351519 215351537
    0x70501060806070810090603030e06181f02100c020607180b03010605270f0f040b0d121103180f031509010f060506040b180d05030304050c09060301180210 68
    0x20010601c0b0b043e1081d03901c1c0c0d844007071500c3c242044042d249a0354100d94a498680b030402c0c40060381100c1c0c501c10341e15080b0b07a410b0303c4a03140c12005003204201c500d81600401e9804020b04000000407005828004540a0f2070713240700d0b44c03592034003140d015410b4880140c0c8464042070080d40516a00c00c050144804201c00d0a5150002c40c0400e50080e0311800002c1c60008449249000e00d0100a101c4400c505a1b00c0c02074218500188101c901d005901d0310440003140c0f84c800720754880d40003240c846805002c03405c0310762850501240540401002c8001b2821600030081451008400c90304c02c0307c0004260080c410b00c01c814012607400318030403e40c03d48100e1840d44410b1034000701c5580314410070000803607042503940c100410369440340d0100c1d00803601400700f441410151400c1e1506c60101d07800f1a400d00c0314120001e1740070410402c014140303000000c1480b061140c08140c16010080a032281d004a032202018107080303481e031118035601403070800007071401460840a0001240c0461400d0810 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 215354019 1250 215352769 215352779
    0x7050d080d09020a150905100f0212180a030503040501080f160e060702040906050601090f03030806100207030b01140117090303071103040801060b210606031602070b0a21051b07050106 81
    0x714010341e04880d001b0030119034041243c0c4c9018443d800c0300c0103242c0303408101c000344000e0180d55500c420200c65003602c0c0100704100030000c3c034110b46160000c02002a02002c5e41da04100752290300c180280c0e400100ca0b540001d8410046d2030103e80510485120140303503c000b01000c030340f03039040e003003145510030810400d080c05a56107006441d0718030700910002406040000c0007611198060307114001403d5160b00070030200e07410038029540404155400c1400401c143d00403400e160351900300420074540c000c004a0781002c0007001c030518100c2a01c4c0c1080b1042c84100e11070031180d08a1f6103081c1d0f40d2013000010800c03441090007071200b1a180007200c5c1071030b840d0003883e400d407400340e00251071800c1c0c04180e1240e060071240d51001d005413550080e1021341003007004122584001811081d503d4440040e100b44940f0810000d40100800b68400c1e443d6418403100510034200325603c8040310030030110040124010b48141070003480042620300300340910b4440e051081d04610800e030313441d559810700024 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 215355269 1250 215354019 215354039
    0x1c030302160b0a060512071e1e090f06050607060207141e01050a1404020d0c030605070c120f120b040e0f0d0801120506010911090d06020a0207050d080d09020a 70
    0xe11039200345070b0460703a4a841c1a40e00112101540454490812500c12042c90200441c1c14000d4444c01f00d940c609040f8004421420701c040d541c89004440d840c1c0d80c4946032101c05001c143c0580d03c24007000d11a1501010048013600c003a80109a8401c104011510000e0340310341c02088071a20518840f0b403d02030f1910000e0034403120300041600b0000c04100c140000c1c0702032107034540c0000340060800403900c000390108580a00180001e0060300e030201d00805115810070784000841e4005001c0c0071a19111200070083d01a840d800c442a12081035045a414055000404030020903550f040321245401d2112020300300349900c00342c105503295074840762140140a0007421400300b1f4020400349444000040c164501648030400e0000c100050f100050f5011a000d81107900381c4501080c40404005041000d2042a6125038060154403090301005182d4018044d4108035030251050155503d06011002c01d90000061654204025242101d121035020800741400034001500d415141c1c600c0f00 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 215356519 1250 215355269 215355307
    0xf032a0d05072607030f180b070c1203090b071706060306120105040609170a08010e04060b0904030e0a1706040602070f0f15061508160324080c0109051c030302 70
    0x1020f0000c01d0204981a60940a030845518042104200c5240c640c070200d0324a500c1000010080400b21004c82c982e1449400090b4415420031140c42c45020382c14800f500501c0e0002007206c1c80c1000f1000901680d02542110302803011748040f160055449004208159000905203a4040b10685148040090911803180704501c903100c00a0001400d0a2540c08150380e1600e484101c8000c111040c0c9450380403c20318119034200080c944031b0703240c2e490110302420b012290740da008080c4400708030a050740310101202c00b43c4182c88005205444400ca120500796401c809a400c0d88101d01180000f0780d01d50003800168041e10500c5d038140075a55641c0c0c49000c1001c02903408082002e026036107407200780725460003841901034520060329402d0028051410080c458000503070080780f060303059070080c3c00002c026a4288603800080750003400c00740b403140050003800e0491154200c4000c07194000c0080c0819108010003030712541d52581c2c00c000130ac0d5010340d41141010f800340b0204282c0c0b40340c20510 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 215357769 1250 215356519 215356577
    0xa020a02220c050c100c05070b0a021b06060405070f0e0d080c070b0703021005100905040213020c0f06060f030a0b0901060e271506060703050705030f032a0d0507 71
    0x20f5551003154031401031400040054040c080c070b143c4040482c0481e00b01c81100e520a0703001f000c00c00700d5941e81c1042ea0090003071092107841d40036580000c00203c600442d9051052908135420841626000e07000c49004100c001d0700e001207544003100396150f19218044c0001d0302e01c12100140b9200807061050f0808225034449140c404000c80c0310000c068050002c9941c506001404205c20303d4141103400385840d842c42040440359581001c2000e640b101d29801d400c407640d40c00c003590742c0c5200450441d6145072284078800075005d1a0046011032900da20303c0c8546800090040440713041b1500c0d840700c0d082c0060314800096588680014800411001d030500c120302080b0f41d4080020488081c3d65010032503072002c0b0030343d004220703a0b4031580c52251000c0e401c000191089501d964091038162114443d009005d0100d10010801200c814400b4000354442c80f103060004043c40703840c00141d4011141c80d800104144001c0c440c0300000300392680700c1c03507001c0300c0d44ca006201c041510101c522880503031001 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 215359019 1250 215357769 215357777
    0x402090a200c150f0907060f02010f1103180307050a02010e1804081215090712090c030605150102030a0509010e010e180a060b0a050f0903030f0c0304050f01050a020a02220c 76
    0x2403c414003883c400d510ba110240108130005498000c02c800e490b0441c0380a0b080c244800700d070038030040c0f41c401d501c41240c07181d4012081010b400d141d01030380c6c1543c10407200e81d24000c26141c10502466008402c0d60b10050703000d401880c2c07150080d801960442c906204443d08089500d6108550405d10304150340103d0240d041c059440c4040c0b940b0380b004523801000f44074142ca0700150401035840d05481141d00880d10300d400c05429691081d000c024013040c050141010f11600c4021041c800366a002d82e010386042802031604544002c01640c61b401840d0b40080410014001078820b0b5000c0c80c01d00c0381416052406004550b5240c001070041c440404180d0500d000001c00c00202c0081440389101424210000604005500300c1c0244a44035850191540140224444c103180d141002070f221800c68105001d51142440452070b642d039007151085074818140001d5885c03041d4025021070700c03090f0311603014140707402c129000c4c80001e12001024225040300e0550b00140c08404d0b00c41c04201c2009951 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 215360269 1250 215359019 215359033
    0x90b2a070b0c0d050403020915120709050a1401050102030406051c050a050601030b010306080a0821090f010f06030c091d0d020304090e0f0a1704030203030708031e0402090a200c 78
    0x1181c6400c3c82c501441d028008200000e02c0035075641c44081303034840b00d0301a52914101620001c5020042100100c01c550710038250302048203c41504514864000d4038000c00c101101114801843c0400384907243c00350b00108014030505202e48020b20740c2c4100c4540038844086a006070400311034040f1602c4001031f89c2c2c0d07000d020071981d00d8000c11341249000d19060200d50304200e001798072104803210080200000042c3d5241d806130b1010852404000c030036102c07444d890900c0703180c2c3c1c86640e180d0302081c60703528003541400303944180e00c15a010340b504808202503480c02e2180c240300815a100d41201c0300d118160786c01040720820400c03085e08070b640780c0c06152541d1421103940d00b0780c1c3ca9500000c015070401202c2d000d6032180041e035040d91640ac4000100b05010301e005581091059400203505400300042c0d01c020701a808005600801120880402c41d0080c240070141800741074400075481a242e0780031411500042c0c100c0700d04118804188201c20041e82c215030308980c42007100b0740080e0010300c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 215361519 1250 215360269 215360287
    0x52502012304031106060f060a02010e0a12081f1205030d0c1e0212300906070f02030703020705090903041d042609040510030803040b0105030d090b2a070b 68
    0x515184c83c0b10030510003400c542c1400000907208401031000d4038043e1201062070f002492003504421240000b060681d0b5004a5a04091151090007103514010450340c001003804008000101e00d2142d00400303480c90788505202c550103c0c207407400ea040c1c60a01c020311040340400400e2142d002d140006468054800c2c1c1001c0410640d4100f12401c01c3c1590000d0440160201d6a801100c0600c54007055820541040020703a104070201e081c0b01410419002041090319800024180d0046c422526444030140b5001ca089a880c800c05100600607040440c08004034140819210741001182e0166418035031030300b882c0440e0700d80112211070001c04041c1800180010740142031490054903001d5181500401c2c40f046240c03140d5044a4011540c031740010311158144101c98000d1584410940c0c1d8a08040c10141a0034200380901c40c4280200e00140d51180c0c0224820011101040300c50b40c1000c42c44603ca84002e24065552258070201100181c04c0b01000d02000c809000341c038082503287c81c944 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 215362769 1250 215361519 215361527
    0x1050d020c030c060103150c140f070515040b0a050114130e01020f090901050607230a06050a0b010801150903060209270103150207080301030602070213150e090105250201230403 78
    0x3c0d41c6031180601d023041c08241d00d50b00610f40469642c0e0005043d5981c0c03000741a0383c9280c0300b0600302611a0143d40c0300d0390078200310b0750141c80c01180141c3c0c2c409940d4960f094008100c42003031061001182c50182c0942c0c0b90b04140308543c0031801100400a90303004800005801daa1001800040e458000944410036142009130306016180656006003440b0b0282c0d10b0500204a0320040040700107010410b00d0f0403170f400c000b00b01c2ca169005000b071005080007400c04020b4400b18200310f02048400c0004074000140050b4090141d1040e620b80c0301e1940f45445420003540f084a000782c02c503a2040071a000f508410440300d00d0300c1d0300070340d50381d080e0744c0342d030900340c401703001491004030312600400552001c902c030300701900e0540c0d13045540169680462f00c00201c203145000c0c0c1c51400030f401d0840f004205000302c075041c41210001070701c0702d4056aa001f240b40c00c0364012559220007180c0d0300320351038400c50201c18140059000e40000143d420000781160a082511940007c40c25116820003080643c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 215364019 1250 215362769 215362793
    0x20f0a0e090d021605101101090807110f010309081c06080a080301080d020106030f0b072303090f060f040b2a0a090b0703080708070c021503040209180a0201050d020c030c060103 78
    0xc192813004868100740000c3c9041c42c0d04064641007121922428040c3d01c02984950405030303004240581d9110341d0302d4001c0840d42d03003c9980c0e100300110001c1c1d41c9194005c0c06406010395021900300d1134080742c0c1c584942c408440f002c0a61a545d505c502c08100408100301e038075281c03030149a1064880d0315001242d4032b00342d0101c08900c11a410138500304001000c082c880140140d1002040d04540c0c0d40c0c90703044405d075412005140c00070520031104c401d6226510011401484480140c444000f0b0880b1040d41c6c031002540c1240682e03044100090101e5001c1c1c0d0b410342c00080b000e84d1103402c21300e004200e40700307030025840954a4142c0002c180302250341004008000340703000b809580c1030102544003d0581d0400501c03000603c11014005030a2502c541250b00c1c50560080845401c5024070b1210401901308813400ca00486100c0045408101c007505203504083ca480000c000117107003035004544907001035035082d00d01c640034450380c2e240a01c01e03c00303022a19030400c0201b20542c03460800c10481c0e02 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 215365269 1250 215364019 215364043
    0x105010f1404020304150c030e07080c0d110325080105010f030f120e06070c090605060418020a0e3706020304050910030204020a0504091116020f0a0e090d02 69
    0x44142000c00c00700300c0840c4851480002100c1c01078580d41c56051500340112503800710605640781c40c0c0002e01c0e0b690541e1101403401103044c21145070a841d100c4059907444505a40e66001680903000030000d4846036480000c818082c0c15108489809901d840b00628081c08070492265054002e0110b00c401744211401420038407003001c01f892954a03036503501d940d92400581418590003808014074083c11400070f0034100070706400d580d00341030700b010340c4488914000c0700034180c00c2603400251440d001d01a601500c0c04250000c1c1d000c0211500c4a0007136000d44074410a200007040c51070b180783d544a140c0070142d481b8507000903000d5218036235041c21701241503543c208002e0103903080c012030354000184e41c140d8005607040c80e0b440c0c8a0307507001e00d007141300c6500081d88140000382004c90150b02c1800f41045502d045824001c06d04ea807003441e440390141b041001d2170f0442e1840307448090310302449202c2004002414200700c4039203441d50080810422201c2e80314540c0500130040d2000d44c1003010b000c0200d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 215366519 1250 215365269 215365289
    0xf0901061202060a09081603060e010605011e210f0c0305220804090507210608030703121506050417010b100f0224060f010509030a02060c0109021c0203010501 70
    0x26003044522086500390240207400f4040100c1c112940034082c0382120301030b0803032204071240c880c1000003510100c3c03410300003126224100344032080175240500483c41071302c80c161900c81d21048400f500d90300103412030f015481003201840c0b80400c00d0140300c1c440f00c142080036001007012071620844c9801d8600d07407034568040510303010801114034502c00b03d806401a166941d106c985509042c87d031154003807a00140d050f50724001c18010855003140c801e040280001d29940c0c070b060706810200045840314840c20310590010062000080c0c843c0070860f0015604110010302505101d018941016040c4c1014003c9803000030240030400840004201c02511400240001d003400004502e064414415140c144a814050006814024000c04680c01d11101d030643d400c0020070b40b205040d54003a101c0c00e0081d1480b212440e07155214601722594001d000e801003541e00750b19400d010303c581c414003d40b07815550354100c2c40300590300e1a0b0043c0c1507680d90315080380811803500403d400c441c810703840140c140c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 215367769 1250 215366519 215366531
    0x3020313120b0c0307030f1404051c020a1b030503071b09060f05060f1603030606090b190c030216030803040b010e25031d0f07091512080c060f0f0901 66
    0x540c0740c030b040690003a900c510050710b80c1c640303400503400b4241102c6144c0c6041d013410303180d2021721b102400042c49103000c0e0b02241e801806022040c014800602c03440d0740142c001c80600004640302a4071014800107a107959202d196590b219142980c010140c00c4401d19140019002200080f4203884050181d81508120441c9020061084040c941c440c0c00e000b00d48c0030854401049141040d2074a0a02c854500381906d0041d203001070090526008402c04954034140c040f890b07420300020b84840c900d050242c2c103030300c1c2c44001c4107a6000c01040d0044046200e0648003900581840c61400c0c0114401c2038450348a060070300e0500b90030001604003084000c2040c08002c0100803004141c220000000d9288410b1803000e0000c4010b00080d417403220040c1c0b00f4503c0d5040700403000030510141400c2d02d040e200b9454448021000352040762004c040388140b556828054021702a0032030304500d21415440303160620724460b0604194044808414450b080010010164854020340b42d012001100800076 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 215369019 1250 215367769 215367773
    0x51b010e04090206160b01030b0903190c110a08012901020a0206030c0d180b151e1201060605031806010602061b13032a1d040515040302031312 63
    0x42040e050441d116540301c1401000b951030315000c8450008010f032921510320160b081404070f0302400e100c101c40c0c40309618005851040044292049a4400c400e0310071001e4080d64111450200244241e4820340e000f42072454550315410740c1402440d894002040e0300e00c2800e0176140a240d040d1074ad802c900c504240818480c5e9000ca010f0070722a5049402d60380303a80390b171007007898280078166410300c0f02868810042d04800820110005092050446954582e00c076402040e4084154960170b4016601251000c1c002c2030245650400400c09041c5102ea0301e504815542901d800da804900810000012701030500140d212103580015040010501d5500d0003074000d513503110090120b120000c00da200e0f00c3d03512000004480341403250401c0c0c001119100d007890000550344035040750190782004050300c0b43c44003c0c080441240e810300035601c0c8020f103031060f84640c0d10006004131028010655079084200d0307105005401503001b94011600e0305101000076484018a0b00003034440e0045c0d45003400 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 215370269 1250 215369019 215369027
    0x1020309100324030b0a1107020f09180703230a03050a0c0606170d08010f06020c040509010b09070c030336030201020f07080d050a060506030f090703140109051b01 72
    0x2128145190000d600c030403440c00040e090304848203403850b01640071000028032490030b644a011b0030314050104031220483c08440c140788201a8020f40100b8043e40188007031a0149101d54002020b148500031030400c500300c0350030b00201d5001120300d07007a8850a9402c4422003024170074543c1d8134400400b83c3c20002d0b20007420314003801900400700900c0441c03100800c15103802c02002840c1c04d004220032411800c2c0c100340c0321442c00004c580010501c6000180d407204510001c000c4400580191603196900d03010b00003d8000102034001c50741d00c4002d407800545544502c01e11036501c0380d44204042015140040036a02c1e80c14000202140c0c0105403204a0106100b4080b440030541d980c410340c0741e0601c4d040e4060700881000c0c15400d0300102e0a8010b01c00c00c50300a2400d0b02c0345410070081d6590f0001401c0c00ca41050207540c0d00304006100081010503071010494003c2540700031604495a00d0b50740c640249154051940d56035107410780d40081003030401185401c120031202c03000c504d40c402c1000034 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 215371519 1250 215370269 215370289
    0x1020c060d1518241512020403120801080c0102010b0a1401110f01020403110a06020601030213060b2803050c090d1401050c121b0f0d0b040f1a01020309 67
    0x44500d9a40d240324805486982c0d049400030308a051818024802c00303503503040148403010b14216440f6488000c403c08030214550041640c03004000f0b5085803212100441e0462060034052404d15420000030020500324103155004814980e9501c5480d0304010070b05080010a04d0060705682c10030807003c02a54800d01400103980b0042007071001c0d5410034004071843c0d00ca6840303124150154410030004094190001d0058070300809107150b44070301c43c07424001460050b100352001a04510010703c0149400101000300c58050140440c1e42074a03030000807030039440780744d00f0b20b50410381150240e070088101100600804250404210b1490204084a624407030310251074420740d0079000c1304c001c100103010084906080d00c1c008112516108166038500d0703201040095110301411700103148180c01805002c10703148103030076040c1004926a09011a60400e1500088264490f00c1c2c0314096112445204410000d00c200401c0c00712040c144a4403c0700452042411500200540c11458542001c00707 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 215372769 1250 215371519 215371537
    0x1710020f19051204030207140303070804060806010203040806071706090702070b0f1227061603020d114509060f03100501180c0c06050601350601020c06 67
    0xc0080710410901c1120544600c0c03484805200165061200345640007580409443e51036580c4582001030008066490040b54030007000b5000c104400c7c022640b082c846c13240c000c60103004481c2032a868403445410300310200e580d00006010300580100305440d0342d440c1d030340200b0143c582e402a07003014a03009480b0006402141440e0301c0025040c4160b0390010100c640e501e24150004085040c044515400d402411842e50003007000401c0094a0940204080c0d003c2e10512480ca40b22900c0a8810b070080e4005d2140700c1d040c155650051003144030020000d0040c04444961503510822181c07401c00000101403075000a01746c040c80c01c544481c10381c8041210190122000302090703554200082285200001c015050f0151035040304442d030303e40d00514103a032444080c03104000102c072180d40454282a010301c0026102c400510040344565000d1900000c1c10324202c40074102c0108038120110300d02c8240580001cac003103480c0c41442804100300380c000c0d800344050a0f00c4503c20000902034015101c0c8 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 215374019 1250 215372769 215372797
    0x708090106050a0e150604080a0803090f03040e13060f0e0f0d02060606090112111909050f1c03020c0a0f090e0106030803061201060315050411010905090703020f07020a1710020f 78
    0x600d800550782c81b02550000e01d04101155501c04045c03810a80036001680c1c4400301e44100440d0010004011096500b41e44120002035402c1c1d481c1d440110852214510176100c8a54503a0740c5003201c80f440c013400d5541404080140f41d000c4030351461520b003244a45110045410440c188062507a48100b1100d480b0400d19025110205101a120081c0003044041039032720000180f81042441010021000500310b48510018603900d105000c0000004c20040d030344809001d4402000001044100c80510300070701c12181c035000c01300041002c9a003a500404901e4800340810000084140145614940d100e0700a11245146649141d62400003030b10252103884034007a80300307241c642540080025600708003800e40d0361070018914001003809440c181c815140244140c4115405a52070310100d40e40617140c07041340d949484c011002074000b849884000c44c810002746c40540d6540220101074a0710310751305440000040d0005244c03900c1d40320f00d0040c0500500091324124140020707984120300c4004 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 215375269 1250 215374019 215374051
    0x6120507090b0a0e040501120b100e0a09050307140c031e07090209270f13120318020a0b041d090a0b0402010309021f02010c0c02091609030b0708090106050a0e 70
    0x110a442c4c454a002c03007141c0051a0000010711b9001504921032064000c000c00300c129154001580b2092421303015071003184400c81c0100f800345603e0341c000034004d0f0065080e6801e00c3c2030347d5206150607038048081c02195000c2c207401c1000345030030301888020110039900010f6445101541a0b103584075486480e003d6a40400c0c01c024548800200858185c0002610703440f8107402401c41801c00d00c00c0d503a13036011801e03520010f8141d0184401030b50308540c0206844a00b0360142504601070000480442c0a11209484850058442ca80130b031015001c040c002035242c606052078485211583c101440e001e0700720130309210b680c08001c10441c03c850340016000f055581d03240016000f034a21200d00035007015010083c4640e0b0703c0d556900d03c80d50050703075000344500c0403426000c40c0c9402d00184042d40c4020054042005400c000d05050780045a03420840744030741d526241c8000b0305500700e4115020441b00e03010450080020b214160162a044500320035480c2454000010040018880a255a00c260f = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 215376519 1250 215375269 215375287
    0xc042a0302070510061503020f03150f0607050a063c020f07080a020f06010501140c010f020c070603050c0412080a030e01180303050f0105090f0a0e0a0c06120507090b 73
    0x3804641d02d043d0058216070490003a1025240100054801e05540110300d43c540c0000760311a008881c2070091620b0b9040c1141c5071600f440406050345c214070380e03011204002c10611798580030060139200d8001c10140485d4442800e0001c290341d1070401510500d2041c0703890002c0c1c0c0c03843c0500c038101880000c03204113449400c03203003110013071040c2c402d00324100308045400c200308400200180390901a85d030941d0007032025041e031175650346428002e0b030f0f02054103134a000741c0000c2c1c0d000140000e06814400403c07031261b0003080d20700b20307030240c00c000c3c1070354200810520216405000d09600030010b13685051a241c80c00601081c01008440010416000010307440c40a5200e600046001c0621030020481546d40d0000c880000c071450000b200801d050800050840f460462600e04032400640f541c80c0d240c0d00d1044c103508400380186032580b030701e994030604000404100589140749110303c11005209041c41c07000f41c2100c0800000b045258108020050f0321544040e911040307d0200581c03c0d11001d0390 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 215377769 1250 215376519 215376521
    0x30c080c210901030e06060f040b040209040207030905100908030912011b08090c010e060708070215040b07020a12150c0207030602030c0d0b010507200d0b070c050c042a03 75
    0x1c1c0d1000182072039908050084844564001c00c242d01c02600d04000404c0e1004002c0e44525040310754a500c034407404040106420140c2200301c401380014001031070035092000040803a00711800c2980000d080080c14810381c14410401a1000034508155583c14508440c10b41c1c2c81c4208901c0a000d10034200407100600307425040005044190001554082104d4200804108003122551724034410302042c0280c55014980005081c09c000e0241d5241800355110780d0b455500000c3e040340c10252410881707207035021403000b51000c0c000b10807406030780c2c14190040217900f015507009544078024100c1584009070100c0654071494545500c08184410100000d90814100d50300140c075550001041141c00314211000704210921000c4c100107a101010045400b4019900000c001d1b5005007500720312041060b0034102c5541d0010803000342200281c0d105105801d0644071381c000306403035001d0a000c001c41130158501e0180181c804200c04441c294803030394402600405060a482e00510010303406100b = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 215379019 1250 215377769 215377783
    0x60f0b27030124090e0606100513030303020403032a0b0402240301080706020d02120903030f0c06040203100b030c06070503090d200901060e0907020703020901140913030c080c 77
    0x10007002081882201101e61407000104081000041014807020600504501c2181d0a546020000317100550350603042c0a028000000031000b449420b0110315502d00b0071a03851409588250750240c1c6591640c603000d4541c65078182e200001ca61400720032994010b406502c140c1a6070442019800c5032124004103101800c000f4000b060000045440200404600019030484070030b1001ca40131945e40700343c106d031100c0882e560880107030040400c413851800481c1c09045100e0000702600c3c0b41003004401c60781290702010442d00300341c012000704420342c40d00344190307044184070400c140040740024000a8a03883c1c507240d20303442050045003100a00008200303071504d80002074001c0e0841100c5040c550200c048c16076500114070010040342d021420040e08086c105e56003a112001c040087c40c00b00200b000d8001d100f001188181c50000016a43d041d94080c02400482c031064580e00c0e0f45003e00c0040300004110205c9602402d00070740c0041c1e8860682d002e0160021041d036100c600c040301d00ba0400807 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 215380269 1250 215379019 215379097
    0x15080609221704030b010806090d120b0307150f1119052d07090902010801140d060c11070f05241b030d05070215010303050c160b0301050301060f0b 65
    0x20b4258100c0301280490040094900410070880c0b680e0381d80440f1030761400f048442c160143c0110f0140100180120401c4180343e02e0000080313100309a09001c44d1074812144d1049030100b14005e5115103403500710340514911260ba14004003404004050641c2d59a4440d401000a9003404190400d008040c08801c60811000d4008100c501c500380100c00002e1070b1750100d4401d13000c2c250340001c1c1000c1d14840c040e0303060340c1031b1101481e40c1e10380314416119181020313941d40c2005010007604009001445115070b289907a40780ca194507403080180919004058102c100100d04941c814407040d541e000528041c00001641000300c5610001250311901800d06250038140d09400c0c034002d900c0d00800a45140c000307006040045139552041207a8910320001c000008030040001440400c2c0704000034820000036a003115034141d80700d1a03101078070481d41d0103100040300c003100511451a0a003d960000c001e12240c80b83c4541c1003450b4403800344100b4520070950b00c8861200c008192101514414800c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 215381519 1250 215380269 215380283
    0x1602120409060e2208030403210c0801060203040b07080a090819260d09080906040e04020f0a0303080705030702010b060304080d0605030f030901030216060606091508060922 76
    0x59803072100300c0180c0b0040c0551040d180c90755001550700ca90030501c0102160b11007125070b0702c2003416292070f10141c0c0041d10a03000c00c0700c201e041c0c46403101c41c0043c07035207021500c803c0007581032a42d2000420074141a0010300454200f00010041c008803c0262080f050f0018605961f81c40e11240a450f80200399000c03601030b019000403180308003461950079003842d000f4000000390310740c1c4070074003a17074454011304c10010510280a014003001140e408441d5180c03003210356600d40f203052000600107420543c46920305c081404100003c60424184c80442c01e042544d070500040d085640140002e2401000c240c108030000c40061601c920035085540c51030000780c911030baa0308081c10300300129403058002c00c000d00e080107000500b0781000545203003401c0e220405035050505010044020b0342c440c00720600c1c04211401c98002048803841900010242a1100d22040e0301d40095000c0f01d1188840990a1164040402c036a549541aa196105288905060746066190606a880000b81c0c202405103 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 215382769 1250 215381519 215381527
    0x1f031d0a05071403030304020a0303030c0e061303051c05070f15091104150602061f090f020a080c16080a0c050f0c130605030316020a0e1905130506160212 68
    0x1101c000310700c1d08160340882d0121100000c103c414540c0d07921098400030341110319604200042842540042c4e004405403400d040c503082c0640004000e60080b005480e90404580c008104002081242100c000844011034030011800c0c00090101d019010020b0f00f5404940e000f0300400125800200c8405a1040c0400a400803070400300000110340c5072072801146406949180444555451001c86900d6801420b65a07511080c50044481a800b00d000d0070465000c041a41d218034085c03c120f04803120340050f12450400300c0141950400b60040e9640c00e81005401c001040c445544c986003a045045155204180f65046410300705042010341280605200b21090740008200e0105520701220140491005100c060301181d0007445815403540c010006101c48142d81e070300b00031000b07000410b200c000595401e035a47e0810002c88509c0503c261901c01c140080030a0f01c100e64110242c80c0001106400b00e40c2c038255900d002800300d0b5924040006800103030352003081342c00d1101e140381710640d0311 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 215384019 1250 215382769 215382773
    0x3070b0c100605030609100b0f06070f0c050109080703020603221101090f21020103060b0a02071d0411211501030c080105100b090102120f07050601051f031d0a 70
    0x45072401d854000311203041071000196850000b4045000340c80030409003103039020300071143d401841c5491006410952290b83d030806a56494003034100e107030144044985081ea649408042c03100c1070303000340d03040c010751074010710a402c0005200d1007502e90545100b0b5491b100c0e25104100003160100d0303142d000000701685000c2082410444070161000e072500007102e03484d140140182811070049440c0b4880441d80c006000c01030001d0842c40034018107001449503218841124194048480c00780982c1c007030b0800700320201e04042a20300c2d1a0000c10401c1c0c2e18240b0b0740d1208a0f9034195000c40c0e12071a4880c4003111115140070b15582500d1154085400d010200c1604030300c519000d100c250b41222201c500040d09a506024507445482215607442c0302034241541d6000a0f04040c0301d40d41144120071400d11041c1c01580140000d0089101e56034031150140b82062414030143c2007140a100e480304c030f20320450861107168039500e030b29003800728084011128604010724250340d00c2040344502050034003 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 215385269 1250 215384019 215384023
    0x30c0e090405160506030c09010c3206100e040201050304060b0402160318030c0506070f06060b0306030c0406300803130b0703050f0c2a07060f020c06160203070b0c 72
    0x103c511200e480c0f044a5030b5990410040340030464188038403180c1000420055881600303400e82c2180b28448104c0c0782c249801a02c1c1c2c440c1c80007a418106449280c0a01d000b0210400401c0e030b0041c2241900e4aa980c2007000e40c0a09a60140c0000c0c14488044003040402c10b00740c02c117002c170610140086440710801c4000c682d400c641d001c416400314002000d0384008a415880701c0051320340003504800160300d00024809543d0041c1c0007540e4a00c2c0b060031000005640b4000d100042c60380255290f00e07030404604250400c240b00a10340c4c407d601d0010b042104441c140880e503d600c0e003c0021072814443c40302c170300d40c00c1400080700610842c000410048115845400e00340300074081c0c18107509075580d006040c1d04840003a204140a003041000003040c58016074001e1072a944400c541e8481580c03c21814600003c0c0103441000d250170106040c80015440055000e800d101c0e0f1005101488441c1d01040e0310303101d00d03d01c80c064102d0304034840301551020440c6c10002c0940e2841d865888055507640740d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 215386519 1250 215385269 215385283
    0x3040f11060919090c0e0d1713030b0402090a02130e070507020409150b030604080301030204090f062f12010b0c01090f0303090b010501030902010e0f01021221060103110406030c0e090405 82
    0x105220300c0c5c0b4502100c00e0b03109041b540c1d803810018100d41c0d20b054003516022651360b821a1001d607942800c1202d0ba82c4c4803036440c201c1004500c9a0a0640f00d0b0070188101b02410380028070004285205000902e9a01030322281c41781180c608100e081c2094403400d0080b5414403412002070340140c04c1840300400c0020300c50310b1020289018501f0004001e0b074004042e2145020303070f0080c0030702c6000c3c0018005450503038041040c0e180301c0c1c0d680c40c4441106a8401040c0d94010b00c00b000e08650911004190000020b180d020000000e20454070340303c0c00601f2084000c20601070120310410104110286030000d60054001c0d0b45c020ba0880c80074505854020081c1600f080101e9064248e0070000480754024019000115816142c125220544000303010600016400550440c46440028055840c1440c018060955030a10401d0b40401500640c161074001801c581d0400d840d001c90b5144401800c2c0a03a0160380c12491f010030452100d5004880d00001b4148190340001c04805000821000007607403 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 215387769 1250 215386519 215386529
    0x50c03030c030d0c05070302280c0b0d0c0801080a14071a0a020705180a020d0603081b0c0316170309060d0e01051303050306040f0e160608090303040f11060919 70
    0x1840700c003101c44e408a501d4042d07080024096032040003041e2400c140e50300c04c0b1118164070400340c045001c1c0c5032940044c0800b02c0d442100110320000399107280c00b00078040c1000d1805141095251545840c44090340c4085031003019000394007555114820100034440c0d0802040c42c04488803550141e00c2c40f20300d06a102c403001c00054801c006000a060030401d80d0440003102540ca079001030380d24004000c0280d444405210340180d27a65102100040008001d0a4100032103600502c40120881603586403040310141184131360b1000d403d1502040381400780c0000e0311700301e01600c0301c030302d01840c5400c0c036500464a0007548000c0c0801c0307803107024044d40d011400e907146903c000c1c081034551400c44c42850f00d0b02900036000a00c104002520390078030390480c1001d0010340800003079030500201c02a007040e0f404d46141c4c442c1006840c4c1040004c1e4070003456600041c0e503901862031070400750b40c0c0069480b40d41c1c03002007004461a02c110243d0395060151510f403030340604806080f03407040e45140b40d511014052 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 215389019 1250 215387769 215387771
    0x5090705030d030504030215071806080a060e01030c0501050a051902060a0522420b06160209060f30030405060d02030c040314030415110303060904050c03030c030d 72
    0x1220040e0f8407900802d405030350590040c0910103040b407107000d01480000c4c141000d0040c0b0f00015040c92074100e001c80c0040c0040c0ea9402054142a9a0340d0140d40c4c1c1c56003d020000207c40041c400b0410311800402200c0d800d00300103070341d1a0030280c261142cbc0150903040c12a4030b07009180d4641e00d500402d000e031140000c030000304a556100c041d0000705002440c00e04c05002e107d149244000340c0d4403400d01d045500c901c040c04030111080c0121800d0303120f060010150304410940010750070180c50295800000d0210f40030780c1481c0000307000424801030f104029103e2074040c0003040c2162103610051010800c041c100075404d01d0040d500851001051280190500c0e04404008011201100380c030700f039a1000704a60f02c0c00306d12030000d602a420142003916440340801c00000042c2444030000132140f140e2000d10707120791400940482c3d00c129100400240200d188000004e04000700441e0750041c0200c030381c0a080d8a8a0500d40e203080394110040341c0621001400701071110000001d0140c07070f58030400c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 215390269 1250 215389019 215389033
    0x4140304090b03161d101703090418020d0303091a010824071b060204050303070311060106020a031e1205070507140d020d120221010302040b0406080c041805010509070503 75
    0x9100d82440c9441032002e9103031003e503480c103440f01510700e031038000c041d0488501546d40c40b0070748030800031030200f02c8071696400001c0b0340449061900400d01c41e40c00c10200d85001c108070750089000e42c003130240300804041d5540409010003600003c4c0910075522034191071895a140e9402903a1000f01c0f40c081c0c0780515805202c6044510481040c512030b03215550340b13000c0b04403400140001440341107001c4038566001c1c040854152000c2001d003070618043d0340c1360b20700c804454403100d04040044c0c2021085400803c260004a5000084040c2400e60002c0d112101151500100d6174040522443d00b00b50381420140100f89900402900c803103401003060310348003094800c10a958101400d070010250b0007030150f00702484d0043c0c080030b840c0d0b440b040c80076107020482860507010240080200e2400e505000060055040c68820240140c2d002e071810481d8604050b50309507108481308040748110707250000d242c509035002c0960072a15501000034042410007100ba180c59040038006c4500a1003860 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 215391519 1250 215390269 215390293
    0x703080a0b0a0b09060c0703140606090f1b0a021c110c0f0d0620070f03030501050d020d02040e070902030c070302060603030a0903060b12061906081f0504140304090b03 74
    0x1004400c0300c81c2016244e240900e49818001144c0001300d82d05014081c58500102041162854401038607030034028262034640b000801020700e401400b01e0420001d050100980c00c29041c03449440c1150f45801c403600c42c1c0c40c07900d0803072070044c00c00300909030206410416120f0070b4021032900071001d07010013a031700204283c0c000e10134250302e4200c0841d80010880760042c00700d29507500c00510751100d003100d07a43c07030900e00400300080d45c0528401c80310b0001c0213407024181603052185e03034050102207a0a01610340150009500a01c1098010b8826a511001842a040100440300c0240030302c030015900c900c1e01e620241c980340c01c4041c0623000740c080d0800181d01458040122540e610f00c40d122003201c141942c0f1410f004215100304950050200c80b0400c0c5804010032071a48600c140743d80605c1c24043c6a6400401d950f1a0384c0f0000f4554040c124580f68089180c40002e06e1691a0a0001303850380e075400c0c200e9540303040030615007190000240101d03400085401c440071b0004213900b1188400602 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 215392769 1250 215391519 215391529
    0x108061f0309030212070b060906060c0703030806031e03091936060509040b0603010902040203041202070f0f03030815060f130e0c0d020307030e030d06051503070203090d080f0703080a0b 82
    0x46d40081898080d8000078007546454640207400100140c903640c10101210201403402e04103800650210313501c04100460b9180400050305640b05c41501c1d00200003202c01e00994a0180d464403d201e403410747d808002d4400300740841d5008205040c103d07102c4a4804098810b075003444800184107041800d04152254903601400007265005809005940d480b622803c210171740c0980500c1d0b16548a0130f5030809a070761400658052402a00e202c203900c4041701003e450b0102a0b0710600318100c00001c1000429040c0794190110b982500304600c0c42c1d503c014020581480020040b0390101c004100d200420702450040c05d040c0003900c2403503d11940740c2c0030480100404403000345202c4410000503030000019005560449081e060100f08001c00a8100d403c0d608112502190150b407050104202d14200003519003c10811265503d1070809000007501c034410350340c8142c01100c540d030003c0c2c00c010218046a00d02901c50080c242c0b0303125236260042820b01c00b075440580103810514154220710304 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 215394019 1250 215392769 215392777
    0x16051c09080105131b0e180606030a030e040f0e1006030c06090312030e010914030d06050d0209010504050403090f0e011511060103030e01090504051017060103110108061f0309030212 80
    0xc00c0440d080b8044160740d0505c2d40b031586081c3c019040208040058203400b2016918082c140d20410b00c5001c4a411050a140002c010402c83c8654420a060000b007500025001176501e000d03503010403807200103091840580350181c109610707442841580840440e4560044050300d01c680241c0c1c0741155110002c0384c80f0b40c0c940c04042c000039403446070300d00c0440c0a6800010f203000840004070700c655483c0c40324940b018042d10f03180c016400024005025440500c07400c4060041110107402042c40f17500400c20810050240702d00480d42c40e8045801e15004200c42c100802c40154403403000c03525502c0006040c4002e20801100107031030703041c20001d00d00607140d00482070702d440700422031607281d0b48040b44c04c40280b280c0765044c000b80120100b00c2c1c0c1c071503000740c034410b803c0c240d041c001280c6004840b054070b16051070600e44a4011200500c005003064400301c400700000d280c000307019183c900006429072981b80e480c0c11082c1c069504200c0958041d040040c456020780c0035503284006a003898000c43c0f01d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 215395269 1250 215394019 215394031
    0xa09080d0206010608100503030a0908011b14130806160e220b13020d0614090c072006160515010807050103051009020f120108030a1416051c09080105 66
    0x442d90061010611a400312a8010652120342400380e0f030740e002182c19948207111100000355558801e110250003406007094102c03400b00d0354555612000c8005120a6040260360751191000620250f03803282c510518014100d032105841b09401c200c5079a0120300300000c081000700e00c00c041000060f1034010f10b0350304003110222401c0781040c6c121140b03200030542c06010542c08240620104003c0f4030a2000c1c0800f040005000500d031420410340c285203200c04400203200d56110b40400c001260000c0641c2c0102c0d0f405590302c040e40b09183c03180c1020001450100d82c20840200d850003804d0108101310911034041c0d81a9883e2403a108011a5082c80034060130075507030700a0000f080254420b60140d540400c40d42c020000030390311104240c3c1a40d0102001d4114150013040212030321280140c080c0c0101302e1400118588405200302a1a2442c42501c500c114440865854084c1000030407001e01d05a122003504d040024074003102c070015200400080000d40040404a4984014414680246 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 215396519 1250 215395269 215395273
    0x2a070f121d010302040b0a0509030109080c0a031b0c0611011107060c0815031b03031306033303080702120a03050d1401030209150a0b0406020303070f0302071104021b0709020a09080d02 81
    0x2e041e5403040e08c16900000c1040d426659a083e4007003c19050f4025007a800b03403090103400312104605000b04a8625422120b03220a11035284000140d03a031200b00701100c1305404c050400451034403405004003062042c50701c645030005950002c011191340300201940c00b58641d45d40680f41d6400d101101d61003402c4060301980001c0d004c22145801c1c1d00007180d40f440040490b071400c200c4484008a5011542c00800440c0e11508031480300050102d51141282c502140c21113043d08a5849010440c0948401342c1540400526401036407221078180714005030544c200d82c00e1101c186802401a404461146000b525050107518180c011500e02d9040340d80080035400f0588583c4490711001d0400c0c0e90640c0d01c0003108000169081114001d0001000c054001c2c0d500ca240003500031f42005545c0305000308051041018800140c50160f203142100c40c00d40b401a202d1110448010100007583c03020301c51403066810001e0302c94803580040c240d030101c55940c1002195100d00e55640c521128550301c0240e = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 215397769 1250 215396519 215396527
    0x6090902011e0804110303040302120703050c090408032202100e010e060c10020d0b091e0106050c060a0b030f2d01060303081f0f12020103052a070f121d010302040b 72
    0x100741720103014a0103a0005007a00d00e00796481c2d0004001c4610214030120300d400281c0c0c00c10902c9030500615420150070740e1420910b1030319654003100c0748801001c2080c01c581480c41509020004d0704900407540d8003608c0384102c0c1c0c00054015000b444207440403800178580400a80a03800e20000f83c91030404000300809100d0300e0080d007807010390060000c0c0e0380e0080d81c0311b40103d515074645815901500800d80d031801c45a410780c98042e42c00070b050f003080c1d00344241080740c01004040050215807001e00440001807180101d40000d06102c03101540d0030007803080e041c50081030003034440d040d400d00341c50b0703407611000d409040180d6083e22028400900800c1142c80001d5612000f441c00c05101c060300b04081c150a92a9400700d0f82406071500892540d04100c0d100d41c0442d41c1610490390003d0022050713080d100703c40949285004c0c410100c0b02c54048000c92801d04000045040342210f42c0d01c0030382040c419801c0c0f603005082080e0007a420070703885006002c0c000030354024406c680950b552003400601e8 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 215399019 1250 215397769 215397773
    0x40807030803060f0a0f170c0108180f010e0f0616050a08070c0204021809130c140d06020c06091c0e010c02120f06060307060905060d0c02030c0106090902011e0804 72
    0x1950402400310760001800e0b103098803140d8440000901626403105034810342030030420f03041100380007c8144402c9601c504503e500c0c50313803c480603942c864440404d18201c000450a61400c0520740310341020113600301000c1a09046000c1003403207000309090101c6500e6a02e10011481c02032803400f246020517810080107006611601c1510382c440c40754280341b4500026036012804030790208032407103184500703040c88800307030314207130000c160050180603200605812079212402840014468030072081044e19103402c142e102c1c003c00400d43d80d0801800c54413044d90190154540108179481c200c580184810107440380b2034481c182000b0340c8140d9954a80c400765200640c1d5103000f900d01660310200c502500540440e0810022440c03a00f140060f008505128051524088054104409200070604144115254072098441e5100b0f410f001248940c2c0882303091b03055215045400c80c0c0f03542044008600b0b2070145d0450901c0b54401c1c1da55005400a221021101c980d98400c440c00084000c0c000c500 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 215400269 1250 215399019 215399033
    0x1090203181009121d01050306040f09060501032f04051003122c0d0602090103140f010e0c2502040605130e070b0c060c1303170d0c030204080703 64
    0x94403610901070001051029481c080c60030700d00d40382145500d40c8034501801082440707040e004506166051403500c80701032101440301c208080c0c0c0380038100306000c400242c096441d03401c05020880d944404101d80003090800c400504002d00041d00d000c7c841d0300300c40f403040400d42d000d80e9150020504c0624142202e2007044054100603205c02d82c80501c0b0380010021640c2422003040c12816903d03803c2071584001919400c070994000c0c0219900d0741300300c880c0555100c4c00ca62400c2260300040c0103a80e0610740c00140d00502d04c80e2804411440307208100911118000f070030300e050796a46c032140c444983d81c20994510030f20402d1004200085260103450700d070b445010104901074402800800e003a5243d9012500403210120030301c0b040ca496a81c0000b5080d01801400c018000d84c4400707900d0311080c8400156108009009180f5090740041c3d07130a900c0c10549000006554400e40c03404140700301040d8202150886c084001c100d42c9001e90300c6145c030380a031088504455040c400b50414074a1621112 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 215401519 1250 215400269 215400271
    0x4090b030a0c080d030c1b0305070804030503070b0405060619050607020103063203060c220e04080a020c010908060c0717040f08061b19030219020c1503010e01090203 73
    0x15003510a4510303a40020704801c003250003501e1070700014044c0404921000381680c0c035205060060080011030503050f49412070400a40b60342504290b66109020301d8424072910855002030024000810600304121100011901890060b0101c40e40c0b61079103001c00c400b00e50340110086603040d081e40100058105140a80303200e074014140010915030716040400b294001c0c0012481060105102c04050829001e1055a08000342c000303142500d0700c094012014490071343d4840c030f40281d0b00824034104c80680c00e0030000d0011010513080d01c1c00d01d8070b0708032520f40010841d03802501828012000070b522414168084807003240081c22030340c84100d404c1086a00420050390703008100c1d2000d0f502ca44020000b8002480c07030b0201804200c0c030b04840e00341440b102602e0f8100751340b07020018070020f16500c03040d6032001d1803000b402c0d400d03800c1c045000d034024820004988004071209a20609650f00403405035070500040d64040e801082a007202c04961009008038183c1042c004011b00000380103038051 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 215402769 1250 215401519 215401541
    0x501081b0313151a21060a1508030406022803020c060a1206030507060201051006121508150a06050a030f060f0b060c0109031704050c19180b04200409 66
    0x1c041180034240e4004282c07030380c56401011110340801c2411080c1080701725850b400c20300342c00c80c405000000403404e40f070308405003600440c0e640720070019040f25212020900200303080800c6954a55450324084d4503130304480c140c03810028010b18035400041c000b05030408213a906034003900800c01c0b06010019541c1013054244201b08021a8003036240e00d6510600c000f031401040104855490120000e003036440090451426410610040008a802c410b040f421041c40c6c420114034194135a031690700081080e4800031162050b00300034503094640812180c0036440c1c49500744009911707082802103c070003a100040040c00441000c4000c80c101e07900814000c403c02c1c601290000c01c001c00645d154100540380d0300305941d26100041056045110030300d2610b03044003001601e10b400d0300d451b610390200a007000d0084001d0420b09608050440082c4d000c2c1010108601c0d1a00119402e44010000510500d005514000000040d0418000300c1d030b00c070711100c00f007180c50541804403d0003d0400c0b500c503 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 215404019 1250 215402769 215402783
    0x30f04110409030306150201020c19260910030213050105070512030903030702010e070303050301030212120a050a0210141303050c120918090303011401020703020406030602040501081b0313 83
    0xc00c444a544a00030310315030324040d136030101d0b400d4105180035000010780f06480c01968030402c0b00e8403000b100807030340c0440202c4450407090080414200741000d00c410b00710b10030b001d0200c005030390621080c030005418401c0090301c003500700340388407001602284604c2c2807809401400f02d50403c140d41c800c100038443d0754401c3c0c0c261130211618819094041d0400d880c010420b4001000308241568244503c1070a44800401414010316548000d00b0900c410700000c1e000d03511540001d55041c0c410403e86c21600c01002e541a030320703142c0080c02841c0f6044a640c110042c02010603019400751a40160140841d01c45c0b421601511007880450000705058000c90900000b4021510480c5040c040c002e80010520744d100d55034034100c01003205041d40300708000450114041444615540001682d054801140c5086a0044a00d0050785080c015038002580642044c00100412240e90050001c480082c0c039034080d40d4a42d403040011180c01030000c11514032050000840380c10300d920b483c10042d4001c5171 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 215405269 1250 215404019 215404043
    0x170106030515060112061206091109070e01170c030705071b060c0210020307050a08131a1b030c0307030525060c08150102190215070302070f140105030f04 68
    0x5180c03420071441d10034055800b0744a108000c0700e940c0180034103181032540003082044c1030418144c01100c40c541d46001e0001c81d41c4007103810030801e0114110f480c590000742039150714a04054000c240e8030428102500081d4481e40c40c402a405400c00746015107031b411b040341d086a4602c00308941c141c006034000c0d5204140501c040080b00c19090205029010551310102004607034018030080c03202c412155411903104100c1000400c50120716000900e5006080d02d40c0c0d0000c40c0002c80d10050a034004a100e144001c207860552511200144200c40598040ca030050a0351003045031170b400342190107070842e042003000c0c1d00002d1050340240f8034a40420b0b4081e0b40c0c43c124210000c03207190f8121080b50f8141c2e903019206000e680205103075500c07189145800007602805d000007034a030b05908024038094400c0100d05070455403505041024031b5100c40700180c41d40824280290750325018456096115011760000c100502e8000014002c1c1d2010b84995195441c0c0e40e0440001d4000100181c40f00c1200721 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 215406519 1250 215405269 215405273
    0x6041104090203100b03060f19180203040b011a04090f0f06030f03021203060a0504020f0c16060906023c190309050d020a05010f140313120906050417010603 69
    0x80600054010034038016240e103003001c100c450f455801e81000f85e00000c01c6c81000080d550750b009140a15a054652200464030807001c2e40503019940c119500c041040e0180d002408500d41c0918413030350141d50049440d903038036045282c01160f4001c81d01800c040402003806551444e402c01801010101000a89440b02000c0c1d041100c40e80d410485107120480c01203814151304004481c0c2d00240d0305c10a81c40e50038604000703408000d0a01c030f00c0d80299000b16855903401024000c0d90344c400b8280041d916840800308071080c192400c2c2c003d50020910605010407514400107e9450040b0655801c810721038400c211078202036111300c407540d141181c005009000395414890000b41d42d6400380341070651503542c40c3c09004a1919000203005500c800352180159445405510890b182070a00b1903007450400401c4407502e00e030340705404980e4000414001e800f408440b9403551030340210100b80d0300c0898000c4c1164200c1079031003440c000440134403003444401d80b0101d5442d00540d098000003403242e942d0f = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 215407769 1250 215406519 215406551
    0xb0a021005040f021e1011010e0102040303111e0a0803090a020d0507140f15070804030b0c04090606030c02060f0702150406050f091c030b0402040512060402030d03090c0e0604 77
    0x480c2c00701c8540e8500325041c0300f1404c0c000606590304288441041ca04914000803820520208010300c040100300800030841490030344c8011100a036800096582d6070b120304001d031400d03206040e034105d5880b0300e40040200c12039091000401e0176480c4050f00c181801900d0ba07410070f40015012440f41d0091203090300050307070703080a204c01303c5109102030483c89280c0020b0300e060070111080140103498050b040d85440d0f40710001c034009401c00ca1241a00c40145040c00701c51802642c1000341140064001d001d00d040c45403000e8000c94404000c240011610303003504800f56046800c110015074820008070308038505000505900914500c121420700340c3c1d03e400d06954071801c0c2c4003510787d69503e400340311003140505481507214204070b005140301c8600c0d40b104034106403c4080b5a08046d9039403074000c0183c0da150101d8004250041002c040b500c9417080347c2e41c4400302607030100c1c402c0c400c0e106140d80d014000c0c001e00626a802500c0d04a2240c6800700208002400818a6a0150742c46200358100300300c0c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 215409019 1250 215407769 215407771
    0xc01050708040b010906050303070b27070e060616021203160f1106030105060f0906090a03060b0102060f090304052133010b0f09030c0901090902280b0a021005 70
    0x1541d07940740d41400d2500388080b5803001a000b65801c1410300302c0070710403500c1c00801c031248942d200c401c404a65849903603145007400403c031030b040b82c1c03008111920002100000c044054880003401c0a1494941404010f010310411803030a901d01c6c1e80d1000d02000d0310300182c0b0603404908040549160052000141180b0036803c0000c56004c410f03a5400028030202e9041d40c2c1d0100001c0c1c0b140c519550420000509900640c10004c6680b8000240500307251600d8060701c04c9400301400508003683c0ba0710382100070b440c1c0c80158074018450800001c4003a2180140d480c0110361040240d80340605100a00c4500c0d0214040e812640001e0590999041d10070807001a031009a540402c001d404a5060358030300180801c1810450400d03100103004102d240011034200501d00802c0c1a0717140029400310b41012100404c1d1039200406100014007500160005911548219002c807201c18900f10841030707103c00545500100c50150100744003000c840e0009106080d02c1d40110b401c100340f8203100c6419100 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 215410269 1250 215409019 215409031
    0x40e010f02220506071e0c150f030f15051212040329040203060f04140d02100606020a08091011010504080901030507030e210403050609030301060e0a03050d140c0105 73
    0xc00303102d00190400016410b401818040360350628040071a140d08040c1840c0ca00420b1030022034008000400010712001c400500300d031100b411084013503010152070018080207100203c0e0404100c01410341882c81000d4100d582c00344400240741c02c28040c00308001c50584500b81500c1010444a54a603880c00035200441c03282945a0070f00002001c4441c0c0c0104110031034100100010901c00140c5c0c0c0810510350215802c0700c14030b4240c1c0c403401c10004415a980d41150340b030040c01c03100f000c0c140c0c1c04150482e00f006d40710002c0c0803180e81c403c001ca0740d6171142c00000d03241400c00c0c003035202c10340340c002d040c0c0040042501d030092000d4400c100550848038240c81c2100c2160002600b0310507540c041c080c5907401076880c107080090a45013502161110ba1041c200441e04c01da00c5800c18540b00c20b0400d440155801008072841c0c0d1405217040d82e0350754020f004100208049032104040b074507040341c0300707003d4aa04c000a400342c030860007015030740303000c0b485801243d020b010700030514526800d11400d44250 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 215411519 1250 215410269 215410297
    0x81008060c0c010b09040c140d080c011a0303070b0a0b0303070510060e0601050c15041506030501050108151012020604090f14060415060513030b09060f09010c0806040e010f02 77
    0x4500c840712182101c1c4d00c2d40760f40c0d0007003105c6410070000c2a000e62504044500044605940c0c03008000080c82c11000d15400071302c5030201007003100d004c01056000c10300070f1403080d40380c5820f4007a0404040d601c0c020140c00528403080d2a001622420690700000c1820a001c1c080302d0420003075949940c10319440c40b51550303110745d4600c0e0070000c003210703072110b603811a43c01e0171b00a00d09a0100c1845841c0d581e00c0028075001c000510105082205145c0f070b14408404480e030400c0081d80320f1a02c0c0d406000c003031156103103c3c0b04105068840c018480100340c010f821076240c0028680c6403500baa0728642c0900c01c140c5c0c0c4070358107100004410300350b8028000040d04000000414100754100070014840160401c1d010780e16105860070700b40c00c4c40101d40103481240c00c1070340e103030741034050072140d59a41c94000526012240081c001c028900244403400744122682d5211a9902d00202600700c82100c010100081d60b0000410300b01d003881e9100d0320b400d01c082000440c0484150f103614060380c0c004640d00c0c1c094 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 215412769 1250 215411519 215411527
    0x10022508030a0605044b0905061f1a0c060a0c0210110901051804060305030a02060702061006080601200c0f030606030a0318030b0a05070f1e081008060c 67
    0x2c005030b03120b403402402044408018031449117034032050100c03440d410b580003010858201d0b145000749012130a0348510310004d00800040d10300001002c1c0c0841c0b0b000310303400d00c6180c01040c00d245142c0850f0a0749400408280320b0075283c07201440742c12407030080c80340c61003070b041140c0306a001c0c0512005115403903201021a4841c02c0b840d00a143c15160038006040c24504031110240104101c211a002d40c82460003580342c0da210364a4100185280c03489550251920000008104012004d808001c140f0380070b4401d25920340d0000d98a41000b160407146809070804280149400307007020350f400500c1031400050400740401c55002c0601c4c011950046030344200c01485503850f019880000003c400e81c050300c03040c00d0400c0429694a14104007d042c041c01ca2054809200700e1513084006680180024543c3d0503c0000b050091200b0340303000c2c00007181829803071040d9018401041c207004010b04001c0d100808458121091540542100f0100ca0a03100c0000c1c0346100300144c070f001c0c2d8520000d4aa50f = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 215414019 1250 215412769 215412781
    0xc020c012d030c02010e0102070c2d210506150a08072105010b03030f030402011706030a021009080f03190e03060106120b06120f07030b031002250803 66
    0x40703820035010940c45403030750880e0480c00700300080d0300c801e12403090902042e500100c4006074003516140b01070040f2584085001d0081c000c013014140c1c1204c0d0403001c4c1380610300c03e01e0001020748003180d20b040c040b00d140d0501002100c0840044118032403480d150060541c0303042e44c42d5401c1690595080c104102c1941c00c007020b51900c2c0c00c90400402141d002001800c0c42c0c503c1c3c01c03412010441c07070000350115400204003400070179041000d103440c0080c02d0b00d54604409900001e2500295000d9001424081c03030000224500804940103400050080521401503420040007a91429101c0108855a5800140c0141c00c109141a1445001c090340d00c9075014482c003540041c1c5541d8441c1003120f8060a040c0d031740c9001c95410306480440c9003802c0c0400d41801b000020b000d03103058250308100005411010f0301c59161105000e000d8210f0888465207400b0800c5040d5515500f0b0144d25404c4084140c01a40d0103034014160300990b2100118000e600382c00c68071021085150079550710f8400020088 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 215415269 1250 215414019 215414027
    0xd060323030901090306050402060c12040906050f012a0b0903071b1a0c0f07090506010314070e040914010e010b1807020d03052701061806030b0a0510090c020c01 71
    0x1003000c0c800300450401c4900030000b0034600c5284400b0349450b40d103070003180542d00c80304121501000e80d00222250507400030007141c80e5070b000744100b17401945062400701e01c0b8904550710302c2c81580160354031040d4401140c44038060713081c4980080c540c1c000b00e0b0354403000a83c1c0c08014034420304400000d1a2100c0050a08208000440320700d1090f41711840410710040e540846400c51504061045c0d0792580e050f01c03101c038a49000400c1510f103a104440001440d5001504601d118072400e0380c0610681412000590010a0a490729400b05123400d9005800c0e007499442903600900480062600804407100c0f10b00311a41030500102d90b944a1030040b0450400d0b410040515844a082d6200c40c60820402034881c04004480800c140d00d80c004100011075000b042c1c89440205042c1c1200c03103048006180c02007800d807199410155075500c03090141805031252204030390b00400030000690b50100c45a0080400400041903c0c203040d50205001c1918491618907c2c150780041c08105800c034001740c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 215416519 1250 215415269 215415323
    0x50a0e0a0e150a0b0d020c12030a1e0e0715140c0d0e120a02010c060b12070801110f030103080d14040303020c010b0901061d0109080a3c080f0d0603 65
    0x1806409116000c004412255044400594000000607142c000806496090412407100d2314030000c004030500030341e1320f410362103001e881e40040b44503e0100102e0702c5007825282964101d211030f0708100340400c880d520900042c083d11403280f07048a0804801a03030100150002400c280c405d922100d00340c241260081c124800038801215000c1c8401103000d04c40d980c400030120000e04000502283c1800c00540707811078400000024040104584510711783c3d5600d001d05e200d211419800c1c400c80425a20420003252210b1244e24a202d1840e030135900d4840c0d0030f0340982540080150f8880a2101c8921a500743d80c0c0540d1083e40c01590780c01681100b6402e446049a0440c400c40c014001040038680080c000310030107401740160f4920a07403c0c0c00580d0300c080c2c294031003012401245070030810068580819804c1c0c81d403800704c4510a00c4c883d403d011002c195413a014008540392041c0101040500c0301402c106624a1003181c41e0036004010305050b507031140d00440b90748a41c0311200f02412204c060031 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 215417769 1250 215416519 215416561
    0x605040807080f0a061e09030c0b0a06120b1e070504090b060301060e01110a0b070215010e0606030606130503010f020a0f0f0819020d0e0307050f0a03020706050a0e0a0e 74
    0x90018401c520f40c0103840e84010440103254955074114510342880031400342e204071101074010484a012030402815a050b41c4030102c400385285270010710442482d02c0341e00300340d440c3c0c030001010000096840746a0010040c0817003600503003126207804010382c0280b0852142d0415a82c00e501c035883c0645407030079108030300140b5200c0d03c0c06200600245612420301c00d400b01c001d18103410b01c0041c0e5100701d8180084518060f013003c0c5c0e80c1e001c100140d60009604603001032440b440c80603da0f82c1e40c5180314400c0069485540c004820000300741549491005014481050b29540c02602d51715030010f42114001020b203400d4940224440e203090341c11940c0740351f90b00c149062070704c02c0d0000000d00401d90709000300024180222082d80100c6000c4903410707903031510090102013184051200d52242d481d0000c010481d120b20030071140003400000881e07525202c40c0d01da00141184c1c0d046c5101669036401281c101d1040018100c0244103582d1840c0341c1c100100560315001c51607041c40e5440c24100300041c902 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 215419019 1250 215417769 215417773
    0x609060212030c070f02030d03380103090825031d09011503140c0304020405130b0c070222050a050106050703090504021615020306010f030507080601111006060504080708 75
    0x740c0744200c440e40440b5800240b51000301c0d603400f4145800c007800104150040c1d0148110481048590b030950300c48220175080c0007030003101d200607140c02607072040300c1000301381d801040c0c0311000c0d490350080e017184180354410a0114100031200a0000d2203050084202400d41301941a92090503000000c0248209881001160301012900403450305001032058004461040030385110700391180c0d00044580c103100004e0358641c10104049503240c2c00aa500764803492400010801190502410800e0b903a4003140e90b200c2981d9822301690190025030099800156050000b03141c42c0121003150f408031141c41c0005080d0403e500e00c0c40031190144c028109014041107444c002c00d810400300d40440f0030071500903a4850340014000b0384020b0754000180214280c0b520f2406180880d005107115000c282d81c0c0008944109000b241030752000e42c1c0c560003181e13822001c204036500c150788250403070000a040341c01c10a004400001198065481203001600c042000d00c481e01d401c0c8440b0f4000c017000d01c0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 215420269 1250 215419019 215419033
    0xe13060608070c06150e09010b06040305060f04020402040f0803070c090b03070302040917030c04090b010e090109050405150711120915030702010b0607060e060a1b140708040f06090602 81
    0x9806000351070040e08400c244002480c03000f0803c61290094078503500b8002c111030340e03290790f642040c003d20000d44442030340e942040c8104450781850f40a90302200d41140044c082916a01e2a81c01c02d4031000d4416a04141c08110104084a000c41d98400800010b001159201600d04010003200b031750b0f40100c49020b007003200c01200d5039800034402c4207494046a0000d108000c603c0c00d01c003c403200c040218a640740100070803000860003c083d00445402a10500c40c14080d030004440d00803100030110307030104085e801800500310700c0e40400c2c1c0c002d03c1401100e0070101c10755a202c60780501140e40400003840048441440181800071200a904c60780c0501d0a001d0008001b640200f041c0841c004d03d24004000143c00d94403d401c54607202401030055542c40b419410700344060200743e078004e41a80329510111380140031911410301880880700b281c03e0110348074002210428098668100c1906081c0506c50205d110345009200400491030302e02c03032152030075501074003658250f8040030554008003 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 215421519 1250 215420269 215420279
    0x51206030a11011215060e090109152d09020415020601260a08040e0f160c0206090301060308030f01050931020a0b0c060609060f0612070e0603070e1306 67
    0x500440b11402400c0c5000c00001c0d0b0a1540024140d0f904040d00302c400c1650001515504004c008039802025240981940e0b00c47d11180107031020023210070108d503c42d0400b00300703202582d007403600d4a0b1500410342948050720300e183c20586106801c104059a40000c04000111442c408103043c2c0019002800e0150300d003900b40322000074072060f601c41c846c00040d2040d01400c01440300c05c400c079038003001903a11651504124500300508071091134800e07a5107000708040103414185c084040380159268107804102e5801d11043e80c0100d06210303003540d214180840010302c2d03007000d14801d242000daa403425603d014100800b03240701030183d0040d80c943d0303078000600440a90b0404030b100002c00140805e42c40768804139070381103e80c1d44000080800803c80070527100001c100180210710458051003103484503010070070580c21340d030070960780710100300030210031200b03001070701540040c8030b0800c1000800c9400119941d0b03032044030038000043c58104005e46515145070000c0440d004e950701086010300f82 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 215422769 1250 215421519 215421533
    0x50a0c09090e0307140304050a0305010c090504090f02220f020d0c030c050d0506061b06040b1807170123040614040b01060c0f02060a09050a080307030f081302030105010303051206030a 81
    0x1600203005c815045400483c0e41004204507001880050714035901c056990605600030f010034282d040000d5030307403000050305141a0140200468222890b920010210390801c03010041c0a1000c0c200078520200501702c00e100d0744600410512040d00149c2c0d0b0b20541e0092100b102d01200000c8141458010040203648d803000948080c2c0600c864000303400d4441c0000a41240075070104446002c41d0381c050508245404617025000300d2068031060b405490302441c00b424005962000c2c5403640c0a0042001052100b0a20300d41100b03101c00005041e080c80060040840701045032454400d00920510081000c42d2040c003441d031010300c0421603e8103007561500303080079040c0319034020800e203803c075107042c4410b540084c1242035004160b15640d01e00c0080c058602e202c0391191078800c0c6180c03d00011100700c04411101c5031981969101c0c00d0185c1190143c550000240c45041c246a4181e6110016202445450702840c029190a07846542c1c91400390710100b40206114001e80100340e5000c000f8800c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 215424019 1250 215422769 215422777
    0x61f0c0515010807050d2a0305010e0c01020d18052106100303050a081f0e100605070804090905030f27010e0d231501050102010c1b080715050a0c09090e03 68
    0x300311b40c0805001114281000a20341030411405040e00304070a5214040640010b9403c07a4404e0009101c24251011102d4683ca01d44564a0250f000340d07072499019031142645a0480b44100755090f86103071aa004104009401100b001c0c4000d003005600c803008104210301c540c003007044045842d1403402c5540082143c001c0050107024014001c1c082404030311040f00c443d400302e5903a80c048008680c0c801c6103c00d0b0703550550322407200603070001d40411407906c1807003102d4280da0005551498140b03044811030050031406e4094400780000c0c0304502e008008000103280c4000049451490100425840748542c0c01d8a162581408840c0002200072303160321041050a075004413500280f9083c803514199039120820200f8400e015040300d036082d00701d0005480741600d00c20307030080040010804055a811040340c101a82074a025000c14000603002030040000f0744c030450040c0d85581110074600c09507842580d0b00000d49403103924080c500d81d800260000140302c1070105105a0045500064507441 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 215425269 1250 215424019 215424029
    0x10503070623041502010912142502090906040203010501061e0f12150f0501090308041a130801050603061b0d05060414090601090e0703030512061f0c0515010807 71
    0x302c042d1007880c46001c614282d40082003e00b8000c1121641c03488024000d014440003185c0b100d64842c00280c0280c861000180900704202103a4585059109100301f8000004462401c80c0780c410006c5005032141c103c942d001c1c41d90030f401004142440c1c4105400c0d248142c002408024503603c1221035051049180c5a600e0340a01704203448802c0004200c03841151481400c0c2c2d1a03041640811600025032401c104035606a000320a019880744011039045015100103403032800240000d0001340b00c400303000c5e10840080c400e45440c00200042d98001240d0a901141050b50f40d1403c200441c1801c1c041944d21066000007100045c1c06031483c2400c40c068521941d03d15580d4000107203554071268081c590b0b041d035142c80c07446a40303403000000fa80c80c9801d0060304900c2e0b051004030140c0c1c00001031800140c0390f0607240c660524035003612030416040028002603024080b001140c5411481c5452008014490f41e500e40c4000500d04080d4601015200e14800145800340100070000d0f001c100c50050764 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 215426519 1250 215425269 215425307
    0x90408030705071a07051b0f07061b0c03150f09020307090908070203060c0a12110a03020721081e010e0f060d062f07230f10050406050105030706 64
    0x100241044c100b81c456003052030116a030301c00240710205030090050300c607400f0219492406100540d0000d512420341400c02141544101c400340b00311401440350740403c00074440f011094102c00d403546036054245500035036070000e05034007151075003000d8051203842440d01c01051000100a07404250b84000030f1041001c15680c0308140005c014000040315050354006045900700c1c01c01081d417003084d0b0f00510741d88011450010a0000c0c0712450700038140e46100b05403400c0c0c282594245c00342e02950009a085a000418a0f071500300d120900402040f00d0401f65035060691400308000c0d6450710800720814100c0c05600e004001d400300410300d85a02c40d10030480c035501501d41d1f0010400d86104031200400a60810040d0300c0701c84c0c1020701000030f40e0007000301c111344404001d0b01040c0e90300c262040a03008120003c8a0020003094064243c0c18034030203421211808018400d01d814000012030790482d0b60748490034442400340c0d500486015050032400761038203920b0100c01800b880c0500c1c081c1e14002c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 215427769 1250 215426519 215426527
    0x110d05090a0e1b0d061d0601090f06021b01030f02070c1a13050d0305091008070e040203090c0907050c010204030602070215030108030307030e0c0a06051e0306010c031202042c06090408030705 84
    0x404807a0025401818480040c0c000c1e00080542c986d030000044503c00d0002d507820000040724080038a0000481d52103802a02000c1d04130108041484542c01c0220305040c0c0316025401003900713a100408400c3e001d0121003181030b00f41041d40c50100005000b18107000b4040c01442c0c4000c001e41c11041c00c9030801c07a91118080c03000c0c43c042c1d6441c0a820f04855101222100300f840c0340f50803410b00340c8180c5256aa12040349a020100000c81c0000e41d51404243c1c040c050083e104d09003413609582060302418541d0030040201072280c203a0b4000d030030488130940c010818004508019800c5c806100d4003003007850075036050032001543da010042044040540b0342a181c00c0841d01030040000313400002c1d00c101a116160400030380513070300c440340c0c024918840c2031a1403894080c910a680c041c4205039034042c852041a2400c54000345202010340c2c0c0304d94204000601842c0641040b4001d1010050481484132540c2c82802c4154005000c00e0140440004103c0018070407011294005200c1c1890343d22 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 215429019 1250 215427769 215427787
    0x150f060e040b04021b0c030105072a02040c03020d0b120c060d0f020a0507050c030a03020706050901054006080708041a01030302030d06060c020a030303050403110d05090a0e1b 77
    0x1d0700c0c01101650b000751001421860315121000d2040707003c15040110f0746d413400c40e60281400c07200112500d100160420070351203045c0c11100421501c1002c00004140c251040d030700002c1c1202c0b070002072a404a940042da0400102040c001c031036800c601210114426591070000b44d84500c00071203641d101d2a0001a10380c0c4455140c0c1c0059040300c0c61079030443d22590340e010090815803202a06030b6891082c1c0041c0d243e01e1400041c2850400d5165000c0c0c6111480d00d04241d41a81081d040a4144101403110f01c0401c6144034888010500407041240c2581e20001c0c030140c40035841c9000e60000006400c00d1201a411905250700403010307140c601c9c42d41c5d5803414030f03000b00404108504c0d54040040b0000060650001c09081c10b9401880100041c66031000141c61103c48620001d400034204801000421b000b03500155102d4043c1c207000141802c48100c603402d20709088561170204202046010740c6040c91650b20000c1d20298400301c1e8681003801001c0c4155013054212540900005a404a = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 215430269 1250 215429019 215429021
    0xc03060b010c0812040309090209031209030a0f1a010807060503190603140604020a0504180609050309101106070912170d0c031a01050301050d030516021210150f060e04 74
    0x46040c3c01154031621103074a01c003444d0a000003928298001140e5490102c4d04038103510884402d540014001d25240b0030404000001c5c0c0c00425040d81c2c076000d910a00c402041e44030b42125140f604c9042c0c940c5407110000c241011407401a0083e07141684240310502003641c0020440b9040707120140b180c140d02c098030380b007000504019000140690b403041841d080c100400600ca5009034070881d40104034944480a00c001c80b0b18207007031103000e80307092019040421001e0344101480d17070140c030669140ec15240b000c1502c0d02101d2003100700149508042d0500c2c5c100c10b0040756088060b034a009245a4a4489103000c6c600208401601a2107030301ca240c80760752204421200c0d4203034608828840480d90100150040c0060034105202c18285e48480005d0340c03241081b40d050307600c002c2041b0351101660f02c080718a0b070011500700045034001440c00016980380080f1a010340141401007815509100000041c1c41c4051200454460a181c0030700540a20940380816100c0a140401c040080305000070 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 215431519 1250 215430269 215430287
    0x10c0503130303051003061b0305010821031003062a02061302060306120106060c060b030f03040608090312150316060e0d0c2d0828210504061b0c03060b01 68
    0x101f107a45030408864a0a003d0030b044904400c0b41c2e1020445682d17a12174031600c0b400110820419076000c03801c0749840c1003002000d141c02030031200c60500d50035205c1d551001124601e60a81241826020000324130044404401122800e6840a40607600349201c9103c00740040b038400034414280030000484a8a0b169414414052204003c0c07004c6a0340d114040c10382c1581c00c4056070b10758188070840400f41800107044400781c801400a41c40e00346461800c894088015151100303a020070000794a88035407241036940101c0303100311070400a00c4c00008240c5481c005501042205080400030800550405c248021924040d00c0410211043c0d1814030800d0312560001c42d001c4440414880d00614075500001c522440c0202c4c088003552242031042c0d80d00c02d04107c03132044940ca42006084100d20604402c00148980c840c402d0310400d0103da100039100781c805a00000300007143c104200d5500c41009100340d02840c0706004201442e072101d116074007844c080a00480d4070344800301e2007a48a00c00310 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 215432769 1250 215431519 215431523
    0x10203090d03030e1011030601050708130f05040608160e1f0e01092301060309020a05040f050f070e030a060c090305070303020319080105010c0b0601090b07050a0203010c0503130303051003 83
    0x1c0340c0300c05650700d8003070010301500c6000300300c9100f40898101583d100703102e840001c60b040070700300307046546100044405620003d01111180c00901542201070010b0701a100901307041c0d4035501c01d8500303002c01d21007111031aa10007503603a44102e404c504404403103030001064904c519002c031295030b5942a00c0c030f03ca844043c0409150341441100050342c858014049050b0b41c00d608061080389204000045030620b06018120350110800040205034001e0b4040350b60f89101809255a0076036460010b8202c4490b4091044c003107449000704026041c00031a4103511501504200000650003000310382c3e901c00c502001028581d5447c081428a4003d44040004503442000c03289800e480c2c1c6002502c3c0d400680051180d040c00b07103803e01800c2d0007101907505a42042c0d450382c12201403030f140e070740d20750340c01901d10303410703c61140000316170080c5500062540710b028070005c1c9450700e11031040c10308583d10031000008010090003402145144429001e040d180c15160220341522084030094092015030701c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 215434019 1250 215432769 215432779
    0x40c05071e03032d0506040203060108010e0403031d0d02070506040f0302040b030a06060803120907061704141b0a0b030f04080a090b161a010b0a120b0616051603021e01020309 77
    0x32080b900d00413480c80140c1c06000b0324140403d848039810f00003070f40002c1c5e5216010541c2c9800600a8102014525a009000385400304844082c3d02603000f02441c81480d490300c60700305a110310000d50701003103801d00928040e12200d20f010302d010b4001380e140c26070703000003841aa22072450030b4240e50108180201706407c55020008150703104011035990f4004032101c5078a500110000c4c800c154041480011241c09840e84408450411020324003800000c00c01c981030340d02c440d400d070b244040402002d0031007030700341c0e2051602d84803480401c15901002d5211140300b440410800c004003042c3b130b0106402a62050105072282990744040e1040400c50700006591040401d010700013000c0d00c1c1940038680e005205080b00030303421a101c0710241c8401d0080010094082051100b0f00e48a0542c1841c480300311000051244c00c09400900c4a900c50010900d010020700300600501074284130440c8509010860000e8803841d59010072030280c2903c0d0940c0e58240203a803460b0140e4000e00441d00010f0740141 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 215435269 1250 215434019 215434061
    0x21030603050d2703020a030201080406020d110c0f120a050a090803030426120423030705010510050303070c06230705060108010c0509091f030807080405040c05071e0303 74
    0x40001c2c407850700402c80740c1c0100021203000c2c2c603c98401882500796a0046c20b400b09041c1950015181e041000e4030442d040c1d54208564030380c0c0b0b800c51182008141404017100d40d14942211184c0c51b145019800742065003103140c1c00c4207901c03101021604d12080b281010380d1160421401521900055403000302da6006c0001000100309104a55281c160644200c4829103c015030200030540980622602d0201032540442c002c901740076500081a0791016500381141c2c241c881a1b411604000e00c01c43d1a0fa444d00148810448080d065a001e0402a0003d50409c0c03550f40f20712180320741d50f10940c5e05018910f181504040504091040c4888400c0070a0390340b10303c103190069907290b007441501030383e509e070101134080340b440754003242c0b2300090050000b000340d00da041a0f070180801c070302c2000c090001e14100000008401d10b0251135039a0140d0a0745489907d0300d4280010340c3e1100108070704004d01049500002850309071400c440e0245501506030802c2d041c90103800502c0815600038420320862 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 215436519 1250 215435269 215435293
    0xa0b0a02010504061505130b0301021b06040501180210030c1b050d0201061e1715070206090d0807090b0913020d02091309080306010f02030d0c0903120206042103060305 74
    0x14018900481c8188010001405030051164141d40d0354006c5e183d02004481401d400517041d6080315030000c40040005142c69421a10320400c9120f1244a2489800040410040c068280f082ca00c4218241036490320005080d800101280b00f6000103005042d0344281c40c8185521850030364030b08030709031407082d11044002e05100da52025141d43c03210040d800d101010400320b00162458450b1405142c204080310700f409234105001c0c10030101c0a0584c851001041c4000c00c0070300c00180940c81d60703009807440c1d09000102c6030604110121078414880780d0018030212030f41c0003000100312200c91111584480100d00001e01a1030000d03035202001c0e00100f240140090b9941c02811091411910541e00b08040200310b0161814200b010b0320013407007400022083d500a1a81e9458241e0a1060300c3c42c01140302003c1003291050280c02c3d0010b00400024810000800034800c481c00f00b50008241d546042d95a40740750305108185580e110030108140791041e4001d8002002540c2d001c020345260708826 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 215437769 1250 215436519 215436521
    0x141e0c040306150e0a06050f151903060f0807050102060402040e0a050d02030406090503070311091e0a0f110c0d031a0315102103031104091401150516020d020a0b0a0201 74
    0x44d00401c0f41d07580c103040c0410142c0f01c10384a420300b1580094010030307554144d5810840d1308420400465994202040310400e02070f580306500b0705480040e100001c2c00360502e0089408050b140c6c000a4441e440404140480e81c3c0000e101940a5412107010402c00f00b410380090501c403040310f00410510030105c16001c03442c0c001c400b51058400c285d80b40c8004030741d04c1c810140c2e0b40c41180700c082e0014540c4a01494141844480030754400c3c0c00454070760003820000344c600e080303074411144801040e80e25103980e1004013003030080b07401a444c101421410301c0e200701a01610f409441400d00c050554460541c040031141c00700040d5524070003402e070340060741514820188120b045503a12400c2c19210703030105c2d1103074411201e4807100b034003000d01d89451865940d0542c001c201040c0c5c10800c0080501000420958038007604500c8074040c0da010f1801e51410000e040300c41900d844120521105101200400c1d0442d08907490880d0100d0310348a602078503002054050381c0640128030103c20020307448000c5030f01 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 215439019 1250 215437769 215437811
    0x13062a0b061302030a0c02060a0c05160c05102c0634060b040501080a0302030304111f030c12020306060f0313020306011e091505040207050c03010519141e0c040306 72
    0x6c11303000e03200c0c20b50702d611042c011a040c0d0541000070540a00000e00ca01102800001c4014410610b194913640c940002484080501d42c0c40c400240c0300302c0380c0242141e141c410b002c2004269141d002d004805000000c1d940e401804c03e42500c0e240d5050401140d24503000a50004440c040c2d140c0c1746c4d1489906000c005008100c5015000300e0915000042c0c800c0c0025508007050b4140d4051030030341c0c1325582c1d2038554041d00424a43e0206001500014507040c0d200020398041854074009403407807804101502110010b42c120580c98418410081e05499500c1140e039640480e075181ca0780d0381c0d10829103680f115026540603400d4411003001103103054900080c2c0e54403a0010310700d00c0d00c080d5646045800d070740402c1488003d035004218108070f581040e4002d010000e1281050300c04104424001c84c1c21280c04503401c4100c20b00c1d5003103c1d404071f2420300c241e64603248000c28540f130928000310715807803507403800d81c02d6005401c0070b030000740d0b154a0b1074003035401865001800303201401c101e5a403031000380c10b = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 215440269 1250 215439019 215439041
    0x61a04050609010803072003070f060206060306090709020901030906091b09022503020a060e0303061302040f03020d021903080405010f020d080402060d090813062a0b061302030a 78
    0x22400e03010801914103034000604a6000000440c5020003644d40c60301c200c0040f00e03c907442c02c00ca1040d084a10b030707001c0c45503201800508004040c3c140c903001000746011009408140290013840138001001d0f004a006e005482c0c0403e03000d641ea103031044c01240106518603001c0c00c6d9601c1c00c0840c6041000011168403485203000d0400c6580703803160445800c9214403501c05d00781c810284660880c0c40c40900b0b03c52030f07050290056035000041074983c5000c1d110403400541030340d00300101b00115403610401c44860390140300b2086090a0801c1c880303241421003130101a101c2c505000c000303c1107550340e05c100001e09418400070a4019a603281c02d8440d030700140226800300b064030006090080c800561110b00e11840c0c0c0e00d214564440b0f4083c00300d6907010b4ac44545a00ea02d50f190b04003c1000c00000301b4070700800070010b650311032130400c0c01800362001c1800455402201642c1441511142920040043c0c10403ca04855141d01c00014000d00942c800c0740030440c008800c124400314141c4c08954540 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 215441519 1250 215440269 215440271
    0x304080c12041809060b1804020907050c031e09030d03151202100809010e0124091b030f0914010b0a090203010602070b0309070302180406060602010b1e0d061a04 71
    0x40002a1070890a014600804a4803c0b11210b6000311103020342140040c3d9019840c00680c0300c540070041000e56240240b401c189400717200c140300440c18600242c0790302100c14a0001d0070407404c07501a58580c81ba091140c2c09820003111800030451503d0111800c40c0c0005003120301e150318828014001d8414042e8540c1d284d888d00b01c001417020a4108565001d65008160f41a00104803000341d03549807000e80008243d6685d803080d4a00d0140902c6000c1e20903212140040c003d5101c601084460180c81e04180501d50900607200c0d800340100c860034100103114180810340082c01d6076050010101c80402030800d0b02c449080d4000850194400a400001543e403c1c06d0103440c0c84094050744000e11a50005a0000004220b2500040c5c0516004140d840560320742d2941c03500043c0c68a82103000495200f1b20300c0e004e1104000061140e0340042c001030009000440b6204001480b817010840f80d00d0814410400d0f41580c2d42e21040040d203c654000d008000ca07400400080c0640ca11842c010741c082c03 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 215442769 1250 215441519 215441533
    0xb0108010f02090a0501031e1d0708120a080411031203090105071d0f040e0109051c02210307030f0c0210061a030624042403090c0e0c0d020304080c 65
    0x19107107500803980a610040d02c002545880c003801100144200d0b80107034803540c81e88001c90074100e02801266030007800103255190b42d040084106040a03455402103516500c290507a9501a03119010344d2100c903d1410102429612424070072440080c16140c1d60703044c01189400b003000d184890145000720100c5000304441e81d80c030f0354241d85d0480d9a0240300e11074005920b0f20106843c094810550710080940082460203001d03040c1402d40300c3c4a01c040303405800c51a0440c0600c901e00d003d031040c00d4182c1c4000d000344041189504207078542c501c1004400c4030000005101035002c0d420076a259100f40204210f07024a00d28000c0d113a00000703200c96000b9081040004204038407c810451001509a01501c3e5454040c100021a40310510ba07070398120182d82001c20018400c80030700020840d0030380ca044202d8074048451008171182800d00103141c035114080c0e000ca40034032880d10030740781c0818564174281c0303880c2c24045850040c900e0361040030b40000b00300400c00010ba00501001883d0703100322400 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 215444019 1250 215442769 215442791
    0x3070801060306060c03090902090a050402162f0d02010e0d0308010e100602070e0a0e0f0a0b010e011805060102100606091a04060c110a1508040506060102030405011d03070e040b010801 81
    0x10b02c039040c11701900207400900705018014480d40108109080100070b20b10540ea83d40120382660003c0c0498201a5006114038041c81310609012035020240312981107400003070210840c0d2550380102085c051142107400400316401013905a15107500102800c0345400b091a00a140c801c00740030b60301c4034080749c00c00300f0854404c1440c0101515400e4001d068143e0401c2c3c13030060400c0340102004259502c0d82c80c40d0a02d4041444649806500140503108041103030800c81442c81040c0e00509038a502c101c01004000115455140625840100403c0c541c90303050040340740a81c2081c0c12401e146c60030070000340060f0000f00b01b10850304032048d03080c1c0303510b80480c900c8010302551040ca070101c1d50320340f01d03000000c80d00b51100c2807c5100400440ea12500c50024016940061010401240ca034000f4001801010400d0503407201017480110714080c10040000c0006d094210030051402018103044910754045c001207010b0500001440740d1480e050a00440200082c840c154155103401d4803164 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 215445269 1250 215444019 215444027
    0x13080a0309050f03031209120f12060102031c050402010c050f0304091d0c151c05070e030105091f090501020a03090210020a081c0e07090e0c010302120a020c030f0307080106030606 79
    0x3d1a03a8010044c500b0000181c08400e580b600050407802c42d409201444000301c1520f001078840b150b41042403a4a8050b40d0552148452020b00103d056610a2100b90382040c421510700f2186500903001048588503403006070f401c000191070040c010301680c860844845070010107041119003401003440341984205010300501c1d122500c50580e40c025a0b12081142480f00c60790100002030104149404040781c4280c0240400d41000c0011544901c140040700c0d522044564603400220b000304a9401d05028080d40d601a1200c1a42080c0d2081301941e01901594030070500181c100000390356881c8540f0b0010002d1190210403841240c80c482500101c500c0021200425540614007918081c2c031340120381500e11110201030310b03050f100c01211403021000d0104100500d4491000f04d14200b0122040c1d0500444080c4103042510620003000510b041014003500200d444000513070300c0440c00c001d207095110b21000b012854500005102020b1b40c090160790489049032780400110340c481c0004c072 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 215446519 1250 215445269 215445289
    0xc02100b0607030507150203070917010e0c0112020c030310051f12051005030d020f1b090a020903030405030304031424060108060f0a120b0601090506040e070513080a030905 76
    0x581c010a0500402d00028042c8000307103819805030301c9400741407034500c20301e0081e40d00468407140080c03c162010085481075502c8907a0000000c8000d2024044160401795208001c510960400202c0c00e40d500b180c18042e4110303061451520143c9513a803904401070074101c030310307071080798000c481c09980741c01d50140c4502c1a0090351040ea6840102e4084c034070284001d440060a102d0007500038000010780c1b0b95082045456044032900600402c41204481030b017045900020a81400740d0488004410342c1e40c2c0c90f5455014621950058a409010b00401e18600454010325014480001c000c0103204088070281054a0010100c4000d40c8d0764802900341d030b401241e48082030045200224071951300a91f0410362041c0060650b03440020701d04002152500079602506513442c800741c4841c240107034103006560100d02030030b0001d4940c0c40c100c0820307510701c1035108444840950b0703808940850702c500200c0b4441c001302001da040e203d4841f104140c80d025555001c0300030802040e000903003420400599 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 215447769 1250 215446519 215446541
    0x405120c0312091e150c010c0305180a030c050f070f080f211e0d02090306130b010e09030f2a07030206190903021801030309121203020f0d0603060c0210 67
    0x12807003403042c990030302410001110780203502c1701d01c4422007070f03525554601a102881248002090506002a0240448034040d08036050001e4030100d4101c4200000384a0400c0c070b526107000400d401c4542845810181d600d4652903107401507440c0020b0b0004541072400583d50300070300351100840004039203079450b40b40d07080b4440c0c1c954210f100e041244443d0405080740010400081d0721203000c900b800030841d4403c1200c05e0030b45a000c688031400b810200110341e8010010f00040c8440c0215031107181c41000c0521510600011a10000d000a4003c0c0180e030503400c80d618610341c83e641541d07040810102a500d62050b042141e01c1c0740402000002403140c100e0790050141c0e86404101d01050200d00c0b69003041c0310620805250000068032400c00c0122441c40700d50030880030f54154500102051100c4e803094400020a04c0217502050110703060814482083c100140c0c5c8904007a01200e440c0210500c454116140c40800402d0084540201c10351961560a954000380180c403018100d56003d820707 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 215449019 1250 215447769 215447779
    0x3070605120a0504060902120321010812071e0503030612011b0e0303041e030c05010807021f0b090f0714040b0409090201030908070503070501060e0c0904050c0405120c031209 77
    0x10448403402a40f016410a010b00720102e0b038917500340c000c100594440c00c00512603500c002250300a02d15000e10320005000b20144803c1389501d0498003d81d9000d800b50403002a0900140302001c12003903a241d01603082c074601d102d0524071118201540c07290411a0484d000d801c210341e000160071010300c02c903480e0707608040c1d40103e10000381030222501d01140c40d800d9014801000003054000c9003420b0403500c80c6c0e0107102c03621000d065151130070841150740d0009060110510502160540105171040c012000580980350000152008400f400d4020742c016044814141405000c40000c032031039206140a0300d03140003220b00e015800c010f0b07204522521050100901050003121240d8000c040801c1c014900800c0080d865119400300703510000c4200e44981c8002219410040e080c02521700402070004134503140d251200903105284903110382c3c58480e07541c4000260340900b2030000c0d50080c0102074040074104000b03503580f42c6d54a02260303519209115040f545c80072000c000044501d100d401800c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 215450269 1250 215449019 215449021
    0x7030f1e0c0201180e0415060501080705030c0403020d031205160f120615020f0c03012c01140c07020906060903030712030b04090b061e0a121b0e060307060512 70
    0x1001c488014081d201207041003c180b5840c4540d402c04002ca20245c200342c0038036030060074586887c16004d000c0000d0848010f08101c420000d903a0003483d2a41d001b41103040c025617903595000305002070311035500002d42c04210800f08100f81070380428410804040d42008110759200c5208a01061400454900c009560000302544051280b141c241d03080642c4507021500369180c070041121070100104100046c0d102d11841e40034583c3c1001200d00144040c0c0023009400d080e00d1810300d640c0d8021034042c035803c168803110b0b8600c41095002c51045400d0944009007170811079441c80d0550b004240980c8100700c402c0200d20585883d03012030b0179001001700114039129040c1d856404111030101104185a07503491840d038651039500801c480548035036850328840c035255042003c4c0e4121411084c0790300c40d500c510410075480d0b004800099642101c0807a034140f840c4c3c900800b502c01c08402d41d14041d05000d20000780c0b01140381105005003030840548a20b541c462404480f103024a015856500301c8400c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 215451519 1250 215450269 215450327
    0x18030d020c01060906031406010b030702061602160e16031a010c050a050d05030106030f0b010903030302090f060f0403020f03160504110d1401050405011e05090a020c0d0507030f 78
    0x9401070900300c80c030000201e03a49139144c1c03182c0100c4510b5802035460354040c00300488403040074404c907401b600180315018114180504003e40d9000010400307007444403003a9801e4581402000b80541c004000c8419020098440c0c0701140540317001c3e034440ba102071090b0350114074580280200b5009ea101515800c0d8808000d00045070200794590b0241d4030390040b51f03010030100b542400940c210108070f850b15643d0354507255000f030403103c481204e00d181602d0105000300d560b030301c010154112501071402503110500c44001522150921060f6a07005400103481c0140c030003410050801c49000b1a00001300c0040c480c1450385481c0c1c1d0304c00004c1d00e001140c009012902c0e103548000b041c0b26020b85440d050010000010b01119043c0c16003100609044004001a00c2e15010716409070841c0040e8445a100f110050780800340b103030003028450b03800c84002a0920031164140d64803210260111265045602d1000e045a031007510190005101c031010408450300480c0e01042406181d100e1028143d018 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 215452769 1250 215451519 215451521
    0x1020c010f0c0c02330d0b090a0e0307150b10030e070504060f0e0702010b1e100e01050a030e0a0203070b03040605011d06010e030114010807140a080304210b0a0203070818030d 77
    0x2080c0e030500707005c4640440d6801200c135140a840c050350004d03400180c100b118810803111810082c411a011810234030203000c41c5c500401920b403420b9020504010741c800070398403c0080d2081244050b00306a2000c000450264141c0001826448010541d07225640f03038000c1c8000d448160140108042031820b04000030f103601e04d1540c0c1e001e001440000b41d11004070001030b20200706170b408500c0c201580481491286021400f921000720217040c0b00b50701d0102c0c000081d24074010520304e1011715584003100c3d01038217002c2c09001015030f801400c2c1c8030950b0300c0d08030b004610340082d07900b6507580740350100108240c20360030541c1c0201d00314190002c55a5981000450f02d5903405164250555220030040780c020404c046024080e00d8100c0140003181d040800700440e80044100a0348188501101080214004004c45058403c0407020280031400c021141e01d403810000c40090802c4142070030170240b8065503002c2c41c011103455807240702d01e403902048040b02c0424501100100d406c1040040450140703 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 215454019 1250 215452769 215452819
    0x6050418020c01140421140c0a0506070c170c0a020402090f091501030c030902060a030b01050705030403050d09051807230c010b040b190509071101020c010f0c0c02 72
    0x480e03040503141c40101e0741c005003910310706071003c50080e04120920081200322800c140d5400709141c42c101000e0007468005014000c203106080301850000303185441c107481071045c0c0320301c1034106003101c000f414410b5005065a8401c07100b9104525100d1030025011001e00c201c401528106000306045860758007000025400010510350091442c40001c104e42c950500ca00d01c103015200f034003918041c000002500342c0d15410484810036150460308801640c0f07000607103800704050310f40010301e40c21100040e41e05116104000c3c02c1c03448042000010404c0004071403c0003a01c594a810f1207a41d61800c0c45481000ca0310700143c0d80190f500020b24140c0b00c0c03660540b1800e80954410985203400c40c000e4803a41c0032a24015a40c2d44401c003003503580c101401240f40c2c40209940b481d06030b944440702d0400d0800390303000f0745201c0d40032000231800c0c442c0300b14400c03c4604001c03002195a40300f1035110341e0003024400b160310645800d0007500c148150203018120061500900260301e440002074070490001d030 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 215455269 1250 215454019 215454059
    0x3210708040f0b07090503100b0a0819080c0c090c0a0f08061f020c0604120221030a050c16090902100f09050402070606080706090303080c091e01020a0605190510060504 74
    0x2808441c0086d85590410507506040704142c0001030219448003030228544a5810090340c82d4040004101601c0c0034000d02290300b03030003002450700c0710040083d10782032900804219510680720700900c05018251001440e41705031035206c540403503070201c00c03c0d590550f0842e40c0c1c5500422100e50b45100035501084510030b907501e403040e107455916103400503030590896002700e507107182c0d481064421820030840101584a00070b182d40c290030840c9c0580e507500d110300d00315801040004540306102c0d00d07041000711804011451080092078513070901100809003910140c0c030075035050120721003440c01000031800b038490039a41d405515003054103101c007940c8200300803110780e0b40d5a00b000504140c24040d11024210b565a180d804a1450500600755003020340401e100102c1000b00d08140e90b68641c00514030001c00300c10710342c1031413481b00507820301c50b5000d03002d0921801d100400881d40c0c02c00b404170302130940d0044100660348980d078a00013640040d004100110b00f00300428001045440584c8040c44 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 215456519 1250 215455269 215455277
    0x1150c030e0a06020708010609051b0d0b060d050403021b01020c0d020f040903050a18080303060d1121010f0501080a020910080312060a05040905060a02090301090503210708040f0b07 80
    0x703031118007185804165074040710042c1c00403101801008420b0140100402c1c81d05001d220504150101c1070754000700f44200641c2d150700060f2900c0230000d94105c20f000300402014980c40d0550710f00e209000d414210307400c80050282c8211240c800202c0040c01c554030a040c0e0041403210030030350511065295110083c0c1e0320141c0741c120b001030780c0d40d1800b8400c19603100341c0c0c5007902e525580d48003421402c00a40140d43d500300c004414030004100000340c0c0d0b400541141d2403080300803d410041c0c4642242d000103034001c0781e020120201006408800144030038810000c03c00070a9800250341190070a00a4590703a400c4442114017600c1c2c000030443d08010740c408419071150341e500b000382c40c56000c0c01c01452011004000c1080703034038146030007070f00901080d2028020035109648898955000030700c01042e066002ca02c100540d1801d6000307034201c2d50712a080f45d9459002c2240302101c070040c15a2022030403440e070b001860032445160f0700c5001d40e512078245091042b0036503a948009000504d100108 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 215457769 1250 215456519 215456537
    0x60f010b030c161101020601050d0b0a050a11130614040e0412020f070305010b090c030c0904052203021b03011104090b04090b130201170c0a0302070606050d08040e0f01150c03 77
    0x441d004200f09100188207150f0b070040301031040000380c1032404c1607010034480d100310044c100104444120036540103403810000103040d514480c00900410003800c0541500c00041035a6030314150300e120341e9055440f05d40703403581d0391110b04100e440c2a22450091707540c045502000f10380000c2101c8400c1d00c00007550700640d180800d07011280c41c034044803580306440d56911001082c004d810f0000680d0b40240320a1b000c5031840c50b00012148042c4980303186240500d554000140d0000d0700c0540c01c24012201c440d00c40903540403410000d41d5400982c00d6408600d1010108403000d03d014031a2140005010002a060624002c3e40318005c3c0704100c807d42c0c0194654140c40009480c00401910500d143e2602c5481e008090000408008a445054080f00800c20070b20071084000015940d500c81c0c1d928000d41c1c2c40400d840d000707019201c0f95000541024501d91810100101e203006081614410400c0d02050b540c0e9000c4030003040d03420301c81c0300900480c41c400c170f282c01c5205290b5015003600030f003461400 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 215459019 1250 215457769 215457787
    0xc0103020c01060e0c03010f080303040c140a05040f060512010b150f0f070c0e150333070306080d050f070201110102120103150e0c030d08041407030501140702060f010b030c 76
    0x254008540101d01c017100000184022840c4060413400b800c1c507000110704510b059584c01c01130340218080d04102140c51403103800240c0d03482050001500c4080c0003480750162507403050001d05410300400d881106220100481c00390144642e000d0740340010441d80b214808080c09641d03560165140140b100c5042003051880a1042d0040079203a11078203c243c0884d2a003042c040010a000d402031181344072200760f12072140d80008042002803015190600100700c0c6e019402100640da05a50118000c42c3d4100036209030180d10400440d40300000340e070040e4002c2c9008980510a4190f01440303000140001130140d4410001044903090b40e000051802c40c0c00d6048011a8109030300c00c40320008000340d00903606941c0d0080a030032202c1040249401c080705c10001e43c41d140030340f0004d030030840d10701c2c000303000e1282c010701d540b0484849400383c0c3e901a0716820030758068607030111214210a190000b08200c0e83c4000b035110f200300982120503030543d0a2880d001c09643c0094500f0108000c1440512a = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 215460269 1250 215459019 215459039
    0x4030c080a12080912030a0e070f060f020307120e0112050a0902010e03070803070602090a330e030c010c080d0614030c03060c031609030c1814090c0103020c0106 71
    0x80d1030448020301070300505240504292106406220402540b0000d0041140c40060441c000382c001d4900551a552a443e4003001040e42001c0310781c0c0d80c841d46100150120142c8413a01c00d9680c65a240b455030300107414282d0352880340f964020a18000d124041e42e0091081c0c80032550140c0515203607918085e6080c0d20702c26914140c1d103d0304100c2d51007404c001150b81000082400d007200f035000e4031300d040c5000155070706c9028591001d030440e50001600301990f50f40d090200090650074444101124206070f4014100d008003294400600c205481051104d010780d0740e101d09500c0085c014203010040c000115600b81d018181241c10580c148002c41c0215154001c3e4030180ca0300400c401d450664079401c040c684651100700c240250070003010b04c24030b401c20f50b08480d0b100c42c0000c58442c8403607002100300c403004156800584618881c0368042228420300764100114540903000b800856468031072600c0b1114291380b40c04866000300810103695000340c0150800c5030029000240969569001c81 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 215461519 1250 215460269 215460293
    0x203120603031306030c0f0f0207050d020f0901060504031a04020d02060703200102090a0e04321c020607020c0303090111101a1306060c021201180302010506210a0311030403 76
    0x2000c29254840086e8042d403015800c0c148265515044810003110306000c1e4840c01e0a002e840d0040c40f443d419041951182c0040c0a800d11000e480c02007150707901c03040280190014001200c100c8a071201c5120341050a03e40c0070b010303036001001a0102d040c2a820003240c0c0d4000c0c0380c118148030b080c24203d03203a07078640c4000100e0080440c001503541e0750150108582d0140640240d2a003519130300034400441c00c22140c0ba903000c002482001040340c42940c0c2014001e088584d00200c91250341ca41040d602541a50710f4840d035400c3d0200c40e540e845210082e62900c5150003800c0c0c0543c418407840c441d541c03050400700d0b81d11010707006880b0008a0206d41c0800c1c0d868983c564900c42080c14400e041a0402521130150800c00c032104100050400c00010b1031202c0e80b01e0301922403541030300c0e0b24001c840c00b94003168610f00544404403c00c43c0f503141c044c2c082c00c02203503401d104260600740c0c1c11036007504254805d14401182c001d8521030102c1d58003901c695940c0902031485201c1840044009500b10b0300344 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 215462769 1250 215461519 215461529
    0x5100e070618080607050702031006060504060801050405040302061b0c150618010e240301051008100234051905010f02090607021e040f06030c0902030702031206030313 74
    0x250000078201800078104011681c504000280c0c440b1003048041404030722103400c4255132802643c2c07076085000203031808001c2c104201c0f010380340100014203d03800400402c2200d005488000741c0741c2c1d981c001c00c0100e480403107000d409038100764005141411504030203c9407140240ca1070741005c1030008554980300f04104140c140300801418004145001210b01003041c061401400540d810711068000540c0e001c1c10240850010142219444410542e1000d4140000c0c00070000c52906026141d04148184954200c902030b0f20700d840c0380e80c1d016000b150360080d03d004600c500c88401c013890006007004030520302c01510000300b846000407018000c3c00c1020134082400c00d04150745061007402c680c2c140b43c0184505104001c0c010301d64407039009603615190110b815040040b03002090030207020941030b8840c1e11600c0c7c4518140d03028032035408881520b010b43c4944424a8a551200c0e040340320036030358000580c0c401d0084006050340b00c458980d00c614044c0c00d403401c1030307005080d45010300c40c19000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 215464019 1250 215462769 215462773
    0x3150806091c02120a020319030f060506090105040b0c0f0102033c060d031812050c040b010509130b06270108060108180705060a0c020a09140c030405100e 68
    0x240202001d00304501e46080d58510140c6030a42440c0601039a203185105212400e06400b00b60300180900038815140002031503914007296440d22000180285800c1c0080e0111a150000104d40c13810f091040d90402a0183c4810780703010708040781502035400048072004148107203d015804107800f0b00155006000410b101440080c0314121840807415003d1101c00c51840c80e007854110b41c101d241041e4000901b030315050340d401994101203405550644095510030012a800030f01580038541030304007140a00300742c40d042d14881c403c010544080302c08890004000344400700041c50280b607001c0700c071402030030002034110250002c5a4150401001071544a0b080c005050006400703803c99440c04100740b9044045151800000e841d507100900308280007404641c00001000e0100072210140078001c0045850b541c19480082caa451510001c0740941d18041d40000c802155014071284256461036540c455560700c00184406e4100400680d842c0c0b09404140071044040d100f2080a5285800 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 215465269 1250 215464019 215464021
    0x3040b09130903021f1404080405043b0a0605010e0a0b040b150306040b06070b0901060f1d0408160506150607030903060e031b0d180e06090703150806 66
    0x10800d00011240106071182c1c1401c003407400081c1c0c08120503101000c8101c42c41005425400440010808489205c6100f9180402d00c414025000c025200326007080341d0501c0450405604400d152355081d403903184c9106902e520f08041101b600c070782080c84400c0c208036942140a03031200d4056038400e0f44407101ca020010240844c01d445400703580001134041d02c050000541800200749100a4501040b84120010012408982e901c0d008280300380c2c0010072450711400e850034501078a00c416a40549a0f6184c1180021750b101c440301283c003100e00c4e1504200c1900c1680100c82000c0000820803110b0082c00c210810105043d83d19001c8003d018000a01051a0080b1503044080009800500c660814000400081e40c0003294906a0394072104c0402c0001c652210103255024420812614410309100c68054000000d405c075261011640c86001d55041c1c0020708071041d405002d084012190140010000c1c1041d4143c1303a00160540707000104685070b10a88483c1c00c2c1c43d0f1b0854450350f04064 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 215466519 1250 215465269 215465287
    0x504031a0403020604030c060e0109051507080112080708040b0d1e1e1802030607020313050a0e07050a11010e0f0c04060509011a070804060918151205030c03040b 71
    0x945946080151031800801a05154401035620b0100400060401a1440082c810400b0301e80062110b14440710091101c1c2c02c1601e05580c80c0c5c80550f01681c0c075400c0700c200003110544a13040c201d04840101d43c10840b5070b1401e0300c602089520100003a11101d00800c400214808a04002d00c00c5a802c5040012080803010000001030640c00f40f5081e1a401c1040380c2800c00d02440c0ca50310141c0c08e001c3c00080b070b154040c824400c4084403c0003e585409582c08020070342c3c2c0c011008050203010b4100e050429034865007048880e0b03c4a0180482c4d565504000039201401a00108040e05140c140b04118141068440c0c0c299150040c0d1190035030001030080045d80d00400502400c0e1104640070f000d154248030206003a003505110340c0c0000e03441c0b04804d4400d011035070700300e0b038040d600180e10341e540e142c507014017a042d5080391080c1a000140100c80da102c40340c45219a8074800d81d041c5049000b1442c18000e00c8024110002c291590701040105400c0c0300020001800140158a0302030f031036030034075 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 215467625 1106 215466519 215466533
    0x6020d230a0302030105030d0906080a05061908031905040b180604090603050c09010602010504050703141f0515030a0b0135070302150408060c0a1e050403 68
    0x2462124050b8141c0003503050310815002c4624a40c01d113807044401c01c078544200301c0000d6a803804902e1080c0f054101c079030000c00003000740c10141ca00001c0c2d400f8480482c3d001c1061588006040c1103044014444840481560704003a07040c50b00c0c1c03540d440a68070500d00e02095075041482c240055544000031f0760b01a00c01d0f290100602c64480c07404c0742e505d4548903480d6114000d001c00000e03070148140101c07440b981d072240c003400c00189142e8451141600c040703a1240c25004074800190105906031901103c4400c01d1004102d82c2000bc10021040e1101e11086010b0707000700c054040803030000e004203411101d0601416190031004050121008550790750403900002d60036100c05040400145081624003c40d0021011a07000c040020b141c4220300c030701c1d40590000790001d0340c45080754020304682c0030142800391140c0a00540c03581203452114002d004101c01103000c1c0140415 = true := by decide +kernel

theorem cover : BRFrame.Cov 215287769 215467625 := by
  have h0 := BRFrame.cov_init 215287769
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215287769 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 215287769 ≤ n) (h2 : n < 215467625) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
