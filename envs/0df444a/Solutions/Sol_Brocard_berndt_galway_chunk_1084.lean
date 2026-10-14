-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1084
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:10:16.838281+00:00
-- url     : https://prove2.me/submissions/8b63b6a4-41f8-476d-b016-6c0a6f889282

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 194784172 ≤ n < 194964028 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 194785422 1250 194784172 194784203
    0x40501090b03070c08030c12150907020d05031303030b030d080411010e060d0c0e030307050703110f0d0605130b0c07050d02120d0e12190801060315050d030c120e040513 74
    0x240c45620241c8040041c5c1f105210010702e1600500c48140604107000c0e45c68010b109a0041c4071003000018020425900700850a14445070000d0880cfd501100c2c0f845015000d0223603150940082030b054045030707014410404d4800600d038104805a01482c003e0307441c46c00c200022801165a50448141d40750041d00c1480310307610300e01e00f40d004603131451142e0600f800304a4490300400d00e59045040107a82c10f41c81200d0800900c40c042c1d1080300d442c6000d6031003050b140110808110b451211000080816640360000390240c1003800e8034074001c0c0c1d44500010300504000400544c19046600161418040c4d004076100303103070000503080c02d020b841c0c0b105c3c00c0c2820a00700901000b0580e288062007240103144d0350701800b010000040500007051140c66500201041006200003016000601414540004280c1c050b285103480ea00b228800c55800c4c1d00784003640f404483c9400d000400401e101c44a1800c14522500005400701040c4295410401c0e5520075440d5560301858880240040b1145411034 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 194786672 1250 194785422 194785433
    0xd0b0301092a0b181801060203040314030f070f0b06010c030905040b0409020603101d010e420102010b04090206090d02190909020f04021207120e03040803040501090b03070c 76
    0xc2c207440b20182c45140d500e69444440441c20b134803800488100310941e002000480ca8038084102603158041070082207581042400303956481940400751225031040c00701400e0740310400481e61200c0b0300141c02a00c40721a464040c58550025008031896046200090700b1544201c441840240c0c05540e0070400c036180c07005110040245101c15a04192652140030141c0c80e03600040d4003401c2c02c11107404006241c480da10a00905402c1c0100100c06503a00400c4200c114502c150340050b18005a035240201e0b003c0d18448210140c0a5840040700c4506004203440000b10860603c81080c0c0081c05456040d03402c12084030b50019000b076020a09021000c00d9040c07a100c040101c03031010305581d219403440c180c03445000c0042d5002c1c1c3c1111ba2615100000c5040c0409140b1540c4400d80d415070a00003100c3c07002c401454010080c00c02c21000010714003524032207030800c0006070003050580c2d42e61034990080580f254854040d5a003c62142100000c1c4102c0403c11244030320010b907100404000b496950 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 194787922 1250 194786672 194786723
    0x130206090105040503030f030a1409030706230a0c030b030706020a060f1404080703090b18042a09050405060312030c0702010c02041406030c0f0a062102030c0d0b030109 74
    0x30141008818000414561410001070900740008005251a4580584031009446800c0003100c01070090030b05024901c4400010390700c01541c400404244020940044802c01804ea121010310001d003006024110b0101c0d40400d14940181c0e400b0722070020550300741551040284940801607200390305610204040d5800401c1498002e400402c049905414000d000c500a031340c203980f40040080c06900305a04155550000c01c3c0f10145141048101c0d80348618802929a1080c0900e48858101c50400340104403551901d0045c480c41000103640034009040340c03814003c481c00f42e460030340841e02601c0d000680b284200080f540a600e190f840a40e1000302d6000208124180680c01c02070300c0041c0d4403401110291b5204299000d030390b19001080500d050111100d040c000c08060320480801e499a070300800540300780c2d0800300e41500710a80380d50a40f10006800111080c404018460f036403501c000100044118001c0600003161890109800c030341640c100202001512031440c095110103512 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 194789172 1250 194787922 194787937
    0xf07021503270c10230f12061509060309071a04060801080304050303070320011e0b010c0b16020309040203160f110d141306030f110301080714060c0703110414130206 73
    0x2c0342d40300b4602c03012035101c5a0441700401c140003401049681e207c1c00c08105055210000b1102c00c0c1c50302213821303030003071413881080100760180800000295071301804000399002002c9000358403a00d80d59080064045402900404c00012558000058155000000e079003d5840041c09189424142d0350103981010382c044891b06090402800703a07109000a11400d001d00034031020039101ca20300c5440780c00c100c81c543c90760503052001c80c15540003c12082400107138030141910342c0000d00c048022090b071850003056400c5034054000400c000c071f1681034052107500100d06440d001b905084c0c0031070944080100d00301e40b0300d003130303206803901c5804521440c1c440070013203950150f4528008010004010320022070f0000800b094035848407840c03d003130520071210b15010701c00125045506114215483d0b1509104018544006281407062a583c941c00c031041803510030111101c995607031500351013000302180e0882c03195203801204001d52000c8407070f1921030394940300f0b6101001c86030750070803269801120 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 194790422 1250 194789172 194789207
    0x303060607020316030c170f070608130b0103081b060702030901081308210105040204030b16030b0a09050702160501080403080a1b180801020405060f07021503270c10 73
    0xba1501c55802a59513007401031401044c2031844541008403004986040d101c001c112039108005500050002241d602c06540d15403a2450b0781d9218130710f1280c0e40103013054018200400c03620000041019a100a120310328110b030400052507000713640640c50f498100c407a0005600204007285540d80719005003580207102070000105c6403d44e850b01c0c95180c00ca10040150a65924500c41300c0c04040300c0928010300c02110158906429030341e450205a10262000c10030000c0c1c1141010598040d4000611814015200b5000e00d0f6a403100b610141c0810707a024800b41c000c03800441100a800700b064015110180c444000795103c07943c04840d109401001c0055007a43d442110800403082d0160022088095841000d02665503a0040c000c0005500c210340c0d6a10400c401c02c4151940000d6810503410120400d890785941d0010503c00c2d0100c001c10381544d00008204032032014a80c07200c0703c207507101e002ea001a918503031410030382d1800320048842c0c0c40000a0b15401c4050f2056290044601001 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 194791672 1250 194790422 194790433
    0x10804110406170c2407031d1018120c0501051b010c0e01110303010311090703110706021b070f1401030e01090308012c070e18072304030503030606070203 68
    0x140310300200000000c0c015074840c0c1014100c40c5462809129515001d503d50907641d0310101403440300292445031030401014011054605103811078075000c08d50036070b10003900740c1c2c2c4041080c22000781013503000311440c100d0310748000c00800d0140e0583e0300034010320b40c0000e103445640c0c2051b0041d95103400c420503c4004d10030b81d41480c44074100a0240c031411a40da82c070b6091010254000240104004200e01c1113a90300078001000402d41c1828105408002501d2400c4035483e07400c001c0f00685450035031620a81c10000310305013000803503030040030b0512210004d00700101c0701010040d164100392160900c4142c0000052150b210b441c00c100c02200c030141000140b0441e8400341600395418040d040c0d02060a480040010583c110703002c0900d00382070405603080c5100c600d0410949403019009600b080070310380140000c1d4032446802210000d140c81440e81603d0180030040140821a98071141440307500c1c00d880c0c908114105540030740354488041c500316903d0398140f00d5550000300080c0e9040c401e5 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 194792922 1250 194791672 194791679
    0x40302130b1f0e0108090705090c070501020414010905040c0c170d0609050a0b0306070804030e01030e03031305010f0207080904051506030403112b080901060929030c010804110406 79
    0x5490941c40c0c1442c0c204191820a403a0300c00c05801015044409414420194100721000c05d0200e084001d59204031010701240c0c9407126110304074041c205004040c2c3d131000a020901c4184182d4110444a0982c1d50300c2c0b8458542c5c040c041a60000c03104000071541000144000904003c1c0c510202184003d040341015601c14a150598030346501c0701060726580e50a010000e240742c0a000c0c64400c05900803c060700b02090020601c3e04018005020461034102c0c00c0d049a00ca60407982125461104580d01c03410009090358207115000c008407015880c1085600d62021140282c0e4001c540144125040402010a010180800801d000540305103d030141c20756170f64000166001c0e40c003981c1c880310070f01465034030580f6012107100700702c0d03005d0300016220160024241038000e42410a01c0c085245442d400e035192301400c12a002402c4e92400c2441181c044281c2c401c1d2001c00c03442042042c07004010007000e154891b06041a594002400c0c03600142c0814178102405c01454400303800002d000781d030b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 194794172 1250 194792922 194792929
    0x1051303060209040c0302030105060d1a120c0906040e03040b090607050f030304140a0b060103090f02120a0b010902040501020604020d051504230c3f150f040305040302130b 76
    0x52a001107803100d6001c1181882c03070400e8403580d100174125040c11440d650501c00051007500480a00300c902c2c0b83c64854a2040c40992009044056405400e840c03145280c0c12420351141c3c0c40c40000381c090f00e00e41000852919040c0038110840d20680061454a410700480e01d0340d0340d004900f0f05400130010403080d40041d50810619541c0c00d6110091520b9062901d4146e00754444600d0920550b4090404800402e4140050b107812600900f80056911118034051060318160300340a503115456103d01144031401140d8080c0311849080105400e81e00c0f0305000381203010ba8050140103034000c40c001001818803550541485003e42d00311403500900c03195616616104450441d40d002e80e8208540b036404800100104011007000a400000d200501188204046641190788852000c0710400444152200d202078030f02900d07003c2c185690804083c0340e60310683c00e440490001d0034400202c0c0402d100005900403a49995406d18052458080044090b0715001c0e1080f4155900030204080c2d4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 194795422 1250 194794172 194794207
    0x60d0c02072606010b0408070b031f060e03121e0c07080d032a020a06020d0f020313050c01020706020a030503070516110108060609150a050f0706050a18080304110105 73
    0x20b180404881e00c0e00840c42d0180c2c20400e0603444000001c50070700003031105100114002060340c01103d0303015101e994000c910301e0610692185024030114180000c00d0302130307000350500c45c214000d400701c0303400c100c5054092030380e48146004403a0310f400070186070701114841070003085002034000803288460340741c0c170703031241051006081a001700c0d84d80e1a075141260700e01c10302503200c10500c0c5403680301e4440e5400085d459495801c030041150342e000503800c8201041da030260151680380c110071500d80c500300b058036003254041c00c0700f51024400c81c008500a5032002a5010948105034098214220f103075030241e0300303900301030000070600105001c00c1c41c00d541c03110081e907440790180c003040440702504000549540000f0f01158000c0d03100300700070703101d0341c03107a0005411480c41c5c8a4020350341c1d040c000c4101c516000f22400c00c25180c10019000c000d100c083d070821406001103003410810407001c40050346001e22138078002800c0000a100180100e14160450700c1ba910041c100b0b245001e10952074030070f410 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 194796672 1250 194795422 194795459
    0x20a0209011502070906140409170f04050f1219030207270507050301080a0312060e240d0201080c09011404060306060201060e010f0e04030909050f0414010b060d0c0207 74
    0x203602042c00c8403580c1c1c10464080144420038040045900340a800b840740050030800c1406140c98030300090070003804074600c0c5500c1600002d19030312040c0308204102c065125201b40d503c58180b103020540f0758a0060783e88042c03805000003d1a000d00068480184a0043c0c4026810b602030483c0c000f9413220a101b046081c0301960003d90040c1e444500107804983e8081d00d01d50401030240014454400001244078403280c0504001d102506500c400101400b070a4205003007111000d001e0110301c5140d10f10107a040000c210072141c0501441c024400303c124000f4000c0c0c0024500c1e0080340024202e00e00070b040810040c5040d007003490b0718440100e5140d0140d03006000195403030f40200100d80e4203200c0c1c00060610704c100a405540741c1a03080b081d4066900071458040b4403c00401d0070103000f0341e10040109508042800700d4982000503000310002141e081e20054400516090140010321a400300460300400413070034031051040b4540200b81c0044240d0540c80b8454001c1070800391202e010130178 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 194797922 1250 194796672 194796689
    0x5010504150507150203010e090a0c1202120f0a15090206071103010f050103120f0c081b03190f0e0f09011403010e03030f01140a03030203030106121b0e030d090f0506070201020a020901 81
    0x307d51528400202c21103005007080300390341100001500240220b449102220300c2003a001503030b40c000d800000e0031582220071030f003418810400400c2c06803070b0116210b035007180141401c401c40d2000181d2002a20f0560100a41c07044080216400242c29505620365000300035000050501c0e040c1441d034200c1d0742c2a00241c900000320243d00c0c2c410b56001e0480980b00d032252405180f018000d941d03058240c000c0701d001c400304103002a4801688030007001614280e0003c581f20b4081c843c031003d4080d0420b61110802800292042c440919134101a131507480600e0340071341510020f80c43c21111245560700c0c090916415500c0c4d0100783c020020403c00b441c00f8540c02c954011541d450104040c0030724005500d058020310300030f201000800d4001c4152411203100f0700f050704101c01e074561900300500100d00100c00750030f40005062034099124280d41d103228011b9040b03a4135501300d008180c070101081c1c0301d040e0061030b0401092015046c008050000c0724410700455403218400d50010f0301002d401d030042441c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 194799172 1250 194797922 194797927
    0xe040602160516091518020c12090901060302090d12020304050d150c0e060703030504020d0c030b07020105100b09011809050c0304060c210b01140a050405120304050105041505071502 80
    0x34812000d2210010032194004000e080c116054010400c05e55209121090440301a211044101c83d0111100211888243c42507200c891745802d00c0380c0c2101f1a070a000310310060011409901a00c00c0380c104c040000c1c018041d42c282a13803640041440c0c1c2c5403440450005000008040d100d02ca2100c4106115020000300001c41c0c51244040f01d544203035031020030588100300c0700d590711000b0031201101c1d0103160105a5a80340d002180420a2605d0000e25000500b04004240180c4000f4580207440550003800641c40310703403242081007254005d50900250030000500c0b00c5d0b000e4032411007140c0c5142d0304100813681d22030040c8202c400444052046290000800c0200441c600c03440303050400d1414060441900c00030360300d034866413048003803003884d03520100001d981c1c1c0500c3d10600041000945140e40d078030030420050850b001442414011196645884402c0402005803000c1c2d80041e580ea900b46442d151103001e240c035240b030900c02442020803441000ca0001030f102120308034801009039 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 194800422 1250 194799172 194799193
    0x1206141f080402120f070b090310060609090c170403020f100203100909140610061107050d110604170a030e09060307060e03010f02030901050417040608010e0406021605 74
    0x2034480c0d90030582030300da0101114509582052a203900640c06540303a042440c00300112a02d070a00301c1d0452041e80c4079541c40005c0c0d034000100140250403042d020380f4800203400d0003050030344815010300c80100320320039403d021002160744141c116140900d007140b0807810002c204055102c040c0c80680058101104a41c01302d042001000b1410410348d00440c0340d45000110300f54140603a000c0d600d096a101c040042c10b0001c510b85100c45c1076003020549040d418204812402c280203485004045960b4440d000005040440d880301242d00181542094440c2e9540b0381c0046008440d031154000020300010561009009842c00d240c644030000b0000c40300c1c1e509020300802ea0030600903119000b503108000c10390700c0c08140002282c0c001d040111960715014001307400b50612100d0002041d102008201d02c0300e0341508894000d600883d85484d10720110080d1364140d00c903034012903021508800041020300c244c40d140f07a80c4140100001428884c00c0c2000c0034030300c0c0e0307032000980380e40d448910040c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 194801672 1250 194800422 194800429
    0x7020d050a0512030f130204060b0a0c020a090e03070816120f03050609010315050901111611010311190203040e0f10060e0d08090d020303040608041109010e0f0601120614 75
    0x41a10a110822504514040850545d154002001a003c0c544443c0702401151140c0e04080e019104560145895481c400002040e202c20004180d200b01c615080010b624a150710800c080c0c0c2015102442c41d12813207449604007039200701450640107000c2c6140c0c0001c200d01c2c00000480f01c01580d0f600c60140712240000b019514040d020510820b20380004000160340e6a2100340110401d001c040707541d5541518180c01006042c170038074551a400074806000000c3c2d0342510340e0301c0384600003401c10307815048011400c407201204503040290042181000070211400c80c501645810b20441e4a0700d40c99980422045a0035101d07035401e1154001408465440282840b000d45840d1038421056001e4100180c05000645009080040001185010340d21400c4100340100d801900305c96807103030f54030001040c65074111000c0c1d4813a15546154061494480c40a41c100c1d03101c107414070010345654040141d50030010746080d0520903850f04004032101180582030061044003640d025a28044051 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 194802922 1250 194801672 194801683
    0x12030a0f06180f0b0303030a02251a1305010f0605011e05041e0f030c060212130b090105160309080f070b0a05220f0f15080105040b03010207020d050a05 67
    0xd84419040010034040007200030ba115078401e56180c00401d50306480114100100015040140c141c003002003004000c649640080c0900b944520100242c2885111595101a80c104000742030002100d0329081d42400d0300003440e00540c540c01248503442c81035613410700311440d04000002407600e03120100219a0000d034031002c0c030301081030681c948100c1207400800e1803055000faa007041c000c02c0c0b024034484041c6200b80e806440141380c3c001c402501e0303003400108410a40300e184014030908140060300c42030382e01603c4d1700c000d850028910103401d20030790450f2030304219840703410000e040c01101e10103001c8015910185009440c0e43c1442170414010600700040c01001555503407114004200c4542c0b000122058148580f40c800d071502d201e17034515110700c00b19081d07094015101d02c03004602660542d102104640c848418a0022503461514078410542c3d20f9220022031401b0b0010049824250021104098024001403420300664000f80400102c26400d0b03800e940100000810004200312 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 194804172 1250 194802922 194802941
    0x14010204091506050711090a09141e0706091206141303080106020a02010206161404060f030c0905010203030622020a020c040c0503010305120c070b0c0c0a05010f050904020f090312030a 81
    0x1403007850315903a5101d2040085402000d64002ca411f000005d860070000c2c0d10005d04075500c20341107200703084c03100c51aa44e07030b00d00d1100002d07d04000032135074030108200140a200b11407154413000385141ca00450003098414906091390450340b14050021030b09881d10751181b040480348031954a0420900300145070b4101600040195806046c0300c1d00941c0c0c0026000e5400000400c03c00d02038100303240c00702c03102d55000703044400401000c9404541d060700003c21030030382030003130340e003001400c40b0312070111901d25581c82601c1c05a001000441c03250301302541c2c40b0343d280035900648030490707420009400407070703001029450050f04505000b410318505405642d170000201d00d441419541036850b9a500c03100340d120b0403e41c98100140b41078402c107007072103241c00510800348155218030b0070070701c80c130384940300d80f14918400c01074001d000c1403a40c0140240314105069607203d07030608000c4018040258860710410711061003d010581007030364100182c4441c1009103010b5510390510000c0310003603420104 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 194805422 1250 194804172 194804177
    0x90403020f060f0105130b03010e0609030a170606030a0c1404060c03030f050f07052503080915010308030c1e040f0e01090603030503150105120103110a17031614010204091506 77
    0x411055440101e1039103640c0b8082000511f00600c800064012310051000c18600d01800082000580002c0090b10b100300164031a44046400e440080901520880741c05a010409002140c0341c0002e039031080044a0050501c0d2544a000124480380d40c0c000794008000641012060002c0503454015020340c140c680b403013840241003a036087c0848680042042c802c02101141075041c46100e03948a06a20180710508400004642002040c05c03804550981c624030401010990107410180305504903600b02d0042821510340d64270b40036041d40141034000c2c100c10180443c10420422200906c0100030403008090b096142407260581100164030040d25117280410800c04241c1080c1200da1042c104901d080e0078000c0040181c0f1140103500441000102850001c01000380e0040040d00c84201155098102c84d51142401001c1803480c003035107140e0f0001d02107420148841a0802c400f2403281c101682c00502c180d030203d017207800aa1081c1c0d281502da600100350709110080070320140c042072 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 194806672 1250 194805422 194805451
    0x3060519020f0a0302090d080d0203040b1e04231b01090512120f160f030206180a0b04031403090a230309130605030d0806040501142d090403020f06 65
    0x42c0441a0340d008200c000014180c0010307078040c2e1540e421031043c00903944802859110070040f8600c500a400c102da084502000901c003041032450300200c8041c0c40141c1c0d000301c0c0515a500d035209015106900007400d201071110a07442116030060140d8091801114256442c1014a6000522003601a40142d026403030a0101c06100b0201003055100c0160041b4440da031000031100c030410342d10a5655416000d00c000c1d10210801803120500a111400b039400c42e486511110006800314000441c403003040d070b200c000400000350348004880c2e4414002d04010b41c3c0001d034035146040702d03072080707540e040e098101d050081c0c2084030120f21009080c05154402d090000d01041c441d0ba02d108202030b05200d65030032600e1850580e0150402c001400300a1701392070144010040c0235000c8103050381e00502c030300c0c281000810010810000240005801800781c3e4660048104010611a90115901c40780c010424981e100c0d440700340c40240110b12a0740107058a1150504660402d40e014010000c0c41900 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 194807922 1250 194806672 194806687
    0xf0901050a0605030c0702060c0105090c01050f07060e01090503040626070f0c0f080d0903081e010312170106050301030213052802160813090c0f050a0e0a0306051902 73
    0x10340311001c1c1601d100d820b0403a62500d52031381c1007005015810000358024130020307001c650a4419000302e40a0980074040b41e450400b00c0006480c603019440300c0425001c010702101c0c001c52101c0d0000174003c5803203400050f10381c0e1369844c0d80d400c2d40d102e0703082800480c010300300c030040c2540428480320550301c0025866280f8100752400500d80745001c00e91104224094400e0420300801c0000c3c1800142d202c5901c540d00d12880035a04054900e00105a010032100b02c001440c0401911211061401201c03940c0780d942c1c219a6800c042c40c17020145041041072031000032190840c01140311b400303171100c2c1e141c461300c2e0f6145204001b9102d05c808182080103007407006202c842d03981d80c00c998000844109901d0954091102e88030024080d41180488180101c18408288641000100070f905000190205510740760000c0c0070030344081c5002407000902d49030a60000034801d0025201c92903003440c2c00d482c80041e80c5e00140740c0000c1600140c40705075a90051000301c0c01d4100c0c1843c6540860041035060101 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 194809172 1250 194807922 194807929
    0x50607121106040c1a0c0a051e031606180c1415070b060603090a1e052b080402060405040c080a0c090303080c1809070c1104020702061902070b0705010b0f090105 71
    0x1d00b4490402000703030561041c51301e20303500801d603011b4808201c115103078094503080c1039a81307020400d680d00c10000d000e043c03110010b0020003101c50010003074a510024104981e03d9400030010710311203003c41c801d00c810030800655509010b00c01050f01014081c01c0201603400c00c0949414203403c1e03885035404001e03e00c001400741006690200c13044629603126500c00200609002245000074208100004100c111840c44070152690f24012411160706031903494020b10407142d580100c8049818071086030b040103200b0268a40d10034400341420303082030395405c04601960284521f45010901d0001005409649031182d113100201c00c0ca000c002d100e1568801801100c00503250101c14100041c19250365031005003a10480700d000b404c40700f070500c0d10180c004d05403051024225110204050140d00c145010300070f8402903a0010040c610f000040e2010406103a4503d2013503041d4024000001059501d8902409032540501d00208d5100c0c01401002441c0d455000d03001c0c445e10039000184041d85 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 194810422 1250 194809172 194809193
    0x10503060604270507030b0903030405071811120403180b0a030f0e1501031403040b03070c0c0801050a150503070605070f05010905100603050c010201110901030f0605060712110604 79
    0xc0094500240d05044500140c01c90002d03810031a04101603911148104040060003604913402005481c103152594888c860703ca100a41c0c02070041e41c000b020a0000c40005800c0ca145141d44040003c0c038507007040c814128070b070420350340151031408050400c001d00d90040c6010200d41c410f4000814500c5c20700c05d40054500074030300702038105596054600c0c2e80e40c001d6407180c000c43c2c4105c0100c0d1100c0c845420903540d6000240400c030b410260120704041e0001c400000d0301c0560310401c4010342140c2c3c904038201e5400d24070600944111041344d4002482042c2842040d0048541400106620310151070ac030b00f102d482540070034042da101c07260400c041903001e41695a8942d01c454154805021400c199014241d1100301801500071200d18226480c904d83c410f000701ea100c0c50075a225100d07103800590032660301d01d408500c0e048007003288e045250321031380c40188032101c0a94000381d455103c0703003c0340340d580010408940101f00d011940086540082d5901e0270402d40f240248800e2034103549441c4400d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 194811672 1250 194810422 194810431
    0x6090b030a20060d0f020705150108060105010c03031d030301140108060d060908070605070806100305040c1e090204080c0a0f0315020a0c060212070e0f031203150a0b040807090501050306 82
    0x7000c0211032100141c1d80c2508880010303002d40b006101d09581c0d1217081e03000358883e000c102c506201e26080c10f1144005201c8103412212580f0141605070328100040d01d003d5110441102050b550341c4241c903505800350368240001e40540300441c2c4a40c10300c82841e003841c00001d00d081c18070062000300440d9a4440c1904000d89620000c00315901d040d40c03a054001d402007404c018246030402c000c00c00c56540c810f0269200d2001203581d6040301d410349409600b180d07001d41c1d002e02841064102030000e10169000c0760f0060200010300c41e0031039950f4244030200d03009030b0041e0f842500015031b114403502c1d02c1e03120600030b484000e00151a452559076021a102d4140400d041007580200d032074040e25001d00c80403094a030308a5801e41d81c03240c21003802c03400007104666030400300310b0030b02122885044c020380b089141c25004d401800644001c07411008290001040c00e070041104860450068440001120062449004198450381400c80310b0303007094140e42042d100c030740c0b528004124a41d00020300c103800 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 194812922 1250 194811672 194811713
    0x1140c07050a020a0e070306090e0c010e030309031506040e0c031c0311030426190518060c0303010312030c1413030b16030e0d02030301050909030405090a06090b030a 73
    0x1900c035945405401c090111101940c0001062000500484039000c3e6510805803507800b002810340310381c20300d41247c20015420f40c0942c00300e07010301000d50003500d54070003048000b8106c07401c00401200280c07034103140e60103401da860801d00c01c0c400b0b14105806294100c8803c400500088a0420042940c030812030803070200e00720300710300c0b400c10103030180c2e211070700c1c0c441710f418000d41e40d01c0c0074281250001705980704081c0e8281c10540f40078101048105880f009007106801030841c0824890440380707500410900406e01c0c00c400f003480280c3e40e03200d004082c908541c034081e507229851820103808070014002d808041c0360a203001e0109659101c000c83c082e000340e0310860b540312100081c0100f886506a04002c03c620510802d001c13400c4010101012020711550742840300d080921005034507200300d51203c602503442440184651f15183c0380d0035034003101c50300c112400c050391080040c3d411007069078406803540d942d450034020441c0b1805441c0413141c0a40c01000c41d02503a66400070743e6130f031242c2e0064a = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 194814172 1250 194812922 194812927
    0x315090203190f0c1518030210051324110706020709020a12240b0403020603060913060906061703120406110405190801060f180f1407020a030e010201140c 68
    0x8103c0324100c1011002e800c0080036458588400400c80081040e0b8a0340c80441c00000212210300340102d00351050741e60140a840050031000c1c41074410307400461450300400118000454100c10100c00c4000700780b0030f0300210784016440343d8003a04003040b61004042c25008070005000310380c1c000840c8800ca5040f0300005985200b054000c95641843c903040c0e14007181402c0c15448400d0410007a080084d400a0707601c400f00359071b80b454549a10a034400250002c0d01800003403200d24000017501d030b0080c200229082202a655650003c5456007602250000c3c0c0d9003c042c820340c480745000e41c2082850000442c0b401e020000208802e103c0100002c000f070b501d55410b044802c6a10781950002e1202820750302c2444100301c020084440f0a009803070707803586000000101c10082645101c02c03242d00c0350300c80e1000c02c2000100c1010344070110030108050b4450b030a5014200401e01c405208000c0c40d0b0241408014500e0000e00e6104d056280750304581c10718103600c0c0d960312803805883d005030000004aa = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 194815422 1250 194814172 194814223
    0xe010507020f0405090601063e01062c220209150316080c010503100b0d0207020a0311090106020607090e041b030503030703060b04060503061e03010203100315090203 73
    0x142c0d0045200200d5401506000030710034144400a0030328161000c603220449044070f0a4001e070b00f134010110320007007080c031441e0425a860b20074003c2e0164244814001041c52515110054048141022034014031000c0340c0c4034001d2001040c0307580e50810701c012030b52504908450a8001c080b0302c2d04074003a114103d03810101b07240030920b200c086601000901036625410070103480613030014007072250304880d01402c064604150b20030745c02c49124020220b1000e0325242040315200c0c2c150419040c80340c003d5820040c0c0c90240e84d8cc0100c15000b5031042281ca0b01c1050400207002c000c400c10303400082554000c50a018038150000758101c2070b160a01400301d003940c2d850030039020b841040350505249469248002c41409000710003103214490702d880901030103a590300d004000e4440c4d803045000052003030011a920340b07031041d0840c1514121340032440300004031000190890748240c8840c517283c24003100810401c1a21a00c40700c80c0098008200103080107900425142e85903800c0100500085281c603d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 194816672 1250 194815422 194815429
    0x20304260703050f1e010e12030c0d1505030d020d05190e040207030201020316080112121809050a18080307031d150f010b0a12020c0c031903110d0e01050702 69
    0x100019504036080b1500e4504c0d03e180e5941352590303040c8940800210304025881c1c2001401940101c2e051540148210f6404944400168101804e9604124010807e00180d15200e0242da000000c0c0720141c01d80480c034100c101441e007540086850250740245002c0c1d44280c0d040805d0b00c0301101842c0e0004401c0e04441d0b01100d41d41001d0304103503842031010a00340c0600d035056019511501c40c007a501d0584030380c04031003030316401b409202d43d000040c443c41442000450f1100c1c2c1d003d15410030b0034a000720320901d075407908500000d9080261010390301c00400048211078050309d03c40300c4445034010400100b035203408115220003440d8105160f114041501c007006900d1022002191030819034902d42044010881002801e550240c01c01c00001d00101d0488030340390494440c440e05488101190031001d100d41b010390041400d00340e03c2c0c00350701c190303a100b500c017406080b02c10744102d40c50032030300303801c81c9405010890b4884150b011903105410401225410101d5800d00c0b0200b420000d45401040c03001 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 194817922 1250 194816672 194816683
    0x21f0209181003021908060a0213170a0501050a020702060d05040f14010204050907030b01020307020d050f031b06090c010906030f020702061c1a1c06020c06010f06030c02030426 78
    0x200e2980110110402021840c0800c800040d04d01c02c03514400f161000c000300d90580c4a043c000c0345019044a0301040e0404000e80c020305441c0f8411445003074031a41d40c4201c5403080001104080650014400901000800e00c901e580c404501c00c0c0446c1030810b60707008a01c0a01a019040c072080d55108080b50501809420000c1a10740c0546080f007010a002174040c046d40140c070580e070003072a04c1c001042c0110700a0144406681c8107034005c600b80707036071a000c000c01640070341e030281d6850080ea501e4011400c07080c001880010f042028458451080c0c0e0012480c2c403500400c8900345401900c51130340340e41c2e4407007005000c03500246800300354002c2c10000c0400900c102d003002503004c10b0000c0d01540048080902c0300c00407500b00410091140c84003a80704030b00e428019065481205c0c1400d00b600901c400d40d0104e14030b40280070043c00e00050254291070200c3c02c1e00031001c080904d51040140a616014010300d40800384061801e0034035101c403005204810301d801c201501c910780d1089082c203008010 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 194819172 1250 194817922 194817949
    0xc060f090d0c14060c07030f0507020105090402090406091109030f030a200f07090501031112031b160608010810020a0f050d0b0301060308040501200c0d02011214070f021f0209 77
    0x1030f90100d040200b200c5402d035100741021401705113170113014232170580102d096610180c3c0607103034140b40c84051020070000b54424008240c1c803950301e18010036038825510964000007000c54240b0780e5003468070708143c034100041d6603030039460f4402c1288111855205640480301e80e1010300c05a440420824624180080c942c29052a4848e030400007602502d5030300106d048074058058441ca04021034144011301c81c00d0318050100350b1040009503071010000c2080e5400d101c0d0441a240010002c41c0070540100c640e03400309000440010040c00141010301c22900c0e0032080d40800c601d40200848040c10305441c03440d08805108001c10de40d500105e81d2303000960381e150020000c004203034480c0303031110b0180c01a005c3c050010301010402d40c020b480c00794015450000b0079004010304440001001401540048101c1c1000b04c410a0b00c070341080280140c20080f440c0040c0b600380c918002c0e42c01010981d041e40c91000715845140144640c207030300c40340010003046c501009a5100c400002243e00b00c040610b = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 194820422 1250 194819172 194819213
    0xa0305040f120c1103160303080c120906010801060b0a1e0e09040c170c010903060f06080a14060c12070c02031c02060108070806060a0608100b0c030c060f090d0c 71
    0x5808540c03143e4401c0d449014a44180d00b50011400720105041d50b504038414030715000b5440c2035050022074000d8105581c0200002800e52034069003079500e480914003a9880150350b40074000500c480b02007805060702400b640100c00b41040304d2403500600003c0403883c461020001c13280a03400542c4a507814401d00c0d880900b82c0121820301d481c00d0006030703455102d540c52115003c18829503590020030b02d00a030710300595804c0c48190a58a60320009c010421000760344075238a0701c00046141c030500034850558002c2910017041c1c41e50364801c0d0b044c00780040885040300e500304039140452010000107030b001103407071610a1180000d480032924140b245102404004403500c0100703040356001401c0c505a03204c0301d00351542580d5540300240c1d211010358072180c0c4850649020f10015208500c00e030341c41800b0929810505036a583d12181d6944542c003000056080000c015a00d05001c1020075040304446003840c105140140c4410b40f583c964100b200100140c00004070280002520415212400709 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 194821672 1250 194820422 194820443
    0x20a0b070528050705010912060f060503070b031501170a0504060933050f0f07020c04061d1806060d0501090b0106050c150c0417150c0301080c0301110a0305040f 71
    0x5002124407144510ba040b24a48503000011545500c542080c2d4100d070003c114000d00d00c6100d550381d00180601c2900d011840e0741da0b03a40021a030b0b8040003900700404070760b45880c0e80e030f0621115102c041524141c00728180300c81403040c0a440040d03020215404210307200300003402c0d1600d20301840030b00780c0280064920611011800c0980c000c100b1440d02c0700c0c1d440803801d0800c5002c3d07210350301a94011a10307105154080e100164641841c0d800721944822203105954045400800080c06c0310070642010203401051001000e0307000070181a140c002c41c20301003c0110703a1000c0b00607a600c52000b801c1a01400c011551282008030940100e108a58090329020b15903171030741c0005001e0307001551212018071442c0d268070484240c048000e80540c03c00892a031409003409a1003803c041d19800c0e40d000c600c2203000030701d05c4494401a0174018041d90408580e80c2d4035180c244d901d03160003c030032248aa490030000b20244080a41200c00310b405608000c6070aa030342e414800070101b8000809031054808 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 194822922 1250 194821672 194821723
    0xc0f0501020408010c0309210909061409061210020f0d0204080d0e0a03120e12060a0e0c2706041e09060c090803070201031d0a0c05031207020a0b0705 66
    0x1034000d001030f590640c000b08080c0d40075007000c8060f6060b0b01030140070040101280101c0900c0024025001061070500303810340d0703503204180c40c00c0f182d0992101ca50713042c240894010501d064508180c000d1000c9895603a0030100051041d00e1314103002642c40c115134001104100069040c0644240c190303020300843d142c1c2c1e0345a900e1901c8080c00d0840c1c400095065031020301c685442480031080d41d0b04401445092002d1900030f03200048800541c0d86d028070769204540003e1000c000e141c0c402c00b01644003003026844c0d00ca409107404006226544100000c0007080740b6425145000d040552920001d001c842c0c4a541c08100100301c0108800342c1441c0c2da6504c0050030549402c4941c003644140700c20040001c50100071240d4030803a000c2e00b486500204004000356110383c104594a00c9540020110041d2201c03005250115148084400704509001008989000d0011000c155060701c0011324069940d4000790121004d07010741440c440f000309104092002c20802850703c0001c0c2d2311201411100d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 194824172 1250 194822922 194822933
    0x10050d030206040507120f031409120a03080a051605090607050d08010303080c0909150307050915030106091140030b0709141c080a090618030f06020702010c0f 70
    0x20700303c40644081c491080c00280c40c55082402c4501c5030f40001c55040c058030142e80c226881044c40d82d42c1c1700382250500c000d06841d07603400603101c502e121140082c0031200103807401902da075400401105500d8a8032040103903034007400c1c2840080801078a40329540e5000400000d086014541018002c1e101e01d0b41d00e10500c507086075200741a81d01a840e400380680d5030b0b0075152105d10805240c5500300126030041040c0748140117250054000080c1a504055250004036900300c3c1c007100c14014841e2410400c24030360500b0311560000e0801801c003400314800020b0700c64542d11400c0c2c21602c1500c041eaa44a07040c00d1202d6035a02d00004a861142c2701c20102c0301500358070001800281c43c010040303004507100500504087c421113070711100c561092914142084990500070042c0b02030b00400c05000400a40c5200013407402050544500c0c610600f000c00041010f01c82a11401010304000c03014008a00441442c2c082030382e0201c00580e1b03500651004075091030f8405401442203907010101c008109 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 194825422 1250 194824172 194824183
    0x204030501020901110d020a0b060f12010b100504050a050d150c02070501030b01050a020709020f0903060c19020a0503070204021c05100e1e0406090204060b0f0c010c050307051210050d0302 83
    0xc200340c1c0c031a0500298005c00a03100c3c180500c2a902503401008213400003084502d1066100760002c0031044501e400c200402c0125552401040daa6507640c3c1e1410810714041400c540881060b29001f4140b608003408202c46070b100d40141071092102240031000c2003640c61002081102403001440130246034000a99101101d001e094082401c041800c800e07548591b068412085a079401040707a103240c0b14801c1700941c00140300104000040003c0010740e03c0c10030030340b40180a6a1082030b80e42080c08184141c42c003a911072781c401c54102c2c1d003898021076000070a441082e501100d00503900c2e0356010b009115006e802c07034040892400e00003000110303401c3c2425003045401001c03150300a42d684802e000480d403406107411007084220760100e404541d0301c0e0b200545091000c2c00000c1c08035111100305c60283c1061070700c0080648001202c16030100d0a002c0e40c50001c80e6400d0503800c500b42400054224062141c0c425030300414400010040000034000c1c1d00100b0014222851007442c3e81030094640 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 194826672 1250 194825422 194825437
    0x2031501030c050402070308161202071104060515040614130311090a0c09030f1a0f090f190206161b030b090a020303040b070507091d0c04140a1e020403050102 70
    0x450b2816000a00760420303000b1035059541c03594494229555410005403440b1180b45407a04010314045054000c2803503200412415004800c50280840070204020a482003904243d0042da80300031200300202a500c00c2e2019580c51382413008441c011111005503d01074910922101c0b1380106001045c0300d02071030340ba034654a080c0e404030030695035001680c05803409a140840003400581e001c00105171403103207084003148074980021540049a82d2400100c03010350b15026241e0701217050041d950000c020000c0a54981c102800101824490309054048440b90190040b8400104c292080e200710166229040d0310118400c070000b5190500c042c00940c074003044070000758007400300c0d0701180002586100203030b008008601d0581000311658650300403540465451160510202d0f5040b414001e103015103410705400321480020b40c55241c40e00c0e482c4061180110f1510280d000302100482c0300d1030380b010034510041342d110041c1c2c1194546422540302810528030108020040000640050400 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 194827922 1250 194826672 194826683
    0x2041203030b0108060f100203071202010e1b0f040b040b040c03020903010b090121030207170c040b101202030603030c01110703030b1009150e2707090806060d08070203150103 77
    0x202ea80c8070015140307100c080d20000c0c1e11092400000b8841e103050014502d04041d01e1050768144003541c1c0c0c03251440c1903e10038000c00342c1d44a01842c01100800c200744103c250b1000d22400c1043c102c2c8001c10a191040342c2450b00540c2c036072261800c03540306c1e40c0040007001c1000c0c10400c01403d038460300500a400a080e40e901c42d50815003104614980a64041c0c1a50a001c80c54008040d5021085c02103209a1000b202940a1600b00083c20420194128400a554000382050884540402045a400780110b511401446000c92400740e404029251b5030340310401c00513569169000024030354080d110f0201803c0d8207140801c0c408504000c050180b10344a07880c01e10131a644a82002030030160604100300040d2442030811860f0a1a1a40c0c0b030030402d20305081014400030300109805c5c1c5c8514091851160f910452402006440a0007a502003a00e2504561050070084420f031604809090795220721041c8001c04240038401d0304560243d54001c01300d440704585000081c03001c5000348030540b070 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 194829172 1250 194827922 194827931
    0x609120e1c05031603020114040c0603110a080412030b06220f05130f0b0604080313050301061415090603090f0705030307231023010b0708042303010204120303 70
    0x80259051070010741c142d020015505114902030b0b03140c180b0307040c0d0105404564880500400070a2111900c074001c50140c000001242c2c103102c806000c3d600b0b08a241c02c0348140801600307800070b070703c0162160030070392007910010594450707003084014200301149144d206900245241e550781034010715140c1b0050045400d0b01a03580c4140031380c41d0603402d02ca003d410184c0c00941d039155600d550b010903000e01741060700190b207104c0b9401154003034000307030003a02e817940c0001290003080040c0c6200c000284800c40003405105d0420002920341484010407901841d614281c07071102071900801c0d2440c40d00003800c410384074035015013169580d0140041010041c0a500000f19260901100322207206400141400c8000401082a00d200300c5048110b441fa0041603950002031900740035200f42540f001400113070741d0f800300140c0c1010b184c044e8000c450076181008442d00240c02141030f5011120540450201112243d06c15212414040c0006625500c001000300340307c420b01c665901500c2c0241c0c2c0800 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 194830422 1250 194829172 194829199
    0x15050306010915021c09060e034e0703021c0905101119020907020a0f0b04081209060a0b0102070810020903031603171e04120201021303050a03020c01020a110d0609120e 74
    0x142c540101c124020042100c60841032b03890a0340b60b0200100c07040d4590001e0780c07582d000d48008030541a0445116104800083c40b40605a0400007a402084220044040e800482c00c0c003518242c4507204181c0074801103a11040c906016001d07c0071210001d40584900802a007903904140c0003040040744103450b07280c003281c00a0710024600b4a00341e80442c4881031004c0301e44130205000c0000b0f0045a00310000c11000d02d00481c82242640a144070300000c0c01a4100324081905980040999604550105504001040340001c1252820806110050b079942d486400303c1c1c25840340040c041140103119070b0803802c2540c48140d0b10121218010070980c0ba455428040d901800b00e1104d84110258001c0883c000c41d100c0c00c1e20941300030032400010701e0000007426001c00d110760b55200b51140c0c1c01541d000014540c0511070b0b005000700920280c015010543c0c1d44c4203150300ca0081d0140103c00c0005100c04101c03466201100e0640c0001c40302081c098035510040a1003031502025000740b51085104 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 194831672 1250 194830422 194830429
    0xe010915080303011a070203010c030504060605031504021903050618010f02160201140d0e030702090f0907030b04030c0f0629010c0602070f0b010b0415050306010915021c09060e 78
    0x900791007820700a540ba591030b2a4082d040810170300d00070710f02010108542c0303005903024406e11030740d10b5013034401083d140fa2604019044540c280e208034020340095840400341d0f446d004545500541c1103035414409102030307051540c0a6450b070001403031440780c2c4090041461420115066a012140081c400241c40c004a48140c0c0143d10201030840e46081080300190b0140005904400c1c82c28001c0f4105000540300c00107903000329400b0141038200050071015814000c45003503106089440d56400c13414501c0c84ea41d6110f0080c400a8030490b072480115042500c00c241252220360031448882200f00c0c0c03824104000c00760411210b241a942c0c51780e00d283c1e240781c201002da004030141c56644680d41e0300e40355074011350300c40d203012a0031006030500d40000901c00050a40640065480d8903111342c100071100040c03404580700c0806003d03040c800c10040c2d80c0d000b0b195100f981c0c51110080c05201e105101680f41020f400b09580300304c0d1211148807401c0390311032820700c102e8201d41e031010801c061401c20f0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 194832922 1250 194831672 194831711
    0x6030b010801030f033501050402091c1106030a0209010216050303180a0f081f0501080a020d0f060c030b0a0f0807050907090e1009050901020a020d080a0f060e0109 72
    0x205001c24909801003011a440700e0a00e0079043c00b906000d4056000300c48520800c080d250078203c404c06038000040803000405083d180505003d950842c50110700c0000100301400600007d900940400801c10402c01a05a040b0000c0c40c040c0510740c6904158841d0340c0a034211402050042c8180c4042d80d400c03078800c0c030941040716405000746252160125440e820044046603813604141e45500c0011440000360489004080f02c1d0098207100e50007140040c800d1884030186420b5500b0800140100c013070200f50540f2595040b12540448031282c81c002c1c4094048220180040349090006c100305c0c1d40503000356504d03020807a4008174140d21040b034541000140d0040110b030364403c032000e02103401e03d01080c0740c02c16400d04040c9c501c542da900241514110071100d100d21000c5040c0e04004100c2075001d2a90040c201038025410a08400d01c000d5485c083c40101742c0c04c0203110300206640d11002d038012051043e52590a00159445110305010403800388148150380746008c51041c1d0018040700d0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 194834172 1250 194832922 194832941
    0x50702030a12050a0605060f030412020f100504170c011d0115090c110d0302090f10080402040c18030303020403050c030f0a110a09020a030c0909020a0509041113030515010603 77
    0x150310007082c1c10314011000921000340303e0002256242400301c0d0f565110780141c2004000444015501e151030710340060808403420042042d50721408002c4030300c14000c500400310003c0161700090982d55402c241d00035007000d1503040c2c1020800a56410b4984064000301044104c403c0741c2c1c410218130752402d50032140618480041e501c41204107101c031001c1034000d04c820084c02d142028280880d0b413215400e049a441c01000407e0b4001164441d034107240c1402e40054504480c1403010f850804000780802c40d00510091180d0740c0d0710003404c4c1150140b0111004003410343e9817581255202c1c90701500961140c08241c445104a0410003060b1a0000c1c801c4c198080000140642d1215565041ca07044110444594440b0f401c490220b4001e01364406481b40040301e50700400c5110072000068002d09150b001b00320301c180100515001141c01c14216509600265400501c0b25a080c2e000c00300790154a802d0040c0c0e015a450000c10310400154001d900d0717100480405560342c0c0c40005500700c0b800c07c2e0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 194835422 1250 194834172 194834177
    0x8071103030405010c1104060302030f150105060304030c06180c080a06052409250e010e0405010e060607020307050a09090b010905190b010c021f090e0f060f03070801091104050702030a 81
    0x542c413000051008080f441c00440103003000c1030b50798403540080d052142e19884001150f100c80c00350440de0719540801c6004241c16910743d865810551002011004518030103446540c5a0301804100c00d55038083c5030034190099680c1680f140c80381c909036101c440300d0030700b610000e0803d40032480801c000d00702e140d40605c50700c40c0650f007240d000c0140208090001c002c2642c84c10241128406644140c64146511009a4074055402d0f2484009003d520001000b07038083c13843c00005110b10061600303003e4110307404550854903824980b00080c5001d007242c011581005441200180c0b4480e1034100c1d02c3ca081c802d030340303110840c0c1e00e1b502044229042203072425118400342c18541c0c4800c00f50350180f000d072001898041d0742c107545a00401c4800000da0440b4242c440010f051024281d032080d0b8803806020740360320100305401c0c505103080202c48040e00d002d02c503040c070b18010082564200f00400007008204001d00a910440c2020390341c20040c14030243c0240e0a00001500b41c62004c81211440c0d0f80c0ad4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 194836672 1250 194835422 194835437
    0xf0b1f1e0e0c070c0906051002011e1a2e0f05030403120b0d030e09072303180706080603010b09010b030f0c0f0403140c011403010b0c010204120807110303040501 71
    0x41d00ca50180e01019021907007912080103540301003919030080c48003a00c0c448001284252400e8280b0204825141c440d00442e45040b1a421309200c1c0c0d88040c12040280c030030046129031030704c18001141b5400b440c2007030744103403a42c034203000c40302d80c0681d241d8100d0b044012160807008181015507445030044130702000602d04200187c002406281d02c0b003500c1814401c006003000803400400d85200d0002019400324000b015081c1d0707a45014952075503c0310592425800400d08005000301d03e800884510714000c4c008000281c29101c040c0340410351480709400c840101380d1b03c4001820211058482a00039424000305071900d04104080d00e04071180c102c042840c540d110502c8440c03c0310081c000002c4d2000401c54183c000da10100904091030040c0e2250031407801c0742c1d044915020300030000c981030010a050200c5008445010b0701d0447c7c1801c041c459852007580807150080c444c030b40014042c07003d150700c29001d1101d1100a03110552083c0701c101c104110000425583c0c0c01144100307400200030 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 194837922 1250 194836672 194836679
    0x70807050f040302130f0507030b03030a03020711091f0602160506030405100e0c0a0909030804020910050d0f0b1807170307050a0803160e03190f0b1f1e 67
    0x8900a20a803039101c607055081c0390302c2c2c1d070010710000038540300d444000e52500f08000c201c44941c40350a80000702d1707040401c2150744803c007280d124004e004c214824954040f8101083c408600e01c400345800d0300030030203c89840d001c500c0f010f00583e201d4407014141c40514001c04c00c50300008100c2d02440d0081d9184400e5464507041162643c0010700407100b9004900d2441076603011405500301418005000e40131004204043c01000c1d04151704c02d14215051040b0013000c6900668040d8110350161003031561596801e0401103141095444140c102500d4144d031020702c21540910300b0043e1290340140002d271900144a2400c15030210b0a10311900410720400c000900c0d0500c400c69a000da0042d03a040c5685a105c1c00e04081d51160180e5072a01c00104001c001906503100103a00e040500b04001250560710100351398012418107210800e254162000612081c1380070340d4580c9502148055242ca0301048855100e190201d03560b40711400200d000c01c400b820240e01d0348010070480d2045107020b04c2e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 194839172 1250 194837922 194837927
    0xc01021c0c0512040f0f08090f01030911090601200709050901050405070605090103140a020408120a050a140c0f0c09010503010603050316080f0a0507052103040b0c0c030703111203070807 82
    0x409402210030780034011a400021b9981248182080c1c0903014040d02c64600000784400540c140c46501c0c101498a4100c20019a10000d50529208145c0704100c0300c0c0d03500001a9400c2040da00026203801e1046c054414081002410b136098550030300c414802c80c1c4582c00400d090b01e8017602d00a000c0d0f0000c200c14400700c0c1c801d0003d40742c48401403402103244903040d85040134542003a642c01d40095000074041c043c0a10803c011010031801d1071040c0d00c0e0280c03035000103081d40102c02c400d004200c41d4179848103985000d40300307440652075203109079800300c031b480c41d031450790740820081080c020b41915000144a113010f103d10021030b074202d8081d503e00480d40e0800ca9211903100340844da2140c040c0074092410781d21708040c0005c6050780e22003c1c0d030380c480b500709a032510001050130708200307a07140c604540c80d810781d44c01d80c0c2d04280e02030590141503c0d4a00c0500150203101d10b0f41008d03200100700002491b0780214038070844201003081d204120390441d09c410091008030b4041c2d01042011010860061 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 194840422 1250 194839172 194839207
    0x1314060d02040f020d050612030403050706050c0715031a04110a03050c04030507030b091006050d0f030309050303072003030601020a1209080307060f0e0106180b04060306020c01021c0c05 82
    0xe20003400020415100d20f8240304070b80000320344100c401e640e0810010241424036149202c500301400460500f455540c80380d941d01070601440003088008100f40110700e40800020000e000e400110b01080200103500070020b044113141d0f00c815501c14204405a820913100d41100e441e52505404e20b0800c000d2015805007602a08142d00c41404200000204106100c4d00e0302552182d9001038803400c160000c08d03cac1c0a0944007a884081c984030040026640d200c401350020b941c00401800c219103182001d0b00107100c50b150140060000008010940d0b522900300000305a0524025100d02142c0c1400e0f0303680d0001301d514030b003d0781c801e02440e804a110209031300348460f014504841210b44500307080d03041d030f00b1082c41100c80035200c4000c400d044025001e140000014200200a0b80f4503202040451303080c0502005907280d0303102c0c04020591600e030030840c00366400031415507452821000d0607000303500201280031050308210400d00050401d0085c4804100c0c00d5845c0d90903c1c24042c0c030a503070403 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 194841672 1250 194840422 194840449
    0xd050a0c0c06081902090a0e060102030d11030610030203041239030e030c031c020f010207083a020a0309021c0212030708071e051b131406 61
    0x845203014000059142908101421a5544a00c42e07030400082d03003900c10905811850040d4018003980c6400c0e21414081c00c200d480e00c103180007054640074010303425403040030100e05403c3e0910030035980c3d008400005500400d000c4c4c540c0507141d5022a170446c200c2c041603e00500328003807252440c103464498403140071820310512101032240700000c01c042c540d10070311413048080c0d0212a444070030b15400042c1c4241c00b0700250003401d0048115000a6150321090402c42c2d00d103196641d41da07000e035108000341e0196064440c001c65890815040c42c200640081000e240e40da50601c07101d450f0150814203011514412216410400a8612011000c1e4110154030410155990402e0015980e0040020f81d81c0c40c00d100c20720744014090041c414400707020301c24050954410005c0074001a0b4840849540070f4000003140410901e4015209070900715010140242c80f42d4195003107050744404103030182c40800c8030703282ca51691151401e419140c9030720000c291842070000048042c01c1404401111 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 194842922 1250 194841672 194841677
    0x30305090904060e0a0302071d010e06010c03110706090312050a050703030e03070f060b04050a05011202060705010e03130603050615041e0e090d031d2a03031c0c110d050a 75
    0x85072460180c2500c3c0c1712440e0401d50059101c5401041130081c00866428018103d1b019100d00c0c0d03040440d014002e4002410700f60400c030010110310149031041004171340000c3c0b030100380e50311580d031148000c01001860200392891840030500d081d000d8003079401c41d0080901a110507017011402d44040c4c1c000d00c84035414500b240420481b800c00554100c004000007881313030030005400b000d140180401c4880060811303007541d240000500c00740f2400300c00d00240035812243c2c1551740c625840d049015007401c0150315064031021a003c14170b0003072071034000240c40a980d4100060380d0307400d0820840c6006000300c540d140c2d00400082c40f00b0120b005203117290b880150404040da6030360700c0502d030001504445144a03604502c02080401e90b042c054034541d03660551101c0070748101e02d44600d0300c40002c0c0145801c5862040031642803030140700184840754800409a0762a40490308034031220129081013900d2162400030350604513405450014081c00301e0746d0040468805032802500c880e840403000005 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 194844172 1250 194842922 194842931
    0xb04050708100603050c0d03200102040f03050c030d18064a030a0206031302030708010903080a0c1803080306030c120106050102060c040305030a2d0c0302100603030509090406 77
    0xc1c0e480c010400500804000d00d00003880360310303606104c0d0400100403160361059603521070f0080466480202c3c3c05148865400392054001111107090080c4102d500c580400516940008140440851424403807881030701643c2c00900c4c80310080703e1114007030191140108200505115082c803d41c181c562050031480000d144141c0e0618022454100324468070801081c03ca42e6040c092a880c41840c10041c10b400401c10442c203a80021a207010041000601c1c2841000c40f00955078200b00340c0000302680e0008000b8501c0030305001348150021106481e0581c1840d035a10149442041e02d61035010340d807080304864900315919241d8962010340b0099051050b00101440b40d6030344000c3c80503c1103100000550585008000390501600400d07410030300c86c0a02081000c520007004881c0c180ca00351404901e212009012500001d0304111081d5041400841d080700032030700f11044d501404d00a40841d0b9180d80d4210301d0906403219808010002035041c015000d55040000719590010b10a000119 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 194845422 1250 194844172 194844179
    0x708100305010e0c0a0f060903062304110301050c0307020c042d060f0f030c09050c12130c1e0e0903070501050c030a0b031b010c0c1e030204270b040507 67
    0x50a5800955148030181c00c9541d07113482c5490445481001005c045085503030561800350040c042502c40e20024160b5602c40011200b400011000340402d1410b83e040d24050741402c1c100071103c1c9400e8002d0303030300a41c80c000100d040c02c2284003e90b032107080c0c00d42c01400c44401080500015105056440c084941c074245a10884172240c40c01c107018010340c41d00080c0c00c82c0781031142102406182c1c8401e0305500039080520110300c1070071243c1d0a641c5582e6012035180c07078600c0e207079005210741400003241d0700c0c1d46401c0c001d0180d000091b038035800e40201e01c2c0700d001c44c2d1610945003078034200b520b00742d82c0413958200170400d40581d403420030360203c00c04081e2418404151562800d403041110303c216401030020070016480400d228007000440154010000300f259400b180c01c4080d09141c000381442064007002c0e08105032114000c001e40300301d41380d058a0324040e08840b80e1004003400b00324071803403e02c2c14440111b19000d804140101c220305c1c0b4066140070035180e40c5400c072000380080c2d9050003101d41c0031 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 194846672 1250 194845422 194845433
    0x1180b0103032010090b01090603080f070c05040f02040810060506160501061508010302100e06070b150a0e061305090a060903020f070e15030a0308070e06070209090a1707080307081003 81
    0xc800010003110b0210700c004846c940170081900580200d04910b15221041c004509030605231a000000206080e958a4081c01c0145403401181d024035840380c1404020540d051050b0051b000300c0d05040300b01c0300c1071100d4040c01c4080d50003d01400d50888002e00003000c0256030414102d85036070098000040c091344034217104074640015000000401d4a0400401c11030030420820507100c0a40d10b030680d032180181c8000f44051041e444040c010500b00c0000c80c818000c1c564070603807a140002d014034046070351240d0090b42410f00300d6a180c45002d414041001d2003c2d2402403902c11105003000d4100c101e000e550b13800050480d22000c0d0114411101070307030305600040040388081c00d5410000398079841c0940702030b0005441443c2840c000e8005410450000e900001c425420817410305120840c0c0c0c03a0310703000c05c449000741c500103503002181d0010b01c0f0504402080ca012010f0007034040f801406c0154006042c80d110f4008000e0240c0402c0001921152080d0012600b12034130110072011265640c0f20b9 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 194847922 1250 194846672 194846683
    0xb01031107060501051f02030a26040b01080c0d0f060e01090206070804031205271f170a060605040b0d020f03010810050a061a03060a0b0f0c01180b01030320 69
    0x1c0b0b9106541c1c00040c4118600300a5103050305541d403844400d980c02440009441e4060010150184454a00300b400035030307000481084191102c0c6c00907580d0340380604100700703581e6003032090180034014800202c005003451084101000d0308008921103842d03d41d42c5103002002c00000f5142039543e10710682c401a50b5000c01410810700414040c1e403150b040d41018841402119103c105100040100041c2000c40d410f410281610380030315807002010200201d107842c0859011001c5088401030000f076041d030810161300340b039080103005100b10b0782c45600d1203046809074051800824003d000400011051400603c1d052107008009400c00042c4c0000c0762140d08203170064075803074100c0071611340c50503894418680c1c804d4021009000441c50061762240060000007003200c050000800540592240103002c4020400c402d85155201910710b410f90147d004420310390703042d50a1400610004d103107040d000d40165004913340d0840e03403179907a0546105404c4242c015840700c044480c4410769006001 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 194849172 1250 194847922 194847937
    0xa0b0d0308040c1e030b0108060f01140102100c0c1b0815070509030d210b0a0504020d020c10050601020d080103110405040318060905010e120c1c050601030f140309130b010311 77
    0x1386030040a0540c0352007840303400e0580040c7d1142e400303030080028041442001c541100c031645400100400c50b00e00407810031007080c82c1c03c00240d0511500c1e03208150311481d0042c42c103000d1072803075901c0461107655804c10071291041d00d0791030303000554400101e203c4c0c9405a4104985e070500f50315000000000c01d0403c0113503888000454002010300c192000000302e0f100b055012030004202450404000480202850040901456020a00240b429201e80c1191038015031002207a5a0800c0b000c41000035020884049005000380d00015100a002e200da080c180c0b0341c4641944003040c03440c0e0920009010041083c1d0801041310710b00e010702200360160741c02400d030540c0c4801d0400e050a0002d4443d0344094800d0780561001e425998918030040394a81100030f003181c2141c2003200000041351340700448038014042e03028000000041005480d044041d80c0e12a240c0f49201124000c8001d445c3d025814605030444203040643e14211800d60102c1da000c2e605040000e8034020468000805400018 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 194850422 1250 194849172 194849219
    0x2030601230d0f0b0d2d12020c090903030112020a12030206090706020a020307090c0302090a0b0306040506040603050606010f02010f0f0203040606122003010902270a0b0d0308040c 79
    0x18100410b04914020301c015000d0800003400340031104070110782e01003050b000180c10010114000d10340403071451410390403006000b0b1070084500307a45c10120110204c1d00403090240c0b28201304003520307080c4019401c0c811890f100242d030450b841c282c1d0416144940c9070080b80d0100d80d04e0304c0461122002d250f146141802030b40100300d1850806002e601c0c02545420100565002c840312400580e8002407a50945242100100c2c5882c071000701503003e4062150b406600404c09107002c180364280340061842200111402d0009841d40300521040700c4440c04040d1840e044540000d2041d4018010300c04d00485a1000081075510321240c101200c8205202c42c154680020900c810f001043c09039134060b00740303000400d078004455950032810558107a43d5001c080c0c4015140146030360291f1055051a0b00a80007103000d01e2111007142055925a4118540c803503598081403070200390b48650b400d4244040d004480e1741c0500d4406441280d4024401c40d010800b446000ca094500030004960300420780b03 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 194851672 1250 194850422 194850427
    0x120506010801180e0a0b0910061a2208010608061f1d060d021002010603110603151203040e01060e0112060b0f0904060f14030708160909020609360115030203060123 72
    0x8d68030881a503940794020a107400c00501d140b070080b00224100d82d007400d120805040081048000c005500c4910303480440c1552800c88000741d480c1011403540c0c807610b10025421002d803a9600e081d4a5810103019110000d01011124089200e603a40250381005004044c80d540c10340950000f01c2d03030404e8070b080c0c0e00142d4680c40108100222180704070078880088400a05510f000b44018565922900d4254810003e0018200c0d21103800d208641c05040303420101c0701a9a140c0401400a0740900703409800601c1d00028185008142e10a03e801d4035040c00132145840c900c0c078014012900039040b1107500a40d01d07800000c40d141c0103030580c4000c18012945102e140c894004250400240350b010000c503410403090b005200d2a0003410320306603124003000040031030140c0003003240b41c0120840f01c2d4011003074009c550031842c4c00c074205041813143d00b03243c005101d403250200c4420078000c0c0700b0b11585000e00f507404810503000303030080e5a01c21010314040143c0703d041c8035086081203a0403081c22036400c00 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 194852922 1250 194851672 194851693
    0x1270f060e0301050f040201080705070f030801050f010507020f010e06040e0a060608070f0c080310180501081e03040506030405010207080f090a060306080327030d120506010801180e0a0b09 83
    0x440769600d28104200d008010a140294940c1c80ba0280104000e040141d82800518101d0007102580c4260382c02188c2c21159400e103243c050205e030303401c0c0102d0307204100d5102e1807507407503100380115542c0c0c66014100301203c55640d8015075005c20202643e55000c6005c3c000481c802414203202842010a488085a518901100544503c40141c244400c20842c003025209280e0010301c01240b8503440002039540e5070350300741d003026a5034094000c5841903202051009006800b500441e050780c82030030503070f240d40e81411541e042c0000207060903d82c07908203100800983c540305000e103502078000c1002500d004034983d15071310300e0b600442e1070b40004000070034070703800a080003038030311000d080c02e0300702001464102010241d581c05151104510509604542403196550f05003800c032204000d012030340784080006000c0d02c416400303640c407a041494900015050747c41455401c0c1242e05861004180d400342d428001c01a0103212054007a61082d00c0e5044002140c0c0a680d501c00e190600203030005000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 194854172 1250 194852922 194852927
    0xb0301020703020a17130b211806090313061b02120303070806030106031106030a0e19030210021801050f040806011710050108060a0f090f0606030b0a020406050901270f06 75
    0x20303505040c2c019242030110030a22840000c0d002d0a407000d60340d440303881e00323080503402d144450300340250507002d1030320800d000c4d00c2840d10240c07109600208040ea160350780c490f0300c1c00380d49010307081d00101420b031600401c010050140c03080507000032140c0c2640003900d03516000f140d40040e485a070b904081c0d2002080244459100e101283c01800c1140203101701891501c0c2c040120702d4580b03080c2c1c491003000003c1084003006501046484035400c09660981c100c69040c2070600f0042c0c002540540a400b48e01d07a0340045920840b004414000d4108604649502c01102c0d03c2d04040440010024108008140c000c01001207600a04d071001d10444074840c202203c0307040c030030f208a124100905003c01486202c40204841e5030180c281d05001407000c0442100c0307409003801c100007401c008e00603030a40c07090160a401c002e045d64064410b8007100d8913050700c018121311881c407d00e000280188504041c540c031410f401c0301401100c10390b50000c22081e60001d41c00c01c43d59840049900241d90042000c6074 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 194855422 1250 194854172 194854193
    0x20705010f0504050f040c0c050111031e040f08031b040b04090f0c08040b1012060e0f0718020319022205012309180901060e1303050a120b0301020703020a 68
    0x400c03a02d4010304040c903040105c0c4005007132503080c9100d162a15524008103106081d6413442a402100034410320040121000aa03442a1034800c50044004088880035884502c05405181e0200300703118800d80c00d4440c3c5540703402c0501442d602c02c14034130100c0462454103000d003000e4044403019a070b60714030b40000c1d00100c5542032204600c0605044000e0906a0028130450744141c02c4600100d8669a0396401140c2c5505a04044c0007101118a60001d104242d070003004030500d5602200c190a41c0800d40c6541d030800c61081200f940034900c140d500c00d2182e038016540003034003800d103008a95040c42066042c1d030064603d0301e541c000e0740c0040c08004402c032082e4900800c000e091050005d078040c282800c61844040c0340c00900240000c00320490b07100d0b0715418003011003016881c1c01d01c0c10610030283c081c152500c10010641e4a07040442c039451486c0c40108065940b40c3ca405260010743c03a000eaa00daa0344820303901c0d8042d582c40003d13400d034a0a00045c56454401c0d40508118600c0b0f1802c0d42070706 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 194856672 1250 194855422 194855447
    0x80324010914010c050f030f070c0f05130b0310051303020d090f0303050f0d090c03050f010b2107030203030a12050c0a090314010603080d050a0c020d05090d0201090504090302070501 80
    0x10a080e4001c101c1c1608040036002c0e55402032030030031014409410038034908001e80c20310034080c0c030000800301440d0f0040000350034840d1041e192042107942d00d14442d580341241d4058554085440451031a40920b00c0c6d1000f003c03120080c040e11a880c80d00300744d1600703d07001242c0d926561a905100d40040640c103224a0102c40301c1d40c00d060369050300f0012890510a40d5000090038000c0000710b0b0126407419000b034494801c40041c1c280316010b2070f80740681d5442158803088406229074400801c401406000318104179002030149119220000b4402c240c6541d000440c1403140155400400907131014402071420700c1d082d443e15142c81e00d1000194040303510041c010501d141050020089450b1700c1803c0004807904006500c2e51000040c918500500b0541c3c00180120000501444644500e410032481105c0c0704004000600d0443c00507a1103c50828420000640c00c00c00044186807403292024154010704d0b01c00700326900c98010400b280c090300310a50250303002c0101040a50713800030030030414 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 194857922 1250 194856672 194856677
    0x150908160e1305010603050f030910030c0219060b04050a0c0f0801030809010c03141603170f06061605061009060807300503070b0f01050a120f030c08032401 69
    0x409262071481000540090040394009420101440c1800004d40140c006181c224054603179103030f40261001d507a680844081c0d0f01412440c200301d920300e40203201d402210805a0050000c401d00709008030b40400b08400c00f245c1055462041110343c0d152131048500c9110b40441c002036484a0402c00342400c80d6900100c3c0030401c84100600002d4020b50a41c0c55503807081c00c0500ba4071910785802e41d0194140c1684640d0448007080e030000c0908007a448013041e501036120581144441c02000314184400c803460750464401c800030031440d0410178000e140400c480a480d001005481ea602420b002042e070345036080300c0e1515010f01c0500c18070701c1180024580007000340b00c1180b52403a202100da102103201824001280c12007407190714803498110086500c0341c1500d56030050b6180c6400c40707000c08da0f2850984a0810004035540c1028042c4009440040c080320000109070354078030350340c900f807045c00310b003084410100c0e440000ca110018500070112030140c85041030408030120450009620300504 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 194859172 1250 194857922 194857963
    0x30c021c050309060c190b0103061401080a0f170d0e06060d02100c24021b0718020c070e0c04030b0a05040c03021905131a04110919150908 61
    0x1c40000849081c110203648942d15200e03421384150a01305002480640c1ca07440c038501c0c10030442e600042d01e041c0c9100d82c004000c070001d13800c0d0850700c0d00740c24043d41c140d03544003180c4600416035602507003030344d207204000d5101d42c0c590740c5a08456542140ca4030b11013054445d840c00700c10900034001a0b50040701600d21042c00d160580004454482c01c407031003018020012000d0051000d000c640256182020901007007444180510500039400640030031144603079510044c0e6528404038450044a0051004000c40110310000d28025404020a540c0c0c3d8401c0040005100300b802c451700303100302200030b8003645492441c18880c0c2500401000c0c084854a000c0c10000003800081c450b134160303501035075050381a0044082144540c0c00540169030f214140724102c0011400c176030488a01e8100301c00346080c07401e01000a10068610028803440c1c580001e000c01c0c47d00303051106140441d00000000b44120542d14072203003090742951071030200080c003920414002180c0401102e084606001040b50 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 194860422 1250 194859172 194859229
    0x603090147060703050d020403020a0b071406010308030c0a02030c0111120906370f0b01030e06090d0e0118030302070608060603060d060507020f0601081e0609060a02030601090801020304030c02 85
    0x51a0f48507555000303040c49004100303100700342050750564000c3c560103004002016240c484040c400e8011050482d048950360168648800c400700303000d8100c0e40d00809030f6040d91a540d44607251500081e00c0f01c0304512062144c444010424040c0e0f01d803030010801540e42c1d94514824195130804014480000e50723010009201149540408c14441340391018211280c3c58040c1204400e6030300c5a0602c0c4050780d0130100c012010b11840da20414041000740c80400c030459001c0c81c0700f6102c45c1d040b125400315800008041c2540341c005d600450101005140c100341c0d0514101c0c540d410b000c280e800950040c1c0c030011062000c03035040b6803016000b12086803094250319010740010284050403000403d11519003001c01c541500800c00c0140b00c04000c0251070075580c45149407076607500160103e0a84486210043c0064900416079074024070300c20001c2d002c2039584018031700c040d600c054a0681040954200052240820303c00745024034400d54031151400303032500400c02242c558604010000120b085140c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 194861672 1250 194860422 194860429
    0x170f0d0504140105011a041a041d09060a060e06120708030721031a0d23010b0916050403032601030302031207051309050a06080307030801170a0c050603090147 70
    0x40703040314030042c2399100b110340c040c1e026034040c0560f50003c0b880300481d80983c5003111038105005d118a5012023118160355a821004003070326824402c0d42c2080e440c80c000304a00e0300b401c0c4281c0075191150422940400d56a5658520355485820180c1d421442684082d1480342c91a5208000c060036280500c10000907285845640126a10b80340c820511010100e041066598040344400f5101d442e02252506154a0501030b002039450140714140d0032000030300065207102c0f078500f02c08032603035060305140c21581c09403280c1c0100e210001c0400000285c00703030403405140240c0d010b14401e60141d9219014501201e04403c00a0714080070b002c4144400e50388902c40d84c208504640103171002240036210480c42d10001e1040740c01840a6000000c1c048081c07540011415048801006002440c0c800140780591100340e004802000c0441c02c102c10403192a06030041c5030001103003400003407a402d14003c00f000001002e101340000480780c0f00b4207130401100c0c50800324181d81140250b0461492903000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 194862922 1250 194861672 194861677
    0x60c0601030f1a191a0a06051c200a02030409021b16060210110c0a0605060a1a16021306030b0601020709110d0513060e0102120a09170f0d0504140105011a 68
    0xb22682c003562004200e0110304011002030000f07002504030f201b020b403503080041c401d40c0404200301c074502c0424000c4009800c14460860013040c06500030074418240310b500201c0e940102035407002c5100503c008a00d1445504c014105908204800508641e5140e10340c0d040002d02c05800c14022000c00c030400c02c164000c03494001150030b12600007103d040c4c208189896005601079150544100001501044110383c0041c0c06400221210003400c6c1e5031310586290340100328003490b0b410b0401e005452640007001000540b081c8000c12502c1c96110301c414203412a180f9034021f40d29445010706000c80765805024040c0600f4860009008200c0302c5940e0028510540508142c11540d03080000d0900e0030318080003c44951280d8184020103492501074041e4000450b2045016240c0b00415440b2a03248103201e26113a001141c0285120301100800c0180c010404414000004100003003608100c1d2241c6c41c0b01c0c0384500140408a80704240035401c40d20141c10003981e031460b00e560f00c075480615009 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 194864172 1250 194862922 194862961
    0x130912050a1112030103060b120d0518040504050717030a0503130807020909070e060a0302010c0b040204020c031314030105010515030403121e0c0302030c0711060c0601030f1a 77
    0x4000740d89005081080303941c001054541030941c001c441440c000c40601400840c12240105018441d40c00c51408000c001e40340d1003e141003d60000240917402d5001d01c0240280c83d07080030914401441da0804501a542c0407036044480303070402c180030f21900f80d150700d950111202c82e0004500703007800100007804e01d100107004040d00b05121b001031405c210f01030b070442d0b12080c1c0c080d100c080241014010b10b903540000d402a5a0002e0030580090128100402040101da80503075034550044081d13140c0d00303c12240038200307076040b0340c0070001800c017080104000d06c40a65a4080ea821782440c000402c03142552255120344a40d040c0001040300396601c001d520304001030117030210b550b40c446180940d80481e00079541c071265820811b072030003002265024004101e65014082c8078404d0040c00440c02c86c8800c95401099076000e2001e40302055032541d0042c203030000981206d140640301c041452402009900480d400f420203001034041020710050080030b00800b0780d0140c254103201c0250392001c0403110303 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 194865422 1250 194864172 194864177
    0x5010c110a030f0b0907081c081b1908010e0408040e07020a0f0b01050910060807031107080c060613090b070e130c0f0201231302190605030402130912 66
    0x48800030954580c0c00c02030003194401283d8a8043d040d180002d4007101c2154058160301170766070300040b1100c01281032a00d07112030903000068400641015143c00c40042d11603240c484403046101c001e195100020070b074a450301c140013980c0795107070b0200034210b0f03105070002d00e45401d5642c14407001408800a82e0f040e030f01030030785001159664100480c501440c3d880040d102e001d241d0f20003018440c0803200e090503901c054941502d241d5a15500760706080c413074031070900041d44800000d00400d00c0307944448016040d000105250040c0c5454145060304102c80124a039049813041c003a580c540041d001080f070721924400c1c48890a90b03150f000040000070666001e01400550150b9207039140003004000e0280100c0400024082210082121025140354805503181510a040300101c0e1800c6107404202440310b400550740d0040c1606805a0a01c000c0f6004224410040024a00308003c1c070060704150f030b1ba660b12441d2900400040883ca0b0750043d2240d89851054008a510a00001c66440e85030 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 194866672 1250 194865422 194865443
    0xb040e0a030f0c2f0103020a1d06070203031b010605120304120201030f02031003030305060f0a0b09060f030711010f1406010804020f0307030803060a0501030e1507200d02010e060105010c 82
    0x14041650b00f94038075580200800c031204c40c2440d0ba803203212040c030110005000804034061003000103400701d2088110742c5020412090144084003020303c0008000c0078007801a5050140d644d010a02d5a040003000000d280001c035411500078409214003401440112800400c0101f416401500c921403401030940e29500035070f000056900036008503512008054046580746801681c45040d0080360000b100000d0502c1d011407414544004100c8000d800108144c481e075280c001d8580e980d0380004c401c035820000034405d8480750300310380c4043c0d4400d0038241c94490102c02d0300107a03603084030010140000c0300c900c0c02c8482e02c07600001c3d50f402c0e0b6000c0c80a08107641706484500000b210005450010b0b945481992004001c020310200690300a040a543c1301000c1c588441c01501502c2d4000d266007801e9100d600c00d15203c2c6900e11079550030160a0030114a010080404100c2c82c20002d4021409070740070341c915142a640c244100c231520702a040240005505120008003107841c036260150480c0104e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 194867922 1250 194866672 194866697
    0x4030c06020f09060a030902030c040e0706210501080d02160e0c0304030e0306010f090b0906092d160216080601050409020a090203040b061207080a080c01090c090204090b040e0a03 79
    0x70b41c1190890f420003400942c4074500820010003a143e450407ca00030b02038452420075604190250190b003410500240c141541004800c444c4030301103c45420b0a4840c600c02031000c03001c64411980600000d101410300c1e50070b41344001c1c0c81d000e103101c2d0b50403109500e04000c0012031450211030b41c00921980c1820360302d80b540c2c2030449009803101803441c0d040c01040c0c0002581c10668044200310381d4084030910181c0110710401070010011542280c000400c94000f41c0c0d00c40038045080203514400c0841c40000c0307440d100480300054119245483c500340d00c2c0b032042626804000340c2c00301c241402c141c01d00b4542841d04c05c81e00e416061098a00450b143d03001e075811541c9405003600500b41d6240b08646030b20305410008204e02c403c0e20000d00885e10040c0c4030500c1d20010508000752a1190000c2c52040c040d90f03234000030740e0311103d2000d54555a030311001002480c107080343c1c0028500c0c05c10250300c680c1007801e440102d40308850b000d44642d2602ca281007500030302042d0520400d41504010710910b91 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 194869172 1250 194867922 194867947
    0x50403091a040e060613181104030209130206120109020d18050a03080a0908130311031504080d06170a2306060d081207030c02070e0f1609080a05010506040506030604030c0602 77
    0xf10180180780180741000402d47c00d18124200c03402201c4800d040c005e0386051311804950344540c0c00080e410400801c0011054601c540e000040c6a1005d018030340742c80c52030049044050030a80103621651740004444031812218056110b259860040c40101001c09a840507625103c00c0c40c018103000e104000180741c1c40031588424a520307000341950750380300d13940140d0f104007030f61900003160342c07080303100c008004e0b802d000910181c001050040c006154481d41c440c8107844e04580c407040501d540360200400d543c0041c20111040815500c0200f201d21541c0c900911981d1800000c8590300f40842000496550001106030b0010415107904000d0040c44c00d0500161040484100c0c0e42000201801000c581c107610881100d012642a5800141c075440611104003007911200c11561201c1c001c1140303103402142002c1c0f541980e08008910599556581d403c0900c00d580580c0c0c60b954840c00c10000303081500402e13038404030440140c090b1b031030250303400b5002d01142200030700740d160701142030340e071000c1c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 194870422 1250 194869172 194869177
    0x603050105060a0806010509060a0908071a04060302090f0a06080717070c0312090b19050702010510090b040b04180204110a0f08070e03101d0105070509010c02060d060801050403091a040e0606 84
    0x2304098030300e50782c41c0c400090203001148507200c0c480e401d00c0384610004094584001000200c103443d01c40b503140030700d02103049004c1d400409070158410f6403401e13081030395610140300000a040e1078890200b0ba151400e00035010300310111013010b0418844c400c01c2945030b07124140c03440c91a810300700350038403030741011640004140c0d0300001020368661354288413820094002c400c102e0500f41805000716560070000700e00b81d03401900c610a00900181c0240000c45064001031590b00015000150058a281c0006d00345c5048240111422030706020040540c1000d00503901130100c071821241c030b42074000500603c0028404250b104125010012a5540d841891140f069900080885031409091401100100000380808401007100743c0704411228043c020180b080f001c5840b80342c01e24004000554042c04c40044c1240d1040e400c000207500c0444034400c5c80040c1c00c407080000381c00d103031510700542400b0090f00004120091444203807109036440d0101c40586044411101c0181c4076800829904d0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 194871672 1250 194870422 194870437
    0x603050d050a1b050f0f070621091208010510020601050303030a0e1009050606040b010c02010804230303010b0405010f0507080d020906040306240f03023307060609060603050105060a08060105 84
    0x200c8816951030240100060740a001c110f40c44c4c29200c07003900201c412030340d03500315201e01c4002c80c0c0120000b61a2a0308845560001d070f08270740e00031400714026540c12005e900b03200029004211441c005000b00d09285140300800e000e40c4c001088554109000603650340001000c042e12603071600c005204080c400e01007500c0000f00340c0807e01203030180e4540140c548200b10350071b40c0030310701e403001558080d031043c3d5855007150b8040e1103003400d0b921941c0b20850071000c0707102070001c0b01040a2808803e00c5041005500800204003056291400e141c0010007030a0444500c0c1c0c01c1010620140010800803800c90b021a803c2c580016a03071800700340802c0b064051756102500c040c0c6090b14051200340c00040c8190400c80081b05419404c3c2c131030865001c0a0040c0c00041d4000c0c0b02060b445904424901044540b88071140c8005441d0310302da01100c2180d4480d00084941640300c040c10080840d40d80100c0d0040c19407400c040c4031660419010941c84e005a070180400c21620f88045003099000c1d40846002c1c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 194872922 1250 194871672 194871707
    0x6090e071103130915030f061d0a080d050c03010f0909050703020402030708060306060102010c0f1206030f080c0c030109030f0509042c070e07020703140705030706080106120603050d050a 82
    0x1501406660f0300504030702480340102c07090400300b0fa1080410064041401e49a1020307441c650b2502545611005280b07521901c4e4030790000d1040c0c03c5075000d0400910742c0d100e1007001d44a40e103803e2403000780c050741d0010300124031540c0140018400c8900c00c10700d01e0140d5400c03c0b400590398010781440761500e4110307840070b0741051002041c00a9964028100b91190b41c09400f159980c2d240c03100124202c1c0d80030302c2120001451141e0f5201108d1007820b101a4400f4070b2480420855102e80300d9201c0e12083e00806c4400600010782100307030301e0007805040ca5000044000300964660754801801f003841d55840c801c10002c000070740c20303280d580c0d5620440600110840c82a40000b06102965481b003140240030301030300c184c510019681c20314440e95482404283d002d0b000003859a03807001e45001c00c81116070014011841c0c0030509860801480c070050140d580d5881030341d4507142010300803405a540101c40b441c00d000d000c0c00824000220308404940e245000796880a0b80c0708110380c10000449520700 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 194874172 1250 194872922 194872927
    0x7080c13020f0a09090e150105010309230c0306010f0602060c071a010906060207050301110f0307020f060f04030809210901020f0a080301050a0f0e0c090f04051e090706090e071103 79
    0x31041d134800d0300b007030a0f10310268040000c0c12070b00600741e944600d070444656403840d212005000b994421380180c16414898081d40031032404210030702c0c01000c01110304202c1c41e0302002c49814145001c00103980100384115000401600b000c0c402502c450004001e402d03401c100042d58801c0024030003a04084030552a2440d0389541c541020001070319092103540e00611172418003060a150610414070210a250715880c6000103000060803603801c020301c0801540107550206429507801d100007841140042d0900a49250a250260002c5000381000c3e12030341c044407481004151500030100e0130022015860b80310208400102d28012117a541c2540c2030103000484010801101e000e18180c42c811a04072100300d172030f01c444054002c0c06210784594010494081a01120300e000280660f10300500703800000c141d424007140a031602a9000141000010284bc40106a200f8030681050300d00d40034010042c900b520050540150f40248200054040b01080005010320303400312100c1441801d80740c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 194875422 1250 194874172 194874187
    0x309060f0c16090e0c0a050d06060503031617122a0f0301090c02030c070905040f02180a060b0307020d14122401090f03080a23041707080c13020f 64
    0x46481ea000d1140403c0f190406140c003503401300205001d605000050401002d00c1c2c5001c080018032070301d4110984119a64200105443e00c040c0024601070b1000d442100340c805a92030065072054100b020408091002d10215010b0003000342c030580c010a007081005580340c543c4920000100c0803a0747d001d10200c000492024501074403000e18100c0d0410a002c01210380342e48420b1f81c0741e101d1241441099002400d060040400b543d00040d0031078000d8034022101c0b41e00d0b41c0440d0200c9540701c0300c5125008900c0c01c01182015901443c409019907040d624103501300003130080d5880c164802d000c0280540c000000d042410300405031400044610802452802c0114515407108400e0341020070085908241040c294061054131044400b070442d1990300a241d5169800741e43c12600d014020030200e014580001c0b40070b419002e00034120302440ca66214980500160ba060200074141d00725000b42d0740400c800300c1d000c0f0360300001d042d0554407140c6c13140190000800070703c141080d100b4030044c0400d00d103 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 194876672 1250 194875422 194875453
    0xf1701091a0a06020a020f030115030212011b050d0507030908090d0f1a1602030301030c0e0c090d0b220f060203090a050d0e010e180a020a020307060204090f060b0c0309060f0c 77
    0xb031700d80900035079a150b010b08882d0300381400d07140c0b6400071498400d80c0800030001810204a10311070400c00100008492a9000e04507810b444d01d00e0242c1c0000b44089001040413120384100c80d0464014203042090004966400405010b40c0364200e10030050840400203100303601084102e50742c1e21405a072901840300222060300c20302a15880c0c01200b080d0030250301d641c00042141e059981104565010760f00d03082c0f1000c00308e100140f50a002c0d0100b442003000b1601d40020490915200f10454906450420020035484444103280f1031031070030540080010640e00b002d1403500b9500824090b9a076610041c400b03103440c1c2080c0c0014490b00c00d0000100155030300c001c005000f24800d980f1080746c044910200710300003201154103106110084041020118a94004d1a05071900e00540b800d048054445030b08a801550140ca00140c4609080b02d020f1014821400030300b856845107400c100400c41003603a01c1c021034402c14042e07040024660007199410007582e056030304100440e051070500e6900c1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 194877922 1250 194876672 194876683
    0x11808070b040f0b1204020d0f02060c0a0b0604060b0d05060117010902090108072f1e0c0901060f09061815030209030c0f10140c03040807060f1701091a0a0602 70
    0xb100000308003d140443e104408404840342c41c04451042407040e169502001213a6110b800200c4a43d4a10000e0a005881d4400035240aa1414002e45204110703801c05410704400101294440da103040d02c18008010580161107003084035010000e0142d40d00b50060340c1c8201d02002c0400c61002c05000001c00c0412a002030400c1c0301c0070b80e9a0f001036101d440c3d040e110641007828407142e4ad5290001c1015906905500e105444042400c49441c111024036010050140426403c400c0c0c110006054482c14803100050041040303140040e080e20040d03d005110045502905080114040c00361030528030801c0c01e036019000d1565011000c0203091400f800a50111030f0315800b0b8001c0b0005000e0728a07155030511030703004024107007030462600c1c4c110480311483c0f112662518514103220b40648100100054000b44c4011001411128184034004c2c121407071118210080141284012483d100c603a80c801381100d05945e004134141000ca45c1c24400710b000030904580003040c104000501c25800900b = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 194879172 1250 194877922 194877929
    0x51e03091b040b0a050906010c120e09010e040503030c030a110a121d1002070204020f0a090611060c2a0a030207050a09090803060f0a091a010807110c011808070b04 72
    0x1e0051010340140000d41d000921801d50088400c40c0030005414001c0d08540d008005141a4405e6451540c582400091b20440e07040014007902907070384541880354425014041111008d50246066034a40d6505c0c40020280c181e18200400442e0001802c2d404c504c186104240302c894450074001d2008084143c031544041da5035007800440715005800300000c0070600c01840c042c08003214008500d0020b90320003641260015420809501040c3d10000504090034150740c503154450303e040c400401412007113100c1070042d0810014041c02440c0d01d0200e8207885c104030b918034030326042c0703002c83c24980b2014401e0b401c00d07004210b10345040642c04100703e0103891046980410094946210004507410305500030451442040132520a00d807100305083c07030100c0280810302081d240c0590030151421058079032550b10103400c0c181895038110b9a1030382d010032035243c10000c2c091014407050342c85152100c0c0d541400415821401d1030450a40d80ca4090803070344007103403078050395001c81c01000e0b4060b12 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 194880422 1250 194879172 194879203
    0xc0c150201050717060f040507170103050105010e09030f03070825031b02070627050310050a0b04050f040308100b120a1104050303030c09180106030903020f0705060a051e0309 77
    0x40c0d078440184d0900c00f1078090200588081200c40c890404d100007007101502d0a02800120050f0004810100c4000d0f4040c5205200100b26540f43c01c03002420703a200a042c1c080c0b80d82091110750140702c3c145050300c0c0d0154281c507010255071101c21850300426020b040c40c002c00100300b4244e40416070980c1001e000903500b501842e034000c0f04900101e072203401c50301488000405190040803d54101c0c00c0118907904a14800307400195120002442c103102000c590300e80c03507200d0003004a01b28051044003403d20090b2000d00007803410400014031040014801814413024030041103400c5042003058014268402c515540c03010030040503040003a044404058860030b090341251a40c014009a0b070480c1e00260081d411916100c580c05200d81086c007000d50013074154008a02c03049502c500450003080303d900c3c005614081030400a040c482070050819165005400811090301c4010072a90381611074582641c4802d60582c104032a014100781d40c8098030008800d001f000c00c2c011854480441188 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 194881672 1250 194880422 194880437
    0x1801080601020c012001020912060a052202100309140c150f030c07080d150518060a060e0d0b04051c030b01080106050d090f03081602030705030702010c0c1502010507 73
    0x60004a948140b20b42c0c003e800990300001e103d02c003a800c03031521006030303c3c1d030780001d410001d058000c10780c90440500c4000d029840401400441e00c1244503194004802c108038a809208282504241d400c42d0b60000703018a0040896002e40e521941c400740b41c0d99804200803007550340c1040306580d140450f0300c8007403060400c07260890b0015138106c100e542d02e281c160105821a603641031000300e030f0f800980050710301082c200000004a002441032070f03040d01031148002c0c1c145040805101c0408a4a8213011009000e002401055031350f403091201201c005292441c03c04544401054810801c8940200b11514060900040100205000380d4210383c080507030001207002a0120309540c1c14149041c0441c11090061104c1807007900200032013041d590012440c003a1566880c0c0c444091410700350006000c2d01d082c0301c00c8001c00f08000c00400d01a10045003000c06030788400f0b4591142075002030500001801507020030030f81c410030348010f1884d200c4010151070000c002034007802c0102c0d41107000540c03a = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 194882922 1250 194881672 194881681
    0x1002030d060b0421020a030215040f060503010906090207020306010509070918020408010c020a030c290f091606021f110406050702040c141204060e010c0c0c0b0a05030a0209060d02180108 82
    0xa650804e07110580080c22404400d01d96000d0020000c1d0038000302190a408000100b222103035000e0480081001e955a1542c96140058400407160160024070303240e401046001c0269800180060644070211002e0300c0c66140c510051314140c0700c0d070b4820b0b11590000341c4248800e0b10554003500845280c08004c2c0020450340300101c4c2c8a14000b42d004000c10750f43c054000104110f403c0903407040c0b00039a0b140350410404020070500080c12962000d181e100c040030040c2d500002d10003400381640c0c0c4040076002d5406d103038020351900000c0d4056000c0244c001000700d0f03400d040350003668520344008071403030f503071a1907560080503607025000aa006604020034803010303a02c55214483c107410303220405030808030f007000c0181c240e220251003591259160007814055607802e108040802c01c2c44d86541d15802c5607441c1a04080c0402d034009a01c100781071095a01841c4c0080440364404a051401a0340e204004009111801003034030225186d0300c0883e03200c04200c08240014442502600d031040c0980d603 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 194884172 1250 194882922 194882969
    0x501050304050a11011206080c0325050405090312040b07081e040b090a02030f0d0201050903180d080c100f1407050d0b1c06060f060309020607021002030d060b04 71
    0x1050790002e0050784040314882c00319010760160000c14038145006080c0000d01250340c401d40d405a0001074494021401400c3e85140810002e40303c40c1101c0381940400c038040d07003111071460681c821a0702a40e20342c0300195030210140103d4000c00201004040a42080c0c00c241410710000c07500c2002203009400400c00c0e21910260015809100e030100e141c059545a641181862015110500314840c202c10540107a60600202d01c59240f050b00a2039110242d5100a003500c0c0c01030a05860364104200270032500c218290901c04074142aaaa203c0c2d440f078500d4042c0e414130866039100c04500800b2141e10001ca0160014485101100c0040c014041e03c1085003040b49010354071807022480030400c058280c1103a42005060150082c650800e100301da412001c1000c510b032601b1240c4641d070788418403100500c500382034082c1243d86400c000301e0850b6030206200d07124074000a0f2191507400140b1107014400c108840106205d03041c14840c290381c0300a2164290454018004c031f081e14080b030380602c6038 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 194885422 1250 194884172 194884177
    0x6010e070f02070506250b010306020910050723030705071e06020c0d141e01022109030915220602060a020906030c030601030605031b0102060601080423011e09060501050105 76
    0x800060407035180c5000c0f40704141c08480b5a1b682854500e003082142c202165071005000c0c02103004000141c2d880740000200100c402096100e4404d1007020310007400070450f450007004100c1c050b0001c1d8462001c0701803806246000740746008106d4030940001064070380700e01c0e06c90451103442c825250841383c0c035510141d880386110580e05e90001881c82201c0040b0702144403902e10f862001c41034401c002c244c1c0300c803c4a01e0800320040c804681d000105081c1c1d4102800da038405500802003106014100040c4250b02c0348162154144a00c40c00b100c00110000e4900880b0340c03a02e81e00071900500d855800b180750300300c140c03489488054040d84002481e041402d000b104c0040c030004265501d0742c2d0b1180104c0c2c195070400b030001410540c0d100c50202e819101040004140072003170040c44148820900020b1038141c004083d2030402824209110011b0030128143c048002c452441010000482241d54010700700900e48500485444455840c0300380c456201c8040c4c01d00500d41440383d6030b290001541c051 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 194886672 1250 194885422 194885429
    0x1e0609120f08060a0311010e06040b0f0403020a080609030d02070c090507080402040f0b010c02040e070b03040b0a051e0f06040905060c071703060a030f0c090501031103010b19150c0506010e070f0207 87
    0x748002480c1d000d05601c81c208c0304041240080c401d9080a44541401d41c680d000480810880340e4002000d00952408210034402841840010202854001825a02e0b4041c451802d0301c05600440e200b000c0000c84200d4a0150035600d07000c0202d442c11a200500841058505074000d6242500303c50803080540240b0301024010b071140c10592500c0c2d030922004002508078030707045001d2a18080b80b820100401140114000d002000941c1400f44506089400203002a900c05603c000c80700c18000411a80e564002664090032404d03980d140045800391008810040ca58094001000b280b4078491000c1c065050107102d049001d002c29042e50740c0680f101b9105e550f4841d802c0c04040000a4001a40c550341510620301c90310002da0300c05080c000d070b80084e003049400701003040d0380c0c3c1400d0a00340700d02ca10400703080381c1400c0b03c1c03440c01e410102042a00e00803c541c1e081c0182c42c50340702a0140e000f44503020b40c000121603a560356109001c15281c4c3c20b482c1000040c0c034502d070004825100080d0380068 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 194887922 1250 194886672 194886683
    0x11040b0307051002031c1b030209011209140109050f010608070e0402060a170903070201030f18060f0b030f070503061608010b0a090306090c211e0609120f08060a03 72
    0x20141003400304103c4604024480c01180310800045540e481c504141040c011a60080466a41c1d0401a4000f81c0720032041d81c181010301c1844031801c5a03a1014100380705444d45680040d0190160030482100700d8088641e561640c240004001004800602050f81000b10002000b1003a200c21b5040c1d100c100e544904c2c203a02860301e0200f009842d00c807004021b40800790030012080120313002a00403c00e8119050102c5820100d00d0000359600345c020f1142c100511141000540c03009040014000380d00070f40030f011329554080002c1102003941c0400c49002c0f00400319500d02c039450040f1540c42210740a802e00038060712000c10b045001100084a109200e80c070f03110b4050f802d04410003004d810032042d100030818031500000100798180300d009040c0c1d00600b440c200c0c150924010f11500c040c504210305048614855a130086500c4001041d214000c0010440d0002210306010000d40107220000d440110040c60400c052900310726250b0040d0b03000d07143c0400a60741c0408109520144e840043d10 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 194889172 1250 194887922 194887933
    0x305030a110c060903040303020d0f0c030c0302030f070b0114030102070201020604080c01110d020307090b0c07030b13080c030a030e06131101090f140301050109020c19141911040b03 80
    0x804190079004240000000c0d0281410200010455450f080c1d0588902c149504000b4003401451790501ca90a035543e0b4908200784a0f00c06c050000300240410039001d800c020220f041c603020503200b0310445030485001e000d4240c0311100d5003401c0900440070720811102040c18200703c03030941018000e4072141034050300903145d01d5560b0380b1011201e60010b4110300b15956104030203280c001e03200e0050f000840300c07110010b0b100c0c985200041c00c900c0694100510407a4244500513509000294440c2a80e0f4080320020040e11081103210811039000c100810040c0042022042c1c8100040540710302c040996082c0403908068102035118a030a982d20103110b4501818400030641d0401c2164a0b20360616111890315070301e107100041d54145030060f480340c1c1c0b0100c00003280e6180902626000d4180e400046240100a525031940d8107600001c0f4106d002c3c0c901005414888202841c100488014058403550101400315180d211035011049171804c100c80000c68860402e84902c422a18000e0004c00 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 194890422 1250 194889172 194889181
    0x30c040e03030c0f040b0412110a050a05280b121b0f09060c0f010e120c1015030501090c0e0a02070b0c1c140402030c0904031704080c01050f1008030403030503 70
    0x42c3c0d654000d42c0710030003410040000281e0600031500400052070710401c220b41100203840d0101a0900200089c0d04c181c1103140c007480669121140c020440b18121125000d00840025407000502c3d240c2084504c18209a000112107240d80000c0c030000a030000c3d480c0103569074890801c41e0303a01c0c8081e04c01a0704001d00000f402629000d0040010706001401107003000d036400142403070100c2c54040f03000309945440303614940d03c0040000d5141c40b013038485640d09000111615a6840300e040c1d81881815031921a100503d030380070f01c2c401c000745801200a1004e80b000e07092241d4a06c1700781c81400c85100c904c10001d21140150310a440300e20b03500043d01c1c0110b88841a60310901d8100c2d09400415140c1d02c1504580b030300c003500c50b0003031036590322020402526007401010b0412026204040c01000482c2c01c000000358040e2001c09a150071401c0701000f0344540c18014800d01841014407a150311741014886581c03d03440700ba6205440f008190001e003a244c0c841c0076264002c0d4072004000c1042880402d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 194891672 1250 194890422 194890441
    0x206070c060b04090b04060609051614090a05030a120e0f030a03121113080c10080f041b03050c0406081f090213020a200d1b0203100515030c040e0303 66
    0xc11610b0081c070102d412540b6032903003106000b0640e021520325a58040400ca100002e01074a540000c85520001ca10750034040043c00d00e02e01c0120803100c8900000303810030303696034031500fa001a20b0b011b42203480c07282042c80d083c2040c1c90719984802c04901d0304e0031307209014603003c05210705c3c01c00301031b01911a075403041d54140d528100c242c1c002900540c0700c984074581800303801302034400c040020410094043c502682d450501a1039581e06000d15040684407074001c1d00800d000b03420a00726155100c0c10382e640c1c2041c10300c04188036040000300074000d0000007403100010740610901c0301123808114859480031019520401c10b0000340708115584101c003104005507000103852400909101c0f04104800600e800300d0380a40028000b103041080f5400c2000c00c1400c5400b2a5090f0000030300c140b60360843c001e0405070094101d01c464030003072051481152000c0c808180c024852803c140200e050061000c114404490050340c064845d18846040381d162501841006104e0b11303010750325544508a40 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 194892922 1250 194891672 194891681
    0x30a020a030b0a1d01091b061e020109080a0c0501050609062103040b040803070b1506030c0a050d05091b0d0c1a0f0703020705040f0b10050c070306090c03020102010c0206070c06 78
    0x312103c5503181035044440070600700140001d0039490001482145915042d09035403050904008404035200d8184500c80e04543c3c0c01d4030814400c00194007070fa9509034100e0140c06a940014481c03900414181c25503a084803203000c0032442080244103e6688005008111000325001c0da4031000a5540542c07031080c12404620a00c1010b00342e901d025110060030459074000d41c804905a40001120011301006004081e04260300142945102801d0030025515010141110902040020380c00c51280d000d502124007584aa500c240130034a0090038082d01d9284015800704800700414010b01c141c6403102003407842c280e110394402c0f00e05060581c01081b284504116881c580c1003081a020340351200e201034650980f0940c010031720f540c100002c0c0010396000c9140e0390142d81c1880610704440d5143c4146a16030045e5107031407502c50120780c000b545083c40d01ea2001d030586190203c410180055080c9440649000303030006c0c010448101801c070f9446004488101c001046a403110300040c03403d820 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 194894172 1250 194892922 194892931
    0x1060b03150907020a140c0306100303030e160302060906120a1401060c05071502030c070801050108073c09060602010905060f0105090f0615040603051009020c03070209130807120905030a020a030b 86
    0x320342c50b80d102103000c2860300c0300035600ca40d40104035440c10010180d0500553b02090414130141c1a081000803e2176820b015a0000900c07070000400c0c103140c00d8540d1001c0d15195442c100441c05541802102c1100601416100c6041081c00d84008103149000350b0700703495a6607101c0020300300207282c2040301009460018401046000800c62101206000c100d0030007e042c0c050000144d42d490300b45050700c0c1040702e50040038024007201407000818080c43c1c0100301d802c0110a02c02d9031040f080c4520a02d03001c60303005442401c0c500070b0301080c8554150b00c445003180c8940219681a21682d01161b2848424070890390b0088091001454082c00e07107807840d0f00704034043c2008600118018808140c0e03007141c0c0040000a98400030001702c4d09840c07403000b00500c000d0500718980400001429280c1c481c524019000340c084901098041c41903014181000d50402c44079a101c5481c0d10300100100800c0c260b00c000682c41c0e45020406107400319054080990041a40c105985142c0c1d401400300c0c0000c1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 194895422 1250 194894172 194894213
    0x50402040e0a050d0e09070801091802030316060f0504020a0b0d020d020a081e01140d020102030405030a06051e010f030320010903080117061303030207020d0501060b03150907020a 79
    0x214a00200002000086880d522440c041d1181c80740890006005d001c40744090380c85031544105018085400400131819a4011100880d2803e004540c006402056500003074062000060800c0303144180d8440506842c07041c9801c0c0310741c20075a06810203454003920081d500443c452402c1203900182e40c0100b0802e504402c001d0304001440c0c6a41d000c0740c220041202c003152260040020b020140900708000514460389110b003941032010102510040f040c0c41070203411065840c80940e8001c2080d200104001000c03600144028030f4020094203007a00c5981410b0520401442914802d00c10103050b54640740680c1007031490b544003224000c0f008030b424816090090700000003040c0130300400307190b14000d07100c841c02c6500d0410905192045540f0a4100d90441c1050010404004208000340c5425107000340c1c89403200d00000311412141d0100429070361800d200021005c81e0b020145100b454000c4882181c0c000e80c00c140a210081110b2610041c1c03c04440d400001d007107402c60350446440d44 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 194896672 1250 194895422 194895431
    0x30a05030907030b0c030a0605010507050604020f15040b09030f0a121409100c17070302060408071a0f16030606050d1a0604060c0b060d02010816031808120603120d05040204 76
    0x3900d42c03142600042c0d4258100103400010840380147c540600d200500080c41e02e5441d010040d1600e40d00c80e45e002d44000d01c107084960100010b0387d9440d82d81c40014040034126943c43e030343d03500c81c0f5456038404040c4900074084d15101c9070820380041240b40040340c0001505011400300c0300200c0b500300c1c03a00c00300d6104101c20301884896495040b071820241d2550f44807241c2c5240301d41401210364031481c40400d2406410841407001a0307003c2042c1d50070941c00120507071100d25518089100203d0109000e65190005007000600d1421000190092840823060340350000200412000e03070b05c0f24000c48000c1501000381840c4140b6a0740245800c1e03c054081c940350038801000186580d20075841500000c050150a1080c860303550f200d590020070844070b800c2b03417000c83c0d8006090350340e0040a402d5040c14008042109038043c1d0802015004001196203082c50343d841c1003255a001540c882c02e42c11051000610682000515a1100407102070890f0410070361503104800740100410032070308591103 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 194897922 1250 194896672 194896679
    0x30a0f081909062c03040302040915050906071412070503060301140a0207060e0115150207030b100e0f010e0a021b07060302040e0c16200a030c0f17030a05030907 71
    0xc40c0316042c1e4843c82100d01185040d05a0b006000358250f042c0c24104180103505050580e200c00800c40303003100d030f05a9011a1014803801c00100940a01e100f204020b824101000702180010500700c1c4203419a031118151104400c1803070b40203000741d2088a40f1660008007003201980100c01450f4050401000441c00d003c021000c40f403000400d641440100c3e401250742410007402d4001e65008a0302c2d00e000304206901540000c0300020a485404c055140b2650170326101032003441480c02840d04050f0b01c1d00300707050495070f41d03238070302124802d01e0301c0b20304448085800306901c07516542c100e41080c0070201a45d01c03000d443c840250b211a0307010120804050f9200c00040041c001c030001000161401a2103030702e0440582d11b000001840e69448010170004851810803800505101641007105d050980b0000d4040704100d0010280c620380c4020503050000410850140c0c800a0f80d14603080c0a401c0350b9540725068400c203031180c126201c0e0304103201f0030140301e01c9107028582c00f05914003282c603840d0b034 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 194899172 1250 194897922 194897971
    0x31e050a120e010e090a0518011b031128020a0c0807080c0105130b1b100c0e030a020a120816050c01030b0a05010813080904020a0806040e030a0f08 65
    0x104401c0301ca68103041d02800d01c081c0c02005051004500f0708014103403208440008a600000510040080ea078900c0070a11030751613103402410b840304020003000340307403000c0b013580c01074501070304e400c000290402826000802c0d041d030958401a818200110f04500d101c6005418811403c0d02d6004510400400c14081030300e080180000700000e0000d000c00f00d0030401e03401e08145c03041d06010306111041101d03810120141040c01c0841d21201011912004401003882304c0c000da00082d0007180c840c00a4510820070076074081e2001c02c0154440106210480081c552200c203540c0c4083d60240b9541c004211303001c06003c403600394034890001c0c40d00d06110b0314000344041d12800b109850b01e80c4582c2c0030340030950301485101c0e00e0030400c4130041081c5250800017025010014400f41601d8280e05031102000b0249090340c10340b00005006644550650000408919046480034812801c0c5810348204000c044100c07080801d0700d0f52030f00d61100e1600f02c140c981501c058000390440c54484110031880c1d8 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 194900422 1250 194899172 194899183
    0x9090c100e030d0f02060c0901020106090509100e16050906061201060c0501060801021306050a0207080706110c041802091e0c04140910060c020303070c150207060e030601031e05 78
    0x1041515252401121101414a0f004560380e016041c44401e40004650301c2c1c0010700d0342c0d440750034000081c3d42c030040b01340101d000d0035070b81d40302c1c0640350308000070b0007a00400414002d4071007403180c400300174505201c140c3e03641d20480070f0451341c10380d1406c0d24103000d9805e11080150388140c002d0210303850568140b800c290080b00c264040000901c07200e40c41001c0207801c1c042d101c020a4400000c3d810040000306023000082a48125070600400041d94500c0f14020b000c1a002411000c040d604a01c1e5030b00b070094030310700080c501c084541c00390000c0d003e410f28003031258130141c0d00004101010440182e007403241004000e0920008280e0606c0740300c5031043c3d820420740c42821300b20b10080c0c40380e1a00e01680201400002c1d0103109441140401940500340c44a0f80221403003454452124021400428158404e040c1c014005100030000410390703800c00d04648801c030706281d08480e0400e40d1408100d0300c0958600d06c0c0360f0f06400000040020070042c42600e008800c6000c081d001c6d084003070765006e2803c0c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 194901672 1250 194900422 194900449
    0x3040b0a0f0c030f23030c2206090513200310080105011404091e050a02091311061c020c0102090108060a0605070213020c0a0c17070b07061d0307050a020901051203070209090c 77
    0x7580090000e02104138860741da00d08d402e944419440f00c0d4202382c40075000c41c149009047c001d150050280b041c0c50b1542d000b005401d680d201e40450003490000201020754030860740813100000302d900000304004144a181e040718189000d0840d2950000104409806a00010390302d65188801000c2443e1600d16051071172031040c002416a141944144410064000c00500e05200c0340b00d0f400010030340810441000c10b4040394542d545103443c0580502040b82681c41008540c80030640d0491448154018004c40c402600c484021361744600402800607a00d0045c0c41c00180d090142e50018100341c0450303803421160040c090304080411440c81d1800b080030380c0a60381101c1254041001d850450b4a00e012091800080c150b042d090840c0e41c5214461000b00400c0503035140c503020b401c0000c04a08504140c1070300d0989985412a0511560701d904014090b0321440600c1c00000c1c1e5481c1c50f18000701820041c002171030402e1030903000c001d00e885005048198502526100f42c440b6940c08207285400b = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 194902922 1250 194901672 194901691
    0xb0117031216080c0f0d0f020c0a030e030106080609070603090807080d0b212d0f0601060806040b1c020310060b18040b01171803040b0a0f0c030f2303 66
    0x1500d210102c010003458002d004441d2410040240c03181400c0b820302210030b5084095004208106404118002486100309003c00e03402a241600205030f40301c0254220000114000c0c4101c0c0d1721000040c2d01d0741016a98610030798010542004181e0190f00140519400b407120315040c64415143e02e0107a900103000384072400e85c1c9411702515440d040c41201c00d90b00003100140784441c0603144c0c4035903514201d226030070b000304000400b500e0500c0039400280504044010354001403c1a443c035943c8007000c1c003500022604803030000f00a810148500b00300500003c0000c1d030a0214046044c0082820100c140c0c0c041c011614031303050800680c046c0c80c0013890142070720765a464010008030741051510306010b00c50350a0070042880c0f60303845008020041c2d02e203c0040c1040e00c581c50000b00c40da1250007400d2030b43c040442c1c0010145420400703010034440c90344485e814040131182c00c4400d0301c0b0818004020803002c6d04405201c51140462090340841241070b61140980f4030b0f44013040d0340040b5140002b = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 194904172 1250 194902922 194902951
    0x9050103051005040305030c180a0b1306030b0105040b0c012a02010c02060c040504050c0c06040b0103030e0d0c090509070b0403050d0315080d081302190302011404030b01170312 78
    0x800404000307180760b002d2440350030491410030b998001c000b0b100181003155400070109607203c000440040c9103204d608001c1101ca0040d030743c0e040400164000286107070145902c2c3d00002013090103405444032a200584d100391500c3d0504a58031840d4102c0f0910424665880c1c1d01960700d498521006a4480d0000840072404e0950300350007801d40300312801e00d0046420036020b0094074007011040e6400e0303130803c860100b00395840224183c0e40e80501d0070510500c6c8181b00038001400140007043e8103980c040d503a0f10520144090602003100018007009046e82e0303021342c0802c0060042d5021680118030441038540c440e035561804441a005a00709031030a80003c8000441140c0510405034107105024603a9400c51401010b66141c4003101001030034012391000248444102c4a01c40c0144c1c0c0c0d0003804090b04400c144000c03840c000141c0022400700358440c42280c00c1e4501401654100c4c3d60241c04041140e0901034000044102002e81101901c410300c0210000d680003905c8a2045559040398035 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 194905422 1250 194904172 194904179
    0x1e04080609060f01080d0c0f05030910030204030218010303050304060e0c06070606080705010912030c0221060402040b0405162a120201151503050615030c0a11010b030a0f0813090501 80
    0xc07040806a000025560048403a820480d4024103003d4026402c400c03405060f540c1c270f003400d03400c5110710560302c0e500c914032100050303101c1c0e0154044c0061b03034000c0d10f4811090b005031000088160080c00f01038003044040c40040c0018040388c2010b4442c10215003a80e00310101403010592030381000b107084504e5911404148481031042000c6001000c09207130513804945051036000d20310143e80b801508008105941074159240e1078450142000c5030800c201000115140141d01c0b07503410746040f481740d4200003a1998916080c01480d001d006415a580c407500008641610000707400319000ea424a900419080b440031814840c42c062800f401e600060f800701c683d4002c1c21222010320081c1000702c44841880107503a81031182d414400981800201925030000003180d65003441500f00482c1c000204100404e11254042e044450300c0f80c40343e01104944c00b282d2401d0784e84003030000360150f10141a04000c50351b50980035605900440003940703000b09509210880103440d1700714180e15030300c810040 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 194906672 1250 194905422 194905441
    0xa090219090b1f091502030418090506060316090903020c0603090f070f03050706051b010f1b0e18070c15090b090321150409120305100303051e0408060906 68
    0x40700494840040c140f21941c0124010744010180e00601842d20100340c5001000340c000c00444000e17000421080f80040900e4519801a007001c4070100c44074010300c00410b089003030001c0d42c1081240c0c010005024203050a02c4c520052420704002d50443c803844440094a84030580103501443d9030b0f0000c2c5c4403080078121010f00e0124150721564800410600c2000800c43c00f0411000303480d040d2600c2c039035903441524034000f207440303076094402d16510b02080c003070760b41c4001d074803583c45404a4a2841c5020b02107080c1990f400900001c2c80d80c100340000603420700403005405aaa001100f4103048200c024140c89000a00940e441d0041c1290b586256060030f0207041003460394001d0005000f10700c3e00700050100362454a215401c0811610584081002034851a15400441d04d02800c10000705a0341c1c1030041c1110300000c80ea0f0301003031400c00402c824005026408090f80c3d05629414501083c041081e060061290300800781030b6000e00011a024000b0b1008034020341e40440240340c90b0030040d268 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 194907922 1250 194906672 194906689
    0x8031008060403050f03060d080d0e0d0906020c0f010201060b040e091c0c02010f020708010e0606150f1207030b040912030b06040807120c0312020a03030606020c01080a090219090b 79
    0x3404481c0e2024082100207944074003268096440855101d1700c0761145c50114051201c2090b004242e90804541064040965440707000070700030f220100d400180d840c0206035260f0006000c0e020041c0c00075000c059150030180408400c1e600c0c10b200004400e503441c00d41042c0c030740242c0c00000d00f281e0f201091141c0c1603010001c04100070a1f5190404c0342151115028040e03019804009051294510350070b800c16000b4081c0c01e000745203002c000e02c0400c404109071910f0348001c03600d081c130075501440284007240405c01a9043c107401c4550b0586880c000340320324882d105000381401c4c01c00d5261016603100d500c841c02504a82c0b88150340c24035040c07041d12805800d68103205038081c05143d044c8001c11804500003224411200c4101c1c02c00d9030381585042040c640c40540d0006070107189044400d0009603400070344a48400c1c000c0d0340801c000c41d1a2003040f41c548281c0c1c04810300042424020035108001a480007059610003080c900c0514144ca0606100f91402ea202d000c0311355492080d43c125081c10000c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 194909172 1250 194907922 194907929
    0x40e0601020d0c02091008120c1603020907120902150a0305130213090602071a0603070f0f23090708270a060506030a0c080303010603060803130312090902030103080310 74
    0xd005101c610b40720003012040b01d844041d11880446010410b00c66490300c070314001d40b408000b42d40684000200c001c94651000d5200c1e503ca2250032100781c4c21220480d00002602d034004d01d0f009080d140c00608450601555408000d000c1da9503900d03800603610f811030405030800e101c10b643d440d2602c10b5030140491f84c000740321004e41c1d40002840d100591740c1050841ca031108000e40001d62031218282903000b405080c400505450003007502c1501880c09034074040c804c100c100c5c12901a02d482e00304031074075581d05104505d50b260788500140281c03202030310300b10000290410700050b0341e44424001604050152188130224410405020400445403051410444540040b41c1540100801207907214041d0401a254580d5070340400d4140c3c0d02800780f01c8000b41c000e5070803d20113448841c9241ca81c0d200303201d0680481d26080c8002902100030007661420f1070b5401190080514645941640b10303031380d03d8080204110a6400704100c5424406140a5809910051f031640ba0100d40e5074912a0186c0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 194910422 1250 194909172 194909177
    0x1c18050609030a03030234020906190911120f1501050705030702041104030b0403030e16210302011d011b0201200c1c0e0f011b03080c0c12040e0601 65
    0x300404064900250002c2ca9640c14a0300513075503000c080d40400c483e400c039200c0c15000c0e00c070f1f160f648480c249020340f0544118001c4440f00015260701080096080030003005094540c2d03014000c0041c0411075000705002e1100052003480d2000c2029000540b820803a00410302c414500c041c04207404160702da200b100c00d42824034030328085013902d40980d42e00940c078000f0f00c6181c03101d4030556441130381130607140115071200b001c118900300340c5400380203031107003803410000784c812018580c0161107182417202c100c4000f55461290f14103850020501a0440142501559201c468084c0b80302c04200e9560302c4e0b1007140000141d001d0142d041604200304904a90086a0400078403102c0b000107154814020f13041265442e584038028040a800d01600e10108011000c119418040c4c640c1c001800341480101154480d41d108480001501c580346131426540c400300340000c0030000a805072035550307000302c0185110750525086081841c942455079074200c41c08070b00400c0411460307001886454002c4000d0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 194911672 1250 194910422 194910427
    0x150b0316090506120d09150903080304030c02030a080a0201200c03030606030403030605100f0816020705300c011202030c190c06090326010e0601030c021c180506 71
    0x500c908103001014052098402e40c1c8001003021035944400c807640390701c0c111040d21a0001074200c05040c84845208158184411004802060784070750028000d80781e01102c1c040c2551103e4908440c03c0e2011031049030140700d044040404950100c0150481030819800403036803403203001030140741c210354100145c102c010500c13181442d00c0b00402134a0340540142d850703d85070b07030b0b503420304401400c110360190750024a061060694180c4c0f1881c011808006511044032644610424500c0340c0126a4030b803005820800090205150100c01140c03c0c42e804001998140002c240c52900103d480008005a610000300c1d01c10558015007800500600c0400c211b0a5180c800180e1450380706142c0b400b6441051f8100010406011b048102a455005a410400383c0c6403440c1c054420031010031900c0604200d102c03260010a007131f0303a00c24184c1d01408000c02d11610742400544c080c240041144d0158041d485140b80400003075602c80c402d0000c20790f14a4003003d4048a1100a070825400c41070003100c04 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 194912922 1250 194911672 194911693
    0xf0606110606120a35181908030412020f0306010f0b09041e06030309090c0c0605060f100302130e0403020c0118051e040c08100b0d06050d150b03 64
    0x71071000c1d840101038445a0401c402202034504000070880700409154280140d0300c075207040e880100b2090040103900102845455070855801e000b1000804d000320040c4114155508000c0580700c0c0349912001c141b0201c684442000c0e0540c0c1158010081c0c1d242d50000c01e50662402c200140102e00c81540604201e505040364046e58640303601070f07498150800900c29100c4e40340c0340d102c0350f6861030520a94407094540300c80840509135500c0141c1c009224641c0200c1d01d10124072441d0300e0001d2648414114281550301c0c040035104c0245170300e5000b0301810013400140c03203a6002b890541f2540d0f4005a407800600030b500844c9900d5084012550b00b102d04220000343c0009000d40b120000b403c003404031080c44039040c91f6000700c9070015070b08028801ca04040384041226140c030040011a41030040c401111011501041c04071103102c2d009060240401c00078800100a28201040c0c580c04078001c0c0e1950085241855110012580050405484c914207410f51103440900031040b8090000c5628 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 194914172 1250 194912922 194912957
    0x30e0c0402040312210e06090f0303090c090402040f050916090c360f030b091209011101060503120702041a0f100e0306090a05101e0209030109150f0606 67
    0x1010b1400c00207000007151021409444e42070741d0980441c458106111001b5400e5030a6100c8406a41c0c98045105003810521400340100c1a40d2043c15000000c000c0f5072091410001c02138009407069800a07030350400d50030002c01d07600941d48a49101401440043c00c90500540400d1030390b4000d03031041e031402c4414500198004c5603884150020120115a924641d440c0707071401c0c0c485c801c001007003910b0b030100081d814540c00c2e128007101d000b40c0d02e41c101d0303a542d4005592a28102480c60840d003400300041e828175801040010f030b801c000d41c000010041d445901003031a04007443d556400c84500030485104500c0d05d4000c882d0080440b4011410096081000c00e03101c0201d100c54511440016a411581d1440707280a1100c80c240241141c1d40c0e030031300300c21042e1500c07461076050b24103000ea4002c54201030540e0055040c5012070b40485003001420f4003103540250030888146525540300c10307408000c10b5414205404c420030300c0f10b000410382c0140c0141c0d000c0701c85a034800300900021700140c0c4082c15 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 194915422 1250 194914172 194914193
    0xc19180620070b0f0d1404050c12190221061510030e120319050c09030c191503020408010f0b0406080c0a050909070e07050712050708071106090a06030e0c04020403 72
    0x4108003440d0b03854402405c01400074003a140c44092400f5201800c02081c002d0001e81843c81000c285c840004200d4003900150300c032040344604081c8582c1d0b103031620380141404c8000f68401030742104c691340e4000b0306d803042ca400c00f070060315114580d2030000d00007005032401503450076000000d8142000201c5828005503120008101c0640720404088001100e22440b040c141050700325403035041045203007400d5030106540040522500910840713a4218103810708400303040015802c94035410a4070f10304032400c4c00400310702d00e480c3c007050740034040000c80308800d0090204103030019101180c04480c20303081c03004035221940442c00c3c50303218122400f0591038200054040c1c0e0030a4a0004646e602c1c469868038010781a448501401c40506c104000396074484060601184192080c030032401c80c240007210349001c0c498018100400400000c0e00280010036401d1215201500d060705204402c00000c00c0312900d98003d4003c20380b04c1c1d482c032610600c10300041031031390070840d030850401c0d0450f1500c00412 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 194916672 1250 194915422 194915437
    0xc0506120a0906110d051008120d0e01020915030910180305070c0e10080c010f08150111070609031115040605182707080c19180620070b 60
    0x82d80d80c20503605100c0d10b0b8002d5050721304054840765545810014410041104070f45804581e585560b02068108010a0400e1041d4000c002107061803e030729100001090440c3c0015134a6508100c412219114034600600c41d540c5000781640768a050340b44d41c0c0c10111400d01c110705640c50951a62002c0d1028082e58004a0701841c1545e21010145005010300d100b9030003580015142d9403c00003a08030f0300c803a10064a8900c2e040c7e8901042880041d03411241c90040240401d108070f0000300001c3d4110a08034102c041403420703144100000f01000c0c00c2c00301a070001c1e00011042101030051281443c29440c4404094410114480c1101480181405140201e60030848001a14a1a5110b10380711046984008183c40c141c0c10040d0890780c0c0000c84000c10503500d4540c600001c00590080c1301336849404110603051900c0c1e04a00c0c0c00c24000788800821061041c400042c040310005801608080d040c55111500e1b400c9050081041d054024850081154000d13501404294115070a45142 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 194917922 1250 194916672 194916691
    0x60806040b040e1b120102040807210201051b03160803100f0b0d050403050d0e030904060b0304021e030709051e01050306040507031b120303060f0f0506031b0c0a06090c050612 77
    0x4c90a01d800080d244c61a03003144041d0542c000300c0c01052007a4081464022185050402003038130301e0608c5240c151903003405001e4042101030201c0c100341e00e00114802d0003030b500841603a00d88031003800d103207005410600042d50410004001c010344500f002c04000b000d000280c00403102e151500202008510840300503001041c0c407030011a00b00343c003940c1076a10803080c5423010f00ca183c40304032004d9540d40040808030711450a159000600e120000101ca0145401a25514060318406100450109803810315609449920b10008090300d0f14410346010704071310400c0e00c001401c0002c0c1c10754401c0060b04128400d8000ca818440014070000701e8030100c9611140410443c1961b02d002028048a9030015462490006012080641c15031144003694148c0404c00341e0316488860f510707420303085406903075005481003000c64a10720307400c942071446440400e0564503102d2894202c48c10542340e40000c590043e155882042009035002c2d840019103030596501c0c2c100110014883c000d010003801803040c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 194919172 1250 194917922 194917963
    0x21303060b1212030f0c04060c030e130903050705010c0e090f06150d02130906080c041a0a0b03010305060601030902130b010c140f06010b0f0a050a1206060806040b040e 74
    0x70540b15030040d40c07440004442515407103d149850b20055500486484484a03c114001810f038411102610b040e1410723540c40b40380503c0156016030700c03040c00c10541d5501144d01d500e134003050740c1203000341703a000f511075541c140e2500c00c20314016080d90882001403041c0310302000700052540300c00d041c0c544d0100001c4d002e0503040c0c80d100003251900103600401c4e03c10380800104042100c205400800981c150350303000c03c84c0b8559038042c04088801c81c0c00b1b0114143c118280c010703050f1800360004a010300705210038040b610b03504070000b6500c0c807985c0e00c140b550100c080300400600c07501b40030007a440744d0203013424070031092654002410085404180c803034142c0d82d498607141d9a4810002c0f0000940d21181030300c0700c81d00c1740b09000d81d10f4400324401c0106104110010904410038410307a40420802003095003082101003043d140d940042840000300145030440341401d5880d0300071403005040c0c2c0e441e01e0400d81081020f10054801c1003079694050360405950703000e20f060000f96070b88a00f1900c3c001d2103 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 194920422 1250 194919172 194919191
    0x219030b07080c09090a0212060306060105030c0a020712061e090b0f0c070203060403030209030c0f0d14030d02120106080c091f030e01021306231204031b03030606110102130306 78
    0x101c40c0201142d0582002804041000d261b255500500d0b007003100400303841560b6525003c1555440c82142c2c80c0740010400c0c00851201d4800303d000e00404c0c8101d00603102d0564444026507901e01e4041001d031a07480d250b040c030300003c14150410000007444108180f1030410a0b4a8160f105207010b480c0c410400c2c41000011040c80c80748003600c12450f4010107540050a19040040194124001e000c2c800e000f51180340b80351340717840d103070746601140080c01580075980240c07641404188001c0503540310307000810040755020841e20040480c00f81c50380c400d00c03ca5040060040c0000b1006090300d0603481c01f0021a0040e0707603070b0388000350110142607140345104190300045018001502c0a51003560020400c05268000106040c040d1445543c075003c014036103003000030400260104256148004000301c000d8204520340071507020740641010356034455082e000a6107000411420b90000c0c1d9501c80c144001540007440920b842208802903080c0b444501c1d01d80050103007071000410f81c07035841c0d4168 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 194921672 1250 194920422 194920441
    0xd0e0112060e13062d0506010315090c030b1005122a070b0a2c0a0804080c0112020c10090f05030309060a0507050315090714160219030b0708 62
    0x440180c00d40d503008009900700102c0d4009043c10300300e400c40300f80d802d011265007040750b801003d004150300c0550310f400c3c03810600c16500041602500d0b9904040d19200c02e4406525880007040c018080828006040c003010b5100800b1600311142c6036100e4000301c1e080d0382426074810282d44c0000707010504507103562220181d40c0564042d070f9072104a61400d654103a04010341c12805812a140900341c0d4221070740c0d030007403d101150720042000320411010791415100604e000001244000001e04960b0a07540070313141c52009400980c0014204c0d0302002c402c00c0d06590103048061014944201542890b159400250302c0c0d20400140c0e900a6607904402d80900034542e884001e0541c1000c1666500d007072108000d501c509044130001a41c0d4240f0300803502251180c000c80e48510480050410328000000400c108080090f01241c20070450601c56420404c1c42c00003003030100101460403880329880e20500501000c0c1d059841103207082074204201003250b011070107034014603d140c650003507983c0b507020 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 194922922 1250 194921672 194921681
    0x603020c07091e14010e040803070e030a0b070f020718020c071e03020a120b01060e031501060f091e14010210020307020714040b0a0306020310030614070f020d0e0112 73
    0x481600380c10803034600e600f0009410101e4002c0180482445a202000181c2808607428420020480d59100014000c21120005590054100d141c07100b010a00071000074501001407506480104407c801d101e003544d040070703254201001500181c00e030305140a40d213040d05040464002c8a0b81d40000d00162400c40511040001e058507001801741c0030b100048010920f085408203e01510b50202d001c1080c414141d8840c2030b256201c005000c0366070030240201da03c1101d50b4420354040c0310f6100144050030391005107601a086546d610715104171003d200406034070042e840000c0741d154004840c94400d24405421050b181071003071410716410301c1e1004070304d4051840071003401c0d54400710600048541c0415010222205212035500c29040801080225003a00300d401c0e5110201740c0d170400018207650003450707208810303403c8000465501c0c1c6a40b401c1d50300d680b0b000c1035291100810051855000302403580c1e01e214510040c1071500e4118805170000c2441000e241c14011203035003020081090340c10 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 194924172 1250 194922922 194922929
    0x130c09030f050a0c0e090a030c0204060504020d0902041109010c0b0603030702090106020d020d0509060a0f030e0d12110313030e04022703011a0109180b10170f010b03010603020c07 79
    0x1621681a005801c125865110309031041310714440b0700800007400300a10002d02d000b440300602030440201d490f40c003034900d8051403900b20b0700700341c40c0c00c40022117540318070207010b47c5a1791102c00708021440b441004229030b8885c5880d401680180b10103c5141d0f4094070080d4200da000c807203440c1945480002070b10394000c400c0700950021030380e00046400c0d42e0125501c0801142602180d114002c00b40b8140c1e824000d006210703402c24402e00614462030b104207000ba1000d601030400040c1003800d00d260b1401d004114402501207510210061074107981e52007482140310751000c1c10b40c01d40c1841199050441100d040103010410a81604040c40d40e03141d044400c0d900300000000b80d031440c2003c402d0275808a42c180c0700d10a518203c220503241544428111000005035192160760303090a200e0741c110a40a98900b211541e034a811480a45030507020a840c1d4940361201c0e8500c03080249070703690103100146020f00d0490f251004004001e80003003a82d0555280d4103000d611694a010f03850300c2e0401300d60 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 194925422 1250 194924172 194924183
    0xb12040804081f06060905090c03060d06060603020c1b0303070206071401020d0e15040507060311070501020309031309060303050306011407051501090621060902010c0b0a0219020c130c0903 83
    0x208507480e4a900902c0075507641c3e81d64201031140c6070b91050161484030480c401e09400103035400016400a03000c0004544c8520000c00380c0d10086030545658040340d00c20340040d80400c0c2c0c0000d000d840c3d0b010420401c0c0c00800c1009881481d2450f80d804292240a170b402c000713010340f038007007040420010b9041f02c000c01495184000c44d10b030002001d0940240c0300d0301c0c03003400300360243c56954910368451204052040360044004d22120307203004001c40c0180384125048541c0c0c1c0c03042c071607403001030b600380011801460703040c0040d5118844603049410300724469200e400c540c0e14114042001a4101050325445142402c02c251087c03000c004100c0746100b400c200a00c24010014034200d00c200200d8000d05a41d19041b04010b00ca441f0b075081c071365150a0400e920907107503090301410005075050300404a007030b2041c54603810758039a83d034500090180a0340c52060b86c1d03801044008191030402c080d0f401400c0d0340d100030107078200300c2c00104401e0210340030140f224603114009103619034014103580d0002e50307029 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 194926672 1250 194925422 194925433
    0x20705091302092a0409110703080601110304030f06050708010f030b0c130e13050c0f011d150a0815011409090a020c07030f141c1d04060b0717040b1204080408 70
    0x5900c50b04c0c07240d020340158030110b858501d44031a070003901c030180c81c031545c2e26032a443c41c1c980b1250015144118014110301c15031000b0000800011041c05145100501c11500400c3c1410035100c003401520058000061072016040c0401c08a007030444200d40122904c1006551004042c40c803240300030003900100510107898040c00050906807001072070460142e02611001d440020401c00c5581c00091843c2c00140401818000c4d0707611a042325400b84e000822907060841d008a00c01b2158005407003c101040001c0100008000e1013058120312601c00d290810084266100ca40071500440782020701411860340000c0c110080c5030304a501019074081103070b6540e55245032a10404c07000d9101112218036509180171006030004e600e00c04d181c1c03c2c0316191010200f0b60000c844000911254100460b0541d080d84034949aa00ca090041d0000c030510650310115810600c1442c40018080c1d8090001048200444a11141071340c4420410780501006521103040800ea40e00035a004500a80a107 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 194927922 1250 194926672 194926741
    0x2303040311030a0221062203030506060c0d0207060807080c04090b0a050604080a030e030303010806013b07030c0212160c0503011a3d02011b02070602070509130209 72
    0x1007005d9030307416154090031144a03035258100002000082e01c801c600b065681801e441c0080e00a8001d1903010b00003500789800c2002c181d560344d1501c2032101c0d003100580c1002c0c0c42481080d81c0211000da011000d800e014684d4281084520340a1146208505c2078aaa0f04243c11007944c9440b45000102001001203840d2038841000c5034481009440c100d022845151401600d8140442545d040703501ca500a0182a0302c0c144501e202040e041d42e054000111240c200b445607010450700c061603585640840c0004e14210002400f16201d4038012401d5500842a028204140c1000c0366042606010703100c0c07502100b444c20240040312900042da1550030700507621441902020714034001c26046420320744289050740748c0803011001048400500c0c05030102c89818101d0300001c0d042400c0c141c8000140d40090760900b2442d480c60707900c0400140c1000000304003040d41080310178040d00303044481c41f426040c455900250401e444030005e00541d00324000030814103000210309100e00d20a03c0110401c0030 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 194929172 1250 194927922 194927959
    0x16021c0302060907090e0303010324020c0705011b0f110301140c0316050a05070f08070f0f050d03061d0717190507031a0d02061e04032303040311030a02 67
    0x80c00c0300c020300e02c2d21032044006603040c00c83c00740c6e88441c0006005940386908645600121490178018002800414103030b0200b040f100d4402807048038050005840c200d42040001040d5045045816001d1407015248601003555011200807050340b009601c807000520401182c090b060036448918807600c203504000000703400c000107500c5a50080100040854090001c3c0c0d8035010303185181d40000c50038030040d40050105080d4184040c0208030450a240a5075540601f060300780e482141e10280c03402c42c11040080030400015444003d0906000385420007843e075405032107568441e048110407002141246014003207140301105403080f80c4040b4a06194400507651000c0100b21102e494580040d490310310030701c58044002c080324480d46201a11034100011181c245000781e91106040112030000344024890700303402030408103560707207a51840c18082d150101a4210b40f410703d0140a045202c02c0300032040b101521b500c0803021042c50f403040046843c1001e6040300070b4000702424903480d450078 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 194930422 1250 194929172 194929183
    0x1300e01061202090105030706090b0913090f0b0c0306010c0f110d08031008010c052703010c030626150406061208030103060b01020d0504140303070b01140109061416021c0302 77
    0xf0300a5070750032456640c0d10141551001540701c1c032000500c2ca03503030034448400900000c081c4000020070040c4106d500900c120120780b00604100c4844050301400f40401042c1c0840e031b0703840100c100ba843e04500e4030b9000601981070300d1200810001e801b600d6078040004030200020103101c0506242c030b050305103251100050340103a86004001d00b0222000442000501484882c0c10050ba0780c142082290740803524910380319004180380c0e03018910780d0503240e18240705241d058001c0e645c0204000e45420000500c0c02034100068440358010b120f5039001a80010b06c1d1000ca000105032030141303a40b0b500300b52000b064180c00c090150352040051009200c8590055030580e170090904104007200e0f0001039950705020528003000c1001801b0411427a600200c1c801c0c2ea0003000380548e442c220040e9110006400240c1100b0340010000a440c82c0a584c07004100000d800706003800c40c0e40400703040e425000342c0106000015400d80401c4114115214000501c2120192170b145191004a03890040e4030340 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 194931672 1250 194930422 194930459
    0x20c060601120903020d0c03030e0105090706030b090408030f1003080708070c080c100819050a0f0b01081015030e0303090c03010e03070f060f060b0a03020909010501300e0106 77
    0xd001d0390ba402000b00083e124881c07000768181c00600380801d5201064940c1c1c02144816003d01d651003410403444c0c1c5003800340030b1182d03c161000d0b00c081801e0401c0581200e0803151058001e1000d40100310005580e003085941000030350744002d50580e00d00310f43d00b07060388440d0401000610007060740403c109407507001e0a0420720941818412684031405580c0ea540b140c420140e00c640402c440d061150b005101080e002040102c0b150000e0514001c10015510252034600c02555204101e403550003044c860460001e50900c4d0484487c04c0c400c003034a6500c41c2501a100303401141c0040318045500035030281e0b20150000b029207859140c01840252203207a41c0381c2c070364025400d044041d103c000d008004c5501d1290f0181c403c0310703400750503101c450040000c0c00c0101e01c09036407400041000384021016004600a07507501603a41c110000c18841c2844043c0d02c00f906014103050b12410440381106070f500000c0c011a40030351041d281940c3c0b84050105084e0250981d460400b0100c0c4112146207600b400 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 194932922 1250 194931672 194931677
    0x2010902180403080f04050118031e0e0109031704120b09010c020336090f0405010c0206010b090409110402031302010207050904050705150706050f09160302060f09060c01020c060601 80
    0xc000403042448060741160300800042811002031055030907007840ca60001d008034000542400ea2501c40d1004050381d00054012a001c2e1040f4240900154401d031a80e00c2c1d1481c101102c40c140b040040c1ca00ca00310302004124040328519460107001c400d0541c0c0051104121121418015041613560644265000c805d15420607580c400f00398000011900b10814200d00d414103215001d000710000a0511107003503250611141c1c0001c1d603238030350040500444000c0800c0b10396040070f141c100c0c211180c8003140c6055402034030041200080303090030707079800c08010381e40030980c0139103440c1c8410b030002d2007904158428404000e00817103a55807024803c40768404c0e004c80e00540c0e150810400404001c80340104a0f0b8040c0c075060140d42440381c3c40084039214942401d04181c000c0d43e8a80075038008036210080c1d040d40c4010841d01e00b50400070000c03820f01c0780c3d80e40380c00d090a60b00450f105101d101811203e0740400100807000761179100886405d041500300031034030f0300c9840030004e841d45c4054506500 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 194934172 1250 194932922 194932939
    0x703030f0c02030f0705010216060c1b020a0e04060b040504140f1207020f0102030f07060c0e010f020d030b0a0305100b01082d0a09020402030a09050d0f0503060f0a0b070302010902 79
    0x294110900c100e4000c500c40b50000d50800c16140800b00b007a6201c1201280c0b25502032240041c0c044060182e009541d21641010a50f200032110090a0f5900c0242c007141044202080402503113508054400351281801c0a210985d0b85040031006090b01e8103075260401d1401c4200014031155070358803128035804005440c1c0d040704443e0703807507507500000ca0001d200c1d032020000e540042c58940143da220f0001801541c0c2015050a211112031300b01d4242690360387c0c1c032024007202c2e41c6d51040b05c00103181800d080c03000d10710105640003035461014480a2003419a102220f50750350f0b0f60801e00780c0045a202c4100c800030450508840050880510458041056900401d0b0f0000400350b0141c45900665250800c280c00c4170780740100004c1c0502400340265880c04108056219400118842d00008101088106591410038030307200040298104100b056007103d8481d80e801030807280c00c102c0c100e80c0e10b400038200d0000551400c0407984100c40c1c400c0c001031038600700354041d00058074040c0211503602 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 194935422 1250 194934172 194934191
    0xc080a0f0605070f050313020307030215090406060518010c06060b0a020709050a0c0f0305040204140f151905042432100c0f020a09270c0308030702030c1002070303 72
    0xf9204c500480030071002c118284001401d95440340e0700c0f49201c0740020216070f8802c3c1c0d20340101ea44081c8000b0b10901990b0001103100c520300b02401200002d101038944540351041d82ea40c49040c00c06140c00d02410002070070140c030b00b4414035410600c00362001c074000a940c0c0c450b42201039074545446c45041c0800c1d041c603000450170181c1e0300c03c400ca07100103900c52a1274546018000c03002000c1c020012070b403180d034403154408c00c0340035224243d1003542c00f001e00035080d0034450841c051304090500d0380c5110710b26500a00400700c4c401590f080c102c8405542c045081d00b603500c1c4042c680c1c010a504404c1045080600050744111007800d59500403400d10140110400c1200c950741605898205c50303042340c402d00c03d4003000383c8030b961007001150040342040d4143c844c40d4000341d0003030320990002100c0c2d0b454042d1000d81003042c280c580f0b02140e100c000d2030301041d12596848800c150030710000e4500b02011000642e036038020720440f802c2d001c409040d2030f880c141f0132240000a4020101c1a0f0001e840c3c0700014 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 194936672 1250 194935422 194935427
    0x20405070201020a0e040c05090634140106030804090e030d0e01060e101a0921010209030111070b04111807021605040c0929030901060501031104030c0608040c080a0f060507 76
    0x8422010542e23950702c0c54072aa00c1c041c802c0ca41e01200d41c1d05480042c040e0300c0c580c0307030315425404580711402e5501c00e41c1240041c20820703000704540d068003466905d00001040000d400c42c0459081b2018800c0100749160f02841c00c034198001c0340c0e5801103641c1031411500303c0c0391041d030101c816910f18440d00303005078031220300b940071a01c0c41e40920340140c0720380180741c4020300b8210080d08041d9030040003401806503042000c0d078400e219000303040c426074021941d41e0f07851a0170700500701e01c01041030000b41441456103461000b260050005452440c03042036803480e90300c40c2034010160030703405440c5070814209207a0003036441460f51258084030b202c3e8440841c0034074150103030031940350790b0b60b98100c003041c11306444000784072042d00b042403103403a140103510454103104042c52144480c0800000c24030f16103030000d025146400740101007020100000e0000650624050701030b40c0c550301d03005000f03503500e10304502c1400c86034106480b14440c04068200700304038140d40181d0359100d010244195111075205 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 194937922 1250 194936672 194936681
    0x50f0a0b070804020d0515010e01080309010c0b0601200304061b02090a0506060c01060303050c1204030b07080a060504020f0703021204080c010c150507020703060b090106051c09020405070201020a0e04 88
    0x908100e54a80490845886031800c03a4000d40020540c0c50304030304540d40c0520309890748400d42082c515103001003001c5140d22102038011300840c0080c500d0304076031070300080c404114100002c205040c044003150140e4403500343e80090900003043c80814849500c2000e039260000d2085000064103401241e00401440d040c017400aa0b0280501c401922454003002c054040100059000740301809071640140c024001c0d00021802600d81503a120482d0416a041c030341403500c070138000c500401040001651100321035510000724503003072406440b9800c0e000c024100c0c9501c8258002c2c00401c2104184100e880103140701c40c426021114400e01042c555074660049100300072464101c0307100114554001e00c2d060400790b11508501c0300180752943d41d1412500d09850002c01070788058001d20410000303214103d01e9502c00c40b280001580b51090040c41445030318a240c41e00340038089078120394505034200c1c00f21141d0080062040d4070301414028000d400c0750901380700117054840e528038141002d03c00c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 194939172 1250 194937922 194937943
    0x304080304090e0c012a0203030f0414120616091a0d050f04020307050d05010e10150e100501030b1f230705030316020f010903051314090a0b040b06030112050f 70
    0x440c1d03c03034441120160b4a178091710603400c1c550b401d0072801c0c1c0c50060b5412700c01072030f4003180c10a84a40316402d0132a074510500300380c02603030300551681c11840c451070760004106034806290b040002c0400b000c1342049414039a41c0e4421210310391803006807504020804007809198010301c05c2040f8903503c0c08517501500c8001c0c1d8010350541c210130403d001d5810302c0d400c1d482c110750191002044104c03003030728030510f840e4500800c881a0f903544d104041102c1e04034203604e0010302d028280c0312000c1c01e182c00c66013205c01e281d120b8030f8141980d03850540e00a40741c040b4085407101c0785c1c0740d05440041d4200c00103002824080c588501400760103150414504902c415074100e141c10070300850440d512189050001814050140107510070034107944503001c82402600f001c2d501c2a034459844202031145043d00c0105a0828140400509901080c548511451170762125101c1310210380e88020001090091450824003071b007146001001151000003070000c900d016100c0d0302181c8403078007080c5110381c580726000b2 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 194940422 1250 194939172 194939177
    0xc0f0625031e05090a08030109060806090f03030f27060906060d170f0c06010b0c010f0606170a02040f0906150201020301030c06050c070b0304030c03020115052404080304080304090e0c01 82
    0x4008038070b9128030390142c3d41c000c0824041720541c10305501c42d4641c2e50000d034402d903140b80e03e80b542448504028000c0e81d0300b01d2034040080c6031107404101c2190312408020107024032610800005140000d42c4184041380340c455500070710400301d1080d12152201c00482c2c10324098440d80313010680c682031614680d0351494000b0000c0080c0c031010340c0480c18a61080302010724000040c090038036045024000d46000b4030780d1a80c041d56800e01c000d200c038251820001440191b5160200800034141c0000f03540c040082d80c412825101e0b030780c0e814860700a010b15003180420110101d00810300c0b00c0c140d071120081d6811410140200103015904900f03038032090200a00b08100740a041020a00034009880300285d010159098161540740014068008070340580000d0700b40c4000c0d8040c1034080c49a24131441841007000130007414140450041c20b90035144110300d0b8204e440380742c0305100303080581e0054454802a00e60340c5555460041e900d40290190480030707841d241013880b598400080b96070340410180c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 194941672 1250 194940422 194940461
    0x130e0d08070c080306030102040f080a0b0c130e1f141302070c060f0203091005030114030c1507050c100c0201090b090904020f01030b03010627020c10020c0f062503 72
    0x43d070341c03950a50000790903150559020301000c00c1c49804124000302400f90310300205215030b0780f070414906a000140181c480c0c903504000c0c0600400340780c078944050741e140c0806505a504c5015010340c2d403080e9a00070303c03a01d469454000c54000e022102944400a040394104c48800714130b0880b0080744030710340008203040c0070300c8010044140104031070041d03120f090041d03c0c14044a42c0c041034030340000f8200140010000001404151203101302d28072000000e50007080d104801b000840c0c075914505505151460010900c07030b0400000f008115604007018007244807651034480040e00340c0030064012800f09141c100e0204641c030040702980c5188400407e030103560384654007400110016150080d040540382c2005a007551000d025000040100d03800061130701750707500e601c140c0301012a00c0c0813015034010460240c02c000c0000706401648420b10005960b840046040c2c2d02d0301e810015070050302d00900003008103c1d46103054950a0a42908035a5020000303801700b00c0450700c14403008900e11216 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 194942922 1250 194941672 194941697
    0x5090d0b0f0a1d0705190305030a0f09090209010e210111090907050a0c0b0a0603061401030227010b16020a090e0c090c0a030e070513020d0608150c03100302130e0d0807 74
    0x1100c400508040d03150320486c01d40342d0701c403d800c5a10030350540c0f020900250910703208540c060a004001c002c0c22104608102201300002d00c000c00307024400c0e2041c010726600c1240c003840c61407030490081c81c0400800604170b074100c890101c1e400582c4043d00c070303100040014415078012412111050890366504041644903a030341801104048c00a010840c2c0d25000030000540609c1000e050b256208036441c80b542c91441009000304024400140d0340124249001c4422aa207902d41d0555078110080c6448008100d240044104d541001950044090400040095199110420204520f010785244185042c140044a44140d514101c454410040590603500c0f0354044c00900440d8800c0c0c07004243d88000065030113030000685101240c2c005010601901c25102d0000109401009005101d00022001e2100d14004210340a0038a00100060011044a00140140d5801415140801404a118030060100b003020504070700c01d02030302041c0c081c011031046114000c0303569a083c0d0b0500 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 194944172 1250 194942922 194942929
    0x1c0309050601061e110c180405060907060f0c0f0f0f141908030717090c0108090d08010b0c0a0f0606140a0b0f09030106031403031e0705040605090d0b0f0a1d0705 71
    0x201e111940006004581c500c010303030ba8546e01d07140950254104012041d04049c245181803501c050b01003545070780039100402441d07400404d81d00b50010141400a1104010308144081c030405810062100e00402404010800c410218000850052207045404101d003e8840c1d66041c0040e214102c4840000314a40050380c107100641c0d00505a180001c40c50318000039560764280213551409680c0c011050740a075959000d6150b0703034032040e600000e010103041e650b0090030201e818000d1045c8544001149105400c003040260104c1d1b0340904282d2070044e40b42400001000240501240030b000860041e00030728045d01107000703940324a07001d58500a120054201940c0c000080309405540b18400040400c00c041020040700d281040511380c2d0b4541000c51a1280b9450140e02202c0500300c0103000041e50320406503810b0301c81c6030a001d079031984070f0000180f604030a18401807203031513500c04000c000e50410b00880e00070140d0035418001c0c0c20f10340040359a2659049064001544240d03000c01c241d24 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 194945422 1250 194944172 194944187
    0xc020615130203070c0b0403050a0f0503060a03121e09030c05010e0102060604020904090204050c181f0305040303020c0102070f111c0b1810051005060412030e01021c0309050601061e 80
    0xe01354144500c40d02c01c150343d06480e64104480540203d000494085855904030302c000c0d0b05604545805e43c80c62404030005240c2000f64080900727400c1803203d040c145a400b4901640100d0540c14511030120400a0007c0c1030843c0b82c00202d82800300041c0004255004240c603010400d0160041e19041c1e40f144e0038003000b5000010810f9000d502c0340a03a00144c0c40b2403298030b000340070f695070560303590041c0d042ca510490402d0110034010540d50010b10482080500e10f2903105071180360201c0c0380c1e01c1d0b500302103001e40241203820031a5440060208200300e6520110380e4203a10135400404000c0400c401c11040410503040c1100f001e82128081002030108200c00c0d07441400c0d040f0f212104460402c10b2450074001d501c40c4a50f480c0c0e600103001d02010809030780700c014402141c1031882c05081911031a40b04d0380c016030040500420140d568807a0f03000f41304121901441c01c00d031140c0410031640c001c000c0c04d4090029a042d020300c10010070300c135214401031801500d065165110324030b500c7c5030455198 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 194946672 1250 194945422 194945431
    0x60f0e091b0409050604050f060307120305120711070801050105010207060c05030d1103090114010302010e060c0f12040303030b030604020102070312030b090a0603290a1a0301020304060c020615130203 88
    0xc84401e1030307051100703010300944050103441400084618111060004440000e02041c42105c0120704022043d680011910160b440a101c25106066145030540b41401440d040c58224101c5004002c00103034080b80c2e41502c40300d140100e5500d0340c0c1e280c40203800c0310001e000b042c0c016000460f060040c14054643d03503034060b1092080340d141c0b00340c1504081c200e45140c0110030090400105104541009010700c0d040c140180d00d21034101e52443c0c0c00681b5030000c00d0b100328001c44005c6103842412005101300603102d042d600569841e5540c400002c1e50a40c010700080780031038600f4103140811f0500145051081c5d0f41a00201b08450944d19441e41c58200002260101525a80c00608a4071940300e00303405011041004031b60350b800c520f4101a040a0800d594012485030032011441007803e1011907002007400e000001c0c10100001811114001e445803190150f00000c00e010070000c0581c042d0500120550030340f4507540794405d0740741003804040d03c044c0d40b20f81c0c400105401c8921030780c001c6421 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 194947922 1250 194946672 194946691
    0x10f0510120c08030f130905010b0a14070f0b1905040503040302090903222c040b07050f1b07081504060513150506040501051219031103041e060f0e09 66
    0x65580780c090511395481850942041c2c20040b0b0881107002699540714041e0100c844140301130740c100280b00095000f268000410071008420b0070f0b60141c80001118802c1d90410301690841d40682406404e401d025104203100c042042c00040c19447c01348a424055540305014500e4640f4513002c000d00f150000d01240d0103800100311501c3d41c000c41424924402c2c40c0001640c0c091840d0000002c5052030f840c00e420f1041180c03034440405810781c848001d602540c0032002c112140c84004044405000d0000b08002070b900c0001c282001c110348241034119201014103e031000ca80302c8420607116600680d40c080c806a8040105001035201d40009521400b09501414551200d44903c001c141148102c5031060350340d0814003989050a001d90f502400c41500ca034508000c06601c090b503258502c1d1505081d00c1a240c104004140c0b148038401800c41302001240d07169a141c00100705910b40c0040442d8109060b00700000d505c40c055400b07101c40c525503803100d11042d55003505002c28200001e111404 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 194949172 1250 194947922 194947943
    0xd0b01090e090606031501080a0f0501060b0a0509090105010f0203070b0402150301031b05030c0d02062101031a070201110706051f0602030901020105060307051f0512041103010f051012 81
    0x298020070046051090106400428407424070805242c10700a95091000800c44200c00600111100045907001c590340509105089440b0382029801030006400c000b0318050005610337042143c0c00406800407400469560354207907694030054071200000003010001d07820a101ca800803030084004560b00c00d00152190024459170008541c4542c001d806c115051402c0d410302d44d070061000403013803000d0300703050b0018040703000254001142c149412000034401d060009501c0613004a003c02040c03540003500e8400f4440d6180e291a41902441080c440d201c41219000140c0c1c0c07d105004102d0450b101a95070b525194080d00d90102414008040851202c00406810689000c404c0c00324018a011f6001e0b64a4a004900081c255a03018141c03d12030741c803030002440903589501405614040d807100c0840500d143c0b16040d1014000c101044131858000c2040105004c6481a050041403040b802000100030300c4440d0001c07a00b065640e01e00000898805229901c00101a6800700e80205032461 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 194950422 1250 194949172 194949179
    0x100504050103030503090f0601060818071205011d06010b031b091f1103090907081902040806040201090902031b031302130c0f3b130515060a050d0b0109 67
    0x4080d900c082c0d104600041001041010888050140c11100105e41c80a01141d51510000420400001c0c01c0d10855031101c4402c000018001c201c0f0700c0080001604581c5c003440b06050560007841250b03070801d014000c030b44034080100d9001c1001d0b41600c1502c4403480c20360322244e58550070403031075003400110482c04200c100e52654410390100100c0c0f4910141d1150040d84a04c010165030aa0b031860b40c0590081c01116299a18660340c0ba500120a15066103290b40d5405d501400800e031101c400c80c403038030000700482c542c44085001d9100314002e0320b422554554a076214400c901c011111070b9504101d1003003403a050b0300d16a00031a08801c01e40c50401c81e20040b6000034030301d45102940001c06070b94501001c503065404c0740c0200f900844c9820f14003c00c2426040c0074212070580141030501150310f6841444010031020100f040580141c51305c401e04c0700d2080640f0007400d090319404d40041444003228000d00d816401c440030740c500c80e03540c142026099000388025041210003035041c01500c80011 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 194951672 1250 194950422 194950429
    0x8301c0504061a1503070917060108120307020d030c0513080609010c030b0306040b0402150a050a02010614030703060f0e010510061d01080105210106060203090a150e06031005 77
    0x8041000a101002555050034034146084510b0020200e550103018030071072100303649104002c15490700c0c0c1e42c15aa505e0380c80100071141071451380c205030b840d480060708000d2450000110356050343c5184040300e1082002680d0810140004c440810050344404044041a0304c26002044000d1440c148141445038a5910703000f001001d0300301c0c0d041a4000010055444824050b09960107000d0078100718140c25207020030b8a4150040c00070b84412a03036000700d421911200400d1900031190f85200b5181d262850009119621004c5101c3c01582030040104060700203501820003032500030010151185143c3c1d420001e81001ca0039003507000d6598050320303071421080c01680c0c8101010524a5183c0b810010b02400c810b5828101c03011580c45075100300180c2e60446011815107074103c600c0c01280b140000c010a03043c4520f000c5101039400c1a00c00103001c2e40010282c5600c00080b00e8018050740c465100401e140ca01104e601e0001d021840b010b0114101030001f10341141d10f021a446c10307940c071807012 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 194952922 1250 194951672 194951707
    0x43305030d02030d05010f030209060d050a05100507080612031c11070f030206010b030603070608040204150e0105010e0d12030507020a0b04032a03021e0106080a0503030109060830 79
    0x1610260f000015500c81d14821031003202e0241c046804d2101060381590003195038040024000d500031000c00d003411042c400200b00d00da548a5001080750030031994514400701810342a01c1580110300010b0200d2100c0c0b0307290302210610b45c105001942090b00300402c0902640900c424141c034156281d420f00048604200200700d018040d80e503c00f00201c940c5402864588141d000c2550410b0a20505c60300e0f60b8040340d9030007102c1051030081c80c0d070344403400010300401c2102ca07051000400e80c500021a03045134019035049070400d8941000e800400411704c12102100c010040005880100d5101924080d90149800840d10710455500040c3c66880322603501c002d807001d40104450781c00c00940c128281d1401b4040c1540100d500403180885e680c040d6617182501c5800b0400510710104001d8000b00f540f00c2c0b4010100c05003180e041c84101c1c10070039101da0080c00790380000340c01c000007c1016000000c884501140d80b100924084481110440c420080d1043c022000c0e041040016200c200c500c4c02d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 194954172 1250 194952922 194952943
    0x20f1215070e03060f011d0103080904020a210e07060509090f1312180902090105090d0204020f072a030506010e040318170f0c01120203040f060e0a0b0604330503 71
    0x1803417070a504250131030104114007955000e002c801c04005000144141068910b0b0100a6401688403400381c20b00fa210008800201070321034041001da00c85200b49a00000c0120000209842040d0f44484089070244207050300160004544008100901d50204c0095030010040c462107840481540c2d50261800c40c2100341000030301c040c24003e09040c0c1e81c661900040c10304081c11032a0140600c00641940640c0000b40c1c41400c65507440030540d19281c04540ca8040c1301894141d40d0401460a140c4c02040b90001e0281c0d0324004207502e2100310380a440d04150381d0801c005008aa29103030040e03800c00c43c0100100e04200300026606e0703426006c1e9900038040c0a090404030020f0210b100f40b80c1c58035a22554000341c2c1da008452100650f45c0201d0070141e4282d000b41b000d40e80b5034036400c5c1501e000c140c50748024500c80c5444400b40605c1d10202c0e5110784144030300c02100d220703111032003000180c6d80074040071120404144045010684907210403d601ca484441c0c00d08141d5a500010f410807521740c4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 194955422 1250 194954172 194954191
    0x4110a050c0d08130818040e030403060b090c03040807210c02030607080c090d2d03140a0509060309010f110301080f01020c060103020103150305060112020f1215070e0306 75
    0x60800c0580d50240880301099280d480d081034035160080410130703d19149031001c0d100c10000255620741503d03070100c4000f0103070050800c2c0401400c4103c216903d511a100a441403483c00350144441e141500c4a98050100005220300755191070300c0340c0d00590300c1100c08a0312500d000c00290001c568100490607092030688801489200d903006241c21700c42c0007400d0400704007445d01040401c1070308000b40c4440d8070090305d0b040008200c40c9005a140240e0b02a41e241825191001c44102c17902404a81c825911a50f102d4603010100c850784401070285030400e00104070203101c00c0c01c8900b08100503541c00300c0340c80000310b03c483c08201d00c101210001000b04414400000c014000c50904001280d40180d030040210300e0440d9515140e03031502010301009042540b80e984c8400c0801c001c8403003e029540120643d00c01c2c0d6035802a10b44840c000142c12806135120100443d604c0c41c20305941420b01c003078080680b1560360400f00301d0b080c84800802403810300180400d81a03040d10100a11441246d034503 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 194956672 1250 194955422 194955427
    0xd090507030204050c0306030d03110403141b06070506010e07090509180d090e0c07050a080301140109060f020d12110c060603010b0301050601090608092b030b03010c091404110a05 79
    0x500500040d211300400c11174045200f042407009a84002608070641c1c2c10707a00c5d0014004100d20140c910920880d800980700c04200c10704000c018001042a00188864842d04501b20126105100d454041e04001801d1030308850010001d1300e00f0341c42c003290b101d8221318040000d20745840c00144080c00c141c4052590303908803040798407184410410b4508080c400d051807078140b480d2080b1444200703801024142c03440c0700031070020b0400030200441a812580442103d881c0d40c1c63b1840c0303845000043c403203180018400007002440c98000c0403044202e40c2e4903406003050320b4031500309641400086444a8290340d4600c0e1003481c0302d60072809020035450040281410741007a004040c2910900245a84a64074000174000301340c0e0010440c20803104c0c1e03410134801681d0b03200c40290801d05040503044a00301030451420204d07114801668007560302c0c0d1401c01c0142550800d00d401c9990105d0f0cc031010034508441031060508403030807001700e090005c0021401207038881d40084e01d500021107110206401 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 194957922 1250 194956672 194956679
    0x150905060a050f0a050d06180b04120c0b010509040318150815031903030f06151701060e040218060a11100c050307030509010e071719020609040c050d090507 69
    0x503070036800208421540b908598180600180300d000d214403555100710310140e00c030350802500c0d8101c1804014a0362811500c08280e0a161659030790449084501001d1240e283e4060341c043c1c1d940c1942d05070002050065030382084140b002550002c1c0007034050000300050b0909081c1d813088010301030009078162540b944e114045c060120003000e8035170800500e2b106514000e984000860541d5079501e80d96032101c0850f035007000d80081c80100c0e4003040b500c0c20840c010038480c1ca15034003214403458a0b624500351050b00c941c950050703030003070092900141d003550140d50285082e03000b506041c16000144401440740000050b6079034401003078900840c010080d007000f562018019900c000c140c14800380300c61400302000074914400189584141035643c8041003200301c0943c0b0056443c8005000c0305c00007600e5000d461000d4204001e000001c1c843d03172812644100c2c4c1c501c00754018076405031201d814000311004002c007070301d52004003004201c0c043c04405000c00b0580a0308550314010703809000c2c010308 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 194959172 1250 194957922 194957929
    0x70c0b0103060e160b130f0b0d050403091802210402150309030d140711030403150f0e010212090d0f0e0d1b0b0a02010b01080408120402030c040f0b04050907030201080103060f15090506 81
    0x117003039201c47c52007074081d00b042000603040e41c1154140020310700300042e04e540c0c510b41550449440c0c5c00c060f400000c0031021240b00c88481d4003d043c1d100c0c030300008010007210300054040038402110001d400554030041000310240030005590000d040000781c9007042e0385001018121908100511110b000341c00034004456008510310620000e5217000c1c0d840c180c00d60b144c415000c01981071403041c0070355034000c5950b40e142f690701580d000040c0e40004d5580302c401000c2301a640740c0903140826180070314401c0c0080240100c0910090101648411480180700c00421030841202e000540e4140c0c08842c0112011902c02d4507100500040c0c81d069480f0388080e01c000b0300311401100d42c5414012404144004241d10a0039100d016162905d860b409699500c0030a04004000d00e506800504181c003503140300000303810800c07038031105039020040344c1c0e02c880c0c2c103d0b0703181c0b0584406808a1001c0b001400130a070a03410110440c200120702240701d250807042e52002811581c803585042c1d82d180c003840f100d40b6 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 194960422 1250 194959172 194959207
    0x303090d170703020606330a0c02040e01020306040f061211130c05040303171014030f030307110c0301060b090108090703080403030f080f090d030c0215041406070c0b0103060e160b 79
    0x3603a4140c0d8081201f403109540000300c54406403080c3c403580400d000c007106105030aa44074040d8042c105005461014800c01e010703400585103d44680d0500740311000c020814401c040445201c01c0e107980c10340d00306803206003c5000c4161002d400c40810040744428a40320b004006040e105503442a40d40c600d035060003081030000008030200f40c00c550050108412400b807100081c3c400b044803403907400718240006858542c6204510003140008020455405d800c07185030b500c807580b4a0300351495036800340105800c860b039a00408a070703004288140c0455502c0740711080c2e03206900030100c842998813522011100c0e00203030f2048000844140761224101d600c00c00090b041040400c003903d01d41070400c2c7c003d44910310800c10404240da02c5c0400c91401d40308001400c003940b1100101141802d041c188002c0c0300e0200005e03882d1521410f0040740c9518403a4031080340c2e9581007520305180342d00310381c3d503403026280802d40c6891074880c088503546240e00980c0d401c0000d1003a0100965680c0b03001c0311120240 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 194961672 1250 194960422 194960449
    0x50307020613020102060105010e0103091407060e01021203070503090709060305061e042102101a090c0a0905130902091e01060219060b2403010f0e060303090d170703020606 76
    0xb4000c800e5480c0144d0300000c03041d040d42c0090802c00381c04002e03280120001c240d101c038090602d00c2c1d0700815500960340410307003030309843c443da0300e10503812720700c03001a41d880b00740b0080f044000e001080040d20030707031181015640020300d032810707240d80341d54a462039400e07560303942c000781c465802000502c4281c81c40b64a0501a50a000706110005d24141d05d444040c0c581b0401b2220003410f0200c890100c1c0c3e031007804065200d40d02c0c03c5003000b80304651041448130103d0791004500071160600410300503c07048040d1007950010707039038a2940a040006000c40035888101c0914640d44030041d107001603a5070311a40d8498008009481c540c1402c409003d65807410690264041d5003195841980f1980d110800d01e0320250400c2010501040f0800812510884095a0559030501404080100301002d0045040740c000b25594401c6607242c5c0790400d19800c040c0c441c96450707070003001000b61500342070100201d064081c031a48000240d0480f0542c040d90300110048005030090000c00c000381c640050420202c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 194962922 1250 194961672 194961691
    0x9050109050c0307030f02190c0215030c1801031509050901141302120f06070503010e060307060504060f0e0a1706010e22050f0d0e042301060c061b0503070206 70
    0x607040a0142c0d40c01840090000010982c0743d00c10407002c14155012900c4c1e260704c54141d140016007140005044140d144012449000c50b48050200139030315005583c0030b0341004580d03d00c0c00700d0605210038030140401c00241410f44408800d195280315129a600815103035402103140d2034080c482e036003101d250711009100787d00c0b45014821410007803141d00d01d40f076605440c900400c41e50304900238070b8002c407041d12030310314490070b0304100485030f20074007950484105207550748590b110310080645900c03142c007440001440c00c2c80108203c5100e803c0845000107203041080c00c02c02c0e200b002c1403e034140382e000b810707a40e40f0032a8166011082042101e00600b12032198080c0c504006194909070003100c41c40c1d0110400d40d8a11406005044c41061340c58a045001c071461914a40b0000d030091560400c241e1041e45080503040c1c82c04c0245a0540c40030954010f0300b0010f0b801c100050f2071032100c40e4001c0e02c0d9541d84001030040541708600542c280052a22101c2d124030301048020318020700144140794 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 194964028 1106 194962922 194962931
    0xb01030e1f0b0604060e100816080a020d0905030415020c1e15030a06030b0f04020109060f09080f010e070f1802070201030908031003020f010306061e02070b1309050109 74
    0x140186c0030381e21004120600d800664001204480b00d10300d100b1180e403040300203881014001e90002e0105030060901a404006000b142d05d078441c11641980000307401c1c00101120071780d0941768841d82c401000d13150307004000300c0d01e0703209480e40403d624480126950025034907d152403010006603034036203031a8648080090050b0100d40b200b0380303959540713a001c40c181d00c0207a00500e102e140c043e110740000c1c616115041390a5902e80400104006500300e011070300d5102403010320480d4140340c00208140e2210040941800c0450384486500c84500e482000040380d41c040c0484e00d5000b425006896140c0c60005802400d02840020041d031000420004000f261403440c00c1a0f0b4002d0720784220413603900300103408843c07240c0142d001040242503105404680303050400d081d0135582c815140f555540700c2c117154607500580e4200c1800543c00b1014004450648180350041082d81790621 = true := by decide +kernel

theorem cover : BRFrame.Cov 194784172 194964028 := by
  have h0 := BRFrame.cov_init 194784172
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194784172 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 194784172 ≤ n) (h2 : n < 194964028) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
