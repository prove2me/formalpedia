-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1305
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:16:59.51454+00:00
-- url     : https://prove2.me/submissions/f91ceeb3-5fd4-4ff3-be4d-667dd03cada0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 234532374 ≤ n < 234712230 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 234533624 1250 234532374 234532399
    0xd081801080c0d090602070204050a15090b0d02040c0504031505150d021f03060b0a03021b0c0913030201020417010b0a050405070509010c0f0203010203040b0a0b0406030c0501110106050907120b 85
    0x3036000d8440c614881c0701107613072111900100141e80e0103e070b0b04107030000d2040c042c1f400c1c1900c0100050149101c8000407404000c400500700190380100c01c00c1840007000c46403054490340a20018050031007850040000821003c0700040d03800c00c03e40284058000009180e15115030014612007104903680d100b188010f02100060383c03a00f4480c01c0d0302c003640c501692032076601c000030b8000e460107421140c00013130042071f90152241d03d54060904131140400311408240041c01482d01e404000005a4000f82c40e6070000d20400c41e610464061144288001807a096903640d200006013054440030a26944682e2104000d1400070030210103400c0c00c803010826410949e202a0141c4100380305a8180300b0014a0702003802044003100c01e60a030050005c0d584c80c1782c24070b001d4074030010440c1c40f051140e00c0c082c015010fa0a03d8801c900940c1e500c03011000801d4281401076951403044078242000c6d640703608001c1410749540081501805c465140c4002241e9601c0801c0c0642e005600c074036000f980099241c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 234534874 1250 234533624 234533641
    0x40308030412271412030d0b03010b06181e04090c05031606082a03010b0703081e19020c0109050c13050f0109021b010204061e020f0c120c0d08180108 66
    0x540003207401003804064200620130100d0030192020640391010700010412200c0070400390008a10510204c0c000c00a000d4482c2c1045100e0107160010120640818500c0d501814640c40c0b500c080700603c061a41490111800601518106441214104c010740e104004500b4100150b50201c0038409000142c1410054001c1803144000e1042c11111017652070000d2a4060074415a0f0041c0c440c01d5a0795607685644e0040c1803544002d07400c5000504100000d240c100e00031315a0520fa0240d030501e0103054582c4c103110754000ca890407603802610703400c00401440e000244a0303002158418000362120201001c100a0404030309071050800030304003c01c0200700c410304149130341980c01082005869481005404095072242c0c00c1c07a2406620002e000700700c180e0071050f004102c2c2c81c48610700f0f0030355141f000c0498980f401010480c00c1039100c0e80c2e90412074036010300c410144180d440120b81c641d011130300010310020428102515010030000701440c14038980b00f6065410314083c00d018074075080c107019 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 234536124 1250 234534874 234534947
    0x3070303020c030d02130603110c0d2609030c240103080703030b030609070305061620011506050405190602060a0509031603030f0f140a1a0a2d05060409050903040308030412 76
    0x202f00c00708892800540f1311a4040e02200d401203001703000b03070041c03840c003111610740d03da02100d9002c4951040c43d8071881110b140d9154001060001c0c3c1050b0042d0346581c0d145641600724800803414143c590b500c0315460f450412000c1d12581c80300c1d006003016861402c14600f0301c04080c05485850128001d05900d1942060750000d41010030f042c500c003144079801e0068010b096400c88011020f819110002d220383e80100a041034807012640d80140328110300c540c046282c01c911406001d80c00c00b0002480c07a00095020350743c08000b070416240781030306810b1000c090308504038048000c299540942c030443d55070b40c46500c3c030b48030b90341008104c0b1036510041001c40700c4004011805040c1c80c0c00c41c0d41e540c480c00a0350b081c854400a040011415291450b0000500307040048090a07080302280c2e01010340f199046c40101c1d40040c0110307203814104001c8a0107400014840c0c40e10b48801c100000c000303009540154803541c080d1807210805004c0200042405040383c17002c000109030040101085414009c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 234537374 1250 234536124 234536143
    0xf060303070b0c07050303011508131e020315101806050d02120a020d030903120206010e010b0d02040806070309020a0602060601120b120a0311190503070303020c030d02130603110c 79
    0x3140c0d0040e6503600c80e650103c0c0d204a200051507070001100015211101d002c008485030600c0d1900f400d1503948843c620840700c2c001c00068001009015014110034107040355200c1d080c00034068500d40c2050820030503620000f42c030303050136602c0311407400c01514421884442c030a0419110500c46689044000782c0715418448010344a41803031030107246484000c11110a0f0140c2c003a1441d10b1189036414042c1000e0708510040c1e070034030242d04030307034502901c04901c03036069400354494800c15900705400c0d000140c02a00840c0c400301e03420080890125010481c0c14401e1640341c0e000f0a42c61450b205009000c10b0701d80c05201503620510902415030f07000000044014084580001d42500300c0001030001001000041da540c002c4802c1c0400f0305a00010030402645404215020b402140400c40b0920880b850041d0054105000110010f403003038006003121103210044034102030240e0760420480c1ccc803c11130418552071000d010041d19030103010384400d608400c420b207802c055005001546030350880 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 234538624 1250 234537374 234537383
    0x30102120402011b060906020a1d0907050307050d0f0b0a0501050a050a05030a0204050d3905091b0d0902090f060906040b0604080102070804081c0210050c0d1a0103050f06030307 78
    0x700400c0c003000c072611518500c071a4210001b07000d890050b003030110095010f0781041c40064441c2504c848840d02460092140c090054036505280c0e4841600321b500303800141c5801c08101082121911000e254050720110110b0700e800010302007105000c002a1402e564480c5041c807605001c1031400d01d421100341c8458034200d06009a40755580c803001c000034070072900a164403154158909060141c111300b650794145602c44042c80c070b030b03800c1d4085000204801140380148100c0c0c110901c0a400e1402c035580d0044040200c240000c104081c691440d50082d26601c144641e8454003401540340401615400c500c1c8007420050360308216000c504280c3c00103144601541d10b41d0580304c1d003521030300100c174010b050410003151505580c0c035000031950b1081c402d40c11b0500c03c0d4444a03404801c0e08840c6504103d03503030024103400b05c41c480b516010380401001c900b070905041c00f0b4402020300ca0b008500c0c1102041c1c84031100000107100140072100003410300e40c015810442001007a440000031039401c1500f0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 234539874 1250 234538624 234538637
    0x30509011d1e011e0e0c150a140c1b06120412031b1202070f020312040512011b0807031e020309010c03060b0f07080d090803071106090606041e0510080c03010212040201 74
    0x2405c405a150500031102a03400c81203806440d0034150113240548444229540d480180c0020058014228010203641c50103a4101c0c0c03104100d080319190000448140c06805107007002c0005051280403c0c044400346c8402c130400c55070418199051281400c50840d020703000040407540000201040140070008160942c001070560612204000c044403199000b022111040314407542e10102c1d81062003440d00501c8002e8441941000602506a000c03e03090217511f010a1241c0045540d81c80c0138180704180340e40e5415100304078018010501c49803c50f2000940d07039080c0b841c070307403421540480d032214109403800400740070300c082c6801101d154250481246445001904040b00c051040a1130700301d04034500340d075400c10084c104020b58401e044980710710000e00807400519850320703800c4800c1921900a1400240d09180035400340d41070102014001d003240e05044441011250140c441128083d4403040400c51010f040202413002c04007034000358245200290104a54200a440281400741 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 234541124 1250 234539874 234539891
    0x30d020102071703130506090d0f0309110904080d140f0708040c06050a02070b040810050601050301030c151103070302010603021504030803010b090d050703032715030509011d1e011e 80
    0x1025504400e105810600782d55079400c0c23120226139140c025524840108400501014890740603200e580c116a4020201c0b1502d004540d041000c068001070003111090000d01041d030940c282881060705001c110329466490741007001001d0300701540201074008019940b401c2100290441c0703200e404888040c10826226203c0040903801d023a40390b080808481404100002e000b4000a0b00301010039090300304206641700d000c0119000d200900006c2c000140301c040030400a5910103006001080500d042c541509980c0022800d6600400040d80142c1d10703201c0c00d10641c0362034412540b03c00d5040388840d06d000c0c6582d80d00c280901051180002120012645c00c12986500d401c240503654041c1c1611070080e2a49070150000760381000c1d4182d50040514900d400070716251904e030035640404603501c609400032500300e0140c03000600751056075480d600f98000c05c80c040c910800c48451079102410801140600f44480000450314080e651b80c140301e0302c12003904031640c002d5900038411001080145 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 234542374 1250 234541124 234541141
    0x70f0f05010b0d0809040501090c02060705090a0905010e090d1b0204020d14040f0b06060a0909020904060504060803090420030f070212030106200c06190e0604060c02030d020102071703 81
    0x7a0242c01107802000c0308140340108403101c3c0c001c10f2040c0c4121010001ca98a80e042c420455107150080400340c1d21410120722031901410140240303402c01002c100340c2c0360312a140b03082a6802a0300c0012850400030902190000a0003160009481441c00d49120b40c03003c1207141310302c0a0180040d009a03030016450341c0c6c064960300310700b21610000d400a420707814240707085041442820011b907600030046000c104940b03441c2d01241e03014179141d034a02c25140e05102091000350301150030207038007a694140002c0d0645a0703015880040100c080030310b480f208410207200644601321410707010108100444a4001c13801415681c001030700810701d4445035540d8000741d241c44151980021071403404800000c40c42d0303024a0300d81001c01240c2810780a481c10510180e6034808210000758040400d0080c070361211000310040a403c0060716043d030704040743d440491842c0d44640c1240340066013803c650025400c0c00c10400582d964184021450300780c0030b0321284c11411081040d100b144d000000458940d9 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 234543624 1250 234542374 234542381
    0x2011b090b090d0f03080412080618250906030b06072001021906020d0614090708071808010906060f0e011406091e010801090c020c0f0604080d0804031202070f0f0501 73
    0x5540416215041903850601a2070302c1b00441e01220011443c1418100103071049a500740140c40c00381881e860344c60004c01d40018800000c05139803000070380501c041e0044800301641083c50317969031a01c0942c28200180142601d01c501c0c500d03030056004002c94400078130a50725001450301c443d141d8008000c0d80c2c0700101d090104000fa0001d03140716500400c3d0620500e03034000c10070300d03031481400c0040da0341d94002440711b40409081c07070794402c0c20800002c182c40d000e00f0b49680d121006142c1740055065007403060181a8550300840781c03580d5100184c0040003800e1003908040c28003e0314143e1413030705c0d0141080d03003010b0501a00300e550070f02900402b85500c8203030a0741d011340d01c010302611601648242e980c8d1010010340341c46002a403c0c000004050a0030702c96403040c1c02d03a507806820f0301c4903181c092040a4441c801066041502003000003038600c4140031072022402d2950317032402e82c4d04150500401c10000194131403111803040110000081e86108a03414240e40309881a0142240b4102907004 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 234544874 1250 234543624 234543649
    0xc02010909141501031514100305040b070c0318080609070b09061b070b0301140103050a0b100e0a0807060807030b1518041b0509130501050906060309070315060602011b090b09 77
    0x30100c6106e80410101241199944540000e442031001600019000c030152a0b068501400c0030359481c0c08200f2007071040304062140e5000e41030008641e0b000140200303907034449512103225a00010184507040c54148801d0004140b100304641c10f0024070000105035225403280c26910785030200030341d900004240000401000c140403159101d42c0d460392646840003001059500003850000002d00c0d004403445002c000d21400b03072284280450b82c407015541d9440b000c0312103a0204141400152101040210300081c00c50707941d070100507013050000078042d1642d010382a8842d40d820070aa003031405818058410701380801c0c001c0c900400000000c5401016010034400140328203080701032003640c2010084c05800d0307007910700f09001c215468805013140d00078060742d9406605070010640928000c005190406031040c02c3c0d821145c1d9a03074031401d444921050000e02c02c0c1d14ac030420000940c0a22400100c4800da009004081c094840c0041c0074241a02400e1416500030540d0300d150f44414012046 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 234546124 1250 234544874 234544901
    0x409032f0706031a19091a060a03020405010f0c05031c0f0c020d0e120d20030304110a0e040302060c0a110a060f11040e010303050a0e03010c0c0201090914150103 71
    0x2031040d00d03010010040d0a0145018840c4c1220814407015410005841682e0b122020454451141040c104030003801020b0031041c3c107641c1a65401140b661408010110080c0382e8a005030340b5441e02c4000740598084031034200901034500c0f141da01080001c011542e030400b00074541d040d0a0b1071129440c00a040c00d40f058400f5618000515100c00d80004a2001102c2c054540ca440c8803002000c001c6100185121481d254101c6015000903d0140e940804418944201000036602000c1420328640044400b0b0b01c849070a00b00914103410440d0100000e0080226a10303041c2c903058402070342c1c9000181c58400001800108a04078174030460208400441c8a802d03a40c00942508043e0043c0042c0400d03501c4161800d1040106080640200c2c1c0c00c440400f80c000e0a0360b843c50310140c031284c004120340014889442e0364004595000e2250049242c204d40b43c12804074a00e000041c900c0b1000d401181c0c4403441c103052105102c000190a55201c06e546420003419480700340120050700d0200001d50 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 234547374 1250 234546124 234546133
    0xa0b0a110a21020901090e0406060302061204060c0302030f070818160503010f15060e061b030d1a0d0206031905090303011a0301050a090506030a02032a0409032f 71
    0x406154007008400c84880403401c0c1c003044070181a82c6070100d105280e080c80c0070461240341004000610348404d90300900400c0c0c0002e440360f880e004521168000420403920156420800007007144a1041c0105007009160840c00c41c07514a41c584c3c0c14070000744c00b030b031b00b401100f000060700c0380d100ca0600050600582d0035038284c0488002c400070228004e000e010300c00e509102000c1202d9a951240129442c00481240b400740d241940c142c8a0204c200703000c50304602c040007003060b059100c80b030f840301400321007008503510300c4981d000d40c04980c2000ac0c1700301800300c1070100c10025900c0181102d5007507012150642d80b82c03100301c6520124801168020607a03818003081214000300800039504076210301c5a03034038580c005620b00f10313402e200074081c03190701c8501ea142c00e228220740e50380400e504c100081d0440f041d0390519000a854071220300303940c0790301003005440341d55802d8140e502107951100599051201c100c1d2aa1301501c442c42e00e804000104a02a203c0756100c03040c941d04441190421040d40d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 234548624 1250 234547374 234547387
    0x20d05011d06060f151b030a080105040f05010509010612090c0303230301080312191401090e0c060405012609030403060606080f07030e10050c0405030106060507050a0b0a11 76
    0x603066070203120390741e40300c1c014000010307034604142540c255032020007010841140001d04a95a00360001c0341040300140c0c0352089444100b50070070040c0803942c06603c4e184040c1d894a402c00040c0e07100e281003210814180b0b0010042c60b00c41c0541c7d907043da5007034180041801c0c2a00d00c140010404d0000c0645a403110220020030b26800102c8000700b41c60500495609910713100c4c0d118210711013881b565030b540c0d200301301003104d0380b41481805401ca11035802c141948410359810a003039070341061b4040c40e6000e408004000816640c418a031020780210003900c041204d000009480340120302c1600e0511100c00c0d00b10003140642c00b41d0600c01c0030400c2c201c0002e810002c5109603203800034041100c0c0645050fa0100741d490191500a100d01d4043d100c900107a03403034078400c90250501801642e0b503071081d800519100c01d168043c4034030850030003582a490317034600805c041c25254168800c40900004121580200e140460404101a009111401542c5510b1012401480c5032081420000750101e10f0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 234549874 1250 234548624 234548651
    0x1216030b01050306071812080c010c20010c080f0406021209100b0a080d140c12090f04050405070b130b040801090b01050f0d0215090402030702030c0f06070e0d020d0501 74
    0x103850507603205400300c404590b1061416101d01307100e6110941d620740740c3c10b01044010550400c2c004034503c2460040d082a9642c54240d0950b200017031030001090100c40d600301d200481c0910740505482e16030003407000e40e243e148041d1507080701500c031220030b03c0c10070001001d201c1c90703404641400031020445161494041440703030f201c85240e500030300f81ea42452260441454500c1d0300340d041d06c1c00c500140c0034240c2070000c10b031945041080802004007041c4200850401c042c06007507983d40c080000d1030350742c04000b801c001c03100d010248141d100e40e160505101c007090002901109440820072001d9071011260350381106540194403c1007180030000d0040340c150419000036075103510030034002d449641c986003000101102c401d034041c1c020b655446c0031009407030102d4100200031034034100d0030301d80100c000100b002c0c0d071302c09c96000740941c0c00040c0100030b084040010360b031421040b5020344050304202d0001031000c039070382290310312070038102008109540d40c04100200c0c01c2d034404000c21200748682c40f0b = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 234551124 1250 234549874 234549893
    0x7120b15060a110c09041e050a06020408010b010801150915030605060d0c030f05061003110909150109080d0c020d0602090901180605030c09060103020c1903030203040b0603011802121603 82
    0xc3c802c2e1400341d1407655200d0304000060501460748600f840c0440c02094100c0c054040e03d400c0c09541501c62450780d000031176018802440500310300e00c004180021030344000740103d40c061f4400b50b4421103003002d0255040e44044202c059034115003060702c039403030f0711b440c100c0c00340c2100d4102a504c10700000e8156131490030f560108101c0032140d1824000410026400c000311642140c046811548015003540c038903109512102151440314032250400b034075400468240c0a0880c0c8440d0010000144c000aa40e084003100e00100409002442030301c0703042d01c004108100c500d01c000d0103a41504818800c0089a8064850340e01001c0d20914896039220349030031904206180c051159450800c005c107031801d02088404412001400101c0c098440310011002507100c0c0e0b21640050060f084421464000380d0748400103203010355005a140d051502f0080041324003e0942c500c00d03071400000e031507100b25504100c40300381c0c0c044640f05041c05011110500f09141d60315a600040010000882040202070 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 234552374 1250 234551124 234551147
    0x12020c040f140c030703090506010b0a030e0321040609211d0105041806080a0809041d060a050c0f1c0e070308040308070201020a120f0806010207120b15060a 69
    0xd80901a0200d90402041100c40e1070900b4201c060004001803001c082510043d130b000202e600d4005006020340e02e903241000720a8220002c5d4010000d40b800c03078981e05024001d03803056040003461603c074005100300035041500100e4030300142c800e000602408250380c400304110341c21100304800d11040550100d9900140030300140410501d4480c14030300040ca1007000400300301a19041d1800d07007000d003010f9200c580500c0d4503400c15111240861080014003017030740420320030810075480314019801c100076669810b1900518411400c15540d1030440040c1041e00130100110015241e15990742d40702061041e003005031052100090703101c20386400c64402d400c00d012151070400510351204e5000340c90b8103043c4809001b07501d0500c01403012448007070050100074814011646ca08040d03580b4500075851200c02e913404a130000e4291b0181d540c101d084690f00c100c0034800350080d06c1c02d00c0d1011400c101400030141c40d162081000852410940d030030040054001040662104080078000b4050348042c0c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 234553624 1250 234552374 234552379
    0x20603130b090714130e0a0c170105041502180a0821090a0501120609050a06090b01111e1603050f15131410090b06100c0510050702030712020c 63
    0x1000054203400c40420a20140c46010707010442070604107003040740400e204101c640509956521005006c40c0801619010520500217450034501d040d4401003914240c2c507060300d141e4140420880003441034500c80c81010484000141c82c0d008480c42410001c03e02407425412420311003020a0400c0c000482c1001100c400000d500c0203401c3c003c004215003e140b0781103400502034034003405650300070b10b00c8940402d042100015034903610241502940c0c03055804000c1140e41d80000e020108003070059095120082c20240842005d0007015561010b21000442002e0030300d0b42503280041044c0000444540709050071101603444c1e0419946414072100d10f1034181c810100302454603030781013040601c40da0084000f25014038407520f0700c0c50300700b01092502da0b103400743e81e400301000b15003446101c000b64080c1d004413101d03113040e0041c01241102250103e0a001d01403c881c40007510001d0300e02c1c1c182801400208031522910390503460760081010080c00710581148803110b6990000f103c02078020304 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 234554874 1250 234553624 234553643
    0x603020309100e2d010c051306030203060d020f06070c09020901020f0d0f0c030314130201020d140f0c07080604121803020123090402120f0606040e0f0c0702060313 72
    0x3000d20070100c48007002c0d0f05900342c001e800654803070400d00c1c8500d048060f08240340320741d80d400030030a41d01311010031b00d588011034800318404a50b400c000328480d01502070382c1021840d42c1000c00008501154426009200e41e41400070030390581c5981059460307640e40300404140711a100d01180010350001075590740144038088580e03085143c002802c201000a40d2104c12054004c500704540303240340751806070305041d111000414100d268840c1148500300301c03015030032048194400241010204803a010801c0f800c24074561806e8451021030b04081410a00c860390740715000c0380355080c60b10b00d0b8042e03586405804100020301c000c6050b219409101c0d50750b5034452094900c552554002c0b28003019000540d00841c910070204489402c3c01002d008000d06401d24124030002801e80c0d010704283c40351591410240714094601d0440316800c50030131070f04542070031304280260782c5000c001400c9030703442d2940b1000700f882c10900400b25000b030303034024218640d2072605030120102100d21100450f0f41000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 234556124 1250 234554874 234554893
    0xf0f10080a0506060f070311190b07091e0b070c09020703080f0a0225170a110c03010207031710051e031b010219030905090f0609070c0206160f0c0603020309 69
    0x3413101c100d903030390086410403e0911203ea2001c8a011010342c08030361061113020003001d00b09810042000781c00c4e03ca822404042d141c4040000c010103d01e5000a211003d068421818041040c0010058451009600e610b480003410003940c50689540845001071001910701c0600d0b502610040c441e03d0b0b10aa0b0b008580c40300c920800403446801d2900c07a110450500c0021039202800c4068200ea002d000c0c1c000010b04241c882940c0395002900110104000215a4100240902810005c6c0320110000c500b08441a2806805401948080302c41c0301a1800014480c84102d044400988005004220200c920007440e0041225402d1514424070401590100301c404640e00c02200d26030690252010031030044001c400c541e0294011800e100b800c902c08941616030403c041c0c89503485203444074036400c2c5001404807100d070181118003002010f003180b00140c2c0300d40c02216924505480c0502a1403410f003800003040f090707100010540400711000186060745900914003400c80d4400340d440d1000c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 234557374 1250 234556124 234556129
    0x2031609080a03030f0e060a02030a0b030a0807030513080d030903080105100c081c091104050603120301181b08040b07030e150603150403020f160308090f0f10080a0506 74
    0x40d168841c1c89860b90203805078100013442508450341c0303e00c0c40300010822500e0f646000e400c0c641e04540000d11a6804030801c24069181e0007100000c036816000350010350400d8039028520300c14100f0140501c0000502011922641001c040081000006a400c843d41050004018001607401030b000544002c001217054030700442a9004000985c44842c0c0c144003d0340d584d14190022040c5480028981e0421900c00c0454001c0c1c0c203500b842404681d50f196804010031013200e40280450f400780d801040d0210400903007000f180d0548840c0c5200394145914090214040c1c915117046009078075401192a00494100502c0f6000e1751054004040c1030307840d158110112003a000d8105410b520101c17010885d00c031005001a0026000b0303050710300032411102182e2503c001070764200c00503400307200c590703c82031414414030149840c0609440d043d1842e640390b00c0d03d94000e80400074826403140603049001c0d84c4035801d810b10307120040c0814420300d011060241c0344150459100210300d0901001440c0da1 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 234558624 1250 234557374 234557387
    0x15070308071106060112150f03050607050f07061814150105041104060c0f0204050c0c071a04060806030c0a14240a081e0a09020f04090c060f1e03020316 67
    0x2480782400402403540c13000011140581182800a0001d5689940d0984000360307413008805070215424038903480b0f213185042c51038031800070700c40e00030404107002102001e044001110f00c0550440c001158802400b40a00381043e80c2e1100140002c400c02d400d02c500d44008075404c07110344100c6a0446290703a0780c1c402e00059482d524000301d00700800700024441c80b801a041404410302902c078851480100e1343c04541203400c01d0303851086000005c80c01d801103080801c0100003400303804001e416102c12000740c551003070080c0d0161070140010440080c5e143e4804014202c010480202012441561065100445502c0d8913085020703203012442021200e01055003d029440145041451300d8000c1c0c1c02120400c101400544a1241e02d860070b01103a55034881030390242500c28030025003400b4610400c4012261003407101d000c2c41c20104d482e03010401c40090392085900340e04000c500c0502e00d400407a104403001c0b1001030301f01c1c40f40000c800d1040c1c0c980d014600c6107040800307a0803008a0b00c101540d00 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 234559874 1250 234558624 234558647
    0x20f01060b0306060c0f030c0f1006050109030213020d1109010906050f0f0c1e0105070f0305040b060f040209030106090c11031e071104091b1413020702010e1507030807 74
    0x70a400c001140d544c1c1008801890039100c1e8100380c50086500a4620381564440d50f80e103481544026000130b01c05009000ba90b4803203000172410000306240070006001060644406171207801c0c0d040d000b1140d514107030111005040031100411540f61098004042900000b401c2800150944808500d6038054400c4510080f10308007203d04080101140401d9035102940c0c44e491805210b0746003d54024402901c1144100c01d800032805140080d401010b1f214180c0c0c00300100340c2050148408600c01204840c0c00110999550340c0e80500d03440400c1c041d20413501d01d250550f2170110700041022a5034044182000c29075641c4806c502150411031350303402010322045611612902c0108106840d500610f00503110300482036030b506003c4000740803550881c02c19100c501081c003080350f51016441802d0302408e44450724880a015580c08202001956104101019030004540003562b0142d411003100c48002030041c0c0001401c8040d00141d500301181c00c5020540c61401319050500941c005c440 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 234561124 1250 234559874 234559889
    0x2071e0b0f1b07020d0c15050d0c0903031b06110d050105040609050c0406110a02040207060b0922110a080f071401050909060105030a0603080c1605061e0d0f06090c020f0106 76
    0x3c0240781e40070010714408000307044070610340803240040c030070b08401c0022101c80e0041c0c490300c2d2101d58000a030801c0d20036810b60700b07040028810041c800290024803e041a82400c10880100601450150010225042c1d66111004041030704040701c0c00c2600014140c0d50103035824410b583d0341d409000145c1e1801c1c1c949081d424024402804500d200364008007070071f02200200d4612218980110741242c2c40b210090380e01d107880d1504441c260034138060030b60308201c121190b42c85c1c1c203145000d240f078841901000206003810041655507103a5a0900403005056020241c891030343e000d004682e0381d1030080c440c0b5200a036900d48051031540c0201c0540ea80c410010b0000507595030f9000044030550300003041c500040e65a40300100104070090701800030604100010405401310f44038034402c021081d8841403095904104125207404154010101000c4400c0b006444110202e60300002d0f100c203a0500f0384480c9811000240500d090b00048d14009444d000e550044040c440c0c03203426524607004644 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 234562374 1250 234561124 234561127
    0xa080414010603020d080702010e0d05030f0f0705120a1b020609100c0f030e0109090e150603120c0c0906030c0307150c1b0e0702060702060103020402071e0b0f1b 71
    0x4000c64004610000841110000040c00c02c0e107960001c1e0b1280d00c80f0400b55120040480d19804550304101c0c0d1783c011841c2241e03c850b4070380040c0c2e111a601e200780c1c032504122810129440051219074025186940c1d44103058805411104411082c06d410020180700051940c0500e00040c4d1241d2020001c5141c020700342601c2c160100c01884501003515140e0010018481070741004210185501807030035119554841040c8504000149078011980019190b940b610354814844200003500080d601011007000d00299200340000c0d0030246402800030320004000380b800c04000d4040703100360142400700c3e402c44031600d4002c1031655410b40034407540d4055011070800d014071508425911540c03800381c541640441d4182e59000703003103050409507814003070800409200aa180300e010039401042c5100030003a0380b801410095955130180b20180c00385d540044c01005102c0d100108990042a2080d07002803e00d0f81d01d400c081025084800f0021400300c8404034030340043d5404050100341d15810001d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 234563624 1250 234562374 234562381
    0x803070605060109030f050c01021c08010306050405190605061507050613080d020d060e1509070c1a01080c0f0910260616030e0c0105040b033303120a08 67
    0x190080002400b8141403051954001001508504045801a200c0d0015109803110300001910b0160283e40c02c4890105070b02c108900d0300d9210103400d04580d001074000c1f07503940b21350030524182240c036004981c00035402c132841c10034483d81350080c0d40a200203407548040c02071402c40d66295030103902002062074202d1008035141c5210f0760305c0c1e44282401048440c2ca01010f92a00d4800c0341d2107103c40ea07d085031030f01070030400d0b241d0314548240d202d40d0710780d016040010540009140e1040084c621010300810134000b0f4103000616103000d42c8014541d141c240300d075840300a220780d200c9081c03076514403c40502481203110b042030301070716005081107c0a070a00c50305100b0a1601da69142e141c0340c002e02c80403090100100c030200030a9000b10301311800c1d05420090040300405035070071140a042d840d842240fa00d05107983c80301c112011690751b142d95503242d841e11080e20045811456449410340c1d09203c007000d0110000c00c140354240012421070f80ea111142178001c959000d21003608020500b0071001 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 234564874 1250 234563624 234563633
    0x1b0607060c021c030603030324060c030e040203040317091f1e0f0c11010b13050402010309020d050708010c08010b1603050c070306051501030b0d08160b0a0504061104080307 76
    0x1051141d1468010b44420310203030751000b0310f60b12030f600c0300200280e19000100f003819050701c11b212103c10614913040000700c1034079010403c130b6080d00c00e81040005c0350700000c0906125095041081d04010401c0d507881c00c00d4103000300107913902d04050020701c1c6285c000c00c2205000250440039101c060314980e581842003602c035401030810040410003150780859107000700c4a10310500301da0524070200041c3c1c502183c0001081a030cc640a110701981c07424041d0440f5a0f80e941c01464142c80300383c408126540c071440124060a040301000350000019481c102c04c005d40403c031541039130030a4008001c1307004107030b00884016100388600201000c040002041048070120255a0305000c0d003005c0b858185160319403481c0004503030003650346540d940c041c031141c03101091900c804000c007407030b0511202b0305400014140c40b200a50007000a00002203000d80356100c14a0f080c0d0303454001882420a2411050300e40c007400c02240c00301d90043c0b4100080d481c0c087c21806a42c1904c0406009604050450742c4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 234566124 1250 234564874 234564881
    0x6140301020c071e0807080d03050c070b0402060703030e2a0414060d170a0302070c0b0a0509010e210102072a060804030e090703020c060105150d0911030d09081b060706 74
    0x803502c85144184c0110ba0000204421070080185000034012204e04190060032a600680f840c0b00c148410014403002c505013680b0144c1203501121079136600c01007490150010b01035580708854030300980703030803158002c0f08100d40e0074800202c250100545442b241000111050340003406001030404010178817500300440130903103140c840c82e003912800d41da1000101150300146c5001000a8000807048c003009141d00b0400f00400c0500a8103042111001000d00580103840c0320300e04102c403101c0001c42d1580e902940c06400d1104103102d08480c00d00c070386d245010f507024140641d140c00c5155561924049582090100407008a00e804d0071070b82807000495021a001e001030b000c0003840b455841950351001d00039805400d075a103006948019000d8180d0920005074001071060140304100d0030307515400710403a42c00046142001900300142d1030300855440300c95a080740c152046540f0b2004541d0030058040503035084008940300c0718050f08000e071280e006000600c1d0451000e100e0b05000030041e40 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 234567374 1250 234566124 234566159
    0x70b07090f0b0c2b121406240301090b01091505040b0304030e04230f0903160816030905030708010b10080402010c02030a1539180906140301020c07 65
    0x505035401e074104420002c031003240c040e04090510301c403640c0c04d08901c1d400c0000c2000710416002e05100d030001c11120300b01c1c007150040078240540074121040c105190501200f0700038040ca05030254607035854500480040c050400310314003084a112002c11804188250201a90050758075180ba0a0605403c500d1981000d0400c82c1801044003034030a8a64803030241e046000c2e807040d1b075650b10b61440391036802c0ca00400b85c1449584907810061205011011003240c2c80c40d4503500e1605030003044c900c0c1c6107901d4410141c0c191244107a510804c2c1c209640030b049102211400c070300721600a5180c0c0085422a140c03484100c1e80541d4082880100c43c3c05070528a5100740141081884040550086401e14100d0b6000303d6102c18204580b85810000d44549104044424004288102c42c00e06100f0f200886061003082080441078003401c7e80d01c6540d0980c001038004c175128108596880103540581480c0c0196a88000500c00050381d90070140309a4060501c6107004021503441e1211140300ca44020 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 234568624 1250 234567374 234567397
    0x3010f1116021804030c0b0c1603050306011101050a06030302010e0303100320060304060f15180509010e0706030905010621020d1e080301030b0c03040c090c0912030203070b07090f0b 80
    0x143c907055510410141075202e0360180d140c039075041c6028034018440341030051603500e586105000d003100d81c09544c0d205d00981a49414403d649480d07441c0140c640d0200802403c00079801c1ca0200451078685401ca00c1c21a482a002802001040f602c8245c5030302003100c1e0301d40d41c8050840100086500c21181a0300348814910600000d8512000700e040c40d442160291074954030740b802d550b2207440520554041a16000051030118208200502c000d2802600c480c000c513141d101050360202e080d0700c91403041d4041002c540200d13960712400341c003030b140714081502d280d460321a0004814400f40c81c0307508051107002c8203000c0c0f69440c0e801c0080c01e03081f8a03001d840511404142c1e40040c400c95814604031030156003400c2d2a90315600c5c01108200700100401c1d91082c003402803000086652080b801036a0020402040d9101c0f02102125440700070780c85071400780c02c403a40f100c042c960040300501200380a0320a0000588c0c40c00401d1f203e10803a80b080051241c80c0100401410001c44090403500e40c04 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 234569874 1250 234568624 234568639
    0xc030c070b04030c17040503031209160305070609081507030911031b120102090609060c010b101115040203030405123423120a0f060b03010f111602 65
    0x80e40301c458032403100300c400300c0204607610b8004090068980141d1031581060007414039090070000420303200d0181e40f0304c1c2c200d210b01c0c0b540801c0c0c5242c42801410000720480550001c080c2e500c1c14655a5070000e44202400302e40e20200c003142901c2c0100700c80480f050a6891000c107a110784030304030010328205405880c24042e0300d20a1402d5a41848000555007044801040d5105040c0c10440c61a414131101c200c280e00c10884101d50f921554143c0314980b2049510f25111402200790034003400341e50084540c0918070031206500c1942100c28201210211011501c0c104560107030040720800695000c4c1d496441032000b0003031886c0c0a50f10501d9000201e040d113020389040d400f158006070303e8458075500000040702490ba4103014400030401800203000f188000e020030803107024827040d0034560301d005190b1001c54001d021030820645150f103500200b042070303000150500b54001d003070407000c0e107109500b8039012080807056400f540101080e114003162828820716500b54030506140c0049030031210 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 234571124 1250 234569874 234569887
    0x408010c03060e13110913120e10020304030b040809130c0c0605090f060109020d0e1204150807090317040308030f0919170901140706020406030f060b03060d02010e0d050a020a05010203120c030c 85
    0x1220580d804c84131a0903161120f80030500c274104070014103518002e404543c4180010004035a0790300070320f500a600075040b85d5580f0140000314030f21030642c50a07040094200359414220591040090714868007070b010800003500d94100b0702d078980c4440c9100c02255480f1350014001283c1640c014080d0750f245480000f10110342038507039070915030110707007210b1012004901000320b44242e0303075883c1c10030300c051902d50b405180a00001c0c1c1006824000a091b002c100c3c0310940c00501624100c401035a0801a055180c2c41e0942d120099200100c034400000e0198000a80341035448103401d07820158000d060800411041411030440c0d008000528100203a403144000003445136001004154040c1402503030322410244c001c2d0a46034104907084203985001010005403400b401902d811040c1103909030540c52240c0012104146004070042c0e0011000c5800c03810028001007000790103109072024582c850b07a40e001640c40c2d0095a44d0404980e0040d0300064040e038540004503071102d28200701906090 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 234572374 1250 234571124 234571133
    0x71502160f060c0806030706031505210f1f0207020f090123032a04060e1f23100507050a2f0109050f060408010c03060e13110913 57
    0x58005094078000d40060000003804424095491000c0d1942851110342c104000032035522110b500c200410035503070f003c0b41240300c03004c010391800603e0700400044010020204086020b001444251000d03c03c2e0740c82c503083e524012541145682c050b40749201c45d001c02e00304550281d4807113038040b6030000f84c00b08508459619511118081c21614903280178801c1a003440e0640e8400c40321903a4465400101902c508000d0300c248a901581054800c0a191042d140440c0c09048a81c000c18051146641084800d0207042c0c2182940441c48055240c46965440300034002d482e202d00b002c0481081340c5d032510150a141c2c0b40d40312030545925101e0f02c0c0000e241c80c3c85040031f1003008121000d42ca0b1a403441c050415030a81d8200602940d901070444440140028101c6403a0f403181500640010102c1c1945036104015a001080c5030002030000c01004480103005004c1e9015060011040343c020038800c076203a1000400c0c0380d9000c100341d91308901c00001c1000c1908e0007401c0c4ad14941006104c82c0005 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 234573624 1250 234572374 234572407
    0x2004060b0403080903061806042a2405031b030c040b130501030506030c090f0601050418020405040513080711060904020c0708070501020a0b061003020405180a0f05040503071502 78
    0x1140a6490f1540b80c50300901090b040050181000d40c140d40e088101c482501400b055454001d0b5100c0700b0b20314411040d990381081301589440090100e0030300c05002450303030340101c819841890300b10400c50340406034040c191203502064a180da0f18441000f04d2210a0707000310010740e0024940c90340c060501e95145900c5a803503000201ca00c40c40407440000300000d5805000e1b20360000320440282c1903056070400031410b80d003001004031441c1181c0c00b022034940d03409801120045c05801c0d04048004900c0400030010f54401d10509018600c0e200c0010b80754015450034121031980002820724124081d01c48510340c480b4400c040b0740c480c030204800724480d41c642c802171000e03c0480300508515480c0248403410031119600150654016600e1400095122220a60320060443c0c14241480c00a0b100300d00a000340d40042e50444c90b000165048c1d4455003074080e128041c0174000744800020741603900d059400541d8000c00ca58410f00c000800a030b4807906016503100270310001810015503900780103070b4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 234574874 1250 234573624 234573629
    0x20a0303090317070308151212030412030c02070e040606090e16080d050a140d02032701090b010e041401060b1809070f0f0201090b0c04050112092004060b04 69
    0x7107541690100100006a003603441d0300c070150f01c0801c0c1410090748024003120401041980041d51a000c04522995281c440c0906030800e030003101e020000c80682c51b0141d070301c01d450980d115668002c00d080624428018446140340315400703004120f2800320803100d43e201c00381040342e41c1500c0724000309a960044c40340a100080a200500c50000c40140c007a28040035a00414095004824988550740e0420116424061103107010311050045420070702071802110021000503000109000a045003a030002c0c18549485148002e00100e83c140b050807240e40e00300050580e00d01c0001004100d2510703000c1a0300600174200c0710b65815a103000b20303003180e007030342c00000d6034140100d0080c5440389150821044880d0540e01d400c03c5041c43d00c0050041016100c00701d0400400001820003d8404e4002c01ea42503403150710403074941864040820030303800c1405001d0020b501d172495034174429032600504807010b4005000442144414416100d61140308203040e801130303100c80340050b0b142141c0c0b009000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 234576124 1250 234574874 234574877
    0x907050105070f150f140609040c050609040b03010e0a0311030301050907051630030504051903050d02120103021201090314131715010e01081f0b09070806010201060b040b0d1107020a0303 82
    0x3961464024400c00046c006880e040c05030340c0d071030100000603d00f621603000b640c10440f16551951400c3d40001c01a0909151480d015402d00e006001c80c440d00140c108000c900c251505200c180c88081050b65a0200f4815103a0107400c46022070308640c014401004501c500c0210041161055110142c46030f10340211501540c06030014003940700100c0341044144071285c0307070a12407402d1946515540e20003103110703121610390303040c400b1042502074000c40e110720081d442c003035441e0840c855070306800c0f000c01d2000b0fa015011104048900a0061140c40f04207541525180c0c450092040a041260003003a404d54258039401c0020450b40f4000500748600705444000f00106e41c006118081d03010410f91004940407a0100140030394074001c40c212900703c044485919600c0240145580640030504615400800c02c02c14008903d603c50701701440b84500703070003e101260340d0b0741c01543d07540308034458041441c000b1301c240c2c0003e0090790021460618208985ca08080254000616401c1e145d8070880 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 234577374 1250 234576124 234576131
    0xd020702030d170f072d0f0903020604030b10050a03060507090501080c0304061a18180a0510020d09020a030308090c09010815180f030712050a090303050d0e0d0c06050907050105070f150f 82
    0x81b0710760740013601040701e991502c0e200c5d0f200c5140d68042441d0303001c2c0f40002048903102000003101490300020a500800d0300030b01c0c001c03046a49081100081c00141c0d80705000030402c0a0100c1c00b54051401c80b030161200040e0280741d0381c3c1d00d4480750001d04043e40c1800445450803021059951041d6440140003d103441d034540c5810220000c1000942002c0121a203400c20741203c00807030404582c600d00c0160955015a440f907164410000070710180c0030080d481000150003206040e4000912031007801014111103840c2d841008125805130244500307007140c0d101c0c541011070b4084694030302e5000700185034100c0c40c002607070b503c0a0520b101d61400f0041035002141c01024070a044060b5004205c0604040785401d0540f000107020030010f00002c1c0510500141c9a2060703145a406220040c01010580c0e4004603400001011007500c01d03010794606061002054041802050000c12564142c461601e0043c10740d495011403490b4680170380d070040b100c0441164551050040c01e00d4040d1924000 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 234578624 1250 234577374 234577457
    0xf0f0d09051c03080c0c0109060f240501030e190f050d05121803070204090b060f03121b03040f0b1c0b09010504110c01020d020702030d170f07 63
    0x40801006a010a00c01d55080032010420031004466002c10340c3c040c40c0007242a603a465011080b84203880c5c203240c140d0f2900c900d440900001e82e110058100107100107201403110741d81c069100750b042500114441d8000d4004124941c040c1c3d10481b0003040b401c003640c0c1c0ba0510f41d104030308859801e800c00c0c2c03950804c0848483c01c00070140003c3c861900c1504180b0b0170302c244054000000340000341888154042481d44d07030a45807040080c0c82c10107600a00621160800c0e2503c1e00d00a0783c29103045000da544500010114030340444d00d0368500041c82c0100f801c00b661003c00000026a00f047c1d120340d0b02003003102060500441c101d04015040f00e01d101c594958207003a412010781c440c0c24010102c0b918100d038901c190399503103007034504584044501150fa200d6a0302072100f039100b40e803160a050340c4002607001d80c1c0d41c107a8010701840e0740203c050380d044104640060b1040f161a14030b074004581e440001030301c1004500e000d0340d000303006481c001d1055501c442c0e0a01246021a0301c05c0388128a44441c0c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 234579874 1250 234578624 234578627
    0x240f040e0102070317070923040f060e06010309050c040504020402040b0705030a080f0108191410060906051801090f060e01090e0c100906030207050f0a0f03080618011202030f0f0d 79
    0x804090712166500e600b49446d04000740007140c98003c1c9029401f91a01020101e2003201240040700e000500c00c100700820300d80d0100c0208907901c43d554296142c0400200e4942c017910800203503030341041c05064070385082c004120003003000a000700c2e442a401c0c032010921805440142400c24841ca0065946820358440034050510080500340f454209000500c04041c0c0403a02030303c0c202c11460001010022494040c440080030380c0100e0b0303288a011180c4010b0082a0888070466058040400031a503c2d0805d0001042107001003694183d003840041001d96201e47c8004604918500c0004483d500ca444140c1203050aa0215505584a4a5481c030940003407003104015501110081e2031022281c801408544071846a02c2c241070780403c1c000103002003880020798000706042030341d408454030318004000d201c151400364001104440001c80d00e0511041c0300308100d03c00c02d0912696807074602e0061207506082c0f0300301d0b054095040d07401080d00040101700c2001d042c2201521080c10403040 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 234581124 1250 234579874 234579887
    0x1303180b0f04030614040807030c03020f0f16080601151803020d030c02132a0c0c030323030106021c0c02040603150f090b0609060a0e04080a08010806240f040e01020703 74
    0x5c1c8114007419001030000296000702100d15556041c101540d5603659820240e040c48101225408035000d4080000392032840800d0005407995a807096003042510340701090780d126424007800d07076550b01913580c4548041c0107040f40e045031144d94441c00721003a22a03010603d21000300c10b088000c5940c402d400400c52030503046190304005a81001c1010460003002c5501d144c41058045ca54040c000303030039690081c400c5c0f81400320584c2101e815820f9039500e05c0c0051103209444228555009610882030340c0400ca002100e040350307004c0e402041403904603ca0404100c2c40d80046106200840300814010b8541d03029480c02540560310701101c0c0003404078028155102e10082500192808103c4d00000700d04400e91a0000b40507602144180c4e10800410240c0c80150050800304000034100010055260014012040f855030340c0512642d07280309160350350100707842c44c4036604048258083d544050f042d4003245800b000f4914940f5a14840100c0c00300c0b0705440840c80941d40026031302e001e040c3c0200 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 234582374 1250 234581124 234581141
    0x24020405040612020d170702040524190b030c04091a03070506070803011e08070806091014040213060b07030917070e0a0b04020d0f090201171303180b0f040306 70
    0x310f948a03007004d500050120f030f1002c00040c03171030000e0b13125010010050000d4400c4a0ba002d0420005820075905d11528100c801e451085100c02803100e4006070304220180d04444040100c4045100d801d1000c1880c1c0d581008040081540c414000001d4a030580d000d51111a03d000800c0f02c2c200780254203060500c0740319041680202000c00c00c40d40000d051b00c0890f41151210240008403007190100c01140e600320b58040392103881180404160100080f032418003941303c6204654040c4d018031124401c3d00d0f840301e80b0a01000b014070010b40582451350800c52901d0303910320005281c9032034205403032003504041800c2e00086c2c40c511052102d590f0300d100c60a414501c0e0380051142070725001c401d0215140040c4110340c1c3c240c45079046000f644036a010f6862810940ca000d100040d150b0b0006d600500c0800811390000d105589040440500594502e0180b0303c5204e1220444125407001d858200290f61a20715910f0360b6440010010131081c060003040040f078040d1540e031899801c1c1003054a0200 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 234583624 1250 234582374 234582389
    0x130b0901062307080c0303010b0318070509040f0f02040e100608031602210307060b1f05030a0e0c0303030a061a0a0c030e010216090b0307090b0f0904240204050406 72
    0x201c0b100c403001491000480030b802c0400300036603c0d600c1c0e15241070240603c0034804400d100200012809007900005588200301100f4088002100d15000907980c02c0e085c4a420b40007680c08000c1000701d0f4401c102190480c4c000c1c00395100101481c1d0104044031140c03011080540c2288400404455550140500030103002c2d000b1801c1071203803103685c2c0a02101c910024070507406d898181e40451650680302c0c114401c52810342e61215020306104d40505480c1c9a440e1141c0c40d4030000c40f0304041d80811708071085115541d42811a44e49050740c034020410b4110004151091803252a642c1c0d404000031440346240741d0303000c00e00134074090000c1c00303101d2010029040002c003030060070b10099100441050098040ca446094540c188006074145400f28205501c0402321082c04284e5071881d03048809890300540465641e1036545500000300d5403880c841580c094000180e021140c0744c00c2d002d8035041800b03140c0e1100311240212000d5070b68000202c0081c840b85c2c021a0810040c80d2034412080100000d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 234584874 1250 234583624 234583637
    0xc1005180627070905070918050906190b150c071505090603190c0e030c0105090609060d0b06030a090c06050901080a050c040801151404060b03040b04060b130b090106 73
    0x610214002c02100d100c400c80c1c1c0502486800e03518110800048000f000005810042410711400c01029284079006203c541c960203400604803a800c1d1091174480c80c0640701805a60b202ca90502c09240b40c884400c503801c584440700d0620a9031001c441c6001c4141c6016500e0381c5884c00c0000c581000202c2e031281c3d502c20183d005101c90541c100d030883e4029041180d81075500d41d58000c56183c1441c1d04110f840314a480c200d264030441340c0000c4403201c0c0300c60031801c507030160940400440e4a841030400c10342c0c114104ac401000e0508200016140760f01081380080340b504995404605150001c0700e05040080c2c0300c03941e03842400500f4044101600c0381e86010ba01d000303c401d0010745070620141070000c4980c3e881c000104a940060180d4024002620091240441c8414441003070380ba240100c42a1240035003c4c5580c52425100e0b01c2c080b07910141203d421652140c451100841001b4802c0d50a291501043c403059902c10380840c1c2021003283c80080d8854100c0c041c0250954141c002100740180d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 234586124 1250 234584874 234584881
    0x504060612020307090f03030c021e0d0807020607050102030408041409070f270906091812260a050109180308180a08030103050d020d030207020d11060c10051806 71
    0x24088078000400385225000750f0389072a804402c0701d8140541d40030340152100c01c1000301c02c05601581c484141e50007120398100500a14182c060920582080283e00c0788030340c4e0340d64002446d008068003000740020121030400d5143d49034203003603034800c40e021038441000040501010300003c500e6042a83c2c03d87d40b14a840c43c010f4800b40c03044403101c5881c402d00c945c80c840b49a4950080907828034107c3c10000c80b2241d00e41da0036031100500264054500c80c1424903003d2a520050744c01c603103003902e42103c003449054465130015101c0f00c01c05001444901c0c0300c910745440d0320110005c141d00034000041c1c002015890032005004965030f88880c07002c080015038010010a0f03000d2580c54100030403005000c1ca900740540341d980740003011840141190340110001051040100b1002c0c0071001c00c1c1c007942c4c0d005e031528604404038429503400a610900c1340074502c02044008126011004003d01041e00c0e1004520b0034600d8010800c013001080768840042081c641c80002d203890078105d03c140180070350304 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 234587374 1250 234586124 234586127
    0x81501030206181908030307110105040f0201210219141c0b0d0209041203060b0c0a03030209040b12070503010c0315090203060105070b1006082409060102010f020d0b090105040606 79
    0x41508001c0d5000389421a10741904e90380c01c0031048000d98149008030b00341c1c1e6140841d42d01c0307400031681603021401030500b8610f440018003c8610030341c0c6c454aa410252195401951800c40c004002106010741c40b01540300c5424603c028800e81340c042800d007000e8180c01d035004084500101e0700f095550320500c19003501c44010314140030050140d840114561502e0004500840347c0340d140a940140c0c210144020f10008a5541510204036a000d2113841c0d00c503442c80340b40f44941d0030000e01980c0071a10030400319200c3da008e0029145d0080012420121200000c1c660907080d90429086811803a82000799180174800c284400c1c1c114201840341040040d00810f42515620501150a40000000308940e100d8000c0701c000b650720021250490524149a03113900130b01e801510046071941010844100503078109400300802200c100014607592414848082c102518540c10341d034803032500708002c00440c00a4940d403042100e00141752240101041066a0180c0c030107401540360030230600100b07 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 234588624 1250 234587374 234587377
    0x90212041113150302090105010801030314090a030c0602011a0913020118091104061103030c1912021801030b040e0a021c0b04080705010b1008011206060b03070801081501030206 78
    0x640c0008401048150a101041d00c103102e100e40000c0c040c0c50b002030310f803205400d40c06403070981c2c1c000c2d5850b2004d030781c9500041d00c1001c001e0001802150000380700c0070030101040014224404044c20100c2031565171356414038030111940010015075100c115160f45a8049001e200742880101e0314241a41401a465a10210408030190410080100d0030a40841c003154110080000c8501000740340c90080103196550041e01402d40001d40c91180040d11010000942e80141041c0c06654a842103401c00140900301000c201700034040500b910042c42c7e0746c640301816900480036200403a6041d448001021035810301c1210f482246020103262016400180407800300c0e80c1540c00c004c1a40c42c507201c1100904080700010304100d0250104420070080ca0040d261061150000b40034203808001000300c0e07003030901300036000110000010040000c0c80303e03014001d140210000203034592103003200d02065200300c50b040c01250400004004690007040480c1c1030030b00e135005400d119415540090040d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 234589874 1250 234588624 234588631
    0xf0e040912050c15040c0f0e061819110406031d0604060e0f010204080c0f06070210030203070e0d0b06010e090906060409021f02010f0e01090302031e070b0f0105040501090212 77
    0x40100c04103c140c164902000118560748410326010210702d00343c0f03056102520180209aa442500f2200160802c0c91701006405010024413045036042c03100051001b044000b000c1c080100c41d01031070301c2c0340041030b442904549444048150343d10b90500801805484168030000c01d02c15000009044054001c500399402590062000c900002c00b1052039240400508400e00305500c00180003030001000521000da810341520160005501082005580d0040c0c12020707400c442001c0000c54100e20a0b0300640d402a5103052540c84440d207000030a41402082c0402c44215001e401800115a0081200300e950242201d525400f49800c3c83c00795142d0704042d086a019031b48a0307907050210350758410103030510200c0300e06c08940b10007000c200a010704450105603221900c0c101d040e184009040c045c0304103844d09600114a00f08000c0c0c004031504402e8a00703850440000e00152000a2142d4038040c0504645c125550141d414082000221801a4002d1001c94030401001e03081905498001c2d50 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 234591124 1250 234589874 234589877
    0x90b030f100e0703050d0503160906021b0102160803040f0509040f06150509070f0806150405191a040303030c02030301030b16030f020c0703050f012304080405030d0f0e040912 77
    0x90b42100c0328074452801116800c002c11502800a804514030b5010024610643d404603920301c514444580543c0c0e00b00c568010540107800150b8840b80301613210070f0342031412038180b0490301a0410840801e2900c1140e42205035550000078041100c0c20340c402c110b001800c0221745851300c42c101030740c0d11900324200c070034020132694551035200002c40c101c4034644010310001e002841c02e468040d10003050704150b0a0300c6808104404046003650400b445850a100407560243c2d103454104010402c242d94003083d045085030a030704011514004001d18001d0b40340c070130f0040d141c81c0e130b045140c0503007a180218544011507109200400216105042e0260010074800c00e080c40003034414012005003002100d8042d6050000a04001141c2c0008515007101d000b04162150020000c581030b007641e0f068040c3e81c403010080c0c1c40e447c521394a41d940280c0c1051040786018500b5030350351f001c64140154601c068012a14213a421a155a00510070040c000342c2103a080150403215a61000d07403c1b1810151030 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 234592374 1250 234591124 234591131
    0x106050d0215040306021207110d020706050f04170a051504050703030311090d030905030d03051506031e0a050604050c0a080705031012080a030606080910020702040b1306090b030f10 80
    0x400d020301d0b01103802a40d041102595214910050701102c043c007510b20710000303040798054103d5a880441c3e40d81a900385680504011860301d00101c40c2e5030000703e15240410b504100002d0150800d80016264400c02c9000d4040c030303840c3d0304140b4148006091b40350240101380b400c1000003800400c0401c00e407903050400150550340c0c201201d50b20b01030400341340e800c090881101000c1c1a04140b01d40c080380e104504880c080340d40424100c040c2c1d001990f024100e035090600101e20343c600072024540c0846200200302e44032098180d03800034083d0585868501542c0e5070140022411b29004807580460510304062805001d200000c0c4200c0340200342108201011000c9044041102d80c00001002c403409103a08400540c241007015030701840d030712408a4641503000130442c0c06680c0032840b40300080041c007540f14202281001035400084201e912039602d8101c10203030b5541c0500405210f045140005405003802d403180200c43c00145c2481c481d5001c03030645512500002003454000315041c0300030 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 234593624 1250 234592374 234592399
    0x1303090501020d020703063305030d0c02010207230a090203060f0d1a07030e0a05030d150f1809080a05031005150906071506080a1e120c0309150509040b030106050d02 73
    0x910000d408c03c0340002148060a4002c0013070340c0c04020200c00e803a0200c1c10f40380c4ea120101c00540b4807200d080e200a0240c0c0140d1b1040016140e0b0403d14005d02c0f01d84048041180542e00000e00c11903410b0b0803c007a46503000c020b02046050801c000c6490303213010307608940320b1113040d29030306114014040309040c602d81c040c00151540e4402d80110390000c010001311102c00b000ca280c030742c0c0c03260845198202032a2500500d98441c00c0100349500441d410201c03011501d070f080c005604405660720118240b1941c44608080005000e0070090050704200c1d90307559124105070b921f58604600c564050307842485000c5640700007102035000c9404255044039400d13550001c5141c81d00c1025041c0d0702e4a00703281c2c5840e030001460000854041c02031846414072f10044e8007002d030032404041b21540e0241105580004503410580544615500e413802421301c51515541c0da50705040241700e54030320b100062800319032121281450f0184030700702030084000340111824000070443d0041416400707845410340c000b40c3c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 234594874 1250 234593624 234593651
    0x3200303040305270307080708150c0901050a1b030f021e03030a090c081b0a09020c06061c060516020111040503060a0c09180209090703050402090f07090803031303090501020d02070306 81
    0x210003038040c4c0030b4140c402c1031b5550340e03145840c0c11907407254041c68020140d5010030008a00c48040c030926640c091071f400d0007280001122240c018202160a1108201454107407001544420381c0385442991007500074490400024101645408601c0c07251a2014803540004408010703640c0c401c40035200020341021a003030003450340049501c0941385018080e95408119803c1a203e00010fa080d1f800c400b60300e668401c96012441050f148100c03541203400410403528180c140102c2c0304d10301d43c20181d400740071a210076045820664501022a10700e20031001802d8080c0619114a8450700409050501d8200484d480790001080c103120a81d0300d1540c2081c141c01034a001016100907a10003205c0f102054020000350f2125080724480c040d401c0c00a00c855101e400381500c100d03030142c0507810a4896a00344912800c020b0701032018030200b14030110300b80d002040a10711464052181d40520902c50802070010314840e04118115080050b041c00d104d50006270017421651300c040d00041b108101c020 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 234596124 1250 234594874 234594937
    0x5041101020f15150a030c0806070f08061c02060d0b04240302061315020a020310050610030509070815101e030f061b05090108070206060a0b030a0609050403200303040305 75
    0x41e105d074041c0300c080c0040113000d5520132190071341c0c1940040b00c6c0a900d8242060f1682100d413120140054269000103800d17080100f82d20faa40010300b1540000d441c8181d0004080f03030000780300340d854035990342c40c2c031145481d260141001d243c05030802c02c04035265500030301c959502075000181c040c00f00095070005540e029002c1c04000d044c18181081c15140300003000f525800c1c0c880d006e0380b1a02ca41806091700b10810b11445010389030003040d8488401808405138080c04004044c0303c00d0340034580001030a0714003403042c0315800e040900c07655910720303003032140c0c442602490300405202041c0800d452803200400a42c0340581c1e0b0001e501d071105019605c0d182000d8980f10748488544020005c1580801d500701c40a030880c0031090720361180c0f5a56000c0100c2e5281c00c203d40d0b084c3d02200c003880410103405488002c0da0030019421000c10455241c581d14001c0c3c400035101100003540d41c0750210100c601a0742c1c03914640c403e01010318030b5401c1c50f441c0100035000300031216141007010b101c1c44102000106 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 234597374 1250 234596124 234596161
    0xa08040206130602160603050c0316031512020a09050f0106080a020d110a0f0e060f0c1603030915020604031d120607030509100b1305100909050105041101020f15 71
    0x1040b920240e160354009441c3c0301d0b0fa038403c0c58084d1a00b80c000c180f55019009152141c502e81500c5030030b6a4819008414030100c3c213419109242e6140c8940c111148820f00c4c000251001152414020302141305201d21038120342e02c043d4540d40741c4028000c46000c49811541100d006140002e125182e482400d0024407685c40c03400044c0745400f607400d0305903415078007078043c0074036546501e011200c482105440f07020320f11403d03640c0242c0401412803140c406001421400c0288422103940c90000014a80c0c010000d40042d0003045904c5010030501e4015100000d4240fa40d20240c825070400f40e0340a032143c07014280c10040e01c8040c01280c092a215a10a00e42000701c1c08116001414500740c09801010107440030140c9000b400505528040c460052040e00003026101c80080f03139407a441280100401303080d021659245100000f02c10106000343c034045801100001950309151800410f5030300d14118580c150f4108078941c080000380400d06030328207100c0711035400d0fa0380d9891840300d03035140484 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 234598624 1250 234597374 234597397
    0x10b070c0902031509060d03090302090c130b030103021207060e06030c0c011b03050907050117040516080c01080a0603021f020f030d150501050702030a35090109050105030c0a08040206 81
    0x4010004403c104d440c0c2d002c404002030b500c0c0c0195440341002c1c00140d03100b01d2000380100302c80210030030042c2444400c40c1c0d4444076181c81c103804c0410b00e1110302c45548143d405000c1e02c030f01c040b0041c000d52810300818540030608000400d6401d2606401502090744d07030003050b10031b0310b0100000d07540c00c84081c12a40901c4015000700500340ba0044490103000c0c41a4030b45001910380320024100150000d841400e4030300c141c49032195401070400c80c1910f620003d10840c2d071809030710151a44480c00b190b4600150020402030607160074403034001062003100070106614203040440c1000940c03903210f505801451100302c0e04400c0c0d580d1354030580c500003a10241010301c0c403001860494115596001e0300d140314102416404e486d58030401101c41d809246800784d0303d40c01402c2028005407010089002e6412099482640b01c04070070280c240da1000c424516101d403100181600d819a8420602000750409080081c20b6040c803821412003400307030340d103030388280b2520101090a41d569241075405100701c1 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 234599874 1250 234598624 234598627
    0x6090215070c080106060203250203010519050c2a2107060e1b2404030b0114010206041113110417120702090a0b06070b0a050615070209010b070c0902 66
    0x4035440c10400c1e03100240541d01441a2003000c291504107000e004105e6041703a00950804483c48d82ca4000d6400b2051484020010000e00c070380140c40a0050f40d2052401b03450f03078103036800d081c80900300b5208010608428500c04104504252224000f514099500c0d800d00c0340c8000800d0850525220003801103420b004140030205200a58500040081c1c0340b00303000c2400b11292081e0045d80c4e9205c01d0402c058001d400c41440d401d03604146c000b003121940e24003250042c880c0303c142030f0980361340300c1c5e0825240d0b8142000144001070b102c070402c0421410038030040c007880c43c05840d5255070300021103174548981c00304409a03002007500d401c03a501841c102007440340d8503945c4146014003600030940c00e0a2500509404424500f506403d44512503000703010741c842a40c0c0c6a0f2807100030401c0d840542d5104405000c00da022410001c01548601c40d000000a45c40c1440b000b0044442c1c684100301c1d20650040040400680b00c6040b818112400e40c050103840d40038038a484105504590070141c0f60610 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 234601124 1250 234599874 234599899
    0x8010f171509031818010302040e07030b0106020c01080105010809100203090c0919050108030f03040f02010306081504020306150d060209010504120c030303050609010312140903101a0603041203020304060902 91
    0x10008148144288500b0780d001c400e160b09008101030100c038007005d8220aa00100090700f000e41000c1c1d548613045082e20880780e141d075202c014440c000c1c0c1002006074080c0c11101217558000c015940506803d0070014218548441e6503030762035501040c40ea00d003580201c0442c3e40c0f410200071030250848003c0c901c01d07091803c0480e0300100d04440401075000c50500c130001520000200c200e49900910260552031940e40f52241301030b142e0b07102000c0b8105503a4039000240c40780c00b4004404461803101c030409007400e00d0b0041514003130b4081c185141c1c1c4035000700303285241c2c0c3e65103420005070395100700b0258940081e140140c510b0f001d241e011a0b1140310380454101003022600d40c50301501d200b5103080006440f04411b000c02d00d8003d0000800798030200c40780d641c0c40303801040781038089001100c6103480c001c6002d0200f400c00c80036a03215414551119044100c6502249200042ca14150313149030a526042e20381c0407801d03040761103041c24142e00001040500c51142c0008020300d40151200b5803241 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 234602374 1250 234601124 234601141
    0x30b1002030c1b280506030c09131a0f0f030717100b0f01110c15070507050303161b05031b040e0706020705010e0f03010c020106060f08010f1715 64
    0x50000d410074090b0300420f00700900d0740007026551549068040d003103501540080c0e9113902d02c10710401d60441240141c4a00042a03550140214030560500e0000394881c0303102c40c01e004016107a003441c504164101a0004c40444680b01ca01410f1071f012071b020319134251188003040000800400301034045c06103d0303003c40c41117460080003200c08558030072071710f9002e40340038118100c4172604821030788600e160202240320b44c80340d03a060110f05a9501642d66643d001c0740021384100704451820041c01001c9403140030300c1020312180c0d00900301034000c1c1d460442804400e94121000300402041e020010000c400f54003a100e07085009448050121012030350f0075012441800201e40900d40700f281842811000044086079030011544660010f1032518101001520110210a891a0880705481c0500301c1943c0074007540080c0d014940000954074145140100341d1000c503100c2d502480200380040001100d0009000c04031010038000481010803104441d05240d2800e00448580e0ba404040c0100385 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 234603624 1250 234602374 234602377
    0x60a0207030206150a060c06150f06020705041e0e030706090507090c0c0209011a0d090b01090b27072706090f0303210209030307050a2904060c030b100203 68
    0x4034020340071241d482da41c02c0044c4120040745444903810102da0082008482e0242034203070f09a030f01c0380c035011602c2500d0000d02400c205065010303405214001000b0400ea075018845036001d0701c000d4a003445030740c1c0060340d24980d0412941c040c07030701181d0340e0008038008082031058a0199074006010710642c41c1d00c1c00c0030b542c0c0700072500601441c1441c00000c07012640c0206880403809a001c1e1001001da071802501d40043d03045400d481e5400b00c01000300344407540141c456600020320071083e08245504008154040b1040c2696090142c102c222405507031416018100300e60529541e0400c1030390752814421111500c41000c50041800b03030344140d40f089140c1c0440b10341039039110381d60f5045003961072500040c842c4280c400034005c64514050035801e041210034041d041c5951103800340c50b086407200400c0c65039000d81d07020340c2c0c182c002054030010082d02e05540e580d500c14105012045c024146c3c0d101203081405000205400d55407009585014000d410804440600a0012500800030303107010b9103a = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 234604874 1250 234603624 234603637
    0x6050301150e030a0209071b0b09060702070317030603030d02040306020702101404061103070506011502100207020a090c0314130302060f01030302072c13030e03070501080a0f0905060a02 82
    0x800d25400100411103200d10302d00b022002d00180203168100094007071084405003e04120b040028840c400c401058111080e1020280703c0d030808685494621011410418007901c80701c01c40d00402002c00c08902090700c690803580001c00429526154000001d00c1c6114034401100c0580c00420000b0500c481da902030001e0381c0c0203039011003086003c490112403000c10151000c03550710090000340f103443c3c420a20704003200044411a0319050b41520382c941303002001d074081050700a100e140c030b00c41c0c03e03414412850000e0844c03000394241005a8005002c0c0119401480000d41d51035141c42d00c001d1003a004031440c2c550920002d007060030800c0c92002c104403005415000343c480c81000c220032040342401241202e415a02408480381801c3c546503605080700c40000c201c0000300c0f01083c072103074000005401002c0002110304080500c0c0b4028200312003003000c041c480d0b08140c804200c2d5980020105901060442c000900b4451648002c4000e08039500c02071f200d80b09600803c0942a200e5006003072 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 234606124 1250 234604874 234604889
    0x3170409090602120a0c052502090f100605041d09011814070e0c040e06061909050f040207051e0a0c08070e1003030e0d060212090604020a0801020c0304031104060b0406050301 77
    0x1540c0e541684050030303100c103200e0306c400180b800c1021960405030010740d88610301c452081100c1100c0241c00041904600340c030107050000000003881800c0b11007001440c001c01346428403a0500b0300e404216030116002101c4458040c01a40c000350028500703511205074000110950282078402c0c3c2080b003035003024450102030074443c0880110f03002c400749102c10300c6100e9119000e4a4036040800134801e101000d04a2038206006000315a8100740b8804105e103124078075620040528589401c0000c1c0350740050405000b60701c1080381798003103070010030510120030441185015540901490341d240051111020b449401110b0010501c403801040034011556001c8100802d511a807014018011881c030009021038402c8041640341d040902d1400c20080c01250014240000d03101c2b0390710002e002301c1361001c180c5c12100c00c12003180350641c8440c002e004224004c50800451021595403803007a0300020380401d11811401c0081d50340c0b034102c0009002d07481c40141d16565240e00140c11900b081c040c202 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 234607374 1250 234606124 234606157
    0xb07140609031c0e010902120105062d04110d0218040b010f0813110d080703020f030a0207030f050709060609080d020a200d0803090c030609060106020703170409090602 74
    0x140340780e1000007542c070183c10580c0b802c081e02188015400c020090221240306554031101700a0260740c03042c5030902c0700740070403001249515000c810010000c80c1c5200c50034a443c03645407110700c0e40b000480041c0e00e08106650005d84031420b2092004540909201840302c140000740c0103c80749108400b001d0141c50030780301070295100500040d10f079048454640c2c000241b08200049450300400003040056000d00400310b0141c0d03140e004604281e02c0d031074003500c12000005040701019810003010303600d41e030b03800069800d04101c1030009407209001d10001c1d2400c0e003140414001d00109010020040810107801c0108956910001e800740c0042e00c50844a80240e944420000d8004038600344841e40c00700ba052443d4007030fa400c3c15401c208010103650026000c01c8203000180d500c0c8015030160510313400070704c0b00a00040402d0b242030b10013000001b543e00100010030440e90001080e4040c1c81d80002911742100303111034a0465030007503a100500d9203060004c43c8061105940c001c02ba120301113550748 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 234608624 1250 234607374 234607381
    0x2070b030a091703090a032706090e07030905030a030c0e06030f07020d090f050409060b0d0804090e16090b120712061b09060f09090f0b0405101503090c0b071406 71
    0x1c0c032540812a03005ca000e03008101c0100c0004c0c880c400960110342d0603146002c2e01d000c1c25603142d41c2081c0c0350300b2140100d15410028405010440c0c05254008054902804072000350741c4c1c0c003030701d90180504150a02d500e9a0000b00c1903405068511464280074100c241caa1070000c0380c1d070b2046da03010707200d080140c060340002c5604180f18044007404e981c00461802502c40c42c0c8421300004005c4504180d80c121340d60250380c03050744d41d11410166031034080d009940d15582020285800c403004546141140d5000c0c1d141e20211030703010300ca65021511840000a0305082c00c001103480d2200c02d501158090241d8580441e00142401600103680d000d0101089070190602c0c0910b800746031000c1c2c0e940401c454803010044644100802000070400b80b40c243c1940d580d6500c0c040c01c0d940c035880542d40854a41c1c8c42c006050805202c2c480e070021980c1128404540f03084484000c0361f9003c5141820591980c0756942448000002e04004010007520180d0710501810072111442c03000e2640300542c080c41020 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 234609874 1250 234608624 234608663
    0xe0114070b270a030903030e0a0909030207080601090c1b14060403020d021b030c2404260d171b030405030307030f06051005071703181005070503041202070b030a09 72
    0x10f112a4543c503485d42d085240c151380703054078182540c09aa551140a02101148a101c18055120340d148240c00030702d12107082c018803506108058202c1410103260852a40c0d1780c682c80042c0c2544540000030b004400780a50030702c410010108811840503116800900c000c15600040c1580c0ca813209900f910700124100c0c05e13076054074450300d5000d6403507405519040c01d1850f1a200650081c0c8011011400542500d50004c0407034104e6880210f5501d1909000f0000c02c079100311202d0081003000c00f42c062000900c0024004041c000c100c5602c1180b14030018180c800c08421050120542410b01e42d100e150500c1e20a0b680d600442d245c3c0e0000742020140d0300000787c0b030b000d04420f90344024060b81c0f0f104a030b410203c0d810f8103e413805440309403140740103070741c40e16060f030080d8003540c03100c4592669140c00c2c00590303141034000311443d1941440c2c1010043d403d680070050700d401a40c8130b8030803c103031440782100300d20380049500003a42031a000000d00000010a5020b1810b0a01c50441900c00002942c01c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 234611124 1250 234609874 234609883
    0x5010302130b09010e030d17010f06020607110a05011107031b110d030225080609060c07020d020d1703091603050a0803061903060f0b030a030e0114070b27 68
    0x400d00144411030521020788030074040e00f0110b0042c50300702d00c00b841c40340010b4a42143c2c0d2a80402090320000e08503034407a10039807542c5c090070340038407008203103890150020f542d01d800400e40020450707520041c01131044103000e80f40185801034028000420341c200356a01540c420401100415411207118580e0441c80003a51000d603000380456584003224014480704200129040f821801100000c11044601c25607003202d0451002000d0402c60406c0d6540c0e1a1203c0a001d000403603100d84100040300c1410720072107614039816140c03401d03040c50314804583c10b07610342c4c04010980901010f0001503451f40102a51040f4400230803151550900076905c85c818806000242c0280c0100c0d411402190450b402540c006401511302200702d410b507001c060400c141600100c85481d205c00c290014100e0a009909503000118007906920300700d6500607140e82d24095a4034148110701c400b918080c440401960301143c2c101211003001d19140303400c41302d0529040002d100a098640709040080d0f80040d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 234612374 1250 234611124 234611137
    0x80a060819080a0c020d11040507082a0d0f0e010b06040e1b040312110c01030b0f0d031b05070e0c090a090e1c080f09030c2a060f0c01050105010302 65
    0x241c01d030207a841d220000c90b540010070107070912103460410b0006841c0d04000e4403000e809001c40751407014207402040142e50005c0c18407410894010b003403107490340468031030203156030210008400300200c24034800086d00901041d88a605d1800281d007030f03150341940292420307201500081061110f51020002280141e01480840e0644140003541c000f1800d483e017080030942a0301ca42c00e040d9a0f5489030311510028a03910006444c000398000c9000d020050f60300000000d0070306008510001002c00d58100080d602240f04204030084401814042e1500740c00d1405ca03140300340411409402e002c0c0e51490b252040503022022200040ca0010903c016607402c0000100989052032a00303000c00054a0740d62041080c50103800800035591209012580414106032102ea15a20345440c003108600300c01410103126400c00c100140d101e14011858620441040003130909200190300301d503c042c01011242a08441c00007400f0064001c228060280880d080380244103da0b04c60004505a02550 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 234613624 1250 234612374 234612403
    0x30809070f090b04140112200105090d02011806170f0c030714130608270c010c060e03030702250b0906030a09020901030804090c03020f031b0f0307080a0608 69
    0x4a00a000254442e0000078500340003d00100d85e444128400000340c171030a920903e0281c0111554400f0400c40c0f43c1d00012003590b25103107081c40341d0800b001070035070310400010301d10800b01c0002100c11680501440c1c42d24a0b03a81302c02c07016241d00c860015141c44c0307040c180a0815005d280011390740203440300042d485594107203c0c2c5030543c1c680c1e03001074515038004c03103d181100d00d06000d80d2145244c4217541400810f000da844a6940c10001c00103410100d00c410400107041302c1d900c2d080b503071040010700b0746aa40000e1805030500c4650b410042d008100382c3c206141907000c00802d10480315400160000c5095682c09018250b1112800d111440c10b190b00c1001c03d20708081c44032003007501d007034001345a020540941c041840450b940c001491080c00342c00c04c6484000c0880c050084c08840d21440d54400c0079402d045280c0002d09040d2901c07400010300c07040e001607010304100f84000d26007040c2e400c603168842800b42ca9041c413a001034101003003180e10101e02c1e86401c0c40014140360020382c2d0000759010 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 234614874 1250 234613624 234613649
    0x91e06062607031112010203070509010e0907020a030e1c080d14040f020918010f14011a0403020603070302090d05010209010f17071d0a0303021011030c0a030b030a0c06020a03080907 80
    0x66549104c040c3d001003d400345d10040c03070440d880c0c040200b800110710501141d03991560f100e40d400001350103600590001405501034200300440703140c000808000a9806080400c3c00c0d803c00b00004940560304000f400d0100d1078505110100b000101c040c04050103644000d0180b486c90014a1240c1d4404a5024000c4680140750070050305000c6021604070034069140c1d035020030307440c01c240e0956400040c5038803010360f90180b480e00142c000f110507003d8600031003560705d00c1ca0100703560051401a400081d2043c00000082200180254102c41d11140e0141c003460a50095040c0300d8000d41052020f180418400d940c0a52140d1040000740c0c1c40701040035200669454690013262010601980141a19035101826807a030381c41c0c04d0700b20300451280d802805c0401c48240e9107000c0d22a850b00d4a844800180280b0070b402110f0415950302c4441703450000380700710420380024645800c00c03401912503032545501003400c5d0360103c1c150912034000e85406a9a84032140501d41d182d81c03512442248001 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 234616124 1250 234614874 234614879
    0x24050301090903090e090a0b010e0105011d031501030c090e0606061801030e12070c0e06030705010f050d0207080705061302030c0d03120219090906060f03091e06062607 74
    0x100c6601080d5094081e25144181603103c420380817803035130169048041507000000010030040140180d6001d04035010010740135514280010f0900008510495020400e4081003001a00d08001d000c01003a41c04c501c001207569a230509402e01c3c01c5c0b500894682c00d04008410100b6a00091b130240500e0700544903602c1c003800300f9004a0f0071000080c0c1c01e810161a190710518031390041000d1200c1c2d04205560b42c0c0c2e918001d1074000400c800591200c600c684014080042558000c111304040329400e0800800751004407808a500e0b204030b0040310071051000c1500c2092101c90300240114511a0084070386540b2041e00c1083c260925100003903050307024a5000d181810566502401c0520070b040c03003074031610140c003140160380108160b00100709000010703031081a0700c0b020920041c88014030412440d0b0a000c402032801c40a0881c210078541c4031004102008100d118143c81d00180b0b0101e034084039400d1402c400603006038031450348020005052161300d82070700c400b0b003c003619920008182d02031 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 234617374 1250 234616124 234616139
    0x1a070f1e1b0311090603160b1305040902100809030f0f04060f080402130c051c0f0501050d0b1b0d091104061a250210030b1c080d0f06170724050301 65
    0x1d4004018681502800070b203c1d407141e00e40b10080000d02400f081d0281c5960270803005140f9200c0e5980068031543c18400c075000540c807810602d102814081c0760804403507031030001c1c03d4552300c558082802d0080d03001901d2141120340d540030700151007040d602c9101c1180c101e10116520842614061f42c44107100200f040d0490069005150030281408d00034140b4040c0000c561243c0c48500c004070300d068841c200604990303120b1080c0d5002d0542100c800c208003815403100c0e01140001003541184051a00c1d4410b101100c40c000e40383d4016203080c0c2130040080c41d1600c1340190305d200e0f11141c02241440000b055020038142420b41c400004018541014092a4400861b4400d000c8045c0510188150580582c80310a18015000070307503180400c0311401070050140044a11010352584400b2070403240014210701d00700c8100321900c00c0081400300d000048000140300c01e62000813014240801071a9410011030032000720b603035200da03403c141e0032496180209284550145000078204000501c2800c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 234618624 1250 234617374 234617389
    0x12030606030712061503050411040207051b040b0607080a08010609060c0803040816120233270114010b0a0905060d0603080d051503071a070f1e1b0311 66
    0x15201c080003044d0705075030ba1113100140841c50048000644c0383c10130002417102c1d199000228800694085217020501c0d120329850b0042c0403501651a030039512080842c1d0341c1c0d42c001e040390400c014034a0fa5035000c680f404280c1c2c0d5000400c00004100460000945c00e0f0207000319100301c411503101c1e105482074954805140e544001d07c01c8540d0700c000d00c90342c0e440c5204215014806482101c2072840d21503412400b0780b40049024007080d82c02d04c80d030750401410001d01244070b8a000c400010000310386580c07403494030958002d20302c108a00c4200803040904001508851001a40b502c905070843e600c6900b002d403540f0030100c0d41c00100c2e040d100100807e0034000014545031000381c4e0002000c50f12a51003541613400840d10075883ca440c1c0b014048107110000341c40301c41c0c5604070014460b06142100c030000d04445141e0400d05800d01264020034403442c5900e00d41d03015403200c0486428034070058080580d9032038140c1a1295003003110405031034008411400d064035000226209070b60010410456036 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 234619874 1250 234618624 234618647
    0x504021b0102040b091503070509040509010902041109102f03070c030b0a06170604081c02041d0108060f01050f0103090204020a0f11280203070e090a05120306060307 73
    0x82003040c81155000180a102a00103401400c041d941e807903408000300070b00310f0080890030f400d20b5000c10901403269000400ca8000c008146c402203078075540c42c0c5509004040000c006074000b1705212415502d80e500030000d00405800316581030b844102c80a007207512400c01d5034607000d03404002c141c0044c1d0f080b1000d020349900110000b12031130b0101550340d42c2040b200591040312641110303007e10070b07260140e000320405840c50301c05000c88903c284030400d40d0b82a002e00098045080001c154003d8440480c12103150520b06100703641d80c41c0d964490f006460180500185920f841800114071000c010800d18001d40750340d42c0450343d590800b0100014a00051b6245041c075654003111340050325540064103c55078203031a9401d01d1003d0b070802400d0100380e1200030315590000020001261f50302000c1c0788905910b80700000e0501c0803440803a10f002c0642d045000b42c074642508200c1c40000c0090060070440c403a0050700d00080c003220b604100c5001c25107034154054001d100184100d403064010005 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 234621124 1250 234619874 234619897
    0x70605040c1d04060f0203190e030f16050c10020d0f090306050a0c0801061103040320090c190c021e0112061502010e0601080a230105070c0b1003020901050402 70
    0x85140d40b400c602860b402c80c8801c4000315004a800c101c00e01c41c2a01c1400c0b10030f041e095082d417561802a6000c2000b4090704180700245035500003684858604005480195000e4441c0c180c1e100e040f1442c001d102ca0001108031440e208604800c0d8981c203084a034943d40a1058008207010f101c551810788240c504820341600f00180410b000010804030b0140c0c50041080d07140006118181c0340c0010403128050304480b003030007641d031000c0b000684d00108480031a43c00c00008084010f4a0300e50114a881020509030310402038018007444060500051495012000b8204031690802d0f0043c1c50301c3e044800c2c06548000c40700181840c10107154224192010140340018180c2900713401c060031100c0c550050802d640d903000608402640907c40c007000c03402e20700014141d40d03141c000e0300da50791014100010040c1051502162808180560314868426114001c0c4100d240004005200c04000c03c02612556011000300761070034880007502d01665000f50030840c45038248403c0c00060351010042c0c20 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 234622374 1250 234621124 234621143
    0x11190c080d020a02010c2102090406080a0501060f1413020309010f1b02070509040c1e0906060c0c0b0a0801030221120a0224150d020303070c050405100b07060504 71
    0x28002034000c0010000c0c1d0705400c10042c0c03106503c2c0c000070b0865441200a9003030141d178550002c0d41d08816075001410f09014140540d4684010b4042005080241e0080352648903103031400c420054107400010582d401020041e110030b80d01c0e0318001520426003910364001001d140300f65186a0709800840e88089100c2c00424100c2c00d2032009000c584445034a0040100071000c0078900c40d9060142100400c01251114818249078640852a05c0580714480c0401803040c1240066510b04241340010400004104030740c69032450041c0410901900485008111180108480c0d0600c01520030480c0b039a610b4200f43c0c0c1c2035a0901005400c9290303421804d54810944044e029410000c514840420030030082d244d10304864042e191107030744024003100364000181d01c51504e9400446130b50041400c0307074801404d040800454098000c0702d02c00394160100213031240c10301c10300545180488e00256010400390340d46150401d4400d0083c0508052900e0800c030b4074011603400c0e04140d4005006400e803d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 234623624 1250 234622374 234622397
    0x71a0717030a0504020102010c0c08160201110a05030306012606040c030e0a03021e0706020607050f0f030a09030f03110711060409020a081005031f091a070c14011119 73
    0x240c8a500100c0303100ca802601d4008000440d6030a0183e0b2255a05a0134042090b03165541c4d0724407280903020089030b0760100740c00c0f80c00039a84254070810b004201001500e03113480d0f080c104076403244e0003114880d021a10f5101100200201c3e040c420000b501030b0318502c0303400d4440200701700c0a04441f80d1803004254079031200702e4280ca802e1103142d150a110350002c14074118040e010686100301c4842c4071115800c08681009425004a0344e16840b0b03145241580d55807030f00d104505282d008040756000e554801008101c20184141d000448090080c0c8401012503a0054120190360340400e0103100c2c50414030140f40001d1007880702d00b96032200209124100b03503c2d919070170b00b00d03001100041e0010302100305019110b220340114901412056020307204140300d110b13564200b07a0410301600c00c3d032aa168920310920600603d070189102146510084030b04007008014800c2c0000a429900d0815400d110021404140324030201c0342400c0c00c01d103040420030503800f2814454451050148418001d49 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 234624874 1250 234623624 234623663
    0x306020a11071d0a090803040f1a0411030f010c050a230d150b04060c0b0901020d0507020c010f0e030c04090f050723010f0e060310050d0b1602071a07 66
    0x1200982504190845400c410f07150440021001400d11200a4546030a69005c0380c2078504a0f90722030340080c078a410000d541d02d0007072280170394511194500c00079801480708000a000d104c080b02101182281c52800900e910790b030881d40030798064008078204016181c2034078051141124640c4603191034861180c0000600d94540e804141000f039003035614041120300701141201e40c80a070400d0400d080c01c1508055024007001c101c014054500c2c060a400208404403d404030341d042d01c602c0c5414450b50425000c0a0351b205038400741c55001c242543c00c0301c0e15662251460001c03160008001380b0031102401d080c40001d00d113000080c0d4100458542e00404500c3c20011540140f0182c074a0720b210100404021420008900703289040010403004030700380a900c2844180310000172030700e250307a80c1c80e040740301841c03204164880c40e080702651400301e06000401c00c3d40b0b84915580460500d1414900504903190440b41c02480c15242c18210441106001c00003c0d002042c80742d24004141d0f2160b820 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 234626124 1250 234624874 234624883
    0x10506090721090b090f0a0c06050f0702030d0c051c08010e070309080307090f1a030a110405100c0c050301060609030b190501080a1106040f091a061605010b0a030c0306020a11 77
    0x141a5a241d0300342045c48000e0ba01040010841000a4050102e45243d1740e200350403006c19100c1c210412034003081140e4151500700403504401c5d401402c4841d0410510005400207040040580300381c040c0c000c001e4166040c9805015045683d03030360721f00d0b8603030806440c4145020060200c40401d0b81c2c1d805e101c1c00203141c110095014010546075043d01c03078680440756400d1095500203214a00b4141031004015034140c003540d03082448040085042c901ca5140401a8080d40c0d02035035004c035a070860f0148090700542e80c0d41c2868080d1030080c07081600c40040c9402c0ea05244031383d00000d2417198040001c0b61036458440d81160394200404141e107540b5940205441080c4c2100220382c10a40741841000f10f0302c0f040147d5140c003070720298200352402092540031041780c440d5460947c2c9912030035040b40140e1205048140b4005c00094a039161000035682074800a8812074641d0318281c14041c9a1030305010030400c41340c3c0801c47ca0711982c11540d46070065080401c841c01409000d10704410000003e10 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 234627374 1250 234626124 234626141
    0x501060206010e100f150e0423010e040203071a07060c0e041a030d0513031b0503060112050c01111603290c0901050f040b030c030f0108010506090721 66
    0x50081c440ca5040807801d841503c00a00084003104481c80d08001c2c0d140300c04c0b4801e048458988154070081043d110a0b204100e8400c2050350103407900120070030440d5080e0b1007101c00c2080000f5051680e80b10340e184c0040c05001e0b00e001c0d502da40050001c02084e800354100b142c02c400d91080f11400c058003591244180e4a07000030301c2c3d01040d404000c02c0c8503800c16204085442001446040304230b00e0780d002094840000b80805d9003000400913484446c070240041d6517004607803021520f00c40180701540c9540017640c50007514030a000d00c0e03000150103005001074000440d00800600f20118000006650f0261895800495401399403100c841952000007282c0040d401a41046032105510b040c801c0607032032803820100031581c0c4e50107200b0321072500c030241c0f480400203003095903450f172288505200b0390041ea40201c0480c1000000c200e514031307102c0051801000c041a0404059807144005821b0741c81c21180c160b0054480d2000507021841104070130440003184a10030400e8556000c100c040c0c80005 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 234628624 1250 234627374 234627377
    0x7082811010c0b0f0103060f18110a0305030d0204090b1002031210050d03020a03180f0302130b060703020102120c04051e01050d320c0706020903070b0c01050603060c041521050106 79
    0x180040040c480342d0b0082a8101426034009c000780c0128813820b003c810041c11003d0110040c05200505584642d4008005542c000701104c0e102c204079900348000c0e52044c0a44113180d800e100a2840b1810160101180780030360b034005d5418031411521901c0142402440c0da1108104540c0018858452611002d08240a40c4c054002240030f42000350804030110702001000c045d03140c00300000d07158100d044040d83d80c110b480c0181280c1880900e80030701210640c055024400040300e0080580550050640078150b4004501c59a01c00c04140194040c40c41801e03004125001110b11034611004031184c0d01c0414102281094480038a040444183d18544105582000d5103803200204207450b0702e076140e01a035800c2c2c0303852801e030a1f000124003810390002c0c1900d802091080c400e94042c040040584116000e4a80b40c0076038100031400381c0310a0340c249001e80580b0021455a0400c00f088400ba2503e0400c0104941c0c0030f0f031400c4a6826154000c0140503020b542c0149802005004090080c6981d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 234629874 1250 234628624 234628651
    0xb09030a0210030c090b030105060403060908070203120a090806010b0a0e040e0102030705070203060901061d04030c0503030403030f1a24090a1d090609071419060207082811010c0b 79
    0x13403c064041d100540040008810030b0004205030342c0c0c0c1071b0882d015a079012001290382851460002c01d24012868000e52500908450240c110442c0019001506455a0307a003200ca41d141d004503100c1800b07000e41c0304480340070081801114083c1000404841b006032000980194200c03c8174226002a14588001503002441d403080d854100812504445948000c000451604214a80c0800b40c86490304070140301a000509150103855a5420301d600030040e00d0fa0b034503181c5001001400c0101449000d81d00e0550380b0000807960b050b030115000006488561989150351424044d1050311131040411081004061110303212440e2100060003000010b0078962681c1035600c0180500801c0018194404001c1080d8050001900d01c200e4a440007a100b6240b840404900c00782a01c12428100c40503141c00002c109a00080349400c903a40d440580d22480e41c205400c1c8410426040130b03280030002040d4aa0200352100801000383c9030506140c1002d011554071020545011100c04084156 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 234631124 1250 234629874 234629891
    0x70803090406050a0e01031e0b0103080a090e09120318010216020a08191101030605061305010207060c03050f0d0216120311030402091503010e01090b011707030b010b09030a021003 79
    0x74a4024a000703468111002c140e40b60038290321400607001448060498440b00000080303480d0704050364803c241c2c00c0031180d5106e68580c240751849a21408103030000400c1458002401e40400b100c89008880d00f201400b44001c1e0f402078002190805002c510724104c0001460102c0c030001d100400941c0c44040c0212001000340c01004119030701640520110340004910203003166520900104031980700550900301115180103e00912140e0400d075002500003c5600015061031007400440b04240e01b250300454aa280c01c40710309021347c0c0020042101400b08055945c0510f02402c80941406001070606a49011000c0c4146030014240d034003844200814602d141c1c0b5000b803000d640003203100c4901e9800c11390302103080c040008140030099025801c021080340d40030340200940c032190900a100d08003907030400c80d074406070038407416151800c0d00030040c0003000049010750032290400c0401666038a02300307041d00a6404410603136454000c08e4982c0c001a0748001082a02c51520b40e00010340d00c4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 234632374 1250 234631124 234631129
    0x70210090b01050306070203040602120c151503011104060c0204090f02030304060503010306060b04060e010302160b01090c1e0e1905060d1a01030e061504060306230703050403081303050c07080309 86
    0x17440900040e086400400050050b603800203006072492502d00c651a40e82c4081c210401e040c186030b840003040003444201841084072100e1601c460300ca20450080080c03442143c00c6003414419407141002007404040742d0000f502e800c0e4001706006001c2c40078103a011000c0d5001034210760140d0030010100700040014414841c0381d2040d00c0c042c010341001c980c03405081c21406496403040722600d43c10550001610344101c61519000811540e000402c240a5611007c440d0043c1241032001d0300090017442200143e1031441d2003030200c05203a61201c540c804143d00074000510444c0c40402c01015082d200080d41c2c0e16407000a203880700056100103020041d0352114000b40b22040010344c1050708041c8106000080801c109422400402c402c850403c040700104015141075400a0007503440c0038003687d0011400400e6120300d000c0b9101f0004076030f480e40410750458409840190004507004001105a010501c0c10001035000c0d0803c1307801c000d40c0c50729045c81c04080d0341113003009410101e000d01075070 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 234633624 1250 234632374 234632383
    0x210f0905032503020601170f070f06020d03140109050c0f0a0f0f021606181206140601090e07120209091512010e10090201091d060a0905010b0909070210090b010503 72
    0x200c000710224442c2940340d10020365a02c018010200e180141d903001000b0840d081164155560840e02070307500d0566114243c104800c010700c22440940106209440c0340741c400e10030041d032a00c04c944803111236400c2500200060030024000310540707608001141035000760201030b010f20300701035460f6200007d00308030082100013041c170a6400d56100300d108c0d000c04140c05040030706940452a03d40a044400c003040d03911001103a001000d1001040300078401c1c4400343e00b1044954180703490380040340e150103004540c521118032803440300e542e01c41c000c16038451040c3c07111071455186090150814110f50300041480c0d070180d500103085244605009024208010447c3c40404800000c0020150a41c1155180c42105440c1d5020581c0c48503c0c80c1103a0054100d41d003d0620198012a003212121403116400c00c02d44201d03100308020180000c009209004130740c1650308414440b8104102001403100401e006400c90781540142d01a200c0c40c0501440f44042d40c601418060046500d80400d16040 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 234634874 1250 234633624 234633667
    0x1101050c0a060b1905061204030212042c04030203040306020703020106230915060702010c021c03021018110f0a08030c0718020c0d0804050a061805010f0507210f090503 74
    0x518a140403c20065031504140d440321f0042c4440010310b42d40324030b4102d0601c0300c0643c8611904401003001700c1c0046285100d0b885042e1800d85c0d0640200c180042440d0040089900400503881080107000152494000d029418403a00012510544440800c1c40d4500c203240303071540e0b007100b030a4505910b103840000e090b000381c4601000003800d171000011921621441d100030b8140300e8400301c29800c5484000c60340740c4c44100c3d8402031880031742500d00251141d0a0000c1c0c1440141000d403640020440b2008105540fa40001d00d414044c040e80c080c012200c04035540700d80e000140340e8001400d200c051005028210414010304081130824043c92080d8400500e8180c040c0e10601c00225207110000e501d9403484550306212220781e4407407810902e04482781d03a00900c02410100f2141005442948404500d032041c0021711901104d10a54012108211007040000341040042d00585100c0d000d0415644c81210303011403603c0010303444906940d2801c030f00700d03081c0d80b001442e40001200e5480680c403 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 234636124 1250 234634874 234634909
    0x110102041805070f1418060a0206040506010f0e04030f12060e0601030f050c0304030806031c08040b1312030b031504110f10021002090d02100f0201050108070e041101050c0a060b 78
    0x42d103032003580b0017003401d094000c034402c03184000106800d01401d450025044000020240c0307940b0506040000c0d200e40b0305590465141c8500300011039502032000d00d000941d40728007102045540c4544040351010030f40160072003030000c541c0895002c06e02c5070103075134027405140f41094043d080ca03d00042c101c40004054603081854a018850030b401c0d0075044039005034051a088116449203400a814541806408019a030700c0c6501d03442c800c2c1d0406a214400d074051a0b003041d1903901c0848242144c03030400c20080c40400d4503070150132007034029440b6880840c0b002d0203c94034044014201c0440050984080d5005050002e41d9403280c9415506a04028000d03141038198406209000c0d54644800c02040149500890070500700d41f1000d503440704058005211444510b40c120002d0620700c06040d424005509010000c02d400400013404411203010b1401e070710665865484007113900b401100014104a410820050f05400c104500c46555014140000e6020f40e000c0401500c908107205999 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 234637374 1250 234636124 234636137
    0x611010606020a061a0a030c090c03111603020f1203090105070c120c031e05030405010e010e210409021c142e0e09101a03071511010204180507 63
    0x40020781c0420200d03c11035110001060b01c45c038203681c06600580140241e03400551541c000802c1c0310042100304221800b509040042c05641c000403000e80b14140c08100446c0010419601d41c00241ca0703050b07801c1030213171065507000b1200d40b80803410070005504050040c1c20100c140a0500000e00c00d4a810090342c2c14400c521900c40d03515280c850b040d8503010310074400e03090380320030606000386541049020103020762007668030f40103006041078000b65000d034ac5940c60540c50202a0905109403071042c0174140040c40c05510002014005081558602040038000d1200141162181c0090445040d4080d40d00c8407800a0398504c0003120310080940c55030702c0a200601090000c81020718101d0301c20042d1204c0203020b840845980c03201c06034042d24041d0342e03071710804c581c0c11800702e20403031042d1240c1d03428410000000f075030700309402128059076416006240101310040071002c00c3c0c1d500403000d007006045018491310789030072a0000c0e407244100029034510000c240349240324203030b030114a600b40b84 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 234638624 1250 234637374 234637379
    0x70e010b040621060b04090c1d1507060f0c02010504050d2307021c0804170a112205070e0a0b0307090510050d0203010b090a0e07051614031306110106 66
    0x41c5200030104020340c2c0103c0ca100070f9010b1000341e401400280449a01c09641c99548031402e4000f001c000b460f800001e0740b2620015101c918603007981c48402d0004003101c6080d00d11a000c1601503120041c1240e0b00ca548540c200390301200390251420804040c3c00010750f40c0f034241800d50a00001240420401010018051100c4100303528541941c500c0b003441502c451151020900c51800030030f1500002d84c90350a03410420811000410640b140c680440c2c000420310354001d5a04c00343e140c2c2c02000701d051407041d40c000d410080446000c1c14164440300d0026104e4203a004226101522080000344980078031440c981800040301c00104024403017546145803003040200074609901803a1b200350507011951034024824815607075100e4600408654950b590b88454400c3d80c440d425140c01403040300c1c00061a04884082184a00d0441d06c65501d0184402c4006075200b040785011030b4411021070000b0f44100703041006d051102c0c110403440304550706140d000343c0111807841481000d41e0501d1400d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 234639874 1250 234638624 234638627
    0x6060b0c0d0f0504030b040b0a0b042703090b0c060108010b0105030402011d060d061707050607020603040b060d0606030501020309011409100e0f0133030803012114070e010b0406 78
    0x800d072401c4203180106600300ca01c0c10458480c8035651003d403124048005003c14800e0b0000a5030180940d040108145450242408255015003080c40c090080c2c00300d0800c60070301c040f1010682944030307160000001d61121b8041941d604082c1850015500050043c00b20b00003d105074031400000342400c078110f1505500007800019400701107401015007040221040e2200804d98901131601c01050003550b803222a0455074074010040405e06121b10280004c01d070800e602126042500a080b1500e15036942d01c904000c0714014100c1034000800f00d00080c0032405030b10074200a11310030000580e403802c107200d07401d082d00c0f1941503103100b20058200b401026000080c2b42c442000501201285948160654a00301f0105151202055003065a03820750f41140e080001c00c04c80842210580c10f415005403050b00c10b40901000b011140d02f04010311000c0d10b0040c0700c6d0b03510745403646d40355002d01c031581e01c81c6070886003c1880c2d203540e0302540040c40f01da41121072060150407103601b120700b8185030410 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 234641124 1250 234639874 234639883
    0x3100f0b041206090b0106020c0310050903270301020d020702010e1f0c06020405100207060908192003100b150304080a0e030f24060102031e090d0c1206060b0c 70
    0x3540302c0d800300c60b419074010480320343c1188203603e8020303800c0c3c8030310340c0d407103c000e515107050300c240a100b4003508203000c108141502c140c9000304010f50046d800d03c00014110840314001684002d181580111440486d40e4240028402e500c0d2200700580c40307504610014050122240080e4481c0381d4400e61002450b08507214103403100302a1800e1000f102d49410254000d1040ea084550800c2c41c441aa100094000038031600300c84d1b496980c150f400799a41c103959110b4440d083c0d68003c044400001101282189501340000c600066264250106400c000b0b480d040b541c521012a50713442c0c00e684d0341c0e03e1405000c000c40d02000310145601d1440c01e0340d1a0326030b9114001e0500280101405940384d1902d0400148600006c004103c441c84424803810850045c071003040c4101c071083d5000054915440842903800d400c450940c0c2c0c540d8007416840380d410325044000125082103034940c04074080f4a0f02c148181c014629001d80f8800c851031401d041d07041c0c80840d080340e04058410880b15135a00c0000130b = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 234642374 1250 234641124 234641129
    0x30903120506040207020a090e161a34030905010c0809060d0b090a02030405100b0f12010e03071b0b04050612100905040530040306110d1103100f0b04 66
    0x1030002400c1d907103550015009000d210b1000e504134905000c041551400c80d40b06c00f201084000454820441140c1e03180e1341c24456000f10924803043c0102c110001c0100006454010b20301404491603425050b01c00ca01d010f0702c1c0401080c2c043d090b039011020300da000004d64000d00807c2c0781440c00302c0c146413544042c40c45402c03001d0340633600000b00d42da82c810055103c41241c200c014040c0d0031700d0410a5030b40c000303900140c03400c1c0c2e406d010381c42c40910011107a200e204c0c00034001400c4903850611030410400e00c4d000d111241070440d503c80d0031007008a4000d000509509201f44941081040c0c480d020403400c09807030300f0070040000b0800003400b0301e51701c6000381c0d06400b40702101c075421a0307980c580c40c441070243c690012035480d0408080c4410054040782e804208092884140002c082c2c0811440f400c05800709184004203080005002140e40f0781c000320840100c1020040c80c00c0804d510104c111240c10b0007041c00034202200340709a0310140291040100214906001900d050a4894600b0b10851 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 234643624 1250 234642374 234642407
    0xf060f1602041d0a0605060405060901090b133215061b1204090c0207031106090f0a030804060912030f0806011211090102010b120a020f0111010507091401030903 71
    0x188020340c21550385400c654200045030702031a80815528a0300d43d070f5500c010104a94041c2010005040c900302442414401d0500030281c4007070b41d1034520303918002c1101040d0150089035803d0b4081d0b0307000080c06220b10101c0c10f003039441c0c007000304040803680f08092640c01100f4464544140074900102c031070401c4600b5811900315513078001c4001c0f08010f6068140862100b80214240100414052405001220307d42c0078140444a40d40310704a8581c0c140e400010030314100c020606140d800c049021b03090700d01026100041440851001550030141c80d44100d07071400b40010140566544404100010482101402010096071b600504500740901c450000c03c48a1000900741e41e1091002004080f81e210040003807800080d82c13501c139580200d080c0f501560918030100c2d16820120005540f1411010207014650443d5080111210407015100d0420088050000c0700040a20485000e100e15454081506161142d5800c80800c8244054141403030710740701c00d0110390054075507034a100d0784 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 234644874 1250 234643624 234643657
    0x901030b0601120c020a140607140d020915031e09030909040303020f0309012a051e0919030b10052107080f0304090501050603011a0a0201020d1a0f060f 67
    0x4041c0121846146401502c3c0564144440e030203d09030003003401d0b1003440c000e0b6505550604132926995039120269001c0b40013907040c0d00c0350004240e800d0050800c1c0b9140000c050300e44079400000a40e1a40c0110340c406e400180082030001104840800760a0f070345001a4000d80c0b49170401c13441c0e8403406040c00080c00f031440c200c00501014800d034103c410381e1541c0340015850b81801e0303843c1030081c201c0c00e540301a4450f9820011021454080f00b06034000c200390394039480d280b4203405121070040b47c40702501c05081e0070300c4502150380d14070b01e055490b15001031381c0d00e403124614245400400006802c0d0354086007156000c0c0b0007074039170441103018942000803c40744050b00e506860714095595020013030134025201d220140e11008001041120039102c800c0c44140d80303031020071825101c20701c2000c1c012482d40c1c00302d01165040c60058039580605000060412001c04000b505030f40340740840d07410b03144980742140c03094584074000010304042528043e00300b1f00241c400713035510303c60511f43d045003510 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 234646124 1250 234644874 234644881
    0xe120f0c030d110d0f0e0d03020708040510050d051005091f03050f03040303090e060d0b090a060f0207050d080412032409051008010c05030c0a0c050609030307030b01030504020901030b 81
    0xc108115915a40c406070300700941044500c2c188040e82020090b030311070a003400d900c81c00400140c00360810381e00034080030704420b450314201034009505c41d1100701e81c5a00140f02c001841e9851190a464a00b45515190360301c0b5100e0030317010200c44009103442080340c030000c000d200e20b44580d01481e130b101270f042c003410442083e41c101146d941615684010100d201c0c10601d280260008009801101d10a803107000b40d4a844180c1124482c43c1101c0d031a42010107000e40d41e011845d800e0101760000016401d441031081640c5421302030310040d1100900d60391300050300c0010060b007080385824980180c50f088410b801c05548099000b00c1d207100c00c20800d901d524602e003154000c2301055213004078544d0200b00240d0f903072424502900c42214003a2031a041d03100002400c21060040c40004105030f40c6603465640c440009040c0b90b0005500c0c002080007000c000e00004038200700d140d009100b600000d6440349404400107080e0703980004414101400c00c002c1c840141c40b2842d255040d41d03401814003125a8 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 234647374 1250 234646124 234646147
    0x3100e030703030207140d11070501020c03060a02072f100318060e01020f030411040b0603100b1b10050406050618060d020316031101081b03070311040b04060905040e120f 75
    0x1903a50901c1c0030316000e88040840e90a4000c07110030501c0230f140b8180e80c0c0342d613034032001a61a045000f805940540041c800110035048543c01864060702c1040040c00303d4519010325200340744051201d00824060803002241d52904284180064003107180c14401d0f40154548009036060620009094a44401c40c9500581080d01a03c02c40090a50095164601424000b115880440c14140034910f40318094a2a00b49031040b203100d080107100101c0c42d01d1a2509900c143e5100500010451f581c0ea6000001a0001d1103401c5504852250102d220305003404e10b04100c03440540101c0c8104090361070560070f101c0b042003103070340030500b01c1381e60040d00f0681c00480c0c281040c2280e890580050034002008000383c85d00c00b00c008000a913038800c001e070354409845000140303042e40d002d07030000b0610000d06034500c00d03000444402c201c60034a40c10581d5075294400d80d81c206401032008101c6500c0c090199082910412a0b004100c10050408103815803042030300d031190070284840031314001003520721395 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 234648624 1250 234647374 234647393
    0x702070f0911190e04090b0402130606080c03060a0e18010b03031809090c0a081b04021624020d0c03050606070b0402010c1a0109020c10060503070620010e0c03100e030703030207 78
    0x1008041c0042c400e0020f60319000100000c121010ac0c4503500f4030a014483c40028810300d020b9a226440c1c9241c9030711a940c464003036400003410b40764400901240403854100340a03a43d400b681d07204003068a9064031941042c2524060031403240241d005100c0c070341d15044040000160203009441c180100d07203820b1001400d0503800c0c0c03011600000c203013000044100740014205240c40303007030f0040001038802000b044160b00c280800400b040303c01411040201e44c8600c050707402043c40a02406507441d401e00e282050b80c104d003182030307a440e6880d00c9000d01950035000f90380d40400300300c1d09030b440c0c40c1d01c030780c0d0f013003a00200584040c1c1000204041681000920076088003e042c04c0244441c2c1d66a540045401a521800c00d00109000322024100c006540b8000c44080d510001d014018131781c1480d40803100c040c0100c1c000d401a02403000c4a2a1650082c45a40210783e505005030189407001c80034140b501058107142c0c1d41c2140381c413041c0003070b201010040d903d10ba07505103030250382c8181710704020552 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 234649874 1250 234648624 234648647
    0x9050c031606050a09090e0313060201020301030b010509152d061908130f0f020a050105121603090605161814090705070510060e060a030218130b0702070f091119 71
    0x80a01c1c0c04c080c00f087d450000080c100c0d03550b0320b5540c1403000f5101d40c0224241d000c20310005140f54052001032045250450096034414403201c1c01109031500d4400041070342a00c80d811a100c0c10240c84a110f0000510162240402e0140c41640c508090304060303070184240310302040104190381d0086010101a00704100103d50051440000e01d8200d06245444442c034105c12480b400c141c6c0c100250039400303802a20751010030070115402c20b50b1021554600c82035808070704002c065840c00c02500052992003202c1c0500b143c10306820041070315120107040c2c000c5298011203c100050402c00114034401800e203000001520444040d4503110000d9400e4025841c0050060081c0c00c450341a110b0346038000400c881c1c44e503028a1340c03a180c8070103015011540b4017010f904406c6040810317a004a020b02e40c82c0d00b003040c4078030801c800d07252900c0c0c800c50f040301541c0f24801030704180810001507806e030030322001816032250200f00a95500b10103108900c0b81d10640040558103031841c0b10601c2c06804038002 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 234651124 1250 234649874 234649889
    0xb0405070329070806030c19180218030c0d061a18060a09020a09050f15070305040e07020c010e0904140106090606091502120304050c0a030609050c031606050a09 71
    0x100000202010042e42c0c5402024451140102d0000d20001c2c841d00020f4000c0788060058403204021348140099082c0c1041c0744c00301101202c1f000201c0d03c0380f441c1d005241c019076280c016205d0300000d032041a904046607030b42c0c1c0300782d00108100d0495950704007060300c55070707200d0720000e14008001d51140d030803d40301d02c0c15503011801032054040880001c0d82c1030703c94032049442220050300c0341c0b00c00c4200d000f00c80e05440001c03c2da02084c40700d414480200643d03c44010321b02c00280195038100e08003030340300304800c400164000c00d041242c03140003070304260806003030300280c030304607a84000003060001c0c0014a148614500300124051040d48000100700000d008000e214141d00c5410340c00c0034014620034500003c0803d18000b46041d602608041500501d40c00742901c00d40c42001d2403065040904140c56030300503990340705000d035910a040c00003503204a1000c1401d04184c18000d007403904402001d40203070040300e001d102c3e9440443c000029140c01d0b09006445688121040b660b00416400044 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 234652374 1250 234651124 234651143
    0xc051e061c05090a031d010201090c120201021002030928150608070f2405040902030f0a0f0b0102100c0309061104030b0705040b030c1b0d0c050111040302010c0b04050703 75
    0x150901c4198801c030355440700400d001d6a141c1d060301d01e60740c00340c0d07010260000384c00c1c46d800d031a90701182c0c9200b9003040e0144008261410075489034660480300c1d622008464011065000031560113210074546200075000460542c0381500e2029103c0083c0c41c08801307410085294000c201d6070040346850302941001c50910710401300708c1003d0080503c1d0003901c1940c403032160006203543c1456400b030103884400500c0f14000da180302001e03081c0000200c00c4400c0c03010500010403040e40b544003a500c84c80c0c40c0e03445a141410802021400c071022102c00d48007103400d0040701d52040c3d0300040c0e602070901c02d00c14001464070082d00c1c00c81c010240004010403480c00c1013070784010031208034042e0007541d000f01040001c5440b41076003550300f4840e03881142c008140c18800200c018003100d015099030702c4403440c00c000212031008074030304001005401c0f0010030000440241400400d00c103107480d020450420794502815900084c08803068000014060281d1400140402a0910409000310360120011 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 234653624 1250 234652374 234652387
    0x50901053105060f1602030c130209040f06060c1113090812090303060a06050d021312031218140f1203090c0109061205100b18040b04090c051e06 64
    0x9903084149204a1050107804122443c2c0f88046440040003030100710b240084600c0840780501d50791405030f034035006000100e00c2c5503d655880c8850700036490030040c0c0d6030410f40100700c2181c6091301301c0e0700010b00e4141c0c1070210b2600098280c0c0c03655001015054003c07089000200e984034401400c421040c1000c5910040100103005030204450360900b401311540da03001ca103652070204a59155004000950802503a8020310007865040c1042c1005440c10700d212660301c603018010340c0b144070240702040302c100500d940040307104118089540240405110300d541040303110801c15001d0104d41d2124090381c4040000c2101ca000e04138440300b581d90300041c001e0b02051507081124207032924003400c0c11202071503100308803190659107c0e40300c041d1138114005003803006010080c212074582c0c07000c00000c200300070210064100801c05101d8241102c40c1c040c1031109a0b994952624017907070401c00c0c00e100048014030400700390f91054601c00403004519440790510341a00851907042040010103 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 234654874 1250 234653624 234653677
    0x8190b04020409020a0e040905060f1909030c052e0c09120303060e090d05161a16021002030c0406030924090212031c0c0e09090105040506010618050105090105 70
    0x10b801c0a03017090301c2d140c2101e4803140900040d40c20300c40c4e00501c260099000180c0c0074410071611500200551617418050051511180031101ca024041e808a05000f24076000c00004011504900b680300510b080c0300c01c152144118580e10a01480045030303128001003090501c5071a0200003004180840720391943c02c0c0c1000350060400f8000c403840e1070300303079000103210190025011482e50f00942e50549040e010b4130ae1900b8140204504907230f40500c490894221307521110805010303c808005c6000c00007a500b801a15001030800003d6606006000704509081c10070103a908a84160401207544600c601d0208000c01010346024440510807a007540c250344960304c1020003e2007642c250003071081011340d0f10358900030241e0f1640100c48100c2c4401810b910fa400c80c1680d849a81029403115a1860000d618604100e0341440e0680d50b600030003007071180c104242c80c01004203080c810290302c844440109041c616000b6681403100002c0d4a18039a480f810886404001c000096407800008251 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 234656124 1250 234654874 234654877
    0x204030b01051011060c0313020d031106130b0c0304140d0c020a0605030f061e130b0a06080c191e0e03010e0127020d050307050303010905100608190b0402040902 71
    0xa594001d1202401c00c40d0f601c1c1c012401004415081e000505850b075030355000ba19141d20041441540c1085840300700016240d6080e03881340c491294035507508012804218929040d4002c00d08030844605070f0242000c01c9858140c0c40c0c1141403d4042940d079500d60500980e60702819000700030b144180d0000c02c524950098540b680c0f18400c481c0c0707c042c1581d606041320580810f0351403003255034008002c51800e1400c21081c120340da2701450806e240c03040030000201240842d9268003441ea4448060500910b06588001c016241d00c0c103000c007081c03c1c00b4100044a00411400b1441303007a1486000402d580070303620509503101e0103000b040341d1410390400140101c105414042c065802c08090b40c14248041c083c42c218110284a0020307403c826030480c0e00c101007282400c2e03800540b450b86403004508240300404040740180c004507035952500c4c0e4480700320b41008102d401c0c80d803001032061064643c0310040b15081440381d03621074240807000c5d00301001018041880d41d4810320000300080c10418a40 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 234657374 1250 234656124 234656129
    0x30301150e0915040e0a05070b0901081f03030f181203121b030b0604081002030609070903020d02270f010602011d030405060a180308071e15051503010204030b01 71
    0x1540c6000003030749902071000340c510540303a040311040706a940c1d00340b0381440d40c0144602c4080c0c8049910920190b2580c908084642c1c014030070400b4001441031035560440c88031900f2104010306000074082c180c2900c4d4901d0350a0000604014200b1549013100d0310079401d07801d50100000c840c11546a645007000da59000a100880200784507040d40441042c0364440d070550b030407080d1100304047e409e03604e089004240300c070031451b0722150078800420f0b0043c1c00c01506100c042c0c000c0005990342802010098000b400420000400c11100010300c010b0321021403070501164151402030b071280617603002483e07220f0242c0d41f08555031225410090842e5014070681d040320109d80080205201d010700c1240302ca085210b19104682c82084100458141a0001c090b003610901d80484501c2054006c1e0a03580c0c200d42c42515900700100e942002d0040315800086c5101800303007522403004142d50f6801d148014800c0d9024a5079031080010031070b4070715581640700c50070010700071542d0315220300e02922000350a0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 234658624 1250 234657374 234657377
    0x3200a0b120a0b0301051003081b010608060a060b0a0e13020702030a061d0c090c070303060513060603050a0209091f050d030c0c060e0d1103010b10030504051b0f010302090303090303030115 83
    0x3d02e88200d2801c040c4aa1341c05212000b089150ba2400c5072038140841d40285107241144104582e2903545140030f00c2500054880c00b8040c2265081170000182036485640010440c41010030074242003a401500b810706658060707030412048204207080308000c0c042c828002e5014011300f004c410400c03401e0307400044241c4a001c02400b01810005500350758040d10400f041c1c1011009010508003c010805000118030030721300807600b551103102213840800480d003403c03441c0382c91b0300d0140711301d98050207910f42c040c5400c501141010460310004158100240642071400403194040c24018031b130390085005040058082c003a6030030645802030036400752074401d8800005000e4081034440c440c59542d280c0707000080500d0f840c030000b616031040158000c0451a2b041d983c40558000c02d88898a80f03109850f110b4a0000315458141030550824424440d9140c44c1020b64480900c2d6039918580c10400460078a001038940c0912408a859485504402070385880044000a255400039440e070100380030f44d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 234659874 1250 234658624 234658631
    0xa030b03030442020a150902030a03080115031103070e1239030606100306081507120b150f070c080c030d030209010905010f05090405040311010c020703200a0b120a 72
    0x4a16450582000c3c80840380058001002c0c0b2004525082203003141010b03070a01c0007030a00782640c0000e250070080c41c0b085010841ea0001080018480c0700f901c80032a84d14103041c84640c90010170341015200c010022401e1000240d60101a0f0301c03142403c0507540c1c40c0700c0807101d070600c0161035910740341c03042003c5100040e910030318411010411070300e4000140000e0014140c1d51a48002c11032440a4030080c2c404156440f0340c0000c0341401044000034086403400c05030014100280700a202da1040790403070512038180401014941c43e00c00b40c081c0b84400301625141c40300c054848040507446241f070054201c0e107a0160104424202180d80d045000c001c504132030012001a0042d41640501c4000602086100700300304030303550240300211a04040b49c07a08034505108040090110354090b03500b80c0005d440d22014180e038000912625018113a13300050180e2440d42d540c94005050340c10107031020131824031a030102a140c4404920107131000e030050703079210440000c40c040d200d4411241e11880d00e04 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 234661124 1250 234659874 234659969
    0xf0c031a040b03100e030f0d14011e0303081515090a08070e060f0d060e0a2604031101020304050d030e09060607080d051b04092c030a030b030304 64
    0x30075220710181d190b40500030b4000101c611400304010301c2d03010942c0250317010802103541d0009003100200110002c814000800c0f080e28641c1051400c01600301c0c140300d00c80d030200e040301c03084244e0008045a1781407804c0803185ea152900300b1440002019116000194081001003240c0b51101808039614196102c2614565500e1348a80d629071600c140810fa441c02c3c0080f401e181003414014840c0352016000030368400c150350391102110549107020450b030704410a80da0820030038020b850f0103440030688141d1510312141190f80944110300c0000d00b1610780b45165640d40e402403003034400400740184140e1402c41141000360140003131b24070700c034030a80c6440c000420b5031900c1d00c1954105500201e090741800344843d18080240340140a03d241b0059130010365100120354002440600203030000031401005481e100810500104441c180e0031840c0e110f04201020000f064500c0c05240f40380c041070704240c140110342544240e4002ea20071a9a44000d109005952011000c0980e0240b005417440b84 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 234662374 1250 234661124 234661129
    0x61707020c060a030b01030b150d050f06031902030708060f010905060301060308041203170910060b09060306010813051204060807030b03071806080609011e0b091303030f0c031a 78
    0xd50105000b588800d0a10418042602c80c2c0d0090072030a03010306000945c1b812030400100c4802000c114104140300000c2c0303603c81001180034064000380403410036165801c24000190304e0f0344116032000d4a80c442c60890781d040d540c0030001040102401c1c0242c51080c04d101e0881c168560090189104031828500030960ba414144108000c603500190454101810007180300f1205805071815800c00c10342c20011404111480302c06070060b03042c50f0041c0252012010702d94152001c50340030040c01002440800200d840d4803003201d901040134030f8915140d6840400d888a00e11903802c02600700e115078441001c050300d01900a10a551b03007501c0c2c048259a440900703c080c0c0f042881d81e15050b40000034200005c1007074a00d4000170129a020104031340d600e440030305140900489040c6800c1e91140c0c035200b040c100c3c510b441745443ca800d00c0148850607401000c6107040c070010703203107010b5250b60a0f1541d0905100c0d9004c401c03c4100040d0600c5410300d00e030401009070020031566903e07025040900d610300d1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 234663624 1250 234662374 234662383
    0x3070f02070602030a121b030209030d0806150c0703061404060614031c021e010212100e0c07030c060f050712090506010e044704021c03030f0606170702 67
    0x540b56680103524000003204e0031545040c03002a01480e0545030136990144071000d07101022008030303603540140c030703460281d04061800010824002c01d000ca00d109201544c0c0305c00d048607242115020920381e40d00c500c200000e00d80f09050340003402c0d4602d00b03100100c2d000c2402440902960050760117110039a100d015610602e408030307101d140e0591102030603204484001e032a2281d41710450040c0c58041c1c4107170765405c94003050305d07507180466540001c0300b14601c40b851024070740003900c1c040c0044601342021048540c07001301401685e035181d00808c402003010b00c42c0c18030300e4200e9404042403148408510304070010300000d4502c8408112000b03000f4402d5250f40c070801040e40d820a000b0900c1d6464054014015840907005840f000211502d0b1402400540c1007031803620010042d40072040407400b4400c10a92400b510000b074901c01109002c05a0347e001040c0320340b03003414210000240400d03d020381c01044108202e0030a9030a010b00040c145412800407681025619010354030b580c0c0c0c10004070303144d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 234664874 1250 234663624 234663629
    0x10801050609090c100216090212100303021906110d0209010f050c0d0e030f0a0b1911041412190302060a0c0f0c1505010e07031419150e040803070f0207 67
    0x120740c0400040e80d03561411450010b0710b8101030055407d8100d012440d50250302003a0002043c0c25000541da1800000c001100b076804142008201c07030075400c1d568000c1d200c584a90b2860a4502c08034940420b2210603032005000d07994070340686589400203501d40019401c85826103011501c4903d42c82c40150090040703403949052079000e88075400132160141d80c0c40010304010707905881041150303000d45030100128503403240107110b40501d40c03a001c241a070304039040c03100b500c2803d400c1550340440c242400d01030f0350940d9192500300c0500e120b1140410700d030600c1003184000500c645400e0408200782d420320a40707074500070380c00c0d200140e4498081d103051b00c107061911000180c1543c41444107600c5100362010484c0300f1000748940342c400001003010b4900c01c0c0c0102014040c141d050004990301840703100d00507448100340d4451032500388040200310498140d003611960312085400221031546982c8800f90502200070203540c1270501340071032690000c0340c1c1180400d0801c038106540d40d000103544002c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 234666124 1250 234664874 234664891
    0x412020d08100510030b030609210c030a030f0906060e060a0603020f0307030c0c0827030a32010e070e01050603010e0114120105041a0a0b01050f0a111005010801050609 74
    0x1903d10f448240200c0750801c410f00c0c03080590300d4000501c80da40900c200ca0085185070f00901902c142c000c590340c8040395110701c49500700c20800075141140004026101c640200e0705002882240290300800030b0100294000e11143c0b0300600401c00308418003840b070044006503250f55001f41c4540e403d80480c8030f40302080380e0007202800010b849a1180e04a080920540e241c091301422065982405540203001c540300b014004041458100042c1c1403080845202140103180542581e120549150b000199407410480c10307041ea180303034401282c0c030006101c4090b40200680c60303003081016240d606034000c1c1e003e0268410000905480c001c0d050764141c0b14030300c3e60b8440b56440c01207540100c21b1002125a041218070300d02d10140c10003803080f50b205901032107a415500745410340500c8003020090203214198a065144070060746c3c450306032200c45604991991b0740301400d80c01620350b220710030444041403150084903982105c0e00d8101904903031807100203015a4582500b04a90010101c80000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 234667374 1250 234666124 234666151
    0x905010f020403020102100f02040e1014060f18190308180307030308150a1802030411010912030806030304090203091e0106060f0e040f18110d020306040f030509090412020d08 77
    0x218021f2140d40003941c0035002c0d4000501c1d041d9070700415400c0f003108a0303202c82201429142006038bc0141000c003440c000d8110341c5545007000c05c0110740030f54001d0325078840c10210000480c25590b100e0400441000c0c041406213180242d4a00d4840c07020361080c1d2600e428030880c00300082c041e040001700281070742d03856144c1e07503055500d00c80d0b1081d01d00c200b038503050703406140e0740000038041a5171100005490440880541d4a203001d0400c2c030800c00e100d9080d40e0400035a0907041100d0300c054001c0341b020f01d5162818a0b41ca40320b150000e03103180119000720102510020a210003200002058501102e194600080801032908428201d965900c00c200104040101400c601e40c0b14036039000016100500024450402104410448500104800c4c0c0c20403030710707101814001024011040040101d6902c0e04404259000c07940b80e0300302070401422600c1c0040050304246c020b90aa81108401030301c0584035241500f00742c0302020704c07250740c240540200c40ca4812618810311580e4803440c0e0f09029407 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 234668624 1250 234667374 234667393
    0x90e07020a030503130c23010c170c0a06050112050d05130b360f09100b03040f0b0702030d060b0315011b17090f06031608040f020d0302010905010f020403020102 71
    0x3d403119070008100c0d00c82c100c01c4902c10000100180c000130f016021400081e0ba0419030301e2000c1c42084980b9003075078141720072041c01c000024030080c040e0400c4108203800d561501d003006201c034075050400000802c0b01e8100000402c1c401284848080381e18050000c0310f5205078456000c0d01e052140c40f000d03403000307072200f0018045000504000c0c880301c0b404280155484811141d4211481e000d034080140b0341c03217010114115843c2c401003190006404482e281e0683c100030001c541c00418078031500d10742d0030011002906100c00015a0614260828200d00c410300d000740e4003d40301d9108020040c0968506100031800c5400142034070b00c0340e641c500e0103e100741d500c08015510f6912810390050300841896490380080e10394134000d61044290700510f9120a28602000200e1206074101c0d4040e050038010422504000032003003040d0605810700e0440c6444030b0400c545200c04d105006500715407280081020140d0543c81039080300c0c084d00081014841c0c80504800380d12552101030b00507071041520 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 234669874 1250 234668624 234668627
    0x1d0601090506060705010905060a15060e0907140c0d080a0204060215090102041823040203032b050f0f01050901120201200a14070f03080417010f051501090e07020a03 73
    0x1182c2100d002050541000d4039075940074259091a0000c4603140c00000c14020280742a0280301c42200c80343e1003c1c503d860a2810042a08001179042e900c1072481d4030200705124051034070785017000d100c0d050703141c0c1c3c81c1240140280d50b140706101000000b0039040c002260060503100362001d498243e4040c014401c0017480142c400d02018119200030b5508100000304000c0145000e02441081c072004079103c0510600030b569441039004564050118008101c01a5804400c80d000c81c1e299440000320b4041910b040f01c7c002c004c200c0c41030207403842c1c5014041d5164560502c3c5210b010a1011050260788520a11207620028410354803050b03000c005c007000641c0500c85110760802641250031600c150303c00790902d4620818800c3e0381210000c4881e0302d00c1101404110081c2500c000e1800e00b1502e590b81d1048140b20303621030900e0030882c8105621400100303400164000a503aa030a020509001100230a1240620412404154030410000d0821000712a00303206a40c25005800c0110b841c0d2070 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 234671124 1250 234669874 234669881
    0x412060f0f1103070f091a09030f0f07051309030806060c0106050d060b09130206040b090d0f03081806070e060a030e0d0801180908030408070317010b0d0524010e0f120a03031d060109 80
    0x19507250040d0ae03005135816401300880481000181d0003400d51070300d05020700c260641813541310154130b410304000c180803076000350703605070840e81c103440403660745400a283d140100400e03044158081c96406582062280301e801c035400c1c45004803074401c06c58440d0807415448410112303009410410030300c002c006001068000d44020580542a90020b90203680c94541302115160210b001c10000000d2002c0007030f400301d00c1c41c00c8160b9540240042e007030144019044c50502c4a05511503000061000801c2d440b940020300c02070f901c14211390fa0b0341c0142c64050b104000c00d00600821076680c048401ea030003d81d0056181c4150041e0005207103403690780710036410b9446540700380e05015031406040e40d84502c80480b640209004001c403a00c1e04c0580075114103031000900500300140c0d22200f0883c4042164006030744040090130088064409100422040d400b0070210942c04a0390000300a08050041000441d0520980d010880c40b01041e01901c00c00948505186440c0e22140050180325035651 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 234672374 1250 234671124 234671137
    0x1908180604031d060301230a06020718020f1b010c2a080705030406050a0e0d050c010c031407080c070503070f0b160b04030518060412060f0f1103070f091a 68
    0x2000c1c580c0403c00e10002c9071440c1c4c002c1e400040000031881c51030317141e0b50180821203c07400003214074100c06464804025900d40c0d80340a090117a8200300401040590294116084080d0052180361156900c040400c2506000092030b040c9500b4200c01c058424824103101e005160825200b01181d0740d841403020b0a906400c0d41229114010440c0710049142040030380300520984e52101ea0300c0c0390304000107001000d01406d0038000c4c10845401c0000a0010880b280c080c202860014812091410700f1251451021070305840c070f0000084190a101e01100103040340e84a00003103440b00c0c0d80e24030505a80381c82c64480c00c940524000018013007500103d005145440c4c807894170784079480161320707480e00030481034034100e010540001d885100e072910118903050351002129a40d06041c5441c004440c4a5000e0720000d00041d0f40e5a0040c00c4111145d1204040060100007041010b0034580e10f01d0b184e51090b5260004100a02201c810841c46040ca00059803030f5030b96103003102201451115070b1a081034 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 234673624 1250 234672374 234672407
    0xc18070f0804060b0306011512020708030105040f1b09030203120309061b09030625030908031815040605010f0e090c0d060b040e07180b1008100b190818060403 70
    0xd0b240104c0d20b69081001300d02a08850a04040c19400d201001d01112040103e180c03a203070045c402c00000c11440c0003503a04403041aa00490400512040400100b50050f001da9540d00f0102001080980c04040d2341c05903031013a011101f000560b030101e0b4000d4001150301c111181c4c481070025200000c40565510180b4620f600301d8201400e0300006030900404540300321881c03000b50110b130003080100741807009621081c1020409040640c81ea111607220007482c2c440802e03840c003001560301c107041014442100c882c0341000308034142841c00e100609800e1282d030b485680700460204580510031207103401528040c0040080e0b1a0600c18480f440d0910036094840507a03562110395180c03114016030000c45405806014041e06007030100500c95551105001d009181a4085d00a5104c0f01b806004103845800c0040065581c0ca125040c02861600140c0100502141c4499005024034402503a1802c2d43c85102003a80c81102000031841c40148940c010b038001c5012601080c0100b081403504800c1 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 234674874 1250 234673624 234673631
    0x7020604080d081902030f0103030503060f03070b090102010506031b240a0c02120a0b040204050604060b07050c0a0e0f07030e0709060b070203070909020a15021005090c18070f080406 80
    0xd0703001c9941403090740c6540b040400c0340142080000d12110700d40f1409a5400c050450450610882502c00c10702c0500004040c0311000002c00c54595a09916100d248401000c403480c0b00c0e10b0302117165064201c6040706015608103000708100e850007040c12841003051241c100701d54441e00d42000103810818465402d00780c2ca0360001654807100b403004111000c03594803001c5202d052841409078012400703407c00e049401a0414000040910340900d4000d50100c3e00803c0540340c450001d0002c141551004054140004140040001c0840d41e204051000c0301c8465a0b9582c07820514050303a070480c0c84a1034400d1620000b043d550007035100d000c80c0160001212562030f00c40508400305c44070350300064249138021805900710b1404000701c0c1c014202104c0140002e15641e8081094149035000300d10a000c1000200700429208012500c0c401d46907500500560401c1d4841a4454103001c40c034602402440320a2001601d0035481c50707000300403c0e600c0f070704440f0000d0001c44a40c0c0003d03108171001c645 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 234676124 1250 234674874 234674879
    0xb01080c030d0f09030b070804030f030e07050d02060d0507180b040e07030e120d0e0106080c01050f0a020c09100305060a0b031009020111010501080d020d090302090a2d06080111070b070507020604 86
    0x1260034818414003c7d5103c210351800c160401070000040180e202080504061030015040c00102d00c3c08121101a80c100000b2005032000550300d0191004035011140b030001004400795100400a9501181050640c2059190030390382100c0d22490050440071101400469440c6200b9809401241420010b031440050341855813080d55200003041d030349035601e45180c809107903002e00c41d4000500c2c13000c1c010014101c034039001800d140281900c80a01020100da03201c1140d00070700041c210800000c00380011450003041e4000300302450b01041d00d451103503900082d030b2580c040c810341e4005000200100502060410248040c20005504034104005816901c08822090080340c3c0a46503a6018110003418468020300d000c2904107000c041200000d403c00168030758901194106d6410b1070041442c8200c490854007052121450508003143d1044182c2e101902c1d40c840c0d0b040d140140c0080c03040e001c0c600c180000c0c500407220042c041092640100d4002406880102881072014001904065 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 234677374 1250 234676124 234676133
    0x203151309060507030b030d110705210304080a030e030c09011505070812060f06120a11071a090d141213080403060902010801060f0e0f0109090e0304030b01080c030d0f0903 76
    0xf8010390764140440d0b00c945001c48103180a00c041d4a02801c14584070242e40c0c2c1d81041686e03681c51a00c240b9000700408948086441c4042c0301303000c1c0c40d03000001143d5076a9a15165641e596500030130540019066503400d20252502081c0c090090b14000d0440015900700305034000a055407003440c0301807003000c00c8171200054509001d00381400040d544914603180c110203011440100300b00940c4240c004110030214031614040c4240c1040050320001036611035600d51140303620640c50060306990303115400e4046090f910000f1171045140d2402d440f500d003103e0009603146030b0040702941d4079070003d110500c841c4e80740d0098664040d0018040030016181e03900d80d1042948560400d80d0126103071049141503503000050b290040125203080e640a40e254a00100308120480725148507001f040f0128410341e2040540310040d1020b280104123540d0304500d101c0c2e60b94030511046442c05003420000404035404298840d1040000d4003600c0780c5002610308540003d548001c4c40f0034081101d4022002c41d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 234678624 1250 234677374 234677381
    0x60f111f020903070801060312120b0d050d030e030a0203070219030614040b0c0a091421030a140c03030f07050403050d050702011101150b1c050c0403020a09020315130906 75
    0x10a03050300c010b82e24003280c028141450641c0e0000d04032681004400c01c000350000c090f01104070540c1c649801e9884c000c81001c4081c0001d25840342d406100c0a20f603905224001c1011000d00b03445440402904514411041d00c0e8002c0c01c200101503082071000502504000121400501c0102195004140c4940d905004c0340c809800040000107540c04000c01c00016691103504488054002424403c114100402c428a01d010b210542c00341618810000e44501554a8078142c40c200d100d0701444070608540d6a80d00300d031085c5400078640c0300120060700c0b04a0211042c641400001c2d518540d01c80082003c0c401024003180104442003000201141d014451514120400d0392020340e0b41c4850700005007105045140c0e64200e0345480c0d030305611100b040411a00300c40d0755401964a8903488800414180703400c0c1d004d040014106810840c40e03415000c001d0050342e101702c0314804060345a49030384041b4001142c0124040300400c0c4040c25510f403080c0188040881c0ea000812211060383c0c0f8202034 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 234679874 1250 234678624 234678673
    0x60d0e0f0607050a02060106181503020915030a0c1806031e11040f090213031104020f04080f0712080909060d050a0c090b030a0f0f0204061e0501030510060f11 70
    0x4030f010410801c030650520001d0b00400341c0c2d1070014030640094132902c004140b14813404002d0b2120075605030f0b416000760151540184000c00d000c3c288208640003e0b0746074002c450f9610300d01d143c4454a49000d0090b0140e10807066a0752034081c0f51410008268014403800d03105164900340c080c03185d8101280f034004c0030b0240c08001f40c0944c903145030400306850000715070441c0c074080d030040c040c20038102c00c00150f1404998000780310303283d00c003018408500284141d100160003e0360010340410070440004140111512040071182043c1d42d800c0c03002400a15224001c00c403a03030030040c100c0640b920504260704483c00429015034035130555070340f5103072200198084500f00080d00c82000815124440d910551100358040c00380c41c2c0107a594100d400d00c614000804904c4002c080304d05544540e03002c0000b0341081c040d0000144c500c504a8901080d07540700702800a4280b00008214014a410311011942241c44400901d1005013040da01207803c94108100762064503070340c0d2381e00300c040d0b45a4000d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 234681124 1250 234679874 234679877
    0x8240901080123040809090a0b0a030606081002121f0b220602010e120304060f020a050d1b0905270c130509010303020c060c0c09011404150302060d0e0f0607 69
    0x10052020030188100f4081500a41c0c0c81c0050803041101181c0c8803c1205e2448000700c1c1d02e50083d81d64041c070040280040542181c0218159601004000e9546d00c00340954072102c1c2215404050004298182d110b11103402c654a1480004249030360340300343d0309841a03003551010000490b16000841525007103000e00d500d00078030b031020700c1364031207001402c09026040c42c0c03009000c1401000300250795080150400c0541e501d0000004050164503400b0450100b410103040d0740d201d07000d8034000c026411034015020700500d020140c1d2118a040c00744c46015241c1501d421409030700e88010410352415800c6800d0408a498244021401d40b01e02d0241c030038207965810300d440d588480c141c0340c2d03050151703084a8044c0b20200018400720350002002000407004540295640c0c0144411500b84117180211a0f0090200303c00450826400010009a03200a03074082000ca02c1c4054102c920904911000c0c0d0030102c2001254490f00f02038100c00d11250381e050407208500d0100d070910786001e004854400 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 234682374 1250 234681124 234681131
    0x21e0304030e010206090601060516060212040b0f0609060d030315031b0f030b0604020306060403050106030609300e03031e040e2503180605040c030b0601020d082409010801 76
    0x201904001c1c064030542c1e0070310040103540f5043d00115500d06041c0100401d111000c204039a6801d00c0501e41200b040e404030741903440311204052a010701106030380403254010f0107400948000230410308280320b01d030001c102602d1501d64006004003980703101343c10741c2011b0f1906210819806840c0d81400194802c03080342204005032080034503121110f40100e10103041903002040420000b071006600720000321001a40c036191500000d10078400c1e544014155420010008203214403540902c1c581030007542c82c036180640060f0212100c052400b40050011104030300c080e15281304003a65000908040d04892503c00ea030b042c4a1540452051600c140b084000381c20311900c0d0108200d03507000b080d604d00c980410380d41400211201d201e0241c8860030541d0355803050444116455120a040d40c004c0d8040144d41440d00304201c06000324041502c0401c12540803606951000654819050856030340e400c0030707250b034491100c4544105d8100454804070f0101140540c0d98140c0fa2802010141c0000 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 234683624 1250 234682374 234682381
    0x1050412120e03010c1d010e030d0306090b0a03151509020f041e030f08090102030403080a050d060e0601120b030a0206030115091a030f100b030c0903010e0102031018021e03 76
    0x4100e580042c01907802641841c11640042e81c218000b62820103003c02003da200d440e020040f18004001112581c1c14816040b83c0864660154804801c0d5040082c0c03d001d40c651a078248001141d40303200c006e180914864455000400035840071740d02ca10001c880c01d05080d9203101d29416604a00041285080006030400031501d081400300c0464203084210541146140c6480600c10b45050b0080c00c0071078001070b81d65981e2710070301c2102c002e95403014030143c43e00b000203001849034201e039076482c0f055440c001000c502034900c201d09602ca00b2050b5240004280042000409024401082c640501c00d1500b0400180c0e00c01c80a1406005000c90f80001160000c600902c40c03805580700c141400c0b0000516144040080116940416840c00e280c0c8141c07a88083d264818000b603002404c00c50010003440b10b8040e181006040042003200203001605145680508030b12080d82d041030745030b202c4402005594207100f018109090030304001824162003034603001504140c52141d0907192400000c1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 234684874 1250 234683624 234683627
    0x10140a050a2112110705040b0d020d0303020d02120402101e050c01020f0c0c15030c03060f120708060a0c0e0a0302190e0f01170a02031e0708070e0f0115120b0105041212 74
    0x5c2c004100031178050100c00c2d0458007081005112101c064002c1c0032050a0380285402a011145560054013086640b2480320b2a0042320341c0301964103d02c220003d0207644c400380d10078103000a0000020440d54030341e0610780c8041d60300b54030688201481d035401703020980039000c02c0c4000d44500a054000703450510000300402070703542e04000403005806d40c240148801c0c0083c09094950001040c1c0310120f8000c0d4020000d4140316491030140713114881d404012404010220b01a4021407011500b07201e840500402a25606d40d0b09013541d0708030740103c504001502d4000c909485182c1c48030800242c503074031401d4020450310304440c1c50814055680040046030200101000a040c100001e060300c484a0b900107510b680e480d603610000318815841e03d1011400a1081c0f6000300100740860303190303641d02c01003600c0e800030031503008500c00001000001e4040c2d0000070b81c0f40151b510780d10903242150281d1600020404416070034104031090002141c0b4084030f1890186c1c003400394404001c002c030308000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 234686124 1250 234684874 234684883
    0x130609050105030f190609080d0504050a0209060a03170901051201090504050c0409020f0108060604080d02010e0c040c020613080909070e120c0d1401090b10140a050a211211 76
    0xa03400050b1711000080840c0c0c5200100c90070200d5104030082002c2c03884c2d0900034443e00810450821103840e05082c001000000075801541610a442c0d0300e010743d40d50010000000041d10014020f4405900c0c10700c0042e000380020460480141010f40c20a0080d810184950f00240c008002c02c4c2d42d541c003480706102d010091070000c3e0714111000c0c0190303412503020412050014242c50305100940e00410071540c5c034002030398003800d0365600711040d81e1600c0c0b1009000c1c00d10042e003401e844c091007202d10501e0a0500038003e4500c0660028500d84e201c0c0e1401c2e1120850709142070340c10b000140300050803541c1d001c290a008101c655612500728030790204002001108500d40034040d400000b0b0000162640028241c0c0c030303174110450040c0c0c0d4042805050142010540007000c1c13200740800c000c4180b82c0120102c00b9912202410a202d50400090020035880750240541c0303e10085401c00000c56000e2090b1410340b84134440c0e20724005140d60b501c0051022081c0640422203000b44005076400802 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 234687374 1250 234686124 234686143
    0x21051e240d1101030207020a080609030a1808071208091503010603050a06051c030c06140910091e021206010807080c0303040b0a11071205060a0b0301230613060905010503 75
    0x85020110501580e2108801200d0b028007a0503d600410141b0940d07844010041c0104006026240301e4500182817030749940c4014900c1c800b00d001000b0f00b85026480441807400e44400d40010131115041103003c015040e054141244c1c00700b000c110106407034568040a0900c50f44469655450b54109000681580c000401500d01c5d1454620100700a03903640200d240b070407907041c40d1890050f019040440d0480394481c00070303250b00e0620780004854000202c60521501d01e03642a2a1000e10500e40041994024040941401106c1c60381000c0d92940f030340d4414101d44000c10500c50302c0320390102c1c1d60400000340d010100c1d641102004114110041c0415961402c044010b9450310782008940f8082d40104c422540810403c02001c4410705020407a41c409131504c0030b60303a1078030452864550b50700c54088070180d07903131410012101d100d414140202c0c2c8034030200c190120030500300c3c03500030314801c440240910b501469580da00d040c04040c80c8240b030050501a100401d8542c10141414034002020 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 234688624 1250 234687374 234687379
    0x2808070c020306180304030b01080a110a0f05130b091915050a03080a0201020c070f060f03060e040b070219030503090c010e010503040b06060d060605070501060621051e24 75
    0x5040090040c2d8000c10000d60140c54100400300c0ba280508001e4694041ca400060840c45030300c0010800e40300010701c20603110f11030400001e0800b40f03001401010b20151284206006007402c0511081c80d02c1030a003808181800c0000520040090000b0300001d000d0354499030b107039900603480c000100d484c000d084807030b030307042100c3c8481c0d51405001c91480940c078440901240070200703243c00c081e4401e4046428441400085444041d12400c81c1d8296944511035200800d90b0000c2590701c3c1c60082c01068100e40104210407055076907034036051240c0100510f00350450080c0b030b20b0718440101d0410a8403605000b17664103512464810030940c81c000340d401c00d25051002036407080c0c1e4903030791140c01c1b2a403083d0b1102c50840e00d0307220000421790501031f20385100718079802d215012500e15881806888801c2c014402408600d035905400e48030902e4104032655800040452a003021615800c40380d0400d017114170407207000e01c050b80f515070051300c242e518142e42204403000110504440c9c0c0e2511540c8000c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 234689874 1250 234688624 234688637
    0x7030b06070c09151514030c0706061502010c031104090c020c0307061709030c0a140a08030a0906051311040b01140d0506120105070e12150901021e0405061e280807 72
    0x1000c05003091440c941b00701da81c20000000038940f903603100f003600c082d16440744051064030f444100a107980c0070009140001581ba0102c0b00a8051084c02840c4034403e1035080e4a00e001d0070102c0712030240c2441a00c0b0810761040e0f0000d581aa14200300780002410396a03207043c1801d040c0d013041c18041d40054400c401e40d500c2400749245180012610010700e5a1022401504900311440349042070700300d0202500e041404020007007401d540c0c3d017240111901c250010045a950344181d06405200c140d005804550203100c9080941015440401c520340c3c14180700d040c2c034851941c0003c10360700c4104608a026228400d1140900f020901a284219504001d001600d0141c030300800e400c1c4c603c2c09492061022000b004854801400035001144001a04844a1406021440c080e6025041140d8030315440c01c00078520750400300c150f400b5500c00030580c0d0b24001051f030309050042002a0411000c240421010382d5114914241414496004007500e42207e0017100180c80010001c0503001800308 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 234691124 1250 234689874 234689909
    0x1080c0d02030304050d0f06020406020d03180b04030503070e0603041101030c02060118090305070213090308090f030403061d031b0c040902030a03030c030e030c0a02090901020a02030307030b06070c0915 89
    0x42c04021381e026a801541c110318200860304125540c10710842c00030740aa40b0014001c20016030110f4282c405d00314a0700c09025400b201003032440d0501c0e0310040502042a0a0040380c000380c411402541c00511600d0f1565818848100007030340c03544140c41c00c86280c101001c54000950f0140100d0444950500142c0580d40c5041c001400c003a100e11031054800ba03450114104160081c030540d01e51540181031612809140344240300200302d0400103401203110000000c0702c02400141c0c00b000d030b1115002a5090529640e19280500a22032203160401c0c0600c00c04100c0302d0701040034200c81d403881c48130b00c440d041a40030b5550404145840b4107000b5410a04880007513140001c0e20350520303a15140004d1055034542080700104034201c0c02007014080042e06d051100d000040404c03406000b101c0b100340036120742d050f9078200e200b6032541030090307081880000c1905000fa400104402c40140c030062a041c1d90351b403065002d400680004c041c45a0750750003800140042100032019241c018941852a074 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 234692374 1250 234691124 234691129
    0x6061e03010e0a180807170d0f060510050906030a0905160303081501050703050a020703150f06050d0b011e09020307110f01060e310b060112061229090601080c0d02 72
    0x302c1c40003000d44a4400050400200b203424050302d01c141c0c0707021f0340c11600c42c103c0b0281000a0000c0200000307040d400c08002140e00d00d07104403600e00901d03d545603a49804010130074085142c100402814500365078111312408103000b40500c100c01107018038611141400c52401a18140c0050b04a0394400301c540f007102e01e2a40c02504035042c060700342c2409601c3e015044070880c9000480d030002440725058101009100d01c180d045a14043ca4105042c01603039150014002d07004185c150140010f1030080c01003101d461009844007000040922020b100e41d00c6000c03a4050340e10681c1c450700041d905000b48140900140140016580d5800003808010f25002c03854032842400380c4000420301d0b0b521000220408050890341d01d521055803460f4800e10641052081801e0031110f80c3e01007003601040c120031784158814030054501500040300e040388a500c5001020b401c001c0210b1030100243d200001c4600540c0e0214403030b42220707000303000703541c10921050b003410300044060340035424686060005a = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 234693624 1250 234692374 234692411
    0x10603110a0806060a090e2d0f03090f09040206040909110111030901121a0406091a06130612090218040312060b0f0d1b020601050906090405100506061e03010e0a 71
    0x46d002007002040c0d94690f003014504145856071400d5041c03a115802e01c2d84e50b02c034045034001e5a804c107070585400021400c3d80d41d80b01c1c81f07403800465100895030342024292034040310040d0410f0000d0700740e609241d19200c04004444018405485c03500360f0880303800e207542e132001b244d03c0100e075017902031401c0140490002e0005181600c2c281c550a44400c0c60b01e034030120718001e030110700100820a004c425615100b50000b026a03100c403080c840b1802000d0900750504104860f189179020005003000751610b48100c179110491440e10342960744920040e4096601d500200c0e00b0861920310300460b90603d45009881300812060300101d8906005040003c1070210040e00e0f07900c7c1d03025505030f076588414100c640007003442c41107110a200320300c0c030109281640017841c0e40c180c98040d1600a01901c1d01e400b080701038203003110005c21503801486690050342860300855000705c0058212070401d821f5500c40d40140c48100700c007460703400001c0010080700c8060404541c00c0170440908010b03803800c900c0e07111000f = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 234694874 1250 234693624 234693629
    0x1050109050108150f0303070305130602060c040b0a05120c030a0501150c03030b030c040608060f01060516020d14010609021c050411102c030d02120901030f02070203010603110a0806060a 82
    0x10800b18500c00da0161703c071851020b20140c0c00405503540c5880f14640540135070407080000e0601007503900045080c600000e03509000710704184219080c00c0ca0041c02c0700f600d521102080c0c0402c501400350120703418040314828002c0d000000c00d40d8a038502220a501103c0050b4007002c490094914500c80c0240c1000031078240c10342510700803508500f4280400e103030410101645400034982440013807000b00c0850a980030308031103042400c0ca0703680c0741c50440e02c90141e459844d1010020002160040c0f4042014001c103511403408c3d6404c1c49488001d10382120055800035940b1600042c00000000c14a54819044401c2c10010801400c080e120588440951442c04d030040c08030110950074540250f080030200a04230380c00032900136014a5080c4550044811640244180c000300720340e0340d0021034420b0741c08011000082c00d03e01800011800382039000a8500c14540c00c012010141e2000e001b008061402505800588101c007410b124007442c480d031001c0407a41107038003808425500c0c030b01351808 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 234696124 1250 234694874 234694891
    0x50103080405211b0108090609070e09100f1506140702091305030a020c011e0e0105160803040624080304030318080a030905100504060206130c0f03150501050109050108 74
    0x20164000303508095402043c0e051440d01e1082c0c002e503050842e084c029030004e00c042a600c500d40350715900021981d40c40c0903030310000190402d900a0141c00115000607a00080c01c40c1240c1065081410400481d40350a180804007503d61040b200e04a01c40c0c4c4684004003054544a507008101041d02c0809025900c0000d214030001d801051350f003609a544040c007942c01005803030b80c0390740c0c0100180d560107004000f82d0104148a15800d559580330540020505090700c2d0081c5451000d001103c465012a541c00c41c900816002000814220f00141d84541c0c4a0b600000b5154001e00510f4101110002d0b16020075004503010f00440740084252812642d240c10a9000c0c1840c84040002101c43c90300140d0241c85070740030010500d54002d860400b00c840644008500c0502600f0854141c4684c8c044e40300907034800008218200f1002c070030383c090304ac05143d40191858a4550002403400c459006076250612a0031080030f00855104503801003000742400c0f0006440c100c00078011180040c603078074 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 234697374 1250 234696124 234696139
    0xa020f0909070e0c0405150306031b060c07060216050d020307030f08120f0711010b10050d0608010e07031101020705090604020c0a080406050a1215030b1f0b091003050103080405 78
    0x115411410400321019150f620302e001114039081000e40c04c02d8100e489010310a6064020140c146840c240c00c40e4003a02028000d041441c81c1c0b03210a24002c000000c0c4d80d40c02c0582044403480700700c030900070400504000d0303010b4900c440700360048105240031508014881c8481c2040e00b40180e6000882c101207940c05551803206d143ca80c03c2c01101130245501c1d190030000c804040103003200c0b441040900c94a001e072a00f280350082c2c07003c0f2600302d40592420b20340004441c0c085a000a004001800854010400204a540d03ca980180c03c3d618012031707400e0190311040342403040001c2c05c4104c84101e5020b200805429140c1400516164000740c40603000d01d40c000b5800368241d5080c450107204980210055581d141c1d1510300412592142000300001010784416070001e10190050780c411022514410102c50f0454403400400c2d100030300301f185000f01c07038003091421024000d40c0f04014154129900d444202035030500c001512910152010186007500502c0064800d0303041d101941c0c8241c1d50369 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 234698624 1250 234697374 234697381
    0x80c0d0308090c03031b010f11030a0b0609060d060302030d05030405070905220309090f0501050f01050a05161104050106021516090801060e100b0a0c0b061f020105180a020f09 77
    0x550500083c41c80e059054040007a80010001d10071105000628205000b08544088041980119120040c0c01503001904002140c109038481c3c000301000180148043c0c58000e0a0002619a40c02030f00c003090b1a0703888107020410f52a00f880400c01054107030030400d140d49441c4d42d610703841e010540507051045503624003203880200c490300e8540c0d90008540e0040c030360340214100903203a0003c074414003100c00d05191840251040a004150403680c02502070303501103807003000565540e00310200d000c0410409020341d14200d03409041c03c006850180401040c0754000b2400d210071b89034160040025940201e010200114524440301e030700920b031050700307200c0d0346d0104030446007800390740c0c40500d40c0e60030401e01080d504c9440c0c061038010103001452240c40303a030301c0c0125840e40c00707504215004030302030319046404203080c401c0d1603902c884014408104440300848528182c4445819800181c0d034a60411104ca00e07054682d4441009080c0100790402032980018008154622840d00407102301020 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 234699874 1250 234698624 234698641
    0x1707050403060e1c0c030c060507111506010f0f08041b09020d060801320916060c020117010f03060f020c01111201060822020109030b1005010207080c0d0308 69
    0x40d28081d5511540500c06102c01903800c0d0fa81d40101944200d0307512070904040c03030650103100441003890f03141e01c480403200324a8643c3e00003810010030744403d11800d0100707444007030400e0000c14529a4032000080082c240a0001400c2c8480794072543c0511a158000441003038015006a1344680d006180230324400d80400250406030342540807958590007c203402c500c10020343c010200b0b40380118000c01100c68011a5825601844019294040309010001344118070103c4181e9001110304200c81319001512111811609564007075000038002044400c03c540e446100300b0150820324800d82c1c40c5504100080b0401102480024462999010b116440302400c1d01034641c00c6110310001c0102c6090300822252640c080c010b40c0e2034000c03207940042003440c011003440f809451144684100040401440301c0e40d04c4c07410074241d05020754401c0005c002900c0820403840755003c400058125860140061f00e04803c0340c06c0b0700159000300a000f4070903110340082e2041160507240141d00c581f600713020b = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 234701124 1250 234699874 234699877
    0x905090109061b1103070812040c08030304030527150918010806010501021c0206060f03031207050c1501031e02011106010b18060a0f0e0f0901080606010e10170705 72
    0x740104180e04005102000a41c44000403540500079250840c1003605018515140c0c818503d004100c1d1001340200b100d0110301d11507042d889841100701c240c0f4281c427000045c2c59904101da088000420014402c0840f2110443c41850841c030181692034040c0300e03900040944e217405503007040e0540c01203060222507603030380c1114584000c110f419050035615007250307a071200700c01d00031305025100b820b0343c0005150001d2900b0540003070b0f549c00b41515449100402103c00c180c104082e506101c10301840606162054604d4001d841907103c250782c40c0c85a13481a07080400d0107040060364080480108085012210314440b25100140c0c1c401880c40c052006940c0c07032890001290240c4507060001c0351141f058002004101d801e80489555207810b17a0070046148a0750385c0000010304048443d0314014016141c0d08200c55009041c480c00a0100300401c080300000da002200c5a0b01c607000f4001c095800c8190520301c1d44c3e060350050030031400c46a001c1d159038040c0e41c45200030340c000350001d078038584581c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 234702374 1250 234701124 234701141
    0xc0c042405060d060e192301050d290601020d0311040531090516080c040c090909210806010518010e0d1b051c030e0d140307120306030c09050901 64
    0x82c0074105080500c002c206e102403d80345a00c0715498007910116001168902c2014224251440c544070ba00304420b0042c10340c4000000c881c1c0d200b111102001c1084d80b410101ca04003150140322099181c507400082c0303018004506c030001e241c40c0040040084180300211002e451003035a40003009072a511301443c603440410400e188444110b441c0500320059908803d040314026000c941c558074070220720080350600f9118000300f40e48070200e071510701d08040d000782038103450305d0030072613880355440341c1d8441641e08010f011240f08152501c3c8840b102e03401a40b03c0981511407504a0551070003600182281c401d000d5003644c204202c813980c000d90b0b8460081c0190155003e001a00485168070b00314004800313800403260901d014000210704c60800c403410400f422a0b51031060058800f9860541d8034815030360216410080001c0160042101c0e0300c0740320600403249000315541c80300c904040300444c9820800c0802c060a1403400c001041400c69170406840240c00300103501e40f9905d00c0c0368018912036 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 234703624 1250 234702374 234702389
    0x607080f0a090e0708180a021009050103110f0a1b0c030b0a050601020607050306120a120203031f05030d0302031e0c0c07080604050307030c020105040b0c0c042405060d06 75
    0x690600344140c000040c1040c201c16840d000200c640300c4004884000007200c0391000509804005a080004499040c0c81c421058080d20480c0000b034002c90200e01e8200325600200304628000c00155174144520103110340082c10040c10001d2039800501584904421501000a049048203554079000d000c2e2400a9000c2e518041e6660b0b03d261a4655001c12251001c1741407820300010038030350011035814440c05055841c0b92031961b884c81041504035802c8295001c1d88a80c0c11802c0008110034940500940c90350011a101d05d00910b0fa0101c1301268080a5a00703c485c000400075a200056117030200b00060401503225540c43c03603404040b0902e0076145c40d00501010500101030700840c020300c0c4030f04030102503401c03031a10780808540d0790030103842c0140668010480700700840c5c442c2500c144401e00c145090340c9415034541c0101c1c22600003606210329900710b00b481c4622498907210708522502c904141e1070904103d882c0c44103048a0702d1050502850000451281103d86940804040c0020 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 234704874 1250 234703624 234703627
    0x2060a020f0f060103110105070f02040e0f0102031e0105011409040203041a180705011403040b0c09060304030207090c0f051c0b0d060605040b0a0b0a050d0b060a02010903080f011d06060708 83
    0x40d040b1035510741c003e120680b001c40101901c8140c551041080b10252034201c202404804141d90a001c003c141c2581740c0c100d40e0089000518010600780011350040a41400e50700803421003104003c0310050691025040c0182603080e00d501c5800c045c161903595400b100c00580300d948034201510340c0ca51210760005056190405c02480b01410a0250a140130880455498540f50001952601070f43c010400c2000f00900020300000d4140c03518a80c084da0440d24141000c4807800424007030b03042601d0440c0541c11040c0188441e8549129844142c0c9481ca0008011b441d130030700182003482140d000b2a01a001c4000064a4494030307049502c2112000d03001403190705640c00c00100401c0540a5148900e041c0044589a45800d18282c02960484106d4600e064003103d41580d40c2d90142c8511802d09403603034415241c9a0300c2001515041e10150004540414103250043c19076000030b00358010420101e005225021078007070242c8082c104000100450307110100080c18502505134010700341c080 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 234706124 1250 234704874 234704893
    0x81306140a05010605090d15020d090c08060a06140d0c1a07050705060301060e1c0b0c0702130509030307110f0610050109060c0206120402040f06030602090f061602060a020f 76
    0x10085480c030720440010008000698030340d02c08503000c1c4600203105070300c00d20070540310010564403a59200d4030320704032600600c1d00c2d051041d690292201154103969420141d0800c10410a09004e02a8825844e4500f080340a0800383c034040c550031070015690041a03c952520304100460340c20300e000d4206103070480001e00c01408030380321039400802c0072104c6020300741000515040546c2528181e400684580715420625014011b80402d0364400034403000d080a40d101c0400c1e1441a41c5003d444950039566580c01c6074014000510350103140c80400030b14140802265138004000e0300d8001196140a1001c500d44401e1949441240c60800046010707140500500441e005148012184280c0303468104c01c2c2d80741001e0b00c03516003d039000b07508042c00b0028101d1300e4030310303080a6a0241c0f00420002d40721f0304207440507040b10b8041c2c00c00c0715102e600003648071907482d00c0300b5000011030007101c0e60780c905007030400111079a08001e04024000c110103d201e0806a0081c0305022030101c1050031501c4910 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 234707374 1250 234706124 234706151
    0x1103060c0306041a09060411190e04050114090105040e030706021b0f060415110c010f200903071406070807030918020a02031806040b0403030314060d050706081306 72
    0x5100b0380d0384602c6146008201e15540007515000140700100521482803692401e041c480580003003442c581e20660100540d00030261145800a1000f2466450b412607480200a1208441041c0c106010340904036140022650359003440a064802c10344000c40e121110480e694514001c4030300007000c0318000324a0071030024481d0a0b0481c1100c0300320844404420080c0c00366102c0e1001e03207000c1d20401c0070700070702c0429402a40001c000c0c3c541b2020a01d144c00c407130248103401c540d40da622200410f40c075804031020700c19601840341000340e40c403c80d1030324001c0fa890009603550444d20803034480d441703403003210072a55480c1426908059001075890303613520360b240740042c00c0d181240100c4500d0360304600c46400110540c429a05940019002035191418841d046042c4a0312011140e40c070035030401001c145414810080c1000710702c203890200d0001c0010401203419000100800e024202103080d80f80032500005184045540c2400e000509441d00301030141c48408016000d1701850814403248100c6 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 234708624 1250 234707374 234707377
    0x9060b07020910060f030c1403010e0403020606060f0403290f0a0c05031311030708070602070608090d02060705030406060f0303080405010c020f0c0f061306090501091406040e041103060c 82
    0xe4401c403458003103540c44050050800c1414040e1400040b22426817001c8140654000b5a0045070f40c01c1059800d20130034444000e0354801d030003803440355080302c046c042015010410b01c1d410180880d6068200140315001603001e0280b40301c0a4503051032049000010200a4600c003141c55141a4407071103881c041c49800d000500646510000601d4456242c13110740c410800d407806080c0d00c0300d901020712100d0300d40e91101c820384c01d040ca40c540901a0006104030701008060010241600900012850a0b2014101c80d2006090204a4204400c0803c40780d5003c00c3c0c0300e500000f02e04149490351a24100400188040d400104c04500d8852021040c90f401c0f1a41a2185100b60002d00c454480500d04a8940000b08020109544580841600d900c0c003a2442c0030624809041c80f0709000e46210b1585e09030100384e2214000c02e550640074802c659200200e0409841e080482c3d107036015042e804600300c1d00c218482c400000e00400046420810300002c2a1b00d075010050848140f410400030b01a500d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 234709874 1250 234708624 234708637
    0x32701090606081023250e041808070b18010f05060a2301110109060501030609110303070b01051e0d0309051207030b010918050f060402040f02040b0901030b010201020409060b 77
    0x2c0c0308426460303401d42494064030300c035001417044564142c0000036100c803034142c001d00700034030300a000c482c0b5903800005a031a117644403107259182043e07035034160103200840d0702c880c54410428a50858031004600b655084520b01030740010f51038000d03900c074142d8250120941c3d91070b072050b5080c09206020702e041c58001c2070080c44100c0c2c0c1807038226520004021200e449000c52940300440250000d62907009020002480149000116040040d030307450a041f03400c241c20413540140da40d4891414007203002d01010003400c0541c020b500e000c0903a25203107500701051045070302c81c04900d42410540841c042000d000100003030401c00760300030503280181c116131141c0140c0d03004040340300500710300d01c070001748280c00c894200c0304070b800c20b900706a00c400c090003820500003000c45d808010030001510801035503005490100c050212407c00b0b10400065945159031881910300500043c013084c03100300d044070101d000c02d0070300241810403040107070f02a001c1da40c0711030305c1c1e14a000b000169182902008060 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 234711124 1250 234709874 234709889
    0x9050a091707062403062d090606051207150203030702060f0c070213050603060903131a190809060c040e01060509012f010e0d02030405060711090c070303051b032701090606 76
    0x1841f5005901944034000302261400442246107a40559840582c40116918012480424442e0300e0300c000c244581c041341c0c05800c143c3d200e560b0030803141104c7e0604a00c4110280f01a40c0346081c2041b000b95243c10207043e112084001801141c603458075101110b0400d64064600a00e000694145400030001154138038003a020302800140e1031340f13000c42221414001c007809081c0903800c02c3d800354002d411000592812400407c402034100003245140c0340f441c0056034441585141460a542c01c0a0000c2e00c01d01003240b01748030620100926962240c19180c540c5400c81d12003085400403a0b104118903540c007060b85056001c4151040d1403041f000a80d4603101c024080c10180c000c516030b41e86030400340400142c0003072106000911f09072005100b400e0003060756011811200c00006d1a44a040e03c14907080200026020704068040c001c695214151003d4001d400120040f6003529210080680158008121f0315048072074034003900319001140d610080000c0c001c0340c0f500500a01c4507002e030305c6 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 234712230 1106 234711124 234711131
    0xe132102010609150f0b030438010e070e0a0e010501140c03030702010c11060f01050103020309010f06080a0309150c0f06060e040c09050a09170706240306 68
    0x2104820b1404e2100d00c0624050300d000d0840d0107a40030600946043c010800881c0d40399411803040e07800c000e400d1510300003800d00c514003801030b81034185080c00c229001141c8450020361161290f11562a00d501141c420010880318000034400c008152242070010700c000d5208080e0002c00c4404d001c0c10509141002c203019095801c2201c2440040c0e40d80e04103038103101e6001402c000e10355108070103844503090150980003d400705014850515070004042500382d01d00b5488a034030302c10344075010410691100c40180d10b403410b1803800c0d800507601240114008003804c19054406c110307621180d91600041c0d071344955150485005a640c681d540340c002035000c1f1401505481a442816250200c0782060204800c40b0f00241100303150628100c031500000749890f101c02c981e0075031214065166180c13071a203a800b82032a0910b2110400c0c010141c840008a03800f6403d0540c2e00c512000e0 = true := by decide +kernel

theorem cover : BRFrame.Cov 234532374 234712230 := by
  have h0 := BRFrame.cov_init 234532374
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234532374 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 234532374 ≤ n) (h2 : n < 234712230) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
