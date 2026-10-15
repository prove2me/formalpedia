-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4486
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:46:27.68967+00:00
-- url     : https://prove2.me/submissions/5cbe1112-44f6-4945-bef4-55e59b19857c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 806654676 ≤ n < 806834532 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 806655926 1250 806654676 806654683
    0x20d0203040c1215051e07030b1e010903140109120f03051005030619060f03050102030405100504020604090f091a250e120a120504030b062e02010b092a040602 70
    0x300390398860790311000003941b5102c4510201d00c441c034924500325060b14002500800a020800d40d1074803880c52680c2580c09044428900c051403481038403000030b101d041d03031a441c203086808941c60801d59200c48080d40003e094410b281050b2500303840c1d10043c082d41c0000a41a00d0000708101c24000301810104450740d000108140c01200c1c0c2202e0081d003103810079045010340850303041044020300100c0004100001503005601c5a0300030416540d1800d134502008007903030760681d070295128100380020701c60685141d00802280017400c00000c3d01300c81a03a62403501040c0c000511201808100410420020080d100701c1d5045c0091440700150440f994042c0c103480c01e000106000b41041d400300203e41c13004120b18002d264200d4441440d00c00301400c000e080e540180821103070030301013202060039801c129030f8907501a5840900020303030711000e490901040803501800c2086640b01c00200440d40c0340c40b8501e900030701c2d0344981900341c5100c005c00240d0700e41c0d00c28141e251840040008100d080d0340030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 806657176 1250 806655926 806655953
    0x16080601050a0f090e0c07050c0f030c01050a03150909020112140126030414030d0906050d02070f0c0801020d11041d042102010b10020d140309030409020d0203040c12 73
    0x1400e1040308002140f6044465001507007040140485200078496414030400140007281e20450840b8186160041481701c40d08070110080d802d40d00041c0a58003d60090000d002c12406a24001508080090501d5580345203940b04028082e40d6113442c2e000c0d940d121100c068403400754501480f0440c83c0c0c038441c0340301e05414415840320420845c864120344600781c0340c400408164404607030f2034507252140105940107100c8950f109103c0c00540180031400350074010121490b80c2c88450522410780005006944654022200c2002c0c003401040094080c02e803c4001e000708000060f10342103070305155001c4580741034058102c14800d010030840305000c0d00b48010412801e000b24500307600e4a00d003103002d03c40180d5862401d0140c258810030301a9055106100c2e0142c21a54007000c611028010781e00c0303028501c0d1000028940707202e8450101d034a40c006580001d14282224542030356121408101d03000703001708030102d80d00042800280070340000710030090035a212500c09070303000780d035120390150b40d24 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 806658426 1250 806657176 806657197
    0x307080604051b1207090e0112080a030603021815010e0a03120e181f1401080907090e0a060b31061706101e17030d02070b1608060105 59
    0x4640001d004201009510300782c1428540e1416111130720016a0013804904403030303110002e20070100020315006038104803070484071319030030810300300425454108059020219104c00d00d43c4070343c000401a15440b00703490307072a082d10007864101e0500c2c0b00006210107442c0b030203030304010112280002654440d0f0100040325030040b1140d820030082513058170b940001e185026880300d0301340b50300080c125140d06103030300c80c1106c0000b10349446440f4800c0100c21019010b60b010034201910701010650240340c0d100d130048005422112410342c1c68103100c0554880e045800e9498101c08040c2d020400e860046011120080341c42403c1089000003143c95413810010604c904000505c10304102c14456103d08064000e96860700e5003503980350304003a0360f083e0070364002e03408082c1100c0002d209175200e07a04000c1305034812a0220400c0c9006480c3c1d103446a02c1800204a00003001001e11011603403000300a05807288191008510306110204880c1182e441d00074107100b031800410100d44e03800310403103104400 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 806659676 1250 806658426 806658431
    0x5010509010c121e0e0304030b0105100804120c020a0602010b04060b040302090c0d2306190317070c090c0c0302070602060405070b28051b210a050d090c0e0c0307080604 74
    0x111078155001360700e504580c041d581c3c0780c80991240c6180c044010020741c1d024188401659981700c00b1306c1135407524150f01c040081d0807000410002000d000c1c8140e101003503460000a03041c0c660700018a08007495200001607950707952a80740e070781040e0003807500401d02426400c0c102480c40d004104c1000740200030042804001881d6450075406601070180c24000035440c2d1100819842d035010400b0041d560035100305141c0c07401a40702c58400b50f401081d01da1041e00400240c403c0c81c0403440301e40000908035500f500c0d0180109072104281f14130000c001d6103075999418000f4604000e820300399a50004000c64002404100c0443c20000d004000c5030300004040c0d035141000e00110008204010110101001d00100104102d40c807401030404408124802a409458132000590301c052003064822003003403140d05400e2a061040207071481c9111410a240b8040c000e280c440100c9019000860303e0700307260403041c0000c003480d220183d03116040c044040c0c51410442d0003d800c101c03004103c584101d4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 806660926 1250 806659676 806659691
    0x4140c03041103031303030504030b061c032a062309061302040f020705010b010306080c011b1e050619020f03060d08041d010305060a060b0d05090c0d0501020705010509010c12 77
    0x21000c20445203281700800000780866160300e801000b9501500c01555201c0e03000020868528144801145103907202070792244800072980c05071005030754108110b500e4070002c615088090503008520441921580700091004020304d011000e101c440701407510392034403503401c0200240c8000341d801d82080590b81d410b800d50b0b071140b001030050b09880c140303c0081c5002092000070410b0540203d1014242601e083c00300c291500141907598800d400500d000a001c80031025540d00800803000c80f41c1e0051018114a0030440c500762100300d8a4942140e00380d001c402000307440303100030f0303024645054103650561a041108071000a41e010280515102d1061091580200841744c0d04a400404450428428121100155400d07440e403d120030ba90300c3c010940010a1408107210b003900340c90f24060000d00341851424420018000200303110014070a001140d042944c51100700c401e114898000541d40748207500d001800d540c0080c102041c01d0b0f051803d240e660a0b040489031071603144504001942c1c4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 806662176 1250 806660926 806660929
    0x609070e09031e0901020f0c030a080d092f06090a14031c0203040303123303020d0602090f0108040b01121109010909170a1704110907090504140c030411 67
    0x14030441c41c0044a02d201d0301407100c01d07003c0710000343c00512000d8017038500c0c0308210310105468400014140d03505070880402580044c02440c0035141050740190006680e990a42e200c5a0b01261403401c4403440412400400c1d6610284820741c0300b1420613a2801d050013050408507940c080309019503003940c46030710020720880d1003c000c6000c42e408204400540c444503880d000c0d413a64040d02003940007840140800350a8916402198407020295100d81b000c0015003c0c0c3d4110404440b400d4080000c4960001001d6038078524602d15403030050b40011b0b942c0082804110328062034043e07040c144640035041001050201550b1030440b40d50611406842581e8a8100682c0c9850401c990b400b4501d00d001054940d615400103103641d03c0750707143c98507844c00880c03d03007814018480340701c00240c4034504d000045914003e42c10741041c410940302c0c108106100000386802812a00c07440056502842040f140c03402e80a400c07078041d4006034812003414100e0a0341c072540310040014014940c1c0074000b441c80d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 806663426 1250 806662176 806662183
    0x206120406140412020d0207080d0e060d0c020606010914090a0c121103010911040b040605090d0b04060e06010f030201020c2704030f141c0b0f0d0b0412020609070e09 73
    0xb0b661070020104414541450001c0b2940b50b1550000d0051185d80400c1901900020300c0754140e54900c401410056115801203404e503ca41059542000382440211482119030042c1040200c0d1a00540300601d005d0000414040d81ca90005820b404d0f20020b501c5251500c080d200c0d000305040d8804910f03110f03141000d0741c1320400b0401510020345003140c1c10103001213400186045ea06096001e0200007000c00500c40b0714002ca015040c126030040000b001494045c2c40101005940502440d4600d001d580320301141c0306c001c54059442686850302421080d209001641c058010441b40050050458000030365841c618414640211115002880980c4444500c1c1e124402c0d2500c0c883c2d0a4642494000c0580b048916050085090103040044524109059903508199500000c0c0300c40301081c2e003d0060880100b000d600043c001c40c3e50034a9494181494604d035009141c200300b681480c3c9400000809481c0c254821900b0401c14445a02c0d0080b5001c000c9079084000404c05458400c9001d04 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 806664676 1250 806663426 806663441
    0x309011e081915030c03170909220b1302122d01142401020a02010e09180f030403200622090f0903030e0d02060106140918061009030206120406 63
    0x607205890f43c40041000f02c0301002905070307440707001c02c4007040d11313148019485e5015000860764080c500000041035540c0915010400500c4d048204039007035840d491781d550b0007806036082080181510102ea003941442004000e00304071020040800c20054922031210905c03c11010303000e0001181c200010035000d410400000715a60f5040300d15050160840d600034030180700c40002c22a0b81e145c2440702c5e43c000f040c05200d05d40c0684400d075140b03100341c040203c0d008004050720600219294041610307403040008118981c0c1c10802076076641d08504220b00c01210400849a81082025070032041c2c2d1030f14800e0f102c0310401e481004410f030b0403598203010220724070380089100c1d6203401c01e1031105c582c540e00041080da0180e2030801040018010b45034403440b080009001507072049004005a40c072685070103209015071024541027907d00d00001c1e00c03119031804003c01049c100d50a03c41ea603d0809941a00e205207800c155410750310316401b0030f8031350140c0ac15003981504032000240c148040398000c0007 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 806665926 1250 806664676 806664701
    0x36010507181502031b0f1606030609060b0702040e12071b0501050315330c010c020304060c120905040f0e0106080a080405100e030307050309011e0819 66
    0x14600044010020703207079100d00c60007008605100199a5451501c8400d0010032079028620b464041c0513490540030400346070300714510804c003412420400500c5059402d00400754081c1d4014034108008042d643c01d50041c2c03d01c1071400700c08101801116080320600d640c1a40c0c041001280c0324500c3d070904085031001d89030341200007411010400303549017248946010000704402c0301e0716100115a607001c100c0703800b0044002c5000b505454500000070b01ca03000000d200c1d910200c2c580040d0340d441040b601c00d000101174004070703412249000a01078210058031600c015410701e841c2120080480b00740b0707400030f0020220603e00582461150300260040d2901400500c04c085290460b00300401c28030388040101e500c2e141c070108005401150148c0503d41012002d42001d00f8901003102c611340d071000b88c400380312442c411410562018005000614021400385448011410024046494002d52207420351000c3d494202000d4000c50199000b4808050041d400c0c1031b410480030040000c101c01e0b4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 806667176 1250 806665926 806665931
    0x10303020c040e06180f0d1e1103070605040c1d1801112b020a1d03070612020313230c010806130e0f0106080321040809090912040e061002063601 64
    0x8004c0207410018203455800c5101c00208e10b403001c00021a20617031440c130503a900e60010410100031031100d4100540040c0501d0014140994036030440c1440100e0240c1c89405a03824010045649284420544120031203c02840880a04002c2d40f10030b109508901c061850015043c08001c41d60301c401c40c0410100300700440d40d410010700c0141c8016403040c084121020a1122101141804580041143e455880c1e4030b00400e43c080703820010390402003c102415544428a03004603030340c160085001449004d0320f402d96a542d6150508005001000a06000e095400c0c0000c40e250780910050036517040500250280040149905050100b4103010f003a40c24540c020581140100c014501c5a003000c0321840790380841d00d042a41c000d004c590241003000240403099441c10301004580c4e00407000401e5600c640d02c0984215959006500010080400c3d1000c20500341402508a011000180000c080c40d00d0424110291030112072495800c486220000d5011035500c034410711020102c00c4001d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 806668426 1250 806667176 806667193
    0x11010b060412053c010c050a0e0301090203060708090d030c0804020f2413082802060f040f030b01121101030b03030702060d02030f0c13060f090518010303020c040e06180f 75
    0x25804580314040100070180e021124204c9080d014402d00c00c083c8000d0319024200461400c05507a082100002030f501552600e0070031005940030b1002510070036a83d21402258103181d402c0300d107000084420103007403620f0403420290071754210760019401541166000c04488138400420361204074904141000b20406040f454140c841031b0103880e04660000030400703510b603158046940d820044010801d21000082540c0c440300321821460821130003d01024030b8140e1a00d190303000d55015902a4000d0484c411b000c0c42005902252030380100030340c0c140c0c070341c074050103480d2101d8051001d0a00c42c141940c60b140c114181e1010700a80324103a800400e140c1d00c903440491143c01030f510440310110142c90040024410760702c52403e40f03150000c071507418403085041c08400d468900f43c4054400500044090000300751b41c5528008081c0c0358040305880a5515600d8007905c2e101c1003200c0c56100e00c1c200011404a010000b507155800001d48026210507443e403c0300d1340c01c00c500994841d0346402103450 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 806669676 1250 806668426 806668483
    0x312040611310308031303030608030403060204080c1017041511030604051806180a0c0b0d06050906030c010c02060c03040e0f0f0705041e08030c010c11010b06041205 73
    0x42c0704403910000c11550a8118003001142e1100d01c14040100752207014008504880c980d0320302481c24030312a0600140c140c1c2c4890312a803858009a004075400b580008003130000f003005019030201c902c0d040c0c40125040b075121101500015241050601810302100001c05010404841411107611030030100101c894a0104681983c011656103016505020115454510344485401540e507010090000d0341c450040d80d2030280c80e60000c41d046071050b03801e0900450003540041c0010120840403a41c1c400c81c0c903140c1d0080d01e58070f51003a442140b2074420454144c0b4003040b4001120802d2801030380040c2244005800750240496403a4130b44004140464400104114680500380c0e01c6e6240c091307540e84a00e80c03c0007150440703c01d00080d00070b01040046039440c4c455041d41100066075100d03a1038880c1d0903903165030468012100039030f44650105007469000346401c800300403408000c2c060551014085466841180b24885100200141400078060180000d866005602000c8c2c24030400110 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 806670926 1250 806669676 806669707
    0xe010c021c0506100b0a0c0c0f17060702010e0304060e040609090c0330030c170403030501261b01090312020a021e0d0318031a0a061203020312040611 66
    0x10002c0703800b4030818010801165103500701c401141c54021300a46000703d0000210307004500080110703101d00180b0780125080303442010560113450081810141501c1c8400328914204001e0000c0041d03924005215546010200444082d80c50030b003480c0d48202c001002003001443e40764003c0b01420b00d000341503c20411524a8501200d0103401c00295001d003212407036030441160b5800894824014030f0711908140603400100d00041c243c00d114104030f680400188014000311000c81c0001d0703071040140400c015140c0540c40848085240e0300940c0551405a9a00d110401031861045031444044d041e0741c1c4140ca05074040c503030202d000c83e603040131283d01a54504820a00b28800d05000e141266410060703180707070740510402013071f10f10489a652000c0e6080c0c2005203001103225111722010006c41d254490810380541ea0f20041c101e2864041c812404440f943d0300a0110614034020500119a000042d41c8000780d501c075544605850303515001000349150142941041d00106550080c81c02c0d44 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 806672176 1250 806670926 806670979
    0x131211091909050d0f1416170307020f1c052208160602010c030506060703030507110d080f0709080709050709230405010b21090a1a0a14070c02010e010c02 68
    0x262515450480b50410541c0c403c120a190f0348a0ba580c14003210000d2200c407603404d500c0074001c0c10555680c9451108c20070300d581c03044070f004025030b002c0040c6449030407040280249030f00a2241245003261610002455845200442d5080d5840700c1c05400516204410410040a00e003080b00c003034540281c20514007010034440c400140d440c190404810b05e0090007190311480004159510f400580e56003900204070140c0b52000b00255862039400c3c08108204d501c018541395120f8180358a40445842c446140003403042c010003c001e2000c00282600040c00004e494030b00764081042e546000e0f08541c00441e503849062981c650555203240d12a01c0c52242c0d51500c4142c03030a04c92681c0310804c03042d2030300c01e010364803400854080c203540c000c3e1160780071540c000c01c1c6001684d00008050725840543d1204455601c04092000f05001c0c5051b060320880b2004000404084038625008a01503d00c01c000303000641802085418400180c0c40380d40c2e00d545503913008090102c4200005000041c0b171280 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 806673426 1250 806672176 806672203
    0x303040f0f0602030403030c02010c030210050c131409130f080304150e010e03031b0904020703020d08070f020c0d061e02090a170c040e0a051213121109190905 70
    0x1078000201e0200c1c408400c54050342d0701610b485020b54403a07401100c0000c2c03c444180d00b180151844400894501e02402d4040e01e08d04264070307111030102ea944851103000754030000c6501c100214941c405e8071080e12043c0e0140001c0124030000705603040c540c0078141030031700042580c0c0c40041000308003c0d06221202005181a204202d608030021556088a104c0d22031002503a0017440010f03641c000d4500d03000030303040250401030b080190400114090340c1120ba0118090b0700403084015020f80e01c07100a551040340c5140409070a4100c581c0030b51640112050306000b030072010480e40130300c0315a400c01001c0801510300300404c0c10300d15520100070340080f07100d94407070001e6034400691201b0003008000c003c1010b002801a44050504100c002c0c81002c4101009000745084c48001c03450a000542e041c40d821105207a46010b58540b0800203001c3e6001a8414040c11880743c00bca20310740c900c002c44013010f490002240e00c502004601c0711182c03510350400d15040c94007000030441e010840040c1c1600 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 806674676 1250 806673426 806673449
    0xe040b0613051024090b1e1330020f0f100c110d11040b030a1403031005120a02330919051c1a01121505071215050303040f 54
    0x1940c070b9001801d44e502d400325800201001d90510115007035500030300410f400c11b42124010001e0050301342c581c3e044000b071001021003500d0f0420164290280b0020b43c40c07648503654000040c24000e650002c1d0130354501034040c2c4076074024040d4544920321079100c0101d0052540072011b23080e0100a020b0040c203081101e10501000d1800710300d00703006019010180c1d001c2500050704410805200003404d18a0034281d040c4100c0c114500407a405403180026403581501555403840c00440381c10301044142d10089c0284803801c030841c4608800b01d6066000c950458901040010103880b40ac144001000030002c1100700918480442440000402c0880c4040c1c0704101d01002d91420403129048900c102c9801034181e100c804800744030f20580c1c0c0c8001d84601d103041a51849010b1a01c41d008090700102451449030540c00203100d107868000ea00000e5140c4240024a000c0e0b40c01044021080e0107010107a840d1100d0400d4507483d0040740011b802d0150850781c03620350754025050a100d00d4865105501c2 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 806675926 1250 806674676 806674709
    0xe13020c0d090b031014030304051005130837050f0c130203010510200d080402011d0a0513020c0303150a140f0105030403050d090602090307050303040e040b06130510 73
    0x1018a030a4905c106031a651420007035142401e400c90382d0b200301c940a6410f020810000c01c2c10350f102c040200203620141d03a400d0301c0f0203104070905d01c1d42c0c03440d42050304030303903c000488000008044040c81406e0582e1240c0344031000c8400840c108211100302c000e213035004441c030300d01c48c41c680000c03200c0901d0f200b203907000750301100c1e00d6144040344000e00626800c500c14035440103000340036100c00b21041b4504522400741e40c10852803141043c420f00300007000680e0340c100b444103560340251119000341c0600d014003249060700000078680359a074407a117802002c0c9409000106012541079403040650201981d0b505e180a400c0070914030512158a44242c1160102254000301032a030f0a0202d640584035101d8030042d84010b540341c3d003008004400300003040040d4040c8840c103005802e41030b84981c001603200c3c03482000305401c01c8e00e03c0d041207010340c0c01031100f041040104040d00340c2058025407160000e07122031004c0f0300b1410552003e40d00c498201010302c5854030070b0708020b500b11003000d0681c0d803940 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 806677176 1250 806675926 806675939
    0x30706120b0d050607050306180109143607050306160801120803010302060906090409030c03090902091507170f0c01050612030307030f06052206060203040b0403030e13020c0d09 78
    0x700c00c0d802d006040c6511000016a409005400840d007101c0024a44400602c8903640380c0c540d44001d81003c0002030312821417200c0c8401d04006550840751103c500c4030318902d484285025040752290740101141e03c00c1d82d654800d4001e10905014107400340a03203205150000000c50364000c103000c880001010003000080310464024048412603000b000e00703245910350340810240380c02c0450b002c1d070303c030000300682c0c1c9840c0d0b96845001c81c0d8030311030303140c000c00800c0720f040140c40a007059005013921030042145078043e645040e508800f006026407115240c0e07280d07003000c02c1980500400806c1e0580e0000300b014041100101501a610041000344220742d612428041d900f9140105c8801c0c1e80c1c0140f0220b6072250107a0401c3c40070200d0f0900000324160f95000181d030041c0e00c146200b00710b05440404100d4484140294030181009000452a25103040d40c0303500320303100302d01c0080d00f0007070b44000140f06641c42140305124052400400e5460b000150402a05c83e1030300a402c4010801e228000110f8 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 806678426 1250 806677176 806677189
    0x1050f03070609290409050a0e030901090314031306050408070602070b031314100209031908030732090f300f1e06071704080a0509030706120b 63
    0x50314042d980790140385191104c00f1400c612800811300c4000050112080140d000c80050030050190050100f01800c0284100c0b0403600707817590461140d04204005003131660024001400c03a81d01c2065114000c3c0c400f00e0082c118014032188408090a00c00300003a40b541c44800340c4142c0d5004ca0544482a41d545004e0742c0d02e0401e48505c090b0542c003400051120441d036040e003205503006030560501001051041424020025100c010866010502040c0350a00700b10b80003180c80d461076580200d00c0c1c60b803544025408010081300c1005030050301049030400646851800e0085d084600d44441c840c1416021242c004114040c0205420480c5902c98580480b0481c00c0c1910211030740b42a0b04080c10311010390b80344140759450740c401c074a0944c0c0d210310200490690381d110300309401c20b01d524212007541411005486d80041100c107250a100c501040a22150051791180a8581c1d83d54642001d5480d40101c07004aa454002e2480009a80d500103100810703104440e10b0402c4401e0601c403c0080 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 806679676 1250 806678426 806678429
    0xb090d17130f0b2803020c060108071a04031a040507030f030f080a021603030c02030708161110050a050a09050d0302060405010c0c05150a02090a0b13050607030e190803070b01050f0307 81
    0x3541a44c4519109007030304140c0060b90402440d00e000352a003055441c3c0249000d0003a4011451940106402c100f0300800c2c940e400c1c0000351018156140903e1601e80400524480d0a41c00400072100d0100307042200401a180003154032008200c54607540c0e0038040c00e854940700070b07000458011000143c032407034540708480040d00c0e004c017038060013021503c04800810481c100d180645c4810030000002c5082c180c060114000e084c00310f600030400a103402452106401c520324010310b110088200c1e03460b08441940e803204c0d281e103042ca03121500310b81c08440c0b45606170b02c003d07004203030134043c14145540482c03100c1c491800784000b881503048250040355000007540b400340258010040c0d012050900c6410203800003001980581400d50800014046030301e240e100c803504410000d4a504000c0c0354118071070091401310341490502e085a1806004851000156071040c0c40d000a0801070324010440800600b01100440f92903919034500705004003001c1c01010b02c00c01c1c10381216a8140740000b0840d0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 806680926 1250 806679676 806679697
    0x603051c050c010e0703050d0302030f040b040c0e0f0901051501020a081305060c0a0308061e04021b0f0d140901090e22120f090b090d17130f0b 63
    0x104100032003045210340344003000d0030020400100070441c5051800d006015032100b111010b0328100f0b14503d000c600e001c42004141c0b0905005104006540e800c1c01405940306130030407150500759480e480c0000b0040c02903003081c844006010280b11a0007140b180c2c081c440e0b16a08020080d585038072000340d03030001812201d540164007840032907000410100103442444135060040c0f81807034440000504a03080302848000c1c035030000316000c0034141c1c08071025030805c0099400d40200b003040043c1142401c9400102d034061500090100d2102c10b001c07604003c2c80602c40d0030785007040030240c032480e2581e250010070000500c810042c102940f641c07c003100d010300b005171900c66a0924201010a00b92002800801d1035512003907802800c030b4542e0300700c40311903110302c0ba05601c4290504001d8880c10202d0301001c20041049818011390000808903101e00e842115020004441441d00c0c100c0640c001d1408180752a0118040056611007291542074941e0600180921504d0718880021405040d503643c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 806682176 1250 806680926 806680933
    0x215031807030206160203010605090906041a070206070c11040c1101060b03010b0a0f090f3c090b030309040615080618060d020a090507090501030608030909010b2d030118060305 78
    0x2400043c00750340401c640e202031f001045450f50b0b00006620b00c0742c1180c1125240c0c11850400040010190942e1010240103680381064104208025583c000042140c03043c071032401044018410603640076045210014030602808200700303c010142404101215019030820310017083e03080500b42542d0603202544603c03810a81070780800ca82c10400b203d00902440054040031501d840300d15281c3c0040d00c00c5214000103031000c020b503a04280c40f0450050742d001541c00c03500445164010070300c0c0c1214012000810140a1900002e04601c242065a50700602c1c242000805d14842c00380d05046140680303644402d80d03542000d11401c24010428550210548800a03003a0728018008100e080e0015112440c843c1c1c542d070001080700c13019035910020030343c030a000704403030360b414000e0b040944807450103103040c5940d140104180d000180170300c0f01201c601050030f6509921489810100c0174442213080d801d42c1c03150341c8410490340203002d60410840e910f64221203600c0140144021242d209004 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 806683426 1250 806682176 806682187
    0xf1a0304023c0a0609080c010f0203220e070e0603182d1e0a0b13120512010b0f1207030b0916120c08070f0203070215031807030206 58
    0x20000c002a0222084011000351190900105140400428200350044000c080c590b01c2038108018400c060784008108204140107010714007000c160417258820a00300340c0d015849000042c1c0c21070280e08103049803010a50180d4010f15440c0840c1800c84190003040c4040c1d4580302012916202254540c0750004e10400101e1029421201ca0400c2c10a1140694030407242500d1490549101d03208001d0b4016004510f200e0360000034041807948a203903a485c5a9808105000b05031a111a182c0281140c00400005015490354120507040c865011030065180c100044028156800c014101103441d21010004110720304094200c9242c04800c801d01410454050340c409144080100300004041c0c88060f07020700e544840c20b04030700810702618401c46400c2800c500400c003904505000321074509011014240e150040d0020713030130400d240360890003084071a50a034075603c500d00f0001e400c0180502c00c101501f180101444c003981103038031000e03500c80c0e1100940b56151058000a580100200305 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 806684676 1250 806683426 806683429
    0x111030c061b0d0c0302032d070f1407060509070b0703020c040509010b12060a0e1c0e030a05030703030b0109050103231902040902090f0108040c05010804150203100f1a030402 77
    0x22404030302402c020110300e01203100c84000e00303031101102420b0209401009200017001800000711104e44000c0d0842e1001c0c481c2241d040603200054287c400340201e400220a840d44610041d55001c03d1840d08182e60750010702d0044000e1030200d560f58124042c3c48004a00c5204c0702c0c0461f4003441d059401032540e4180901003000920003d850b2520325940c5928104094603a641d0344c8111194090281466244c508000380aa4810305a115840d0300072200d00c1805181400c0501500c1da0540f074000c0406003d14003203458220b28400c064403070300c07011809008150741a007003407004620a9959410140d9900c0054042c2da405441440003410b0580100d0607103160b2003061a4014907030300c40200c10180c04d801e1581280c2c05030304079549140d0000b82c12403c90901d2180e03160b2030002031030600c000b49002d80314014101d0440c000c1314100404007001c2414001c034215400210304101c0030071562401c103040f01617901e190b030b07104942c080d40c03001c40d001450300d64030a00348080d0181601040e00d555525030 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 806685926 1250 806684676 806684701
    0x606080903042c250c080d0b120a0b010303020c060301050915010e100801080111160b070c060606180503030319020912011e0f0204050f300307020111030c06 69
    0x803210700302d01c58850810f520400000d4510300400b400e55070b0918401c6000703407000f0300655540710341042c40081820600003c00400c12140c050641220010301c04815500190380314580d10200d00261050744441000d02440c84800c2e03040301e110fa0215039007610b42e442405030f40d0009201e45503010030620002203201c90064803c3c078110305c1c145407040740800083c0020b1210b6000c0c0b00107000240501005112101c03091054807100f81d040c40c000c3d41800c034a103a40c01c1600428120081c0744807000c0c03001c500300030f0152170650003055000c1420702407a500e84100030110052754400d4072a0010040c2c0009140c00d000c01160300860714841611030048a4240d020b000e07510072030b0102e070812468165410040f00a200700c07010029200c04d20003400c1991040001503c4908044074a503e104100801603540c1d1030104030b00f071600541e054080322600c140c0401c006840e915040c0d0201001c40d02d00001c0480100c001c15515101342ca07002107082598110a54a002d59046030a081d400000414103040c5844c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 806687176 1250 806685926 806685959
    0x40b0711070b0f07030314060d0f050a0b1e0f07080105010e0607141c1e03050c070b0a0c021905060402010c02060705030c030424090b030c040b031801060608090304 72
    0x4104485005070b03a4004015141d0103c40b0205a901d408a101c108050789070051146802c0a00800302c9641000c100080e80d003480f25000400e2821080c4001040006c18003030081002d400038031480303a80c0b40480d1440740501c040702c0d0125083e0000703000184d08188548110740900919070302e001e1036a0030840152610a00c0e400444e070711107400e0000380005108a810400500c80b201c000c1e054503802c0c000040d00000030940190300b0f0021841c1107801074a901035010501011910780469681c88644079591207114150018214500b44000c110072070382190400c124412556007240c007103035648841448192165040141a0b4010f503020401540c896505411410300041c1540c0c500015541c5007407850380051341e01555908040350070400c0040c4005442142400d20802001140046200402daa4568001e000e030016020021908028007070702610081d0086000556072030400105a0241183c02d00c000c0070f40e5800d0003004200d451240c84070034041d5100000a42c1001c1c1890742e00d0040c0c0500 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 806688426 1250 806687176 806687207
    0x40c0206043503090a0303060614031609090c020f0c0a0b040e07051207030b030c012a0c05030d18080114071209020405040b040611040f05151306120b09040b07 70
    0x14480382d60b6400d07a5420065010345504001803104d0301c524036001c0c06480b12a4081002d011020000000030001c01049a900c805d003007001c010180344540c02503e00006070340040d8485071410240e1014150005140c4000c401c2440072210145914000c004031349850303009090349968240401c0104600c50ac0d50580c1105090078407500700700209050000c0c0310011103440d400240c80f240603030300c04d040610030404110000e2a2446050102a00c041520b45e00020800304800c0c00100b61402d00ca00c15682502800c0020255410b03c103445070020716520b0b0084500010810f580c600140c0080c0c14802d9810100070080b030401d190350741081c103894902d80120487c54030b5860300060070050340c0d00d10a02d4800d610616603031b201400c02e400d05404036a1044080c1008990400c0203104003844204942c00701c40d005c40f521441e100c0e03580c8248005000b01c0517a440c2d00700d185c03080405d5654100110456003c4800003c0014620300403c200341903606440c0545409642004206039034841e81d40c55100419 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 806689676 1250 806688426 806688503
    0x2d1e0207090f02250b090307030c0b130606090c120606090b0a1106010906060201052a0f07060509010603051c050f22271b0f1205070509040c020604 65
    0x754007150908410a1049508115141c0c0c113920070003081c140202e8000380c401e0011410540c00d50381c082c20002c0204401380c910400c400000c0c1205202820001510b540030001340030f46503a4040303001c040d102e10090031022a0014003000385444d8248510750484a40365075009a0074581904a0010b5100100d03d800700421182050404001040000c0c002d10110000150861400b41e0080c21240c0103013009000202900d9850703505001440841c0b5034002070200c4036a51031449810b901544548200240500e0620301046001d50041d031010049a0040c003e89403c1111304078012510700ba078029860108d8820300034041e11507116070103480f00a4200c000c1842e96071404c2d0301d010801000d40d00c004154071103000b00c228443c028110b0090444148030007070211900344101c6c545450304200d2140c1c10022844005201c2030311402002d0050201d10208012600f40f418004040c1d5000100460280303040100d0141403070320014009100d01e030003442c05501e2100018407006540b0141d0001c030117111 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 806690926 1250 806689676 806689687
    0x406050705160b041101050310260f0c0a050102060403140a1b0b1b1206040e16060908010c0908060a090204020c0d0819020408061302012d1e0207090f02 67
    0x4040700c10b0840c0382c040e203080c4890746818a0144c1c2014201c02c0083d0412030b0920501200000500801082c1c0e90700c1044446e420120304844841c001c20400b05070382510590104802034040455034401928054581c420b020740c03a00016aa501000e4074010005100311114026504e0040003a181d42c016a281a04929400e8087c01c0303180880c56030213131860700107441030280c240700c079000719104400490422030500c254000d429039101c8008180500454442000038030b030340e80c24401025041c01c003078038004480382c4801004040c1021809440700c1503181c10f0315864105c1c00790110804440a1800401c241e40e00c030100400649070800d4100d0f0025000e111001c50800203102c1401021600d545651051419004046002c409084011446481003000340641203011031000e40c0300000704c407448188415840101c8030803008140c02403101d803c010711100146901600d07540142c181d60f488507001c01194103000442e2521803c0400541c4c4007002c01c000000c3e481c0c1000c80f6445040d0b50050a04 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 806692176 1250 806690926 806690947
    0xa150608131a0f061f122003072a150e010c18150903230106181a01091a0910050a11070e0c16150c0306050312030406050705 55
    0x45482d02c81c0c81c12102d980081181c10b15515100c103602c11822141180600c50010110b510f150329250000200200d054001d0307411402500705410400655000d40c1c00c070a40c0120f1041c60382c00660304c100c0001c9004821107440d1048140e80c8801e0066401811840c0446039030b400da03440008900c0c2c0401c1901e805507a902d5080a2181030445401626640710703410b0342e8200c3d454800e1050b0020001101003000038030032203138844540402d0740c2d44000604180c2000e0310f4030b010a4240b00c4041c50301c42d03003841000310303d120340f101404016030360304003003403124103030210307a02400d0000f0664007800142a850200705100101342c1742d901c0004401d0b40180340044840104401c40c50090304800403800c0015402d5803c0d502c21040c800307200c412805407c10a04009060b0881c080180c411104140d002c2440403040350011402120107500c004c2d6041c03c000c0d07011042010700003a121040110345428400646401c000c150030081303004503010350340386580e25a10700d0000c15020305a0010000c041c000d5080c0c4 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 806693426 1250 806692176 806692193
    0x1205010b0a0f0f050a0807120203070e04030c020a0902030603120a050c12040f0819030e1810030b060607050c04051803070305071e1a0a110f09090a15060813 69
    0x2e007840c5004120002d003400300d4158214038640c09030f80668901c85040001440228040341900c1861107104074240f4a400040d1032300740e107030700034801e204000c105000c101a0407d83ea02c80c000e100340e80191540391b0b1040010102d0004407555600341d0030010416003c000400004c01001015003045030400b081ca410700740c0b4206000200400352140001c6c2400000d08048244004184450040030004042e0012654055007500001d090001d144601c941c41d55564503407100e10ba0f40181c0c003010500d42581d0007205414517200c140c56142941c000f103021414403a0459040c1a04180200035001841c030500008040c0101403010369016041001c808210030700081280c0c90013652078a8a03050b40741005a030389040c041d50841c07040810742e000300001740c480c031109440b01d04980c410202e0755070b0500c4860282c045803070820851080011a50907003108403000c1c001c0c40000380e640c240c0319074450312080704036080802c42501c01d03001100b08216951040e05002d41c4100071141020401401d41c0c0d4441c00e = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 806694676 1250 806693426 806693429
    0xb061207090b040b0604050d11010306211a1e150301020a171003020108060d03091a07060b0922150f050a0c18091d0a0b19090203071205010b0a 63
    0xc0d407520760486210328501130003050140d1804581701c4d46801c0c41c260000300034410200009000d0709040b11400b030280c1c02548180001d05982c489031850340c0141d038100f44c0700011030004449501004140403031034940c81c0c2001d0320680d02003044907042e0001000904004200408540c00c0c54940c60a0369001e4a00380060605030301030343c81c0c420300d49400004c00d4802d640028000b00f188040d8000800160f80d201c0c0d0002d400c00419100c4020f000403c0c10b00711480c1c1303c0d0382c1202c8104018070015504044038280180010f600500701002614002804c01c8456041607034502c2c101645041d85580000702c80600d01c0d0741e103105115036060005546a484180c640c07007402179845039034620402008145500801542d01801d15000080a108040c41199049107002d4079491a641d92401d0000b00d002e80c0211540e00500d400b194100700c0d45140c0001000c000f203070340450050344000b101401c40d0940c0905909140d0090162a28500782051114003201c440401d0741d5a40d240e80e00c1c0d90490311202d40410 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 806695926 1250 806694676 806694689
    0x10c0201090c081204060806030a0203011a03100509060106030e15010f05120307030c06052e03030f090b1c02070b0a0b0301181a041106030a0506030105011508040b061207 75
    0xc0c10080d01e040c2524400d4642c0c0c000010f42e00000800c0081c8801c1c0c508480590711542030400d4607403610b0300440c0ca496001007000b9015031804401c6443c82004080c80b00440200718100d440f2280e07002c3c00002905c40c25588040c90341d00c80390050201500a07003000da000c071070800484020400420723001c00710180030380c04104880103840050049042040c9a1815200107200441c641600d070f5800501710318880c3c41c090b000c0c69941c8040f58990030039075216103020b020200350305041507070b00072004002200d600c021000316014007102070b003141c0103000d86400c4403400c1018504207040c43c3c020301000310781410081d05290382040b0324000070311040c03402ca01402140c10005900c0c030000d010306084401e0903089411180f0361000d608002080154007c050705800c2d5541c000ca51118940305000d108918403199008401104010740a403182e8002c0c0c1c4540800c070000d02540c0d9071085a005152103101040001404000009001c202051103da8202c0f00c00342c0080712901070300d40400d0410060340c1014 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 806697176 1250 806695926 806695931
    0xa02040303030b090405150c160320010c0f0c0602040e090d080606031009090204090206190305010f1203030209012102070314121603090f0b0403020f070e180a0203010c0201 76
    0x50040c158907200c1c583c0c0b0154140c0d4a0f18442c102a10380ba65607080143c150303d000303001100042c481c600326805a40d40b00c0412074101002c081c1610b4090140b034600c5a01c05c0d882c0d0207a00303042c043e20405000c0c998030f104e02d41e103030303100180b03d01a02180c0031241e0070015594903408120005858000484052060607140f024017200c0112901c0240f4141e8050700051042c10207100740a15600002100402c480b940c0ca4000342204561010074041e0102d070b80c1c0654010305c041809505206030000b014414089541c04105a0703817a4151f061049000b40a005045503c552130000040c0c000d03402040b00040504bc000c0300564110204c0b1001c0761a110b4031183c00ea0003054190030182c01403002000e1081d1120300030b042c12030f030030b81e140c20000c0700424004050046c1200810a0384c040e500c581910b40d0031a0025014000c50b0600c080025001c0d10304a00502c0f0398202503d030b40130089030303417010781b010b00001000540b250a00319024803900303282030b40140642194800181d07001d2160940f1556280c001 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 806698426 1250 806697176 806697179
    0x604060312121415040f051005120106030203150f0906010b09091807080d0e221e15030b060409020904022202120604050606040b22050301291816050f030a0204 70
    0x61000b40c42103008035a4242d0700307180070b00100c0c238507154816040c0e400a076840e55585400500c428003508440c8c0c000ba40500900c04400d9a5035001c41595208500d42020000745e40c50313410b15180e0740c900900c1103192018080c41404824641041c20a8000d5607051000034061800d141041c14010b02e6480507143d07610100d018450550001e000380c480040413100c9950303645640a00b5120811582203004c060b50b0765070303445005440c8000c450244010040c6080002c00001036a9442000e81d600040e02c40260340f200044181c0740c50700070080c6540c0e01030000090740e03c4680c02d120400c03d410001c9643c01c200c03a0907040219000388050904072504550824050a00005010807684050000d030702400d030402090096125000440e503079050f00e1204602c41e0100041c3e09950f0070b1003a04641d0741942400a0b4980c1c911101185010303440c0140b03030b42c0d480d211011041040e0950141c40e06259004064002021200607558074401c02c103103410181d181c00c903202460038059100311814080355502080 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 806699676 1250 806698426 806698429
    0x1b030c080108150118020c0a06060e0f0c1b1903030501150c0f170f1b0601050f0d0b0603010908040807080c1504330e090604060312121415 61
    0x1503090050030032074050300600c0d21040c5041d40d001c405000384412916140810700c0640c6865045a242c06d03100001d440d07656482d480d1140150050340300d03c81203040c01101240301148282e20150046c000b20420502c1c20040d8030300215113003c44017813040603000d0b001648481400103044101080d20a03540040e00b076041c1080c5540c450b00444814040058248040340003031411050360031b0780b07a085030348ae8007900110184030b203ca2268510104c5d070044007280326280340e0252400402000024015a10284e886005002110450002c802d41c00724003007140c1c0c000301d0012424a03130050405400131582d031000c0d4440b8141603005510070b017030580c4140c0c410072622100b0300c0455240c881c05c8031040280c001004118806015034090f0352107c4110080d10808102c02880004220b1000c018203030740070107110405807079070a0203503215008445541c0003c07210300c0c00c0c0c4500820b44c2d03401003403d44c003070b00c10000c101c8500300710024507240a5600c034501c071487c3e05000219445440080c80145190409a0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 806700926 1250 806699676 806699687
    0x10609080f0307080a0c17071202010b090c04060507170f1e0c0304090506061b060108070b121b25020f0925030f020409020a02161208030402041b030c 66
    0x20320260320390001c1c84024001500441140d44c00242403401d01c2100301a820b082002c107c00d8487c0c00d4154000090342000c02410f050031108107003154000308481943c013028044140da00311414040c0b4a410802400a28051400390607418000c00e488140c00c000104050381c140c0c4034401c0120412404641d0300d0b4040a00c10321440310f0584111082d082030803800b0320310f40c0c82c000c900030640030384c0d12800024003545840040d01c0150952200703107a00a2219038009489030828002c043c014001c04602003200c84502040303c640c2d88110350020311907545c1050081300c210020300ca20542080420034842403443c0c03119001240b0344445004800e00103648108804042d00080040c0200401010403061080440000d01041903000b038841c0b41d020b8400c0114001c0c030003801140c101c07610104000c184800550b02074060b5807015001c440c100103480021601c80c40c80b0744502101039080b080c2001c0014860005190858405000815120b04180100301c0f005c01400300038000a40c0c9a0034007451640c00f4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 806702176 1250 806700926 806700943
    0x1120f0608120d060b0f18010c05010914011a0901030b0709050d1a0130030513120203070e010315180c03200402090312130801050c0403060e0d0807030c09090501060908 74
    0x10051140f810106c1e5800d6450743c09440c1030b111182c4801840745800d64046c008001a1540c0b103002001035400500d4a02028140412030040c81d600e801059190200c00e910703192030450700203120324040d070310b940e40700710100b07000030010302c00c00c10701150001e41512030003c0c203581c1511501031201255119000d82004820580c0411807461140403104041c03101e0804540103280d00b40c41c0f000300e686a604040e2402e01c610022803020040d00708000034203840700c016880c5035a10803015510803980d1110b03602180c54082c0000345c40b0781d0402114402480c130561001100114600360390095180755103512a1600302c940c0107403009000c0f82c00c8141509079211031112103000480d0214241821140480d580356803e10803440041c50000300e018184401c003401c0401010100028809458602d049141580003403000311000350926417002d074440d81c08500507181030090366450800e5a1950012030290250188602c1401195071004c60041c12030f01900c0e000e405103490b20041c0510740300c20a460a0f400 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 806703426 1250 806702176 806702189
    0xc17060324010317091813170d06050f061209120a110d090b09040903050403020904031707020601060804080d0213080606100507150b120106090504110405040201120f0608120d06 78
    0xf0170255070706a48904440031005107481c080b80485ea02ca04101010415000000c5c0c00507200b0400f104802c926030005200881103500b003405515601c0341030195070615100c840794090002c6c0600c00c03040802c0b808103580800c90004403900001958500052070740584040340c00507e0000000781ca804080004500140c80b40c505403001518011a08216010306440ba61040e40c450801009051280098401a5030018400221410180350260600026880340c0024104403400184002e002050142c102c4a50b40c65482035992542d03580d0b41c0b168000030650301080d07800e201d603080c01800c00c042d01c4040c000c0d0400529442c1001002c2040140030602c03480304000e002c1000c200011a12280740f296000001404030301343c010f44000503071000c40c20058085640ca000400103420301d49400c1300c1c1c0103501a80c4c0d609450070307000e001e010644408480183c041051207044070002c140d1a4010701d40c8206070304002402030785440c2c2c0c0605060210380b10400c007041c04640c00902425900c140b41c002d001 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 806704676 1250 806703426 806703473
    0x120c0e090c01080106120902060c07030c06090f06080406021b010b0f2d06091f090b030c0714030417060f01080303071b05010204120818040c170603240103 68
    0x1d520008001001c1405103408001032110341009601d80c640101e100a6402000036840b080082c1c1440e5490940b0710041d1a441c250000000340e4501271200e40c401c2c0d421000c10200010b040101c00e4510a5024104a811301d5081014041c01d00402c05072060301041c0f4000032030412010800c020f40740c681c0c0f00c00d040c40b03801d4480d0343c0c070600144620703940314504044410f049c240c420380d000118507010710018190400880c00000111129956450105a10903160248455141c2ca041042400105d8113022003141c20090b14011848000c03184266071a200110791401c0d03110042050900391402590800c0d500807010710011440c1d40100714090f04c4044015400e41c5000b14004181b520320704507510034421040c401409100081d01210060011a0788144042a95140134180c0c0e900c00c1c3c0d0500143d070b120310190403407440d081c0030381d1901c6049507541d4070a46034001c1124402410150103558580306035006202c00c401c5511114200b001d404003d02d40941c0b450500c07032034400c58098890b22550 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 806705926 1250 806704676 806704693
    0x40602091810090e0f0307051018020f012304080d11060702060117100c0e03010b0909120d090507060c0c08010b090a05150901032d021513120c0e09 65
    0x15104070b0703407000c460440e82d000c40c485600e04480e600700510205801258000050082c060010010b1984a81170100c2402c00c14180d009100915800814200942c0f0900320391400c403d541c8114180c00c021207426081c03580d44040026106c40582c400d0b80008020380140a241031400c0d0069801c0107a0b050b041c01074a040e00d00810000d4440d541402011100110607007601900d401c100582182d1002ca03000c208490085014043c0501d400120b4891103036003008042882420030080142c000d154400c014202c042494480700b0f004d41000503101030781556500d003036001c260100301c204010419a00d9100007101503040c01d070101122500262820b83c140781d04000151900c243d15039005048160024460315601100c04c00c1803c190042e0741e109079240c00200070f00050b2a090312000100100040c9240000c1042079050b45038904081d5004038010120410b84a4540003005040041480385030440c1e19400c0c2510041ca01070000c2d100f0300071560003400000559481e550f000300c09900101102e0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 806707176 1250 806705926 806705941
    0x60c02010c05040f03061e0e010510080f150c0904051504050f0f010302060702040b030a05071e060915051c0f0b041a012709020d05060f10050a050d050406020918 71
    0x40c0062100804c0303161f50f11200c403469861022a61540000c203001480740c201c801c00740502900007510f5400ca0b04c0b54509001400443c009541456040c051005c2d01c3c8402c42880a21001100100340b103451311010071032542e40d0340e2588122441034403a00102d840c00c10940091000701d0308010606000000d844003030101c8001145501d504595048405660714a45803003c03d01406c01d04041d241c041c400c285503003003080008034014054a456002b000552519200d500603c0c0d00c0520038400400c031002c43c140b0138a0311440301440070199600301189008008a0380308103400b040c103110b1000a540c2d1661101c6030940f8062140002404c40e42445410944001120350841460085044c0a4a2003426500807100d291801c0d0301c11600d000303100115544c0000e0000780d4821000303841490306d48070004000d8075140c901d040781c000300505142036454001c6c009480c20741c00300b100d5009010080c85800c880007094025140710b140b06160151300c03489070a080c0a500d50144403040001c40e01b640800512 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 806708426 1250 806707176 806707199
    0x3041a070206030c030705040f09020a272105070b030907050109151101110f120f1006050f13060903021801180c171501110c010807081f03060c02010c0504 68
    0x8010501e41303155598845480590391481280d204a9039201013180004480700f4940c0507101c00c0546840ba41c010b8814030402c0140020740c000c281d4240300b444042071000301208214807030110344140e400041c0b440030392590391500c0c03c1d607440707218426000010811900803d01c8808001e02d030a081c011201d50400c448480480000030083c805c000d4442103180640000350400c11030b4009003240141d40b119041007806403607200c0e0008050b584c03500c0c0d0110f50095100c48229110380603210540400d40d0600c5011100350303001f0741a840c5242c100f4048181000c40c41c14900f40100074544078402824514070510250582c40200520302188039401040744000c0400d00c00030841c90b0300d00000d41010400030540d45402d0780d2441030505d4200004014469083c04403122243c00241c0721080074141da0f0030321595940d081e014503800120710b20045960b950007984030035080101c08000b030341e003020010f1441081003025441078a1082d00c5594403120750b034082c80b0b034484246261420a24042c00e22031007484 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 806709676 1250 806708426 806708431
    0x41416090602030d0216170310050a1410020f010606080a23040303020c0106080a0c17030408030a0c14030d0504111c02060a03140f0717040201230c01020a0203041a07020603 76
    0x12251700003a0b88130480c15110915824158051a41e2401c0b440d4000c4000300750300304944049440d08201004151803802001000840e200381d00c7c80c1d041101c00700c0c2400740241134501c444041d4400ca40d8050a00c5c8400e000c0c1344003800040d030f03c0f00040d2610f801d0140c1038078165a0303883d082c86100e084845042c00c0c2440090790040e050304000d0b03510074444081ca801040745600201c49070054a419004012445400b80101d401c501c103402c52140003a00380e03e80740e2081d8411849168020046007040a0040b030b482000306024441850f80350504421860031030b4001d05811004c1e66071102084200000000c45140c4624180c0c0c84a841002c55554100303964203141c8083d200f198003169840219201f038119800080460101a01a00f403901a040883da0b054401101040d60400c24140c8400401071a51045405944400031402460b0382500c903505d052540c0c1d503c84000704440519003070240010b190400785035009641e218a0900c5203001c61a41201e99042d07581c0400014016035594010380e40c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 806710926 1250 806709676 806709697
    0x904110d0312110405043602030102130303030f15260c03010204030507080615060426121218070b13030204060308190908062404141609060203 63
    0x45020224201910040440b548203a009410049000421003000700a003007100d500361028090301d80e81c05805d0280c140004940c090840030400314000201d50840c0f1041001c0c00070b8001490320070000121805101c1d2030708103402080e02ca009115106078030703108021003505a1004021200d040040c07400652030048040d045159a502c80b070402c1030b10600c024199264024001c5540341c2c0c1d03c0c41d000785c540c0c0c424809d401d0940156400a4103000b04c1c842d6810103d40002c180e545820f0601c1c0c45c0302582034100d0071000c042022680c00d440e114208000403000f80340400c070300f141c669500082d604000340f07004002c011452003560041e8601d0100140ea0303000d41e45100822034444850005514004019074000f0f580700c2e051413000400c1c42108001000c2c1000d0340018010760950418003074400801920940210f41c2c04040043e2035448001130021070f0072031465840e40310303e20701c40000c1d00b51240c4403a206a500001400e0000018202000440019044c00d02000851a0a5019441c1d0041c104601c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 806712176 1250 806710926 806710939
    0x606040c0513240305062d03060a1d0708030711150d02040f08030a0f0807020a08070c09060e0903390d081503060c07020a08030c0a02030c090411 64
    0x14080e24020026a0320500d009074201d00e1565072510b207681c50800b003800e450075a803601d204039554148640902031140c1c20180904c0003074082410041e940709400394904440b9135480c448107809641c18049240184001c0d40c02082926260341003c40942a668034111a940305e0041000490303c044150b4a220341c004507280084150140818081d1613403940b00302d91440002072078184401313203502800c166240c001d03030605d000ea04c0e01003d56403440740d0b07480c040c00f01d00340240b0708101c14400c6200781d03881000751058030f94410896a440740c2c50307003082c4001c0361081103540e010300c215030661117800000c260210109442d4101001c05585130310400c1c0302c4a8100120b100c155815110903d6410b99024100c040b0100310170403000303041e80765060200c4d007400041001c0e01103a8040504110044032900c024007800307441e242d1403048003003584840001c0740c0010003e103000840742400c0c8040c2c65245054005010403150a104041c00c0414964115104160f12424040800d01040e002842c04006a540 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 806713426 1250 806712176 806712191
    0x20a0602090f1203030906070f170a15061d0d08030c030c1c020306030c0f0105040b0c0106050d03020709060e0f060913080a030c180b0909042a140a030203060604 71
    0x1098581e40b403185283e0700940c0c681184211407400000452040d4010700c1522a240c5621404443c0e0301602e042ca1400101c0c03403001162085907000d4219081800d0354070000324100021001e04902c0d1155000c800450180d5039000c10050440001400000003284d031071110000555489400d4000030304a00b9007080e0100c00500441d4003075040300c0103006264a021003001840001c1c001035481207424601074083c1d807102445c00d0405603100e07032070010145c407500d04160608489601c280c100391011805592140b00006030360319000180440d86000754003902c0e18031306014400c800d580070f40d44008100c031601c05c00c100344240035103401a041082146d0801072a101c0460041c0003048010000e4003940d40011082c02a5415911454403c40c1ca502c5601c000c07480c148100e07600404a1050300c062690070000301a540c5001180107900c80c1c032070564204010003076007144882440c00301c0448101d140c014400c1c07000704242910060140030481d00842801d040da8086a21020041c1c4814050340d200c0d581c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 806714676 1250 806713426 806713429
    0x507080c0705010204080613050f0105060f0103020d09020a09060602120a050a03050411130e0705030318012604230d0e04020307140f090103050c040608010311132d02070201020a060209 81
    0x445e00105024011261113040c170301d5840c201000507881c12107039403141c0780615104500601403940700d02c0006020080c031010f0180190003030342c40311907440c0006d070781c0e800001d005a444c4e81111001c0e007104080000c095091603406464204040d0305000189414022003a44c43c2c0d010084565907046440c0c0412030351250318205104608400b4055803200c0b0100480100c040503030b10921450b61590110350700319603180c05041d140d03c12120313040800d012484a425140d4055124014021003800030160326800c4d00030003401c410000d450407a0302d100303825034050309400000c4801000c09003800245c102480c405c50060601840c418405014075000300c000b4424500030224480700881341d0148030b66503200c40c174000540b5804003900c01d000c07a141902003800220120251070944000791561420369003035464281c0710140c2d407810740764000018581c0400300e2849000d140c440504080140a0403541044505c001074100c0e240d40080c10f10510407080541e80c001409003500b504004016079500740d000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 806715926 1250 806714676 806714681
    0x705160f032904030c02100e010504120812070903050115120b06040e120910031b050d020910020109050708032106040b090c030f01231905040e070501080a0507080c070501 75
    0x64000b190b50a18204410b058004000304000362084030303003c1c1c0407024038006440b001c0c42c45941c240000d909000074800b50084400080300c041c02041c0207410620302000040c00c140044503443d0018400c1c04e41001004001d0248100100b0041d00c0d4200e403e0500843c22840701111034007030001c07603d020102303200b83c9030b5a20410b06800c06105560084403010b021018940c000e0b00c0850049204000c0403a100e0700ca1f11451010510340302042030340038503c05040329146c104d1a1100b8100380d082012841540d21683ca03030150540e02c0d000031501380c0c00c0d81441ca007010244c1e0b02110442e08100700440b41c0f443e401c82254200711651029610b142c0720500420000e203015416070741c2058148050108890720500075522508462002c40445c0c0e0300d4a4180c155080c20120300501102c0c10350684400785004900107207101c4e140101c103802907030f0f80c1740044e0648000100031120b540003100d06108650340050615413210f00c040c018060b42c01c0000001b04002001081c00400350740100d10201001420b4 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 806717176 1250 806715926 806715983
    0x160605040f0b010b2703120c070f090c1101110a0311120c191106060607020d1a1b07020a0b072604170c030706120618020705160f03 58
    0x218102c1d0381580c582003520b50aa01c02000404420309402e40c10030302001d2040d200418082c0540602030048840915003916000311000f10203501682c180072600f180005200c10003000380400100d1100c14172080a0801c142c142c002c101c0590410151510b0803592100302e8109424500e40000c1c0080035003040f990a000e0700c0c100341c100c40580c000340a001e031125030140003440101d00080311000b118000c10356403188041d102081036003103800060b4203440c040010306002c60004d450008195126a9514903030501060740401c2044410240150a40d1044c015144410403c0002d0f1038000d540d000528219268460312151030000200441080b400b0300e202182c000f9008290351044d02c100703c0c00c1c040b9400a00841d10010360382c1400c0d204140c4005100e8800e054054090180e035400c0c141300f120302d1300c0900d511784401500e840d0002605116400010111140b40d00c0050f01e405141c684141024410500c258114510b06811310111043c1491541101c0d480700e490340c06d04c80001515103448240 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 806718426 1250 806717176 806717183
    0x13020f01120213151806081312020601061407050a02040f09020a06030b2d041a030a0b011409010602121c0606080910050705040b07060e03071a0606160605040f 70
    0x880c41010f111a40070000090b60b10007a00100540d824960131104038840e8114104c2c9515800402c1003414010302950343c20409090980040c1f40154a901f20300031150400a00181e1018004100c6a6131002c810307602225681049890880c02761189503030f99501c00b001038481d5580c0c18040c1c0a549956002d4008203501510031010181e0f91031004d002820707a07650040c000e02e2800b40a0680700d03d4481140150030b0003030740505058642100303100080c070404206c4002c908508030300c040d099400300310f4681d040d841603204e070f040e9605050000c0f850100c14082035002e0403030074006000746500070030000c002219040095842c3c2038030048080044a0100740d1501c0c0c0c924040340400c1030b640c003401c001e205614100c121120352090003a614111101101c00b103000950a1106100c8101c2e80c4000700441401450082800c0400c1c0050a04607409400205c40300c00302d20f00211100f6400d190701548c010f0044070801e00746500d4079201c0800d24000307900141229590780004040290100384102d41c0c640 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 806719676 1250 806718426 806718431
    0xe0702030a0819180614040308130f0c0801061a04080303061302040b030c0a0314060306070f090305031218010b090403050702060d1134240c091d13020f0112 69
    0x900b80600001149004004e45005040c514460ba03110a02450203000d590302d52765050f4079a480942c0c2c01014154010100c440d203101c44003c5000c68404c20004000d4013041d40002001490116030000d01c48500041004060061108100303450380402503a910410035250010041102c1c1c41c200000d1095801070501010080706000d12103104d0301c00382100c1013032502c081150707980845040081d508101c804030b615070700100c000f5510a1041100030b104100d07a0030017010658881e41c5032411074000d8841c1e42c02d2001001c0c104071007681040d80240445c3e4074100200421740d01d500100741c0a8030000c2c00a0240300c07000036071034215100c042c200d07240c0f029910420890075158001c0c08031301c0d5000104140100e51000311802500305482400a41c48a5443d1040c2d0304100c0c6650300c910300b101060103080c00c03ca40c0310400c9006040e500404a05260513a00c03591041d05090100001c40340c84140200c2e140c01c10f200b00b241a20b2040303002c42c0307200c0c0c04441030b520003981e200040320750448034a00d60b59100e0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 806720926 1250 806719676 806719691
    0x20915060706020c060118050f01260a0609021810050108060d1406010608010801020a02071404061706040203061503031b100c03090b0a090b070302090a0f0815010e0702030a0819 78
    0x40405c02a05880341c0400d55818864190402e00135114240e4884a2001003040100182e81d41110a119807500f404030007051089000d1500e803e0040c23000701070351456100d085e88030841c901089044002c2044a1303d10307080e800d1a40c015880c0320042d0248a041c8003941c0081800c559500242e00143c50b4004c01c6c600015100005c1c1c1e03a1211003c0c490319001c100050004100c0c0d41060003a120305001e560b0040050928041641c124144904522a0825903031440415803c460340101001451842c0052400e0305141c81894600280207045403540b21014801c1c07102c03607602004132060f00700c400041001d00c00d4000342d0781c1d003000161030b12020424601480d5251041d016007080648a01804080c0003581e1503180c02ca0030307900d40c0503009003050300100000d10424040d60261500c9440a000240f035280c0710311500302445000c0d00300710903903070040a41191204201c40b1140c00750500c0b034510301007030601311800f07542c90042d44030041c148040c41c0c000941c083c0c025480301c80c00781010b07101401b100d03 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 806722176 1250 806720926 806720947
    0x27090403050a08010605160f021c080c0d1806050702010311131a070203060c160f0809040c030b0f040911060403060605100206010320010e0d0602041e0302091506070602 74
    0x154402500500410444000041c1450040017910380c07d0104510866400d0721541c2da400c050207a140080380e000c000b421840184000c0740c192850310a10854003582d0350511805d40a15200c00c0501200c204092180d03502040c0d40c040ca43c000c00c44e4030341c0c280181c503464188010790103405100a400341c5554040b03101640900314088440848040302a02032a0080804d2000d1152185540294066000002041c1e00310a250010510240e442c03100280508140c1c0c3d44115400606106031842100402c221340e0615061083d0310744d407003080c181040600c81d8040410702c002a000076180c45140e4a01c403080611291420500726282e000b801241d03556140e140c03d000030701c40d07405003600030a46040c032604114000200f07541070300c0d002000850350804546081c2418207520040c0ea040003140a2620f2003a207554000000d61403080c1d20241e100c90410f00402111000741494440c018100c000800258031a0440140c019074101c1c4d42410043e00700c00850740f0761203010001131880c1e20008682962 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 806723426 1250 806722176 806722187
    0xa051027051512070c051501030302060406140402030c2215061e23040302101710061704050f12070b0f091b0310060f030b07020604050327090403 64
    0x15124115841030070200340c4460345440b806200c03a441c070310302c3c0e001c408100d02c0f6024101003283c89201c1c000321024040c1c1040200e4021500780c0c801c85c00b41e80900140410041203000d0078084c209562030060061901c0d40019a4132030b84d114560b806440810700000e44040d6a5007072804074604544103004010000d2800c0c00e215105204140014011011050f24034900146403c5811015950224003080c822a1000d1401c803d220317107690a81c04010000c010b0315041d6880703030543c0d100d859000741c00440158041d91440001c19031400c04081c00c805103e0036030415408407500541c0800e00c00550307940e103801c42c0380010390050340c40382c1c0c841c8104c1c0645140840b40100056481a620514503032101c0c4000704100a090300c4485d0b40d50400300352503803803011100d40010011401000c45d050b1140202d021411912650003103119414100003d0090003a81c030341664004d042c80c4000e01d07003480d06465031500e9006800b130070701482840c2d00310500c034001c4041d200c15985800030100801340c105803501a00 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 806724676 1250 806723426 806723429
    0x100c031d0423090a0b36060405010e121209100513060b0f060a0c05100e0a030305011a0f0f0f1314090c0d0e0a0602041e09020304020a051027 62
    0x802e24031100c0000c0c1e030360340c01041c034921443e4000c01d480e0b01510f8445484805080805a04e01103141588800c4c241c098050030240019010030054102030505e81009425107148030542c01c030f1603003d40c10481003121a4400c0303034208640c0c0f425000007503c0e60310005040002c1c080103405464182810303c01000d00d00290860940d1055404006101001c4240600c0080e1110f0304d5500010504c45038440a01481480c60304c01c0c0720b442a5101c404000c042c4000302c9420741091b860302d6000851200400d5090311545015210110702e4201d03401caa90701c281c200b03104440d8442020300d0045050a003180440e8255100610300a07155030307d80c89488000200481c80e4810039402840c200f1400ca5982015031001b80200340080c3e40c10701d072080c0444018040e00c0c20441c0000d05201c0c0150f820003180785031021b032000e00f601880c04200f0f0b0440150004100086422170080070344104103120050342c40e01d04003411110709071100d40f03520b481840c041e141c000d01003003402142008650b5070120506007920590 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 806725926 1250 806724676 806724731
    0x2070213051e0c0d0f140709051509030309150403060c0c12051611150c060a051f09180204090b0f13030504030b09120a020d0e100c031d04 61
    0x5500c07a03010200040c030b601c080d600c0d070040681c01c0208004120311908600d010000401c03011484400c000100c1003056400c0302c0d80400102d5640041c0040d203081c80f00111003e4400c050306040040090009460384525019144601140c80b03031546008206019540210340290f420840060300d03803000340111015400850b191800d40580c103640e1401001680e00f02e0022000711208000725989200d004007a1001f0243d0110030992101c070b250580714000c100799003080d030150001e410007026071070035503101502c1100f05002403041c5411220b41d003c000012500c9003000070558003910a1401d1446090350310194105040c11128000d00100355052070042c118210240583c3d07503441d64005240d102c07200010001a020003040012440c1080080c0c0c002e00070105a421021101008211640c400e40054000d81c00c0b00142001c45d503042150030341d000741c3c2642c4c1d0200213200c9110041110090311070050070701410b072441a0440290400ba030a52001c068030400a2500c40000ca0000501501d42c13a07 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 806727176 1250 806725926 806725951
    0x10020a1a22080a0e0a0b0f0c0706020a0201080403050d0b0a170d050301211e030801090b0916080a0b060a09291204080d0920090108030f0703030207021305 68
    0x41689800e540103503001c6a00300d400e00b420b0981c208000c490071940f0810705640080044408a4841c81d05001803038650345030900a03660329900300c0c8850410246900400541d0040e128810150341c00420841c0d000da41440d02983d80c0e41000c41c0d4000418164100e5a00410711840200fa40b8907840302c140d1441e11040c0840f0031b48029548104c655201c24000c091030408810303000ca92084071f481285030218032580140058500f5004c4d100103480c884502500003484000c010400e00446200d442c0302c1c0d00040e1210005450000048d03948000000100f0301041178075400220201c207190301520411000504096030f0760459103004000403440c0c0290b00300c0e4141e89103501d0301807100d400440100d220030040241032440300710404401c0c41009109980c1070b0000c0080e082001881d1088404c618860051812140e50301c8000281c20581515418001c4180d1b20041c0b2100e04004203840039000b0200d00b540e600c3d4210b117022070107801007120094020072281444021030703001303030401e0744141c001003180b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 806728426 1250 806727176 806727211
    0x80c13031101031a030d0309030309050102030a02070b0903070201140304061826031b070305040e0c210f06040510030c0f0512030a08040209220309030318050f10020a1a 74
    0x90904c03080c1e184103a0580c031607010701c03641a0080c0c1042000902a0900203034000554603001d099920403111010301660000310a010000301040440e003224019000318204942a0b00191800b200c011040c034640da404400a0b081101d84d070014005c81c0c900c01000020341000d460245400905148032540000d8030520845001c0800340c1074a2207104030301200d20131030000d012045407940c041c0c4416810404204404908001864806805402440c003015594071807644a500c03003034010069550341e16010001d11a2003160b042c29283c20050445000a080e1074001403000144810390009041c00c102c1312740002c02041c0c0509280c06c4450640c0d00b12448031001c800140ca0b445481c81e100042045a00801d000d400e0040d41d42e980b0442007a1016644109015402c2d81c0402203502180000c80401045c000c1543c0b10a09a8684501c542621103035400c090020781c1052042c00e9030b5001d07018084402841520801600425a4010800441c0800d032003102c074000c40b500f120894270400302042d8 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 806729676 1250 806728426 806728451
    0x7060b01030b010e090103022404080706030f020405130507110a03020f0f03090a0e07090909082205030a0b04050c06160c1a0d150e0a0603062a080c1303110103 70
    0x30a0407100001708400807503801c43e0308104403800360134003202400f0818080281500e04a000900140c1800d0300200a0f0900c1c195000341074031107004071800003a0050100308480d4544060b040c1c1e001010200219236170781c0380441114000c0d020003220030310303101d124420804e041d00400c3c071400701e04080d0180d80107031010382d143d55501e104005085070020607411040045103e13400d50703d80c000d84280b40200c101540c803105003054801c03008056481042c0002e802160034801286444903602c051400da640519002c00a40c481c101000007401d58140724001030704112080c003000030040d00c0140300c25111425500d072400056445441162504200c80020074442c280c48580900383c1c070180c20302417400401d0709980000e06001900e4400114a080e00030540445109205103e00038a00f40000c1c0c45146003420415142e120302602c503d40c1b8001e4050090b4009284541d64144040c1881c1c5410340703e000680c803141c450f501403040b11040410002c003c000c807141103c0c1c04290700745c0e0144010301503200b = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 806730926 1250 806729676 806729687
    0x60c050405031902030a1e020a030c320d050106030f050606150c0721060c080910090f020402030c041502010516021516090806270d02030909180307060b01030b01 71
    0x83c020b94103911072a404400919031291001020f16100149801900680d0204035034551076017046600002d076400501c250380038501850188182400609944500c4240c40e500110034081542d0180704143c44c000280700d0250829001541d100e540900c1d81903e504145482c0d084c1501c10394030440354a000701207824155016141c803552064050080103103014071a2a14480d564101100f2900150f14600450030078420240040c1180c3c58980c000d140000a081c14000703030b84081c0d04400c1c41d085000c0301050580c1c0031009404d43c1038034016903070745400e182e42c01c1d103010355030001100d07040104003008042c3c0d041d000240a010005940301180728400c40030390f11244401510003402062a00003210022410700c0c007400039a00f4280280c080b61500d40c1d00381000001c03500841e41200c060f00410038542100900d0341609841c0b4081c240111000100a403248504034480d0700c680c022401103440c1054800d41d081007050310700102c1c0d80d520402d1404002030580314401ea40840c0c682040645154040c4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 806732176 1250 806730926 806730973
    0x60a090b062205061201050a1401080d0c171306180f44071403300d06030b0f09030f0d020309011407050c0f070b0307050a0c060c05040503 61
    0x22007a071040700e0b03040611240203003001480c03e41d00c0280e00d600912010020b21440d4060b0096503c08100c10041d04011618458180d20000c0c142c0e01041801d4101031b401224554819404000303044800320038030564016000700d4800040c40070aa01d070015095410400711200c5405103039883d0626583c1e80600c02100d000c5200d04100021402da041030984001c105100d40c01c1600c185801c4400c129002e010208894081c500841d43c0c4603660034890110145031308015400c08400400c03201c441d03c403004101442007440c3c0462221052030340080b2428810503290590721400c410860b896680c1004010420f0540d8407440c40400c03d408180c403110040102c4a5100103410ba45181a0141d01a200250310042c03044c5499560380c0400442054156546c0d802034137543d642607200d0140f0f0f035030342e0306004a03144c0700c040a50040306c04100d002c20035000c1d20303400130140c10a00c0d156100b080041da9180b003803e01c020607542c6425405002207802c100540305440c002c0d000c4440080401282503a02c0092 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 806733426 1250 806732176 806732209
    0xf030b0f070e10031d0c090606190c0c0e0f0a0509011104060e13090302011e05010e06010509061b030a140309190f0b04062a080a020318060a090b06 65
    0x2240140c02c460074445110002d0700d80c180340c009070042d0b24090010112419815011050700180d080c0d09036031402c0790752280c10907011101e981c6444050120508100a0031040360309000e61800107100380004010b0b10802400300019010032441c0031400301c2c4262804030303030a000c4945418040340f0408414400c0c00d07501e111500400d840c0c03905101c1d0a032031102c0e0302d03145168403100f04154060a0940b502501101c03178400c1c2c00210b00d0b28124000484442103c00c1d0340c025207440c000c0104140458401580c0e00010300b0308000390386101d080082034851140c196038508603040c005000c03940040000007445121600c2d900c94031728405566400c1101d110036a0b01d44690391110403400c10040051217a0030b0324034450099074007400e005a6603401d02c40e804440650b84607644209092100e40d40808200c491605502502d030800000d240140c120382c0040c0c40110400c0e40840010207220240e42485076020790f8000316581854020b10002c042e0154100c11181c42d561800498100e00f488400055410705 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 806734676 1250 806733426 806733437
    0xa150c1b0321090501022206140403120e04020304050c09160e09070509030d0206010918050a030e12011d010c210f060e131a0603030d0e1203010f030b0f07 68
    0x20b0b401d079034100803540103241c1c4589580e400e407900000c0d609100421076046c040191000701503000b200d01c141810030f54086000d2140e1100e244000314592070856042e83d50100032201c2002602d4422074003481b403c60850340252000050005008000558081c0b400088414070b0403991422401a00010341424003804502c065021101e546003203c4102c0e8000290b1a04034180419140001d240103981c10190002d41c01c44401801040c3c418010580c07020484240c4884030b5241f55a119554101440c0190400c4080b800122007640d8041c54114010340074002484540f100311105030b109001418003031120f41c030300490009414000c1104c4085429250300695490b40501f1200c40a82003009620302d805560f4000803540d0031040c2841070003140c00c010511000c810750b190114091440b0070942045221060400c6500d5800000700e812442e00500d000c21151228006980b0b8016520305034840804040300124410201105800480703006049442040e2610100b100440c20241c1d121400100c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 806735926 1250 806734676 806734697
    0x1006140a051c1a0f06030309010e0603061203030a0f0b030f0c120f1b01110a021507050f070b21090703020409081308030d27140a150c1b03 61
    0x1034010100700d1480c584440c0c000350300c42c80390f031514006034854000881d90076289013441001550305003103030750140007030b40214038000e02d01001a11a85003e1720040c450071002000540c2c41d1a403424442c805031003581101d840e8200b491044028044600000e02c0851502c14100c1452400040030340d254110308014103039548000d0700340b10308610781000d000721603c149501c2d02880c00c000c2242800c42c005401609085125840004048400400c601302080c1d04c5070f000d400140c1c2d1011807241000e14131500c1255a854540b500b5800d0140303200340c1d00e5241c002d8040016010791004014000c2010400c03010f0100c074209004070581d20b105030341721100d90b402690140010b04283c0e005182e000e0140300c00f10300309a6101c0ca24418102c040d040517560f604049003010598006004001801e2551a0b9200080081c140d14285103401d0140140100165084180309500c0a00500c80c58170740100000000ea00341d01841c002901c1200419030000e5079042601403082a44132030a01078952580c0c030b051121 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 806737176 1250 806735926 806735929
    0x30a150e0a09030c1b0609050108070f030c090306060e060f06120c072a080d030e0a060903030207150623090f0901060512010f06050f01091e030f051006140a05 70
    0x1000ba1480072020b100710343d660709022a00011014807000c00c103a054004107828140d00900001c01540841d040c00025000c2c092011b03000a00400e2031002c1d40380000350103260260417034400700c040d40040c2155103040310202c3d0031a201007881c0d1082c0c40542d81c004c9640401428421284500701d4000a1003116001152001c1e200e07100400615019042c1c002200f9400e00341032900011241600f504050342c0c0008201c90b04040c4412180000c1340d08041140e00c66001c480340c1c031000c1c46100203203415610b02402c420103000303030705035200d0540145052001d4401444004000d0448c0e006143c185810301d2410001e00803181d040022100020b4032041d12a202d43c4854070440002908050040d500c5250104064840030091000f1008000001c40e0441141c4000710840300c06411480c021150380c503001c480f80e604040300c0021609d4900b80550b070200000000c131040410f030740000780500000040b000900000040361038611080c04401c015960351841c060403900160000c040d00309901c05400c01c202d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 806738426 1250 806737176 806737181
    0x3080d051b120a06030c08060f0a020a141605060106050301080f0d0e0f130f1a090c0406110c0d03030c031a010e061c0c11120301080303010b090609030a08030a150e0a 73
    0x1c01001c00e40800d8103a1a40d0720890a041c0c250000c44032903200d4020446509c0d104000c4c26040320035400218948481401c3c0240b000e40c0041c00324801100008154804030080401c140420740c0080035a8040d58458800074041d90080c82040028410841b0722889490082030342c98000b05192903070540e0074800402d02008050301400c0581c01200c69071030b50166034150103001c008801c60040020000c281c10604034101941a40742e6001c1c0b2404001c1101c2c10601d0422074095030504d0a00c019004d0a41d445a4503142c070381d50b01c00303030410b0b54002d40004050f010340010501648a45041c0724001907041000000040d500956000903240342200d080c60510030018010444074060000c0386241150000c808e43d00000c00080008400030081403449400f031051071016000c01c1807080c61540f4003450302c2e40e6800103008450700d21a00042da680c69030355640855810707420250a43e1180040c50038107500700d420441c0e14014180c02c0600a00c4207680e400c070400e060303542102030301e0f41507143c4100c407800 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 806739676 1250 806738426 806738431
    0x9190204090f0c090f090803040f052b090e130204150f1e06050414013015090b150d02040b0c01020c0c1f08040201021603080d051b12 59
    0x3045559418100041084a20402a000c0c02a66a520b020746045181c41c00c482c0c4208180c0402803401d0b080c5000502a00b048036042508060b041e007941150381000360400b201c1d000d0780302c03480c19007580001c00106a82404900d030046511469003490b517034040301c0e00c690b100312680e21100c215451210018901540201120324250a00c2c440064070358201c501075048940141602d0f0350040710324101c6030610304c1100003518552911504280c5410380c01d040e00c43e07a0200315418013a803443c4c900611156078035008403080240e00c00f44076040d40301c108980180000111700f074040320418008613a200541c003407400b62000c09000640003404141d039100c840d40000b080000070320f80030040050440c400328041d0140c2401d0100040e510029091120301d00070b1000c205500619914082600703024228101d60000d0413a810562110341d11480104d080c0718120302c403131150200c0c00c040802400780710f03c003500030394102e40c20030070142c3c039042080b0301501a070400703070a0301d844100841803819a000b00400d8 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 806740926 1250 806739676 806739679
    0xc02010c0b0c190201020d1a10031a04060618050114090d0c08010501181505090402040c1223100b03160903020d030c05060f0f01060302090f040903090303120203091902 74
    0x508001c220300340420044800d00e60f40c00140e4001c44e01701c804e43c10398800c1030b00d4052a0407200b510b508018003c5000c1c01c08021800c014196500d00e242c0c03c0310300c0030099003960100184200305a5440702d501500b419141009039015030600b01011074ad9500541c0c0e0380c0f0112400391403541c10210b148081041000b0050340c1152400b45a4100081c5c10b00e0034041c00d8060b000550036541046a0701410318111a182d500142002c40303400410003840d2035a071802c4d600240c050310042071034661004195041c51421148911062600c0030103920721013020807a45000d000001c00b20140c3d252070104080840150003081082041040410101261040b800380800310074240154070310340d80d80000e100c800d03d0700001d07404a50a5588101002400d110060b071015600d61015403e0600c5056000e06482c1401a013044c96400111f0101968400c650b1900c8010020403d000349056490000e04681c911310084000c1028200d80e0003a064941c0281ca108a00410040150781a00480440c1515581c4405d0303 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 806742176 1250 806740926 806740951
    0xe0c0f0d060b04060212030c07030c050321011505090619020a1a1009151703040e0108031809090c0907090b21090109020d110109080d0c11010c02010c0b 67
    0xd03000c0034007401c001400c40c50203242d140c0b40703001006410141b0700a44c4030200101002003040d1984400b00740c481c0d590300b42c0b4040c03032201c1080c54845c1c60751040e18500314624107048005920b61641041e4141aa00e5400040c0d8541903001000d42c0c542c021000031713580c003c070700348a00194003494000405401404e0701c100d854240342501c500110140b00c003c1340030743d61405410083c01c03409005114004041ca504200141d18008612a8410000e8000c4e6880c400000d0605500c014007041a203000e442802d41d002025650340c0d4400342d13242c2c0072404500745080e02840490f000c0c50301c2a1080e04c60b99800021b000e01140507010000a524001c1080c02488850703900401c0104050b07020300910540500041c1d6100000180724403071107001092044c15a050019200042c0c80f21240d0342c0c1181e92000c162040f9044107001601c1c02d044582080009208540c90851900e50144200e48524024a0121303c40316280d0300440f20788401f04d00103408200340c2d0380b4020000d18881c25440c0c2c001e8164464 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 806743426 1250 806742176 806742187
    0x10060b030a0e0102370f0c0b070e030313140d170a0201020f192327100203040306060b1213050109060501090902030c0d120f030609020a0818070e0c0f 66
    0x1a02516042c01121111005c490b121403180d198580300341240b185083d0619000f8480c1c0c4580041280e84a61801407642e558030012610311401054001400d5034000c041c1ca85072000400350400061281c85080c011030513040c54800c1c036040400c4003444050300844075505000c22490034403000c0d071203440b4400840d942007180b840c000a01401a1441c01450380b008803800586d804000e1007082c1d90b8004009103545040e5440304600c80ca030498250084039024945002100200748510507101c0402c00d0b040941c0c0d00200045031340c007100410a8903c00c1e4004c00c07107280c0710000003006020b01018160700040101c0400d0b481800340050728045446000040750407031590f500c0c2c10503a40b0030b90005050035226007240085160601130381070010001e50344920032540988a5540081d000342c840424403082c00020f0003894401c0c0c010901a020f240c0003507640c0e030207407100140003480803104a0f840d80c01d03015109042800200300c0728111888040c0c4c100c55510b40f8002ca00031580003603100f14444908008 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 806744676 1250 806743426 806743447
    0x270d02060a1427010e01021f0603051207150c090905040f0218090f2b0c0f050309010306140a03020f010c06050f150901030b01030320060901060810060b030a0e0102 72
    0x419a034a00410624400d5920402c0502c480907260100c1341031201020f0440f01d9644e000035910f0b6800e2070005540340384c0b0741100e40131005051641010b011400340c85002800b06070100000d100161086078400702c1c0c000020034803022188100030714800112074500400a59030329800c040e0f0058000c06001d038003038a4036030005120301c00142100a401d060300b020003009010900080100f0b1000c10050000c24001001c51034210304070464400190001e484050201440380c1520080682c0c01a954602c0384514108541e032500701c80e50701030000303081200201d58402031100513100110080c0c000c0f00c082e8116400c01c034124002403013003810170105640120200c1c405000c0c0c24001c014651181c1d20a0821100c0040c401341c3c0440341602462150004200260000c4819130449405240c442031900b0703082d42303000000302003100b60340f280c1c42010203010100c003042d40180c5c00c892100003298000440c011812044d102d991140c105014010300014100b50b03a5500819031102110300018034241d080d00 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 806745926 1250 806744676 806744717
    0xb0c0a1e030603030f1b060207210c06180305030f061c080702270c09010309230609010c090501030209180c0706050c03160c0c030c0b270d02060a 64
    0x1080100042c2c0c660070100241340e04024071201071340c45460031010708103281d1201404038000110050141c1d40c00948038050000c2c4d80f90694406103403000542d040d001c3d400000305070900f0301a0950701140fa241143c250340c00c00c4403003103110641c181c0b100303801c55540528685240100800b0b00d07402c903a02440c3c07400c001d24500c40c4451084e05ca26641a100d2000c0d00601c4001c1e848104c031440032020f403040d12200c0280158200d54403104402c100380c1e17a1300c8c1c4980128043c180f6000000e00b80700d001040065640c542145c200c0580e400c08048942e280d85941c0304500381d410001c58400407401c01d80007400154800d4000300003d4401500501020b0001400d03100f00d842c04491103c121140407400d14100421401242d0b0041c1040300c003e4210b0808a81e6101c07030382d41164142e000c7c002800079150410194421440046810480d000141c65503003460740200da122001100312040e080342e1805c1006054401e03404507180280ca40c071003030221a420701420758440300b20101842104400c96035a00d41c030310b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 806747176 1250 806745926 806745977
    0x6120f030a020327030a0219050a090204052e030c200601052d0d0f0b010b190306080c01050c0f03130302040b01050703020c061b01020c0a110d0b0c0a 66
    0x2030b8000c40d52100d004004400b180c0304a80b80f00c107070444103000200a580c00203000c002ca10313011628008124030400594110221640c403c5030403201e0404005103850441d4082c5c0700f103480550f80a03001c0b5512103016400103076031004040381d10340d1818030380e1501440b9521012050540d800c2c50400c0300d095400854004035487e80601040d84080010301c580e00b003052115140504030001040484034406401c1c404500581d10280500d8101000d4410320492000d01e24101d40c004c6441a450750f12001002c003c0d07404000380f1400914a000e00c1c3c00f00500c248147c0c000c40d20003001400b51040e4a00044803d58807007046107070a0703c540103a0307030314091090005006124075140181001455441070000f59110009040e040c0841403001d080440c0c5c000c1914003051000f241c900c2e580d400a015206010481000f1140c0290b102013100b01c0e220000084100999010709a5a502c0354800f50420004010b480d80c000d009030300e0000400c000c1281c55020300710001450509003651202c6200e6003000c0007a0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 806748426 1250 806747176 806747197
    0xd0b0a02040302041a0a060f0203180a030f1412040e0a02160210030c0f081905070908030a020703020f0a0602120304020625211d0d020306010b07110409020906120f03 73
    0xa0520585c02450300c001204014242c40c144940d205450450281d10384c060b0018051404111854401d00b550b84c2c81b640c800a140c5c807038604807514516040908268030404030000c1a0f114407030788407008120880980303003100d40ea45800c100d03542d0b40c05030400181d0040c0311241d0b84d00c104401000d0042e610700e100f54248040c9554002303600d00b81c0c6440200501c441001e00b00500c40d24009011092a0142940c0241e044880010a240e01c0708141100d2400f010351001e40b5500001c500c00d01c2017540480c6160450b4007c032110b1800c1000901080414039062103044050390203c8003003907521188401540c0d0141c0010500e9090085e071981494045070001e00382210307189140850320410001245aa2075100505e02d841103240c1c2000010b80401409414040304104100b08092655100040b510500d640a41610b141c0d5947d100c203203280d50001c940444072081d00940c2c2d80c1050405110b54800ca940090030081030342c5501081c05404c0b02c1c0000d0350000b0b03000f002403402c0045410802001c40d900c9 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 806749676 1250 806748426 806748461
    0x30e150c1605090c041e0801021b0111130e0c190302030108191101110709141006030b100e0d120f020f0105041203021308070305101a0d0b0a0204030204 67
    0x4198101c0c1c1c00d0941d641c01c601d20819401c03090181c0101c03204156015500310002c40030740c52401c8880383c12000b26a50010a05600001d80301d80c9d000030404540083c82245402840040c0d128a82e05841d0300506410038a010325680c42041200b00000700aa00035220066091800140440140d0b4000c042c408840109400100400c1410300c10803050f9502c03060495540c1c0d1109481d5515441541143c2c4080d04000001e0700842c0c064006200080081c52090b200300820704c1d5202101c0e01035003040351514044154a10006080f5019020348100304800410b0800e43c19409001503450003400441107801840321010440040c12001c03003810301b80400d07181d0b10000100440d009290100044d03443c04980d051400b4400056500c003462280340800d0709026071544003081302d14030f916585511401c0e161207000b0000041c0100030410900c007948404060012000c0003d21103081c4140c03101654003e410a681c520214400d00c0c1e200b90840008800940b60030354076000103050340e0400404020390032 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 806750926 1250 806749676 806749693
    0x70320030d3801050c1213271a0909070609050901030c0e0c070f0507030b0c131a09090112021f0507030f02031903150e0103030507060203090c0d06050a1103060d030e150c 75
    0x180300343c21902c024054112404042381000c909a101042e81201018503140c42d8803003400e003660a50381c40410042d001d8204881442d014141580d00c41e500d22407a008150011008070342c5d801d00c0080c0e1410b0320380120186002c64130f4400c80c0fa43c0000300408280300c4140034803412002501407400d8a10320703402400107000942c10341c181200c55400281c40078000300c20410405090300c0040e02000120382c0c2c1000a5861288084e070b80080c03a100d16041c039640080a500046504c40859210f091301500955412010303482c001852101100d289804602103841030001ca80000d00c00e030408800c054161065909003c5400000200401c1581c9180003080c0c681280502400c0d03102419802845660340e00c0b04954910384000e40148078507440a848140c0020004034412000c015814503203001502803013003900641003a8008010a0f40c08803140d0741480b0214460a02d6803065134000c2100400200c01e06d92980e9042c2d907000c54060015400ca4840d55044d401c03500341e41c0107011080390401c05444044e = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 806752176 1250 806750926 806750947
    0x40e06130e01021c0605030d0e0604030c03080d0c050304020d02060a0c06020a0518040c0e130e0303010306020a120c0801060f021513020909070b070206070320030d3801050c12 77
    0x18034210741c8118a600e1701d00d041140303990005080b01c0c00c010030b0a019101360781441c00b080b090312131a00b0162000c15142400002c1202c443c00074070490500b14070401c524202c1040c1120780d03100075500a98000c40451078040035151041c010210780d100d60412505403d038039a199800d07a0020000800822000f055440c000310300d1108202002008680c20030101c04109806030480344102d400c14002c080b1032282b01e80d441d000c2d903c02031a01600d00704581c1c4a603500d15003c8045e5110894100000e00007020a2020508a020364003800146480d0403050340e08050080f108030540000b040304511803511490304907084528158011030248046901004050060125020001d005031032181d20041c401c0003003050070010346061513070444030141d0310704013428111030042a00d8203071540c1113140700c40d910341480000010000d9450300c050a2100c1c45070040c03001e8200079283c044283c021196840500c00d1b5202010901d00d5040504156007480070307040c1d65502d040d1844415400124002420391182c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 806753426 1250 806752176 806752207
    0x1509040e06090d0e12120c0a0f050c0112090f060e03090d0b0601090b03102c1306050a0b010804020402130e040606140d2a1211130908040e06130e0102 66
    0x4082594030880c0c440103501718954461030301004225201d004656044244c0042c080711501c45d030400300320002c510050404540b62014003148030b0100700c220822080001450051030501c82e005000c40d04000e01d90345841000d0050103402d550940410011104245d5905606c0303c1e1580c0291404034403441c2c060009803611401c2e030003049214105001b00415810000000810ba90b444040190032100a01200300c0006c1028a00100b00c828941004526603180d4440345007103001d90014411a252141010103c52600c2041400124614002009070500340c005040340c2559060348402c9540d11020100408015a005c417041500d58808000d401503001c4a02d586001c1103031102411a1140d5481c1c1420003c015894200000c4c6e1490b0011034045d0b034000c00007400a00030b91000d19a50b4905031090700340300e0004921076020003410105040c604c0c801c0f01074581d800340c4450302d0241001035035200500010100e5078003141480c0c0c81d4440c80b40d035010315207004201c48005601c03212900c803444107 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 806754676 1250 806753426 806753447
    0x601050f0105040f1202010c0b09031e0412140703081c15180c02100f0f1104051822030c060b0111030301140103060306020f0c0d0305061509040e06090d 67
    0x10000103000c1813000456000c0ca07a0111641107034081986425480140e03a0700000000250544060700c04002d08940084000c100c40d11441d941d280205181e0f503581c2040c1d00640c0a240c84403d00c942005d000917800380110882d846031740c0c0881c0c891655030f5443c801a5440321a107071000c8040008081c0300800140500c81011481a50310030000d4200756810102e4030070201c411315041c0d00c0702c81c1455050700a0050002012400340b050102154000140000e825030141c4504581d242100d40703110008884141c030f080c2c91005010701040e039507840e81d10062000c0902520790780c1103940041103179003542000420142d0311030348401c90100b06508002c000c64182c088803d0600c11903e40074004ca000c00f0088905580548042100750806c240048000701a140c100402951000510400c0c0d41080005801c01c804040121015030740342c02c4080302550425548542c00c201e04411040440c4000c4005d0410707060007a100040050134032103968a00300060b105402e10ba0010f016000311360364414201341 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 806755926 1250 806754676 806754679
    0x2130b010804060902040e0607091e0e0109020f0c03032a120f13080304060f1d0c0904031403040f1202030c03091203040e10090c14071716050601050f 66
    0x58001540000e0405400184003c00035030f030b6600507108540d0303150f10080001d075002003151820719184802400200c018010348001c0c10300075454100310408610704100785d9411044522440c1d03e402c0c509000382d040010107c0031a00c040c04490601e19040004d188140304034a818148000d404128890b042201013404040c20010080f6a00200829007102d80240707800000d0700031991417a622048032a181c0200074840c10000003400181b00640d00083c030110590a010010000e20071018041c40780101d071401030580000b23803100024540141490713401800703400c00315400d82c8a01c10018180e48200c1d0b0807192100c0d9001e4213000c2c007201e000e43c181e0404c10750000b90b10703080080c0c45140d81ca0150096142c411112100c0c660341415040c41543c00034105204458010f04007e003001701d403e03225025100c0d55505c1c03c0c6890524a100303c1c0c1c40854090a4007605241400304d45542288410010404207002000c22007a030300c803c80c0c00d158045003070142c0090607003941003600704003c5402a03829a07 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 806757176 1250 806755926 806755931
    0x30105040b01091508061f050306100f080115020c04180c05091018020d0c200a0b012d080a0213050402030c0108041502040f17010903020618010f050406090213 70
    0x44c81a240f024228072000308090070003102d65581c81d80052008a00000c1c1e143e1101000030300742821075000b00145019038012038450754086100f813021180390303030003084400c000382072070004018880303801c0e0300201017003000c0c4180e60201140101040907500d000c0356100030340f09002224400e03c43d6034002c2c000078240131140e404035800c0003005d2129a400e14007030f81c05040a064000c143c072000590441d00c121850131010f01c0810700c0028080d00c5103c1c0c85413055103d0321040712078100d540d0042100d4900950026078100107900300300e07a1900c00307680750800080c41c180e0301c90f00200b00c00111209100402c01030009050100f9103205010b24010104115848141080b040c80016640496044110802840d1140c519541c0703042180c681c04900320102030403880007802050501000035003001788c51a000300c906a00d035890303855500305c8030350403409070050300144082042040d01b4808900781529030702c000729074602c210400c2412030306c0c2568200c40c0705580c1c00c0d0940c11401d00d400c00250b14165140c08 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 806758426 1250 806757176 806757179
    0xc090f05060618221b03091203020a03140906010602010b010c020d031b080309160509240d05060c09100f0801060813050610090e0c010c020909030c0d05030105040b0109 74
    0x20038080d0294940300c20112a1400c1c060015441e40f0704800b00e96803c3c4100e000c50001002180070003451076003124044170400d083e62000641c0030340a006030080d40f01581da00c4040750020114001d4101204030403c154503559034100c0081c0c0c3c0401180203050100103001254544103000e82101e00c0121030398184042806220301503555081101d0030150103040000b854640c5011849031115203120040c03000c2d0002c404d00041202c000344511546440c0c0c2040e8850544500c00c002c1e045004989009480c020700d42c4a07100845203254a500102c8003504d104001c03949541c070300d8102042154100e19074500407800c400c4070710784521910708040032410084268940500f00070301c0c14a050103103100380146840415150745428000d00e41d12600403096a15074100121112803040281c03040402e0f01e410140340660381079021500d5200c2f107205854503180c0400d07907130a020248900a0018585010030302c80b146064000348042d187c05180755a59a60301d44c1010104011110004c02e86070402c6002d600 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 806759676 1250 806758426 806758429
    0x11041406121209090a021306030903020c09040209061e030a0602090405130b1f05060c0c03010f05091b0f0a06180602280c0b1303020a0b030f070c0f0606030c090f0506 73
    0x1282d144403c00e481c0d000481e41c4001c0414003900c20380d036941c0d100140043d000114203074198441606140710341d0907a0715691404c01041503035641a54040e5011b10b005000c00c81ca840c1a150058000d1161300c6800c03200c1c085040003038180344960009850141e00062002da40385003500c030b4a40e1051228800f100420b00c01d445030343c80244014030782556104040908011801d0040c0c440d001810003c1103070b0707503c14412001d16242c00241d21f01b41e0103582060a1031040c4c7c1d840b07000d003a100d03c620000404401c02c400c8000080030510016240c1c001e6002c07448410241c17105202100076142d0707070700c0303001071010f01e01d21440101d082c992007001150003102903078801030403031207041442c203208080c491101e100c1b41c00c1007148c0c4540e50b4003116407602c00003810f80c904003c2c0900003088178000c071545421980e0320842c1e80070503c03049039108107610180d00000c0906014a21180c507083c000c036464405404181c0c2c9440031640640c005070f400320403070101048802014080c0030013034107008009020a050080 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 806760926 1250 806759676 806759713
    0x64f020f0301051303261003050f0a0503160c0b07050c03121c11090d03080105131802010c1e0b01090c030e210c06151014090105071104140612 63
    0x40f004080141040424280c206d584000c4004645142810356142c2400081d40525800c50302c003c607803034021288a14410326020900f0642990058091450109101c01c18140000454021100ba25040b14080b4110724071102415074980300310002c28220612004141c0741c42d10341d0741411116201080903134000d545070091251030102245002c01c040305240c0c0041410300a02c203010b90014a20700054003407641c002c0046040703c0c0255100d03500203850014240c01c0d107003104072105c00207a0f4502030324010352142d1940c01c40e540c081d448071100b0000224640e0704981001d40141d600341c400000500c6549014810f0f46548140c1e81010030070001c018510b540c580c0c01058605021071500e100c10503084101204680b0039010f41026211140340152141d04000144c14450f4010141e0b110f40c00c1200e23010b50503041028103c000300743d05043c504001100c1e9580290411103564071500c50500141c1c80e0340c01845885280c80303280d0440c0307184c0740f0240641a85500184c8290358848045000480b2802 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 806762176 1250 806760926 806760961
    0x20f2b0f021504032d0501090f21050f090409080c0303060f0f211002220b030108060112020114400314010204050a060906080702064f020f030105 64
    0x10205c40440501401114100941555014180c1e5003014140c808004080c40c0790540705205030742d8420800340101c0e0400c0081c1201c0c90f010045513003048504114100320001e045031000040003c1124900741c0d450405c550440d0340440b0403540003105100c45460686001510301100340d8840803401c10341400140da5035003d1015886c0c2400d094400f18111405202d010281780c0c90711000d6503a2400c441007c80c1c50103009001c0082d040c0c00c1d07040450032490034030840341201d8540004021a9083c94001220351401d200100d050007055030707131400d019100c100030303284102c101506444443e00c0790120884420713100080b9018182c05100901c00044843c8444060b0381d080002c05c00403d610500180c024452a0880c40d8881000180003a0040d482455036080e00c0d1650f42d01760030b5450702d11050341d031a0710079110b50703200c550301c100000c1b4070150304c3e20550700c01e202c980c42042d080303070b1051000303c0c0b2924000001c01110000c5ca07242420350501e1407904a9002c4243c008100929000c6890608180360 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 806763426 1250 806762176 806762213
    0xa0501050f06010c020906190b0403111009030b090f07032012070b070f0c090b032808070614070203030a0e0f0c010516061109090112020f2b0f02150403 67
    0x40d000841c1c09a01c0d210701407040b020743c1a190f038401d2343d103c156204103030700148411500c41c0c01c0c00b024070000341083d0100d50160384064640040d000c0c00d5075950102a0001004c5507a18852115000380703402040bc0315200441c0500182a6a40020490654000d181002c8180111100403a005503044009840710441e030350003242c652250661318202c1e012840d8103c0c0a00b040c90b4062000c207250201d640320700c0e5501012012100c00030010920104264010295518180c043c0361b00c05012a0004000b845003030701c00c640000d0a000c141c1d04802d00342100b0781d2000d006a0010040040e14070080c4a9817030354030300900082520b07060394022a660b80a04c03e004904200300449c0c4203c0c0c61303110032221868107502542c01c1c045484c140ba1a81e91581010321500e10500b200c030000140140720440c010005900501003010101d040e070f003404804100c0c1003109540000d045200b83c40c0e4071110b01d4014600d8440c1d04400c1c818902801000701d031024841580c01200c1c010001000000c61200d1400314202c2c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 806764676 1250 806763426 806763439
    0xe0610120e010605210106051e0f0d120c1b080c210a1b120b0604050405031b0f010e0106061b0f080a0c0c060f050708090a0302120a0501050f06010c02 66
    0x1010301c0c0c0501410307032000d0341001041e054601d03c40d0210030384070012884480200501e940d03c5040142c410301c800d0145d54411486060801d407800d00041d1200488005002c1c05a8000184c0d668403283c19040384860000c0c9a07000440204400d20a140150004212040f400142442a02500c40c03841c0201d00b84240041c0080140340701c05280c900b4009400c0c002603980d10310781410031a009112044d4a1255281d5046001c5641c010f014005000140c11000c8403100c8d95600c0d090000500d00608160b41e01e103c00d005160703d28403403002c4031904103821406005942c00c580201805e44900c01079080c90340e418a1028811194880350000591107514840341c6096110300b4070841c4100d034040041d210181c0040c503000c8030b60b0007515400c2d80300d10601c070030030815913140c40c2120046100c404080000c1c4c003c2281b5008981c00344054815504010300740d6010558907070000701344004990401245400000c070721014040300388074040d13001c6c0c82103001090714500040000c004212507600248030b500c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 806765926 1250 806764676 806764691
    0xc01230c09190302040c110d030c050405101103030702070303030b0a03111512100519380a0f0f030c090e0a0b1315080a0b1305030c03130e061012 64
    0x8000c2c0c04940107540240c410003c2440e46400180002002c0340d1031703080380c0b060300f15941c0860f1007882007014000300c40d52968102410a810401c07101051941c7c00c04001120512211040d001d000660040d034454005007a0146182342c080c050744e04158480b8401c2038104010004503c10102c50001c1030b81c00c0390754108002c41d11004d011035000c0d07005043c2182c1030100c00c111800000d880c2c08001d4500480e0890007040d004100c10007080d000d0b02802002c00f03004164810300d02c686005962410f0080740700050040030442500310300b43c01094111001500341c90441c0c2c606604010451030303040d8503190a12000c0740c0910090304a170001e1003506690f8003a00c0c000f802d580815030114084210080038003403025058444507000d0031038840314680800515000040c01400000e8200d80d15520501006041d0340e50f602c034000618040805560740c0c041005407002a0f8002d20041ca1050290041c0500aa00300070fa80ea50005d0004c000340d006091a402c0007503095002400b040101445503804180301 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 806767176 1250 806765926 806765959
    0x4050303040b04050a200f0306041109090a02040e0d350606040e040b0601020706030c0206061c020603041a0106030216021e0a060305011a04031a0901060b0c01230c09 73
    0x4030740720305c01818000360a441159501440140c0702d8018101b10744500890700e03802c0815032100029035000749505580000b000060501c84651603100c0c44100580310290b41c0350300814245c1d4440041d0030b40640015000c9124141c001100c8108444800210070b68000c0640c0142c024558010002000e0004d11000649980d0f6034022074010b49624070581a480c1494501407207c410140c4001d4054001c441000c12940d20074491284448010b600911554a034241403025901d0b030341414107044c1940b48241e8002d40c031450025401544100359a0607941085240d1030340030349060700400109401001140d003c4a282500305001ea5011103040040d0b0350001040c4102384802c01c00e041c3c00c03080d071010008a1580641c03025040385c45910603190030320300d024000089845a07010040c048900c00302507010361111948640d90243d0304100000d0741c40e868107620b1800390009501011169102c680425000c001800511414400100c03410382c0e03424100b904041601801041a02501408400c0c4929 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 806768426 1250 806767176 806767183
    0x1509060f060b071203231e180c011701050613090507050901080f07051c061e0602160e0118020706020a030b1203090604150e0a090b0f0904050303040b0405 68
    0x2240c4260100440d941d07030300c00041aa0800700054625500000b0600b1040e4024000c02e107685855070030741500324900000e07201068001400200104845180d25001d0000d84c040d00ca00403034002c0304032801c810004640754901060900003c1c1001091450b403088100b003801214103444084a10756102e001031262050410029408003240505100c00d10080d40c2e0081b0041c03003003c07002e030703103a50035599003c1c20322a10200944030100050f02c100b1201503c03403100f030111191000140f00100344c107a580d41403003503003d094840309280d180b00b048007002155010421b100d001c10b04868420103492038422a2580c0542c1441034410a0144808207d00a20298100e504036603024030110b454455040004004002c05146c070390081d00b034030711161072040300001a01d080d568000c109500d494100019013203d41d04c1c0078051000c0c403800f654412401da85542044016104414001031400c00020800820700b0b00f0450041c040c0100c8400d00010610210484c1d46c040d420408650741c940751454214034 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 806769676 1250 806768426 806768441
    0xa090e0603010e0a2d0203070e220302060a0c02060906011503150b0306040b011d010f031e05070807090305120906070c09020711041404061a060d050105040e0109150906 74
    0x145401100401c804000401c1e1619014a08070303111684190811a800c00d040d200c2000d000c0e47c0359021030420080c06890901752507220398811848280b61031021401000d00c164100101c006d0f0b0011030400c20a803107140b040d400010490702c000c00690070301c035121940703856040c061249041d101d807010542c55802504102e0710216440e00030440980da030b0390303581401e40007a154188200c0c18034118400300e42c07194070703211b0071143c00c424000e204080c603200664007141400094410705455050100b000620490785484000c251640030580e4606901d000b051035030014140c90902041030800e0001c41e1000540e0044002c00c02031f440c1e0b85001c9800000c016001e040340003042107a681c0c4010030a044c1a8002d4161144600311690118101e0001c00040e0f89030300300101e071a003080c0b00c00100414a60303082200300d40d592108025181d01c401000c10307540c1c1d205084014002e074440d401000fa50810348248003448940400030481e0500720b540302e04158144a0f40174030100d85883d8a0410b100c2c2640c403040 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 806770926 1250 806769676 806769701
    0x15030f0402013006090f0e0d0804020a0e04050d0e12070501080c13170d0504180b01030e030307020106031e05030a200d171e190b0405100f0603020a090e060301 70
    0x8000e02d0010f4964000c0c1083d402100d50301400c1004c012020b28080c040c617045541c0320750140910340f17903008085490750030051042e42d00c200854030005a04800c490464021030181014204801c100c0342c016110501e0001414058508a10100c03814a000700e0b41c03c007914401d00e050061030300e4509a4404600400000400c03411000100041348410448200c80c60b6041303d054410180c40c40c601910300d4003a40c41440203030030b40315101810074406a800500c4e50001418005000c2030898450342c0780d600200c0d200c50140c0e40d648424000d101424050071128030080c44507000035102a0342d15a00c0e4054080003c0c10b001038585014004045c0700c0d80f00003158005411102c412242e0b41c00100382611986414803012404004034051003510780ca008402400340452200b00e44034209040301c08040410344005455036100b8842240d603442c080e0794001c000800409181e0b0b030504051202403c140d50209080c107104005c0c4902258024104100310b5070101001d105580c0c0e0300340400d0150280880d6034 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 806772176 1250 806770926 806770997
    0x20d05010e0d02070605040b0405060906120403050918011a130b0c011406010c020307051225090c050705330717060d0302070b160503040801050615030f040201 70
    0x1d0061000200c00c2440d1001c3d50031100d041c3d69a01080e81e691245009000c1901001c0105110b14103204004180115020784003e1401c60b980c1031201d5006800c0d42c1c200c0000781e00041c0071541c1d240c517401f0306850384001c1003684142d52404c040550750348602061492140c01c0401d110703080f401d04000400c02413601e040607695410f030b10000d0328020301200e114940900c3e45d03034000c101c031944035510f000b5105502400400555007000c1c00c0088032903a04104404900c030704140050710360090109441402c40700c142012005081c490b280080da8400220001089070522203400490f078002000c110080c03c110b2002c1d180034142c0d40210008440e01141c4503000000ca0620207030310f601c06400440c4201000040311241c6a0b001041030003200c000016005030b0105034280110940c441c02810110552107404403840c14035901d03d811038010707070300c80001a503440c0c0030059030b800c040c0b81030f0000f007010743d0710203196140c0880c3c43c040c07002c0d0103800641040b03450326040e010000106890781c1609202600e1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 806773426 1250 806772176 806772191
    0xc030b010518150c060604060e04020607022404240c15050411060f030702011409122203050607031a060d0b01120f0b0111010c2705040f06060816020712020d0501 71
    0xc04d0707981d45003610a54000d51400030001800c5149240603400b5550061001e4909602034007002102c45a098100a040c040002c1d05441c40103588001e20003800c00200722022100c421081035138104101d400c0da800e11812010010000b40e9000c7c01c4884282c0d005000113030781e1036605012a07001d2032041c00700d8100c000021401251423580303016600c0340f102d640c028400c02c02903003110b640100c01a52005440e900c540765200c001040b180c050b181919030210703005100c1102040e4801100250f50007511107802100900c14103c3d4180528003484412050143e50030983c100440c85903c03681b1180f0202a9842c2d14840d03e03a803140c00c0859000366100c1c81401180c544510160040202840b070a0128500f11340c090072030071040c06150340c12059610788107500d0903450002140001e640100b0121130485d4080031450f81c0d81ca10070303014002c0184000103203040c200880030346843c0001d0040c00f408402000c0015a00340d0008540068451070403020b52203a03410b00c003040d20341c580404003c18035400c2c80359 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 806774676 1250 806773426 806773447
    0x1b0f0d060f03110a0e06210304030c03140303010f0e07173108070b0c070602030103062007330e0607021c0f05130b0d0509010c030b01051815 62
    0x1c5501a640644000b00c00341026400f04030210301144186a841d180b041c0019800c1d140014000d0b0f44410380d5030f03480100514644140b41190300a030021600303161452018001e1003d980510b018800d2020011032a40d41000c212030851903492041c2010303200c03210000340d60389101c0e41da0b5541481c29050281d03564205a18543d0500900c0c1600e0010004003803210541c554000c01841400e0b0b8010114503d0241180c6500c0c0082000406040c0a80010030900c000990f95200542c02107015170800502c0900d0115649503500044c0c03008096010184481c501007454040b402c0740c40c003005441c0c80304424440300000403407902d03220040302e03540c49d04440f407660b0900487e00700c0c400c2200b5804d441c041d6110010200c421101502d5010020b0070320100d0b180503034055002004844464203c000000b9940e852a041c20360020b80f404503215141e9090180840702402481c0046a86007000d020401d25140001c01c81e00a070b0088503c0c0f021074544101e5a030301c4c0c0c5889510340025517020955940500301c0d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 806775926 1250 806774676 806774699
    0x207141306080d0f020c04090209060d020d0503030a05010614030405060a0f110705030c0c0901080d0c05011b0e09061f030f06030503071a100b090409060b04150306141b0f0d06 77
    0x240c4c40e501501590312110f602d0303e018852241219070003024048281c691505200d96845401000ca802284482a4901041d1b04102070742c4135910141c0041404e60501c04014180741100c4501003d88005100340000601e010036996030002130302100064580d481346c0a10040d01c8161844503540c0d10000d4040705011000c8010312224640d041150703460000b4809204a0090034491000250420180d11600c1442035800809840c014030000c9000d01c0203a46009008400e01c20343c0d004940074030062181c3e82480c4030341c290300c0714007151014001c1d5107041d092030140c884050020b00700f541d10100121144d186501c11009941c02504481d142c0391940380511110007036000755074000c0071050024010706050500c12094030301c5560441d062071000e105000150171a480c0031a80c031502c604801e02141c941d445030b035856200040c07002c02158510b0421204680c2d0b5290008502c140601c204840c03002002c81c50800c4207003501416582d060110212000c40c040d0308249000503041c10b400044469070704 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 806777176 1250 806775926 806775947
    0x30a1d10050105100f0f0e04020417010c0c050d21110a090b070203030f0a0e310203045706021506130f0203090105070306060207141306080d 62
    0x540c810400350740c0350030810014519512550001070086036604e24640e02c284d1189950301d400d414030040010105000405a0700550000001124980960480c4807405d01612190740c443d810f10000f403102603280c8586a02003202040d0034400510052501805201c00c080b200d03d107842d02c104030000f02904414035039480007040c080014507059000c107224100070100c1e059030380d00a004501d81031a4082e186019000541c104040c03141038000703034405494407995071840861046031a1600380f0320500c0351034031070315601024041500c180100800507840d80d0314001000308640c1400400c182e0300034101d01c000810640c40080741542c40000440d0b200e04018118022140032013000110b407118000c9030f031307992a102c050415000c9140428030a00344200a200d207120264404550300c00001c5905c01a41d105481c80a090b80d518410010460b81c14420400a02198400342007036616001075060300382e042500091141e541084441595001d0340e106a004162450544003080c20b451000340c031a0030b11 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 806778426 1250 806777176 806777203
    0x411090a08030c1b060c030d090302160e010b0702120a030903050c01140d090c08010c02031b0f03030103112b0209010b0f1804090803040b090c0d02060906030a1d 71
    0xc986000c03a0101e00441a200041d507510003c08000c01c0581030031100c240340d4900c3e60b4000c0420800d00b9840300c014002040b402200810100c0c4102c0e0900c0d00910746080701912400c06464030780c2c288031042c641e120060461340e607000c10310380342d05580c0006401a12101606110361142c0440380c020540c00c51501e60440b0300500940740c4a200340e10040d6022a040c50100703551030400c10003040c8000c102e91045150350302940100003219190740380c00d821141194400c0015900200d584a401c03841d0401c00c06095062802401c401c0c0c1d0100c24255490006000c02024818420050030b880d440d0280040c00d0120030030400743e6403000d03482c04c80394020901d00060740a402030b0f83c0040f03030004a45046030050314510007a20b207041f25905c143d070481500b4680d030940c015180c0780c0400100e140303100690700460143c0000920383c1810714007a4230708910000264002c0b95034110180c0940d40b03402c2035405403041550703003070f41c0c95035248606401021000302003d01d403400d000c0800b81c0c00200182d4036058506 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 806779676 1250 806778426 806778439
    0x209042c01050705090d0507050306010f0801060f0b09100507061505040b0d020a051504030c151701120303090212060703050a061d07030e030d09061b0305040f12020309041109 77
    0x88186550a903070080380c3c80800704008100429490401d450030700080785c05203099841e071030344070f00020303007801020b0b408440b10f01d2104d14240140803080c442c3c07000605885000ca8201c1d4a0402044458001e10403094464481c00817200c140c02e010b00304480960b030b40488100180c02d4000402000c07c9858040c0c240520b1808030b42c152907040000352000002c2c6c004004040352032804042003426801a4204004071100303100c0000014a41c9404030090000200401852015035070000c01c0003100081102941520000400c480b42080740001e0380250940380100e4400014000f0070084880d1035141c0c251441858100030f8410383c95400751340500d0303030080140203072a911a0301c0140d421045403403440f00d20321003000c24446030003640052940c0b5800c4056078280155000b84c1e104a43c102101510350a880e01414426a0700410110300c140c0c07601c3c14104100e013041d0f01e400c1081c1c20342c408014242c00c1601e03200c081ca14020016200000c0d40200103101910100c0c510310603a4000144480c0502c0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 806780926 1250 806779676 806779751
    0x30d0c031505091009050601120f14240609060f0d0c11030901140702010e0a27050f0417040b0d0603050709060303080c03070c0c0e1501020105070c0f0204020904 71
    0x1818203443c502030082d40450413402070404400f2001000301409550600c400301c0b03025072001103c0c0c05508201c81101100103400304a41001214504009184c1d0b201a021032803071941d03950300d6411080b2104170a81e55213440b40c2854000c03e240d4420440c0983d68a5008100c2c0030320704125810200906e84955038035a456030400e0f0140e541c902640c00750301d020a1038141030b80400030501000c6e01c4c8950051400b651250080404604512002e03080700da21f554803c04c1d0120b8801032641840c2c0c50117040303941009640340c1071000c0d1103c0440079000414010428103180c400b0400311080c0c034060100f10a4031940d031804050040000c010611040703855000790000054020410300c20701341120f07016180c2c2901c0f0b03070f00c440500c0e4903580000c0060090001105104011440209400014016000c040b2613030b400d0003c070081544040702d50791411a81054104000d440d844094034103415403140e01c0362498503662000801070700507013800b43e810030306d45800c01c141551501140030200714500070714907000 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 806782176 1250 806780926 806780929
    0x915160e010201060b0a03091518170301051c02210307050f010221100810270312021b010c0e0913020f06030a0b04090303020d11040e0f0702030d0c031505 68
    0x2c40ca00d108a14178100c0a01c0810049402600300340d080c64891180782c04200d65138501c1408942142e505500c945403481202410408100750079a42c0790b0303110170498119031608000031480500d40703903101411690900c4400440d00d40c0300d407044039810412002d441d8041c2c46110313207949401c03c4a00341d50610071120616018130040c82240e0f58240d00c2d82042e491710b040c03503440540481020b8146c1800005001d0005a100c0c2c043c0440b14000402080205030f405502403071115110b020401c1850344101d14901c0e100084e00003c88140034040307600c2c00368450b00440b00f00fa20130326030180385003002d5092021040308564841c0c404250154111a9101c240d111150304000c00400c08000075003280450740900d0741c03407410002441e031240030b8610110b1400070120114090b610410f0049012030b070040b40e054408249402050602a4480042c50400b4500401064400005840c415094654101041c2014801e02c1202c0040c239000e241031001d04115000107009007800c0448007107070748005401180c00d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 806783426 1250 806782176 806782181
    0x60b030d020d1205040809150d0504050d090905060102060712021312031404080a0f0c0306020a0909290607021504031203050106030e0d0e0319050601050906060903150915160e010201 80
    0x1146c001407a1400c0c00031600900880a2003058050b4003807406100076803420480d80212445140304101405500d0114031b405003a102094010349042c600300b40400103580d03800200ea41d804031040c980080100b0480f00c2090003442800da200c140040f2443d0042645201c181c0c8481401c1c0c0309956001d4042c4400030003418a014134011103a154000f070303c0350004204601a03030b40b203a5005070354000015949544100880e0b000c1090080410301c0070204000b485a60b02c282c43c00050010f011881c005004203298103807000c000c074510300c10007001c5003200c2992214220142c0c40707691140f043c5e0b07a8617207a003405900032402d441c4d1600000e0407e0000b20b22a4070a024140c04491240001c3c480947d50701d80c00e8510100c604950380d003500c100303904142c401940441c81c03000c0300d0148020740300c254102005d0180101d001006103000e070600700080c91003038070300107400100341780c1c41e141611030b9840341a221802d00d2030550300c0e2117a000c081c0d01840040e910000c2e200c48061001c4c1c490701c0e160824480168207 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 806784676 1250 806783426 806783431
    0x129030601151206060f1101110715020f1b0d0e09010620030d020423060f0c010f051510090f1514070506061c080d09060b030d020d1205 60
    0x8054000000400c4092011000500e0030b80090510031a000c2101c1d0b581c070104d4a0a07408840065184429030b50f15030b800c10710095102d490320000717000c3e1080e01f4801620078815960014101a58001400c41c00e039800d5054910410b038500080343e80716401040c00d004000d541b0030103c0680928074404c0d003c0c03402049100d0202901411801e036582ca01107098501c103103102c282248100c404112119200c030706100809142103202d80c0142c46138140310350750b2a00d2405034909803c00060100c40591540c0e071105031384101000100b881e90350f00444050340e024102d440d40c0c4241084c00c0009215400313a010002641d1144160745070f401076200b480341210781581c44d220364400100c4103101404600c10f500c00460700740d101c0341012405000407103640c83d80d0fa4032502c0203030b07029040441400300f149416000f503950506140b1401030201c0c0707643c43c0c3c590244500c00c110038000e59103901101c1008140c1d00510040c41009007503c04804000c03402070b440d001d21903804000210b02034183d42d654049031294a0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 806785926 1250 806784676 806784679
    0x112110f2a01390807030e0616020f03090619090914010317090d020108060d0821060901180c0903061a040b040903020601140a05090c0a03110a021b0a170129 69
    0x888103403090f900340e80703c0d007000c0c005900305519110311b001e00306002c200960045101401c80781005844200003410144440e00c4400d42d900100550f4038a03030303100e009940507100044000b2071140f041001c240d07019620b0f03a1006c02d545040400c1da8000744141400c1c3c0c0c0c1268002d14044030081d180c2c90f040300d071134440d400e8660750140c04d5001c19030141d40300e840d60b00e6000c0e001400031412000c0c65110105160821075001c04030f042310710082407820944008064000700c054031040741c00c1d41043e2140070013003003034000d5201c6103a9954540040620600c1004000c0d138000c0010421642c0701d5560360303018150a640e850140e81401c045c4415400c051090702c10300ba415078003800031a400c3c61030810b0103644910041e6484048008086400d64620180a0060b0821030b020344e40d03041d085201500340e03081d69489443c0a0700511900010f00e1b0045806104110350800418a41032140c001820180c07858020300182110440b240c0c92001c0c05512100940b01200d5262041c03021a4081002500d44040200e = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 806787176 1250 806785926 806786021
    0x52710090b220504061d060907090509030a03090c0e0c070209150607201009060201050c0403030512060a2606010e161b02030604060b0112110f2a01 65
    0x2903071011a480703c2d4101d881403c0c013048600140d5884149820601d14800d1a070700268144445490200800401481c0c00a4144014680306c00380c1a144d000340389100042c103032103a60f500108824004400050324051040c02d5807030030300c40c824007070641101400300d000c0c0781000041111120408989200804000e051034a003815994070028460011030103201e031840c01d040c10004550f6143c0718090500c2066590700d03074162030000004d094460240c010342211804000500200e42c0c007034111601c1c101410904091515520041501c210341603009500c2d804280d144d156640c0c2c040012500580080f0084601c5071340c0340c0b03c0c8203006820aa94108007209510f1012040a001b2030510600c03140281e590341c4074500c560003007410480126070840350550750345180f0b003142da00200c6400482450703080400004941c0340015010f8403a08a281c9504000807036482954a4007001c08401710000400c00c200f1107588036881400b0303200790324041c02480b481d00c000c0d070300da0350900c81d845d004038001c091003 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 806788426 1250 806787176 806787229
    0x2007022b080a020f1b0f1c060b1005091f0c050709020a02101104050904080403060e0303040b01060807170c09030304031406010803070b070507020f0607030f03050c1201052710090b 79
    0x1041106e0500210b0709410016944150070b4905c0c040010b035200302e0144101003001c0c094407003085407148002d4041310a1050a000d84600c540703400300c040c2c036880c03d000005084081d107100165040c0100c400014010312407120049071a010940140001203856000c880e801315011034007c05440c0171140e95114144140820855440c06e850140d401501507c40140384c1038480e00c4040a072589185aa0402d501c000140010041e80c024240d0041c030309440d0000c2e1500b8814401821012481600252002c122020072469404c00040b100039940007811642d849540e40b50441c20440060700c7c004860150400004d210440030084a200d80c0e4002d07100085540d03a403205884c0354215020698001030b5940b4a071416448450045c10140d00a484480407640d0030000242964001002e0050544091000351040180e00d801c0905441d030841d0091000321104141758050b030f108241ca509a04807110074440386009194040d415900b11003003d0010120020601410b2201181c8030300c8d2040c1201d49 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 806789676 1250 806788426 806788429
    0x30f030d0f0b030303161d01081305120a0e0a080a0302030403060f1514040605220e030f071416030c0603020a121e2007022b080a020f1b 60
    0x400c01101403803000c0040c00040d24008a861134101b1901c840352451088114601140c01001d4100303040c0b10404100f2081010200003440700340042c0040c00b014aa03421508100724040c002007510008092000e07464411410005180c054181403550148002c808046036454010600c003114681507001189014a1969044020f00d41040058044c40e61061030840d0307030340d4044000c8024081805905400c1600078200000c0b06e0240d40140d101c0c2501d030801701e4010445030b40004041010080018a407000300e04124198414010144480300001400804114140180c1714030710303120008a4280403041c5000c02c017817400070302001c0c0441c10701c1e0740c0400070a442038004000c00d00031450302102e4100c40b0300c0f12100b62207901b42e0b100359040625407080801c5402d48504101803800407007212000ca186100342d5070720710401c00083c0c01054110740d40c4010301c0c504075954810720344490710582d0f0200759003095242900800341084c0107000c1c1100c40801081c002610801c003030300d4030503014501c004a80 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 806790926 1250 806789676 806789681
    0x6131112060f0a090803010b19030e0d0c03020a0c0b071406040b06120a051237030b0105070803190516090e191e0b010c12030203061824030f030d 64
    0x2c00207018240c58544440000705e00d00090b50003403a640c2801a00ca2034503c202c0e40c1804c51030880d0204152514039000c2000c1400603000003040d0007410540d04100d01c034281241441c00c01e08020341a4000c60100040456044008000e694041d2440e03d19605d00f4000e155200c400c01c0e40c001d016046080b002c10107070b10b0024241e61281010303c045a450385072660320309040002c3d814104040c04000700b112003a0601d403444e07000d444440c0072101d042c3c0b1031034180391561826a01c584901055601d20070329205034024411128400d4101c41c02584918107220080181081c000024620f5800d01d400302e0013256540301b00610000003070701e82d01c06150600c080c030044105d004105030042c030809060503040b00c60b5842100400344082040c40260045560307150203961481e4000317810880c8a0070000d0100d805551007050350219498091703525151400003e4030420020a102168030074803040c403110486c0c01825000d00000c00e80700c001185d03901c00405403507211420155095800c1046020035010301035 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 806792176 1250 806790926 806790931
    0x3010b03150a030f063e2a100606050f0703030b06160605010e0610050307051e03130204050c040807030605130606030803010e0c0405010c1e020306131112060f 70
    0x203006040e040d603070781e2207241c4c02403504a42921441d50311122020201c0850f411030703460450100d0100c00d40096500d51940c3c0c40707464005820141c5000c10612030084491108907101c0092a9980c40000106540349450b0120103100040203464400f00040050040003521482600c001e00b01d03081280541301034020b8070344002040d5100c00200400c603852610781c0401000c0d58000d220000d010f6050a650302d40f200c40c0070b86442c4c841d0030003003079a103000c2e5800030440360b000c0704910741586c40f02003e150084943d500d6040e003001543c03000c810408070156600484080ea03000b2101400315403138902800e0400c2c0301d140190300b4136410505e82840401d5850300000d4004d120300455560941250b1560400c45281d90000c0354017010010040122202d0312807240e4128403428122840e2600d0800060280d0307244090041045040e1030502d90909903803014084000c4d0080c0507039510389040300350340104c0160400111017140b166205005281410740101d5a40c0d0301140c020401038450400550090100 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 806793426 1250 806792176 806792179
    0x10b0a0503092b08090c0d0f03020f030703210c080c090a050307150f32220512060103051b060d0603050606010e0f090705030a0e0f030a0201050c03010b0315 69
    0x10b0a0301081c40c0003221202c20000340e81450701c50842441d860004284c40340140005000d6407080111a4142e9105142000c980354008400d12100c14646001d03030a0a42c010540101408089840d40c01d050304524041070803c0c2510108068403c2100000c00300e40e0321818010000e494000003c0007001e4010041503004001041601030303a5a44c1c00092424059800200c908210b09090403104c0d5040320310300d0031840d0b850411041c0d00807004600720106002040300c40318244c5050006400110000c200c82c8440c00aa0740c40014640c100104081c180300b611956000360110030341c4441e00000030829a040c4ca03408805092006200000942054000961070342c0c4a42e080281c4124410349200c1c0100851161000d405545881c0e40098400d02c01c080d40705008041e0740c2101c031110395408001c19030040035030402c2c9899446520503540240080c000783e501610503a441c20341c808030000050aa405640d5000b403300d0707660401000011f000a00c0b40b003040003c1030001c100410b00318031114418a00 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 806794676 1250 806793426 806793433
    0x130b030c030a381c050c01020607091d0601050702030303070804121404050907030204150c0b0c03040807030804050c040618050903090306040303022d1c0b0d0f0c050d0b0703060608010b0a050309 85
    0x35108030016402c0c85000308464551141b00c00311400d50f014419540d0000d9107042003114240303070404c3c540781003803440c845170301c0d00d09400002131480e030248041c3c40c060b540280490b81c0b04c0c41d10712000340092509a0f4260782c1310308605907104c4c440e84107c580d030444202c5440001c0c10b1902d00340034009900c03005444141415024040410340190003801d15404072066624004142d01078140540c0400000e05042500f031030401c1080040f8411208031646240d0515020a29940d81d041a074104090000b0703003544103003440030001e03601c286807a0300800d007080c03050104055202e007802199a8462001030781e8150300100006000719002e58007801700305220200818800150041030600b28458529a0006c40300100784011004104414041d40081801080041c40ba04000103010000d160130002c02d5410b900c1c044100300301c44a51000000c180180a50040c400b2030320b05a00741c04c20490780d180000b40303040800a0950306c03407409103040f548040980b42c0f0b001007030a4211626400102915018071 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 806795926 1250 806794676 806794699
    0xa0b1309020f030d080709061803020913060507030608120306030717010207060216031d010203030604180b0901020306012705150c0a05030c07050604030b010b130b030c030a38 77
    0x200d013802020003802455031000560b03e01440c000d0940301843e000f400030008012000d015828181505409594041b55202e010795189100300511140c80000102900c1c200014440742c41d4154120005031420b0360191626071008141074070490204860b010781c1588010300c01c002085280e4600b80b07810004000140c9017440c1d5803100400d9030720100400143c1051024020241a0711100031a1031408041c24660b2441c0d416000079644e00010703060078844c607501c10f001e0740203120034109254010f900c0700b03521181d4540300113246d000750001c654072400710703030b04850041200030701400c0100d075008012400c102050800307080c4850390b186070345400c400c848104039141c52a8030400c800070480348a0b100860b40c039050049541d09000e125030040d405020144000c0c40003e86c0c991815055400444489480714815242052680215441800d401200209008116110398015442000d8180b01807140170344420300c001c121100c00402081c009162020b0850050907581b003290001c500510400111 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 806797176 1250 806795926 806795929
    0xc09090b0415141f0f090611100b04090c0f17060108030403031b1b03021e0609042d02090406051c120e061612020a0f03030f0f02030a140a0b1309020f 66
    0xa44114134001c003c50000840000c01540c415800c0d009040640b400755404205d80c001542d440e4400100f20a034952600c100102c02e4450740d2221090700d800203602e8480300d07611411240c00507468051602d8602c1c151451060240001484a049034820350046140600d10303203040304d66008903030110640141c11460382011401643ea2905050308229211035140e1843c07041080e03524002c040200c03410687c178000f04090f51454181c0e500490f0544010400d420f644403800d400350002d1402c620000c0c024a00c1e4007040340303503501074140e204007038808000b030726118010801c083e003a2449001060a01b42003100004080304c03281d2400840c0f81c01c240c01c2c15881d03500003603166006600c0c840314101510303d400b018070a480d00030000c1d8030f00301e001034109480941c49070001d403c044840030302807580764074580103a06d1311035000700c05120f15440110340324100038500b8000f4011881c6080c0e4030081390b1001c1400c002c03d0748603104180030010511103990300c1114401028160b141d40681c0d00c40924810103115 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 806798426 1250 806797176 806797219
    0x3040305070c03020d05061f121e060203090f0d080609190608010c030e011d03030f0c040504060f03030e0f06091207030b250503040b0415020d0c09090b041514 70
    0x11184182d01804041c5854000c01d000d608c4030a10419424056000801c052101510084082078010000c00019162556002800070749004014202440042040703c045004201ea003041071340e0f042a110f040380003a204503503200043d5041756014008201045852040704d0306800e1000d854040030032003560f070b62002400c4401017440800032075110000032740710306402c5c4100c5091101c14031041c0e241e01007502840c0d640303010041c900f031107000ca040701184d0036004050585000f07100003081400416261416014248120300c01140444c0c1100e40400c45460850610410b030800600f4040c00c1465030800c0040b10383e00d81c10780d94240e0003030003404000715a81826051040c40010300709900000010840300060903881110800c0040c00c0c0180b20008400c002000e410a0b08911080b00010544851000070700c510070030301007158544030400960f240c00c403918204540031100c04008420f104020301007680c06201c181d109a081e20364050144a040314541400a9000b5000d90090818081580c99 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 806799676 1250 806798426 806798449
    0x101d130312090507300201030902190b0a0809064b39030a0b090a05070e030f0a0803130c0b04081c1b05100f0b090a1103040305070c0302 60
    0x191508240300500030715200250140c0311180801c405c025000005039603082c07112090304000d0405890b008040e0541d40c46001d20045500c1440d80003804698030303104c904a0b540030511040201e6071260015010810200d0000d100314003170300b40700b000c00604140c2e2800b424510b048040a17100ba4840b060702c40c0c5038510348010a0f50340d00802d0b00c101d013013801140131540642000d007099602001200c0800d1001c058126a00b1028090107070b84903220302c0c80e0080540046000c00b504078054808000d40c420542d00030a0150100b070b110700b01080c80803070605d61a99004450b2a0f915031101e54500c000600304801103520250004c1d6100031000c081e9074081d024409136100441401c0c01080903c0701d00828080960410080c500c03411000c0780c05c0da00508000c290000f0701840d55000c0340140c2c107100c018848081200c10710b240420042032a0103504000b42009002c60740521140400211881640e10940e001c00508004440c11079445650444450740301c00000c031200802c034000000180c039003444003003 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 806800926 1250 806799676 806799683
    0x81612060e041703010b0a0e0d0f050109030305010f12081309090309060306051c060903090e1006140307080c030a0b0303181021020901050c060708101d13031209 71
    0x46402c0c00d06002e82c0c40a0b44a260482054007080100016400c203c100e540c1d1440a061140a01e540c100010782508204e140241c036484858402000300078041d444444458840c1e20200510390300c0d14000e583c462182d006084180b4619010900403130040c002400204c080c400030307000717a1a1030310490340507111030040480115641c1d1805103d0f01e80c00d40540c1c0040c02060b51010102030201c110084254400b00004d802e840da40c01410003454442c1041d100900862002040103003024000c6c0d100705140e621860740025284010302d07030300000c1102141d001d081c0917541c13020503032101041e079141c5500141c68959196a100900c2d100c03914240090403840c1190020740488540c86800d100200e02c042450300308101e107100c3c0510a800480300600030a142d4064016113400e2040010b030b0301032180c2191300019204441c1006a081d910440c20792080c1035940c0c0c2d84030300caa41c5208200c40b8140d0403401030314035859200003d21356071400607440300c5580685059213526404240080071500015800d8 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 806802176 1250 806800926 806800949
    0x180406030f02180714070609020315011d0411270403030f0c022b09030f0b040302011d030a03180b090d090f0303170c130b09010318020108161206 64
    0x10705502c0c015114a44401c40c1d03031203880309850000002044080c9008840821035808140070062150707503448444040e50160444541e0045a00344811060b0700f4440d01b6034107142c1001004030081c441c1107081c011035210f440100c2c08040c2204102031a0060011580c080703108410810405c0500036100b4042c40c06600c0005076101d00810500c25120703000d201c1da0640d40405484400c403514000302c02c44c20500e1503c0e01114001c4a00121002541c0c2d80c005007103400707000100c40c207001c02440400e006507c00c0d00208144e05840d400f08880030244107450a060304244604001140260880b41e160354100320b000c245441d1030750310f01030031140540f0000740340c0d07005108800c81c0c1c642100201000d4198415150142c0d032030f50382c004044040b00c50100c50988000c00100728031080307107000e407a09039040c0405000340e1a25017010b00c80540040541600003410f001030720044182c1200800e4800790184d4a00c10642c1e01d04070b4002142028203550020002000d045644151807442a02c0c042c01440307154 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 806803426 1250 806802176 806802203
    0x503030f040e0417042c0609040204050406020c0d050d050105030d050418021e0901080105010504080d14070c06110c04140a20190818070e0703061e03020918070b18040603 75
    0x410032131030007440030000c09074050411f02031103584840140d41d11690460300802c0355500e03860300ca0041d000320510700c1c14603c95070b10544039003504000a8104c0014407241003180c0d03a42c0e03004040e41c80c2c9007030029802048003044184030b032292803840c40c0d044850382100540b5001c001c4ac411349902c0c0034002030012040021407140241e6070f0110b0103600501d02460000c1c02d01d8208112681c0312940d41030000d00740082e502c15100b605042c0d105460030380e50407030b0103002c500b80c0d60f8002401d4000e0800307009426003c4d0007130141030751603e4812944154900005048240c0d210f40e1840b00500740600844030495918842049000340d85008240d0f00c1c0c1c2c26080401301e500402d10150a89401030907500c0b12a415050401d1b60020007d030000480b032510054101a44403001700360014206608044019025000400d02000386401c004040302d1094481440703660711860010b1701102c1c00c2c5400c59041d0410b00b400c1100071410009410700701d5103501a00c0489440d00002000c680b06a030007107034003034912541c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 806804676 1250 806803426 806803469
    0x1a06070305450405060f040c030608060c0a200a0f0f02041d0d1d091801111315020d03050a060f2405120106050a0c06050a05040c0503030f040e041704 66
    0x3032000b00c881060b1820310450500100045200c0c408111141c0540d54403101d00e018580309401c00401006200103413001801d01c0e1160350b00c41d40c003050018011138548a0001c80903110191203585030010300020303086080d1107a441d0a100001b001065a8160a008030070007d0307682d074418503000c0441d42603440c40d001202c1461038140722072204090103010b000168002c5a00d00d11640e003a0801c1d04403031035030056980d040c0034084414021a94400b6629083e070302194805803400a01c20240d0440b46210466030f0741c090114150f5008a02400680088290541050103504480d4000300710743c0c8082501510b60700e919618000031350054241d28224802c106640512281c40d4000d446140b400600d00200e24060403091401846100c1c10020005140200355226140ba03519056002c00c080c007007401d003540144040c2c44141c90603244491450703c001010700c1d00104440c2100440803006003407625254100780d400100500aa48030b401c01102d14451003600c034010300162200c1805080310040b08038 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 806805926 1250 806804676 806804797
    0xd0c0b0121080705011d06060a0e090a06050702121305091005060a0c0203120c0a150614040b040605060a0f11210a0c0506010b0d1a06070305 62
    0x203215044102489000030a5810000c030066141d03a040303200c840da00c01d164030380740d4014452222100c50074840751214442c07861001c91035074084e1034208c4815501070f48440d80c1120245c800c1d0b440092a0b03100840290000c1c086420490f0b125a06006a514000044840070311726400300300490b084030400030341804070f4a0220403054000c8035151000000c1d0f420007010402500c035109130b040134400c079107a0200071036400b000035040740b0070100d6056481780c0e0b041005680d10030607600b0031900300c89080c0070840145003074402e107822500e0307080401c0c55818204042c0801441700c1c2e0f52440e0020f4454102041ca9104d81c0001d20031a5502d580e4028131f0000981c1c01131440c80148d841100c4c64000241e00b545040c0b641ca0503012100b400c56250ba40c0d02d500c00010344980c00d6140c1700070094000c142c000a0440d0a15014103c031100a00c01441085000950414181e003524070440d8400c80030311240021034400c03805080000300f01141024002a10110460b45c8142580c210324461140350381d1100804520703 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 806807176 1250 806805926 806805929
    0x30339160303051510050c01020f07060509060906040b2202030d090503061b0904020a05090409060203160804051506130609020715050633070b18190813080d0c0b01 72
    0x141540c07a00c2030140c000215040c0401d580c5c80f041220108406043c9502981210145021803810070343d584100c1c601580a010200d445444038043c0000081d41e445011804910032507101d01e4034020707a582c41e03400741000b000c0b001042444140c0b410340303280140c5041084a0034515151511280d0a103080101482c042004005100307400c0d0f00f4003400c41059006c000d40342c001104540168a480c6840c01c104c505000d80b240d42d9620600741101d00061104590003180590440501044407000c1c0d01c409440c0310100303540c020855403218044c580e106020006042d04018000e10044030040c0c440c9416041d00d03c140c008012250740026082c0812504030392405803940f4552050000e4902503000560207140724182003400c0184400c140f22040301620076250341d140310185241c55191a0601656005044038081c0130400b00740307240b20f00803400141c000c1c1c40544007041004840500c0c0d50714106500000c180b618443c40301c200100d041f0b10140910803440b200d55888a281c0c0c40341d41881c06004806 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 806808426 1250 806807176 806807191
    0x30f0319050f0a0516020607061b030e030d0e0a0b0109063201032a0503040b0a0519090c03020901060c02090703020c030a050705070519150203033916030305 69
    0xc00503841400386000c242c40c10f402d1581802501c5a203940c1ca80d100607110520000e5021a00107015002c002460388481c00300415421050050f02007000d0035001c0702c4000105100355441071003100e004405580105605030046419680802120303595034200c0b06081e04400c90032038440c0020b1001410010321050b05071610400700900e80d5410703203c0d0720100c51113071641d030415464141285030448006540c018018800c0070150110400c014010003a81090b6400c40b03071203802078003040342c01d40755004142c090200c0c484003c0c110114103a9402c000c2c14156012901160907000000242e900c01070003034003c00d9187c481c074500101e948108588040010001014144140184800c02c500001030300c0b0100183e06005a490003a414100d140500c10b905c4158020107030703107440e02c2d480311000c07144080b03500b40a400034000b21301400c166143d000c1180d60a00030841d040910701c1108405103d42c4090f00450751516045041884000d40743d4801007000460100c0d4100034401c00d5818413910307601004 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 806809676 1250 806808426 806808437
    0x10f180b061605010e0111071b170c090612120a0c0c0605031609030c14010201020403080c03090a0b0301320306150a0602010b0306010b03040c080102040f1a280e030f0319 75
    0x1480f02510002e0302922030301800c00f0b4540d524442c060141c0050b0400034060242c00106003200b800c1c4001d2f070f00c002d1b8402250041c0807443c0820318904118404040303a02c925005000c144400c0c100c824081c0d00458040005c0055070011b540109150345000300c090310301d03680c61a542e894143d44a1140c0c0c60038945010811000303010420110b00c00300301e0300c4151080190741c3c0203007180c4600101d01a000350340014080000000340e1040c4e5460020045c107034440c0039900001002e0b030b030300500354650102344901f40510328120740300340c05c000c9068910303000c40f41c100f98400100040f081c08246001d000710340d095110004900303031040c60700d8007240800041040784000d00110840f80e02080e211001071040f500030b1580800480d0822034115004005401084000c548456803140c40382458041341c402c15100400c000e00c5046415810400c81c4c200c425505200c0d003130701c0c3c1d1020030600c2e21420380d09804204011510038010540d0184400300480c134444c801140c461103251010210204112582404e006 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 806810926 1250 806809676 806809691
    0xc041a240f040807050907230904141e01060c1a06180906060906030708192102070518071e0908160810020415030504050a1a090606010503010f180b061605010e01 71
    0x1002340058807880050802154481910101213030280a549000d1301c2c0e60f184001c00c100b4100c502e00e81c011081c040700e000360300300c0d0b9a84440035151103060000c0a04070050402c005007401c0d04401c4030603003221014204c00d841ca07000070751181f5280801c1c0c0d152a155005502403040d10b1824142142d04610300300c01401c50720b0b00d4080c100743e444c9101a884410201118500018480042030503000c0102c3e0f49545001701c000340d44025250411402200d103c0d49040400003060000301070090310440c420385410190f0f2030116500311103034080c1d86400d4204104101d01003241c58090101003007034008d104101940f9800c0c00d96450030301e10041c03020317000d541c810b100420200c1d000c0c540c12448c056540c1000990342d00d40c0c0c10000e08100b119980130b00401c4919001c50514143d003141c03940f107450031109444154031004011100c0c0c0c4428403400c014682209170900405903030f070903c504141c807204000140e0280360808140c0c90b801002c05805901c00041950081c01402c1c02140a500083d81c003c01460 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 806812176 1250 806810926 806810957
    0x4090212092b140405030102070b09010c031a010e0d1e020a15050a0c060603020619020f0a2f0d08040e0108060c0412030309060e0c041a240f040807050907 68
    0x8003002c04545003044070151000300905202021039000e050064000c3d940d688444c10300078013122040d18410700c69884c100000110354428403034400030f850307022841042d01151800448644520740c054a038400b00c04102c81e4006404810340c140751804010070080344030301600400420290380d62000c0c20201d208002880d0b41d81c0c1c000100d818458076824003416a07405810044010003454000940080c000104514000001400500c07800d100750300b142c1d51551010056515842010001804848190304070b0381001024154031408007440405120810f00c042e00090340b0002c80b4109480030140040c09011044d02c40301424050007404c0b00030000340c1031404c20280144164440c5242c540b0001c69011300b090f00c06e40142c012142c00c0f8030180401e0900070b001e16242c44181070b82d18410780c541100e0b105c2c02172580c4001c5a02c140300a00107003c401c1400521715917100c45160855500c101001949002d000786400b9201811a100040c50410700b05030500904c60000b60400042c015031b0314524410 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 806813426 1250 806812176 806812243
    0xe0a0e060108090a200f040903090b090d050a1b06020d0c08130503061005030d0e0d0b06120a0b07020709050408070f020a05041107052e0b060409021209 67
    0x2140c400e00c0d20102c1580c0320300f111070400020840040c08840300d15814060510244883c0c0c400040440b01005811400c00c204001c480212a0003004030b0420581004401d01b444041c0000d03410141c964040c01c51580d4490703003010810b4008407000ea0084440708a40f542c200083e070040c0041f40000c002ca100ea207900602a0800182c000300700c1100000d02114400d034100c4160010540030301120441d05100207001c000da03000e405030a02904c41c480b54480301520502c0980704040005d000804c0002007501caa501303c110061000390400c45c0d00c05814658070040140402041c00b0300804d1a11f070810100090404a80c0d5012554803401d040c14400496440d82c202c1e41c07002d60000020303004100310302c0840c6152149a00007544145071550440c03103400084010600e1501c0f69080c0c0d0082a05080440f645411407244042000745010b03070700e0240c01c031913400b8551504004104a080030303500c228541c1680d020345042441408040d042c4441c98030b042000d480b2103101d11031410100502c1e8519180c1 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 806814676 1250 806813426 806813431
    0x111332030a0b07260a14100b0304050304030f030c05060601081b0a090b030702010903180e040f050f01150905060a0308030a0b13020d09030212120c0a1205040b01060e0a0e 75
    0x902d12000b190b0124000e0000e035516980d07038021000b041c04003081e04d0f45a00b604440c4078843c1c6051094000c400c4c0500303038603580300d80c102c001018040c600742615007140f03400042084030540700400c0084013140c01c107580305010501c0b85c1d403442d24850240c90100c0c100007000c1c1c90b590601c149a001e000360295600314003400003400080c811b46442d00d041c1c00316200e0515900140d00c2040001c00e10046030703819000000164001d0300d5404011910855020401c8064030414402c02c01c80c1c0040380028090100c0103a0b450300900c01c694121401080050841d20050f08012081060032020009100c0e6805440d9100d02d04a8600e0703481407031a00d58044900c401000422411342d55050384100350f50300d04503d60403103c0300c5003c5407902d500c440b000004103148041540944507400da41058011028101c90b509012410440d1168a5542c0860f20a8101510034000d1141500c05580710990034855984124015a100107955250881c0906a0a0b41d0a0f510b80540360a01c428440a0040f070070098 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 806815926 1250 806814676 806814683
    0x612030f160303180302060709060e0a06050a050408071d0c07020306062103030405010c08180307020f0105070b0906070e010e0105090d0c080307080306040b010306120204111332030a 80
    0x41c0408100c0c64100c0090862482d424080050b90500f03000340760740054402d1191070300d51500340d20144c0310f04041d920300c94640c1d841980719840350020b201c070718442d10103000068283d09059007859143e0618a0401c451600003449031840c08110300050304026202d82c0c0c0103080d040000c1d1402e0a1a00481d8490800606290044203214185200c5480030b600c0c2c0e030164010442540c2c4c46e4200746ca4164040c068843d0320a00043e08180800c42c40030144d8864900c1c41581d40040d40341000a60a10407001c0c1c0a02c8030034144041801000c02207078084144c14800c0040d10060021403805801c09070405500c40e0001d4104100442c41140c1030340c100044808407030f0100c0e0071710142007003031400175000344058010802034003004c9401020850750300c1c09180505022101405060304040044007122440d1284444c003144605010000d4182980303c010040c900003402d074035241c00d9001d8406200d40c2e40d03000c0c450400c0d9040240b00e00c0004540c4e00ca44e90040030440e030410065101c00039a40300c11540014 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 806817176 1250 806815926 806815957
    0xc030402120c030106060314070801060813150c030905010f110f03060a1e0f0503120a05090307150905040b09060904020915090f070f020a0c120f050601030b0612030f 73
    0x114440001004500950b1000600034404140c540d240103010f00512044e80c5100001078000c80d18041c0206c2c43c450681d03030b681c0c3c1c401381240c4d41c942d005010040220400e44081c0182c411070442d14145010303203404900309460214818107146045800c4654101890207801d10789060072001240c40007c4411010030070750038903201d48030000000d00000303c5034850842c8281d40c0ca80d80c080702c486218860100e40120300c02c903030000d0f03980c01496190a5899003080a403882040750103541c9018002410340207001804031080f050700c4100c02480003111303618550200e505454100801d280600030400c010106a6851045083c40b5011554011020f00000d11038100d01c40001c0c0c07481107420b903004001d840101000c2c03550401da45044214042552406c00064007a11010b00d500d000060a200d95036011203543d07502c07490010400c0080c000b115040384c680301c1046e42c00d030104404014803800307180a0000c060b00c5c0c0c1881c208100566280900400b42d0350028404400242e601c0e0081d40c0301c02c6e0700ca80c1c14 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 806818426 1250 806817176 806817199
    0x1e101206060b030a090212010203010501020d030f14010f08100b0d0b04050a0c0f060908030a1d030c090a0b0307051f0f0e03100504111815041104080c040b090c030402 73
    0x140e400340c94141c1060342d00b80e801000b0020443c1003034102d201c0c03440c02903540c2821401039100941c281c1c4401d028050150f40490b0789010202e10a501ca401c03d002500c90005881d0000c000d01405410700381c2c08001c0d8815034800911000c00d051003401407403028014100070305220748001c616921500107014158046102c000307400c1c01000d2090608207644440780d4000300d42c071034071840c80c1480c0ca0300941e4009010b0103008504542d0000403034040700b03240d40752051700c9501d45410f0000054003010450b01406111400100380d20b440f2892401541607100120f400d41c41003050526080140c0d02551081c1d241e10b01c0c0440580100a0100d0407510920317280d460001200d0040d200d10380030217807980d00740c41800c240d040d2404c0c1075800300e0300952141c9401100e0214080030088103801640710204941000c0f40800c480f81d82480c400302100344050700c003044240b03282c0752000894216a2041e07032140c014803e0304045180502c034400c12407100321090310725820200b8083d102404010402030080800440 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 806819676 1250 806818426 806818433
    0x61806070f08040f0303140c07110607020121021e07050c01050301050105031603020702060c0a11150d051f08070f0504050c0a110f0304081006050f012a060c081e1012 73
    0x80010700007c1041200c200d410210b000d82001c1c0d200250640d803107400d101e49440b0514040c1c00710b50344150140d56000240a0400309c48611460188a6500869007008005661610b0f0181001003080c0c0c2c1100c5619900a41007480c01c0c0410140003604000b0200018401a07030040c0503644c001415181c040000000034005030024880e00101139031140c00440d09100762807001a245070701a104801e02c05520740345200388400100b801900d5602c0a10030300c202903c00f0240c4d4091603004480711b0150104040d6901c03101900141500039480300d8000002c248240321140407a02d00500c3c042d1810401d52078200100c0301d0a014100a60701000410041c0303140b004810071000100d0542d0350185e03075680b517965041079500d140504411990500b001e0002035985003041c148d00c19004183c441c480207103071000001d40c1c200840d030240d480c880d02e200458000b08041d4800d980820341607459601c042c0c00e094080000ca2800b04501400c170660080802c000030700760240c100121684508030150100c0e0500c3e = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 806820926 1250 806819676 806819681
    0xc020a15020c010510380d0501140109060210020a0504180b01115106130b0604050f060403120305010314010b0d020910030b1302041b080126061806070f08040f0303 72
    0x46c90300c042ea070300c04503900c0c0b10b036030243e840b0300d040303400312484400c0c60480c0c1001175605800074800c031009a0440404005070031501e40003411074034418a4140d14080d1500181004503860610010600707030344000d00b2201c0d58200c082c00d00c2c0918007600802120100c0a000b250a140c031280c980301c0d01c220040e004d940c01d840c0003070321460381c40b05c403958040802c00c4111110004200b10b40b5207200d1820440c40500d02c1d04c00303104415070f5820107069030b482c19003000d081c000600e1091140e15080780c4104000804182c0c002030b0f440301000035a50114a84d455070801040d9040403034003c5c001649005c000b5a41ca64036070b219898a264150340701080d55441100c00303200d0104c00c2e400500f03014a58010045104002c002c20101a4401c8900b0840c512251030040d030b10039800081710010900540040c000c00c080184410050180a22a0303140c060300030400900b4082c09480181a0300034a04004050040c2404242c1e40684580f034102015202031f0002051507001a2000d0004408690700c04140361094 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 806822176 1250 806820926 806821019
    0x311130f0b090c07081801051b03071205030603060403032d051816060305100306020f1c020906070b0a02120f07080115120c020a15020c010510 63
    0x4050810509444601640c0944080d284140c42010204005089082c5103000d0b10307604ca0700043c1541c1044281d080801e011030f00482c0301410f0020900c04e0741103a20a00c101040107140c40000f464980c003452030204000c07121303140030340240300d0280704112080d2000245184c1c0070383c0500d00880c0410500c5a4111107401c240403444000070041c0115410b01c2660304042c0c0204c240500c00c41d20f03440c500100a44843c007082300d034080582284400c024803442a08119044091003601000c2c9655980d582e000b03e82c01403042c00c50711140800c00e00c1c51080400d0a80c2000c1c100140103500c0d200d002d1000802500c206034005042960840100302e04030101d6040c3c03024550105d0500003281800664100c03041c0c030031590f010001e29168000301d140d6485c4400c142d481c50f1170b51240b07107000e1640d2039554003170300084503804210b10490050601186000728240c4080c00c0d40d840059903a2280420319003580c400800c41c5c04154280d07602007041c00341c406100780382e18040303c03030b80405103001d0b03020214170090b070 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 806823426 1250 806822176 806822209
    0x61e080d2a0c05211c0503131a150103051303081b070b040f02030d0903050d270b0d0e0105060904061815020a0801060c050c010518280806010f0311 65
    0x40c182c031007000150700d9140c80c842c0f0a55130b0071070700b5500d860300400c96104050015000014030900c04101c00c070781805907000110b485070052840a0b030503000d0100b4501c01c1103608540d8003030802404c10503540c06114503600140350a00b080300e000103a480c040c18401c0017402d810b07c0b0401d420141130300ca14000c4162014543d00c091203029506042c107224200c0901eaa2040e032290160000d0480414090b441c042d007200e520101038079940388941d0301034503900c0302071400c0260f884c81e980e204200c4000c0846884041c000038900329803520600b007400411660f1070440081c2e16032510007401103580d5090a802e5005500003404618130841070045602e410052400a004001421071100480c5080c0c001e007501c1c005990703801145030b036500d0045502c2d42d650040a00282c104c0e888802080d445040101802c000302004841079008081c0400d003c0100a403445034001e15901e20f404416140d483c5440060281d48005d00c0340e541000c20300e020100080c4002041c80c0c2c00008052015240e81024140c401c1c034 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 806824676 1250 806823426 806823439
    0xa031707020a151404030b0730140c0f04050d0201051605010605010314041a0a290a0b0a02060a0e1005010306020702090615070206030901061e080d2a0c05 68
    0x15035414940304950280c1c21400802c02411032806200031314800c0d00c2c1165008490044152a0f441040d80d0059001ca40d1051300c114141c0e050000500185102001e40100400000d404400645113803407540003a02c50350200004000480101c800700c4282c82c1903c0741110190383ca40c08910058800d032080a0b009400071450510a00500406501c0308007201c00a0320705024248245021891409013250020802403098190031804c04401d800254059581c460010b422a80079496020300d01100001a24441600d0700003450303410055440740042c6946800c0742d040ca4417000d40a52960001400075004903543c0048155440040000c05505014150204401e5841c0e0400402a5001e06001d9010b0401100426641e0820a0300340d40c1e45141c01d1403aa080007810b43c01c00c0b190354005445840507640b11030001c02d0640f05100f041c541000c540c03040344540307031170560540c1c00c1c8648010150309010070070310030301c144a10707509204050405c0302c40342c5c41c0342034194508031400015a801842c0c0055 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 806825926 1250 806824676 806824679
    0xf0c04110403050115060305060114030a0c030f1518150b0705070b0a05040821040909050a0c151209020105030c0a03150303032301051c05120a120b0303090a031707020a 74
    0x101d45c004800381d882680d0305122940d07428005484003440001a003c0c0d0780410400201c04000e5175014445005803450041140108080340000b80d5082e814408803642c02c0c1a41040440c540840704180490142030a001c400010900303050120030034400d808048100003048810444188401006809940d9903951122604040100150000e008002c118450751100031504084011700006000c80d4040d890702e0180ae14440b800a801500d0f802c0342c4038410320327071414005540d01c440e08014210741e00404902d584140c0c0020126418119409005c620700744a21026136030140c102e035400740ca64031206581e5200f50001300d000b4040c41c03800a03001c4400260110805a2640102c0c9000011200790500c40b1500080858104401e205a82c1d00400c80c0c0c1d00041030b2069a0000c062032405201600c0f806a4030031039202695200d43e0301100010382e02e48100c448428075100307070203400b402a401142081043c00114190040500001d82018124402000400707020070072260242d901030300c00001c15 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 806827176 1250 806825926 806825951
    0xe0d0b131e0b011d0a180b0a0f110c1504030e030d0c1b051c0201051e030109150b030601180f0803071707051e0a141b030f0c041104030501 61
    0x80d01c8241088a0345000d84000140e041d006844001882805103008903d946030846010300800e0100d40910b0400390351206140402c0030524001d1080f203a40c48003203414007604140c0c50843d242c000c10a034020100b4841c06005403000103001c900744401400255981c1c84a05040d02c1e040f020179520342e4507100312681c940d00c0540c0411000c1c0e026210b6007148103d4086c0d01c52240208503280500e0b501324044191000300745040cad125542001d4018100140b425200c43c0081031086101c048080440b4000801080146082c0c41a5420781d44140074040d001800d080a081c0701e4417000d480389040007010f0311800000c002100391103000f08010100e041159541d9440d60b0388942040740182c0c1d01c58004619015038030a008211091160703c000500307074030079005044400c3c183c21a951200c41d8410341b0144000204510000e0302c0b8110420010502c031004a8018110105018102e9020f601b01080011512000084d04d034042c1c40222030124044c2c11000828225014aa0000c3d1103903003404540c0718003 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 806828426 1250 806827176 806827223
    0x60b0616080703030c020303090c06030a020c0d091809030e060711130b030c12061807050301050711010b010f050d200f071221020306040e07150207060e0d0b13 70
    0x543c440c0e00d0070b2141c01510102641c4a000880700e0416941008030010b005240042c000c40c2e11504c4000018240012540c4240c81e00b07611442002c089030000b1418030000040c100860000c10966000b4400c0c203c1559001380401c081c003a00500458022801100b00300070030081c0b01c8040b201030405010301c416461050090322074100400d0181c007030340e0307581d58281c10710644a00301903600c88020301c1c1c1c1e40ca50100b8580880c20340900100340d0b009441b00881d0765030342802602e0080c84280c0e1001d103400e441c0010a800c4480852a030342c1803040e46506024010340080a544400a502400044224609807a400442d0000311100700310007001a082812789000e00c0070f058a20b02030800b07180c41050711002941c0701300d80141a840c03494160010240248000d0b00215070100e405800802d01c44125500d01e8503100154200c5941010f071180c085d040c0a6041007408010700c07680c0b800c1d03a64044070002103030035000041e202819295504000406030001342c001c2402059000e081c07580003583c0c400340d0805 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 806829676 1250 806828426 806828437
    0x20706050f06130e070b0a020f010c08040b0a0b010903030f0302070501090f0b0f0903030f04110d1202010e03090109031104021309050603060a0e0d0815031b090a0606020307060b061608 81
    0x42075038405503482c0c21005900ca505800381515004007060390511181b140c17039410011210301140b050f540f594400d081e00b03004040303c4086503101c3c840729092500e0148110380000f081c0303140c0c19280c8102040aa0703440080c04c0301b209d8050400e8050038413644c3c0c0071000b901c62440041c01305d41c00c00846008011596295010307244c020300c0000080d0b2a40e91400d119a941940c589070198824404030380c00010301c0581d0740c0c101d84100f290b40854081b00010800d0000949012f07160450400c0b90400080c3d028003901010403840005503262045041c00030b804150b0a010280640001a4400c80c450319181e0403109610280320000011a998940050150204803070481c02030088001050000050303000e600119610000035240c0b004c0c051608640c07054004210103821029400358441584040c4044c4017044200340342c00f440d1058100070700c52810405002040e900b8276111081001c070b6408001e66000742c4e801035011800f1404100010a940282c40070714126103d2f0610900810070004010302 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 806830926 1250 806829676 806829679
    0x304120210090f03170702040c030b0901050108060112021809010323060c120405120d2405031203071206090606020c04150501110f0f070317030c120406020706050f06 73
    0x1d08441e007500c0c00b250050303003030700c6900b640700c05501c2d0602c005403040c04d0007461207032400101c0b418400b60390006401e9804042c8041c001c41e0f42c82c1c2e44940385080c01070101d405050203081c00a080e00341640000c2441460100000c4070640c0422140041c501c421000c000f0700000400845440d61641020710071407545004071403a000d00b0000320b03a40f0b2000800c446100e00c154040543c1440c000071607820f0302c860002d1084543d80a00c401d8005040900c40c090700141d0300c0d200000681402c403008000d4140384100a12042002c4040100305607038000861071000480c45c24143d07102d031940300b025200984540e03422141c485c2440e202256080d0b1543c8038600b164026400c840001a2640034807048940503203500400700040c400511155000d14031415a42d001102280c84800861004906000c908040d01030183c0143c8020028004501d90201380c4c2c125039042180b03141020080600640305420f640358400400c40c0028091281950540307801a42013001482a46000d484207461101d040350085d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 806832176 1250 806830926 806830939
    0x141f0e0a09060f14060c0111040807060e1e01021906020703090506070f030e450f040b10030f03020d18080c041a0d05060411010e03150a0e03041202 65
    0x41c008002c0c000c1800310745840035210143e9007007030b84200d090310071003200c6a04142e08110184201400f482540c203001c0c1a00c0d945500d07141080fa026041141d960f1003d000c100003100450358654900306642e100420b01c1114800161702100140d060032241c800c00e400304100c01c4620700c1070254a40081020b1446a628408003d880e8400c10035140128100a4082c440c60040c100000b4021204a1000c40000b80b0700000c034820828103001da1054001d40c4540968130102d104048401c2c50800112030090840d8404645040328021030122002400680184103a2004c910320300030710300c0807401035500714180d0441c080d0b141c00d0280d07580004101100026461483d002a00340480c0d003040191440c4001600f2001e21100402019158000000700804400c04294904c2e5035000c01c03411020b031103240074141524203410070518440b42810840d05000d40039000a41582e400302d510310f84200c402e40062420b40704c005680000700b0030034803885070b0341c4400034020800300388480403d43c609100f11540d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 806833426 1250 806832176 806832179
    0x405030703090e0103081617130e0907030209041101050403061103090705060a0903060b040204080d1e0c080406111507020f210418020c03040f0e06030a05030301141f0e0a 75
    0x10301c3d419500c2480081c2c802d00c402d0095900d1103a2691a10462174011410b007009403484484285141d8041c81c2c03040c2040e403c1413402c01c41c0040030780f41caa50195512002d499840c1c9581c0114071000e500078002041210032302d040d903006a01490580c0c0186402c144d081044100d911425001a41f00381e13085900da1103000c000203480c1c80c00d0000c80741d003003565070741d4121407900c0e40d036415015001300081541e00c5502880b02080c141001c11284a551406039500b50003040110001440e42000b0602c2c2000c22408561680c08101c402d0115001c603901482c107481120750001c031007400e05c0380b00c10310340b02c003000e40c40c0601040d981c0c0001e0200001100100707907002c48520092010140940c0e580154a03040148070070400801501626000c14003001c4c005881e203c0050780050840e80b00303400c030001c0300d0707031010050103124505800264000c00603001040501c1c1e43d6110550340f1b000511548030502c161403d0000d50b912450b01410303072000140c1c6c411801082806001e402d800700094440e025040f00341d0b0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 806834532 1106 806833426 806833439
    0x1030b031e032d0a050307170907230a0501180306020d141e0103080a0309020307080109060e03070b010b0f0c1e010606140d020d060806040503070309 66
    0x3540d581c0d00e0038407905110308141c207401e196891040f0381c8410940e42a80c02c880c10b60320a0705015841c0d50b9a0141102c3c414150b034040050541400d0901000c0000011500d00b512048640b24030311142c03450858808081601e92a0341c0600c5840041142c0d5020791440d03d5040e5a010b5900c1460f0740b25140c54080ea4090400c20f14090345e03410203401c40c0322138440c03503c0c1c0001c0b03560381014400300b00d81010300c2c6030903040c080641045000100c0e4200d0502a03800f2071140c5502405490304030390b8941c0c03d03e00801c00d400003698600e0030108844002c400210840f4101684104003824030790801c0a540b8003a0004030802188030020000502410b1040054084800d0080ba04d95201440b01c200c840c25120700e54410004c1c8600100316404000000003959001c0050441c016103da407800c9241015180c294437401d041c3c0100d07002d200c02d000004c0300824105000351510241e0540d64007 = true := by decide +kernel

theorem cover : BRFrame.Cov 806654676 806834532 := by
  have h0 := BRFrame.cov_init 806654676
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806654676 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 806654676 ≤ n) (h2 : n < 806834532) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
