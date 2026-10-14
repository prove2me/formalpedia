-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3517
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:53:34.136029+00:00
-- url     : https://prove2.me/submissions/c76fc53a-0dde-41aa-9595-be4e3e83571a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 632374100 ≤ n < 632553956 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 632375350 1250 632374100 632374117
    0x130b0a08011b05072001031b050c010513050307080901030204030609030201020901030605060903190f2901121a04020301060306150e09060f011a190f021006050f040c020102040308 79
    0x295641150000741c1c40b000c12100818200342459841c000d56501d0301c5540420f64074048404030300030343c030b1428241d1081d0700c0007a40740806600c0d1a03002e806004000c04950140400070003070344c01d05000c10705403800e0581e0340006591060080d490b25226a903120840e4000e0b01c00e0a040c16403d100001c00306080d0301401d800940b01e6400103a0310f41c0303c90000b50440d01d003a00b00b58091f0105000c0d6220076100000c405201283c0501d150f801c2c8411450b0034164524180b000030510132902403048100c034103844003032081c881c9800c94000143e8032400f0b820400746842c2406402c808011851903200d8000310031140d04140003030004a029a180e071103a400341c85072900e50061002c901c40080110352600401070390000010000781c0050f00b131a00e4046031004040c0940c0f00030301c030018440d90010503c42c007110601c81d0312159140c1c5020441d4805040f0126030600d49025001301c02c110400400c541c49072030103440c2c1c0208a902d40c40c003100240b00060600c1c4000f20150741d0300300400700103e8490b501401080c3c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 632376600 1250 632375350 632375353
    0x30c0c01110a02090a021c110d0906021b0304030212190f081308030a11011a3703030f0c03080711100e0303040c173304050604061b0c02130b0a08 64
    0x47d0b00440b4034040300604006a40030481c98a034100c101a0340910440c0c0c1d0381281101e0200c2d80c0f41071810208001d00c0380740c1e03124041c0c0c2404031251045460100190084a00803141152055601040c0e161903542003041040c41000a841c0c4600158203182410030440c081c0011605055801c500150750303242c66044061103500c0072600310743c070710303404080104030390101d80003803004030400942a07d40d9852040d03010f10409240c5c2620850801590110384040340b58032418400381070140749203000c103000307001c02d40c006103600b1240c020440c000c05840384101d505a0b1061240c0c3d0300c4244c1103c000001c0107a0300c141d8000c1100c5240e800c2400d00400b03c0c0389850700082c5941c2d0900d4030b82076030030f4411603100325400306514014080c01000443c0040d490035820000100380380e524040b05041d103001c4001a801207058609000511500040c0e05111340e00c282000c0124031100110108030343d4082c450301c800510503200380c0e001401c102412190b036031010340c0c3c0822100241e8000600da030006400c2410b40c3d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 632377850 1250 632376600 632376607
    0xa0f090c091508100b07050307060f180f021318020108060f0604060e090a05090303010905310b06060f0a0302090612040f061b0507110310050109021308030c0c01110a02090a02 77
    0x2c0f10010581100405c0da50a0141c0303086620703600c280d207a00071541c1c00381c03050756514140c5038188050380142c0130f4401d11a0000c030341011640380c000d450b590302c110243d01841c01e46000240d191058800d00c400340c90b249003a0b4250310f02c55030044030950700040c90160001c1c1e0310301420450303032030707050182c0058500c6880300340d071180e0740c1c00030300c0801c2c94010004050641042c3c180020700002100300c9066a12050020031a9900c0c00b42c3e44500301c1d0300d044030b4049515071321a10300d00e00d551070b140400380b10b12580b01141c490321003204002080c02070103981c0100000400a00351501e0285d4001c14100714050402424824016180444010111415a012003844400400300300c0c0c2d520072400407041c1e040c2d0b0303a1001115290f00030075a003d0300304000d18121520b41106a9950104915040d05003250740a100940e11507200030040d4012aa03212540e400b1444042840d01002c01603608503013a400c010a6409000001150010a509074034481c40c080e075840381c0c02685540305418440e0b15190405641d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 632379100 1250 632377850 632377861
    0x70210050c0c1b010c0b090f030d0203090f0c09010522090503090907320c07151101050c0322050703050d080f0f06010810051e0405060a0f090c091508 66
    0xf0250202081a0100080d24582ca41e903a0000f4101e0422a0803940240741695140745181c42c003019104041d58a21021034080b0251001d41c0003548070340b4a003c00d44425040c40b0300000d83d00d000c021122940200034a00511450500c100091003041c200e1034030f5228044030004103000c450303002e98155001d410014200e09542072044401c0d0b000703803d501e00251500803005541c0880780000c0c4c0c01082c03030341c041c8c101c0c0054800000260340402e40c43c0300940320415640c00d15034000881c06d606203000700f92110b00e8400d10070418403910348140c5283d0852841e50362004142e00990842400000000c20030440c1103000c24001c110b107502441c4540001c0c01090109131000c0c00c0002c0050950401c3d40b040301c10840100b90045070150080e0707003800e010100b620360320811210500360b40c10168001d509468401072000910b15101c00c551030541c0c04000d66110721082c4034480004d400307000d07000507001100f0030030400e1550001d003120000d0701d007a10b0b030581c03103000300503043c090b001c4a040000d1444e4280725 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 632380350 1250 632379100 632379103
    0xb040e030304030f050403050d03051b030f071101150b0304020105041a07020f1f0305070203160c030b07020d020303011806031205120901020a1d120715110706090905070210050c0c 79
    0x1c44e40180d081c458205407460352040da03500e540030154400c041d2590007265181c9103100d40c0c400c005c0da40c650101d40742e1611400c00c83d00d06000b15914400102e00ca0700700f005408040c03240e40c03a94082c08008240ca00e0422003010083e5001610481c100802004000340d03040c001c11103000e8003404200207960341d0405004110640b60a8420544150341c02c601800101c183d031442d00c0161a610f06021a4590300c0d2a001c1e81140920521602c1c44402c1c00182420425210320090a5a21a407444034881c2c44450080760b464820310800350241e4410801400b0400c42c84642001d40c00001c0350101e40c1940f01c0e0b83c1c01042e00030107041240030171008146641c414142d9803a545d0b004400000840c00e0100070b0100038000700034408144e14800d030410010442d9210070b24180d0424800302c08a442c0e80d0365070303046416103241e0400103c0002c0c5429500c0c5170300704070208614007191040d903206030440e420001e69900a2030064110300551203201903005000c41030307001d8140309400c4980051745401348071703c240303 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 632381600 1250 632380350 632380367
    0x1501140c011e0f0c0801032405010603020c0f060708130f150b01030b0f0f0d081303030e030706261521071e090504020315100f060f0f120b040e03030403 67
    0x240f045a040a600341d4015a00c202c010341100e410105501c8580a101042c80101b104010440f00c0c1604000010444642540090200f0303007a800407240c1a400c1003940a80794401031b00c140d00019001000704084075014a1500d418034002c00030710440000e40d0703540c0ba4800642581016032a078994440b802e1541c0c041c410034004480949005143c0380032040080c40660303120100314031502c5000341d04020700010f070702036450200201c0c0d0382205258a0f800c02030004011410414030920031101c000c502c6a104004041c0312104403401078100408803040112101070041000482480050902181b80d0356044801c54462811002c00e101c01489900303642414569048034040360440c02c410781458451680900846440850004250700c1e6880064144400b845c0c2d1102c0c08e45500051040000d82d181c001d03001c42c0d400580003443e8540d01c07901aa5500b5040e900a40030403008016002503c1c0110800d10300e40c44901000a2a1034200000804440422020b4180b0f940040200710416070881d542 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 632382850 1250 632381600 632381621
    0x1701030b06013f06050d0f260301030204050406090506180d14040b07031e050d1b2f030403030c05120c0706110c040501030f17031501140c011e 63
    0x111038421007288032020b003500a402a40c0d105203946540c03c44064080d50140c809000c4c01400c4004800c1c16007080c0c250031030645010381e0715180d082c48164803800001009000c012050020360704503807843d02000020040108241c0300c590701c400c0d007600040d03814441544100ca040589440c000200160540b030070700c200c00c11805004a5845003844c0808946c03c0c0e030f04440440f2080b640d01c5d15a81b070125200c0440c100340019103500c3c0c880038011b81d5044000b505201e80c14142c200842c2c04684940d006015001242e032012824070303108a4101d1610542211440d5840e00410403107680789004a0710710390041c1e000398002020305000408002080c007900c00a05d12141d1002e08150140052035120032680c440e0206124669040052480040c0161075810707100410030041d540e540e0805107150585a48111220a030110b0041d9a80300303403400741e034041ca404c480e103503c04d010714800546161305100340c40c40f0031210a018138840180240102c4c0c00000d00448440028101d070348260041d80d010202 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 632384100 1250 632382850 632382887
    0x34030602071101020c0f12070e160201141314010b1201021b010c200c030313090c030501140418050105070f18030b0a0203190905030307021e0d050a1701030b0601 71
    0x8030031060386e420000e0394050404658008417030003030344000c41c68846603a1002004640c40740c01c202060100309035000f143c0c20641c00a02c201001c46141082100003107485c4800b21b10203109120100c0e05010407c402141d440d40009400384103207001401e100c2e03160410a1a90703400040d080d0303000507003615598021000c04001d0068000508014012580a501c00701358210045e00b02c40d007140080220300e031240c40103810b89540e101510034510002001d4080c0071a00c9040000da003000030303c2441a94105c0b0186004aa0701011040c100700c003030044060b005003e04543c002400224400b031081500500f0140c8442e074083c1c000741d001611980420b80101c0751400703c0c5170708101050303c90000f45d0b444440054016542d035a6600b518011865000700404000d14103007603d01041000801580510415021946881c80e150a45d0100c64000f0302200c9460700541c10820480d40200d024081c1038015007400d0181034180c4e00300c21a0f2407400da10688483c070703558040c8100c0b541c1215255084480d80070 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 632385350 1250 632384100 632384113
    0x270203011206020708070c0e061f0909020d0e01050a02070c050604181517060708100b0d020c150a0605041a010215040219260a03023403060207110102 66
    0x40355402001c20030700c005460703160000303081010406161308032a06281d00c10000040981c071048950741548040360402d0084148086402010303441c608020208451b50f41c481c080c01e800c0c260550040c6d0000c0741d101d41501d84414640c55030708004e0080f180714038281800140c40e00264289001c070801503500440c003e1204100901c401c40f400301c814140701c2024000410050200c420000c7d117002c556203e010381e07501d0000800c05000340880d4070f602510042d9603000d8203440321314104100e01024400d0319040a420030110440d01742580240404045640a54800d1001d1804103c101001110840c1d00c09a85120a21483c80c19115501c64200c41c0a500c4104d000b000c1e0010b07540784a248003481c0f8242c82800041d04540c0d50700d20f40c44500300c205550141c03550395080c1e8441c02c072800b507100941552a01b0221645001d0020341c07030f184581c041d03005141e16019000910500c082c1c201c1303040750b540e5103a0b030302c0080440301c0300c550030080d80f268600690302c100740c2c10b01e12400844021020304540005 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 632386600 1250 632385350 632385359
    0x306181e100c03020f0f0903070902181008060f0d06020c07171b0d14010b060a03060e090c09040b070908120901170f0105060a05090913050d03020f0409050a1527020301 74
    0x1aa91b03d1180144550b0360f030740802c00003d01d010415445580e0041c00011301e45a413000718909403540440580781d500d4040c03811034040d120107030304440c9150042e20b81d414041852030003218160b00940a02c82c014549206041c005040495942052000580b42540303002940004c211840c002e05a82d00c18a07440c08480b000100c0e10103501c0030191901408030f2104010010a5021300c0280e003008003444d03541c501c0100060050800c5114440281d003000000481882d0702117140812a100180980119956991080d50720b41000e8034203002c0080c42c16010440d004200009501074030300c100360340d8640700d0340400140060100b20000d6048106070051004541c956020039066038402c407981d580b9003003e00800c69203802002c0b41c45501403040e0b0240101c4220708900c036440d40f03006030b040d504442c40c110380540a0b44107081400902240030001042100903560110350040710504c03012031442c3d03c400c0340d420010100d40141c48104c101028620607914221007103001c0d48081d0700c0c19821580741 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 632387850 1250 632386600 632386627
    0x6080c0714010b0a141311120702071809120f12050606090910050418030c030f1e0f0e03070f05040207020111060403050309010f0b0306181e100c0302 66
    0x40c500d000344440c03440040550044429000b9008243e07004d00308140c415030f501c3d0003c0c54180c1c454500c40c043c0d014500500003143c8035015440c224814641040e1400c004185d41c4000040e00524034001c40c02468408a440d038006038422140c8a10650041000c2819043c001840c0c83d140100c1d0080c00312204400c1c40c1c40d03400000500441001c1c403400900d541e504808205c081c401ea24546600402c00d0080051545038504003106550054408100e191200050004007a152210160200d0300b84405080081d201d111124800485480c00c812001c5a460410000c2c511010510010680e220b8007601440d0b0f00a04a05204008030024004145858103c16144586e4003178240559000211300d000c0d039018201030105404503600321134462800d030070010910341068604000c035501785101405022514080d0301c865071001006491151101c9040c0001000324054044c1d0300d02404203040301080411b0221124900d1000142059180d840038507000c0303960850100050510500c0700381c0c1034206 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 632389100 1250 632387850 632387857
    0x501030b010e1e041e06080303040807120e0402030408071208060d0303020904020c0708073308251d120d2d051809090d2d0e0a06080c 59
    0x1034888088041c0d00420303080f010110300031030a4010381050349041401030000c1d104030f40c3c0f52000000304415a101c0d14500e8484c44191006402d01c0340621410012441c244072001c00c10290313080c009040071407140440c0aa81040304c05032003e4a000c100f5509010044203030741460300341481c0800352854100c0010f9000c01e050640a010580c0c04600012140c90b698101c900112840d411100129034840300705035944064040d443c600c410300c0d1910751010320400642c103281c44180349520040c010a13001122074180c000c0c10130182c49061004481050300844010840d00a103503111000c0001c0c400845038900040c481c00c1d800b400030680c100d40b40d40720200d4800040029880c01c5200902d864254900014610400c14048441100c2c40621590014000d0854000410b0328106144c090002c00980c1d00c000c5800f08140c0e04401d02c070070040392164007042d500c0d03070015440c120700c011030000c0d09100b03000000100e80410410a036044091900f00d07a080000d014501d041c1b05c0c1482d100c06030080500 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 632390350 1250 632389100 632389127
    0x2120705090a0e0703020a0803040612090215030c130b19080f041b030606060203250201021221010b0c01050c030709060c0c0e0723070201050405060d060e0406090c0501030b01 77
    0x580c1c90700f48810b03104040c01240d0003103170010040d845c1245c031074494584070751141c840e40b80860445071000311040d41501031a205550000c2031426504921416144141e00c001d25940d09483c00b040703181d0581841c181c4503000b0340f075204801034840042c000d6034507600700a083c014080c00085820030014151442d6060307846035001c4035a61100c001d141c981c02c03070600560002007595050030400b03d00c0c00e07400030140400b01881500e82e00c41c20030903d810301c5444821507001e401070f04081901c0700400440c000800310b4140406800d1082070001c00000245d0303100307030072000f540900044e688001202c2401001e030001c00741c0308030903d181091040504010701394800c5006004440c900102440b6062b201d400c0103040d15007602c201880d000e800184109400f035060101102e920144460290000e0142c0c0c1007a035040e1902c40c0381a040504100c881e1300142c05403101031380c41d448080354a4100d0400d41c1c0c050f51088801242c6100b0b01e1810303407035103481d82d0011030401d890400092426a84008001b40c0b0350b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 632391600 1250 632390350 632390371
    0xf1203011503090b070305060a060807020d0e010509060d0609110c34090e070608070912020d0501060b0403030e10050702010809010b031905070f060c080a110601120212070509 77
    0x1495415415000f07016202c001404003030b01c040400c82d400e901504114403912085400c07420a0351250810b6800c02c0d0107a40d203400582c0034a48403081c2500900e48040700c010141031441c10140300b4130002d00540c1c0702d11180341c151521660208141c40ca10f010f01e0540024815081e800e0160100c03000395560042c00c000b5540c12140441a5103c1220248081440c031088148031111501d691040020303001445185510f4401e0038000200d041c420150710303000343c60300d0750703869520340c1784c4803024001650966050f640004181e0701200040c009200704402030030943ca400b82c43d1481c40c100646005070603000703140501c80019811409507404800c640140303a0900380102030392a20045140101403680c054ce4040c81201e0070034100c115840100b408a81c0700701e0444d0f40d2540c5601418102848901c0b40700e02080513040b82c50009610207000d0030b641400b07460288101c550640495240034400e13405402c288805a13880c00540c20140c081e419003551010041101d0341c80c200208200c104002c102c075a09 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 632392850 1250 632391600 632391629
    0x903030103020d1b05090a0b010e010201050709120804050d1110020102090f0108040609202e0f17010b040303031a090402090a020405180709060206011202091b03090c030f120301 78
    0x38401c8007085000e00000b501411140c0303007c990b0300d00100014411070f408982d501207010044e43c414090648580710aa0300c14201074900030742c40c24183c241800807903041100344400301d0603441d4810f5151403a4041e481d01650750307040030140700c40040c0d000c80c0c105c00c69004001c1e8662070348038600d1000444000703180202180e80e031418050010040382000400c6403c451b550329640810040409006403803c8411000c0c880b0741c00311002211480f8040341081c42c40351209481018041c1c500038103200c21504001c80b40030b0781032000040d018000d030084140500c0200b0180285075040c0300f29840e45615120301e09441c0c00000001d101c240c0000c2000b4828800000052018400d41c1c054400030407024050140c2681905410307009824111007040004000d0318000850340c3c800254181281d41500d541c6103030404540074030220602c010729035429011074245a1440500400040d841191100060b18814444604040c100100004908556404004040340c506030f1f040072603044940c0200540030 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 632394100 1250 632392850 632392883
    0x92d0a050606120412111014101a161a090c0a0b2a07090203010509060319060504020105070f080c06100b0f0c0106030b1810110906090103091403070b0903030103020d 73
    0x4401c44120721090840c015108070804121f9035030001c1070218900603ea808a40d80c6030445903c0c01c0fa903104801c011110441400c84141400f0300411008610b010404005401e40c0c03680c0101c80d222603c104c104012940030086688002d01000164910480d1110743c0e1038504418903001c0d000f111120300c00c8148090b4000b000680742e02201141c00d1501069039035282d910b2518200941091144074001d40e22480051187d240103d400b030200303004840103402e86c11060720303003030002d110092040741400020040240860100051946c2141c8242d40c200d035143c00740710707400d0f0030010090b02c003540404c1c021505001505901c41560070080590703a505864180d00c2c2c1415015205a500140481070f042043c45460751b50031528018003215030046400f0002514440c50407143d1740d501104d0140d0382032042070858030344140201544081407601041d45e80203500d9a142c11010003100d00f415605c0001c05800f000400284940e00055240145055614680111b07410b00c1e00341000034030080ca0261b9501c03 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 632395350 1250 632394100 632394107
    0x50606190323010c02070503010506030f19080405060d09030e09040507050d05160e06011707090b2b02190e030607032a09050a0503030a0905092d0a050606120412 71
    0x140c01c1e01401009101c13249680401030340320f00450182c240a9420000090348038200014a14107010aaa00511107054032407250580c02080b0301c8225090201040700241c03603a5104042c29480c0703000d000000d07014605140180501182c000818000d1070044200b0002c03d4000c140f1800700c0d6000e4038100162546450b00324203082980b80c3c400c8503a5040740d00071a50121120660703204900070b0b03d41d4414000c0c0388469141c036010445414000661070310341401500c3e0048050480c003000c0030080800d4a0400500320b0b00380741d10032024440c003580403171400c1454a40f00e00c00100b19030141044c4050f80c1c5842e0100e9180c0368000c1c0071038149915000c00e0360540c002c075501420309078000e08102c0068001464014050b120350f100e018803607005440c0204451a0100840b4040c1045441740c4005616102c2032042070b071001031000380d2010b0342c9110740542d103070002c81802c0b00c242c50080841240ca05554140c1c01c403840504403500912041c4035040d0040826490641c0013500035101100000c01c110048 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 632396600 1250 632395350 632395403
    0x8160203060109090210080907090f0b0301020a121a0f0405090705100c0c0e0f0402040e01060b040b03010302190312180f060c0302060106031503110a0911070506061903 74
    0x940500c52070000148446032030788416041482103070364007174200000c402111044001d5443c4800385d0170205080200340c0140e40003010942e19101c1c045006024400000d0881e0020f03020800032402d03165041b4081d000b288a25401c4040a1509021000070240810414030340b50703500501130740e910300225180010410004004140c001c04880361504091402130014030000030480d400c6055001c046a040c0d4400c9046214030141101512941d50b103408200280c21400200046950307155000b081100340c2c007004101820780031020981d40d5155106000707101100e00a22252548460b205000040400c4280c02855906250104900e80442c01d040d0204103d54001c0c001174810303503000105e103900001184030341d070300907005e4444581c0d070703030030b080e01916446041d211651600c0d00c0184006417404415102002002d01010311290703c90403c4c004603403441a019011102c00f04140c0c040103010007883d98400b40548080000b4000314050707040d07412541c00b0003480340e16407410710806074960640d47c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 632397850 1250 632396600 632396603
    0x180203041506061110021206010507021801121a040c0e0432190309090f02040909140d0e06030f04030c170309010c0c020d0b06060d11090a120f0816 65
    0x1040481d55840c1d000e050450070700b131480310900072010b024a02c88502c1c03080d18180400801040081d0751140300444240d80b00040480c0d00c03089416408178005045002c45028250b030358009443d40c000303403d144400708000f1402d1440e201103103003084001296120341c0022140300c507482407a1619030345440e000715010903003a00c40b24601d007000d0030f0f00d0703403000211601a40034040981d208140185a5503115401030034010700818441e40742004107800d1a0720246048050100040c249606c64003240c0594a40e80810303100241000c0f1401c8403000c007070040c0c5400d202c4c903050020111103060081078840c04024000d01b1012a50000141450b004170407061140da8401e0000c4041c0c03c0e501c440101c20741064030ba0282c07541ca040c0a40c02494010040c40707280c80e40060007a06150000e9907110103900004003030075008442071110a151240a01078142d0f80d014002105445e1b4003004140010090390f50f01c103003920415101c00340301081c4413990b803904d6180c0042e00c031076441003200c2c2c0e1041d02d642014070 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 632399100 1250 632397850 632397893
    0x60705160905131205030709091a040e071809030e030613061d15040203121603020c0901030218070207180203151912050c060d0203060102070503030418020304 70
    0x481030140440c21494016291010010006525010500c01400303110000c0100722056034101c134842c01c0e000d40040c60b40700c0c1c000d16068400c65103d605040640d1041040c540c0091001c89a101d460b00d441e01a607078428442c41e00420910740741910103011070718080c80d00150565105030300c0040c10322401c9558080700c0040c0c120f510300c0c10b00d031100110f010300c007500a949081c0341005d4107a182c50580000d81f01d01c03d020700208100c44850032442c0b81e1200c09041240e051090000d520f601450b610041e207044400d9010620320094039050207410724000b004058450300c100e17001400180d03501c026105618460a10b80030083d90390500503480d1102642004240c4414012203246c0d40000d03400a40c81006400029a01841c0b0b91040c0628103a9440b4141c404180c03a100c24440c04403009001c04038030780100c0440d83e81182000105e84203030300100b1500005034000040010550301005120000c20058005507c1c15160100c00014400001030104070141c000000c84c0501071020070100c0403104645 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 632400350 1250 632399100 632399113
    0x2011719020a08181c1206150f020c030c06120711010e01090606080105010303170c0f0a050702211b0102250e01120807080d09150c0e040504080d0b060705 68
    0xc80c0a4010794040b90b4850340c18000b046440700c1d062010840c1780d41500d01a0012420f00d05064040d076009041300700742816941c4e0342c00b0000d411019800065082920750310381c42d480c5d80046000070f0030300761110b040a020794008003c81d68203172a83d100715540051386c0b0300454036a0310388000c02c440f25064445441ca40d5801c2140c05c1c4405001940480c0906200d84402c0000d031f6554410142603600c00d100180c04641413021480d0501480d1845070360207002c0544551620180d06190305c0c2c84e801140b01440002e0009c2810011414005403074190b8210042d603c81e098078030b5a04103541c403a15003059680410600c4c4003000164001c001c030444200780440700c1094a02d090300103070b01ca03280600c5007000007461503000282254090740c03c030409540000d0340d245840001e0320f1320300c2c180c1e120454080302d03995100b00d00000308064040004000c810f010011940b250100c2004003000b04514038107118620305018040041c1e110800c8a55900707842402207003007101e203000211706024400b0050064000d01 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 632401600 1250 632400350 632400367
    0x3020c0105040302030d2403031b06020d0522050606060c070e0408030718140418061803020c1c12050c1002030708010f0303020606010309020a0801091a0705070201171902 75
    0x8805483c0288a60904114285403001d0000847c88807a503080d80c4591846014000300388035141d1400700303a058600340340b81540645d9621003240d002402c1c00244560312024841707410704008000701a0f21030120014001100f548840c2d4807400c0150015200302400121101006418003070236009125503c180d4246140c2818410400d50045869070005054410180340480a01d494001610039140001c0c2c5810742080c240f200030401c009650a1484140c91844001003040c002ca141440940b010610000007038500685055003480131140f042c032014440340442a580019082000c3d0008016015805608010703602440b544090714264001c00040b8100300d84146c0003903014142c10f5940194036070781d0314480b012002c02d9000040040c0c02c6500420603943c0b0039080310254600061a10745625610f02c81d01c0e0848105840498a6221000dc0e84000603807102c07010b03078409950308003140741210700c0d0b0000b40081140c403a240341581c0b0210100764400500000c0e44a0221030300000c550310080c0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 632402850 1250 632401600 632401603
    0x30e100f0e0a090c050c0c030607020d032a020a0308150f0d0804080a0c0e15150d1d0c09130b060d030e04020a08010e160f05210c0301030314121603020c0105040302 72
    0x4075144d8000b80c1f08003425030320503040008031f003441303a035403a0301512115001540440140610f0148410050760801c03032180248140ca50001c82e041e410b4000700780549042c90f01070480c6070002e10107100550315040d003602c1030302c1d4200300d44c00d02c810480d074840c00e01f004d51800612034026034000b0125403107000c0d002801c121180f201c2c2416540f411151342c0c56651a102102c942c008026945508003441d03445001d42803000201501500003001404640341d6000b00034584001041e501d030800700d03804450198818107240402036000f10181695150b01c0c91365454200f020000a0801c0d07004e016080ca4020505118203800c04042100400a6549a14010707004018080a0141284098482011542510038201c0c0080c6d00907417500c81010b8007004540544031504001c08102851a101896a0a03103004036202c0d40b0560481c0c519580b81d50550400070810607004602c02c4900c001008a034041140418000c2c0c0d200c10003413a00030f41030740305010440190044010b0710700950b00701820b00040540 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 632404100 1250 632402850 632402857
    0x18050316021509030c04020705010e060a0510060201061d0403020a0c0902030a05070503070e15040506040e090d050708041e030506100315060608040215040e090703030e100f0e0a090c05 81
    0x71a4201501001400310303648911408004643c564410300d840c005c14201600648a00d07400392000007192001701e03256a0402604507003c07448665650204500848600c2c0c52101805252008004032400d00e004000301c90014100398030603889440000f07082610030090f04450552050902e20750030383d966480c4d0080c0d041a5010407400d81000000b400e1180315100f660322460780c40d6120b41c0b54130070b007400784459400c441070080d6501004000106a6840b861300410043c08048840c40706450301201990425140405040801c40f0810002000c500e88809680640d80d111003078000490040d41421402d88403075000130900e0007202c0c00c01016608100302d100450b0700078050901e1110a00c01c000d01143d64901900021426000118025051042000d56003036500c8140d075140c26190200444020008c90740c1810980c4400c0b001d104240d80314807a0460610b00742ca6001c8220183e01e070180400c0a0b1800050401020120328000c5540c3c682d400c6004006040042000b020b100c1401045d552 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 632405350 1250 632404100 632404103
    0x5090c0a1a1317060f2208090409080903010e0c060a081f180f051303030902130e1b01090e01061805041b0306120507170a0c1d0901050c0306010318050316 68
    0x3e0313030001440b4000c45c0285903229401e1000d04d4480b07034809400c402c581c601c0205040c2c44e1018140700e006034a44941c8190450306019107000c07600c85c81010101401e540d03c0c444403408070b40201100f00c3c1c25440300d2007aa075418071309003404507141c1d0b108a444800551a28848020350528071000100c0c500c200c0c0300c04c11000c80c40d480c14031505e10525405826241e05503500f40360f5000c3d002465004c82e2103640b021640034401482d00051b25942605242550004a89056117030400d4980c0c0001e1042e80180ca00c803010300b8200304101038a0031100c4810110140710780c0c0203122810307052a62000410552202400c001031041111107a1106000144054000b640c0c02180c61302401003541c03035007294104082035200c1c0003407111604041824045502c0e04c5c0480341c051181c8141c100c0002c10446015024020fa05130400049a16070034a81c023500c4090000c41c201e9141105000032010482c0481e44d1185007800c012907003d060403c1c18214500301d49003d0010301000c50302d683d00002a038146000709 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 632406600 1250 632405350 632405353
    0xf170a09030e010801030321091b0602070e040309031220010e0d020718020f0c120910050a09030311030c030c0c2403190209030a030c02010305090c0a1a1317 69
    0x900702d00c001500c0c1c560007800050086003480002090350310b40d00c0600c0443c91000319011810a1569841076503105000d50310100f09100003100740040e0358100018001445103044000e600d04054a001c0c00d524001d00000c0d1103100c0c48075125403250301034416120318500a840001c1c02a0800000d5402000c14403015040c50141c801c250248610000e01c2a00b61020100041c02c1c186800f28044002d502442099003c0e00c2c0a21446a0189043c00108404905145d4499585018008200010040c4007442003400818444d40b022175a11008203410760307905003060f001c6417402c2080d4510318025042130100910002900c00c1201c400440d2107941c0750380980e94410381e44a4118150900f11504026105690080c0001079080b0034041d49005501602c0000500d0003444c500800c0c1003290000c0258080f1360000280d00465a00d4420b02d640000450060480c05079024002445051140300d03000b0f01e888100c2c40150b4980e0020b0450f248146141d000802441e500c854080800301000486c00f0385 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 632407850 1250 632406600 632406617
    0x1c020f07051b1c051e0a02120a0b0109090503070311160f08120a0215150d05011d0606010903020d0c0e07180f0e010b18092e0b0306010f170a0903 64
    0x1c03a010701d414640f000754818050007031080300001550329200842000382543c825101200003503118a8404040f02c44600c02a100c0c24003d03042c0310010720410790028000a20749007402d4041078010081c0c5040551629003039504108a09c00f85241484c1640000c0121801503000500c012800c9801021503d0810556803490350640d410700c9580100508900541c2000140702c48449880011a80c014003040030078034a0143c0302c0200d85210940f62013195281e640710314000c5407080c0940d81e014202110801080780d85459070000700341c01400c3c0300c000d00807030060351210308011280c1d03014009080000130b40382ca18644070a00401800240e518134a03940c500080120b460200c89401c1000e54035445000718181e46007407103501160b4450000085081410b005285080d654041e0301800b07440e026011001481c00da5990a1054503030420020b0301e034540c1e0100300543d012483c00d803a40f0100034203000010740c50451055408115100f030046a482d24074042060004855202a903994081d03590420f0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 632409100 1250 632407850 632407879
    0x20a0e060f0922421818050102030f13020d020d1b0605040603061e050d1e030201021b010506030703062c01060e09031c020f07051b 58
    0x2164858203000390401c0300c08001d6140e441c1003050060a5081000e2880280346850380000c0c0d0880715204040c84a1100b00081900300d5040030b08110882c4a09906044084040d1003070342c00389100c144103c075400518000c100d41141c01c10791180001154441002442968614001d4000d5008032000584c04010001280d02c0d040078080d510041035000d80344503843c4507140c0030412881002c02c03044444c4000c0c10304034100000d4214109008003000d031100d40d1a1410000090196109074110030015408c003984084dc3c0200548808221030058039403840c50309842c140308030002e2080c40b01032211a440c680c00c40405a05500401c1c00aa811000b085d0030701454019500b03840003a513040e50b02d58002c2c9414404200d065001c50148100384440e401000000c050f031025500004030080d0807039640c2c000030003007440000790b0160b0050034070002d5807501c2240021540502c400c184040341c00d641c08100c0022050460f0100c0303403420b03046411901c1d0b50900318541054140d001103801e010310000c0c0218030 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 632410350 1250 632409100 632409109
    0x7020601060503011a03220501050610020a0c140f030d1706040b0619091e08070e010e0406020924070507090507021f090f05060a0608030f070305030702010b060409020a0e 75
    0x241628040c0e400303024a0b269101704100981c001070094610300e51241e102d40040c0010484004c042480f46c0000300302454800b0801c0710ac100096510030a42d008903024000140901d004541510401c10250148505007404205156a845003258152207004142114a40c02103041c581166100074103404940d101018001550f4000320995081481803280c0c43d42e101650ba600900310b001440c01e0303003107141e4485074051080480800094800d0320715005204840d818040100a0041418021859450700301c0c01407058200500140581c1da007c00c43c004039540d440d948040000015440d0001144510303d600a507500811040b01d09115021000513400f04070700a2038459803041d0058204c25400b111410000900300300035104190741c903442c00d0300040c501401001078900903001080c0614007161913008549a54002038815401441014510302000342101c4803641e00d0301d8440c4e00c0b42c8030100c060b0301501c40791182d1a4081c80114010400ca441d50b80504140072580e520050552005020700 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 632411600 1250 632410350 632410357
    0x6310b190c030c080318060109020c0c04150e0a06030503030703051906062a0b09010c02060117030f071a0405030c01061e0b090a030b0a0501140612010635070206010605 74
    0x42c041070100070300314082500240a10f50101c0710120a0802002e001710441c14000c0c00d0b00007001142d40441d1002000c24104890803074050705503030400030712195500307102a90003d44280d149649100000910310501604603200031070b8444200d0303499050410000c3c0c05000700b150911894024104040c218411038001c09007120403586440d00344012441480e0021162100807184181c0d44451580008042500f07283c41240008000a550655850000d0030076006034005143c4081031401c541041402000b00d40003c005513605075503c104518201114103842d034070090b0410141070800c000e2082c080b0041148402402c000c000c00da864461148080b40900701d28400301c2c04440c814400002030000500212000820303a811170b50783e0707a03200e1a058800711050ba01868881c0b004108a410403010508511811124213081090354000403410b264144500400c014150001c502000320042c2712842c2150b546a50910201e55240c00100c07610040d200034006224007400040c1c80e074490401e5 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 632412850 1250 632411600 632411603
    0x703060b0913030905010503090111030a0504141209093102011103040806310f1110390303020c060604020304050307030c020f360606310b190c 63
    0x41c0c80b84e05040c41d004490940008240c0b026640d69140030910080020001e140316140303032000171545250510b0302200490a403407040182e82c4c0a912208070840e950003c0d40c1502e08280c47e044e50030741d40e6619101180354200740011004c2d103000215040f40400c405183c84060003070326900103814840100329680d2046114010444d04402c1c041441d001c400c80040f4212224403400700c4100c03610b401852002c1c0710500e002c4910035540c0c0780103001c020000103520400641190a0019030011040142c02d031071500c42c0c1d40c5a1b81c0c08801030a00c0c042d40d201d40d102e040941e0380d000002074005525000c0c0c0254001c0c141440c407449140d001421030b240c5030084910440d4004041c6007002c07501da40544040c9072401c2d089074456001c0d4030745086500ca203000f892003e51071341c0c030205145400c0f0000c1000c0f000121040784108014404004d070a4179660211003038481002c1420581c800c800703020003010980340d03400811019880800007070480c5d10b40c0c05040100c09c0d0200d440780b2070300514000e9580000b02d020 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 632414100 1250 632412850 632412857
    0x30e0606100c06020d05011e0b090d0807020a0f090f180203031b1c03061508060108150a03050f0d02060c090d06050a020705010912090b130905180703060b091303 71
    0x160807000d81d100b8105006583d00c1010090304115444502c0130542c1c04c00d030000901c060f81581e0104c0b646800150316001446000c001c03928107484100480c0745002a40c1c030182c0003020009401045413203146400e0000c0102c4800001b07095110744020019020010b1600d080b0740c10907034006c0300c242c0da441c0c1e500411a030042c015440d00c1884146010031060240e0200c5860040b81030040030105e01003d00341c0d07070410980d00050300300e05082d4140020b1040c01036035000c210550742040480c1c1d0304800700c81e40114503400c0035491822290002135080309607410003481402400c180d480e8544000905148902d019020342d101d9682d141d10768140350080c1d180f180e51002074060300a001c60102d601070303a00080c0d005d4015241032032544500e820344210b414101c5902c80100d056400e940e51203030301c00001d0f0035081c900d20700c2d06410249e03c181c4e03034065000d4240d599980e000821040b9001115240c81c4d100d4040c04e5400c00795a80c10540c0080c1071900d0020300034100a000a82c00503002825101103503030545 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 632415350 1250 632414100 632414119
    0x11090d031103040f080c100203130314010905032a0d0c0305090f0303031003060606030b03030409020306040b0918060f0903031512010212151005030411040f0c0f030e0606 75
    0x8404a40700c1c1600300d8405181d000401c0b020520301c41c42d008a4016100300070050000703120b04414000a00d1a4001180441d001404040345120031f40c05050704a0350084a040360183d0408030507030040c030400e48010103e03c00055210a081841c00c40b18000d11100d10a84044612030b000c42038503640b00204e1140041c0f904005000040c1c0101d0152506c41c5019003064011034102002c0381c5141e00a80e4a90900401c20004100f0030550b402914003500083c40d040c4041740c44e04022039520300450041e02c0506030007000050366500c8070f03485501c10180c020030100450034441109116078198956422050003024000340110720314494003801a90f4078001140345507076150f0b07905907181d44d25400c1540100c080c280c007400a0824000b40440c40603030003100d0614101610410000c07002c00003024001c84a07920303d411029004410b50780d0058005100d4401e000041e000203006000c0d0705c845402e420714084242139415480680301c9900c1000752810010041245100e035560300085035820303400003030381 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 632416600 1250 632415350 632415353
    0xe150a08190c05060a0c150b09130212010e0d03050c161208090d1403181f0608070305070605031519090b0a0b0a0509011b06050912032505220911090d 66
    0x104aa01d0707c1c4d405103c00101d80d0800d0b070010341c3c0924243ca88088401c18101c15809510304203000402c1000200002c020312070100000c03a40f50180010100b051595840c00620b8070002582280e640c150510388d400d001c00301c00d02d002445040e00c0c0603520000f03605480010650300b400154140905816114440d40d0100c00f840015242e1009054150400c4511070001e40402c0800c5a0180341c88500030913104c00410b03520318022141c0552004075240d100c1c1c801000414000324099080c2e61461519540d6940d03202c002141c21407440401d180c002c101c0140313001c2e202501103548002c0d07444600c0c040c4014039280c002c104191a1600824600e180300304102824680204010030389214103060181a11204448207055403c4007002500e6180e192020401500c07400c0c07040c000d04e1f4940d0030120342142880c8802d02d04001c03030600d020546080d884200804a40128140c40005e000325545000420080d4060f880321241e41c40391807100f40c142034503003c03484100d4054440102d401750215583d80d809 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 632417850 1250 632416600 632416613
    0xa080f01061d0f0a0605091e090601050a090e040804030b070c020f0402090d020405160801080a051c1202130f0f030203100b01110a03020303070210060e150a08190c05060a0c 76
    0x2000c201d5a840b080f01090502540c0310348500100a03d90360b01c1e02d07038880c20f2110900c04042c50019104200c9003105c0000c0754543e442d00c4609400000a2a0158442c8619282a950400b0603002900061094030030070042080410042051381c2c4540004000d81d212000159403240304894003c0d4428641d05080ca0359040c01e43c00b50a1845000306041c0c02c0b64801d8000c10b08541054541702d6001400380125071681d50803095182c0141481d500521004071903464071601d81403030a44000101c0140c15200e1010780c81798181d803041c0c40d0703040d400b103541e03150680004407070284900c070b81401500c080c440019070f041079158410840350040c2c01380c08049050394404000700433042d02103060040c090303d2400e040104004221402c0d2180c4c0046649040c411006803600c203000c0d805190f264101103042c06454084c142d465000322000c0b41d5032496020340000180c08003056040050306100e00f00300f050b030030450500c0d86d111140c05210407000c2603460301c051100c1c5200b44003450001ca003031002c606000980 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 632419100 1250 632417850 632417897
    0x70b0412320d0f030911312304030c0f0503040e07020109111f200109081c1104180e060702070e010e0f01050904050a0510020301090f0e060705130510050a080f0106 72
    0x9103251500b2901c8170500f1244807c400f0980001e046030366408817001c0c8452500c80000350340a004441c501500e49543c0061000a200000400d500c0b6411500350822204209070340152124403404078881c030b000c0c3c0009008241140c0141e400d0070300724003412920709018a000060654001092a0b405052907007918150800f04800900c80c446038844a46200203104a89841d07104011842d959805a204545880b007251000309009181041c2191200c50400c220303402c560480c2d440c000c11303e000b8001c0e00000c1c0200394118109000b003004200d03420b81d0108200c0b00342c412961004c00a662240c4d02c00400800c212903924a01461900601080c03419105150b8132522840842d0752581640d40d5543c00d0203840e5801e0b9034095000720051212a8007401045c860111206040003084010b82c0016a908409800c0d8800d00c00001441c0c449448038241480103410b0280c000e200300c00c0074000c004d08680c0254140c0c0c0c00607010001244040180b9140c942c105c03a07640d601c8800b0031200003491380a104 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 632420350 1250 632419100 632419129
    0x50a050402030330090d12270302011409072303030a14070c0b04060801080c0d060f0b06070503190203031311011e11070b0412320d0f030911 62
    0x9134089000005807181c82800c2c4c817540001003e000c955060200151030301a4105040c41c41a00300001410903002d01c0348190340c1c1e070f4607045e02c20302d03034401c18141039004108207500342031084c08800810181c508e00150680c00c49403510750301c000c1c0302e04265003101c0b0103020400d46507058004108846440344240020324504102840c000d10f040c1c001d0b0380307a02603280194041d40c09040081420010603070403803030060040400e83c0280c8002410075002510010030b074000140250707614820741c0001e1303d07164410041414050082544c4010b1303803d1086c0e8a8104000980d1062011401e20140c0f51022059074060380702554401410441d0b996020441c02c501c83c401c904001200203d42d0b02c0c4055104510800070076502d402d04a15101d04101d420903481c1d40104880440c100320401554407007003d5400307415089103184560a5403901100c2c91070041784148030b648400c88040c07100b42c9a0100d2031a148510b1910354560711601c4400a60540341c5543d0040c105944403200301c0138070309040c24401c9100 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 632421600 1250 632420350 632420407
    0x14130806010b0a08011520010b0103111c0f110d0603060c0c02060f0a032c070501110309010804020a12050607170103030e01050903010e0601290c0705190803071401050a0504020303 79
    0x47c0303404010403103003201c200d40100c00ea91a40714641865802d40f1a081d85c0c1c8032111091483c00446d540041c40200780716024660603a915047c12851130825030000703040c00020500103642b1001906280050203240c0401d98500380741000e0700304000c0c00b0b05290089540d0103013034107050047c03405440d880d540000203e01c01b490b4031103c000800454040c1c0da08811840300440399a4141401c88082c506803207a0000c605010911a03d220340c0c0d00000f0a691110400b4a0010920b81c0c2c0d038070114148140325400b40740032944001081040200228409109000c2661811303da003d0009182621000a201c0540403a1584076801c5c034551141004003010a001760011511080da011a41d16080c02640203503000d40139121711420b541030715180044504d60000b04a800c05050b050596102e9540c2d00c92240305490003000f00740c00c1e480620030b88009284110603030791903240d281003108200c00f2004820116510700301c0011160522441480d01440e0060002c5040000710150402c1c07132607003d4044c9515 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 632422850 1250 632421600 632421617
    0x304030504030f0c0303021c05190c0b070305010e0a06030b0a020d1506020304080f01021809100305010c030c0f02160303051c05041109010e04031202070314130806010b0a080115 78
    0x464000800780c09007511a04c242e41c2180e2850600a0401c00629410340c00d0350302e41412580019400025076079443c52284800054419281c0180e4880c0040c1000500c0518000c08000001c1c0e0036500080c121a01e003010603019507a007030050b50446519000c028400d402359004540e903284a640035052024002d54001604141440080b6a18400ea8400c600581c00001c1c2405130030000e1040d1484c1e9a1604029070421580b03c0b210f400072480c00c3c40d03440c0140070000c0003448840130038503e100110780080080242942c503500007005840d000c2054004503911880d000c0751548002072540340e00a07444c400140b400e0840d0381c11176007644595410f00104124040c20142a0102d00c1014046c620030340c415100c6080d40c03c24840f1040050b070013040440714407001c02011980080700e40c0c1d14900c4000340141d9803103940c903003500c52118500741406031500c0418800803100b03207201604140c404d040101c0384681e907100201d48203071140590301c42c00222420010410140d0118515420718564200703480f1 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 632424100 1250 632422850 632422853
    0x30409110a0507061503080c01090606090605130513020a090606091d0f0c130e0406050f13080702190e0a0f06081f0b0621130317060d12090303110307020114030403050403 75
    0x1d42d800080252003d652341d0ac401a040082c4c03071052170018000e4040501c4031524102c0003034118611030704804034131500c3e000050304000d071055105e1100b69001f88a980802c0e100d010070f40040400303004000106100703c7d80881c1c854404010f402260100c10071004141e9903501280c40700c504041c001d07010075641400b03003010030480b542031030014204014100c0e41c02d10703150400340c041d1103000d001d1003001152130042c02a100307603150350344501c107810480441e62042c040c03020482d0b0040780c0c0c00700540c00000c03c5010a00c003088078030352030060071813103001d11021201d51451812142644140402c55004600c0d80d803569240d0341d9510008805818005203014025001c41c16651000c041400c1c1d0030230340091005862680042140c22070a4070a0741d0150b10081c1c1e80141914090034402c200b0801a0000070300e595903088200e440da150311a42541c0140c480340c40203080d8444a01044021450480c524042d46100005951007560140d5034602c003101c0541420035030340c1c4041e00031340c00c000d4200030100 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 632425350 1250 632424100 632424113
    0x41b0806091f020405062a010204030602070b0717060d031806021608014d13080f152e030b010501081005040e100509030409110a0507061503 62
    0x1031145103044050700c000e80c0700d100101c02c0c030800d80c485940803500c10f010a000d01d4036510300303841101d043d1712124901190070340340a03107061650700c1040c0c010398000117010080101c0c82c0c02915420b481000d5008207901d51100079603c404601e1501010ba1107500001440352614200c91454035009040289031040500c0e5107103104161600590050b1f4003407928030518140c24242d86006006100003001b400c407410701d590b203194004408418442d000f13049a0000c1411800c1c01307010000503950364045200ba10101000d032030300450900b00a840049800040301e00d40815055440000c0c24050541d800460041482801c0050150390001444a0504080e20319942c8003800300c407407511003072054600d54a420342c04086c0503002903041048034402d004016850f09403000c1540c90450b0089019803090b03094528023040c1c4502c070300d078450502080c481842c0010000b48151203050308140300000e00d0751034001e20b03440348028403000070320104004808241684e1140c00700540f50000003003580c0c0d41e910b500 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 632426600 1250 632425350 632425363
    0x9090c0d091506050312070305031b04270506040903080402040908070210021f06060e010c0203030d0903080907050102190605100e0103050d08010f270204050612041e0b041b08 77
    0x3009a02d43d1110240010700d401c10144402e262038200c40343c6008000d40e801425400302030a95994070301c2c2c0d500c504220900c24005c5d80c000c0c1c144641480410959503a54212460004130503c003090f14040100d0042d0600d070291800b03494141d00c1d200c1c01d80c3c8582c3e00b800001c0c91000300949003444d05100840060b0350301c46203048807054560080903101c1110140781440da446110020595140800820042e0b4020380c098800003c00d003080114100d003030000c0303030841c4a180009480036103040022030826400105042c0078815080403290312a4542005a0351041c46e6180300528250308002d080006400c0e03082a43e200300c10004603c0e01581e621240c10401000380c00480b000d070080ca8150310a030742c1c401c050314014040e000d5001b0005142c000d584240c00881c00100454224101514501d400b25804075801800003503e025510341e2940043d8403143c5081d1401c40b00c10703645484114501650f08904618241c200c1c102c14240d48450b90b80340440c1099a242d50000c807400b07040002d0300c182c140100c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 632427850 1250 632426600 632426633
    0x11a0d1115040603050603060402014118040203090a080309150c093f01110304050f060a11180418031e05030903040b030c1308070603060b09090c0d09 66
    0x2168030baa04240b4050140d0b0300c0100880d009a10010400004d40e0340302c201003410f10428800541060b40311072703d04c0658a8041580e43d4000503d020804c468000031008280c40a03481c00c0c0c40e6080c8180c0c3c02080142c4c8016500500180d01140020300400e05071401140c0003103098003110081a0885813500d58034104451800c03803400085000202414444417040702c84450f0a241480ea030071000b1720035026010700f404010001768401d55545007840035407084044040861581e03880740340501d00f0755501d208201d144c41c40780c06180302042c101103090080040a08000030b40e103040070f405580c50311307001898650807a48140c81d01c0448201191111400200d54081d80d1f8101280c501e0000c0c00d0002040321042c03804000707080041000903000401035400f6649103d41459494440208400c0140120341100740200d00c0c0d124000b0b460311001640038100c0751980c03414400c8540c0c070804103d46025410b81c043d04540448001903c2c408200000c2650000c038070f41c00207961256460700c04a80000001 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 632429100 1250 632427850 632427889
    0xf06030a0b0a0636020a0c020a15181202010e13020a0c11030c032802030f1b0906010509040c05160f02150a390506100503011a0d11 58
    0x2000d000d0840390741d5140c4950460300950005000903040008241c0e4071940340d130040c8550220314140824491400000c845800034000080180c9880c10400c5045840041030003003032990002203010030700003807544100d0388248840b800ca01080d4005403121340d2820200c560050802c503e4010203002880600700c8074a0340d9903440e20b02e03860313460000b0b0001d001c00d006502c40e40c001d1282d5038041c0c1c0c0010741c01480f80e2406a501c84011404408041e010f0450070000394140200584c800c00780c2c4002502c0c5403501a001c040c03404a81d18102486210381040d244140020002c000c0b10344c2c5424190004030030090f40380ba1151500180112100a4a0342d40c0401c450003a4080e100106502d808400e090400180c600c2c0a071170b2800700503000e002c0801078103101448811042c01025024044218442100d040f800761140c152424545280c42e54001c590700c10614400317041c003054078141440b1b89039405040102c0071100341154001c016000c03501e405c00702c41c064020f05036582d968580c09808050b28050070b2 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 632430350 1250 632429100 632429111
    0x152c032d012d0f0b03251d010512100c05070203061f030b2206020c5802030403030909020909010b0d0f0c02070807060306030b0f06030a0b0a 62
    0x5600600390b60445200c0c502600290103003106a620640515a1182c41e5060004251240101d408050f1a001d4080c03541400762110264650913031441c1205c058a40b10340303201c00c00703403038180e10a0201806000550394001720340050000e41407801d05401e08031103075011240940f030000c01100554a8640d40000001e1000c01c000d03003181810050750b42c1054880c1512004411003a003002d03034402c580d110240981a07900c010038510004042c040b40060280c40c1a182c0040d01d9045c0080a9403041d14101001c3c410001c0013408903008140c0d00461104046800116a40b401c800301110b5400ca50245803404000c00c4110010200e40d010301038001c2e01d500078546403855170401501840c056804103002c640104400501e0b82c0c0c0340980203040d60711600c444e1b81c07240707001c807161001440001121003010b440c0000071940300303400154103c2180c44c1c10301210225910380c40d003102a101d041c4802008954214049081c00000c0000180c0c4000003400b107a038203020b1a01c0b9016440300944801d10202d50781c4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 632431600 1250 632430350 632430433
    0x52a040614190c020d05030d050f0c18100e0607260c030904020307030605120717030c0a060518030406090503010b061c0507030b0303070309152c03 65
    0x10158402202950035854141180d42c40004a0307500082110010040351815040455880b081480200b68228003120380b18003040000728000c050950b00340c2c80d80c2142e440011801e49140c030460f181c55050450803d00c0440c140203010710301021604680c1070081c5100d000b00c180d00c030b4601a00c0580e0160710071120b88070703a40100b100c0840846203010000c00c3d00700314560492000000311079a6440648006a80c0e60722441c0c11401003080350130a0b43d10882c5038094513821031000034448103135503582176140208101c10058555912402118805a0b0828008070303001c121658001d6034843c0c129080f00a440290200c0e00c0d040d6032040d04420041400b5402c24403c5050900c510b1000321002d446503440d20100e001080d50b80024107402c035060a44620010700342610940007004481405400c407520742c0c00518014046001d0f902444c07051246403124103109a20510441ea10030f940d201c0800004810750b41813507440200c55861540600ca6484030300101c403001090780305500c880c6a81c41c050070b5040e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 632432850 1250 632431600 632431607
    0x913021e0304140d09171c05070c061805121504030f0206070e092403010e1510030f0f06020f0a081503060108060612010609150f080619052a0406 64
    0x2441c200648135801215580d802c690006581000e5034021284003001910007580b00d4540f044119954240c9000c5c4070080c440c0c1500100a01030803803180c0d0105141c0c51320381c10211340c8560021028851141000d000b04013030f06202c04501c210320b01e8075003960b52408403000c00c60b070b11032820b032003c500150341c002d410f116440e0b060080f5074000403141760800442c2101800601c036105e000d0700c845123406007e0307aa60300b07261281d607145042da44041c000f030000c504d40311125a02c4400170003c0f44103018080002a4031164000540ba058a078010348008001009845603040440c0351801103c00990030000c3c2c05000e500000542980f0f26191741da0003142c9821074230203042002200300320f8003a0703008400601039404041000d41e030001e401c0ea00e41400f9883c0d400b8240c0908150341c17060712344903e8a10440082000270004030142d6520007855900c4a03a12a072040d501d003011100c0042e00c05040d4103900c064044c54200c00d8000d00045a00c6036204812030508000901c0d42da205032558500041c204200c640 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 632434100 1250 632432850 632432873
    0x60b090316032003150a0203070917070b0307020a0b01030602070215090d111c0602090405090a03090308033303060901060303080c0702030109080c03070204110406050913021e0304 79
    0x9407420015101441c6903a00000303c07100c004222410b00d9450b03541c1d0302e561000c02180b580c2c5e104415a05566041080b0200020351050710346a002035010940414816107140e080e500c4842800e004180d158030704500c20080e41c2015000b8400c5010314414500444c001c0320680e40a540075850043c0e44031651b104104a2401d45c40003001035203824800d02005a0b204090840c11130342085140c1003040381310f000101c1210440111254600018883c0410706c03103581c3c042c6c40a8030050340c04004640b90b00c0c84040c0d440704034072170040c0080e035510310074000100d0060140d5042210181500202580012164000b8070342c1680602e0500c14440310f0201403400b000002c2d044140300c80208030003811528024020030380240600c0c07145000040100c02c545095101e00840c2e42c200e1a841d4a4944503105540c0f20380c01038506034465414020245091030661044508480550b00c070b0070704d08540386040c0207102901146030320406509110590321900d06a03800d120754440740c42410342c1c03072620746041d040000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 632435350 1250 632434100 632434123
    0xc0a05041e1805060f150409020705011d060c0a050901050904060801091a130b0c09040905071701050c0d050a060302040c020c04061509060c050a3e03060c0a1101060b0903 75
    0x70f0811007072004548804070000040d05c0160744002842505e0460b040c2240b05a6000b12255440000c040051107010340c0440315140c001d5054061542e005e042642d665042680d58000502c2c08000302c102e003d0080004114650042c10010300340459a0300240c200d83c1e00e6403040305640d4481c00c0e2a01002100d011000101c0010006106075040c06102c001c41083c8079840240000700d52404112010002e40a0b151507800051040c44400154600141c5407a554030440e40043c4003c506154184418000e0138403807200c6156481c103000140076000003621000c0e11507008281d460401001503140c46c0110307843d640700c84c1c0003000340001580500040b1030b0f05a0044000c034210780c03050304c0da0b66808041e16049600c1c43c585508854035505045007401e00084005098508240d401d51451203004071804818911140b15003152201040400b03c0c0141051450b0341a008100002c1540001c03070007611291b01f540c0742812103a12000180d508680307454101521101d0301285030380461404014510442c0d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 632436600 1250 632435350 632435399
    0x31a0a061a040e1f06030b0a0e040609052103040611090312090f040213030206070317310c0b0a020f060108031801020a080706090f0602030a05180a05060c0a05041e 72
    0x114002d40c01e0130030407240d000709010107440d41c01000d000c0c1d0303c5440041c00b6000b842c1e0400450700741481c1c07c034000c054001d03080340d46010b810480e2840303034008202000d81184a10344c951550741d650356064004c000481800304c04034030901c000c104d183c60401c000600580d441c0052681c0d50035032010820b00e070885c42c1c2d00c00d21850042001081c443c1003c50044100c942c151546500c52500e803800399500f004050742040400024010010454900040c00c44402e1429000ea142c04009010a0404540100020b001017544003c1041607040210051038840398500c140c0385450321040381c0f2420b254007a0321500c0182e101050240c40600195081a85407209000614140040ea031343c0500b68014100c004e401c80c1d6480c81c0d003d0520081080d510304066004400315500d18141501100401c81680e6004c550109050f54040d503510004201003419000401080a41d6803140d400301d050f480418800c081000030f12000800841c0481c8a40038004841c5a40c18014103003500c0700b13210b403181c44001002 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 632437850 1250 632436600 632436631
    0x3030703020307200d080702090a050402100f1b050609070e19020906090406260c0a0e061309080c01150b091c0507171006031a0a061a040e 61
    0x390000102d0300f0169101440c02900a03000040d4074101c3c2009040c5500100d050205804014202006000c2144202c1d0350580540752014490103ca1f01150029005030100c1c41c003e451a0185400b0854115546044403001030000601200c2e010b10321002c07503240d40500c081c011441401d1203c0e00141c4200b00600e0910302d44012000705140c0103841043c40070b54000390205183d1185c10031150307075020141003804800c1d40c41076001c0240c82d600310b01509050320b0350544452440d01140e250341441c1c0042c9071015035402d00b5004c1c1981c01d0301400169100b04103030316903000b1006600501034441c0c064014a501d07146205800c0342500c01c00c2000303030807488010714240400464141900c10380740e01955202c03001000c0540c040003034140100040e000780329802000a0034013016038182071403d51101503800c940b0180d424103041e520b4600004200c024051140309100600d01c000d42c0e805810181301290140c3c0d198448072000d6802c4112410760340c0005400e003c602641000c8981001c04502c181c1c22 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 632439100 1250 632437850 632437853
    0xd15030813180507200a050d05030f16020606060a2c011115040f050a0b09030d0c17011e12120801140a050927031209150c03060a12060e010605030307 66
    0x800099204005882c40c04001d07070540c2a0f0100401c06c8403580c044c0498040480840c400760040e04101c41d03445446a041c8000303060b034489000440c42d225502d400a108a4a802c010042c2c50742103924802c08021810301d201142c1e110041d40e4101c14419030019290081c0c3c0d10f4001003c6442e0070f4510180c55020303071340b5140c442401c0c6081d01e030311075004256400d190a00d8608039080600c0000041e1064500005008a100000c40200f0120300d6540c403c014a020b2070b80141c90711882c0c4041d1021484604004110601c070850300d600640410521000c1419103881406800042d0f0b04801d035803850030310b070003200c801d40c02c10483d9001d0149a030410041415078000500c1e90016801128010483c050204a8205141168084000040c0b95140c001e548005500c1c0c2c2c0c9412040c03480300746018100101d05242400301c0c082003a13011440d00414299204000688107030701c09046543c00040005000481001c40303030100700f24900c1010042800a4180d20b500e003555070a03000300e48a50410807a520 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 632440350 1250 632439100 632439107
    0x1e06090c021e03161a070801050909070605250b010b07030801050f0d02041113060e100305010608070f05070606060809010f020a0c0b0a0605090903130f06050d15030813180507 77
    0x240180b10540340d140e0071900c1d41c07800440c01c3c03a565228019125888046c00318054029542d103060320801c2d81c060703450395103c042d4655141e003984119000f0840402805010084508070401840c1c44c000c00d81080c890a9170380e10300c8110099000700c80c07425000c5001010958004961030041030201c404400382101017000a070b10741000040284a50758841c480d0201071b2844083d42d0150a140ca100b0303030410f0351020302400c100d5966194510400741d07605151042030291007400c0c183c445558654049540b500e0b0180d82041901ca01c400902106014050000f0350b0f0b4001c501c05800c0c295258911410810380e41d9007502c80b09a4400000780c018403000102c0c5902000e003a040302d80103c4c4071002030320b41c031034000024101508441d81043c00b04003004800500000100744848103080e00b481000c2d51881c0080100d2041d0042100142080049034032400198011444c04049001503c1500b030b9030381e840d61034640c403c1c040c0c0c03e82031091090410801c004000400768070035010200380424541104000d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 632441600 1250 632440350 632440357
    0x3120a11030c07020f0a08070501082d040305041a0705100501031101030b0a26070f0e070507030302271201110f07140a050615061204061e06090c021e03 67
    0x90a541601054800940d503179000c0d80130700704a01500b8802103a0711a0350303003612a081c41c003031980403070f1100011a090b05c44420a042ba90b0240c40c1964001500d2001c04803000d15001d001601084000d0002040130b100d000d041c003144200c828591036560711680b41460410004551100b0500e20301001000800c501a00c40b03070016109180003d413081d1001c0000d0b44140c203980241030010401e0748414900001c1540000300c0784a140c0444400b281da4005800814403940620100c0740425030116204078011005080c21602c40d040c003505021020b2101c841d852015100410311800c01c0756000f80f64180440c030601140d80d071030001d1000c032544100503a69441002201642c44100044800c244050401204489480c100c241c8840050300d04040e981c1d04d0701585c00d600c28240c0304442601741d02e0710a0880342c04110011910406660320f40300e0000030304411094900f100009088607211194610442015104580c0c0003d01e541d800e0b07400070b24003501e202d016880c108a01000710140600003054 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 632442850 1250 632441600 632441611
    0x210d111506090a06030602071b0e1603090606031a10090c080c0f0c03030c040509070e010804120e10020102180a0609030f08071a060f0102191704120503120a1103 71
    0x2e00399507482e030420200040013164409010a4800b01d40c074130400c242d41001d80f0142211040801880343c8806030010442030540344000654040003070402414043c6c1c1044102c68024640010b02a9036034641c01d000c0030002c240100d4a2001700c08212010b0b65011030313940500340e0010100102d0b07019650240c0000c4010b440b08407003080c04101d003080520a41d084071310030703070369441030742c0c0c59081002050701e1a40142c0200c501c6132000300c0016407110322950545500e55416590202141c0725501c941e40c07030780341c0e0865800400200303000b03109482c0c6401600c003484480507800141d0b1491801d860310306018000c400c480c8104030307941003005116403000d08041502c1d00500850390288481c50311030028403445000900f091202050b1070284200000e509119038800e0b5183e2411610740e000480c0c56401e441568505210565241000b240c0240030030013a0300c8240711000d1605444000040c0020343c07200007110036a0000a06d40709480495151580202004c1818401c174034102c40c3d44529800f00819 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 632444100 1250 632442850 632442859
    0x80c060a1103011a0c16170f01270510020a02030a030501050406030206120a0f0513020f09100b0904060509130c0f03020a030809010e0a0f0501020d0c02030d050702210d111506 77
    0x22810a80901030122060f1900700e01084c0421568800b06070000c42d1082008007000c0c081c81403100d400310810300440181100552b5800407950300000000e099241e800c80586940c45101d03100104529244020488000560015601e58446903402010ba880c143c0001d130145e820030004000580700c079410f036102c0500c1e00754143c0c41955501108001000b107040703c600310034281002d0007000030600d0180d0441c0c2c3e0003039507010800c110305001c1c4404000246d400056015080100708a001c2c1150040d1030001001040440c5040d690760002d409103000391142e0419040a0040340100300152038800c00800403136a40c01001855a00054030180192201a000d240d000070807114580c07240d0b401c80e02002000b484415013948030071034407804d11504e00595002d0b214001d904c1ca401401401c0440d841a4010001c0101c250342101c2100c89030480b42c802ca0b000ba0b01c0140b01c0c1461b142100740321740c1207072402008008400701e080d002400c0380051400d201080e001038024015458041b0705485e8007000030355 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 632445350 1250 632444100 632444107
    0xe1507091701540308090d02070308090f0307030b0a0c0c0b07080411030a0b04030801061d0d020a330509010c02010e1504080c0a270f0207080c060a1103011a 69
    0x21070368000c50040f825110014031107000340c0d6070b401c06114000c44495000e541c81c0c640715981e0003940d41e0740c1c0010100c40005a4407069042001072404c0000f495560009030260955407440f00c0844e10b0b01d840790f0011150b06100d90f080002c140440e00c5007074205031061038050301c41001e58451811605020300a201000400e00c00102400342181c1050380648019088a0900569041040003400c003583c0c102c00040081c000011002d01c15541000700d000600c44405c0b55140010410a529015090881e00000040e90000d80d00d500031b500001403d015481c069800c04094070b02c2e100e08040841540e041c400c041c000d18580e66405100c4d50790903682802c01c0d14003e544c001c0040c1106000c1506094a40000103000c180c1000c041030441d00090143c0703c0c40c4040e500d440c4422000d0310400240c1c40d40d2540c0501d07000d0210744940003c840e116003240010b10302105600e501001d5440109031083c9548400184800c03020355100b4890040030900450b403d41d41810100041c00c4000e5401001026021 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 632446600 1250 632445350 632445431
    0x100503011d06031e010f05064c020f0d020703080d0c2f01050c03012411120901080a2f13090e0f0f030d0e1507091701 52
    0x40200c000d500b09000ca80411400340181c44c0c5001e450709886941c91241000007091740c5091003c800300102049006d03600d466850a1a210710714081c0c45004400c8008040c98050540c100c1d6034191220402ca80c080d0442e014041c83d4680741c03040b40306062003154803640041010522070340991700311520951000c10131308000c0320116100600b400c1c185000b40450b600d51740d007401800d0102200300800714000d0180b82d0740c118108031980402d00c00d420309031281c000503c0004510101e030320309840641c01d01b44500b44003040c0e85031401000258882805c100051403090540e004404075074049d0401c035080c030080d07001e544640b1541d002941140b000c02c107000c0c011794104078102700b520082c01840c04100700c101d9450a050f000b4118a400100c1c090003410955011200701084c008101d000201c02545005540c590840c0200140045d0200d140110307070f8142c050318019403000d40140c60590301da04095081640c0a0074000e440e02c07180e8030726858442a0341c0d501001a440c6c0042007403001ea02c3d280012007 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 632447850 1250 632446600 632446603
    0x6060405010c020d06141e040b150117040506010612020a0905010e03030d0f09170c0c1512040c050906010c170706090813150518090403020304090606020c100503011d0603 75
    0x91300424203401c28402555403030b074441c4131a02c601d040b220302c000340c0c00c55441d580070f11141c1501e0281c42490101e0004507401d0500e88030741e1401e0810b144c0f2454054a4600d200101715054500310b40c2504008010044264003008407004000814021484d200307500c0409482c402070340c41040d0601001140d0301000741c1d01401a910040c1ca9041c01340283c0b00140c01000003000420000c40e4019170403840c48004d859003100b40c0d03c030041c010f001498180d8890301007142230b00c041030b81c140b202c0130104a11020403442c843c41d0350056100d01c001a680604000030040b80300c0004041504110b0740907506004561583c0d509501c00001d500103640e14490303070070a40c002c0d00e000e1401070403008000444281c7c3c0006904804202e07000000d0507507031130640e04030031140342c409d0324603160035000701808200c0304e440c0070615150031902c01e00450b85816640d8213540c003660078035031090340540c110503150b5049050098100048800e00e19100d461036041621030040b46110015003900000000d001070400e850 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 632449100 1250 632447850 632447869
    0x5030607080411041a03070602010923070510110706080c120919030206041e08030a0f0b090112020109080604082b060306091b060210020a020a0b0403021e0606060405010c02 76
    0x3d0142081c0304085c3e501c0c001401203d6044030050180c4124080054428070612502244641c0442440d020030a5101400c1d0410f190a801e504680079503100002d80d40e80303883e0b6801d00c4404a8540b0304249002401032404d01d4581d502050034801f000301001502c2d401802280d40a03003000c800c407075054407a614024909000c171100d40004d40500c102d01c0e0141500000d11910641c4602c2c0e1807110388810045140300c54032880d1004068040500214070030b00c003242c01181500c4602403000485011f8500001d00715070082c3e010380d02071030b101503040c000e550703220700c0982c05050075900400340c604143c4e444200c0c601c41c8030010941040c82c18201c2100003164000388880901054051256a03100e040400040c20f0f003180c21120808200c020394613600d108801801252626000b170810000d803219414065481000040114090300600000055000001c9405140203500402051466040507048a0240140600d15a010b003080104070382d100001c4809861080c42d15118900c1240b01140c2d0909 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 632450350 1250 632449100 632449133
    0xf120c140403032001060501170703090614060411030603250f0f090b0d0b16171302010206100e06220f050a270206090a08100e0d030501050306070804 66
    0x140041450380c001c50702003107180030a802c00c1c4c1c1103400060703042c01c942d81c074070070540419400e2140c0b981c840d0f0004280740e800348550401080d9541141d6622044071000c005265581c0040e03070074040b403424944103031001504c100446d40d1a600b021030001c2c2c0c0d50860f85440f5007038402a49003d032214403000341048010301044545200300e544480c80b501030f0f00d0607030081c2d0310745c45d02d840c05841c40e80c0741015800703030283d400c00c0c1c1030481516030f4440607940002c0003c0c41801c0c4406c620301204420960001780d8031031070400441c80e0400803148002414440f011341040b903284e00c010b00511418800c1c502c011342012080302e01010180121100d114a80d4802c0c44c0ea500080c54000128070700f0400d50041c1d0303c42c1c2003490080100c05017903000b10070300701454190202012181078241006042c02001049072000040c203412080340e88250701c07864030f000d030280e01c0002034480c94410500e0030100265134004d86503040502640d030500e4080b030f989500082428013007081c0000410b060041740a29010b000c2d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 632451600 1250 632450350 632450387
    0x20105070b040609061413120905030708070e13201f02010903181a070203190c210f1e0b010b07020315090a02010c110303030f04050d0f120c 62
    0x500c2d05040080082900d99015244c080c20181402c0342c504440360054071404101000880f28691a125500182800b2a0a4040c004001400706565a00700300203c000c0c03001d9801010002c0c203110503184101c40181c410a08071805042ea0303000607644145040701100303001c0c00c400d4807403002d1001038031081040e1a41c1c640c00650079502075403640e06400a810241c003986031000988a0110980c180c00d10310320401414030100c48800e089090400000c203141c6000504540e80304003c110300014080062504580c060140c4404100340b130540f407c10844041100ac170020b04002503200d1002100140500900c2100240c0c0030b2200314285105060f52550004040d145d250384804810280f540100c0081c0c5c0300e031044425010b1400c05c4664454802d01303800300076040301c1405600555200d508a501110801d4209440300d00a440400185102d101e040c0411000c038201820f03c1030a1180341c40c4000104000c50401462050b0801d105c082c80f0460f00d40300040d5010820000c07500280c1c81034242101 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 632452850 1250 632451600 632451623
    0x1203040e0c030403110c060d0b03210903070b120601080402300c0406081b0102030f190e0303090a030215070f0b0403020d1112130803031905090c010e060702010507 72
    0x41034541e102443c0b00d20300c25107540e11901e0302002400d41d103111000705254010301c200a00d50188000d070708010794003000070f012070f11000c00c03100041860300500594030580701c1c4042402c01c0070346000c00954004201c002c2c5c0c1d6500d40704506042e9000404020700041c113106d4418041421902da02d8802565014031840800c042c01600c4460107000c900d00c1100202441840349604003403400b4494582110460300007000e4041c5010102c52600303000c400c90f241940410302c460480d04030b4600040c0081b0b0700c842600f07144c4a1601c400a401c250884123a00c2c085d6209100565061301ca01d40b4050039030ba011078624150000411a0300218402c4080080001a1200351001006604103000780980d200b50252000002d04203011103030421500e00c501c03059404040145140c0d51900000c14041c00f40500d503e80140d129036800d0f241d40d0003540e6104800c16500e54440302c1c0d8050b44242500700003020080d01d078040c08140000d041110150740f0758400c01c0c002071400c0071a030080e001c80b20245c3e84000721000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 632454100 1250 632452850 632452861
    0x9080a06150603181101110604061e09031d1309030818010e070b1309140420060f13270f050105010c030c020f0a0801020406110c0a051203040e 63
    0x24080206250304074202901011424900a000300780f1110402c0181404500e5591030303000d0300d1000060024140b103915100d1130240740c000d1000c184a01d01904001c24544940025144400d140e41c1c43c0c000b00c28600340294000a0b80420281c9041c102400c00c056080100400588400c081c4003c102d00f0320f1924076a90105070f00610b005100341405200881d00a01025075182a1350800000c924103410555062140c00d100e54060b1201c40701700881c00e4600c540307403000b07002254200041c048270051034000b0442046a80100040d07030721210301040704e9058401002c00d020f03000759038440c01e000001142001c125083c880001d00188a1000c0181e4400d041007010850301034240194800e49003822071000c021070b003a0056a04171541030395100e20140140d242100c6003070300c000d4200d80c080b10200907086281d480441840113021034100041e96230b0f00c2c181300600800d240d005003291a4000750348040340d542d40c0d4280d99044403c180d5000301c00b5038a000c03150b400c5102d135802410075011040207021 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 632455350 1250 632454100 632454113
    0x303070504060f12060602010e12210c0d14010302040f0902010f050d0e070611150103080a2a0605150118050d2301020703081e0402040f02120405031908071d0109080a 73
    0x4040886c001c240c0d42c184400d059043c03032b18450302c506a9004151440503174440140e08080c654400340300c01d00e5a0901c420b800a803c16249a4100441c540c5075010040c0103503d014440c943c0a103500c0c0030f0411044519600103030010130305011742414014086003411000c1450303046100300940200a039000b042d201c85018010b401246c1c0301c0b22040c414271581c440c2e070301071102d4186e05a941000384c607401c00c2c07600242100c44060142c1510510604003062000d481008510f0442c001e210b064003042a00e42425948007082c01d581a140c10485c65240e417414a250103122102500c60982d075144038142c42d0b00f4504103000c504507401c41210040c2c90301c2c0084102c1035000e042141e109580d403902c80e80f203000c214460b00c44105580b445a16290003c07800520b01603020b00540e4050481c0541807030754035690564030507000c880586190b00002013030100110541180541c102407400c0c1785d42c2d60f080a01d0300034042891031100c02c0302030b03103d202c1e2001b49a0085103c240105550011104040f15602c2d02c407 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 632456600 1250 632455350 632455361
    0x20702030601240504060801180902060c010f050919060b0102031612030c14191803150606110307030e01140307030c020c09070c030302131d010807080303070504060f1206060201 78
    0xd003c0d03121480f4055010ba0300c110110b5085880c545d54240141c1d08000b002d60829800c05000741003699980c681100507100d5801800624030b081c00000f8087d1007991805c1c1c1520700c0208614080d80098a84800382c20404e41094001c0741c01445c0040c0c28881c0a00507032851054281440307484174202c25240c104068400c1462112405580510094402003401c0e514141c01002c9410781003014042086914000526005485014070b1b240000203c40244c00340342d25500d400a0b00d00b03c25403174002010105600540005140524080c180110080380c0c1c0340d100c2c001c1d603100404102900c449221103038802c001c12134800ca43d800c9083c0e500d042100c07015006004504041000d8081c82107421414580154a144650032907124011104a01c0d80c0c114021b6019a01c1070454038002000414a0180d0071855107100d6540e01c2c0b80c0072594100701c0824581000f0b513220300d0880d030080081012007540001990120350322400c00802c207858031741c42911012840d10141c0d10080c030f042c000180b02d56054112 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 632457850 1250 632456600 632456639
    0xf03031701060912030c170705011508120c030405060d0c1b03211104090c180f050d0f0f0501020307030e0f0d140d0903020c011d15090301020702030601 67
    0x6244111618198412903010248034850200310011410002a0000300c070800185100380782c4150720360420354941a0904440030000206180800c0340c2e81088001d00c00c5001c00300035040754191243c0350444213540c0c1c04540c800f440d440d03400400d0342c0035501e030200182d0300a000c00030003c1c0e840700c070f09003610380041107074071503281c00900e00c3c400340e1620180310340c0d003940c0c1c0d580c040d07071040c0d10385c5c8114001c03840400d141020005030681d1080305600b0a41c0c60b80281c8050010345a0205440c1d4010200801c0f801800d81c0045080088003000c020a1b40f80d0001c10040b14416101c0081751500340c00e01c0040b903070f8040e0f0042c01c14290800f141c0b0801c401075008501c21201a14100f0440001d42c5a8540d500d5125400304a550300141030a10460301840b18598144a1405954a0005800d205400780d50700c1030000c40141e4408611080c1560300107402865a1003050300d00c16060a003000090100840d1450002d14514001f41c0080329450070740440d441260060300312005943c1d110010581882800b44 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 632459100 1250 632457850 632457857
    0x4030c09200c070618050d1505010b031303030906020906070b090106150c02060d1107060f050f15010e13150e09030310140319030e010f0201020913021e040f0303 71
    0x1c540400341902512452215003004082d4241000019941e01400d4151804281c0740c10b8000950742d507544541d240035034404c4035032084d00100b052a460950b0f01c10381000071040c2d01803081040395030b03500e02500100c0380c051901268250450510400034072032072100720b41080300002d01c081071140c00c502c0c030307802400074200811866942d04500280c0220751400d5030009440e090107180985441c10250609400c20300340080c000c0c060208455495002132011100d51f80c48001085481019108042d401801582010494a0082000b0f103030100c2282842d41030281a007010780168071484c880d0b107140401c164041040c0c5000c0100f801c1008454441c2482e0141d021f030000d208940c0c041300362401902c007440c00710521400c0802c20280d00082d074a0f0f0b0f03030b05482800e03401e804c8000e0214290352914020b4603501d5541040038001050708180c40c030030105580c010001080261a4561b512000d1400b00304016100c1c91358183c0329101c5041803204000034180810081801170701d48803600c088070711946 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 632460350 1250 632459100 632459141
    0x18010e01020c010203070303090203101e0608065a131e06140f0a05060130110703050c070e09030304120309050a030206091213061404030c09 62
    0x180120381e1202e21031400703030040c0c02c103110083c0041d019400a040e1a0720040c01d0314403c00d1000f10321011511444050120440c40580507a000781043c41000301901501300030b004c10745007401c040101c4a603560705903440b0040350000c15110a41c02800720000341c0b401010038a45143d0082d004800b11810710054039004024004110009541d00e030006941d548001845980e40300b551035040e42c410001c50507907482d0740744c0d4683c007800d50020740d03941e110b450940e0f622000d03400c1c652691422140001c1105040c8079141c0c02c4a038940206080700c00303845812500440c06964a4450b8501a0580510164100c0302c0410184200354001d4041c008100c99202164145540d40340c203003000f0301c801d442c0d40c00300e03801c1007001c1030205140c072800c282c520041d828045540a082c0d910245003003042101540142c00031414880498010700c41041c0e00b031640d081541c102a40c5030100001d005182c401d030818081c0f01884c07214619502002d607001035812024a00440d5522441c0002030084441d103502e500d900396 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 632461600 1250 632460350 632460377
    0x140c0a061d1e0703021908030a0c11040509101526061b16020d02090f010e0114060301170c101e0507110d0201030e0d1e110d050d020d021801 62
    0x203980d40650300c00b80c01c000c1030490f1954003480408450804201d049082900f07001c20540b90801c000c00944419a41c0c1c0a800e11603801c1170040c04460719407642c0302e2410b240c14010449000948001d100580c0d0500280724580e90b0f101c140510b000341d014003c128181805030031a4030302c0a03000301002c1418401c1c0c0d019035441100101a01d041c8800f41d181d00b21040c04620005801000401d007800c2c40a40580d41c03d890580004039158022121403140c10038101c01802112500d0041e10b00502d0340b03070010224011140700060322030005001d0409009100d20207480c0c2c0102c00c0040c8404000c1c043c0009250382084800100309820500392030b8003a0b0704035a0ba00c0b01e01442350303046403881c1c1c3e04203a114401d05140400c010790080c4604040e810107031075a13203844449205000300c0d440c50116840d0b035121020031321003210006501d0034084050010445030140042c2010031800600e5015242155440804000040080c0100001080350b1031020401d02103101800c20b030b541030038400741ca0300d070740d01c0544 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 632462850 1250 632461600 632461633
    0x190204121a060306130609050102121914100504020d0615090e01050906010801090c12020a020a1716140f0706030618050106020d03150810051b030106140c0a061d 71
    0x35260102d50f61420498900072441c1b903840002c0d820b01c604c001603e401c204001a410205060381c1301e04d585003951102c4403034910785c0e114154030440b80324807202403032411092032621201a44180c0780107517000a00307500540450360001c0050881803074010035030422500c0080015213a40600101c1d144c0000010450f440c1603c1075511606c0143d661242d242c0c00c102542e000380080318410340501c000082c0b44d5202c1d119030700250484d80015030040ca030143c424103000380217241102c40384c140c0140400c282c0040440103105507070a00c0e00404080401918800749030304d045450728404400c0e0050179804038006526030021130444045c103451001d0700280c40101011241d080c0314140259100d048201402c0b8020340020300c0700115510079921065440c1150342c01d00b07010780c440c20112030b82e60342000601d81e82c1e840500c025540401c40b0038115818207001034051007491410030075144002c81da441d00441c0400050207400d40c40700d401d00101c4092038056a21101181440c0341a009080300300321712858 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 632464100 1250 632462850 632462863
    0xc0312020708120c0c031e010f0e121c0519050601020105060d1101020a080c2803020c010e060d0e0c15090f0f0a0f08070302010e011403190204121a0603 67
    0x10b80324054000c0710400001e01c01c0340d901800d068411809076240d4040d0a0b9014482042006242c8040c054400c0c004c0c03406500b154845030480120302e1520b4482141d450002410b500d2160b116020a9514041c0d8000180f074011403401c1c6091340c50a040c20807034084020700b00c0042040007090144841d449010040e802d940044030101d07000b225124600f00420301070902c109171a001030043c0c4003002e14607103032070b08180d0000c43c0d01ba80c1640151041900c1404580141c227a4100051141e48550100e680080d01c90f0807411480781004640c25424a042c0c0c0c950741102c464032600401001140d28502007e5107810003d5106441042814007044031041210201d9007201402401400c43e480c0305800c100401c08441000358101a11040204440c8140000350002d0035203140104007a07031452000401100c01e11103030504214400040c070b29400c24440c2503980125040000100222138945000f000f401250f001070082d2907160009818404c006004491580c04501c51000310366403502419074980 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 632465350 1250 632464100 632464109
    0xa031104050703091109061c050309030d0903080d050a020d020423040e030a03050a020904050103050a0506130b0a020702040f061d011403030307180302270f0708060f120a0c03120207 80
    0x80403e10300d0079070f51030004642e55107c5d400520300034210482c5801c4000c041e01d00301c400ca41517880007400b00c801d0b180c00c102d050b222003587e05c0c01600e2503042d071f5030340441c50050440c03240110b0b8a40c80800c4a8a4882d01540c0403100c50346e000315111903950141182038030060007500b08068000d5000030711070a260256001c01c103041c000551401d10541030480041100038810700c44c0b0340c1e00303214518680d600c07401801d000354012001090841352505183d030070304401410505040a1038103850300026180380d400c81c1d0280b0243e00043e164003460021030064441c0905d544416494000c0108081c0b101c5a004000b080a0714010219a0303282d1a8884421b0b5080d80a194175a105000180541c0e11820644170070b10100340084040320340e29408148808040e003405500b1414004520800d00140703c0c266501108900c03031403c550421002c041c0589401a00d180c0c02208031180d0b00490b500c5030302500e64040303c05401c07100005410f00b4600075500f03c5000031281d18000140c4084000e00c000b0350740703042d107 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 632466600 1250 632465350 632465363
    0x60f02070f17010b060304060b1503100311010c0507030c06121806020901050c010e0d14090904030f0201091b0501020c0303030403050a0318230c0a0602030919050a03110405070309 79
    0x140c1041c03400000b000c8440c59071503980d920f8090b192459203458000c0c502480c46010f000c103141d802d01040000b6030034290401510740074140300700440050000403110803039400640081d60780b4140e4004880c46001001c0c064211305c00e08030300200700510301611000300c4081c3d984084000485801b01c4082c1d5005046013445100a0400540071840303a41c002e000803035050500318035080c3c40310040c0303095408a007518031580d007100025002c06500300d5418407052141d1400f0034034010300301c0d0020b005410064000b600304464280d41d480041c1c000d52080440030380008a44041301d10000407904066024080c46005024000f40404641000001d8070b004941c9500e07400c0c14210250001c50040025101401c51500e200c007030080031844084044041000e00790703041444040300280280750500507002d0718001c0c0c2d03034094100810350340402500c41d00b8408841502040d505034103414001d41103a0891540001c40d10800801c20114200303400c7e42c00c005480a20903a541c408050301210510940500803 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 632467850 1250 632466600 632466629
    0x908031608090103090c08060723031308250c050406060219051e0105040b06060306010f030e01060e01080a2d02010318120914060c0c09070306051306060f0207 70
    0x1c20078006012010018900010801c0c050344038038840074107a0380a9030198001c0404e0042e86944400e1040844a050481c5202c0202582c8005c5075440000c010355600c0d100607108604221018003111100140080c54000d1481e500740c04803140c16a80404071043c0254840008007820709000708402c440d603e030042c04c40d0078100d80d8000107000322507030304503003900444a241c1041c10904541c404144400400040e880c41c152030817500c3d01c038000d0141c510491007401005902ea9021b5034a03007400046180225486400c5001140500503a4104006440c00c10740041144100003402101e0103029030607101070b0900d0150201d0740a80314a258030b045032280031340720f000341d40240c000d01c8051103114195501d001013074035050911452200040300090080c82c0c00c01c00300d81a0074000d4040d03082101c000f490007601c3c2140070b50752450203400c0c43c050b080e1100090f10a500136402000108400b070503000811403000003610042549001d8000030456030740100c0e0f1298070003d00c0c3d030151005107170710030704 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 632469100 1250 632467850 632467853
    0xd0605150d1b09060f0c02090f1501020106050a0909150612030212070308060906030f0f0d020d02010e150c120106170109050f042a030c0501091a0921030c0a0309080316 74
    0x1403115005c0080e00a00280d0121800182c4510035000d204800c1c00c51500d201e428a81414031080d80400c2841c0e04680c1420301c107100a503146c840e00c01c1220582d005c00181e1296625007000741c1607000c00c0d112080f43c0b8100001030146101d14200d020a40720768241d460040b0800bc404a4a0240100250000f0034000c006951800d00080540d0008401003c9400b4041d401099502e800d0f61070b03018012a80260700c1322190260100202c0484900c540001d000510700c00c443c80c0c0d5161403062a00c1040440314021850b811140c800300c410490a0080005566071140009804513652132415017020070004000180241188141030164008858599840d245c0da12420104905c10204084444800010003215030044e185400154410307182000420710307000000d00303420b81c00c0d03200304020002d400082d40e08202040494a06100c201c622000c41190410228071901501e800d40744988000201494682e4001030310b02022840b0340e60b01040c5584032024a45c072405413a40584c0040c0034000a80b0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 632470350 1250 632469100 632469107
    0x5030103051c1101240501050408190f12020c0f040524061909090501090c140a1809021e18061b030a080a0f020715020d0605150d1b0906 60
    0x991a0290324000a2044103400300f036013120907a0300c0d9403494a41c1c2200c184042d4160031a108002c0c1400d09020381040e18003181d0a849180c3c075040c002c024175005c104c070010801141115400c035604102400340c0801001c2e80030b0f41e110b406242c01440760a94011902031480c00d401894800da030012900c0440507511000b440d0039090003002c440c2d1105050020700c0f22092400d4020000c88181d0356040d680a151031203000488070180c00c070b501814100b0208261040d00007428850700000a048036640380e44071882102c078a00d4002d600980d407080040300003849000c540103030003410444940c9141d664500c400c4c8a41034440c03001c0c1c0c000c1c2c89841958481035840c040c4090001409500c940781c10780144502d040342181d1281d403002c004610004140a03007000e492144514223550f100085160680d503403a1005001c0401c00481c40356500010305241c0c0c40c4240d00110000c0c00045d0904043d0b140000340d045587e0084804051954501801e41814094000503c800e500243d26121651400c090048 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 632471600 1250 632470350 632470393
    0x12180a030e011b021c060e15010b03100b030a06051c02031e0f010c0f170402060306090c090409121407020d081b03270f01080f060a0815060405070503010305 69
    0x60080303800606038400580c5501d501c2170071105e1410804580d943c2140303452000c8880030002d010180d4880070400b00751000740c95425065030743d80c041113030b240e5540d803003094403192198000001c51000031041c0098038100e0b40010342643c1046a4040503407400e9050101e0796480d84402950650160803000940021410f41182a488a0381510b0021024400d000e09641c084500764000800c40f01e485400c60b40d110040111342000c810010540f07013043e80000c0c085020203096240303d0380015001c260301006c03680846900301c101130020b20002415040444000030303201c00040100312089460011180d8a500f05c1e03040c1e55000300981100c000c0350310352210340d4010a15074403c141c900300c40e07402002c4082001e00051250b0b400c0c17440f0100f03581d8441c511003c40b00f0f84030a01803010080422056a044088654000c0450f0413000650350b40d140040c0f8002d12682c06002c0b2070007000c0c0903400481120050911400302590300340701076250725904880030b100c24800600180c0144040361041010200c28 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 632472850 1250 632471600 632471627
    0x1121703062d040b030303041101030b010c02190806090f060c0c0118110a0603061202091f0f030c08120d0504081e030a06050103020f0a0c051212180a030e01 69
    0x340080c510216010103001c400310300c40340c1d60508004074070b0b019900d0310b401000058002500994203604255403051030f81030340901e0003414152144d5a030121a446084146c010741d40003407000080544d552842c80500f1024013424180d07002c2c440002e070085000180070080008018005c0001c0c1e80c620408541300e8000000440445d500c4045100d84004568081100103006130050301d44d245c0c0072405c000c0d074600c407a4481c40905007001c208005441c1000021829290150f6441c030a9550f907951591400d007503000c3e28200c21400740008140c48441e640c0f0a0240c0b817040c044d5070902602c40e513a040e0b8a0411086804410b0070810030990458900d0304280d401c14446d150349814035101e03c1124155960b04118400b20140100c10000e01c11118010030008007002c0c2402c62400404020180c0548180f8140f40300b403090346000340c81004002c05c800c06c2d00c411550416911351601100502c98540c2c1030381d0039110700b280042c550241d0769022072140c0c4103e6158582c5440c4040b0300700190f4000040262 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 632474100 1250 632472850 632472859
    0x4020307081608070503060f0705090d080d1e0e120a020c0a1805060d0b0606070203030903120a02151e1812030105041104080a260d060e0112170306 65
    0x1d14044104030000500e44024844040c041c2407030341c3c0615024095000d02c1c441d030700040034008a241d460710303010b82212041c60025911541c000100d03540b11070a010050040038000740c005075120341c69000d42c079400080001c03813014942c0c118103030054070000341c220707c000e1b001544d41400100480c80108010b01c998012340b82d880303202e040010200c0b050796000079541416000151080c403094410268080801c448014959010f82c40d0310300103440042165001d854009030810a6680401c19030b09a80c0006088410307000703800222527481d401c91107481c40940705040c071240d02403d00790440c44c80f407549c1140f05a003000c501c60090441d4980038000002c00c0140502c664444a410b014071303a8a088004160390790b03545008184070032602e110b0075045c4030241c1404184890080810440601c2c2d8008030b010202188888041494100708503a0004090340056041c10340d604a4005500320b43c800000d0308101c2c0c0e624082e02418200e040002800800005410100a0760b07200266800c268081c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 632475350 1250 632474100 632474113
    0xe0105010c0f120816020d020714010201060e2a0c100c0c050a14160605310f03050706030c02031b0f0f16061704111f110d080618040203 60
    0xb240d000240e0182d06a0500084c15003003046043d6209841682103000144020100000403a20080d100c02d503500501d111034240b80d510054a82c802d401101c050034100200315400c2c2410310a00500c040b50842c51403800c0b0307038030701d1000381d80642ca81a11a0010800c0107007081141000380e4900902d003066400c0f0900c601000d054010a0040001b45106403081c2907081c910110344141c075190005d00c010414014039411018840e290303014040e600308114425900c0300d5103031078414000160346000b42c0c000040300000b00000c0e2070020b141d10b000440c0c0c050802d54882c1c45d01c0e41c500300c0c151103103c0c10711809a4010003071130440540c11000080c001d00010143d828121000c5983ea090140360404059260303c8001c0c00c02000b852108501d0003060700d820070344004e04144031048100380005101038000c040b40c0403c40c03560b41b07511071002c41c00341561544403c00702e0300b007138082c11403c03143c1c00d4148a4854102030a0071a8041c3c2805070107204018051504004480200407003010000c10880c0c25010b2031 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 632476600 1250 632475350 632475353
    0x11060f04090509150114130e030c03070c0504062102030a12031406030a020a0b030a02040302060a0305070f140306130e061312140306010503091606090906050a0e0105010c0f 76
    0x140050000340488041c00304403814120010b40c80c20001280442d00d054003600100441070b6200b03030700c041d50072003914800c800210701841c0f14024a8944a86e03417550100286241c0c4e40f0002100821000744600401c4039072036200c10622040b40c1c1c141c050b101242810b95603422001e011481c50030350452006084844600389a510301000303221010403680426180d05d0404524580c0248407644010203500a00f00c0e0241a000580144042d108a00c0300309400000700e6408081ca0f01214051078026000136660256090020001e0000f210410300082c008011400454400d00e1b4001500d03828078400760450b124101040b0000c1039459001c00c0442e903500030480c040e04103008203841103c0c2c40c2d0220100100ba400d110b404080c143c00d500c0100140c81e6801203c0142c440c00390781d0020428a03001d91207a82c0da00640d45086919182005680e1201d440081d501c1c2e809500c80080c0c8107600002d202140d5640144040800b880c01920360500d80c0100612095219600c40010303280564204441c0f101c4a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 632477850 1250 632476600 632476627
    0x41805010f0e0d020604085d090c010e0303040905130606170304030605180a050c032512020d230105160e010809010e1b190509041106 59
    0x819a0110142e25014414114031060058907001403807400680700919013076841140d28400d03035800768003180302c100c00c1c940103412011141007402110b01c0602c0c80301140c0c0d044010307010f25102d80b4040c41d50001c0a9281900c681060190040704680000c102c40e160000065a0300b84280a82c80d805100c28400000c620300c0038000e4500030070305c0d11018003070300f0350b641007950507645c15410405031002a1007e083e560386000003100c04a0b40c02c6071001810703072210094020f03211381c100311455046c80f444607440c0911002280e6110405011801c440081c1040c80c080351030f11081190b82c203c84428100e00b00082c0c5c10380020920051300c010016903400b0712035940c0501403100044c00480c3e1540c110b800c4102d44800744a8980c102d40044200841104034820040c0020981100701d07040082d5480400e40d694001d40046410341c0315002601d6260380b00801601030070b00e8180c05148100c0201100d4000d03c0c40440e5444d051751409170500084da540e076144c144840d1140c020050b080742d010005010240304 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 632479100 1250 632477850 632477861
    0x718050a08030d0f11042705040b01030b0c0405060d020309150702120d1104060c29270d180b070302060708180109030e0405060a06200c120c011205130204180501 71
    0x2848051401c211f040441d2050982e5a203c590706040d4541418403021600344094141140d51203514080d041c0e84251480c01d0300d0040e03501040d08244045400042c0340302c0781d000345100f560500100c440c41000410010000030303007980c1a101603004103582d6030807954050b0017898000c50114010400c860340c0020032100e41e000c0d07480400020381c4454143c04210044c031403040b01c0d070031941d45500c0540325140c500020000c040c2420320142102c10038090251030400c10801c42022200130b540c01c04102030005003102150404100c400342a02c640416001c1210050700c143c26055401000b296641003415070f000c82c1e0181038002c10341c0b6001c50313050b181c40c004d00030a24201d11a5440d0319000d00c1e0001400141c03030024000c240302e2400c650041c000158010030305243c0c03468080c01e802038003440240c003d0a000426820340c0d002082d00202d440000000240d1080c5140c0aa1f120f4110f603103a070303080c841114020780f4515061030502c20858094640780d0410b0361010b25200b116500c09107142d81d021f08441 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 632480350 1250 632479100 632479109
    0x17030c07030807020d1b0201020c040e0705181302100219060204172a0604090e060106020c030a0b040809132a050a05030402130e03030718050a08030d0f1104 69
    0x2585030416922480080d004a160300003030025080041000d441d81c0c01d00448641c3c04078941c0141010341e0710070040000c800102130010000000e964a615450303e10320300916002d074031200030b605001c00c40c08550a10803110354807014511400c5508214510b16141d90200462180d004031326180702c0030034089060700c0d20540300180d45500c3c002c08605032400c2c1041684d41500300070024880143c80702010402c044001042085001c0307010002611030060790401700010313161072003a0491990010b2918140c0303c42d03400706c48213841c4000405644030491400100840303014404035001a12500103842000c0c0300415140000c0c1804c102c100c1196600915100e00b910810284044824041c2c51038034030210768944a80303481c424400c050501d210180c402406200d2041e4100d070101020f6200d820043c0b01d8405507a8ad03818007035001040e8483c04110032860b0701c10398000007402e282802c50b8030f0889111101071414890f03074100c1540200303c02c0070324805444d00c840105940e803030120010b0010f003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 632481600 1250 632480350 632480371
    0x1c08070206031f470d05010905010b070206190c020607031e0201061a0306061e07060b040b10030207020a030210170a11091512011d0f0c161703 63
    0x109041c80c0710007403080c6941c840f04601880c0e007030f141c22030300b409586403404000c03142401c0e50281c09201c1d16240400084281501d8540100c0c00f10317001d0113036402590484031001014403003070341ca0340b0128190b8410750200030f600840403c0301ea047d200c0c140100114001160500d0402400140c0104401e81d2115908034002501c5030031806802c0c00203807002c1c3c000c6607584001c010300c50800183c26034409407000d601c4100f10020002a4450303840381c041f120f8800400c5084401d1001c60130420a1035040454220351490800d16444650b00306407280302981a8000c1002c90f40c8aa4074606034020351040350181c2e04080503000c0172015803501540d001c250082e980d51000b08000302d620007098050f016000f0b03550b00727082c0303907110340c0f00c0202c2c400b40c80b904d0900310f41c14420350426501c3d0b100248030b0038a0100790f0000351400001c14402c40856100310f091901b85070400d60f034840503c881b640000311000d0446050620040561460355000700b00007601c1204640705c1ca00325a4a840c00c1a082102c2034007a9 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 632482850 1250 632481600 632481631
    0x403060603120c030806121614150a0203030f06011101050c0a120b030c0f010921120809070b1b070b0a1b0b060411090603040f0b0105010e1c0807020603 67
    0x2084402961400c1c82c40c501d10b00000358021542c0c004016a0026000e13500c1000020110f00f400c660a0200c0c0b2607000800f4501c03031055684880c60350380b502c0100304607440b070951310f00803402150658080b1a5010101d41c00b8510b15034514400b001440c4010b00440d04003c00350662844c1c00b5002d200302800380c403a0300d56490311400f141400610b210612040300704071900f8400d06000a0701c0008007001c13103007021a91038125a8103c401207a06110603400664a2200c18480100c540d8980300540c220600650001c00c41004101041c2c600ca00b098030b50040544c4070420030090540302401900d800c40c1406210701032011000701103440c0c20b400340c010b450070b510005500040c55400440700b010030140840d01340030442468940c0008440c00605842c000d68550040000c81c454440c1102c1c2d88000c010005610f03801d2504140343c0e140a841c0c4212240542400007180540c010018000754010040503080440d0005000c4402d80b5903202c02203400c520184000001603032184003561041302d03442c902004 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 632484100 1250 632482850 632482853
    0xe071e0e0901050a0506120405190605040302122505031c0614040605100e04020904110901020d020304080d1116170c01030618021305060c0d02060c0a021c0c080403060603 75
    0x901c1060344400d00c02d011041040200c2e0b154102628404141c540c00d071421740c3d80740c1c280315041601c108006007185510003d00400c0100940c403040c0079034080c2e0708807144c85035080211a071600c904450790650020141801c01016000d00c103040503248980280c90070007182c094240a40303522412090010303900d0354814007826010341e2000c0004082104c003407244515000124070300c422850203890401902d00b801c007190b51500e80440321900d0000d0020030408209008074a400d8001c80f200d0384c01401030041c00911144000107550986001e0310180c00d002001200a4442c0380f680006120a4040ca450110b0100350201c000c500405030080c2010142c00501d00320742c10100c0c40946030303041c1482c016050021344c1e508680a013081d501c1c1e40005907502070303010305000441c03d55400f20342d01620028265168810100798881000095005c03104540c0b640d0046050f28081c03000d5407001a8040c10f0007800c4041134a061038204401410301078580815501c40c44001d03400ba0700203450785a00c0c0d000420 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 632485350 1250 632484100 632484109
    0xa090608060d0b0c030a11070b041e031d0d060e07170f060f060418060e0d03050103020d170c0d030213080303060a091112090a030206091203010e071e0e 67
    0xd5000d441122a02e90005841e40e683c4071403900503000000800010001480f814071a0b4817490912012808094549105281c0300c2c61300482240c040b14804040a08002a040b90340e00003200168543c4408140d00c5840049480960880500b45e034440031140c214004200b00c5e1040b400800c1c40c030703805813895a0801d00c8200c0b42c800960740503096035010100c24908a000400c2c442e800c004415070012054035402c00040140c10044804907100084000060400580740d001e45541101e09040d1100301d17520500c02d808403882403102a4110b82c05a030120000b840c0010b8074541d04801442d20790400c031100d11003a15101c410b03502e010100364005041c50003840c0d0750701007500819564008510f1480c049001c100503803802d2140c075260544660011200440076025075411155070070003101c0600c1c1400041c3c3d55940d0031101980035000382d10100b0460341c80420560b003019621101d9601d10b034645106030713841c0c01c2e0003030200c42000550351440d030200b040c200d4800d0595195a585a00c8148a00c0401 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 632486600 1250 632485350 632485367
    0x4050d0f021c0f09030b0709030308160219060e0d260106050d2d20040806040b040611030406150e01060c11060d0612030905040908040522020a0906 65
    0xd000c0d94407007032420228011a480c20100300001e450f12a00c58189640d0560b600071640d00003c100e030f80041d040100b496441031010741186d010b690b50039400d0702c42c074200110300c00010f2510001600840f1991001060414287c0c50703e9114610004141d80306400c0c5600300ba803410700a9000492501c00c1a40300c0700700c195100e15200e50403418070300c5549403443c068858420400c60240c440d031503404407029a080b16842c1d4840c4403541c42c4041d40d51580c840010024180e084503110540b95200d080c44500208605490a5a00040092601c0d855a0f00d8503c1112070042c4210790380b03501e801005541c80c003500041c3d80254465800803441004071480c1000924407604164951692000104203241d0710501c101c581c2500041c000d528aa00c01300403030080e100d0f0102c003038145820030200042c00352184814244a6000e60341e0b050301e5544034400c00c0251031442d031014202ca501031006100c0351402d5405140582215010703c4002d14001d2900020f0360818400100803503e58035041040301e8110121 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 632487850 1250 632486600 632486627
    0x302060103030f1b1b0e010b091207050312180618042a0c030203160f1a010518070e100e040b15041e090e011b0c050606130902060304050d 61
    0x4d070020b64600c9601c0500102666001d811031420032540e0314a4110040c2c3c41002d0010307800211210b40c0c40342c1c50380e00b1a900219005000d1201c2201031240c020010030a0002e80e0341c000d000d40b10301d11141e08505843d802c411400c5404c00079240001050390b460700000c03e04900780d0000901050807090400040300d41098401c0114184807801103444116001c1190100c4014101260614810f080403403450088540040700c2c03a4217100304c0000c0c060b0306540c2d458914800d0714085014440c011411112100a1080640049c10201200a401040c010840d0f00915500c1c1407200c10280070300103041150a005542e02181d460311080c0b005e0309050051392201102035940180508042d5000101131003288100401b030055410241c60001c2c0c0e01c0c01e032200401d0004418004103501d501514020a0521070460b106110005618800c9001d20445060a03030040c0103020301d640c84609001c071022002c81502220b50b99018404010f0780c2e41030240d40a280501c000349021034480070060f1149120000 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 632489100 1250 632487850 632487857
    0x8030c010c0306121a0c07060908040305060c0f0a0f05070b130c0f06080c0702030a05060106080702060612100b06160609020405130c0303030c12020a0f030b0f0d060515030a0302060103030f 83
    0x1030101240041c5228005940c5c4030300700043c075a4820843c46081d008528000b40040e007415002d400b405001409032003524040c00540b099034440300700c8244184102030316003404490900015605600803440d8001c414900e06040f40380c0501592510840002200c00d42c104484014400e0188446a5048006401524070202929050440103841d030340004121310480300340095840219101441020356041e4080f04848503940c42e203002610720703002202d4a00c014420078000540920b0710300c0709500243c5140000d840180c03900e00a040140600c2e1807016081402040101c4151416a00c103070b6400303014400020b41120281304100540f00c0c09402407080044c03518103880812016084802125414200010780d8941c0e11000c1e144203041c650102140c40c40450030711100303074101010545222483e9020031580840e607080080f5a150203650f1030304a880d500907003000030516030200b50814030303005624500302c0030080013a2612080c3c240c11401a000280104201a048034849821540505 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 632490350 1250 632489100 632489129
    0x12031e0c090e0c13182003010302090702011e020405010e090402010801210503070f051e0601140a0f03110a0e090c061b0708281707030908030c010c0306 67
    0x181aa07000d8000d500d12603410401059803141d80320116401521308440422900f40e958001d81401c203540b442401c0307642d0600d901c40f13000f00459900b1102141e40c11084900b16401d507000d1040b05400141980250743d0303112613620002143c4200d460100c08441800b5070317074905241c001018000d51100d540c4c0110b1161042c800142e800c0204c540c19a80405800da10004488070791401c220070402000c0e04a001c00209481403100140712541518014012071f11800240a907a81c075a40c00c0c98400c83c6203030003101c0180852070901103e074413240d1006140d40e110903103954840341030b48440d9000322020082500c2801150030242c403110300030304286200498501c3d0621540d0740b41d0030101c450078454840001c100c580420790122000094904030101d890b295250b0300125503401c040d0741610440da4503554024180d031119040c0c80e0605500003082242c0c0e4541050b84c08543c0c002c41c0781141400075002e00401c0c801c00401c0507001952172040080380640c4000c801400b120001e8011801884482 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 632491600 1250 632490350 632490371
    0x70807081005061c032601031202032a0708070e04050c030604050a020105030a020d020c0a02120f0a020f0d02060706020d15030803040f0204021306020606040c111c0c12031e 76
    0x100041464110541d044d4566140c8900d0202d4400044018100400d0b40818508105402c102c6816059900c0b44e0103900141c803001c8020790b41c5c1c0c0180740f80500360034801c418107019000721541e01800c800c0720350100e42c1510340303070701c2300300e05240702600f142100821490030442444810880c4001c20311094019010070305140d110a51290402840a414003000001007401840f19030b045400100c42c0c1042151034640c07883c0c1d442e40b1aa80340c81c00ba4800e1511000c80f90342440c000c9002006103261400410707110038036509100381d0030101221940c1c05002035403034001603240d0000a11580c0e01c40c540040e035841502c0001804c68030011011900c80c0500c42007030001a181800b00c94015402ca2100078104401e803001030003a00c220613224011005d1120002400380d000542c650244500f10f509200703640c14564212204807000b1414041caa0044440b0340000c442d008a21b0082201440c00010081103501d60310141e06040c003402c0e00084d59101400c5a40005800c0007555405482040c040603004 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 632492850 1250 632491600 632491609
    0xa0305071e0e160908010c050909090a02090403020607081e041b1a04051804080417030d0204120b0f2502031908010302090901110a050906070507080708100506 70
    0x268010403511103540c0c81c0141103192040c00300300041840280000a0745040540803c0c1180700b000700101060203003602080d8040d042c00b8199003151550384076030822000404001c840b04000d41645d4880c060b0140103405612070501140c0701c1e40c0290014031140c103007108010595100244110b041600800121018903048407071f15070020340013619118050614105000e680d21f090b03000d0744c150110008240702149445018000b20344084840c4500040e58424040c40711504403002840c26100704401c1c44443c1d440300d000100200d110088a09107800503c81074100e0b80107802c41640a8000d4102c4010020b012082e69440600090000360908191a80004600d101c0c43d12595440c6540cc01400c010f100b08107540c4188030516501100f07000280c0b0181c490311080c041603004091040008090760700500521040003915907419281510544e03040714160803090040394003040401c80500410000c025140140c4201000b50005c0c918040351b440c6450084d0f5110f0424a080a0400c8003c0d0344 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 632494100 1250 632492850 632492863
    0x3060605121807060801090b03060112020607050307080f130603020c0d080702030708040f0501260406090305090910050907030903081611030309060a060e040b070c0c08011d07050a0305 81
    0x924900c40c41c20351604120414040e4080002c1a80e6205100000603d15801040581220140a0701704080c6802070140350b15510240100480444a440b00d030005090403001004064042c00980b402e000702ca580c2c0c22819400310441d98070641c80030a118250340014410240140094102145010b240510090301c68030418401d50600080c40c0000307041900034400c07100555032100c0e5041d03440c2d886010b05088102c05001c2d6500060798910032042e1601210309101451003485502456a680e80d40e07014050029010210100b01051040b60402d860f08104180902d403440c01b0503000783d00b0b1400380000618010100000c041c100201200032a4101e0301464120369460200300f90a8034104058500020403004000503100010400001e090086401d03405002c4181d8248002e9540310760f203411400050310090030b46441d10000c100707054001d00c40c03069464840c0d8401010169244500c500315012044103030301c0b1043c2241c404c1c0e21140140191b4000c3e105c21148900305032304549031140d8949 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 632495350 1250 632494100 632494117
    0x2030f0f040203191505010b0408030f0904061710051f0e090f07030308070801050904110f1201020a27060c03080a0f09030c03080f25090f0b03040b0703060605 70
    0x4a80001040c25920141300311a5269a20f096000c80c0414030303e0600b05084844400105040c580400481d030071030b049088508550b2900010350515000e003181d20102d0b44444070950740260b5450b400a000c1d0b12080c0414603840011002c2c00490641482d4081900d500800c5600610240380469080d0b410152652013a158601d9000c0d40315500c0610b02c500d08000200c41e0030452150782030000415501c0048544030343d0103551240101e9a07140d061101084055400070b0038500401940c8009081000f40c0351840000206440304031098862002d0172a44501b0340300000901d05050200720740704915403180700d5020182c001c6070803850800010161005000d00504000c081000304809008076008441d036048003140c01c00a80340a0f02d4050010f074414202280801c070100000354442c0a9010454410f1090703010744940ac80590a00c1c460001c0b21400400034400b849030007003522080c1094400140941c660490303078906050400790301c071580040c0744c0400c050500d00c050107055400810380c4d01d030a = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 632496600 1250 632495350 632495371
    0x101107062a020a120f020d06020c070b03060d0f0f1502090f031c03051b0c0705010f0206040b0c0a021f0507030608070f0303050904020904020309060a06050102070305150702031204050d020c0402030f 87
    0xa1811700e07180c240e410000101960080101c000f81c01844099030040010110720011940801d603500b00c80c002501048550715130000380c05100d2400303c0c01800c84020210310982085002c044030303031b80b000c0d04034012811400c1d03001d038042612000e41c280000d01c141c4510b0b04800814900c0e9140c00c10601e0308140301e040a04040d143d0010640c403400802e001c06440c4440c80065841e62051203410355120003503c1100d0000b0951031000c111140003040d102d01468200c207191200d5501e85c07888078000da000302c0c031020861003101c51001c0103441c11b00003c51a09c62034000031402d420300010080c2036801030741200c2180d420440c82000204281c021483c1280c1d80360400544504130180000c000340140c000c071a0300326000108104030000301080c0d443c40303440d1862701040010380700c0313004998a142d2400000c3c0107900207403141880c0c121110310180c0c0701030984112490803c0b2a0b123200300d001400c0e07078100c9441d0300500c03101d41c1c0310380c0505ca041240d01e030030342c3c0860941c0781c07000740001c64450240461102c1c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 632497850 1250 632496600 632496629
    0x18010801060803070f060b0409080d09030e0108040f030c14070303030902030c0603091b0a090507030b090121171b0601060f0e0112020703021614030606040c0e101107062a020a 77
    0x70ba4236107070440d81c00c05030010443d90b1680307003420f07030180506003607501280090b042c0c4011001070340c080c0502f940500d40001c4640c245d2031060350b05407001258a941070310049010504400d64a20401503000610700ca0ba501090322601c610506180c6680d001030300d80310350700520401c41030000c0090000e0314002007100c0d5000c0b9410752804103030105c416800418a507030400040100c540d0705600041c0440005a40c80115a1f0384c49195241c20841a440c00d0424601401c401001c035003092034046050b2410b4821610300703001c0701c2403408010440140212940c1221004002c4c05030000c0710340c166681242480800319940d0070009203c42c000005900c0540d602090681c00d0520800007041c4061200300c0042000341c5a844205118000002c9280301e80b003100001110740c00d240c05402c880c2281500d440d030304c00c03403900100242a0303954000201001200c0c0c0341201d01981c00c1103c41c00414040d1602ca00d10001441c41e50191812a440300c8010107504450500684840d0010021101d000910105 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 632499100 1250 632497850 632497871
    0x12070f170405040516180b19050906030106020f0d021c050325030f0e0313050409022403062b02060f22050301061508010308031518010801060803070f06 67
    0x1940d008a81001e41c00615050800640c0c4194440b500c60080540d16408074440062403d80324500c113a0061824440c414007043d401510694023511554002d17080c954180f55140002c0303030030f44d0000da0020005920070981d1810300d00d030031f00506624a00d14400340203442c50035454080085422820901004400000255038240c00390003204034a1440c643d42500306803811b4002c014054201c071a40225242c9010703443d0300b40e000800c440e11104020780340001c01d803074141004010b0094003020390300401000100d0240782d00180120000d0380740c000c1111349a080030802c0c820314102e040706007150540c40f01414407000c0040110710304555411a401d80d914400c500c0900c17564003d0200000d515007052810307102840181c181e02c020307a10160002c12081e03540d83e84064100c40d480383c0e280c0c0814822070050000c0740c1c08d94021940494080d280a80704c40c40000840c0020381144c0042d031040c60018014019040280103000060807034400448c01d1070900e17118074060074103000c0018465503482e9501c01c07 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 632500350 1250 632499100 632499143
    0x61801081f090b04051c03290103140106050304170a0c0605151c1a06060301090e0a020604060c02181501050c0a0b1311060304170703020c12070812070f 67
    0x207502030f60084122042c1d080034680141e607104028072021403a00003251416a0310302c80c1c0b080c0c1c0f06504403601d510b6580d40c41c0300740c0380c504109801c100f01d04268956035000c803080c0c2c0303d9800c2402000300f039482d1a0780b8605410541912502814a50030f83e810070085000e0090788440b0b0310041c241c021a0010325500ca00f04a48003000411990580015001400034401680311b5403601c42540964030100c05000e0303601200210010483d006580b000781480103010140b50307a4080c8400032034050441c1d40c0022940c0000f4000c2d0426441940050100d942180c2103050091303d50114459809003486242401d00c0d98009081180c6d405904001000c40e2101051500f04840b00f8401e03040014002c06060102c2c0e950f42040c440041070324485d40803d031104050404508481c0304941003606021203020660360500540c0c041c1509608503c07030b00e44003119650311601c0c003651044420009081e118030b80b928440c180340085c1008110f8210900991001c00c856100d0700d22050b5004083d941c4211051030081c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 632501600 1250 632500350 632500361
    0xe0a020a1808030405031006050a0303050d0f1a2814130609090201020f12031b1c021909051806010203070609051b090721020403020414061801081f 65
    0x501c01481214000034400008001801a6401542994505d5032042c10000948000d03100e8250400f2204104001092003113005d0100c1c900c01400c00716100340300d4501d1505642e23504550340010403044050142520f88001a00c1b424010a045100d03014803008034100e8810051085840c001d2111043c04415550414030300310700210b20208111103503c56041c10010034020904030f002d40b1070a600c1c8000700c60005881040c0401c4401c8551441d56400e1559111780e01c080006a0003002c2804a43c4440c0c4200051600c0310301403c4005840d01c0100a610728120444502ca505104c00c001c000d1015813645500e8081c0b1040c0a45806103546070140100d25600c2004c00c064151450302c04c0074010002d000c0350406075210f03628840c0b08440d44a0080104c2a40141d6002003c00c0d03145034040565407003079801c81000c045002c00141031507600d802003026036098040070700d100c18000c01081076501c1c052610061054404884074410740c10281d8040d03503203020915102d0703102d210748003943d403030301d46078209 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 632502850 1250 632501600 632501627
    0xc100504030b09030d060b03041e080702030a1b0f05130b030c03030f0405030c060a080f101d1b1309020d06030c031401110310030b100504140912040e0a020a 69
    0x406402e4a01100744a8403504000c04101c0c807603041076400615200e042c0300380da000c7c1f900b020f0303180c03290040800b00c50485503c41000300da400a05011050140e5402e00c114920203000d0b60300041c0304513049260f8041510700d9000900344d20010403007807029407200b00d2482d10000c0004c200044940208001a15140501182c0c56052000042207002240c01c00301074421101c007a0100d894241445007040a54051980d010f00010380741c0e40000c030400c100915864002180b0000d9007282a110784050b84d085195400780704140148034203001410500d80030b200c04101c1159541410030141a00c0511403000a03c26039003420b80200d00110203903600c0d84038500550b40030788000051a513074907120b28480d5004a40340700d29442c0c90380030036041d15420201d80c440c4203400c402f0a44942180d507a06070200c0d0140403003042504001021960707807198895403400380c0700d0604090641c03418030683d0340b4000030103e00710080710061104224012840c014a6042030b041000540c407601c04446c220b5078034128021 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 632504100 1250 632502850 632502863
    0xa150608180d23070b07120b03100b01090f0e06060d06050907030b04140402011b08040506121b040305070e0a09050d1d0a030f030e03031b011d010c020c10050403 71
    0x6a4100c02d4211079004410b5011400f03030006804284041021805424030142c03a01d900400060340080c8109030f000500d0305103600005080c0b038520042441c105000b40864003c60351040908607035a0054001d030028800c001001311020300f4610140182c4001611a901640000c40e02c843c02509a4103c2e1010340740280410040e07103449000200903101c86d107151401103103004001e40314018403072881c910460701038568a90000c41031a0f00d0000c7c802c219401d4a20407400d001c042040d80c0e54074014800380d0005d00d9a01080d003010203940b00c904142076100d010662041004000141000c900c4070200c908224100a050740c584920340e0140103507000042950041e240030481950300040f20100f210417440c0c8008120f00c8a17002d01014846038000500048850282003002078824a00002040b10180c02c2e6401d00e102d1043d904590803205400c100c4d6a51107101400000d40c0103102c1880c41d802000007480884185c500194a641090740c8160186d501d100b801c1070414051411200250b03407012 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 632505350 1250 632504100 632504113
    0x60703020304120f0314120114060702030a060906060e250e181503012c160e040506060d020f041a0604140909010605060a08060415090e060a15060818 66
    0xc4c00c98608411100c007200421000f0300303c00f80f0703501d156040da03016100301101003401c2e074203141c88089070300d00e03100096034011005c208038070040c2ca0620800c0034a511400010501942601d40784064400d5604182000c20400c010850045050240c0114104400c0485101c044400d80d0484090459121607500f00969a0340c40208108080d0704501c580d4060361702e0900606100c1c04c0509076042c131101c140d90306001c840d01341902030382059107000100c1c180084030307009000024601c00d4a00c941d404102e083d0741c0710003040305100045c004164407420433502c0700950348540d80002c08105244442a019903547d1000199041d4810014003441400500c11601d46503a41700c032000840320810100d000d0241c09010a0001005000750f1042c2c80c8014140750600c0c501c003504a03081c400061550764001d80399800c0c2c070340303907005203c803a03000e4025000003103060105444418900318001d84200740d420301d0418441c2c0000c070051714907010313159180703000c022980350514a000214903240c6c5920301405500c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 632506600 1250 632505350 632505353
    0xc030c0b070201030e0c061c0b150a08010f0b0403060506031e0a060e030702030a14012004050102010b011106070c141501060906020a0312091505040c1406031506070302030412 77
    0x380040c00115100340d809210741101d84a140391104040c120064000000b40700307000103042e144003c2120904605400034401020305e0000b0200707600310840050403100001d8403440030f41d028003150b014000c007020002a05280a41444241c4654800030704555551b20204550380c1c1c041c0101c8090b80d00c00c80480b000707401e15103a89600c82100c80170440b10310f0314080c2240d01c00c0c8004000c3e1513030700303070001c016204000e600c2d280c030036000380303441100080ba550712a1100b020a42c10844d040754805088256074489051400280c21541010460340c1488403075034094000b102d0014100703602c0405440c3c001400d0703d1901c1c1c420303e80c81500190310001d0190b941426240b890101000c0e04880c03070741d035810401543d01c98040c1d8440c0fa020034054000790501010030494500c0d03030481c03d0054031038144201c852100c051030038200d03482550122041070f000c01d003c0001d010420040c1c0c9144008440c403a2a41c100701c2180c42c00000d020070054010900400c2c100d0615009200391001406244201e4502481a = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 632507850 1250 632506600 632506619
    0x712050903070e090d0305101d0a0b04051306020901020307170d050c0a05090108061309030e040b03010e030d3620210f010e030c0c0102150f040c030c 66
    0x10460340d0301a200da84800228032038800302c0c0d140901c00010144c010650120001c401a01c401041d5106640c0c0c9240005242c03071076140410411600340b10780c4442070a0019488041e11501c124072480386040005108a0b13010000222041951050780182e9444800006038114001c004000e000000340303c818540d042000b1000300100b036460711082183c1d560344800402240540c0420500044082c000328480f540500120b940000c2c1c0103241980e109c0c0c0440420054400046040300010326100005015017014040c4c0c55101004070000c1c80328825401000d6660301800d5004c002050f140c420a1a400c8401031462910401003101450585103c01e0b846500902000d0102d031100c0d617000c800b082c0c02480d2040390114580c0100120f17501606044407084009070307031388070013098015420f04158602091107282d01c2580030708040e646804000c41040c0c140002490740c5415500000350a201101000800c1a071003440c01180c644140ca490400c2004000f20340c200920b04440c1c02c00c007042c04020f = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 632509100 1250 632507850 632507857
    0xb0307090b09070807091521020d0507020c011202030a0209100f140306090f06030c042d0e030f1606090305040302041b020601090b13060608040309080f120d02071205 73
    0x101642ca0300003d40303c160b001c941d1300701d08032140800565002070500002e8809411110080000c0c80c140c0413a544800c0031024030b4510855540100b6030026400c0b5021005008140c0d0244860015220500e1a800040c00046201212585503680000080d006851703e5040e50540d2b900034108a4162030611006810b154410f141d01000c00c5074680d9081011580c070341164031070040900f0303201c0ca5031114091041c0b4040b0240101c4e0b03042c051030f0b06c110b585840e01d00c11450480c0c416543c02c440d80808070141d83e240308a000319000c2690074409030b521441d40000494250710305c41d00c09107560316a200302136080098403a9000340024104103a40b410715910001030000e0f039000321800c100700710080314844003c04007114882c015070010b5004109651242d80004035004024041d603d01840849600d81290f00b1900058041040c240900c0140f40d030017a4144040c040c49001010205440900301d0782e10ba1741c5e140b265002410010f6454581d0260750103549030b00d548104c0e10707902d81c02c1c1c400c0b01420a80 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 632510350 1250 632509100 632509121
    0x310030302070f0602120a021009120306060206060603060f03030d0c171602060115120f0c020c060c06040b0423010b13060b07153201060e060a030c030b030709 70
    0x8906803002c503600f48101401412a00590010640d0403440d81130041c56412984c104030070b50048065890600301d5030302404d00c00c00e1040704418250b09498401800312003071038001004540c01141081102d4507107004403a0445821104482c2c10390070480042e20710b101d600d404114450512400280d410313044582e0040004a409030b00700f40ba0354018180c124880a00b0400c001a4040030040004585500e0780d108a4101850600441d210f0041c00d4020755050040c40781e6003d03900d000c0c400d821a8184507951540800b203c401d441c0c00c00300710102da9104400b920103440100f0b00c0300403071b040002c42c0340d0070100d28a54100c5980052801007041d402800300f14502d9005011988824850002c6c84c8560303802e403a94006903600f0101c0350344a14400e801c0c010700352304112b541c40c01808017800e1310040c3e0744a600035000180c90301482545402c503c107101a0b01c03a50610010041c0c103041d50f5107074820340d00e1418003884d0010364030044050460142c50040003013900b501603401c009c101c0492a420810020 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 632511600 1250 632510350 632510353
    0xd06060219150f0609020a02030408060a180b07030f050403030912080106050a0806040e0a0b0a1104050603040209091e0f12090105190c0b01170c040c050f0d09080310030302 76
    0x4100c950035054081c00401401007040542c00d111200940c841d902c0501c680e092200001640c07500c45071040d00b240e028a402d0800750340003041c00c002008007004407070b80c000c400000c1400700001c1c6020981080f01d14500042401c00b5910000315013030b10a6011002080d0107000a00882c01c0905014009203081c0d403003581d40c1059084502c540c0c03401220068100d49083d40ca007482c1420b003410890354048007814246d03125031225070000c03000303404000908141e406440301c100ca60401d080c2a50403078640700020084a4402d010402003541c604069a0303001c0d8054804040f1680c80044080c00c00c00301101040d000001803801c4203080900103005800d00301782c1d904440c10721740c500c903400788a4001c2000c0c560010310100042150003292030680b0130a0f40712401c040202400d42d544104221109030001048039004604025000c0020000d10b46000c07003d50b003c1250810800c0001d00900c66000030340d041d000005a04007d21000b584201c0540d50082080741e01c030b00f090030181e064080d0a11041c2d005 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 632512850 1250 632511600 632511613
    0x6080c0415171501090e0d09051c140d030501330e1807031e0c0c0b0615040801050a050609220305090d03030b0427060e0c060d060602 59
    0x1142454400d903900080e61516201d4418600581c041039120401407020980c066424164860141c40c07000e82c0c003908103141d0108521402c01c841d54941001054103500300010007200700724589807860002038141c00e1440124011210303003428941c122404100c4030b05c0c0c1c890144480111541a8041d6041c0d51000c1c006480295106900411a00c0c01c81d10020122000e202b41d2109680202540d400300f0300090111080740190141030b9500d0781c4103d03080c0002c41d84803031800d210701a0b00074080c0e03a030100d2810f0800000c800035000600b41e805001005242c0d25440c80881c8059498402c41d164910190460755500c40d16100e105003e0072090302c19845240c01c040100d00300745002c1c0350240c81080340302000c40300d80d070124102c0504617000f80c4040d418054100003003105912600d000c000c003c2c0c06510082101c814210622045403a1402881d00c4802c80250700058040b82003080452a0b030070150204942c28607034901405c00208000c0b459001c0c00000c0c039440d4803c81d641042c1c00300c40079502a541d0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 632514100 1250 632512850 632512873
    0x9200a0c0c090212010b0a0c1407080607050415080916030f0c090902010c0f020d02041b021006050d1401020c0a0308010e0609062b02060d020d0e01180f06110301090608 74
    0x42e0300903881d82c4444c038050350005001400c0c07a1005014011a07606c1c021101450b40e4075100807103c9140f110881c0b0340c200c082c0921001c0d10401410340c124105103003851900b8a00803060000c040d08a14600411032014045011400108400301d007020f85907280682056813854102030b59501802c084580740314004000600307034030510402848a806031103160b0a40195a906251445052005ca07031018461089201688403072282c521000395803258100700c01c403005006440c103200444014201405c1040c1030209482d03201c1d000e000c03c1e50280c0c2415006991180260281c0902c4607103a00500ca445560740505500810a0f8101c80d07032004240f586445100a0100301c0340b044411640018900507114803520341140095003113850700039020100348841d03000035600c1d070102c0044000300d50081800c07511000d00e44248001c0d2115800208501d9451044c04d001c001600350010340022801c1c3c41d0314050168a40204044903000030403a80c1c0c035a10340344098020485402281120700c1004100708 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 632515350 1250 632514100 632514119
    0x60e01180b040612092405090703020a0501050a022b0f03090c0e1510030e01140f13050f010c03020417030306010c14010b0d2d080409200a0c0c 63
    0x405440109000702c2c035080c201042507680c2c0b046841d10380845a51485da00000c240351800003007044402400010030308480c103900781e041d590042e00260680e0840308040005076117030481141140e40a0070816141c0e80780745416414100d6942d482c80d400f4050a00100d0b80900c40b1848624403110350310f482d00110362a480881c2110400e00f0000c1000c600c4040502c11503400e03540656101c01c120703007028603c9070848041030708004c01c1080d40012a03140c2e00440c2c9031a000780102081ea480d400801260781c500030411801d102000780007118103804d02004e031000e00c0001d02c0225255504003000380040c110b0300e94003c00035402485072128011008680c401c1800d404002c407402898141e607843c0c000c01031070311032404e202d4003a007100c444c0e9980c41c4190008c0307032160381d02100018025100b0300c05110000c407403d40c41c80d0842220b4189038a00701d10b4840002c803140142c03425031300c1404000844080c6130b8400c0b4105400110084103a840100d50b00ca40d00f41d1000710601e4540c450100340440030790b02c0b99503c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 632516600 1250 632515350 632515397
    0x40f0311031c02030606071a0f240d020613030c0302040f0b130b010e0d03050d0608030307020a0f0323070615052805061b070e130b09100501060e01 65
    0x19100900301c0c0700b00d042126aa009035800500c001c00c400e260140c9642d17141d6039203194406060091142404000703c0b0702c90701e49510350020781c9070007012040d40640d112000300c18040e4030f03a03841030340c6060004055440d403505680001c4101da810301d13907003034580c14a880c41020360b1004034800d50806450220303450711f9000d040f009003006004103075000c0d40442c16201401c041c0c00c0c1c0c10704118100f038118455585005c020140180a921115981c2c00c4452095055036450f4000d07100c0c40d03000f081840003099000a5481156400490400008040345422514041044621188920403004840210860324003e00c1520b10a080400901e001c042080801400074815290700c0031521741031140050780c0f29412100454900d1003810103030345074000101140c102c00c11120094400c40052103402c0020494000681080d80000d90580b800b1440000403400c0e840c0020100600c440102c2e0305044100900d14001404420500041d80c4641e0700070900c4188081440c002070304242c142c1944040030540 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 632517850 1250 632516600 632516617
    0xe0f072309010c05030d0e1207051908040b0418050a05060616030909020c0d110109210509030607030222050306160504120c091a0a051215040f031103 66
    0x20841080d003452000140c81e0400c94606060062100c103481c0000c00034070042960507000c0600013410700703c1074903841c03034035410000200b01c00404000c1000402c400241c0c00e2003d07050b034842d81e0b40840c154034056002d80a0f0b0340c09040a0071001c50045145148200404120284002c1c1002243d48000108091301c0013903c4682d0441d47c1041110f20320700072040ca050300030780207003001c007040c41e9182d1591040340d02c00b60311404c598100c4021149a0781c2d1052642c10340603481e00080c006106640c0392031107120b242107500107005120070651560103006509842c40420300905440d02490a0007010300690320114520b541c2d44210900d00c203150000768000070554038003400030a01c56481c0e030060b007410101d10142d80f040c04014040000e00000700e841000b00d551041c22002030300c6142c90041d20503034002c80841d07600540350b644181859101c00248d00200c40c02100c118034186080c2c5da24508000340f04210950b091100800c000511003902e00e41860b01e13110baa601e44241c0880071226490b406401e92 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 632519100 1250 632517850 632517887
    0x120f07150213170f0a0b04050d140418061d0906220206030a090f05030c10062304110706052a07032718060602162d0e0f07 54
    0x6083c4040620480d070034620802c180111500c070078038000020b150002c142c900700c1e000c00c0508100802c0203018404d0742d120240d2820409000c000e100000c107902d005038081c0d0040c035090315400c0030100002c0d0700078200074000c0c4100f903840307805030312800c0b208800d00711046001c0b403103800c0100e00c0c80c031007003900c04100c21444081c0202c1440c5940c02c2280c542d0016004011158a9101c2c400104290715080600c46120758001c1d580c0300d10111405007000b482079450001d00e881e01c4404c00c0134a41c0081013403501003125150700340311003d01001400401b1307005ea61001d022000300b02eaa003000000e611450050385840380d1707030000314507840000c101d83c0c1160341c4210717001400b40240300029000b2010b5041c21110041d1845075001c210f0300101040344154440c540ca1041101184041002c1e03100e00b10160202c0e10140c101c00c9a1446148004021071003030b410144103080c6070202c124941040000c0030091003068915090b90350f018002c9150b400c0d540c0d4684114217030007090000c3e00520301041683d100c00d1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 632520350 1250 632519100 632519137
    0x4030e0f1503060a0302040c0f021005060108013c0303170402061c020408030f04030b06011e0f1218052a0108090c0a06031a240309120f071502 63
    0x8001c0001904007500c0c642e0030442151000c00140d0b110702844d440281c0a654040e80b60011180003481d0002800ca01c03084540f9200c28400141d910003030441c10341c0d20040e1001e28442d0360310301c0c600103541208040070011554122001c0b41580c112010004c40e8081c0c2c1c1c6891001d503d8607102c52501c80c0580d80254042e0041110340c14520310b07180507004040040c680103007465900c0400300d086d0fa10103000c1c1c40041100117020b00410030040f01880c0c0011080c07800e44110300d00c400c2c1e030b081d1004030415603c09209000c4a8991300c14803414034106c200b00302c2141402171810450031500702e020189411106406420034140055058500c074502c1e0490103002e0314441381c6920015945103030050300482140c003c0400d1000c880c3c9074408240024112603800040400c03400c00f400040e0600c402065100c0c40304003e02044400310b00c18403078020307265500055520f0b1121180540b5101c1c048a5070341c080040131501e1480507003144050000740b4002e108090404095681c51022803040d4803c3c00640504807 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 632521600 1250 632520350 632520379
    0x70b030906130507080111031b090f0f19030f030f0203030c0d020a0302160c0303031a01051206180a0506010e0f130902060d2909011d1306020d020304030e0f 69
    0x5400342c2001d43e000e24280d5113816100d80301035003501e04a04102e0a820302c00028442240391242c0e42c102020403422a180c1404200000600620003000c0d2040c0b05100e000c1901d24140d8540d5284072400c0e145501800b1003d40d03d03e400514484c3d150700a4012a40c06517881c04401d0001c13003100e101d54084c10385546420045000280250071509114080560a20400c5001070507944003141480c020050320104514603d00201954540c1884071588040d4161f00c0007140d80240a84460360103071301144401d0740d81c0fa0007150304a902e50a1170411001c200303041c0b0130314900d582c2c0210701449081ea10450210311002c18022000143d002484d00a00e00e00003041e000c8030594801104244001d19803841e2144490041c0166510100d644610301c1d00f551030b181002800d05402d0107800c0c0c0a0316560110743c50071003096402c0e940300c424100c5210300c4000040403c1058403000d102c11b84c0c003c90031501c880c40036940c0c00083d0000c8404034080303200c06500f01aa8601540002942007004005181c11804c2 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 632522850 1250 632521600 632521621
    0x501050402040f151505090a0306021b030f0d0e241b0901080414071a120109090c030b070302071e03020f071a0714030f091f0c0f110301110408070b030906 68
    0x1501d4246040190034040e1f04c05c2942c03105001d0000754001c40e405611500400c031905107500100203030001aa10820000c4034064a050560700b69909402c40081c00040301c0e0300d458180120780412010440740000191524084041c0300c501819201c055402d005600d0108805684210802c0d2030218000b40000b500207100f246a07402103d503500300b0381d0b003e0355841546e1034051900142d10507541700e0100e8011200050301892500412802c0c0040c00650040d841d090300403a03803400040c00c070f580c140c000114902d000c1d4040342c4a5681c172451159a184140344800c81d5900c024508034014041c06080070403040f4001415404d80340c007c400d02c8185c41c0c5082c0d040e00e00343d0203a9030898a0116607400c0413401402400504103203070500345801e42c0c42912004000144050032501501c07503414107140003d095004a80c10320480d404003031003031f400d4618282080c40800c8240034660560810300c1e034100704045038010b071048440c008100c81549450b0041c0c002203010454040d0007561203600040c244409 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 632524100 1250 632522850 632522879
    0x9140906191d0f100f020711040905150a0b0a06111e0a050601080706090501170a020a0c151407020f0c090601090f06020102090a0501050a171506070501050402040f15 73
    0x480c280a40040804000b0309081c501008801c80721500846010024841c003400f80b5940d08004440461400f0f2103039489469508119060178000d5695a0903c802c00004001d100d0340112a83c0401d5818a0300500801c054407603010424050464041e0000e03445000d6115090b06101d004090140072284506d102124113100c1e40640d0b06100e42c130b28400c08514140001c070b0180154001500400c3e04000780170302006d005901450400c41c10388200044100d03504110394000240100142c2c3d120b400e440219095100203401030440008004021102a22a8000811003074044119030b001d540d03180003a61212056844002035070441291607a041c80d169040c96030000d0141060f11034141c84044d44040811180c0101015039800104210302d441e042d0700440003402c0c2460b20518184c0b270380350028040944200c17107100840034000400d0029100008a10003070801070130981d158481414001d028020a403070990180f0b1030000c0e00e001c4a2003a0198500303030340f0b05550b80002c451425018901881 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 632525350 1250 632524100 632524121
    0x90d140309060d0f0e06040308010b130314030a0201050f0c070b040609050f060106140f09066102010c1406010b03160314220c0914090619 61
    0x8208008006a51141c0182000403143c0fa000104020940d40920407200d0075030701d41328075030312a0f41040002548400c1031030548000074601529800040c8842d0b0000c1c2c504d42008105407005880586174407000804de10f203800c0107034003e00c05500d0751100000e5160040e034898400322030401c030034000300b680f4224182e0440d1040b5030004003c1c44c241c480c03504050824025201c02d8000c000100005a84510b078a8030f85610103424520b0300c20500d0140300180710303c0c15450f014031404034551044100075034018241007003184c0322140001c4000034000501161804c0c450503406a09601017400d0079a20743c4641c120040070383c044190000b900103460400700400104d42003242090801c0b401c040070301205000307004103000746451f8180149041e406041c005018130415140101c900800e0070a540101d41010072000318071b0140d04000750144911001084c0508001c01112000800426560054444420584000a0715266190655228030040da261050a5003c002d43c80394151147c0c002c0100c007 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 632526600 1250 632525350 632525353
    0x613020a02030f1605070e060d02010c030e03010c030b1005040803030c0702060409090503030601080901090f150f06080303090d050c0a02091323071e03060e0309030a05030c07050402090d14 83
    0x441d030440094a9510202021080302070084c00c0d001044020414500a003048641c01c1c2e040d13140940206442c002c1c07001001e0304006290f811082410300403817941c07008050240c028021b5801d0b651018010308610314806010b038504900030080340e0f10401c160703010344180401641c40d40c1c48050398002d00740c200d054141e84c03040c1c04100006854165100b1912031900c6580519160b141803c0050841e1100602c0d46481c0d034180074580b000221840300721400180d00a051500501088010310003c3c0410120a44180d140060200d120000000030750f00c60b880c0c4000315110b110780e04500700c4041c06400c0c129100c03036100080720f10052401c40c003066400740c020340c0d01c0ca000850076103803400c000003410540d40703a22000400c0e951000f1428005407001d4040e000b04241c030b010160604020300151840080e200d559a54281484000305204480e20709000904481460707940382080b0391294800000c0b500307240b1604100103a10b05040c0203944140c0c0300141400241d05c01d03900c0700000201a010860742d41d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 632527850 1250 632526600 632526607
    0xc0b0d110a081b071e03120c020703020a1a030a0e0109061b08090d020307030e030102210108011419020d0608060a06031106400306021801080613020a0203 68
    0x41103495006001054055560502c00341000b004101424000c82e51143c11500d04021020100d94640350607250240c0001c04502107012505080f181802c0c2c901c51940036604000c2d0131510a5030000c4c40c041070768001c94040004139175840700b41c00c40196100154000c4141400010815a01d660051400a0002c40045080c5d9413654540045640402c0001d032580030307542085010907071209050340d120750184010854000c081c400a5500d0091001c004c041182d01000d003c4161000c0d01a12218038080c801668100440e60b4007520009003406003107015032800b01c0c8024180709000381d071402034117041801e00d211005640c01c800690f01061048008a0b20b820001903144003c0100921548140c40c0c0000c0450451801da003079030b680f003941d03136200d81014014200b000804039140d8800745c00e80b07010141c50315458501c1104440e0600c860a036154000d460000c03d11490350002c080301c810407504130268114800040d0341000d0180e50380303074016086075030745000d001c820b900824000d410380c0112070070b = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 632529100 1250 632527850 632527871
    0x91a0904111c170409051e0105190305010504060203010e0c1e030601030e100f0e01150506032a13050102011505010503090102090a08031809190b04090203011b1b0c0b0d 74
    0x88550340340124041900084d0803c00d4000034480c464128455071741080485000041441c00d8203410300829124001c00605d18414a01007804140103580c040d0090045d443d0078280382d0000d4009110b00d520b13294040b800640e80300070b0300003161403001000401c00e4903601103041c14410390b00300a2245040c90703560101e4600b918010007021492850295020840966200c84401510441600e92515a040c040341412004e01c5400315010384d170041d2007180d2a170343c40440c443d40303d0700e0104200010701403000c0c1c00664010400001d00c40d1500c4550789030980c50b5210012800c0f0b96080c1c8900c40003803007041003030085601c030700001c5821805100026050150010000e800074945030301c0405540e0001524111003070020a800340c05503002c646900c9640707002074001190714514080302d04119a00c55400c1d40555440d4898180c0c16005002006007101d00440044002c01c0e0141510201d00300300c0740d84880394169003101d1025940140c0300310b200d6191030300d072002c0c68110790010b0805540b40c00301c0306c4 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 632530350 1250 632529100 632529113
    0xb0603090a0303270507051c0507050405060d0803074a04021306090f0603020408060c30040b0f0106120510050603130c080c0109140307090204091a0904111c 69
    0x442c4c0c9000300060004d80d443c000400c481c120020030180710f5405001558000300d000803480d07008a41c5c064402007056030300c21001901c0840401802003030a46c0200500c9007142c3d101460320484c60031490488540e08002e80d040010311581442d00789401c040307182078130006880c0300803070001c3d100c0030b0005410440201001000c21686d0741000c1c000400c200010000014100090002007466080441c503180c20410019101c050061280609080000700f0001c44d201c4402c80d6010707030b10404200298040d6400c20081d10700400d460030b866a600c0800840c3c0c0045811480300c1c121607a80d20356403c4080ba8080d410040d1000524410840d801c940b80000c6030b85031500118440d0810f0000365036191410714003403034521400d800841301540b08081e43e0071a6600440040c080d034000d0211031041d011070b01c0009240440340c0e007110100740c1c000b10300041c21181b59041000455034000401c0c00f0030000d4010301988507011103002d808039400c440f56a003035040003003803a507816024400d0000141d600d2703110744 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 632531600 1250 632530350 632530421
    0xa09050112030318171c020f0a030e16170709020d021b010506210c0d0302010b030c0103050606160203030c0d1d0f0a060818120d0b0603090a0303 64
    0x2640c88200103181501003681c54824400a181003250a14010384191283c41c105080c80d10178203161680002d090110031002200e51000424210b000c0d95a5828030100d0501501301da00d4030030100303007000181d8441d10004900d00740030348451018602140d2501c5006e440c5540c1d0400009103034050b070000881c144046000806041324a50400760351180b419200190600d0002c040c030409914010034042e4580c0d558081c5910a61108403661202461182003824240605022503010680784503580030181c040d00700d00032190088050714888026440107600783c070001ca1b000c9520034810019400b266050103040d901940c0040c0c11030b41060100d0000701d140141300c200e55004116070b501c25100c80e81856203281c25690b81922080e2100d1070741c0010a464100350f026020500134410000780344440301d1590025420810400c07145011110300035545682d204141c0031304014240740c00c0c84200d05094048901990b0300d04018800e014080e20128000c0280e041054004140700391101072041544400303 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 632532850 1250 632531600 632531609
    0x210f12020c12040e180309010302130504050403020609240a0c020a02060403030306080601060509060a081f060309060506030a02130911120102030711010b010203090d0512030106110d0912060b0a090501 88
    0x100f42c0d51400c00c01c1840100f4801030013400412030b00c40110748480b40120a84404100c00c1c2405611051170050104045640c0e401c0960060b29110422040c1980094030f50b00a004400a640000300800c5a80b442c0d64034003d00225902e02e2500444d2110240c0c1d0312101102c0414419501000040d80c0050501c0e0f00952080d00000e44030001405072242c00d10020f40141007504055140c1080c41c00880c4250140052050a116071072000a00e082c0241c001c100104014580300380b1800e4072160302600814210700c1c10348d0b440b40340c0f2000444d1414006a42c0c500c0325001000d40c100090002c1864024100d0160100d071161184a031542d84e6482d22801440760364045000540c0724a4140c0c4000c10880c0c0460106139a6070521101041c03507600030003100e030740c000b0907141d907032101101c0e043c03061038010400380d4086003200000001800303541c8200e100c15003094030000c0d1521000d50800840c0d140425020b00358040322410030142c005810342d031008005c010090000e2040d0340d03590300c4103400c03288240d00 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 632534100 1250 632532850 632532883
    0x709180302010e070609120215041805010f03110d05010e0d0504050916120b03120f1209031903020c1e0102180409082b020301060903210f12020c 64
    0x84080800d60207029070f030001c0f540800106446480c00400074800b00b424802c48910780c200c28420b00c00d64448096444681114000e0340303030b41d1541c41002980181a002c451560780346802e001040400710805d100c01141d8000f00e4101d0490550010402881170301003003224590b69509412420200601154407840016120b2036203651074a001c1c13000c0000003d00d050b501174202820071650503040b29900d0603000c041070300098040103042c0403900c1c18010b1000c0541c0761101152040c03201704400010302807081c03400c200f280152100c4020941d680030340401e0b0241c08000040400c09103100b0b0b40507100c035a00b12412100101d07480607140360b4250140222101c20703500010441c0c030000606030840340d46002650100095801070b2540c20352401440e01c6008480c0d0701000001c20b0315880805100769920201c801c540e0f950307507007402034809d440c07600c4120343c10100c0c0c0e04502c0d109c102c211140d036054882602d5480e1500c55152040705c1e4080f03600c4004801070340c00d1040c0e284c400420007490b541218070f040d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 632535350 1250 632534100 632534141
    0xc130e1009140f37061a0a020a02040f090b13030809070b0717120901050108122104020a0b0d1a120a0807020a030f060b0405070807020714030709 64
    0x30032600307603840d558501250114503414071106400d40d8032015400405098010309108940d904e01101c400004455140c40344201140b80b00c14505034091001c41e0f001440328040e845040307007480c002e8081c182114003d80c00c17207501b103405404c098100b040040501d24002a5a409551343c0483d40c0000b074460b20440030303000046a080540010206801082c3c4000038040b15151602035911445100c2c1c00402c088142c4148041044014003565040e680c06c90062401c0e1502c04030340c1d07001703007024030440d80144590030308030701011000c20480d44081d0030800801101c0661070000041da51004c1c0080380c22040340305000403080d0f4920040c01c80040e04080100c0e00c20140c01c90128040d114000051003403030040d10101c1e143c0400510850103036400b040b0701c0e446014500020304900810352010301008010341010b0200100c40d4020341c8400400c48080009d5102c103141185d0b5400200c80c4000580e0052400307104680320482200d041c070350300070126841b40e074a4035042000d0b54101d404204a144e20903 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 632536600 1250 632535350 632535359
    0x30a030f02070b070305160216030206130918151a0d0c05040f02070c1a0a0f0507020a03150f0e191e05060402010f030e070b09010c0b0f101406030c130e10 68
    0x1681e04440100c0a1004041e41032000340090008030270351000a10a100001301c0818a120142c40c41008010340307102000300083d6004211a41e03018000b080320390b07410b13024809a80f28068401c00e00c0048051111903500c6850b03205204a21600e880207450b0000350950004580cae480780600205000c00d0400582c40310200d03c4c2010340d01419402201c510843d0380c501001643d0f580c4283c40125a02e4544a5080c16002105407030302d01c108540a90001c09628020007440200c40009440443c1e58504001d07055905610200310340c0201440400707900100e40010640c03200b40c034001450360168440307203e0400c986210405924190b48201c0d42c1e60046420081590707000302d5580e81d09031860405000e101d6811001d55140d051501400320442008541944143d00c107044604225a10100448a500f4000001c99548000302c442c0f00b14840d25000100e5450314001c06401d00003400790000b070542d1110092031000b500a040b1315410b0b401d43d881d00140c081d0030810800c0c024003610700d0581c08107042c03 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 632537850 1250 632536600 632536621
    0xf0903110d09081b04390509151b0303040f031b05070e100b0d05041e030801291c1109010e040b150a09050405071e0e0126190e030a030f02070b070305 66
    0xb4246081807003014070811203180c545c41c02042902746d00c11180c80e07440402500c070305850190504010345038030011080004106010640e190303540d0103511034a44850711341c0c00c010400840c402c8010803d1308aa40c007084050320001c0d981e500101c000b603041c0e030040d4851103c09650782010b4a00d0104c25144c6051001340f08603c40703292102c08414404c0c0da210b08c020f0310302604040041c0b00303441941d0351179000250700442c85c0c0710350702400800a103115501c9081c0e542502100c410341c90f0424040c0c1c40c01301c0000c0c441d002c2d2401c991002b08183c45502441900d1400c0000501141e41d8480d00208410b080000598170341004042003000342d103407000342c075007001e0600c422074030018a00004c2c0b0815014465114006059562440c1c00c0e42ca4083c1008808030012070f001c1d10301d1009920008682c3d000d0000d4141201d102500c41c22403031401850320700d1010280da040c0d80090142c060142c00800411741014440e4000715400c00e080007025160078103075504c64000043c11510030001a60340c000344045000d5 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 632539100 1250 632537850 632537951
    0x231009080d052106010504170a0204051501181a03060f030a05210f18040902100932090702011b0c03030f050c0a120f0903110d09081b04 60
    0x840f0000300f0700d4902140080c00c240f007940244a90151a0303040940706910800c0600b0045901800c140301500303112104c88250784000090714041031850008001301560742c40c0c90412184071100d0b444168040d0528101558000381c41150801040100f44840d514200071900440b80310b000101a2040514074058001950b0103404180c5d103810015a403c130702c041c4040d503188420124481000490b00b000150007891107a8001350440e95a0003880100c035040240a4210741145c80c02500d80b540ca02d0200305640d080303020391030480c010701844080e68205004041c0d0b003c4907d00001908105d4552101e0004030414000c0000130700d06000c031000c043d81401500501c141400e000d2169083c00300312041d1a0092180c40b4040040102140550701415000007614a040c0101082518034504005000c407c0040c82054248940007928500c0d0b880348198604440d009400b6006944617490300041e00081602e10701e0b4041c0c2c440c4105015505e4074110000d04001c954a01c000c95009001d04440015 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 632540350 1250 632539100 632539147
    0x3060d0c030f0f0302100c09140339030c030a24020c0105010f0504140714130b0d0b0a080a030f03020714070f06030903051c06030f0302010203040b01231009080d05 72
    0x1401c0c0b1180d1218680c0000d0810199030805032704030b4421a5480100741381c0200100322b09000d151100241510300f08404020416014050b11030340709400190a150340c800e4880d0040f501684111013800c04251120146a01031300000c1e40b220440c1020f43c900c03c00c1ea0080301c001401a590b0b18010021183c0500c0c0d07110080c00c041da02402403c00c100300d0340c5400c8600030101c5051013030042250481c030070044210345004520098031000d280d250100315000350400d0000554041ca0300b410400613140441e4410202c4440704010242030120b6503044039002074a0045400b03164091008100158046c1e0441c02d11126040c0109081c91400003084280c0600e58004404c0c580380c1000e25000c01c0d4844101d85990142200b410001034205c29524000d1415a0020301100011510788040590640065001c3c40c00790000959507600c07081903400240006c03010400c0082c4a1250004a060800d520301e103000081c2007025105642c0c0500c0c0d8105280040303038a00140d000180903c401a0501600400a = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 632541600 1250 632540350 632540383
    0x201090f06020a032d0510080a060501080c1f0e030c0d0605101e050f0609100206010303080916061d04050c070605090c060406110102190c060e0105040803060d0c030f0f0302 76
    0x40c0700c042400f11680c10608003000002c1e2a140001c210040c070f040d0b981c0050109104270b92003c102810104004c010078050300159000343e05221034945081011503000400ca01486103003646030510a80d9000c84250103140c040c007540090300601e40d5421a070310354a6010b00710114451030481c0700404400c00340d41141c2941e4a50350008403101401c4130252044e030724182c2d0210031035010070002442030300450302895403048401c1c000080c0c4950200d07140f8101d81c8640c442c002907864900140752520343c1030500e0104000799900c100714080c8109900e800b11007400c0041c00d11402c00c51301081c1510022544c0d00c0c441d82001a40008100441c402c0d59400407010380640b421241070030016440d4490b9109203000c12100040b4401c201200390b040311130007102c0c0c0700c020b282c208240310080d1000d03151520a0f00c80c00e103401d2101a014506004d00d5200d541e2000203103107540d4545003088110228154140c440780c89041000c00015000b000c0c40b982d0500404d80304c54810043c1c680285001001400480300 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 632542850 1250 632541600 632541641
    0x14060310141b090603010915060906020c040f0207020301090c060f03230415020c0606040f0203040309050103110403240b010215013011040f0b130c0201090f06020a03 73
    0x91044031111941244030351940749240004454003410b1030082d90800381e440b07800000002402c11541e404001c02080001c081070b100350303542100759511501880740304051703004940e203400d0914081e0701007202c15600e00310041c00c1c01c4040d000f0900311030000e0070842d0315010182003444480d1300700c103c04070300005514040c8400400d5040c0c8440900e02d8641d407a004550360400b08007008851809450f91035181d5004544448407500c1c0e507030744c4480680e10940664605841d061180c1c8c40d9001f00c0b8829509501ca01e0180d07898030004500800050002c401208418000400042c88211a40c0d60400000c4110050719001503100000c58109802c52815076100c0303074141c402a418101c149044030841809001e003840b18110302d411011920048001c0f080c031070f410840420911011411041da0255420000d80b40c0014042003101c8002c085640d0001e0300804100d071484807a001304c102c1d80100d100118590f600e42d81c03014a100007080c01212a5500801c10265182c0c0c90303c500308000301c040c03015520 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 632544100 1250 632542850 632542871
    0x8060c0f0d09020102030c0a06090210030207110d081e03040b09030c0a06020346050105011d0315040b042d030e010c050601060203041806050114030907030614060310 73
    0x540705841c281800640c854091409583c000d00a89512180e040262000a8240c5c900840200b4034600100c1c852405280003800942c8240300b524001944803623485446d0f0300c003030100f10141740011400c0b210640c0400102c3d8410030107240ca2111804c40018840e2203041501c0c100b140807074010040f11284d40103101d20754020100003810160702d374000a005030b59894950b50b14001d001591500c1c480a951200240c50592907c0311140324080e040402604503281c101c11306080d58820303c660f070b0000b24154450108183e510100400d08030b401002c070b80181443c0c164150428204480c2918002c4c17210080005120311841254030b10ba020304881200404400e1010410940c0030302d0180c20000c0038031400d8000d0340511014281642c000086900c650780d5480000c0d070325482805105014008031403001c80950f51801004e09030340c016100c100d41d0324090840d101c890f40004100b5102482000c90002c04180580710707140000c05d0340c3c0701c1000b5031300d442014149071668070313406826072600d04140c554 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 632545350 1250 632544100 632544127
    0x110a090803092d03030f0c010e0f120901030204152001020307080a050a0f0f05070207240809031207020c1804020d14030d02030f040b100b0307140d0f0608060c 70
    0x10400b03c880070300000700d14035009a0309080c07454140e080d0076110008101c4e9000c44080003030491803040100a10603000e824030456211074100400c000c0c05d52149072107126130038980e00a0b20050030185401030030a44d40303d1110001c0c54a6070b0101c4081500d0000e4032000321200030a41600c0b01d8107800a61541c280070b0001040c03801d00030000c011490796500410f0980206810404441115040074401e58005810340001031006030344130800742c0b150060020701300d18004002d981c40c85030002c407549058841034007900c4001c0014a05d0115010420580641100e003801d00b50190000c1c0e4010100c0440c01c00c18403007034003080c00c100240c7c1c014a504100040e41c0b2118040303143d640c01034500404c209480c2c8a2441d50250300010203000d4000300410208950218a08d441103000b0741c28003d883c2c4410010b24106e00081c007414480c0d010400008981d03034000d042805604240c0c0200614103829455400200c072003401c03910800d03540f0344008001e607042c1000142d420000e10411035240146420200 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 632546600 1250 632545350 632545369
    0x60e0108070b04150c0f03030b010306050f010e0f01111605011808031902030d06062d0503150d150f0606050910030e0a0b0112060f02070b01030b060f04110a09080309 73
    0x5151004510304d181d211885001890100c90748281002e180349181c0c0307400f80241c1216290140042c0c0385c002c0004107172501c2c11415941550684030303204803890081c10300966a1400d1070280c1841071030500c1e41c54801003042115009600701c88803015680c00c01c4001006600000f06084140c281500e0502100a000c022141e180303600c0700e00da10110b0000c101c2617045005003c540341040e031514000140c8582c001c507404583d00c65141284940c84106518010261040408035001400c14000140b14241d5201200d02c524170082c007000304510b9a60b1503503031001c2c43d281410071254448030b44640c000120b000d00d40103440030341403d50030040e4141c040341302c6030200d00c6242d0405d500c40241e50103445c424046a00095045095000c04c3e41c1c586202c1003200004c07140407940e5520300040818110300074801e40d10016031080040c1d41c0c13a440d5444610780d07028040c0455074007a02d800310320111540e6138030408501c46141c442c060748a40566001500070403450740324030701d0381e0402c10101200f0b9880986d034 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 632547850 1250 632546600 632546609
    0x903031b05030703021b0402180913050322050a030b01210b0703090b0615030a020706060905040f03110d080105090c0c0d030b0a0f05061e07140105160c050d030b041e060e0108070b04 80
    0x41880cac0c1d652410720980c031505607070000d40300d4007000480f04034000340b102c0c40380980e640020510401994400501503185058480681214540c500520541c0340050282c103010340b50303890015150555450b654420f1005903006004282c1c1c0b10100b00400542c01181a03102504807081c0d0448204035482809511006104110306a4001034140410030540d001c070003e0701e40940100101e01d400e103400e0040810012003030300400d20b590020303045502d0020b5507891030909a40e0300740e000d034a000180002004050900c400202040c0003410604104004a42810000341e80101d420f0824005001610010703030003070b001c2c00300c83c1401400203448800441c1d008008294681117407000c2c21400c8140c40c000c00800600d00b071030340d900c0084d04200c15003103140504041c91090280c1208140d080e10000a41013005109801680d44400700e01c3c02a0300c40300e40300e0009000800c201c1e402e082d8450103924010500c5541580c0c0e4442404040b414108480c007408112004200031400c00f902014980a18401d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 632549100 1250 632547850 632547859
    0x414030f150a0906090c050102061f03030c02040e0307060b10022811130e010b060304120c15060f030b0a020304080403060e1204080318100903031b05030703021b040218 74
    0x410b10b10101a03200302000f6412080410201d20303145080a114022881802c0c0103202e000c0115080d0500d0a00c9140c04900c00e0702140441895070ba0107070f40d0900344500603a4021381c0d452580340549014001010501d2150400007640300c002010450802403089412007107500c10a243c4191500d4a42200e0701141162030840c4c501405280400030380000629030b0750086030b044080c00a480d8690015200b000765080280140d80c41c08040c401c80d400112070203411921000c000c407900900514001c5803c80c02043c4403640051628110760540f0300c02e03842101d14848004003007050001c0e640e0100d4010040400070741c9942800c0d00d800f03c45014901019103020741c0c4150202c98500100b0200c400d8044081c406a25290740307070503103501d80e000508140700303030b000c817502001d118900642c152440344481d86604c08102d065440407501c1203500b6084503442084070b522900803ca00b00003901e6060702c031307078000d0100510101842d032200d01d064041a0145005000c119041140540d130b0500d060426074 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 632550350 1250 632549100 632549143
    0x105100e16110f030a051201060c0b01051306090e0d03060503030906040513020c150601020d18170f160302011205190209010215101a03010f120302070801020408030414030f 76
    0x400c50705040c840103c281d46072100080c4403810300d80005c068030010a58510744000342c1e9031074030159090380107450010403501803240141301070714000c070000d611611514400030310161100c0e1b401d021901d4030441e41c0310f0ba521000c01c5002c40caa16029020291500b5009182007510b144049001406140034407482014410040400050710743d064903018030700c400032240034000111103090060310a40c2d0590050040005a09940d80540ba15080010580500343d00d898a08030700b002c107065400f0480343c420700580c42c0c0100f2a0070b04000c0030b2001c500c0200040c600514501c0003510f050360200100920324245810000040f1005140601d20622030001503a00c8860a004034180302c03076040000d104581a80c03d00c00c072208000c5a000545621a40c8415040818045070051b40001d21503030404900030201404035109000c00220345a1080c0121030f502c544941c081401d90700541c010780e01e240d00c041001c1081c42e46002c00f4200010095028000480e0a06240e81c2c0700c13405400c0c00000320b030347c11 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 632551600 1250 632550350 632550377
    0x8060a0c05070510021c0b1509010e0a0b0d1803090b030c0412060605030d1805120321091002040303051e0d02070c15020d0f0e0a03080c0105100e16 65
    0x410031103000b182c0c40016a84440580d40d035444c020341206072101d02c10383c060614001100490b2090142d800001400c5100071324010036048415400b1111720380c1000000b452103c9070742c5072503040c2c90240180744032039500c93b18420640c1c411100c407445852106850101c1341d90100c0d40010a6030242c80c082d00000382d8a6982c58662500c1d486158018032802800e01c00c00c0d0180441d80d4000030940c0c10403002d4409d030b5400e0403001c81d15240d17120b50400c1898014002003015240110740c032403802e840d0300300396070a0030280d01a02141d00f1010722503020510b41e40c410800400d206201d800d1a49401103c2141442d00350384000300580200c07003076041803801c034104030b84a0350703604402d0302c107030920101095540c1d0f0094034100740c0c4403295210b801c210b81d0034142008400ea002081c0c001c00e1078156960855256942c92084541c3d05d00742020039008440b00344044081030007440141201003a000010070942000e075196042859a9400303c1800031200c800d01c28030003a02030070406142041e00e01300a40c0c2258 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 632552850 1250 632551600 632551607
    0x106050a090f09090506060a0612090203010f1103070207050102060c07061e0e010207020108010e0105100804110307091d060c0406030f020919330c1a0103050c041508060a0c 76
    0x60b00601d5001c440e40b000042c03980c040e5000f103501140328506444903038541c40305001d0301290030b01500020903501204d2007405201039100e0280140001c00100d04911505a28802c03030707807480c41e000c02f00c10000081285898041241100408003807008001c6484d000103400303064000ea1600034180b030749402901101c0c4150544030801c1e03001140c0c00700f1514501d000098002e40c13205c5012030100e0300c1c00b000028030340e64000010b4103d80c1e0150002041040808044618040061045032043d0201c031201c8015141001220081d040006d800950904003042070300d9130242031500d011a03079201d102002060102501900d08552260a0216aa21446200304080d000704201240c0148060010b01120160340d907080302240c42d96a5550f607014032440468806403606410350035600d403082080301941e03120b02c440306802401000000892183c1c5001084202c500780c0c8140d6840d8405088141186028850a815014a52145074100b0b2500002c3d07030b12150014910151680d0700d08510310038500 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 632553956 1106 632552850 632552867
    0xe150d0b1014010534080d020d270b06030f12340b040309030b0703200c0c120f060906070f030b09040f0c0b04031a09010606080106050a 60
    0x220b101700e519500c82c03801d08003020020008112008542a039001e00050f4001032005070f91013403204c043c801a00d03543c4110a013080d00c8101062a007131840010b59441c1e60340400c890649542d2000044d007041d80351155001e0f940100b804a0003503c203d00010301c030000c60401580c498a4038090001d440c10b04c08491209d07050044240a4003142f450803a0070b610602c0b03031401090090310703951045001041a101b0401094680c0b5041800c441600d40310240c49080d901018180b1441c44240b43c3d41c0c0189020041c0a0b81d055031108241d01401e02c00e4250203100003044600b0f0307060003031409541d0b0740220b45010004140e0500d11903142c0c07082c010003c1141c40206030010585850300c40b004510401030040740c0b0031081c801c00040804005020703000860046503004d481a42503000f80321031103001000e0501991504106105c1d060b00300110906403459854019122040d904003600c0780c41 = true := by decide +kernel

theorem cover : BRFrame.Cov 632374100 632553956 := by
  have h0 := BRFrame.cov_init 632374100
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632374100 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 632374100 ≤ n) (h2 : n < 632553956) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
