-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3505
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:51:08.388039+00:00
-- url     : https://prove2.me/submissions/4c7d5173-fbbf-4cfd-b474-11ed6a75a18d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 630215827 ≤ n < 630395683 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 630217077 1250 630215827 630215843
    0x7020610050f01120f0e0f3c0703060c180f05010302090604090905011418061618091b03180f0c1d070912021008070504080a05030405010f020a 63
    0x8105820801d04040e0461982c2c10400440540d9404604e42d004500020054000000310b15505800d01400e01c20301070305010003940b2039006014100300d421701c2400724030300402d800c501c49024034100c1158806028407015161007011008424020254000401c03a035050301c9403404015038032010300e440c6071a0b108040142044020800195009400030005071200030051481c181e20384e13000c07004440301e0440a80d500c1c0e56030741d031402d0789803e108201e81d04004890503141603400992410f541c1e841000b05100000c00004030180c20a900481132206180c41e05940c81c0c1da0b142c0c41e283e40100504c3c4015201080105203002d00310028000c0c89400d05407101202011960000c0743c50b000846c070070504085840741c05d86800003428140000401c00c05056010200b056170801100003070611a1035081000c6542300800030b0401130b80d45900c0900500b115040400541c1e0303e142050318580030b268003501d00c90248003030500070000d0110081c030655800f47c03108929482500e008a0748c0c0c0e525001d0080c4001c13 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 630218327 1250 630217077 630217079
    0x130908210a060e161803050703050109020f12070b1809180d09031e0f020d1208011403030702100201200d0c051312022209020306090f10051e07050c0607020610 70
    0x81c40b98103600e02101001000c111206d96170b59030300340707040c10560042e40d1f5030359202c01c49011490881100e81d0a6601142d0b59015410311481190b2602030302d1143e4181d01c80d002981010f01095000b02d81c41d07030035005150040728502401c4a00c61340c1284030a10910b8012800b0141360f0901800c00c034401d49810503074031f14203100300d07005202030001d2a00c8203503a4140b031300c2c80000040e51140860420240300d031124440080142e04040c00c0035030181c02011480c03940341c64034901920004107540c56150101e812560000384042c003a801800011000c1d00000481e56000825480c15801485031884d400070030031410201d00801c41f95806230141c00080900765010401880c101b600000f111980002c050070380d40803203000c1c06d0b003402c90410502c21440e030320f9294010561505001e0103501c4a035006c040d0503a020700d510781d09c0d00c890749070381e50600140d95040890444c1d0351800c010785d08081900c0046a050604c13807405840c6400400c0c0c02c28141c440c680c00250001d1011484601030b8801d0700b001d05601d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 630219577 1250 630218327 630218371
    0x613060e0a090213080d1b060b120106080c032b1103120a0c030f0b0604050613030807030c02030f010902060f2512090801060302130908210a060e 64
    0x491a191040d60106150703002107100400ea10060040540c80c100b589a0b10345800b842d10305140c0c004a0107014420840808210f520000410601c13031a0b1000d0005050200000060448801290703c030520313602c0e041d00826007a6000660f03032400201242203032200c0c040710740c008844040034401c40c0400f105403104540340300d005000f0b01d010b94001c041544e0401180c0f80040c0411001141c900b9151a01c0322010540300350903100b41446022021030a012044004005c5422841039200d40380c010354002400301e01e03000590300c0f00700180d680061025950002070070010003402c907011301a8030900900c2e00440b4842c8051040c80301056000d00303014203280340241d081d82d940e04042a051081100030000004207107c0c41140c1081c50b102c4c61640398000b50002000380100c040c7e1300303c280b060389413100c1403016944011840c41c44110050020500d00e025182030705c1e543c021000b100500340d1080040d5003000d841106a244902c2d500031040021966074000d10390702c1c8500b03443c0044c2d0052010815206 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 630220827 1250 630219577 630219587
    0x210b0607110102030c03070609032c06030a02120c03070810061d01050c0f0a15020405011d0102010b03030a05040e0c070812040516170c010e21010612140705061306 72
    0x10820741401540e0400d00500c00c2d05096501a0302c0480c0d04a42d500704100c20140c0117040400e041204100f0a03807200344404141c44651035550b4410312640002c800140303204016012260071000141d00d481060400c00301c10103043d00203640043c0401c40800000c0c24154040001c48100c0c0d01c556121160010318047c0034040350030050103030b41000420800c0c0040750704200b01c541c1700308080030000c01d01a141814042000910782c17207100c50290040104024036a4820f0310054044800c442240f60044443d005078014894904419014000420700729a550303048005001181c04407201d500d000d5440b5551354546105084000780070314000e00a0070050000100e00d40d40c0188200d04507010b1856007101c071651000140d0081810300260949804400b0051240304000002800e121000b480d5100006120002041e4541c054090721444c40e03040b80025040540208090510782d4485012030500b441101c16084886149200e0b0640002d0141810300441e45000407400c5041443e508211080720 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 630222077 1250 630220827 630220853
    0x105040b03130602032502010506030d110f01060b03150415060c0501060f0b0a26070f030b100306080d09051e0d080d090506010e01060f0f0507050d210b0607 69
    0x124090b03144200500041a91000318007a0805040281412042c1c80c903085c909440d840c0c0400c01c5905000030301040361400039105101150600300039074080502e415080c506040513402c3c101541c20b00a00140c0140900300541c0510712400c85c00310b80c0c98003442803000307894001410421041d502141000130910034500665003900c1880080380f050f69400011000c0262070b0001066090001b6540c507810783c02072007000d8217010170440007000f514001c80750380301c1003401010700382406129004021000c0c800d901c034090030700c0018951901020700c44001401840e00d800b0712003661240c980040341981c02100a1404c440004141c02242000d90680040c2a424140460b1300f02a80b0140d50700015a404040c181c010100440020081c3c202e0400900e0000181d00c500400c8921200502465070300c02d480f5100480700e810f04810540c11000201c4483c41200000f404501aa4078595481944600591a10390b151610b07445100b0a4070644c2d0102c0c1c00c2c6542543e0300c0901085454006041c40969075 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 630223327 1250 630222077 630222091
    0x303080a1e0b1306150e0f0a1401120614120610090213030602070809033304021503190606030e070e10030c08011413030507170d14010f05030c0105040b03 68
    0x35043c071542002505071110b81e0091507035809003495007802150b00c10385200200c0021540840018041c2000c20001c01c11360145c0111180b001c040b0020310f0340540078181c51081c0000c81042880d0380c4101039080e21160010003131007010460440d022003400050002e00404040e120f07038090301d1a002c2c0040080d07000d515006c0c2103440402d0b00101181c01440503000140c0117480d040e950300000d0040500f058104403a90001c14881d845030f4001c140c0000c038403451840420b98022a40e200d50001a181600d090f685010360703000042009403990100304d5003080f403000000d05110541e12514107406444030a41d0440c0141d1050808218201e500707207000d40c00121104140001d65140d8850080c42c003043d401000840e91900c18116003038122070640c60b441340001021400c0300300d255600418521843c1c00c0502500c6006411001981c000000c4903070150b030b4280104043d8030310115202d0092001d01c40e0380c405440c1c0003030001c0e10b4100822400d1010005075111031610b414802e01c006941c00240c542c0c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 630224577 1250 630223327 630223339
    0x50105010f0c170d051e0c0a0311040b04180e0105070509060717160302070b12010e071103031f12030c140c030d212a0210050f010303080a1e0b 63
    0xc114800e070100202050004c440b00400c0924203039080f400c41015140c0703114507040c0600100441c00f18080141c0d03046025500d40411200c10030383d00d4030241e00803504802c4103604001000542c041c0c0c82e04495002140c200000d1180001211400b422203004079080e401042040045681511742007004001c150b20031041800c2810100c4c5451807503820000585155400c0641041e06041d0100310440041c00581525031030300340030381d0000c0013040043c4556607028080002080c0c26078001e25010003200146001c0340e40b640361a040c450302c80d811030f002c00c240685603040c02041184c40011644211505034440c412180070556501095903080f0f40300d0305640c010240b00185aa80074030100b8150700e01307581c809c3c41d0701c245d5207094500d0045081803072a4441c6070000c45020550468480b200381c8202404002c8600d2440d0302c107a00f881000c040c014105031504041105600b81d00c0b071031505032070080d5589502a034070034415004031075051001003072070119080f8481b1000010781003501140d90140c10 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 630225827 1250 630224577 630224603
    0x60504090c1b05071703030c0d0c172d011401050a0c150c0305070201050402031b19080a0606080303040506040215090d03080108011503080d05060a08070602010b0f04050105010f0c 79
    0x2480b11406640d500480d010b40001e00c2c10800d0180c188111050801c00c01c0156185081c40b101c45006482280c9078400440d440d0500d0741105405122007241c143c600700200040740c0307440b04080d001e1078a400d4005150721034141e10140d400360007940d0641610072100603900350310312042c0155415042403006c0c00400203404940400180d064125040d01290100d02152404244102a0a0f00d8004101c0011a85050304000141c0d400058000585104001d44408218031001044151380300c811000400e50719a03000140b510800688841302900840302000700341c1d03c4401c0d00e512480152000780c8560300007404100546001c1014400602c001c2c3c0c0144d2400141c0c00100f03d6801e0944030a8001c80d00d640010003401100380189006400051005c401c0c090655031810090b004601100c00115a02c2c00001e0854840b458840c010700103c1e41120b003103540e5100024084e000c10034925002c3e0380d0101b8401c803070f07003494007c40d4161541616440050019504112010038911009a80420712050 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 630227077 1250 630225827 630225857
    0xc09060b090d2315061c0f1b030c030209090c0108160c14030a02061602120309011d060901060501050313020d030201111b06091c0c11100f0e0a060504090c 68
    0x80014080e000306409070504840366440303810311300c500500726401210108090342203850012095071070158406c20011000b00281044003010495401c2c1c000d811070020004018807124001c0403045900c04c4402e01c840795907082c02c031074480a00a22482c0070500d10008202940b0a010784032180402518180303444402c191541c102e80c8900071459a2690000281c2280099050041d10b50002d4010214132801e80400002950750b4082d0340306400b020b2010000c241d03445000e4000410f000c0c4c0c0075098140300203205d01e51700c0c0c9030107041e1042901036190460000351540540140e0380b080e105847d00c140c8440541e02884400248860300b00c0031556145d0101003d590390700003400d01100182e21040d55016000c0c0464134200c009003c00034260700401550035178140780b003004401c010340c07880e2034a480509880d14003c0750140c0a500b030390003111002150380c550ba0005c1c404407003802580d50b010304a0b200005214821442d03014a0000132400c01c02032002c092950010b02854001d4580b84c0b0001002c50 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 630228327 1250 630227077 630227123
    0x1120b040207080c010c08010819020d0506041b1712093c01030506031b031207050313051806012001090b01080c1009030323160c09060b090d 62
    0x2081242e121402241c01c07074089000b4420486c16404c607040021031941000b601e65607540c00014001c40416a5a07880000c544644032007010142d401400c44040e030600f85081254941640b5800a405010100004000d240b2501c622030f544e03480f0001d40002c00d04400a52441d600003010f59800020340c150180021185213100103080304900004070360412141340c0c1114460700b0b00c0c0ba0a04040c02c1409010b100da40114241c01200610a441b0300700c0046000032904023008441c28051b00300011400b00c00341b004c04001021946425043e415030103888070100801416961102d11010780b100b400500654005c959090b0409014078480e0059404448403a01b50b03080742c030b011608240c924004020401d03003007051140e68034003202e07085c0f00071713800d103100902d0145144006002c0100e01c9501c042c200d0b01e42c6803481c043c1801c0100c2da41e513402081c0300e1a80c0042d42e0030300c21505021034110018041e4040d10400056130081c80500c0d00d091085000c000c010000340300d040d00c0401c20035a030119851180 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 630229577 1250 630228327 630228337
    0x603040c210c0b0702060405040c11100b0117010e0a0f151d062b02010c02040212041b060e270f07030e060f0a051302030607320901120b0402 62
    0x1c00d44035040d41c540d500d0921007005840e84209503490090142c00d00617594101500e054a10507180054a4454140100c03442005004081d4aa006020420711902e066070410082da070000c6e2100c04000310716542180f52808248580042d401c002004a080650b081d041402e0f5940c6103a008142c140202e0308d00c0c0c1949d00c1c5644202400c01c11510b807800840503180000385e01c5041114103042011405116400c0602032104180c14015140c20b140116030041c0d404400d0380340c01600c119290400001d441004900580d010f450000721640c104081e071607401203002c181c032550354404910580300b4081c00940000e002e5844007044483c10034102000800c51020b1144102c480b541001e03080c4510054115114481358120b10740142040044400007440050f0300503000c88000959543c80c207000d10301449002e0402941070240c1402d004003240e102043e255044444500303c000c01c0c04100c101428110758416139402c680092140e0306507076000da0911458200021004034120041c900054226800 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 630230827 1250 630229577 630229619
    0x50a030504171c110301030c0308030403170a0506030c041509091a04061b050406170c1e04050f030601050a0b0c030705030a050d0f02030420310e070308090603040c 72
    0x11040f031901284801d009001c4000300101600d459941035440700b4190040c280000b9003481000404201010f1080003800484141d45905800d1420601d4180b8003914060f900c16100b0b1080304604040352800c0e10610b0030800c000d054801d600c9203003464100c050103502900f904ca0040d151110000b07641c0711401da5101e140b207280d0002d03001141c10b081c1416000703042005010440c00b44024000c1541042c3c003280c0310301401c0b41020140d0385107100c0b0080c0e03120300390a01c002c45450700344100b4000b009401030304c2601c0c022030341e82ca2401d0fc00d5003810303642c91091103500e5002c13607428401c01c4401000300051044049140030340c0d1400001e52601c5e840c660150b03100300002500007d800240042e98860901d4161444d032080d4650700301906c405a038035201c058000641c0454415400c1181e82d030750154840c100c1070703032406481605400da40d0724100b00c0c015100c510b42e83c1050701c4200605d03408a00c40c402e0340e40c040c40441c01c0003103020138003005070001070045404000100000c58116418481c032040500 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 630232077 1250 630230827 630230857
    0x9060f020409110408060417160f050d051e030603011104270e101e0c18090b0a06050310090e0627070501260f0906060907050a03050417 60
    0x8544400c200481c1e44400f1003030500d400c00e00c0140300c00360010911580013030f000041545540d07805003000c030507403107240e650b0284140c202032017400b0414a051070700101d0340204251003038490486c1054440c1c3c483ca4203d92682d00c1c030503962020928503000915000b08000c0d00018541c0c4080307006025030381c0240c1000d4504600c03085000040038100b110040603403002030003408140c146501035590b030540708401d2402141c8070102c00c503504a040300d52807601075103684144002c5c3c640b170101400390200303075440d010180c010a5000c90141124000d0701a0410041d141429061504d1400c641c0c07500007a180b82c404490811002403414142d008941c0c440300b1100143c00542000d0312034640464100314082c14200c2c440f9421480540042198400c0f22020708015840301e01001c4042d007405170400108154140c1942400011080e080c0354500c12882c04042702d0f000e84a03001040f110000031190040011010401140e425101e5002260440e116558048280c55200b100303142ca500042070380714240c8 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 630233327 1250 630232077 630232079
    0x60302060c151e15030a0804061709030c0316030e0303070809030c101e030f05131e110d140a2114030105040908040801020412060e0610031509060f0204 67
    0x140301c1c0b10a6900484102c0b521040c8034001e580400d00524028090f005000c1c60700d00c40c1c01192000e1110602040d40440110340c0c6070340b1058081d10740411960340c6841581c0140011324640c00c008211810055050011410416072005030704a03000d0420f003c03410010030039408085610100050424644103688294858070b805e8103051910782107001d0b20f84510707003150340f034541c541c1c01c040c3c40d0010303491310a205050a4032001d011740141c40d140c4407201c0e0381407405041200030030343c802000e41c100303115510b02c014203001c120541100041140018109101c04044d00748036180404a03103110b03074880e50182c11604102c0d4080340c180b0040c428103607240707007824080034883c2c03e0000008400b100f0030b09002c203200c007203101c04400502050103141e0140d55078117551070134054500107a400410581000f9945c8a480710440303203124400c4002125031500b81030305858404004910399111f03181c40589c8d280780519580315210784c0890182d01240b640e6444901e400811028040e004500001c6030340980d0762 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 630234577 1250 630233327 630233353
    0x7051b01060e1f0509060f0d0f0201021212010b0912010903080621030906090a050d0c0303080a060501082e030f0c05010306120f06140f2406040513060302060c 70
    0x41c0d44000c1c12603c2d481d20a0048841c040342620404013a02c1c019518416642e90f03002c046a4042502c0d0f02c034540c42142840801c1c2080350800700071440038401c0c0d084d02c000d6071403c040364280c1e01440c11000c40f8401024014818042190060308020030010804200c50b05551000d40c2119440c000540004105804001f828204205c5200d200881c1440c802600440c1d0760040781c5038040c000380f962158600040f400f5031907a90489080207032500030001c8003490314520306144503811902c0110082001c1d0130001d4250100784c0304420441c0d1040c0c40d07140c01c030b42e501400800f40b8842042c0c0c260f2040c0c0c0051103140b5500305201410003543c410003001e0708030105418550302d0b16840d6440326041608005e818001c1c3d4002c0c03a280204568080c0620301151517916210003d8040f0f9240b040346218038004001c0d10700440c81d0000d014114501080d035100a8000f2400948500310380c0294019401b080100000d01300a2800c3c40c2c0c549920100044c030640325800100140c0c428003031082c00da40402510b16203 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 630235827 1250 630234577 630234599
    0x5030702010b0a060203040509062707080903041a030603151006181208030c0c06070c150c0206010b0d1b050912030a0e0603040204020d0c0513060908100507051b0106 73
    0xd0004201d490002a0307181c813030020350300d01c500c2c09514091440c95022030060b40310042c0010340e5208015580700c50070f11345040d054034a24121550742c00242480081208281e020044030b060b503000b040c0c0b102200c40700500d40441640094603a0307400d44240074a103280750104c840ca0394062280b500f060f42071945404002090000101d49014a0840214040004010f03140f1064880c40e4020240c9843e1740e5003078190006c6018000c400c007150300444042040b0160303c000350300c00701445509422a0032001c1c1039014100d030906000100540d10040041c00307071480c01000b4250303440781e4007400b20315000d507078120101c03290300d00641c030010401c089025510fa26181001c44c1e1101e00d080010b6040030f00131007008103404481c000540c05048000f0115041d0f40342d60301154012001380405000c0003400440080807a0701085012881141038400410713110321842d00001203410020083c811242c010320000010903014140300c0500904200c0314081c0d9a60f01a0b0b1a110008403000103000c502c0c180f90740708 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 630237077 1250 630235827 630235841
    0x70f061a0a080601120305120a02030604051f05061305181b0c03090402070204020904240b0c120c0705090c041406090d0b0a061d150609010503010909020303040906060503070201 78
    0x44a05601d030001e00c8084000101241141c441403461040001103090070740c2c40b07104a10504071901040070810040140030340045010f144251803c0005648541d0a411029007000410003840c6100104001c64078010020345110020000c00c1140140d456002400303240241c031042107800260010094403805107141c02c03014018015100346025540b03102e21341c80e449121882442680e0201d850300071740d106c0e54180c40042070042c0c0200000244c4100b4003c1100c20081c030740010017220070000c01c0d5203041e20f06a5030004400d800404001032441551324094000d8043d500082c030400e000002e00e5510b040d40603014003a01e41c41d880e5500c1c180755142c200c00000f003528038016402044031008585881c5146154141c000004200d00d4071012804409010203510481080900100c0809400f070b006a540d40104600d1034203480380354504051102e18001c01400b90f012510500040091041e02d4008800240c801002e80745400c8d114110717001100c903660000c00000d5008030400c02c0342602441061 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 630238327 1250 630237077 630237079
    0x905150a0f0e1c0903020a0b030901380303090d03080c07060227031902040c12060b040611190209250e0405091c11160b0306030d0c1e08070f061a 64
    0x54013a41543c0100705800b4107449903200da0240000051a58202940483c120780c00d00d0000b0305081004001d1400c2e03c02481d01201c03c0c6000c1c00802900c0392a0010440710580340141104400d6240f6840685501000800c40180d003181088048001001403005164144900d01c41c202009441d440c50788048074500d5006001e64008020301d4040d8180c045440819541102c010500045602080b207914054581c0c1c0c1c80500d00b050400300781314607004060004e451a0b540c444d060842141e001c00c0d610307030049080034601e01c250700da840301500300010440da000c20b5982491540d0b030240d4040041003405000c2d60400030b00c6511805a542c075080c000c10b50409241402004010048043c0001d07007000140072106001c100101010011400d001d5580f0150a802079007a50540d9109145032030342c0f00b00d810620900510b503100300e10500036a90110341a80148000003100102c0c241000506401d21058a200f0300074410000040c0c024081c00c0e441c1c0740b0405c800f250080c5503071308110302035010207425 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 630239577 1250 630238327 630238337
    0x6060914030604060b0315010605030a1401052404030807081305221d060108071518090b010522170307030507020d020f0303040f060e01030905150a0f0e1c 68
    0x100956000900030f03401c9a0840c900060180700040043c0c40c04824007040c00d407800c450000000d49980041c013070f51040342010000d2044481d05500b44140710b00074002c140d48440200b030000102801e40348207121140043c000b5500d06034490310703882219000b0604c100e958010024000d0b1259403c12021001080141c40d40b0121124200c000440325182200a0b08042d40c1d542c542041001684121013044214406540d00b40d40c42e07025058803881d0038011228040c88000d5800d80c003d01c605911184250007003090200c850070b02c44d4420103015a9540c05042000078021b02210003000400840d070303450702c540b4042549160400380d45506101652514894100344841c03070109070000201e030305842d411518211030b2511807000400c0d4100101400d5010700c070109011885c0c485041104065401a4495094500c085c1c0c00460607600c58000c01002078012070903050244415840da41d4211003940d0001c0750800c5800e0030003003211100c400786101e580c80f41043d00044035082d03c0c1d80740950254500 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 630240827 1250 630239577 630239609
    0x150603051018030e030c06120f150102120c10050a0f050c210406110c0604060e1204091a1002030403110414010e04030201020d0216031b051b01090b0409060609 70
    0x408840da060300c002c0035062280c554642c59496030300740803600300028024007594680a0802c00d1010100088807444003c250f80c8002c2519020400c45182c46500c059004140e2056040c0b04005031b500b1038201500b05104410210714a1074540c01040d1142002c402c0010384900381e02c05c444140c03030003c1c0c0441868034007001801401101424804101c80d2901c160580c2da407610b15003c00100f0940c1d1a61303601c0500030404190204002c15618017450040304240301c00f200b078861254585100c10b40d1184500703c100b01c10020041f80e60000400101e520041c00b055042e00320106010343c12100c00e40e03005810002e414005c02c101803100012149040c0e07020001400040c03980120200d040c01061102e50f0380d03600203804c1603c00d404644101e0031510041d5207a401c3c40088500d1860501001c8022035006030b80030381d030451001c8022042d03070b07080801010120039403d01076640641020101f030410100760000f04103810700c240104020000f1960000d0307401d181400090490307644e078004035048852148 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 630242077 1250 630240827 630240851
    0x90708091e1002091c0f021009050d120e0a0308030109240509040c12120f170a0c12060806090f0d0e1302040315060302030c060403030c1101020a1506030510 69
    0x107420b2030308924003500583c1c8080e22800030340c503488019030024100300c4018100c000c002d620300205446920130b462810403000c0c2e140d0260754840c0c41c0e0041076040004400c003500851100c400440c0c0b42c48407800c00409480302074000c9404402107410a6506980006c01007291420302e00c201e061080f46103d0300e40034520309032003000b604641403281c0c500c1440b208000c507041c001d1400d00007004041c0038801e0801c841180ca032200c0440e004850104c08600f48204440b10030380214401c0140710f4a921801045945069484e4002c00740583c030721082150068400034101504e03c03039240584000c000900307075851304c0b100507403030700a1081030b148141c0c20401508a0541e0080702d0071aa004044403070301403001c02e400454000707000b198400380400c054900e9441118003682e01203000e0300d009800307641d1115201405d1203481d10441c0b0009000820850f8103034041a008a00300920b03400c14419038412501a80b00c050402c5d0580c0c1c00c0042c444c0ea42c4c0360400c2008010050005080840c1b01c0a21141d01529 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 630243327 1250 630242077 630242083
    0x30603050307080a140c0109020f0d02060d110903010e0601080607020a080720040f0203070f050c0c04271b0801200310052701090902090112060209090708091e 70
    0x1071000701102008100c00c1030344c0f40582c0b070529100c8000080c2c81e844465841e400303406088221403d901914a1203800300715814000301c00c1500a402500f19881c141c0845c42c0c05005008a0005192070201408030415960742030044840700703407010780185001d5040403815801c006000e49080155030140c14035400240d440d909591500750400918410000e440d00300020414482c48810b0b44207107031490444011101d42e01030340c0256004c0d03072440b45201c1c8541054400e441034407000d01050b842241d0042480c68160007950800700c40401d4020b940e032880310800300024030014100d03180038600e10800700e0b203480c2208160003010700d00028030050b51098011404003490080004c8000030000024455052800e9a14000c0c1000340000c6081c0c0071900c8455120202810310f01200c0b8240d0000003068200d40c0101220140c0051020419910b02012510f822800316000c40f6865028848030704141d8801c0c1c2140d04c07945581c0c0b90642c01d4a2300c0001641040f01c201481c580582e441000400040000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 630244577 1250 630243327 630243337
    0x12030909040b0702070305070f03050c01090305100b01090906090203090d0503060616030e0d05010609060605040e06060a110105011d0a020310031104020f04470d06080105071106070306030503 84
    0x485070410340d54554183c120b091100ca40c0000d4200d204042000a0080c0160b1310b07130b004c4034000c800340c4c0e041201c0e4000442700040300b8800600158488540700705c2c003959550001c0d03510101410044125035032007018500fa02d1880e84000100c540c04020004034a0046c0450300c5010802d2400c1d80c070f9450300500040807070040a4a0700175104176403821400f0136020b03a030004c1c0180c07401401e03444c02c1c0116103022030117003a190041c02801c9091000000c4c01c0740c0500c0c02d0340c040c0c4ea00a01160880e5803a0030910400380c10040440003003010302490240072a03000c1c40391078064a040c0b9800c9124160b050031664058002900c00c20704a881001005100441411041c0070340340d0015181000d17825410010f400f074001c080d40c50485030f90010b0b0010745284542c0f01d100c01801e034642c80303902d1184c040c11285a441d150802c1a15608490301000c0c501c3d0021000401070ba5254010004d0403c0e2161100c900315541203c40c000411078400c01d10500c10000c001c41da80c031a1452405000d850700390760380ea42e164090303 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 630245827 1250 630244577 630244583
    0x7080f070c0812100816031203110408030901140c060406091b14030c0d03050d0b0415030501090c0f0605042612030f0703060621140a0b1203090904 65
    0x254008142400c0c441c1070358800e5603800c82c480365290f54101c84a044a040d09880740c241d00800050005031003400480d0750307a00c0d41d0391682910143c914649a5028501c0790300003000415589442e403811803440040079201809071a40216192a0b84000141c203001c540d0010784c9040d00e0601101840203400a00c035036110340e00020205400d1074500c0c1581c40105a401313140c81c4038040d000081043c030015980d00d40420002c40c211a1144004014000c103425a0b81c001b8000943c204040b15600c0c21a401014640b170002e0000030b0130304101490340324040040d8104960726510b0702c03009800d004158980030003030700c80302c1c4034480310619203100604940700c4c3d4860600042070304219140745104161001c03550243d50010b444c101da4641401100c941d20403501e40342d0401c0010b000c5007040c1c1c407a2095100f61440c0340c80784c80f82c4030520a030714408030b40c3e882443c0362a1525980043c0414040d218458003889440101062048130001088410100f46408840a90007446140d00756641d03800311a8005070 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 630247077 1250 630245827 630245851
    0x30516140d1a0c09010905040b01020a020907052101090c11030a030911030601080102040303080703091a0c0d1a01030c0c1104020702061303030e0a08010b03060406050903091f090b030708 82
    0x24280b4010b01a1590000810014070340d2070100909100c91000600c0c001100366038414261740c0b5103003080304440c0c500420301d0050780000440070050501c5c4010700d400c90501d003040790405034400402160181c86440240104d0403c100412121007240581e03022681582070400029034080f0199540e805690f091301c040548030000b4209000b200c01e000051281c029055890780d41e100c41d0224007035441444114000b0751842d0010b01d48510903c540e140300c40d4018450240451400c400101c5c0351400b50016400101c1040f400510104d1445549403031f00b24103007a141d1018442c800901154030f424400001d100807a030b945000101d03031016000d0295002c840043e103680d00f500105805008016101501c814120004828182c000e032640c200a0300c00c0341c00310b07502d903140e2842c207080e44c40d010801905548a0000301d000541150805030317112801000703d0341052000c40c0014555600c03100002102c0589100d11014560301c45905006018440b404510b03600304140c0007007110702e005201000d480 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 630248327 1250 630247077 630247099
    0x30e1c17040b070803070e0a0b03041203110a181d0610020a05030a02030405040f140a0b03100c080105040e0705150d15060503061f1218080309060103051614 69
    0xc0091425a00a049401d01054070b80c1241c0c03070043c905901c1030f51544040380b829488201189003640c2c0345002d0b5126245c1c00342c02c40e00d440d07803884500e07001c039003030704090640b943d85a0648442201c0035050782480c0342c1c1d0310400c45245414507212a0403a0300700b821010b4003080e030640c2e020091244240c0100007616403955148100d241207040036801c890007000c0e0300000402d01000c960003c05401a14001c0b0b07020049094070002d403604941d403d00342551006200c0c0b0020b607030159107070700c400607800b406800e1710103542074403448000700d0724013015410220742604014016414584a508501104007008004160400000615020500000c0740010074000740d0484120b40039003100b1110200e036803d58a140d41c0b11800030b002600102c8215008452001c04159625004101e07500c583c902c039128080b0380d0041e01c00380c2000d00304080c040e42480008034000740005013907900640c0720702000300c06069075505501d44903050410885802541a031489000d02408000c0300e05c1c0d1210260407a1031075816 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 630249577 1250 630248327 630248363
    0x10806040c1b110901030c060905190b030a060503070b07030e0a03021825120c020607081902120c07020a0f050a1502010b100207090b0a030803010b0306060706090c03030e1c 76
    0x4981c0c0c041c0f050300305501038000410441d07603981010584255488020996440d1818843c40510710180001c82c8900741c0410014515600011a01703c40e4401001c900c86c3c0d00c0707002013441e04041d940141c2c0c0c0303050001201418194400d050b408034640803034072140491b00d560009a0300da078900800b00c50700c00c4c0c00e10200e619812185d640b0b25440e400300e1820500d40d480184050b0140c101421014003035810140c80e01c210520104240e0f104814030703103588041d900c525403003071040d4140d14801c0c1c0401d6400c01c44816805000107006210756046148695900e50601c14400c20100c540d100300001c0c0003085c1c091041c1d0359002e134444140c42041b9452045e20b1580382c422405000d640c0c100541022810807940a017030b9000ca0071405480d0b083c0c405001c44c20b002400d024280b202444082d0502a040c001402041c1c52240156004000102940e0030001583c45410440f610b400080340c0204030b00350b0410030150064900b83c0c00c184c040b6005101d441c801d42c490120f003107039013000421026018030f6001e40 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 630250827 1250 630249577 630249593
    0x1d0715050c070306050402010f02010c080106050c030412050c01180608240d0506041704060804060b01090b210c03130b0405013e040b0d0906110309030702010806040c1b 74
    0x6211030790084454080e96810160001d00003903601b0b03400100580107203e802e5005000e01ca03d5000d0a41c0c1d0f118040c1c4c44c041c001c54464010441e2441c29001c1040001100004a42c40c0b90419000d600030b05259544100050b001510540070480041600b020412150307801c201482e50010016a048450250441d1081c081011120f1840c2c2c2c4038040b401003201f403003000a01d151041c0d12540b410031030340d0200903142c0b07594029445400700042d40d4500107030005101740c10030070402c20706040c030b0074010340c943c00800f0030742e00b21055662360046441003003c3c40490058800d5084161102030528500341200740c03020390058044007800c07150416020804100c0d09500001c80143e5030880c0483c04203103400205070300e0781c0368450303074034446035544506c500307616524111012144c540f01d1083c03600e801500308402034110300b00161072090360f41c440b47d60340740c054000440c031540c0c10501859982c442480050302c0c040300a01154029031404c011102c00b6500001104040324080c4010110b0054610381410 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 630252077 1250 630250827 630250837
    0x7030b061c0605030c0a0810021315120f02160201110304170a060614130b0316090212150f09150306041401050a060605030a0e0a050a0602030f0c0a09180b041407031d071505 76
    0x806012040300360010980c0300240c000840c1c84cd4009000322007149483c2d05c2a4041c10003c0041d0840c284040001507000300e1514038142c0040f000c0d0390600795104151025070000c1004044940c000f600703a1010020b0b140300d085c0150555001e0340f40c0c1d5150307410100342c040d0400c8420841a0360ba8542145299600700309203040d0b461050150040c682c0c40b101c00784042d42002c1c0c081c8500114140224110358541000d007828941c2c041c000426038194902080441100540541040c0d00c0f05c00d0401d2841d00c051206500c514028002050080781d500e1003d0f003156001807140640600c0c00501f8840d090303215040301d800c03802ca03da000c40e0050324032003001e05000514600500c035104000c0c0c10800c001698014522aa00060303c4c2c001c60350b02c050b004989407090f00194000118820000c0c040c1c2440d40382d185000003440130300040d2002d03410000c0b074100c8007a03804210b1020f140d5400c200d50140c1c03502a4450080c4106503041010000c10380c6190383e09036500994440f8610140d002c0d0300300d4400d01c190b079 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 630253327 1250 630252077 630252089
    0x2010f05091b0a15030510030f1101270506090a0503060103060902040b0603040f062c0a05060c0c0c090705070209180105150907030b061c0605030c0a08100213 70
    0x803140c240207064903a074001c01e40c0c45111200034141030b60103c0ca01400c841c2c04660118076006880d46541c2d10032001400020180b01e80800b41c2000800461420f80e40d0180041c030a80e01d200749900e184001600714078820341140121a00d071450311501100d464000320448200382c801d04d0300c800d1480c00040c54601c2a07000542c15104502c00001404000e42002e92158000c1d0740420011284030180b14041c0700c2181c000d8168014445280c00103122680040b8607196400014904400d0300340c101407001c2000800d5900a50205502c401030044c2801502d410904550f41d01c1d24010400c82080d490b40d0581000c20320401942d0000741c0510301443c21140c403540e000300300d84058a02455500c4c001810325031000d00e950b2030000099400d103001403011440a5000303114030400c0e41c03001412000381c40c5851a864000c6814844180c0c009800e08101c04403042d000c4001c10803a0810b801e0610b007811195080740f04075103102080010b050045a01c10050000400140e69100301c0060305010445940c40a = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 630254577 1250 630253327 630253331
    0x103051b01030f02180a0b1e07080409060b03061801060905010507081612080a0207080f0903070e0a0603021903020a060f02241f030803270f010905120f0f030702010f 73
    0x4038440e810702c9407400f403107200c21a45071140c0ba847e000c2c0981203000d403110092648a070b24820b8108150a03001500400b482201e2440c5480e45513507c03801a10100c1c0e01001c0c0c0340c030000c400c3c001546422201c000413010b01c2241018550700d811030040c510910761007005e0600c1760010300d500600c01c3c03032030031102100c1c1c1404008070806424500520642d4a0744600700003d01150f010403400a6680220380743c0a80162041c2d00741fa0664807068425805208102d5040c0308406000071581d200b44241c4e0300c01c0116400016405181d40140150031075692000312012203104170600040c2c0d1031084201c2500d44d9440d24104200500c1c10a83c98a520f00c10f107801500444660080000e01c802c001ca4400d041100e442504c5a8003040112101e01c0c0e540002001050140001200342ca6415034807024500c41543d203810801d03003118414285088440e45202d6070b5100c6040300c0501600b0841e10304050a0010104d00d4404020040c0c066400b4031281e528900d44000045a0803902c01d410070443c01411603c1 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 630255827 1250 630254577 630254587
    0x90c030309050a080d050f090102160303110c0301060e0a09021903060c0e0f030a060b240c0708060f0417040510110d030903050d0207020d08030f0f0f0103051b01030f02 74
    0x103060744030944036191051030680342c0403843c014041007240c450021500d89908000c8040d5810203590030201354641184100d144031a200c61402034040300950098070307004849104882054203046105240c01d01036030421104110075014501c800b54040f02c0c503040043c030302c0350b588001a0b07001315402c0c1c00f00310448500008000c0c001240c0c0242ca0b4441542c6a4111540c20803041c440040c82541c061030349900680350420104819821500e913415005044c45074101c60740c0c25280d02030416614041845102003040c00207103404004500c00380c00d5182c02440181b40400c03d05000c0900148001c10f02008051140c0d2010b51100c1900c025141c02464080402c81079040100540000004a089845010044c040041c0a40328190303201c3e42580e209444e1150030010171020307520400040381c000d214070840704040f90401c000b031401160030071801e0381141045070304010b0901001d003c4200c841000801000000c00000741c401513811403050f01c24100140d440103900a005200b6040405c41c00000c0b = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 630257077 1250 630255827 630255833
    0x20106141c14010e06010603090809010c0c0504150f0603052401021212150609010207030803130602130639051f0e0f0303150d060e011103041e110402070501090c03 72
    0x214504013070300801240c010b681d840768105e041d03802511000d0000d0700c0800c2560b0441d485038121400007402003c58200d52aa510003160031921110188007415150327600c244003507185180384100401082c5001c0c0800d04011010080d07050701c0c1a4881c4074618a005900080e0340207001c2c80e032086850600140c2c07541e8130701c088201603800c03c4a1010f03100310100761210592a0a105880c00640c0690042805606664464000c0d0344068691466032001e1110751000a1007400200044551a10b01e845e00364605800604070800da1100480780751450110085000300d004251000f25500d44001d1040a003141042c60400741802210000882c0070742c2e01032440c60154000c2102c4031039003001c0310031000c03c90000e5500c3e404241d403079030301245040d001101c10b440c2001c0c54100c100d000d4040001c01c004810380641c00c40d6149105503041d5180803040005000b0321a0301000104c1d034002a070a400101da980b298449100c0401440c03040782d001c202c3c00240082540f140b400103038003494840205446c2c0c2 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 630258327 1250 630257077 630257081
    0xa02030f0f070f0e030c030a0807050d03050106020a02060906130f0609060827031204030807030b030f060604021305090a0603060507020307050604113d020106141c1401 74
    0x45a003500c003800d038000308801250448003944501029502d8440960461070110b40b0244928050740d454810100c541c5c03031999003400290907861081d080d0946e500c0139454140d00f0708070b500400c501814a001f0040122507008506c08a205504540c01c1ea620010b800c0020080d0195802440001d00c1c0003c0100380ca01d031b040069000d070b0300d840d1107125025513180c0044410300c90403598a000c107035560301d14402e200b0800f11120005059403041d20704029440004c1c1d00c1c1070f80110303020360018120380e050040e42d5230144a08550100260090314103541c0890310640c0c0c608010b00300c81d006680c0064641c0b582105503c0000180c40d00501200c2942461401c44011700306902041d03030091b180c440480d19240c0004207c42d59150300074003a0030a56201e8640e551003242c0040d40f00d40040e007590800080000280e0707514551034540c254184441c804c810a00032007910754081c03006581c034092080c84180e50340b45841e45450812254091004260003480740d400700c1c903100003000072500700a944074100041d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 630259577 1250 630258327 630258331
    0xa02010c02010f06230d12090e16020a031812110906040510090b1c050619022118012d0b0604060509010e150403051002090928050a0203 60
    0x40c0d0003800580c00f58084601142c200f44642c158450060100d401c580d0140c0305a9946040010048400c2044a440e01d00d08541c4c18000100098806c007011320003243d15216554026551044000c000345440c84060b5854403040805814841d1600401c442011400354070342c05800240341c501207843c5c00e450310003950120b64258a109a03004070005140b030070a40704240c41002d0624210850358038040b5a5401003482041031a080809040c45845552190001c0c8d140079200c3c10080c805071601103034100c401c003138001c0f41511031030040100702500f0080c00003481a01c2c0904468040302d440d08092962607100800106e580341d402d04520102c20405020113144159a403444c120301c0d0b070305002548084440c4030034078550109003404180041803041010b4680120f041c10401a0000c0d4400020001113200c80c0c902442e0134005401d00c2000414030400100007805d00040d82808107100002e43c100318014014460000d030040a0100340d0144422080b480c80c0000d03080116041c5458148003075841 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 630260827 1250 630259577 630259601
    0x130f090f05090606060a08070e0612010302040f360b0907080f030906040b03070c021f0e0f0d031803060f0501031e02010f081008011b020d0f0206040b04080d020a0201 73
    0x290000248502c01c002c00c105209039002448585014034410041d180d85070090b10b400200407800100c007074240c852100030b00525020f01d280c08565851881000155100c0c248181c2c022801c06125204000403600e0318592102c041411a5440b451080380d100d070030800010240c82c0003103020521003000c401080c1030701980c91800035202d80d0050940680e549100c2c0c0300c50706401880c00c000c10030607000d402c005190010824580150764611540006250185500c105070305c2d013a4510f4070112485d04000c02d40c120280c180e440c004580d10900000d1000041d103031026040c015070407503004030341c503014900c00041c56105204200001040c404007000700400d010172107006025000ca4200010044040d10a95038160342c6c6e0b40c82030404007000c0b90740c00005049a24a50700c1c4400100b02080d0078050100701c60158144642c010200142c02403130424034251050034090b00e6210500ca06a02003070140c0c0c0301d13421010310320840e2140d00c3c0815903032041c90800c0b00ca451011a048182c03981c1900410207000c1e03 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 630262077 1250 630260827 630260831
    0x1203090c01090f0b090f0409050f0d030e0a23060f0402010f08010305100c09080d0e1905130c0504150f1e020c1207030b0c0706200708130f090f 63
    0xe8180054500202a010726400030b90b80b001c08002ca441e02d0b01c000d100d1141c2c00b826241402d5500b03004541924200c1c01e00311495000b4009040f490b110400c4401c840714081c0c6018040304424606240d03d8404140d005440b84a62101c0040030140704145032100005210440d0101d14181d141402089000e47c2c08900241c407451600a405129612080c10703079030040e0180c00b010401905000090480350b44040030b20060f448000b9401805001c0c94070240301d99260811301025000070000420308080c0c8440342118540e0061009850b8400007075010b4510101c0001c00c1e0104080c00c2d00d0500442d8400c42c40e8021490281c186264083c0e4007401000d110341f0344102091540600711105400b40f80108016031100d11165217901d481d03115160b01030803100507250303c207480c1d031110010302c00200d1710030001d00d0b40010b0f1a000c100c3c2912621500d41c00740c00790b04014400270310b22010307039104482e401382c2180c41c0444c0c1c004003c2800708005004100c41d80240c0d481907070b10a0401c002d480140d0214080314 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 630263327 1250 630262077 630262093
    0x1d0d061a0a0e180a030f030e0a020312040504050c0a080712020c07060c05100e06150607060e0f120c0d120b04050a0507091d010b0307051201030f330518120309 70
    0xb180010403500c4181e02d1b07100e04007441c116240807401801410300c1c60499208510418000d6203085c071403680c0750158400420b64450510b410b000986030040c00c01200918200500c0390380e141d0180c80550045082d19068440c40c01a8507040040d000d8001c51407424010000c0004029800034841a801d51044d8296440002040850006c684000c040c04845030004000981191620b1051850643c8000c00c0f590030141d00340c40d42c030116030407400f548207a9805210142c40945080104042d02c4c4c0c403000800d4500811034118039101e01680e15090244071444018111580003a005086200b0002d0010005407a05074201e40244c172081e5071070008204c88080100e00c2e5219146d81c1e000c07802c50343c08a0360440c0d2800c2c000600ca580020804002c101c0288131220741c0c00559215180258040d03401001d006d03101d07040ca10207480c0080411102da0b03030f810b002c06048038100315000003d08001c4400084a90300c1c083d07141da40b505c1c10b501078111030291500000402c0b00c400c0245004542090803148a2 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 630264577 1250 630263327 630263371
    0x100b06090906041d01020c0601080610030c090902150c0601060e18130201020127060f0b101218030816020109020102060f07020a0804060f1d0d061a0a0e 67
    0x920858a100780c00c0382000c80020300c1c505050304402c1c0b04408001d159014200c040c0c940a08a0700581000d1949412400c01040708505c00c110031904001d0400c081c1c0011450341d500d012144d18144540c90609440326810425541c07000380e40b0243d40c258044450b942c004c10740065840304003d0007414003280c1c1d190b113400f019045c20000e0322030700040d002c100c044945a540e44003513104540001281150b48810042802c009401c662001d5140168004144aa00d919154050728040780301540101c0c94620600c0d5a5a1070480d4018260101d00300b44203035120605006010701907001d400301c0500a0b02043d5030800d9807141d1074130300c0760202403004030b103106807039400b01d080c0c0f081c1e907102030b00592241010a003868040c801c280c0c0c00c81813038011601c05000c10b0340c0c0e10720340c1e0300b0030752201c0c01054030903002114103500300c40081c05c04d181c080694807000b05000c0c000350042c083c1c5000504a03e0b9107110825501540100f50390710010002c003106c8130a5500c2c54280309001d022030704140028003800c0c2c81101 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 630265827 1250 630264577 630264589
    0x31b12181306080712060213181b270b03150112050c07140f0d030b100201090206031303090b0705070f080a030905132c010606020a051507020a080c100b 67
    0xc0d00c001c0006484138520700b03691124416560300c410380304140d00b0444482010400f4044034000c0c40304c101d00312510000c4401b0002101c2c9880c00e620284029810030312103c40e4411350b00700f9011903424070008100c03000c2d460706000c51700d9500318248041c40001440801e807003149198041440036661262007480c42c0c1c107500c041d540c0503903280c58a00405c0c0101d40c00254020301d800c030f0780003031042141c4508402c11080b030714010707038030300800d01091340d4141c072965034141401102e00e150042c0c00280411401680410442d2000070b15111942d5500c0104600b0184035014404c0205a8440c040d03841d808a814081c0d2034440901c42c0d039803416011400092140c0c80801c0c2001650780648a040710b040ca84800e105143c0705456103ca03d441c2e031060781e80b00b40c070b1143c0140c000c0316141540c0030200c1f10342818006d0031a6610f401900c15507120388102d00c0050310014a000707021003100001703c09501c52140691410100100040002c0804625601202c00020340010b0b4000d2410081c814040300c8024088 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 630267077 1250 630265827 630265829
    0x7050d18170709020c10050a0c080903070512180a0b040602010e07150507061e0b100306080615121905010c0903230c04060305010e061602031b12181306 67
    0x1c201d0704800c004214420081d4058968000000203844504d2210b00e40b4904503401198603035003042e81d0701d20204e08241c2c030080046e03110a011004524010581c0c40d000e550360b0100308860031940000501002d80450102d50054000000e04401100d80d195034650107030b90414068a40150300c1e0008542c40c440d000944034044a800c5150079890104002044071543d1042c030044e00c429468401070700e00303040c944040c035002c603d0f2600c00117a001d0901040101240452000da41003600f003101c2800101008644190081d00c0100b882e0176810048011644010b0341c0d40c0b902c80705c0d00580c049400580b02d0346504100c214403800c001c2212080c0c00c034090303805034150f02010b0030741031031a0300d00341d111110712880c3c26030042d019044504141d08813001400f9100c1a030011521a51207510501c9000010440d258002440581a07a90000d1240f4001d580340a03402e441103100301081100042d581d02804281d071100104041e080e51510443d240a080b020000c022070701603040403a0b0320603211043c0c49018 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 630268327 1250 630267077 630267119
    0xa0c05240c03090a0c23030f0d032c10050708010b03060405041a07020f063d150504080c0909300a090501090b030c07030c0807050d18 59
    0x15960320303544400c0801d42c0000700015060b1065000740004500c40425010040800020307044801c0084440129814880c054513070080e0b020030300710381b2071841c0414540400115441d000503032140c0d00c2980f460b8100e40d01407240514801c0c0c2090b072500766012842d54180b4002d24010700441c0c40306001100e80c48400d02c00c244a24038148041070180c0341507040710360454062201c140c41e100c8207148440e04208261014005a401051240e14008050182e560300660300b11b034039107800118811600784100c0d140700425040b2024040c005000581e00c6181c030241546200c0c030f03064403144038005071032075206000c1e00b5500d1003a03100c01c0300503107081858240700f1141100034000342603803581c2d10b2103403c030701c0c3c1c4020400341c222500c14620b85100401400d03a088880e9101c1034101d103040c0024062034007680104540345403c00c01c208258001804580c40c003a032500e401014158181010006400381c0385004105000e0140045955039000200200880d40e1400b495001e070380d40c02e0844540d00c0244008 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 630269577 1250 630268327 630268393
    0x2607030b0a080c180c070b18070816030f0c080102030f100e070e0f040b0909030d05010806160513050d11040e030a020a020906011107032105090f040f060b0a0c05 71
    0x51500011681c3c00e507900107005e5000c40e03007000050f99032060101000c07103140c1240b549810341a004039400700304010044c400c00c80030700740c400c40346c0c10140c0a42e0110300003d8842c030b100c0d40c013402c208080c04001000422905008548a0802c000c0c0782d044100d041d078040c840d03000e41510100310f501e6040c520b64060005600ca41c0360300c544003000c3c0482c1d0725030b070400c1c907a1003591082501400d440e080c1c1c560740729580a20203140c1d540c0405c0050700c221001078100500c00e50285003041b0f884801301d1004180c03e0307074904000d9101c20103147c4007400241c4c1600181c1c0c1041074901890f040014002c15002414002c0301c092041043c04260a17a5034024a98a00c0050380060510400f40c10042020f903004407061600002d0000d20310b212501d80080d95004688240c0c007080c2d1401903020a003003c2042280e00c3c608649042210740000d040c2c81c0081ca0b40c40d02c03c0e40d45d0389107440010480e9000304010b0407640500c5031116404840982100321a0700291010700170803030403115802c410441c44024400e4804c032 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 630270827 1250 630269577 630269599
    0x31703070219060f06030f061404020a031419051c02160b090f031e060f04020604060509011211040e0a090b0403140d0603060e0c010f0f2607030b0a080c 67
    0x200b500c0100b2281a2200e030b0b0350b01150461181c050060a02941c02403545000030071103841d20208a1380d086010605e00283c0500f03220040e0b444041410440340c10045a044651007400f01c1c0e8141444640c0030801e1710400c1d00c1c2a0308000c0d000c652480c201503410101070051100803410303a240c8080500000b0b0401c0ea148060201d207050901030884410081c015100b4541c00b400402d00d0041d0b60000102c90100c3c903074001c18641403c0007441da1045000707855054904041d408540e20b0301407800f4440901034003041035821a403090b90350702d1401c541050144189000100034100642c404c0c082c0e2031803521070344005104500c060060018260744100811116611034504034ad4000c2d4542c0c0750350b403802003008400a040303560301a25016500840000507010f04905500d80340900100400c1e05000c40d43c03044602032500240c40545801803802e103080303410010f10a031810001094940d04850107044240001e403503144d400550381580540c1d0b540c48013034039110661368840f00404100d0344001d0081c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 630272077 1250 630270827 630270853
    0x30f0c060a0309210507051b010507110d17030a0e0606060d02070c240e09091c05070b0a1406030f030d0b1804030c0611040e1803041805010317030702 66
    0x3c090920503004680c103003074960301055082c0c4a14003003d003080000742d011a0401c1804000e0186001030f200c0c1c0b00800312400000c0002800c54055088040e004803040072840c041c41e2201e120406200d0792001105110f07900c4000c10708225003003070f1001c040c21841d0a642501440300059410300480c002050700d070804d0f605040a00c081d42c802e040c2214100d00a0b00000303a03011946041c100c2058043c0c47c241070709005804028144480111210f10070500392081c420204c20114a146201441e0401a807401c50101c0d0151260302c00d00d00d0061240d880d010812802c4007403a80081c00b0502040c8844000b0b48800b030405545c0c50101c3c4440740300360010400d100032600554400385001c20003034035600140401544901061030304581c10340100d9214024a010441107120704070144c4510301d1005e09050602034507095540780141800760000d402034560b141c405003001900c000b800d50080c20b803613513602c1302205005090288800c460340b94000751118948407403003040d40d10809556000b0401d01801c0b103 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 630273327 1250 630272077 630272081
    0x50d0f0309020a121703090d1b080d0c090b0c070e100308030106050d0609021206030607080c07030518100f180b0906160501050c0a0e0d0b1303110d0905030f0c060a03 73
    0x60021034543c035074148404d10101c1d441700598403c1d100c2e0405050413902c9a00003410f403210315400300c0684100100b00f42d001507a10000d841c46a0138070800044d0403482c0e000180e948003241e8200d000f4000b0045144802c03a840001e5003420346031048070951041c0c032411340c1c0c40603108050000411220060005000d100e220300060b101c290500500810754940d511080800c0764040b0054202c8802d2220030060303030781010490150483c2451409081c3c924080003403500c3c50251260040403c0800503070502e0104040d00c1c02c02002ca00100a04810041ca81000e4503250543d0410b90101c4e08094200600f60142090079046410003042145429000c108001d2a54400c44901d41c03203901c00c44125000c10b009100345880303054101081c5940380b00540c0050140303030100b02030501c101c01c03454010001800d8401590b801603250107202e0000c0b624cc0c5000e4502c0001d5900c50711407031041d450240452039016040900320384c4141c099505101d002095140c0b41c41e1300712205a04070b0f00800c80d001a0034426 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 630274577 1250 630273327 630273359
    0xa0b0a0219030e0a0e0103050633130609050f01060c080a0c03021009031112090d0f0807060e03040504050603011401062f0a020a0e0115030522050d0f0309020a 70
    0xf8588031220303c05250020701d180446401c0094041d41e070400500c2000340400c0401c1e04020000c40588404071802000c0c0440ca401080d0307103038030400545c0309828640b280c030b07407082c60f541e0114000d11001303480d648040014a17040741d00f4412101c401000140950041280c0d10140c1d810a02141c5846d0120380f0564000c60105422000c5100b201284413480300c692058a18942c070030354410480004140d40b251401c0d0703c00c258507190b40c008101c1c06180d80d4449030420800b5602c0200103880403190b040c0745205020700c820280841d4200000040d88942c0480104240c031811542082549c45030003c1c54220381250040c08203c03102d4600520501d0300400115441d011a083c200da0f003030005810869403440d114a40c041d940c0e1042c0591811840e020031600f010f00305000300b40381507615109080541512070054107040c9540e440c085082e1010030300c213003100301c4c1e1a0341c510802e1301500c5c03501d20398994403150110000394901c581c48026520a0003400d80640d0010b160510060030030042c0204c00c0e001e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 630275827 1250 630274577 630274583
    0x105012604110a061b1e05010504030207050f01020304080303011509030c03050d020607051207030b0f0303160c0803070525050909030a0e090907140f04091203050906161b0204050a06050a0b0a0219 86
    0xc0e240260001002405527078400c5200742c4c05010541d2908050008006900c284141075410500062200120000c1528111011103903086514030001c8030640e04018a07810150111aa40c2c0340403051181c000b41548202c0d6141c0d0031a41a9a900c5208590a000e0701c090301c449441e00c00040381c4402e10940080e20030100080c82010403110000020f440d560088415846041101c1402002d0080884828008001500c0a507140048903920180c4400030701d000c0380074040035005400310101d040415a4082c09000d01940340d40c2c20703c4418240c0d250410b0840c0c100240d00504a000c0904140ca030301e600030400d40c001008024141908410b0401c0380c190340c203420242d60400c000003503a9502603d0348290086500d1706503000078400041c1038034401050080c2c56400b5500340700407140d90303030408003070b04000c0e141c02000f0444604114100c21130b00480a58010f04050900c900c080c1d0540c40030003298002c40708120303140e99070820300003039000d1100c00c4405604850300c441540c4130540480303207050b48 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 630277077 1250 630275827 630275873
    0x50a0305090c040f06051503090c1e1908010506040c0e01030b010c08181002070806010605071b0b190905060f0708191e0201050f0105012604110a061b 66
    0x4142c401040c11203460035140340000341c0b5074004012504000100009519001210724510300d042c0000340d50785c5524200710740c010400e0b43d06061107008803410401820900800d0590725283c1807c48610402c42030003070348103a520700400304e80c451510b131140c240b540c01c3c0e40e2201c01380c0c2c082c01030042d40102a009030303580c14001018484000610140c00800401d035490a00c0c1407a2400a418000385503503802c001390641d40000e40074000c1000c0021890304561181c602259101905c0c40c00e030141c0c03440a2a075070681d14001002081800200c4058140c1000311180c2540b40c151182044410303404501c610b0707801100030008079501c084c1300402412410b018100c2c26290104ca00c8640c00f00a02c000d01d088002600b0030340f41101d162074450321507682c40080c4024061800c0c4000201e010940600c01c00f818031900e180c00d51503400550100c0800944c0b0300c3c885102ca071819040c100840340705400c0c4203125540700345011401d54000c500000c2552948200c4200a070800e036284003030f15000e051300e800c10031 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 630278327 1250 630277077 630277093
    0x103021b030705240c090d0209070c12030c0512090118030c0614240f040c08010e221203090213090203010e010b0f06070c050a0806070e0a0303050a030509 68
    0x1020301003580c8000300611000795619401401d000703082200114460342c100307001070031201c45080211010350300032090007203095507441d02c4030020380d80260030f00c1e000390064814410000c20300d0700501018401c0d8042c01902c0c085844009003102213400000101e001702e102400590a041c54034504554440414800010360081c402c504541ca030641580840c00100c6800f01c81040004500520b8690294640401181e0521850205081c2078041c091200c84d035101083c00e84030343e01c10103d840702d400003910401c505841c07000001c2403808240102c145c80815403011400380100f002181c440340790034045244200086a07a070411071403004020f4002c144d11142d4030009170380c1c1d19986540d0207a00f10b07000159426a4414142951000b28090a241e4544010105181c40c1c404000c610700d02e040f1807203540d1754500c0c6489040414103400c50340c0c004a05420200c1c640070000780680c058502c603110b050203004c085041040c0242c89010003030001e00e061000b642c04502035007106030040300c04001e5500304 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 630279577 1250 630278327 630278347
    0x1403070503120a020c0a0302090402040b301c270305030301060908150708150411030f040b150a0b1c0c0504170303060d022b08070c0b12010e06010302 66
    0x2129400340b031001d0044000400965080e010011103200d020305440070300d50a45144c00045119100900c068015615030050303002c95521042e06020701c4070845d138a5011001080c092801000b132a41d0051003522038608484000200010400d84001060341d41e4280987d10000d450341c0a15403e510030140320314160040300154040c80a18060001c659905200b14500304005250154483ca044400001c000c18010001c0c0c0c803855180e0f020703c072011741c41e203c4035041e00410010007010346c000c0c03250310b80030043c007060901150880e401340d409000040b0f0a900e400060658070080d00050301d070304c0446400d040018046045c050211800c0251440a4644a0180603c10703646910070020006200040500c85140340d20803820341c0502c1240214214604a00810814100d19001902c01c6031040004100d05c11181212220000001d6558258070405e141c641000d82155004481030741d001c140c0824103140e040d05940b8010389902c9a0704699291005030f4540d02c1d0080d01082c1015000c000d44205 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 630280827 1250 630279577 630279583
    0xf0b180135010b09240103020a0c0501050907090e0601081906021b0a030305090c060306060d09081b0c0f030a020906040605100504030b0a05040321140f0a050901020f041403070503 79
    0x600d000c031000030a0583c400410000310820003042c8640a00d60440680c2c10f402418000792030301842030078010380e144208102036506440c1400006e02c07540c00c2c50100403004201007060005c0342c18500b0144088a0b00b20703c01c9032129001d0241c0c59541d4040315907c180030500005600519018420052610300c42c0114500c3d0030041300d0746202c907a48050001300405d540b6101b4035030300012510190401012000004a0a10014040c14800e0a01068141464580d90f00081c3c0c0d503940841840c1c0d48106140340c01c1e40c444000c0c0207468140c066902d0404141c02c1c90003030201d100800902400400700241e0030040340c4000540003980150341ca0b24042040e0300d03160441800b0400b5522856166440c62921911311640200f0329111541800f0034480042e030021425000310038030481c2c401c0200d0303d2840c444021303c6402110302400c4050f80a00600c2c0e400b080b911030003904100c1b0301784003503603452030102d007030344118421a40c9501302084200908040c0920524240c4c800400740c454065446000030701d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 630282077 1250 630280827 630280919
    0x103020f210a06080c0d02040e030412260301061b020307090b131401061218210315050d0206120c03090d020a151a12010f0b1801 57
    0xc0281e500450100c0c0340386940c81194000c0380c1d84814000703242050462a150801c0400480c007521304c002d0510300b15941d9070030000311105140c089036141d0365100c00781e800326400007606440720014100c01d1000c100601900d900f03841080304815246901e8404d00b201c1030315200b0074901c0525984206800143e80920406000313011018020410745011002c0055000455a12452044c54440320807084203104e401241144d180381410507808004100e0500a00074103600090341c4906405080c0400c6880a06030750411a014285040024604c106400311088910398201c4e21040800c100103901e802003c5030041e03440a0000e9040c00080c2d440c9a021080c141ea10b060115000700c20000400c3c010080e072281c0100c0d5200810001049448000100310300030144081182c859924040040c040c00d04040b110801900010609071440388244c0245244c1906081c440d0420080c40240c1c41c01c020105039210900900e00c00300d0740307003008281c0c4200321420780c010042554181c2c0c80d82502003030f0741c0034 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 630283327 1250 630282077 630282097
    0x40f120306170f071e0305150f090309030c060d021c020717030f07050a030605060a0906021204080c09040c050a0b0306090a1a040b030f0f011a0103090812060103020f 73
    0x86011410502d035011500070b10142100381ea0b102c2c54480c203e48100203100e4040720b00c1c28882e400703a130281d01c01c5460702d0041e5400191140c0b283c200350208400d407212001c2c1c8200c2e150103a20381603490301080a902c2c0d214030b0700d03080d91650042c8006c00e5286041002403106241400006243c0001c0c1e1440304014081c692180e80440e90114100c0c061000306443c03004005c40381c50384075180d46000c3c9200d09800b9400fa00d2201040130206010800d94023960100004d003000410307041e03e5000c4254010318418007801034100500440d243c298182e060340041e07400f0f0750080d101501090410f0350900500a00c010410b031002400841c0009141d11101c0c9040080c08441c86c0140da24503080c03040c00303000c01c0d020700300c88000c0b480c104850018250300c0c124510000821580404c0b41c41300440024540040e00d640142540a101a03151007850150300554003903400f444450031005500005408981d94000061304500d401c00950810110100b0110341c0000141401401d11003541074107040c0350003001140c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 630284577 1250 630283327 630283331
    0xf140d060e061512011404090c03080c010b090705040905041a01030320060c0315151c050115090314160303080609060405061309021309030314070309030f0503040f1203 74
    0x1004007810320140301642541200f40103440d01080f800a12003c0c10705200d03050b0940342110401681b0340d2160400c220b100d030003c8044900e16264103108145601c01c002d40200c80d0710701214281c2038104404c00030b100300220789981c0d0a05141c241980050030f8010701c200c8000e4014600d03614140c6000c650380307010718040c0e628110301e03000c1089148055040880c4003504c95200100f001082c82c05802125440041d00c80e4401010705c042e00854903003681c1518290760840d002c542001c01048a200340240107a131034000303000c640d9850f00840c00781c140d8140c8160010b0780940301480480e2010050b0001440100d0403290450120f00b0501851000742d0000c03400104002d0500c95940f030702d100d120340c06c070034221420050390522900181519900d01000d01050792074402c210113650380c3c81e4145c01da541048100784070007000e81c50020010b02034002511000301403000803400080c800c0c421603403030a80c1621050100700e2400c0040e0f445800090007102d841d5030040c0c0c1d9130300046440e10401e205030396540300 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 630285827 1250 630284577 630284581
    0xb180c07030801091104140f100e0a0504050408120405071a0d141311190f03020a060f0e0d0f060213170a0f12031107030809010b060304030f140d060e 66
    0x910507141a840b6045650410965030110800d0705c0455045994080711000024900f0000c0360141501c925140e038440341903807d840105811140229070081c4c1241c0c0c8001c81a141c10400044500a89000d00600d8051018500c0c100d841042c8540190140d030444030034540d2075010620200b03801d543e40315140c4020031400700c01c1e8081d008004428000d501d501125241028022100c8181c41ea4081d00b002c4844401c3c644940710406800d050b401d03000d42c2c05484079160f28000c400440c0d2480100d0040c088200001400c500ca2021032420f81202e903103540c008002d4100b00b0040501e9040203942c900c1a000b038134030002c0c131a072008014184d404000d0380c0c00145003400380c41681c6010030559442d41c001d00c0000b00001c000d00304d5025569480b02c00002d412900c0d190440c000c1400c14455a4401380004d201001d240e0130002c1a40314070080d90003400100344403030511841e4041560700030085080000380c20441e90003100c600040a0f45225001d003054003110703046040c2c80007648090105c880d1902 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 630287077 1250 630285827 630285833
    0x120509030114010311011805040204060e090912040b0a09050d050105090111040b0706020f040902040b031f15030e2a0102120301030809100c0506040b060108150f01030b180c07 77
    0x340d4010302106080807440e5604d180c648450340124001224100100f1441d131409046d040500c5602600c170203001151143e0301c0700d45c040c1c840600c00100e0b9100c2d141e003000140039410001121041840b1000455052078030b031800407121500400c41002c103100305420007040d241c4980351110700640c040d90020641c0d051402099084600990811081b250100070900080c41d032401110f000641c0010010fa5800c0d2114502c181030245400504016000040000c2c6000841c0b0247d80915903100025051004100c100c1c01c3c25205407140007119410382c510000081d010f0303030060745850210003d4800101141e26452503044111001c0c90440440762100182c030b503070410000c1c00b030060383e40c0c0c924615411521003030403d0203680e1040b8403648144c5145c001081c81100000c00b4594803c0480702c45040a00d8520350340340040b20400d00151940703001030003081c440124605800c0300070340f01940d008a410300450281464040e295004441160701d13203e0120000d11142c414200d100d174994461120745 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 630288327 1250 630287077 630287081
    0x504050f0f071d130b03060705130f050d0818041d07050910140d06050702150718030b060a0b0408030306090705070c050105031801020d0507020f011112131205090301 73
    0xa0045401c2214a482268000c40c10b0f210340c0d4480c00040752503580c4907043d803042602070845003070300e5501400703160103205100390020003506110142400345d8140b1a00c404050350341082510415610100622405002c90300c1c80009000b909a621441a010342c2c1d0180407506451b01c4200700310884500c1c0f405021411010300c000c4024001c129148200350401a000c4541c3c520940a18132401c0100410103000c6e030350f1200340d0070080350712030411f000c00c0c50617070000707074998400e0035003449030038024800030b2070503485051103841120404404000076411512503040b2a10018082078100c180031002003908103411024000030a082c47c02550340f0325000301486070f128000303051102401014014400018001c04038038061f50800c0c40d02036100d40d18161a04c0c101211170007480c0441d480050f60b00c1c40303241607800403449584980c007102d030286041c0c0c28980c22200d900d5140902c1600074400d64514036011035a040c0c01c03000c3e03501c0c001007140680d01c90200a508020001005c41c1d0005078070413244c1401c2c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 630289577 1250 630288327 630288331
    0xe012408070b300c070b06060c060f090309060d0509070609030b0c0906250507081c11070b030907230f220c090603050f010803040b0a090504050f0f 65
    0x300207000c2807450014100c0e02c07406145103d030fa40b00140348684045600701e02448080003105001c0da10181007920490f07009030311040d03003a2070350309840e0700240043c1009000c8030381d012a0703200280790341d07603a003c02c0c002c2158000d440391031079020410a4405598410303015100b4840aa40001403605101c1034042c075140e5681e2141c03040c00100d031020000304021420f591fa00840c02618240e94052500c00510107102e0101441400b0307804d5000780e04148071000303506511602c200d0848014070384802c4495a192039030990511410f200315245803016204110040c0700b8241502290504d9860b414000083d810403070f002141513014076020040240803904030074803144040604c030b04041000c008a00c0315040c05800b2400340c4984515601032111101c1c0840c4e009500e800100f040c58091880207000d0403a03031207441c002a003040701080c81a4010303103095040380c0041e001141741c24070f00005000e0581000c01d4000510005403c0040d03d030f1141d020b803510030411508000194038003100c030050840c0e00 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 630290827 1250 630289577 630289589
    0x1b090e010510090b16020a14030d030e07170a050703060c02100209060327060403080712052203050d0c02060402181006051308013615050a0e0124 64
    0x1401c9a5185540000c3c110341a80c80710801c00c0d0b602d6a8a509006500310141c0c0c0c001c1d042088217900040342c0c11000078286040d00110150345078441480022420303500440032000e20303600b2002c420001030f42c0d1a80c59020704450881a40d01b0500692201414090741d6070094443c0307900d80185081107035040c003c025095000710700850520107441c1c0450000c0c0801810500e1042602c001a400545400b51007213240d88030104659051915190080100d070701550720001003010325494444091140c01014818880b1890070035204038400310000034030480030010790520608000d2201215601e0090131818031142e002049581490310605c8142d909600345410203030001e10500019817440400300d021030b021481e0442d04d400301003402151280c0142d011100315840c2441b0011003940c4038040c1c0d80c0c086071840e0114188840110101d1022110030001443d01380041070344c00c0d409905901042c1c000c05e07444000214103000d1001c0c642151301001301001ca0001c901f080b0442d0328078000840c40900741c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 630292077 1250 630290827 630290839
    0x306052d0f1c1b0627080f0c03070f03051207031106100f050927030c010e060a0f0207121103040e041103010c020102040b071709091009150b030a0c02011b090e0105 72
    0x13181c040005d00d1181090f80301038404040701494031080040c10307540009460050151495079040b210440e59a098042415001c1e020769075000501014001030001281c0d00840a0b11514092a1401e00c46074442031049003031149250940600403000c0100c02e1242086c004110000e908001c0440010b0b03ca940c003881c0308807040c80410400301403108060045140540780c1c0b100c40030000ca4850b0460103034605d2a16590f20701507102c1d1554400182d0140140c005050400a015601000005a02c900d483c0079199140400e40381c2001c034455154500c0d0031000d401502d0505407a01085807440b20252402e540d030b141c0f501c00e020458034080c8541c1c8807040c0c41d030000710701d42842c1507080e44030341c0aa03a4010302a40300d000014940e642c405000c9074404c1170b0003020821203150403050030f00c0c00740403070260f103014ed4940f07402042e10040c802025415105914501e50840da14800040c0c00740c50900d16550465480311564040300c2040c2c240d40c108040161030301d44155081c0011190f03881e405a1209229003 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 630293327 1250 630292077 630292079
    0x1b100509010b0d060504030c020312120108010c0806010c1506090504120836030f03010f0803070c09020c030c0d35160216060207060306052d0f1c1b 65
    0x340d5400d030b2950640794001c1001c0749580e1b8604094a0200007800c001c1e406000b80c4008003180c50407036004211060740b0300c40381045640c80c0c0700064200c4100054860100300c142c004143e00d0760064002c4040d55104101d0780585400c40da25441c16181749038080c0180580350070034482002000303401110100711030301d080051440c0400b84040f02c80c1c8003400186510013920360f20400700b0700d1010746c2090350100b503045a90b500315030300d41c0302c5042e40240306d82d42c0c6d045801900400d514402004840d88203070060710b4581e0703460905802c3d80c020350050070410010320080110381500142444822035008442e100c2820a40b1503542503069182810f9000340294030090718038096440d50f00445400c0052500381d801001501300080c0c0c507001c2e12111030864000d42c0c3d540081e6407070340011034000356081684c041c0b04c1315035240d0034420404030090040d04590800418440c81d2848181c258490140041c10140340082d000e01241604d0181d440614040c05102041010702000040c0ca82100941c060310408003 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 630294577 1250 630293327 630293329
    0x120f150b031002031819030f11060a051312020109020f1c06050901140c0306030d031404020d051f1b090605030a0c140d0903030c0201050601140c01021b100509010b 72
    0x940a0720412810780b581c08070101d441054000303000b10507040c03840c0441c0e1038500554508039030b085840c0002c4000500841c800d01c0d569105051442c04182808000c041c035444155204002d0500140342012140c0b0a802100103d10101d201115140320758000142c04c448078014444500c120f214554000d507046901a0000301602d0007036001c46800c9003000034682c5502184d94007514650220700461202c000c1403003942c03140e2800031405402e049046491140d6503a4082e0151100030b000c80e090481c0b248000b070054248040f03100c03103442c0f00301c1c00e0300c031768946084c800c0701a0030305602c0c134041ca150b5580da11154440032013100c1020a50500b40700705403500d000c60003485071000a215490103074072190440d881601450284e0520885607042d6900c4099414282008048504050700003d0070120b000803840d006100d800e0240e80f041c0c2d20140d11080507040d84507980d0040c028042d866508001001c0c0c105e401c4408103030103040341c2016200c500c000c03407500303020340c0c8020303041a030b0b1645071140d0a01c00d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 630295827 1250 630294577 630294583
    0x6030a0c020d031b0e040e0d0815101e1e0302040609080a0b060114120109090501051608010b0a11010204060203130e0c030412120c030203090114060315060604120f150b03 75
    0x2141e84c1e840d0074800d03c07181401290280c0034805801546129480c0c1085901d908050b1241c46400f14441b4aa40200650104030300f000c0407007102c90108403040700365030030f68035a4212894021414106120141d01c0d000c0302e01007600a240351200040d40c041018007072194000712120042800000070030800e249512818011080030749080e0501c1201c6001003030020350704003950508140c1d000c400c0c42d40e40c6d4896015029144c034103c121201d502c0d00c00051341010996130806484042ca6980642682c240a9100071590121a020061003002c00c04044c654509000a1029001540c042c64030341c51021040c40303a074100c40d08544100c0143d88204210305111109690303101d80c000c590b03440c0c602c58a001c192088450036000311034540c200400c544000350035400450041c0403007c02085a8200070703105400a010581d00181c1c55048640c40001001c21003200541100d00113011034a8a5030310860700e141750541c601c0488020303442c04640310a110b81d06c201d00814142060341070100442c100c0000391 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 630297077 1250 630295827 630295871
    0x9080a08070c060203072a0f080f12040503131502030f090111060a1d010902010c060c09050303491e06030501060801060b091008041106030a0c020d03 66
    0xc000c1044006841c1ca80300b50742c4114400d03000802107683c1d007400d010081980c1500c101980883d06540350841b014a440c5100850881d04040b01c0f08142e4105e40e02c6903082c1c0d101c0881041c140b034003403190301c107092b007105400c1d8016031056000b1075840310400280d220310340556000508010000c282860300d02d40100c2190394040000c405281c0d14400c810060700d0300d0551a0211340d0718860403080085030407040d840344081400b02e40e00c00d50000c115800007820b940c501c58000380010b00848440300050768680080f0030701341190800002098440c0042461500540c03808050313110038100291500d000342c64014888107403c4248480042600c0485d500e401c02d5541845440d0b40d074112216098441e0b8110b141c41c5019414288585562401d00038041c0c2420300071b001d6294680000000c095820074226101654060f0591800809221003514403100042c02a07c0302c03800081d0180d0240d0b901401544549e415290014540f040424020310300070b110303140d510600d460a201c440d60450404a014 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 630298327 1250 630297077 630297097
    0x3070b300f060409060608030703030b03011109061b0102031303080105030111031f18020408100506010c1e06020a05190804020916020c03031b061012020f040902101e030908 76
    0x71203192111000f19000305801c3d1006000c85242c1040882c08034030201c0104680c6009070343c2070048501d4801058201c41c29814940404c1008021509581c01c20341c028100901c0b0421400300301d120400001030aa0f44122049041d0032b0b002c0c200c00007015004240d103405444250020481200b890001000f03620002e0000040c00e04d940c50340000d035009140c00c55015001c0040521115000211003402075000f501408900303004a103003075260041c1030300c80c00e0320070001651002d410b04819220108402c22020412024644140811011500900007800188001c1d40d6003580c1c1c008801c842e043d01e0b91a9128070040250000c1030101607920b02009940018090781c2052448141403002d0b4902500703000616050301002c07600000c8540a8140016003000c2042070700c24aa5400344070fa070700e0150b40d0040e421130032802c002c940003500700864800b09507540030304001030840b1160000350751000340b80c50040001f100b4000103042c5804402a82c56420000c0c10103101030100c2c0e0351703000c030300f0b020340c4042c9 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 630299577 1250 630298327 630298351
    0x501090b0702043309050906010501032406090510020102071502210a060303020c0d0f06110f0d051b180405060a0f061106130b0402150903070b30 64
    0x2990f0310b075840076890060904165a0f0000328220050300081c0480c1c50800d2108111800101040c01c1d000b050302ca008400b01038079050b03080c2001540200b51165000b603000c1c030301c80181f610403d03025031700c0d4000d4403054503501c5095250200300960ba03082005100110f90040c8000b00018902045103240c207458a01c016899206007480144d000b49200707802000e90440a09001c043c0320240d1001040e24003d6080d1390b5400066070074000e41c5105030000410108a001128001c24280e41c0074416070040000d00c107207001c20449ca82075050700060382c5a0354203136641c0203100c40c2d0032100704d00816140810080da030401060402d0742c14041c0440d55118016611400052000da942980420280090100d0100c0183e25003200500100040d00605071910400d00410b1000103401c0124040580c86101201d5543d00c59084c0800070034402e801c1100c04405003c500429036051200d00003030300102000725142c0389454550300e5500260074929042c100701a01c80000782c2747c030700100c5a00000d00e42d00 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 630300827 1250 630299577 630299587
    0x70305060310060e0f0a020c010c050c0c0a030203070603020c01020f0712080a06181104120b010608130f030f0c2a05040204050d02010f022a090708010b0a030906020d020c0312010f0501090b 83
    0x80e0001030310a5a040000703652800741c80c262b4068024020304441c5401c1000c40f40142d4800041c0703d9030000d01d0202a501d81d002c0041041468829002081c0e601028000582030049400d098090390b00000c81c22120318200e41300b10000203520151740c42e48030b03030110320030302c045441c000e9440020300740d18550800d10381e100c5d62442d02e00b00180301268001d24640130010f014691508001d00800000c0c021180007403401000720f854492070038075613207905401403e18800d22080b80d40c161200040380701040306000c910200b10340445d401d040074120700705822101e603042d1a50000d80c001c0c2c00301c0c25042030b0300c0b4610601062040751591407a02d100c0c0c07070782800c3c18108803011684c01e07480e20040d0004100b01c2d542414000b15407400c07a2619400880c0e00303646550382c1740c584000a6130303155001d020303072007140c0320511250000601c02e80007820030500800340103103828050802042640d0100300c42e8041a400052255200000391613550b004015120202540764102000207280d03020130b02c5290321580e00411 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 630302077 1250 630300827 630300841
    0x7030902010903020a090b120708030a0c02030c0907050a231206060715232a07021908060622230f010612090308130515070305060310060e0f 62
    0xb220502441c0c000f08200149a40c481c200f4015003207030f030320141c003801104e80d00081c030000009500341901e0604026600340469040c081300c0207110000140d80c5813240106450302a00c0e5003480700e000712500d0b580c01303940342d46648028190404203003c00c0c0380c400d840d004401c14070524205032900c0ba030041ca094002078032388d00c0004203107004002001d01011220500108050310707583c4000803e1820741400c98820f030102e5038880d42004110340d8408100149402d44403d60500d10030035000341d01c2200e0550a1030150f801103542d1680394003204e200c000405500b480001030401003250b01c403604a0b0121000e0014140ea02c42c1d401043c0c013481e404949996808000d202c402d402d2180074107410348a01c04a03e0151003c2510780420b200c1c02d40400d0b900c440a0100c00303d14001c912404d034040d00d071a0a60b80301c400d00510080700f00d640549041c01081582c150071846c002c006409095250307004240750401000b00b60601400c0742040b1990fa19050003008018502182c040e444400704c1003268195071551 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 630303327 1250 630302077 630302087
    0x901060506040605070c091814240103050c060c1f0605041406090604020915031506070c0807060207031a071103031e010b0a1b050712081209010507080703090201 71
    0x3401455110002140100b0b10540c464040c00b500383c05551a110040d42c0c0380c8501d4110781d144100c0c0b00b12036414503105008190807495826803a0250384c01c8070115103c5410500c1c5202d2940b0540d101005048010030500804120b803000b6400100c0c3c51510b0109ca4207422982e408038040c4000300f4242548020030b0304ad885600010090201420a01048a04044d0704000480031500b10b881076000030702080e268286032007600c241c0f0001500d45000c5104071401c2c003035550002000c000c0c0003800ca94400885031a004d0191600e9803040f00c203020b4090901078801e081c9505034000c0300448d4040e04c010004519208c08041e075500140582003c035458246049400e54980e80f1919418440081400301c43d942c0c0441400342c5d41e460054400c501d0b620b51707000c0200c0d841550001c45c001101c091285041c6400d000c50080024458402c4030006641c0e000d40c02c1d101d440110007a9044800031480c04002103071001001c0d803040b0048001c0140c0d280641000d0328110020708514209a074a103e0700c0c00316400341c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 630304577 1250 630303327 630303329
    0x1206171f180f050114060102190c030f0602030915070e01080c0c121305060906071e0609050606040506011806050c0f0f03040305010b03031201091503080a1223040209090106 76
    0x80c00100c0380c0307003810303003071028550303104410071900380d0720304080805000300b15a411402060140c0c05060194184200003085000805041d640f110b01d1000c0040003440c00032a180f2000c4c4641400b40e203034900030710b87e14201a51003079000e84020881c2e08000c4601c1d4810724281c200c01d42400d050740c0c1034072043d008902030301034055604806c0c403540c10520102c41000300600040405801400350841d00d51047c00402e0107100320103908020144903140c0091501c150744403002c86100108504100a40c1704c1400340c3e03c0d0759805071344940100007804042c0c141401425407160083c04c00800110141001404880d041e00c151410405d0100303d030f405040003400703a00c040650120842d414148400411500c0780d003c1c0c0f204548d55071920803882c80c91f0a02000781ca030503031031b00c484103a2140e00c0d180b08a406070525600c00e422000c40c00700040005007400000d804503c609503210b0500c2501441030500b19103402c061b068130b005941007881140b08880d2074007684250b05540c01c0c24182c07140c2c04824050082c0e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 630305827 1250 630304577 630304601
    0x3100306020c01060f060504030302030d0b010e180406050c04120f05010b06040311100c0b1f0b0d0207020f0f0d03110309090c03160906091e151206171f 67
    0x14210042e18054100405075a840b000d8030070131903aa82d0080c1d925110740d01c002409a041400049450b03036441d8403140d20201c060401240300601a0000349d4003404202011205416140501c4140b0616200f0321303a004004004141c5410700b050039641c0b51a40a010040c40109003015402c00c2100c01c1d04500b4010034050141070311142c4910f041010048844011401405240b25002d4020b11510303200350701130380050030303003685031122681ea5140c0601401104031754048000c0c00661501c0000050440005d60000180c644440e032041100032440071038840d105600800c007001c000c0e95140000c0740290b42c1810b20310211803910b00354070f0a601a12440d00c0e03000b180e45007004504e114100086106824181000703004048104060791800c81d0b5010301000503030341d40c000b44084080b04030000c0c0944c0050400e0b00350590f5464415843e074001e0f116400c00500d1031a00c42e80040a180501000351500010366141103d14074291a07403444513000107440d1310126500500c1e400f04980c485010100 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 630307077 1250 630305827 630305831
    0x10903120c060f060305060901150302010c03050c060103080a02100b030d05091206010603060321020a033e01060501030b1309021306060e0a0e130605091f0c0207150e040203100306 79
    0x140b6290b43c40300500ca03d102c140e0b81c602401000810030300042c0700350242442da004050031043e0442c0c00455607985049002c4040c02000c12407103100120404c1000e008501c907005a80e500d1000c80402410f10707006a461154071401d10100c24456640030840071003d1b850fa180281d01c07030405500140060450000c00b60301741c054075001248055050b0480d0060340d00030a4030a0940301e61401c2640c0401216603a00016004280c1c1d07031300000d101d43c0103006001906e512581c5801c21414a120f840c20707010149125154803041c180d0740f45a028040c031030091209003010000100310001113a5400c041521603a106991b4031491011949c0742c3c00642d40b4020800010003015442d602c02814900d04010311030301c40c8619100c00106102c0349050248a60070620031201d101544c1d44d1454050031026200e403600d0f000c1c1e848800780004c2c0703140c0300c80103a0000000104111204e134401030304214558000c1d800c1b043c0c1d0340c1c044404d115001121207118510954005907a40d0340c1003141003615a043d00014100342c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 630308327 1250 630307077 630307091
    0x105160803101802131a030c090d080309010e160b0d0b0d1205180a0602100903230d110c060c090609040204090f0c0305090c06070215040f03060b0f010903120c06 71
    0x1190340c2d000d002056405000d905640ba03e404407661b0024004031503007483c401c100300003160b02183d200907020001c2c2c01360200c01c00945560b130b0304086400882d43d002050703640d2003086403906010005c80401c084000f0000c0b52141c18010101007600c6194007140e249500c90246450300c0e2035145000301d1258000b480540e0034201c09000404682c8014038064030f520748800a00a2840c0610701e01003203942c070350010403c030410726200401078103c02030182e09000311642498100c20103c1c5140d00c98004904041356940d03c4614000115000586030110400d018000d0500a040025425400000c090304241e1074040000006401e84101c0b003c150304640081400a40b1102a07000500c01910646050195648140d822404c0b1102124410150b41c4624142d00031410700000130030303813280081e120350035000b00302c0080c4c0c40d25070044d44000c0c0300321024407041041c0140c901c144c00801900701c41c03e90b80b282030100020b01c8410180009007100303250031049500180a0191040c8203640000c080c8015 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 630309577 1250 630308327 630308369
    0x2090106091a090105070b13020604080d1704050c01111c0905100806090601030e0a0b090c03060108010608060601200a051c0e0a030b19050f0105040b010516080310 72
    0x240701d80308541050b09505210744268103000c00b41c4903031840680d035007401d1241c0c503202c600c45243e025118480900000035110050b841d1203000784041e200d214007c00305003500c0d040040251000780d0000c0c011402407014817000850103d86290441c1303092802d0034180c50040205070510411041800d031a0411820601d105500940e00b03070101d81c4103c2c0c3d10440c4d00d07194102980c0b850070031103100781d00402160000e07490398060b61140700014403007811507407282c00b03a80c1d940f480108140e681d20f8080d8408007980e011807034200012405401070342e00a101040c0b4009a0300c0c1c1d9084060401d9060003030340c20410440000c00009909104820011541e1080f043e007000380c1c440309910000362b01c441d041c100c1da0007107500645102d0009074014085455141ca56290340d0311400e8040c0000c080b080d449110b1100d41c0100e405018040c540d502225a07155140030108800c5600101e40b03181400424055200f00441602d8006091508848e0290b980d5a85402c0792000002e5500441c0d0081c007114010100 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 630310827 1250 630309577 630309587
    0x1b061e090f170f0d061403030304030e040c1b050304092003010501080a020706051005130606020316030e030a111e061b4204050307060207020303090405330d030c02030a02090106 78
    0x102c940014295848006c81800c0c19100d01c0301303c0f07000e0041003511000d40c00900703069103d200c103a40c0500d44013100d6001019000020740250800303a619030f001090a2100b481c07a4400c2d0161b400c24220b015407038145c0d401c207452305800140f1032207043c000d0041c0000c4a10505404440403968003803800c100c90302e800903c46204130b181e40242809034a1150038480d100006204400680e0f0103a0010342c10304880d40007081000c1c400d06402c0b02046400c1c1c02c49941900c0800c6084812403140e25a04404115407051020b16000300c041103013926a42d001c5068242c948004a90401d402c200d403040021280d04a40e0b40f80c8a01c1d035100e541060844403065001080860702e210098404902c401c003240407402100704003e0082d035000c1c106800070041e110000305d5030382c01030180c80d201030142c0e400c12003240c0005084520480300780b0898610415200c620040c024240c56a012601d203480c42c6400042010030602d44d075010006050040314030324681599010030a0f044140d40c018904141981c4070f40004103 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 630312077 1250 630310827 630310829
    0x807080a0309051501050d020f0a0e090d020d080708070509040e030309030c0705090417030709080d030608010e07030c12060905010c0504050909060403050f0306011b061e090f170f0d06 81
    0x181d04e005880c9040010101c0504c41412110014400010000280c08002010f01c403080660360060880c03030000b54150070340121510422b00c00c0003030940e00103040c84c0603080002c0d0311114420440a8010001025040070500340c008006140040d2200c188802040060071103070202310f40d82c80040100b108944c030010007400340280300015070f080c040d034070400d2000c440342c1600d0051032040c00c1e002c1d40b50680d01c413002960707222100f440c0607140d040c0d0b01c041d85810980c02c42840400aa200c490a20900d0030902400c0340d640a01c000030000d1500c0c50304d400c1581c0e0311500030550300003030711540d0a09000c200e4000d03071003080d003080c006c00c0617200c005c00c041c225034418440c030340c0507400217000640400c2010442920641d015201c0b1403030140c01c0080c400341030340020403a605001c10713400c0c940b161005403041a01c4091203a9400201d0004169034207030441340700500c450740305040011050000d12500020804603511000210b420541c41d4001d112178040c034507204c0d0300c8400102d110040010503400c050 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 630313327 1250 630312077 630312083
    0x30602030a0b030a020d171e37030c0509041d0c15072d0303091401110d0506040204170703110d03020a0308180f1b0109031e0807080a0309 61
    0x154607815800e1503150313041440042d50050441a40902050a01c0d111290030f2511815051070401c2140c513400140705225407020040b170380410000c030022001c902d0341d12846805103103c3c803002046180413406002c900c188800b016100e8180021040c01031042e125180d4004205004046490354030030725805140018144038030964900b0103803070030011100d104ca00d00303d44540c0d252549944500401c01e54880d81d01c110000382e0601c5482513042d5048100c40c042c42a074000c11682c0c900c0c1480c130304c40080c020301004180d16000102c680c900007003040382c0705c0902c00d950102c1e41d80e4481001170000c1c050f40e07200017070b01140d591600c1c24001022510b50141c2344580c02541e0820000d4040c84011000a2001809a0302899486011038080e607409c0d940f062a80040c260070300ca0300400c032410b01c4040c2c01e041c1e80d1640444036158000103000b5520415003800c0c07911000307003895502c1e54908500c0e42000b01440f102506000c5c020300501e241180c48998100810550380e02010b4002002451203000c29 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 630314577 1250 630313327 630313331
    0x90f010f1112220b070f05070306050a0c021c020709110c0616020d0302070c170c06221a07030809010209190e06010305060303030712020c010501030606030b0a05010612090503090a030602030a 84
    0xb007a40e6440f0041415542c1d0707401660700f0184070340e035400702050100394203950038851024000300040d040e00400c1c0c8509180c900104a410030001c1c0649000070b040d1602901c50300300000b50003ca640001e1000461740801004280344c0040424480d6600c28410006194003c02003006042000001601030700c14556003210700c0075000d0b0404504030b00071000000c046000319036040021004004d10070a4900a40040d01d019503034120019540b40d200d5040d03004104051042101c42c41c80d1050f0000081401001c60342015034168040c011f140700702c4e000202402031400103c0c88001096044c0da07103141020f000982e450150881d40c0040341410b10500200c00b11f51800500300754800c0c098140980400380046066496200081c0da03d6000312401c10350155003403000e50300c000c4090064034000c60042c400020b42c241141400c0020708801001080b10343c1c00c140041007843d50110a2030740c1c3c030303000301c00002d00d20a803450300074210312a603102c50703502c01d568107400710078024180c1c0154003680c112181 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 630315827 1250 630314577 630314617
    0x2b1b1206030515041b080703120215180d0306080c060c1608060f0702161814010b030601030e0a0f060b0d0210211a060708040b0a0c03020c06090f010f1112 68
    0x3880040301468046c407109604406000c100140e080100030700e40743d0181c01076a20046041c51319092209080303d101e10342c0032000810050b502c00c240549070010030685001d0000c542400f50304c03a9100655a840307409003200040921170748000b48a00c41a440e00560741441ea141c0d81c2c131103199030340010b4a0000341d00c1060404219403e000040c45415428400e6112043c50f00d4411400070402400110740c0d0169125100d02106d2240754107400d01070b00c0d04000c10ba4580c140b0b034000408032002c8000101c9260b000403051030214505048407550305030b000354081404010b41020651510310890000d411505040340034464035005840f82d1004440c001c0700c2c1c0650b44601e000c00c025075110211580c1c0c45c184d8002c07442003d0400308010700f011801074840600c1c040d6109102e80941e80200f0b480d4002840840300701080650500c070b262080c88085a4a606200892000030311a0b55203920713803410700480c07101a03120240a00c01c4095140c14480c281c0700a910304013014a816408903400e00104820041 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 630317077 1250 630315827 630315863
    0xc03040c0f12030311190201020d0605032b020c040e030c061f0303050f041205060a1404080405061612020106060e030a05032203082b1b120603051504 66
    0x18204040780e00c070059400c0c0c41c0160f43c4040d001000c1800a56407421402c21510030b4200000c11407010540480d400144d4808221004404a0703210b604541c0c401e400000c07002210030725200030310340e82a22503100b80d015200300070341c20b0f450f01054403180d641207414160281e4882601001400f90883d06400b52450f5030b50381d0704c500100070300d141003441103030181304818004684600003400890742086103041c47c254984055805400050100302c0d25580400200300f917141c103030f003d01101e2101005d110400f90500380e40b440141e000d00c2c080e4500440c80841c8102c00d6107440000c2c4504250081001d09901c00c090701d00a019041074041d00003c00c5100703004800d54140019841c2c20305400101440c1440540054a400700c130013082c080c42e20800d800004400300c0c0b00a4010681c81d1494111201d10004695171400c50f1940c0d50102e0784c1e1365217082002030303001c0d0782d150310030760810114036008586051440807607005003016000a4881d200324104852403076a090813950182e80110450449058285 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 630318327 1250 630317077 630317099
    0x80a0f110a081f060305060903071209030305160f0c080115060509090601030e0f01020c0304050f01020c0f01030b01030e0a060b15042414030a09060b15090d060908030c03040c 77
    0x8420360986610a10304a4154038110f00c442d00b1003240d0000202e44280d0300d0312100d14007032064500e8100c40e000051040d0802c000281c0d4102d2105c01c070f0900360552851070320701070032a000e400a502016640300c244081002a4040f90380c5202d9802004140c8083d1030b0103080f4002c1c44500082d141100e850140401c03480e00a0742500c568041c0104001616940c0c800110090300314850840114810045106200b19080c0041c0c202d0302c0c0d4000040d82c80354030340300802140c41d052140141c150742041503c141181ca0b00140a40346000c203013004141d01520800403401002c0d210410000c078015903a1400c1041140e0700000384a59080b240c941925141214500d020321480c8120403031002d102e0300101c03c0b80048101c8450920071400c200341c00d005120003000d42d40e441151428030203a0b4a1b1142010072242d8410b40c01d13151829030f01607480742c00c01e00041030035209010b803452085400448100400903541c0000c00495444070b00786e41c60f410b02c007901d00ca0680040d18116044440c80e4070204d07200c900c0c2c0c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 630319577 1250 630318327 630318329
    0x10f0c020609040b0105071712160c0620070803010e0606040806010303030c0c060203150a0e090c19090c2102030c0306190e1005150301050306070513080a0f110a 71
    0xc2107a841c1030189801c10008180c441203031414480b05224050204688503400c81030301204101003652243c1d81034124100c20002408a440c2c2c074445c2000301c540361b52000080c400158441c03800141031442c00c480c01014000b0041d070740716500d0005102000c03c64148040c60484a0a8491042a40b201e00801030940240e00501100b603022500410120344682c2181041541e07505000c00c4200c06234540006a03401140d410182000c4400d000010382000c20b440c50040018480c40c1042c1d0800340c89103600d80f050074080034070a03116813040450303041d0203051650081646410800081c0c0000708060800c0c892545400d180c2c0e021000c2541030303000f42d8022244201c07065100d1a00d540da603082007028901c0049030800690452660216905e17030b5070300c00d0030b0081500c0c07191185000c0c600410402456402c18642e40b6180c0203100410441e1800942d03a03800c40c2050030421380341c040d03040398900442c589500002d400d11407111204280030f910b0300d1070034440e8090211a020080010f060114441c01 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 630320827 1250 630319577 630319579
    0x3130b010b0c210904060b03040209090109050c12070803030a051618030b04140d09080f030915070312020406031a0102011b0e121506040b0a03050c0d1718010f0c02 72
    0x8000d02c90f00441800c88080100203003240c45142c2840c40d5600845d0840f0304a03084198542d00010030300c400d40c6042d9020a03071148050307000340241e00c0e00c0c0d96003540b02d025464045000d0342114084042d5180244000000b4040c040304032505da190480c010303005090150f441803050b8880c07030001c02c00f0920030011031141e0042100481c281c03515641c0c81c04084100203205071595951001c0307643d10084103008413840324881c0d594661009050110309410030041107440902544100f00c0c030015a110342031101345060081004039290700850800340d0711001c1d24038407400c85c0d500c0003c7c0410f00035010340c401c10b1092070315000300e81d51a10f01c0005a00702c9500c0c21620803882c400e1640280b400c0c7c03265850801c490006400e80e6003504440c0355017440c001903200c0000c41e0004079400c008590615204101040c401102c010404c5491520b0703039a2140d07000040d031401074041307210920a200308000a81451000b5900e096581d4040003000e409607600402040e0009111440005482e4492100d80b10340300c3e0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 630322077 1250 630320827 630320833
    0xc030615070b0f101e0501020d0c02090628030f0c060503010e13061e060e130209040312090b0408070b07020c031902040f060b12061c15060b03130b010b0c 68
    0x2c070802c100c1e50a0400500804541640100104d01179900c0310348a804041980d401da0340e541d040000184c10510230300b5285080082c2285c50b900580c1c0d03a0806160014001d40340c2c0460810b4090800e41e130310405000c180403c8803138000000410041050301c04e4501e0044041e0701145032500821181e03403000380310f01c2d0449031102021403480e620300015050004c2c411540004c0d04130f5820f12280094484891030661190303240008c1140000501240f82d1102c2d0200e404c096180b2580d000444a0101400260400280401034044250b240e40585175a682204108003103181ca46820040d17a801041c003226408010801f281040d4000a604d1840503001009807070a03541800503011900ca41c120180e034420386036036241901e600fa9200c0c40c00175200d03c0d00101d0b1b0300c2054614a034000e400c050311039401600742030364603851080302c6050000490f40c03003050b401004052181400240443d50000301601d8000414481c000442c01e600e082514890700200b1116a44c5030141c0740076000303d10310103560360 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 630323327 1250 630322077 630322081
    0x100509071e0806060919182a0503073b01091e0509120c0115091b05031003032f0609010e0601050f100909060b1804091703070509090c030615070b 64
    0x280c5500118034991560440c00007c860ba82c9456000c40543c00344c03c4100b1881ea000c030110003181c0d8800a01400c41070f001440740c1c038504104104421001071009860860030075074104814090742d24400c00c400c9185040010b541c4804010780103001e10201c00880020f10081c0c0f00441c1e4180c042d03144588424005850301616001d0303041c00c0c075880103030010620f543c1d4032001c0f1003044c00000c07284041c0240c1c16000030003480060301c510310001d0054640c801c0c04420b00400200504c41d600d898183c82d0705107000340f944404800c00440d0301440c2e6041c0c0c0e101c001c40e00041c040d404000642644075050b00c1000b8844e683c0000c1400ea11444280101c0da00081030b01c40c01580760a2481628224000d18681640c255a54289500c11100b141c0c104030320390380c4005440301c42c20100c06801001c000707040340c0402200001d41e5501542e800600c03030400b150000400043c000038051026540d4194003d0480422841c010722581820350044405510500e108284c8583c0d0060040983d0314569009800240703603 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 630324577 1250 630323327 630323371
    0x1061805060312031b19170919020a08190c120c0b03150a0305030307020706091401030b130f0509060114010516020d0c0612050603010c02100509071e08060609 70
    0xc2c4d803008040e920020920303500940b94507144001005400058002c0180c844c072a40001801c1000c200c01aa04509100b0b00b8000500d00100c0c100d0b00100507802128120701e10307440410f281c0344c0107511103030081c0100e145400210700000d111142c1c10348114419814107444918007008010b03a840040d11510300c5410511000001000941e000524030082e003841d000f1002c0021120200b5800440b0075030004000e200003681c04010340d4024180c2800c10040c50b41c00e01b203a010402e0080d911180c101038466105098a88030130140075050181b08c28180301d88003180a003000a49410780c2c0180c03561003244000510011200c044049070072050350755610304100840d0402d03550410740420b0fa48440341c0c20060000079441409040240300f00d440707400f041e190400c500d84c1264001818a40264101400b4420283d0701040f03204148802d00700c000f843d9216480c0c1c00c1d2812410b5002220701c041c24500242c003000006048008840c0d840d41160501c1c0d640d9002d2100c000d2044d01d941e9102204d2201041c00 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 630325827 1250 630324577 630324613
    0x1806070206040e010f080c0306070f0f14040b04031a070203091e060d050403110106030210050c070e07050c1603111e1305010812030c040303050903030705030408010618050603 77
    0x250009180604090320b44003a004141d800303a128204d0540443c04c100014a002c1c0030304901880c00701e0241c00646009100500388111624012041040c1900c00e209460b0240d01100e075070320010b001c49a00c41c2d440b0407000314654068003055807146d0340410b0f404003580d070040c01c071380c80b80310740b6800b95042500d001c0a1006503c00940000c911a50707c420b484c0d050303100c680241c18500e501035808105802c0c9820068007016080d4170300491641000428005603c490001d99030014040c0780444e681d400441d02282000382d1074000c0441501c2d000184265180e10601500c0d04110320400d583c84060300340b07413124406000744001410300e103681c1c04031451032800c1c5240e456400c0035601c04c5242c0ca00c007900006c080c0304002542554240d036880041c8030701d62040000c400441d5525402e280303903081c460040300190041e03200c020208900010214501c1c2c40600070f413550b1984c032208881d01d482d02c41d6520f9000c0c1109001d40c8050480704003108200784030034021540240d4020b409081120808044901 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 630327077 1250 630325827 630325837
    0xe060c12070309080a0828020a0206090f0a0b03010501030522110109080607030518012304050a1403030a2d0902030c0a0e1014060a0c020d0b0c09151806 67
    0x1051240300f48000a40340c0080c003210070a1031040044941da014541e201204004c440d00c1e6000b4030300b03551104509801d400060703e503c11078040301c5282c0c480000c140054000c907501d0141607000344060b14001811402d01c000385040c1c071000d0700d0510850b07590010a44000b20034410705042c0e024980030150100300354a44600c42110107141603000d15459042d590700c0d01c60141c0b01c200009a50700c0400100c00740c140c5101422030f041d00001d100310181c00354200c882035502021010200c10480200d020008100440d1100b00e500001c1c0c43c1880414804540e1070f90411560303c6111400e280a0441c1a0100010f00d00102006031180c680d41000982e840018094a00700b241c251241310b413107031816614940d944e07004201010018050346000003503400d0001c1640d010b500034131441096440940d880c0c0040c1c2d11507090740d103481d010084080c00001d09040f2032440243c07000d01d00c103082c00f80c030340c0c00440200090ba0301620300c44004940003d540e40140b08400c0c04200c60110110300600918000340208 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 630328327 1250 630327077 630327083
    0xe1005010819050604151506050a0906051e03062b120f090b180306160e06040308161a04200f090109020c0a0215120f04321c0e060c1207 60
    0x1480c0c1c807c0c1344101541c910316005100030500c081000c050181d403051020010300403a241c0541818414912910154840c0e0400394039071a002c400184242c6452405481000d440d56403185004d02081c000e280078180720034181e0315280f0001d05040f6031406210312164036400c607628074419500d010000d4041b070700002903c074010304400404c51807940e0b0030003145014401c1c0010142e5030601e450703c080c0284d00303041d070340034024001404200f0209001d00700f654480b11801c0461858803050b454210029060034000060140103030381404141716101010b40f280034034820031040d0725121102000308501c1c451720030540c04000400103100b09207007900a4800c4200820486480a0b015400155840d140100380f4024000200c0c1c80d9603502e6542c500240c01c84081451002c0780c0c10a9100c9401103686c1202c20700344840c92111b40103054060032401135201c2c0040c0d00755101da000a1003224a18012942a90001000c42451080c50310303107082111204403a1100034101c003071034020042880e8000800503 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 630329577 1250 630328327 630328331
    0x1080609090c031c090e150621010303120b04140a0c031104080607030605010f050d09030c140705010f02030a05090f060c070801022218050a0e100501081905060415 72
    0x101d0702c143c80c100141942c500d440e015110710103500c030200034620740d034135400500721a542d0800c1c081c01140c0400481080b240c2a600b85580310207202c10b801c842c07007018251005219900d4000024164491301c4110348060400003030007082d400038200801d4600903805083c0205406001c1051000307554002d1900b030303405080c007040f4028a4503001c6140d4000d580034428680005040019095140c401c18020308801d007040300110b044840010001d00a0410071340344295583d424400341400754690304801580415a169584032041d01e050701c403d0580f203258045142d0010704040b0070300200a5403003c5216a480c41d0406401c0e80422103820105101e8070307081282000507080c90002442128017a20a00001680d594140343c0c2c0044050340090580005805581044c001c1500d404008034685039120340102d49902c40301080001024488070004040c407038120707070040090b0250029070484480d1170907218038001d44014004440315803400200150081000200001c030394108000054400c4180 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 630330827 1250 630329577 630329593
    0x124050a21020a0518030f0a0605150901060e130b010516080714030403121e080601030f061d0a380a1409060a140114090604060f09080a020108060909 66
    0x1480c800c82e030210103403c0000d000050844662081a5120180c8180a03802070030300400760408140c0311440140020152601c80c3d001c41c5e00c8100c210076180042e034005003201d110756510080603000e950f072018154021004003200c8940c4884520500c5820101a101e0501e0311380a1034044014111030700040b100328000b40010404601c0355000f00c200080241e0042d0741d614118200300108102d000940d40400034403c0789401480d40111100c00089194182a102e1780c131600c006174040c1c00c256440c0c8003020b24001c40001c105586100005000c4200c011074882e644985480341c0c280c40042e0354030801008062190350a06400c04074004105c6e4107200441d40360607900001410680859000800030480100c180c005441e090041c1500107074100e030709580261410100050b040540e52080c0e050202d50318642051076a58012204d180c140109260b54850b21500c0203843e0301031195130f99000684c0002e000c2030706e0600045d41c49030550161100ca0099813038504020010400a02688607400340b680 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 630332077 1250 630330827 630330887
    0x60203090d051f0b0a29370e010504051509030312040c0e0604151a090406030b0108010b03030a020c040f0209060a0e01030b180c0304021203120124050a 67
    0x600150f40c000301840480c402540b1810442d05825603000340300740c0c04548039a07151034840d8514440304800701501003511150400705000003124102d0411a03032003814844c1400c9400102a0f04a4400c455141e058540c3c2c2038000440d00340c0190300549130041204c642c003201811605001c0d00da07403d4010101c07890a113400301038010068054400f1121002010b00c203000001c2040d20080e484042641e00300324600c0d440040307082c004510320a0084243c0040c0010402c500720b54201e403841d00d0090000e1068a41d00d10348400c607007000b44960350640d441d25401081e10b2401100301d5402c40070a03401440c41c0790100c4208002007041c100861000c1d64204147c04164035560054003018480f0748490003111080c1001400755060101c10512800c070040f450071010782a00211a00000d444e80500c1e140c0c1e80304c0c400309071a507650903003a4181d4800410340b002d48001c42051281a5900e00154040c0048140c6030801114182d803620408540300340700484602c1d03c030b00703c44402074101d0b1030401d480d044d40c05 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 630333327 1250 630332077 630332113
    0xb070804051f02101404150e030a0c0b070801030218071b030c0620120a0f05040b010305071a180112050a09301209020414040b090601060203090d05 65
    0x941c10451110700300c1140542da018450200061010007044c00000191407004030401402400180701d990703984a2003040854941c4904d9488840004603035480c0d41d10f60303015010a403031032011654146c48000040a5502c100d40c994100c81d405809036401000d1100c441c580b080009101000b009400c1000e100c213454001000c1c000f544c0039880b00d61a072142e6042140a0310007040005040000c0c415159603024a04401c4800c441c1d10b11a101c003242e1600d411210151420100c4540603a003814144414480c503000024120780c401c4e801c0301d1810f07641c0d0f000610072088540300150600004d010b1040040150007044031064414502000010713a03994040d0101d803004c0d213440004681c1c0f09000001c0007202503945840300d04045100c000e214800101403228410714240404020503020751440d8048203030810b050080d8010814004280000a001000001100c00341d8090785242c01140c1d00540200d5014103031840c640c0a9440e0a1000c410b01084400c0c03058100c0f003510605c2d0241d01090240 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 630334577 1250 630333327 630333349
    0x160206030f0a18080a050901051b03030105090a0903092c07021e0307020d0807020d200f0d02030a080c030d0f061502070f05090c0702030a1b140303040b07080405 71
    0x1800314200e40d06040c10307000119821421400141601c21242c48007050201080c2d030705e861050b15116503102c0340040122118001d900e40d2940701451100c032404403c0000c030240d410380f642603c200d80302d982c130340702240182d50768140c0c06000300d07078460414001098403a81000803d40c62080c2c100f02030b851075070300d801d040310202d441d01c0058003d11080206020410445c50803d03561100031030a202840e00004d0300703211041802000710000003019011516003202c0898000d0300044150008180303034400200118592404d588201800a0102c446151602c1c8205010f0740103401040081804e90703034588a5031000c040e5080c3c0e48801e11139940100345a003e0741e81c80c04110100071413014030300750032091000038410b442001c0d0341240b4000c2c0a0000c2d041400b00c02c40b142141c00c4403483d00d81d03a26a003154451008046e426005080501c801d0099a0891421102c0c121810118950ba58503880303810b028400f040992682007044100110a66000a07146003402100c41500e0705a07036100060f414408 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 630335827 1250 630334577 630334591
    0xe03100501060914030709050709080a03020a111c060902060c1605130501060f0f0915080f0a02132309011206060e012402390d0b0c16020603 62
    0x100c00040c800076a002d0a07030401080c8014480c10680740d0b0400280d298030441c003446041d00c0d92100084c0034944514581401496054241c41030301400b410700949541c0b000c80c05a400ca101104c0002141c1040c01201c515107078010885121300b10150b0303559000c4c0800020a03079104200384503021201d8810f01c28070703520102e6218980c090600d030034203101c1c856000c00d0045940c10700c2c0400400c821904548080c181001074035251406141341d20341500d0b0940943c0000c45060503088809050503003140c00356000d5940300b00b081e0b0580c0c3d510440c100580c4140001c100d150024140104107003500700b0300c1c100b041c000744280d85100a070341c007003c00c2c4020f0f07090348030b200b0341040d01416005110070b47c0f0510018082100100c41c556040040c020410150700303181c1c0c200c50040c0c0007001c030114800e01443d002c003020748030400c058403000c82200001d01c14188107403085c4840148000c034036107000b0320030703000280c0e0002810801d9a80c1d401420a6904608084031020820507a0f0030010303628580103511400f4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 630337077 1250 630335827 630335831
    0x319050c12010509070c1e08040b041806060e0d11030f03071a04030905090604021308011a01090312080903070b0c27090a0e0708070f05151e0a0e0310 66
    0x2014105107049040d06030301241c05108507005110450b81d01030440189940c00c221250800399810840d490046c200303141c003400851021801040c1c02e00510010421640142c4c0740e800704000c00c08260084804c18890900843d00d1000c8038542d601b090310140120a00980e481241c0b8000140400c0c2001c0b445242e0b00b07400d4200007449810800030f001c3d99019013000300c002c15860301d06641c025004070500d001d450300ca080d4001c0041c225036690740448810301044844451055554040c081c06015540034501d49500d101c4050500355205840c61801c80350441408499101c1c0001c0a407101e441c00307000e15803640000c0200c440454200c20802c0d0280c100144900d90743c004018500c8441ca012100c101030301c00c0040406416641c2c0c4d1240036420094015002071a8914140d016141000315845400180109000000c1ca08404403540701110030554071900450302c1046c0c2c1e400f0510880171410822821039240d103030424400c202412005c1110305011001d014a080024601602c0030401d010440d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 630338327 1250 630337077 630337087
    0x801050604051f0b280206060901050312030109111e030f010504050403050d11090301060821271801030807020406060e030d08091c0903030f080c07080319050c 70
    0x1c100380c414568822585003000c071000014086481000400303224426801101290491400306204d640704081603030700e40d1800419442140c00794480c04200d441c40e02c16010000000740381e080124000d0000207506c100d5074178603801d0072144001002002d41a80702d41800b40141442c03204140c8103103034100e4424100c40e03103c0c0340004150076000c4050b000b40780039038102420f01c000650031800b07550141080d4600070900780710b40b10241c092401001a40d40c0c1c1176080083c00681148003140c08400c000c508810100b10410441961800e403140d5100b178114107402041030a03803502002c070089080c1000900801d0b0711020007103081c442c0002a041a0703100d14002660504503d098410700008141303509081e848580d1942c006915807034952940341c00e0091040014488100074045a4075480b0784588a4030001929003000304a018540001c47c00314017000004020f650213082c026101e18054480f0520300001e0740e0310094283c001038841455643d81101d00ca00501a034001c117071003442c4015a007a01c503 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 630339577 1250 630338327 630338329
    0x1b08040512040816080a0c0b070f080a030c1b051c02010e01050a02030108010b030604020616020d0204050109090201180503031b031303141014060f0a0e0c0a17130308070201060f08010506 82
    0x20713a04a50112485601401101d0b0001e1070b20f030102001c61f40d21701c4c1069281d020600380f0703070203a1b050728000500c0420005149648030707404d03900c615109540350380e5610366903001154448500c181030b01d02910343d42c4441c640e1610403641207800011b40c0d01d28800480d040003c1c0c00c0b81425500141c1d6118810390300071005004d0050240329117002c05004500400807801c0540100d009486000d4002003c1d003080c07034400003903450300e0602e03401e6681c1c00f034020011580d5600040006104003141240050160015071902d070388800c2a107025202c0c010041e500d0281410740e040710780c0400d24005001804207118079480b5806400010f0010344c06500a01c200803200080141003030003926000325568600100881c0725400c030802c59078415015035000c0c02c00601c0600190842416601940040c5a844200424454594042c04034044103440d001054500c030860710820035070407602107461480103050500030a00c203241c5a504210640000034a440e240c500701c3c41508400e8122044582d140c5080c0010303 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 630340827 1250 630339577 630339613
    0x30605010302120a0b0613020f0301030506150a081002130e04120809030a0504050d030221180109030218150616050d08060102031912140402040b041b080405120408 72
    0xf000c41c8809070800c08120355031a0903042c0045c0c602c0e40612030303c2e941e22103840a00e5049400301c0d0360000c002a140d40c1d5a10b8810f58607403048072140020742c40000b19420f20300340004504251038016000c1d2500c10030441e03202c0001d4002c540310180c0340c0d92130700c00014403407120840240100d0047c440380d4011903003050013900080000d400101160300070416915040d45c40b40136503054441c200c0d030480704915141001c9103025003100080789001e0040b2103200404408000a107485001c0d204580701e0119803500540b91507205110194000030181100c216000780c01103403503406250f0454211000e0031800211706c00c1d800145070360a100c400351b04010107000381005060f08044176450481c815180000000f5203d004100c3c55866220244464100c41e1b4041e004c90284484104003c02c01d0180c04010700d03110b034109403000c0c2e01072840c0854002c400c0c185800b4400300d944088401c1e05080004203000c441e1020000c20903250703405191803040000148400510081402030020005440f0900c03000103 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 630342077 1250 630340827 630340849
    0x15050406030b041a060d020d02040213060f1b0b010605031b0a110f0712030f050f0d06031115040b0f09030d0c05060c030105100e0415060522030b06040203060118030605010302 77
    0xb00c41303282e40c0030004070755500715641d03408590507034020ba500c698602c0840c1c044c3c082c3d4008441c0482010f04c0206a440e403104903103400c1304446e42d6000e08103020802d800400070200324058245a56100103110840c080c3c001160006011014030050000310032000300150001107030307840010504196803e60301c90810060f05c50304404405084860301c3c00360100560400d429008080c080c6002e140d001450045003902d2003808840c0c0c000e5500c415440005005007100d00084603032416030f0100d075003d03007404200111000134036a2060f02d82414507040c100c89170005e021050720007104224032080350300d05003c10340e50f03901540c803a84410401441c005043c54401040e070b102d248030600040125944202c00140482120f0030815000303c034507030102d0051b01d554680c0351241c001304400000d00356801801010031161501d2400d0403120b0990402e0054902448094286038070304010900b41d00c2d1503801160011414104218280c03d00780c00318072008800c0d8030070750302c65941b18010025400c0c02c0004074 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 630343327 1250 630342077 630342113
    0x14011103010f2705040212060f07170720030702061b0601150c03030c110a0b0a050a02071505100e0a0903090608060d120908031c0c050a1215050406030b04 68
    0xc1143e00701040580b24001c42441041500e0310345000c1025902d8404106600714a4281512084c0c600840c200e14004819160980042e5a030000c0302c54005080d00414010000c9130344000758a12011001c030000b004207001c24245020400000e001680c0300002070120507030002c404241c641218854509000301648020f00248904580d200443e61040002c0c0d030040c0e00d4100040c070291300e4403003160856a038605040b00c51003a0302e5050280144072401502c100c00c0850b05025981c3e4002080c000d078083e0440042c8100d40301c40c1c031115042e83c190800c6901191102040060300d40e10b58022160312420f6420340802e5503541c201000740342d48410000047d10050a11140c40d090440104010510001e4041c059241c8466164145441f40c407561005204102c120b9840d12101c0e401101704500c54045c042416160103c8803031058041c1041d112000c4440d191520103071440796019000e4116140c010701c41c9c1601c49008182c9940f6485080701841c002ea074083c009181c070745000084519142c4180c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 630344577 1250 630343327 630343349
    0xf050411040902060d0f020417060624120408220f0e0105010504120c090507050a0216050108010b0d1806020702040c11070b0d0e0a0b160c1e14011103010f 68
    0x6035003d600d0703107011039070b030001c06030400100c0d02d403440071002c000d000d1030b0407414110682079000b8402c3d1070001000c9004030b40031540b41c0074a102012881c0c007507143c80307041c14448590038440321001c440324402059105008910052401100e003100c00c0e6000c680e645c490010f04860302050180c1e2120408040150100c0103010326254101000a060b078001c0d4070900101803070868003001044000d00f481c1d40144680241032100d410b00c000081c2803500850703410b038018800c80c1c00700c000300c807860342c07003101268010384800c0d006900706824135006902003240b4044046d2145503000703018600e03c10340d0b403285018450041e01c804035481044180c4640041d03220400031a01152100e0708008514101144c482e012200d03610048600d1000290a21084103031080c0514003410050001140700c00e1720403840d07090070158900038420b0995655500030400f401840500030310b80320741e580c07058421f86e10038011000d00344c4100c00c01180c1420340d12181e8a80304615808401048840203a041e0300c8043d000348a04 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 630345827 1250 630344577 630344591
    0x12030807021b12010e060c190311070f1403030c070b013321020d05060306130605060a032102100905030304020904031704050a0506070503090d18090f05041104 70
    0x1d624114a9414200388901d414040c0c5004481003588050344078070751441602c40301c0c68107c45188194011143d4400345210101d402c1d10b03078500c070748507200e00c1d0419081010b00381100f03522406c4146110301012134582c00513140c200340911040024500c41c03081030f06c0c0e580c2d0721017440c82c7c061100001a030180b402c0d030500e039503400e88020400801524170f0005080401c2124041a03044820142180e050380c0103420304109000ca459842d0001e2520b5034184206000949610041c1682e0781022030744144800880040c2ca030004040d5040103400240091142c403030030f40c41e51a00711050300d9031905628442c00c041d24161103240c050242c0d030140125031200700001040c90b1a08c548034440100003d10603280b40c80003500305401906000491034281000720b450740340c1850300c55610980024191150700c500b00010341128400c00449106001d403a0182c0700c02640c452060340d244846524180c45100b40c071074049080d00c114031903410401802d030400f08803420f290405140c0e04800105907070099041000d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 630347077 1250 630345827 630345853
    0xe1903091a0d0e07051507110f010c0f0602120c0d0e03031b0d020f0f0a03060b030c0a0305070309020306091605120d050d0e0604031205061014130f1203080702 70
    0xc00d0302c1c88030307401c2c10340071a084440040140c20032031144c22040c3e00003140001c14080100303003409421203600c5078a00c000c445161404000f001ea8110082e913000075848112840050480442880082d11a8001600f030080345140703c503400004030743d0707442806404070301004e800480d4090076201107074080145213103007032a01100340c04244c200f0380700f240403000084035484405c240e41118800141017800c140c80741c80f05007051801d075002280502c000b80c142000416160354041c205c0c0d00444c040d2040600d480905a010345c06080000c0000301416510014031004d83c40c203204140c4240c0d29000a030150700b140c1081c007440180c01750801c0d170240309107026040850100007081948a80c1c14148175480321914000035001c0c042911580c1668007905041c0300030076401059a610410710b031a418030044d82c80c01c050049000c1113802c01c2d03000a52850b02038607215031000040008a20940302c4600007074a07510035184101e00c540c0441900d41408581d00203060b484a02150045e5035403000c1e01c41001200 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 630348327 1250 630347077 630347129
    0xc030418051f0b030c071a400605070201150308040513231008030f0d06140102060403050f040e0f012c041509120e031903021506040e190309 62
    0x20820401171100203401e80c24001c1000c0011080483e0780041c240701c0c948a443c1541880040d07424200c4410180e2001106210010180955032018031886c913013604583c40d800040c0201800003003c0d55602e00f80307021442010032640c0041d41c007070009103945503d454140800409501e00b185000e80c50680300c18645c1b8004142070014050031000e020540c0c6800c441c1201401071544214a24807000031000421202040580910440507030b08104142d0b07603004800d4a603040801180c0180c000d4000a40040c3c0100050110342e04903032240ba040640310b0110091041d0191134540148d0101001000440c2910701c10207040070050324024004a6200e550054159010b000182145041d0702070314030041305507000e1030340d00760000c0b00e14030401407a040107800c02c800240083e009002d001e2048400c84221a000c0301c40c541e01d41d006100030341c0544a220000d403806400c00f54800c0d22804150207182c0300708803485114050084c0e64040007024039020b8000d950543c0b0990460584510401407900700d0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 630349577 1250 630348327 630348331
    0x9090c010e06210c16030c110d0201170a0b030d050309061503030a11010b09150307172109090c0301060e0a0605160204060f080a150219050c030418051f0b03 69
    0x903010f80381c09525800600c0c41240180b0400700c001c0c051a020240a05620000d030f0030005014184030540e014840c001c0c025012122440640846c800d0000d00171402a038070481030f808034008100282207048403000906000401c004200050030100c10701804c490107010706600300403d40040e0880070f1100340403948034041d00b41c03540c3c00d2064407080c0c648402000c1d0000248003400130042c0c00c1d08e20707061000c0c820004841c0016400b91040d00c801084a0103040120080c81082800500006d18a401450300482c2c00c451418450760040c0b015800c02d803a6249164081d200c0200c21580300e6060900040041441e400c007213108010503481041001d4200c0d040351a6800144211214407103240003003005003005038042580c2020200000600e11008a070410f08603220303880b01c0680b4401c41c0011002d070700800460382002c07590300400d041c0b603600540003000c03001d0754074007640d007401e40d607080071034512001c0180701c81e0040e12201008480c80601c01c42c06100e0b912040411901d80c00d06280034164040 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 630350827 1250 630349577 630349627
    0x406080703150b06070b0108010f0e0c1507020a03050706081506030406020f0c070b0901030c170c070f0506010605030a0b030a150506060c010e03070515041106071109090c010e06 78
    0x11641460b400704030fa00f02916015001c2c0c0364076916030b513038500f0700040e1074244140400c1b940380104c1d07507481c6107490050b040031048aa000340711040c030740c07002c01c802c1ca51162000c0751000c5041141e10300507101c900c0c54200640c081c0b005415014034140015122040080203104950910881e10075581e81d0b400130f40ba0410f800000041c2c80380c0c02c50320180c03402c2c4520008100c891041250004080503410020f0141c40804ea800b40300a102c0e40000380c1d404007002914104500e0b0030300010b030b6900c042c0b001400006002e80c0c0510b010003480e4880c1414a5070a07080000003a10001c00c01510003914059146840420380c000c009010403a00c500603140c2c16011800c3c2059203a4000c140c155a580701501c03804030036071000b00b000030840d01400ea03480e48071020031161801407013041c103006141e0b28051841642c01c034200070740c1c0000303c00402c5003940c0030683c2110004c0400c3c28940c0f02d6110310140c80e1140c0c5100f0020102c68a040d00050310230302200d04080d20960b010040030103101c0b4851900d25078402 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 630352077 1250 630350827 630350843
    0x10e0703030e0114030417090414010602010c050903030906030901111308061015080604021908100807060504090c12091a010e060a05010e060f03070512010f061b1406090d020c0406080703 82
    0x1001000c0b030447d5104141210364030074141642c1455007000708403d68100c0c1c0b003a400030030203034000410a0327403980215901c0d103034150410b02c40c25005040410003141e01481c3c1100014480c000c80c0c40b1301245800005080e421080440402d00c00000c04110043c0c014408090003488c00b8900711a00500900f181803000030050b65002090742c0340c6032501580d000e6403481c1b0138040b0801d10203000811012048a0090515454100002c0c5204001c10204107803085c65036981d290a0504c8c4d10350015144034270035802040390162543d0402c0c030991264441461207595030031410000d0016002c0c810006800c111801e0101c0c1062000907034512800c002164401e081841c1200d50240002d0080c1c00f03060702400344510300004004460364080000d00200d880302052000c640d880303940741480012180111404203540c80031a0403031048071002006098031440e00e0035400207403c06a50300704803003a5021405c0b6400300071600320b0180c05114107081242c0944081001c03038946280c0c04e0382c80d400e902c0f000d00200c1c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 630353327 1250 630352077 630352103
    0x2a050306060d0221060118150b030c030c09090703050a0506120c0f1f09030c0f0b0a05090316080319180608071e020a14160e06010e03010e0703030e01140304 69
    0x1010448206500d804c2e0310f0a0320281d40c1d4030110343d1003000c030992000c0051480d0104694000251680c4601603850307815400c0e003181d0718898060120342c03000d8102c520140080c050300c00c040e40c0e5038a0350752241c142660045070a0500b41020b006450028000d9071003031080789a1480e1307031200007410441444080307981c050007001c52004a41880829104401c148110080c0c014129411910020482e8461740c5040341850741c1d86555404691180141c4040e0242002980a585d10845c003405098038001c050300d01a2400d038884025001d0f40d0f901007412a0000300e240e1600180158800d4030380d50326420121a4140d041c200c000c40701c0402e02030b40c02448a1381e00490700f150b00c02d12408410280d011601d005044205001960391502d01c0d0040350880c5a40f800703844042c50214174400d0900004401014690605042454464000307008504200142c2d48040ca1503409001c0d0800a0301c140c000f44c241c0b079046060003071100500078501818056000b8003a45800e07250b4003140e500c144c102805c14014 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 630354577 1250 630353327 630353359
    0xa061e080a09060e06041403040b09060708091216090902030606061b0a0305090306220311011503060515011e0e03070e09010e010e0601080a020108090a2a050306060d02 74
    0x280602c0c0310241195241102551550900042480c0124003650041000340c40b00c05003150f41f03109074058030f07640e40001c0c04034403420b00b0010080c0c5a018070840c0c2440c14181720202250030030044800c00e041c10b91105500346108000011030601601c181441400300c00d0154000c280c0e50900030780351a000300c100195141c0d0006292445a08685012058401d0040c40703017401401e50300598803c0307102e4011140840c10508640c1052110300003c44038400080030151026515503004001e10302495480340c40d0203080400e03200714030014520030031300020300c1c0c100a10400b6001c020422414184146c5c20702940c04044d4048401d90145800d2819004000c11100031908204242c0d01501003000c48405000049806400510580003c0d0008200c000010300c22203035110801c0c81410115006000c00d8030255210304001d0768001d0750402103c80d80340c85683ca07100d11002c001c261844204000840d24100c0030b440c413048005100071002004603040081c0000c1d0500369201000f0b1250700c0141d084048 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 630355827 1250 630354577 630354581
    0x132a050a030e03090a05130b03031603020c01030501031101110a0b0108101a0d0f080f0a050a0305060102070e0105061b19120806060d0903020f1002090418080304060c09120c050a061e080a 82
    0x4052300501501c0d1141171030541c10101307560841003280540a46030340c0c0303215540700e03203e828101d940091a01120342024401511031020362901e0038040d0140c10200c031302180b40000700c18001c004400c02003503180c0030040040126081a0555680154600442c08256941c4003c608842e500a8010107981e421845c10a80d24424440d10010031000401e01d0305510350040c002d01003071106501c09003c03503950302004a0b1209aa0b0140c25080c20388000103000500703021b40034140345035032000c0042d40950204040d904d00000704038403140d414010101107040080c0f110fa000c0d0594106d041c1600f45081900000380d141c0101241c03403100640e111801014903108001c40308600c40341c00c0c15070b41910790040c0840f0280d402580518003607400d14644804035200c0810107000345410500c1c09046882d260740360405403032508200801c00c0005a070104011a0031405441550f01c039000c90f485c0d01340780c001801000d0340f0590100e82400181641d00e0451580729031100f00c6001c031803604c40766550ba00445100 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 630357077 1250 630355827 630355841
    0xf1701290d2c0c030a080309010209040501030507260a080a030603020d0c0302031921140a0915030b01020a020906060d141e0402132a050a030e03090a0513 68
    0x1e00c182800c0c0040e280c84000d00041c2142d405900c440011540e5001002e030703a44014035a8542c040e07125404040114140001844e041400c420025161207100000541a40c01c286c0040d0f031140c000d401d082290541c0301c80b4100d81194061078000c01301d40008010350f240c0c1d44c841d1b400f401e460720010b40e11040038840e40c0802c0c040c5034010046d501000311410310300e80302c18450204a001c1e00c44c44500c02c840040d0313416524801d0754094454401c01c2d403c5881111701c44503020142044c012a00f621120500444c0d02500409610f035450160f602c0c54614103484005034000300c1c00c1071601e8600b1300109a603020035042449074066451300e0a5403141c1c80822024442c1c0070802d079485241ca54004440100c0e0a115801000c40700c03801606410052412800072800761030081d40681841c130904141d4105800140804001c207194036158207402c0404c00d462260350030240c00140b030010b8a00152905841220340128650303004504141c0720802240c1e81400500680d1f21030038803080d10039940c0c1260b4010b01 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 630358327 1250 630357077 630357097
    0x10f0c0807050715141008120a110c09010b0c071a0405041a09070f020f0309011b210e1207050102030d0b03030906070b061302130b16020a060f170129 66
    0x1003d90345818261583c5c40381030700d02c050245400e8100041e0724a00003168104005d1070903900b4139107402e001c003d0f14086519500d0304036034080c0d00c422020f10343d04c00c00b005000703028100d4413a40c3d411901d105035060600980154000c0152074420040b0b90300c403141520240c405c2900c00003803803e0408811484800c506150581c4880340900308a105a84014030742d040000903001ca82d801d9076410110fa859004921071140054503400e060403d407003002100d803031103030f001d0f29134056250103401d0000d4040c0150f40c000004100064100549400d180c07072200c000100500140c074455003400e0000f500d0744181c542460b0302684840003174031030796414011107140843c02451583c0d901911b10b001e20400100303d404503c60310f00c144054032240154002c407466414214000007030b1606001141029400c1884003030300722445603103551300523291001501c015010300d4481c41e02e01080c0c500c1c014900d410004107620000c803104010441040005100c80c503c1c407138220042e5482e90a0400d08009000342c1300300d8 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 630359577 1250 630358327 630358331
    0x10303050a02012a020f120906280306182a020c030a0b010e060a2115021201090b0d05070311060c0601060906020712050a03030525030e010f0c0807050715 68
    0x3a40c040019555420b0b55044d82c0d80940b4080c092002d08a03880700703c032040c0440d1900040000340c4161030040d00402443e00c0c07601c40c4034220808064204c1c208001d80c1900310100c0c3e61950107002e02c00350050511140000041d041c496240c40000b030721940880103110302002c501584e41154041e0090020b18081c0b1b002400f06d030b940121a09060428590030301c40c1c01903052640000c100030341046200d40d01902d6500d0703003290700c00700080f2220901c0903c2400035203a4200344966415020110300040c54111417400500d8219410302c8505011104035160080c0308150100380130300003c0c070201c0c1c3c110403641c00103090451020910042075840c0310780d40c5844101d00400c4004515181c2140d240300a42c0c03200d07070885c0c101ca51680181c0700c1d00b40d90500040e21580c003038004800081d200c2d401040d80a11900340c1c4801800c4455008281403001411643c007083e20f440100c810003800344100c4492018400b01405424042c01d4060400140504a0400c0003000a801f0083c0000f01040604001880381c007 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 630360827 1250 630359577 630359621
    0x201021b061c1406040c0912030212070f050d02160302060904060e180d0807090b030709032306060609060a050315030307030c02120f251701051e010e010303050a0201 73
    0x1002c0c00820001c0844007240c83d0020100310242001d100781d09600c149074a40188003410304d4001c881380122030b00124114803038007040500121910000d41000741c410f40040c5140285460140d0800c921080c0d140c04550001c030590b011213145810710421250191001c50340c2d01e02d4030021401030240c42d0080d04100012a040c08031400080c8071441012035444207950301e094070048100d17909441940c0c02c0000640145c0184034076403410000b150043d103581000c24100b550783c0d5030814011300e41d20884d081032a5030045030103426400d11070740d644801d013242c40c141703405138440020b4114043d0707901a0040000100008461010010071085030b204010102c1b82c68111600d40140000c1c078407401240608034030f0698040c08400091109044460034001d000074100b44500300d4401d44c0400e0311102e0b003450751000000d950b822032200c924691448c0001042501d001b601c510800030110f03000358034112402004110343c01c0d2450740c45054961510b4402d83d41c0041050480c0076042a6a80400c03880300016 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 630362077 1250 630360827 630360877
    0x90506011e091415011701090c0f081b070c092a03020304030801050f060708040305010501150f0210020f1b0c040c0306030b0c0c030c030309010b0406120201021b06 72
    0x28040105200e400c070050590340b038001c2282a107078008150142c0304002d1010800c0084030103950f40f000c01040c50004513207501c101003004941820392017410300c60707a2484040e110300c2d84001c0740d281c040e6803403c1019031400e0610001001c50395141c8104203006000c00c14100b0805c0003408d11000f4012a4018482c042c02182c50300704081c80801040c1c610f0f0038007042034071824040e009031303841282c15482d10351040e0701e400706100d00c042883c80107550101e410840c030350010300c042020380b0246004a000040c690f052181c011484410b20040300d0510641040801e070301940010031103000c0c1840c500c056182c2d41c0300003601000303004040040898040e03020140e11a031100042c003000c241c5d0300b19418084001602e100b90700b00c4115000c003401807500240090b28500d0240300802d541d28405007203a1601e21010380ca070342184c005072003480303090351102c4074130006182c207010b01c03005404117200d6003c0701a00e40d80040d58410078120058504074240810354031590304c24059411a0386ca280514140c424681 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 630363327 1250 630362077 630362099
    0x4030b1513060501020712020f09071b030509180f07030b060d090506060f04020c0a030c14070305061602011506030b15030a06030c14013011070201020d020c030d030e0109050601 78
    0x400b030f840c01803088803000241e4400e0345a0002401d50064041005c0c01c662000348186400f0007020981844260b410306100c9500b40900d070510b0300d001c0ea81c2c00da06d03280510100001c942d100c142e048a111035901c10320401003409142e06420400608001480368180c10104c0e0041c000d41000c0c01e4645d10380500807080c4200402c0807031007604201c4040b03411010311740c100022401b400301c0c1a219940604000300010b03008010003480d8901a10910018860020b2840d2401c0d10680080f03841c4c0d0442010701c00391059107003070610f8400c42d500081c00700702c903900f04045103011248555000c01d5101c9841022035114078083c80640d204d95000f140d0390b0315107144010050803c80c0f200b00d43d00300368810002041501c5003854030741c0b0741050b5114480e0150b203040691050b41004c88800744641c43c2c5203464100b454520507000c2d40045418050f403115080d0001a007071666209610096400c03030f40142d1841e542c081900e80300506241800200e03410a245014014100444024038901c100c1c0d0011405501030 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 630364577 1250 630363327 630363329
    0x305280f0b16020f030a030b03070f08280201020604020f060d0c023003062710090b010203210907080f0c0438130c0f080105010c02030304030b151306 66
    0x40c0302c001c1e021045001261389002118802d40075030014000a800944690001440c20170000c00700e03018162944110340c00c8001e281c0c0100d089034889089040c01d407200a5881c100e01c0ca685140c6503245020750000f035221a0010002403180d0800400c05c034583c0d0b600c4080c1c074206a40003108010380498100c0c040e64076074900e9000601c1542000c42417002c0480003c02030044206d60b40ba850075a15000d061210181300314250240d4000c00d064583e18130010901c02c00d101d080d0013500ca44100385052a1034040365500e080d1541150420460320003000c4134241e42c403040c07000108900c0c100e1341c2d808107070508045c12a0003403400f600400091500e0400300040d000600c0314102c0d0700300081c003041e41d0000d00d0525110b280300c440c241c0c095030800c0b2600014001c9036002c90007810310014030381808030960407200040d1401021070346880341007030038580c0520301c10b002d0310007800c201e0000000e0b600007a82e203008902c4024842829840003c807804004421101d140b1000b1b0210100c80080081d0744010300300d1 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 630365827 1250 630364577 630364591
    0xf04180609050f2502100b030c0310020d0606032c0309040207050c090f01060212030406091406070e041806110403140a061a090a0207060603020a06050d0b0303040305280f0b 76
    0x51503c013550030b9416031090040741c1483d001000c0c045220030850014090088241da81400340246082080d2000d0102c100b50105103100103075034a80c08002c5e4400c4811682026007058a404c0c071003592031509aa45040402c00c641c8507617003d1240b03103029440c620818234042d42160001c5524000c2250001e051440103104842c44d00150f658400c0c4c0d0b06000c0300034414000113900402494985d43c03440d000441d000346c05440b000c214540ca549440e442041240d025004a84c400b1040204580e0303c10208040c0343c10071907003032080040c01020040c88010703144003d44000e94641000b2150113a00f02120021984074850382007150f4a50b10a03511018111010350b0618100f6070220080600d4180c042d140b20b0f8000e16084003a2244500403009411206084800b69603c26012016a540c60041d42c0180820b980701130f502e034040d04480c015544d00b084c00d00c2c005e0f0720901c42400011000b01d00440c0c0181684141c28804940108440a0411810019181404110207002880400101c4900c1000 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 630367077 1250 630365827 630365851
    0x804120506060d081911071409060a0501120c030e0105092103040c030b06042003010807060c0b010e090a061b0f020a0203070b210c0d050601050f04180609050f 70
    0xe11002404408007800f8402040b41c02d08000340110309100c68408541e281e1207143c2201c80e052510000361130003c003604094541c0c41e040300c40110914207501002d42c0301c1404d030342e52222a0710b00800030301040490422544040d84588104071118880d500c500d214640000090007603044c03000750301d901c90300c0c0c00400d4040c220440400c0106106446d040324021380d8002c0d10240c0052454507451403040c0050015030307005842c2c8000b540c07000d140d07108810800501c241215920751600722221300e0503116600c145c0500400c41c40601c0441c060f072011504450b1500c082956541e9116007003400c18610900c0104554600149000c88021804504035102c0132900c6070503000c001c880e4146d94400c04000000e500d5440785209001d1468198050444000358035a000700031240a001c0c090040e070308560442c0d050354007003606540350103d8028070384c00000a007806c510744185c000c501d08070f92049006154a00b000d400505068040e81e9201c01e0041c2a102001c100c00c1c2080001449113a1060310b404203045 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 630368327 1250 630367077 630367081
    0x20c0a021c0b1003050309010503041118011401230a0306050303040f0311060903060711010e0d0512071704080f1e070c050402030603150603010603080417060c0712030e0a0804120506 80
    0x10103e41c0ca0068903000030040d130425002d03100456040d48002c1003100e000340ca20300c98603001e0f2178914401d8508240700b010300006604181c2404264002521074504010f404e0014002e405002240c424151001040c0c982d915011207000384c001d05100d51203240c040c0b0001a000420703100c1041d18005680c4201072190808111000b001f075113008402c6140d0303040d00008042280540646c02c85102e1038403140c00030440100f1001141c0c140404c09180801017800060440000a40c0c00d100a5000030203050071804100140103203224a400180014551940090f6100c40100071006076050980011040d0b00e840895100c80f442903000046d085a840c50324440216031071816000b41c0f44285000307002010040c0c000031a01e02d403507030017070303c0641c040d581c6980200100c2c8100e4010f0014003003801c407049000c113104040629040f001040e112618034140720b01c400080496403820ba4106461401040703014500d25080d04041403980300a1003004005800951100e581d002542c44c02d01130ba0640da807039 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 630369577 1250 630368327 630368341
    0x90403020f240a0c180b300103080f070b191505030d0c020f031002030f070801051c110d060f0b09040b06091b0708031602030702010210020c0a021c0b 66
    0x51140418107400c1e107a0403200040d01049284d21061035222103103000c031082190951440142840707500500c2c1001c200060140d14480c0705ca8489040b0102e00da901080f00012100301c0040301e02c103000060044d24005414400c80c110001a601415004500c0c1801800c02900701501c21881c01e21004442c0c0c2048004442024941d1050049035005800380030080500700c801c4400c507106a01c1240c1c042c3c0c16114948040d1001c010300082000c25205c01a581d04107400a0a42c04100500e00410000500014400398549441081c10581440e000020b100c00d01d18000c04031002072031f034203030300704056485910500506030400f59650004c2d01c010001c01404005008580710102c401401040e000808203d90382000c041c1e00340d0041120300404d1a49e000720410b04070a40c4240f8040d94030150200034005998156108003200f9021400214500001540040d444040130540720080590104414903007042c107001c034070507281d8028054141d00101c117038251260801980c040d148000d10320001499 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 630370827 1250 630369577 630369613
    0x10c1106040c0501030b010201020f070b01031a07050d0507050415121104061d06070c030b010810090b130c05031906060501020712080306060403020405160e060a0905150405090403020f 81
    0x1e40d400c0412204014104401034001e032181d120340c0c90440d98200882101c03002c01c50003520aa520030244034030194903509000443c2d201404580c046906030006011031070780c006044070394002c50001d010072142d5400c60107454502903139005040500c013030300c0911482c5034007002521140b40c400004100b00c25125003c40b2507400346000341030115011090301d0000b5032840049504084004000c986048c00340d07a00c1c588600b206510071103142d014480180318840b8107008490015000610801400c00c0d00d440318903000d030010380700010f84603a41031054140700c014480c00d030241c0405070484241000c0d42880d214180c040d100141c6d402464010040342da5880411a00d080392000d00c2400303030007541922524146e500141c14664442010000000181c075240229445000403521412290203c200050401c4c03540e00e02051041c0810082420403d0b0021207200c181c0d801074501c003031044203000c28141d262040d5040582d000190104110805500195080c00d01d8141002d4036035103c200c80095035 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 630372077 1250 630370827 630370831
    0xc0f0303061c1502120a0606021506011b17090a05040911060c030c0607090905070801060504170106030f080a02150f010603021602040c03021e040f090507110609010c1106 75
    0x781c010059082072181010102c0c0c00794140d070258002c81810201c0403d10030072688a0220504603244a600f04895a44d6621501000340072600140800000d86500c0316a800f00041039141409070854003841e074140011109108154482610310b5403c088400400c007a4111020b080c1c46440030402c0810641458010b0103507043d4041070031088081d1520401107540c0100c92a0011840144003c8034415420000d06018410549400a0b101c0c1400142419107000070100e109002500004000303c561183c00c40c0e00305c40c100185265541240301e4100e0141c162640058000c00b01c094900f014030400d0300080000700c00580850b61310111030311000c6d0b410941200d42980941010004004181c080e80090034170315203003511141501011b50014088660f00880d040000381c4c0440d10360303510380e1082d03801c400c100800c1030054146441c01d40b940c101c02e0034034001e100c0b003280c507103011407801401414680010400141922200c5c540000d486008100130441ca00010b00902c903100305d10f100101d0254 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 630373327 1250 630372077 630372079
    0x1c0206030f040f0c060906200a030f2f060906010e04060f1805010504170c0a08130f08060604112a07080d030f0f0b0603040f15020a050c0f030306 64
    0x604556400c90444500d031802041510244080d10080d0000b60204141c00060300b1651a1311006c2401c2480003030000d0034400c800d40f1038001454804540b0400004d1400c0344941c146400e101940c03554600704c074101040701444003d1000881e006807045011100c281c400c2c00c0040032500c95650316a000d0396108400c2c80340100c1e080c01000400c0104805802c42032048965820100d41421080119030202841f8102669540d64410601003042103c56400303507060b4500c1c20f1541046400d5440c030351100c0f00483c0040502c14002019200402444446d00080104000e0307015065540c20310541c85e04401c584e00b61186151601e4001c250034400e0030346200c0b40e2800c0c248540006928484603080030070381c0c007840d0340c2c1c481e8030310004032404100846140d8807030554020514001c0c44a861081d1040ba0382c1c42c0302c1050070140c0c4680c03191a64000e807540039421200180c544066030600003000001210400314180c00080c10b001410740060041940c8907500c412502c465501d0f0a4058482c00143d41207 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 630374577 1250 630373327 630373339
    0x12060e0105060919060b19030e0115060503101e061e0905211f0608060403081902070503041706060a1a0d020904020706060303020607110303061e1008061c02 69
    0x80350011390410104a2030100454001507429140d41540109412a140070030755010038480d002e452550600980399044205c400070b04c4401104030440800141a0080204000300440012400b20703c05c26010018154441903482225413540c0c000f100400c940100c402040414030804860700f07810b0714455060401d039445040045c1080100494031f0320700401d0700144607504040c2c00914400f0b05c102940d00704182d20894082c482c541c00c031001c0c0d50203503005001c036800203405c200109401c031210a034014110304003081c5100e54280e500d40240545031000d00948800b0a01040d8400903048083d5884403050403503c03140c0c2c4c0c0c3c004208042006d4050744010307100040246040e004400c01a001c07090710041c0c00b504003141c0c640030070f013242c000c20300c152a6140c0319007080040c59010300032a50828858079180309414010b0088039503d100c047c0c1540d016142520227581c90a041504030310300e1220040c10580c0e41c0c400f40900900d0000d0a84034244900b00c21690000d031911409a4002020350141031 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 630375827 1250 630374577 630374581
    0xe010611121615091a0105130504020609010309050703120507060b0402070201021b01140706050115170403180b1201090c02071d130506040506070315080c0d0204021312060e01050609 80
    0x142003140801d0046101449880713403800c0340020903650f41402440703030100f0300840540c50203080000411603406094100307498030b4140b20250b11603e08403075654000f800e0206100c100761810b00d02d071182980c00544480a0441c00c10200c3d54072030000d02f40203020300c00501010804034100f00480c402c825000340541e12681314010000c0042000c0c4020380303014100a1500e5501d045040750700d0313210b8801101c01aaa070700051100e011040c00422448409280c05506180843c1400a094601034030140c1032046a40c100d0541c41c20540381d1102070082c1c0ba007841e40b00c00c001585016286000e00403409254140010076102c9440010100102c8142c001054003080140c00b0440d08801c003c2d00da0b40380c41d5480d1083c0004100d003004242d0049200d20300505d60791a00b181c0045c1111a085070304140c106804a0406c0f0388400054520091001140c00008440741d44c40014003d11079101489440000b100d00050415000805601c826004103024002c0304803c034082801c842084402079070141e13181c40 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 630377077 1250 630375827 630375833
    0x501050a181d0d030e10060b070f02031f0f060b0f0a081f0e010816030f08030a0f05070e030c0612190e0709022505060612070e0106111216 61
    0x1041c0c01440d500b85905401008a0301c0d4542801207282e503140129807550281150a03004010205688100090070480c641c1013040305041071046d943c0160400a01904038001e550782031100d0aa10b403400c1d440710500070b00c00196503015000020020100504c0d00c02300152036407001e811031384d10880c2820154a07040210744241c85141025111195554945d510003002041c1c00003100d002e40491074000400b503240080907460181d046207160102840d81c80c00b00700007a170112501c0207203684102d1103030b101c0d80c0786c0d01000f00925207070106425040c100720611840c17a400141540700003170140c00347c445d014106000c1c0f0019100c1c88125041c10300d40c400006001d00032062029a940402150205020b600103007128a00301103a000000031641c005502032540481e9803410b0035035844070817010b660410030f48907141c982d00004e045c1d9024003054114042c445405100c0c24001c4d20481d601c10a0702c0d40c44038801080041142c04850640c8070704190645070a8100040c0d42c1d82454003070040c64011581d507 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 630378327 1250 630377077 630377081
    0x40f06050f010f0917010e0d0905010f050705010920121207020f13020a0503060901080c03101a04020408030403050f0a05060103030c140f0d03060504020906040b070c05150d0501050a18 81
    0x807080200300065190b001c91414035900801400c164050004544040003424990172301221810314418805012020002640c0180e90764521030a5030903e03c0e2200300c035042c8507000d00556603005100000c040401340041c0c11080407010264400c0c0c1b181803e12500a180315a28104610b1100c200003003808010b00524004450704000f0601070400c1019620341005a0142c0e0811040316010400c0802041501d06000384600e0041101c60010b1031100700c20f2010949681014203506001600d408921843c0c03400007020401001000e441103581e16560131800d03860707420030b0208075581d02802c0d41000c420100040c200b20035a070808040c002903441c40d50141d51a17480040d0403106400d100c80101e80c4614103100c1d003003040500c000074001d07083d0803050080444006810480c801e0b44140a9402c0ea521080c060381c0a0315259648544e890380d40d814a5141402d0030360245038407140f01e14501e0501da40302d602070107a091089030305020366601d540c2044848161405680c0c00c0c05818265404100626 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 630379577 1250 630378327 630378347
    0x306060901020a0816020f06120f07030b0d06060f0905100e1b03041b06020d17060a0305031306110a080313020111010516080c0a2c030109060b040f06050f01 69
    0x500445104030840e54a01c90240c105085c07892407210741038441002d6003008081440c5032001250400d00e05041545905c040c520041d0072000ca0b100f040c40002c0c0034900070303404080d00d00001001c0810f90440e0f89085000740441d80100400302510f2000010000304501a0034024861112803205641c2001c0446440d007000911015080c01c03141080b0b103035010784c0f00c0110f0045004d10003140880404016407102e102c241d91150b811984403941d642d070b500e6808805000400d0205075039540a45070440040c00c09011500080c02500000601c8400555a03990a1040344c2035030f201c2d050744192002c806611142c0080f4003600390b800030000201c4070140701c4901c1186038414106046101c4501d650715007168000c99001c611180c02d03962030701c0382603005240c660b40f25041051207454900e840703100a1802c2c8102c07100c084044450101c0041003c2500f90341000c4200c00360007004800032a0030110080c4c000840f040707009a10701020b021111155000704000d4400180564001e9028030004503440c0c801 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 630380827 1250 630379577 630379579
    0x1a2502070506120601030e0610050d0c1d061306150311070f0c050102010b1c030e0a08030c0d1d01140c0a0f0f120f090905070306082b030207020603060609 68
    0x142520110715955600c0140c02481d00c801c100c16101c2c604100007504542c1d83c1c01d41e100480d40820700700110480f81040c200d00b035402c25915880480038900d02480340640075000314051a465088090300c01a40300c031454400c260841d18440281d20440b4000d080700c206000707a261581d02c409044081074025000320010b4000e40311040d00c2c1001685400b00c4851345880d0891340000d20762801c101c0d030340e4240542d0701c0c00b00c412902d10071b210560150320341c005249140d0080c00e20400004012165603000508002011060252541d49200c40507158a4142074180c40c03000c0b401040c013500318400725000800c0f0b6104180c50710702e417000c0618841c083e0350b000821401298800e42402c1c4c0c0010710124070094049114400c600c491800b9842e00410340b00880a0240030014030803070b00e420305584462070300c0c22500c1a250005040d2102c0004402610807900110424429515180d6001300c400c0d002e000401c40016204a0741c04201404500340e01c00c4280c06507200e5002d00121f00315287c4a4020310203994 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 630382077 1250 630380827 630380833
    0x5040b030a1a030f011b092303010e0f0106030506073204050d15061e0e070203070b07050a0f03020301050102030703111c080108060906011a0a1413031a2502 69
    0x3600181c0703065243c0254020740c5c2d46414843c82c8003140b00ca0f020064000c68249085c000b420060120b600400c2140c0800265001c6a03440c0d450303840a50200200800d600e090741c003080403c0c40c03103030b0191610348012100c9100380f1000a0302c152045e0712603000e022169041c0d8400b1001154120030002c00c1c004c0800d03407002c1c1000002240d03510381d904e07113030414807c506400c001d011090091089507801d0380120f40904001d51440c08080d010020b8100390f8105141007841a100c404c012071035402685801460381c14402c0038000480c0d0018040d0183c500580c0d03400c2c50b00e07003074490110181c0c0001c0c07243c140540d209200000000b8001d452a20b540c824242c2200d03424401402c0e00c0c11000c5142c01d1241c08105800700500c80244180701160303020f0144801005103500d00b0300c50340c408881c12400181c01c8032000c1209214188900064000c132902c40c01903a813612241c0c40120039a04240c07000301c60703111405102c18031a02c032070700805118550f0003194805140035036100120000c4803a0b025030441c0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 630383327 1250 630382077 630382121
    0xd2d02120114130f0606020106120b01030308040f0f0b06040b0a08062a03130507151209080c010e1006060215070c0813030807020a213503040b0705040b030a 69
    0x30f03943c4100141a210110b0203d0b045107000030207400c4465a40104030640c0078510000c0c0450900c00943d81100d61510705541c46940c1c500304880c490421100090409076110360020030f01114246040c02007038115008c0000d050755900700300b030b90b00d01c51007510f03005d410280024180c5032803008400a403402c940803001801e01d65507201012503000311a044988002c400b28502881000c100080160002c812045c20110f140d801c05400240503150007a125500d0b02c100c00c1c200301c82070094507040d20b22403009004a1781604402900c42040c009500310061403d8400580d031403002a920482009114520300d860710f62003011130780140160400c1d28080c0d002c020070700e442e1190002c000c00440c00342c0070251f00c6a005104100c004001079000c1c08c4203411419800c02580b01e0803807200c2001e0391244107890080360508600000c0200346258a2090040002000582103607200651280344a4940d202e003030340c0d035858103a17014050782c028808a06414000107038031044680c84000003801000002010b4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 630384577 1250 630383327 630383359
    0x4020603060d15090b010b0a0512060d05030d0504020103050c04030c0506070201090e01060c260307030b030c100509030d0318030e030a080c011b110a0f080d2d02120114 74
    0x4184490243c3c144a0340c1d65140405101910321041d000d85584002d042c03610f003072280000c4ca50300400742c0c09090031240c40045046a070312035803c40a1141c0c020180d0b5103c020f4035240e00c0060400300c0341603010a0030702001412514510301203405a9601c0520306824608000601ca240c0d000200f04a0610031440320204807459101c2031240280310039918a80400c1e90303403420a615041444204a43c2c0b424070070640071485110b010380c0e038010268a0001041c00b090341c000f07458410000c01042c2c00c0000c0841e801c000d01d90080041c508078500358211000040203244c1207048600300107410a030314040e0140e09001030310414008403071040c010101d65122209440d4015079510055a8000980d03440c084184140e400600c0721030201e4150134801880740c0803d01203030b180d18881c00001c1011b400b00560000b00201c0405076091616040703003c0182c1d5101100750001030020041c002168020b9803800d60040985000b200c0e05074204402905080c0d00c0c10300310982c3d8a1098000a5200860b18035031001 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 630385827 1250 630384577 630384593
    0xb0a08030319050105012106090203090c0f0d081606020c060114010f020619110408030a030c0206150a05040209011205191404020d0b07120c0504050a0b1204020603060d 74
    0x644401005140e40e810401c0d00d1400300168072408441441c00d140040107141e0300b0240d80d0001840e20800e03040c0d40c085a00c140740003051a41c210003c2d451020003481001d000001d41c8c40c1c24110165038401491007040c0400100c1200700b000280341d131604100c0040e040703800d5020520810312804016080c038483c00c92450518000360800b0881c0703a10b0091071402580c0c01a4900b03029001400544a6814946070081c80003960313128803122203440b2045028101d50303200480740103003074042c10b0303c2e02c8000305c40f001406040c0e045d8400006204110201e400d846100c8080f0003210700c000c00040b10a0710f003406010180d04a40300c52414408100f0a0441003281c900410748603124442e0034003174100c0041e29820460b5040319407180b08440039400c000041e12601622020150400c2d000e49441e510100121200080705100741c0030030381040c51081100e40c0040152041e03400031500d8000c0161244070940c04c900030100c3c000020440312000c18090b0800c0c100442c2c0149000d099050300100680712011 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 630387077 1250 630385827 630385829
    0x102070f090e1915051e0a0c0507051b04140f0118060806040f02030f01020705121308030409020316030b06090d0320031201080a051c17150109150f030f0b0a 69
    0x803803e00b8444d81d81d901001d00e1160540c000010303040035204880304205c3c0a00c1c1d0b00d0040198080d10307030b0f0728401e60042d4001c41c2514032440d0b210080700e40030207050b4124200c1d1601c035503401b4041e50a00002285465150f00481c1c072a104450138135480b68601a103070701c060800c1000c5018090358820010404090501100348500d00800040c1e89040052050600d0004d969800c80000d074070500c107040000f00003140c2940d1540041641c252541c3c032007107020402040640c419000341c403000500045212b801c2d0080c51003a2202108038070300180100c0107506440c0b11102a562025003009140424030741604034003002c1e80079151030005d08000d0110300d8165401e001c480c9420380c0c00810f401007030701c0d0240400c034054101e800190401d40100e60315a0380d1a5001000900324603015441084407070310600b1448051401e45000351514241980059000404000c040340010b103204808030701c8001130034980b8190703405907a9000d400c444022045004141e203036200c000041c0c80f440c420003640e8030562110 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 630388327 1250 630387077 630387083
    0x50f0406030b18010609062001020c0a410709060603240b030402210105040b06011d1e1302040303020d080a1e0506010c05100501140102070f090e19 65
    0x40c030b84203038000c2040b01d6168980e1488a0300c4014010f00c881035000c0101011151035041a42043c000e60450301504400400d80c0f00541d8070200c2d000c0b08000c0d0000324000051f0094202c4241400c0c00c15641c0c03094200d09001ca144603420811441880c40c4900e0303c1c03105075428000790b940154552094106607113441d800f100010383c6420300c54244d03900c0002c2d49984a082209600312581c070307040102c07075030f80002400a403183d000e07101101e03141c2480d01080301e0000c01352402004140381a00d002d0303000120075a070b4180010205d0b00b00220110710010300c81e06889005000d54a82d003031051501c8586410103541e00d81000402d442c50300041c00d1400034001952094001d000d02d0250114001d00c3c05a00500860020341000004440000c46030905840201c80030000700b2596140070044c0c50602001c100104144125004007503810042d03404503060318003000341060f40c0304007103004a99450460103014a00b06d0410010040900b0726400701c40300b01c018005803481442c05043c01c082643c03c105c815 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 630389577 1250 630388327 630388331
    0x90313140d030f11100204030606050f030a15060512100c02030f09010c061d010b030c030d0203032a070c060e01050708160305040f180e0724050f040603 67
    0x90410401a016800942008401030380d240140e48005001490703a050040d0522420280100c065403042424036020741600c001c4038948a60108000001e40c054881070760464035016004c0b80920300040501c982c0c14009005280c0c00c009503d404a00c0702400f8017403806180c1d550340004041d121410008140300c8104090f140450f40c030341d4a8420b45000d1003401c01103400401c00307585035007030507002d80b10048420704e48003041c5040c40c40c000008000c08410300e1344480190349403050b40c050541158003200819030a0310311711459502410b66175001446404050780080c00043c60220042005180c60841407a10f50701d00b850035200e0350102d510881060ba61501c0d07503217041c400180c2004003207030ba10b0310a103030503032421b411906c60075014011196001500c0070707036540480c18944030f001a500508140000c0180c2a540d440c2125035808440c50108100c60500000a4107403c2c0490018100c2d00c030102141c8010031104449002c3c0c0c050700803407600340f00003446000e50a04606014001030801a100 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 630390827 1250 630389577 630389587
    0x20c03100608030d1e061e05100e0405370c0801032a0306022d0705150403031b0c03020c0a060e0d050102070203120a1803030206040f050a0204050903 66
    0x91504114603458148580da041500c100034003680007044680c56051510005034140e440c042a03141d8584a0074990000c40c145100440d5468074500c44003803803c00c611404840945d40c0b010f2169201050402e1030104080288a034010b0030141c1015611a400c0c01c0d00051900d502054444c2028181c40140b00d8000407619103100403455100f0540c800c84281440c00340380d80b645d80d80f41003c1c900c0c10b0b41c029005960440c0640d41850911800d0f01941d4004c4043d034540c003150100c481e4001510360522601c1d8010744281d1005807040040350041c03074218000c1c00182003500199050800041c00841c02c1603038843e405154200000c41440084d81244e850a908109a05009113051000d8284a101c0d040f00c140c2081070382d810402240007110180d41c0034182c1006814281e0080c0500c040181d0107005510105c03c0d120514401820b04201c180c803800c200022445210b00c070b1403882d010007400743e841075003c1000710b9098043d55034400d02c24421121364241960124084d00c0307041d240c2c5442948041380c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 630392077 1250 630390827 630390829
    0x28060609061d0708090c0d020102011b030c090e3705090c011d240d0608030d180c03020d0c03061506020c01030917070501140c040503100209030634020c 67
    0x2c03507103400c41500e01c1d1091140c140711100d00e460720001e009141c4120250f40c01c0c0380440e4001c0d0425040320180089840c142d05078541d015014084074803060300056480080805c4904035080203d004042e40d6581c01217442922010300c1407040302d041071070b05412000e103017984a400c072406118490f85500c005844080e200310005020189005c5140d0b20120b400e0021512a850b030440003140d20015100503640310040030b10b441c900740304410091140c2ca0a0050102e072a8100200074200f0004600081059034420840c8040509207040028811480140300f040540340c08090114006c2c01120540c1c2e00315174956800048910502d01c21150400c000420085a038040c404001c00d01001e00b020300050901d0b65452980341c00e1508030300141903010401d4010700c10b09500c84119106555509006401c084081c00f00700c0d0014403406229105d0b9142c030804005d218001c0d42c401070005401444980c0b03510780040c00310604285640d5200300a0601a404092003540204043e00d441e0083c0800b408010 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 630393327 1250 630392077 630392129
    0x1240617011820250f060504030e03121201050d0f030509040209060409050a05010501110c1e12060f0702070308090d0f0b0a060905010b0a050a050f0720030f2806060906 74
    0x21a0303513115480000200800c29082000d01190391004001070b440d92149410f61b80680025485a0984282001246844030000040280320210b000300c0f482030f0b903180d04105403170b858420000e02c1c903440715202c07a00290190005d07000f5010000c0016080884080200d21660803a62081c0f0341c50762158103010f41101d581c45510b025020a182052500f20179464007551405180c03215030085182d5080b454441caa000c0c0c3e101e6141c1c01c01017060000c03010800f00319a8030007050303542d10740b40c058000201e564240001803a40c200d0fa40140203a05200500041100030f594500d000c0c1e402c04a11041400007444181089d0710403585688002031150074240c0c1e0400302c0340d05030028030303041d54100811a002d60b001001e540042000c0c0c540241d9542213010503040600407628010441242c800d1400b5402d510021356491210003503003229a509000c2507450380d110702440805440018800b08410b07004a040485080c5501580d000709100e65140c658604903011030b07000d080401c40030090510780036552 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 630394577 1250 630393327 630393367
    0x3060509010e0c101b050d110622020105070204051f0603150e040305071202030d0e06061f09180b01090b130b030a0e01240617011820 59
    0x115000700725507404510015a1002040070b058800c6a882c6a40384107076101e250a80c44070301c00c00e5019005c08802c3d16160350f0318403c4209000c08142802215640028002076a5101e45018074410214100c2d64010b01802410302c1416030400030100f04036009038035103014850055040c00c410b00b0500c223010000c81c0c80403909030001c0080500b054a038a06208031508500f00b80c1c0d0b00c003001580d850f11645400d40e141c2c40fa400009011795039010211100710b80100203058200801e403024422050100c0d00c4686038002140e07039540c41004000c940ca0031038131810744404420307806e04101c038507152030300403510380d0840c400c8403003d00750b4a070312405201e5688602428001c0c03480c00b42e00d03070501070300503d07011011049000e006001c22002c8001410380700310360451100114400020040c002c00884894000b081c4103420651481144c1c0002420304e118060154040d080c840c44000b95900701b040c0c80100c442003041781480503403620f14402c1c20015643d00ca86420070005843d5a441c2065901e186082c0c1803 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 630395683 1106 630394577 630394591
    0x4060510270b090613090206130e04140708060c03070e0406060203030f2203030f0b1c1b120f0f0c0906051f0c03050c150c0301030605 59
    0x68640714200301840303200a01c244000ea10501c580c105080e52400d402101c41c0700703042010308680e4040342c4201e2005090500c0e101c020303050071407a1403c41d0801c03a00303074203210140800c03c1150040420000c0c100c034046d0010398035002846445442c000c11030600b007500000007442c413512409400782c0008000340108000394481c04000d6032904125159902d58540c1404190007400703202c082079201e02d80c1c03402d94565800b030b0fa600f10043c2203140c00c0c2d4220541c590780e0008280d5140c0b0142c0840002c5507101c04d003510818102140d180b074690600d614a00d1007103805020540800c1c41031044641c102c3c64440031164a441d000c5680600034201400000d28a40041404030aa81043c82140c0084594800c845241c84000288201c18005440400d850021940001c0d004801074061000280b00f179500090300204c0744001d900040751039200c007200010040c800c0081f540301c5c507504440 = true := by decide +kernel

theorem cover : BRFrame.Cov 630215827 630395683 := by
  have h0 := BRFrame.cov_init 630215827
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630215827 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 630215827 ≤ n) (h2 : n < 630395683) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
