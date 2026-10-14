-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1925
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:10:33.951955+00:00
-- url     : https://prove2.me/submissions/6e45f608-4c20-4c40-bea3-173ddd29b75d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 346043165 ≤ n < 346223021 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 346044415 1250 346043165 346043183
    0x5101106180c030a0503040306051b0304110411070f0212010c020606040507020703120e090a090b0703090501060504330e0411060409050703020d06150c02010c050f07120308070219 79
    0x254481428482c1499495008046805110741498400d8581c1c0141c401a14001d10b8040020155600580c01070340c2c20640118551569550340d85c0c01e01c2e008074000c2d88642040c0d0341c1004090040c40840204206030081c0c0070410790b0701040c81000451010070b1201c40c0c2c113034100032039400825000a18a6009081114041a1603842c040c0c102e14040c0725910151207101c3c005010140f2942003110700740304200c19901c540b010342e5924070b560162a91240002c041c41700000001d00880d00c02c0c2c1c40391315a188a003001142c01d560303840004003501c1511a49010161040420901d800d2032146a114001c0038541008080752822800240c000c00040003d01740140e41d5555602035503030350044402818041204200c6414030000c024029040307445089002071070324001003155412035401c0030101c0829aa075075690b100381c0c1d004560501c1000012030710380c0f26010109410702c40501a207006444e04281c0d814a50060742401010490054010010341d00007145c400840c83c240b400c100c0845030090314035 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 346045665 1250 346044415 346044451
    0x50c150f0d0504140303100f05040b130f090b07030b04050610020a120903120c150506031002130b0313020907090509010501030c1b0510150f0e04051009080405101106 73
    0x11484203420080c60000380000030400030a107d103440000c082c0e40c0703080c000c400c00d236440704d0a2100f02c4020110b0300c1e42c0441d89180005051050fa003014007103403522440401c22502030b90300c160f40310605403010b50101e603c0e00721850b00e50900381710b01e0343c1c80034049860750540400302c0006134440c0c100d0900034080c50042c0c0340d00c011107030103250010b00456000190030320310704c529080209505000c2ca01107600c149940c0300c000340007003507005990241e80020050301d4012105044e1500079403124811030008001d481c8005514a002e5000e144a0004400000c1c46c0311140e20400c40c503420003c0c032020a009141009101d15200c2c3c1034502c0c192a82800c0c00144808241030a48900581c0940f40760140e807508003c3c020840701050a030481600b030003061242120f10380342d5850b0300440780100e5007000807030740003002441019032415800ca8080c2041c0d4030700303c0c803003102e40d01594070150003580c651000040c00c002500b041d006615401440d45072500380c0203501184a40c075150041c0c85a01600725a44607 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 346046915 1250 346045665 346045673
    0x18060305070219021f1b210507050c060919090b0406120809060d0207060507090501090b0f0d021b03070c03020f0604080307150e07080a0b01060c02030316050712050c150f0d0504 78
    0x814503038103184182c01480c4441b03601e03011060b00034282d060000200208a150581e40c00364041e00c1000c0d500030003903d22841c55905002e2941c110181c01644a84c0d5032500c05d103004c05280c1008090980407101160f00400d807001d001c1a540c842d030100314800d49280744807010070503450580c2e0381202c085500d0b5035613107404990703080a4082c580000d80290300d807406204174640c20078420f00407200280c0b604180385940c0c00c00411140103d02d40d040303910104025041e4540c2e07865004004c1d848040c14013500307104014620321301d982c028500440b01a140d181e418019881c1c0a8040c1d8400703841221880e107040d003002d960b10384034000c4a030000c001045a40c1c114014660035044000c440d02d00c0001c441d41c10399106401583c401d02c0d01c4080ea40068003800100c3e40380e10608030052219006001149000398615400070400c201034010784081c01508008141c0000c0681c50344800303401400103140b420044410042c6600b10211107208195080012503402c1031a08144ca50308010314500061039a26410 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 346048165 1250 346046915 346046927
    0xa030207080d0c08091203100b0c0a06060b04170607171504050a090c120210052d070510060e06041a030307050312010e070206010b03060118060305070219021f 70
    0x289402910b8103106001c3e2005900c950441c0c842d40680c011100c0c842c820740110703d0310307100a40340709403441c0c12648140701a501c000018014110b05908949443c07541c2c0d11200102c82254020f201020070028080003c1040c1e200881560156180509203500348218054541c2c0141340c1c81d40c1d0f4680d200710000300c04c0b000815003040c3c2804054414411898500070344402402051021240700d11a410302041c0300181c0b008898045034058048407548111420949503a0410340360582c1c1c40007090381452080fa0100d5a01e40e1401c0b10114143e1a00e000d0702e4020305085040c10b0303030903003e0314100081001c58007400401c2d40050040d280010000d52084414600314105030103182c2510000519008100000004244014002c02c0c1d4010690300c030340c07410f40d4101042e19a0340059201c1c3e4010f1042d9602c0740e00071500070005040c1009100c084140f1050180000e511410220341d0712410442c0242e0180700528621002c02c0303400d8102c40d207580c0020f40341180402d21881c000d503140c400404481c0240 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 346049415 1250 346048165 346048177
    0x100905071b26090a080307052e0e0703140c0a0605090621041a130201030510080604060c0905010203070312240b1305090609040f1e08121006050a03020708 68
    0x303092440c0d0482050b20894107507103c40f00720390003510000f80005400d0004419650310390303401005824604441402d6102e080b554102401030b80f07400c180324808103461440f41000c401114000342500f0313451401d28107109a20f008154203581c11611400010759240d4450506590141c1401e07030311042140b0100e80a4003402210042d0341001202510440126056080c800c61041482d810161202816800a005d0503100941d00319a07415200300150b0183c1c01481d440038401c501e20180a580d901030364607010080d80c050310801d40d00d41c91460459807003210034000d4a0280000c40c5004c1540e42c0040817500c0b403080c1c620045550312a015280c01140c000341c041807403d0002c400145032512410720301030303100440905465000c05d1000441d418040d8007a03105440051040c9000e503155107a00e254044080d00890340103c42821001e03290304102d8580302d15500500016032030b61924800d080b9015806026400c00c0040c44508000e410342c840f00300c40e0a030301c0d01e00e4003689501c81407a00a0b0300f80511 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 346050665 1250 346049415 346049453
    0xc1b210a170c0c010609021308030f0a0c050a0804030f15050712110903030f0d0b0405190e010905010507050a1412160c080d0c03050a0b0f01140705030c0105100905071b 74
    0x105d0303000101c001c2290042c0c242001d130351149000c42d0780d1764a5060354134030400006210f900d10501a000605008a81003140a40a034054400504541e501c071b449682c85504200c40480283caa000d0034011030403e07019034076a602204212908008074040c0081501d810102500342d00e4403481e100405030754050b1124081d024003100c2d158201014108100e07003190611601c0c9500c0e110b80301165103014010140201483d507018900302e1090340c00c0c030303025114000450301290740340c00100e00003a209110303652049440f0390324140c81b000e08640c010308206c0040102c10b55940188060706c4419003444085801422000d00814200c1c110300d02568150641d80014022802c00302d03002c40c03030744000e0b004070140070110b5500b00503564540510008070340c1d4120391308d030b0020344c0c5001c01c60b040d502440184216503a820062810070005030f491916640c132512905504d0b94440d024400c084106452600c080c0803d0401400645401080104107240100c58101003412003920720b0700b44140300c8044610b58007d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 346051915 1250 346050665 346050671
    0x915040b0d03110f1513031803060e010e06040b0c03130506040b1504050709090b030c060313050d0f0c03080c070506040308010e0106020d0c020402030c1b210a170c0c01 74
    0x307076050282c0b000301026560034050082c0c0b6121405084042181103029140700020780c810389820a80c544000e6005008409001c1e075118203084a5101000c501c0040d8403d55020640da00704205003820344403c41070401241d07100d0414000044c0c528419280e000701c6640c0c00c3d0380c407136459211800c00c00c1c01000b00a8901e0107040d05010500c880c1203041403042c494502144003860b1400c3c01e200072140229282ca0016005460901149070103400c1658510401002c0ba90f0720309000000625036401070301c2e2120b51804da21110400c0040c28002c4c004800e0b40380c2003850901c501c0030b90103080d040c95020018100102c0100141500180e8800e80f6040740d00201141c4035803405150190481a00b80202c0040c51178040c00022002c1c800681d600803200b495a031103514103000d40c2400081e410141c400880c0060501c40143d07880d00c2240025914001d8200a0802013400010310150f00c806011003403042c04104130500c4240d401840309500e9180745c60141c0910b03901e0304100e60040c008e00e0410002942 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 346053165 1250 346051915 346051939
    0x1104060b030c0c0c0109080d1101060504020a0309020f03060c0403150f0903020a0c05090702122a0a060c1e081302190f0b0301030302120d020c06040812150915040b 72
    0x31203403020f400302e020348904450054000d80019109045141b165605a603c680004409a0701c60100e00fa5041d01040001c05c999859400003820798003c0d150702400680e13502c00f101d041d40380040300b21003100c906901410140c00e0500649119100d00e000240c8007280e0b180140750b05c20510b0780480c0351031028503000c02c8880414074000f52641c4c0800001d941304441c05001081c0c03440c0018880b4000d00a50b0000d100f2180c034038a1b8103a00303070044660304040b484500b03a541c103a40e00130401c800718442d071400030381902c41903440c1c098222907658821701f040220441061a82c449076201040d409449818112590f5aa00f80d0018801d60340c0c82000750000c50780302d921b8082007580090201910301c1b55450f01c0784a900c4616006503400244005001684254004000420700c0402010901c041e0500585407848505419140950664088401d400300284800c20305510700e0703115030400ca10381342e0b103d0f042420074001406c014014048007580030785800d01c25099581c55220a1000744064030301e5118031 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 346054415 1250 346053165 346053181
    0x70c05090109061d010b160f02091008060109090f030c060902040e100605010e030606090403111b01091e05060a0309050f03040e0f070206130f0b090a0c050613031104060b03 76
    0x600703840b0b44a001011101c0c22038002500e403a130103058031600800d20342002c0861100895001d040340b002e651030200c84521001684070310344954400d11561002c41c084502c0e0000ba989003180503801055003a2a01c0345207800507800c06151000704d605444c240030303425942d040c060700a18815000a601903d0502d200e4088000400d41ca5401701381e100b000c10441e603031480155080703805192030310fa154000b1800280b0b40d1500c0000540c00500900d411900c13812406c044500d1301e10410341e210580ca030b90304500510f543c0e001885101820100c0351824141400d1114441d0080c8a0301030140700e018041342e14200c40d4420b91000220710742140449881d84412000c07503440e540140203030080b0100000014003001c0000e08028021546a40241110341d10030208d00b0000c10031420442d1145514907111007c101416400790140b0031440180920440c6071420007100007441e80101d001c1d035001c0c80040d2444900c070081c0c504a03908040c1c0d400c0000704600001c2e0060000f40c10400c112807010040c00622 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 346055665 1250 346054415 346054421
    0x605030109060c020601154401030c0f050d110402090a060305010302150715051302040504110306090f03120a060902041217070b06061b011803090920070c05090109 72
    0x3d020207409880303160345c07500021507160301910403600100e102e00071300ea44c4219642c441280e00c0d1000203009591249040f40e500000912102ca044d0020229070040c0280315140030104020b03d009504420128940804190b04c10300c03075800a094403030040e581c1650383d02c0b40e030112203030360900a00d54001251910030242c0180002e0101b80c0c0503000c5c844540740a02d00440403a18a9a00044220f40300d44032020110094400145080c18600c244044400103031528000c090155201d0115848114401000d040c80c0c110010441d4250f54000040080e01d81c2c0c01200300c82013103503494294940c0340d03194500403014143c10391142d205a4400540058030400840e240d00750140f06103400d007070100c0e03401403501d424041c0400190445c1c403150302085051516000915a5920211a0035040220f607100542111105100c064040014003c00010540e000200ca00a0002c018007000f10100150001700c580e100e181203030b04e0003540066074205010350062828024017005011142075a1074520340809 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 346056915 1250 346055665 346055681
    0x3020d0305030907031e0b0a09240204030c0b07030806030c10030b0f030a080405010f020f121c0e011b03050f0c0a05040e0709180c020a0602221d010501110d03050a060503010906 78
    0x1044140008101c0080310340c050312000c02d411001209031945510440d111138501cad0200030484c50707401c0000200281e0030702d02000041049e00e801c285c407a040c0c3d05000e0224503005000310310a40001483d103149070b450700d501041e1015136180c00140c4802c96000324803000e006070003c82e0700d0310800c4440c00030801300100400a4590030399030000107108070001039031342e012401e0341c081e0380d9008222200c000030004406001405005008002441d013140a203200325011505540400e9458121000724003840110f000d95880b40341c17a00b0042d41c070b406000c010381e054015017007410030440007458042640c0310b40e0a54024104504034580d1070b0500d040017802c01c1c01d0900c20391501074840901e40e401200d1394803481904254a80140c04100300e26950742c0001e50209a038a465000c54145601c0d0384c001d040401b1000e88036008546034889420001c45404032016400181000740348981050080d44c0440e81410004044c2404901c60312000d0340175024102c550403080d01076190007954030500000790003040c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 346058165 1250 346056915 346056923
    0x40801050405010e1905031c0b18010f05060408032a03040e01150801271b021b1507080307090302040921030c091205030408030f0301030b010e0103020d0305030907031e 74
    0x215820403001e0f98420980c6640091b0454106111061a124450550760325541e0fa03403600251202c190000940c40c4003401d03502c0b007031843c61f50b0018003d0010004050380541401c45045080c2440c00b06403580d01e104115401d554031030f208060b40d1303210340410201001034140b2410750fa2201d1300d40c503280c50306000910039444460300e1450301e061040d01030300d0064140ca40410340b40107804c0d0110003811b410070724000d080c900a035a65008044c0016002c2503400300b140540e0181c1000640c0641d282212810501641e10a5100d10701d54100005018202c6000e5940110403c1c1c0340d50f01c520054585544690000e0b410506000b0800d04211758a05160400e001a020045464860300d004508645c150b0058202081c00c00c00300344024130300324041011081c0314204503458517031550802410360300490348000c131400c4044014400c20007201d01c000d000d440b614001c00b08540c910740000fa21210b00910203400d000380000030503401c520501003000616040445c0002d0b84204d1006501c2407414810142c03 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 346059415 1250 346058165 346058173
    0x203161b0c031b0b03070302181804171207050301210b01061b0510050912191b0f2102011107030531030b0108010207020d1502040801050405010e 64
    0x1a2580d41a111103000e80c64000828140840c256601e0b00c0303810710000030498840000f0000007410000c41c0c40214400c074a03d41c3c0140c4c46020707802501c0c1a0b0190410028810f001d58500d0202030820489a90741c09900440c000ea07192070100c0c0c958140e40700341404806620410010001256000030040d4100d40841c0e801e58204028070300b14443e010090324006191459480c0104421071091804480c0b00c0e4084042044c4004079503290b84c600b8591500d6031481640703507000c1210401c01408006542540124040d01d8400b21581c1c11240c0d98243c03d0503400c0c040e4828040c1c1070351103003020711044a40d007e080c2c2420076200d804c041284055001d041c5525040d40314458142c0c51041c0140140c85a4005800d4142007196a041d201c0d9088041507207000c02244001105c0e15188801c0b034281e148403e0b65070401541103007007003d61300700160130407d0642e004202000045c0c44056507203d0035a04041d246201081d20440030001e88290351248a00390300b80018002400810741c0f009000b06a034070229 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 346060665 1250 346059415 346059437
    0xc03080609090606130b0a090b01090602070b0910030b03010507030f05100f0905070c0b130203120c0a0f03051c0209090702070503060718030b07080403020106090e030403060209060d020316 83
    0x410420703821034400304190003501c0894036a040440c3c0003d42003841e200040b40c00d205040200b408140a5806441640d84415243d107055812800c440040c22481c070241040034140f0110b07014078460030315258010544400082000c0d423203603000c00041c00340140244054103015000802404828207588186850301001c01c01c0d61040a0030740c01282e01d11136040c1c1c142d078903000e410b0340140401803da0080c401a031080c0400203840f03076020b910074092550300c0c20080340140103141ca0100d100c64a0300702e02000300b000403040100080c3c001c2d4500d911840c001c0401d07887d45802c030f88502904a05003011000d0742c0d114820164240c024000c10340c01034500d031150740e030344203c1241e0350b00c854420303140c142c0c006038040b609507407040100001090046c0c1310a00480d13540c0c1ea0b040f01260086466500203a8542c090100b090780c280a000010050b104042c880d444030a8141c82d100e1255106c0280000e074001600030f03594230b910080d603110300b042c91000c40d00e0385010380c804140c0c102890312000014004141c0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 346061915 1250 346060665 346060669
    0x91305240f011206030c120302060f0f1602150c0705010b0411070b10030c0905090d020d140c010605060c0a170703090902030c0910030b100c26070609030c030806 71
    0x158815448008103607101044180c030055900c5828200b406108649416010000c29950f500490050403600028030540c3c084e418000c1c20000c000c1c001f00500440d00050000c0c610340d10341a0f43d0000380807000c2d60389290380c40109902d40305d42184448000100141004031004211002c0c0c41ea2902650090014000140070030044070351000e15400e280c0170611460012502c0d8100d1564020714248a210740613860f03403102c40c1410083e82c00b220880d5110000c0129400d018001a0361803206400100000c800322030004c1e0901c03080410300c5034281c00101e103803100004250402c400500b8085c20b101e503183d00740301505071204014101074404000b602e6070906400c0000c811207031120b0701a40c400c032a0a00301100300b006540080d041c0c2c01c1d4500144204802a03035030a1412500c0f0b162524009540d844050521481d10704d42c1c10440b003440351500070003010840f100c40114824010326545004c4030080320800242d4003e00e0f50117450240303401e850004068000210004482c02611203029950301c4d40d01f = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 346063165 1250 346061915 346061971
    0x8180d0b071b050d0c02060c060a1e152c090706090b040608070f0c020948220803120c041203081005310905061803091305 54
    0xb4810b0348180c0360100710305e2140ca600700110784001c0000b80303042c4040951030f19103c42035841200c000d58407008640c40e05072600c40c1600b080e09040341801707401d94000c205007644140d445a4004004032078405102d40c00040d150b032560b1000c0ba004054030b414400006a5521194060440480c501c40d00204d030281c401d800b91000c91b0b500ea40c415000355a04a8215119040415050300b80315440301c90b1f00041c3e51740039021384a440f43c042c2115000052031000891880c1303980c2010003104150395030203e07100b9078043c1d500d45070071182c01c041c2c0d858a207114104982d80003018541100700b0001008120510007000800d400010000c4012040d03c4208104070b89100724400c0385618580b00c1103880000f4003990740311b684240740e038007070360800f81d5500045a1400c1140300c0850780512801c40305000d01100540030441445c140c0c1c010040e4800340d43d91a540c03014080e01c541c00e401c6210000c003c120100f001100c800c254081d005094014490f940c05010307100c25200d07414201c14107110a0003e4203207075 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 346064415 1250 346063165 346063217
    0x320409080702120f19050a17070501060501141b280c0602010605210c06040f060305090102030f0f0c0c15010e0f0c0a050c100606020d14090a0308180d0b07 68
    0x680500681c4410071309600100d02000e408451071f0140130f039400c0100d01c004600c1c00b04001c0c00b01425907a603010745045800c51b800b0fa0002814071000b0f0b078200f41840281c6081d2841c03240003a9108101c400499807a40c41d18a885001210200c2521900050800101c80703111a580c46030255101154680505900b61100f602495421030f621440d0b00920000440f5080d50100a01007528941807164001c5081988250401401d039082aa0100642c80e07040c07090070f0303226500310002c60440c103100c2d0046200c0540500500c000380505008a1079205000040f10400d04541045440d8000c030b140e001c281c0d4880911440d00c500d401c1c80c00140f074400e2070302c980c14420b49000300307500c3c90100104420b48082d0041c24607a10305100307001c0c03940300401551089c8005000c55400411450881d40c400412001b001500c55800181c107101102503031701c683d4610790981c6c0c0d00c100d8568807400b451400303840303101c00d4a0b0010361005000009400344076201030702c0340c010482550741140711038202d03081c0c1503440038417 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 346065665 1250 346064415 346064443
    0x6070c03080903030114150d06151d100e0105040b03040605062d0112090203030f040321170703180605010503010f09030903020d0c03122732040908070212 68
    0x40e02040c0c052800c075802e041c0d61800e880322103090401408c0403c0454096412210030b903442424101106508140980d19021041d2200c0d03034580080404201c0c201d00919101e000e03c0030090b0f25224580c0104141c601400d04110300584900c0c140c202100509820b40311140500b540410032850740101724a0021004101c24190b816000040011a8801d0040d009071403807555640075040103076410700c010040151070025160300e40382581458500780e8800030740c00013454400b00c0000c000a812a03246009901d009000b2007095880c40d4003500074180e203d192010203540c00d203980c02000303c07691103241614400d5008020285101e4004001c446d0324010140103e00c0c403440030801807401c800c0d144006031013501c90040c5543e030703955810143c03025100d03048086081800300480200381400c1c180128400640700380180b42c5081c60100d003600301d050303c62070701c074150440001044200c1c58180000e0200036204008820460034030401c142c002c0d1400b02d201791050140040d6040b40015900021100c0c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 346066915 1250 346065665 346065689
    0x3020418140f0901020c0a061a1f0c0309050d12020106151704051002030f16090312080a0b0310150e0f07110a02040f0c080a050403020c040c0203090306070c030809030301 75
    0x12900b8129401400900783d44480d0b400300900d4038110424041500c074244145000b01d00e081c0b0044000e20420242c03141c81c0c0c0103000b40d0704030050001c100c880f08148000c3e24244410005200d0074121040c03c00740c0c015613000402d5140071010403080c240410321808583d8020044151512581c2c548164101440000a51200c03414100e810746901803941284c451000c0b211040c46041024081e138200300c0e0180d101c209802d0400c40360304903180304078425621500c3e003580e03280c0c152342c0e60001c40f1004441034002c100b11a000110391808562000b80680c80040403210708004043c000d10151a0b40c0500a02d59442041c0010f03105800394481e5000e0361102c06002e02c00d543c0c1d068111100d654140c101c0340c0601c145440a00583c40303a10580344451500100804e51f0b00720518050422980a400c900010b440c5c00c0c108804070ba408215003540500448000c01e2811614800300d00d54000d60465a625029002c148100160000380c404000c07072003501c07a80969a07949600c16103d02003441409040d907a = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 346068165 1250 346066915 346066921
    0x150907080708010b0d0e0d080108070602060f0a0507020a0c0b0c010c030501050f0d0c0e0c0d0b01110a141e0d020f15060d082802010e01090f0210050f03070302041814 73
    0x4090340c0a000464000c172000201c54a8070f106041c81d04c0f03041342c00a0041004c0400510038000148107032009018903000030305442c1001289800c0d07a000061074840c00d16a290302043d02980700317104001406401c0480403c0c0d081c2c965501d94803a910540c10155076618000401d41600c0c020f00803141241c600400320000f0728264030510101d04802a01161000c2c1c400c2c60101e8400b940c0d044c01070091051001c15034981e071486d041d01044466a40300a8148200c00c800300205180001d2690191588950b80030700480111061615001412040c02c46004601d0a0302c540d10381c00107003d0030210a640d0803101c0085510742c2013070b100c551198480540014090024840f07091422030010064410300010385409943c040c0307030461410f221103000d002485024040a0130750b09000703940f224803a50000300047e404d20341e5101048600200004e004040d0003001480c1c0d24011000d55201c1d070000c0400d2a580c6c41d000e04024002e42c0b09000700c1c8150307001002c403c0708203445c0340f0485a20800300340000c00591 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 346069415 1250 346068165 346068179
    0xf141c1b0803100f030f2f0d0203071805100611100216121106150604091a04020406020a050d0804030516020a1503022703060403050a03060e15090708070801 69
    0x30b84010941c101031900c0c0a00043d450503044640b400443c0900c0074030b15000c0840c54040310b0044038403070010210304142000c4541d0550b00315040360182c4100e07040301c5030580c2c920109082c03010039400600c1d18114500200307415141c940101e441a00750099515045407038850a80b01914080401022980400c403808500c1410303900900059080c115000048460350b52680980500140c40b08005488032160300c0e4035842c100b202503003004485110000c4100140f021814a01443c03154800e41500d6411511141c441c000c44940d03510000b03003080d5130b501e49601000c0d5880d00b403060101c0303d620843d48881c010311700c01c4d500b05000342d905603100c51030000700004500501c440640241d0388030061000024507819450560003420031140c40c0940c40d074a03a03040001070b241a90a03c1010848030261100700d035a4040f6030f80341c0c02a41030810701e4a54030b19002c1200105140d400440c2c810401c0304c240807541c00507451024030780c041101c202d6099a03c001c0d0440c1d08450554600e0042000000144480 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 346070665 1250 346069415 346069417
    0x60b0c0c0108090115060c0303050f190b0415290705060103020405061201050a0c0909090c0504051f090f0515030a08032e050114040f0605070f141c1b08 67
    0x3c19150400403980c014802c0c40d070304c108030255100d03101180c0c030440003208264260003040c2e44400380000008080c90704103043c07030a4101009070600d07000c1d40c440241044c2d90340c40d031103040380305002c03828000501d07225101a03020b16408020307031818580283c108441311380b81104440c0b80710352180261105901e10790902000d008041c01c02a448040841080c015150034401c4070300c00c11700200c01040301c1800403070260065030b054000c0c683c3c4600700f0001c0004105071000d01000c41d441a140010ba60740c1d1800c80300c00300907094200841c464178540c00000d03c8065608601c80440c0382c001d0821007a1601c00c0e4030a4070440042049805400521100b030104164a001e5640001c280d80417091000d5000c140008450307290b0040c0020f5001d82d0024492540d000e010a8120082d029182c2e241505000000b00c640101d40708600411030000f80b40b908100043c1c1c02120a02c1e40002d00070310540180c580107444034000c0c4000170b111031240a8004a561080040400928112560340d84684003900c3d52001 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 346071915 1250 346070665 346070671
    0x1a280b07060e1b0108060607020d110114040b07050c060c0d0809030c0d02070f05060f0f090a09090807060f051605070f050610060f0518010e0f09150301060b0c0c0108 73
    0x14642d07500c5070034515050510007410000119240640845040400940500342c003030b003400c1c01440140400320040e04c4111102104581045180310300b405400012200da108181c034901072018081800101210b0410107011407510030019038482c424a041800030038080c20b000c00d4415440391038420410350181c0e03145a008007515040c3c0740391800703085c54946400042203415005a0000320100012101494054040c11702103402c0c07450304c44000f10b03a1540d401101c80e1551590000074000b28103940e1180d40800500301200c0c00d0200802031b050044c0c458200c00d0060b524541000302800442ca2148600c3d482100388183d4455500201c00b402c031203c4c0c200401c21501008a40400f6000c26410881c440c49018802c000e01c0a80e410204001c10b40d801040c110f4091200038000305120601d1240d0480e0000801e280000c50036080300000303030302562403c40c0c00740c003ca03900b0180140f00c0c0c4081010111203406400030301150b591001484118880c0b242e083c003194001e654100350319846540040d030 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 346073165 1250 346071915 346071923
    0x1180210030b0a08031b06040809091510270e010b570705010f05070b0c0c070e0907091d030a0e040c0c030c06021c1a280b07 55
    0x7000c140d440c2c00b04034840c48507040449260b10124000d00c4001081245c50b168820000203050242499927540990703016452101c2d10481d100400207400f0700c1140510301c03880c0d034018100c080e082d0403040051314945004140c44c0c1c0c0c6d00c02800034010150304100d00703001120a1098100365581c80c02e03c0001144d0414900c14400407101542100034070f09660710006401c0303010044960f140d660642d04021480540003800c0c03601e680304410b251460000c2008804c984c0c0c20300f400d400c4c1a081c404100c840e8030070201b00030318411103281805112201d501c00b420410300d100045900ba80d85407041d15011103003c03110041690300102047c8030508003070704420221a030103040b4032070100d0801445400c641011a1540008020790003034183c3c1e261034000c20f00102c1040c101001040090745004040c0c80e1014005003c49400260003080e4000309400030680683c005410000b00030754040081c0070084269145104100b1411507000754070a00400c4082000c1d2a15443e80c46441c102c42458150042c0da8296 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 346074415 1250 346073165 346073171
    0x5070203071a0601021615030218060c0109050601060306180c03020c0a050c0901050d0209070c110a03031205090c03070303120221041b1211150408070e01080118021003 74
    0x1000049040c0c80a504400c42c01c00c05003a18503040000a1030021285841c50240202880c00c0021829014440c1401080d91030003690310000702c42208449007030b018155800c140700244801e903008041d88160595446142602c02903603842204800791a41802810b461201e909802e41110312141c3c01540340b440181030150a2104581550341060040e03142038605400c450040700662910011403405448200d0b0148181d0281d600410b0725003400414101c00e0100d18030655003481441e811010400301d0041c00803000c03c4e1030f8540100294032840454040c070b420140418101940480c51001800d0051b0003090080e03e1600d0072140f1034200c603007060615508001c0000c40141803d0111000d0705c089840c070841b030405203402d00202c00c0c2e60050381d07540d1060610500502310405900040700b60400d402640000e1404001440f00900602c0c1c003007040070018000541040106d1120100d9444042441c156a41c81e2140c0303080e0740303920400c0b100340008000c0410040c904801840d050316050301d800 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 346075665 1250 346074415 346074427
    0x40b3007030f0b1602070f0e060a030501020a030b0111010e060433050402100201050903091905060703080f070801050310020304060f05150a1e09110d14070906020604020d0605070203 80
    0x142007041034914054920700c4000e4104070301c40074000782088030303513016100a01d04030380303040303441b01e00c6500d14080d4a255082e500e01003803060362501e9096001d5a04840210f5464805c414080c000705800c001b501e01050b203a8100c0728410710188520310f0b0440f9044040c0810350341d10303502d008a500f6458110b0320365402c2c1c20203142103140590001d0040034085200014a42094010003602111441c400c0c011603041c001003200c0300802005647c1c7c0ca0809540100e440c007030021424200312026040307590803030700c0482e401d000e05500c603501c01e001d1655400402c1140e100c00b801110028801d0050603016030008045018030a0f80394001c45c1e015001d02d00c0090500502100740007a643c045d80c0888180780d07904200c1e8003030710300040c590008120502601c1c1d102c4140714a8155201803e101da20100355494a030b044241805c00100c1c2d0211400360300400030308080d608000343d5010b09507946e0000039940b082c0840c1d00c034000281a030282e60000e00c41045011250f841001500008042030300b140000c1c000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 346076915 1250 346075665 346075673
    0xf0210020703020601051216150201020d020d06140303070803061005040e040b1b0901021002070f02100302030103151406040509160b03220320030f0d0506040b300703 73
    0xd44860751195010348940c0d4501710800040c001e950030204460341002500c09940c85012044204481026a11a00c01c10504009900901030f02400582c41030002500c1809441503900c400306403500602c0c2d8402c2c00c00c04909056880c041c84500900c040301c10030100d81b06207040e588842d80c840041c41c0c00d0303250540700e2503032002c041c0c41a6003c4404c07040400c1440000d982e114007005155010f007402d14282804600000e55402d0b00420303030744000303500060190a000d000b801803039640342c003c0c03c04408040c114100400942c800d100a4844907591105585e5008850144500002c12080c4050040c0c40c0c038401c002c0141405000c541082c4150b0300125000002c41000200a15501c0c028a451b480d2520681c4101d494002c81d4220586004007a40002500b00d4900240c50140700744420300243c01c501524a18854545540f0100c03101080c002c0c884120b5400c8544100416903060003540c08450600826450b43d00c5504051207542207141180302d0494042003501e8100011582d03d6662511 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 346078165 1250 346076915 346076917
    0x418020708180f130905010b0103020307091403030d0c0c030908010203060904060518060a1401080c0d20091005030c0d03050d111e04080d050c07030b07050c0f010510060503160f021002 81
    0x300d002400c5840304802411b101b801e01ca82120905c080c2011b41c503610703211200404106107802020900f4043c4000003425403020401d0700c4010340909400c00041c0220b9a0242812030344e40e2040300000c0c00300310003040c03956060090b280200b0011b04140070380c0d21680d03211030240c50b0007004485901d419840c2600c260008001940c003a40000790009078809607100d4a03100c2e140141c1143c0501d40c41020341303203060b880b0f518031084040c1c2c110203010086002402a09034007181a4031141d80320007400280490b492030005080b085a0040303040314400d21f010024800d02d8048614050701044e001d00080d002c85081c0d410a0210b81ca100304c0c00d40c80d16501024103801e00011900c12504080041004d015901c0204034000070300100703013401410841032104603075591215000051401c00100f000c038030b20f140244140c1350110060300c10340315030040450f5030034020f09040b0781c02c0001c24030005000550034050400c07280100095448044207a06000050b18400c0c2d00c01c2c0b1810031031107014041c8985c641648 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 346079415 1250 346078165 346078189
    0x2150406230f04030c02010215041a090c09010501051c020f0702040608030708070f02010e1210060b18060c15091b060a050901110c04110418020708180f 67
    0x40060031040c48041d005412140c00039400c111076100052003120301c19458440d5202e5410303d085c0d50814605e100403030520340c50b80b50b0b21061403000302c24413007040100c006600885070b40880307004986d40d4040c038495440001d000d100b41c00c000e802c40140919403041008240e0701010303a00800b040b00042003818200da0019040c0403c69401203807010852409008010050000c40001c5061290940b00c0d01154440d00e07400400e5186811030b10f4046901460003c000034000070840c0a42018040c28940c46001e0812602649441c1040106100a140050300c0000d80303c25420403804084000307210056118449120b036078070800100c004048600564a031240614001902c0d104c2d002002070b2050a0b00c04103032600c50f0b5000c0c400c443c1050341c450280c0704203000910300822545800c11102e41002e034404021038101c2c2c2410441c00042e6111701c024400c4580302852290b01110100c0000201d006d02076004042d45820000f0100e503480003415807c0400c0028600c000c5007040c8000520300706501 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 346080665 1250 346079415 346079423
    0x20f030406020703050d170a020306040f0207081305100f08040c120305040612050f0f1e07020c1504030201170a1e062c0601031e090303090b010f0b030109020901021504 74
    0xc0d0f0414001c11606106c18011003045007404010710400036016800d03040014000600710368080005012542c1d15004484a183d40c00710840d0382c0e40b00750034a40c0840d40000540081121107840000385800c0800394884445c000c0c7e5103044000007a214110b42d40d00c40a4001e071503040401001080c80c03110402a040308030310139112943d689142507070107030081181c5c01e01c0386405442c1104010b0490a81104aa4404641c6038080b0381750382c1e07545000c500800340840d5000804001c0081040241e000110007510300c80881e8603005141c04080303d08180d204601000b80007800aa49038401801701020f00b6030454080c80700801e01d000c10301c0d40c10441c0700c0c80f600d20ba0280d07900c81d241008012103440151070300110034100c0054200340300d440001c041101030801b90415580701501172150048118040600840074401e01c054480c1c5c1c18000c2c060400c2040560781002c0c1e000c0001860990504000c0c200d440e1401c145085a00e0841c0b054000d4000d00e0507181540078843c0da500c4103042001c3c49922803449 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 346081915 1250 346080665 346080673
    0x11d03011d03040f08010e0c010c061e020d0f0b1018170304030b01140d0201081308040b04060305010b1914190206100603020901020705040f090506041a0f041e03020f03040602 77
    0x350074012000d8003005e61201103564036080700e4810182c40481c10454002c400e007056180003074103282407001010b40710701404062802105070303035040c140741d002803860b003e006006120a85d210805801212082c03d0b03070660000e0403500c0c9003007280c010580703144030032005c0c00141d0340c1a9445814290011022206491540000030203000704017605c08040e0140c100240311208607503440c070104c0c01d001207007503000e814440c000001079003014915480d440c005920207611510f03980d46081440701600b05008620210303003403c001080d126145c4054840e800e104543d01c4440074141d81058071616000f243c1c8072411003040103541d0f501d040c0150b4406501445500920b082d1400700117581030800385401c8107007010300401c20800260790004641095620131680040d00300c0a118902004180f030f800000d00310701415042000780101d4804028020050fa411458160b554404880300404201c8004080150008034003101e100d005c0d0055241ca03100740122001e8400507000613285400a034810001644 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 346083165 1250 346081915 346081919
    0xa0803041d0112020609090408090d05011e0b06030a0203070507060e0309192706031406220f0602031e0a0c0905060703020601060c0f0209012c06011d03011d0304 71
    0x1c00011880d0040031085129910240c20303030b00003002032203031858052040345140003140500098074200c170103541000f4440c0d40008402d01e0100d002c1c0c18485200461381d40c0f0616541607500141c052038510f124010b12241c5169601e1b40c0c40c0d802900054805401c0007018000200002d001c0c0c850104045030a800854507050f11030708110a03400c1d900c09040e00e90000180400c22030a4441c0152920010102d0700203801a0004202c0000c00981d4406881981310007003211180c800441c070030340140c1003000146501c0b103003203906a018003011000180f102c90b1440180b00451016806150806001a41590100158a43e56107502016903142d1503996a0715000400c2a41100400000701800e890b0282020781d142c60207901da0105201d85401d21120860100400002d840c94484440d401844000f8a584614801007070240d00711280c482826075001d250301d05000c4000852003814140d49441d00190b42e1080304201480c607120351901592521a00c90803d150b00b483d182210580300b00854940f8 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 346084415 1250 346083165 346083209
    0x510020a1b080f0c01050f0a032c12130302040906020d0908040503150c030622021306080c0c0a08090f03070315051e071b1b03020102070f05031b0a080304 68
    0x100d42e00c80807240c1075004800305801070741c008047d03440303100b04810b413641c51310070b003042c1540075200e2042c0442446229251030080f80c00c0c2060f03c3d0f0807900400c000c95944032189040448944a1100c5c40b0384681e480700820401460990080e9803102d126400250a0140d000c4007001612402c103c00c0b0743c4460301181c18449030038208644085800d081903810580c0c10700190485141c403000e0308a6000d084840000c01c500c00344414491101d260fa40f00455440302000360300800001140103a100203650100807610003840b68096445e10700040d0302030022000c440c0d84003410303540310345001034212038601141c0c1c1590b43c0c00d02c2403170000e502550001c0c0480403d20b031048129100104603c501c001300c14030012500f1400c1c5d01c0b0381c2e440000b6041100500120500c01c1e080c540002c1c00060070f00840312a08003c42d0b0103000d00100b240d10030b80842d48016120540e012078224107014861301588421015a01c080c959101c120700a1030103046105103544075401d04d07080d58480d4100710b4045088582c1d0440030 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 346085665 1250 346084415 346084423
    0x4050c030f010216020f010504080609030706140403021b010909020c0a11060c031803120706090b0f090c01080a0906050106020a03080606040e04080307181724010510020a1b08 77
    0x15541c1000210b241c00350444070200c000700c5804002e4042e013034580d400075aa90098007150701500121040741c4851070030b00a00c0f0760343da10664049560710304251030100400000c52101e4065503150300a0200c0d000040c200c50303069490254402c0c10440607203400140300740188000d00340321142d040075043c0b1141c907080040300c090746041207901801d010041030700e958002206581a40311000590000700302c02e0703000246841045810f0006658001502e401000313000c0d44010f401d0340c4191300e03401305981c85c46105900d116040724480d80d82d030400c2041011541c41030503100d511940b82132001510820644448045801c240c0060006d0303882000e6010a1541012005a002c10b0448510345024201402101449405040106104400300210340290701a400118441075203d01d051220390b0b03100040c3c8100344a84ca41d00f016401110f0007403803400001c0041201c0325400f20400402c0340d20746410300c04201c820207070030703021401030780c1c031000003e081c3d00306504000e035010845804060800521900b4 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 346086915 1250 346085665 346085683
    0x10090b0f28150b0a090512160902040e071e110304171f0204030210030f0e060705041a04050f060c0a06050c090111010507080a180204020c0615100801150e0904050c03 73
    0x10f40c5a040c0070800c00113070300102100680304159811040c00a203840d515240500401e10403003444c60b07000010032513890540c0580219007440d2a04110707900c032000c050710080100a10ba01029005a8240030002d0194100c03803041900401124501541c44038240da040c1c0c040600200c903070b00030805141c1c40c1c5009120342d060010100d40d0451a0510750b5000a0303001803400c0a160500d0b45a00111601480036484030305401c9209081c1c80e0709191034100104241d000c1d000750f115603030b1101c10340000704900e0300954041c0d45003d0159600028024100580c42d00440c07010b900701c2c8102804040091884d00569018111521819407203200d103c0015000103c4c1c0c20700c03241303203a2415082201c019800801190800d462940025061500ca40d00c400d0481e01030390080d4109000084540c0e205800040c1c9510480b4900c20004100e140401040004074010154800240c40c0000500c1011b0b08074040ca568402d143c00c02c0044028082c000c10020031045a0648454004020700c9209080c10301040c51 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 346088165 1250 346086915 346086929
    0x2218230132060d050a0f03270504050405010b03070905010501200d030b01020c03120306040b1008010303030c0207051e2b03140903070f030510090b0f2815 68
    0x4100c40300d503070322440e881c410000d252902140d100100350942c503821046500e164104058078001116420441c2c000070b44000104c002541d2204c05c01003401440d4502d005100810aa03084424900001c1001800c009001520b09540c0e8908402d0700e40e0341001040001c09820002041d10340c9058000342c1204100642c06044013008550680303600720102e4a480c114005013000510280c1d5100102d2425554040444c0c1610441103c51100c0100b0005980310301400c590a21501a960080c041c02e04a156500000710711460014000030b40680c0018004a80f9803045901150341c0718000391f40c0304072541c0501d0f9407100c1d0ba603d600c0035080441c0e2404a03540000d1201d1540d808030b030207000c20703c0751080b0301408014840000610314004542111400391000b8100d0f110142c48500b1041d40d040c0501c020ad41e94814080405840d01841c003e242e629034110304110310b103682d03983c0400c0d94807000038148000c034503151204a1444801d070490b050900040100054000c0c05000c58204000d03442e0040c0e2 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 346089415 1250 346088165 346088201
    0xb01031b0c05071e090b030304030b0f070e041e2910090306060f1d060603071d0904121815140c06150a0522182301 51
    0x8421204050a1a2028003078036001e1100121801c1c56410040150030069842c000019100c4041035152003100c02d1320b142c03a504025640008040554078030031072000420224481c40000e5007017107115442c1d64809401d00340350070441d0100c00001c04803540d4060244200302940d060b41e1004016203d8132002c415207451a21340e016055420030200c4074003001c0a845483c1c00b10711840e20a100d021010003e6a0110f000d22009403641000c1d000b181c094000c4024024551800840750028802c0b50350040d0005403010745503484054040320010380c0820443c8900441c3c0c1c004440c40e07282d820742e03984a18011894100782d0041c105004001000d620000c1e140c294500c20309100e05041142048a401c6507424400040064000d4000f0580120b905405c40381c00381404008844800100d54100900304a820358a5942c4944c2000549451a485107484444540350603694500981c4141d01010307548800074002242580c41c0b102e0b40c000b26540c402c81d50710398500095450424050342100c000003035299 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 346090665 1250 346089415 346089431
    0x6080304180218130b0405161b0c06030c03090506040606030b10060215062d0907090e041205090301021c05010906030201171302060301080d0f0201020c1b04021218010b0103 76
    0x101c01c1c1405501641d481044d054000c0c0c080f2210550043c0c0034103070040c00600032803501d41080d02c50a400000c00001003102d0064884640c0040c08003047c2443e030100e00160840d0078044114002e01b4194030300c0c401e1556600040011074000c118051043c2d12416020aa050070b514080040c00005000f8119541841d002840076507008035800c1c0c2115082480402680d651000040d40841c0201c0c50740d0000119403154807068102c2c5101030b0072204280c44121807910303180c01c2114261200d01c0381a4042ca2080c005c500052400140c15038034800519000d41030010702c41c000b9003281d01248030070f02010b0800c04040500c1500b40100e9004000d1340d01e041000034910380000c0c200c00101c94109110000f0a00001d120360640003010210a07000f601107078a079078440070308540d54075040c800880411007a081141c1020b105000f03d030244c001204c040c00310901c0c82c401c50b61210b4112007601e0361003070702804094902d08041ca81944682007880115004419001c0018215642640103a040500344111 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 346091915 1250 346090665 346090687
    0x7182402100c1b060b0a06020f060919020d0212010203010b07060f020405010504030b040c08070e0a0506121905120a02030915030705030609150d0c06111f050702030d060803041802 79
    0x30030f0038461680c0500b60780144241c90100c0c000c04030b2041141d44804400c00c04128164000f966050740039001d41240d90586451305860303135443c01802071860842e01c04840710b00505084218102803440501800c6044046903c1c0c6401d83e0000d0700301c103144180c04109441480f400f40030b070303070116100e2500451401c0c0c03c010000b0207910a0b4003001e0069845140130408004003003444400a240400c16611501c3c0c44807003064900c082510200115802d0001040c00c1c1e14148107031094110b8910010480c0303070028115003801c0c1400c4039003500e20f8010400f15904007030542000300b81e081e030660301070340d9540c040004100404420042c10b480400c410720412030356a810104803a0070840032079901d80569580748003010302408980989403ca04405041402c0145c0203101200340c40003600c0d10820a0840d1482e10f641d610316642290204401c400c0d00705e4013281039448030b6005041403040c2c92401e06c0c0c1c0183d01e010744549078001102940001810030010030042840f48201015032001c0d0301e84000340309 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 346093165 1250 346091915 346091927
    0x3050f13020607060c0804150c2c0d11030d090806060607060204080316170a0e06070302160f1806120b07030b0d060506090105010e0907182402100c 65
    0x214040480314048440d041d5a1200e0584882c42d510010a00c181c0320f070700c0001803c030507054031304a802007403a1521003000c64050060010b1100c040c0d541c1c046c40880b003011000100022200503a0b17110303002005615948681301295580c901403010f103804109641d090601c0d10014140c14070030482003076030500c4285000f2880316048101114070f0b80d115001ca0800000a2046501006580c400001d80344c0b83e01003c11172400070b15000e88540390240d55400c4180d00244140b00765480090443c001400d92480d00c04043d0140c14040c1c411112006100c48042c201c1c2c404682040d007001c10b811070100070240c0100030701500086281c806024051a15080400d90942c03088002c0211280c2d00c0001d0b050b070700c02d500a40b0101c000508c0140300380298200b00300100020398480d401042201d00208107175006481281800380c000c0d040c04010358031070204440b00d101c0310703214210360302c4d04250020341a0030b2015510600710754043c0300c20500000d0342c0d01a02d005481008441000c0c20305654100c1030760460 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 346094415 1250 346093165 346093171
    0x40b09060103231c0806100810030f06150602251202280b09121219020a05030a0926070b0f0405030d1e0c02210a0b0708090d03050f 58
    0x819410346201a00d4580c6003045900c845201c6100a1841d804401c2a4001140c9020301c00548007ca5001d07400c1c1021150044102c42c0e41542003410b1a04100164800c9201505c060003124000350314880420202038040d074a9000c0401a40030194800f0044141c216a046410a81c00c09881440c9407100007a11541d14100c06441240da0501e4201c030103020007100d450500ca1002900b004503252110010309812005104d809185048201701c11640d0015415845103950350440c0c2c02e00451140030010394006149410440c012142c000002520400242000c080d0507180c10000e207003803400d242c4000146900341d182c0000804028801c2d40c001040c0c1200799484225000e1f034500280b03840e03050078803465221581600c520a04082d0781031740040345200f900c0a017900c0ca10740d40b1501004640b541a1007030017030b500644044481d0300102501c0c242d03203040c1901500b9100500901d88420f061880111124404503980310308204150200f80813021015425060801c45801c182401060800b002 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 346095665 1250 346094415 346094453
    0x20c090a0225030e030d0504060306060806060d150803040e1b030f1f050a0906170307050c0409110d050610060c0b06100509030a110301050a060b0a030b12010c0503040b09060103 78
    0x9892141d00f40741c4215003100d0a010301500b16240700d150303c40010560740c014490680040c1c0b801c0710200e001841001c1081c02205c0080049007000b079070022180c010014104800d002c52058103000902c0c203000d0014000400f204200e0001900d0b04c149940d046103100204d0866660307041040020407540003840a030070851502c0c40048444484001d003120501a0b040f207039100103400e20002e41e40610350040340079a0540d8400140c0606800380340c6540303001c0d4410040075a0400f0080321014100340c0d009551050107403500003800360312203001c41c0c400700000c0d0090f10300750001c03010800d601d094039103102d005181ca484c01e601c008040d41c940c114100341c080d120a12806c08002a05c032103611039010381e101c1c1080203095518503103580c46d0107403101d084406064007a50a000005415012510401044550003204c0c01e14000c00c44408500402914070190741c04075490f108500c14050910612400200c00e403a02c0380e40303003002e081c04c038a0050014000851603102200600008090b02d07410340980c0e0b02 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 346096915 1250 346095665 346095727
    0x3010c0507240f0e0109060c0206010b07120525060608030306011202030a0b1005071419110103060819020f060304080915070506131401050f160309050d020c090a02 72
    0x1107000b05800380c5060440996164189014081508010341c040d0300d855105500401c00c8400e001c60070398844009202d8901c011000b80802c60105421022400c4291003500d015031400c0c0c405501250700000d990500007525190903c00000c0041c503100314809410802c0c0154214602800002d150104a000b141c19803900403001c2019038000380c010701001400280f940b00f40c400161002880368008820680d61000c0307190b0010303003680d00418143c8418540707901c0040b480307805486103802500b0482c0e01904166480c8000210038101380701d1803076020000d038806181400603004100849005c2001c203845100708106020004100700d048807608141a141c0c0400407a00c0c005d42c0c1d25500030100081d20034015030042209401380b0840707d07000c8a115140003079020305c540382c140e42202d1003200d1541507a01e8a4003c1800c146000e01240c0c9000090318000c1070f0001c9543d107440c24646801500009030b4881c1000491605d04600d4043d485901c5200c11410050211204544500b40c031401858010b0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 346098165 1250 346096915 346096973
    0x60e0705090a0302030d031e06030b150f030f0615010203090607020108130c080a020a06170612031309060e090a051c03020d0e060405010c0906021b01030e06010b030603010c0507 78
    0xc41d4070105000f5500107042c0c07107980b0165440500a1b101540c2101d5041c885003d8891800340c0034410b1405070ba804c0394075840790399203084600315149048900154801106481c0703505e0343d5002c208040c031003616000940520300b00240540148070158840c2e0381990824040420103403205c10076103080a409207840c4005880c0d46004030300d08851a00050280c203220140030519840002d1a000201d10a07903001080541d19441160310511a82e80b030031001c25a41c0205089250490503403903102545000c2e00d1a00c011641b8000e04081e496005480306134444000b001000c0500d80c980d5400000c201c0584182c41d50b9032b41d06611445001c0f540b588054802a034004003902c40e0b4142c49914486001c1080f900c1350103c51140e841c01c00301c4085031f9a42c04c1c003809840d2248282d807141c08841d00d40c0c00400d11040520b1400e2503861080d00706d103041650b03a40448100101c1040b46900824021640030358a0030440289400d4480c909815018804204440c0700056100d031914103e0510a040c5261406 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 346099415 1250 346098165 346098169
    0xb0f06070b04170f27060d09020609100306080708030906040306020d110a031b03021608071514010312050f19020106090e10060e011406030705210103031101060e070509 74
    0x90f0b200400c01c080f074a4003050350300001045000078504081d4112130751040c0c0304014648080101c280d0b100a030000e1003071000041c62041500100b0740c13107100501c6207041c480e91001250411141c284503e0020745c440c44100101a02406132901070140880035502d00b07200b940204030f55104611000b841c4580c000b4014562000a1340140e050500641c0555910210b00304010050310740c41c0040b04944101d40070a080f01e034001e05c00c9504540644103400d5428400d501c0350400c2d0381002005a40c1d4040c200e031100507000240c4200455501c240300c50141075411810b11181202500c04060300f802010440302540180800503200d1154203072800844542d200c0130708a024008541c0b207042c100c0d0a01440c9080381a01007035002c027080d0501001c001c05555070b6441c820b0290b080c0b1812031140c501d600000c085040071001581d01c00b20320700b411890941074042c41c40f484041c540101c645526401c00600c1015881140d40b20003501c1c50009014682c1131580044804034060304500903c50002401c0180f5 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 346100665 1250 346099415 346099433
    0x15150c0b0c090d08070606120b01170f1e0c13020a0908010e150613140106120b06040608180f0717062707090204180c090f06120204050619030b0f06070b04 68
    0x2908c58840c050407034208516100185800a00602004100c08007884003020703000691040c18a15a80c014804034407840310120300031031018001a40c1c0c0c040c0203007040054581944843c0c804102900c01a070b1140000c400034803011f85a0403120560341020a1507500010002c1d90403007960b083c1c0007c0120381c032000001031150402c0390140301d9035410521035200e200c5402c24101c3c126400d0f0744600720714440c3c0021840c00ca800ca904155030100c000c0c08103100251240c17000940c080f02d07509007140b41c01c610f00c412500d40130b0482e404030101c1c0d00c441d80503c00030399120010b8105c10380b80e10052265003480c41040c2c1007124160080c00d4007094050b407000c029107041000c840100b004120840d6501d80f03e0603401c00240c400d90b203440d000740c104240b0a01e03080c402d1140c90111000300301c05021403810a02c3c11604621010110807501e07801f4080454155a040d006000c00c80d41455070040c500c0e40504041c0a66030016180c03131040c80d0300d1441e0421034603100102d6200c01d5201ca00390b929070b5aa4074001e0341d0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 346101915 1250 346100665 346100669
    0x515040503011803080a1d060a0b0109050604030b0408030c040503150103110a140d080d18050c01021519020f03090607030b03240c040f03030809061012030315150c0b0c090d08070606 80
    0x2c43d100d1082030081c1e810a9034000b005860003a0303260cc0c0c5032619501400124400c41c1320003091030350b91100080c04100c01d0800340d90801700941d0320a00d0680d43d440041c0c80c1801084008241103800401002082061088090401e4082d500305201070b10b4402e464400c030001901950040e02c03410211001c01890030304960200120340c40400454401c00e907032007584102030b00304031f44a11540d2100d0601d03600001701000e4284084041100b141c0c0c81c485d03941d000ba215801d1801284c0d400340004038120626201840c4203050810003480540f904000c003c0640b0342c001c941c14003035040404800c68941440c1e00c3c5c0960a0001303850112a070b140d02c020b0781030300e1285511140e80300950140100826500c294418016501740c001c940c425103e110320081000786a200d100f0150f44038040b04000240640c000301903040600460840207986c070002803222403030030401d4100080300c840555041000b107814494026000b43c440a0400005802013000b241c02041e0140c0309501c0400d5210800136550003543c0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 346103165 1250 346101915 346101971
    0x50d0215030a0204081506060712050f0f0c01150810090c0506030c070b0a0b0a120f05060702010b0406090902090a1d15070e0405070212030a02040515040503011803080a 74
    0x10381d81c5461100c00000f50850301900c411402550340701034031180710803040350159500800c080e01c1d01020f0703074450380e40c0c0c00c2803003442d01800400e01410603011800800380102500c0394041b140c1e0ba00740a00590b00310340e800700c1701440c2031029840c240f0400a00041212000ca04550000752062032402d00e0001c030095503000690118000081045500050001e44041485481415443d4450303560040075510031a240c1c035003101300c181080001076030b05454480c220340100246610140303591505030504c07204882ca800940e440c0c000d1200542011b1080400a1120b00c101304141c00b02e07039000030003010000d00109009034581c4082d2003c000c00441a8003140e038070200b2540d1200d0842c2c1800080300c0100c4030f03007005c914000c07841140c50419006e03442c03140da5503034090120740700030640c81140d60700b001e44a401000e509000c085003a03212003070358000b540d00329050039441d00c1c6414205406d481005c0668180507003030740341c0b1400013a0006006038120034564800701d034582031404034400201c0c906280304 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 346104415 1250 346103165 346103167
    0x403140c010603081809090309090402150d1b0c08090f120d021f06030b040b0c0d090503030a0c050c0d0c1a010b0702090c032202030703020a08070e160504050d0215 72
    0x411025100900b0170400c10500300740702801150800220b4001200c0010b42c0c0c2c0c0040048510b203140c03121000d90b100d4401030001d01850744546002c143c40e00008080c1c1d03041076030743e640c004050b51100c162500c121014a4081c228814580d103003180c6010703421696024818025444209942e0903003010020111103003295454181450300969440030341c0070b0b0103452500c003440000a884680103231002d0f81c0c1c220700244610b0b103517991182200c8c4001050618000c2080c06101c490400902500e00f085000d10011038580c2403945d2070004641121090505003c410000c2c182003440214010041303101c1ca040030f003a00e8409062290304803201400000b91603c100c4008540102a48058107a01c4d000b40c840401c1966a043c01c20028070013920030740112042c00c1209404100140b07102d01c48144003805890000741e8940c04241c00030070942208146402440003031010243c8006020b6111110360301c5803605082c11070020b0003a01c00d90003520300030801440150150b454100c5041c40d001c2c2036100f0b007 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 346105665 1250 346104415 346104419
    0x717040b070b011a1908060d0b0c0a1206030321090804170c12070b160b070509090708010f030308090309090439050405090708010e0109030e01170403140c0106 70
    0x303640b070000900440310011000800000344a20010907250a140c1c03411740d141d0800102202907601070801050150f012000b078480000140d048007000c0e0084003403150840c0c80303c0030b602019100c0300000c00d103080c1151030060200b003c00d5000c41d84601e8441c0c20f0700100401c46900700d815000d0020401c1c0071f421584001400a000c181c1000060344e600007403c1034070000f00c00d46007000222980480100c0c2640c0c0306200910201c04840010440d058011000384031200c01550750714440481110381001041e070106142c50981044c071102503120000b0b00d002c00b101d604090007509a80e0142c0405010841180006078900038100200c07008a680101304892610b001d24102c55800210303802014a100c500fa4038000c0344c0130035001d01096003035040a15a502c1d0a00050000a0400038190000c61007480400140a01d0070320a405800e9000000418442c202d4203014214805c0000c06504115844054244043c007104000f81c00941c580b03010a00e000c1d00003050329081c007401c841030034030394600000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 346106915 1250 346105665 346105673
    0x30c0602030f0708011e05100e03190309050a03030504090b060d1406010906020c1309030903080304060204031a07050324060a02010603140a0f060f09080708090901090b0102030717040b07 82
    0x2e05200b02c1581d40e0712910740c0c1c1c0b00c00382140003498041095024a401180070300080c40c10001003098000c20b40f402e00315004014002a00e003921a0700c10400c900d003e123100c5014140e000781c80c240030b0841078070f1a00d0803900d9558000c200784110720610f4051a551180c40d40d080e5103000456200c1c42c002c4000f80500411101d01092144096a045000c114400300020301031b400820514a4524000d0452004800840d05034002d0060788008030108001c411001c0006600c0c04060340c0100d01a020043c0c1b1142035140c00c40f080e144031203405154500c804203318046502200b00c0360300c25440300c00411380300314104010080800440c801a0300840100b00400140da0561081d0704a034011005c481220781104a23031502d0360740000c4040c000c204110302c035901080f401d40010100300c20010000421840766142c07107070260002d41c401c4503614030000c1e010481d468202d440c0380c00760080c40d0003004041242000030750f80740f00f50724000b41083d110b003140805e29003c90003950020203d19000c030350b4030744c03152070 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 346108165 1250 346106915 346106941
    0x100b0a0305060f10090b03090f0f0f0c060f0f16021002030c16051f0e0a03030c060b01020c1c03051606060609080303010503060109320a0b04020909040b04030c060203 73
    0x60b81d24001e00d000c012110b640d02d0600800c980c2500551141c100041c20b0400c0c020550380003c200722014843d0914101501604003d00481c0075043c0000c5c0c22a04800c0300d056081c03d03d030b5240d0520501e0300b80701c01440c14202c0c204584002e660954940c1c3d407a480c1c04141402c1401100c80658440f820b8140000e1898011000703181c1003d20380c00744c80000710001c4441c5c52504484c000c085e04090b0016803a0f9004440c10b20f45c507194441410300d45031014541c000110300c0340c0190800c400040713041d0340d8003041101c50301550100303440c240058000740c0d40000100b409201e04212242c180c102d001c810a05042c010001c480c000d54030440c400e10030101a0802101070586481135500054080000082c41312021064030305858008020b40810f900c1c1691300c0c0003030040302815030403484000280c4046454100301000400124a5582082e85480c1501034103c1c2c07001d500d298040e0b801000114002c0c0e0303505a0f83c0d83e10551048028003191260700f0100c5a240c00400c00402d55072000040c4440c032402c10b4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 346109415 1250 346108165 346108171
    0x30e0709051515030117120d0b130c0504060f020f061b0c010203010e010e0108071a0904111605010f021806160b250c0224220f1401090303030203100b0a0305 69
    0x1032181d0009966805691f0380e40d070f180351070301e90080301c244011400c00d0f9190308041d4500c84024000000c0c0c241340c000b0321003101d0389101c509000c600001420425150003c01400cac03603404c60b00140541200d0082d2841d00c2e10300c0201501d02850b119880000b2403035080c010303104001031f1a0003c64907582c43d00004080310700f00307000d481e920002010000030f52540000c1d80c0c0381995000f240c032a85900518091a100f50417040010394881d440d00b210000f40d00112000e0b16009881580c24051041241091401c6500740300103035454600411070309000c0c1000c00c1011b03074289416100703903540c1e101200014280c059000c2d0000c1c8803104410500034100000950062484460354030414103640309101502c10b0f00d405d010080d001454000000d0383d520b240d1996402c8a0000d192144c5030040c0145e8248113003580c6094a6901c43d0180f03000e0117030480c00402c040162181c200860480d111080000c0c4c1140700510006041540000c0002c5013008402c6881c07009003000903191b40c03280da6880300035000d00b0f021 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 346110665 1250 346109415 346109429
    0x7240204090e07140607080f03060d14032214010c080c030a1806050304030e130e010c050a080108070e0f13020a0b0a0f09050a06050c0102270a06030e07090515150301 73
    0xb04d140100c0c940a01103400301c541c4a4a4107103002d5148e1000780c2c0c20f800082c00c0640c00b41001e8101800b00c0c200c0c0c4040d801d25012840a507946514403419400914800c40b6421041c001d502418455007041000350800c01c81c09003843e1090b10468505a9064804c2da400b00300b441c000490054141508580e094407842e20149850403250b4540104854a0100b1100680007030701c80c40e070b280e0003420845d101c2e06051b030300340e10046800186200c400342901ea0120603003000810018a82c402150b004055502608403c07002d03006a80c0f900034040a0100040c10042c017081c1d010010030a07540143c21400120b90b4050200d0704850303920850458a60800506003011a030200440c1583d18030401110381a00d200410049819042007402c56036900b0941c81032000e50360801c05125241c511035050044aa50348860608140c9442c090002d580c2c803c2d0f00a0041c1818500c400c0880310b4041640c0042e15400d16000480d503940040d0401c003034035003501c1c141d00000d05104180c192071000300111b050f140d403 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 346111915 1250 346110665 346110689
    0xa020306090c0609060903160605090f041404060b03190b1e09120901091e05010908060c090d11090f0601030b010f02070506070c15121107240204090e07 67
    0x500c0c01c1d8142c4803040350010a80c0480304124803141c6140c954080c01840c0005400c8828603001c00b5189100014540c001101048000c21020403500e058400c0c008801810366092241c008600d908070b00c6840040c0004004640b00e40084055880c00c001000140c00d03000c00f241142a80780c1010b14000e04261601c40031401d45030381d4103038040d1204204030b014141c03000c010320018400d039140f0703402c682103010250304104d9081e00016004000c10544071001c0d21041c6103025441c90700001500360905940710308010307001038003000140740d010000d494512300d0603140c03020554a0b500e0021b2400b1900034000764000032041c103000c4455448410355100e0042a00c040000040d40ca0054403261864820000180d00c030003401c0c071660a02801a0080500c02c0000500d8580c4400c407514230140c0b080002c10004212001c44000340750b0f14010a11000700441a992622a041e1038503e814010180301d2800c0d40d4034a0a0140842901e0381268001e041c070000c200812441112450b4030751a0701d00c10400e110b11 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 346113165 1250 346111915 346111921
    0x5070f0503070804050309060a1205090a030917070909050c0103151811091807020c06070f020d020316090b150a0509010f0207150807030513080405010302091309050a020306 76
    0x8016114012085480d494650865a428100300e84185005004039030501061110b5030301600c4500c050003180c80d598031407004601d40481b155003241e10040140003181e001104090102c0c1d000320f902800d0303d120b1041d5203000082c1801031864107070715078046545507142c5500341c4180b00c000328a141d00314100b683c0c207108503115204a480240c03020300403884c05a5010141541015407648034800b9040040080c609015511000450585030440c40006014502c130400c61080e5041c0720300c1c980c2c60000c6070303120f00700710070fa44541d00c460f500000020b005888010000d8150754080041101c0c54007000300410b200354036940305c00041c00c20400f03d503018001c00e84ea6111148401010750341542c24560303560f41001c41003801120004441100d0f070301036004614022516000c0175485584000b26a1101049420030460080c125440100f458084851191a01000800c0c000444003110001d107809070700d66104c140000ea01c50400381c0e00b81e00a6281035400800c02001050b44074905000700d003900c4a542d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 346114415 1250 346113165 346113167
    0x2040e070b030604020703031104081608060106120e030904050c1b06090307170f03070302040f170703030807051b0604020f0108100308030c1b0a02100306260a0b130203010507 77
    0x20920380901c1030030700000d100194080c10141d02a0501074045c3c503001c12660b501c0303400401141d2190304042641d4100c981440d540080942105c4010801031008144030762401e6001448140320030128103400341ca80c507284011020403c2913504907800104200564104201c032a00158820b01200704a07122104102e0450030300400c032144200350450107145840240e68510000c105003030310b2401114418445003801140c0d85c00030f0b512171882600c0c01a940e9040845c40c254110550b44400c800d40d0240c0100b40c49190b012401d0401c980c3c2c1070620b407106031600c5034150350500031400b07200001800c1c0041c4012041000903181c3c00b460095504a102c030b0100700045410752411900d500c4550009502000052070102c001c5610240f0000340c1e03030910480510f001074100380c01a5040c1594841e9001c01c003036107000c0a07080610360445c11700700207041c03421031a20540d403c002400c00f02c3c00c0c01607445580300703a014044c1c90714607076221120446c0e5291204ca2201030111804040c1d001750b28080000d6941 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 346115665 1250 346114415 346114423
    0x5060105070b0103020d1e120e0a0602032d0c06150904020a060e040f0204080c030c0613050103020f0405090915100f0506070201020a231b0109120606030b0703020702040e 75
    0x581000c1100c140f0384c21a0213010b000e0104000c200e507040c03a000318840d00904208404070581d840745801020300e004100000b4440500062002d00c80d01c1541d030200085500001203526041d8440380043d45040f010402200d4109480a054291003000400100c544404901030b071160341e030070321017050a0401405000f130b0140100c4000390070400c803840510005020b0384014010300700c001c001083c00ca540f0145c203c141e820907408080035501c0010710703060b140b03000d0044e24080c01041d600241005208070902c68100c00030b2050f241416800546241819810000c0300d02815024002075801d00b04a52516640c1c0d418200b82c41448015601240514600502d80402c035010643d000445d0b03070421041105950010100f01d05600c45c031300c0c500b40085c00210f000d401314110f1120f10303450f2200d8100030f242006032000f020300d56002d811044a03040d07a0002001003e0710301c081e030300c9203003034034203143c0800100fa460700017802209918081140380c560603001040050310030394080c04114001c141103962 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 346116915 1250 346115665 346115677
    0x215010e01060c03180f0f1503050c03011a19180605090d02150c0f030a0f0203090d11030a1406010f0e1501081012050f01050106090b03161e0e0405060105 68
    0x43c00411070302e40481c2c41502071012032400032904500c00d5549000700c6198010380e078040744601403400400c01140307400d000401044461070405100354540302c1ea0440c020300c0140036103600c24840c50118071003404081c007500c50342d00b211a100c803010f21603014050501b11000d04650104440c020000c103902e44124161003045601505900000e4002e508004e10788013a10035a5010030300c240690380c61924104103056040c6c5220014640e201169000200a10140c0400c03505660040090665540300c0303500801c003454102a103020030034008070000341051411180a040c80c080924900d182903408a07003d412641c0c1c0300d2090844540d07030541c03050507280031500c00b542000c10320240c44c05075015a00760340c1c0c02450445007040321616240a0812501000000d603441c0d40310382c4004071202024800d4074050649400d02600d154a0120034a507a40b000409a0200b0220700d20b60f00722407401080016603510301e0600401904946000050a6880c00c2c241e4500c80c40c20311021400e80d500510884032 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 346118165 1250 346116915 346116917
    0x13090b1008100f02190e01090501031406090702030f030708070e040e062403030f1c112502040501061814010c030e3c031902010813120215010e0106 65
    0xb0303200d100c00204010b241c84034100c1119030b0204140b00c0d40c0f200780706000d00d900040351641c801c203080f103c0004040c11400d0b0030060506180c0400202640b20200c803580d48103508442029084d80c1e40303c0200d040d4040c031120070900081c04002d00400c00c0d00141054400c1c0c2c5076a80d9925614050700c100030540703c816080300c0541d0003050220b032601344000c140c4040301149c00d01c2c80a20f1f01e214804a481c5600c4049210304060012440e0001405508290b442a186507030062080c0a2080a00b568502c505402d0750381c0b4803030711000041c039048a05004403403507400400c101300d01e6945000c054200c20914501c04168282d4060105243d41d400702c4407901414107a4401e181e2101c10341d0150341c4e89111942c02d90b0b0145400030005006219012003c6a03280c1101ca4126041c80780d440c0c2c03102d41c025100d0300700d2003600300c0c000c0e0b0141810176884071740000342c09103400003058a132014203591003200c000c0090504158803640d404021b4000920000004041c4035050041c0c2e81c1c0d821650030b000080c01020 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 346119415 1250 346118165 346118173
    0x80310031a0103140a0f140708070609060305060a0f0506210a050601030e0d0212090a030501020c0a20010503070302070807020301091b0504150506030702070909120f08060901030803070201090213090b1008 90
    0x20300800c07c0301c00c00300c84000321340f03080340c0f2210b0301c4411036854540329a01280c0043c124450074400030b0341c0340c0903107034002200741e82000c025130030003c04042480160150314003882c00403524044180c3c0150440000680242076525942050640720001e004212003140c003103811700c1c0e011200c001000640b4510405c0f194050304050301c0340385003009103901c581c107802d51200e100031000c0007040d4288002c0101d800e0980081c0740030314842c41c00d280c80004071a809041d403140e6038041e0080b0b9030801e0403683e020171a8940142d41f24650f00d060b0f051405208000780d010b600c2c1040450400280713000c40c10a00d4080b1a03012046a40c5c0c600f00010346142d01e82c100c83d4455010f10030070590400802841d04210b440c010b0300c0d031064843c200035080340d00d06c003015206800098200c0a0058000c0302e0200c0000d81454100201e24007035001c10000e401c188030042ca07020300040006d1104d4404c0d03000030251680203110101e80840702083c3c00160413400780a45130407a45801280c0750410701c8803102d0494003104098 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 346120665 1250 346119415 346119443
    0x303051f0e09030d050112171c0c030e0d0801061d0d11040921030c111e010e011a0406080606090a05040f02060d05070e040605010903080310031a0103140a 68
    0x40c0a01c540d01401c0c5003020710007482142101c0001d40a0769028044403560640449841d0903c1c44050540d10380d41ca034090400c1011103201110501c41d41100c0b0000440850b540c0d40f1070004a0040a940340e040c141e40c041c01c00c200140d164010031442c12205183e44001c420341c1b0042c01d84c0304c1c400e0030403c802d50244400f20340e200003c071400d0b00b01d561035000420015114101c3d1712007092240c800102812114100400c420340c003601441440118a00c42c83d00340b003000c003a60380980e0b540c094601b03030303886000030000301d44060300b400d40203142c0c4420140028021007408a80403500a028603500d64071883c10500e000c1004a80041c0c00c3d4420a0002d1612005846081d00ba41c014440500140c806e04003036a02c5201507100c0c500207103003100162000041c01d291950004000c2241d00070494490341c10003008001e9a07900410340d0b01503d800004465498950b000c0109a1044135800100410f1001c1c4980604021101c1d155040302d018120990420700b40702d02054440500300e900400040d030311040 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 346121915 1250 346120665 346120679
    0x4050907080c01121d1c020304030b040807060e0d03020a030e010203060312070c0e0c030402010e09040201140d0605120c0901090c140c0a0204150f05030a081b0a08160303051f 77
    0x85400110a000000308981c40b030304c100149114260585045500c041904050203c050404504001b058400746043c0b40c00c5645480244001900c0981540340210b4040300707011187c0d020900510044d0210f49840b4a4046c0181c0070b07400803007185010902e08040c01e0108541030003140e1107400000d02400c1c29241c014401d40c2243c12801d4113031070748043c2000c00b140c5140c81440d01c03070064400429440d100e1801c1d03c00101a0001c1c0ea412602504c0f50005000040c0d0700560040c244005c0020403640305c1c4030814504005050952100307500403105082035442e8100804d0b080c000080135209066181e8892500320180d031380b40c01402c800a481c00189250311a00b410107405000381c1401a03908194983e00080d00382c03101150201c024001015081140440f040204002004140c003d0b09041d0007903101c007c5c00e030045200d4800c0804201b105001c220209020100c0541e60205100303032500400e0502294500c90003500700e02203442c1202040b881010f0030b0424000c7e004071440504402e080c154 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 346123165 1250 346121915 346121927
    0xa06170102040e0705072901031e0c09052a070b090d020307080f07020d0b0109050603010c050306040c1e030905060a0519090203030409090602070218040201080f19061404050907080c01 81
    0x6c81910484c5810a1301c0c401d8544816a007e000130b00c030003081c51194114103180e0702d0105a1800421084103c145600c0003c06404468041b110480070000380796075611016101c003410700002e4503130780c00c510142c076a01d290303014080d10aa03030240030000c3c12541d80c0360382c581d80c070b4401c4900c1c0c0e005130b40144610400907082c03000600d2264031001da450b05248003a80030890000414008680a0303100c00c0060008284510520380d01c004210000c0c09142c1c0d80e401c020f0418440030340094011a294880701c0e21581c0641c26000e10012030b50700f1081900420034005000b4031501004481500a02000c901d001d5101e008a60048c2c50050031141c4ca041c4004d0720700010808004120303054001031000041038481c5204500701c50b07015400160307454080e441007000c680c440d090480050704140049c0005070742d00c002c1e02e0358801e100308041c43e800c1c0c58070018241c00a0000401000c45802c150011510a03032407503482511050030f8406000545501c040152501203a00403004640d100034039200d050343c0310701 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 346124415 1250 346123165 346123177
    0x601120303140703020a1403150904051504080a08010504060b0f0a0201060b0414240301030209090102041e080c0d030f120e0a0602030106140c070603091a0a06170102040e0705 77
    0x1003070016120462500036051503104a881d00003082c1d0100300361800030780101c2c11440e0618649a480d14600c1c0409100440804100c80240254540e500040401104000c818881c5600c0f182e803980e0f41c642807500d80e41e0365000d41400400030324100000112400c003401094140c4204010550900481c10220b0301c4035000164010300315905e0b0540040c1070b802c54130051019100c0402c0d040758240206007445900915402000101412041c151540c80020f5064905681d8100d9a08806448072610140a406039400c0050710229602041e180c460140303003400f044504880c15a040c08154904129202240300005008908030541c1004014810300b00d44402c80890b0000003810101d80307049038074010042104680e0107500000600c200d6400c0081c0409103000780c4c248510f000321a84102d0703184c0c03049100b4017003410703103410340740c001c214400c81c03020816003200041001a14000a41c000a48800c1c4214849607074038601104140304103000700c07030513980c0b0b40019250351f490700c0c01c0841e61030b0701c64 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 346125665 1250 346124415 346124417
    0x10302030c090a091202030309010c02060903070f051f091211060406050a091a040311030406090b1305060c07030c0b0a0519170f0f0604020403050c0f012102030103060b01090806011203 81
    0x44c80c1c0780d00c0000c00c4241c0885450074598011612440c02d0300090742100c8402d0300d201c09640c010790400c034880400104940015500440109002c0403510300b043c6090f2041300411805008054000d1025100d0f60045410900400b50049050b02c40c40044d91808900940001c4a40140000074007168607500015044045010300103a0242d0f00d441c3d0b070000842d41c40401854441010500051503880403658404080000166103024600080a4a00231881c880c0410251000c50b50341c5421000100060040c1030103003101c4d40c1c52244052468030360006020441e4036410340c1c800400d000d00042e090361041085511460303e400039080c01c0e01e101c4100505400c0820500186108006840c000d01c42c1c0151004c1068a41d10700300501002c02000c030080459000d0762043c00300700081040050107010040054844800b08825400101c4a051140c0300007040b503401624018108092540198101c902030102040801030500046600300b05034407c031251076000c040103004800308040401026482 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 346126915 1250 346125665 346125671
    0x1302010e060c07030807061a09011203020304050a0909060e031312020d0512030702190807060506040b0406080d080c0c0a0320061305100507050a21050103050106031a010302030c090a 80
    0x41c4000151824586403c01c40d117408000c00c0c0041006468081c1115510700040d00e174600c010003074080b6042010503c80c800f00160f1031050740c0240b50082c0101c4010301009805521300c240c5030903114003d4580e009048400d6842c20b50400800c800201c142e0f0a610301ca00400c030085441c0601ca2103a00e170b50408242e0703100070a00c00c1140082e0f01008040c505100c40032940e500c1e031610303003000707070400c40801c090040146401c2441c500280d201d50459000716070044d070009807a00c500b0086402841c0480699070070520301070000c1101c50300080e81c1d440005040e07840c3d4115954461800403107006070108030702c0d66032002c207807940000e00401034880e801da4030881000f040c006110703688d4540281503070340e01040309035000010244141413004902c41903020b04280041d090000008000d0f00c200c03400c0c0c2c02000b07441200401400441c507480301200001078414406540c41c0c1c00c3c0305d07008246a03c02101c000c01000b8401d000948000c541504a80e0001c015108032070f80e10080c420350000040050009680e = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 346128165 1250 346126915 346126927
    0xf01060f0e061b1605010e01110f0f030c0106060e03070302060703050f07150b01170a05100503060f06010206060d03020703080a0e0907030902030105060301090c26031603030b0105031302010e06 85
    0x2c4071405456401440c0c8208080e030340b2082c3e400c5041c08400031544c029160030050034002640c101e400024078020a1a0101003869007621090030b0081010740d0389410b00032800341d84074032840040640340d0b14101d64000c00c51940d031038006030360000d1720070100c40d0180c0140004001610340140940102406824903600e4240c1c040e004407820343c090002110502c20315800781030f406026225501c5102420b01b040c5c142905038500c69044640000d021804854607500001d481710803000759100100400fa048840c5c1b41046905051070110865110380103202d10000200d00c1e2500092400780d581e0075401a060050451f21841c0c0158042d088031001d101c60303c1c1c0402e0311515080c0d216440352100d9030300090040003620405013500c02c007418091103a07040800b49030200f41907000304822214514680040c8585442100d202100000190403c5010119019891014009120344d00520aa8040044110002c01544c0a000c141ca22080002c8080400b10055020f100d0501c06a5801000319040032 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 346129415 1250 346128165 346128169
    0xf1103030318070f03030e12030d0c0203030a0c090b030f060103110f1c020f0d1a03014b0507120204060c0b15030a020d1407030c1701050f01060f0e 65
    0x503105a0312076403240180c2890b01c4220805022440103400000101841a0b146860003010410100c0d005803080c00c0751044801c02d10700801c2200c0c0780c0b0084000a00480c1c8020714042d44940041b5629800141030004e6141403e101d09440b406861181000038111346401810102d400001001a410705507162500c000d10500000600445034842003a182d036440c0d000c00213042118185130281000340140701300800030103440705460950904000c0080c0e103c10641c00c480104100e00c0d00960194645140da003003200703403540a103a90244d161122620103c1a560018400040d42914008000d0322490300810005a40005412040c140703441d01001c2d800019800c104c1e0b00c07585c40440452440010581007003c1c1c0441d4582c0040b4008503820f071441518042501c40e059281d000380304420004142040100059004900030401d104a625075a12850072445400a5009a03203450000c911421941031050188a1103000b8803646420f507a40303400015566640658959000d1200f0034201464030703 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 346130665 1250 346129415 346129417
    0x204031a181203070e0a060905010f020a06060803120c03060a0501030b03100c021b2b1e0812090a0218092103040c0515120c04030b04050a110d0507030f110303 70
    0x42e015481550b60b90410940181c141d03010149024081c01064008001d440d412038488001c5030000e003880e5207681002c1804a0400003402001031140b860f01d02e005c07403481350000c0074040d080c0c0c482e500c42c05641c07500e01c220401ca000868081d03038402e40c403060501443d4401c1d04941d4514001400b01c410b141c104a1403007040d101c0240c00034005900c031000c00d50f2280f0350301e640200b0070041595030500c1a0000605606403441c2900f10a00c2042c4400300c490070010f4007070300c1040d226240c1c4040c2442d500e0301d1134038000c40d0b8041d8400b04044410713100401c00c0301c4400700703020030f403140c0c02031010340100042d64094400364001000440c40e40248103181310031005614411446040c1a080c00360750f8907003842c210235441c11503081140140b504d0030003071500505c164100c40c0f41a4014a0120607a500d4280104149c03050350002425040e0083c240701c20060700049100e02d13188500305483c04080c075041800100060f40002030041e6000c06410804681c502419418140c0141e6104542e5200080840d140d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 346131915 1250 346130665 346130683
    0x3060509060402090105060a140a05070206041e050603090604030c030e060d060f170d1817100e010216080c01020c0a05070807080607050306061c0f020702040509010204031a18 77
    0x306401600c200411498542c002a025040446106003410383d0824010105d1008491103400444001001d104250046080c0c44803242c0c024201c0e5500d98940745030750318000824100d000b07a40302d44a03010801d4549542520f100c2e0000c0002409642e4a40c0c5003152880c0c1c1d480c8064040c000710111800c0e25886600c001c2c100421040300100701185040c2281c210303852031b58030070003e001e5401400c0c0a001c1e00481c60f5006400607103800e0784500000d18142d40070f11035035884100200000349000d55023103008140d13030f10304911a920401c889664102d44600b80d12500003010b441e809144119030005000c00d024110100742a030005042070f10b0648101d00d4000f04070420b560961140101f008133903000c000400103000340c00d0140c041c60034540e0700074100340005402984100740208405050381094080d10260b0074418100340a40100000c0039002980019020303030240e41480002440a6414021502202d91240040307501c483e00d0740d0348042c0c1c3d0502500c9035043d0802d200d070030381c0108010410004 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 346133165 1250 346131915 346131931
    0x60c03050937030506160905010807050f0414190f1a0403150b0306090f0d05030711010f0c1403130b04021507201002060106030c0e091003020a06080f06040b0109030605 74
    0x1c2e49030950a149240c90720040001ea08194103a45290400380e115505104480080c00d0100301074842010075a028054000c1e1424a00340208000074058a0211410710042003a140c0c8030104d403040079149151440d5006229480075000c034100003000c1c4505c1d0907075104a02c01ca0407800e058890b9102c0c1c05030f0291194000d40381e0b40f903010456552a007404a10b4101302c0301d40050038010080020035403900c5041031588148580400010710440c01501c40320040d0000724000c06c0300780240c4800744024180788410b50005901014004001d00192040300e015070168440145e1400700340c1d40742c818403030004008076040001c5120581010201d00d018180540c4243c903e40407020040d10404905e410043c1510720800b203049404020135008641e140c1980e611745404140f03200e0300ca50550340d00500c141415004144c01003000040020450710b503090b04e100315151104241c0c0d810080751900c0d020b8a6410308200b40001051403840c00d0307404400c092030b040c1070034001940e0304d448400c22140f003119844 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 346134415 1250 346133165 346133269
    0x8150a0b07020307061b06090314030406060e0702031305040b0303090d08040e06040612020409052e0501090203100b0a0903170717040b0909041a0718060c030509 71
    0x1402c40c501440407a0240806242000300c5440b60207540caa03002c1003040c0908080d6840041d02e0503d803041d0400e408d4101007051142d584d00345480c108000f00b420f4801c00d03110305808004640c88078404030440ba662603030741005207a99401d00080000034500800c1440d0305100400c0709085945924181d100018001d41035907490760302d001003107800c24074000c00d0341d0320036880c1c0102402181c0320744000c0e81d00e80750144d41c00a408485840c1852410140c40c0c0240d1030748552110411000e07202d281008a4490140d0083c0138507640e9540c9682a40000e982c40b1100052440080c8981c905c014060b0011005070702d00b00c160365546c0d403146803902000c0c00750320059601c001155800e00c0f10b18255940d21108c0700c00842e1400d803801c00003d120380504140248a00140404035040c0100300d0384150f2203146010040030303942000d8030040c2241040004442c42c07a2100c050001d0854052010310041d1509034071003915040c3e20004018540f201d110125051100380e0094420007001c00f0a07801d003802c00d07400c0307034 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 346135665 1250 346134415 346134427
    0x5091606050c01061202010819060f151803030c2402161a0609270303070206090f01050c0307030f0e0a05010c020f01110d150e0a050a0b06091008150a0b 67
    0xb00c3c01c1d6540740c1c02038a1005000041540180d905c00803c690020b088130084050070340000400010700348503030144125040500011500100c030b04050585564540c1f070b8150003800501d040a0801040e00c40540030807140b03100f82c404100040780d150100c20011119004194400e000e000c1240c01c07501030102101d4582406208008201c15524060503181001d90840e00c0c00c0c01c001501c0000041620301e00200d140c60030b100a111601d003003043c2c0b481d1807003642c0e1a843c141c1c82c003c0d50f5100c1181e9049413440b941d00d03010000c40061003283e000f0945d0025091441d681c00e0300940190050b0042d084516607a50f460140b290000d10000303804511070b10002c6042e904404009240240007001d0745142d900d4040c0080784030300d07940100c4084140540020450000500c03242e250001300750b01c07041d095007c040070000a01ca035640120301c22100184204031950135031041c0f041c81e0141c503c080c1d4001440310b1a80400e44e0252440d00c1d801709080700404c0210a0813004200f80340f280b940040c0061001142e0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 346136915 1250 346135665 346135687
    0x3030c020906221e020408150618060d11030a050709110a0c02130213091b03051315061208030f0c07020105160602070b0108030307020c0f060405040509160605 70
    0x41d142c00080890700218101024042005099410003146003200e6503042c020221000c0383c80c1c1c0c1141c074a0152811521240d0b10f81c481034440b001c00c500001d4100c58407002032420f1030241d8542e071031300e120700500320302d82e50704c036001e000d4a4000c0d05025203012902c010324194565040000813441440740e0060404503180c819084140d49501c80c6d19000002c0500c03031400165407121034000380030380446803058920300c0c440ca480002c0c441e042006106000d6010042000c2c2800c0d00f001021000c6885640c0d490900d480049044500966046042c820040f00ca800032a4070940c240280d15050200000d0072681d429803000c40e5008400c044880381404410002c009046138903265000ca032a0005da89480c81660000344144100e048456121135501d01c031009001c080c0d4184c038110399010b0000d4a01e942c5a0704401c0e43d0ba042207811000600c41c1e42c003494058108841040881413002d0304003410503080c030081002804004100100900c2490085140408640d00d5080140556290709548071041d0031 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 346138165 1250 346136915 346136929
    0x604020f1602030c040e0a0206090a0b03161814010c110603241c021318060b0f03010b130b0301020906120402100237020a0305011e0603050a080f0d0603030c02 70
    0x4d51240324520b811180d40b298680030449400075070b03045840326503070941e07540000c2035150307950842502d400000c42000310044031048280d00c9031504d40c841d5024280b03128200c68035105a40202084000c0b15500012194001c6030901c0c070483c400e02004030051100350200c1c01300d4000316110846803800c203000b2003081e841c4c00101e0383ca110040d2010882c080b000381c007500b20049049402070007203091965003c1520200c2e803142600589242c1e10b4080310321135082240c0035154a00c41203104421010f480040c81c0b40c144241149501e01038180b040700b909403558180100042d2450640554007003005503000d5681070010241c012030044200450300b050b00500403288a9640e401055520000032110340c4a120101381c00320428601c106000106d91203d414240814088002d411400c010004410080103400150001080110760040c0c00c942c51141c5c010303174240c0e20000d0aa5040700581e200850404030017400007200414840345002c032102c03c0c00003150178a0b402600081c0242c00c0b205c04615240c8 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 346139415 1250 346138165 346138183
    0xb31020304081603020a0c0605030402040e06090d05090f0301021c0c1b0f02120607200c06190e060705010509240703051f08030c0708011103010603050604020f160203 73
    0x514114214507103942d5008251003000740d003a80080041092034100b5208200c1155000d83c48043c80c48101d66945000d4074580050b10202e2042d42400c903804444a00010703503030305c91010040101020b10f140c00c0141c0d0240d00c24a900c07500801011150412510240018008040c900009031a615003030907800c002c44a1803001d800800480044c00c04002e0007404110310240c0d04411203c0c9103c48038800124164058241000d680c0203401c20040899003104d04400507840b00c1540c02044001c0030303402c42c1c840310300c42c0c000e0b81d100c1c00921808a01c4404a000c0f0f005680c1c141c00d04880b4001208009001504004012140e07691500d0412440c0201032281c1d248034658951800f0952070f070b14012824210340200724400301640d40f00042c0361001c4084d000c1c406022400c0f262081c0c15180c070f03806502c07a8030081e11001c6c28401c2040c000b506c0c000503c40d0022283c40038100504590034110300703e018000c003413f0346078015003c0c840c80260011b0070b402410350203184101c80450400920605040050701 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 346140665 1250 346139415 346139509
    0x105392a0103090b220c0303050304110a0605040e0a06080102031006020d02011505060703030605100210052203050d020c070b04080d0c20040e0109030e01021207240b 73
    0x100d0750810000b0440c00c0b00e641c014685c010b00e0b002d00700c1c032004004284101460080d08140c03060000205154011000310b004a0154040c21000c40b403160501c00205040d02c10140040c104202c204884554900e000b600801d241101150195496001e1400d80e003041c1c41e03103102140c0014041010710740401400003c0d8040380001c2c480c02070a1003900306003007114400ca038007030f120000700700040522950081c405043c1c002d2001d000d03680110402995541041324004050789000d0208002e070f0f03482522005050b501e120701c0700084c035003a502102d043d001900044115038003031044800310765040c042c1c00b0162185040c0e0581301e0385882c568034a400c0000c0792207418014442d46100c040740790000308030901c4c0024600c3e484007004d40c40200b001000c0d0403119401c0ca520b003e000d0b908055110480c184c046409074211200b45c1c050091107901481107000c0242501d0400c1912039124101138000607514410b0035000a010075001c02103503100d00400940074003404042841e88841c00c2d01c4888409500396 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 346141915 1250 346140665 346140671
    0x60c0c0f010c091809022d0603130305070309080a030305070f050c1507090b1303020102010b10020c0f0d020405090d080a18080d0e030c0601140105392a0103 69
    0x10394026001008500603c44507044181280300030a02640005c003040385e01802107440d40c90020100c40c9a02c80c08504401c0840c5080d030340d00058640076043d20300031041134220ba0b4034101c02d50f5084d221503204110407014803800e0400050b4600060102c042c01e030380292408503203031078204c1006000450105109080c41024010b0140c0c100c400103000001002c0d072404101e15440c1c0c40c1055404034a194000e100202c80003c05161304480354100360f003128800e030001e00841000000f00103269203007008200040c1c3c00007405ca41246000c0490303880078480507202040c04d2810b600845c05807481121300c0181c1c2d9104074030388042e9583c403804180c0d20220000040041d05840c00c2c00200044031018040e0601c00c000c00c0c03620300d0400b1581318900840b000001c581e9204103504400b500c48000348a250000f416088103a80154001c50880c0d904000e80450078100a001000f1030384020722220882c0d40181490b0045440c08a040001203011121440c03102030181c1000c0c9117035549041059401d0405003 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 346143165 1250 346141915 346141931
    0x209150102071203121505060f0d06050f0108160306031e02030f0c100302030a0609090f0318241206080a0c050a0605090d1a0703020901110a0b0703020903010b03060c0c0f01 76
    0x81c5c84200b55801202c4c409001c90594001c400f800303101001900010752050f000100444c0061800c03000382500c905100301807000c543d8980402054400c2c40031080e0100c0c031020300080c041540e1901a16040169083c0020002c1c0c481d101c2c5010800c108040000721251804100b0540c9400c000d00c13240c000750b820045c0079009005003c50803070348560102e8024583c012001c07440f0100150403c40141551f2181041410042e0a0404606030490000d41c003251000f008029682e8401e000003042d22210f0328050b05100440c0b040c032a480c50008005e000b0049440300c180501d2050b801040000c00d09040184401d8419090819849009a0000c1e2141d07001207020065590080243c6040380e201b21040c100340601424003405d11204228a007050083c80702c1044265074055014094200c420390341c2d8021807404503080c5564540e41c030b41c080c005048400009030720320300c01c0d0020814282c0140012a560012401003440e00e02c094900d03400741c100119030426143c2d003c000e540c181018260003404210 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 346144415 1250 346143165 346143167
    0x60303050c0c09150f1807020105070f0807051b012a0e0d05250902040b040e01120f1502041805061018030f0c03050d0f0306060201020f1b07030209150102071203 71
    0xc0c03584c5081c2d0003103c6800100c0400c0c0c3c1c400c605d842c07511035a4a05c00a843c40e04440c001e00811003101c240000c502408031605d54248075142d09841a899522000d141c1a01c010a04207041c0203240351114a41d22008a00c4034440a0780c6d514441e590000c448922002e00301300d015014130310907541e103401240c9a030b183c0804983c3c00a141c4820000d20003c035801030504c00f40c0c0c9014a025600460030312400024005024440700008204580220414507860390302c4450384c00441c042d01d1300c064145110001180046007182210041c2000c80c940010303c0e256903a00203501c001c58481c0c26a0440e55074500b000f085081c6030000f0040180c062416007a603504518ac068000600c030b000c003404c610700c5142c84104100e46090f4004c00365810004035651460706490080003140101d040e0f400090802d0400580070703005000752aa40700c8540102810040302116543c0d003841e4000341e2004500c6800800005600c444100d01c2c0500d04a0803100d6525011b003001a1400c8465403100980c640e030184028042 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 346145665 1250 346144415 346144441
    0x111216020c370e0615040e0a020f1803060c040b030403080702160602150105180403080a0212130312060b1804060f080a060e1609020912010c121a0108010612060306060303050c0c09 79
    0x381c3c3d40c1f001c0d0350105403240c1d080307540240280201080801c10000c0c4404480c10b80c91280742c2c1010301201250100d40d81d03421141d002d4000c51154041401d414008580003a000b03030780a55000d90035104035108003002c0301c403410000507290300c1140942c010700e0741c50b000081c40401c180e000d44001c1c1c8043c00b00315004d1b0a41640c070240100050304000002d4080b803030310300c4660111001d15016011564040c28295402d42094400000850120341e10801952070308245000c1d07901120200f1901605106030070210211a003400740a00da03105546410200d56400da4011160140c0000ca0042c007103131a141c034001003168400c2444050130380c04103c085691008040500041e01c2c90400d015850300c0f0840040b0f120800b00e80c015003005e50030300d0988040c1a5008103c015200c00d03000050101840406004540000118080c0d0000300c5402c014462180a400644a81b40c3d506c41e001840725030380d440754012174106410407000940005440100050104483d000c1c020f0202e500281e1428200114000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 346146915 1250 346145665 346145669
    0x10503040f0b011805070309110d0305040503070b0301081614010507060902150901020d0503040b060105070507180b01201b04020d111216020c370e061504 68
    0x1000400400a8108240c50514000ca1540008480040c1d6110507504020002c103104202140380303081e001440c0c05100c0d01031040125000802403140d144001d081c03060030642494140c080c00010000000d01d500c04101c1680200b201c1c5820648035410400500c0c20150030040290301030405c081c00780102d0b03800c0401c4140c410024200b05030b440005e0320f031000181c001780e60040d510803d4030f540410850000d10041000b1f40c802d90a1300c1c10807541e48810f42d03c03400284d0b0040e0000d500440095074650140c0d0050140c503028408031070712103507160780f0600602c418a203580c1a81da1600e03910031041d6002401440d0071400144d020303c0e0707420800340640d9941544400000517030810b11b103400ca103854550449170122410324042c40540c415909a1480d03a12110004100c032100100058403400388000001c64500e880c2c0c0946030186441040150780d10114116002c811070145440440522488450100250b4130034000707180c1d031030081da0500700000100f8050182010f80c0326102d40044580c12074003 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 346148165 1250 346146915 346146917
    0xc080718150801090b090d2102030402012706080a05240a1203050315030a050d050d06261b0d080c0c0d0b010e060402040e0601050a031b031d01020c0c01 67
    0x100c9032403003000718411407940d92000105510b0300e08250180961080362a2040d50884100d58a900b0107000403900c540c58820180c4600070320f040b0b0040d40411680003180c0142c0145003442001302c01c011076012414a11000040741210700000304003240c0c0103204580d11000c00c140c00c000c1c900d03101101003030700b44c011280e00c650f4101c1c00d950204c00340d88000da01c001802200b07201d506042c400c2e00c0c001c3d00c5d9900645485260305007007800100649000110402c2841d1701a010f00100307259408156016007083e0b1140139000c1d124400403c0003182d0b5900d00c41d05031000d506040310210140f06150820180c0501e001c10610355001d01001f1f602d80b1001c900010741d010b03500540d00c491580c09181084c00107164540c2c0074000203074100900451a034080c4c16103400c8210502191114003c01c41248610300c13401580107500000100158028806480990860305002c03540e070542c80c284031841d5003540321000c04207039070f0000300341d81c60801c1d0414800a04e41d20000c6182203581e0392810741d540002d84181e8 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 346149415 1250 346148165 346148171
    0x1c1202120306040b0d060e1b0409080f070809040504210228051509010510081603080306120616030c03050103020d060c170c04090e0a0b06060f1606090c080718 70
    0x4100380d00e03400c0609030717010380007002001008020f0240c680c43e41442c05001d96417110001d030107046481e2502c6403895003070348001d0b00da10f0940001000755a0381c10131082a251118288808240e98075103004540c451441008040c17003401640840c1c054444d05140210110b6201c11240c000300050802461009103011425804600c0f0500d06186040104a9808002c40c0e0790340500c180c0d08415007015000d08c9518031800030640c0c40e410121f0791034480d000d2104200032510b10420206403104000c5801c08030180440046044264245282c850191441da0b42040264152f4602e00c3e498429a000030007145804e000c1e42d450341d000240e50001203039003c1c0c4003079541c016031161907000e81060381c0026a10800303041580741c21034144045801ca481109505400e090032120510000b10712840c0f00c55100c403050300b9981700c43c010301907190800e00008056480400c5200706514081d0003580c1c18520448010801c2c0501d49003280c0c0300005a800103c080d0300400d0309002104140302050030301c000b880c00c00 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 346150665 1250 346149415 346149431
    0x2190509030307050307050609190503030708180604032d08010302060d02040f031b0603020910140409020f09040c020712030815060304060c09080303060a180b1c120212030604 77
    0x2410340c40f410030010418840080d04804100340820341f030b4843c020b0b4809541400c0a45084c6181920382d0f1b4400510365002040007458090181da04240c000c0700e030481001c000c05948125915181c0305171025000b00b40c802094080340807c1c01c60025403041c5d58111040c840e0700c002d178050124035040c003000784500e1380030501d0140388d1001e42c1950000c00070030309035070f174800c1e980d003003100a1164507c0d502c0304004d80d035807003c15a54002c4c0220b8440d5100905039051324a0f0440d01200c403420004410390040c2400c00000442080e1800034006020782c040b409583c07510301c9004c020440c2e039035a464009540100700c08206480203d41c0d0b1001c965014204030341255110840b0b200f032492810946a80050b0100500007440201d078020032050002c1e4075201026a03c0341c0c0b45c1d960b00c0c04100c4480750701ca4282d800030f1254048002140c522000d100101081c141210f0001400c6e0341c1641e00c14008207144141c0c05024440c0c441c1c10030403a800240042c100d58214203401640e00c0c4401019103010b95262200303 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 346151915 1250 346150665 346150669
    0x20405040212120a110c0117040501060807080c030f070e0f09031c09060e0601081e1609020702190b040311060d110a0e0f0603071b140a0b0a02190509 66
    0x80c0328003000d10742a281c91001d1561083c1c41c0d504004045000140001941250b00400007940741072000d0503100c0c40d401808110450301d12030b000800c00c440c25500d4810000f400d4404100a2003d080e054015091030b842103001d141c640000844446034075400700504105002c022074031181c2018a8100c00c00345e03641c500b034030b40d8903602c01c0b950780c10f804244040c1d04011070301650b030114802c18442d01c0c040c45800c602d9015140d440d40d0038043c0c103045403c441030840704040f00c075001407094200e01703050f80c4410700d545080c03c0004842e5031140d80c2081e00060040c085107811220b4160b4140c8002e03035040840d0030401051103d00580c00f004000704030603070a041c1c03da511017040d1a40e2000c02c800c28007400c050710210380780c1504103480030b9001c41d40d9036040840a02c0d05003030310911004007524503829651541c0d4208d5040c2e02c2200c02010001d02c0843d07a4004c108014124040c9000b070b0300c01003480301e0040c603058032040340040031784149910620a94114251102110401703103014074001c1c0d00c0e4044040 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 346153165 1250 346151915 346151929
    0x30b03070312030504030806040203090d120b090f09070e10031e050105070903020909070605030a090c0806042907120c050405061602030c03010b18040c09020d0e16120204050402 78
    0x40904550b018001105550b40d158201d148150700c20360318480700740c40794420300c01070380001c0e200b441090300001e91009403684104402c94240402c002d0200c0d0000c101c6c6c01103402c1d00b500f80c4003610489000003c0050046d001c00010b00101201c2803100241d24002103a841003040ba80802090b01f2083c0d0004c080c41e03210748960049203600f06008200300e04160b14090001c9d201840202d004020710000030701443e4010442000301d030080c0e2039561465564050240040404610031100302445040110b90358604101f11031080340306003401c50b10181c13269918050741ca80107100301c00d14008403007004a05a4400c290380038105d1a1003022801c0503403041c064516001e9900041d401a00104001c0e20b407004482e20066958002d6054510011010003071600740c0b000c000510340c020440f60901810444503400999101e40079102018610703403111300c1030060b07038089a4030000c407a40307402002e08040006c0c0940d940600c0e443c4200c94215141030a04500b5580001010744035a60301c400003800d544a00d0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 346154415 1250 346153165 346153169
    0x150e010c0c06030b100e0d060e0106030b0705030f09071412120f0a080a0504020108040f0f02031c030c0801030b0c0a05090d0f0b0c1e09041e051f0312030b0307 70
    0x6012101c02640707910006000300074031241c0714410882e003039000038400d01030980a0710341c0c0809020880d078a4805c6c0c44030300107809020390942c2c256586101c008085040380f078115000c1c00c0c4c2a0b58079950b0f400c0842c01d11305803400281040302650001340040002c1019040c5d1101807420036140031031019010756841f0b003024960707a010f0040340000134291252407a0380c40200410040741d111213207540c441c0f10010707040310340454000b404580d802c404100400c06c03c90b840050f039881b0300c0b07540301143c0740c95012900b841d140381800c0401e0344061441c8802c0c0f94044c05603112004880c68698030661650b10791f5002d9020180060035104d0000440203c02c510074000c91f51009000380c1014030780311051030a0800540056410383c0c0a800e05001300d83c9400444084543d4880001080c0020049020081a4643c003a603500c503401942d50080050f420405011000090701100000805240c0f212525074178503520140302844a07840303d41400000c201500700100d280e02450001844440100802c1c50990f8035 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 346155665 1250 346154415 346154423
    0x3150f0f0406240905030703021203071703040c0b03190c020a020d0b0a0e07031502340308150603130f080d050105010f0e060d0b010311040f1e150e010c 67
    0x20004581d1251056102844024256000740c06518140302154122140d005c3c0d1075250300b00b050100b0241c40d1840c100000c0020500681c1d18003141035071800344080c4500420401104080204028498840004401494040e100a10f545030140110400d03941e040401855a0759490000c0032640c070130414010807540c0509490385c1d00441d4200080402402c40c2c1c5a0407842c24450031682200e40403402801300c0b03038084103071040c2c08811104a400394101107002114003442010348080d003919020000b4203d01c12040b00c0368403001c0c41c14020407138078009040c40c107003a18800000269440d11401c90303501a030680781030309511190303107003060000e00381070720240440e600459064100d0055070720032812500240c03590a507440c2210402e072010a01d051205501440602013031480d207000c2d27040458901014500010240d500581c0e60320180c125800002c68044801d1081c4181c00312083e0115007100d142807102c43c041c1c82d1251003c40240400c1e501e808001c003003401904241d01583c068961141c0c4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 346156915 1250 346155665 346155671
    0x20303041515270c02030a11030d0525090f1205010b030d08011514220902040f05010909020c0a080705010b06070303050601020d11100c0210090f020a08010203150f0f04 74
    0x103202805080d440004000204000d8014043d0301c0c1001c1c02d1041001d10f25150700510b081c4205100d0540d0304510424001050380820800c600f0204201c4c0720b250700c541c0e003109010031120107038001048a0341003000c40c6020302581c0003081c06880042407542c0c048481700d0f01540015003003468824003400c90903a085415104124003d010a900503810f00d050fa2003038078039603420a8100400315050b9203410707110940307600200009458a03800c0390240e6480c0702103080c01c030300150751132158508a9105500c44e8882a4490360700740120360340f08480b0802403103103d00643c1441c0ca90400d154591212020003071000d240000d118040010a406c02c0c446000700400c02515038080d0705020b00900412950700e070060080c1316100352003500654016079403000c0140100a00c3c0c081115010090900072901d4040d8840c0d07075201c1040c0c407254040d003a035a5109000507603584400d807050286540f2950042d020340d07401407080207901c0351010300200000000322111103100d40c0a0010958580c0f442020075003140c2 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 346158165 1250 346156915 346156919
    0x8060f040e0304030b041b03020607020904020409020a090e07050603090d080405191a090d020604120216090c14070b060f010e0405070e01110f3c0a110a0303020303041515 75
    0x1d084003000e1b00c141c0c0244420400104441c60480803a00381d800001c1d130040d0180481409230400708556070b40103101070310025043c12640c002802d0b00c2c07403a901c50f59196484606c070354640142031146600a000c01c0d01c907181542480b0b0041030b00c07485220050b104001051000500b4000300700408240c5142014140007404018108140707017078103800c442c1100400d9400800c04171940080d0906030766503a82d0252003c0c0e1520b94500c030500c5201444031085128203800c82c080c002c01001c3c030000510718a00f000669030f01c0404003401d80c1006040d41300c0c00801c18003080c03000c92030304110340b580503008031b4131000f0040c200e00050f100c0044910000d9001450300c810450020307040200c4c01c030859400d8852a0452008403080c035580c0800700b103c440e10b0380100c0c08081d0300c018842402c8a041486800b0103001c01106d40140e4502c030010401036900394003d2a0200900903021009810140c040d00c000307110780d0071a1800713556440701074002004401d4070411180b0709040e56200d18101c2d0501420004615 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 346159415 1250 346158165 346158173
    0x90901060c0506060d080d0506060903010c270509070e03030d0c050702030c061c090f02030d090e0a02040e0c03100e0118050a090309120503040e1801051608060f040e030403 76
    0x18600c08129914481c40740030408514007003403480305895016402030b151a000032010b101804009d00000c0c0c005e84144902a103540d0700f03004400d500c00c171541e41c40304211280c0080801140c04036003100000171054205100940ba00312105900110500381513101001c95404245503202c0c3c100060525031138007200f0403c040d0320500070134859008070202c55103c4a40010008180f103201c1d00c0902c95003d081e11030380f08101e242c00007050140640d035000d41d585800e401007800d10311012002000200030700000d000494941410b150000245a8110b0500e42411500c41006030003401200410b40c0c04000148407000401890000d0003900004401659481244000c0e41030202c1506039024204000612005070a20032014407030307015510010902d01d04000d90410080c1c684064485000c104000b0444030810304080780103480c0c00828000c039100800c883c03421646e025040c0030000c412101801440c6601040b4142c005070b0480c0d2a41e682d000d0070b400140100030318802d413021400041000000d00c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 346160665 1250 346159415 346159427
    0x90405030927180c0307050619020102160807140d1b081902010f0b040e0606041d010903020303190b090103020114040f0b07050c01090e010e06121c02100905070e04060209090106 78
    0x2204050403151a0313803a000c03c15880b50983e000d140e40109040c0120801d8a44000003880c1050311400010f00d0415280c82400720300f03400f036500b56001a1700107400f004004045682d14200508003000d040b03031004801000f01088040e19494169096030070b51442442050421161111007200039094801800c81019010381440c1c0045c06807030b0f144c4124a03d440c107050003402c44030784115000c0c0105544040801004120310311004146511042050304ca40d4400d10031051458082d4000315146c0c5400c40400c0400380050003401c5800d810045070750b90a40746c00030303080d05403542400c00c00700c0c088645186194501807940288010600b104c800203030404460010045075001d9410790f80c0a0003408015030380b440991090f140f118007400d004015002040e4515034001c5801000065007254881105191001c401803180c80406c144490000c0740b41c0402c110340c0b107004c0e012402d125601d0240c0707030b10b919507100784202c110308061100007400300307e1194111240048020102c041650311000002e000d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 346161915 1250 346160665 346160701
    0x5150607030306060f050c0a120203070c06020312011d061003020c0709060f060c2a03080d1409060c09060d330602070f0302060901090b0a03020711090405030927 71
    0x1181030800c400c01824864800c6a06202c7e081c0001c0c04400096900e41c1d4540d4102a4110114002440900d002500c006084c40c014040c85e80207584a08404030300c032040c0344040e8420036041314900c42d06a03d0480c4030351107d9200320700711450801e201100005401910500c11450154000c8013408101d403105a801001951200742101c0c0e0100e407100c030103803041010030721302038a408848002862110190039082c80400b44240c0c0400000341c0d80d544100a40c0c0054003601103068039030348603044200c007c41b1076561044a140003070403103040000d210380d000d2003800001401042d0000d0b0401c0c034100e00d43c00c1140d0a50858210403102003002e100003003240c3d08050500502d080244000820303510026240c81070310303e500513420550385907a00b081286c0d880340102505104c6c00304000101004c1c602c2c061708403a0000c2d100940c0c0c8034400d24040d000c40390301100c0c491140680c002032001040c000002c0e55102c490642d000310800511000014041200050142100764000100014007855500b0307824 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 346163165 1250 346161915 346161917
    0x3271b0f09050109020a020303042402070303020d051b041a0c030c011d06040309060804050a05150912071101200d02013e13050d120206090303010e0103060515060703030606 76
    0x421641c8442139902a44100d40e10440141d1090000c1004200040403407942410241c0860007004451705400c016604400e030150301007a8080b6030310f60411454081e0382c0d40840400d20292050340402402100d50185024036221680d01c001c000328819818422640d01070f60f030728122038640140f9540c0c0350123084480204251045400c528407030509000038000e0149a044c0c0b280450907082c6002140d081200501c25949031045030804808200103000c0a41c001026840c05076940c6001c030007481c03801110b82e20007000100200300e8007010860081801c0b0f423004092900106803070560150781c07509940b0b42a00c1c08140120000006041c0c0c055014102441c1a1f00158117441c2c200c03a8466194010202c3c014500005140038011444c550b00c000c24448000919101840780c60740c1c00305042303c816142c201d501e13560b00040e021210f03404000351a030014490340154555030420f00444140039044c8001003030252200c001c10321450001540c0b0b01c8a00014090548580342400c005001d042580319001c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 346164415 1250 346163165 346163171
    0x6180312150f0e0106030605120d0516120905010216061202090a030237120201030902030f0f0604150524040b060d0b09070203041406091503010b070605060103271b0f09 74
    0x48c441c10000201391142c40d07078102500050b000d003282a181d03940f094102496080c40d103183d450000341c16401303880b1702608550340c20f0002414507002907d0004801b24010b601c0e0054201000100c0d8041684200e0324100c40e000b60700c6100700e001188101140d43c000940c0070600d1010f000d40c00c580d00400d006040d81004ca02d00d10560380084440885505020303d009034403011070300401550094109031607452004e012149403480200d030b45410525041c48131074103508668140000d1200c82121306500d9410b4450410441c100582008500c001aa01d0140015122040f03400c0e241d07926441000003140c0038040701c4d942d00101880c4001002c080708041d103d61104070210788030900c0003090710f05941074403c81d004035600d12030401c5600c3d080410959400700d00c0000070b55506900d403010b14002c1c0400e042c01511020303030b46004000d030340c0014080c82c1094903141111810105c400c01c10380c120032841c6000c000b11001c50800016121426181d03800c482029600081d44030030301d00d0480c080f103072200810 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 346165665 1250 346164415 346164419
    0x270302060f0c090607061503140307110319030809030c03040608010612201602100e03070905040c1a0c2b030b0a0b09010207080a060906180312150f0e01060306 70
    0xa101140901d00d4040e8109030240a18000100c440c0d01c00f11f000d0004140345454560307640c0d0b80292100c80310448103083d800100d107110810072043d0842c2120501107000d044044060581d9101c0003410301e401500308220306000c110098070500884442041100660382d80d0b94507804041d190280070701c00d00300040c0a2a4400d80032006510609031609810115100f0701d90404a00440541008108003002c498000e00c4c100180d0b42c0c11040a401d0703401d5100c4c9075900c40080100747c1010707202d80c0000b0000d0b00308000c00002900f0a0116029144036030703141106911011692030303440c0512880b03c94240700f49068006001c071030f1006580d00420706004408903002d00d403401ca05403174001c40c10381d411a2903610305000c0e0078021005014a04010b1040324119580c60301c9031443c06059090544803995a44220010311106014100144d9011031504000c82c1d80c503600204400e8400b900d03121903950740e001e01400f0007048540000182029071800d102c0588800c2d50301e00e04142072103120003280c40c1140c0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 346166915 1250 346165665 346165681
    0x30b0c0307020d0f031409010501051f02060a020706090b0f01030213020a0210020d180b040506100510080402030f030c0304080f011e271103010b011b0204270302060f 73
    0x460384980c4095000d00100f058100c0155039205928861000307141c1c851400440c601c480680d0184100d05a50000c5690751608040c440d003210840368419072000c01042c0d02441540004025030020440500142d8400d03150411070020500c0ba54010156104401800440c06943c600302d41600d000715080815523100f040d041c81248640052040543c100000100304001c0a42c0585101107a100c0c01180391306826440c0079840040700d1084803544c0d0404144024804100403103507002d40c0300006012803034144030000d954000581110820400c4600009046450612082a0481d07a2408880e200c02494880540b00c0e0030500450690f846842030403940c030b013014020904100c0048200740c5d1021101007010004c0c1500410503801041c2089020314103008160550384400d0103aa014480340c03200c00704050941390b842040504010f41e00034051211000103040c1c840d1282d049130b0014281c8082c0d990144001396001d0040c0c0031448962007030051603004203459201e40b1050302005025503c1e180 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 346168165 1250 346166915 346166917
    0x1103060a03022101020a020303040c0f14061e03090a1103191b052706010f0813030c0813030311121e1603020c1503130f1502070c030b0c 60
    0x10440da0180000c482003026090041c8848041c840004211400e601c600000c0c40c02e9a1080e100e20005074000403c010511400007010740181c00310110642c241d6150400d54041542c07441d003000d00c14a03001846410080b10444c0c99100fa8520246042e02c91400c0c1c4a155160202d95105441800c103003070344400c07180f82c0451801e0842e071840500401000e8991111006500c80a282d40981606003901241c1035850b2400c0034110019a81941e000280b8040040320515010740030320b040c4501d10080204640c1c015290540c452042e884d1007130360400c50704044501c201c2602d005000e80d017000504580304080c080349501aa4020b4540340070181c20518074603615140e0705003034002c4110074484c400c402114400c070b404402c1c0d4101070700f42c2026131040c1c01482c80d00c1481001c5015030f00c82c82440b4400d041c01000510450520508242546481805810900d142c10701c02003140c4101d00102080001e500840b64421040401c02c5407114001d10340600c642e8498003003a180154410001408860250 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 346169415 1250 346168165 346168171
    0x70510060603200d11040807081c0f0f0311090406090504061104240c140f0c10020a060203131a0402130c020a0308190c030f0c020a0203030f0307140a080702011103 72
    0x1000035180842c4200304d4401444080c600f4408107000304000580e44e078082003010054a107580141c011000804c030100d04401c01000c44405000070104032692441d0803020440154035141004145511143c491120301e00c00c611210354004e140050208400103568403036071003188564400c000e40e642044000b2194080c0b8814180c1c00e400701b00c8070f80b801400d00d803070300d4081c0c1c4554203210144004079656043e150710b00c2da00c6c56903668402c40c0b844104100401c0b000300340030000d4400c100b4002400c0d01c002d4a0303c0c103422029201039000008210072500c1800d15170880340d0030048600010f040001c0408000c4010343e8241d1285c00072035001d50140c0355510031030100081a40050611507400c0da0309640070f080044c1078100f2040300d80c001c80624801c034014400c00084175600000c080003448084800c0712021a8490b046501090035100181c40000c1180e4995442940050311b968442d0000c42d0801402c1000422a10020401d40e4055030031070007484c01070f09242c009103e450500c9074814042c2c0802c03 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 346170665 1250 346169415 346169471
    0xf0c0417100e03041a0717030103061a0427050c030a031101060b0f16060e1015080a0302030406050309070801110705060f090c011407061a01140703080106050c03070510060603 77
    0x2da40140405045d030060071914070070440c587c05210700c681c5070720158000364001d070b030200e0301d03040b84401460204400050341c1c41c0c2101c040110403100030036a84004401034513800840074020001c424080c08028024641100034211006501e1503c0c00405940300105454004d6003807060100e0341500c034100f0b50303490039841031045051541160381281410006c802c151a60340d920390803005001014040c122903148408400309907000e00d40d1031180d010704035a00000d62038014004a0300003a50100458049550301d2404c0d075200c0d20b0b5200c1090510f481c95000d083c0640c0f0301900305842d894004040c02d03115021354260740f900d940340c03002069100002c4504064030340000c1c42240300ca60059101401e6168108a640c0c284111030341c9000c00c50b58801e206540065030700540e5031142d03a01c51402044240c05606c121304040860b07602816421040c061304050040200d400c412040d420000c0c4c2d4078454208044800518401908000a02d0270303014a00001e0704001d141c62910410303131501981a658 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 346171915 1250 346170665 346170689
    0x605133e0103090f0311102706140c1c020f0d1d03040303021b060307090905101a1213050a17090301020d2004050d06090c05060d0204060e040b090f0c0417100e0304 72
    0x49803400d14482590140845110355030b808202b9a401c030200d04184219040441e4035900c0421a16980c006100c0300044a055401008002070600303e400907600d101c440c000c0c02142400c295001d1100b0608840f070811020700c004200001819030009132480400210b21440d010503e2000074000c1c07a11046490790003080c840c41d400c0240e915254040c95020b031a10010400045d111010203481074811581c044c42c024021070b0410344014056542c03504890725040b001d00b540143c0e40c5542d160004d009001d070001149a40b039010314410340c000c4550a18000340210350b034409a40e402c500910390b80c0c2c1030552039039016801c10224404001164180d500c02000e06200c00f0b240d580d070304060086008100c03610001d41c080000c0f10b4403040d01915040c041c100000d41c8450400c1002420700d10302c0e0411922560808180407103d84174070503120f4016031040d140c041241d036255500740007840f0381d0344200d0381c1d44100c1200086540c000300f04c4d900340040204080c46441081655030f13640e8041c600580c000088 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 346173165 1250 346171915 346171961
    0xd050901090509251b0609020f01230306030715050711010819050a090804060c2607020f04110301061106010e04110d06090605133e0103090f031110 65
    0x7148144540b1380702038a0041d1268603c06880c045100f0050360407103903d40c480d01c10108501d407090159010040070f10300140d03424942d8084244051307a143e030b90580d0040020228840d600c090160b0800f50a00c2c140340b558881d8102030041156020b40802d607180a08000e1402c01c56120b0b00e90680214400122010b0140344000c000005010240c18040304603991901900040d894001400080545458014404c0c159040c036410300c80d00b10885540340d01e6091801d804200743c050907030f50340701e070140c40a00d40c01d034891b408140107000e40d507040c0840110100000400d176601580e040100b03006402560b0080e40c0c0e41e051294100c0c800d950007003299607524a407422a0501030490354109000d81d4000c54401156207407803003180c109444c000302c103580f040100c00510504544203140444205c1e50941500c00c4e003034200d8001611462072000d0800c10001810341a07209400110802d90445816070310b400591602070f0940e41c4034040344080d80111030103910701030250b215000c1d10309420402020040 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 346174415 1250 346173165 346173211
    0x1009150b19200d09060504030c210b15030c091021080705010f0b011b0308180313090c0807020c01141c0f0b03240c0c0d050901090509 59
    0xa894211103008000701038403000c107100d88190090001c089070307074003030407041446643c018190b4010360013250502c070b0304000c03c10001c1d0300c050951007280d0015002c15072200c02000c111111030450000a01000903620511610121429181080c03820480848102c04800f03414861151821640d5030700e80c0b00c0032001040401503182d001030250580703001c4c4c90881407495481d003905410000003a521607548882c181c00300c6080740b14405400600b4200451003201c4260302d002d0700083c9107001820408020041408003c008500459081c480380503aa1a200d803050a651000194072a0801007070030600d8060040d070155400d54000e01c107944c0549004001ca0005654813904040c1841c803d5008000960710840c810740780304030380301d04560081040c150102c140030035901c540c0c2d4251301c2034002e1881d80000d520f4051241d07684107039509012410b0350303031880c15a030140100c002c814218018600e49034442e5a01034000d1914402c00d8035a107010680307840030b1148034802150384140081c080d4125460304 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 346175665 1250 346174415 346174447
    0x5040b010519051611100813030e0a090f050615040b04090b010c02210f010516120e010504080307080f04121d04150303031a0306160905091009150b 65
    0x8512035052613031900e0100b44445040b030f24000030030354070003500c20b165403c43d240640b200308174481d01e40b401c00c4031401d02881302a04104011030040a106c400f44044038203803598454a001000719500811500035040c8030200505011903100d4802e001140c0396441800c05a4250340a443c030000804e4182410419428010b00c0310300d5010341030198040c5180010b0b910360210501c5000300d00303401400404a440d542d45428122400312400d40d0420080200700240166607600c0d1513030a03d8200d207003084040fa080024510b0502c0c2020b40d50078081044280003000009501070b0b145990f810001d80d40e8400c0c1c985502c001a1001004040003020145105d4890888e000720711071034100d81c043c455018000a0100e5411987e8030756a581080010002d1641510946501c503194000001d007605d80507000070740751903005040c0a100d404680310b01e242d251041031030401520018081006500384070b10b0581840b407003482444200760810307009000725004101541c00715005444c00c6810194801c11800903 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 346176915 1250 346175665 346175707
    0x50306011508070201090204060f03020301050a110a0e01110114270a0201031a0301064a090a080406020331171504082503050708031b1b010605040b0105 67
    0x71176403103201e2100980d9a91007103600030841c1e40c00001ca258554810f15095079002028000400c0c40c0010648140c00180300711212038240c1c0ca005001c02075250011f0380c052220110402c60b07903203440030b4043d0468801c0701007402404040849141081d00c03044d8040c4220740c40c2c074584219040545000010350003604642110b907042a140d604c20208040800d0841d00d1503400740c10820320030100241d400001d105040d003100103400e031a50700c0c40c202403007a05d1003103228010b20301c00d00c0c4140c0010b402d5403028810004481c0d40300b90101e554903a01c0400a40d86e4000301c5501c500f0602e0403400050601c40d40c2c0781904004611192603011624251000c0c0303c60901d0180d500c01402000800031000e54804c28480c455840786d03c1443e01e070365280c00480b20031021030b00074105030750481b00180042a04070301940c051580c40500c0c039940741e82e022020b21143c030841165141100010940b028181000c0b0203021842d19079000030010700e5550810403051b03604a882003404100304010364452201c1c03032010400 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 346178165 1250 346176915 346176917
    0x1815020a0509060c06040b0105040b0906090405191110080114040f0b06042303150406020a05090a0303020c0102010e1b0f0406080d0801081006031212110318060105030601150807 78
    0x1003401c2001c1c0215815034002c580b1301540703400140411040000311070000d40540001d9400700700102031a00420704118020f0001481502c003140040c080003020003827041442540d996400c2500010316140e00302140c4012a148a68001248107200510842240d8100e6424040314408070030018188001000504000643c09855a194031442d0b01e0b2900107000a00602e0300e1901d071a840303114004031303820218404511a420254000741084030350a282ea4200d90828030069603140550b00644c0d2521403c0007094100000c0c100c00410315402060045141d54207800a02003403400071003150f00c60100b0380d180c9451718440901e41100b41080e500c50b00081c400903000080898842c400c3c50300c0d1034003c1001a0000e614580103120712901030042c116a0805800d003405000d0660381c03007074101002d6074004c1040014801043c600d030209604968508504140002d0b5241481c1686038100702115807011040d20030000006207504000031254101c1d900c89560b8101d44804a2007114415070180900e0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 346179415 1250 346178165 346178167
    0x2010801050d0212060c18180f1e07120509060603190c0b041401110f031c02160b0618040507120c0b16060605181605040e090d031815020a05 62
    0x10030413240030020a4056080e003000c035500c1d0031281c1c040b00040d0700038480c154000e10066500c80002110441515049030b43c0f1500500941d0310481512084001407083c01003c200d100c050120550f04100d0030f040c6211a02c1d010312080c1e40740410241e5801c02a140140c241c0c1c4a5891781d11190540200420342a20411103070740f034030313039241c01e19800c540003600040003044002c4851640303584c0010341c42050040401c041c004001c00b1a035419120700520000303007003404c61541014005036459045030640d20b03285840d8200890541845810b0201c1110564002d180c04c000f07e0302d40150004a0310b00ca998894000e0861074246011082c0708060708800712409410383c5008101076517030601402c20354404c40928003012640b4208001034645581c48140110481c1407042c030000e4200541c00d81c0911060700c00814440d03006ca00b01c03554030540e84560740d038501ca90240400d442002c10f043d040501c00b0764040c025210b0000404007003c0b001398000f0045030542d89050380c0803a075600038100c1c400d400d05000d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 346180665 1250 346179415 346179439
    0x7020f0102040f05030606090f010e06040209120106140a0509041202010b120d02120301060203031f090f0209030d0504080d11160e091b0102070504020c1002070b0106091202010801050d02 82
    0x41801d982054101031000300907140709200078181080b000c3d500c0fa80880b980605030508442a042c0c60006014100900b03821100090071500c0304d404a4081040c090032100203000e500030424020880390080000040141d40240107614000d00120143e40006051110b541c03610f03610000b02000c050f00d50000d40d52189100001ca0703640c00903000200a600000d031041c0300c00d0b290000d0038856401c480f0200c2c20030034001402196800400e03264080845150440198000d0091524030704040d88641ca0301801c2000b2905400c400d50003400304484250702f1140d0990f4010400e8506000c1d9000311012039001d80c0381845420f01c50350102590407121019034550009228001c0e940000341c0e0804040104c0700418040003d10030461111007a400f04801c641008161000070f445842d50700c100340c820707034000c5510f1602c0d02041c003500304000b010880865642c403071481c040c100b142091140740301103014102d00061185402c3c00d0040c0480c1d05954140300b40e0308081c100701021025500c240d8101c6035907001 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 346181915 1250 346180665 346180693
    0x9100801060b0d0b03191203090804060c0c0e070e01200a06021803060405070909151805070801061a0a170a150b1201030b06120a0c15050304110402030702 68
    0x80001800011100c1c40c0d60315940305404082d41c844c20011030180d482004900512914500b40400c096400000c1c00120758100381e08402400b0041c00140092000040000350075810502ca503d400340300741c200030182d5541e11b03691607000c0b1080f118240880d2044510780706540c07103040c005010081003a80d11008200000b002d0b0700c2d1500081041322031316400154001c0100c8120941c20210700304400400c00c40c0f810355242c0d40c4518051241d448140d448502c1d4404105203a60031983c115440c040c104103d40c021441105800804042030300c560080140124101c00103007d84029070b444088134003000d030180021300300650301c00811481001030760b42e5102c0e04041181d0309107000340c00030800410340c0030700d180030030700c3c0c0300001e0307210480c10101001a1054261200840c904494110621084941e2002d002c41c60300460a01c05003141d00524002e60200f001c039502160580318006181d03410f40d1140201500d5500c0290b501401440d014080c0d03240d140741030380045034080764034815103194941e00b10f0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 346183165 1250 346181915 346181921
    0x17151507030507021309020f120c030f06010302090c0a0c170d020703030b1c03082703040306020c06070f02150406060f170d0f0801060c050309180612120909100801 72
    0xc82240050320001d0041c0651a15000e40040b881803190104401440b641c00240311519845110317020780042d02000345085c90a11a10b00030490180c156066140402100c0d9150b040900080703100d5214600410b040c401500d007a114a100755440b24107080100342c8404001a0802392810030007241044806d10001040c00a004214480c0d180410198010f40420040c0340491341010203807518a0488008660b01150254006142140c00c20300c43d10311144202034284803010640caa071000050000403c401c950017014148004400d0780c0e019142c48104076200c105c00b050000040c2e210044111505603101d60594006100e481d0002d039165035030444041c0c075510b580c0305155108403050317584c08822003440038070f49895403450812042041c0140103000158180202c0b420000a10206810040100f04640c0940c1009001c600c03101c54841c4000445003048841a0040d8210760900c50700d186c00180300403d80407171580850820001c0400e03c0008100100030b03074181813070b01d2030021754014284 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 346184415 1250 346183165 346183177
    0x3071503020a0306050316030f0804050301050f04060605090106140307031b051c0b150a02070317030405011506270f0e0115080103231005070915171515 67
    0x5240503880b4665844082c0481e440d41e44458060342040307095050303c003814914078055940c40301c485c0c041444142440c503040d000301e401003500742d0f103000140640b2079400844944901e01c601003d02c2002d44407010f1080e101028881c860100c2c88801110007001c0c20740300a16889807162a0008010003210460442d07440070040403404218000f80c1c2950048200103149100e038071100e02885130300400030200344101c074a070381052404800400d658224070710a000810055405c540700041e66501402c40e1206940305440840d100d600e040760842c00c2c0ac61780403030b0604032070054881041d520710b4020300c0b03481403210066542d1800d603081800701c0c03100e80d80c060140240002c18441905c03503040c0303800304440041078488203040c080c400c001000081c81c8010002c0300300d5070945480102c0c200160039145040d240d20411104541890100200c06a02c080300b00100c030300c0640a049940785c0b4aa0a59058896008008410f4011800241c070f03486110b104141c2c0d420301a141202c8074803a908514000d070402 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 346185665 1250 346184415 346184417
    0x6060308220506030a0903170408090a17061602010915090308070207140d0305071e05190503031305030c0303010803040f1a1e040f03050705090f060901060509030715 73
    0x815074110000c03411486452842800200c0e002003814140041d035640401040d0a4099461b21024420548110850607a0901c1e035442109542850b18004c002500000758060090a0601c00019890324222400c00d02d815080080c1c16140c54580300c140c6069520070410702503640300c10381c1c480015a02001800c40100142000800d8155031600402d03d01002d0064001c642c0500030502c08440302d8041040d6004044071a0b048042071860107407070394043e00501034005240744020030100d017440b424130a9898421810b4400800703404001d024007114515019000c0e5100340300044000c0d99449603516240d010780112814851884103251941d8000d070400a107503040410200309150040700c405002d04408206880f840e00c02024502c03442c011804a51202d00100141d5011000f03070a04a4015081c2034017600d80702500c1c0e0a140e50380700510311030389000d0030201001603118a190107400d80503090043c003500c3c1c241d2034a003084650f134012031500b03603150140323100c002669841440c4160400c005 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 346186915 1250 346185665 346185667
    0xb0a232715030a02030715030f1b020f12070825140705010905060d1a15210f01061d0a0e06090703060b160f0c1e0b04080c091306060308 60
    0x8201d0040d1020452a4058040d60048070680c1c0140c1d008500002901c1c0d14102c4803401c0403040d03204401510601943c881c5d1f41d494444420420b808218080012414030307022109101103071540d40d6600c04000c856030703082440510807040001c014100420f203003e01454090b940c6906200c0c04444820b040700102c440007002a0740b03042002081c46614028802400c10060031450003000c00d255108510b02c3c2214a0703030b5903400301f02d003c401710101800394001070040136030064200c9400903107501801140d09002420030a540c0300c80c00071140544240c0800c02045010707403030310a050322520207124400f0306420303044c0350440c0280c0312081da4500070807800c08042058100074060009180e00030b03181004150800b802400489807040841d10300246841c0c4200c42100e040c2865501c0310b40b007002c01000d0f008a6900040c07410382070b004805002c07942800c4408919a1403c51001920440c07044142ca07400c90020480c0e10b240c40b480ca0341d4840e03c0c044a001c00700340c01d5500e9108031000b68000302e0342004 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 346188165 1250 346186915 346186921
    0x30209151204290402011b0b0f09010b06040503370f06050c0a0c1e0c0815010b180405070c12030903030b0301020c19050a050d0e01030b0a2327 63
    0x4100607124020120045070f201c80e20800b16615402640081c0064140120201c00540c59804c5d0b00006c07007040e40151540d20355040450141c3e080a00c01c0d100c4140e41c0d82001c2d40d21034103140c004226021240d00500500440c08426003031081c034a24031075900ca660281d2003880b450707040c109105050b40d40c0708038103450101031a45131031011600b014140d040401c60502015808540291010340c0e03454002d1240e0001511b45850703507038010550304004160200ca10800249840005540c81130480740211503181d0307a80740d60381c0701e1890007006402500c0b030200e102d210345603040c103a00540e0040d12500d45080f00c2002c0f601c6824140c0e8051b07401e40b0000b90360745150b20a16a26119188020b8402c03402946017150702a500c4da901c0702c604c0f95041000700036101801c100201000700404540d448015103c07008800c1f640a884510080c5000d8007081c00e01d0080f46480c44c0c60302040041d121001c3d4820084040c0c0c0c0035100595040e055869000b17280080252042d401880c10101202c0104078100010320b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 346189415 1250 346188165 346188173
    0x30f040503070b03010e0a05040c1d1e070f0807090302150304020118080304140301020904051e01150504090e01060306021303031106060d030c0f0606030c0e09060f0106030209151204 80
    0x214441d0f00c14180d0080c00e2005000a12001903500d42054520001141c82c0d280e9042148150100f60b000a0f506460301c102450503000500340b0620980d11b003445041c82c503450401e00c1007a03050171202800004c0d0403200c10559103005103101a048045480d044407915281da020400c0600780d21840311507a42c3c04008c01c4110369100404030b0100b05807030000071003140b40090160f520b000e5401100c06000000214a116441c25415120510350041c8140b046003000d4002420140031403400d9004841c0c800004501d04000c0714100080d55030955803949032500c0d20802d90300402c00300080d0045552602c0c000000b04e00b0a001804103451040c0080f00a540b65150281007101c00e06603076501501b040d000c00c00c041c1e07109140c42c9005074050410b981801c1040c5000411a285030328014010307072a0010210a02c04510f6410303040c3c400d4030002c3e66494603403054242e5111411500e11300c40b0b0070b0100041c4151442900a01815034015161600741c000c14200440c0c4c036040b940355155556172040c2000144 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 346190665 1250 346189415 346189423
    0x81b120d0e01090201050f0c0a0f060203060109090b0306070e030a140309030c0307140103181a010509060d0c030212120415090b03093a02010c0305070906020606090c0408030f040503 80
    0x41c4030700c0020041100c0d41d600103805802202c2c2090301e11040030840000d0b0341030030301032101d03d0fa40c0966000740c003e0031362910500940041e6805400160441d10105140c8114420107a103004010000c1145942d000c0c801c540c840034140c0b409400d40104459007000607803020400d601c51204001a5856000d1030007458582000c00d9000c80c82540001c904100c0b03550705585d12018600b080c03070086a4002d4030100a00b800e800075000030a42d540108501c000b00c4812a14030f03040e00c8048a40c0780307064540e402004040d031880140038024605000003000185000e103000611f028501e819151924010300d80190590050750040e420028040c1414004a40c0142c0640c080e0007540d20003400c60509903030b10343e03581c1503210700b101072081c4c500440243d4ac00c0c441500280400c040140c2203880d5515a4028042c02d610200a000f090901e4045849079021b2542c01d015102036034010842981c030712080088400014004645103e000c2201207482c0105000030810f0a070001c1c101d682c0e90349490181031034 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 346191915 1250 346190665 346190681
    0x1b09060f09050123040f030311010f0209030c09060111070303030b1002030c10020a02010b06030106030b0f0913030509060c010e030310080d0801060c0201270f08060c07081b120d 78
    0x822003180002d00c6603a820801610721541c036500c4d00b440000080d014490f8a1003960482c0c2c402440c1e000c000400c255101c5000200d040b2404002c1c03104148069000b001c0e801389080c5540d15800480c00c0c1002420302000b055405401450310402c0b8000c1c40d51100e0510400360403e5002a031200020903960424410441000d01075200462920307030f80d1072005448184007902da0300643c2c1c00240291225200750401d4400c00c000a0029903256500c000181c001c1c00c000c1200c03070040e0000d0524002a01d0803100d130300d11441201a010307120709600c1e44c088800380d20141d100c591100051201000c2c4403024421480d1400b02d2500070360752800c005190000701140b1380d203d04180c0e8000000844015808001181111300b47e0034105407008080c07005884e5a1032807150000094001140303403200038078094a10341210200c01580103240d0b104d050994441c9402c440002400c0d00401c0f15070b00080c1c01400418a4a1441000c20415888022641d00b04a154501c1c441400c1d000324a4690f1003803030b4454100 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 346193165 1250 346191915 346191917
    0x308092a180c160c0302090c0405011101200a05041707030b0c210601211d030405030c150409063201020c090702010b04090f03111603080307031b09060f 67
    0x1254540300035000c902d84159010180402404407420301049202c1c1200b0000d0b50303008040c100c85e07243c20320a83c8400c1d08144519070004458800440d48202d061040255026020302c002941a40b848a40501c43c0d00002c001c0e42040820000011404044006060100c01ca00003400c01c0300d1a500308410301040203031905517484410022071550211000c1d1366501c86600940158150f43d904006031048000035000e00035018402c05040c0803841260b002187c400340d40c1c4814443d17206541241079aa010390b0140540540c0201710304526450200302e2503d000300c002810340d19064540041400b40c0d1000da001d400b06005449010092198403c240e0558461200145c614903103c500000d40e0742403410817a6000703400d00800715000510079000201c00d20b2000d8824010f21100340707424090040e8030032050b000104103402c0750070b06603404101e4607180310320b10302160714a81c1140c9a4129960001e0f10300070605940307401c010b000001d0900c26140b2076415440d51304102e882d01c10060724400401c4240741c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 346194415 1250 346193165 346193209
    0x70801020c0307020103050105011d010e010e1020010606080105120c1003060e0c1c111b150a0b010c060f0b0d0b0a0506040606120f0b120303070215130308092a 70
    0x3018014003e0085182f0000c01d203002560064a0382c01a01e156201c01c03c19600f001c0d0001140e0080340d00400f1104e03074807003083d1045020100001c0e405080f0f4240780101c20001d83d405d40104107900c1e11680342807030b000b0404103490740740381790400140b40c190004400c0b2001c00d403103180030001c0810071003c0307507803006400180c00e2610440090fa2620360840c24040307214581e4407080790015404a006442455150108802c082072442c0c07201c0380e84245d007504001a4a9404001440f101c0e0b09010301d091710441a12a140764007220390307506c4090302d6079207440c401a9039100300103005a40d801d1010120b140c054024282907082c0843e400080e00d5004010901813410130600b000850380c171000010b5002c480e00000200c2d8140c00410300040c042802c411980200000c0440700e03a4000070000754040c420a400715510100c44401c100c119440840e44155600140365500000c20300800900307a1001300355050364103440d090148c42d0780a42803201e42c40c600701d09110828529041c14a0718101c101c204808403 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 346195665 1250 346194415 346194437
    0xf150103020711191e090b04140106080903121015030926040305070905180a0510110d0509030c07080a0b040f020112020a05030402041a0a0303080702070801020c030702010305010501 80
    0x100b0f03c80c00c02d1500060052807180f010303103c0c01c1ca8107003003078000c0c280501744840d101c1081c440d00c1200d68414080c100030189805400b10340b40c0b81501c90603580d01c0c44050005c4090b03103401401c1e40d0201004110b44503600081020355444910803d80902c80e806c002c1008500c0750a1200924503500c2c0320110000b41480c00310070308081841c8805d105406c0c480c0e00603020f00d0341000310700040e441c00742e0381c0010203030b2044800c04261000f090300311b03a100302c1350010158a40d2440c01045561007200c09005001d03130300400e8a01e18030f0320f2a500b1484030554480d24182c07515001c20302d41c0d000c43e40b00300c403044000e0b0000300e0850310009062049100429481d40203103480540c949501d035403c0c00181000340800c42100110003164042d049036120410780020441d258040301c134000d4160340c0f0403a0101d00c62031030302c80019200300080804032150000600030808181c06c55030300340c0e2503510142c500f40940c41010f03070001d07070800700740010250f1a074140055521040a440003500703494068210300e05120401542c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 346196915 1250 346195665 346195673
    0x201050f010b09030f010501091406060f181c0b071409010207050d0507030b0c07050d0f08060f041d0a060b0609060d02181203030f0601080709030b0606040e0f1501030207 75
    0x65410b544071909440d544101140010b840d04201c0311000d0095420200005824030b0aa07005102c41040320b03401070250741c0da5008204080c031030b1000340c0b034030310009100e84034034048521201c840300c80c4054411400a503144110340c400100e04502240d0048038070707007002080b9a20003405e4901c80c018a0704d0758200340170400080d441d1059401400d018100e0992880240320b0104841e10045411500003055414201403003c0907034403c000c141d42d2031007140d8000d43c155105030b10201e000f1210b55184001038807080100401e41c00c0c00e007400d507440754960700300540c1c8822042e40035010400c044020220100b1910b001c106a803000700c042485020103000396806a01c1c1d60b400c40303000e00ba80d060300503524a0f41950403042c80b0141c50f03805800000040307d2a0070081d0001c004c60103500140300d0004690f840400441d0034010441c0d0f550001480140c04100207044110b401340c10240007005207050070f8403040000c07a40c0c3d03412121900040c40d0031061184424003104d91403814882841e081d0701e8030303001d521 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 346198165 1250 346196915 346196941
    0x803060312040f120203070306060b0c0d0f051218010c0c0b09070503150c12040809040b0301060605040902130b070308041208042001030b10050405030c0406050306160c0c06030516020105 82
    0x3040110540341c2040704c03401c40da818040900510b43c0040300300007164880c0011034040e08046c17103032003c910816040b10015405001c204883d00441d82c0c5451a04001c084900c604072405001800c9a86a039071f92413540090030701800190040f00c2d9954035070040c1504000750100e2002e00440b103281c01180041c42540c801041d4803102282c1c1e03268904079611491090314040c80340d01c802c1610750104905000c20800c400c001400507950460b400d0007064801400c0500300c90b01d071321071000454800c0000304081c4086070041c02c2e101c20b414143c00c0e07104d59980035044251744801c604400007a0076078100420003880848400c654500342c9040956440c055a810f1421240e422403280d1141e0070108004042c0e01c0303a00540c00c094030142c05150342c9946800c000c1c00e0758005000c2c02d032080c040c281038180e950506104032021900c00a0090815443d000015008826160045800c01100c83c122401295185510310000c1c044d42c3e60006151400050100d5001310051b078000842e414407050040e1120201 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 346199415 1250 346198165 346198169
    0xb130f0e0f06030f060f060109060215040303150305120c011d030304030302090a1806080105010603020703090e31060501060c0f02150c010f0222030236040803060312040f 75
    0x4810007040e03071942c60000f0328115200e440d440c03207440341e030041060001e009503896000d02001e0f04c41544103a1103400980e2110a000181211500b01000290119101750024a040f009002880704265241c2e1121030038082120040100c01000090b40c02e0000b0f400d00c0303140403800981d100140943d00c09419680c8030300c000b5001070200754002c101c20a03d80d40b91954600201440d01155090703818014001019103580d101d5840103519000001841034024001c13620780c84d5150b600c49003039905090408070494009840d407803007080100c84000c4081c16901c4003501280c0003d40020031a62107141c80010780341e058101000300005862544001480440e410b47c0c1340b98101c0d01d1081074440d03640d01710094001d015071400c20b0b40c03d146042008810705c0d1f00400e01e014007103000c00b48602c440b49a0040720505440020340002c14a200b62143c0c4882c0220072103403c4007911407407034451700c07290000264070050394161500341001082c03026515007000720600e005905810305082501c0c041e0f8204c0c03020713814 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 346200665 1250 346199415 346199431
    0x9040203070e061507050d1e0219060609060b0d0c050a0804060c2a03180506040b0309010b040207030e01080f041509020103020c07030b01290f220b130f0e 68
    0x24000c43c81c80c0e9240c0000203964146540c01c151103c2c01030502541d2804007a041601240f00786070920040c18029500e03880200c0ba940080002c00140c541d10198170b0200700050310041d0390784e140421188c5060007460014071980341c3c0161104400400402161100348003a401e001040200544e200d4024513070707583c090b42010700040c1c48140500c095a44c5841030441180c40d203640500b410039584107105c071040d198026039a0309010f0100744003d0034041028062950b101e94240001c009140c034450065601200440011030b4071350303034130700030a060340c005010441c040359000744105801e50748510441c1d88045130001060080c1419240c01d4004600c61004290560b140e05004040da406a01100c150a040301d04444d9925034a05003004100b03800c0c0200d071248080507804102d010700a0401c20200300c0611886494030b000c51646074250b61101c0c4003c0501450300e000841000c0d040702100000309071818400c0d50310600010403502181e215041040301100c5210140503000d000d078582c03a80310b400 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 346201915 1250 346200665 346200689
    0x140708120c030d05071d030105040803130f1509111e0907090e0901050108060c070809010c020f300f1c1701080a02030c010309030f0c06020f0a03020405030c0904020307 74
    0x155900590441c41415072481e503075400d00f13042c040c95907406919032503140102c0f895013802c401803108240c03d0350002e64000d0038041c0d0038008140303400d1032a403610f40c800d442204400c005180715a0313111038911141011031303002582d41503000306109680f0b03062081703c10202c0b510301000e405080c42104190b9048169800f90105100240c10180580040006400c0320861030406103809158039019040074012031400307000c8d100c045542c0c201c9280540340c401f48c1c88100305040030042c1c4011036040310150b400fa40d001052520000700d54540d000a01908503015582c00b03c0041c0d01584078446500241103d100c580c041c5426826901d40802c0040c900a030700e021040c5803445050088403880e0413100c4081160603000000100c401d000210307d03161904c01e0b42960003900031040154100c0b00072410180204841c029592501803069007584840ca11a810040c2000490840c1400302e800100240f40400d60018041c00700740b81c20003429038118804c07596119a440c0c46d5003c6a11028144601008401 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 346203165 1250 346201915 346201927
    0x1020a0f0c0b0412150c0c0f0501060b0a0f09050f0a141f0c05120f030c090102011d010b0906241803150402090f0c09060703030e06040c0314070812 65
    0x41c0207000001001c10a40c1a0b440702d0b11400114200b001044007210f42805684000407802e0a40c0070705500c41e620b90700c510300411b0450b113900101d18580002241c15560b100000f09403a1800b401400719282c40750b80b001d52070f00f25000007425509240c0c10940c4191445001a5078076911101024140c40c2060140d10070f040c1c2070004194001d40709280d0b88101189402000403503a44558402d150a0003541120081c54180c0c030420708900c00c0d0704043c0704514040001a01019180c8002d0240344d00c1031000241440800350b0954104103040043d80086e5142c0a41c4455031034082c00c40b680120382200d03064589044013112001101401c180071031084000b01c0d0541c010b00700842d00c1c4090f01c0025040c5d82801c6604614a00b42c124112802c80c42600e41c4408070340d00a500070503851040c42819955482c5c02c40c001c00704440c2d900049411420582c4990104c030b10312100380000b46c042d074811182254914194580343c00c81e81708410a0b9000c0e640448004c02c4640c00c00074030000844400408a55220 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 346204415 1250 346203165 346203173
    0x507060605060a0302030912040501140a020c04060b031b270d05120904061d0c13080f030414060a0e06030c04080f07090f0e100509010b030709050a0b090601020a0f 72
    0xc409607000907070012011514500a40e0181c000b107118503480401e445186d5030f1003c1d400b5040c003d501030980012061030704010201e00c1d030f0005080ca80110300440e6001d081c164001000c0d95510b402103403401c540801070000c05018103000f0041c4280390301c800c42c249a00002c10040307043c084840301400050303901d45100140c071820503500c8815045002c3c2c0c0c090f018071050011199201003c044e015610b06407000801c0c5646104604510a8807801c040860b00ca4000c4283c03e80c00c10840704050028170940003416210070003110780000d00060285484901d00034209051020000300c0c1c501864017000100e80c00d03070380180c10380103444086810580740d44a40320b000240d400b89070840c0945108074a5503041001c2c000038001e040300d800000a201d01c0410004d40b1003528003502103c1003c0d40300c41b0180c42c20002a41044d42d00030440d400014500003148000781c64281540c6c8902070103a9500d06014030140c00d0300036044084000d0341c900b09035090200000391b8030b600440010b810390700110200801c00c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 346205665 1250 346204415 346204421
    0xc060911030312071b02010f03110f070c0f0f0e010603020a051b0a050f1b010302090d1a1f03032a0b090304050310060b0f0a020a050a03080609060102010b030d050706 73
    0x20040c05030440c1d4560401c90844200a042a10042c012070324400c5402d1a5613403100c20164002d5040c0e4544a010641d00001e8000e0400c00d01418401c89040c4040d402000700c5038050b10b4100c3c055040c243c00030303141104e5051350b1300c1d1980041401c40d00c441014461304100241407811510b06140050381c4100e00d40045070907000c0d607070b54810444441c03500c0c4e806800b00080c40c0d82901d8010317020707610204265a2003e5441c4082d440315103100542d50100f40702503010758040c0c040020f0103070200541f03011558808120312100c94140418240a0080c4440211040065600650903405100e082800d40d1400b80529403e80150800602e400c0c2c01d03588280c00624208440e41e0740174069040704d00340f1094442e1030f600180603680c001d1046000700d14020520740204070850f41441145403500040c2a0308803459804030010b80b040d840b0b90f20000000030020072840d941316029030786080880c107000c2d003002281600500058110783c10510711a9090b078000c120303035001c00b01c6814151366504042c5060405 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 346206915 1250 346205665 346205693
    0x70b010e090a080d0b06040b040513051005040c0905040203180d0c0803011214010f020c12071e02031e1011030709090e010e070311090f040503030a0906060e1009060501020d0c0609 79
    0x1b10301c0114000031913910b000090002d443e8211480080880c107298460b04999040b80d0315408410103a1080005003480e0f40003101c2d28a1343e103800c21070541c4030300200c0d00b42d130700a5a0b4023150050700c1a2200c50300c9402e10160141303500c1c624001c006031000e61030318040d50006001c2d61a6007048103034043c0070082c42c40f40c00d1040e0341d4164024400d1303400814082c0000c1d0001c50403d486401051840308544400c8000c0362280343d030002c44c44014006e01d003010751444a090343e04a030584078008001000a06245454070000281c1b0010300c500c03018501c454042e80d010a80d00b45140700103005200d0040d801651010680710f03401c00008107014480c560724094403454590b2007190145040100c02d0143d41c030410040540d056401c894140c0381c0301c0542c00201812200a0710680051020482020032a0014036031203000340804601c0d5522520aa540d0304808d55007414103202202081207415524042c88008010900180905c2c0c05e800d40083c000042c0c1a00c02003e03255202101c81c00c00060303404202d4 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 346208165 1250 346206915 346206919
    0x120a050706090c081e100509120c0c031501080613020a0b070b010f14030a0b040f0c060509090c03150607060e0a150e030304230705060f070b010e090a080d0b 69
    0x142c000d1414444079000703650007565010302560300140100050b00c100d80691119560080680b89075120104d03000344806401e40301c190252200c50403081c10f0304400380c45075440700d0303000d0300708000d07104105894144076404121811030610010003001d000419565882a603404110707a1454881c40001d0500e03648d17030002c0268440105510090003264250701e4143d4030340c032030105001d54076000c10800701c580c1c0b100c61561640c4200c0e080d02c005030300034489a0708544035550b2100d810034581e50f9038202c41d050f074120000082002c50f4420282c58140c1c50a0340240700d460040c5e00d1030401da43d41c44000c294111406000d2040043c040341000304981c0003400e007035964003d680460800b45000d640a40c64140c0c014010740c1840003124464001004a83c000c0d580910790748103103500300c214141c00c0161803603182118020040e00150640b5144020200c0f07000794010356139504c0705403400d9500c2c00810b07048900401c0c00801000807035600010003400280c6c01805035610f488030350341140050891500199 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 346209415 1250 346208165 346208171
    0x6060a061b1515050d051903030e19020f010809300c0607110d051c0e070605091c050304050111101806180209061909020c0f01110c120a050706 63
    0x201e0751664a41c40000300910108021480503134820800c28800c6240a0140140d00a582080121a03030f4047d0015200d2113802d02007248070043d0142c0741000c0890810342c0303100d203030460b04008614008521000d80310003402e1090306424500380d51681c41c0c1e800503080701a8603000403d8015011160100c1003140303401800507582d03c1680040e180c4441c0243c680c000030602d00007004040741d0300802c14031000c0a0a5441600741140c0c60021025000011000d194250303960b41544c1c01c2030410f0150394040c200360344071581d488a40303900b84840d049020450132120915240040c0000c1c0001c402c80b01240e0f402d18080400c1050030341c0481c20032041e010030030b50880c5020501c40d04184c0a03403074a503c290246008200d0f1000d14922514908803000001b540720014800044032171401d1a2000c000c52506941c40031800d45a43e0303550100d03441192202d200d540003107050100001c0900400290200f4460118209041c0100d850755941c018010f5007070128001c245111014442d2003a105001d070806014 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 346210665 1250 346209415 346209443
    0x1506050a0c08190206070c030522030204020304050c0109090606050405040906020909070f02010606050909071404120f0c0602071d0402180109090309080601060f0305090111030f0114010206060a061b 87
    0xc0120700f2048001c0015019500015241c00c1c004d030000710700c064054031014500100981c44082030166050300e107095a009001c04405600c861024512452091005119400480001404801807984009042c0f420b0040500005620800389e80440704141c0d00032071125400d14084000c0d0042022080d0401e0b0180e00708003c655111605401d0151070b50001c2100d1522140104d401d03214184021380c0103100b01c00861000ca02c00d4202c40e102500c10403405040c00c1c0c07140422000d000340c107042956030482480c400c20038084902c82000080400780000e00403d803902454030403226860b8050100908140300003000e41d1501c400c0c1050140303400c0181002036071150b54220081901c12000d41c00102035000c0840c0c242c4000600906035080b9484000c0600395410049000d880000c003040615526a011101d801c0024409035000d004203110030350b03456040c440040101000481c1c100d0465110806100071a20303582964000c0e5500e501d4281c008070341e0740c1c01c900321214142e0b400400401440c005 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 346211915 1250 346210665 346210687
    0x30c19020a050d0f031214010b3709140918031306120b090613020f09030d050a02120906030f07020f0d020c01110a08191e03020706060501031506050a0c08 68
    0x65404e07294440e44411070024030010700f01d0101c440400004640011035401030003d1000705015240107481850248243c1c40d6440110000c20115540d02260425a072046a1166044507041001c0d010101404170090042e0001440c07181700a080000c1c0c0d41c800c0100044c2005092045401c40d1031941090050301e50f0341c4c5070080c0421282c01c514843e0340e14007401c009079464040901402107038020000d5004c01c142c80c2d1070700000d52010010205080c0d0410450030181c806101c0c842603401d89441c5c181c1c071500d100f400a404d1071411a410b9042e100d082000e40c07020b07903419041e40e8000c10742204034101c60b0780b00385040e46852008107051100707109501c2001c2d003856001602e660b50410030b0f6117600d80c007040300e01c1c02d0340d41d50341545d4000d044900502040d40f0920050300c03d1a10480c1500c3c004140b034114648000488680308004030001e5000524681400560f02800c0300415080c68200b150301028000744e500141c0300d0088001304400081e141c044d051292541c202d50540128007656200641a4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 346213165 1250 346211915 346211933
    0x803031303110c01020a12030609090b07030e0d020a08091305041b05030c130e01090b10033f050913020d0509030703090611150a020a11030c19020a050d 67
    0x80032400100306942031511004045020f90703190380183c0042c07200000d40c0e82c0d034960300500c00c4054410540d8511002038200810302416003044c1c040d881043c00c1e42410007008090740e1038070f440c1075542d61141503440c8810f6400076100c82e1217500b001d10207443e0350040b40091008206210a086080d0411040c23100348000315071b09210f015107400e40a4a039994035414503488240e510319859001c422049851442c001e1900f01352084000140001104200c90341c440c81038400990740401d00d4080e040c014000c000074450880c442c29000704e2209108101004011252460620082000074030b68400d44c00e9980101e0a449907031030024891001024013000b04402904421244590903042001242140e68084101c40f005030301075440003480c41c104002130700c211502c00341035002482074a0844100800205c1c1240c0504e03040724001d1703660262104001c00b61192900b180d2025001042070050401000940768502000c4140403164042d180c0006515019250b01440c0c001400010340020003000342 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 346214415 1250 346213165 346213201
    0x6010306033009150302030c070506011701050a05060603041202010b030102040902180604050d020607050f011d060f010f170a02040c0e010f08100302130e1606090812040b13080303 79
    0x1e02a0781004070410021141e586251042e102113600c5107000800f8944641c0066603c441e20032031142c500905543e506160030400d03480101400501c0d950800c4203142802180d0300455a920b06101c0380c2414000200c45210262008007001807058820041e50f000b07410040c0c000074014003c5455560341c8804c10041c1d80030741c4610000d8260701800c1d4045160580a40d01179540160600261030490307824403803e6409100140c4080c801e10341d02144c400d409020380007a00d040c4503442182d540c10015004d18194015046240d01d01c00e0b4001404020003045040e021110722141002c5a40c124140c00350512001c1c600294000c0c0c100302c26002c8150700704504600001080c3c3c2c508401c604850340484403900140c07108141c0741c40324101040035241c40003502d03081c0303000c0103c00549800a0460b19140c01c1c651f2581e2010001d0150040000c5900400e20174000c0035a40c01400410210701f800c80312511aa0044035600d0784081152400c62244500320409000c042c0200c981c1c03414220004000e84540f4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 346215665 1250 346214415 346214483
    0x10b0a0f0c1a07021c030501120609080f0406030204050406060c0b0601030506150d020a1b17090a09090b06130b060405040c0203040512011b0509010c2406090203090f0708060f0601030603 82
    0x515101d081d1781c841c0c0301d004d049031104610300380302d5a150744e43d40c40030300b40c1c400c001d6071519004d0201d5060090b082d4020802071440392030050b661864401031206868603540711f03405000d800c0b0274840200c0e030155511940000c0c2403900003255564400040c014074141c41c522f8454074008a6000e2010449a00400060b0038940303800040c107080d410003092401d0032100083c401c4030f00388130280409c0e0085014084400e0024084a0081d456410050403a5068081510301e20700d0001480700c14103000003128a1140c00756010312841a20502040540c440d511607540601e40d155003020196109200303a070041c010080002c244054100c02d0326010703144010103003900031007180702120403601520458901c048182c41d81c2502660340e84841c0d2101010603101c1e072004560001c40062030a50780320740005031107008401600c80c203120078028a0f040b0304030340320700f540d40c81444140203078000061201e9221440401910290307a4550049001d84080d41c0000c000704101c0641c80019107180b07500c18000052 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 346216915 1250 346215665 346215703
    0x30503070c290c01060e04110f1509090915040b09120406090603020a02010609020a020f01051e010506161b031104050709050609030f0a03050a08010b0a0f0c1a0702 72
    0x40b51050725000d10628a6003034101d400c03211648090000b14040c24182c210000001680b958480040e8038a400c00c403401ca640060000d400e007080d280512640c402c0c0d980c1500d85d040008400c44400740300f80b0402c006144903840420005400000420410302d412074003c000d40b443c0e003014a00b94030364802c1070301c45210b6805030041444034881c1d51015101120350581d5a80e2100d03180c240103400035032002c0c128400319503d4480228090189000078240845940d0080641d229850700c21400c4a030003410f0900445004074190300e05101145a83d410f540d81143c4182e562040c1641100e030013108500020185507a010070b18004928070314100084900a014078a943d82e5890100070490308100c40c10f0000c283cec200c5081c005414008050035255078081d0840b80c5486080d0900c501d032991400f421030002c0c20000d041c0760400d500040403401801c00c8401030742130812481014141149150b0b004081010840b512020f10004042040d50302040807000800707800c00500017525586d1481c3c2c0e8411584d0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 346218165 1250 346216915 346216919
    0xc0f030a3327021f05040609060809070e0c040905150f0906100e0609030312060a0518040213020405120a050d0504030b16030e06100f06031b27030503070c 68
    0x406010350030641100000e01044a50b05040d9880c1c0d0314072081c8141d0b0000d5200000841c001c0800e01810000001034403030540325840c3c110014814152a0410000c2040314424401030710780029890050314a01c1301e078000565100301154400b40030f0382d40154103050800040c0b000032074002007100500c0310107451300034105c0070003c14402204400c1c1d905580003418104100011413040d00607080080d401001c55162192600010b032864100401044640800e4014001c451516038003030001005c0640e0b04564040d00070343c42d400082002400607014070321a800750788048140d581114007400c401003c80c24240301c13480c5030603682d2001840c129080c0c40703a05141044d003801181079901f102ea01070940b103d036543c2c4c0e000040186171007503410824942c454010403080d500c1446581d104e20200e180c0044514584404002083d00c680d00034824145403502034620048180310f0105014000d081c02160003002889454403c001440100008000e03151301000300800480102806406080c1191a50b6 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 346219415 1250 346218165 346218263
    0xa141302032a0d0c0306080c0a0302060a1416050c01090b13090b150703020f0c0d0b0114010e03070807050405010b040e06130e0715031a030c0f030a 65
    0x211054500034800041201e503040d00030181600c6002c50001031404a0401c0090452281920015400c003404a40c54400034008104100608100500222514141300b807458010078214032035140c26404009003207006540010341d0b041181c000c1510442c02041000c0c490810b82d84070034105100c80e00054510100266200c07100050f9480c3c1c3c12000120a4440d103030007103032070061000010310754101c0c01801c000202c2d007142c400500140c42c0241c02030f051030549181c1c62070070b00714043c403400d1080c10303201000070120760f000c074089040d5410050b44d000306900e0400166441c40882c140c82d64544518240802d403620301064641c101c40b4107580a1095907200c00594400d40118018403901400da600010707402e1800c0c64080c0e4140e001c409000510300800000c85003000c0844d0081c10001048240301c06c00d01e03605118503010441c0c1d00412001d15111103000a888221480c00a4800c0151081404003650180710002020341d2202c0c010441d2400344088401c0c43c0c0c0031a9090008034041d400c1c040710b01c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 346220665 1250 346219415 346219417
    0x30a0c0b090a111017010f0e0f07020706080403020a0b01031b080f0c01050a11060403030606120506030a121101050a0f0b2211070501021b060a1e0c0e0a141302 70
    0x20303d5003d0f90156032003010109004c6030f454407800c1d202c20071204003e40c890074440312000ca4041c110390100c20f4680c03428407a09254000c405802c080c001c14070340702040421580440c484081d10031526003a03101c0d807542d007000ca281000da0140640449500000041005101c50254110f902152500180310395148200b44d101c0700c0310303000d42806400802140006611680041c00d42651038109080a40c44080003649042c100f1103044000c80d940e20002d0082d203800900c983d9a085113001d0070b010500d04240480d8030b910b28004014000403824600c400403d0060400b02c2c1100c0c070402c02000a860a502c2402c0608111250040309528003001d1880c1c509142c1d0030500c00007141c841017803480e00d00503030100c01001c0392240451906414000003000810038001044a8450441c0c1c0c00b0241c0d1038051400d0601c82c024121005d01403810700c00c1e4040242d816020040d40990010001c0c03040340f1544143e50a85074070300c00b507500156150303010500c1405804d13641815901a10070030081c4200d40c02d41c3e022 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 346221915 1250 346220665 346220683
    0x20d05040b04140d080705010b040b06070519020411130f06020105040c060c030e0607240e0c09060402040806090a0605070305010b09040c020124140d030f20030a0c0b09 74
    0x1a0a104000a0098608050003c404500003416600701c40f10030352241c9843c0d4004030012509a5107c030104a120b1502e8003510801c81d000b00c0c1c2481c5012907503544c0d181c0d61040c1c2c0c901c41e4520300050328540195900d59020b070702d0001c0c031100e107169114000041c040c07109929025068a020b20440041101441489171920a40e03000d52109142030908905550700030500c2800c80400005152640c9292924009488210310400c07510402c40c45007003204440f9140314000c0b0380030500c1c101c00403000c4500014129148802039074402c40545a0340c003c2006881035822801c040e1261006110602d00000f4442182501800c020800f680780c01c2002c8059034400e12800b40303c480140840103151520344e116001302805030000042e000560f5500b040c42901340c83c800c803202803540e08100041d10508a4040140108581e00d0300c0d00c481a42d0003a148144011414007000911078400300b00400944180130a039801c030046a07140d5080d05802081e00c3d40c80031045580c040d030a00840c8a100c000544441 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 346223021 1106 346221915 346221929
    0x30602040b0a2309100905030f070305240408030a0213152003040e060d1707230607050c0c040518060708010b07061d0616020d0504 58
    0x711100090100380040c0b00c0210f80300c00254000001c68004100072500811142c0341c110044070b41c0003541c1c04c0180c061094449043c0107400000300c600c112840340d003c07110f49281c600400c0c0c01c0b0350b43c41d102d9540381d50f0101000c42d0004410801440d40485401801420250181d020540014050344040440d41c403012520f00c50300d600070441c0700b070301d203001d032500b9441000c012803280e40b441180b28400ca10381c3c407000403415a5803100d0500702d071280c1000100c0840c4641c503001c068554030107030044582c8642c0f141429484048403524120000006000e42115510faa2055495501041e02c0040a014100e01036000780e4847c40f4090041d664104200860004295624036100c0050300d0401444061801009816509001c880085500040208160101c12182070388001d80036480da4031401040c08014038912100c4000000c02d01ca80d08859010110f01003d884501c680e000700c83c = true := by decide +kernel

theorem cover : BRFrame.Cov 346043165 346223021 := by
  have h0 := BRFrame.cov_init 346043165
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346043165 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 346043165 ≤ n) (h2 : n < 346223021) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
