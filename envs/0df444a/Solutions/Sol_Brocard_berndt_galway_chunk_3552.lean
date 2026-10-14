-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3552
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:59:39.568591+00:00
-- url     : https://prove2.me/submissions/40ae3d94-98fc-48d5-ab4c-acaffa098ad0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 638669064 ≤ n < 638848920 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 638670314 1250 638669064 638669131
    0x70f030305061306080327030a121e1d04020f040e061314010308030a0f050403050903060a05280608060408030906100b0a031517010c121112 62
    0x70348800c14844603007014043c40750395103099482400024200946140e50f0701072445002e60188502d600400c1884440c584008040c038043d0a40d10184132600345104400025400b1800140d00040e101c0d4410444005940a1841c41c1ea80d01030900712019018203140300315202c003a40290300f04404440005801700800c001c100c050681c0010713151150070801c00256041c0c45001260500403912a000b1070f4280480c1943e921030304840e141d458141c120340061906040e690701052030b0400b400705140c4c01c80301038a0540001c40480e80143d071142e03d884240c60064034284050f121814401c0349007802281100c021451135440001e1455540420501d01002580d040d15031500020030700c45040030502c10306910944051070008941c0c548195028640b28504007072003015550040307080c28460711704000300109035142e0301280721514041d0080c02041c0e42c1060070045441d1405d1305851700c1c0e0b28040c1c0782c0c4070255071100300d0800864001c0c10f010108001c240c0c506844140b81c01c1b40169240301c1c11241c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 638671564 1250 638670314 638670317
    0x905060f0910050306090307080a0c030504051309050d09081b031c0e0111010b0901050607110d0305031501030501180c09080303011508060319020402090301110d0b030106051008010b030705070f03 86
    0x301c0d030f440d0805060402e81c010f4060f09080d00100419404699200b08640c01007000c0d01d001d4000380c05d2820121010701498015a6000c100e0900502d42001c0d190021080700303020b1826a000030080c00001e03a12038115214070b85040d00300c800300d45688506a2a040611000601904c80b8400e0b203c1101600c03500500000c004603040b01c00076091542c1c003010181d03c003020600204845410341e0300280a128052144611841001074a0b00c1044101e20324880b10403800b030145644a0b49603d8050120381046500c0b0011000d0b0004203051503100c0d028a80c12100c00310aa03103820281d4003841406070550403c00070610190080c00030701090100000d5009084507101c1038002180410000c0ca03510380a41800d1180c0e10504060b002034864203081c3c0500c03641120016558a554008680507103186d0703410780019180841c00e140100104d40100309002c030101d00801c489504c89007041401c861511264001030310142c01813004040715030007140c0001890400d10306003200c03075942118204aa000840 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 638672814 1250 638671564 638671591
    0x2031503010f0c11160e060f0915130627091e060c2a2607050105010603051608100e040f0c06050c030919030804170606190905060f09 59
    0x1403049604c00940190440d00a010389903507031150b01d44281000c803a02034018074040441c045001c42d510400581448a00a000c0c3c0620b49416400141002a51f5800c0f0b40518103039000d00003056900d1080100780c421003110401411076503503400501125101011054075030b544c1c60030011843e0400c2030541150700084092562030585443e20580d40c584410406210320032030101c002a0041d44403280310441180c800c0001c000c0d40c20920305102c4818410072000024030005405040020010054140160000e00480c1da03100c400f00c0440d40c2c222181c0b40030303aa540b804a405213208070134050f0007070b0031100369104035a10388140040d510010740c0c045680400311415a401c000c54880d40c0304c010012418040c0c144809008519103900c10f07440c41901c508089044004a21420000a00603540101a40d81c450b601e60006091429192010360824820000040c5c0c040c5800040003a40c41c02c0200f5915140d8070340103400001e800041c0109510501d540c200d03c1103900c031a10b031648260208036001 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 638674064 1250 638672814 638672831
    0x3030e19030b04060e0105160507170a0f11030f1210030c0b03160e24041206020c060c1c02090402191d030601030b010605030702070906060905090f090703030302031503010f 76
    0x100c0403154112441d4116034140360401071340c0c0c808c0222941d15004141801580c4954074500501095280c00d641140c0c0807000c80e800307124030b03480940000510b98039150078191078040c98003035549010b01030303121080701010000c070744450b145a000150440728201000520b692643d80e506108001034024100045020003000780c1c02c401601403030f2049805041c6003850b4501500404c0032011507240c10340161440c07924060740d00d105c183c102c0d030090184003280c001c461854a07082d400b9500200000044e84240d8020400c0041c590701150890800010f009071142140c0c1424000382d007003441c505910580c00d00542492081d005031030340340d880d4240d0780c00c0d5080b4030040d2215500508000141d0103071f070004006000240c17041510701e041d070780329040c11516560343ea403080f842c14103039410842106042c200300207015500003850a00b540c2e070444881f0065681c654518401c260708480c01d8106505c840010000309001e41e00954014450000b100790b1080300f20042401d40c3c803425008942c155641d0441c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 638675314 1250 638674064 638674073
    0xb072d020102131d040b0c09150307140f031306090f140706050a0210021612080a14073006030c05130203130311031c0f06140a03030e19030b04 63
    0x348005003c5070342684c1d60b0000500d02001304480000e000808011218001c10f000204c03030001c0d9107010721700900e85c048200d2248a001c0b40d0307070020b445460225901100202d0b5001041d010790309420840000281581d42d21500ba192031000c90341d003031b40d2460ba9100d49101151100e079441003094042c8151420400d004200300d4a86a03082d40910204102801305c00700645c0c1c041071942808445000160b15000b0807121100044102c0000a00c0c603c1600d043b40740103500194002d00c01c904e440b40030052034813900c1140c4141c2100325550720001d00c02e25080b00c956000c01004010622181c80c2a550140c014010720007201c0741c54206a49441c1ca2101c00c2101d0300d80001c0480000801c168207504504142c020b420840c0034080d801410f12072443d81e0050a420104165440c25855560340e00b0f00c0e04000e02041d0003040d1900e030700784910382040804501012040401034030314002400000c05a0310b181c46c201d8a10a0040c1256800001d6481800031300244801940265010f0841c10b00302e402d0070300c0d0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 638676564 1250 638675314 638675347
    0x9031902240d0e03090f04020f0406050f04121b06082203111e0c0f0d02090a0f0c0807031b02062701020703170a05191d0f0c120a0b072d020102 63
    0x1b4162069004211055007407a002c4281c81c1200c50a090103038864100212042c0e6900580e0407601c503aa80b1620f070142030100041c1348500c545014400c205202c0d03119801150141030840705a403191444958400c10500c8615003aa1058001d20f00003a620052010142c01e00c0150344504400d42803801d14405010405d106610fa1807400305c03840c3c008000790001046003402c1984000e48030340d01c0440001c0c24180c1540011814050058042091040180000c0c19044c5c095604000007440c1c0458009184941d120200306802690007c20641c0d46a44c8000140c41c212802070a07020081c40d0141c2c10804240050060a8820f444815000c444a0307154040b5010040c0803840c001c2c10a003d105108800f0001b81e030340f000b5400300c04190800080c8408140300c10720411000648202240d0064908020034110005401110b403154074064400c41c0340d6035000100c00143c410000840403e001500500020004804072400ea00c40c000c80c4140c6050504410b030340c0e07a40036035000215207032900c0c40c2d41d0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 638677814 1250 638676564 638676589
    0x30c1a03060901030f021206010905100b0a080411010e030307120f02120d020a050913050703050a0c0813051203040c0e130b0712020c0708010209031902240d0e0309 72
    0x246060304600e070820001e40001810311000e0100f50380f04005400759219900c1500b1342c220248200c880390359441a10750000e0504aa51200c0c4c5980303a400851956404c8080790311290312a0b071005c0305034503544c0754401c050202084c014140b0604031005000e0f034800f07002400606026004402c507141a443c00a410b0032000700514045411540d080c041049012056440810383c0b400d00586400d41e10f00296858411138201d190f00a83c5c80094490803d40f50300301522980c00c030b03501070103d030b210400c03140300352142510b41d10041003100300044c000c0c40e06203074400600c500910071a40c001ea000b0785080b4042d4400d68044d45d00010281c018000500320b0000c0d40d41140c5102c1c00703881016010b0f1603000d004400a02071600b00119840243c00d0462190191881002001e05944660b0340d10003040303000390322020440c0d010340030b18042084d042003100c150941007074010300561002485480800502c01d962010b84c154104140070a44000c12544160402040c25000640d5603124010801911030181d0303 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 638679064 1250 638677814 638677859
    0x51501020601060912030905130906061509030f1502030903030f061518031e0d170105031f09050706030903080603010e07140a0302090c090a170d0c020613030c 70
    0x50004200c51a0f002e0300c440100d80185503003401c14201c506e0103d41c0020564002c40c0d1000c0b110050b8041441154028a0810710500c2c0c104800d81d40c80d241c51038114040740e00040410140d0360208003252003000301d81c03002482120b048141d481c86410708800c0b40c00a45507082141d001100b0441c070140d4200f80160810b804070b641e44200440c01a1414091262101008a501d4039400200080d24104000e0a266031001c031588805819450000d42c3c0e0010010014002000100c074901400b9441c41020305031140070740906030012288601140d4518082000c5050b01d5903112801c0101d01d0600410b0080d007400e6134003140707200142c01e0003030000074040c00030b80c03013a4035010810001c0320b40020100101c0d00d00752544082001c0e6000090840030203540040c1d0030000200801070f00e03100d0f10340100103951040b55880c0f4925104c0074101303094510680c40b8a01030307101000c5404400d000e0080608424401055585880b8000000c0c010000e42e5034001c40e4405000c10050100c01610ba40e9860070b110300 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 638680314 1250 638679064 638679073
    0x4031214030402040b03010905060903270319051509030a09091505010f0e0303030a05061002120d0213031506061e020715030e0f03070c140609040b0a050a0905150102 73
    0x14032209109100141000348110ba8030030f40b070b45a64800b904000180354120302510002d10f0808001500d03a88152241080102c5031840305500220340d04000c040c40b080680100035080c04400b554001ea03600000036505403080b44540d180415030002160300c184020f2014548030541d00d0005400202c082d0040c0ba0142e0410701c1100c0c003840d0080c0c0d10307001c0760005d00c2d280900c80700041080c1d8400e03100c88242d80d01400000100181c025454010f5800b41070143e0f0070340141d0f5403900341261030712042c140c0250000c00400240501c111960060222100042c07000e08845503030b50344808441031001da4a24900b40c65180801c0381c0d40d00b19800758100301c4d904a0307030016140b402c0ca000f516220b0303c0c0910154150010855940c061007035010040b0010f13000c0481e49003400d06a0600c4c3d0700d411100b411110107214440c0416941c21a050f40c5100d00c0c0c0c06041030742409440003c000184c8001803200c1d4102c0b00b0b4010008066031010250300040600180001f454142208141c0f1280035000046055500 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 638681564 1250 638680314 638680337
    0x70c03150b0f310b0901060504050108070525050c010e04111b0a0804060801290322050601140f0d0c12050c0a0f1e0501120c05160602040312 62
    0x8412a0301404104211107101d0502940e90801008400019001510b16003881481c0d01c1c3c6511030303005149810049600d41e40580c0d9811084603984241e01605000421540100c4ca03420302800180c00d001095204507100d1a071074180d40d40510b68861016034280e40004116140355811004071745003c0d001b641c00b40319100c00403e008040b4809c1401c070302700c0d00144504150f01c0e608140f00c01c201320790380034114079900d540c0c420f4002d00e517840a0140c0d4865007401241102c800c0b03441040d602c117444421403410b00315036640b8421400203000d40c403450010722015400c840001d40910041e070103040c0360702d08036030716100c21000d2020f000d1900380c809005a619048500101c0c80340101c03802101e20f0440e01e0b0352900300918215040007031501c201d941040d00f044e0b002c5045404281844240c0782e5142c0440050841214400280d0100b8810300d4042103484001c0341094045e80c01880007180c907806c0951400c0800c1c4a00e0b050b0132000d40042e12801e9005c64103004100035618001009111450032000c8a00c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 638682814 1250 638681564 638681569
    0x4030819060312111207081207020a03300c0504140f240c0a0c030210230a0c14071d01060203031f080a060c021c050910090b070c03150b 60
    0x100d030840308009002c4503015900b1043d90410445e0800036007a0440c0f030300e07482c40d80392104594000e4651060302030422000200c0d0320340b0000b01d0f41c00c0700f81c1599803c512801e50002320107420007030100008034800c001c41e140e51001ca1502031410b40f0901c3c0d41e2095a1180740040c202c0c2440b1030700c1a007503c01c0030240315011281d6550f10342489800c3c00c06454090071803005e0780d011421320607240040c0c214041d0403840c85c20b00c015601c406e42168000d8030b4070741d10800c0030700003280e0703040c0b00300080c11040348040510031031440501e001d051401a58100360138802e4242c1c96141d0402e40e80e801d401e086901218081c05954529035001c06443d8058401e6069175050400c0607450340002814458401581c9074002c44046560704240e00406040b400c0d02d14003022030a10001818008900501600c1072100e2405015224640a490509c0396078825007041c00d0b4200300700310345695000040070004100c8000ca051500040100101c51140c4440d00c0720030325510340704541c008080c1480c2140c0d80340140301c0e001034 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 638684064 1250 638682814 638682833
    0x806030705061e071b030c0e1314010f0204080c1008010830030f0a11090109140f27150f063402030c1509060307030e06040308190603 59
    0x840e05604251003980d07041142c070f00d14010312001034039040c41901c522508859519034001600d00500210322044d481d00175407240c20b50309135100c01d40038550354001004600300300c00d81c06488174500700110b28a28030102030400e0360010b0300034266580080d040104070385070038140a8a00b01c26070414484540c9024407013511740d124240c0e0010100b900200d86044180d501e1000d031300042010f10087c1c1ca0b801d02c03001c025444101203d16603ca1032400c10b0248490620005480c0c0100c4141c2d03030005802d09000014a10120394030200d6000034410080c8900e580c2d910f0014460320406006104803020503201e00604424003400380300b00d200140d161410940c444031142c01d8100341c00e0341da0584e6801c1810702e00f185d030500c9003a8a00ea601c807048a500144551810103c032181c001c804a800520100c8100140d40208291540030030004125a003043d0405070003643d80400e003400c0024021001c0301840e81000d5007160114001100d040411510308545d81411840c2d030940c8404100486c207554420700c12 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 638685314 1250 638684064 638684077
    0x170a06050a081b0d0c050a03060b03010b030a11041a040207050f120403050c090402030a12030209040f0519110d0c03020714010c0c0204023105030f03071707020406051206010303080603070506 84
    0x18650f9881808144445c00c0c0082d001014080c0011840a9403814018020703c1801e017000c0c13082d420000d0301d04643c47c0000c0c030042055000050300016004000c20080140141c2401c036000c0340892480c2001980d4910291282c180280040c0103110100000281001d80d80c40d40c2c2c01842c20b041c0014400f01d0300004411401541c1512540416115800044c1c94040c0640c0c000701400000d4880d280303d1581341d0007620303e41c00d040e50f05000607000c040301d242c02d89008507030400d5002c081e420540700e80d54680d0452600c07003a41c182203030b103021251440b00003500c01c04070a020101e45c00258003000c0203400711000c990b104008000b049140c648400c001c000b140c08103c040c1c8119000b107003881c079543c07155400d0000c0b8501000000d0000010380302c1040707264694070504c1d119004600000d598000c01004582c00b10780d00182c0a0510403036a00002c140d030300301c10400c1e60401c2e138801000c40d95455000050440f419014000d0929600d10300d002402250003c191764001e40144c0410422074807046c007503840 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 638686564 1250 638685314 638685319
    0xa021513050d170a021e011a061608160b010e07020a0f050c180f0a0c0918020f0d0203181c030207022806090e0613050601170a06050a081b 61
    0x28a0b5034030f0502c2491031203850201111804006107212441d5000180030b002d50551038084c8104400107007916003211101280c5018a2366081369903202854120020700600d0002c01c00d9240e203613080d46071002d903070b000114024854200803c1400170b10441038000b40c01070080405441182c0340143c4000d4545400780c40c002c0c1082c90001e40e030010064248401d1601c5c00000d410400901e01e20080ac406110045d9056002c0c4980e02020601c008503078000c010710200c59444207403041389007443c0741459044601c4418010350b424030809220030364803801040c000451507070245e22070900c240c101111013034031300d0050082d82c04506410710300a60703a00350604440082c24011b07200c04090011404c040f00d0136102001204d90301b0203074010230072284020010b4030525524003880b01d880b8881488100c40c2900c00943c02051003400c01c0310503640707810042e440031040c5080c4080c120007810b070038402c2c2c0080d10000311540d03d80304c1c184141e09062000784028000c920003007907030b00303042540c084110150303240190 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 638687814 1250 638686564 638686579
    0x100213030818060c03180d030c1b0f0f051908060601031505090c121003050309060a030b0306040804150e2b080304050a0201030c0c0309150309140a02151305 69
    0x162102d282d19440c02080c0030290110b60745014801d5a140c0f2940400100030300151640300b60505824103c03207400e541541a01c64102c80076864440008001d10f07100340780c480b003c49100201d4440b0141c940d08000b01ba440030980702d0607080c00b04005400c503082402152940081c2410481c01074002500c40d001f4000f8240060702011084044904160310b40020b500101640107105081c0c0c600e900070028816880e030250b11070703140c82c8103180f5400030360310002d006680140015006031030440001c04d4117504e01d00b000580e4148600110f03043c0a82100c1c00d843d174940210301002103140300003034050b0100e070310716241212020f0342d40040d40303000c5101142030201400000709070f40e544000c00554003060304071007030300d840340740038500b081da2145007000490000e402c01002040f04d078003540707141e0255540764454400c03c90030b0242d6250f070440ea000040e0300f05070f00c4014210101d4800403070710880c4180e20b8050f052180740b038018054010034400c1da080c1c00080030023400017103001c000070f0070090710000c0310045c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 638689064 1250 638687814 638687827
    0x8040b1612021b240f040b070507050a08030c030703030b131814121c200915041401081f09061e03080409050403140c0105071101111b0709050403111002130308 70
    0x602c6031b400f46030407040201600081c0c80c0103200000a40388102c52007200c604501b583c0714002180c17240111a00d0600c13542c81403002900127400b03500030b00301c50040603100015810300c0003512416260420413103c503044100b032000c81401003100050602c442c456005110900f500e03c490940c2d40b18014050402041106e4601e0904985400c4400c40c3d40343d094030703001c8070880e500015200303510017500d1910403550340320503690000341c0c1d0f800d407011034280610746440b01400c0310066941d840f004000709000e071544480b000c0c01a03020110540500b2031094006421420309008101c140e009078132040ba0201140410030000d03102c5000c03201910109900890140c075a480d047d100c1301e028000d01c80443c4000305075042ea01038154407462040c215070307841c02ca0345905403104a00720307414a900700344040c00400c0411402807440b105d02c1c0120200c10115515566901d1082049031800e0390210700040103601c80d805405030401446803c00d030700d034008510740020741e4040c5405200d00d11004003c420f010806 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 638690314 1250 638689064 638689087
    0xb0306070c080306060d0c0f02010605150a0305040c0302030105091b09010e1612020403150b0d030504051e060d200906040e060d0f0b07021908040b1612021b24 70
    0x6a45c20b1030801031040c004491f0b00c0f88081c2070040340355641c000640ca04a000143c0e441c040d250103c01c00306508019140c00300500041340a000001c00a40300403850090000058a09215140c8203c3c444000b0b0207032680021001e4610514801718075100c0d0000a0042c0200d1081c1e00c3c1a80d00722a44192000707058148504c03d648500074410740320140340c4041707000014800b40c1c6030413554040b40706004024002c40c0104118520512080190016909100510050420309010041c019190207881038032500800040e007594810103a90300800c1c0c41d200c07681074002445558544550300130a0035400c001c040d0300482c0aa01503445001080d90302070002c0307802900d451001c2944544c110300362000200c5c1074104840752240507242e6400502c50051034128260134480c0c40110950300a604900d0300f4900b03a2803140300d402c11200c4424040002d4424000655500c04a0004118035006000d0b04000b42650603562085500d4650080101d05a0810701010030030340c801500100c42c541c15180c420002c2c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 638691564 1250 638690314 638690317
    0x1032a0e090d03140708190207020a0b0d06080d0509042c06151002030d0e01061e05100507030c022e08160c08070f02131b030b0306070c08030606 64
    0xc0820010410000d000c1c0307200c008200c0100701c15050f2802c0c000040c0205900102040132294080040c82060215a2144084188852041103070b80050700740195500040c1c411203180e40190940c1342c0002da5040e0008050003084000c00600001c0e011440c298030001d8224464980007a2285580d6415655020340983d4414964000c000040c03102454a0341c07801e540301c00540f80500159416813003091149424101041c031000254091410262580300040c0507041c5801040f4a82d500c070708000c14803011100c0003181d40f1002d003021584240c680000e10046102c021042c0c400c0160030007040f000319802055400c0d0865040d03c1918a462041008200d66581da0542c441d41c07a066951940c512544090007a020704c02c0c8603550503c1e100c26040544140c444850001d0802205000384004030300340c0310030341d219203001a0407819280d03481c65a110489911000382c01f00300d40346030008111141d162003540806201034006010078100600d01410a03c049030000341722420020024645895900 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 638692814 1250 638691564 638691569
    0x6040b0f19020a0f031a1003110903060403021506030c0603011511060a0b04060b07020d080307090b0d050106020d0e031902060d0507170f0f060d022701091401032a 72
    0x60045442c0c0780c00f603000518560313403124071a000a041045e20710b80180104032040003d980205003c002c68141c08081d805003a4144580e45015000c8c07002407070544044c00b04030310075071003076002e4079100c2c65010190401175800341070306010350301003000d03001c26448010499055038104482c1107011010170400b282c5405004107070316003500400c0b0511000040c43e400044c0494012102804010b4442c04819058020403002951080e00140c202c0040340b0060000e58010040e0301e010180c903521403002c6c95042d4001083c1d010196070300d4004001442c1e050140c81c00d90300711441c00031030040076a00000e0742d40449609600e44404004060720465031a07000b21440301c200d004007400240792290f00030313100740031018841b00500d19500009040e03100c0b00c8502441050070002c0c0801940341c0900303000b44507031560030490f001420b50011398520400b11400313508641c0e02c0c9030051215814500b0312015a48079195054098090f140180000f401880c1214207a600740c0c1d03200180082c68000b00840080c156 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 638694064 1250 638692814 638692861
    0x807020d151a0603220c21140105040302120d150305030a11060403020d030902220510060507080315010306031502030a1425111e0c010206040b0f 64
    0x14030300d440200301d0380c001e085211a0301d401201c0c03191112007404103e200840c0d0b443c03c49030504401c0794140502951104c0390f140542c1c07107a54501d44070065001ca48001c98170b1105002421440b260070003a10b40811942000720000901c01824140c3e80a0764800d0140c88070703000d10101081200308585540d00034500031001140d0b01c1885075072401c16a4407640b003440208002940c48443e01c2e4a400005812070160303034540e001301500e5664040440007495010412039021a001c1d11035484011408005410311a9000b0f0000726030501e0606640000c01079400181400410701240020031030b03100581e9405031000000040500283e00120002c00380ca4000400c1142c00840b010328102c0240c0c0514490142010204510700d40c810007140501c8045880d420b80007490100341040700002c80c0740300110560340c100f40082d0041e03807070601c0c14000707050340b80c5251907003010007020020810064240640b03420b001400341800c10f0303101e42c211940014556526030b103c40011070303402c041680da404411001d8 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 638695314 1250 638694064 638694083
    0xf02030d090c0905010f0f1203023a0e130e0106030210171311100309060c0e130606050909040f02040614040b0907021b060c0a120f080708040807020d 66
    0x50b441d080c1c0c4038040c1c0303000349030500f403a0200106d0155651001c11059074190340000003c0d41c0707003086094810a54410850840c01010391504680c40b603100c20805032106c0c021204071012255100c10b2807a0340180203071003000360000c0580c1d50754840c030b80441590b40c1865404144040041c503114050949031384000d4010011210b0715048941c0400107910312101d000c0c0b02092a210502d02d16a030003c00040600b500e42156007100c1d140c5041071003810144064200402d480e04686c65050444503607808a501042c19440319800314508100100780c000302c20b160406c00d8600f0004020f2140c01030600c444d01414039075003c5803d02002c550520041c80c5d00600c1801101e403030b00c083c1c20714003e41411043c0601d00f040450040c40c40c0001d00640f2a58251b80281401001d0180c1201c00200c080311300c1c0d03000001002207104071102481403c240500441c4003404055500400034000e1136039000c0c01d0304009505040c401c2041e4084e9045410a4010381d1007900d60900b4000140803010450700180140c41 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 638696564 1250 638695314 638695331
    0x60608131a040501060f0b0c03090904062d0608030309070905040c080706030f0e1504060513020604090e06160207121a0f040606050a2907080408060405061e06010f02030d 75
    0x5401180680350900b110780406d540d01c41001c0e48078001c03e51156615002404110344030305000c0240380c1d0081c01803c0100b0302d07410340450148001510390b9451201c0e03004202200036021140180c00007803461308000c0d8690f10b85528020348502040c06019070031a1110003050600000080780c90180c1b51020031742ea070041d5508000b40080a98460101400d418041040c04d403200105280665454150f5004526036840e40d8180042c00300600ca0b650001240c070100f009615102d002d04041c102207140041e464810a5256103031590007401008110140c0e1880c081d4a85e0120b0f0b0002118442900f4041480e0750b0702c0d00303922141020f84611100e83e40702080100c0354000a0021b4042d500851003003008988460511404038003501603540b288081c007149156085940d6921141901247d00243c00c01c502a80d506c2165485507001214a0384044280000d110341405100d4000340081d821400a0300001e07140c1d81d001400403c0141030045805002c500036009104590700c0c48500c50b4100075010 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 638697814 1250 638696564 638696573
    0x7080705121801020d0519080a0e010e060406150b0d020304080d020d051501020d0504050909211b060411190812040e0f27070510050c0c04060608131a04 67
    0xb5081d5082c01e005100315012401024080c508541440d1084d4060740c40800e004034040d1402d000c054040c04c401da5464109282c031a03020300c20503030000804400341186061504008084e01c054001024801d5400301c003c00c200e04040007113494266a9250150b00c950b80c0e42440021400f0b4000307010300590000076903034601800c6034801440340f0300c80d40041800817a400012aa6441d0344030350711003c140d0410050000c2e16151019503070101101c01129401a0043d403002e20f40540008100c3c03180402268899121001540d8007103a422400300624180c07900d0345980c1c1401074000311f650300944030308941020301c0340901507140c080c107416401c8400d1100407420326101ca0384140b0a901e5407000c0070000c9140d44122142180c01144124600041402c0b0010380031402d2002c1d56001d0000e201c3c2c100e0004054a07214491100d82c80c09032640760312440d444083d14240301c0d1076010140704074645403003440b00b16000700e40142c00842407444450041407038908134019003655030700c45403240340805c00c00c800c00 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 638699064 1250 638697814 638697847
    0xd0f0c0f060929060901260334030801060807120c021e06060901030b060d060e0c0a06052a0f0715021504030c03081b37050708070512 59
    0x10204640340c003c541c0701c44220402e0b00300054030b410703501034901001007160140351500c0d070003007845180c20001800502495203240d40d008030100000840c030101d208070b0400d0201416504054150807000c99081c0707a9a00518500050040710300340700c910f01c00b18612902c030f0007051001443e094003c020030f03108000044e40d103040070040c42c240180304072031402c101000480c005002e5200a40f2a60722642140d42c0d02425000003407130316030814071600181020990900034440c0795848000580f070341810400c1030080b0300b420742d0803200c140a420081702e400d88c6844c0e602032409000906610494220300701f8514208030310aa080d49a500c101140841c4a200700090400c1413600e42e0200c904a1001003a0111610011200640400d03813400044001c00c3c003800105d0391043d060610481c0d0941e103251502c505130442c1440d14841490041000043d282c1c800d44411541030b071030520380da0640e101b40d00600304e12620708020000c0d0000300700d041c2080410400070b40b441c00046401ea071030320760035460704c681c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 638700314 1250 638699064 638699093
    0x1209060a020f0d0515030303070905011803050c040c05040b040306060f08120301030b0a06050d050a1406091e100618050a0506062703030307050a02010506030d0f0c0f0609 75
    0x90044101203221009144200c68001c001850880c0c140100d0543c144010b0030020032a005a40c0b15003a00c1000396014030045210f16850f4413160043c0307003010001010024010003070146406030840905c0420b0703002401801c402c10846000c0764102640608984500030b544c00751402c040b0104c0d010080000c540c008000341c403a90080301c15400d9072400307030b15901c805440e84403600540400061010420003141c0300d41c010001340001c2405503032140030071402c0304084003c5c0c500f07400c50a0880d0400040c9a07814812020070b070010301d21800d01084103612040d1401c109058954024104245030206011041c011040c01c48100701960782c507050611484c18211030082e04503d40360020307071707000c550384102e50041d82c02503d024245114050307121841c0038801030b8000c1440100c08109036556080000310300c00d440c2036841c1c40c3c035048138690282c01c0d00d00141c8001c0c420340100e000c07903070040e40c444140c4003070a02c5898500380312040350801e403d116030414806000b02e8145000d401c00d101c010b00c50b0104 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 638701564 1250 638700314 638700331
    0x20c03010522030f0306180b011b1112072d0602030703080c030c07050a12090f051503040804090204140f010e130b03030d02030a0c080c040305070306020a1412 70
    0x1c15070340e0074814802000012044400444100d0014000c41d02c5490301d03007440681d034200024000c1d1280321032035a091404105e5940241c0300c0040c004d2550780310000c5211624884c4074101040c05036541d804984081c04891402106059106c10102c1410040c1c2c4d002800013152402c2c900e1240c124a0132040c0781c090003605503a070700042c0007444500c00400c94984c290940e032118219200c9000e4000e003940041c1c143c003801001400a000490010310603a03030a1032041c0c80c600000b14140c0805800d49071a540401d030780d4060008100516202c092500c2040d0b0900d0b44013954a94a618003420680140e8101121007031001c6800f0520310450241004104411a004804075060400442d81100b11201c01600414101556142e8001d0354000c280c2d40700f801001d030b0f0f0800c46082090412604121035501c265900e81180344880d58201300103640200b141041d6601d090306686500f84c3e541e1451200600e016800940c0e003542a02c0760000ca1100ba04181800f035981040100f1995003e805075403404 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 638702814 1250 638701564 638701571
    0x618150201290108010608090d030b0103020d020a0f110109020d02040e03160c05090c190e13110909090c030d0503040c0314030d06050a121b0b12040c1e0306050403140307020c0301 79
    0x401c02e007c0d800e0305102d0a007880c0288510350541c80b013100504400e00c0d4840c1816020310894000307240c6800540030f510015a2400f01c0300d490000001d1035032240d070800200c1c6034988124107000da1503203044509030a40640d4042600c001e1136103d1884c41c40340034000f452642d1403c800404002c400840a401c883d81100c080c9090386038189128800d2140500d14a102c1d1301c1202e200b42800d0051194064070390000744013803050394000c8418404e5480031084851207000010781184289095201c8076000014180200480c10603c0c01082d0b0351000c000300301042c04404070014003001111109100690746c80246c4140d0511000201c9590b0b8100d00ca59003c007900309500801d403420030344034040854802401d8140d91102d1900d4902d00b04d4040304241600011440020600820100003404240b020b05a012040e28050819451030710642d0000021466200503542e003485074034407224103994005000103560345451030103841400301c1451941c0e1880002c01089100d0b5004a200065404194001e0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 638704064 1250 638702814 638702819
    0x5061912050106080414070906080703051c20011b1106090f0304150e040905070806100b030423060901060812030f0c0c0a08040f0f061815020129010801 67
    0x200964909014460024500c4c400041c089110701d1000e040400c075607001c0d1418a51200e10788401d8803038039042110a90320003a010803c00008011507a501d80c4440d4040c03d07440a040030060200e60006001c00498401440e00c500043d400e62140d40f030f148402d96410100c1003480380281c600c0c0d14404948041703000f03500008481c12000710f9030100c0c0c0101c074009036140908141c20187e4541025103000301300402d01d0242c10030380c2c13164071070380c035650b0700030401860039a203800300340e070316000c401000200041c4103403001b000104103030410750790080c0e808180d03921040e1080c2c4010b40d48000c40c2d82503e54a105000078040507110661002042c0c030100d1003501d24200e04c0401d042103038030040e103241300040c166400154440918078080e00d429030700442900c1d41500581ca43c4000741e0002e801ca07000c244400070b0304006c0c0c0504947d040f03000300254240540707a0282804204031a4881c1c0c420700e41c0d10081e18030412031041c800e42c41f521041c20410020103d6810341d1017a0308841070f450390760501107810341001 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 638705314 1250 638704064 638704097
    0x305060a171f0b091f0504050f04170a08010b07060b030102071b09060506091e090405030a0e010e060d0506150c0a110f060d090f020901150e01110a06090c050619 71
    0x41840e805000380401c030b4142ca03031001c0d007184024454580c40b0317000390084000c1180c2d41d860141a02501d140f1522544070304017400d116129a40d14038804401c100e00300700000a0300d8000c0425811561050b00e041c0d00ea0304039050000191010081860745944005810003c10100c1000300c2c143d070385000034000c4e046490706500000c9801501900390301203020f20626200b850805505c442200350803500e0040b041207980420a84002039408603225040810448035a903032015442e4550802403a103c0d03902d25582c0046442403040c40314883d42691136200180702601d0380030885803160480030a1658854030803481944503200f00008840521124000c6013640c64225810150844001c01c0140703404240c13000103008108140c070072511062a66220000b40c1d4404031254024036641c001e4078600b6034030610003800030f00d12501090500261040b071501e050320014072001032a900420010362141c081c20000b030ac0b45040e0b841203920035800100d40d01103812200b882140e504540c0ca44d1501d148001c8807 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 638706564 1250 638705314 638705321
    0x60602010b030a06020c07080304032f13020d0e071203110102250f080d0203040b0603060c1b07180209090708040f03050918040507050a0b040b0a0305060a171f 70
    0x4826515a2165100d031000c91500c1d4001c1c019800c01b2811680f0040e540c1c4c04103421600a039005640c054505099075a02525020004a25100c600e0f4400d0a40c0701940004201c025103203092124103901041045001442d94000700f102c40e60039084503030003075a4008254000003c110220001034008000514160050003510b080341003410964141c510030014514205100b00415200d0b941b4140444001c01c4480303008200c400d85a40b40541c2c2d9181c142828031494001409081c065071014040040280400003512000d0b4001800356507042d00c401d404628010454200b8086040711010031728030310100c3d80c01010f80d91000e4548000c1580c03689425500108122000750810f1618903180c00000d1103880200400d500c0140808043c4401507200070500c07200319421201540601800c1c4000c1c9403d120010080a003425218901403e050152403207004a4100405042c1c0b10303004118147c0e00d00c21040d0240c840a101110040701c02c6d13816556500a0030248440480300805181400c00c2500 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 638707814 1250 638706564 638706581
    0xd0530180f070b16081210030c050f031b03011113080d050f121b1611060c070509060102070b0f1306050a050304032f011a0105070b07081f0b0d06060201 67
    0x100f4007400c2101801c0382c0007841d50070020803070300c01204100c0c00c2d444030110040c0601600000100000803070462401e185801e0481d0004c2d84181c1510450070700a41c0c1c00a071084403030240010720b048982000000c02c0c0541440f00c91441a0321000c201d20340e107001d0300503048007124035800032078841c002c49840c1a1040c1c80769001c21545008200710801269000d2201d071078100784080c0c4400100b4500f4450340709260803102c0c3c695800c0854070891070902000800f541c41e42c2c4002c585503480c10707249107100c0360396600718031545020303a80040c00610640c0c004d01c0184010801040030361f80e02c0420f1012984940c2c4003e484846860110502082c2107100d0016a5200306060312000e19546450f14251203403016010f2004500200d5004226020000c503407810300e00c40400d0002c20014842c01d0444001c400080046040140500190010034403800031030b40c224100382040091a114910788442007825020044094180b0080c0040c1a0315031f88020284805001c1c8100031050b1038102c100d081e40c040b06c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 638709064 1250 638707814 638707829
    0x40f02092205011a0d2004080c0f030105010f0302040b060c0f03040306061208040306240807090f0510030312090c06110f16090b0105070209010e10080d0530180f07 72
    0x10b014101001d00e00d03510034040d1105004030446506c0301055400701546c859040141d103504074512100f01421b000042032910882100280b282c0d40c182000300c0c001000d6403201910458071245803141c1a00c90b40304070f0301030b003015030705072104440c0c802119030750781d80144001c46071103140603c0020342c03240e1040101030b0700c0e500c9000e40d8a81031943d140d2101902000f030310604620402003100b90002440e0f40036000408007440540710340d81c9800035400c212604a0b920206d010f0510080144034500c4606410580340d05040108a41504c02440402402a07450003030035440604008150107401818080072400c8031001c4603904903000304240d88885103040040c40780050700000f07220b0300b510354001c2d410700b80b03042c903004d403c00103960000784440c0da083e80a0b0645800742010b012a1154143c0f0003c0601003020041c04000f161107001412481000590740f8480c3d9003412104007c2059001c041c0004801c84101802e420030000315110035a190901d01018880c8441350034400a020a8220403100d02 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 638710314 1250 638709064 638709067
    0x80612031c0905011407031a0301060f090c020327040614030a03030b03150a05010f05180103020112020c100b1f1b051e070305160b09040f02092205011a 67
    0x401e0500c090b00030084120b03450354070740c1d9042e014100c1106542c3d100300000d90303001c04d00c822007400c40000740840304102ca000e41d040407824000312019402420494407020300018080350440c0e0100e00f54082c0007403680b040070301c140307404500d0307100c0d1030304603407144400ca0301040002e5540d40112069060b500020b505500041d44201c046230190340505c485400c09401e031038807014410001e518800c4201c03510700b03c0c151744034014440342c480020018041c040542e0344d00e802c0718410304100310042c0140700081c10448420b83c0d160002c40c841d0152040f0001034400c4401009031144038101500b44090000d0007030340c0300c060050410054035003540300980140c440c180c21500c14a00300022100341542500c240c81101103001d49800c0500070000c00d03821000203000307940d0541c40c1450410307030110042c400f00903080c0301c140111f02e101c4080710b43d4070b0b40c11100011a080c520600c54064010000d0055001342ea03210507a54071900c90303d001525000d403490401041ea21fa290340e40041e49601c19600d1070000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 638711564 1250 638710314 638710357
    0x40203062d0315040b1302060f0f090d050102030f061e0d050102090a150212030f0f040c0503030d02040e0609090304050621010308040501110c1e010c1208061203 71
    0x7224101c00c045034801e500c500c444070304110082403404a103191005201c0075203804000601140b00350b281d80180d04850280c0c10150150006a01405103020340310304d510000891060551b1b016040310b50540000d400c208040031107003005030007500111003a26011610500046061906030003202d43c0c207003821140f0524500f060140700c3c80e10107080c070840c0d03259400c000010490b501d1645200017414014042446403002c800001d041c08003907084410002c1080c810b110001190501c3e49a0246c60501007407003564450a150040303195031751005815000c0010703107201c2c10b40f05030002d0003a65056900d941c96620340009120340c8000485035040913400a20050049252290080100045030440040908070500007584070703000c20b90044032540c0380003c0c20001541c03c500e07a1007415411078080d1a400c00300c2000f241c0c5007101c8a000c0c05d00c8001380048211241c0c0500304461485401246540840c02c0380c40c0040c04820b01034400c00e120365440e19016005000000c107c6c3e80d09203031130000506000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 638712814 1250 638711564 638711599
    0x2202090a0b040306020a0219020102072d0806160905060d150e01060c02150c072d09020306031e03090f18070c060b0d0506270d020c040b04020306 64
    0x41010110603400000e60100040414401001d030001e18010340380141d540d55180c9003c0c0c0707090105600040703044030303d050b1000544e0b00412000100c4032100355098080420100c000807000103030707504d6504c08820310070218180d100003030458441c440c0000b51601441340b04d80d0550700307200385106050b070119041112090480d09500210706607070014189458203030715801100c9085800340c110100146450b00c004055140400c40410f0402d104800e0384c3c9041c00203540b1544485243c0a0030301401e228104039484421002540181e42090084400596440d200450302035031054640d248241708401c1d001d030328413501c014075402c1c041c0740100441c645500401440917000304088a01c0d4420100d02000951180c150f58075032003014182ea4082180310301d494003904a894100585000322100b0101c3e0780042c1000855a80011030b40c0328828500380c00d850741c00c072074801c0c0c861042007a000d541c0404094503000624015210402c850070b000d8403d060080c041240170840e400c56119260740c00320001e00 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 638714064 1250 638712814 638712817
    0x7051e030705030d0e040b09090303040f1509210203210a0f090305031e060d02060d0e0f0f100b060d0b0a05280906031703090a1506080c2202 62
    0xa14015081c0d031240c90740c4030b00080c20020f00150990104480088000191405102e0341c141e80004079495443c1d03080181c0c0c03496803404001d00041900c0c0c2c0103d04c0c00c0034411000c14042d213000400d403083c040e2894a2401d2001949802404050f90b02c0c080c4669103028004001e0341c1d0040d180d60310b06400300206031810784006030003a1881c04542e5a500d0f03850071b000c5060003210712180c0241c82c0e05969040c040400514890b10051041d01908400207002c0c0c1666500e0b502c0845980481c1d1383e5480b80850301d4204002c001d000c1001f10315100d91000a181c40c08080740d6000756003400c070140ca050316039481240c0c0540301035510156100c681004000c1c00d002d0240d003d00403009024288009807511440455901e4903414281c104a500001c0f1000074210b00074039000c080c2c001118180002d5245589030040e0260445501c82d140e6000b10000d12116020001e1082d6a03420915020200c6810310314040104018091112240207204a588003402e00d941c40040380000c2a100003109403010580000a = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 638715314 1250 638714064 638714119
    0x20312100801020f0301080d020d081303110304080c030f010501051f02010e011119050c0703030c2108070e030a0b1b1c0f1401030c0b030604020403060516030e0705 72
    0x510589034000c241450240301905503000d01440c00d56903075040681241c0b03001c034040c8610085501c240241060240c0c03080e80306800c2200da02d480c40c5600400e2409490b846001110051244400714000502400015440d444100700b80e090380c0711034140d0131032242668001d000d46034104040740c4103485502c0240002ca21103180703a100004080d8407d03c60305003941c2100c2840312441c20b0104411440e14004100300c009402d0a0510a11b400800d800e01c41e12604548009070030320046841403820f0010002a6008442080780600c0022820380da0242c88400159640c1000516101c0030503600e040006d0010165a04980c282d00e203a41c0b07842a0150b0701070031142e050380c103150038082250381e0704980c9044015501d248074082400400c61a00c001107510140000e07010650b540010000304942a04030b0040e0340a4444042d07880c0d079641c021802034030503580002c20a606e448104070042d03006c40780c401400c441c250b50500a28000c120415a10780341e0780100d40c0d018160180100044c5812240d1200 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 638716564 1250 638715314 638715331
    0xc0e01112e05090c01080c04030506061e1302040311151b071a04181b05070512030f0411101b021507050708060a051308030910020412140c01020312 65
    0x1d50160441d040050b68810b584003103603039108004075812581c01c05859031744039190800d41030402e440e41d1505903441c81c002d40110b000d140b280c0364080c200d03010650030044240000d801c600c64101c00300d6000300290701c9444146c500c00b0399210b900407145050490007114404d000780450420052801d00561110000603055081c400c00200145210b0300300f000015070014080304070b8403540b406401d131040900301070512100518201e00050104101403a512040a692805c6515602c182ca8410700c0c080c81e40d088441061804410401c02e8000e840340c05200f44e00c40c18505a50415020900501d0080702129001040c1402e046500d08429400144804ea000034810818811026078881e40343c5e011400c1600d40303401807642130140714010006a900900089420466450044c0703960401c1c1e150060018203420300007001c00c40ca04010480344e14000900c00c8119940c3d40c1e201ca104101050f91001100c281090380c0d0100011840803c0201c80000c1c103030047c51408005410140d10030038004c10452 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 638717814 1250 638716564 638716633
    0xa05090a02180a0f05040f0b030715030e0717010c030902011d03030d14040302070f0f060804080d110c07050a030209010e061c1b15121805030705010c0e0111 69
    0x2a19690f45070b102d40040c2400300e4074038825403c0405000a96640790398190500f0f040c200544041e840006c0c000b42103607403030080e8003811856a1400c902812070903041881c0341c444e04502043c0004150325200c10011030070000c10590402c3e601c25001c5c0c0340c011034040d010907440c0304082420749218029142102004050303e10b0226591402e000321201c00e07401c0151110b600e030070401055010418900540300742c86110412901c0c2000e01c514079200390140004009151011030300f003003a40c5c81a1241490f261030306100e0422200095161600300ca00040f102d0310418034000303240d08240c04620280c1c0d0b00540031b2042603080c0203071842030001c05409075410282c00043c0e845100522000340e81c0841c820b03843c180d4004403411a0503944045a008040b180c0a00c3c4a8171109030f4020314500c501c4e001510010840c2c3c0205881502c5040c030342c901c0038007070b4000010311004000040d8443c61f510764081d1500e00ca404140b0004407240e4001200c000d00302e500c007070100c041122200c2c1c01188110300300d81c1d1301e9 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 638719064 1250 638717814 638717857
    0x9050303070602070c050604140f0d06240b04061e09031b05030115140f030115091e02070f03051818070e0102060903040618051002070e060a05090a02 66
    0x29145501c111000d072240380e4041400800c100074080100014041100d03620305040c280200b001d507010403039130100e01c201c0096070203c200da101e414540ea080760300140100043d01d09520b1407201d102800d281c500c00b11807030b03240104950300703000291001c3d01c400c0c2d030b103080714402012400d1501c0c2600481d55018051410000000200c840800603071480d00001c00e40c0010b81751406050030b450143c1980400810100014414030000014a070369402c2d089800b21120301c482004203004110819a401c6540700c0b50001003803a408903009101c0308070006006c07602101c020b090786401ca01030f01c00010041112080c0504c08030b84a1405000c0302c8c5214406d4003a41c0003840000784409518642043c40018001c0070401c45c1c03500904a403514000a0000e4030880c5014100141c40388034a0140500b485880c03013609080c1c0502d2103a0314050000a0801000405280d0010355120ba20b0700c14955580b250b10002540d0381450403560007119030140400b0075a403640b40502c0c2c00794014004102d144490700100c03 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 638720314 1250 638719064 638719069
    0xd091a0712090915030b280c0509130905030a110106050603011401020105070315052412180c03120c010f060f1a040503060f040503121e180c0108070905 67
    0x1990a1460a0b212900d405141011110035a0f00c000e00700f901100c0d5841e020400b14904442d029840326900207102c0d92410180c20800e04034540c0d854000816140034526082e19030444000d100903030040b15140f0a0381c8204210320240d4681d060010100d030400d03c1300001850113441d8041d00c0301c4441d000032482c80e41300c030040b540030f4000340d02124410b80d160540710340750b50702032007500d420684918040c44903041c1441c01d000c901056128a9000d44810f20003031100308003e0402c3c441e1200f580c1d00321550b60740c00c50403609207180141c54242c0c0000c2e10051030402c007600028941d03044a4090040c1c10800c040a000c451325420204007174015540314200c45002442c2803160801424030703d0000f0505a013001c054465418101c2300c0b07807050301c501300000c0c40241e80001d42240d0086200048600b6643c8034a007280c158017401400101c1c10080382c2c20b010760800d07814011116880c05846040b02940c90007a84e10501d07026401d100900d030815038421100d54816005c1c1c982c448a54101070380c6aa40c0e4034003 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 638721564 1250 638720314 638720333
    0x109030609050c0901140d12180308070c061112070f02030607020f1213150314040807032c040515030703060f061d070c030e04020301120209090d091a07 67
    0x500302e0791500000e245501500d402541300380584010b440854403010b00e80013040c0080d00c0000080c0403140c000c03180900c4280300e01c00e1042202a82013400d541e91b9034030f00d40084180c2004004641011004d40041111407049000303454945941005000e00010b80723010702c1715507002e1402520400c80e01c1c1d12110260b01c0410525009007001e40c01030a010924a10712030070034440440b415180542040441e43c1000f900c50034506844103c000950300d0003070f04e18190000c0604040340ca02c0c1948030800c00c820b2003d0b8001a1400760300903160b02c0007882a03001e24804443c41c2c82400c21440c080000c0b0a08107003899403080d90310030352001d0008284c9045000091420030194000c650054680c44a05a04000f90095600130810000d581221524602e0012000c040040c261000c100ca0411702c5418148900944052450060001c640d0b958480034080700c13540b208041680603a030884086180514001052009484980e0703e583c02d040c10303e4010360344080e14850410340d0f9001800568042f600801 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 638722814 1250 638721564 638721581
    0x61a03060a1e050c210705120a0f0c0c030206060d0b040b100503010f0b15030f1605040302040204121a04020619200607090b04061b150606051c090203070504050601090306 75
    0x407660b1741c0724900d04103c0d0401c00d10043d200c0b9441182a4188811103802c10182c0e070001c10b03031480688160351080c1da11802041c01803403a07905141420030481c0c0c0d00703070010b007424041ca0080c1d00b5103106985402c1800b502815041c0004d140012000010b000b081403c6140c9401901904840d04013540d100c0c0041d080d98420703d1408503e41d0303034805004151030858a100d440500ea182c945046282034090305442080040ca0b201c26001075102000c0d0080c0702c1d800f114051a4001c204648032a190101c0c02461061050100c40b04040c0d0080c808a0311903008109108942c018000341c030700100141d41d110a4030740c074004134ac188009a400b100d20181c4400a6103e400c0810380104242c1c64051001880b20000340d0110030f8041c4200400e0129a90021840e020200b800b041e0051800c05403500040c00c46a0341c401c0c1c4106450040040b480641c403a00525060360f0122090052403403156400040380e4110b100254180d0000104011a0500d5086664480c2050411854581c2d583e01c07003e05407804031 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 638724064 1250 638722814 638722831
    0xf09030d051b010504020904080c0a0c0303050d050109051b0a0903020a1205011b0f030b0d14010507020d0f020c09130c06050301060813052119030504061a03060a1e05 73
    0x400d10540707442c0e60340c40010078900b00000074005800d05402255007000041c1004c0c1012500044d07088041004210f940c20700c1d584050890640c543d81c1c28000e1054125100c02c100711420040002002c1c0001d0244501400010350140000301d01d115601c4003d6000f08510000d1011120000000d0303a501500c1c680104082140345180c40003a1412500f1188010403003e2a810301142c000c540c6039000750498540c4070706040c0020000e1542001035001c406800c0e0040ad0400703c05600202800d040d0000d50041072503801b21800b030000000d0a8410b0502040008010381c011515207102d45005255150842603143c1e072143c0301c6a0a4a0381101611140c0080022a0740040100010399000c1c00b0542d00180c90040c11a005005075100b41d111000488940080c000c8100106080c1c0e154600b00d4118580410080192440c07001025020b800c2c1101c0a6800914100c1d80540318150400701102c0ca05004014040aa440d0402c040003000b201200c07006010781208459010015403040b2805506078 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 638725314 1250 638724064 638724067
    0xc060608010227030d0504090908190c03020c0f0607030305060f030d111b060315030114011d010803190c0302120403081803070b0d0c020309190f1e0306020f09030d05 73
    0xe04401c0401c080c0d43c45009a020004440c041c075400b40545040e224000d401240358001e6041480213030160050054000320704660004200b500b181c81c100c1c59521940a841c80320380703280c3c1041050300d0507404554100004000e2007001910a50045134010340003001c1400c501c0c81403021a00e025028503059010030703e498202c2040342401c108034140701c50141040e0440d102030310041078190001034800c1d92a500d02511401c0165400c1d00708150710001501991b50a607501d02c2c07e00712585130400d40009243c138403c00400c0e1640080b08603107680030607074890314000c03082c04c4003200c030b03203c0422094046002d0050f07a6800505148001c000a50052003001d841d0380e442e4640300c61000c5017415036442030b40062400c00000c0e21210030f860b0a1282e0075400140c042c840311040c0e0441c4502c44203980c0c2b01e041d040345903580409440080c030035100d81810541f500c6403500c90381c140032030080d00c021000b541581c1c4100005007050300104110003000c0e0340c4a00705142c000209150410810b031790004140c0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 638726564 1250 638725314 638725357
    0xf060524093f15060315090a06140a111204020f18070f030c05070b041b08030c0105090c0613052202161709061e0f0403050303040b0a06080d0c0606080102 68
    0x1000c00c0742d100400790a5400c42c6460414030b00182d81c0d0080400484046c001d107000064054006000224110760000c0c0c1c2405206810600100310400455040340c21510388002256505d83c1d900030364010880c01c11644405485507001c0124a0350101c0f51039030300048090403800d950307070100c035018014002e9888441c10b84070080800b8003603822030740210040002c01e00c00000481c2940c00001d400ca45c204030041032175541c040205c02510700b03a0f0002102031000203500300c8000ca05601030b510401c0507401b610b1401c40d411007000220310462018445400005d041400117240c400c1076087e8207540c00c8000c010242040c0304e82403d913080548200740502014400034144400740940c12641050542c1c3d03135207014030280010b22a809040a11344000c0c41e40d0760600ca0710920b22049800f141491005c0740d440300d0740da14080396698402c031012030304d5907040380c0861080090381c001c2c0e90a40701d400d4040e00300c1001d40d84013150500b0904005581250700e0b9040003880b124284018040d421580b8070030030b9240c4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 638727814 1250 638726564 638726689
    0x6120b060303041805060109060c0f2003010212010306060e1e130c14090702030a090e1e01230307030206030103020f31110a090618090f06052409 64
    0x24009d50042040c030070401c0d007e0001401203480d0050840c2e20031a040900062840d000b840c15100c4014075406610014010b1401d41840c00070a0483e4450b100a000076500c41404560901040d2050480f0641d001c00400c004403000300c1c0641c0c409050103180703070003090a03192142011910f90200e1807511131401c020210381040c110081d07100b40389000861a108100b10010104c260300d108d0700602011601c08540c2c90340032156403402c004650380483d500f65842e182d0003c0081c0442078501c0c500038250400c0021401c0c04a00321702200e40007006030b41168650b40034032640848813060264480030701d19041c18003007020746803000103110141d600001240010300c04c03002c071307601150951020345050107183da4403079203c0200e46c01d40b1801d26003002800c0d07403038006000900d001d411a070083c6080450545100350240d0114046032801c8503002e00107415600a8403e1440ca1204101031003010800c00f1918103210341c0030101641406808210810301104510b40c581007210382004010700d41c2c0c908002c00c0c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 638729064 1250 638727814 638727827
    0xb0904061b0c031e0509090c1309060302030a0201031a1002030c0f0f0706140d020d021801030b130e03070b090a02091b0304031202040b130302040f06120b0603030418050601 76
    0xa00500b000540900e031603c018142103141e43e0403107520310f040109080d4451044051728000c26011304501c825040410000c042c42d0010241c036140f203610707a90b0000c1c460903140100c0d0201c94000c0d020b05000044e0382c00450190813050341d852000d014600302ca408a4482520319808038542ea40611b40743e403044440b00d810001c0c0e03010b00d4034440c0c0c4000ca0351018840003003040c1046456508140c8030b41c8024510900b00c50044201c86102c00303202207812400040750b60014210010480c4000c0c040920403401074045500066000ea0094007a0030309107201d00743c43e4442009400f0b81e0003181d05010b02d07170783e0307604030694101c0d900c1c0160740250504c3c404504051401a41004010811204e48404140c180c2d1850100604c00340030402d1100c8201c41000ce203a04540c0a4660b2100d02a6107000c0000418014001480203d009a19100051080100504c40ca000341d5028409440c0d00310915102e140890902400d459031600042000290824406007442c00d6805d000401160b5480d0000014001 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 638730314 1250 638729064 638729111
    0xb0a0815090c040b2d1e0a050603092e060b1b01020424031803080403020624040209120a0b011703030f0708040620040e01051516060b090406 62
    0xe242407100d0384c0c2440e66081400c1c8102c48001c0c00520340300100401e00303c9030010001040b07400444c21140404806286080d00d40c0b408001c3c0c802d1040719070355105000365444101e40c402616084100c000841385281c6141d10780c90031022020b20000e40803c540c0ca0121105a8440d07442c4020004200c01c1d50465000610b154208045c000c508152601a0420b14054400b4001d0781001c0010040120a4069030040103107000c1a072078401062010300d0090052001a90198054800c020000b95401c038441d030011036500591070841c1004000e002403001942201400300d500c540c0d421545441c0706410000a04068002c91038500ba0754500480740e8541980321800c1c54041e041042049501011031405580080003441c2024403a030f1181403081c0200780c0400c409030600d8032030802021404901c8050401d8803840040107441d6641c820811074000fa0124281a0402090052003c500c11514203602c19074003480300030805009220000b841d02200301c03801c80300c42e952450b071529002e581c2c0462010 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 638731564 1250 638730314 638730319
    0x9020d05090d050f0a120212060f0d02011d03030c030c07031b0b07141609020c0705042007140d09030b06010e0d02040f060e0906090c01020a0807060b0a0815090c 71
    0x8240b80c26500105284110b840c1c0505148000034200c03d002d2051400c5c4150901034001113485408a03158140c440d00e007941c40034441e1452000454161610070456030700d06505841d1540c950704a81d090812403004008095403500052100700d1144500303100801c01d00410b900a0441d250940c9070080b0940020000b4000c0781004d48003d11814010301d003120036503508000100c0c000141689143d10300802c0050720340c5600d84403440003030141c080341c01902190b0301143c1596200d940742c4007800b048408000200c1348400c6504118030800c0d02c918001c14031680200c4000c14208480014140307030410400400000071088441042800860754119801503000d1030700c03a840030300a80003d0804218540060301c1142d0317952100080c1d0089070b1200e801024640014240c41ca45801e02d06e4458808480120240c0200c03080344078990b101007000c0044951022250341400c40c1e503240c01d0300030103880000355086040c05e200416021000c001d40a290668030040520a01d44113030110b06100305c15031201d0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 638732814 1250 638731564 638731573
    0x40b07020601080606130902032505100207171c021606031b031a15040305011a031005060d150905070e160c0206040302090f0a050106020613030f090f09020d0509 71
    0x400074040794407508a00c04840c0703100d0311031b4000035000c000c12510800035030500c1400d0103104400003100a81702407488072401c1514042d520000e1028001d41e03148107000680190b04240311000420510500207504c0d40115402d0044241c2d2031025a41d421902e000580c6c0400c2180c055160322103501d1f40075210720b142c00e11103103002008840200082150310402e16860750307002040b10494844280e080c410003040b082c005207a41e21079181c954824001034920b5400c1001c008c0704400440405042400f01800a110f80b0703580d44c040724020880031b40102e5021001060800200e0b007104030a0082d0b0b1400300b000510036500745032052074040942e2103c80086c0d100c4007040f0000c0c00303441c01707640900f86904243d4001f10041c400510035104a80000b0760103000b99092041c03a8554814080c031036081114100071503603ca090a0742e603584215201002440d06034071880000b48600b60306000540c0c242444900c1c0c940b103c12200002c0c8080e042000000c0d40803c500680c20344902a068004d03102e94043c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 638734064 1250 638732814 638732819
    0x2502011b050313050706050a0215040506010302060711030706031b0e06030c180a03060e1603080304021002010e2a0a05090c03070c0f030203090a060503060a060f1115040b07020601 79
    0x4540c03154440314035109001c00840003810410b00000031007070051340001610282512080040c00d50b4201014001c0103210b41541d147e1000c1401c02d40074010354205004044c582c2ca99402c1000f40d071702c041007c2f40e240070016030480090710100520340c060013540d2004100003218040c500001c800c06101c0b0303c10440200103102c074039103810b81101e400182c601d0103540d5403628840d1010ad5042080308894004c40700110002c140f10340780e4029242c1d0107140d41928a000304409020b80440c1041c0405000d105007000410014940b601c00344c440200d0728000801c03d0019010b0f16420031310100c9038440c2801c424503803c0c0304409a80000585c80c08100c3d001241103082a000c907100c001c0041402c4a45480000401ca0460040b110181c515034090403070f858009083c03400035100d40000058074040e48030f14802060540c0502d00b601c1c8a40f0001d807410310020714050088600036460301e10001031004400b03008c1541d120901409032284290b691860040c10940751030244103c004044104640009006 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 638735314 1250 638734064 638734091
    0x1b052118060709031a0411040513050715020601060f020c190902160c05010f17060d0506040303090b010e06131116050c0a0e04030903171b0d031d070902030a0212250201 74
    0xc10321f070307501030b140020f450380c505082540303030b20140c0300240152144040008541010902042003a03105609503202030341e8548094960b00020310750500580c0082c2c00882c2d49040140c918044031800c0c2e11250b90a40c1d403200b540c42280d11203a0500343c8031030b00305c0f00142481180b0680750005d24080c640070351130f800070000041c1070f982030419000c018009400030824030394412900451080c0c0103410340b052811b1525000d00106030050080b105004440b00028200f00c103144021301c07031b10016041d40b0b80841d0000b6143c1c000c1c20076209070030b0741c020244050058001060812a00b8621a03001810402541c2e8200400140b03150f020600d4407003a0410003000980c804c148100b229440b040640b01c8006558000806020702c00f80305200803034240709000410380000300d580c5031302103503107041046803441d4545c40214132003080c000c0015031000d402006407004950086502807600440103041c801424000c02c0d61886c1902c090403500500d014410401caa05005450904002d000070040f84000610 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 638736564 1250 638735314 638735333
    0x902120601080d111e150f040f030f14031f230d080c1006090c0c051b031e061009090519020301020903060106031b052118060709031a04 60
    0x1050402c200c9200c0d0102d0b4480004c11081c5c130792203002410b14500c18122030724165a030002622510150800303034080b440709204032508a00550b0019880b0424800755201516a580c041011100700080c4480e900700000000b0041e50203484068032007400100d00e9003940c3c200002e2604815800e03940c40c036144c008001004410b40c0755403030543e42002000060f041204050044001c10380b09401100014122f110141d40715800b59030340000c0800c00b11009031000c88010003200001850b60307000260303020004190700c50458100700010100c035002c00f1271840308041c0c0b25130f0a1520229505c80003d01501c40c5076005404040c03c0c0190003004140b540d500d810383d840b00301003401704407030451112078000d40d01c4c00c1d01150342d03c440150445034103507560b144c024001c2450040d8202e4507451040701c1a40c10b845401100c42c10b4280400c661001101843c0700f0f251041c001d46884014881c0c540310f40c0301312101b0720a180c8280099120300c80010314506100018038080341881c402e9807800d80c10400007a22982 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 638737814 1250 638736564 638736583
    0x80915010f0314100609140c070201020d120608120316180e10030f050f100c020606040c02030c15070f1b0b040312061211190e06060409020a03090212060108 69
    0x39211020818011001303041c02c1c114001402130030f0918001061700e6129070000f101030100b69040404607950321140340110301489100078016049000f0a003035040c0710703074400184c10900407170000304696101d0503681303441541a80350130462004070400440c803511600710864a140d50600c010611000300010304083c006001d000100c603030a0000c40e506419289950005e15441204581c1d5540e0328202507a480f901d00801070000d00c00c0c60340300d22512095005074001c6545d19001491780d80c03542d40800000d001c46e107080404510040c41001160001082401c0c3d07503407884145169641070080d00100514100f0507600b0510070910750900700103a1880200300066080f0322000800d032280c1c80c00300c500e100360107000148a8107282c004a042444120000052441100c0900c5e041d8240401c2c0251004688504d5400d2240040c0400200402040041c0d01c02802040c4615050b1904045070898000a24550003e503a8035543c100f141004841e07440750301442002040158034201c807050352a403000c1c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 638739064 1250 638737814 638737823
    0xc050105060109050a1208160f2a0e1b2115150a0909061d010e090c1003111306020c090411010c0602090406031b0b040b0a0807050702040c080915010f03 67
    0x41c1c086e405100c040c8003511018041644443c00d0501c10b41000300d200740c0b0b058020307030b40148004604465000010003103a100d9002009031801646020641c203100d2a0003030106501440e111440d03c4c034070b803d0200401104400e0000d81c140d0440755000f4401310040244080d4220200c2c0402c3c0d05075588513200500820461881d0656440c520802122180390940c000c0101c941002004110103192240042170b50030342d42040181c0761382e191070100080341c0580300e1240fa900410b041d10140d0410300030014a503201414040345504201d0a01d080c1a031140d207070f50401821428080c000c55906100341c0c8a041070864000b401801c00d52144000c1c00e4810070601c0c1440300850454040010a030142c80180d48000c10400c00c0d01e0390b03418064400c04070713003d0180384410403010124400c08020195400ea0b83c1d03100e11941003210389401030701c5922002d0030940902000b840440300594448c09140c124103d65a0785006901307020144515251003000210782560f00700c0014000187d51103070080c1140e130407 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 638740314 1250 638739064 638739089
    0x305070804151e020418020702060d050c07140a020f03010915051b120703050c0a090302100306050405090f010507020d020c0918030d05060f12030306040911030d0c050105060109050a 80
    0x801140000302040205150403c0100f10445440103241d03001d0011a08840c0450604002c0e0740c801a080344074603c0c00940c03101082c042180280c1c15540300b194058400e502c038610700a016200e1a01c200d0b01c88152640c3d0390300294260086040c5641141509602540284051011075039089a1410090024017101d540c410018a20f00700c0c07850180003441e130301c1c000c0f191f035030301401c0c0682e5030890100c5001000c41c0c06c10000c10180079041040b114881901c1d40d40c4611107066608124103261215003010806849100105542c0d590b0310829008100c1d03180200400714001000909583c402088481036400c45191103040340c2c0c0206140303030304c2001110b08883c16540c50141020014044901609034440072031300c0306c04126550322580c02103400b1140700c18288d050800300f03c0d0900300414007020582007440401c405082c0ba07000050035503c5091844003100c1c05030702103450940c2c10504200010080004802440420b105d1a90809030070319110b80c034281002c0103d000c280e00c1c5d20407016120b80 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 638741564 1250 638740314 638740343
    0xf02040504031e0206040b1003080a08131a09010c11071823150d0809010e030106051c02090a11090108041515051002010b0a1403010b1c120305070804 66
    0x424940343c1c03145541a03c2c0290414000c40703000b50b440a08850465000240c80c01190f54500390001c60740807282d101c5441031500e40900310441c0c859001400380210015844050400100c0d40c20030f000c80c0c0820003544518901c1d001c10164251142083c0e2103007405113400c040503054001090242c1540c600f16032446d207040018460000419a480e00803034031303081442580300d10301c5501e60200d000e9003004901c1c07501c0506400030024003017103a08004001c15030400ca0440c09502501c1064030509000340001080c0c0d581341c0119211007003c01d001d42c91022811211003c5160112620340c100d14940303001c000702e909000c000d0000d4820810424103106c40500054100100c0712035400d15520a1001400001d0310405032204000c0580200da01c00c203180c100d61541244148112465580000c21911070035180140001c03410190300c00e465015501c400c102c01c030325280c1810390403e034051035041c40240066400d20b008071203486000c0c2e500701410f02d010b010324070b030b48110f282c0d810a4105403180240329 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 638742814 1250 638741564 638741567
    0xb0a091505090c12070e0901020403020325030f230d020106060311070803100b1306080705070f021201060e0c09150a08010e130204090609020f03010c091806050d0501061a03040f0204050403 83
    0x9480e440180080d22034400c107c00e204040d0050812030380709604071014a0304c1030824a50022000c1c2003800382c0001c0c1007080010560b16851054024080c02030101e124800c040000584d02804044c00d02c030b03602184444617135560912074200101210310342000300c4035151003c040140b00f4424007401e24040072020941c0040e51108000040c03802401050791015a0011203500c484140f080070045880100080e03c0c403406141124149503000515481204087d0300b0403c1c03000b206451800700f59038840340400c00c0c0d055054242e006500d1b0081c00c9444134400820815800f210711001002c0c00414005000b2854106006505440c400900e69076603540300205520018924030000e0750240c00c1140400511103a0b138415a2000e00035100343c10700c0c04080cdd0500d8244e91084c2554070000e055400104948a2800d040220340f0040c0d40380491035959070400a401d4048100e4165287c0c1d40d501c0c03080214543c1c2111800c155121042c1040c1140707800e80701c010000e070305454080c0c090340c1c48070000f90825 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 638744064 1250 638742814 638742823
    0xf0717070f120c0608060609150d020705010b030c030a0803130501090f0318050a1d0a02090306091c0311071b0e0a020c010e030414120a0b0a091505090c12 68
    0x8200c1507044100040d80c0310039040034081601c40c00e03120116075040202d496480380c00314034800e41c0c0182c1240d180c00c9200303050201c20040040d031a05002402c1c094604a030400f400181803581c010300010481c020050101360501c1c40c6d10780340038070a0307200f080150006000311065075400640e41000340c40c00840c0703080190240500400050090121040c42c2d82003540040358100700c0703050540030090003622001803242c0c000c1203005290035182030300c005030000000300302c0d150b5119034000c8000d030a1070102c1c030110740303418025140c910517504007280243c490041000002040c01c268502442001400e090740305040c4155840030700540043d203229581600105d000900601c1c029802c0a81d070b1801c05040070080d040052040c2280d403d0410000d1911000030948042c0c400481c2032443c2c4d225100104280e461620941e102c96000d10100c20001c0b41d041c44489119400b0450041a4900f940c81c11700f41d4038035010280310700c0034900003e015013050001440e00741c044007600d404000365818204145003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 638745314 1250 638744064 638744069
    0x108090f03040320010207080c0d0201090f0b0730260a0510050a18022503030b0f01020a120305330a0506040b251b170f071707 56
    0x36403000240020420091341c04040025001c0c600d1000344244001c01281c82c2d071194864100d1310340c408064a115480d02c10030900f207407441410b04203e00b42d84c4a103103c2401403a58441030303508401182050074440d101406441e052082c40b420b1303001c0311849420080100c0000d11a50410426203000c0c02c40708071408031881c80d0399601c20042c109103013480c0380102501040310100340c8a9820f0030b0003da02d04001d941541071f40d43c1c501030720700368045000c0700e58029001410001000510411980200c41c403060300011074501030703500401c001c5032001c24130080038890241c2504551040744404081000010f44481c80a21460003003003603160b04104055000b8942550510f0207a10010590325400584116107c07100540712501115910410090103010320300c27038030300821002c1115040c458413200884401d0102071804070407901c1c035038403140d0202020011124810001440600250240081c10424040c011000705003441d0203c03203583c4c80e50494800e0340114001c00055400010701405030501 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 638746564 1250 638745314 638745343
    0x70c1a0a0f050c010e06100b2a070b0c03120c09030604030c050313060e0405010801181b0e13141c120b0d0302060a0e030a0905092809060f020702010c02010809 70
    0xb4169500c104551506c80a840e14582401c11910004400c10030340c05030340c2200000524141c44080003d42c801714508254842c20050081c0c0c0c3c0045002450321014091910f0040020b644481c000c2441090404029160050400302400306810079540014150391080d81071914090b120300d1071601e640707035000d8424010a010100b0b10301003000f03540481ea02e01f1803d02220705226507662604114201d6039043d4805002072210410394000c202c00f00c0c0780f02d045502140b4100051561081440740c81d441c1554841c060350000e8400c03405020702000c6555610718500c1c0600060b01101c4240310040700c6014030300083c003200421412400b9025440754400c03a1019101c0300e4480031a00d8000d4450301c049490a40741e9140614292000078000150f500900464403109609800c0804019410600400a02200041007641007c510307180304842c0e01054001070210300980300389090b20540d0a0603e43d200841d00c1401480050707a0b21403807400500d074083c2030115070307901c92032200740c2003400c444016103 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 638747814 1250 638746564 638746571
    0xd110f04140c0c1005010f03080a11030433020304140d02040e0a300503090c040c020d02010b06120a02030903070f113c031f02070c1a0a0f050c01 64
    0x2c040820800200011400142603807080c038804e00115003241c000b0b0003a0060801c4442042c4000b5420038010048240542000c1d030351491342c9404185180d0194200d406102c44016600100e00c0409030914030091090682c4501d204100700c00070b6a0780142c1c869248441d0b034074461248640c41e11091840c000c0d0700a00180309140f80c580501d40e5400901d00111140498400000c55019000b0a86c20208407040310701c2443d1144c031041155540c20160419207076010741c0802158542e254480d1024000c0300350003414030300303c100b100a800c460424075544d0080c03400b000b00c28526419201c00c1070740613001c00801070701d0340c8640320164910301910b50010045c01034905100140000f0300c042000d0030f20200c8010240326107820b14107102041c400c0c2c100c400c04512000c041e03800d520803810954035100150846034103c40c00c1007403907208203d02000e110102da0000f6140d06012030f203190500030b0031521500c0846c5a82264400c55144511003050b01040280d54404035240c1c440d40850b00e084141c54001d1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 638749064 1250 638747814 638747821
    0x100f0f09060b0909030310030b040309122307062703120c021309030815190f030b09030a0c06111b0c0f0415121703071d0d110f0414 58
    0x214000c01c0c0103402e051041c9842030002e070300c00400008481c462054130754a5100e41d032071907540743c0050341c0103001241031000301000411242078000480060901811000032113841d8001e40e511a810001c0b09009160002c207010b00c00c654020400194654144410103100305061180c40400300640e00018882c074440031900031554ad0003181080401e000710740407025003404001040848400c40d1004020030305441c0014800b403405c4c0c2d82e4810408010700380a0031440301d03160030110b803400c030b030010b07860389001010030300038051034450342c2e07901940c0c80004510b00168484090242440000001c0c1155255407084d1110131912041d14030710155010b401d2102446a087c454881c030640d11810b00038600b404400000d03107054090b500442c0c519901c2e41c0055814000341190002201c0001d86000080c454a110000d1001c4003c0d440b40c01c160f610441c10540034100c8060001001d0200e91143c4100c01d0158085450010144032800c8112807111200030007002040142c078400715203668054004041 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 638750314 1250 638749064 638749073
    0x8040608010609050a0e04110301142707080a08071103010f06031a06060f070303020903030304060c08150105030a050601030f06150f0507080429160b07020f100f0f09 73
    0x485050b50680d450780c1c491980c071074042c404e5040c154400c3c50113400503400070501180c0102060300c10741784054008142005910302c01c16005100b0766081200b502c0100c0031108a6640c040701c0c0b200c10a00da4040d01c40c0f00e203406021703940d4929109001c9c1400c0400a90701081003201c19401303000040180080c0482c0300c0035001c50300184014802511001c410490040f2000550740200b489200014512424040050450030031600102d104805240d405c01086017150360801c0070714801e0703100e0325000c921280c4404008240d86000340554100240045a031541a0780103000e40340c0c4520116000109a0790725030049000c1e113210405100e80c0b43c41c0180100d002c3d10650480305c1d0000340c03134403502e404460007941216103200d2000041e1004005009c184090300c1c1102408c404510040d442d0000510480c03140001940904904941b0082d0000c0b20800c1081d0501800d40c050f28070b0020303007101c510784045280c458920150341c4800503074420f46000400a558000984002491802c1110890700d203070 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 638751564 1250 638750314 638750327
    0x806100e09161806170a0312141008160308071b33050403020102070504020717030f060301060e070816091a040e0127050604020d0203270d1b020607080406 68
    0x420f420302a081c070720003050864550041d19003103c204d800402043d83d1548048621910500d060040180c035000c0f00c44e0280c01f181d5009010700704c07180391820440d19110b1058900380d07100162030081c0420060800c0401c0c0f4110603240402d40040c039001c040b4502c2c0c3c9119540d000203400440000382c40c040c1407a00710200c61030ba0740c43c4c0e4240101c80e80903c13890302d90039505802940710013030050384513100034041810240c010300501c510900c40e800811010500107490f07600102d0f0039100c1ca80071482004001c0c582409050010011210a20613504000343c1c001c150000c000d042400d000208074864080030701c42d04d6030b0303402084201102541c105c40804c00c3e42565001c4c5c401d401291102e03c0c008500c00301d40c1e003120a44541c00d07200f49020034040914030009084014202c3d940b03d94203201d102c1c00d03424103000035441068442d00b13280090a800c4800c0095100c9980300640a504c11484446a03d800010a200c1044280800d046007843c0f80f000880380d10407454000c01031030010800280c00341c0c2044 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 638752814 1250 638751564 638751599
    0x11709010b150702030f060613020c0c0d08120112030818281106030c0a08070207030f0809041404020907030e01110a0c050d0f05120c0d0c08010f0806100e0916 70
    0x40c10f41b0325442041c00c4141d40c1d00c80589003a5449034020402d540f54500d01c0d401071080040400c01d03140080038000014044024034001602c06080000e00301c00f03403c6103d000580500340c1d80910034070305600e03038500604008004110400700b0103001c884a00c012420002c0780c14540c0c00030103403008460800600038060407100d00c121001000080c0c8030301c813031500310141c901c68902946240d04000c000c0074112802d10024102da0305501420b0004408285032a850000c000d0007503c81d2a6282d038490107100171030309126100c01401700c80c030b010301c0010380e169920a40c00804c18900410b010082c00100360040c8805004200c3c1e4010002d01039842c01d8000000c8408240148141d4040042d0080103031b5005100f24a00d0300003c00030030100001c8a0301c001c1080d00940c0754172546003820142c0e03c484c0215044c490021003c41d08120042101c41c18001120010340000c2c0003070506414009040700b00c1030018014503c0780c15040c00002c0e40380b68100504c0ea08610131035142020b071036842045803007203400d41 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 638754064 1250 638752814 638752819
    0xd1e0c1e1b08010203060616021906020706090e2503022101050102010606140415050d02030712150807090b0613030f020f100e090702010f142202011709010b150702 72
    0x1030030000b070051040c820740b03109083c007604440c50403190204200941c240d00c50102d0340980508120303000b203010341038082c02030300c2d0540040195504103000500604e5031039211000c200d54110400a044005030701c3c000c0c80d22055000011032440d000c10680c080d006d06a181c04807920040f41d401440a00180754138120f8500f03130020081143c6030704045030103050380800141030050401080041c5000d0b1110302c94030f10b1162610604000d604201d03082030ba441502d0b4103000510248040b40c140e08540301d188031401405072079508280c6004103090302c460041c4601180195101048038450700e501085848e4100c2d15070008408170348920308484e400c81ca004090740543c8880f02402c06a052402c40c40205c0f001640710901c182c02c451f002c1000501c030003040e43c408c654948100c01c0c02c41c461401600141013000134100054a441003080750424a8018050f441003010030b11318002d0b036001140070b00b1411600300c180e40556209150180507000b21000d054102078201c920914103801c1c0806002128403c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 638755314 1250 638754064 638754113
    0x1051b0f01150312080f150a12080304050610050d140106030c0303050d0f290d05101e090308160c080307120b090405030418180b090d1e0c1e 62
    0x13185000c6038500c000301c500c0c01c4031600101c04140144614408144820001002c54000c2a00d40364030070385400c8500702c12910300d44044140020000240010741e44407403030b00304904055140000041c07400c0c07401e0b00c1c05007000c81c0101013042c01c00760a400c81ca000d07541015a0a403040c0d80c9160080a990002c0500e03510303d07190030000d20041413a40100080002c0c02178017a420b0580400c04180f44181c40e0703441c1a4015461500071000883c203104206010008000010703480340150b05c1a800c2d51a0758090f005107500c0c00c041e030780020b0742060001e2780012000410241c00e5040000035982c1c1000e000c4040c0111030003004000080350300401c161b280140328030060103585e101c10280070045109940041072500280010310842c100e0051030b540c008401100031820001c1c5040032000c0106060b016110390a500d000c20036107800401c40020503058910f03006440392089800d042410b2540b042032000c12100d031340483c05002c0010702941202111040544000041c0e2a001212241607948902011407 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 638756564 1250 638755314 638755343
    0xc08060d1103190c080c01120515040501030b0a1109031e1504060507030f02090904080a030603020a0f05010e09150108040309090f0c030f0207050613081c0203040219030201051b0f011503 82
    0x3004900881121b8040c1c60780c0484e6074030a202032007e80740042030a42c01c100d1041c00103810f41d94900034140218082c01c0d41c0c1d40182011450344058400d45002c0400500003000f003501a900d00043c404402ca21040c2996506134031110801e04100f80c07400c94601614201c0148000e001c140e5104900a03103076500c0c1006115004100b034170907400307944d9409500c05a1880044d0100c3c40c0d00004110310791042c13800190607600d0740d0001c0c410300d00c541c00c400d240303500526007481103507003103422482281c02c01c8806020318034104501103108032911000a041200c1e40d0041010180507200910240c000c1041c00d00484082d0640b100c01000006801c10001e0b0404c0c5140483c04654030803502c240c0d8022000d0b02e510703900c0552850161031120070403140b00b070040200c1005510001d000c038400480001c409030383d0381044c0c010410305070081c1081303121090241000700b0060b070f000300485025201c100085407141c00300f07280c95414038046002a81180d4209041a107511103102c005400741c3e407043c080381d200c800 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 638757814 1250 638756564 638756579
    0x8070305090405061c061a150706050a2007030c02130c09061409040e071d18011506390212070f060c05070b12190c08060d1103190c 58
    0x562200140c1c0040004005003808503a0316004428800b40047c003a0300600c1c01e80010a100440c040318065222502141d06010000d65000742c94122080c060240044411413651410700d40d8420603074489070740700280000805004c1e00586812039001082c50a6204941d1105009494440c2400001400c042004500c0c58000c0d203411140c004a09250340c146140001440014100c1001c400b0790741c898900c0010b013003040800c000d04003070441d65041050717003130030500c080104c04007160441040e418002c15842c0199075038807010880f1014a004003c3c0c016951030606040b9200300310660014500c1419048051503030168030340148291803244003052002802500d03451280a00000d4018451007041254843c00f249900540140280c498040d034900448a25a11814044100300a040c00700603509201450001302c0ba03420030800d00c1080c903000380007000d0346401041b240c4600207036501a0103114215141d1041c00401504031078442c060810f55211a00039450704403103282d80c00b140440c0c400c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 638759064 1250 638757814 638757829
    0x4020f0a0201051303230d06080304051905060f09040902090f010812032412030319060b0a0804140c030f060f01080a0b060405250908010e03090a12050a0807030509040506 75
    0x5074150340e4480c82c58841075007280304140200f00c582c6d001001400180340740d0040b480341c41c004250100085584525080610040403840fa00010001e02c14020801064840004131200c1c000b0924116685402480000d0300810034041c0c00703504440d00790100039040e018841d2650595040030f0440300c83e00e60900701c0020500c0300b1100f58044e080721b0f031505205405521040142900b00600703d0401010039002c040c80c41d00116144001e0030142c514280e1140e07498400d18000e001d00101d11460003108650103052400041c00081c1455800000480c40c4241402503140080004059a0061a000006503030f150010750b40b4030030f026808400082d14400006d98044401d5104030381304203c0c0d41e0705042100806000304549019a9100d18061070030180310070a040105c9240c0f910340426007480a03c608548910b0580e1825900070003207020981d03511044032040f900004490254000d040c540b940c00d00c5c152050040c403104001c80d4a004040e0400c01800d0001410b85041200399159000c00a40 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 638760314 1250 638759064 638759101
    0x30a0f2304050607050f10060e0f041211030c01020a2601030b04110d0c0602031e0406050702210115080c031b06090f030717190302250504020f0a020105 67
    0x100e820041080182060340103030281c50300850a407004002d40f00181810541031142c00c940c3c035031340e900b41484406000e44c1803581104041d15013002c146420b66502a060849a841405105074041014001c02041048840810440c0000d5480741c05241000c0c00981018426480d18860301746004d580300200b01009040340e8000360170360304940351034884555030400d01c0803503a0811071b400146400b00e91402d455a0007880709500650796480e00c030f4803400105502042071611002b0030072081051a44c404280e40c8001e130112101007100290050a007000840302c550700010b0b50901540ca40180038000c400000c680741c032001e0700c410403102c0c4101030715800120030350310403607131311a20140d41820118094003400a000c1c8c098800098090f00084c80c0281a5204080e0100b141c220491a00418009403031104101c2a400c02c1010380c2d907401035143d0b140c2491603514015100174010309081c2c0c503d000b4004001c00f40003150b031000088013207512a070114890801540c01c1c0008252041411a1102e84 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 638761564 1250 638760314 638760377
    0x106180209010e010c0f0602040303050304120f08060f01110615100509060f07050c040e011e09020d020d031b08092d1509031606030b01050406020d0e060c030a0f 71
    0x25200c43e050054030b81c0a89084107468005c17200122000040c03482c40107101450098a41070b84030310303141c0340c90b840d00c0001a40c52030400c00c4540720748000940040d800c40c0c100781e0494400410351005001200e128900b44c08103011441740d1018000704514501500007141815144800788040303010b015503103841740c012080d400080400441426149120150040901c13450581d0700c411032410000e01506c0341c05030140c502d82d6507221098042514900413090405040b00c040c02201d4458001030181021002d010b801514212982c0701050b108924031100d0784c07201c003910180c410043c01c190b01180c0010711a80d008000905000c507000e031050f40c040400d0310b108040030410b101c80d0800c3c40000a0020009840e440b03045c03014048a035014411001c0a83c0c0c0301c000c100d0890700d040001000d851140b959a414440200028410154042045080001d060901d584d48212010102e80203115031003400500b40404503030969010380c0150b00181482d110754408a0000d0152111103450800f1060410b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 638762814 1250 638761564 638761577
    0x307080709021c090309050112060803030105040b0d0f1a0a1404110411040303170604020c0a2d03030f05090105010f120215031905130c03020d0c08030a02010618020901 74
    0x9403a401c2e0010668205501d0602c194500203030b005074140c0303600701d1003100820304811080c403140d64448403800039921b82c0721080c01114a0501840d45912041c000e40340543d49446d49100380d515a4000001000e90042c0844014070050070207184000803400300c12a105800b50100b4000c4409004191641c039100d0407240c1c0035201c0755030305100e001c078441c2203942058075a403604040400c1030014000440c065101e151101c543d00b96240205034005203407a01c294414000c1e0b04040c100018408240c07503002005401120b14541c80300c07501c2810400b08440300025200040c00c0580c1500711032801c06054070300340459221010014261407090142c0b104114024004000f2950042199080f541c0040c000c0b1880b03420a09440c0340c142e00454a1607d020006c801c0f02400d040c2da03210312a40500750b08984402e030702e400c0d81c40501c40045484007030301c203000e8821404c081c8407194020900400c0e4800859584425603200a4003808291042040d1480a290300002a10f01030085860004c016503640 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 638764064 1250 638762814 638762819
    0x180b1c030e0612150120010b0406051f050c0a02090114040c0c1707140a0507050a060206130204110c0a0302010605181003120c050312040606120f06050705090405101403070807 77
    0x4130818075030040001e04100314050510004c1210303100100c01d03400510300100c0c060f4030000038802903941603840503006469001c200b45000c100d60140d0113949100d4074065075039500c6254911b2401c07100e0070010354003a10240001a1440b18049001c030001002d690500c00b81e5100300d010703a1148040380c0d025000b031200c0d0100b210344842100042c05039900c42c21450100c2205110050f00c1c002030340900b02c4071944841001e1040d8035041d08800c0003050103100030549845c02a41c00d10b80b60186020003030080b502c40a40040b400106070590381303800c0c21803045940300308107401d009000c0c100701d100310b60044460b8989524200030a5610a204d050408803243c009465990703104206408003d0708400c00218914170400110103000800c1c241c0c01c0030307880310f40034102420074400719901580702c000c02c5c0d0700031001d4800040d030000c89040c002e40c201d840016580d60f66901528540700303001c0f409510034544020814102012800282503564145440c20400d0303980d81819078913010f50140c90f00c103601c40c0008 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 638765314 1250 638764064 638764081
    0x305011401080a2f0d060807081c110105070806100207030f080304020102070e0a060e0f0603340f0e060402130e040206070f08091513180b1c030e0612 66
    0x443c00c40140e2904203c80d00241041512030b080e101c1d0600c80c00c1e107000a0811105da82402a00046c000c410040c11201c2d20308041c03150348100071306080354541c40d031160380c031210b5002e04031005081103010000d001b1450801c000404010b400c458003481107100d020301000c002d2000403001d058a47c07080c15104c503d80183c480d0001904000d004038114400c01e000410100e00e40f556860262100010224056040048120201400a02c255185c0c0c1d416003c11807103030307800904000941005415120f103841500506040301d07104451010001d507001c04000792040c0180355220882d0709100d003486447d01c50303804000580c861841d000d000c5141440f000c4c00032058203841c0780d400c41d10003813005280804c141d42e014120850032400f0b41d007a04012a2a44030b6052a4903042a41a000680c02c1c3c5441d05001660010781030700c0c080c3c041380c80340c140c40e82d5031040042d40c01083c0389400104001d107001e24614124148038440841140010480c1e100c218642c00c00106071030044050000c07848655503061310 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 638766564 1250 638765314 638765321
    0x1e0c060306180e0703140d03050901050411130f020f091203070b0c34051504260903070807031a04020d06020702130504050d020d140a1b14010b010305011401080a 71
    0x806000c3c1d8020040000000342001100454210341c00d00170700401600c0742405012074a009204c4031859040000700300c0040d007429050114003200304e4412021f0200400c0110060840303401f001c1c40c15100161003c80904d0b60f101810418004aa048069010034607581c0d849000c2e00c400201640e1180e0081040440701202a0250907130304844808202c100c0422042d0300113214105040404900d550401448414041551610102980c01d4180d080a9541003010040000c141c1b40007114000c02181080f44070080f1503500d48000c04454000d600e4040c00c43e220200c0d4402103601c1c88440c94500002a80302c12907911450b001020320310034050b070fa11440c02a5200131012613000a400350300403011805c610402d40690302500003800e0524454101914021480340700005018242c4142c640043c17040049a003404610b01d0619480404584000701e0302e541480c004041c881080406801040f0541c08128414002da809001070790307035007142d4000440d000d261540002c41650000d83c00c48401d40 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 638767814 1250 638766564 638766581
    0x303020c160b09040c0302120c03060f0a090614030607091e0e1005030d11100b010e03120c0c0f030d08070509130501140f01091404091e0c06030618 65
    0x241650030049200410403880390450304011070340c0b600070070f009200b41081c0c03007100441d000d035007421440c04140100c501c614020003070035403040000010001d00d450310307260240100e40320042c04020700b6581b01c034002005451070340610724440c4002d51a4420a1070001a411b008940640307400100c01c2c180031b00b00404034100180c142080e0802c001c00a0300c030f120240c445100b03032010080c0c010420f080104042c1005848040d060800c44041201900c0d440b002c03820501c041c100c040d001400018500c01690704000340010740b84c0c94002c3d83c6001517080c44400003480d0000c1c07550156071203010001c08101c84040b12111550701a0300440d144010140030f00d400316003110301820117030306101d0480700041032070345003065241d1642d4442004120003901d80b10012a030f01812030b0151602008480028002d1469108403648a040811004102e440710f40c040b9420541104000e1104c000d0807481301c1c2580d090540845006469400004009129100700415640a0b094402e458180b400d120701c00b03040d854 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 638769064 1250 638767814 638767837
    0x902010906050d0b090106200c0a05040906061d0124090b1b0d0207030302120405060307080c271c05060a24090c08100302090402011b02090c0d0c110604030302 70
    0x16134a842051307440b080340328000c203905e41c0c4000c0380c0c03110002403107aa5804488903112690000050344911744e1204805003da81c2c00b5540050301404906058025042550110502c909c0c812083c0008100a9051303034180c0d9150340301d040f50071023240002ca040b54801d482c3c03000011401c0000303204100c000401407038562000030107039819048a100352810207030808400c40160b44001d10400400d034040c004032940b080f40f800a03038100303464a004543d031407200818071070401044200060b008d00611064880c804645600825425009410341c816130690204640c840c558060703c00c03c0000510481d10b00c02d030b078450083c10042d200d1524040240040154200d0200c0703a07414056a100c403000d03400303c020007018801040e03d510307a000c007411003000a02400e0b0003074024181800980ca17074280c00d9400650a00c1c11211581000d071402d038111150700d50007580000c2c45824480040000d1004e040070001d9540100030302242014140c03064100c00f0380400780b0341c02600004022038080c7e4041d03e0b100c41d11 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 638770314 1250 638769064 638769071
    0x30f030a050d05180f03183a0f0b06090604090c2702030a0605091806070f030e010203040309051e01020c0906010c0c0e01030c09140a09020a050a0e0f09010902010906050d 75
    0xc840f051810b0064010241c4202e61010400c58110168007114036051031782a41c01a400c0b0230117100c1401c0000e201100144070345180c00c0300040d40444100b503840c0c0c2070703042000366103285001e280c5030f03510020566030103100341001004143d0a203440d1050f840d40b61340c4104859240d0b841c01c01e076280000c0402c5405c4c19000340000620511707103d01d0004501c540c108000c00114903050000b003000c881c2c0e014152030402500d0007281c003071080f40000c1c919044444c505285580806459044019001d400800c04035540080b042c0401c02da045100107080d01e0084510320043c40f4010319000c40b40c0c5682e880e01e40140d216003074500190030601209600f0540600d03254541d110300741c0710301612142903800b9220200c8008010014480741d202c412024006102040c80294018695001d003100041c0050030020340d03c1c5050b8086545014401d4001c144c060401092140e0790980496010021075240741f00800320000685c00301380c113205d003c06840e030585400a020b401d1910403541500855181002e4580c2c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 638771564 1250 638770314 638770351
    0x60c010207030e090705040b0d4b0b0616020411040303181e180e0106140a0b0a02070b1803120406020d0806010206060609030a0c030b06030f030a050d05 67
    0x10a0004102240c0280c0302e01060865440c288201210014803100402005110501c0f450303100030111202028a110007141415a06541148034130030030110b0110221280d03c0d004559031403441014031281c6023841c400741d9860300701001060300c007511260760340048100210443da9002c04101905580042c200290200000c91a100160300c00d82042c0c0109030f00400a004280c004440b0501805a80100d100a00104c1c180b01c0c010342c040d40030b0b10041040900d48520000f02c99445480011406402400000d0386d416610010320f856400c11030141182d2030703001ca22641104c044405030300c000d0307004041c158944120a50345802241e115039110a030102024219a02084194182c422111038550b039a80b0300b54020b45001c0f80500c00f541030080507002c01c41c16a0700030841503400642541c0c01766075514030500087c1001d4000c40010004881014080b0a01658200c0c4038443e41043c2c0482d902c0c4007e84034034a075240100c3c4581000114200700000355411540c0003180c0120188091244bea01c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 638772814 1250 638771564 638771587
    0x20f062109010203061509090112050c0d1b0b0403020a051005070f0b0a0f051005510c0c011803021e0405060d111005040e1303023906 59
    0x31016928400969004400e00041303107407496044090300014012903103441c07000008a0003030030b4144036408041c1444000e0703006001080c008140725900082c40c104191240e8503000c0314002c0c18005091303106900400110b0100389613011a4180c0c1d400400024081c0c4c641801c00c22a0741c0c4012072001040014819040000d6984c041c80c50712a200c1d40c90b045da2440c04e10196011600b00365040c20816042400340000c0e00008900d45094400603960102c8030b208104144a4012420b0022241c1b0300c0d8120390204001c0b8100d0001c1190032440070720031030140700c2c43c03104211030058102a1a00740c014450b40c0320250301500b1004512006076500307011042d035980019845980c584262100d90101c00024022480c1034840c0707961095046488545040c820f0300c400310004500c64180e4000c030288010007950f980280242d03001444416284010b82c030b011094810050005401100035100b41d9010180341d0001e4110300c14540c140e081d104610b440c0c90b54006d070008c00900d500b40c2d0406420004201c1c40d0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 638774064 1250 638772814 638772877
    0x5132003031c05040201030f0b090a05070212040303180504091502180927030a051e040e0c07060e010b060d1e02030c180d050d05030a1407171003020f06 67
    0x302c0305454005032030300d480d00000d002d4900b00d2a0340d001c00e510780307980c0c01002d56072990b420b50070203441d40d8009800c0d0f85100b000da1904200350300c0001c044002080010030164030080b04070341120010070310250305658000303000942d01560b0008000c03050702d6239817540102e034550290070a8100c0303d0345003654000d0fa80204510240030389514100302031341d81c0d181d417144404c0703021078440041d0344008500c3c04000c0c4000400c14043d0000c0425002c00c584e1612041c131a280c0d007503c015003036030012482c0d5030502420b182c0041c4c2c003414040b100c003400c0001480e082035042c450380183d28001b401c0c01c2c1c0b810b50b00002d030134014525450903c0701c8401c04944034280303120f24805036100d440c25014950b80c0b9110a1060f801080c02c4004030751003619000f41807000980045880e40000c020740c20515125111416220090074202215040b800b00c2036003001000d80d440380c10700c580781d0081541070140342c0300c03401c1ba07840c6180c039030001940040b1400000003050030441d0062148506840c0d90501c0c81c4550300c078031381c1c00 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 638775314 1250 638774064 638774107
    0x151321021f0e100828110a0f0513060c0501020c0d0306050f1c11030f030a03050601120b090402150412080a08011e03170c1e010513200303 61
    0x1440d540340110140703650030101c0115040c5044a01025201000030000c12102000f00141840f140c80095554110134141318070150070007121090040300c03100440c007000e5801c130440f40300c00102c0c030741890071205010b0412211080400c0c20b810041c903003003041c01d07038070020300d0002100e1542d820403951521403402c1c44030b952883c0040c0d0303010548a10300010014000403540096108000c00d102000b0850504e0b040d0344d441c0e07940300c40a10302c081e0824001030b040801c110701861560000250461110751305a01103072141c3c000341c984d201d100c0541c1051000300c07400c526041da040fa0b1f40001050261414100082802c10610303082443c0c152501a40003110529000480392000c0104252850640016a0310301410401c44c0b18038038151181c04c520509003c80c0304c0904030040070840e10300d03107841d10402c5400d01c0c500d900894160701c0300a82c2c00c817805960403810103031551a02c00480d14403021079058982660304146608005640100c00ca80a68607400d00030b54076100c10084008505406101843d4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 638776564 1250 638775314 638775349
    0x2092d0f1c0f02061c15060f0801090506010c05070303030605090f01030807020111010b030a030513360b04020301061116060509011b0f240504120806010309020909070515132102 78
    0xfa035883c2031b581ca080302a0180c10500034401e01c8030f0b12410142e403250710b003030459115040c08030ba642c84000c0165600484000c020300345009a28020041c140c040c0c01c9002101e01c15030345084a035490510410340340da428000102084401c1018030095881032081540c40440700000007000032078400007910b05030790b1400072404220003144200140c203811500700b00401a442006100740720b58a1035420f0072003820340000000e41079002240e40e2207135a92000e02a00300c0900f0466036561201800ba00381c6140d5402030b156849805c030b002010046650208d4101d540a856141c10501e00d1401901c40c12021100e451500b0300256115011401c03c45000c808603018000ea08140c40f00030102000c1d03482c0e41138180d462942041c0500c00044d0900c0300201c203411503860b190000f502d68500403409424201030103948201848140424000e02203081021035404403402506070302418030100b1039004501ca200f100e1000105c04000109a18090340110854201042d0040ca0305500140500724103c21416 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 638777814 1250 638776564 638776571
    0x1203111c0201050c04030201091716060504170c060f0d02090301020d05040507060c03050403061a03010e03180d0b1302130926120a02092d0f1c0f02061c 67
    0x1045660203110707451300888a41c580742e1a05065800280221800d8420010408800c80f01880216402c0c4803400405141c1c19041400d10f50328070700185107400500441b40044ca10800c080001000024482c0c5485da01500c1d80741040000900480183c1044c001c500c070b165000c00001c400c640d000c0c8020150010b00c15000105802c1a083c0329107019142d800030410b02280805602c04685c0250035142103a51164020a0b0041d0000054204e101c140b8030458140d03003003a00010710803502002a01d205401c16060b2680400e5100400c4080021124003404844145002c0b80e0a008100440904940003412852002034161203903802c4849810050fa84c03400607100c2c40b803000222600d0403241ca482c001c0c07200c0c00c26040c0c5100100209018040c1c4110640c002101c00d425101d1a4060003141d00038400c40c4008081070074901448072040380c0c9a8400c00b0544030312081c0b440e1850404882c0c004d907403110450b018040e650701e2005545644280e030311901c117114040302c0182184a15640c1c41002c030010 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 638779064 1250 638777814 638777863
    0xe010e0a0b010807080316060204030210092904050d060b03030307030506030d0e0f2107080a06050912041505090d1a070206190902130c0f0206060604060504120311 72
    0x44500a5040c3c11009032a00000810004200000140c0c0d041e141e0a80b010301d980c038000c3c0b070b05100034030555000940040c1e20111030310120b41c0104182c81200c02c403145115070043c103c003c078100882d0262604280c0300050005102c1410240c0701820800e1048800080303203644040003034616002202d4100001e03845104205082c1010b0001c182040000c0c1000c0c889018080c1c000b801100301102e82901990308210440c810f00104d0101c000c0400380401681c03c0240c440010980740d0060074801e03a246800c050106542000c0000c417038240b84004031100e800c140c100104200c00105c1c0d0011241041428406100e45540301090007114920509002e03a82d4100c80c070150000720002842e1000355000302e0200080c0ca10710341c0c00e20480a1b86010000752410392840000d8a402d0000c0b81000c0080c9010b10004a8603082510900030701501d03001c07500555143c20800842c2e110794024000000c02c28402001800c1440141e0f04800e4800d091400b45401e10200d194039043e11091442207201d0b00c080003 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 638780314 1250 638779064 638779073
    0xf030117010b01080a09170309030d0510030203030703180803040b12090c151c02030703020c120a0215131209090c110c060a0c0b04030917061504020307030e010e0a 72
    0x21003400e00303080d1000b44160040c04001a14001d40244000051911542d0300d00c10018850303600b00b8030888071014030751a4104112829603030740245043c804000e2420000c110340d440054540c10403203600038011854403050b503070b040750000b4a403a42c244511455550215042c1c03014000380025000700b10440c0d0b2515001120b41000ba1009440015181c2142d044450f49480e0f1414204c98195055811559010841c1810542c2000030340e414411030310210510022550580081c4000d201c04800c42c2c1200750110b840e14000c1c1b10b981c081c2c0700940d00500f2031101140000c101c4d654002a0740d1903151209a00e82c4800035032100a200a6000481411050001c2820f911551041e0407052401009403880c0c0411640e03142c4440103440d01c60341d001300e01990700a1141d11251205540a01d0000071401c007442c01610110090003001e40c09000c0c9842400720080008445110b03a14840703041c0b900203a0101408020b40c07020340001c0805464100240c4541400d01411000c100036800810360713001d19040 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 638781564 1250 638780314 638780339
    0xc08060408070317100b0f0408060109021222030c141c03050c0f09060903010b120d1713020d05030c0703051f140f0a090f0614181e0f030f0301 63
    0x205007440305115828011919201c96017541a60f10120b0015955400c0c0460107416000c5c551100e500d51040384004212a0541d8020300b25141842901a4240d1501004004d11904015400034104400101c40340031034850740c0402c1645010b44003071018103000660b060700302006003000000d40e020a0071180c80c403a606208440d4000000c081d02410308804c4d051012292081505031031107100d01003420b00712550203601c11881c5050062000f06207031a0010b440384c89001a010b484041414081da040450a8403031445200e02c042e04a41202040c80d58204040d05003140001d50701e40c401030101080a1500f00400806903024000500140b2040710740913901c0604021690042030820500022407540314a01d00d4110424124a800176624000000000c1100030401742855842c240c44000780041030f40082180d0f928091410342e00e940c0d10307000c29007440340c1c0825040150b100b928051804d1034400080143c03144094181c40034000b141e506e41f071a41d04117011010070020000010480c0201001 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 638782814 1250 638781564 638781587
    0xc05040612140d1709010e0f070317030705030c0c010e06330102070312050702030a03030b0306100312030b180a2f030a0c0c0c0f06030b09060901050103090c080604080703 75
    0x30002c0c12544060f0200030500100c4038009003c031400d903004210042000c1d007100072040e070380344c0c2203410901e0510b03101030b6220761a200981e0440e50005803103c0c40e00c60003044a10032029519902d240d070300e482c40301d40320a5014550b900899540c0b580d40e20344070070050242ca409402911905c5a40c0c502d41d506e804640d40300c04401c030b15403105485245001340d802044110440b5040521040d0f15a5181010b980501c94690003d5040c0141103c070f508040e015400780c104414140e0488049076a42c0741402800092404041c0c200460400c079864151f00c290070054100f000a0031a81e0b00c2c000302c0c0740000000d602078030285250b5454071a1203440039041c2507140b0390207411310f11152101c84480003000b9280700207001400000d482e11503c400c031500592503104e03140c2d40060522841e0742da4580f0700450780503138003c1600007804d04d842660300d480c080308420300540d00149040e003640d18060054005050070042215084003a0900003404803003880450b200758003130f00c40c85582c0e200915008010000d0003 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 638784064 1250 638782814 638782853
    0x12010e01080d051c0c17010b030f1503100b040204051804060b0d08030f13200a0b07031d01030e060a0b15040e0f0c0c010609020c010c0c030503070c0c05040612 70
    0x30b200f110a484c6505002d41c6008860718000912146441400c894030712082040140c83c1108800001d03002c84c20400131072199845603132142c2c40b901c3c3c00ba141c005402c1082000d40d4181c0c002030510a45012581c0881c0302c498000300014501070f03841c404902e6a01246c1c2240c910b10840e08104018000280528a000501202c4107003104945554000d400d0002030f2284007907804090006100d640e19498282c251604045011880491140c10101c1c01f203209008a02500b0542000500385002a05036841a0740c036444103400001c000c980049e80000070000c0604058454003142460701c801c0c0161809042240c0011800c0a0b0780c400340000c100351b125241800740400c0204115200d80044015006482c4440c3c01a454443da5401c0d84140103100c58800154a4030000056000c510790003403210070315601c000c6c01040e038200d006482c0140c00580c0a00400c000304005150a44104191b42d12030344281c0d1238001907901c540108080341e0541d0072000480113020130b14030a010b59204940000070700b1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 638785314 1250 638784064 638784067
    0x15030e1005040f08030a091709040c1e1d0a1508010506040509010501030203130813030209090d0905060706020f040b0703030e010e0c040b031e060f0f0f0c070812010e01080d05 77
    0x1940d10041d101e41c0083c80640040300100201d980802550001241c0b07230b80014400c0c1c0311001c9247c51488941c00317400c0c16407244d4075081c00c80081601440c1c1c9400c000e06070441c403c14030341081c0801d42e001d054074801415509201071401d2030ba6a60041980c01a205040c02e41e80c942e190484040d0691030183c0200f0f21494060004115596444140c0f5066403404c0c80d0160b00c03901c65580181c48000b07400c0e00201001390204030a1a1071543c0e0042c03400b124021035441d402034a81d5003c0e16121401041c0110000780c0c0e002040c0940d0400d4001803011511900c001441e08128901494203500590042144060006207840516616001700e0703030300c20210b10081001110341e14800e50740746003948085001e6900c0d00c000980030f075400d010a542e05400504408001144200450f07201c110458035007a0321801e8401081900c01e0034155144118005031036001a03440d400242840c1ea0442041101c000208020400302c2480d400e07011340c002c0c070000e24184460350504080504020008009100b0000b0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 638786564 1250 638785314 638785321
    0x4150e0304090f020d0501030b3c04020616060b011214060f01090506040b0403060e0a050714060712030c1202090d08070212240a0c0c030f030615030e1005 68
    0x11007110201c5810706070000c0d8003100340c0d01110180c010403100040603440e100000060010700c0001500c51200c0107400705100c29006c010300c260541c400f10036004400440641e1041484a8841d5500140020520f03402d060748401048540001c40c0d0003103510688a22405203103503048241c402c40b00c07601e038101707101600800425128101c401030169200d13683e12541c110707990340104c0b0076501a00019040940e125102c001a50a56205110484480d850558901c5002d003000c206034807400e0b400700241ca562440c01d80001804503030381d00859480f240400442d800590980e4640d0a00360581d06c0101d010010800d028081804a07075014203264010802c906160795540c0c9048034140d4000403113615140c45002284c992250300010b0380b0300f80300360a150111140d61400b41946000000d0075600307195259115a000d07101c2c10b038056400714400c004041c0000303001c0d1031003008001281c80d0000348240c0d0f4503025007000c4035087c050404640d540d030340705e944040140601510f103a04414107000c07604 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 638787814 1250 638786564 638786591
    0x250e10060507201305040c050d08040308091801121103070b0d020c01021308070e0a1b0e01020109230715020607120e0706030b0f1212180d0b0415 64
    0x4a205001400e00c604025142c08a00d202d00c04040f080741c1c0500390b0781900f6022400300d8010f1005441c10b503040c1048440c00121441c0c12003008110503030014503c0d051504c0e55030740740d440c0e421224105e907016282005c080702c6125204c213b01d009040c0d9a02c007001c000910b0500c21640b012418100b4000d820030b4105201411114081340c2020b20100030060b030b2806648441c80c024000d01140200c0b00c0f0201350001004d43c0c0014507001a187c2d550922000340d02c0b07421510701100c40801002c255051550b400c0b00840b80030b4810600d100d04180004103c00e0000d40e1038800e4424554411020b444c1e801e120300002c00c004101c010050f2483d030500203015820f05001a5a600c2d004003d00200100c80045420100b81c4d0303004141003855a500315441580c0320f42001d40500105000280503094007001c075601440c14421181c000c90904000e4100405288527106807a0320103010154183c519202141898580c007200b102d68030300401500396141018a031601480103400b140310b00182c24a00c0180884 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 638789064 1250 638787814 638787817
    0x9040f0c0206150105120403020f0d03180602160501062309010f0e09160602010c3522060f0501080a03120c27051005040e010b030603250e100605 64
    0x510143c00c09a0940b102c100403141c034882c940c2c4440c0d43d08102002c2c002010340004000c41d000003000162280d43d14854000c0b41181c100905000113580e2102c450008908a60300a000544401c090804401d41c1c41e101c1c40c0c2500c02c19800104001c800a250000d0807010112100d01c1c03403411101003020754903040301c040366851240a010961941d03800441c2a195042101000c4510510004000c1c0703950742c00c0181c0223041000e49070000c5080d02080c400c250107814804407502d81400030303650700c180030040e1025051340020b00c03004c1c40b110303000010f107001401e40614450f0310b40320304004076071300002d11480d03030940b40c0c1079100d42d21580c81400080e00207500176550361140c40344190005030650300f60004981248212441d200021800b40400c0e85202d1041500000c2d68000c4c1e542d522140d06d80301c030131181c610540c800c990007101c1b035100501082c0c0d070f820010b540011004044030004204103001d503060107114400304508000d402d03820401c0d03914580c00b29622400c0d20400800340351500601034060b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 638790314 1250 638789064 638789071
    0xe090103080906070c0e1605040305060a090c0807030b15101202090a0509010b07031713030509060f0307050d05090c0904020904020111030a0906021006030c030210210209040f0c0206 80
    0x7a5031020500e8034040c0c54500a03a818150400d9114001c1c030703030300c4001681380300d41922a850900315070382e00810168019000c0780c0840c3d501600030300c100d5075181c100740010409060202c60b68622801c1c00103203044200f105101840c06400b664080c0c2c1801200d40131031001d0361039140d010702440c0c40390300380484d0000c50760714026404010250b6211032040c0000e940c81820b070001c0b984007030a600042113034613503c030190070002c0c425181d0040550600002c540311410444042242c010070541c0000041e10800140c088441c01402c9282000c07200030203d001a0400c07644a00011004101409840428061180c0100250700a0112980b1402c0030524034100104080d0091000c0320214085902c10a1380d48143c03091401034948802c0d8084c401000d01006103d07640041c4122181c6550010091180204882c1c1c460020b2011501d10f6007800042400b807038841003807240f2045504118450600440c58440d100c07000181e03184030b00300801c0125601710002e10459490062012542070300091116003 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 638791564 1250 638790314 638790323
    0xe0103020603150307030b010806070801030c05240a080403022a0405090f0a0302030a0f090503060604150803040902040f0902031504051506190807110303010621140601020105070e090103 82
    0x6580e642c1c501c0180503080070030f182980510506800005000b9006480e5041c1c48452041c1c40d05c0761210401264801800c0c00098000d000800c0204aa490503605960050241800426440142c03581a81c100e4001c41d0800300898400c1c42040200f40d030512821a80c000020304c49646400d80754112070102c41c0100c40d09005664820103e0300010040001001940001c0c003110390440461a00940f07a801100d50be8010070b01e501d1540a40c3c1c5e0107400b1346420b03940050300604003551303540108409000e40304410b80000340c0241b00800d1004040c4000c0000d04030035000541c3e00c5190004d03c21070a5141d9003c2d03425144144140030ba10b401e007214002d5984001c4802041c3da1b100c280e12410034100c3e0703803500da81c003401c000b80c80722102504c000558010f1311a5200c00c00c9070340e5695030a603030003400014441425001040180b01c9a0302804111030f1501500220702050240c10303440e0821142c0c010010760070703a031420741009419a4240201070f0b1100003454002c101d86181030105a440b50107010050 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 638792814 1250 638791564 638791567
    0xe060601080c16060b121501050402160b0a090b07090509010911090f04230f0912070308100e010303020115050f0a050405092b11060c070618060f020a0305010801060e01030206 77
    0x1840015009903000702d0008201406c03e44200105940d02c401b0b80450240030712111000044c80d16191003503c850340140c0c07058400c0f034031080d0340740c48030014001d1a0072491a99080740001044003206550b10640c0d10351509070313101d410b002c2080015117050b80040340705070511004903010000079064071540c00050303c80e10141e048140000d4007820301d0103032680305813241440f100008c01404880c103000d03800011981a076515503800040d21420140109800141d080003460000b0744074041d210ba00404a211011085465940d18150f840c001c1c0e1059005030f4440304403881350001c00807610f00420040715044065208680031030200f0000344543c5200c1d59031840081d0411a01b4400821988040300003210035201c00d5803100036582012901c8400603180180c1842240b01c0014030b24066030303600c04803030704105056a03200301400a0240c00d105c9412180d942900245507070081d980074414580703015864a03c482001011180141d1155902d81e060400401c040f10f1225042c81c1034903010384685 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 638794064 1250 638792814 638792857
    0x121031407140607050703110a0b04200901061d03010b0f150408030a020703030210200a17090105061203040b070332130603022107030b12010e060601080c 68
    0x40358860102d080c001414010001000101c0354040010914a4032a0310ba289910002c2011584e4a035840103004083c264540081000709141ca10020070404070362041001c0c209080c07000c115404402e920900c04074404249007480408981d458503540031042c0d0080080142c404002420942c040740c086010710004c400e050701c214505000c841c00760112000b180d641e5100740030300035500d0b04184000d40060040c1c030840485070040780a0380645a881000c0c5030034060883c401000c00381d004449030780a10040803000c00200303030415240c0d0311484110000080f10700d000740a20840d1138840d101c0083c3c0d5081003006002100d80c050680d01c02580500c0c01c28050108a0b9045400c0416400c2c0340d01c54858000700b031030981426500600103100c40502c0a16144d0756070805505a010f00300040b000340c031a100d5042403035600c0d401d000703503c44070502c2c01107080741003a0040740e07040072030110100103651102004100b41c10200b08141d00301b0003e1914804a180400003002c2034000e1100c031101029481d0300f83c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 638795314 1250 638794064 638794073
    0x2030703060f140103140906011e0e040f0b1b0f030402041805030d0b010905060a23160b06100210090302150903090316081018050d080121031407 64
    0x1000500014202031038000e88900c0070b4603d07000000b107954002130806645142c2400048403280c0200d1038900241840c4e420318484441040181c05400b000281d41c03180003820000b002042030040703010382500b030742030402800e18514810004011014001c1c05058a456048258040320220600d000403203440e62038510024003c2e0002407070140212824803100018803901200030540406004400c100d0080c1c01401545e0201c403900c2443d61040040c082c401c4500e005184040c0c251280b000400391040300540c41003450303040001c0c40410803402c6940c940c2000b043ea1892a0490402c90307001d8020040000001e5441c80140310402c459501c4e03030030080401d4000c010b0484000c0c001002080b1510301101c00b95941c0d000002814464030503c2c10003420070300c110361034400352400c40700036008070b050300d14100000d4242040c900c0204c0d191440d203d400b00c1d0043c0081d4100355801d43c0c50302c40325450401c2d1201c2d210010800080001300c89140070740025045450324440540c02c090031911003038642407 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 638796564 1250 638795314 638795321
    0x90a03030e040e010207080c0d02061312182925030c021008070e0f090c0f040911070b010f14010e01020102120702011d15060108040f1a190b100302030703 68
    0xc2c03003111136002041010401c040880a007601c1040700040b20090000c041c03089948801c161880b003010010740d890301001c14070f00c14548007010100d082103181c84130700c1803144400a01951091640311140382103060141c2d030300c401c440b4003000b000d8103240c2400701c0d07180480110500c2415100d140c0c51401c210200b050702803030040d0100c0750000c1c078450390802200307406000e004084170080b00180607088400d05501d8060341104800501501070002580c0e00c450841560340000c0c4e0b20b44d41c5c4103040c030000030844210300a100000412102c200d031140d1191402c1104500c040e000b40a101c000c03114184441c5954400d0704250341c00901c1c10840301d5210200503402881601244403510140d074041108240c0c0540021184280d4907280071845040904030944905146107448580310074400031407201d43c41000d03660f80040c011030100540710b28a6540800300094004042040d141a204100744101144c0b11012414104281400300b000441c001801545206610781d041c1035020010842c202c1c413a62 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 638797814 1250 638796564 638796581
    0x9010c050a03080a05160f18080609011416140f0403060510050307141c1a28020403080d0504060605180a050610090b3405070506090a03030e04 63
    0x2081e9400452541030050240300100c4030b01483c0e41c1424081550b001071754202c00c403503820750340e5903c040c200001d100b00c0b0a00507601116040c240c6000c40402e036074405000c00c6000e03003140d0740001030442c02c40c80d02d88800f01008020301082c1d868034900085454100c206888215110307200a591590701c1030012640303016503000a80902c2c40c107010062190034070014102560422000ca8811f565210080c19401e41c08a0117103810207025200c7d080520390805007140c03c58818200305003041c1c02002050000441201d041450552a034400f00d0703501d85a54050706001400d2005518041c11a141c81d039241c851015100c2100342e030f4600080600080380d1210000e4040142036254152843d410a294940305844030220189094041501171070300f02c00c004680040358031080d040519242c01101131760020429030944604104400c0801d035201d1900c2d454000c00720b8480c011511482c1041841d20f500c1e9003000d405510100132030009551801980740860742d151404010402e2800040b40241c020350 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 638799064 1250 638797814 638797823
    0x20d020f0304060903031b0504050609040605120d0f1707051b011e0f06031101122316090b03011503090501020a030c1e0e060705210919050a0b09010c 66
    0x4002c1c0000c0010315005070060034000d907402d02034400c80800c0318568a803044403510100324104020412801c018024110300600108001011651540807865001484820036aaa088481180310b62a0060840c500c0180a89080c000c1c02e0222070301e5200090028180400b482400b00d40d892014245507580302821841320000d0066400c40c050f2044409009281428a41c0c140300056007032001ca03224140c1200d0304060030007545104400103552403002290b170b0a100a4072069580c1f0003220802e400109110790f000114451300d000c2d940b40034159100c82d0078904002001710304100380c1819000780c038151003032442c2c054064001210117a000b4107110b40003c1080d4001702d10b0300809500f5a001440c1d054090302d980c03d29180c80004514414540340e0b41c8804901800c01c80303075180c14507130007800000e482581250380d000740355846071500340352803240032000560014000c1194100008450a05140301a00407501403e080000309120a14003442601500220b44904a684583c2003010b415030407 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 638800314 1250 638799064 638799067
    0x4030c050f0d0914060f090409030c0b04050c01080601020102130512160b0c0d090806041502160f050f0a0b0f07030219031a0a030201051e0f120a180302060406020d020f 74
    0x1c51501603c204098418030164110400c440310031800c01004445034640c080072450300d410a414104001450303d02801d03020041030f10352240001d22523081040c05a40100014000941d030840014001100200664110f90051200e548059100000710303060b03500490329800303404030307040400c1e00d000018011404410f5020000040d403000c49002046a080180706442c4218000c05081e240d4160320311030022651f003d41c000070040749507068078146245a100000d486c12001e401101c86c1c814141d1800c1d2400c01c000619a400c1000802c03a280c4504020310140107480001e0b00c404d0f0031100014801d00404030700c040001c4040b84a5411101a900540d0b140d228503148000010001c21a20440fa1280c00b441c0c0e229a1552030218500c3d4100c1e903059480915080d40000702e00e102c90743c0b002010800c4c450511072116050524005403500e0103034231003051058a843c107641015207904c803085c900d600380085110b0000c00c0d40031440c558040d80142001d070340c41d401585000000c0c45421294004c8080 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 638801564 1250 638800314 638800333
    0x519021f02090901050d0b0420120606030d080606090d2306040c09152d140109050604031a0907030b0705030105030d090828050304090213090204030b04030c050f 71
    0x455409400c25190954182c0c06a07170300c81c028003c3c45901311401038a22520980000e00051414100c0c89001c00c643c064003070b40b00d0785000455030b0405401c5002215821010410002d0b00b82042031000070100c40c07900102038200300004c94a40c3c0324158031039000d0300c03040b1581000e020011401000d41481c181c14820710743c030801c60351501d50b203041e10708585d41103c01c0000940704e11a40510702c0d20542032419484d08601e0306040d182181c411140c04850b5012554440d44c1d040d0710002c24000a280c0401070544115001000600c01119034010601c240c030140800d02c04140d40c03402034851190b021690302001d840741070103589400c0040d8401881d002116040150740e0380d124020750304a0301e054049440c1c8401c411025500050a030041040681c007100c2d8184844150071501d5000b992822907070225204a03840c0c0b5800c40e80560000448580c00194440302801c0c81000d0400038041042c0450171f103415540e5802d1511000341024041080c017461240500c4030038070070400c42454860803a0080e00 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 638802814 1250 638801564 638801623
    0x301080601080f0d0f0c030c0f050f070b070b04120c0f0c03060b010c05060c0921010606140406020c060f04120b040b07030b01141e0c070e0a0c051902 66
    0x1202401806280d000da83e400d07019080e0002103800f80e01d07840c0e45505205c8814200300f298150820041542084905040079000c07035005c1c514480300c0390007071014003a10144219024a443c140d03500c0100d01110400c44c0101040743c0c41c0c01a0b4000b80e1102003030b003050075a080c01311461010007901a05813205151064100030400b00060200c038450704050269035100c00c015980003c61000160881c1c100c1000039119a0307500004081010b002400310000405603c4613014601c813160010040c1d80d942c082c00d2000710b801204a400440b00c04280f40d281a080490003505c444083e0300381e60003401c01080b20b50890702c1c00d100313860181c600d08850401041e21400e120580341e00951f02518084212400309494600c0382c02603240f90101a1071b030300c100c000c181c00014882d80c00074500418892482094440c2c0c051100001d000c07901044005103112410616000441d04015000c400014a4840e2401c13841740c0003001e45101032030031a600d4030711400c3c070801030781400684a440c0c1102c00038902c80b00c0c908c5 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 638804064 1250 638802814 638802823
    0x1c05070c1806060c08031612020a02061807080d0e0102070b0c0a03080f09031b1c05040305010c08100314010605130f0f0509031b15070503070e01020c33030108 70
    0x8040d40007050100954501058501c0d003100a0007400d008410000684580c003001e41c00d0307842103803520745501c00c08411055401244c1200b044100160480f00a000d08114111001e0002507684c402810000303240c007080a81d61100d00301e403941800540340c210303801c903802400040e0060813a0185550b45807003e188080d1206400d80048022845550110b003180c0600f90031103104c3d885550095240c003541c1c41c41d90403a40e100c250104424800c60410501c18041c11302c4080035100151a07003511103046d4503000c0e00b5510302e0a800700420404070100040141110b03280340c00c036034008004103038500b00c44444074050300303950300701c41d801c20350564100b44c692850703911810b0000b1a12504202d9009511a003c0c2590002e0395191915801401281c5050545803c0b418101520000701d42001581c150083d100c00f0088400c600494400300400c450755400040c5120b135140301348064900302a0322400500b280b0b009080e4868a101224110015080c44482d12052542408130980e160340e541c05000782da6 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 638805314 1250 638804064 638804099
    0x4021c0503071110020d080a0b0406030501181205070209012d0b1e0304122f010507110a1502030a02040806090a060b0109240c02060304051e0309031c05070c 69
    0x2402d02c102200089440420406d5041b0880d070f442a007951101d211501c0541003030100a5805aa241d10010003c1d109100714207120400ea02100040001f60406140c0804000d80d80c4017070000400418005a032070300c0603035042d203100c01c0700101d100c54041b101d070b64544003201a6210310070401d02c0104541c00140e0140008000084141400070404400103402c1e0200b520001c00b06000c0310701c010400750040440c2007600740d000c100584400b0317032502c0c0d04401d400410301d01451030b55500c0074011060303402009440d00d18981c00090140790095a00d002843c3c901e00764174910180c3c04000316881000f5601110002c000f503804603100380c245006802c0e103554100004030342c0203142682c4440194002c011213012104540d194070038920300c0208140c501131a900300102040a030100c0c2c500140d903081e000e94007441c0624000d018942d02e0326000c810800000c020350410364414800ca43d0260b0340041d000c0380485075071210f842c000406030380644590050b801e00604003090345a0100720426409003c0f0711 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 638806564 1250 638805314 638805319
    0x3060f0504020408030d050405010e030f0414121009150e07170106151805040c03050a0b0102070b270901030803040302210a0e0f09010b0a02060901110304021c05030711 74
    0x10219030318010441284524810440c41e50802d020001d0000d0b01c0c0c0d40010f40c4240a0b0001045050100e4803441c110b5222600000c40e9282c04981489421a07045c0e152800300020b4400001001748413940c59500c4c3d41a0b4044840c094075103003040100070a0441c8400e960040680038170103161151201502e4090600858031405044a08007207640e03014010242102d00780d92601c0d440100d42c0d0022600c00b803044a0184d50500750340f10008080d1154420b50ba1506a681e800161030b04003000741c02d0030799003286c034158110362240c081400466142e400321600c0140c220031850141c4140444102e854610350b071442e5021041d04000002c0c405058003c0d44101e10a038203444881101c4e211002d00007080c0111540c00240502401c56440e028420000010a001f0401042802d00780001a4410001d03003008111075000728080b810380703804020700e64210034100b009110001040d040d078031031400010400713886054010780300070380c403403400055091298110050360364a0801c0c0c2490555200b02144050 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 638807814 1250 638806564 638806589
    0x1303051e15060d030f05120a0506192106060803030c03040b0124030e030c0109030e0123031506040306020a05130816091d0327120304120f02030a030306 67
    0x1500010100c0c00244282c9004051012220007901d044076500448030804041c40b00420201c4441c0082892175031088800000c08900d5140c51400c0c0590544542c0419200c00f0480c10140551982c3c42c10600c0c00c8181811035a40034880317414003c01918840d441070305140800802e0101c03800c40131b001984140d00814203610281d0740c7d1000c1191198100c0004507204022108140740c06100e0740101c503c1004050440c0e007040c01100c1e010707003100c203c0c210843c0400d03050070903200256000380f05981c5c040c40115021034204400380302c80b42c0c50b20000b480b00600f45041070903079016070f0f600383c2543d02560300324401719211008680c0182503580302e01c00b018107440010704005855071000940b440c015024a0310b41c160300e841d00c100362000e4507403140c1d803805040540c540884113040130000361813030010f0310990280001a90311100941140300802a016820100140001d084000202c0b0100d858a03070b032030741509405040040e00000c400304025458014429103d080c0b590580000060b20440382414 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 638809064 1250 638807814 638807833
    0x4050615060412050703140a03170c07120c020307091a040b0301061a030103050c060c0a06090c05120709060603060602030403030804030e06120a05090105060a051c12020715030b090604021303051e 86
    0xaa034a0217090b4008001800129445c01c00038243e91552f500840442c1989042000350b948003007034280d00c44e40c0b040020b000c03183c2000a51504100020090007909000c206441010025120030010b03c040700317001c2c945640f5a54001d8909501003001804030812030b0840c1d4441c840102c0d02a8428030050341e0620030740d00d0f64000303860208111654660000020400c92009a548901812024500781c4002c140e841d00081c00761540d00b54003450400c094090215541031048030000c480301c68100a0406182c0403007030100f81d400204441c103494141c1010780c1103503920320302102c5044d20119082e40184001c205111124040710310315000700b60407101440696901d8900c0f5080703032411501c03140d01c00790383d603010001803c01d07034200003c4910180400590f0112626071045181c40d5103100f10042e0f001e820100710320300c1011450540c4808a180a105554001c80080d0420f640684241c1c81964005100780f00103c000c0c1e1208021a071003002d8800d0703452003021b02c00c0d4449421010641074001d003042e9 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 638810314 1250 638809064 638809103
    0x7090c03020a2a02040c050d060e060f0d140703030309060c0810150e0405070f02060c0702130b03030c070801020307020c1909050c0c100605130504050615060412050703 74
    0xd5501c41c1c030b00d40c0d440e2084940d205140b01440203082440c00b032102621586900562561b009600d050b05058580c80d588898407410503040392a03590201c16102c410f5801d0200325610080030707241c45d51049928242c910038604060003450751400040c1214820a4800010560560402000c29003d0903080164007034a203001e5900320783c01c55001b2140a0104424010b80f90002031042c000c164510b841100c50f0400c10101c0c08440064903904007003003040308140601641040290b50016003655643c0c00c20102e6404140e00844802e4201d025507200c001108040c0c40420981e23516a174000b04840505a17106441d41c002d50040d110480180203030760341d035490b50402d641640b035141d52400c45000994030744010940144009062158202e00802416542003420024100d10000782c2800052982c5024108520249625030700a40c041c00c00c0108804144003240e03803035001004d10030f01422034002c4800501c6c54401d030317000454000c11070083c600910000254810541c0d108021416200e002d2000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 638811564 1250 638810314 638810317
    0x190303090f06080f0c0a020c0409200618100e0d06201e0c01061728050a0210050c0d022a1509010c0f0302010902010e2407050a0c0807090c0302 63
    0x5440d09841c110070041107021140c1e1004184580c5148192028022310000007000d55125482c00c0d0740c0b4840c40c03440d00c9501c0d0411810140001011501d07030b071405107900d01044042002c4d4030031a00ca403042c44060044c0c00e00803581c40b180d12100401805480308946480d80c0100603c03000c81d03a5016040d40150005c64134a001c540c0703e6200c80c4081c41500c014030150404941c040b0211903038a54890750005400c4041d104540341ba4142030014108125035101134040045418420000d651501c50001003c60b0011410809090701910142d0b00d2040311034081c0c81c148101c9030040c03454071592000410b19580030442104144800074050511080b0310100c50766800c1420240b83c0c0401d04100304a000c00c0302100414045006040083e01540f117916101c0501035480026070140c1d4694040031704543e44890300a030921000c0302e0420170703010f010384c140300c41d00e6074403d20750051140001c007070061180030086c00400315800b070148005a07440c2c1c203402d42c42d01110300c10011030f142402800d0030036a01900 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 638812814 1250 638811564 638811571
    0xc1209020a0909200915040f060f08150702030723150a06030b010f0503030a08282319021803060a0b010207080a0803130609060608011e050405030d0b190303090f0608 73
    0x9031540440006041100401b900190442c0090f80c81304000ac042a907100f80380c00602d0050047e0102400b001540c0044030f100512480464008108503000160480482c6460103007030311411000c8007021036100d1806a1101e4100641905003040124040080d0000c406a86c420240e14400741d80c2c0c0c2d0701a141030411401000c0e415003081c481d40d6000d92241c5110303035200c100f283c0910f11420301c04000d503807038110f590070000d000340c0c0360402821500d9040040110790003046240082d145024004008010210040080440d4001409101c2c00a2140c40c1c50f00009004041c1c0f42281020a040d2000300519048103002d805140300000300d40001090ba0350040d90000922481c5a0324501e03840e25040100804948050f9200c8808020032100d04c201e2001c0d082d10030002600031112801130800009030341044038094244070400c00010004000c1c0c030f11054086001047d206001800181c00035a40c0760b0390071000034048400405d1581c4107591404503180c003520100540d8070743c0011140307030302c084 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 638814064 1250 638812814 638812831
    0x50612040303020304020102070f060c03030e0303041a130c0b030f0c07030e0f0111011b1b0201140a051c09031d090711010f0e010902130c1209020a09092009 69
    0x4800090110340030303400071076000f881481911032003601e078545028082175035049040000c0003200b84404154062007100b140c2c0504800079410341c41c140d52106800700d10040b104202003140300103d107440c0e9010111001c455408400d5030651600c8052100e4281c10848100104040d481d020400d480000f000300d80380c035038040c1e40c0c100380112241c040c810710002a590b070138100080000012404d42c002e110710100c81a039140700004142d0300c004010642002e81c984807207070f01366849450b0010703038000040200102e602c4100c03d444612004013540c0901032400c540c0c1c103041700c500a0810050066101141e41c900c241c0301c0000418103943d105001c1c4441c0341005401000c035001152200b0b0164481e5420341840500110b00701c02003103c16001d864280c440000c10307a440340c8010003189428035407070428038504501000340f01c10050740204a0170b0a200c0101c2001c0c2e8420120041d501d4002d07148000c6c002c0070b2024007802c3c3c01460a01079400e440c405d026142010000c8680041c0b40803000c240c02070040 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 638815314 1250 638814064 638814097
    0x1f02071b060c0803130807030c050f030a0f11070504061509060e0d030c050a060e0c0a0e07141e0f030f0604050c180d050d090f1a040312052b060506 65
    0x95980f210115400942040a9003020701410000214020b00070a46248a50341c0c28100d08134900d8030620b08035150109601c03542060040100040e801000801d00055a181c205810344a0b0023405050200d9600540d41080c14040d01080e0078502d02440020103850b0707a16060b90640d41c13401115002c542d10840c5a009110100c7c42c408644a41c04000f06203000f00141c070304820003507585000319401841c0c66440760b0003219505041d4940350b80c1400003000713106200003075490050001010b4660f00c030f12a80d403508020403500e08282c0c4c001d401e461803001081d04565981540f12340881e5940003154560402074080700003e90b107003000d000e224094070201d1191800d224501c028440c0800f004c001c9681c000d000914800d020550802089000300c5a54a60386040e505140c02411200501e4000d0809000580c0703400070000e1440c02150216034010f01c8007003200b24950411605840740d0740c90079260110780d0040c401000340c240d2400c04110f1340c441081121682e52000d01425015440c41c800405c0361 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 638816564 1250 638815314 638815337
    0x8030f220b04053a020f030409110d1a0a05011b0b0a020705190201020f1c05031009050f010503011d0307110609060408010506031005040b0412021f02071b06 69
    0x304141c01a000740c0700780700f50303541106481c503801010246003510b25002c0103507801c14855000781000c4000c0750006031020b0211740501c5c041107543c03846180b003070712061079170b880b010380b50f5821201c01d5030f1042c40e001d08140072030501c5140c03500c89004104089449919020000a1a980904c1e03030030114140400309040621840c0d00d5003801940020301040c00503400b0052800011000e102c0d400d40e02031200012401e000c11400024030300f100303070307243d01203213a001200c2488020346209600d441c007561407605135039079900c0c0000e2106c00070303107580402e004908003002d00640c030a034400298140e9400350002c104002c0442a42500c01e10400c1400050703410401c250004910791400c4032800c15400f60a1603e40003148010850341d138405e52007400035944d10b8081c04040d1034148404c00d01410100400c3c070081c04c03d601c682400304805400207011028178143c1c40f00650081c0304030444103150100301503c41c1008000b92000c0d40c042607048903c03242002c2d85d691039004a420700c4c0140c038490343d15201c0152 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 638817814 1250 638816564 638816573
    0x402151303110a030f060b030f0f03040f0f0503071503020f030f0727050d111903140610050108100512030927011203020f011e0506030615060d0b0a0308030f22 70
    0x4a407c8000341c15004509103810521010894101d000748403000440c1c2e16458038250204190031500054002070700b41904100c0c03913074002850000d450090420030311060000405030001e10868500140c9000080b08004000900d29203840c07058000e03444030110a01080c1d0040002e20a400c1184040e45211034148060305068840b4003040d485a46140c84091010000078500380303900c1d60707118000030803400900c104484500b160349011013000040c041403c0c04003510459500600815041104a2002809012110500e0741c02440d01500180c0c10b01c0b00144090b0b00e0ba4012103985004241c03100034075014100c9155903000070342c0e0019007100940d0030b0002c0403280320940700c020342c210b12806c031882c110428280300d0307411810f141c040310030a040c4000c0752640c240c40000b01054442d030040020030030780100039000f06000d6541100d4041c0d91307902504003072000700010461980c21074003a03c0701000b00b007441801075004407591464010582c0e5011750300d00405050b130703145102408842c0c40354000503 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 638819064 1250 638817814 638817821
    0x200601120201020a0c080d11030403030507080304021f0e030c031507081008060f06040c11060f090109050a1b38041509060807020102090f090402151303110a030f06 72
    0x19071051060340c07820032070b0b610f401d140301d060341d00700f40700340d400044c0025a00e5401400d541c011700f5030794001d181000d01c0c50f00d000d009402185030140c0814000070004085545544ea54940744e483e91414805025401c0d17402001ca000640c01c46029204600301c0207064030700020300c3c02032501600300d903017683c1e80c4100003114010809080c01d141d0a0042c440425128824404035100d5180c1290100507840d007181000143d41100040c3c2050001c00016640040c0f001b05040c3e51201200500e0401621908552401014011001b0f0281e00032100000204010a00340800095180311500c0c8440e0b100c02e492403400301d040941d07000d05148801800345c40c2c1e105198480080e080c00810508069841c20710441c034000300349a420001d218120113025140e04401401c1c0c100050788021410702203a0710105000d244031200301d9100b00c0c100d400250031503480200d04914280c0a0200589901900000c40079400e042e02040340d03139600102d00c40301300f070910000301030031650440f5240b407500340031703031a858004c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 638820314 1250 638819064 638819099
    0x61303140118060506011205161404150c02091b07060f060e0c09010207060e010e01050c010204210b0901110306010e0a0b040b0d050114010c020118050a15200601 71
    0x541d500c031101c4091041d0a2a0300c010150700400c00882c0302d00d804400100701c580903404030004070b8601410f21080f43c100500c81001561755080c00c010b9107031600f030301c0f02c4540525844510750f00b603a000080c038000d9011400396840792080d94003c007035440d4032500242e00c22000c1404880c065081c000d201c0071451540040d69000101540041c9854580300c1031015010202e481000c0394034001401c0380156410864480207014a282014059088500080588003440c071450704203c0e0208030304122410070740c1110014002586800e044455904000c01444055103013507a04150034000140c0340349040c014034020390941d00f00d091540e40e8510042d14882021300440d50800d825080100381c0c2806080200702402e261f4203860b0303e075400c000852040d920141c02080140c0c2c0c2c6000c00440d16604060b800401e594242000d194104803000341e080458000d9021941c003191041c00003540c0d400082340c08940e501c0c95030303401c045071044107907064406507001d2100c8190390090300100880e03504805c64040 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 638821564 1250 638820314 638820353
    0x105090114090612010510021c051c02040f2904090504050312010306271e24090b0108032d0f070803070f0c0b0c0d0e010e0f0c061303 59
    0x800b00702d0030205070b80e600aa030408054000c018014049460940121003500c00240300900540c1c02034611004482c1c801440c0001303121006c54000103089102000916080408038119200c070385d140e860002000c007a2003101080c84522201e000e0720445002640380c10742c1640032052402c0d14001000c0d008103002881a50a4003040c46110410b40400098900031030080c540403441640205444c113410700e0b00f00160700c030628100040320004074100981107040301100c1450081090724140042040c5200010406801141c8c041050583c6680e1042d01ea01d8003820302c5440680e2248091070303503440713501e03040e0b819582d0303907400f14410611254040002c204260308087c24a240c00d1106682a00b1205c001c4400c118040200401568820842e44440c0010b10744454514000d4507454007041c80039080034a0b0040004440b050346100d03410001081030840700070454031001141c210344a44042c41050714078012240c41d15494540030040d160325041c180602d000f80343c9141c5c3e901c0b140c8689064a0070 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 638822814 1250 638821564 638821567
    0x60f0601030609090308071202040f0b09030f06160212090913020604090c0509180c030a020304061d030a030b031b010302091915030e280c0f08010e0f010b0105090114 73
    0x80c0380b201c5004c0d480d0307540d1181d120840c0d40e0800400181102868840d02c40c1417510601c810024200b841400321b08481c24549500c0e920b040440109042421841030010f60348070b84024400504000310903034007440e4032036090350a91401c06500702c425201d00a03855502403a40c00104031619600d41913420030920042c421860a590350010605884101007041c0c0403881c042049101403c080e00c64041085c61a440011a441d280310261400e0002400f802c004550220008040108582c071808000320102d40c0c0100040a40341c1d250394a6108002b0b0314006403c4c0340d01881142000150032605112445a46990440d10f600440080d0048c500a0b43d00003911a40540d903d0b41c00040807000d800981280d02c48020085805420f4031244a1104c04075403090b5096244d048120210003181c134450344154030381d401c26003803035441c601c1c00d60040c02c80d000700302c9000100c00c4070540c010f81c0000c039510207491004402c40707240e600b00d03a01754000902041c000c000c140354640c1306944212100940303c0d10325 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 638824064 1250 638822814 638822819
    0x2030415052209020406180b040e18031801030c0206150d03020c04110a11070b0f031302091503010b030705100806030319083405030c220323060f06010306 68
    0x99034844603900a4064035130006041c080281d00c00c03010403081c135000d102214030700c0c585030910a15200e1880b801026a440a0126820174951801c400c02e220341c032011a52a9032603148000c1c400c1c0386104c00c181c0402d1401502c440c0060000c16070b035100781415070b10034601c1d0f40c10a05204c44030541c21000c404601941c030090806075680e201c4e454001c004c4141c065240c8c0d00c0c991028101e2840e200342052554088982081524012011548035040300d00c8103940700c1c1c5903c2018203d2841c070a00003540441001c0802c0744043d000710591289180c110024001d00044505054490070140580c9400009103141c0001c410302035800240c2204000d0f0440e13140c41d00c51265600302130310004102000609a00c00c1c03220b009030002c1824040c002c5a40f02d02540702e011401910a0000440200b0134450048000f5034a00c3d00fa000399420005840481076194003000e20421010049000840e041ca05822140c402e1104902c1d5601003020710b5002040541c17540b010a480d030100081c0818101f544980c0013 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 638825314 1250 638824064 638824117
    0xe041514040e070b130b030f010603201b07060c02090a0c0e0d0f1502250206041805100803032a07020d030e04050718060309060b0306040305040e070203041505 70
    0x1803d0080c01c0c0b0102041d220500382c071030134001a14030340c0004d40002090041c4003405444180450440d003044c01c00282c4010000884400c0b0050611344058144001c42e0680a42c1540410190081c07266020345035059115601910368019043c80079403c810140300050b50f140242d0b2041c001c40030903080400d44411820001014002d0700c0900300d80d100611100081001103001e094441c41000000650070011240b5a40c01d54440841056080ca0150f8440c0000d40d02c03048210741c050100c1d0460b01038100c00c9020010094001590408203e0880c139000042c840404400d9900030036001c45003030061030030f113900000314011014111031041800c002d10401683c0700068805114425114040400249810002150402803048040c0001c0c807804081e807101c0a01d14005503540d9080000f11000c0d41c0c100907000305074500c001a0544070b428180000e05802001400448010003001a440ea0b0750710422070316402103114131003c0c0031100302c05054041c022401b0b04032041c100c0b008038002d140c4c07800c1d0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 638826564 1250 638825314 638825323
    0x31b010902040c0210050f040803041203060b1306080c03060904021002011803030c0806010f080109150f030f050d05090a060f0c02031c09091a0d020105040801020f0306010e041514040e 81
    0x46980564817000b01c1701400d4002c2e024050707119407201d42c16080d920303160300c40c004c03a4440280b0041000c803e024031680c1c4103000343e110300090288541c1040d124030142d2461038200186014680102e41c01000040751203180c0d004072440341c8030160814081d9119507091242e06008c40c1102e030290754072544104070494600d2584c03000c0310300907a000301d0341d5650840040c0000300c0240000d4100b00b8851074107001103802204140c11980041e4000034455407011802102e00510b801044900780c6501000083c0180d019000541300d01a00a440000a5010081c3c446100c3c203030380c013038000c1158041040210702a2003000f81007550b9003042c80b00549980e002a040492824035010b00241070101c40c0c038465030114449004d0300321100100648204417108924642d04c110105216100c8081c018086903c02c909540c01840118000d645802039213661124580086402a0008600785902000740c81d06018525a6941c103c1c1c06080007410483c0c02700e4010303005a070881d08680c03030714900c0103000010407 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 638827814 1250 638826564 638826581
    0x81e04080307110303210103140f0604020f0d0f0803010e010503031e031518180f0304140d0b0f0108010c050703050d0f060506042607080d181502060402030d080702031b01090204 78
    0x106c43e9a581180361610b0502d1305158510a19401128100388004000507520340041c0c04030390a800d8502d078440005c2c4440701e0404000c2c60312010180160800000101442c140d45114070287c025070b0300c510902d0354034010f60104502c4d00c050000380b450813141410040d9044049041c2c0440302c902c11802186d4100d2060781c4040c8a82100ca08208240010108104031909450090240300000c4152507a9034001c42c0901661704001c5206c50040b65500c0c0c243c1502164801c86034281c5151509540080b800c09200d901c070b1075424410f681d4002841501100d10311503058440d142491850f504100040011032035601149075629000301c2c0c15512140a44003e01e03116282c4000c0d1500ca54071205961010b04031750004c3da03c442424000e807440407400c40981d44592030118009100300504a0440313000e5030000740d4100d128050840d00300d9011840702d00c80c900030b80c12643e8401403440200c0e0010030484013440160000c0c4003503180038041c002e60502c0fa15103040003040701d60070358002804880610 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 638829064 1250 638827814 638827867
    0x10050409080a03050601210b040605040c2706090333020403110406030f030c15050a14061219061d0a021e01050a050c0a050a081e04080307110303 64
    0x4503560002ea6070500580e039100c0c80a00c1e2401a03038801050002c0e6a0b1b0940040007283c0c2d480d66a400501d49687d40400c000300300042c02840400140304000d07040b881e091090640c034500b07a244103e62104a00318850845031f00f65520103d0340c0c034549506094541c54030501d841c2c50021405111184610003041189140c020801691a45186040d529007005015118042c0307040079001c1001c1589521000304141d01424101078810b45031508580310605081d140d580145014240904400c0c50f41c00501d0729000b000c08440d4680360482080100c80c04804e07000d0f02c5501200b41d200501c107200f5030b80c0d90824412a008a10030304141480000b070900d441d00d443c0d00341c4c030240483c0c0662406000d1020b0005811418140401c1c001c00000d00301c0c42501007217818400001410629014200980f10b40c55400a0a44100c18024500508140c0c009041140224a001c1d0400308101e581c008072000c40300080011881c0082c0c0340e440c1401080382da04990b0785404107101030706103141c13042052400d98900 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 638830314 1250 638829064 638829067
    0xb031507080916050d0204052211041d06160903060935160c05041407020c0f0a14041112040302071202060306010804230a050d03050f0c031005040908 66
    0x51600786203410000f00308000801503181003089103455100f004c404468040d5004241076440c40501c06105150301d48030003881f04250812414428400d59101341903008813001e0206180145410143c5448020a20404d410070310201c1d00341500ca5990342640c5105040500c61240c0c0c0e904c4060445010038070554244645020a4040c0e0800f40c6603e0300500c038201c3c410300b9144003030420440d14040c050300c01012301c605024080510103001500001410018014810506071856410744480c050b10500007504c9009425201e502e0004012141c481c0e015001c482100d2400c206001d1301b00b546040700c0d4015684110040011000100070020500341c0140280355080030b14000380380c0740c242d82c007004940701040c1c07041e0016912441100c4d0040d40c00d10707149060b51944c0c00c10a9115000d025106000030500303031100118070020908115050080c1c0941d142400084400d40036101c0803180d5400c03020500c00026808a130250280d50404840420341c03d0181d20b460100301105c0e290f84054500140 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 638831564 1250 638830314 638830321
    0x4081209071e05040510061d0307150203130f080d05090d0501092003030f03010e070201321f05012727060807050111151e07050403050a02040b03150708 67
    0x40a01415402c000d89868402c002c47c1342c07910041c41c0400301d00954231207642007403070124513980c1042204090708450780d00145508005001940d00c0d40404080d0350554516600014240800801c000071203a103900509070030000c0800480d010fa210000e026132000544e00f1160204a0921030050041d206001b1071100d00b40e0011007064070380c9030880082c4254005c1101c010314010322070949045134032040b500f0b6001e8545030300a9002d070190045115a01d12945040084444000380111784100c0314511440d450302d41d44002c1c6d003c140008020800307001c0c12401000307207510405c070704404898228005040c24041039070701d80714108244d002301d86c90704000c0b070b107801d003028000c03c2c0e0700d0411500c0204101051030a01141e0303c40340c29218850500c21150388031450b01d034003840b05406901180d16291007900d400c040e07020040e004102c0d40f600b41620741e8001004e003030043e001c0301c0a40750448000c0806240310790030400a0500c3d0726000b07815000b5040058802c0c02940000d81c002d01241d19130380014075 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 638832814 1250 638831564 638831569
    0x320091309080a1110050a020a0f030b06040b0f0d020301090609110a172a0a0e09010f030b1510031d0c0607120512010f0e0106030504081209071e05 65
    0x803003044580003145030412000000740c0550459035050034504110801c0e031140034566041c05088010000494109001c00950403050b45c000c01d1002c0c21a140c0c100c000c030090008070221380e003104a01e604858100024007000d10201c01030400c0d07481920ba81d901d000c048880400907a0800e03400080c180b919180309008010b56030141c41001c00c0300d10061818004040d0f802030110104048050b0051034400100b050300c842801510066411585540044460458480ca840c0d2001103507800003840c014000003030f0702d020348000b4101c86468600426040c1541c48001c04004e000e07000d1200848600c01d112200e4036a03414200c40490303ea00c001601900041c200c84060b0b14004918001c1e0300500d1400751995114000d5410090b08403407040c0e901c841c0c009040c0d585101d80340720804080310b03072070001032841c0e5090104800e5550226449a042e607840300c00703805a030003d603001004200180021001002c4044034a07620402140482e40c91655400d545c040404a9000c180703082c0114810510050 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 638834064 1250 638832814 638832829
    0xb0c010b1203090f06071a070311040e06030d030501061202090303120405010207110f0109030303020714011b0f0807270504050a021e030f160e210f2b032009 69
    0x5841954175a1510205940d001f0680d000c0c41c60f40d8141c10140c1011851080c0300e5400a103c0c0303001c800301c1540c0d8540352010800b441d881101c100384284210740c101c4141c2c40c07003030051504890b007503102e5481640c00c50051901a40003030441c0d9400d880180311101400901030711803802136005400060781d90745a41050b180d1038072070a1f03040340526501c01c0d00000716640100b405080341e406150050700c40c0c455191200030b00448030301c661050360070a00180c91501c400421981d01243e0798030b44400c0241740f18070598159070112031100100e02d4070b00e42040c4410400c0800c18215684807011060140c80d140000c04a034000d6800131071403a80400d00c1c9d07298842d4030703101042e440d881c1003810b421842d0040081c07980702d50040c1082c0304199168080888035000d1000348001c201c005003848030901055000307c030000741c5685424003600c070f0319800c001d10b042e0125030201032860882031551450345866600030014041e8201e0320815039544174410700240c1004481a074030750034400c030f1a44c503a100c20802c8460f = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 638835314 1250 638834064 638834089
    0x12120609060d081c0e0706030c0f1d060318060c19020a02030712051c0f0e09070c060c020c0d0c09050c0a090e0613140a0e0c0306010b0c010b120309 65
    0x107810058052001c6861582501c40080c000415240c1c03032110340070711310301038031044861025601c10000081026509a0080f0500321410782e02d4071082c5802d203030115400c0003813480120005a4058140506080c00802560b1000d031103040c0148030780805201d1841c01c0402c643d4545c0d1035001090354003030f885103100c103c0010301283c4020000305a042d0002611000076114403440e44d0102c00c0f141d0b040000c107100c40d5804000e84204440580e01c03519002d066050401614030010b80b142c0f40e208100d20301284050b005140036901e5503101d5104c0c0d0703201001408050715140542c8180490396040b5134425030515081449814020300c0d00b0f2500e2007140c00e90b0800f134031812180d02c1c18800310071100c0d80100060201c0302441e030b400c4130780d4a0700f20220b101550310141c45980c85003070480c1032001c1e84010303100b940a0768241c001006100032104005403205000441e40c0d525800003001001600c91307410241400701050400018561070090004640c00d06542c145201354101282004051034500d9030f4042 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 638836564 1250 638835314 638835319
    0x40e0406050a09082215080109090609020904030e040617030a0305060f0301110706060f150302220914070203190c0c05120a060f051603020a030902060309011a030d050307111212060906 81
    0x104c40104003005030084605002701550503549201c0202440002d80002040300c0e0058100310a074185070600506d00c2d240d15034500d0003181040b0b80000c4803245540b0035001c96a0745000755042045041080300a010302500090380030702140c0e0b008400e81c0d400c3c45202c8010403000099a9240c0300380c502a0b0554820742d0244228880c079202c10040d00600542084500c5118600143d039100b50f00e00b0f0190861240c6c4206220281200c80840d002075181e21000310321115015100042d59088002c0340d4034842c0d10281a0b074803030700214040545000f801228981c0344900c4540f521700d0b80320380c00301c0e0b107a6a410050720ad26500c89031003042402113503c0750034612142031005206505e05070852040840e55405a48105980010b035001c1c1580b096210b28580c0341d0042c40d01ccd55034107000c0c20141c082c0c60b50069800f54a500e5841c520828580042c0640901901340c075030905513034074031a0940e03401e13248000041c030300d0084190100c40c4451900007001742e4600700000e05000c0c10103401b400b11101008141ca030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 638837814 1250 638836564 638836589
    0x306091407260c01081816090b031905070b0d060801022803090305070f031106090f0106140a0b070804091104241d03071701090512040e0406050a090822 67
    0xc0060342d101c000d46a00c090301006d04002801d45622242c98070240001c4503404078072100d070100304651582c005062950046040318406503a4110415180b005004002d207154804c0c6000c00c52600b4071005041c0c41180c5082c001600da81d0717024007609a81c049403c40100c9204170016406e080c0003100ca0903010f40a40c0b43c01c11555409650140c40e0f03200380c442c05804280c0c81e1108004041c842c10400404405039026501c0c01c0c01d03d070710b05d29600c2d580c01260030069401c0c40c60104014080340040700c200c40c1c0c0104030302c240030710748114001c0300c1d030113200160b9550004000200300403a060140300f0340320000c1c50400d640c0d189080f01c20610307100440403801e00c1c1011841040c907500c0e4801c03180c0000500b034400d954008031558000034684500f80d408440d0310f60040c0e072513003410360043d03000b40740e12400b40301a18007151030a204070010b40b0882c080e1f4902680c2480c0868041211640aa41e10072201c130750001e0b4141c001d8442ca89150028007882c24012623108541c0b85035808510300c07000038024a80e144 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 638839064 1250 638837814 638837833
    0x1b0405090d091202040e2b0e0303160f0512040f17030702040e0f0a080301080606060a0f112a0a051e190504020a020706091e030609140726 61
    0x10325a0b269442400b49207045998a0340655445520040395220142c0440318030004441c031090384041e005c0513001d0110001c401e800c40c82401150007a0031584003c0285240040c00c20b8052481d80d080c140c16951901a40c058000042040101944030314411054a1325a40b410324034400c85030302034010600340340403400700c0c010001c0e0000c192070149a040b1404114440c51000e005c1c038141e031300c514080c424450b04000505000a490086050b00e280350f0a071105603032420188000d61040c0d900c030000140a42e145008030a20132443c0850004001b0300740c1c1c00c03003002942d0000b00c0882d01510b0784a50880c060b44170145103048040340c4001d20058404a1881141041605590064000b220701074000305649040711b544d10141100a004001c004540340e00202c00002d41d114514091400032074895800032502030345001140d10100d038100c1c04039051a046070307515000352000c079008846034025400715100c060070600556014011103035110b030f0359039040b02c2c110200d8601450044100c0c0c001d8241c2 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 638840314 1250 638839064 638839067
    0x50c0d140720040f2901050f0c010219091503110d021b030d15060c2619050a1403010803030609060607050d020c0909012f0c1b0405090d 60
    0x140c030301241d0450b410400c001021000b6102051241103060f0b8007900d00245068100388640c0082121000c00200c030180c02c2e4030104500803040741407405408140b0901081314047c41d808000c0050090301750025007000c3c40d83e0800c4141c3c1400805800c042500b0400611508000320f11a0410a049140c01c2c011600d01000f5800c4910a03100d018a40780d4000a81d2180628110032210305c896112007240d40e1580000d0a81d03006100803008420620441c42001405030301c00c01000e103015401c20300e4008843c80c03641340f00b1110002c1c405c10380100d2405000074002c601200b0384001c818107090b00c940d40e8039210107200410240c030440c013000c0356400c144014007450030004141e9034009000d481d0f0b00001d482c2e03800003801c0d45c002c068008145114402400070f003d176003c600c031210800140d03003038021910340c850102d00703860b010216100340c80700040a08032008451f10144a0300100b0320111482e0140d080d05483c1041060320488543c544806044000f40c202071007825441101f18024080c0200084c60 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 638841564 1250 638840314 638840317
    0xf07090302060a0512130b0601020f10020d330609140909010204030f060903020d11060a091112010213092003070905060d0c080907060c022101020a050c0d14 69
    0x1010b400b03844045072059020380104210340340d0f041556000d040038541403070162000b100e014421a1a2140f107404199030b9400002e66507813142e03502c40909078295041c80540025000b9017200300c0203d0b00c405c2d003180d004141d03440201c0041d00004100070620341043d2070310801801c552080c0b04000c60100b04000c0924a02c030b0381d07009518125616400d54641842c01c0d4003900590b040a071100609800450070005241c2c01400000d1003034007911951022000c0903075000c4203d8412500c2d50b0480c000099241c3d0b01903211078002441745483c00f1b10055404041a494000080d40c0c0c20503a40c0004c084000b003120008031401080011814050200e40618085100704507441c00b21a0340c801001248135a402401c10401505001d04803580316040742c00d2106c050100100d10b1400305c1c10b0300000c42c0e2440c0000c42c0b2441a100191035406030310a00e0b90900203184078401c440a070300d035541c1048000ea44005c0c001068005030503500c07107032501002d0661600300f60405021409111523840d0620030b8191000 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 638842814 1250 638841564 638841569
    0x3091b090c09010309060b090108030406020c01080f0a0914060a09020102070e1003030f121553102c070e0a0902100315050604030c0b0304081902060109050f0709 71
    0x380c042110005d42c540a4058041410415444201c0328004110400700002030412141181c0c2154000d80b40000107503003802007518001c400036031440c005a83c04103150010009240302d0f23072140c3c1e00c1803a200300490070010b0942c3c0d110300554171070050700203540e410005580078116a8050361014140038000d6000c0c000d49100c0142070012100342480054000ca08844013050114010701c00f00f0b0f450440910100040d0144480d07041c45400c0c0c4184803c400950034158000e043c03002d00c5083c1c0380d02183c0020072010400d09440303200340700d6104c030703e407405026070300842100c3d501c04150501c44075039408000d080d0712440c8074440c40d0700070403020014002032401d00311414039031030002540720507040c80040e02046c100a500b00c440300c920007030310706c1e85a444080901070400740491601d84440420070350344990301c8050000315008105114120045000b150082e21510000d031812003910545440d00d42c40d4010340f009600010010003007a4104c0c040e03240e010b11103100f0b00c001c0b4076160b11702500303480c0c0f80d0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 638844064 1250 638842814 638842817
    0x603050f06090907030c080a140c150d0b060c0102030105030d0f3911100504081507090812030103060b01050403030c030f02010608010e100c020102160b0406020d0203091b090c0901 79
    0x40301242d01c0110522501300910741020200a000d80c40d04d101e56960540400100d83c00e900c110134424049001180b0003092200003860480e40080500c0700d44030365040550851100703030303442c51f400c803c1d95113410007001e200f84000005600c07503141904143c00c1c00c0d90742c10500d0500c14840000e0b91f00540c00704541034550100034924010a844254520b25030340e4004100c1d13001e45c0a81c0311078040c80780480407600716100885071140d0070304407810201c03518040d0b4405c51000e40c0c03025510542601c0c07017030701003a4080b05034038100050315540e43c40305181c518100040071540800200510521026025403640220300b800c040d4903051070f60354010b1001112031000b400302b080203000c46407002d10039000107005004441c006d020413420211040c1d100d208031883d503e00a0f1030205011403440c0180295100e442101058184a410741c8c0c4880c0c140790402002120100d500300310005100a95102440c0101d40c00401008515200d8918410010b6401078540c442c81b007000c20031501e0303d6024210303101c45a00307 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 638845314 1250 638844064 638844079
    0x200906131808390a061802030a0c15031b050304050a022106010503010c0818030409020301032409020303090409150c1e051215030c03070306060f0603050f06 69
    0xc0011030803503880e40000618048000401c0d40d000018040f400105204203c0a5141d920001484421181000526052a41000a070500860640c2c0d005921004d0300e0186210300070b46d551b00103802c0075210f04044851010301c02c01400900018201010317540d4680c102005820b4112500803415402e0100010401c680040020100101840f403440c01d15406440c02c80c0002030300e01c1d80c80c00340003550004a618802c4100000d494a01402000c0014110ba121034290340c41c3c140d8124416021003681d2207092204200000313040210b8801103009601500e58070250b00115011030403240710340680100540d0602c1804001b585c2d011044507003000f400c5800040c48442e901d080004003024101450342e07a4900f050410800f038006d0500a034081c4600302c4182141c0055130295943c0c0502c20b860784182d485ca00018070300e030f1140340210060000080c200c0d1400711b14040003900d4220150030071602d080c0c0710740e0b003040300e07044428420010700814103080c0b0040c03810702e1001042000040c10a07129100 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 638846564 1250 638845314 638845331
    0xe1611070b12280203011a12070809031b070905060118140109030f050606030d1b030c080f03070c030e030c01050706090c0509150f090f0a09050f010920090613 70
    0x144401c0d00000c20f0205880d090401944038503070000d40007486405941000d100410006401c0c003400c98401510340f01d01e0704101e403540d0504a44101380200746403547e10040005226050345041810510724030310b402017440c103050a06c12010340b4400340c50300d4184580c01e00704142d000c00c6515028180e583c07501032054401010070040b1a8130000e03030310242c4044101c0074034100784079000c9031140c07060405030304541e400c00000380120340c943d00d0382042a600045155031080001c2c442c800140d034107400746102c6030404051540401c6141e1056464001145460075030701e04240d08580c030a81140340071400b400c40c0b101404006002d612841c8001003000d6612604042040421495200903100281c80800146400104034064003500241640f20341d021544411491610a80c4203210b12092004944030742c558480840181110440c200e507540621081807000c00c82c01d103c0c2440d000e01800a500840810507540e550f0604d0640301140515074040030014142c0b648207009804c0c01410200140100 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 638847814 1250 638846564 638846581
    0x60a080703020f041410141204020f040e01091112210408010507020601030c0e070e01120b0405092109030a020607060b0405010f031b030302060703150e1611070b12 72
    0x814410f0700f95902c0c0d00403c020826010111512141190564034843c60490003c026940f00d00a132905d25001407003006075209500300900c0803a0402e10161140c24144202030005007a52250030036112141e6642c4200700620138036401104000005441000c40030a0100300306468800f051075030781426100c4100c68903180c0c0380c40101e07001040c08400030402400c00c4000291540030030b10065441000c0d0742004181846145c1c4014003d071001e40b904c1d05955100c0d401174420410440d00813041c40d0743c82c1850f080948450198500ca0a01c000161a0000740d0340341d00318003c20510b00003418140e051041c12100d1702e001842400e43c0f5011200f8580321031321840d10b980941801000150018141400068140e140940c1001564811031404400f5603210080c02d06010241c80b0150040c1d01010100e50014003a50041d10128940780e0800070300d50321001480004007003030365204e1522007070000c00141246d0003d2100000034122002e015910720b084002410f500400422070707980c05500c0081a12207 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 638848920 1106 638847814 638847817
    0xf2406030b2224050616031b0302010c02150f1b070c060309031e020a150906061205012415120c2001090b041707050604060e0c090105060a08070302 65
    0x1140121b400403425048407041c0c0500084010f41401000346080c5203081c0c80c002e400220341070741452002850715004140f0803000075114800e0007103440c000025240c1000341002904102840510000140d00c140e84000304207400c0c06e44000381d80360b01600144001800398440c4d6400f1070401e5425101d850644846000581149405500250086640ca181c2e800203100020381710100350340d0007040b69000e42111446c24940b101081c100a82400303040080f042e8211410340048100280074100c0c5034501900960800220391034801d607210742d504000d5164100c1040c007014903828405400c005000011500007031503121040301e403150501604c6e000c594000c07401e031000d03a12521001c004403415614000c1480d03040042c800882c0e810420700d80114024600012400c06c9050414071303200b000c03031025015800f2400100001d80d1900240d0721414000d043c84201ca603203811044009 = true := by decide +kernel

theorem cover : BRFrame.Cov 638669064 638848920 := by
  have h0 := BRFrame.cov_init 638669064
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638669064 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 638669064 ≤ n) (h2 : n < 638848920) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
