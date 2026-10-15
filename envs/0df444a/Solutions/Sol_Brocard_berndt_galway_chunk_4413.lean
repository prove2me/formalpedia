-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4413
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:32:29.688976+00:00
-- url     : https://prove2.me/submissions/83036b27-887b-4095-bf35-551c8fedd196

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 793525179 ≤ n < 793705035 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 793526429 1250 793525179 793525219
    0x705191b0b1c09061b020102030601120209150912071418090a080c0c03340602030708071703070305040c060201090c031704030f0b0709091a010c02012c0a0603110a0509 74
    0x141c1174907641c0006a803400d006001400940d4202d00921829004001980003501d170200300556460300000d000c0e443d900d50380c00107070a07074048590103125440b034110000340141d0171102c14900031006403213050f0315156000d03a25005081c22110074031158000060100010503000003050144038134415640c2090542c00044c0c01c0049802c02005240c11200303182c00d060103500c8040d011007003040b0200c0c0490f0721384103019440340a02003002c3c181d281e010900f00306029801c0701d0310320340c00e049100042d501e29044001400420040e10161400a0407501c040766060051184e207200390381040140c206c2d50f18540d1141800419140e2601454006120000c006101520f11101ca14031520b001911443c00303460040402c10302c1c4d0300000c0380d1030a100500390a0280498040540503081c46e00c024404000c0c00181ca85103400407008240340c0302c64040c0a844075480ca07954103080c4007100d84074030b01c50ba2072100310280e4400101020318180d0400a00001c5030080740100104103014114560810041d00c00603 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 793527679 1250 793526429 793526471
    0x11e020a15020c100608070501030e0a03110312092505030a0b180102040605040e06180103110a0803160507050609010503010b0c190c06080703200705191b0b1c0906 72
    0x5651390310750406001864050200070042d100a2030100301c903078201c000c03c660f1068000006001c2c0a0304c0902d82c0759011040c0110341042c5680c8461054a0401c0418241d440034082803401340d90341c0a103000100e20340512154000c50f50000d0041640b031341142c0f40c501d41e8140c0500307500c01c01d140350203000c860b450080c009800105043d03211030f602d962030915250103000000b480c07188a04100c40700c80c40300d03c0c01c4c041d40f0350650390000c07205071280140702d01003513500d2600d0b00901030f54400403561038050300852420700821842072041d140b1840d0b54806214070b03030107004001c5010820600040c004420b40c1c5000d416003069000031551031145441240d06114001c0b0426541d500e00c10100707000032508002659040003c1c0e14003003080b41444120580c943c074004201c10340030000007a0700300c1401010003e2034220150261030300c0b01c5a03402d28050503803006448503c11415002c100004046140c5000d403802031018956940d04180c0020889000b0101c0d00d1044600c07a654004015400d84d90820071 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 793528929 1250 793527679 793527703
    0x3020d0612020a0b03060310020c0a0b040c0f0b07050a0b130b090d030b0306040201020a02060a270303140f0a14040306020a02060609180c09040201031e0506011e020a15020c 76
    0x200c100d107009006100700e20700560802c5000c0007041040c05070589000888400000c04000016115007400e000b5600f042098040038014003003c034107000031312048036a11030465500010452405a4031146003406010302d0501030299040140401c01040003842c00f01d07404510800050300704030841e5910702c112207040c0c034400d119601c0403500900061b01441440c4624a0403001881d1502d072950000b95186026030009000344400700b000ca8096000e25600e242d84200714442c0e001d00c0304040d0030300040b000c440c4000c0d400200c0711080e10f0740062010040741c0b83c800340160020702d09075107006c0542e1059840c40300f007441200b00f00400404551948060314201c4880c2c0d000e02140d00b0900c042040240780640003198803600c24036031000c000b000141020644100ba646140150355600069008010906201001111a0898020001a40d8040362141000340c807445050303503458007191f161041b00740701c02d000760380441c0e62180030880c00581c1000b212031810b070240c075003001501365030b041841c09118 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 793530179 1250 793528929 793528949
    0x1b0606050a030b060a0530030f0705010e060f06150a0509150d0b060c2e0c02030c010c03060b0301060503131e02030723012111030612010912030b0103020d06 69
    0x6004d1903281040100300101000c44103603420100010501c490b0701d100d8a614880b1a403440d0700030520403001d0003036401550030400420340b82d1641b410000e0207040b2007106243c1a000d04400648900d000c940114041e0001034100c413442d8a400f502c03554160300c08108401030050078400075880356120007044041001025a040d2038000108103241074400b500355052044600341718817000c0c1180090707211000c1008040c0300c8064601c000c40e1000d14890084074030005400c091500c041c054001000b04a00c0c10140f00070000818500021800c903000d600900380403100800c01081101d229030051074020b58007030502d420045490707403142074440170101d5440e00e01c42c2d6102c4180c00d41c07405000700e1008101c2508141e07052100c001e1906245000d4525144c1801181c1c007c440c48100b142c03103c00040d03960300104008004000c045640c16800482d48140305a401d03400b0341b031481d041030003601d0041d036000f00100340500480b03500364041c100d000240d0381019401d00ca1a50800290b0003548000c0542c404 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 793531429 1250 793530179 793530181
    0xa0f090801230f040203030307050901090510081e040c12020f220c051204021c12181403121e031006020114150904060207210f0903031b0606050a030b 66
    0x200355002c1c1d040080282c1d020060300c204202c0503890200881c0c0d03200c8542e2906d41c0d50354903803a0041e688270085400c116081151900c0600c0d1003078001003c0360241820305010310503100d4041c480b0408100485004121034100e12042000100e05860107100e10f1000345048d00300b54071180499042c0311039845148064108440d01c40b140030842c45283c1209440c1e02d055450800c3c141c1100c052130002900003402000c0d080001d83c121081d030551802a164880980004050081001488210100d08503801024486c0001035508150750b14014222800b80103044050321100c00c007030560308522070750904980d000c0031641d2010300350b0004510890b00d040c40300e42d03107506004000742100d403014800c002d04950300090184203180c0c0c11f000c801e00e04080b00d0301152035982c3e29001005e4051021b000300451404000701a01c1c84d1400b801200c01d12440e9665034810780045006c5035002d80c02d100c042c0224201c040b42020103803820080e40105401982c010560690310001308000e800c59920644030089018 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 793532679 1250 793531429 793531481
    0x9060d03020d14041527060504030b06120d02011b0e18100830030103080403241b0f1d090a02040e0f15090c0a2d0509091602030a0f090801 61
    0x10341102a01300f21b0307211a0401414858080c000348524003021308980500c200045480c5e642c2c3c0c00e4400b1030310105003601c6520a4be007102a000e80602e1038454583c4010815108000d44218200e4840703860081968001c01c910f203517000c1d45e089014110301205920304401042d514001c01c440003140f4080c0c148075480c3c41080c50750280c1d60380811a440d2010004000400c04200c541040d581500e401c01c21a0b02d0f87d950143d604001c2e826500000000305080c4200e82c80350910131072400340848050b8823811002c1c005501c0c00c440c29004c149030f014100c08403001235251401c1840005034005180c4800518003900ca90200c4203010080b01c03523040e910801410420048103100525200c1001030700d2210042c240079004507441e014200d050001c0100003d601d48541c040780d100801002c07507a241038408162450001059980000c1d4000e014094540210791310b00d540384007010080105a000e9414044401c904903007480b0115071034006c00603100d00201342d60200b0f20908030b00742504450035180c3d401038 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 793533929 1250 793532679 793532717
    0xc051801090509131a1017011e09060c0f0f0e0105070c0e0613060b030c0f1315110304030c1a04030c091b0e010c03030f1d0303040209060d03020d140415 67
    0xc050b00f210242c2020a0021101082811200342c403047e05400041284401c90240103043c800c2c41c28841003602441181c400c00282c0c400d80846004102c244440740d8483e00a07030384420850b44000014050f0010b4003140f0388140e205806c6400140b60552804403161a1310001c51040d800100381901c20f1010b000f003624080303c200720403120100051150300c0c6000c40c0210351b07000c0102403e5081b400001c011192844200440e6991451640e4004805440e01c2c07110f000c030096502c5070320106110365110041000004140c0e03044a80c0071100c25086420440c48002001d03480d030521500d104244000310008086070242405054001400500150b03203c1766000381d48120300e140c0080c030012162500d20717a64000d4181d078041c0e402d401c000c80e0705007140742500300500121a4015411542c07106014502c0c2c004801036000f035008403602d0314552910b204100c09051044c3c40100941e02c4064030b02800350180700d034410b03902e440c11491408c10f41d841407050f480c0600c2000c1503001405040072108460b6034 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 793535179 1250 793533929 793533953
    0x60a09050720031b0601060203031b0903030d0b011416080901171815091009080409090f0605060a0b070b070306050a03110a1707090e3d0c05180109050913 68
    0x513200188003a502d0a10060f40f6403001a104880d200200440260f0f40760820045440c058000f03001c491340d032007211080034000d002c4001071030700082c15000c843c0d2100c000305054880c605100154403600c030780a941d820700540d00995145060045003620001c2c1507900c003640314400c13441402d640400e0a104501d1078240000c1d005407030405c41c1c030340062040100000800411000030014005040105804c0910150041d40e01210789070f030034140c4100c2080149201102090311803001070000b0346034070b41000903607401c0f80503044455038144400000b04e0800c80d0100d0700720f0280c2c240020749640750000316141c4581138000782c0315000d0410b08442d01b814010074940040c400c620742ea15000180480d0543c4840c0c003449000682602e0307102031404501c0c14820040069250f40030700d0340d4587d240120302c0400200c5c02c02c510b00120a074840405901071401030622000e1190340700c2e860304e032002e40380440341d006e00c0d051581007200549001c51f207074680c0d41c4040c2c0203407880741c908002506c23507240660004107 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 793536429 1250 793535179 793535227
    0x303030506030d09030201180e0907170c060901212d0b090601050f131410030509060f090f010606030b1306050a0510142709060a0905072003 62
    0x101c081005002540d0000c580380a03179a09191000d480d20703007038405c200c121039550004072003185410280701c0459400141c1c0c00031074055206958a032221200480e84482c914103000303070400c40c00c1002a2040d88142106c580942c0e0468040e024044040b65900803196601e070f03424031041414207084001d00303001d840d1000c03039000740005108100c00d200101c1c00908000d040c080c140030021501c1c010600d401c10a0311250304041704854001a034071803510845100e4401309902500054003c00038841c0720b07000c0e4034440c040035401443d040d03c81400174107550f40004c05852080c001e00c00e80b14501308080c054100201a1550089102c0070404200071400b0305452901e050780340761000c05c0060b616013102440c2122030442e0b6003041c40035101e0301552040811000703d0551000050520b20b80c80e41c1c90001000d2094250554448801e4413050143c4944103848155000008601c200f02c0340c4681c2d0031441e4815041d1030084c0c5650f000030070350b001c0c412000728090204d400100b507030803040c4c01807907400c00549 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 793537679 1250 793536429 793536433
    0x111306020d20070501120b0d0b0f070c03050906090a08190311031c020c010b030703080307080c0a051803070f03061a0409120806031603151a032a1207030303050603 72
    0x1015080c440d030f9109281d2052906102d40c1812007079001c00d1036413080c905482c0151480304040340d81c1c0707000420140f045a00300b5454210402140310644a9862480706642c1a280e55261000303c40400c0106d03000340d42d000d9030241200c007010403101d105001c020082c030018612043e174030060740340260003845000071900880c0d0041c00010500c102140030302c2144809150b00680da041e81004d2140034002c90b901c241c0c0c0510901c0d40c000100038102e0019440b400403995009107a0304c850385805614030502d4424400180d007480214a84005100c01420b0000300400b11040140c1d83d00103944d90210682c001e03030742e060381c46004e400001c1c14801c5800008500315020440312016a0f1500501590751855408000460001540c02d803400c002c00d00c3c190782c5d07210341403610035940e240041d56045c0c0c40787d10030912420889001000742c01c034040f25081e0840103010b0002d030705680350541d1185e61941c1900a42d03000743c14014a03551036107545641e604c40c18030064464030342141400380c262140035010f0b50003a = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 793538929 1250 793537679 793537727
    0xf06050c0c060a090e0411041d06101223070f0609050306090307080d0207150e0d032c070b0f0406021b090f04030c0b0c040609050609090109111306020d 67
    0x21a1380210b10740162200b24001d4030440d00c0e6400c1c5104001c6030000f11541040c948a00400c044c241c064014040702d9040040b0b078940c0c0d95408801c0c1c0c01e61911b1040a07001c004e406d0b0303200700249809408000d009100c1404111000500d0107092400603568000c0c0481c856440b000e2010320390100020b000703080c09500800140c2000220ba5540740300b00400039024880101b00125221050f8045504013900b1000c05e800807503225181c2d01c005e0079480d2003680c06129a103025806907000380954001903041014003070703079559102000000c04000716400c00c518014a0740105808508002408100302c501c0346180e00d0703904080300a450103541416840c4007030720459800c0819580c00d12041d501080130740c00681d242d00e451600b550502c0c2c0c0b8103001050341100004000c1901c4094000d807084451643e076a024007540c030811f00c07281e0310071805401e4001e00c800e8014051070350f90b90805030b102c1e5a800e018602e0305080e04050365000310f064010000580000c4405c00b1016444860b01406085804c4840c0340 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 793540179 1250 793538929 793538947
    0xc080d0c0b06012303070206271b0604120507030c0f0e010302060906042105060606040b190e13050f0f0702030a0e0103060b0d020c010c0f0903110a0f06050c0c06 71
    0x18001c0020035050400044111141c2540300001c14550485440c4071510707124104114080e480320422034031076941c41c54020a44002d42c66800321404400d146c40041e198500c031100d058403100c1c0781100071f1600301508000c0000d880d0074a00061450b140104054084c4a003186020007100031280d10203050403441c10300511002c0c187d9558141181d90489004d81d1711354a210200c0d1070b90040344c1c414003103181e4100700001c605003107014005500d8460b106603496580c85108209450065026070920040e0501c503505000c07401d50a03811035440c031820403c040c004080000350604d59406481c0c0ca20340e0319030f42030098034a00c90081c50b41040b48900d8070440ca1500c42c400079079034080c3e848140e04000e4400c0300414280d009502402c05059020720b00e55039502c258013003c0283d0310502c4521113940ca05028412032600c41d080340680702c9902c0d5540022a45103440d94004400c840c0000c96218440500002d103044034045460000c060342c0c1c507010385030644810030310709050440020b140500020070600407 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 793541429 1250 793540179 793540193
    0x100f020d0509180f0603010f15090506030a060c0507050d0804151d03030703140903180d11030a0c0608060d080d0c030b03070308130f0f032009040c080d0c 68
    0x18400c140c41d0071616024004002140c1c4508560400e00382d500c00010701c8620065410034900c80d81040c0c000340b240078101c0c51200f04580250400c07c01705549504140084e940e40c1d0009070b003101e4000e046a2402c4d805484c0c04044404400510b0085540020540c040001c01e10100402e010207003811410382c505500c0d00d5203c9494000c000c2c1c52150784003501c20a01c044a41c0c0c2d0034a02a0000442e81c6a14044e80c0283c01840c0c61042a0703c0c02d0362080000b61545c40c004100d0702c07a003038101607a120038a4080f050064046441e00122400181450100c00c1d03614204564004240079034402c48410b8940b8030094003158000d8140b501440001c41500003290181045456508400304002007404019030100d0090040540c42ca6050140c40030000070300401002404811801c1d03013904425039a60443c140c440324845c440c0e031a940389401c1c03003000842c20780120b500c40300704402800b055440031800002c00c0210116001c403644014280203004400042000242410290428860544140c0c072604 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 793542679 1250 793541429 793541443
    0x9020c03030a09020d0f0b101703090411040801090c050a05010806100f0c080304120314070c060c050d02030906040b1e150a1d1b0f0702090709150905100f02 69
    0xe54501c1c0c940c40128110745420b091000d400d07406c00304000a1941900d881301012400380d46154107500442c2000c19201c56046541541e40c050f030780118503100c4d025086c48007070180d030ba040030100401400000783d1480d080c0104069039120b484c560010318144002c101c400c4500350803160410150404000180e210a0419055a803041c206107010103407030031003103c440c8022107008165030760101c01e0008001285848180745411600c05010300300c4440f511a4001c102156a00006440c20b214100401c5259120204900003440c00c0380c9410350041c008006d0380d2060b540c45025911407420003051103256014540c0101851428203407440c12b005101c8032540b0043c200c040b01c2d400d140d03a0001140d5904041100031f140c060402c504a16002440310400031040302c510b41c2ca240d802c100c04645030000d1045641c618400c21038542081d040c3e07000d00540c01801020351f02481000303980880d0071840b1400d6442002159501d81c848181441c080c0b010090000003000700780089821080c05083d0041908 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 793543929 1250 793542679 793542691
    0xe01090608070206041428060b01080c03071214070509090108161809051e0607092304060504020c0f1207050c09070203070209180f1605130902060c0102070c09020c0303 74
    0xf120282601155003405e0070004441500b220307c0d001045c072032000c0d040309861102405801d0070001075003aa0019030f64064121140707001c1c24810000a40c4207401070141e100c518080303c40029140c810442c015001e0901a9036000201e20040b0b100d0716645031020505014280480140040e040b0b041c54100f80d2203483d0003840c498480c086c0c000e0305401c0710b40c1d1001101607000000c0387c0c1c0b48000e0400f0806492804214811039014020008000c18040e950f414129900769102065030769808450420000000381459440307074841c00005096034171070020703007440102400074000c02c0545070022450045903644030503484c1000d12855001c84c01c041101d40100f43e0903501d040c00c0ba55801000c0342140b04102c0002d520103800c034288640082c40c06030480e600007941c4112100400044052556011400c0d9440b40804940304c05201c103081040f0f4111890281c16000300380b800503980040c0a0350071109100c02543c6d40410400e00f8060300c0a00c09004060f880d40452401c401c00e0f40003500d910004100c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 793545179 1250 793543929 793543943
    0x40c090e01060c030e040507030905100b060a110a0b0f160c1a041b14130510090e0f0a060c08060a031208041e06050f0a14130212030a0e0109060807020604 68
    0x2543c02498091072030000080030044c1b0400c0345107020400a0300401c07980c8000d403942d1107901191045050a48200820060018022400d1021903101201d130500c1e08205400d0301e016149801000400c2c40b180c10740500598881c2040d01c1c6044114591440da840c00b1580801c011407074a00041901c01c07011082c0d008843c0d0301126a5543c5040c140c8811045003c4800d0014401c2c1000a1400b501222104a5203040300c03801a100716584940050701c005070341d54808644a0503041000c03060581c00714540781800c20075075036484082d0b42c025043c500c46000607a80c903511074041e4469950b000841e41c0e40410200d940c8c01c400c905540b00e5241d08070303200c0107200510a012000c0350a1050031b4003005c0300a801050b0000c02211241381c4280a4032054550b0311000280d00c3c00308480709503500801310303103071807a000c111900d03a142d0202121000010005a070071098140c6000b000c0c50080c401803002c000e40d40c46800d031844c61100010a94134035580004100100c0c6030900042641c08651680c1058202034 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 793546429 1250 793545179 793545197
    0x1302060f13050310140708150f040605030109110a060809120a12060303210204050f06090f09010e0403080f0f070c0c1520010e06070f02010e011a040c090e0106 70
    0x752031551007050703003005500d403082d00e6061814402982101d1003a284101c820034564a800345d0a0301c01d6a0295210500401b4480c404403043c104120104507040d0010b00100d556651078002c2802c65800d0310055800c80440c041c14045400c0c1151060014409417030040854500007a0f481c0d2108a401032580d04442c00241c88100c0038460340940b520f41140385000c00c0400e58a1902521401c40c4e9041c01b066031402895044504420b8801c0e1002c5038400740c41070410500f2102000100d82c443c1d545030f50311840c00304040d20305403116030155020b03001c68840780c401801d0900300580f0740403000f011030f42400050001c0042007030101007001d0b04251a4100010302030401d00d001381d03910b0f645030012800c52020500c3c1c10105644810307001c0129030340d80e1a0301c40b0218100b001e14240e070100803140350305602107404100418861007401c24080002d02c000035501c602c83c503000307096034507442e500c084600d8041c290659030310f004e1280034040010781c10406102e81c588102c010103004144074600500c00340031 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 793547679 1250 793546429 793546447
    0x3210403020109020a0e0411010903081e16060e100203101a0702150d0e030909060603250207060e01020105060307050f0109080f060a06050d1707080423091302060f 72
    0x5003003c0e03050b0758001c1c413101480761110944814040111015030b080c2948620040c0954041e0844409503508000c14034a40f41c9403040c44101088080280c001e09501000465105034483e04801080c40c403511780890000701e80a0000c2c03071314600b1903001e440b41b0310410611540b11a03407000170040300c0380e040f8660041e5a16030140c1000d401111300181d0044450007441842d1030a40000f0201c52400007000c10800c00c50813803460b943d004600c16079401072317401e0780400c00c10701e0b09002a50340a852400a561060441145001007009020f01c602c050fa01980c01841071340d8001b502c420402d5001c0c4002c00c55441c002001039518949440b40354020581c81c011400c0303503489804880c1c01380035484212541c003c3c00500565641c0400c40d6030700300261401401080b075151070460810a5504004840400c51800601d2034140e400080c00300d504140402001445920034040141c001520b00400310700d0140c01d034240a0030400082c080340c408000c1502d02c034016a144016070b0500100e401546840311084 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 793548929 1250 793547679 793547681
    0x2121e011a0906030915090a0b041419050c01090b1c0507020c0d1109011521060f0e0a0501090e0316020303090315040317190902010c151409032104030201 68
    0x141a542d60440400030402c00030400001e05048001405090304d06241e81e10036602c0d460340030700072000741440c0340100800c010a002042022919581c0804e40d00b4604040e00e4087c0c0d400900170084070244c0107014210070b60343c0c0180b000d070001c101800c0c1c0300d40b40660708020700f680220305a044d0b130f211603a520085010b1510800450000c1c00380500f024015031601e09168600d0384810f10440c0c4141890000417400d8001d205055100580c10b03100c4041200301c0064680040d4202d2030b148c902c82d5034407140000c8142d0b42821500c001d1101101c44d000c80e040210343c0f00142c1e54160006020790703044c1001d000c5d101c54000111681c0d0981c040d040d0280306002d10010703040d8230680042680c140b241c4c801c03188204100c2c0100c0d5000368401e4980000e244140700041808036000c81302c81e90011800c01e8400e035804090340204001900c1454041c0050303e079540c91000381800f401c44000d031035a8900c4088080c049001c019600001e00000450409400000301080744c1c801c140d403d883e00f05103074046010507000b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 793550179 1250 793548929 793548937
    0x1101050a0e060d060e1b16140106061106060a03050309210109050705120a120507030c0c140301110304020904080f0d0204150306061809020f1b0102121e011a 69
    0x80126580d194189070310f00141644d401010320a0010341e011407404d41c03813907070903148032419101101c1c200303078455440c00f14030b90010100740da001d00010f004143d480402c1c81960701600082d11a80020420354200602e0113800509881c021400d80000380b010030b4000080d559070120480d0041080c1d544036411801101c1c401500044948c00c0080000401c503000c9040006c0c2c9138240d4801001b000e20740441a6611403404000d400c5030301c01e50050290600c210f0091491324000d0801182e004c60300e65a540c41c0c000194840680841a00040d08442c502800303203a0180c0780344444141541055000505018400740c8000c29038540004c00003801c6000c0415150b0794201d014003152038640c1e4a9000244c0f40002e00e2480009140c0800441c001c1c0c045c0490341d0b100e10340d44000d03509460030800800c000354448032516900410900c03610040a41d02d00900d009110342600250711251140400b403070b0060b001e82020048407005d003c80305080840204103044448080030a5012144035502c05010302ca = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 793551429 1250 793550179 793550207
    0x307030818130905010b1507062c07080d02070609050405060307050901060309030e040203272d0610080d1b1205031f12230a0302100b0d1101050a 64
    0x46420050325400710b40d62083e074615009a0013404408040320800943e00c408041c1002c90364000e1100710003260140d0300082c401d01d0103224a40b00030082118031108128030104001d05075000d04002c1c0070010040c420f0b00c84035441400200328443c01c05001400a40c224010709000b5981c80c000900c40c0d6600308000c01c010003010b41507100c02e507140d100080103482d146806501041c1041c24029490030075108981c4604001160040c40222020b840c0c4081c003490340400d143c9202d80c1c507030544140d1114452070216110381001020101d9106007103410001e00502020003122030a1080000c007a000c100e64a228ac0d00c1c3c94800703c1c101d00380d0b40e495204c40b2045005081c0b0064487d140d0025504040110b00401341c100401c1c10304403a900710201c0c4160540203a01c140c455040401001400c038520001c400b071800f00f10180e1f04518898050304d4905078603c250010780c400090815284618032032030160300002c0d1074842900280d0303111510789440d030030280390401400051251010344102104c8000c10 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 793552679 1250 793551429 793551439
    0xd020301061206081203070e0409050d03020406140c06013f02010e0f03032205100806100e030a0807150912030606020a231203090102190e0307030818 66
    0xd6101c02008003908161040e5038800c5107040d00c040340381c20000a0001e01c44405444035031440d40c901000329003403450045a2a0002d48905802001078402c1c040303a0544685541d0050f113642c41c001c1c00512180e113150030b14500460400034010500804140700d419101c2d0b8a4108a692080154662645c1403100105141c1c2e40030501c0403085a854195502446000f40d94400702c1050b0b250421840e0000e8550013030345680100100c00c00e0764810804411004c1036204070314817039a5500c0203d00c514041100540c000f135406010007403145015086401902001d20301300b815a11288040307903440c990703144d01421000c40410050108a16030102030300c0b9800501c010322119104e4135001841400000c10400403e06004010490f14800507489030015001a081c08900f000312891401345c8050404840250040d40d1f420b4807502e0000d0f0042d070003000200300061361200341d01051818042c201c880300302002100c401d0061686d900040a005882d0002000d079924182c40700104012520306008a03000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 793553929 1250 793552679 793552681
    0x3030b03100204081609140a0f06090f0212011e031e02032b030c12020a0c05070b091302040b030f0a0b1507051002030c0a030c0201060306090b180111070f080d0203 72
    0x41840810301182c00c40f101030b58241c03d69110b224040681d50007a034802103445d051f00000b0024a51500074001c2404811000581c0940750410502564060071003c48003d8000030b00c1700800c00e1030b0b00018010048540c04c002c0240d441e070055002c03481c0300d203c090010300740f09a94160032031b15403403d0b4410907402400c9074001c070440c0c02c0c2150740b09001d2812201c1c4225209541009a00a01079101e9003030903a42e60304104030503c12548000d420041145041082000321000098010010302c0060041d06142c1130700d40c1c00b10801c00228480108541d66420f0044c4803c2060342c150314103072038008105008151351613446102c0c9000512441c0740c0d580e4006d0000042198107840800200403150113a000d860010341d881007000168032090700c0840e98000208071300c0d0f41147c444c0c2c3c0529502c2000340700204007569644c0b00c3c80281c4410703140944910b1084410700600124000403075600c0ea20030b000900445064120b5a8064040c102c805440041c0e0055240c0822681808462684501c01021526 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 793555179 1250 793553929 793553939
    0x50901031a060f030a08030c07080c060a0609060e07030b150d0b040609060b07020d0c0e0411120109150b030109080d0e0601080c311a0f0904020a0303030b03100204 72
    0x703006106801032204920540200b2070509010310551850700b0003a000344402c24203070362a00c0e9503910082c00004568000d01100c0c0004401000608001112500900b035605103501514211000d40c1d010f64252890181c1c1009031503110188140d00604900b00054081380180200c2c100142c0103000c880d004a00042244808c485036000782407502c800d4500700503d6440e0325105007200c0241c02882d4200034180400030051800048085019118904402295030b6450340e000d412081a50100d81d404c90040040809050203080b458800c440d640090002e0040c41d1543c400f007181030010001140d071070b40c948050540b401d400107040c0d55440702101c3d646003061406c0100070311059103500c0a0780201000041d511500107a8070711034170300c004c0c41c0218401c05e00440c5030744015040103203c082800c856040c010150a0300c920031800300d0505010304120020030801c0a0320703600003c0244108507510502c80962140312440099a40c18180028240046c200292403c107296603000c2000740000780c0451 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 793556429 1250 793555179 793555193
    0xa0207122a0822051c140708060412030b101d03061003021002150a0506011403090f0705040c0c12020312100503070b07050a0605073b0109061e030605090103 69
    0x85004001112003d40a5601c810f000000151081650042039111003c00541d140010081d92a100e040c4803044860f0f12551141440c64551040404d50400f83c2008180056040201314203001c500d0200461111500042c482c02c0465091908114030f228007100c040d002030400d81d80da040014110b442c5803805000703c800c0e1074454001240140c192007541d00340680005212901c4040060b001c00569440030f000900512000301510704000240300180e0b84002040001d42c0590305500141500d62004d0b41100e20f011340c294007035409140742241020009900062031611154000807642c4011000a812807450044e40001181c100e402d106214003410b51100100031288240c090350110f52740d5801784040c0d07004036070016110742c00c50350708080010b0850f840075a1085041c00d110125822050118841402e40e811441d18401d0b103000c04914007510032262902c0c0740b07003443c0500703440d800c001000781005500c0780760b8084205201e400b10000da00076000740c00035000241c1032040b65a0b407818004 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 793557679 1250 793556429 793556437
    0x270801020711032e02040b03010605070b2406031b03090f100603021503042f0301060b0a0c150e030a0c12030e0303180c031c02060a0207122a08 63
    0x35281020a5408681420b0205000480e807611107081d00019511800400d20718207103040340075020760700f004081f1300070030f00c81c3c0510b0103040c0da5540c46e82c5401c03503407170002010480504280000c0602440710b010000c0d0702c0b4122000c0000903503046413642c86401811640c5580101c5030301510350080204100940006503000f07040d0603c0741118032100e000c40c052400c4403d180070207908951fa0102c10300103010701d03200441d0800d1042c880c0040c0035440108220000c801d0901101c1c13025059906403000d840c09002d00005400c060072440d01e4400c010a01030180e9114400c001c09600c50101070605000080d446031902c0c0900b01c00303503903540301404002814040001011106002c1720f003240200350344280300e210020030108000358551f807a010082c1020707081c603e01c490320b684122980c2d06550f440a01c803500e910100c0381c2a03107603071740d114480190608200814428032188140420404110942c000316038180260515880c1c070000c0644003004044980c0300c00710340074098030001007007040c0c241c010 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 793558929 1250 793557679 793557683
    0x70c050a141509030705010c150f0b0a30030c0b16030e0c15030a06050409110a1d0103030c0c0909030906030e0a02010801140a031a0105010228032708010207 69
    0x9801e42c00342048940c006402035075000c0e0303096407001c4001c1c42154010105094424018102980c0380c04a810502040d00e10744081c070301c00242c0ba280b1440090a1002210003d4000c13030214100d02d5580100100518500b20f000740440605124880c040c5405040e101030620340200c0b0a040ba440d004401e246441c030a5880a80028540048601c40010104440003640780041c040281c00d400101c0844403900094a541d188980d11200003c20b90741e02d00c14441a54466880081c6804d0307942c007081383c981804d42c0101111080031781c004942d007140707400c41810b403903150400c2e1703421f015a41051042000290446039190303141403603036814580c01000d86001c0f500301d95006e01c100b01840c110640c440219000c001d0205030604014804451405c0b4985480c2c034000d007200310125a00c3e200c1803814400e40c1ca10104170180c690051100d560305010300d030300350a01258449000f0a00d0725000b00f14942002c406810040c40842c800034881501d080c11440240c481c40ca010000e88880e02c0900039030105800b = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 793560179 1250 793558929 793558939
    0x30207060e1c061104090605040f090b040f05010b120a050c010203130e0604020c011806110310090e010b030f0708150c04060807051207031d06100b070c050a14 70
    0x924144a5074500c03100781ca010b00520030780c1c001e101d84007400110481088403410380b14070783c0151500004000e4001800811000304e80189007130305000441d00007100d201251800c01194001250704982016082980003000744403203801418018010b050b00500207a1040c0c01155240e40640d00148072410b541c0102e0684003186881c1c801aa81d900c10421222800983c0c1c0d142000303600c000300c0000350f0050010300094605151030b01a142103550740401910b55100300581c2506100c0c040c8154643c04035100e240528608100200c011480e221f486010200d80d21101d01c9505498203401541c607990000d800ca0380c0f0b00c146c6149a907255120b9018181d140c0c81101c002581103008158800e02031074484d4045403801d07040c088100d4010740c00810180030302008004c100b81c4015180790700c5d4441c50035645c0005103054220744c02100c42d240801ca4030320070b6100340180410700c0580c90280048403002d411481d0350340c00301d207032160300000254271003a4080c40c1160001500c000d001c416400b00203040750 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 793561429 1250 793560179 793560193
    0x204291c0b070c051c020c040b120a12080a0c0207051002190803060f010c020f01110f03030f070801090e060f06041509020903120403030c0b04020d051615020703080306091b070b040302 81
    0xd50b04136540026028030050340000b1a43c00c1f54146a030003003a04400242a54072800c010100e00d618009514100300c40480214000c0303a00300f035001c080e260701b04541107024024082e0304000299100c0c6da0303000d194810008016080c04050007088451814070102d030380f09400c1c624038104500c03542c108440c401c4c0240105803c102d215842400c1c00b0a00304d600500d1104041c050130011220799003040d040140d6882400c0f2140304c031100c10409107201e1411071040480e07504d80b1000040541c90706a000c01095030400712031180000001c240c03558000e145a442c0801ca984910004010380341c0c3c14040c0220026000011a8821840d0018007680f141a400c0307039103a0300210000c0ca01d5100b20b20000d030006907014480000a080305100c0c9400034002406d0503507091460b2903850504103112104424201e220404103d1405e0039107010180d071441d400689149881c50700d44001c244001040300b403185610400290010402400312590300c0a4401400e840d0b400500d00400700141c1600c081c1d001d8440c0350 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 793562679 1250 793561429 793561453
    0x301032d05010b28090b0a080303100302010e09070c060b01030617240108060106052b0b03060105060a050f0f0c070f0611030f07030e0f030d020304030204291c0b070c05 74
    0x81c104075154000801d003461454604921720340100000c000c1190300c05800980028446000c00145001d9850040b9000c1c40364030710320002d03064406200145e0b0240059804200318a9002a01142415080b107008100b6800440040300107000c10b821400e244192040c20a604a8001918a019211040c02c06050040411922003c03040034820100280d1000c0014000c2c235108201a20450b10f11404030712125141c2002944501d0307401c1501886a40c0e250075030001490704001050061a0030b0318020310348041940000d00510075407030003000e0104000340310320140d80100c085804511184090b210f440d0784070710325507444240503c690070001d42007140e4500140c1000c800c88c0c1c4842e40c0400790f04d18103c000e681c06d6a0f03440c202c11143d40e000180b1545844a51000e00190030012076a42c095070752b5078150720411085a4240890341c02c402064124400c2407008000554141042101c0c52400e41040303188607080c507481e18000514040745a4140305070035801c4803001501300c0c03241d0141c4062b04041 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 793563929 1250 793562679 793562719
    0x504050103081b030d050f090d030504050d200708030910020d020714040e010c0207091103060a05012d09090b0121051801020f13060908030301032d05010b 68
    0x2800040c0c00007900304620300c1c460440841c3d004842c402c100c240c1c0c1c10803903c2c020719012154120391452440c00c0340300401c0385442d018860280007031411b040800003030801d519265502c101207400781090107502091030404103005620285030300304150444603201d8941984517200d400610030513001d100451642190b031400810449002c8443e64010071106141c2104060f203c11400c800340e80182d695030400090100a010318170001000d90001c0c181a841c01c003101084440e0007802d401d100009005100c115503a640c80001140c1c0c007441c18902c04541c1d04889829403141d00d180c642d0b0021158145448550001503c904441a5510400c0402820380041d034400f100c0100324054054030310000e480001103680007503085002255546445591040c6083c226030003c9944440c030740700441e0038981815a044188058082c41c54a001d10034500041c4c996a400103020003094010001101210261040a420b4088810f007514110440c05800c1032402086945c0d1268081e02804507180100c0b544 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 793565179 1250 793563929 793563931
    0xe01210605150d080714211303210210090f2a0305070e100303080708041b0605090a090e0703030f05270103200f1303020a061d01080c0702280605040906050405 70
    0xc114061b50f21f60050074168030f0b540310380801c0c201040b0a11021001ca00d4881c44161545074603c02c504101401d004060321b0081a00070b140d200c1400c1008410002c0d0280c00848030056004000503560a00c54521800843c8c0c821540811040360510000a22900003941800c48407584c1050116442e1500b860191100d140805408541d1000100b18002e00c030310359869200c0e0042000c05010905440e28500c951005e0b44010000b800100c0d00c040280b4029840300010015a60200003914024109603240d84640c032014043c000314541d4104d0083c0620115820045121428002c01c2d01c00c42201104604041d2694006440c2034809007414626044502000d4501c10000e81443d01038200f4001641c40740b401c5440246070042d0000041e141c0f0000503000c1c0c98162542d1182062002c0782c1413084c108210782904110640c814001161101c030211000c080c2c055814401450b000e51440c0840340e24420720411080c504200001c03407640c480068415186030340c10034460907075103a0803c8107441d0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 793566429 1250 793565179 793565203
    0x3120106080f130516060905010806030a021c0f080409051510091203090806010e011e0e01050f1c0303150515030106031d010c0302040e01210605150d080714 69
    0xc402c00801c0c0301421081e5070410f6144600300712041d069841e284204540d60300e5200784c0200c3c181460502c003d6802070405948108107500030305464800d500060348600185002e0001e050003000800e050044444140c15290b0308078941c10341c1d8a60f6450031400034401100c074110092003501010609207048510b206035001259a00c481d414100842504020404003080741401020300001880441c180704031402072009040204956240400440d000400d80d416540c5400b070300382050012402400103036040d00c0056844d8850702c68014040707648108829003030103080707024400c103100f015850341183c980f01d031603040c900d801107640c2c00900c41641c82c0c680d401c0c401c40c10180010b105103840ba9018404424100009584210749196035600719059400b0020000360001418083c10501140703407401815040c03c590f402c2e44001d040101020002c0c040113000c2c0b42c0b1040403071804410204124000140100300150112592918050940c05140112050300f407440e02210b114101042c5004485 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 793567679 1250 793566429 793566451
    0x403080a090c0b0f07050712020a051017100e0f0106030e070b030604020a1b080a031a0d03110f070b0d0b010509090406050a0914030c070506090f01030504080f0304050312010608 78
    0x6040107403c0e181500140c49001880006101c400040340e030400c1040d0081840398214900b1480c07500512030b06520a070402802030740e0040d00100181d40c0080c2460001040c107030300d4600c5803145625101a0165603002409100000b410310642c0303903188480d18101d440d141c4080141c03c0c10b13090740a44030450340c49040c0c0084000e10001d42d0904003900240031844162518481e00d103a076031100d82d4100912103041e5092100420042130a54061280120000806ca1710b8aa07000460b000540114140c800c000c081103200b000c400d41144041240a04100c440740660300c030603441e0844c80c103598000d119a855050708110b1916000e5028104541d80440080c4c40d0f080329543d1034403094007070300f8090510840b0130f03a20801d50000c100c129504e80c201001e940e0245980d020221407aa01c1c2c13100d41d800c01c0d40308040400480c4c583d66103d140c0b0104040081c2004611075641d410821928000c803075000008030310000800c02001000f00042058420364400300d400e5036212803049070058401c9035060810 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 793568929 1250 793567679 793567703
    0x3020c0616121a03010603050a11031605010e03010f0f0e1c082d13140708070513060b030108010b100305010b18040b1503100e06031213120503030403080a09 69
    0xb0321000d80003407500b5002284020403003054000801d0842d40240c5c4140c0d06e03a0041841e0f9020042e030401d0307020030540120300515004155030b1851b180c0d400d880c40350a041c8914440e080e00c3c20b46081d0420700b15001104002c04c61700021021440140c0601015418940224441c81405004040300d0182d40344031076036100070540e94050391510030307944003a0002c0b014000c140c0300c088264035030385a0380c03040400100304104031507545410003d11074080d0035055241c00610050241c1c4070002146801c680d4103c900c1516401741520120007400a03420110380114008000300f04040c0540007a00f64901c19500c0d505049043c081c1101240c0081c001d5a226840410204194200d52409a10700140041c40010015018070000741c89210228a07182e000710003008101200344090448401045031207561591490200c000031303152140785132076800b403090124a00d954020045010300143c04034100086543c2c2c15030521a03641d82044804500241c2007500044000350a0300500c044a94080703491922 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 793570179 1250 793568929 793568957
    0x50601050d1506090212090f0a060c0504050d0c03050601080f12070303021603030504020306130f0204020318100f151527030812060315010e06061903020c0616 70
    0x8011910090b1100c01056101249000c81c92090600800c03d2100050351441942e43c50036007010005c0c42031840b80c11804060007048004200c1580d401e40c4100002441c010013803055601c1c2c001d41e00065088840319143c801044600540002507a028008840311aa6100d24445d502c6034818010002908615034042302002410094442c003446400c0150900480c2c204000300310780714001c182c0c00291101c0c284000d50509000f1140c1040080011204410032520f501340c2d040c1d10398200900680e400000a0008181c403010301103012800c40948400f00103920b0500040c240c5004440744051900d000c2502c0c41500c402c0d202c1c216000981c0801030918a290151210310721101b0100c0424001501244920807801c4507102440c8280107107611850844412015044010170660203a0b00c0b8030800500c1c81107010009044507492780c1600304c80da440703e01103909070040c0360298100340c48c0098041c816070f80640152202803030b00000c903800d03a07403404500f4a51a000d031a80c140401d2180310304801c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 793571429 1250 793570179 793570189
    0x3040f060e030114250201180209130209010612060f1a030403031407020a03030e0c180a0b04050c0a0e090118020d0608120319020c1009060f0906050601110a05060105 73
    0x207680c4020000158100f42412818070f201c8116001040b0940580c440c00d000340c40300f030008402d140b00380300070012000d8019056643d05880d1a01034850704134400001c105030203a90b6026186640940184e240c0e517500c95010740120241b61211095a0410304082042c40c6205d04d0307202103c602c02c11104a0802d81d4194001c02d47c0094800c1d4101a211503038002065a03602c642130040c00c144d0300401680c8a681002070440e802540b010f0002d40201008410603030310a4240c41502c0c640c01c010302c1d01c80d217910340c0d000d000303000070701402e6041814002040740414400000d09810ba850f0340300d1200422140c0c003001108402405001d407080303000804000e4903a1a075001e40841c05200c980054440d883d48901440c0c04c184002600444600000b0480791840300034024141e141010700640c14101800a0307184c40300c1245010141c0181e4902c2000203025281d00416440c0d0b142003010841184281040d2010f0681180c15074081a0700c0c4400342e10040f0005102201c003a0840080c103643d90130710003000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 793572679 1250 793571429 793571447
    0x605041802090a140d02040e0d091d0a11130e04060c030504021027090e010b030a152c070e01061b020f2106090d050c0a02100504080d02061803040f06 66
    0xc0e005101c4c0c400000c01610342d4483d0548038000c1200409100090109c02410000c06401040c158910003141c400305a10108c01c490b04001c80c2100440c4c0203080a04a194500910703008190045100f00c00150072070108080c0c0c0c1c02a401000b050020300200741c020b6054500a55000b50082c910344407640140c1d105400004400221500d00c480007081c0c52050b040710101a082446210340d90030080e00718103024404e802648600350301500c0d104107035032264601c03240700b0a4600d0f80c1c01e80398030b540e00581c0c5070300b18440516091011885e440403206481e11380c0d120554002c40d45402c40704400820340c540104d00c100b0742c031241001c2d012041015607007440005c03451080c995401256071030210300d90050741c4180005c0c0100802c010700281c617126994601c2c1030a526509420300c1020400103480303000c0800d0f041c01c1250166a00c400310850000111414071403940402128040c107200707405020360100340300d0701511207600d00703041d0003031540c0c03104c0d07180d02c01c91003030103100000d00320100034042c003483d0700c8 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 793573929 1250 793572679 793572719
    0x206040f0203190b090105250525030e01030c0e0a0b0d020f120a11030c0307031505031603060b0406080c090c130603091209061d0f06040605041802090a 67
    0x10f900c08580c1c0d890f010003003109182d01129040e6105040041100c07007441910762000d0f42d14485120301c0c0e604c0c102551100e4101c5560800c0020000ba4046035441c40c0200814260840300706140d140c4a41c1401005030794004041c500107400c281207a00c010b881801803000030500148500796041c600702c21044554042c55039111300c00c2d003d00126100d01c0e0f0f00d20161400c8030642e0054102890241c414104855400c10b0100010b0f20510600442005280660b54445039909001505c0000d0981d2001c55030355990001e6418801c041d04025540c41310108d00044030b200d25001d00c46211080200310a48450380655a01c03640800000341c25440c110b014260005555031901307280460f05110781880840c2a040000420b0b10b45e9182403c0019084400d40345000b00d00d0900c28550500500800421440400100038025901c0e10b8190f6a510342441036006070040403a95680d955000c043c250ba0014400d00324801b0201440d4240710000e4001c071a41594010030a80d00ea604100b07035820303849081014 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 793575179 1250 793573929 793573933
    0x6060301120c033203031b22081e0102041815030602030c1305040915050912040f06110a2a0306020706060e0703020405010206011208070b011814070206040f0203 71
    0x200001140e0108407041245104502104c8000302e01406032a5400e540c2d41449080e501c00c004025000d00740c14818610400c602403030550b1400901e118050142d244c00e892001503a00c41c0c0c00003490103002514001b04007a040440f0903607090154042d00700c0c011845204070fa40e005192800c45e4881300d520000303100c81070030040e01c0c1d82a242d86511080380c00c1207030355442002e000610a454041704911650040c5000c6505125401e0795a072000c000d9071b0b01d0f0b81030190b040e88800200e81042000d01910500c00000700300f240d01c0c3e56440700c101d440c1c0c400340e00c150400710f2525215119501404904200c03c5038024150740352142c0b02104280300501b45d0024580221018400400000c0c1140002d100540c000c0071f011607454141011451801c00c050204014507104000811080c2d8021446130f0445100c0302c218000a0158100144540301d40e103170061070210a4800843c02481a94201c1c0080c90185400c0144141b0380810005602e416110b803809640100c0000d40000c40c0c144045081c9440901 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 793576429 1250 793575179 793575203
    0x15061003020f03042006070f150615030510120b0c180a06030507080a0612080304050a06050906100803120c1e041d06030c18070504051008010312080606030112 70
    0x1103503074160f03041500c040b100b0780d406080214049005c88101e0641080c00c9840368985050750383c850580308010b801c000c140d004803070300100c0f0840196001e6030080c04d003101004580003660000400070312040b035290240c01c501400100b88018404a19984a135001c0c0002d02c5544903149903845035040008201944140a01c0c100b030f16440e80720261009000980b008a181d0504600c06402c2510003868281e00518120f0100000b14051745489070851708515a965a82c4030390400d5801c20000c1c01d0060901400c140500c03640403400a10f0031321a00002440b003003030301d0311007881944038130031941441900c40c1d00ca00420402000440107210700411195070364540344c18500e040c481030700705901040091100c00218a8081000340485601101c00c0b006400050340c840000b40c03c03000701120720b10000b04c0f0000024a1b43d070191040ba400340400509419501052140c02004540c0900040360f10680825842003214000c1c007409001d0200240b4507829682408628044e00350444003d403800d0b20089 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 793577679 1250 793576429 793576447
    0x3050705120d02030412080c0a0f050d090c03023c130614120312070503060604080a150b0609010914040204091103090705090405070b03041109090a0c05031506100302 73
    0x1070010884003020000268903450207003481e040c498504222003041c440c0700800c101c140784401d0304841140700d41d13003011001903110520480745800ba0304d0880e134100d89000821401d201030801c8900850b842203920750102c0b110f800081d800004003c01888520080480702d0010540f0700705500801400a4040150241074440039000e032402e40d4800c50300818041c06800807402d040307808290b084003000c002c500e00410b20410101444001308820200500880425095594075044400030300200c6c1c112481da2801d801c040d868000d002e85140207180c9800034280680c10510251200c1010503120444514a0b05200180401d41c4c6030001e0383c0682d0030400854080c14074855a0014903082034100e40302c2c03402641081c50484103421a62141241004010002d600050f091f0140c81c0c5c4040c1c4e890303ca4842c2d1400c081c0d11040070074025070200030a0100040c00c100010444000c6001d03031540c1210a507100241504c0b0040080507110f240001710004445041203203a400c21504140380051070443d10f4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 793578929 1250 793577679 793577713
    0x70b09040b040e0114010f05550503010623011227020f0307080316031404181505010f050313060c050309060702121801020a0501050a060f0806070c03050705 69
    0x1210b404d10200d822070700500511001481c1f540c0074120596511541007017070401e90945e0951920304900c4000144640020140881e08200e4109079402a20040030624803207460140058002c3c0e601942c039140c0002990300c007400c10040c800d5000722542280710340400045880380324011010284d141c944c40d08030f20782c0442400c0c180180e20007094900c4144407030710400502c250f140051911961142009000b050004070845084900800c0000303407200c0f40340b405a4040352515981003480c0720110740000d0602000a49088070010340c2010404116101d118207003129040c040c0301e0010b027149009804050041c001560030182503455401c110400796600c6041e200b10401040004802009000c0c50b6a01000600d81211240c00505805201c10810b0780d414080c002e80c40d9001c20010314181000d900030300c8081c0b072880c0c000000384042d00d464161703400175001601c1344040c98035004000040140700410043e0258256598801c0c3d130101c0313074900302e0300364001840c00e940078050106108030040c10 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 793580179 1250 793578929 793578941
    0x207060b0a0b0a08061f0f0c02100e0102011524050d0e0a020910060e060901110f01051503010504120e0310020a030c0806030f12030c040f090212010503070b09040b040e01 75
    0x511071001d542c0c0c00070183c00030328448028240c540100d962182440811a0a0b4000c2d81004800c1c1782c4080d43d0350b80d200003120f151441c8000a90031464a801e101c1d0f20310750004400000f82000c2c0c00a00c40e4104241040c40c16206da1300c00c0f0032400d2400c03903000441c050462205403040c000c41c41c0150800102851280886001c5d18003442d441d401140400214240441c0b000c0d8030152110b0030385e03100307840c00c40090b004030402c5500741d04c50f100000d6104140da0103030742018004001001217500410011803198024202695045201c440c9219442d43c14501402005d128560180d50303801e005c4840c82040c1c0e21401e201c149142e06000e682c090201d242d40d0b52000d00365601c05940c0220720201c000700b01820214020b88800c2c040c0c2c001c1c0091246c94600080c0703030342e00500f80d01c0390710ba902e50311116038881a0040d604042080d81c407000b400241b803040398029048041c102c0000c031119903a40c8041541d180000c0c0700740340040c24107000010700e900d4141d1006601260260010510380c0071041a503003150343c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 793581429 1250 793580179 793580189
    0x170f0d060e0a0c141602120102030a090507051905090601020a050d050706050f041a062b02130b15160f0f0c0b09010e0f030f0d1707140405040207060b0a 67
    0x400c54082040c6500c150140c015011280e04140900280300d8078003840c10301c118200b0b85e60041c01010380004644408003c0f0501e40c01010085450f03044c03014a40010f0301400d2810744e9944111400420a403134403000851000f03450384034225419107030000340031400e11700605450660144102d2340c00492410b01070f40700e0030400b82d615140d440e032031450100102d60000c0d24005c88a80740104000004417400d00c20350300c501d9400b501000300d0741c402c000625500042c82206840c044420b00304070004d200d1011240070f5901c2154903840a0324445e0f090000c07a4102e6600355840031051129030511384612004140c00c00001280160305981616120010540030b0412150f20344280c3d515018400e01008910150044034969442c0180100000380315081d41c603203603849201c4660f4405500ea408019025080c4003030020b8034841c2c41c0e180405013040e69400310301202d1007440c000007012284105640031040b440103603c1401c1508060500000f03400c10141110b0841c0c2e00c031000c1296643c1c0030781e1070000b01 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 793582679 1250 793581429 793581449
    0x1061a04061808011409070906060c08030a090c080c03060c0702010806100306090c0519030603020f06282d080a0c1b050f1204050a171009111804170f0d06 68
    0x1b0800360b02c02ea25007070565121040c502d14000060000652007924040d6041d0003429103500d907110544284010099001c00a02c000f481d00000901c00b1008515412885400c034191401c0340e8445d018000248201d0710000d0014465000003080f61a100e01050100d03151454001043c68613001d20104403600ca145810210b1004500c440001100e46420744c01c1c90100d117820f00c012481d5030301085403040d07101d018074416680480c07a014850703000340e464805494051101403c483c20000003800e1403010440140030b03219040418a00d0601c0811000005282e9a44154182d50f07000d040f4802000800f203903804202e0800d810411150030380d80f0700d29000b40103501402c03011b0000d190082c03900704019400603189030140004c01c8035a07581e22410303084400c40801446080c0c0e032030f2410750401d2454803188507010714040c1e2140921001200e010100c00d01910441c01c00c94003042c0507100c114084400a01d03032900c0110740844080500d01800c84030164403070300c50904002400010654600f034100301c05407 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 793583929 1250 793582679 793582681
    0x30b1912080d0216021c051b0f1c0b0907081f09060c0e0a0801200f160b04020906091501030b0f0a031a181207051e010c0201061a040618080114 63
    0x1d4908680f0f00c1042e1b8103600300882090603903649003500d481480c00030385005074042d01154000c1e192151020320480c0c0050107400e11500c050502000c80400b0b0100399501884c040004505030b40001d5640c0c203a520850080c0b005810012000803580301f466004203116840b040700c0000900b80b80595400740c58552502d8461140d1002400344504c1d0310b0344211030b281c0c100004000010082c1d24000036100e62440050f94030b10102c030ba1b82246200d600551040740700264645018000e0a808281c001e80c42154070100d107403181000c000d400402520b00418148034042075000a40c0643d01061070f070356014017110309130351941002480c0b10406a10544841820b284400540030740d000300b041d40403c102c0f04045001c400820a160740d030407945042c40440100046410900804105102c1e121107600c1001d8044030954076028041d100f25030a1001540c00d082c00800c50f01046003281d143c1a210581050401e4600103048074868114003004219250200010515110038002c002422960102420003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 793585179 1250 793583929 793583933
    0x91a07030e060f1206101d0307030b0c0711090415090f0819020709050405030304030815060a030c110105190c051603020309120d0c1211070312030b1912080d0216 71
    0x54003000a044900c2010f109000f2281150044107000c44d200110307d0722419401e00c0c43c00310717291110315000600344290600c2000515003003003005110342032040ca880741005031500141305413118152402842e907558206136044413610b940c03001119038080d40303d00002c60302c030361114661548140d18215210752075420240c90680c0401480c0b0040ca0401c0e400c01c0b4614013903ca07030f500d078040074100804001100c000b00d80c25540120000304145c0c001003102303640c0c03803070180041d0040c203e10042e400498280303031031039568800600c20980304030821140c00301c03000e03081481c00c0e0003401c60744021800d108ac14841520030300d524a00d1400a9882600255500c40d01c20040014819510340000d442e5031180c0d040710301140d48030849040c10303130b4401d244900070703c3c0c4150281d80000030300c0c038108a00d2040f45800403c0c4122005d5030400101552410003010038260709001c2c0306054200a1040100806010000050003181c1c0201c1c1d54000e0310681c0c1002e034a032040000340e92002c81c43d00c2d06000d07414843c0003 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 793586429 1250 793585179 793585207
    0x90319030801171204091113140109060e130f020c100b040501121a060d0b100924030206070303060f030b0403030b040c23041d090706091a07030e060f 66
    0xe0f61a0340c0300018a10003502c40c070001e180340b00d1400b81114058455505412080d00030b8241c0d50914a08a07103e07140359292403c0c02480d1408251090025103005400280c040c015444800380e003c5c00786c00b80d4840d0214013240405881a081d030381e2803203a4204212011010305100511b000240340c0e0020a450940c00f08010603208180c0000e03d180d45201e00740b2002503103864081c0c00441080461400564400d0000744281036001009031810181c28100043d07034100c0407403541a900c5460041024081c0080e0200300c11544181c4607940b508100002d001603c0c0400280030780500c01e00d00401c2a6844142445a40c1640e90013200c80500401c244002c042d014018445900000c1d030b0208510b007010a4000c002c565144d01c404107500742002000c100031030741800c885c041e0210810ba00c0d06060300070040300e130200080340c41c03003032a01036200301081b998424080c0c0c904803201c00ca420000c40140a5000795039600c869070840602144001d00506a01c0b110301070102d10003440b0740f05894456010180d0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 793587679 1250 793586429 793586459
    0x20f0f01020f0703081308031806010906050105072303070c081507120203090a0204180314030403090b03090a060c0c0312060b04090b033a05040e060402090319030801 73
    0x224199005116003403940c0800c02c25151420b800d403500a4003511507480880211821246c080c0241d031000003000015149221210011203000080314942c0e0ba0f1109280b04680840c06242c2c00030750100076000200c3c4d59452005031034140d811364964040906580c5d10314590140600b10740a030340306070003041940d1081c020b510a4002501400c1000d250031580103040d01200140c00b0391480d8080041041c4007010800c1c0420107a014008200082c82070a00801038030454508034002240e82000c42c800c2201d207025a0700650745134595070441070400080d0580780d00010302c1d40a03d03104401c4a0b4000c00c841e401703446401c881945071280d4000c0700d418000c1031700005070340900b8070340d0610741c04210380e8100c40c007210225030a04600083e4121141e00181c20101a8165408401e400c40980e500b00300302c0c0268007180803a900340940541d0f4103070300155254001c5104086445444500244040c1020b400070078203404001d05980c0364044120302041420245407040c0c000420000042c41244908225a = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 793588929 1250 793587679 793587703
    0x90c0112060b090607110414100602011107230610061b02011d0102010902060301080102180111150c1c06050307060c05060112172106010306080d080903040b0a020f 72
    0x14080e940c104032009555200d1a10306a019400000d007520071b001070400c4440400b40024010721006141b134103000c06100e010b40d21a4448580724000262041c0140b050030380301c1074804002e504062158032045c10074804058a804148440361402d98051420702038030f4400c400000c103094401d0f0074903a000340311030b000102d0f441610440009000160703030013a80414180c1640c40280c0112015940102d01504924000a4002c1310200021800c45410340140084184040134412568003460046949201a01c140c8000e5000041401e000c10b03c0d10010950204007601c1c02850320242209035078101c11445e808441c00d40d034400703050119250501c10782000b04114541480300011700d8407200e8903041e0621404140c0c100a0b0b200d60708008104041558101e07a04a44c02e4031030f41d811201d60001e414600c00d50281c0c1e00090000fa40c03660080c4615026203114100905003a10510415110450045c2203d2854403050000180d000781c00c5004101204855001c6c20581015004080c0781c0b440d1003410b = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 793590179 1250 793588929 793588931
    0x1e030d1d0108060934050405040f15090e030712030903170c270d0c030623060f130c02010e1e0d080703060905040633120606080105090c0112 62
    0x140805540d40c81c0309140c000e180c010684448480405c880b01c800c001c00e40b03003841c0810044002811039900030020f4001c5034000c0e1800c0c005802d2425030304048490824140d00095454030b400e0010030103d42c00300b29401030400c1281d20384655902d92152002542108000083d2103018810415621264075550b2800c01076101e0b1090400140300c00c0700b4056800071401507082248182e415581103001101b03039920140c10100402c000341052001520301d070100390b40f100d040241469000c1907546104954100641c41441c0f145c42d07100800400100000d2003641c8400120580d808010880c810042c0282d40c0740c000044e43c2c0802036000382030821f4503100720013220b10303a445a031500300c02280e403401c200b1252a207a45103507186507054004003074942044800c0c0f454001008104480c550049800c100090b00d05101c0400c1e0003140c500c01e0400c081801403080b030215040104140f00b08245013414071580c000300d507550715810b026084484c12603c044003580001c003a100c85507000b50301c0b00760003030780c0d008 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 793591429 1250 793590179 793590181
    0xc0304051507060b0121020904090213091707020a12020f091609080a081b0f06010b0307111c0e1309050c01080f28020d0e0601140307141e030d1d0108 66
    0x341020841c82c6d01000207543e5400055038202940c4541c07000c070381c07180e00030603600b04120301501c01c0d401801c010718112415446440342041c02c00d032042c00d40f02c1c1a44e0003021045817600340801600c510019401c101d811065903010802071340d0307484003110710652080060400141c0c5181c001003e00a0550150465800074500c3c000420010421100080b00040c00e556003600124091071400c003030803148141034020324002040c01d118003401140108406c3e56805d05511001c41401d4944201e080120055841c90709004455030044404450010b8010002c1450501c0100c640307066a09040c0b0442d519005169101815030304017602a4204000d081c00d00303101d06c0e01e48a503030801507014082c802c405036818030300074901c4070980441c0c3c0260702d080018480d00302c2da000f06558500c4280103c28a80c8410000581d15040c0042c084c030031950ba907640a51007050398404e0140f05c030035912108803803038038240901c4a580c4041042c1e0186c0403c6541e607141c010a00300902101c28140480c90341008007401c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 793592679 1250 793591429 793591457
    0xd06051c030e01180915080a0c06030c051908150d051c030908030a0908090a140f0105190c05030f0c0304030b241002070323012a050c0304051507060b01 67
    0x104c030582a6590070b000081e01410280115040d00c1d5075030310403541445a07501c49010089110aa4400c550098906202c100008117040e16180103041061500900d85c058171314003039108016094118000c000d581401c4225840480c041c6d04840400707541c980d10041440b440c0b000502c09a50004000303240400c40d000f95640c0d2142240700182501402da6103c002100a01507442c0c00c0f102c078801c1c01046030020a50394034004d0f400302000481603105401000001c1c0555016004640200800c00a103540003c28500240e55584001400b51190b03c0b09020200b8155101d1001f0126000108015921149149084501400d0007031120b414032205c9861004099510751028480c40000c0303840c180080c00c0144103d203450140d40c000750100300c030000308061494000301003e030100c0e03c000088c40059250000c0c807560601c0c1f00018000074a1141c1682420f03403188010784120650381090380e142c60350360b000140d0426050042c0440b00100064050704100ca54810a0310302c81c2d007030809a88070021a = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 793593929 1250 793592679 793592717
    0xa091205030712020c0a0e04021e060d11160c0e07030207020102100203071b111207050f0904031103040906050418150b0301020403021e09010e0f07050d06051c030e01 73
    0x808000d0682031000810f8400c10b00130300100800003c0681021185591260701c09021a02170b102640074440301d1000c68143c1c1c95090354940f1882c1e01a142c41d141801c0d00d03205070700030100c08014450500041c0328400707641d0404482d40350150702589072105240e0400e4409203004030007038481010b040c4100140700040c0d0b0085074144640602007001616540e5550303091742c0200c07280c800c0c141701401c001007040801000b03048490f0000c6081d200780c08025181d01445a840400d4016540d0100b04203845c100716291000040e5407041c424a491207440f03550000042c03031038002d600305d43d900319103075481442a42824880c4005c04201c40300141042c2466890b000d00c003640e40a034643e41d0503100d802a071450340702501100c0c01990701820b40624075844840441c00d0070101b84000b845456020000504042072100d01c9004001c44841c4042030b0300d41c0b44080c3c405a114807400e4144903240c43c030000e1581e48404007002800041c6400d0400f0160341d1400418407840d104015050102c075504201d104469 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 793595179 1250 793593929 793593937
    0x4020906061c02030c0c030d14071107030807060902090a1b080c0307080703240911041518170a0b01060815040905010b0d0321020a0c020402220b0a09120503 69
    0xe10000698984805000c0c032441c2c0b0454807400d155103c005544281b82d48c180e4005142040001070000c040c3d214004102c524280300d1801140c0307980a180d007800480c01e0000200070144c4240d100192540860780802c8407944202d45101c2e0542e0f84860300c0021105007514001c01403000e04d041085031502c41900700c040d0101401d1002000781c15000074031454065802090012505281090001000c0303e60180e98000b81c0240407000b07091049400030088070001ba1000d40c1c0e005400d600c0c46160000b01140c04c0c0024407070b4120f48005242c800120006003605064a03c0f21207406000000d0807410300b2088030206a000d03008201040041000c040304013004008080800c039000315000301e45041c0140035001032404158045031084c1c0c141c0070150000108010424260003071381038488031000143c1240108141000802c042242080c014503207580105900500301e0440510352505401d056001c0701c1035007060102c0c4a0010300030740c009800c0403003080104004000034000c4013a80d030343c00b512405 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 793596429 1250 793595179 793595227
    0x307030c12020a021201021e0702030c1e06040f090c0206090c0d1703090616080108030304020607021909240305030a2d03233601050a050402090606 65
    0x100001c2028111842801100d01054009140409032194402d03003074000c1d4001000c00540007007414004114101c0041a02c803210740003005008954150300c1400b003104904e00d075840c1c030050700900121660f81c072080644080c1c00044820040700c3d08180c0b85404440800c40403500b5548070808000c0c110070005201c203400d601c1034401030f0428505141c100200680e900718000003400120130010400340c006010303445581d50700380550644d08620000e6884500038020b01000b900104005009810440014840c1600c00303060700500c580d0f6610740c0c1c141c43d002a0004003050341c8070301200c00340c0308110030301d03246002c0e4018001c0462441c42c0d80d43c2c0d9480c464240c0c60740901c0454000504045400000c110317000c455080c003610a01503480004000b001486507518508240d6141403503951a0151014450f050f000c80007225000b01104283c8407030b1504103c1e00faa12071408000404140c00e00601e401045c86480101d11810184100700d2064001031825000703010070f2101103e0f400c0c2c40080380584034 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 793597679 1250 793596429 793596443
    0x5030a0e1807120b03010212040203060105010c120c0f020d060c081501091a130803090102211804061d100806071d011b21031a09060f27090307030c 65
    0xf01959035510181a01c12281070b8954404104002c904000c3c56016204910031000c0e128aaa202d80040d83d203107601078800f510740e28003200c0101903039000e00c4007144081e00903e010614880c55134001a01b254200d0360843c0c0d00c584620220340041c0e0080445500910001044a65950b5200000f0700c1a00c03640300c1e80c1d226068191502000744802c42c00c650303040e1710307295500711b41c00e85031020156070b03038001c00740580113210f95004400341103055590b0b0a0f04210010b8038500d4007405000c481c100c00c051b07036540799005544031000201e00003482c0074004c0324031071400c40c183d803482c141082c1980d103c006e40c04503403203801c407030300304103040d540320f0f030202140c01c3c1202c000c076030704945040101c1e01c1055041d00051110160030449040c8049140404140444080542580c0c5460340c0c08909503040d00c0c1451134114000061607503585010518140e203c1009070643e1906071800001500045441e00f044c042c541c061030b09400041170302c450389607004444200841c5024640c0d83d00611944040401410803 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 793598929 1250 793597679 793597697
    0x601110a06090c15050711030106140904060e0f07180506092706070c050607031104121b15090e010617180a080901090e010f030b06030a06060305030a0e1807 69
    0x60048002c80181049400e00c91132011240c4001e0410ba028010586083c06541d0510380c1c03030700c1c05005a4065803400640c9040c5014030a0a002914501800c101c41c6103458111902c2c4914080141103102c54004000380040e40c03070682400714400710003282c0031800b4103000c10400aa194203070300940142c80001101011815080300985070308540540d440b1602424007846070480c0e20000081c0400d0141d000c0d20340c00c0e102d24400741c048070030800310381d18407a0050000f0020801e1103140740c4071250003a501d0700110700e00c075a8440210746503034116400386e07034404058141e031355070050b903450207800b0384540000d243d4189000508104504010520b4803802840090714107002070a00205541224045401090892901d100c0071703007144a03100c0c001048820f001504e8a001e0304032074102ea031003040d1014a5815500c81f814120070040030280c051080701c480c00c2c005456442000011030190010319100c80e00400000c04849007081c3d484e110b02e020049000c0b482c0821014603030408180d08005c90300d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 793600179 1250 793598929 793598933
    0x11508100e0c0c12090901080a05070e13020406080d02010e070e042607030c15090b0c070611040602061005040c05090111070b04081e0118030c0c0b0a12050601110a0609 74
    0x1948101d01e2010f945000d122215280c07050924040d088a640403600c0350842e0f030300c442e2001d50f244111003018020703900c100d10400096480900c07458104010030640e5203d02c4280e00440c099600380e9108040303551001c41500c1005034203101e600b0031020325a020b0101140b0782000c0f034001c21400303007000d000606155111407840c4039101c80298007424600b47c13a6129030036410083d01d034001e82c64040c1c50a080703904240c0358a07070316807107018045ca500501940349921540518039554002190456015070b58400e5005c0050604000c3c10003045245d008003651702d003400d52203580958503403005003e01e00b00300c400904642c10070140d5030321040a10307000d40102640e1210701d00d1b044190b071000702251400035008c590f030b55020a1139070080c01c0348280c41801d00c600d0038201e4200c400c510781c101402410b0703110070000a4810104400400d0040d0202c18007151030303c81404031984440d0520003c5284144007001d10201405400d074005003d00300a841407190200c00d540f0364405100003008984d94110710b5013 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 793601429 1250 793600179 793600201
    0xc0812072004140c0702011701050a03060209030708070e1503010606090504051e0c071e031b050109080325020a020a06050903010f020a0302091c020307060f030b0301050708011508100e 81
    0x3c4124042c050500b030070b0501c00c44014280e4070926040c0e00040d20b012000104083c82d4824038102d6601030050b490091943d141c0c0c8000303401c48051540c2c1400362203c00545840c013000004040c1c8800b0030229020b08040c084a8810b10560314040c0c0243d0411204002d400d0b0040d00342822240b003507501181036503d0000d8107080300c410381e9104d03000100440034042c810710000c0250480c2d034840c824a48d82190800100c109000035040c00070000b030400b002504400c6000d51000c45140c1c480d00011403044000c0c0c0d6031003216003045900f00d44040303104001c00e1075440780c0410102004403d0000e45051812500403400401e250b000b520240b0030005a1403146441c00d42c4890030070b0807200c40c215240c005900d0002e0280d445201054481d1440e46c00c4089140304030003500a549a0003801820501d243c0030b01138030014201d0920703406159890240c81103c5c0c4080c0200391003030125542e461040d41c140000c1d2002c008142c0c03105030070003401e44100710070507070300b032280805541001000b80789580d04c09413006 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 793602679 1250 793601429 793601441
    0xf1401020c041409010609020f031512011404121115100b0c0102120f01060c03030906020f031e0106030207022b0f110f1c030e010e0406030c0812072004 67
    0x503049880d0803c20b20803010002a02c03030207081d02c03000a0026565501003502a4040d03210303604041c80d0304001040751440303005003000c107500010303109503240c011a501c1c15084800300f890394094244680100402c001c0d00520b080648182c81c1004d1800b0940b4007101c030f80c0c46e103448000880c55140c6401050501061100c82c00080a4003180a6590411240d400b4042d400c031503440c505942c3d5540c0030521022004c0b240700e051f543e5039030b01c8140803015030b04c0440c003030681a80c007507a455500308641900365809600840c41040e100c0202ca4540d5040d4502c801c090405a1007002094814840000140c3c0e1f10001104001100084040d81c40203201c0d410f4084244a840182440302e80e40303456003049010034031020041003c403180344034024030780c0900640100154103040a4141c0101041c00a0b0003110718101120062400c0703042d510445010400700d80080d041554102850790080080007000c1100070350420a0261190130b01055a50780460030580403029064001d41a80340308090301d07140e0002e = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 793603929 1250 793602679 793602703
    0x110d0804150c2c130218090106020115060f0c15061203020f010b150712030e0316020312040f0b07031202031314060103030503070f0201021c05011d010f140102 70
    0x1001080e400c00303805060301080c0d00041e458010b00107204402c40380007030703121200218040c00c0d000d0100c1d04907003c00025881015481051b00c40e00208640c030741c990f01d40090203000550000a003804044001d000c1e0064694480310420001e00703006120244d00c0401c0078035140d070040c03644c690244550780c2d00740900b255400510444403102d038864107242d4001a0b1188082c640c40c0204200340c0d50b58288501c407a003803401001c0c0c2800c100f00c03400000304480800a40c542c40384c64001030382e0728104002c60450740202e07046601a100011003030151310702444400c41c40c10941000a01c1d1915002c07502c3c56100d6240300d9410f2a09010441d04241406030424012210780301c40115541d15200c41400b010880b0075201f0344091720000701c94400711100007071442c141c0342c06886450031583e0f500f800710348110f20340b2a003c0455400b4414002c20444944c40310401c1961100081001c0d070424500d41c54a030b00b082c400300c0444d070022004001c01c1c8502101c1009a84022000580741103105d00140d280032030030f40da0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 793605179 1250 793603929 793603931
    0xc170706120b0121021207090305280f030201051b0403021c150f020a110303040507090e03040e0a0e01050601050f0403150b1f08060109080705100c05070608010510110d080415 77
    0x318104c1112554010801070302400c0e0300146036180c018007201d808800340401044c0e9400070504407181100002d6801c100c0050880000020803070342d581c3c2400c400030702c20031000760307468a0030b111032004148000c404100f0350410483c1482e286800050a030480d0804242d00c2ca0101603071704043c4101c40403480111050203e040c825600f4124040300250300034601c3d403000807080303040080252400b0080700d00440d0410014401641080e0741400100109100007130148000c100000702c0520746400c2030f1041c080140c2c0010400812a000c50940394000c1405042203402c026168410309088107960960303400a4641445003842030802c4001e21f00300c101c00c0c1d0f0007405024850149404c00c810784c10044001e03a44c00b1199180c1c0c070015900d8081e0382c0500350540d000840b0500140c2450b14442c01c01c140e061411204400031034660901b0480141c01100c000340d044001403100e0300b00704031000c802150501c0c001080c40403c00c036035500e85810100440400c43c4090200d820700c02d0f02e101c10601082e0000c0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 793606429 1250 793605179 793605227
    0x20a110712020108060103090f022e02030d051509040611040323120f12090c0604120c0503030a081302190f090e01050702070509070512040c170706120b01 68
    0x5040e02007440e84030340c01ca000800900000d00594404e002e054417039648601e0310100081103a00700403400d81122988203800703601c25207580101d2002c090014100c02e907600a2b587e0f400007402008281c44006001104188880c10108029102d00188940c02034114000180700c140c541ca1001c400c0c4030710381c80034240d8180f6a4804454004c02c01c6407011001120080b603010002a912440050203101e00d03203841c0030001d111305c05400701c40040547e805441c0070f080d154509052700000d4800d400c0368010f41c80214011520f881013090002d00800500300850043d410301400c0c49000308060700080c2010340404c0c80c070410b0421500e81c0e8880c00555496100f404000544a46441d41c4c1c407469842554074090400c02a034807a0207040c460716000300007941c05410a1400c5c0400d009440708040c110f20200b2004100c602d80c1d281703078000303504d01507481040c00c0191030389060310340740c2d03000c40094100445030080c00301044000d4022000301142458aa408190a2034210044c0c07094142c0414040307440307480714 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 793607679 1250 793606429 793606439
    0x5033702040e0f0907060c0f020a0b0306130506030a11060c07030501050702160b040605090d05060c031602030307080429090703020301060608010614030a0612051006121104020a1107 80
    0x500a001942c4414407060000c0c1c0c1c500e112401ca0000685010100c2d401404042c0f03c003510a01c06604c02500032000309406a10b250f020840000680d40720300d450b0003022007809503504d014070750505141620841031285040c2080040c3d1981000c0e48010080110201b1408640e10f50b4819905c111400c101560183c82da21b060040c0642400c0301c94070018055200c401040460600c03220040c4c90180b00790500f01070819805a409034031880320b566000441410340d2303000a004100040c42501003100594036828403581071180d894044e080e1205541041c020040ca980d0310016240c0d109400c09092000320541c001040c8c0150300c0300301d920f0041a42542000f4560400090880441740b082e40200306c1c0ca0b55131001210780000c2070180400054600580101d00e8100202443e040141c1000004540c2d41c2c5101c0210019182c5004851507001801e61805070101807091900a100790030001400100542d52403d861840e2001c0700c0c800c907070118501070341c40d01c00d44000c0754420700f040848030341540351 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 793608929 1250 793607679 793607681
    0x7060507170a35070c0c15030e030f0c060c0301270e070603090b0f040816061104030303090204050906010b070611040317070510020f030406020c0a020901120204150303050337 77
    0x4003c0c0c1d1460103520408902c501e48200d085d10702464204101240540c10220f10000403a171030480f0100701529840140c194043c240300a100b800601400300d40d41b489104038040c10060001d002141c0910240010008441603068200ea00c946410441d04203410b0303918050700030b16807041081030900c103c0070003150080e05a4418106180a5054400c19560384050064419000c88004001c4041840b007800c822030041001e00c54a4412240810708201200e0804869001b5900640020b915984a2400e41c01c7c50320441c1d4002e0540c40c0030f0440c030b40c1403400c004520f01c528140200b5640d40c644081990441280507200510b522910030134059606c1008407001c2c2e00001d8040e10b080c060101e006600301c0c0c20340b084031910b01c03001020728190b585a40341c0100130b42200c100e03107806020b820398240060342c0d10305800740a800c0800d10303001d04011ba401030104903030091a520790020004001800425002810b903070340a000f0621040442d03125403964201948508005001402002c43c503903206401 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 793610179 1250 793608929 793609007
    0x1909030917070504050612150702030c1618092a050604080609060a0b0306070f1e0f020f03070b010e041a01030302010902400612060e07060507170a 65
    0x304070b84c280030a45030300342002030070382c0503016243c00e940c80096103050291003640d40660159140c0181d0b403c01c08044826801e00e00c111000601185a03e130040c8020285210300d00601c80142908009810b1595105c0c0e10781c0030840b00c11400031424150444000d001402c02e14082d1102402c02d640703e690780c0c1211951900e00759011034150044600141a40c003491141d003c681c44010001c21030341d01c5e540700a441d04038045104a08200b6450f131034010b0400c0c1c2c103a440e0180040da030754840440c000c0b43c000034244420079103a036009030010841000840c03d03405407141540d0014100c044c19440d0707844c1181030440e16101119444980f000000141034065111420090081c3c5000c1d414103078090425200010040845001c0a200a02c91580c05d85000d001901d070180c0b404005600c0b500c8040314046800401c00c111181071f01c840c9641c40110092180078000c1156080250428810ba611a103001540c42065000032801150b11040584110180014032144003844158031300d0441008248250b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 793611429 1250 793610179 793610189
    0xb0a0914070c050a061d0307030905120a080414010207050a09271a04021c0803061905010504120201020c060d05060907080c0f0904060305030a08091203190903091707 73
    0x50100280903a03014468030a0740c1a8050060266107103283e80b80c2004001402c2c0f00d400306c28042078074901d0104104028090703140030b5125030458514010802003a6540c88200d00020741082c07444100040d070321800e0340c1c02d880340c120505240c0304031400101d10340040c40e8000c65100a0810001514120592140400083c4000000d11f0507150005a60301c100803094001d11546004484a0300000100010b80d00a8801411004a55500200d100184898241c182c8800ca000000e2080c6440c2100310800c140d5001224445240c0c0351000180c1207008510914000c17980400780e0ba0116072081c0450308810100820343d075202c0504c0d003400c100030602100d075503029160180204543d031f0f000f5040240300301d03410501185002002d503251801c640115040c5508a51140780c00300016800f03002418164409a480c40702501c1d040c5203461074280b4200c10054040d008009000d4800e0203980c01000e4007100c980089200001481c0031106000964030038500c0d0751070045407070075070032020403a041121 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 793612679 1250 793611429 793611461
    0x90a21080a0b06030402131514010206091902091e010e181b010c06090c090509160e01091e06090605010905220e03070609030503182e0b0a09 62
    0x2a9800d001c200c11210200c128562012080c00001c0062074081c00100c2d40019141012401c980d00441e00000301d40c02c2c0e0840229240f07251030400c0b080d641040060f501910840050060301103c100004507442210b030b002c1d0080841000080104a01c4820f42101e60342d50103142c061503030f64a10116006006030b60f00c580c00080b404850030b0a101c0080c00c0c056103403c81c4203d121040007035006480007400d03420201c0f152503c503804a404220307060524002020817040102d02454603c0f09141040041c441c2d40c440843c00083c144041e6420882c1281541c506003000212080800c80b071442000701c030160510400c1c1004008900e0311241d4000c1001c039082a00c1d9554219225410070400100c9048603080c0c84c1c0c030118641b0003000e07098102c03000d0f4101002c1502e161170070603204d400030b03103c80213415400b2400c0002442210140200c4042d0021812005030090903440b081485003584c4150002132000500300d2107001060b8541d002e20f5852500403d0985507030794850041010b80035040b404020341c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 793613929 1250 793612679 793612681
    0x70e01110136140705010810080a0611121e010801021e0a09050a0b040806070903020306061311070605010f080a020303041707030b24010e0d0b090a2108 67
    0x814050180845a1065111020740c0c941c0c80c5050090b00720001100b001036501c0c10801c0b0001c9154080035800d080d510b54042d05215080038009414120080c008911401c6480020804000c000c84c3c100d0102d51b0111001c100144000c01241103801240c4c00070001c02c3d002c10070f102d5240e00242810994001000407844181ea0319441c035030817400b494128201d50f00c4029181c1d042c8440c010010280000d9904100503030585400100b80c1404440c1c0240410300d100280510109008000b11079109200c0d2a191a8050659000c0b984400e0040c00b418025100144008110b0542e900108002400c1032100c644891702810814041c1c08288100300e01220707640004150b01c2c3c07000c90422075241c1c001c2d00540c980707417130940c400d0003006c00c0141d41409401820f0340800000d40e44100c0f6800358944146030300e00c0c101a02c00b03414201c102c402c0118103001c0780c0000d09681d5140e441c0c0c504006604109010f4455668903046401c01c1a1380400401801540003100040908002c41e100300520940c3d400d841 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 793615179 1250 793613929 793613957
    0x509090d0f08090c27070503010305010605060901090b16060e16090608071e0806040303020c060f04020901180f15080607020a08043b0a0b010302030624070b070e01 72
    0x1840c0c0544140a25401101c0084c2080c288100c204405044405820340420382c1d07840414402d600945440000460010040003845400d0048001034230301121002c0c900014580003900d503506500c200b0000b000c010620f000300084d4102c1c0d4851164000c2001d11041c00204a00340d1251401c64441c615411038446c0400c00e44510310451040e02e213010024080c1d00e003481c41644158180c4000b02442c450b441d00c01041101c002d2244900440c8252005a00c1d621000300807810150000d020240c00043d44c400c000160b43c45201e854112110700d005800c014a000c0f00e0040580f0703089462480e100d003002c0f11900c0900881d4544c00c111128881a20569215031b48100e8603004001c5000c0d101c2c120900003404038441c01450202c10010190702010160516030000010840145a201da01c5902d04200706081015006070880c410702440c0071461450800c00040d0720580000710f94a407226010000c40211001d88211040b142c3c11005030541031401540080c21190008130b6035000520040103040 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 793616429 1250 793615179 793615187
    0x61b0b04081e04050d03110f0a0312050c0a0906030e0106080a082a030d02090414070c050607020d0c11030a15021c090308070e0109120503030f010501090f0608100509090d0f 76
    0x36100005c0540c581d003501d545045901c40000c210b031034964041c500008e00b54060402003003406603c030b40c4070011000308540e40c0e0811103100820240d501031007004a07408041d8014550410740d020790400298201c0c520710013900412050300405054410760400038184100100949410031040440c02c040900c00030401c40f802c40c80a82c248001e510500ca8003048135a541c02405030000d003c2c0c00041d00342031300e204405800300280e6646010910b608094800e212061100d264060b015000400d0102c685d0380006100f0801f00e0302c0640084d03045448000c1d1a030f018441100c0031078100c800220062000c025080095120a03d0300c082c22284ca0b0015550356140e00907480d4140d01074440f80c0b0165551181500d0409112464074100003c010020070411041000400c4d294002c0c401583c4914015002c4101c400041c1c01c16814012145003c000d0349014280c000309580581c0343c0099035840d400c5051031800d00580046d80d210400408214002200003000844040c441d034400e0344400f20b250003a6 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 793617679 1250 793616429 793616437
    0x50f06030103060209041803113007060b040903020f010c030501030b0c0717030c1e040302060a050c160b120a0506210316030c2a061b0b04081e 63
    0x1900144184010000314101c0d078098410704001070070102d4620390703050b240092440841d004401103582a03c1090b80c58504101c09014103800110125040c01e02c404490f90724074611030315080d0403900203100b000300151501300d5200e03200c0240c41405010020324019407900c40404043c03079250703c0c1480b0781d000306119010700c5040781c2d007206204290380c6501010100b291b010300015181103039090421200c3c1c1c5111402148182000000c00703803900011201100d600003c0710095484c6c10040c8000d1002d0b9480c1c41c00c640007804141846550b8180d125010744c1006105018212101d851400026040c1d202c807000700445007140e2101e5001d42c3c0d03100c10380030407204207561054008040800e50070385070040070510210b01d1180001c03241040408403020500034180c400840019640c0001d000401540c001d000e200d4503030350004004810030401e00280048010b02c501800c02c031113010780d00460b2000304406c0b64001e0b00801c12101c6403409042c09405503201c68a034551014591840502d5065610165 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 793618929 1250 793617679 793617709
    0xd021501060e101b080d1103390c0304090f021e090117010305031827150324011205060123030d090810062117040611010605 55
    0x84080030b50480e042c0b280d40700701c001400c014040381c00035201c030381304010350014241481003690326612030041c40c00c90107680d2803080e2006580014828003180c06d40c01c0d500f030000d000c0703682207122005601103440c140780c8006250210f17400ca40010f240c506040040300800a0380e40c1031030140210318590300c03000200c1c482c454280c510b24800240c05404c40003110014801420140b4280b0401c054800b061403c1100a030f00460321540000340340960005149852094074804a40c81d050688101c0e9a0301a42c040040c8580285810200083c001c0d25141c2245114243c2c058129120041240703244044d42d1140049545060140c0d400041d242c0012502c00c03400c0c65104002c0c100e0742c0d01e025101401030b444101c4c103140c010071030000310007580c0b800c02c9400c5009110340d607040d8600c1c1c07610081c5820001018076007000746041007010f01c050082401c140e8202949540900c500200e50b08001e070740340140c039a0000803290001b03400142207a01ca44040d1401c03804000130001d060b500e50030080001034440c59 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 793620179 1250 793618929 793618937
    0x70201050f13120309030e12070f0506040f0b0f041d0402040e21030a09080708030403031136030615030c03031318090204090606030615030c050d0809030a050d02150106 74
    0x5000c1c10f6038402d801865540d0312031f082540d082040395000490082d00304809019650145404118800711480d00f14000c1c00143c0700149441c1c00e0402e8500410740a00400300703985d10009142e406071080314119001400c0314022a004e820b038000c440701040b00166030580c0f0075410500d44030000540070903074446c10344007100c440c003040002803c0c4c021203420003015500c01c039949054a00106846000a045861203007010980d80c1c038083c5005000c0307038503136481b18001103418021001d5403000c012269010811003048840c08120a512801031100d81c0c0540390f825004d55410311541504424035410703641c4085003503c402091071014180da07800343d054600b44001a140d010006810042c010a440445260005c5061035640c1c0109040d41e21a900407100c040d6520010801d202182c4994214108029542441c19107103403610b101d482da16025440c802c1e4510b003c0e50040246101c11078200c40350203000d8a18985150500c02d459811660703200c0050f00405800e81c1c1c04100054400341602c0e00754903 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 793621429 1250 793620179 793620203
    0x903060a1b1211030c0c070b040b07021e040609150540060806100b07030e04020d140906040b090601080a0f06020403080c07090e0703050309040b06070209070201050f13 74
    0x303801c60304804842d6412602036a5400031501d070504110042d0700c50021110225540d9500c0b01e501791800c000c41d40200080318050009100d100a01c404407807407140c045584420414140c800030a07041800b016081d8032a10b040c070002131280c42c07074000d5414400c140e84207840943c0d9030f0062010300f69203020349200c5d00c0744100c4c4802721071075060f000e0541c00180110801e141072180325448120351080e004545282d016900300000d480c488450780b0060402c7c1c2142c541809030343d0f600501500c00b82d000c0c85100300c1c2c01150041ca441400e62101314a41601c0c55661038509205a01035180d04080d0340c04d0314880c160100003024a0400a0280e04a913202c1c00242219040c4c1d49410140d0180d440d001c40d60207400b0000000445c180201400c450f16118000d490b41c5882d101034501182d03600f00300c1c0080340e0890782d010804580040180c9085031010781c0c1c003103180c101ca070b40050000e20035404025440071954051190082d4154005842100405854101340d122038084500a0748207060041c02d40010031 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 793622679 1250 793621429 793621481
    0x3061a0a0504090e0a0510020309011b0210050702210909060405061503150604080f0610080705060c01060312090617060603180f120702040f06082a04050109020903060a 74
    0x6440700d0300011462059405c1d0421030b80e1801d090004881c0c0009159802100744030b8840002e12581d568640110000d5801e048241c1000c0e4403140080d0084103016580c81c0024002c0d8024403175002c00742e510300004d051203528039038182825000080507900030000400020243e0900703105e058001d0400908000b08154984002c46069200400140d00f92000140c600215203603207010704050011400a01003450b2000185c030302e840d40040c1060303440c40c072203402041409000f02d0f1242c140c03113055a0050342c50f0b21b030060850140440e540014000c1e0070b10000c0002459005041100b9280d25585605864241c0c0540107203604050f503e183e030148042002c00d800c1841e406445c2084004002668a1105c96680140c109044911400c0000e0300000d81882180b03040c0c802d03052040d4088804210050501000c959501582d03003014295801600c2c2d03030310701d943d040b003141504940010b00502156844848610103900200c3c440e034002e20600000c2080c045050043c11140042d80d124001c0c030103001 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 793623929 1250 793622679 793622681
    0x4020a0e04030c060f0b0102010c021f09050a02060a32180d020306190c0201051014010903050d0306060e091e060f030106091b0f02300a03061a0a050409 67
    0xc0c0c42241880f0000d000b1400081660280781e104900350718000030503c4041d0000b90950b0b0542e1020000c541111030f030120440c680c03400005501c0d00075100081e0041d5a880d140c0e1428200c884003030b50100b000b0034060b04403a4401081001c180409400b41501218010b034000f03075800840c000c219080d81405000c098010074120591034400081401810200b1600800c0c2408003e64000c2141030190402000d143c00d64040d000342d142d03680c07008002d00d00e000d1040c5800c0320182d000700c0d203c01540c4e030902580d43e031254148030050368005041d03d0510107a00c80103130003020ad901c00c810110340340351840d56040c0f800c003c0c01d41c03081c04514250780508408140c1c040d204070b0018001c0383e0045030079602e401207460910076040a084d103a2000512003c9410341030703810420031080141005900002601c00e11350116011410709100c0c4003c8482603d1086c2454100d11801c501c1480389c0d00c04141000c0c01c0b64035800680032152803034144040390002c410114158403442c0b000801041c01044200010182 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 793625179 1250 793623929 793623931
    0xa0b13031101031805061605090a0e1312020606090714160804090e0102031008010203010617130f0807150e0c0f27100b090f040c020a1509150504020a0e 67
    0x1c145000520010038807628a0040408041995180d01040070841211301041c1c0c030007400f10351400d0050070700c201c0c14002030008030f00f4020581d44024810106041604419120140640c848a0050b55600310720009503140811102d161080c1802c5001c00c008500070f81c602c070088a070708001e4514014032070362154a1401c0d0000115070f451801c0000090f607140707610441c10706807101800940e407400e154814400008440d005a40c56901c108010403810390040e503005c61003107070010000c0c00e56580102020740d402c0000320152046140c0c225903820030240a00410704075100f45454400380448801100481e21a00c1002201c2c1c0e101001d00c20076441c3c00d404001040100404030340c04c03883e1800248084081d00014100050021001d012041e0028170041c405000703422401400c122055002030079a00010034110300940d0b81c3e030201c000d030910034007860b0307481c9411001d20610420b14507004402400c0b041c00c103444890b034100d03c039110410280100d6000d10340050202140e00c0c2400d450000b4010 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 793626429 1250 793625179 793625213
    0x32150915041d060c0c060901140103151b0906030f0606020706050c24160507032a021e040b04060f06111c020d09080a02090f070e03010e0703020a0b1303 67
    0x80c02a84040d0742e08010000a032040c0110f0008540302c1000440162030180090b1001900380d0601103c4135842c02d500e5203003030441c3e4001400c08000c4d590703411828010080001402c0d00c2441a200034014150010300b40e00803500c69a5042000b10883c504100440d801c6015580c0141c200c07140402c0924070980140c50451903903819a40017250107404c40400d02d0b007052880343c1ca02030460401a541b07040c00c44e0b100007c03005040452404e074043e074008181342c3e5000c05c00707080000c41c4040b0700c10015103003079848011540900716101e910009102d01c8049001c403004c95219a0503c200e85d19242068000c0354101c4a101c0c400380000f6081c0b034010364844402c00c0010200b03100714000c071240383c10340e50301e40d5125181540107425901c5460030300400c3c41400e82c00464103030740300004250050300c406041980c861a04090040d443d1036034001203400e44180341c1d1a6500d1f609103244100d50301004166030b01200e100721003d41400307035942c03001405806408000b91140b600040d0030008210100c044550242e = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 793627679 1250 793626429 793626461
    0x90a030f031e0c0f052503120e070e0a020702030a02090c0c070f05100908030d0c05210a0e0a0308040f0f02060708030702010e0f030a033215091504 65
    0x186061205800444031210721086240c0710341100344802d03000155580407144e545404c2c1d03e44a0402645500114002c00c030030340034510710910300706062180a14148030810a00c09220328240071805944e52131490103405580b0041501140e102e030382a20031070303c0459015014007020520303a0200413400c9401000d500d8000d1082040d807490396014064000903104045001c005d0740c1c105418000009285600e0400b4807024010620001070004146d50501202030400300340c0d010035070000c44442c010041504041c078041c03100701c2c061081e00d40c4554030443c0002000c1006504d0804007035900c03c04058060049000100031a0100d008800051401400303484410f07103a00850b030200340183c3c41150162406e000101c24820101e41c203006000315802004010b10300c55000c0b191242d00c03441034100b51024560340e00e40f0041140c0d40403036900950561004038084019041001442d40d041c1260054042c448244c03840d911807078140300013801000104003d80b81d032084081403000a0901810b42c641032 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 793628929 1250 793627679 793627691
    0x30f1834050901080f0606040b0f0f010903120e0111011503021e09070e04150602030d0c0e120a170a080a1d1209010215060306040813090e0105010501090905090a030f03 74
    0xd80750b201645008100c000e00130844002d11a00c0c803030400300c0242c8600e2007242080c016600c6a1348594945a8108044654181d249001c4006031008143c50348000c3c182151401040e0b4441d070040b440d0400300c0301c2a22080e8403001400301e134500b09d50318030340201400c1c4500d06052026041600004502401100041c07410341e0310403000440307641003120b1940c0050200a0000c145080a000d01940717400c500d0000074495003406006034881c000c490400c00b060380d8070b0301c601c1c508601c504d624210880f0083c01500b5411042104503407904043c843c19100244503034810b01c500045e0740f04845031402c10f5569501c0c1500c0716003803400504804070075808104c0443c0c4000d9258030382405074010440e644401c0c943c8d00c6104000190030b00000413500000c4840705002c001c201d407404203c265001c2d0b40589802e5071411524070f40501c60003a9040744811a2a200d03036119009415802181640e50036210002c03802d6584540c0420307103e007100c0ca0400b9400120200c0c00080c00f4210541440380030742070100e25 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 793630179 1250 793628929 793628939
    0x30f10020703020f100f0e03070309090c05160c05030f06070813020d021021060b0d0c17040602030103060f0c0c030c11130501030204060803090108041b0902030f1834 73
    0x307400c002d0041e024100c2d980340703106d40f960151072240b0060800b94601450410686403005402c20a8611404170145e40b60900041c51a1040c005c0301c6046850a1034442030715032170309060402c180d29002d041d000c0e01c503039107800d568684002a480c3c03082015640d0311815560348802e458510429440898110f001ca103d00001031f5101005007104c014260b89140040c0b0300b001c140101c200e00c100044900c2c91510760140300001c5848202d901c881e80c4624040b4030305c0c040c1402240c10b541c140602c210055120703000c2c0300070040190010342c1280c0c0201010b0200520355448213040303550214480010601c10101c81c4006400b4680390043c144c05a9601c402d407800d102d0100d44107440101c0c18200075070b642e50040c8110320700f034803030302003d8103030000114240b141c1c0c0c02c00030f81140e001600141151a041c0240c170000c48950f0b4001b000b0300a20002552070b4205035044501011040d110601410407000d41828540c0c0f0004818511420b00c40911604880b4103080c1c0844484992142c2d804402f030000c0414 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 793631429 1250 793630179 793630183
    0x2010f111306090506181f110606040606080613060504020c010c0206010819140a080703030c031a010206180a1202150106031a1318030806030c030f10020703020f 71
    0x5024900c400d14a591101c01c000c0d49412449150004001c2c881c85410602564541e881504d5150785e0125003005217201c0038001560003005082c0131780d000003000c0c50840c2d6483e406103407040040a0502126001c2d100c0e00c04010a07503400d800307181d00144a11002458500e0648020490145202c10008913503884401090583c0d200c1c1c1c0c0c00040303d0f910f8034040005190304024150060125201600d4083c4aa8800c54101801680c01522101808444040f901410b1210001032544085031170f0780d400d1685005409020601c08690210385041c082c12103140c0701c10704074404140d05a002c0c11159846292107058042c015000c0030710fa20030b018494002952031941c03c0c801c18915001032030021f110415941115805810250400d810090250400e4240869141d51203200700c03120150780c0c0c80c4107400401458560a00030a1310f440000c039005140c2c11900c114043c139015000d031800d450381354044c15550031150210103100c0c1c3c0300d00c50105070301655601504e8458440d2060f81d40b95466610054 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 793632679 1250 793631429 793631441
    0x103020d0e0319080f06040b220f06150806010f030b031609050928060b090a0e0105011409010909080403080d0608100905030a1d1e040507230a02010f 66
    0x1d155000095185003610201d18072140002145070100d541d1600c818001c03c0c0384000717030040b4052034441c54051180d50300c0c0d07900d6440c144201010b11405210364880c040143c82504804482c2c1072900c1e0000c61044c094281d50307213959020b40c4a401c001c3d22400300442e4008030024821003010740e100700380d4103d0350b000c1c481990301c180140410803d05040201100c210b0300090304c14001e0340d2060f00784001e94403005000c2a40c0e402c4502c40499181001c0c14110054881a0900b03079201e62040c04100e6141450781c410711a007140c02000f04402c0e80c888403484445128480310b940c6c0314003c8001040812490b40118030682e1182199509090341d958030b80c4055044006103108040c1c89407070030b000d03020040117080070000c58440180207141c4039842e980d03128800e02a40740d04001901d541880d104a80603c0306180c420003a0601c2120042e178681e808012600d0400c041c421400d010110300903902c19624140389802090f5480110860443d85c5141a40410308640c1595290484110003044e584145 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 793633929 1250 793632679 793632701
    0x12190f0b01050103060617040510051317160609020609030307080c011a060403060b0406080f0a0209010b0f091c020d0b0114010914220504030314010f050108040209060103020d 77
    0x604210101480d203a404408160001da0426190030000c20600d5803114400c01c250b000c41d0015002a184c504040c2e0038805402810300040741004180b01100142d50b122251075405440100302984002c1440c404600c951602d21440b5050300c035107100440c110358015a0a544000c0c0007a03d45600c83c808070b401d40c0c004c1402030b60403400120720381c2040c400038041d080c00c0d549001d81619041344514001031590046020182c4410354980010410762070310307804040504030300c400300e903102c1500c086103503951040c00100300e004110103000007543c0b141c003006540882c403102d081e050503c0c4000c03051081c0b41e00c8151000102515a00e080d001580703030840f004c00701500900f08054650704003145030403182c56440d40c15040000c507101c02c000c4205040c10544003d1804c845101100c0081000c1c2410848801102003030300749070000b03000402d40c059202c01001107010f801020140c0c1d81d0b903100c000c001c0304c1d07128003408070b038500c0006001441c00f6810746602c0070741414014108042800c450701180d02a8882c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 793635179 1250 793633929 793633943
    0x3020c0c031b1903051207050f060a050114010809030d02090a091503061407080601110f010e060916080703030e04060305030c0a061d15100308130603060905060904021219 75
    0x1d5080e060680682c8800700d0075020003a4154a90f90301ca503544c0006c41c07200c0420000208095040140c20b11400c0140d811200c12950f05007014010711000b81420b205111703c0b0b09906040b0030b1154000d44186100b020f00d0b8000d94102070548a441c0c000e940100740700c60307000e5100500494602128481c40580411555003c0c1940d425803512034110b8240201003e02440030400b00071805038041101c0364400020b1800640102c12032401518000761129255000e508206ca0401c01c0c5ca40090514407a52944003150200c3d51802d503044244115401001c0c0307140c004401c11701c0030030702540c8a500c4451024000042e62a502d44502e0b0640d0000e0054241c150130103c01c2e20188a0076000740b2018131045000889404104440d0300d0350791400120303510001c1444000500361100c8211984011a008002656501ca240b4580c5e40340180317601690b13002c40c0c42c01741c000c24450020b01c84c50b0f03c2440064074406564907580c007040440c40442c16561094843c00c448007803041c540214901a10b40b190007 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 793636429 1250 793635179 793635223
    0x3060302090106050f030a110f0a0c0b070c0203120f130b03060301060b1812030c010e15090d0e090405010f0204090906051807210b07050910080705090103020c0c03 72
    0x410807000c210180e000c0803c1180a11100c1148292102100e4200100c0030300064803ca8003041c0c030a946c050010150001280490404d1070b8541281c0380b204902d206c4c400036603141d40c2d0403400342d032048911040650141d10442c00405444100300060a064180e103038054100b039020318032a001c01c6a20340080944144c04810322010341824003490303010308110b840b01400c019818404801c00d0502c25840c2c0c0c03040d6050214402046400e004544140c2c2403003009001014942e2a040d0780d0340301c29420b0b031054011a50008502880104200d402010640da442c0d900141000c204911050054416106d079507980d0501c0c0340c0340c0e031940300420040036005008114078030181050400c407500185203d25180315041b540b8180b01000c54100c1c1555015483c01015043c03074420840c0000701801c1c0103010203100c3d001e0280c9a40c100028101e140c1003182c0005480542040407180030200fa03802d440804c0050085081960194001d0300307804004601321038002c014400000d203848a4141c4207424010341074 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 793637679 1250 793636429 793636433
    0xa0b091518012d02091503101a0f0a0f110a060510060509030a080a180e0103060f090c050111030c070902030604110f040603021308010c020c0f040908030a02030a06050d03030603 78
    0x70103142c00c0c501e8103035001010003d02c030f80404000090301000350070040c1c0c0050b154015030350700700904801c0d01180c18000e4903440d03c40c44641201d0380350302404100c2e180c1001c5180143c4e0540045030058402c00810030b09011b0300150588024484889000034002d03600205440034904204c89006640070702c00105090034039111242400ca215080b4004006080020b00195200020440c422541c0045415a42d034400d020031139100c400c0202104480c680000001442e180720b00280341030364050300c2d04110002000c41d019003103912454000f400d84002420070003041d8080e119441e4101c88000541e403a01107854409400d24805402c01c41210b503010003404142d0800c0d1080000d030b104c041450307a10b81380e1240c03a03a001c24015442403104040d000240305910140c0844901c00510f1038400a00084c2c1122401940798a00034081c540101c0c54540101050f1800d4060100b13640d03009203040d4610384419001c40040e40c8004e00303610381c540d2a9000041d40d600c40180080b18540680c8d0000340e550b00754 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 793638929 1250 793637679 793637681
    0xc090b1303060615080c030702010207020d320a0f02121527060c0705101b030509030f0403060b0d120203040e0c1c02090f1504030501050c0a020a0b09151801 69
    0x180d0003240f1921280c4560402042d08846417a030007135201c0844584035600c2580c102e0182c451210000d4012596042010410107070000c282c11080c82c604202100c01d02190000900b0015403560700c503103502a904c0c14011604104803030030900d0010b4510f01141b107040401038a40403550700c0400f13002d13002ca410041080c0668640548480202d0170b2118040c00c030070842e543d00d01c0c014062070408600003c0c00003c004003044a4503a0002402c01840101c0342100114052180001a240407a0520b0001802210301204450303070b0030050100a0300345400c0d80c071aa0020405001a540c1115007540740c080407580e089105c0003201455802190360300c0c00c10391201c1d0580c1c0082d100b8000340c071060082d41106c4261034400040350400c0000140c0b00c0d0322040000c2c42c4215944611500400784402500314a0080c40090041d68001c0b4001e1169481d001990f155a10801608900503004a00390b9000280e480040c5900004440300f105c0d502e901441000e818018143c030102c00c4020041c48925200c41c003 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 793640179 1250 793638929 793638941
    0x120628051806010203030601080c1908060f150a0e0a09051006020d0c02010c0206090d15051e04050d05031015031d0a0507051002070f03050a031107180c090b130306 72
    0x410704054036141030860002c4d50f24000035054074140080721000400c070709900800d0381e00210580500c2034803120001400781c081ca806039040c80c0103501c810004d03200b90804000030410300c014003011030302c0c012905104590006412540c598010004a40050b425003107025480c01846144040380c1c4070b91a180c0c003e883c140103031a5100601818080e00000350786c000130b00340c44141d012740b0050742d20103a400002d4048800800020711103458208105603042d03046d4800e6101e003100300070503010120305000c0c98000c000201c2d40200703a644004c81041c10741c2d200b24061074000842c407920351000c60f110000c00b8411a26100201e0009503161142c03401200040403440ca1841c030384004d00600041d5880301c0780c460001c3d01446000d03007812090207203514420001e0030010700314003104c849260b485c1d14119480e00060031094000407c1d6000910b894400807407a4000c1f00d040790100cac4900c5187d40c00c01c030041c0c01d030390a42c2000e020720b604000645248000c020500290201c100440040c1145032920131501c0c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 793641429 1250 793640179 793640209
    0x30e0f031f06051f0e040b03150f0a0905070513020702090115030b0f03210d060e06040501060806010807030b060f0412150519050402030a020303040308040305150c12062805 76
    0xd002c4c694480040c094a9505408001901d081101c51440401150103050710030340840d0148a464030719185000c5e0151550b00541c400d2603000c0707458a40205e80c2c0c060321603500c2c01a1540e045014100900e1411f00c48525130a0350811001d81040d0309a000a071f000746e4240d203c0211105585d00b4500501d0341441602d20f80882120b13081c420003110404260703a100022100c04052500e290001c1244100b4800d5034154036452030240183c5440d000081a2604240e0710503020b24200000480d5082c01011403038813550040e0740b131004130703581c1d0b01d0110050041d0081c1c46400080c1000510a10481d0500900c050720f6a4865001c83e05201d29044210232001f140d1143e00d2480c00040c0720186280b4200c00c00c401e003044501043c540c0380c82c000682080c1081100079414070000400008110070800079000300d078002d00664000503d0202c40c0315030020210b56400d12000100141c8100ca020581c009810100c042e001680e8608030706601d00c00c15281100c1901c441c01c20950810003461b0441e226480301c4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 793642679 1250 793641429 793641439
    0x51f060603060609050f0d05030d0b130204150503130b100326031f080708010507080a050603071715010b19020106050a120f06050a02070b060319030e0f031f0605 71
    0x741c030300f20000745003020301c1c02400e2081c1d11000c9100300381e40d52110025106a04142540d07038905048081500030014400c503c0d0080e035181c40c0d040136000c61031087e1411a2103280d070881401740010000c44480d40020a07032500d400314440340b80b010500c00300549110f0343c6036000340c00c3c0403820b5003444210001c0310b0400d4241420001c842c000c03e2034650701580c0d08807040e031540d6100318110b410384cbc1509100b1f0b03801c400304612504800003000d042c1500407501841e16030b00c1c0c209039a12a40000c00c04d0b650121405a0990b018400c10002c51041080e04a0081211000e03035204284a0345424042203003a4411007030313900049070082e1054408600f00000580e0f41c0020403025140c0004100d28030a144202c031410074280c590032050101f0341141c9030142c0d622590800c024503040035504001d402010702600c10084401c0000e00600b0000746540c280f88040031640210900d942d41160449044e0341c21540202c07180a01d100c0a48003000345030b4004410007c4208042604801c1504541d032640c0254894 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 793643929 1250 793642679 793642691
    0x13061d060c070b0a0203271c0f02010815100810060f0804110301060305070603230c1c2d0c0309021003020f090904050d0801080303070e0913051f060603 67
    0x100e44002040800c0b00d400c3c06505859042c0d50400340c1c118090042e40d10710640c0346d80003000d6014003011481139850411141040300d80e00300500c10214100e00200204000440300d84403000d507000e1528103038056042402c44074508220004141d00c0024940aa008a9005000e110383d030881d420340d45003d0062498031988041e01258014220b11020300044e06544a201c0081c9482e1400c1d00010080d40d000411280059030755030b001001001080026034a102500d11000102041651b10764010120f442982d424241500b500c0b048003e07201071481e48650703a90181c0d28050240c9880581410710a002c0d4100d1030b00d140031010240c0e00d031000c1c1441003600d05441800141d0b40c21401c2259010286001a10b0380c0d1911180302c054030940b04855070118400b0200010032800264010f00c00100e680d901c1c0b01666242c81c00c41e546e00003614001e0202c2c0c103200e0080154146035056a9005282c4801160501c5107920342c90b05040540b00b0050b0f0401c008000344140c04103901a54006100307e03c1d0411603 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 793645179 1250 793643929 793643947
    0x130f090209010203161e0506190b10050d1409030a020d0216210203061e0105090f040803040303020c070f03150603151a130c020601120308010306050c0903011a01140f0306060f13061d06 81
    0x107820a0701c0380e5428020013143700d140c400416030003454010300f51a04841c0b5401c0a82c800c0d6542d401640c00f1500610526880140c02440486c1001d00c1a04040381d0300c000a00381956400e401c805a0402c503078042880d5407400240e502002158020200060381a01c4038074555a424102d00c0b058000c0c3d03002d081140d060100c0c1540c02031089520030741220000342c40f9183d5180031000b92083e40e601446510035103c0c0802da003200900490b04a0b8032400040007c0d008400b1044180c40c1284000f500510f40420000c20a16031030708210114880f40d0b00e022803005040d400181503030200301c2c7c1003400701c0e40c5040810709584c040101c01d001d48060b50010394002e015603030003440300205001c020505629280404c10b101881c0098481e0a01c0040013400142c8850300001d0381c89038800380d8240050884101c4a40418420041700c401642d40c1826607c0c41da108000d03c1995480182c86000407102044400d4040270500d105e000035203da07036902c1d041c6810710010103192080f2003060a1158004101d5011 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 793646429 1250 793645179 793645189
    0x3070306121a1008010504080306010f0305071d0609060f0417030415031a030607110d0912060207020f06040b040617150f120102130f090209010203161e0506190b 71
    0x3a480b0008284030940d5540051459260441e80c048565507080034284404c001c82c01016510840c1c0030ba035500420142c2c1c190850030780d0010b85083c3c0120300b0340d021070341e0300212030a290041150054841ca1416010a0210311b41c0e61044d6140c2d000c950001c03c0504c15000000d10b002d0b081c0180d840110305060500d1144440030801200c600d061640e02e00b58a807607060882074290343d40e00020140c40d4140351015018000185c0007646001500409251f03c2c0c0e0709008112000c1905e0748000d0800b104e00c01651032000940c8002000d980c01036004482103141c0e41d844001b44040c1c9264603035a41c4407803900101601948241c0030040c41c140e04030080104100310b540c0521910300080302c081c401c5512f0f4002003200c4284900b00049154000201c855016400780305030310881b501400900d0b001966481580c0c1203010b120300441c01a04100f106400b907800d80120003003214010301d00c01148601404941908140742801215190419010007040c00c0c1481d8841420300321130007003407205494140c0001e07 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 793647679 1250 793646429 793646453
    0x40608060c0307030921020a0303241a0d060303050c010b010f050f030a0b061801020f0a23030c03040e04050c0a0e011203020316240213050f01170c0307030612 70
    0x2000c0540e115100030a0088003020910013000d0b60358000080700c80c1600088d2107c10a4000341c02203400c04031142c51400d140842900c01903080c05036540000d080103900300c40080c10040a010b10f02052000050b80401071003140025072180d2152076440850112403402d58400c00003c9050101800340460002e4000b0104c4003e11034003071315a0750f20381d10400d8050040803e28100b54200d0008142c48100d401083c0507051600740076000c03965120003581d1265528082e007000104030000d191307100d10441307608840640361601c048041e24242407146151502c2d54000c0d91040340881ea004c014481441350600c41c1132a00d040551345400d2075405d14414540f80c510600c10700504003400d2150798245482801620901543d240324102c8042441c149180c1c200341040079110240641c3c40d00702c84101ca14822604400c5c0c3d500042c6041500d00000c10502d925075203032203810700c1010200b42000d145880645031181d91501c034525103031704000000a049031101d030080c0c3e0980c1c018562807400305441d07040003 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 793648929 1250 793647679 793647691
    0x42105100c0e010c0f0b0c0310050a120308060a03050303040515160207060503100509161b110d020d05160905010b0a020a02040f11030f0604141311060c0706050405040608060c03 78
    0x240510b5032a861708081154140e000a001010020301344150141030400860282445049030250240c072031042000c0c502084c890064220f00c15850140068001c0c251a03500c100d0080200c90700070350b41e407034040c1194030403242181d1031b42004204200d10f0f105080500c2c0c0003001540842202014a00040c1d80e40c1c80d11f00941c000c2c00800701c0016030750f101c40341c603031005400050030740c0c49242000b4121000303440d00305801c1404120001507540241040201c02c40d1513035044070814000341c50100600007a0014108266000210440003d000c5082007000d0080c0004002c00910500e10300340c4210110384068221040345041000307100318241c1e00194a02040b60100c40000c2c20201c3e41070400b0040058482844d011040072042041d00c160059034544540c9065406010183e00242034000e0020215181d07500c00b043c00c0d20000110b02d11100000d14014041c2501c0c0c6887d0f51307a81414038001480e030102d40010700000d81170006003054002d00b0001d026640082000303050840748424580402090 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 793650179 1250 793648929 793648937
    0xf080a090c081e010e0d080f130f030e01030c050309120306120f0303071b150c030b0616030207150509060703050409060e06040e0f0303010b0708042105100c0e01 71
    0x31036040c480400264001050036404682c1804242010b00c0c4007280301c0b81c401ca00039440d1a500c1026540003180c0c4a10442c110b5403007170025610030b2003012440350050801a48002c4c5001c400002904202d0b4202d03c540c003a48521055a001c00001070982d0840001c1004100090042c0180c9802c00100d059074440c1c80500c0d10389030f0380d03030001140c0c080e00c14880481182c404c1c0001c006810b840032000354060000369a4005000661409000c0e80700c10001d40140902d90100b040c040c0000c156201d01d00003003452401099480303d00000901d5074121703641001d1010075402e4030000b007507010003030100200740f002c40400c6803100c0108090306070f0058094540c011071002843d2010103101d1421140900220502000381035158140d1039401c06040300c3c074901592500a03001e031494400204903007205030440096245a0828603d10151f8003c05412242d1050503c408104000540b0f0b4210300d074105d40b5050306000340c42d420810320f0125500d100107007003840c0c0b494400103190300851903d8414001c0c20 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 793651429 1250 793650179 793650191
    0x180a0e070c03020a020d060e16050d02060a0c021801091410050d02011b05100507050c062202120607030c050c060705090120012f09120319050306100f080a 68
    0x18244d00f80a0032401c02588540d10b03030b07008001c100066007c3c02c0302c0003e0300110fa103160444c01d014900040c0d1802019403211401d42c0b8200189004001060202c8552402005d40500b640c04a007041080710560408140300d403005000b01070143c07103080c030a00003000381c1f10440d09140f61109181402d0b40960382c01499030440c11000e40e40a007240701e07509a00c8600081d500e81e445c1c10002c3e1034404401c0143d082c40d044c00302144901d80b040060310f500c20710200103040c49440c0d04180e0720f20f074032900e0240c200107040e51a90101682e11141c5680d14041c00d02d002c6c00e40e034640140d00408548051039004d080c46014048501002000603210b9444216030609699840760140140d8003950541c24109940300c11504014400b141900a01700c0150040c29140407100500444408946080d0401c600958188504052803a040c1d0f000c1c1a105044400e591502c14440b8810349001502c0300480c01150f40002842a982015491940c0541c1c5a02d0308010201c80305200610800c0060144c50940d40c03114 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 793652679 1250 793651429 793651433
    0x1030204030c090b030c12060709170d230a030f0c090e16030f050108160504020a05220b040305060103030909150b030403022a090a0b0105071b0b07030302180a0e070c 73
    0x1010b03031b072203000060080a561011000c11503403013031b0444002c40050304d10040007a402c80705d806410403400518010340f001d07040007031742113130003882c62a5129000292261300c0300801910400414030050f49076804a003180001d4104403d5072100641d220400130003850401400700c111201541040220301c0031b01629040c884203c000d420700a600c3c040d241d00e020300020f103c0900145489402403843c21600716603035127500700000c0f400384041710004160708000c1d10194001c14400c03090851905030402c00c1540c0c1f0740c100e906480d0807a40007154144d00c0301300140181504003a500c001480c00350018801c11219007201500c504145c4200503d010010011408050080c040448442100300561241c0030390070098a41425041580390b0144e02c3c0320000ca50545031720702030103101101c1a100c2c54079002107aa1105004c1e001c020042d0403165016002056440c0d10310024650315000b42c0d400741e02d034074000c3d4010b0342001c036000501c0e03c140000f5804000e5100e440102950140b03460502c401e08604034 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 793653929 1250 793652679 793652683
    0xf0501060509250e10030e030f21130503040b0913050a0b01030b03011a06031806012c040224070807081201060908150411120c01080601030204030c090b03 68
    0x60300040d40c010070b51400c00031440c8628035102c3c1016074007520405151500e0318262031a41004440030380040001070803914913030017a0025040603440004a92a11104000800c42d68000d105640d0400428401c0402c07c15070508520760002110303c00c1c0050100955506541c910403403180e418807013404600440d043e03450100701c0b03000c1c1c18148010b124514020030500010600701e40c400d800719282c2803015441c0d0805100c1d0702141100b002c3d15170380107282c0004200640d0801040f48903113210003400e09121440900c0114001c080c1025900b40c1c40c1c2c0ca0181c4400c90b890107050040d00022940208000350350380e011818207100c5421038014800071025019140b912900c20003a02410f030029580040120707500091072024140100c1d800e0f50390300d5200c00c0315501944c0c403501c500c5d541f00d49440341c0c2d021010500150070038400d440e15020842e0110200f06081c01c21071616502c3e400404d0706103140d580140704654402c0c03007460304610b03090440e907072000d4180c000d0180c00c8070703a41d840080b0038080e201 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 793655179 1250 793653929 793653941
    0x1107030320030706060317070506011221110724030c0207090204061d030601230109030b0f0703050705090310110f04030f060b0105042304090c080d020c100c0f0501 72
    0xd20a507a643d6405082000140c01d0301d110444d080034541c1e2406c04400c0c07014040c0c44003d6806006444241d19001c00da00c202e01d100d8100382c1c0c11458440c81003100070000418010119100c1e100e90004a91a40d00c0030708000305544016200483c51b6081100c2da01c114000503000c620034240003464202c4940c0483c90302946403c100c80d0340d1b100003004214113030050311500b2307030515070454401e410151105150320742c40207114480301e0400200d80c803240c00c00302d1069211000410715204003015500d48a00f00c0c030f280241c80d074602c201444418440d4441d07050080caa80700503141071061070120184042941d0b184103a49119200d656050b4864003105014111403044429020690300c940e103d0400c100001d0365078104441440c5040800d1516500440c26502211500c41f110b4902d086241c84030740c00401096007a5a00543d68000e060000756411503040c01f51044a00400702c80002c400c000c4d281c000307281d600074485c440e8800c0c806051030380200c1664a040d8080020103030b00000b07240507805006 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 793656429 1250 793655179 793655237
    0xf031802030f10051305030304030c03031e0c11013308060a0608070909080d05090a120f0306050307080a082a010f0c0f08060906010203070602030f01140111070303 72
    0x9a01c030b00c481e00d5400060103e007100740f20340100080c2c0c99408030b41d18200c80840c1d000305070b43c2003400044c003c280900c4050f0200e5029086c0400e070a400d940780c0003072542414803548009550348048420940d440030000d071910101c03400030450402103030220112000c5c06161810b00502c6180d400c580d08184581e4400201556422500a400d00d086205c01074011406034a1107817040060000321a001030003250186500440c1c07091414106082910281c0801000403120f40b050328041c40006810851540e014901d60740e5130b08101c00e40308070040944205d603200030301c641d06c14281400490300100358102503aa1010b0442d03528a441c40200107442c081040e201c03030f003202664040000e04419001041003054806080001020083c0c0c252060080c0180020000e0000070001c2c0301400e04000c02034101d241401260708001d125500c0170143d0b402201d2603281d402c00341e00108600c9400c010b0b6a00c2115090902170300600c024000c00c1d54500040c80041d0400102c11090400d110740d213100f030540c1c10 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 793657679 1250 793656429 793656433
    0x1050c030304050d0e0d110d0c230f0d0804180e070303090501030c0914101b150f0908030a0203040303060f06051806090f040911040612030801090b010f03180203 71
    0x8506800d00030746601c00c52961350089500e0000000c0b0911380301c0819046194089001110040040140010010b03001303800c41f0200c950000c08a100c02c4c00c8007205030002c1c0401c05108140741c3c11021f111203a984580418050a6034060140005030f0000030b40e81a201291800c40410384041050409011107007900781c514010700d240030040c0359011428006549080c0c9080c003c000608508503100e545500c00c0a00c40140b028541c001d928004032034032a20001440c0a427030201001141c4030074688110021512556001c0c03407440844468001e502c51650300315000c00000100307440d00c0c41188801803000c0909580003000600b058041d0707009d0405015074201c0207500c0358552102038029032050004025525046c101d540c0b0505c0c1080c201c95418030044c01141489042c01d0510001e0803c0040440e9858480306101209441e980f00f50740061161081615008500d0704011f00b6118042e080b16803018200150b610260343c00c5044104070801e00d00e8005400c11946002040081a0701e100035414 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 793658929 1250 793657679 793657681
    0xb2b02040629030106090b03090f01050910060f050f0603091915150321030e0d20010204030b010e041412030105150316050f04030c030605010303080114091501050c0303 74
    0x354a02000000006150b041c55005140c02080c0c0c249450000344204800030365503030000e01001080c0310203540c120b490b21046881d0813030854000350075142c04030303006002c60384030304c000c03040da0034150081c0f20062011240d401c003078074100400705010203081032556000301000000300703185910801031180c40880c000c030203e5041001c0d1510303004442c007a500f815002410300e9003040410b5040000030084a61110306044240034008030216100c84e0700720313542d09040c0ea511400300607044c103005100c40c03540180d035118150f0f0284038980170248120003482c02d55a106000070f000145005040c00c0c1540d17041e07200000310380d440c0d1a0280510781c42e00360802090007045090501700780200081e6040e10700440c1e0f517000c900c0e020300100b0464001110016041ca1003928241f9000d40210010500c0c51940a0b2440c54281c403500c032440706500607401103440c55515001081816071100100b4094101c41d01641c1030841084d0000302c2c03000000d000052000b00c0c0c4e2409010680c052022550a40362080c15070b512 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 793660179 1250 793658929 793658939
    0x2505090c1b0706080c09030c0103050703090515060901170a110a0b131401140d0504060b1804030305060628020c130207060b03061311150705010b0102010c02010b2b020406 75
    0x89540b0b80c8141800324140d080400d0040c502d400036541d00c503c010b0000d018007440000110003410000e001d07407003410b9903101c100010420a1055a08240d0700841807030040c00c01005200c1551030580c007400ca601e508801c0b5843c0504040f40d079100c1c1640103405098031100b0000001c050031a1940400326180000030f50620b4090840901c8080390742d13410710b69858070000300041d0b416010212401031089001c00c2030080d0808a0350080340c1060041c032002a803102c16002050385816a1806a6050b000ca03000b0001051342c90300800b9400401030b24402c3c105803030030f01c0008040c082400b84180708020480c0e00b001491003084000800c46004010140c14100442c601009512400342907074001e06011291506003400078441d4024030a1f10301c0c1c001c44030034540750880200d801c1c1e16103546c0f05028044041c1010761140c00341154a008a00016008610000190231510500200001d5906003994521640c0d214a00802642c0700d40c1081e00845207101041d85410041c000000e42c0180b821300e0200d4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 793661429 1250 793660179 793660183
    0x30f0809130c0e010f02010e070e190203040b04052b050c0c03030d020903010f0207170d0612030503060315040b1503100903050901020607030902031b040f1d2505090c1b 74
    0x40f203034800c2c1c8a04541001129040703098940c0da203441101070744489010040180600e20156000002803004600341d419010480c0a903071040e5400d58080c412401440140402480440903410900c48130411350b126500d0341c044011203480900061240101d1019100c0109010401010800038207895541a0701c581c208000c0d08a0320300d80f07000398a003243c0e18004058502c2280c44c441d402c042009042480c080042805520036844d6542042e12001e0004a900c20149035600c805d00c2601c0307a41e1a4984803041c54a04040024161175040d81c4905101c003150f480400d80d034119204400807004c00e0741101c0440d1a1000c0c4441200200f8605801c0106055101e00a46aa048242d0076100b40d500d5000e01101651440303000658540c2000700c81600441d0041c1e07038190030550290010905010300d0400c2c20868008001c171050550029140c5481400c3c01c0c80101255100880100d5808138024121010700c822030265038059804a404a0300058004065400c0030072030311191030903240030300b002035 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 793662679 1250 793661429 793661447
    0x302070317011e06031e09050a05060c04030b0a0c1422030b150a0f0b090418050d1209030c0215090d03090906060f020d08191503021207030f0809130c 66
    0x4401d25601c000402c038944a401b5111040003d600c0c1c140190303c0c9000003100604011034106c40f5803090420b000d00064081c42024819420003038019202c52843c1002009144002d200b0803c00346450044091a504808064803081303484151584074801130424024801030401c1d1198250070307901c4000100b14440382000d2042c541049508164001041402003100d0180100800049101000c0c0591101d000140c814000010702c0820340a1a100400c5500035060b501038a242d044891455505500241000b071400903a02040020321510340b80105003c26580c0024820f645840542c65441ea420041c2c1c0c1c1c044100500c0c0b81102030462072702401c00e0326103201301d180c40f90a0400001700e841c040d2002d1030203040c5c0c0d60058044400207040c1220f200100801c80a4201100e030201c40c003204c00c80c0f1454003400d001c2d041e60340c240c50030341c010004a448240201c0802da8018401803000551a81a44e40d40701c5c1c0c44841592a2201c0d14006440c5a666201001c01145402c80440145902210071 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 793663929 1250 793662679 793662719
    0x1b0405120f010c0c05100203100b040b0c010b010e0f09190e030a030507090f0312181701061e030209090316060626031602030708030a05210610030207031701 69
    0x20464100301c88026196584d44401c040c12070740000580c0a40c681c0c054004651000359406d840400c26140c0700b80703040c0d5400c1508801c1e00d5520101e000c201d055001d12400c01524400d08044040c00d04c203100052400c1c0710014440d00950144000c601414185483c85209404040341400710b50000c0c44055a250000184000024281008511554041d404120540f4809098950101d045d0745407926820784800905040210704038080b00750240c0c1705020000f0b0300b0003000c401010400d403034030390f401c0d01d034107030081540154803441c0804141c6841e4038400c21a541a03848460fa65640f0b00454114011122118003030f1004010050070040e85170f111301c054a040c240c84100480e4240310641c101d2508004041d06c9030310030040034401081b907140c0350f820203200404955802c0d8440031310504682040c40070502151003c03c4521203042214604804d4940c41d054034203a0b440d00800003010780c003400302c07408280b5900250950505100300034502c0c10000702684001156134807031500003900b0301d801c00 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 793665179 1250 793663929 793663931
    0x31002120f010509040305160b0906011503020903030a080c1309051819110a0308070602031501050a05030601080c0d020c1e03040303080f06030f060c0a0905010e01081b0405120f01 79
    0x8080c41e0200700d03610305840000c2c1c4808519aa0355800351442d13484500d0a05580b401420a8070000749070030202849003080e0009824194500000090361040410f008070515005110308405a18000103403108080d0700e01d44401c158651104105007841507034028001c22800704000301d140011900054022101a00b008032540795010180da200c2c402043c0c0e1041c040348420b1800c02180c2a6014008000e000415007008a5901c2e07071a200d21b41d0101c00115407061700441042140ca14425107180d0b0107000303080c10b500d0150407590003003041c0f200920703a6052100c0c003004500d544d5141d4055860107124410110354070703007410b981a5a610031003055034100c40001c9003900200c44010054900f283d505885912507502c82c080782401e0304a000700a281c06208a4000600e030f0441081600c2c082c0a079280925541c0c1d0807100c1c024000c0b450fa8211905000035804c3e5550f150b40e0140701150b202404064444a01c000c41000d00e4052080381c0c00030307a02000d518442015114003080701c401c61984840 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 793666429 1250 793665179 793665181
    0x30606010e211c09090b0603040206070b1005060711040623040b04020906040f030311030307171e0c040915050f010f02031e090907111002090105040503100212 70
    0x1195034444854926401024400140040300d08030104005000480c40c26500419001003120f0722000e0040180000a150001d0800c6000400d2140d0325600d0801d4804510350301e40742e004600203114421004010b080c211001a503003452040b0103002030310300242015520400b0b4204150b062070154502c51140b03151000c00210340300030540d541c00c410201040940103101c0c800c00c00c001000c00960a60304180c08120903915075440c10300600c05002c280360350b02216411800d004010b0303080b81c072004080c0da00c01c001748401301d03400203007081240103811040d038419580e201007011a0018915040c002045020501000244c40b602400640b400ca410800c1a03600030440c080240d0140c0c881d03581c10401c40c0c00d0490855105c1c1d11180c10b07000b1103004513460490441a0394406c01c1e009010701d800d499010814002d030345400110190021030320718201d69070350302c3c2e00300d403c0d1104509050440e506500040340707401c59014505450003048003d09640302c07580c85106030302c080e50010850042c0c4c40a000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 793667679 1250 793666429 793666441
    0xf1101060812090d020909071712091018230307151803150903080c070308010b0903070801052a0a090329130c0603140604020d1116020306 61
    0x4032914044524400080580d0241c80031842543d500245045401140141030306000da00c40c024007d008010300c10051802c58541407421120b00c0c02c1141d01e030b42e10340020356202d4040035180107481c0e420800f141c201d482004038040907500d4004550700e190b2001d9101a0009040032180144107006841c017003484a540614400c064851032180100e0385e2041c0000c40102d40c00380b084840001130340a0100d038044583d109c0d12801070804000511892268569458404141c0d12240315a04154401030080c00c00d80079540103804a201401020040034000c200b46030199401c01424000302040301c002c1040d03040c40c1c9404000351101d00500300c05203007554149450b147d0400c04840c0c2c401c03002c2e0b071032407040c07400c658072000e10103904808206204074a41116001650b0403c4442c00b843c9240c0420280c5420391078100c80c041d40c9075020109145c030303207100c4007209a02601c80e02d03480303030702100e00580d10322000c81c0c9140107121002d070818465101107a00911320140040c10b40300d00d80228101d45440d0703690 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 793668929 1250 793667679 793667681
    0x405060d03080126071202030c01090506070b15190302030d05040308120615030a1a0301060b0a20161a090607060903020a080f040f08060c030403080a060509070f1101 73
    0x300401800120440e004000c0b0344005440b8844000301c00d5014590036030500310862601d00300760024000241c40e1004001103240411414034283d1081c20145042441d2200041040c0100c1401820364140e00780003c1c44034546000b480c020b001300a12004064809070401041c40169000483c003030b1042900c1034030500d01600c2030320200ca9004c0c001c9440c018815079800c50009010b072205802001030f004510744c80c04000003a5204141d401d80016405080f45c007130032f41040225001e1360099140c94014040e28007940d08540c0030311007904010030401301e841da07411400c80300c4046100c0b650103522101510690320203810f004840c000f4810007900054042100c240c1d1052500003a8041c0c010010040000c44a81000605a000c2d0040d5070401c1c9079911014000e901291812080c9080000c0038400481a0b12162014140c03001c028006840e10302d0507210309220141001d428008914006042040c1d03641001e00a00400740989603036082039600a000514613425041c0031078400f40f0a90304039001 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 793670179 1250 793668929 793668949
    0xe030c06030612030d09060e24070311040b210f22080c0d030e1005040f0f150c0c060e0a021302030a0b03030f1e030106140d020c01150302040506 64
    0x24419481c689a200c2045850b141855084029000901407141a68441e01c00d80d2480390043c200480c2580c0129005428022420399000d1028805811041c00c100c503c8580c40d400746131800e0008050741060780c030041600442d07002000d4820005048103401c007040d415030446110b071408601807030302c511485050051084031240c407140000304111a205c0d50452114111a00a40c80c4074505501e1600c1b05041c501c4001c0d80d07901003038175024007000d10402040204880054032038100000c0c206960303030800703d603044203003c0c00d4185507242c441c080c0200005078000c80081da007020410307080940405800024040c0017a01c0481c40c02c0a6014000c1010406038066507009016041a006107010140290000b4111440190790360305560702a44007080141101d03040c40040c6030b241d400701125400c562a00e09104944445c1c24001000f0040c0c01400c02220141c80c04400d07a2121480c80482c0000e016400c2d01c0030380b641c01c200007140741e1141c40c02c442007942d0082c3c1c1c05110641e01c0c6030600c092004 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 793671429 1250 793670179 793670203
    0x708072102010e010c080c010525170a0b090103030807170402031f020c0a140d14070305220321030e0c04020c010e0d0909050106091203030f0f110a0e03 67
    0x22900e5006610900c60a00809014100144841ea09803525034607030700404e100420503076591040c012501c95510b8000c110600c45003040361004110003004100c40358a50003005058a0040407555440e2290801c0b262110080c008403115a52810018218401a10741001240360b40854980400c0c610081c14400c0c0d4000d4014003250200000001a090000c0c604401c070941c24801500044014092842000e020f10001e003045045002058206200000b402e001d200c420b80b00c0001400000301070f2034006030107060081e02c03030001c4170345010b4500301c0c0103000d840551032080c04010409240c2e004d0108400c2c408201480d05c044501c280d044415400900c13100b075101c80c851044600c0c180e0000c111049624001041c14264203401900e03005043e070b01e00c0e0114402c00d10a12110b500d610456006007007901e80001010301d403180300c02801c008094040c0c20180c81e461070000d480000e0704a80c040f50a286420448000b41035020b9915422001c15600096402002000185000104410307030503 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 793672679 1250 793671429 793671479
    0x506030a020109050f0d0501111803031204240606091403070b04180207060509061906060c06050901021e0405130501030c0b07020a03050d03050402040b0d120503060604050a08070807 80
    0x213801c3c8000c001d5000c0346a60810ba010070740441d5000000c80c21302540e0b5900040341941519404006840c8240d0b4000103951380c042e074014040442c80d00403007244642c00a800101200c1c000461988241003245d031201201ca1490405800060660f4070030031030401c582002c0138002100e003000c820143c41d82c915100b0590703901800e20003130011421882c4186070040c1900380c018500525540c0718001c1d108110341e448a550404e07810001485400c403217401c58000041c0042240341d0800c140500030203015000a40181d99410009420346801d50480b070103c0410405c1d410101c842c0c1840a04035030281c0100740c01826010a4074009001d940205030599522441007070200d4207207610f80300c0e50740005038141e0340956400c0001001c14030912081028507d9907034046828500b034014081a0b4540d030641078000d0354920a00004200c039507041c2d0558a170f552901c541c4e60344030200020240c1c09103420840e440542510000b6103031000040000880b04ac01050340c001540d11707444a0140d4003a00c42e87ea0b042 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 793673929 1250 793672679 793672697
    0x2206020d0e040515030a0b0a23150f0405280605090112032703020f0d03021507030b060a120c020a080f0a02100f020a02010501051f0c0224030a0506030a0201 69
    0x2d25040c1c0060768094200309040841c9001e40e00043c2c60100c50300d006442c42ca04e25424080c902c9014040c040807009085200644420f4144076640c0850b00204010400f04840c03140c490640d94400b111807240d000180203000c2810120304592582d04840c90400c1c51424607000402904214003038070013140c00007400805240e01c4c01c0d07141100c8400042d0304a080040511014140c030f8403c40e0030a83c0190301030403d50000f404c52040c4001c401400145604c501920060a40002d5002443c00c6038a82d025245950f10b880c0c4c1c81099026000c00c0b0b0050b50b0001c0041440303034040e0b0744108000e0705c950020406200c60807080034140d8441180307031809000008100720800038080c201e401000c054043d0b104644010751101620b000311685070500c40700403900000e030f00420660900465006d000125400802d0380b0004980541c441e0b14a0000710901000a0381c90055585100c1e40c0400c03c080c0950054500e030852000e0b81156104507142001d0500d80710100e11103080014441c2a00340c3e0607180c280f15 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 793675179 1250 793673929 793673957
    0x18090c011101020f03010f06030f0603080a0c060902030106060201020d200f030c0d150302030c03010b010504050415030f0b0f010b0a08040602032a0306010912020303030109090201142206020d 84
    0x70a0540300e6181055902042007164200d10f441c0114000c0c104012845407503801c1c80d100800361811403100340040c5c0e00b801000d2020403401070440d41c0740304403410b00c1c0080b04928606940039001c0c402020b03605500c1c0800028000380c042d0002c05007204070010422181c0c41da0109064042174403158512120801e1004100c0403e440c0010358018440c8100c00b402c21850f00b402c48165090300c030141c0760000c8071800401c214142005400142e035000c48c000c3c0300d480c002c800000d01500451094511407070700d4154081e42e0014528022020f140c00085411030580541401041c002d01a2041040c080c4a00c000044c005c125000742e03a4500742503507420410340c0300c0785c071003501940001d856101e03000710038840d40c0801d03800004c2181d01c1e03140c407200243d200e140c58000581441200d502a0110070301d0307a21041e0040e0703004811070341500c0190400180d204940d00048446140a4200c5c06100034001180c480c00d010900b01140f218004c403070b1184030141c03034500032601d52480e1080344000ca010601200c0d4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 793676429 1250 793675179 793675187
    0xe011505120a020f18010b070c08031231081908070e04091a040609150b06040b1e040803030103050106120f0303051b040308090306060d0b2202060301031118090c01 72
    0x180700080104009038a0704105c590428a8401ba403015508500020340882001102c000e808000d041d0350014500305981c1c03251038100000c004046c00303500644000e41c0780b81c64501c41240c1d40350160300040f01c0c6480180d45480c02031507000030403400d03201c4070750956413901501c0703084180d20a850543d070702041d40d40c1900a0102526000804032103034580880c5d0340030f6100d450503002d40f286008950100c1c500c00e09080403450800380402e00d00c0040d040404400b4240c4504045030704545040e61030313558440040300503201114000c803075950942c40000b0000758045000000d141a24040c10003004020390702c110070002c1101401004101c001c07480c1c48400402d000317922150784440c01d00205441c0d59113a803003441c8158495041281c0544000c40d04280c0d40c10304020306c1c1d074800342c180d0301d0601ca040c2648603203040c110700501450341c069015420f01c0d0f00f196400c4070f01c100140c1c0030344203d480f540c59291048000503005800c0d8091260081a0040ea42d1030782c070aa4020040d51014042114401004603 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 793677679 1250 793676429 793676449
    0x6050702060f0d050a06170712060b03060c071502070b060402030a0e0607020f061008150a091a07082412011503030c1406190506040b03010e011505120a02 68
    0x1a0740800180140d5420140340401002d039000d24090025281ca03040100701c08980450b0403c00542c0b088a480c451501c9001500c14127079172101c82d0700d42c0c0323a070041d1900c60090030700040c00942501031705062110807102d40380035180c0c00b885081440c144815070940907080340500304001e02940300450100390142020fa00440c0c2095001a0208448203020216440c1200548018006a01140c0700c1100100140603040e00820780307100720841c1500e0700402d5650750550312442c00c2178403446c9002c51900800c0f6032040034901d602c24128060064410001e00040c2c008a42c1d00c0080355050b80080c0c440b8402400c03e5504141c2c0f0a040e4104150b0b100900c00800d0407410509602e641ea03000e881000f120b10a4580000c5219682d2002a00c0c054541548822981d21403440241d10210034412200c0c2100c6480c04c0700d242e10321000450355125000100507241c88001030340c055291000c0c0340c01e540f20640100c400106021320141005541e14203100d008030b4401c1d035004043e00b10030002c40061911a03015 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 793678929 1250 793677679 793677683
    0x60304110102030c0717120f090f031903020d0f050a090635040201030c0507050a110607120207060306080a0803060603070c0503131a0a02150603240411060310060507 73
    0x2030382000c0e035066440d49084e1036500b00e406d085c03851191540002c1e40822502c0d41c000c0c40c2c1c9000504114060a800c07105004030040b10303200381c031020f1800440341c4042020103c08071820380e08030600086801c0107074681c803016158400160800c410b04808901a10403502e0700801551000030340c3d80307002d20440d000c04050180075100d03090900860344103680d410325030080540801103011541803030320015044401c580010b1050200030b0100c00c01140c004500c1d0403040d5000002c15082285400003d0340c0c920800c28000c0161500340f12222426600165103000d903046a102041041d1302c03810303030585e50304411030010702d804402c1000501608040c8041c682100c110b080246050500d540c9407410354018900803004030160b0f4074200460b02c1c60744801c05050610840d19450000700400082d100c6800c2800d1a560b0989580410903e880c10000618102103042c00e201050111001c0103c00d40c80640d011349000f000d04842800c549040c0c0c04481c0649401036456006903c0c00d203081d038881c0c001c0042 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 793680179 1250 793678929 793678933
    0x60f04050d030e0c04020f090f09060a15020a0b0a0c080c030c0a05090307051f0e011b08160606080d12141f030c270e0c060f040f0e010501021b060304110102 69
    0x441318945803130001d0f001c1c201e42d4940040e00d5104240510584900c000a11441346050400b40109911452142390035030300c03201e01190003100424020b038500198410018004e180f03803c10040921110b90005c9002c600c01da4443d60f250f2520392840142d40001d030391450804004003d0382c1c07040da00480080c414898040c0903600c01690729000113400100ba004203007801d03031002c9078000d5007541c0841c074400402400d0070001c80305602c605482c911000c02e040001c2c95080c0000c0d246041032244810000f03003070b90103041800410746803104075440781a103408207008600720490b00055440c0502070850901c2d9101031f002c16039903d0403035030324469503620711840d04200d58080101c085148040746901500e8100c2c03004c04ca455081102e0b415003490909480c82403440c08141d0711384034402050b0b04081e10422100107455007503401d60a4958481c6034003620751401402c1b0f0015084940c0301c1c501d81222000d800340c40305200030a10381007158038280e804580c0051300300700007400604484000d040290f01841 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 793681429 1250 793680179 793680193
    0xb030706270806100e011a0405040b041d0f0f0a02030309042304050304050a061d0405190617010b010206070f0c08120907180e0a080d0b060a11060f04050d030e 70
    0x3a0180c181181940d48544c2441402024480000e41150382401400c440300900d0301c4071140c0c0a49003d6000c0c0740201c0d0302c03c58a84603a0320043d61681c1040ca00b50707103540000c0e030b400b200b42100709941c1e0308084140c04290080213091101a040864541080ca801802461070003001e0070401c401050002050f111100880342e0850007e841c00d4102c1c1d100706d02c03810086503103d00b040104540a0303010344c0102c0030803402082807a9408040c205250040006450100c1c150f19540c041c0600c0c46040d20000e07104501c0c014000134030304030b806814100b51820700000c101c9400c040b401282c49280855071180480d00082c0c50360080c40c45150141405409103180509002c00b8401d01c14954600b9074070307a2059400580140101c2c1016100c4101c3c08100d088100032242d0400007035929103428590181c11503202103080c00b0001c289400c0411190f500400540da12050003001410000e600b0b024140741c0c7c89007a0000340205403081807180120f0f003140c010b1900c4016010101e000d8019242410400d0180ea9 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 793682679 1250 793681429 793681439
    0xc18060604081b03070e0601050d0509010b0d050a11042705012309150108071e0b0a080a0b27060a091803030f05160c140a0809040b03070627 62
    0x10100101800c4041c05604440a803801010f00c0d00c0170f02e0b00000f0b1841910b00c14041242c0c0c100084810902d510303d00400c4964440b42d0544c0101001c03406c494001d20002c05120400402040b04024507100742e04030803145000206110488449003480d40000281d800701c84040c000000c0400003a92042d0004110007600700160204059410303800105000000c090020302d250600c0124098a181e80c0780d5011580340425042c1c0d9040c1030310540860380c22010342c070b01ca860340030303203040c1c001c0c005480416030340e080f081100500500301221800102807821041f84079914244007054149122048003103030f441051400c404410402030130382c43c0d03c1100400300040c00e04c114050307641c0211001e04c0158145c0960b05014094440081401c000c0f98076000c10001801d4400120741c1540344a8501071134845803903e0001140c60964401d6101841100c0601d41000003aa009000d045000e55052080e0713807802c0c040c503554a801e80a814040b40203030342039402d0010119105a22410300e02400303005656a8 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 793683929 1250 793682679 793682683
    0xa050625060501050f030f030901030905030f030c090109081c031a1002010b13060317070302070f0806010504060e09070b0c160837061509050a1407020c1806060408 72
    0xea40111112621000100818075040c000302140c004150080c20088416044164481c440c0c1c865060605170f83d45840304c14444204246c2d180c2c1c860310140035075282800d242c3c04d266900403115079030005804072001315681c0c03c0405e2400100d02601d80c2108070000422065020789441564051061043d5518402e90f90307485150120000c001d4000040e1109110240801881d40e1162140103d080520810007d540e51440e44100b080d080c1000b6150b510380e2030120304044065204140309841d40c1740208080001050290494800312010007200c4da0365400e6000084007102c0780340c0d080e08105420030040c40113000424a049080c400d03034420202c501d134020140000c03600140603950110b0502d10980180b0581c0200d40d00c21070010510946112024072600131403010300030310f0f560b103899441d80b00400030003800015010040044c005840d00500c4d450081c8a615403e00003d906071b00402c0c400ca001203080b10803140041c02c408100c0304d08084003000c1d440c000d070103a030b000300003044001001001 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 793685179 1250 793683929 793683997
    0xc02032826010603050705090603040803091906150f08032a0f062a040303031515080403080c040f030305090f06041205100605010c15110427020304020a0506 69
    0x440c6490381d00300e5041410040442e0001049481440000c100c0c4800301d41c0c5040c1600e5001d98010901550390390388141ea07509094492400302c00680c25003020104100640d003000c49802c0000c05403c154958800605140d2101442200c0c4250010440b440c1c0c2000400d008624000d9540f002c06100003004d01c17450310345902c2d20500c500c03542012051001284054043c0c461a00500154119a0714a0700c01011a4842c07403200500703240d40c0d04411104e4103400c030003503801000d091131444802d0030084d40181118900302e03411800180d040300011030500001060703909030751340c007035102c20003505664060720254840d024499200043c40014215035036043c0080001d041c0d0700c240340340c40c048140380c418500170902480902c12402d00c0d03024403032a40e01c4440100c3c440c0d006498100c1a4840d0102179008100741c0c1042c8103618400180403a640d244850a000d45a40644080b07460070400c60b4401d00700c6c0401c3d24003e5200340045c408100d50314100c0050207030150007040c549900d64544040d07900c0c00070 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 793686429 1250 793685179 793685237
    0x6030a0209090c04030503040501120f091103190b06060706090c060207050315041a060d150e0f01060f0303050a1206150306080105070801290c100c020328 68
    0xd0000703800d00707050400b010074641002c0740b800300c02e051a08542d9040d4890269000f49410001c090030291103c180369007000040010651080060b050f45040070603000401c400d28600a2144070314070443c81c035820419014032034228241d55a141c1b02c0d0070030092550300c219400c0d1002034980440d24045070f140401c5a0003010560018540c1c03a26010926007070021101d1215139241b02c010400c00403427001044503001d001c10030000c280310390b01d00000a1080c000c45002500742551032042c40c0e140303d002d03800701d100d42d2032000c11140c030040000c0c0e120b4240c034641d024125099103920300c20000640524041d000d408064184070000351420641c8000f110141d41c4601160084601600c070103640500c91040034007800e20081c001407801500181071608180b00e01221341820f0400142e050241c0402c40340c035000035030116a51303040303c40307211039a0f80d0511106e1f100c5103140030010040c03280000211a02c1c4089280076103800d10358981c0d0030b00e080001c1c501d2070f828440810304c4240315642d2601a008594 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 793687679 1250 793686429 793686431
    0x30b0111060112020a05031c0e01050706051f0510050412060b09071701151d03012c0f01060e07050c071203050a0810080a0803060d0204110c011103060612040c030206030a 75
    0xf90040015040e5294056400b035009104008080c0981d854400700403016810841e0740130400c2001218640f1440c4009000940781c002402644006440b0300441c0d2000030f802c0030055601c3d00d04122040304010360301c2d004503600304010003031a115541205034460207103c0020f40480d0001c00310701c1800c800c80342507000424401c0c17881c0301c050072003c0032400740480d41052002ca00d40740001601d13101228401e40b440e03810116501502355003d4104501c160714000c10380a440070801e006a050070300d1800c8014140c000c0c1d00c50301413490414400c0c402192035800c0700000945800f1400c1d40d0981c0521619000c074090070788085241c1007040d02c7c4009003407003540c50300e99600c111a4020300c1581d004d050602c112202e000c007081651000100007051f541c229400540e00d4540c00002244250030b440000e40090402c14400742c1c2c3c07401d103009007008001101c02405040c032581540c031081d1004550159000c40c0c248010800c1d0980c00c011503611a00c590100c0d01020b4498000800b560004c46100c3c403c5 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 793688929 1250 793687679 793687709
    0x50d0615030807210e210708010e0a020a0506120708090c03030301031a0f070905061819060207060801120b04020609030610050f03070506071209170d090b0316030b01110601 76
    0x1c4502e070800c4c944086040c94902c0000220b0030020341c60401260000f40d000d02000c9661912078014410381d0024a00c89000700031100100c900d6641f580f14421050b8810240780700000343e5400c040c070031646420403000310f600c0343d5034a1010a4032a940098040324041c8102840071001e900c041000350b0285010703842c00071080190300e001c00040b050080500d1034001c5901c0502808940000008095840c00c0320600e03180c994400c803011203200010031060744108010707502c9401c8c42c01c807923800c0182e80b420b50954031180c2e250217041d00c00403030a00c40d02180e40d0785102101d0205260519043e003192005008900d070115180010b803a140040e034204030500c504910402c1203190034003900600390401d0300030305040c1e454074000034614000c0e0b81000d001002d0702402064200e104a10136405000e00c5020780c181d860050401c1d43da1410201d00e1603000ca041660081100e0001c201600c0c480d081a004a03070401160220846c080c102902e020750503c020022600c2614409120640c043c0001d82540191 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 793690179 1250 793688929 793688963
    0x605160f03020c09090307020306011413060e1b0c1c03090b0403031508010b010203030a0b01021207030507060501050a050d03030908041a092821020a18050a06050d0615030807 77
    0x4201300c0500000d16640c010800800140c4021541604556110310502c20702c07414170f40424891401c840c0700702c0e0b20514019011402c0d0700c1460400e03018400080904010072040c88c503e04181c4141c0b0340b1095540e00c42c2c1003c250384003044480701800311003490080f50140c1c0703d988041e500c003400d8a080340842c1c0c0351200512205200c044180042c1045802403100301400310001c5d40364800907116400103916412107039a540d0081002c04400164455059510030b0b030390400604a030088071086516500741000003509142101070842030310700042412049014640c0c0a0700208100340084410075000e02000503031010300b1018800707451040380f6460340c0d03040000c200300e031f14510701100e081c40f22004130b0759040090405954205417003680c45154400002040034000680c209180254810351803a40803880b00c00a246080202e1881002401551034070344407101568454020035030010b03015000304010038801d4100c0c4016850107101c0448854a0340c56a2140781d10a4205540403c82e0a0b4200b00b = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 793691429 1250 793690179 793690189
    0x3062d090e030c0d180b030c0405060a17092113090f061d101206060810020403050f1f0b1504080303240616060f090c050315040c0605160f03020c 64
    0xd022010302d0600c21100c03044070a1142175507140a0402e40d401d0103c000346104040c082260058500240196114822400000c01c2c0c10303a030761a100389240d40180498502d20300080e918030805a14240a0b0005080c0c7c7c03e5408207400c00614070366640c106150002c1d0070140c600c590b540703503003101c000842c14a007040c3e040d840340250305080c9215501c5490800184c62054640c81d170945520301d0b0b2002c4144500c2c14036070003401d44c94101207550300400204000d181c41c1640103000700d070b11078400d8642c1d0301e1075008400c1d02c4107000013816902555980084c1203001d840e600412120400811140b0311483d6102d810031190401c2e04442c104d0341c030000910039004542c0000422414107035400c035480d04080c0d00400c45a00641d14401c2d45a610082a14100021604501365a2015540802058005080c2402c4400191088038003a0003409c4503e503044e85645480d038800c0350003110f14801c2031700d40702c000c94003a03000405440c0004c82210280c2c0c0060285880601681d0080e40103040300d00000c41000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 793692679 1250 793691429 793691443
    0x7030f0608330c0715050708061c050d030e28050f03070f0204050a1112041203090308160903080301060801080c0a050d02130f0c0206040b060103062d090e030c 70
    0x18007200d02d207100380050b1002c845000d9400010908002e444098600d41880030380c1001c440c0740111420700b4204402103a220b222244104011140c28054411b100044000c0790f8041c0e00107400e0380c11440000354401d00070b80203c05202c0c500070031204002800310080e1a02058640c0da44000c00103c03080c2802d0210411902c0301d01d44244003d5444d141c41580d4504070310450001c001c0c040d41c0c6520001300d007030300c03980d008100340c4103010000341d80d6281828140803990001c840031605024100320b044c584602c00c7c070a80f1aa40c1d410b0322015059140c9000094201c010344a03244100140c4c0c44000c00000e04001c0a18001d000036200c8a10700e5040400781400c00d025007184500605140d042048140d03504508042c4454069650642005131040403078058081c40e42e03078103d80d6003444070456001d9400640c03980710714010511089545c4500c80110142c40ca00d1141d10002c1e5080303081b0031440902070310307a065555002c0340702c0c02c0f90581d20001c00081d50303401e074400642d80d000840c02c1800904140000c0c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 793693929 1250 793692679 793692733
    0x2b2d020d080d0f050f160c0b10090c0f0f08101211100203070501050105030a2a241b05031e0d0930020717030c06040c180b0102030306010807030f0608 66
    0x2c6d980c0000038400041c02c6400050014101140b010089403029220025444c00f502103000240094020040c000e8a040654010140069410407840108622a0416902400c4a4450030816a02d0000415a00414000c1c1501c00002034042821f1582d51b8203079144101c4115000340d620340a02e030610b24216401644001d010b604060704420010703e50180a40d05004250b4581070006112408820303c000c094004608400d081040c1d1040c5403000024060469442c2d65001c0d00100030481189101d1010071000700f55030b01c03e000c14640c1c2c1031800718a544c0105003030500c600b01100e14081106a0311121410703a0368003180702010341011604004801a40219010040c280e003007050025518051486440d054101030040b42e040d45070140101c52031007030f219084644604181c10304c120b0f0b003c1a8440c3c1d81c4015000a0b518000b01071078004c14640010503005181141c0d074480c015104810014110000c140d0b85131040d6444d14150b00c290009044000c00810461000a10000b8405480406 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 793695179 1250 793693929 793693951
    0x30f011505071a1302130f110f0f0c250914060d0201080907080105160e030d0507030c0311060f0a051819022b2d020d080d0f050f 57
    0x611002c20b0721103070041c54250380c9880902d4942c0e140c009504c0c0840422000135070110107498920b40084050300300c00d400105c0d05000308210b515442c010425441030000d181c0824a05020381e40d030a5082801600c01c0d285640241c844210f01d80d060314041141141540060300340109040c48001da030780c841c17100306410081c15244182401e10000381c2054a100d4024104602d103c00203103c1c580c1800204000c080d075000a02990070236440c8094924404182c4100191405940311124903001900d0500d00d0301070385a5600c0c0a031141c0741103800f9804130405405000c80150604013a400c100401032007500700d60700c8403041e0b007480c909607010b0724070160005168541030009810b41c0b81011030804015071003020b96101d036100074804200c0c040e0768440100400009074140f41e02240c5a082043c07004d51103481c0701c15140018124084004510560440d4584c2900084000508103004c0031901c02e0302959419040c40700b0541c6100c00d45040390307000e501d11030f12901031140c4100010b01d0769403c0441d06c51 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 793696429 1250 793695179 793695187
    0xa020a020d09052107080a030203180f0a09050a0b132004050a050402030a09020306040308100812161b0b0403060609090b0601120b041d10050f190b0303030f011505 72
    0xa0b4030302c0091000d801d100010f0000400941c4d8200a1540101240002d1b60140340b21400c01130f450340c01c0b81c803501042d003070600c7d440406468100102d215840c00100006141820400100001c01005201c2500d00b55581030380001d80c0e0302c00c102d1249807800f2240c0480d401142001c4012a80920700c5108c10b501e2b070600c0103005a50302c1c000d000055070015180143c480e070f81c51341188040c00f007113140a9014001c0c00306001c14580d10121742d0344070b11002c0c1d2a02014a80e100c060725a981d400103910403c0c01010b206814512104d900003260050040004425a1035840c00041607145680d20400d11030380005007c0040050b180074450007086045003c01c809080e98413074001c1d1050081c40b150403c40c08601300788a06041fa4405016014050000c102c41d00300c080c4c0e1440240c00080d00c181c0a03201e070900442c402507450140c01e205e01c411041c07292598880c04159204082e1919401d0705c0941c44840d06029510200040d40c420703000082c81b554107500d005070440d4000490002c200401100308 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 793697679 1250 793696429 793696439
    0x50117060106091208091206092802010f110106080303071b110108040c0f03060204210c0506030702030d020c0c2403010612090b0901050405011a130203070e090a020a020d09 76
    0x90f000f04115009006151a41801c514100e210b0741b00e0820ba41d544540b17000800011400c00140c40352290b03800004584401a443c085c48420f20a0240e0b91044200c100e0320080c0154410055900c240e019401c203402c0400303030012941d080d251181c002940a41c004402c00800c0d42c0d004a1075240e010b011a0301c80c9440001e5103d04040e07900001680341071210f280c0100e410841d01c0701920b4020300b8600107460307034143c8906d05007019601601c140080a000e41d0140c035410039414580b240103e40c00842082010302d81018025550001808101540024084c00c0e0700b0b014140018461411070601034035208002808024620310810594004100c2c0000104020440e410840781500c842d820700302c2c00010f01d410b00c2005444200c0d0000c181d08101000c0c004405070540000b402180300d41c4c028044006698030711125044840e00250b80000c0207200d00800f0301841d4021500514146420003100c410700002c10142041a131301842d025a0000719040490b074103005442d0300513218a0b150b03032264901 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 793698929 1250 793697679 793697687
    0x90516020d0c02010804230a15140c18060903030c0f0d03020a12150b0a0309060f0c050702060705030d09030801081b010903021002101e060b040302092a0d050117060106 74
    0x170801000054151040c20408000750011f50044240604a43c10b501ca1490300c0009050a820f2100c201070030040350b490000208841c50f4401c010321152507040c188605400d018201e03d07112901d801400801a4007610b4400303100814108020314001c5c42c454902d04c40c2149080402c0d0030b094101823060000c600c030300740c0c040c0c60b00d840161010300124601c2400600b0554051160f400032034079010004410705407075095009070709501d029441c10404060200e068005407010450010009481080428014509140a041d1290154040b02c1c1070507200005141288d04021040d001314031148010810180100182e1303030070150080030a180076040d2030000e0a01d50042c000280304112213400349a04c24400c00400300440b144507428002007040750b065891120f03189049a02c4c0c503040c080c01084c2c1c111214101c030116940901103c00da0365a01c407124140806a41c40030030095521200e41c1c1008500c04060010361010300340014480d450071141d00c1e1440c1c8040b580f611a81c0080004000c500e0b04 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 793700179 1250 793698929 793698931
    0x2704050f011205030d020a030c03180302061306110703030b03060907210812071809060b1b240703051e04021005130b070b060616021009090516020d0c020108 69
    0x1e40085010328183c6062411401a40c6860404910205d0740c4400154140c103c00c401880b00d4070b003080581da0318804940d0320300d410701c00540940d00c90004170b03d030880c5124a11400034000c510001b2800c000200c0b00e10315500051058000903298402d4410525042c02141c1e000f02d0108001c02c4c0c1146002c1e809201e1402c02c0c2281134000c071602d030600d41801411300440f541da03034000302071000618100a0182c0b48400807560b03841051496040450a90307880e200702015034103485199410f00248801c2c2400ea0000740c4a034a540b40501c000d209811441c05102200180490101940c140303400c0d40014125a002031404040c03d050511201c1581100d40300e81da0801d0701660440c1400001b00d1099071103100c6c0c5403c4600309110350744002020f06014003e801007521980711b8690035210401042428003a1103811400c0e1021204400c0c018a8540c500e080607001d07500b00002030660b00c00114007110000c54501400765042320444054030303414010442c0b11046420b0070b14841c1c0c0f1070b030002040008 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 793701429 1250 793700179 793700189
    0xf0306060b131215020a170a09151508030a0206071707080604090c050a0e090615030d12060f06030b0306010911220308041509090902010e04090c05062704050f01 71
    0x44003500324140520f14a0740354071480400425581c482c041000204007c0405d50b95400426550307010400c03041c1d59004081c2c3d02c80c1c10141c001f010104d2034130104003c00040050f801e18002c902c0001030310340c0090014021311261500644000e00d0403040c007803d14010310340d29400400d607203c200001141c00810f802c1c3c0142e810b480c0021080014900081c1501c2903403c0035a0180d529680024a4042300c4411881a419507041c3c0d07159407140c5516600128241801c50f5040d040300200c42e13941c40c0f01d44c0c01d51400c0e00c0c3c4c8a5001c50040e6a49440c0e01410065803c4000041e4455140301d0300c030304003001164010841910100f02d641010029604c0d1070044001140341d01001d0300c0c0729103280010b608440080c6402003c800d40d216901d420041801c10340500e204046440c50500068020304ea10506002c81d4040c1c4482140d184a24100402042034020450701c001c0e0040000c5907503103510021705181c07149000c9408428006221403001c8007540c00005100740d080c00f0401c1411503000c6540c904681b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 793702679 1250 793701429 793701449
    0x81b0604031203020d110c0f16150c030903080f0405011805100e0607060e1e070605030a020a050c0703110f09061f0903050d030203040605061c0314040503070f0306060b13 75
    0x101c0d1200a0014002d50048124045408101207880303410104001c23000d9080c600889030300c1000c0c4c50a50341581c07024032410045850144078115070312700400c0b075118081c4c882e00e041c0651b11740b2903490460607017001494104203200450180304558008035044114a030798446440024503200015900c04c0441d0082807c00107000b202c3c21981d00c81c6025110750f02c2d0b1004c410711900c40c00360b6000f603680400703801d1511a44521140d5005401c00855100b0075a0035075555035284d0b82c1c48402c80000380d07201c3c1c80c1c1c40b410840c0420a0902e102e909200c0c490203107110b80010365205e01e4602c1007001c070340360080c002407107240d502d400d00170903584011280c13080c0d03509810040b1052003840001d40f840300031644060440d0154118990490b81d00d580103522840c4180f03001c0103142c41320303014000740500103410004100700d01e42c921300c00719000f102e00700142c030210b03d04141b03080d4846e40400c0c1003402c644d0002080701540901030040003a18001d81c40501040d69040c3e003072005000841c0040041440b6a032598 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 793703929 1250 793702679 793702687
    0xb010f081522051902040b090405032203061b020d02070803220b0708090a0609060e0904171c060603230a02040b0c0f01110c0d080c07020406081b060403120302 70
    0x308140e015010045410105850b0852032944142c0700544030100e04911480c60544000349604d8604919400340790042e0084cc01c00c1880d81c0800008410314444c00d0316400c0c0544000700042d13490103951009001410310803d20800480c019151100c945005c00079508810003e1020b0200042a90a00c2c1e0019902c03c00074280e80050a1000760290414004104001400b8050000e00e40042024140030351708444000d94840c4100c1c4c03064007030b008520000e11800007502d082c0c42c044031102c1d081802407036a1031006c5041310f0001000d074410819200c80307e9851052258800543c41068010285820281b090340d44000305401403640c40311094080071101c00100743c00c0241541910050014200300a0b510702100c005c00d135a844400710503201546c2400142f00004c3d4000c0c09880c001d2646100506010620b0201a070b02d0440c01800b01030144400c0c0400f4025960f2401450014888880078224250f540700a83c0e0300781c01554640c60140004000420014050156500340040d1501d001604c0d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 793705035 1106 793703929 793703971
    0x203040312090302010e210601091d0d05120703150902090415030b06120f0d2a02220213140a06030e031b03160b010f0815 54
    0x141b0180340a4440d03003000c21605202c04140031144100d02171a50400d0f2601c1c40990140f6181c035142d0b00109120028100010003c1c51941c02500803c1100c0030701600314031030091110180a1010005401d8034800d41c092140c0080c0855140d00d65541d856454002e5041045003500c42d034644048451148023030a151030450750b010f604c540c0103503540020400598008103044007980141c5c20036504590041c000714a00c0300907521220400e05101c070480e5041c1c84e038520f81c4121101000a818050303942c1c000b440c00e240540254480f1415018000c040203070180b0401da11400b80409408a400a070503814541d4043e0107503200c1e050180d80c0d0300101c00340c1d010700300e40601c00e400801c00300d82111501407484102c1c860500032645851902e440c1542c03480f00321241540c00c540d10000500603510010400402032071540014690b02117440401400b400004d01801d064400d8070540b034076 = true := by decide +kernel

theorem cover : BRFrame.Cov 793525179 793705035 := by
  have h0 := BRFrame.cov_init 793525179
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793525179 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 793525179 ≤ n) (h2 : n < 793705035) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
