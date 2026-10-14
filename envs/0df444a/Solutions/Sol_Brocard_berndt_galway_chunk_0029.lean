-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0029
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:26:34.573075+00:00
-- url     : https://prove2.me/submissions/0b960b06-680d-48c7-9adb-fb246bf94313

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 5035978 ≤ n < 5215834 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 5037228 1250 5035978 5035999
    0xc06060b07020906040507051c051f060806010e0a15020a02090f10030f0609060e0607030606020102180d050703020319140a02090a0213080609010c030b0409050d2102040b030114 78
    0x21640f0660014846030045a482e0b006c03070401801034064840ea44440c0c6125420340c1110003c035400f5101c107449103400b002e4140e5100882c2813681d0703000003c4c1e0f038141e07072240c00c1d55076240c00440d1180720707003038403a40c004209130030124800010307400301e142d008196001002800f4040c81480b10b4804001c2404903003c0c1c890b4148a176494512020760102ca4005048000c1c008450901400030070b03061030014102c40c41c04110020440c00415414407a44aa40f01004010b55420083e82231380f20329902c1c40e919803140c1800030511b02c0c000b007003540854000c8003103030045a125804a0300d0b0000c0d180391501800305081001007000f0030403050003400c18001c030190802110380d0780401c0080384040d190758200da401082024103403040d00c140000a1410804644160610546007402006d0928580300020305000d00d280035400e0034040c044a05601200a2007070f51010003044500d004a0214145064020500c142c507001e44e50000c1d00181003130314130340e03952545003010701070707542450301c0c4c50f01c0c040d0099a0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 5038478 1250 5037228 5037233
    0xf0b041508040303140f040b101a0f13060203070507090603050307030c05031204110102010c0c02030c01051c0204030302010c030501080d080a020d06170304060f0207080715030605040c0c06060b07 86
    0xe5004999616060003126a1210714064024164440d881410308503c1010441007980d0f000f01d140c0518060300c14040c468a801101c4039012000d4090a071500481c6400340d10080100c0009180c50800b50071302d1810300c0e0341102c0744031410300c1d641c0c0070500513070010802400b805414480e0300f004150003a400c0044d189076584260f280d0040100250500a8001c511014807400340201d52040b4007103201c42c4c50354034043c07900e030005051150300d260066280c1060210702e035020350a602d00c241d800500600185d8407090044410340e00c90070701350344c81901c0c0d402d8041c00300c0d4040c0007400c003a602c240c00202d01d241d034201e0001c0444030140d1020f805644440c0c40e0400075074103c2d0b2000c1d00003420340d6016950380d00b80e25608000c0c2045e5804024620340c120203421002501201420030342e5900d41e2201d1900c020410101d90760b035018091000d042d0030441d02001103100103e240e461400e040c0c10046141683c4800240c2199607502080010a6820203d00204560751180201401c105000941400043c1c0c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 5039728 1250 5038478 5038499
    0x3030a020c040f0e0609011406040606050301090c05041a0c0607051204030309110604060504030606060905030303070503060411120403020c040203090a0602030402040f0203040c060207210f030e060a020102040f0b04 94
    0x201d031a6008554510b001403034020203030031041c00e042551088a1017400c00100300c1d4000c1c55060390400010700301002003881464203001d00340407601c80713990f01401d59080142410060061090181c02d000c010000090304104850354000d20202118002c3d0302c46001185031820700400511600c2000804c004542d868250822101e41003501468005007110191411610180c0720b24007803039110001040000c1c0190b844001402a0b030310a01082c03003481d0380e51000b500c0c82400c5000e40c0303034140c005000050b246032040b80030b1940b000c03000b13001240d10103855508800580c0302c90278040b0402055420042890740401c000c5513070314020b413411031651500704003841c3c85d544005c0c801002940c00001050540d502d54002013030742203003a041156282842d1030310541000e80340c800c070340c09401100d500142261402c22040403007155040208803801440c0d07214603241d00030384e80c00c0b82030000c07006040880c0d41341c480c054114111540c00041c0e8460400328003000f003607501e03441903884800c100028880460709 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 5040978 1250 5039728 5039743
    0x803071d01170402030f0717010b0d05060103031202070804030803060117010305061303020f06070c02030d03020301050a151e080a14010810021c020703020303100b03090a0b0a0e070905040c0503030a02 88
    0x40d014808900d40f40d40c400030b402c00c10084004081e81c8140e071804070b0728119201c07100c59080d01f100c00800c030b101e5004082c0100752020303550160964124400403c0402c1c00f80e4400001c0c0c4400c41001450800980e90741c100719005504251400701010040096558110844112050501d180031a0340c0d0725654801e03581344e2005000c01140c41c0c0f07815041e001c040c02040101c0403480c505040d5a04d9140004005050500d1b80e081a81300344108541d00140e503010f8400c07a41030710400340149103201d04106081010141204000b0100b01e4040441d1180c03011221702e0208030411030f5134003c003d04110040e0001e0303800080c20b40201c00c20800040140c0b0703500050031500030480c44405a200c4010304075540c400199485000300351030001988a0416502000862081c14243ca001103070765103580410009000480b500c0349036034003100540021800450280d80d1240f4082c201042d0130840e050141e042c043d480d032001c0c0c0c415448100384001c01c0f0034001800d02400f000d034011801d0020701c8200945d2044c0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 5042228 1250 5040978 5041007
    0x807080604020723070504140a06170703020f1f0305010305010614010c0b15120703030201050703060602030d0e03040f0305060402040b010309080301140d0b09060a050108010b0604090f09060501030803071d01 91
    0x104c44081d00034200c0c1401048001d010060040004e01d002031000e41c800c0d80d0071641d504650785401c13000b18225140c03408406100240c04000e103019421982840181001c0600095100320440600600c10082007040c694010351582c0103d40c3c0d500d503260050941c0c110390414007680e401003915140700d99006081c4010030b504800917200c59101c01d0b0340c0b03a05106440c001580c02c8495808540b1020790001100390032a84694001c00a80d45c6005045041328418041c210058000700014280d04000d50000c00c03070245110281c0b485c10f9500c45900450b5a507552040302c00d078011904100940c6440d2041382c0c8440c0007030806129904080d5520f414500c814056000e5030072000348500d010340c0f110300b01c040e881580b25a00600c00e003400810070307a440da0100c8029182500300800418030700418040c580800102070001070500e820107454501412010080c88801c030303030310b0380d0380e102091290042c580294020389841d03a40341006140105146506111002c190f007106903d0398151741e211140200000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 5043478 1250 5042228 5042273
    0x80d11030a050d0f0204030609200108040201050301030807050106080304080d03060e151e04050c030103050c010c0503030703020a050f070f020a0603021e03060607020d050606100c0c0b0702030307050105040308070806040207 98
    0x5401410b804006d00071600003616680ca4100d0000401c0080c000389080300a8541802c0c0031100e0301001103880600450b8003c1c0095030a20041000176210b0007c0c2180034410800402c1d61a1520343c01461500982d000f48981e40c40440c5a0520395010b00c01c1da0003a1100d03243e0708115240070003045a0481c40349814a00880541003410403c19844041005c2820010401d001904028404698070b80080c003054a09003e000860780013580036400048855500001850a642e124403041c1d0081d0030400003003003400f40420141500503202001050100c0c81541d80681c0c5e150180180482d91603030b60854024103104101d11101d00c2540400003985503400a0420390343ea566001050050042542c02074010404484040400501190b9035100e80c5040d1444058a4158801280d11061a4a0207080450ad1490034000302202e40010010707140080c0469141c54840d60758642110400c44040d400141e940c0d007070002c2d1381c2c3d000d42c070346801c80e00071582581066016140d10301200d145071150068003 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 5044728 1250 5043478 5043491
    0x5090307300309030c0608040308070305090106051207080706090b0712050f03190c14030402120a020a09020306010210020403030e13060b0706020301181b080903070606080d11030a050d 81
    0x40035046481c529151032003203058141d40b441c000d4080055404112100d602410001c620540b00d281e65503c03d03901940d80b040d0f0f1707484090040d0014500900960969500c8220102d95500c0700c0c601070599040340001015480d01d4010410300300300098101a04100c08407404210004442d81a42d41c0903030072503020708189240e100e0a40c1e05108000b40f003038180801200f00002d41c001c6000207411245010703001e11901c400d10504403241ca0f25407280d80d061400c248041000350410f95440e4103600344d00000c650b52082d00c7d400080e070b1071401e07034010324125400204201065a040c000340b410070106200c1542454119500588402c5807031400760b0180080e160b115201050542101c0001d00410043c02c0d640d650b00d0400e04040e50090254107070000f00240c08801d103092500c01d98480040f0345c809420703880d442840171140480007810720320a512003401980702080051040000810985000f041741494282d40a4050751126803d807070203070401c0c4030820104c0c1d040341c01c0310036040c0914030002c0d48 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 5045978 1250 5044728 5044769
    0x201080a0c0509040501030f030206010911120a0e0111030405071d010e070c02041802010305010b07081e1903090203061e1b0c0d0201020304020111060402010905010806130507090f0605090307 84
    0x18000d160f549944a42020000030911280c0380860540600903800c4c3c2d10396030380303034a40d11058415040d41c140900e0010072504440a80c00307046030340c01c240b4030100070849590030500039007035400381813044c0e030644400803d0104100003001140020480841c00295403807140d4031924502d5414801c010408481d0000200801e00c00c41e000640158010704c204044c0c49541000c5801505451080703012a1401d030010032425140426264402d6200502034500b4014810710990042c109101c07444000040c0711545d406000300d1030240c0034440d1550005070070106401014075010010300000800b01d00f001c02c60039541d081e60002540b02c0900da070310b04034010303583c0c44084040c420317660ba100c0c5c1801504207203012154190001c40c0102c2c000d134bc1e51100b00058021854031040706880007800710b210900b041205500a0b0a6141e010000402602004d200c40e1402400d550382158a140000e0041606101901881c0306500140c1010300d4035504094508002c00e90380d038014010842c41e203402d034258004 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 5047228 1250 5045978 5045987
    0x170f0607030203180a030807030605010201020309030a050c120304050102030618090a0204110f190206090313030f060b060a020705090a151404090804090e10020903030711060c0f0a06060504090201080a0c 89
    0x25040095022545e403c5d030541801441c41c1000e54242000034100340001074650320500950b8000c10200c03000e140741a200000a9031950b124103425030030342c010403800c5402a621800510300c554020000565207140c504100300741c008031b00749840d8101d0941e60600c44110320003d641c100131a4160360000e1000c1c2c8020f07201c0a28000c000101461850010b03004055003041d602e070070854555038080310f10513152009003030f40780d0042c05800c020040322101c01f0404580c503416001010303030140000150a00c01100030604652000e440da0016a01c65002085641441a2042d0744490103140c200480c4516012903200e11405124004220751400d0420340c85689a5004e0203074a0352284c102c03551182e40d80341b86009003419250346c4403603000e510400d00310a03845000300d540c90352004014502d801650b035a00c000104520f100e0a0300401d041c4003114020008020051404207102c0003014401c885240c003805440c0b45d6088140207505264100d80141d030880b1900d0b406c00315030300b0085076882840c581142c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 5048478 1250 5047228 5047261
    0x3080a12060308160c0b0d09050601060905031c09090c0305240609090405030f12040515070807050304110303030705091504030804030311010902040c11010e06060108011a0c0303040309170f0607030203 88
    0x2c421b000001c3c4d9500f10501135000d113648034854070030b070341190baa1010140d401d28040d100d401e8043d007003940c244604002d440d910f00c0140f40c10b424802d0140d07444408210490b1959501d03400441d80c3c0d2418481013108011141c0040c2c4140112105480c0100021a501d4080c9854a074001c0f10100085410403806005850031135000307140da40c5c0c407103083c2c0301c503231442102c2614180c405008080c8405114403182200034858020341e152a070203502d4007201100d5940c0028800d8a0508001500745c130aa0303010300007180202040d6440a8503528130004018280b18441c07280c0b00030b018104020030000d0f001c0000d6404484d01b40c20450007030041403d101f0b003d8090b51800039401780c60f200d2604c200d00c1d04082507550b22000760f002009141e1988840503a17408041e228280801c098800422011010002c5044429060383c0820b080145810183d46160000e85003200495070b02002441907140c0019210380907070201008000040c100080e080c0c684502800d00e10425400000280300d0201d440f1103407 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 5049728 1250 5048478 5048489
    0x7021906060509040c0609120503120711010504080309100e0d030b0109080d020a0b0c03040f02240d0203060114040b0d09060207120c0209060409030203090405040302150103080a12060308160c 84
    0xc00d0703e20305840c1c00c5e40040748500501010418444001c200520300c01402800e540d4010025898108841c2c6038800202c0001d00000070010103003201c401d06882070051a0195104c0d0000d55100d00f00f1844943c20180300e181030600403403405969030181040040c156544810500780013507002c00c0c031001203503400140e8012200a00c50031164040055001507280c0c1d07014020645036110342c807225134400c1580b106660180000d800e40008001629005440092450740002c0380884010070b040652102e801242511640300e6001c41003001c1540c00031056010026526256440c0c1400c102c140f0160b8096410024241a0f6882c005020440c0e241d0440d054160012005d03030000e018a02c00070704107042040200e00610340f440c0403890703e0400d800b075454155810340256040c0f215000520005040c000d0045d8214894240f0343c00c119100389003010b020f180240322096582e014003c1c040c102031083c1c00200f020500d03040c8100003142c240000e5a0f24125000503e04003643c140c21302c210f4000c03898101c07 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 5050978 1250 5049728 5049739
    0xe060a05030f0c01090b0315040c1101091406010501030203010b0d0b01030207060204080d031103090a08071104060b130602030306100e010c06050a0605040e06060306040807030918020a02010e06070219060605 91
    0x981c075080000315401400c034240e171050130980c0c5501d68900140810303900560500c03d4403154540c2d81c07030180c11036070642100d480c04c4070150120b07a685900f5030780b1079201a54558204000e00c40c401c80f060090318050300080c201035146516245440030544240e030300c16003405548201c1998980e100c1e40403074942c00d4000320195165501d4801030350303c0303090701070766500420b161580507120680402d05591140c0b0840c2c0151120380c005440b2046107510442c0c0481d940007183d514240c90360f540c2d118100251035a051082d44a0b0040941001c803442c00d500500155072050041205980d02c0d82131191001c0603d02d03201410ba6401c030011703035225424541c0205007600744000c2000032111540407104841e022107040c007a4000807032805441e214207031295900742c0c000000281c003180d680d1000f403404c0e40c402d250100301e01e5900d900000355a4101c0c000408220740010b403400200f5424002d46100c01601c0c1d0140c403207820241c1010b981c582910500d205044c1001008405022241c1d20842c01014043d24 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 5052228 1250 5050978 5050993
    0x915070504060806011d060904060506031005010f020102040e0415090b0702031801030908070201030e0a06020301030b190b031c020f0102030405070e10030803060603040c051f02010c02030a090e060a0503 89
    0x18080c025812034040c902c00a8040000100d841d84900f00c9410403180207190244403050711000e111065000010294110707444074000501341e126100118440c0000c41d003134846450810f8001440e10400380514421603006201c00d001c01c000f200c015035000307940700008010604011408001900f4a1140540648041e074100145a030300400101120121100034004010a040054040312000e04002e4081c200921010300194002d90103a84080914011200d0302155640d0b180107a0303009810032240304881c80107000840c07002001130f0140c0842010284840382601c2c0200b41d44903100358000c1e14506031110000c1030503000303209080321500408003e642c0e074600303800c11903600d820500c200314400010100191140c0248050181541e40c040650751660300c0307510411989810140c001e0310f1311410094001103581c0e955000c0d8880094145080400382680f45020f400c69a034040c4920030741d042005180092a4442440001e40b1045074420100c3d03210140495084080390b00501e405200340d42 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 5053478 1250 5052228 5052241
    0x90803040c05090604020a0503010b031302030d02010b0a05040902010e040f0221061519120b0a030609050111030601020a030c11030a0503070c05060702010c0201030903030b1f0305090604080a080915 87
    0x1c614400391003050707900719256107a21007404201e22880304050005041400180b045018070401141c1020081c651a00b0808180e000a400c0100920140025070341da0118421941030140211004007000c40f010401d18201e900041c140703403101c41c1c0c401d104642d03a0f20120f010301d504c0e90568404400c150ba105040c20003901c90320b0800d50042c1d4100348909450145061241503000440d0101c3c2c2d44241c28200513149050f040e02c011315603504101e035040e126003140f419506c07074060340c40046001d00c0001c9006070060070410300311a40c060780c280940c4410420003189903000581004520b0381450100140052070030448041c51f20064110b515006071010541800350000103001020701411001a59541d100c0030080036110f540b200038003044104d46c11001540c000c0e807000781500d001c0c1c100828000490070014080507000481b02d80c2a50f04d02214010700396051041c2540004107030700608845c01c2540f42ca440c0d500480008034200b080040000b01549000e020001d009038803121180300754103005 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 5054728 1250 5053478 5053493
    0x608010e03090312040f0330030c0e0d0203060711070306060605070203060703050103050a080c030c0601080706090503030f16030908030c03030103140d12050a06080f01050907060c08030601080402010309080304 92
    0x181c0040b0f20a2182180200e942c0b6804812141119500d94409041d146940d80745059007082040c540c4144000d64a0300001401440e00341909868650f00040d04480884024001410041d0064080c066440000b001030700c0000d4029000341890401038512a18500482d00e080b800d908014500d600b02680010308a402401508003031703100700c0694a06545030b40d012030444000b44005032480e40644000000f040c660001440741d41e07071b003106503890040c44442880c13402c002a40540c64a0b803020070100070050384100d40c01e01400044000e0340c642200e210b0002954002c1c1c1812030784008100511200f01070144000301c0003400c401055a440705040c0c0f040c29141e81091001342c0e0720403c1c54113501981800400d64000080c15030f1141848260210346201c01040c005003d0f407522a0398600118180008009107200c0d0f0074140700104e11850f08100850a25846510100600c04040d50f85400202c02c0c5041d00d40c4140d0030310703240c0f000d6515400100e002d04010100070b07042c241c002080c0014010107 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 5055978 1250 5054728 5054737
    0x21206010e0303070302060c091c050624010e04020d06030b0406050402040f060305030711040e0304030b01140d0302030f030901090605040807050c01140403030c0c05030d09091a010503040209040201030608010e03 93
    0x262030714000c0c29504814140c491044040060040c0c028a0000f059403c40c04050104458042d0500140f210b141c0b425005501c081501a9219400035040008840052a59030350340c90b0103144500c0f1568000c40081c0c6060000c0502a100310b401144c540141140c542c0403100464210020120740c0c00c0c5414500010041680c050b030085045c9462103600300010b0180b0401c0700d40c03000c002c2d8500842c2e81c5542c1074012079152502d50107615401002003060007000500f019500030f60b100201549040c500b0802445407044050044403158401070100341c01000356101d100800c00f0003541c84c1d483e040194018003603100024040340c0740c001408180f0034010060031781c4521810450306030880c0e01d00151214112251211540481000180006031003003100241c1c1d248900d4079914034940340c900003030600c8101940c000000d401c2140400c07080c00c281c091104050035800d44c1c00300a94042000030417900c401040a805010b50b080130604591090780410001c0800300020490b030155090040e440390301 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 5057228 1250 5055978 5055991
    0x114040c08060c0301050105090301060b030901020903070f0b030f04140303010f0302040f05040b0105040b010c020303030f07080705030108070608070e03070303050a0e0a05090f040203031207030507080108010926040302040212 99
    0x520400c00700e111907000581500034900e1014080c11a881c0400465959220110454042d500c450000448111080c09140a10300c071100158503400060b09152502c1c5880d030260b40a99501c2c3d10801a03e8250b008a80c0c000d8001d106010a542e20750400304190a50008000e2880c4400400003400301d5800803040b0030349100326002d0000c0504120200d081d50700c2990054100b0780d4100c0100204c2c40d007036014001040c01070512000c807541a4000a0840c1c10484010901000305401c2100c00c1da8040a050f500180c58145a405c45d418540c3c029650603050140d64280300703958010490003401062036200c082d80080860380c655841c2d240c010055003010304880c0c0800d11240c080340e12840c1c001e0b401c606480028000d103440d89c1d10982c020380b440030041c01c1039030035010400c904200150a01040e030311844c011380b008203031030800c58001021100145d004c00b40303a074540000200006e156103807442c2280d40c0302140f070317080f8180e20000c0c0110f81304940c0001c3d4020705c0020901c22000c3c440c04900d10610 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 5058478 1250 5057228 5057243
    0x30106030c030c0801050613090603060b090714070609020d02060703030603051207050c0409080f031005090601031119120212010906090c0203040306110405060d02030414030a0914030f011404 84
    0xc1001030164259040d40b03d45501103501c0d08010b00c1581801d0014110800c0740c0403021711603130b569115400403101c1070723001901e241e40c03540521001c03820300320003660704900a40f615500120150100d102d65009111000b0003a94892a0580c155a075a01c0001c0000e40c0061909039030b2000c4d8135000e00101520311040381d4a00524240410f892242825618441c1e08a4042c0004070b50000400c070040c00e0b1700004540d07180d42441848410a0315401a51040c150444502643c070300b001c04016440100030529410142454050000d43e0000c90645144c07540d81c04180361810084001500c0e04204e40d8100c022080c03012580081040b000c1d038034181200d911200c00c11106440e4291901907481d0100c1030300250740100005c00c005103043c1c4c002c2c40300381d070340c8400113080c191074a0003e884c44e44134803003118000d40c0101c14071050195003480e01403041410b10007103103017104010010b00081074500ca018541d101030003090b80c50303440a204c180d1002c09044005c102c002000301420b41c00d4101942d064600d507 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 5059728 1250 5058478 5058491
    0x4080d050f13080606090604050709090203090304171b040204140418120215090601030b011701020405040906060312030e1c03140709060f030c0e0d051006030302060615040308030103020d0203030415020303010603 93
    0x88c00e091280038028245941c1c0c00d0460b0b8140001c0ca0003a6001811640707051000b003000080b1081f0b03c0b005140e500900402514450581210b00152103070b03a01b203010b1149104010401c00440c8007045e2601401d8141c0d00400c4401e581040060340c003007049800b0704510000012036030201d9010908001c00c110700f40d421040e87e103504a12550310380d402d01004020015210060010030106480d011503028100b0001d0b26141d01c030008501601d141032822990b2989030320302071040000010740c40c0c2c0c0241a52078204103207a1003015547d81c5178000007038031a814021a5004901070700c2500720b80352210028000400b1810252001032294015120340310018401407490003416210340161307a00201c5660381c2a00001c104420411003034440232040310f062144410300c0a04503030f0350180900840c01b0f80c01500052820b03800380a8840c846150b06003415804000610000701e42e11b007624107607501500c0b01106c095441c03000c01d103544119004120030000341c009002c1c1960b40000154180c50490303405001d030 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 5060978 1250 5059728 5059741
    0x60708090f010b03100b0d05030a0203070605070302160308070302070c080304030303140f16050405090f0a0c0c02061806040305061602010b090105030d080405010204090e0304090c0504080d050f1308060609 90
    0xc890840760310300d030b068008070317411038841840d5000384d015498010007001d101c0c4401d598040c9591700610429001d41c20105400003804245e20606030700c10f6050405610306195142850800c1000000080c244001280441e04c007605c00d82c10f540303245d0760104101200c141c4030160701d55250041c0c4004c07070010b41404503503200e8250709031140340604120046140540c4421042c28071598003e9480002c00200f48000241079440381010303405026640070321080740c1010400041907540d44041c10042c00300d2010608011707141d0720202e07104089641d10b00e071000c0c00c4510014450344556440985184110414400e03400c1c131020001103d008241c008102c0c003580380042c0300d2172900c240302d41c40e80760704240d8103030034214052200140d000d0301c00d07400145440e842c2c0040c101240d1100008840c0b56001142c244a8150144100e962101c2181022814103152907142a940c1d21090301d04c800300000410982600740741241520f40304080e482c00150107039110f43e4243e5a40b00200c444a20820051020520 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 5062228 1250 5060978 5060981
    0x403020f01050901080109020304030c0f030315081614030c04020a020d0e01030b130207061b020f0708030421030509030a0f0219050609010c0c090905210315010f020f060708090f01 79
    0x401c00c045e116100941e01c0e0400714002504002c00590902000028540008000c1680b05000741d210303803400200340804814069090810740c215000560010800c000485074002012048a1b1168440800c6400c100c002c603061441c400750300c0f82c2150011403800344540c4c000c1107140340303c00707144e503452400d0701580011000c0d42c2c280b050050300800341c0541d050340700082e60024905640964404074003001c0d61844064031840c690b0718a801a0401417041d00c010ba002d0107280c0040c00e4410080d42401d0801034003e1070441082c841c011540031501c07401e001c02d03019005640c9100c20003400c0d20030302c103c05c0c1060910386580c13403422403180750b8508001400120070740f1050150f8101400756030500344030340b0054942e103140030400d4035001952000080e40300d0b400e000c0e804184e40701e038001d402c4c0646a440c054440329500d00b07089050032814020030401444c41020000b40000910301860f40701d941c010280d050460114200e0b40364021002044041600f2280b4180501c400004030b80007440100480ca0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 5063478 1250 5062228 5062237
    0xf07050d020603150a15090b1206010e12030a03060504060501180303030b010c051207020301050c030103030e27070807020c030106060206010506030c0c0714030705010e09040308070504120303020403020f0105 91
    0x66011180114180c09810079401540e485240c0d51290b40c02c0d041030340c0000c0c061929960004116801012030010b016901040140003408821841800c061044400040c07a0a0041c0400d04008010600b070702c03d0743d101e9101030458103015095964484680c0c40007400761101d4082e0b60300031824031100083e103501c00e08200240c80c2031082c101c0c44c0b00781141e4045002c0c040010b986410044400420804900140714a18016070f9170764415039540020300c18107003560790007003000e03c0700f1000f0700041004c29008200701d689100704030b81c050356505540300e0207110200300c0000706c500c18507200d003000140c03504100c1032401408240c003210902c40704136003014266040c034000c400041c0c100400400082c02e022000d10f800001907206941040139102c401840c2c40c034a98400600341c0120035003d81141130178402040609400e00c1c0000c0e451610304c01088030a4000340006007008801c90009035034a00c00e005940141040541e0316580148a060041c041c0d0414041030344514581f0304900050342c001d40895 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 5064728 1250 5063478 5063489
    0x304090501140607060b01180e01090506010306030803010315140a0e0f0102030c0a050702040e0f0a030801050405010e070c03020a020a1401091e060c140102120103050d02070b0f09040e030c0f0f07 86
    0x45181c9510303907136900045c0c440c403c101b13070621030300b015089140c010f01d00c1c0c0701c030103080001d907107400540c507000e0b1401c107540000e403e403414180741910a0011400000407241980c0d003000520011340455100c41004084d80110f54446003040700038818844a103404c00310b0002541000ca852441200c40058204d01c001c1e039200d1004001048165460350184010b00405800144001007841c0548070207410603100c040c0c0e0140320303003003041001c0030150400e00450143c00300752820001c542c10f2010030800f9940180100c0d05000751074043c070b020540300f040803a64850b4090301c150109540d9903194080f1600d282101804200e0242002c9030308220548042c5c401800c01e0394074400d071484c00d4002e4500880030102500c110207083d44008030b04109000600d001c0010321000001985103080407401c101c002060710003190003040040258090383c4040c0d6840840c022403080c0c1d100c040c1c41c0024000c01a6001e2000303d80400310b9810452007001c180c50384040226010754400c003c0d160141030300d40c007141c01031 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 5065978 1250 5064728 5064739
    0x5070504090b0f06040306050906070e030304050402090d02030f0105160201090b0705031905130204060801090b1b04030c0312091e121401020c07080705040b0f0609030102090d05030409050114 84
    0x1c0110041d0354002151160000c0c3c1924802d0380c614011070f980313600c15001500c41b40e481c3c1062000030407007040419840422494108076a200c000e001a072640304920400d1b11841d0085100c2c2001c3c5ea9101218005550041c1102c07c1c0c4859801264040c0a04807411800303002d58a00c2d003a101c5006000b013643d01d690000695180381d5441078107a43d190009072284c840d0311803255860030703101114032659000b086168100b0200d03500f03038410030040d00d005403c40901d0b81d04191041c03000510008615810043e11910846000100c05042c6414007a42d4800f41503a4000800041400b448003014882501c03182c0d110038186895065090171b6084420845e4107030b89002c0410880400004051018148114412020741940c103c145083e41c10001d010032094000b2a400c110085042107800001c01e420b441c00d204861a0a0005461982005034240205800202501190760a50484050583c020301c2a40c2d16940c50602c243e0341e030007a0040c21040ba180100224517454403032501040010000c00 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 5067228 1250 5065978 5065987
    0x905010c05030f0a17090601050a05101b031209030314060f010c060203070c0c0303020f0f07080a0807050c0a0308030a050604050f0a090501090b010603020a08060406060c0b09030f0409060e0604050705 88
    0x48840303a902c44c0e180364042000882200641120b001d0b43d0b03601a007500001071600e0350404003001660251a84002d11855641c280f1203030890f0041c0b2842c02e007a161080f840b0840d401403c060b101c0148521885001c2c52604030104201074042d0b1000c98881c0220700180c2851380c0301c0c024081150110002e07540850784980e002ca0006131260001c645c40a003e2610300548040c540d60845911003d400440150b0401c003010740940400b0400401e400c030f42c0c1c0c3c1c001e00c3c50b10300e006076840d240c400c07045016100c0700000840c1c0c0140072082141403e80c1e030024188180c0540d40c0d05184d0030f50b41090303401003041420600820542d1500c0d0141a000e649002880b074520348070301210800400003c68116015502c94450801041d50074219070300802c000d13103000d42c0d1404100f0b001002e4503001006580302d589800b0040c02403036405030600480590140c00d1000c2a02d4450400e0700d180114011044001c0b0001004140288990417000c2119002403a1b01a01e40b41d0900f004150346040707a800000640501 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 5068478 1250 5067228 5067247
    0x3050304021302040806190e07030b010506070212060c04061704050d0309061407050309150108060601050a0203040806090102090f011b080901050405030f010903080f070207031203060915060905010c0503 89
    0x1c101c00a0031000e0b81c1c01850300b41d0310418181443e0701110315801e01170001c0b81520f8212010301a030501e10f49840b019154081c19039503120304010041c05428022140460b003003086460b0303410204040302c10f8a04551291410400c41d0200e980f2600907e4009201030030014a80108226298043d65000c0c000c1c00d154030300e61904500610030b0001c1035440507192070a0f0f0000703401d151151070190b00581c0e00c1541d40d01c1c000c41d95524000411410308842484d60300100310365400400c0c8142c110b1402d2070710030394868581d00228651f004a4001000740d004142c28000d03804c80550003048016401e4600421515080005640c002e50101c40e100c40040c0c007082010002d18080b00030005128141019400c02d0f80301c10100340740034100952029617030341d01c0309003105040d08885540d500c8152030004061902d00b80800940700d0400d03200050602e841d109407080024020740000025003a005010002180030300d0081001d0070203407003201e001c500c0402020400c1d5200340c08075580e06030000c005600e8958901c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 5069728 1250 5068478 5068489
    0x60203070b012705040b01030318030302060103020d0305070512030405160501020d030b011b060e01060f1a070501090f050303040b010603020a02030909060a050a0b0703030c0513091d030f0d060b04030305030402 92
    0x102540e495a414298440e035603440c5115560017140143c95580c507942c154a07001d0041c0b000c059990301054a15a01040081c0d40040c05a06480e81039070010f480200501c0e003516907008010004215015010400081900440182d417059000c2c1e02141d0200314404001d4000c000e090040301d0068005d480c800c2d035030601a40198181030350625041c40c2040e9050070001c040090f0100880d5821740320513265130010024026240900346207034501c0314140c60200c0e0a0108800c10f283e1810259010030340c00e0501c40c003940074054068201200c2c01030440c15142140d07ca51007202d08891071070640340082070144c400c0c0300361171100d10960021440d0003203840411044a00042c0420782c042d204440200c1c0940350400740000402c16042c545464a400b480c010b010f4a98100d603030820007206000c079001d5032244e98012000c0322480c1400149180c0c0d0442c50302c040c40c00c50620b1010728440010351040030117114008044400c21288104800342d181c081c01002c6110f24480a00007941c140045809880c12 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 5070978 1250 5069728 5069759
    0x13030212070b13081002030601020304260303070503040501050702060906011802090301060609050a0806041112010f09080406020106060203040803040608090a0c09050615090d06020d0f020301030501060f060203070b01 95
    0x10812100e2840e036403144441541d0040d00d5580c01c201683c10204000c83c810000408240c01c54002503086250a41c0004d40e0307400b440c8100c001040c9400340740f90050403c45000783e50a209101580e0b80e1b842d00d00c43c041c05030350083d5012034a5603e09000a001c440c03010a0072401020850040c0a180e46080f402c10742d000114030001c5e012641c2000503200c02e039024030500005084c5074a40140d180e140001304103070100310ba031007282160050420000011038481d0851004642203805c500800d0840c0003c13401400300803295004d403442c0411040902001d070002e4012500298001c0c445c5a4030340404a03240d004521a542c2a0303031041c4024410240510201607010090404440240782503441310000e80f11140c6c442c406050369039041c40083e0411109044542c840709103a18942103090001c03072055600341a001d45407a82c082a050380b4001d103500300d01d03426aa814415502ca5840382481030080c0454440c40d1721b006c0c03503413100017460740c008015251030039001390785210300b60310301040750320802d10 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 5072228 1250 5070978 5071009
    0x4020f0f0f041e05090609010c1b032a0b0103060501050301060305120c0a020303030a021306050403020105090f060405060c0c040509010509250302040504150c0203130909020402040b0403030804030f0302130302 92
    0x3000700215580c070701501c5111701c035540c800000d01a80c1042c264580c211b4001c034112004200d003041c41c64900044020210034166414a0301003102c42c0c5640107181d11801940440c600030000c0c0816000707004c0700c0345c12541601d000c0c0b03508000350f07640c400815080781c1940c0301c010199081140081d24040150019000e41d181d0758044e17a08080c0b071075000070709680c030489400c01007503408030300540c4401c20301d0322a501403c214104140b41c2415600080e20b075024804106100e1801540105115100d001c25100180b2001e04060703200c0603102e02c0282c490782c1032a50140102e16002c002024081e0502400c0e00400308440507008a21258900203070070240c50300c2d20586807018440010044c0c80b50710440c0e100740d010b4032921000700a5100e05000341c4040259610440d4014443c0c418040d0848114030304a96035204002042d6040e44041006802640e1142402e030030085000003e05401c0041284102e100355602076024642000c15001c0703000d48012038140e0703010303140301b8001400c00c0f544003c4800c6 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 5073478 1250 5072228 5072261
    0x9050603091203040b0a060501020109080d0c170a1a0406051f0512070c051615030b0310090501020901021005010b0702010806030a0609200103060b220f030b04020f0f0f04 75
    0x281015100c403143e1054504444618900040100c4284140700e0040680800d00c02070110300030035280d0305400d001e01e10490102d02d80d5002d41402c0d260007150402d001c6d45120f8808000c5203440700400e0014030400a0341451549034104080e02c03460f1034030590065810080c5042001c0e8050091032000140c1c01c0460030074880104250340c0c02c40c144140286c4180d0056450280403072b0079140403410110422440407079103203c400244201041700605a4013800c982c580042d28405180c0040c1c03800c411441c0c4000c80510386941c0c0c1003880b0040d0020900c01c0400c0c0c00b00d58002c0d544c0c801d44404c41d44244140c4d0301c200003c0c0314000056200b01c04464010f9402803c80300c0e5200540ca900c0b003202c0c08400102d450034003d000c6000140220f00c540d59621009080c1049207a1605c00307005218851032145543d01d14034084001d1414042c0c403000c901400407012070390b071026100d01c0c01841d003140907a403d03486020300c1d458885152404022a80c611803000e0000d08003444803e0610019000b03850b030841200 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 5074728 1250 5073478 5073493
    0x307050c03070c121103030c10022b060602010b03030c0a020603072106060801080309010210050403020a05030301060206090c0402040b090d11060a0306091103070207060810030b01060206180c010905060309 90
    0x1201020050b01500f040c40c0700c02e40044c000d140c1074030050842d44a80340643c00074000c01401c0080861000c00300d00301c5013005603860051200f55000b840b00c0ca2907039010142ca420b03000c0c8098035039500c10020b558154008011010103403040558900401da0b1540c169445017000c0401410200085c5810041da420040000c0032000c42c0d082c1d4410650903540040c0340d4a1104202c0c01754050b42c1d1500414032100654984444074000035154100b1020a002c0141c8400104040510821100ba030164108080e65142e503100c80b8020340340d05040e81d000d00c9501c141001d0100310315041c8200c07001c03a00c040c58403900c0c1030022024400d103d029800d003038425414640190f04203483d03013402040500420f5600090040c10702c200c1070100c82c150001d0613540c40c01401003108d015000074070482138900c2030801416560380d04034010f10742201034000402110043c0000901c3c1070f0000b0341613000700c401034030380021100100045503482080101c05400200d032200c00704003508080300110741144401042d911131 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 5075978 1250 5074728 5074733
    0x6020a0905130902010f0305010614030c09060a1d010207050d0b070903061505040510030807080d0b19140306070206070f0201020403050a0506010f090e06060103020307030e0d05090102010606030506060307050c0307 94
    0x124000c2886942010785070b410300302c11582d06c078080345183c40741818100318550500340003c01100381006c100c06605000030120f8400d6036010140d80c0d2300000180140e40c6ca20f8121303001400320380c04d8174210b03110403d00ea1004203c1c0d0700104400e0140d0b6009808104528110340f40c0b1866044003501c0c220910207451008404604035000d0840c0c54410013103a14099071402040c0822600000c207041c6071003440300c4040c40010301d904112440c0a800c6401c040e00c48651091420081485000c00c1e68032000c94005101d07802400c0b00700300e040300c3c130347c54045074008100d205142d154403080b2101d4005030044c100040c4072a0040341c0120400720507100041c1415100e60f200d0703150100c02d800980f615800710004010a8030006c40810180c00c901c10b052003800000303da110b6645034050075a506050f0007000190b4200c0c0f0030346c40202002179060454040c00e52a5002414640c00030002c54015401c25501241c26406402818051840034101516682d11150101c901360000700d03000000307000c20402c4002 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 5077228 1250 5075978 5075989
    0x10e030706050316030b0f01110312040b04020a0501030e07170a060905030c16080604020103110c0303040303060504050709030f0f05010207050303070e211506030106050a090506030c0901030f06020a0905 89
    0x16215540b6440c2d6a401c00d101030810050410304502c00b01401c2c030110402c15140c02c42170b8060711900b82450752001c41e07160201402c40c00340091551041440d4010070062003110380146000d540240c80c508001c0e9100d400440179240500c40c2100070783c0c000b0a00300030400501c420203030b007184481c00b41d422008580e41d5000541d0344014040d02d5580c00070071041d0f1060ba003404090301420010b40c0015006151031011070f22203000900180c18590349508038802c58800340200c0d1030350640e07101900c2d40c91a062030060b00504141c000c05000d10f1030000042c100600818410b01502d403c4101010514113a60700c00300c19404d412011113855400340a0b22000a5007080a10f016010755160140c443e06e00c0b03030511440401204002c482200100c000740540344002c14a404080a2a407001c4140e64545e40401c8c00341c400c0b0740c020740c2c022250349800195208264801ba000e07031000c81c10b80c0d61012001c42005aa0182804040c0c5440c5805580b0300020b5016401864602c0035402c000b000e05a44070001070 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 5078478 1250 5077228 5077243
    0x604060801150503060f07090306020904060f030609030f080c16021201020a090e090d050d0c0306080d090501030b030309010215130f0804050117100501050702060d020d020c0706170c0702010e03 85
    0x1228042c0d0340814000c6113014060180c0c8189405408281d511b88a8402841d032240b40c031001d00b58a50000c0d0105598566800c418042d1613030500d1007007540d41da80360640041548403019000a8414501030109600c203e140e6401140004481c0b0f040500b0052000044004004226408a5144100c04000d08d0a0018040e5500d840e00d541e40f840b8604107200740c201d0340003012059983c0041030f02814042e0800103442c001c02d408400055401c9410074160006d00c0b443d04880c01c03030f10034074203402d90f080c0d40040d0f4642500c100fa603085c424254031034245a41c82c01303203000d841c3c0581c0055501021254007040c4480c0e10484004100c00d0000d4546c5a0324032550020b00242c3d107100c0e00203007c0c402541c105900c0c005138500c010210b01c41d0310b032140d4200d44150060007407504120b00042c3c008255551a4151000c1710b145541c00c550390b045c1d01800500a40c0001d0300c16a05029445000038510b008001a0504807030300c40b0007040726524988a015150f00c5448105d050008a5281a256481c20820748 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 5079728 1250 5078478 5078501
    0x103060b030f03031311010513030b06031e0706030c09091104140303030403020d0e030307140307020a0501051608090406030b09010905010501050d020105040306090302030421020411040509040b0604060801 90
    0xa00100c40d030060500301802910308140c03561081042c0400750301d2200f004080a0f400400c5683d072104c9041c01201c4078800d82c01c000b031a542c036550002c41408151007109000d00803c50480c1d15045147c9121500f0940c4a2032103002034101050400205010750054015005103140400310b69484841e030400305da240c20800681b00001080c240450704c881130281014083c1200154214a4240d03002035032683c0c1c8508a0080140d0200e89290b1920200305950b5056070201c1c038000001741c1c0340d030010740c2da80108200764810550442d0018255006c0c10032201c1c01650004091701c03031801c03501c418090341e21100e19250001c1d0740e200000045008005030034003494100001240d484068100140ae440701030300158071800325680070348010307a008401c4504803a031000e80490a002541400da0440c09664803200d0200a509802003a0002c400121443c0314401c490401201407800c0450f03a05c0e0045001d0660050b04580206001c038021104041c0d10050003000030403102c2e11551000c0c00e483ea9031086 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 5080978 1250 5079728 5079731
    0xa020d020705030a0807020c011b020d021207031a0a02030103080d05040206120403030203040606170a0618170c100b060409020702030a0804090605030709050402010804030804051203070f02010e06010f050105160b010306 96
    0x180022241c7c107010004044c482480d004070030b503241d165180107403204000d0091166458402d07440464807004044075601064000b40c2e00840c0d0b69040180c101c03a41c0c1060425000c40c402e00050081c8414030070380741600e410003101030808000805600080602034401d0307901074014005960403501c500c102d540b0952003580d01503260f0a092134450296902c0350802514440400350541031a50000b40c3c40c0c060704c2d003001021038440c10a90019074524840e1001a014182a1079802000030018004020821020302107500f441c51a4040c0011550340842456100b40100020071402e0703a02c1d0064511980010150342c254490703503a801d8515803080c0d2145075426111b00b4108185e18050203044c006141301c02003403099141550000303000000c01071008003130018940205091040400a24080f920740d907034003035a82e080c0604007400c3c0c0103491400400540c07d00300810400c0c07101158a5048403151001120b80d03500b0140151000e820103055119688003520700034002c0f51751028850300a5024aa0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 5082228 1250 5080978 5080981
    0x3020a06020316080603010b100311040504020403050304080609010b030601120201021c08010602010b0102030309060601050f040b0a0e0406060201150e0712020f070303060f18021c140f0105180a020d020705030a08 93
    0x10f0107002a080181510311070b0b49030500206650b158040e07030340811002d074500040e0070b00c0c541d0150101d034041c0383c0000360024800f01c1d0100030414008000c00607a110a81200c45541c1c079140258283c0b1015038005401d500071000400c90000721040c032000c40c601c1401525440311081d101041c9154a640440000800902c0100070068084c8119250070f8003c3c8046c5203141351800c4003d0341c40001070403103410824002200a0441c8004050303c0190202042d000d50704c02001000a00304c0208044152180346040800243d4a00500c21101d0901e502c81220381090710381401e5211a501c001e0011062042c1080b0300807007402244000d0042a0502404c2e58680419003401400c03074070300350400e80c51260300e6401401072045220045080c0c81b1551030150707846d4540041c1001d409090844505180c0c10600b100c50740c403102c0c1c1c003a00d2040e000c0100300e40c04e1780e90341c10030000c08032054005060742e00600d0000c2900c902e01c40d0000d0444c945440d1026181081d1944e44914541c8219007a40000f403204c030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 5083478 1250 5082228 5082271
    0x70302010b010809010e0c10020a02090703021e030601021c030e01110d060905010e0c130504020a1e05040b07030305060409080319050105010206040201050d0b040f0e0f0c100207030b0403020a060203 87
    0x40f403681154a0100070081104400c5c2d02c41c1c0d6400350038800700e00c50500c0b100080d2220b84200640f42402d80e003e080740b0100e0400750000780c06500402010080201e00780503500c824800041968400c0764140e00030710307003a04076851165819011418840070103032111401401d0080c01d0041c1004420319041103a502d41110345107408a5a2035001900464201001042440702500c1c0040d0401c910310912992640d0b04814601014255030109410500110f429001640c000115802000c00d482003400c0ca0b240c1900c0c1203550744100d000b410180300044c040040400d110354800b95000001401c001202c44240d15010b401c0c1d0411100e1005010840040e4010290705000d002e0051400b8001020036081960000e0500c0c000c80394850481035035001f03a400f855a8a8001c0120550f5002041108a1005880c642c40300003d40e520549071098544101d40d03418203440c01001080b903940502000380c15943c500c0d0081c032001d031080c0c0441c45554130f4800802c89d00d100030350052040c404065212100384 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 5084728 1250 5083478 5083487
    0x3060a0902090f07050c0d0503010303030b0406060206070507080403050613200307030b040809040c0306060201060f12080c0a080d0207020a051c230a05060105030105060604030c1415070302010b01 86
    0x50610544038101840d150040c0c649542407a00540902d8031010a03a075041800c41d0940602c8143c05800c3c495100034120b1179411600a506030b0f8020f9809001a4111000380420f59400e4410300d40140c0c440303800984518402d10103885070f0b40c4608190742c5025a2510340a10b413f600f80d412080c01020121028208040956020301002146113090716500b8608002a251380c0507201c0078102c0d01d45240001d0030400d03124112400150010420010001070090050040180f40610b40c007640c46c010b030204514050701d08017000c65507000000e51403c107403555030340c00a81110b581f481e003601c42c050400000603407450180140c100440001a21090b81e4010088044820707030055000f600c038007480300f0040e141500998600c5070040062071000184002d0140308020b80580c481c06e43c00345119290800501060032030485d4411402402161038050410215100c0c500c001044014440307410041e090000b10350200d03441004041c441d20031001c00f035800b603687c8455802c4005035500c014000b60f540c1c01 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 5085978 1250 5084728 5084731
    0x20c0304080609060709080d0912020103060806100303091e03020d02010e060409020903060c0c0d030905070503030706090b01050102030903071206061a0a0908011503020f0f0301060609060905010507030e0108040f020319020306 99
    0xf4000100b840600c2040b02402c49c992030300842c40c203105600e82280559010743c002100078900d00b0122082840c1c03046100980c0044c50000303c000496112002a004104d0580c02112403080455103111a207180d00304a40c0200e460412814800d1010100220381e0b5544007400c004c000d246030250b50b170b030000c1c1c0406090410081180b0480081840300e1040744a0010b5080c4100303915040000309850113052076450241c3c19844641d00d444001000000c00c480c81e0880203000d4800c1c0b41c810380c1d598a071001a601c07405180200ca8140d44110010018a0941508503625a000748030000c0c001c0e407600c07c00106c0301c02e44c14601c00d04103000103c100042d1750103c0040c000302030703210080145100710b1201d609480c0e001d00c400ba10442c464040c0c012640d5038120016100301005000300000340d9500b6000d00b031a83c0c01c2c41081d000c00e4021310b0018265005004890007113925640d500740318880940152100d00001d00b007580c0900c0340301d4001c03005840030450b061346003407102035403e844070580c810503140032070 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 5087228 1250 5085978 5085989
    0x80d0504030803040209060301060504020a0f02010f05070f120b060315010f0306030c091104090518070803030105090a050705070512030603070f0e0c03040203030d15050f060705060a020c0304080609060709 90
    0x4104030070004240c0b000156a08503604582c80c81c100d445d41c500190151030607030083c0b075100d480042d01c0035440707410000c400c09001e09600240220f000c4924001c00b181c4c81203501c41c01040301141c2c484e5070580b00d400e44600d21400d82100041402072071002c140380f50030803203003401860320015510f00c042d030700070441100c001103919050003018155031b00c000301d0b03104070320510600c01e45075480700ea034007040f11055030060110103000b08160700d0400d002c00d43ea0f50300310040c9003890080100100384842d012003128182c82014180310b80544403540424000c001c01014041000300600000c3c0003d5001e1000000481c60b43c030100c0c0d10390804404040c2410311951218160000903041040f005808803003c0e6070002034101490b469036298004682144103141410f11114500315206810248042415041d10310036103900c943c059214081c48150700c80c0003006450355004d440000d50b500700301c0d001041400207050959041c19600c14942d85820429501c4501e190000760801200b0780e40300801000819 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 5088478 1250 5087228 5087237
    0x160e01050405160c02100309020d06050f0907030b0705090a05061201030c210813050a0305010c020c04050f060904050309040e01020301090c0207030f060203060a03080d0e0c010806030717010e07080601080d 90
    0x9203481e10150030b524181134003e000d92800c0290406107402980000000c0790090202050300b172207450300d80c005000894100c0520303c0382c0804200312480000380d41c0f095075401581d129240d210004142d81c0c075001501982d40c00103125401003030320303103841e005030000706000d405501540d41589841018000203401145020040c0c00c0785c0d2648403104c56180900701c0d04140100c0e80d501c194030818007181d0941c3c2105801a00c18035000040000562142e02100c00c0c0e0340c20b4405590100007040181c2d101a43c401c0c0c140781c2c0040101c0c0103490500600754009200b0b0301141e28202512001c9000c0d194015500803140e507011004101c1710242d800356111507c180e00c00f4080d401c1c15551800500710100001910703542e4003100059050321115202d6008e035400c10030710fa403241080700600020380701000d0108568001c0c446480300c0c40d40035255490090310001e0242007000c0c149407031484a201c94141030790326503480e0700c08003140e9401400000041d1202401a001c10747c10514000e16200010f28038a0401 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 5089728 1250 5088478 5088511
    0xc0905060a06210606050c01050106030b09011404060503060a09060b1f0809030403050714040b04140109020d090c08010c0f02030a05030612010e100b040b040b0d02090702160e01050405 81
    0x756280402503060b035110303090046141082d10201800c9084803105500a5482c181021032115003120140039104565002400603030b880c0c61045050301d2414451940090040b0014485650030000300c0da0b80060140001494680e5000020b241020982d461030050340d86040310014802103000c1c21205110130b441d495144c42059900309600300361043c0d42c600b00100348010810340b0101b4021140250780100403540c1460f200d4603000c6841400045c1c81c0d100d1460b00038981c0c12810107019205041c208103030815140c1c0e182c07940c0c031070103503102120140c0416525240d000c001a1a88211409000840d000180010a082c0050041090141c1d204c0655200340194201507a00104407580702c10107442880c4661141e01d100d9014001e6507000070083c1c0030311000c484105500d9804560400012a014070150426030180811078411001c501d41001402100c45c0150420303020294204241c2e10444000054264540f0000b00043d003040c1244020040104850f16041c02401d070040c10090790141c07030 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 5090978 1250 5089728 5089741
    0x3060c07060c020a0b0c040906060e01020a0204020c07030b011701060b0c030301030210090306020a0e09070302040f0b071703010303050405130b09070c03051e0403140307020303070809030c06040902070c0905 91
    0x540180003009021a40303405041459501c01c1c4404402d0960080300d8036a1400d01c80032000c62074109006580a083c604000060264400c0880c01c0e081074040e000f80124050303d4003804003940c008000380401d0f1160b0070002001940b44c3c003059000346040f015252403000003480260a4400b154003083c99483e0500443c0290b07000070003102d0451f64120b80e401c2c0044000d5109480720740c5982d001410360791022580c44600b68101100c14148030044420101513581ca49040d03040b0300460080300c600d01c402c04070034809600340e43d005201160003811002c0300450350b8400d1007400c0d482608210009400800c00f0003241c105440040e00c810f00e00307203060001818000100c3c0c0d2110b4014480c10801c04180c44440501d4000c4046400c001c004040e444940c103680010302a0769802407100302c405842000207040c41c240c0c04410345192946c01405540380c44c1060b1241c03901d80d0080a600d540c107000300004200d659903803d00030402443e02200250719900f00e4184080d507a40300358001c0c2041400d21080000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 5092228 1250 5090978 5091001
    0x60703050c07050415120501060b03070810051f08090a020604030c0602011103040807030e0103091202070e010503030c0c12030904060909030813030e0103020c01090b0f0906070e030a1e06050f150306 87
    0x6460f1b08080c034060402050505502414481d880500d00e428000300b80f018550748000400e110381e030020903088113540c5d20760030b1041046032010048054108000b0405119110b019616045503d90b8101c07004440780f2340005069070310039801200d0105410398200302454080c042e0a03200c080c003030103050031441c161302c0c0c8410324424080b00808020804007051000e038020780c8500049034103d0103a0003601440c4c100607690b41100e001c1c91142d411903600004452400004540c0d00e5a10702003c3c0003a80000014800d00d6041883c04a4180c082400b02c401c0329140da1007900c00a010030f0802040d064403a040140842202611040005080c0305e06500801e41100b001154038100303180c010780ea240582034017401040060402800e01281c0c0007488021080040d00a0003880180185c5401c1d0315103250940704030541d8214941c02d500842429004116000c20fa5001c0c030814500b40c440414a956410f030403a00d040360015400c9040d070051129904548a440c02e0264040c0c0042c80c0704e0a21104258 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 5093478 1250 5092228 5092271
    0x6050403020102120a0c2004060801090c170307060509031c02090a03020f01050705030304060603030206060901030b040209060406030506070f03060812161106030a090201080604140f070201020405060703050c070504 94
    0x1404ca140000b00308a04910691103003c489420007000141074034112907150040c903066002c60f105c0c03410f1640204100f44180f0800080c6035000d02a036541c20329110110651300d00e0800ea40085010138014400480c06038000c507407040060330040c45e6580c0c200c00a8010045462000460440c414080702c10039442d42c8807030100713903a011180720341441c48110040340d10740701e02e6000134054040441070104000d5980c0110058900c20703025101e0956540040c03218131030342440041c1c1000702040c0070501604102201a404c06400b90012502030740329124075142507419510b050005813400b1315000c41c640e1620441c0054820721300900a03e000d4514084e402d40621545a400a070020b80f010041280e003551552903120043d1526441cae14011103550010308009400340e01240d007400c0003843d1454203100b041c148100c14054205c150f110a0500044948000c000e88250740d400c004c045100d603075000150803420300c02c0e5203c81e034680305014114100034440d0300c42401103007400c00c00480030f00c02e00d06aa = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 5094728 1250 5093478 5093503
    0x40c050403230f030703090e150307031719020c031005010f09050a060302090415050f0f040b040c08070b070512030105030309060f090a09050108010b010206090c040207031107120c06050403020102 86
    0x50034142c0c007540d40541400c1e1041c98140c4103100008100e0109900121960219400c118844480e5a600c40a124000c414a41c0c01681504800c10900c0002d070100301114400e201410841d043c03503150f01c075118010f42e040140d200503920080c80c44040d854100b0100c3c281001a40c03085c0069450121480000249406001c847c00d8890700060a855180e9100380c004540007000f54a0505060030030329000241944810102400e02c4001440d080780c1d040d10500400d0f002696004c1d59545031680304e110540035004407070840c4060000500d03100100507103009401c2010f04181d481081d4940f891074120300806d0190b540034140010015990080103494002c801641c50b02e80c0e611203516900010700c15241d41d5a40280c1503280442c0300040c0c1c0d403005060f1500c0e00004c0252954a100582c0d448408582e07600c684e5000d610040258145a006018042d00c28102a80c0382c60358050301c1801d0100c583c018819210503102202c00f0b0241c0588803d00070441410710a24003401e50300000c0d187d044c210640c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 5095978 1250 5094728 5094773
    0x92003060a1109060301150f0302270f03010501060806030c010221090105071406150d020a090e0717030c06010509070206010303030903050d0504120e0f0603040209060a0e070206010302040c050403 86
    0x90020904241107070700001c2c0080c104c580d42d40c1c480c918010900c600c808a080014083c0210904090281c4225900d4801101c3c5410200361520f80d070500b550210064a50008603003001c01040f910240a000e001e8141c1d80c440d03060070b1a11505142c601803040d8022411580203d04010301501d140c048504504c24511a45694550340c400503150341c855440020211204500c0d2203980c000081000c41c01180511f01d105c410801c8841000483c0c0f0281102035402030305040108001c44036980203885143e0340d4000d4544151790f4001188100703c080c15021100d81002514041d0b84800340401405000c0031640c603880c6091040e4025a14181400020141540c810901d801d150241040d120f018030609000d01091405140c020704a19004d441040401c2050b240f16681d454048407205c4441009004642180d4468080044255001d0f00d400d4100c84291404110130400500b0540f04411940080c4103550ad180705000c11220100d2980b02040401d20090001900c412145006228100320 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 5097228 1250 5095978 5095991
    0x402030403020c030708060402010e06041404050403020708070f050909030403030203040b070206040306060b0a030507020d02030a0318020316170102030c0d090303110a021005010e01050d0311010603080d092003060a 94
    0x8041e854140798120b07813503051107003600c000b036807040c00165584114401e0b41d424a40c817000d00240728071400740f0b0190342c0c000101c402d60314140341465480154014007a1049030360440d0345440ca50f00b04441c9810180d05d121f1005814800d030304041d400319400c8580302c8000d41c501407030342c2c41c025124011800b40c181100000075030a015552040140c41c00b03550004401c000c3c40d5580c610070032440d40413005c1c0102190900d00014100c80c00455405c40340c040c181c0107076103840b400030800c400030958a48080481010b0140c80703000f6840030041e0406a1240322f000c004403a042c030b00803040d07030300c900e0041c450a2f81c0100300b0401300061030f40580d24417400283e0302186500091409030050111800c1a00ca0350501248200701140e000a0490070078201d81c10800c140e0341c0316082c401d8000703424007849130091280c1d07402d880042c0c8211030819143c02c1900000407035540ba641c40761820b9108210034103036640c07204219000c0c0481850804400b600c0907001c1d01600c040a40803e444400c01440d035a40d1940d900c0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 5098478 1250 5097228 5097233
    0x50901030b100312030b0f100f0e01090306020d0203060a0806010302060d02030612010c08060a0905040b04030c08040e040302030a0822120905030f01020705010608061306020d0605030118200f04020304 88
    0x41c802c0300a550b00040850011041c84001002001c4101465200d016001100440342c206202c2818078000c090351403544910740041e003514110010441d4604000007074030000041059840540040b00510202503034905101040201c11310413500002c1440e0000d200400c01a40c84100306c1d601d840c000e10000d80c580c3d44520000300c1e0000401d02611b229400c0900d410400c40c2d010110074410740e02203820311419500c0b414120111601107400410120351840403401003400b6010680301c0c030748104000c610f840d4542100341d5070000e042c2c0e0214096400416818280c50300241c006911440400d0f250b44e07030059420a040da082c4c070b4401c014010310040440c0110342c030f20440078480030300005801c450301e4040740740d0414001e42c000c0c0d0703094501d07518015010031320310b00c042901070043d00e0000900c10046400c2c0c888400961202c02031803c1255a1880024661420b0041d54103280340b40c203011742c2200300c1e4204240d07800043c06140304080580c165664180d41e4084114140c501c0c1a074005031a0b543c0e52 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 5099728 1250 5098478 5098501
    0xa050a0c0204060e090717030a0509060c03041e08100e0d0c0206041505030405070b03130605090a02090403020a0501060803030105010c080903190f0507050904080304120909060b1b0304050901030b 86
    0x80d00300c110304c410131500b00062441c00169800c02c9550300b01020085080311103c50b0744a01465000100144003005040e0716850924003510014a107402907900e465662201440c0d10309001c0000c41c148958103500b0040c145091240310002c08000304140040704240f18095229544a4114410b006080c01010195203551003503c0240428411001c002c0c0001302018000d41c02c201c408403554842c2c100003103089580081074a0145240c08040b00c80c103203942c2c0d11000a000002c0908143d4860b11000e6005643c0f0400e07072500450103234000c3c0500f0491401c200c1e0940d00305030031074107266200b08010031030399a015031f840c0c11581e0800c13002502c0d0740c3e007000080d0400d008801149600c0c924104c04a0601c0a9041680100382c4294100c40301c0558440034032481180480d00640b03289800e000190101d501150241c504000d1403074582c9546071148505da04a9400d41c02000d403025010400d150510344030103060b01040708000013141003514010010b21580014080200301e0004080440c0c80361988 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 5100978 1250 5099728 5099741
    0xd09031209080106080106080705060909060105030a0e030301060c0b0901050103020906040903170a15061d060d020705060a0c0906020705091501050f0f070201032702010302090d1407030b010b0a050a0c0204 90
    0x107100a04c015580c4180c0700d4040c1400740603000341800b0700d020000d59072418070100e07070080d0005000c22001d0340c3c442c0c00640c1d040c0c20003040e844229864010100e0301c000c083c07005502a1049446048607412a0705000000e031000404040c09607150200602c00b40c1d40d00344c0f580d079012004640104003000d6600d0129164052001c0b8441901e800c030090141c030403050340015904081004400d0b0150399038200869000c49a0081010305c542408890380540c10141c000f48801d8650b05005413510300300d65100b5180500444003010820758802100d00c0c0107505c512000d004081520003070180d41e007000d0000d100c0d2000640210f11a110034104100b4030303405182520000b004011503103498180c04810300c02c50368801c01080380000c6c40d02254500070003002448418204018010600d501060ba0041d4025886200c030103030310920b00c903014400545c002050304945141074001d0540649189041411100c1c181c0144c0c010f07240500031000c1041e804416034506810782e00d498a80c40445002050003003e4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 5102228 1250 5100978 5100989
    0xa050703110a03020a1514040b0a0e1f0e04181113110a02010507090e07050702040906020912030405040501060305040b0a050c070206030103050303160504080705060304060b04050708070e030d09031209 88
    0x85d0007a0004404c814445c082c60740d01041c0e2650403495035504401c00092041d80034030054058148604401144a284d044d2100b807000380501041c10700210701407040701a104003820001e07401248440007814540106009405041e2011003505030f5580c0c1c1c04e0402022128081c0600717034045000c020907005401204a0000c5450259500c07802180003e0181000700d07031050206215140c00165102c11250031031040840366100e900f405203950811000e084102010340d901d6409008070714440d5210780f4a1403000f015070005554583c03502d0705100a070390301644a00149450a003c100110342c1c07040391194002c007402c00005d8690f4680540b0401c0c1d004240010707401c000003000100400c400080214050b441000c81494600c4262004590324461401064201e4104050401107400c10a0103190414440c1001068010540c0d0105003128402c07210f10001034250000d1282e0190481c03001c1c860386a0550203008649004d0034058034041e000c0c03000900c10140030382d810b03040b98401c0100101030f04 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 5103478 1250 5102228 5102239
    0x40b03040311010c0207050114031506040609030501061202060403020909030706020307050301262d010f0203100608010e0601110a0606080606030f0109150e0a0503040b0d050105030a050703110a0302 87
    0x10036060061021094102030072940d0320380f0841c2c1180c5400024200e04a8005a4500440c038411461180441d040504056940743c2c440317180c403000e90781e894058006030020b50b48100402e85141042401e407a1031f50700030341c882e10055903c800984c0300d000c202d4095940550b828140d40e00da00d03101c0c80c44c0d44141035000d0000c3d40301105024807142e00400031030407110005862601c024003000c169000c0c035180d04580450b9405042030300040c0c1002c0c4a140001c0807008688051107142500850a40d0808884807924540c004108425000c5140010001d009035107482149581002c1038205900c2001c0d01180c1841803000030030264800070000c1c0f140495000c03401f80105660317000025600d850540b500da100e4080c80749601d804d240144114070542d80c0001c40d00d00c1080781b610011008194000740c41c83c090141c7c14001c0080383c1e0800007080140001c10b8403e588250541031101101e0040c0c001d2807181d08585030303810106400003161400d481e080001d20903e508078000261814080340d01c02500f29 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 5104728 1250 5103478 5103481
    0x62208030315040605040e0a060f1107051606020307050c010302070804030206070506010f05150304020d08090303040e07081302060304110105041503020711090f01030b09030d050a0911030102030c1b03040b03 91
    0x41002c94815240e08152824861030f51120708100583d01401040841a8011142c502c0810001e812a99042856080006441c00903000f0300020790b00c0084146c030396502105083d5100c1d0700140404005107014806507040094964403d03071a100d404146a04042c0c01241e16814003480c40125402594002e2400303076180c00500c2d1403501d07043e09201d140c46542502c800000c079400c16442600e81c0031060001c03180f0350b65031076003080041c2807440400d840d820000d1044542a4030100001e001401c108203415440c0e18028200900110005268842141d1140c8460300180c90300002c1c2c80e0060f030312444402d1101c042c280121664041c0b42d00001042e03100e14071900911390154000c200060142c140142000700880a00c00400f8090f40d4a41846800b540100041101384400c60b40002c0c0d46400e41c5d18001c00103d2030415108182d03842045c03240c1e100c48a00400000151002c003046041e0b00950544c40c00102488460189100b42d0207401c0d002900c100c1144404c0c400c560140003211007107902d9 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 5105978 1250 5104728 5104741
    0x309090603060c030e010c090b07050c09100317120f06150d0f110c150c07060212070e100f030e0a0204050901090b13080d0e010906060303020606100504050622080303 73
    0x1a0600f8052007010a1401c01d2807100c510040c0a41c424642d565244c504c0202d241111075801644415030a0b590750044590005041d501c084446010700c45d03013540c0c00d280508501788503500c50b081c8100100550005c01a079643e1001c0100380c140c1c0045040102c0c0c200340d4a135004688004240314012100036000103004000d4070103a405481038035060041001145034604030980e07541300d059850b80065010441101a0101d81031070240e000e050b05038060f003400c100350ba407070b004da070400500400209105800c200b10254441c0486442a004070b500c8c1a14451a5201a150303c1c000308050701003641710b01c2c01c4150f104c810000d0780f40e9264050420800d0b498103050440c000d200040b0212030b100c0c94800412424040020425a095086030a8515001854640c20b009103414001524507540b150350300c00c080382c610312440000354020740142c6594580001048284201c209401d0180407061005009540380c1e03106984e22800c0d909100c4912240040061201c5001644680350912001041020 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 5107228 1250 5105978 5105981
    0x21906020309070506070c0506031009090c03020f06030717100e09010e060c1306030b0d050105070806090601050a14070212070b0c0d0e010f12020906070f05060105030a02060301030f030909060306 86
    0x401c0c0020b2040e1064207481d9410002c00340b0030407a014250001619040c455858034000454000d41d030050780000107681c0c0e5420006a6114500c252400c0110750310400950801c2c81c0d40140001040350820b1445c5040c5801902c210000032030542c2c003019100000b00e80000318442c0d94058013894040b443d0700d02c0c02060030b50103007139400c203001d5290080402294150011100b9901120304101c20130030524140300b42100117059082c125903104411003540c2010800c28030071240261110340e1001560315202c4140100501e000d4640380c10800c0420a02c00c2291b0301c156800c00c0130b210003054580c0c2d00901c0c0001a80640a40000c1d00e00e4040c1e00800104880320100400078107031184c040e00e44d41c0041200c150b40d0003034180031950101c0e541441942c02c00e031250300f10808402c0115001070404682501191550b040704038112508020a83c00300c00b8000304028040c0105000c40080005400e40e501241030380c041131000a0a440c50140342a0405000c1d81001000c1c01c030801040100c1e96130390400c0ba0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 5108478 1250 5107228 5107231
    0x402090312190903050703031101110a02010b0108060603060303041208090303190207060201050103030f080702070b031e010e04030e01050d02040302030114010312031a13020408010c090305100501030b07030902010219060203 98
    0x10440d4040b400142e4a00740180a900c2c00c5a0f0000003030090907180d0b84054450700c03c6807406141a55039502c20700c0c5107401c1180a014114142e50000400488000015021010152459200c1c403824820000c413680e0003c1150b0550302c0103040010000507500d0022800d00400000940c18040450b80a06041010180108140340e43c0e0032150317142d6880740e0a900302c1e10300b80009800509080003414002e80901c002e01c0c2c01886910403501096aa80003032042c0307070003c1d035140451502e5144809028440d000d844c0e07001d00b041d400f81600d43c0c1840c0d40e000e082c00b000141c9080c1409000b080c0549866004c1e41550020340c1c02400070b00007000421407014501d00240412a111581c0000c044507080c42881641e041d00182040d42500c03844c1e1104008650742a12007000c02603030208070100e2146400e00032040b0042c01d85d21544c0400d800c61602600741450403074004051446c0800410200e0341e0900d0741d54005a00b401c00064a1480c1e000407802c00c00d002d24000002c14200c04102e00300100e5a000b107 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 5109728 1250 5108478 5108497
    0xd0f090b0609010b070b0f0711070602010203060a060306080a02040902010c06140106030e0c09010e0603070306060e0403140a050403020f06070b16091a0304140102090907021b010504180504020402090312 89
    0x503442c0d07a20341c540825140903c00020308004842c4001503095410041c0c030301d03003040c406c0c1090400883c085901a00e0601c1c9074000600503500032043c00b40307605040c1c0c14003000c0d2110b401c0601100c0e042c00320035642d981040e10f02901c1962102107071070079039008640f034901847d0494014451500051f0b1111001c940a100340c2000910380664011a5500428036003074200000b04681c285920f05000c0303803802c1c1000391509516000d00c7c280040015a10312a030300c004c0050400c100c6c1c0074a00790402400c90003074416508400340d0b0030002481310365808030450b802e4950440d44405019440d10109440d801603607402402691303c04203010301c7e0660381c14803280107241d56540060035522400c0d40c503100558a81801d0040b14244045030000c1c0741c481a1040000340400010b0400d600d00c40000c44002c4152540030150f08001c495200266010078544041d58003030030802d113002c0c038103040c0114004418410f5041d481c0d4803030100302150f42e540c04403004910001d040b94001c1e03007000c2c4604626804007400 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 5110978 1250 5109728 5109739
    0x11190b0307090b03090a02010c06180302010509070504050108030301180908040803090906040606020a0605060d0516090c03020a0903080c010603061a0906030a03021903090f090203150a080c01050d0f090b06 90
    0x3848050140c204c9200d0042c03c40500114416503006440da1900e100040300e00c951601c41c09061006052005440c1034000e50000c68541031031414641080d080d030300710703500550500005010710a800011241100c000c065021008001d0500f80001444000c400030500c4c003000400041d01070340000900982141100d03140c145440785010081220706512075800980c020622000c0030804651201d03620017800b41210b200d03400290b0300c003424201100d1180245090030102403024228901c5142c24111490a0461811014510280c4642d03101d10005200d114009608400761800b0340007503000790351011052004800314000d0101c036203040714003070b030040c02001c002459500d17000900007003103601174000d01208990001c200700c00312041c150940600221a40014000040400e000014050990f0040e101d062003032071007010785620b00407181720b01040002401414000b083e1220040400d003007051f40e40c461005100c02411f094151510190714058408040c4060200003d11802d03003100d0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 5112228 1250 5110978 5110997
    0x100b040308032706160504030203010204080304060f0801120b04030210061502150f0103020d02060403150203151002120319020301120203060c120c0702060d0e010f06050109030206030411190b0307 86
    0x3a840b80120516101c20f510b50000f0045000b04032400000c12800486180c141c1c9400c2d100c0e00404e003a43e002d0340c00404c19900026041000c01d5100f0002403648883d0328040c001549445020788078501e104c1c01c00b5000882c91008241014005c02450b0002e009a507800d0209669480612403c105545400344c00742c090f4089001700003844c01740c03041c4140809a440c10b42a420b64007481600c030300040017240c000701d04200100c00302d50101e0442601400c050009644c905d4001c3e1000c8144c1c4001b1035240c003a024401842d9060307a004912064a1012004119142d640d107520203450516900403000c030080c0f00100200da8000c429086140c1d45001b074040b1000703074554640d030102078170030840b607000d24504840200300e044c0074040003441c0e120300082c0300c1c0341005d0761840480101d036000c001c0340780240c3d582e100031000d80344a406140002c00342404c100e46000d1441d00810f12900c0700500042842081c3d1000c0d140c56990160403c003541c1d40b80b040c044c40240c90718410b01e507551040e43d0640c04644103d4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 5113478 1250 5112228 5112271
    0x31b030d05120c0702040b0904060501060e060a0806010305060109120302060402030f060708070509030c0a06080609060405070c060b0a0b070f0506060a15030e0a08030a0204030201080f0907030209100b04030803 92
    0x1c80306200ea180c0a802c200f640c0b08840e44515030401c5008036406070315070200e010641d9501da00540598010316000070741d540750003006403031800e1004005e03028081c1801041030351900111403560080080c24085140d9540c00c004a90f0070f00c003a0410004104001003100034141d0000b0080c0c412031003902281c40c8130400515040da1000e04031440d0780060b04032000280080c0c4108007500e0101000b5080307880c2c1c4141140040d400e26103a401c0704000948032800c011181c5800c40030513400640544040015040c1901c0c010b080380701d0305030301402c025107541d00b030341403602c40520100017000d034030b0092601e8401c00d00c0e05112820043c54180c4151044001040c01032030007102136400c0b250460170380740c40c1d6050020b00342c0143c901621a074006020794002203020803517000c02184560003d90005030360318214400942880c9000c2c0080c1e00c00d608580800c040101c000030b080068a404440c00d000c0c664401507c0b419006454000c2d40075000045000000c018091018500801d41100100b90703400340c04 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 5114728 1250 5113478 5113487
    0x40b06031005010c05030408070e22020102060105040b030309030a030e010906020106080a0212150c040503100605060d0216050d020c041407090b090f030102040b0d060b031005040b01030209031b030d 87
    0x5440c44007440410007020041580260100d40d0b0061107002a203041c01d540300040c07402c000b265486151601c0741326041041181d062555005804840f05445d2840c61705900000e6030756405001d10b5000b1551501076a5441d038041083e03801540b80103044400340c0d0403a2500030700d103004441c403035404500e00d80c001107182d038018050101603403400c02c011310143e401602004812504030a04031224050243c07124003000000c1c0923036210300c03100590300c0e0f034a518150030305103042d90441d0841c00080c5040700900c1590341c1c0c001200c601e47c00d41d400240e210b40c0c1c03044903105103412949000701684281950000f40e60380101c0d00007240034042f18100900301ea00054940c140c8422144040007548400050011041d00e0002d0075400c5405442d280d1000703e240c01283c00c80e070282e04454588080400c009500e80c0450040ba8058040801d865003181000c0c80000b991040b10301400344240d440300c3c0e003900c89902c298180d51140788014100c404c90754106401c15130400c285520140a07010b000700c4680c03410b010703 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 5115978 1250 5114728 5114731
    0x20403022e050703030f09050604050d05040f030809030c03060103030e09010b04050d0b0702010b0a09050411040207051515040204030b04050d0f021e03160c080c0109050f091801020309010b040b0603 87
    0x101010070311540c510003401c8955038041c620031001d050b500d060b100050706c40c0744900c3c00b640c0c0c0300b0002040b0764140341c00c00340c1c60101055411070401004000c18480c480c80b20800804030790703120020030b40343c4000300000b030f041c50a04c9241681501c03840000109150384405c422890490035140c03601d507640c1b1040301c04110b115a000b61a08940d0038000c0d00001100c004081c1c1d4071699620000a40c0d15142c2d000030404612980a04421501c5206210a011060f8641d142d4002c1c21101145030a0342c43e50340980b81c100940304015a260601c000815030540b2a100c1c6d00d090200420840da96074481c90700298105e0700b62030645543c81071200c0b1800f00380c006c020128843c010f580041440c8120410070400c2004441ca0b400401c0c0005c4c0562204840d02d04800301c0c5603841007200042031820f00755007900d011080c114403030410000c03000030032003500c070307010070383c00000050315008840c0e5940440407118805541c1c8030b00840d0710010030020340500c19442160704a0049600f072080c10021010022076000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 5117228 1250 5115978 5116039
    0x30c0a0e1f050c0c04050702010b0306010807060c0803040314030703020408060609041e0c09020d02040501140307050703030e0316050304140105030906070320031f09090b010e07021f02040302 84
    0x11203400e07400c801c40c0900060421800401e00b00c40300c0444003030200d400d99030281c41c0c410140c1c0d154402c07103c481c5070a01225024040c060700501055181c03c1c1e008009071034094001e00404030000c0440c040c036200306841d0b0b0034542d001d41082d81e282424031004009503ca407007410b505001d400040340d203601c0c00c458480d006903000041d007244e41c101c0012001030182d00f84000c44600c41110380015042105001506d010141e6500040c0c47d249408005451000c0c0d848400348020002c008120002d0f03040340c00d607229507806150000301920080600e5146200d1010554100c1003004000c00070801d000000b03000340c9e9005022202d154100a0064480c0d00058425051a40044e000a0305151090740b220b1a99003528041d0b452403400d80840004c1c0380c4c07041c1d8561910b00200d601c104c01409c4401002c44c0106800c481c200071880c0c10341c50704502800107000d015100403018000c12121780c820080e00d0740030342c9541d52003c00300c250810088025802407204900581500c06c84020550201840c4c05000780c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 5118478 1250 5117228 5117269
    0x80c0f030406142703010b0307090204050411070302101503020613031203060506040e0403020703080c030307020c0f091302010509030d03020c0607110a0605040201050f03090c03060a1a0906060708030c0a0e 90
    0x104074860300c00d80004407411303a039003542da071705802d5016079403c201c03102c020b00c0f1030200140c0c0e590801c003e00c02540d03180050003426002c10442440003c1d400980d5030640c1c03508000000d0300c2c403240745116005e2000c0e0751001c1c0d44904081246109110025803040403244240b2407540d10228101081d02542d4035481195803009040c40200009a2404100c0354042d210744140d52189441e90748481c2640c02210f44002c10b41d00104c01c01070200e404202c80c3c91809021604081c1c17002c00e000000d0480300008041c0c10036802c0f01c0d4000d07030441e4003c03019555110300090030784045134170402009000307402c103042d445c07090720032100031401c464001d031480000802c03588081c1c000318140791500005800081c004a0404c241003205036031100c81030000d14018070083c4041c0c50203031041c0d0101480c0010107481c42e112503180604081b0030000c2c1b400008001c0780f00342c49050141c0c2d21907000408601441001904da001e001040000300c010303201c010b20300024581c440f124241c1042e07080c06136402a07284000e0461 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 5119728 1250 5118478 5118517
    0xb03010e0712080c030409060303020f100b0a0b130302060a022404030203030106050a0203130b04150905060a0e01020a0804061806020601060503060405150415061b02060f0304080c0f03040614 84
    0x408502c0101381e140d008004480ca0544c2e60031107001114001e500981c01a040001c08c05d8a4410510002d01e00d4030118605200c02c5c00c0d0480010703608819480b4550074010f001960082510000c0b410380003e540041c500f030703117407120948040e48402c56151511003240c00c0c0052014144102c41545000d00c1c0c1680c029030443e8208070003990503501c248a1907003988403e01448080c0f4204014550140c40c612142c203880c1e80c9804d490840342607076070344200b0600034003580a0240e5201c100981d12442028a4201c0d40800d949005030700b00511660041e2456400080120303a4940004030050030f0309410042c80c0c2c03055540e000490f02d80c0802c0c000d410014004001081d03442c6044d070030254000e0081348101d103804024074001422075030308207100b102c02000d60808100c103941000d2241d82018031400d807810310360a654006001445003041086220030f01001143c10700c407110055904415580048484d04401403541590701e8010384514000038078001c1c8502c503040246010b442c1c80c81c45603901e02841 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 5120978 1250 5119728 5119733
    0x150f02030c160201091802041403010902240405060d020a0e100c030e011106070801090b0301060e060409110607030203030109050a06031a040201021f020702100c0203100b04020904050106030b03010e0712 89
    0xc4a03031055041c0e04101c0f0702c1c85c000c60394100c0d03c000e9170501c003400f400c0103a41e01d1600451540e10b422803c0010302c02c0c6d00d00004000980c03035411880c200c0c07404424132000d20040118031842503001e80e0f001590000701c0454100f1041c4801d600402c102d2406807079495540c8680010403140c8154051a4000900d8010b01e0000190044000e2021080c0c141800c20035001015101c1d403502000f140d1745c2d00040d028900421907109140304036140c54101790000e00190b410401000368000000e0a420b0045a650f40303e542402541d03a504081c8020007005540c3e82d04103802c00135030300e41082c00343d41415440c01011038219121403003035104480c6d0214116070800501044188501401402681540900c4043e03050304600e0f080b00900b50301c9030620058580100d4010300c140b1804070f010311300c1803010181503400982e8000a034401c511034102c4020030034444540c003040290081e501e4003070304107051030008943d441e0540c2143c00a44020350003000802c1c0040e0700540c1d1079255220f60a4940c00d800040e101 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 5122228 1250 5120978 5121007
    0x20a0917010902040908030703050f06280504060305030301030303050606030f0103060c02010e0601060c050601080307050613060b0301090303050f090c090112020604030b01031101080a020a020601090906090c03150f02030c 97
    0x100360900c00090b0000064020400765640030400b2601010000100141c964051050541005009200194920b01800421102a602211410180110350400c9004000c4d8030748072028200150081c03091554910307004e643d9800a00007140800e050070000790043c103005c01542d10445503011241102c8c0d1940c0c9445000303007081c90f40f2340215500c881803402c070300c00c0801c0114000d0a540d61010000f94007414020b08054043e04002e03120b4004005040105071300142c0c0326041520320402500365203840c90002d000349000507107140c041d42440c40420031305416a2005104240000501c2c00c940e8a81010700d49642c00c052070f181e03011030203400511400e1070000c84140d00502c040c0c10180b8003501c0e500d0f4810b800009034001c980c00301c1c0c0e001d0341071255640645182e804c950044010b41c1032880941d40651101d205029411501d552040c209040c001c0d550421550244c001c3c8071800040d4490604100c1e40e00b54075884800e241c24014600125074080c800c50b84a111075460f8582440501c00104c0c5 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 5123478 1250 5122228 5122259
    0x1091a07050909060402070204060f1514030402090603030d0501080102030106110c0a0b0d140408030402040b0a060207030305070201140a020606010906050901080105090402042d06060e06070f03030e03040602010b040e01020a09 99
    0x3c5c1c002c0e40c28804400140c465100d01005481c2c101107070000180b50861220642d0007981c400000c0280f0300c8696a410200b140c103a9800c40c1d8101d07169401a43c0d4080801d185005910341c8107513082c280000003400d0760043d4000c1d81070f1031899480c1845000503071040b40d9200d00300034140381c0020700b1801c06c01661110708050714003042100d001140d01ca091140ca03d105110940e41a40c800703800109000031490544100000d8180030303244807450f10701d8058041e458619911015050090005911085a10449403c0400402c00306040e895540c1c02600a541d180125245400b2461125001c1000c6000f00184c03844124165200303100d076801d220600402650161049800c251a501c0420140e25218102e40386c6e45010700c01040700c3e886040420060700c42c540d100005000700103c44081e0740d15500c0031114819000940306046040500d000c030010000d01c0600c54080c080810045289907064016503801d050031141400942d54550a441c201e21461030f5803c04206603080c00c0040b82c90401c49070 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 5124728 1250 5123478 5123491
    0x60307080a270c05030d0c0506010e0603010b04060e040c050103020c0c1504050d05031e04030209040602030718060203070302010509070b070312020403020a0e0f0703050403020c06070516060201091a07050909 91
    0xc09880c0d6203841c0b039040c620740745001c40e28844908424840d5041c00c0201070045c3c0254544803900003134030788403039072035078018042d0000710540b4030300040043d00c1c2508405403914000c1c00130408503030303282d625110955042d502203800c0c500540300060558824001c2d02c40c1c0343c4202d0090030001c098141041210890304590004900041c0400601c1d42d03200c14919075140e0044010b5996010107a0905000c03440000300b038152b5140c140001c4c009a2201924241c0c440c0c0e120b100182c5c1c98840b44400e840d031001c041d0043c81c591807405408102c05902001400401f0700c2a002840562200c406681d05d43c0c209001d40b80c2081403c3c05041c0100703120310000700302407040c03000042c64540c503600818025101ba401200701d00e8540002c0c0b0111603261080c1c65440700c480c0c6010001424103590003510b4031900e8120300c0c03040320045401000d101041c00249180f0351740c400714500385a03440001034003030b10403904240c1d20310080c40041d1403e03040b44400140309a8080da00e440c54541c8100030801c0702c46000d0b01c030 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 5125978 1250 5124728 5124761
    0x120902120601080102030106120e10020a030b030a050705030c0405060f06070c030501050108010903110c010806040e120301170d0c0b070804030306170a0605010506040506030f092a0a05060307080a 86
    0x3060326014203000c06406000d40c030001503925810610302078074003104000f246a07130624040602c0d9061f030000c00c04290300c100b40e0744003503640c07001841d04a0142c94545030071503050042282d40310400c0b100064480440300260b041d40c05e90103180b01048100c80045030382c6908030261000c20901441d103500200101482281070704040c5803640c4616007120000d03001040103a55a08051013416040645082c16407500030040c5816408480000c11300b0074007411140c01503440d980107024600d000e109641d08141c99a64103510380d81e5480081d0004200b81e034490016004080b2501482c61044550800147d00300c1c80b0550340362665007086800d4080280250201a56100041a4052940b151100f0005c0650041101c40c0032410300c40100c1e10180c0c0000d209207810003041007607450307640c07d03030340c6c0480703100310710b40555940469240c00c0c40c0703141c00403803081d00c88420817030f4815070704c040d0441c0a8801510900c203100d4072401408070032310054403010042442c000016000c084203412200303c0c2d4000c03014 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 5127228 1250 5125978 5125999
    0xe07051005160308151002100e030d020a02030304020f06040501170907030b04030507031205060a0603020906070803010605030103170304020f060904090c0603020408100b01171302060706050403020c0301090201120902 95
    0x181c02102c036800420071400140000305012480c400008100d0403080201c0e520140c0c0742141402079513898010886003142074950205003c00e010510607280e41520380d00040d540c401d084400292258011242240300b40d00407c01140c41d42007040985058030b5060712100d0425031036842c040c4490100501d180400d100340721001c030000700000c1a05008901c242caa00341c80328294600035180c900890700f005c0540e89080304000d01c9541b950114000c46809080050b039403042040811903610800401800b400d00020002503402d60103130046040f20700444003068580304060400e03413103200030348000e9070003803074a04040b0703030b92400c02d0003045000c100400001e0020030036074600032080e080d03511040201c0d502241c1000140c03000e000c1d01014464030030003000f61400510000e080ca600f07100240d80a021408002550041d600302d18400350b54008180d01d03141c2e00c5601e8104085d10003258101d0050068100851841c14140280400907034142c40e1840d00f0920b07504994000e0011b240241e0b40140c0034007 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 5128478 1250 5127228 5127247
    0xd060207020d0f03030b03010b03060106050a0203070b0f0105031e2d0d0503070f02010506030d080c040f15090501020a030e12100e0115080604030c0803180328030e07051005 76
    0xb01582940e1192407503181030090b904002e01110100b0340424002d906021a4260690b0301160250540d00d05040c070719118003840354200d203140100d41000380486031801c240a62103098215040c101e51044040714201c0640c02ca400304e44982135520b000180c1d010084040c0a20b85003a01160608a0301c026081c1d1008600303281450f009107901c0d13260200c1c0303000040c8a0700580c081035084004c00030b070000b404070341040d402080c0ea44901c0000c1c5030800101c032000c1076076031002a0450300100380824241001070f8460021408200490312004003188592000040c0c0f9400401d96040d400d4140e200c0c0c2c9035400c40c050621401d6051241d001f400390054504d0100c0d000001d11420300002440710000030380d6540c1a880c402240c01c03540007042d15034040020040081c1e840000000754950041c0c05d140c50303444505030449041d40c42c0540c400c3c0c900010403405100702c00000e001c01900c4040440300851004050300307400711260443c96100e10380201c00c0611490070f021105e40d10907072085c035001e45818040f6 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 5129728 1250 5128478 5128489
    0xe0f0603190506060f120c22050a1406090409030306050406030c09060b0f0a030903090e0109020a08010905060607030c110402030108030301060f0e090a0e100c03020901020f0a050a020d06020702 85
    0x85841c1240100103528420001c4014401c86900800582e031203880c01e200f800c03c0841c50701540003d40c0780550700000040a01945101b0713226010b10b880d1002d00c80700411f04048101d80071078000e09010314500c00c00024142488001d00549090103444146401c1d135031000d02029204021094040c9622013600180079103841c41508000c601440c02c0c083c2c458105011101541c03e1988545500401880740582c3c00803d00c0c2240c100c98014103001404071082d00c0c00b03a13004ca00643c0400341800c2100d0000800c0d0b14640c0040041c1419039035404841e03070b00c0b00c00704421180281c9032035401000910211001900594860040714000c0352141480c0c0c006100040603a030098019130a503410110040004503004a0250215210303414100340503400c200102e00141c10013001038100ca07445821269040700c003440389140c1080a1003060040403402003002d07001e50701100ea483e005109540300110071260204000d10900d034400050700c21003482d5000c010110808020980782c1d03c0d400c000078001603030781 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 5130978 1250 5129728 5129731
    0x20a0308040f05010e031606050c0709090f05010507030603120309080f0307020309090108030a0c0b06061b06100e01030203250803070c0306060506190807020c030307140f0d02030405010e0f0603 85
    0xb02403444418104400140110048100c244c001d5119601140c07401d00301203000c07019210070349803064a80089454507494220903620480416282004c04814005044d10714010f01d8080c0000b400184c88250003142200c8443c84054201988548009240d078401c0d04003001e164062801a0700b0200301ca40e40c0d5031036074016208440583e000184c00400c0d4140901070310b0044c02d20a0186081c10722019014000c140e070b503070b4001c1c46141c480000039400c2d034401080c1c9031040303507a41d001c041a00700c4010303147d03031503a0540d0700000f400801000011146160320006050b02e60143c00340c554086d0100e06102200314502042003010703001c01d0089a07140d400c10141c42100c7c041c1c840000081d14504003172045604a4110b0360003004100710101020282a03481140d00d9940d207807546a543d20201c00300d0030f118565000c0b6905020000314002404040104001c01c1881d4074141c80b4120407440b51165500780c90030240e03015800c00d2104010960240380ba40302d00c0d43c005010f0000a500320000648140e00 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 5132228 1250 5130978 5130989
    0xc04031703010302010305010605030c030403030c0908011508060603012003070309020d05060106030b011e0c080409021c0e010c120b010504090219020606030d0c0807020607020402030108030703080f0f0105010c020a030804 97
    0x80c088010815981d050052a0044c00c4600303019241d8205051529401c5c40024005824561030740c80001c00b45105045035001400700200800580c0c240c2e28101c031048800d48903500c042c0c070611001c14154034040c42114a1a4030100003005880443d410140e8140c200600a40c00d040e65a15a9005600c648841d5400944944040c11603136042440240444001c410920704204500b2241107164440381c0300400da540442c14801e04403841480d140c0b1240c031440d000840d103d030000c900c0f907080804100711035040440ba10410712940300c0c40d150907822201e10344145030000758800010400020b03580e00c40c2e0000310061410303524040d03e40301c10100380c0c0d000244809403c61004c1e80c5010703050b4103015030394011208401030070a0356010040100031901541d0090704c245400101441103656800844291550141041d522980d44250b00d03a200e812595013075020541800000307600111054240b44503445041100c0d03020303401c21004580305400305400300c1e040444500044003280100c0058001080b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 5133478 1250 5132228 5132273
    0x303030103140105070f050301050904140102040b070c1a040b0f04030204051302030d020601030210050a020703050a0803040201020618030703031a09090c0f0103050907050103090812010807061d090703050c0403 92
    0xc1c4080c80080c21a0001485c440030000c40e9400d00103019030020403070b811504201e070301003699251820820303c15202c07440322103055031002400140d82000c40c030207006854025000341c101c0e169100940c0f210407040056450001c00100001c2c400802140044c0565920260440c0e040c607442e540807404595003528010383c0c0d1a850328041045250800800d140c0c20040d201130412549142e0124014224500e104c505024002c50f106001501c200408002180c100040741c40b0340d01c6c903003062002d0b0341c8240d9003a4018044c02000a401c840504101588070001d03400644c90912030f84c80440c000c1186010020041c422400113080c199101c04e1542d02441c990340140c508a504501000f50480c0c60352030841c1410f0500d420000b00440c0416118212002801c000c20034401900d80880c181c03240040000010701002c00114090100040081c203491450721241d400000c442401114a5a9036005503409800000020a031503c80c2c0c0045400c441400211424030342c0760b684d5154011080e621032007078030 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 5134728 1250 5133478 5133503
    0x30902040605040209010c230319030c050a0e061602040e010e010b030a020f0904050705060f040501030605010903020d121407030201020c0c04060f1208040f09020c01060b0901020a0605060f0303030103 88
    0x529052041c1c10003080e0846045182210403000a804006000ca000c0c0910f148481c0c01e8407121244042095810304010a0380e545403c2442010080034025546400203468402000301060185088651002c03180d01c0b080600001c000422680368481c11001c0d9201c3e90300031510780180c032075005183c02958880004541072119020642c00c44115508162180e40100d810320003684842240381c0c103c5805070b40a29095646083c034500d000102c0d4001d54014400041e0091000503007030103001611001d81c3c0621480e0399403001100e0013802030101940c041c0e205484080050084030a9480c0103a450408522814100d28000c0d001d401020003680940d4000030b45030005c1c8814041001d990500301d404000503420701201512100c0c0728065158080500083e100601010405541c02094402c0360b0400d89911580d455010f50088886540198203044000c56988108015140076010690040030f02c05801d4480381c2c064a400381040b50060b210000144280d141400114081c602801e40c0b03166a = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 5135978 1250 5134728 5134733
    0x5030d020309010e0c0312090d1110090e0106020604080a08060102100606030603020f040203091e0102070506070309030f02010c080c0d0609020307050304030801080a0f1101020f06010e010510021504030318050105070309 96
    0x1780b44003060854071079042020b1080581c107880082c0c500164083c1c0c1d148403a00101c0c40c008000340300d000c0ea050f42c807600010f0640c146986c01a2482c0989aa41c01c008040c0e90340d41005998a03442910014208ac038180720300380600d0310805c4120b81c0003105104032800450829015401c4809540140000946a14040c001d60400341030f12080103034251421451440c044800390740b079042c40004030404010140d030080e10ac00094041e250500d800c0780c00c0c1c07402410a050068024100d09808030003040c2d407010395241041c0180b08804085201e9280c2206079070740c07000540c92641c0f02d0700241d5020341d43d401004c103c0c14090700c042d6104107200d0719116524182824064401d4105070f100300c00560040101900181035010701070a02a804050100417406910060381000c103002c41c200752511600d000025a01c0b040c00c0c4543c12180c0c02d0b1400b000c0300010300800c1340c440c1581481d0070800030070b000226001921030746c050301030030340c80d030801c4d40528110b59612400d407141038500e0070000341c84040c5c0d20705 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 5137228 1250 5135978 5135983
    0xd05030c0c0604030515070221030601080108010c0f1b06090503030f011208070803060411031003060f0209030c09090109050706050d0f0203070804060f060f260a0b011205030d020309010e 82
    0x3840032540103040034135550f034182da00c04580144d0020041d040002c64940b074000c00c1404100d16408031010758a0000080c994110b80044031154001803940c00005000c0318184554208810181d8951050742003c46095036912725000104840b018504406004940a44241d0445910076030145a50742840302103603252a006810075200402b4901d494000a90307500200d460075a40984095280d0b5030303500000f4000c05001c2420043c2d46000020801120785a07416001645c1c0300e000c0030040b48041d1480d810480c06417004440e003651242c4c05441091400b1010716904c186030000100d04400c1a40c5d8603810301180d60f01040c0410000324861408034118001ca0b00b40e4010300a0450441c0b40003180200305a402404c06412503680c0c2004150324000d50f0420000b60420942d09800301303940381034080000720303a1a00c059900e6a042207917401114041444c043c49a044030800c3c010380d00309079015511b1548134604441c548010446d0349031072111800958811a5484c4c000669410024402030 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 5138478 1250 5137228 5137243
    0x70305060601111c0203070206070602030a060b190c02040209060a0801030506010806100b07050a0209010810050609010e040201050f04091404050634090803040b040503190203030304030302180d05030c 88
    0x107040c485490a04040d4010009441c03604080400c4c0040c0c02d2442c2c001c0582c11031046100c040e400c0755001595a05100560f001103014400619040003038035500c5a184a09000301025641d0100d409008048001d1080c4119940180003d00040c44c000c4051700240b003940c021500780001c64050b500400501ca81800aa030042203040c025159602c0c010200f4409901d0601a28000d0317580440d0840500c8020850441841d90103030061072a5611503a6042c0d5412007500303101145418100000c400782025a4414122491124080c005460315401528650019820040d94403400d0000048a50240c0188400301c2c400c1d142c0c2a030075080904001e420590000e000c41010042510500a0180d100548500c00184000820003184180d40304850601055120320014440481d010a181030848001c000b11b0b03c0840c00c60709685050008100d092a1300e030700103981134200b0300019010902035001421121144031515500b401c4c02c038005404045006000d940f00d81c004684100c401070b0400402 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 5139728 1250 5138478 5138491
    0x10c0807030504080304020d03020a0501050a0f06060504080709050c0706090303060501030b090f06011101090c090c030b0a080d0e150a02060603100b030304090c020712030e010f0507030c0b04150c0207030506 91
    0x14420b500e4141c951129500c8041c02c024061031000c213688013414400c0c003512900b40d510400a01c058289110714101520041102030b81140c9440c20020b150390051044034200c41080c000f40200710b2070f04007160000e04000302000486602041241c000844a1242012562082c0ca000402e141010001001ca40b814210030b809505564140411002002c925950045003443c0c51944404164a002d0140001d232800030040c21001901050380b80098202494029803507404110029880c010400455003600c14041e482c4c1000064900e8584505148004d50030040c258006117403400b02410500e501c00c180c41001038000700d0511241d49800e004003509000f408805100410784030700004d84921441c85108401a0750300c10300910540240100c20041c19100940344500402e810080d0607c20103000450000322008054003000f0f0003041594581a010395030740c2c070051480e035504a40c1090181003070300e102c14070010b4a060400c15001e039601013200b0740c0c0a0710b0303070600e90b1170300387e2a2070800f03001e9 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 5140978 1250 5139728 5139731
    0xf060c0206060103060302060904050402040e01090c180204030803071202070807051501080607020d0806040902180403080703021e0703030603080a050903010e030705030f0703090b0a0c050c0d0302030d020702130509010c080703 99
    0x5c10142e510023007920249003045400003020b03101d520000e8001c007020b003e1100d140d401c0100035001d016989402d00d0444840c2c001e0f247c0d8003106802d0110481c0300b640001002c03100e042c00441d0245100d401c640c08510b1100c040141b03040500d4030342e85c1c016001408120385d168880c0f000c0b120210404058640100b241d2001442c450400b00000303915035031424428002c1254843c0069100ea446401c4040d9854015000d04dc0d0045c00b08440c9642c0d10702100c0540104d0034420203c1d010b03074440d2003101c0500781d0b0340407000c000480f0320503a08480d901020041c1c04158403250003001048140c4010b1011a00c291a12075440401000385820f641184031602600c0c0c20030310450000c280c01008580805240400c00e84d90307a1010b241c1902c0141c1c003034100d004400c5000c01d02100c45a00411400c2202e070080342115000501881005400130305024001c0060300140201e01c4031003201c0d00a00240d0340b008100300c00e0f03c0380702c0d0800c80445104170b840003c2c40c0e4460100301c40450f0086815600484079140 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 5142228 1250 5140978 5140991
    0x2060403110f010e010e010c15050106030501030b090d020703030503040203030d1a01110106030c090e160306020715090c0312050409051302090c03040c03080d06120b0106091401140a09030f060c0206060103 90
    0x6041d0046d080e01a81c144400040c00340100483c2d00c500700310080e02404100115616810002c00400c03090104a641840315000300b07280c240d0008446008100c280c1c000c100c2035080d84e90454054101920498061005203ca01d41c08801d60080040313079000401101503001040303000501d6416846c4080070240d26089041c000300b042e080248043e103407000c8000c03420990452002d440c1c01104a0041030b04d56420201000300281d9070010440140110b441c2e0621490440e80c460403940f41400007041036101000c10000141c50b80d003000c20591881c1412400c0903681c1596000303a440842c1d95900f00b90000d600f150861030141d0515402400d030840090451800c5d5840c0c083c42c4081d40000b800e040c10204803944072500300d40000d8040c0042010000b01c5500070300d40080c107140207000380b0700499941500441c40520840d4900d1552205a5524111079103203004446941c1c0b080d0882030810070000e80200108600310706800d100d03071081c1c0300044c0054880400070300f0401c000c6d00087c101814001c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 5143478 1250 5142228 5142257
    0x30302100209030a0b09070302090a0507050702100e030f03070c0605120a090c0b07080903010608030f0906030603070e090a0c0501080705071218080a050c03011401120f02060403110f01 81
    0xc6022a400e050140140d0301d115110020789460001000208000b000d40104241901c0200300241220310130345102000da00c41860120941e2811944040000d00500c500c01c05031074266440404000142045200104000046402c2550003140038200e6031001036000100100c1140c0000100424a0054140042c2c9100b441003004054002645207486845203020f01214205500042004a10180d03840241d03103030043c5113800c0405018429441e00c54000b070100e03030100458031007034507400c1070754500800e013030803c10190005460301d905440345000108105224001581c05400010010305401c44075203800d8807488090303003140b410012940144505281c000e03080ea5201940181156840880e10400b01c8031020720020074031400c4070400c0e0016400b44041041e15a86008100baa0581d108079010315003030b02c401c00c124a40c0c003014003004108020058141c5440c1c207104190030413403e9032540001c0c1503600142c0041c0c0d021614209941c070725181c0901600140301c02801e00c40310018851 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 5144728 1250 5143478 5143483
    0x209190302030c06030a020408030d0902010e010306050102060112060f020c01140a0e0304030807052506110102090d080c0f060c0a17040302060a0b01050f070501050702010b0901080309010f0e0306041416030302 92
    0x10000782c1c0200001700102d28584420380544007c4c0c0f407850704880c1c403031034801102000f070400100c00b41d0226541441140d042e500c03a001c2c0b54296179068000740f032141d10f00701400e8170284484000b070310019624000d20000d64810f00091240851000c0082502903054501d50401100030340b82070141440c00706071898095002c000d03a4100e81e0844221500d500b403504105080480c00c03042a8401202c4550a01441300030a001405894103580c40020001000248900301e20900741e0841c0d1000e890042140000e0b0700d18000c003840c0d503c01c000d61700c421a078041100e140000c01c1c1e460280c1c070600840d07820300941d440806840a160a0305500416043c1a1006034a0b5207002d4064050303103440340f51341461640179008885c0c02c9000040d040d980d981041c140280204401d8070044015400c0002c07107050380c03a194a0035410390b8040c401840c500740300d4000644120035407a60407400d0100139509503416036001d211162189020b03011506807088092001420a4040c03201000100203210f414030109a00 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 5145978 1250 5144728 5144743
    0x60f1d0607030209061207080a050a02040f030204020705030408070603050906060904021e040e0f0f0f07150c03020115030f0b0718051c06050103080a030b030109020105030402060304020a0e010603020919030203 92
    0x1e0b4240181e0780c04403400410314500c140b40d0f540a064105100707100312164840703000d91140304100000c2204c0e440f902440000d900c224410303490100c10003d01440035151980c0141044c3c0d00c100102c0e0314065132580554201051681b2640110b035448003009440b01c0c00380542648075504454001d4103290941c0010b51301a2950b5054410640f66015662242c45544c00405e0302d102c1c01c01142c0911a040403030390b9072244034098001e1700e03010f4940c1c0c65444040005940080ea035402041101004c58508102d400c0b034080c58064007190740722807800840780c5900c507202025600501e43c000a180c1142482c48123500007a00240070811803411580c441e4180001d90815102c04607080d1103408509100c9490000301480302404c0284bd0800010420281a004203519003090702d041c00084c00000406080310040b1074083e010400030000500149403400045911601c020a40d4501a48031104d04901d29002d80012000c02d0b40058042007078030f0705003441d8103819620300d480b164943c1542e0200b80c0ba00003 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 5147228 1250 5145978 5145991
    0x303080112110603012d0506032a03040804090b1008060d0203070306050703050f070905010206010e06061603020c010201060911040905131203060e09030c070b0903031303060f1d06 79
    0x10a290500c0c1080701d407070202c0350840c200030038190310380d6158552910460402000248000c000300041c00b90700c8690348a0f001101c3e80100f100e4216600c450118140426001401c071054000581d800800045203000d0350140380282c40d0140c5071410000288201c03044488103e1040203005030465450354841d901c1d2b0f604c2902511008004c02003440480c0c940b04641d04010050b90420040007002985607004c00c0c0704d6000d844c03586486480340c2c48140da49500740d00070f060058000400512246009036503141d0008009000546020a00140d00b030540444541c110300580220210b0b09a540c4d090042c140580002c940030410030340407006581445c4a24482d01c1c01c4162507200107031204c0c210320204640e0035004000140781c480b00810080050045000d03400900540c0004508503220004c01c0d00c4910050308001d15009060a40b03420054011101c840d40c944003c0010034004d403107116502c0d000798811040402d43c00331000f40c80c4113481900d08040a20300e101000341229260000c1c10580102 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 5148478 1250 5147228 5147249
    0x203090a0201112a04060b0c060402010503070c0f030305040b0a062403110d09020406150206070c02060f041413020a0f05070201030603140c040c050918060a0e01060207080f01050103030801 83
    0x250390072403a900300000ba2031140c22613200303000342d40c480b102c1003101c0546094084a0400901d510f03204102e000b40507405240a280d804040060015402040299048142c41c20007480c072810540e0740000c12020302e0002c40c00607407100240030070807180d00d02d000c1e001b424200d428004a0b090612101c4c018020524100c0c010540e4440800164085d511001d40d80303d03a60000f95076080190407000203020600403c030302a0f480c111000a508200c01801403400700194060300e42c1d9280e10500701d41c18070740b242c41603078003900812100c00c01c0910503005100a048800b04d0400d620488400c01c00d0002502c04440031040c0100403041e58603a200c03403031503c10081030400c5a1542c0050004070000e02c01a08000c001d02241064261034100c00a6506404101240c040c080d4240010b011507071809800d00c907039042043c0d041da21130155041440280e04c820041c0100c4550b40d074488840700303050300a07444500560020304090103710300600c242120035001030b0080c070903945503550041010750140b0030080d0070f0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 5149728 1250 5148478 5148497
    0x60e090a080d0204050a03030c0b0109020703050f030601110615030105010816060f0201060b040f03020f010e0a120201020f01060e0402120102040b161103010e03090a0914010306151211040c02010203090a0201 91
    0xb40500d40c150f6000d0080a425609441d841c3d00c0c016048409042054582801c0c03c000007400c4243c6008540a00303600d0340e581403c00130110b0040351a0b800140c40386060221100315070306920400c10490303103c0d25003003100040e04504041414215401a00700003403540040940b1891034401280886c200d0f009441c0400341800b82e18022801004550001000c40500040000340291450322000540b0300840c0c60714520816000156003400761031500d150000f200365002c110895015130703031420207030040c010f84840030900302440d421a00079410160062900360203000960a001340c01e041440d00401c02103190a041510700802400303052a405846410055010108080007550309128600034000303100c50120b00000540b84d07004121598020240c125000030030207040c0c041c0c2d00e10203c402514058590a58440e907000d040b410281d0004101c010b0b00024070ba600641076601c04501501d01e60409610388000c100550364002030070800c5a00510502c0700314003005c00c6400b500d960908001c01ca4 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 5150978 1250 5149728 5149747
    0x30606060307090b03010902041409060307171002070506040b130809090709120c06110109020609060d02071b0608070801050102060708060102070b13051014040306050408070b0c070303060e090a08 86
    0x3c0503a03980040d0303604400031000149104940d0040c00c00d440801e076150350f44909440910800315004c43c0d0b099030540c4141d5040002c541c0300da00720308100b8403010a843c64040700308110320990f802045d04039425803180c0104000d0041c00062150460001714800320180001e880d40d00c00b03030044500661240e403500300491002070107454180010642c51400403188000740c103003d0340b00d90441c410f00c0c002c10300200c00180c0c2080184a400b503415401010141031814040c103101190f00010403041d10700e582080840040b07000818090b4006240c0301708500c2c01d50a22800a11080018002c032040c025044010300c0f90740e07008542c03540d101c1010b29281030300340d441c20300403407415180340c0c48105079180c0002c043d4558070350040c46001f07403901034507080d1080c2e10b20402103604440c40c80b60950042d40c04e001c28000070b01160003940d00107020780b1001c1d007045403944070302c0b807081c4094840080b414070025440040503018040c2100034003c480301003101f46410158503864042c203403001080800d00084260705c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 5152228 1250 5150978 5150987
    0xe090102040b1207051c020c010c090b120604020d02040b070309050a05090a02030910050114011e08010b0a0504030501020d050103060f050603030a030c1101050106020c01140406020d05070302010b030607032306030606060307 98
    0x625029440c1b44403484501e05c15128000c1d44500c8041d003d81d401c0c002c0fa510100d0083d22041c0484418008a529000c80c00b0700251280760050640303a0301c15000c01c031804800050f800900003500102c0c0401ea41e4403254540580380c40c5040e40700341d01400282e0030400c0599100c5440036808074041a01580d00c1c2d80d02078080741010701c01e8141d002d0ba9443c00e0004260b45001c48400c01e0442003c0c0c0742c03092280361602c0d211062507000f00a1a000540d100e0040c0013400300503001d0103001d0342c941415400c003916a541e5609903003005188401a9558100410a0021038081d8280c9010404010852424003c020a881c1d1049022000c241a00c4900e4481c5582c840c0108051414002000700815611401e009440c0c2809004042c0000c02c0a40c140c03004190600444044072100d8000340114803400c401a030f4141c00c5124180c00395540c2e40c030550303075a450a00450780b1541041d03034000340c050380f00d01c40010724034508507002043c18504020441903480006035141c1000007100c1203616541c4201c2d0489 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 5153478 1250 5152228 5152237
    0x10305060d0c08031b010b030d030b1518010305060d020a06030b0d0b0a020c1204060e10090801020c0105090f03040e0609060d020d11040b090606070605040302030c01090305040e090102040b120705 86
    0x405440000380000f41040c00032001d060715203905100b070b6082d000d10541840c203032280481081d138582c01005102c200b443c0243e218502c46034014042d40099403800c80b404500c0d802c440e0300c0c64005003076080b011080d5030b41072260683c004000c036002018042c1170340109011347d002d4080c2a05250703982c5200000b40ea40c02160040050b40060607046d0b5140264070b1401035045004041e982d0700c5840d20b80c1d038807045000f040d82d09440903070380c540458111600420420000360b08040d410303c020028086032040082c0005d2006102100001c21a0306018100511300b2091986011154205000521984d02d00c0004150410b80481d2140095119900090100320b41c120000b0740c414007403030f1013a080040c0150f10446040c02114100207018129003841703603141d03084642552000c0100500c9001980b5a03004640007402481140d043c520304a03901030844401080c2075021a401003400c0011144600a040c2e1110703403540294101407625a44240340e000720800c0502085000c4001400030348102e00342e4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 5154728 1250 5153478 5153483
    0x102010b030a0302010e1006050d0807020103090c06020a021503010f05040504050f0307030810050406120305070510061412030c0604030f0203070204020a0908011a010e011206050d06020301081b0a0302010305060d 93
    0x3241c2001c60b0b40760180c000c0103100d06aa5440c003c1040400e0b0b0100e04c0c6c03140d07030700310741005e048060711103065607922409520171901203052541c1c40414501180440e1003c5014000c1600140800320349401001100402c3c02002c1e244001e08000500105004140607001c031101900c002c80d041e2110720b000c500b003000c4000100000d01c008030700042816030004400c2d01546000c0c145c4030030291180c00344070a48529000310030700301c8420f080d000c00291280000b4000c8074041c100350f8800e80d01ca0321511040e40d6132940050706103015464058862300e03100300d46404080b0000015803400d40b141d5101c6440e040e0041c4050103116000340819400340c001d008032402c0e103038010411903440c1d40c4000301a018020394000c0c0c0340355600c0c040c00c100344409013200d410740c00d881c16150800d01080405c01100c4181a44e0280da404680341c10f00050a17480760041200d21038840c80700540c0300e40c10241c009140406081400015091016124080743c50340320419041c0c80d020700e0089829660340002c00c0365901980c800 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 5155978 1250 5154728 5154733
    0x905030c1002191706100e0a080c010e0109030f021212030712060503011503171215010e01080c04050d110d0c03120c03050d0207020319030302030709060906020303150102010b03 78
    0x8081c1d50074065004224400b21007405440341819010200c0360503210607901c003111046400440d40a18100d81807130216840c510700f0107401170001c000b040c4082c01d160302804450340311503d2000b0b50340e002400045514800e2038006421499521420866081140060302650700d0801248241b50240f00500350000400c84d04c503500d00340700c41c00900240c003610403101940d01c0c120011805107410700400005030807862504290904548036102c2134501c107104114100e400300940070f044210744044610070314410040342142c0c100310001419482003080072a041100d21810808250116401c0d1001c0c0c03482030700e0351460402c1074907000c441c2c1d401135040c850740000c0c0d04805404018080b0341e001d0540b403184a4803011151008015220742c1d0300c29000801051040c09102e501c1c0c1c0c2030764040c080441c0010200e420f488050b0013480314200741110300b40c0c0000e400004100113250001c5551307004003118580300640c03a15101c8025280d002c003030003180c030600c015281002c980e8400d4204d81c2051000909 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 5157228 1250 5155978 5155993
    0x3020f031303091205100e0c0a0605070b010905060603070315050d050a02030d020303061c1b0b0705010501050102030f0901030b040b0307080a0b010f05010903030c030302070c030b0103060f05060f040905030c 91
    0x26450307805154000701e0004a042401281d01c0415526000b005907000004214105e001081000644502d038034901d402d10448480070455030b140801d0000034240c6455440d0b0752181c0e800c16060340d2005801001f100c500b01400d1082c80c1d00c1e60360440f03600004c107150002d40c1600c000e40e2078804444c0c0d82d101d10741c440c4122450400307003c004560605254806c800301c4a840719800030a03600d0380401c03280b403a488090100c4441d10407a0400702110114811070644981c806022501011000690000c6ca1101000708406e01000303030034400d0341d002d0b200c24001035003825411030f91281284102540302e410581c4074070360ba100540313454000048115006003a240181e0312000e0655581d8004241515401d000034000180081201c10b04070a590301039450340e1078039085d500c054400701c1000c4411130405030300b0002c13172011a1a90b41c28078090751180040600179451030a00c141980c00710180540c00c01e1800c03040c010960780d00c0c0141042c40006680210f6040c40500f02641540690881d00165024050 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 5158478 1250 5157228 5157241
    0x60504060201050702060906010b090d0507060201020319060524070b04030302090102010606030504080a030c11030a0509040e01021602040b1810030201090b0307050708090402040b1201060225031203020f03 90
    0x501500580d5800d900801c019a1400000caa54000540303000c000c542006005001d214611802449802c40152484012100303035070f58035103000304a603c56001030754080248900100d504084a0b2807030344c102d105006175804c00001407200004900344403480e0b41507048988210b0102d00541d6001600407182000341d01c3c007410041c003e544403901850055107843d001180441c01303803044600603504032109506202174180d069005104020030742c820b20036003043d007146150b020070041920401315641c0d151101d600c1018001590310010040e08103900611403a519182080700b0302c4051601181d0201d01c216140c004203c1070101c001c0e006002440030001c2200440d02c14074080c04581c17003070f60350300034a0341d03944880607003400f040d50307024006201084002d002c540741c0700240441c148020001403610f83d9074100e0b03071200d0340807810308221050f0b0385004002898040c4120f02c8a9810b070386005083c8145826505210100760000070a4050512400c0c50070034801d80c1500c0d0306500304034101d5a01e05056 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 5159728 1250 5158478 5158487
    0x105010303030509010204030309030803130c080a020a0e07021b060d0f140a02030105060703120605100309060b01020304080c04022104050a1202010c08040f020d060515031e03031b0706050106 84
    0x340410740120341000c000c11140f410510032501103a40654400d001c0a00303695841c00150720140c0442da964506100d1500800c0d0700250b0440103211101c02010240c0040c4180050310200d0b03480030103003203071060401101d25004611300c00362042c1e03000918000054540010400e000e00b01d842d81090707140071814010521950700c6540e0150501d50400841ea407807501c6401a44001d00801d0342251003800000b0019003e0001c00c070700e03180ca01c0b1001c6003041c2c8a0303012900944d1050f0b50200080c0e2a1518101403042500c5280345001080c4003541c545030400f0b0b01665140001e80d00103008560010300302414654032540120742152400d205e44140c242418216075491a541d41594544102c1d40f0f4901203d00500c41d074250302441d902c2d101001c0d0b4483d10340065207020100c059070080c0c40d5403418000184103100f00d6200340c50844844071f80d241c100b81410310b01900403050114580d000d9141c801e035104000141c9600c8040c00713640d40e216000403031000103540550764004001ca41081c0011031202d400 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 5160978 1250 5159728 5159731
    0x5100e030706060909030c031206050409060504030f0206011401110f0307030201060312020601050a090b0d021002061005030307051e030f0409020403150b0f0103020d020f041508060102060114060711120105 90
    0x10b407105014540e219001e010443d60030001c01000300e40c0300c0c03407542c000070b0240c14182c01c014031210000401c69a2000498199015480d040303407560303035640422003050342118081176494400d2000b0711783c940c182125400340d1695140c54505114410090f00d01c190010007507004118148025203485140034540a03003c2c010360300003143d60030403044951210500c0050784c83d040311b43c0208000d051518203c500300082500701070347e1b50480c03021301c00e8601507200c900c0683c080300340e076a00070b1402c0c0c80d10034842d10001000d500104d1098000300803000104800103804000040c001c0e0950790400c00c0c0345c04207480c520800c001210100c10100e00080c080e2411b5024004590040d400c036500e894400110f0003c841f650381c4a81e9000f81480121110365100783d000d1b1260740e19030400103203090040c44646409800039800b0300064440c1003c0940c0459000202d103070085002c2c0000e0102e0350620048110300d82e1035001c564020807003c40c90b0342c140b003402c1c1d4501140000150900311051003162045018040 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 5162228 1250 5160978 5160983
    0xd0203011d010501150909090c0305010203041a07020d0c0803060f030d020303090106052b020109050d0606050f04020304020a062106060203030f09030405010509090c0702030601150315030209060d05100e0307 91
    0x291600000b1040d42e402000e5150032150b96848503041e0a00d2214002098011016a003d59275541c1c00b00c0021700920003540168050004404121074034600362003600002003025045420000402d01d01c142c001c209030305d1050744106001c0c3c50343d482d880807030b5a60f41e08481142e407521424080317483d000d0b0080015801003080314000d2260035100d01c24002000c0c10b4040614035003070140c0708003c09210400384081a20303c14075050030401e0740c4000060f11001541015204c0d035580c0e50b41006a494004034008882d0000e030f40075801d40c5025000a01d011059224420500040c0c074500100540c0c01ca1035180c20a422920420085c0d840702c0c0000d40c2c2e07400444c1d0a01c50042a04042030380d0b10b40000544040f580705a50f403030314002c80001800034419000d060807080720814002040182d8007884554040c00580c03080381042c080a59004050310301112101860820542052025868620701036038805000d45a10152402500d00503190503007986070030440501d0054030901d90131000c03000701007090 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 5163478 1250 5162228 5162231
    0x5030a05060904030e10030b030d0e031504020f10021207080a08130b07031107050708010e0d03020c0706050702030c040f05090d050c030904180602040303020304061b02010206150d0203011d01 84
    0x5448800b03014a01d10142c50180204004441000c00c2d840e0540c0d180101e81214980810030082100103e07240580111030a80460060101c1c5641d9090400c83c3c607080541060380d42d91642066000304d40388452800350240101c2d042c01d2581240e60081004054107032001804580e1400700742428606078100c1d4011200240c03025020400c9001d800352001403541d000f540da41225140d0500682c020304820240780c40300201401a0b10210b1011f011031001030001c0300c0040381d00c1c0c684920140c1491403642d01c140915205010506205d40001a404251090740c02d005513106e05500000b46820028108541d100741410315950421070160411070180004004940039403401a405407003502414210760842e80c81440b882526290540050380a444030031803415803103503d030711498160380c8141c0050f809a403000408000f02580301c8035200c8000239822061190844641c0001e4441c4406464140441200381e008103040d600d0034000c4807800d0b8000c0c000c011021820582e0a098200400d80301c2c0e4a5 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 5164728 1250 5163478 5163481
    0x1080307020f061305030303010b0a02010b011b06050c0f0309010f0e0a050604060c0507020a06050405030d0302040518040201050c071202040e0606150a020102070b0c1c060f0b0705120a05030a05 85
    0x4000000d03100640d6008040404000182c01400700d0b54010303400036602120310b039800040d02d481c00e1001710f01900301c040400d5a2070702e4145019080d00d04d8502500c3c10406040b1b0724020004442c440d00e80d145a110001184980303450003041054003070b5005c0a502050000305021403a40c05500900c6400d800c03400901000c008101d005480f80d0322408050500c6c3c02603400680080c00b0380e1300110f4035044600b070040c1041c0d2103401290743e03d50281c1051002c03960016090013145010000d002030100c00d032a081d803405040c07002103180003506c491800085c62104002c80e04581c0540240e0700b2988001045a1402d079984508070403000419034140c2c0214540711911144c0900860311a20815014024101d1803130f005001d0100c5901100750f20b41195070034481c1300001408038014501a0721464607841c3c40d004134000e00c40c00100d045416082031407918400700505420b038203d02c0c0480c1d050f001d206071920043d0801c6da041c081341c0e030040111176000003600c6601540002c05180140b00c08242040035 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 5165978 1250 5164728 5164739
    0x50c0702010206010602070b0414061b0604050105060d020a06030209010e03030d0c0305010b030408040308070f0b010303030b011b0507050f010c080d051b070203030f07060f0e10140c160215040905010e01 89
    0x80b42d401d8041d15003682360800c01401880e8441c0c0b1902441200907200302c0c90403680c8013081c4519810384c0c640d054640c20600c20322090060900400790030800c1152087c045a42070343c006142c40d00343d44566824584c021031202d00d1a030181410401c100d80103010341c0c3e80d52044026030310052100b9003c03600443c2c41c2100100b503240d003020036248669070088c09140b0700341c156116079032150441401143c200000e00c4104002034602140360b0700840c82601c021840c1d03110b050001d40082c1c0ca4803c6500408030014503203000c190300141c6581160003d0b02c5010f804502d81c00100c84008104030080d010000c000354140c451301c03007548958442ca803040c0c0899440394076007040010300d1090181c007a5240d407040c061101d9442c0303400f00401c1c0c007038840c0d20006102304640c0c140c80181d40c00b11145078580d80219000100112040c06540707012461199030222602d00203d801d4600d0007002c205141c0d851041003088219224030302c8070003040e500705142d20b031242e60315151000038103400d0190381102d41003000001007 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 5167228 1250 5165978 5165983
    0x1005160804050304060c0c0906030b010603050f090a0605150d08030114060f1911010e010504020108061c0b0717100315050103050a0b04060b10020f01050106091206050702010f050c0702010206010602 87
    0xd2503118003e54681440c040c070403501050365101c140c40250201e00700085c161058800c1c00000c0d8802c03034840d0120b45c50304c2d20240c11143c0041082000301980010050740300e00100700e0b41d0455a115070005403a40b0f0342600c3c142d000301300710b8410f07030080101c0d11008184030700c50001e90304075100a910500c2684440342801000d00440103403510a00050111111100c070803040c0800c400400e18110000c18034041c0c055003599080f810080705030b503540080c482596805176400354410380907201214559001c508025841c80c040a0162000502c030000c40d6a030380c0b00d036540d814880c84041c0c400101741049540b071003182e0748500c402c50702c45d2208401c01d000c0003218000c3d141240e4000c0003505158030b06031104c41c0101b400510888002d56100c441280030b80d54400c91010070312103907002380b0803461b10b03902a40c06c40d50103802550a01020710030401c48078081402401c41103a04c4000402c41e40c490050690140082d200303001e00b114101000c000940350490058101c59000364200d50756030340d80c4c00c42a40c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 5168478 1250 5167228 5167231
    0xa051b0118111e0112050a0207020402041202090109020408070501121b0906020c01080c0d0f09080a0207030308060904080703050a03060e01030f05010c030501060801120309050a03060506090f070c02100c020310051608 95
    0x1d000c05c82504031035071314060540c00341d54044404a00585003820b180d0015003280c1c8540c0242680c03128102560b010b42c10803c01a0303026212030340c000c42c90603003014161566850b0500c1400d04010070115492440d8081c3d411182c1d0058540c103004040d203400c164060000b56460140a00504c0742584e12102c644c40747c0c2e1028002c801d41d07041149000b000303604100140a46003401145140c83e010314000042250b401000e00fa00280d0207050302509615006000c03060107444e241c850203801c824000420040b4003128805680360804655500080c1801d07809000c880c6e0200310618024000081800460b8910074806803161000704901c248000c420b50450f40c080c054500050541401800803a01a600342c0e20f03030390301904100c00c845580e103001440091540e001181c40584030b44c248809030030b0500007650000b15505500000c2d240800c0c0c01014070310003003400b9102d0142c24982c03111070b6010720003c515041d0041c09a1f2501c0f414000c280010b0301066070503200603000310328400680d510904805 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 5169728 1250 5168478 5168539
    0x3060912030411060c06040302030301080c0415060503060a03050102040902070209070f08011703120a0213060c05060f040f021309050601050102010c050405040203071106070c02030d03020a051b011811 88
    0x1800c0d40c030b40d81c442c048403a0b811000c45410010030008048410002c0100c00c7c0b00724840d500440d81c030340c109004142050b181d1044c0c14029400e08010240c0074404601180541d00140340c0309440e55039010006e04841072030751001c5c216501c0002c01240300420707a00200b200b20300980312503c3c15125070b54201c56180604981400151a81005102004c1d1071500c24588014200441b8100721610f02c0381c40c0d0000054490b603007003076800030710900c01c81482c5002100405c41801c1c0154096004d4071030b1034031108000c01d101219440400000c0c00c0000e2200c440319169005003920039503c0400c101d540052042d0001655144103640c000240d961050140c49990000384c0c0c0c03442c3c10a850300040c030029400152460003480840c40701610082e1041101c40d00c521680d5031901d09001c22801403504200a40048204260041021004d415003040481c0c0040c1030000003000429002c800711801021204102900252106402424050160300b454040001118840200c0ba403026180307110400340c8619 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 5170978 1250 5169728 5169763
    0x10509061011031309090c08120d0507090902070305070309050f0109030b06030f0a1208090c0603061002070302040c03020c06090109111c0507090207060f0506010212071a04050309030609 82
    0x108075814420910b0044081010080320b040001999402c0c0813291644c105011641d9501d0580e0301384000c000d882c20051610901800101c1100e08003000940305075141d8086082c1c440000c508034074800e0841c9001040075080031501c8102c103160013402907100c0e60050700003905010f404120740c82c1c40103004001c0b400c1612218007843c5941c3d204425000000d0000d17616019400858030444018044100c500b8410041d03221903001202d0080d105050145c00d42016900140c0d04501c00c0e1a104c044a070444400c80b0841c1004403150412880c044450700002e41250500b8100030703031a0b825401400c2c100014500341d0b11155100420b0750b0880360690409040c440402031001c00c20304090305607100385002c0d41c0101c508a030300f0303454003846c0c100581c0c01810006c0e40005c0c040d00b0300030144504c4150302c3c040b01042c000382c1460300000355900c3c0e442d90304440a076000140c80c02008480d0050940042c8840c0720360205140070300345140c4903041004aa0b00030300030000000d142d0320340801c40c84141c010040b0b6 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 5172228 1250 5170978 5170999
    0x20c030706030c050c06010b0a0f02060402030c0108040203010905010e03040918020f010309020d0c12060b0d030207061202040801051806010506040b0d0b01050702030303090714010e0603010306051003020d030804030801050906 99
    0x9084010744040443c28091010030480309111190030b0090a0180c440a40440c0c0c0c0c1c0c040d82c0600800e060140c0540c001150800001c0c032006980105911181392801d103004c8440e61070324000a401410300701c600501542c40d00030240c0d1040001310141003214140401008030680c018a0040304011965000b5800524080d2a4110398040d0340034408090000d01401400112a50f0312100881039800c41001d44465a0143d010441c45000d000b03405d0505a4a24142035901d07600a55102e00c0d034003070302c1c0c1030003841c0c00000d040c814181c0c1982c0050441350b0080c44142840c0541001c4603244444141480c0078640002c107140c00d156084408072012400f07031910b00780d4005549030051003212a9581005802c0000c403000d0303541000554001c04150014041a600d4203406e84032018944801a050092085164407241e860a00380c07030440380c10030b40200d40b40ea0307010110161010203410007948102500c84c0b21090640c031245c001c1c4964840d88811020f66264000c1201c1440100e401641c40800c100 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 5173478 1250 5172228 5172239
    0x9090102130b130f0b04180603020d0b0703020c010930090605090a03120e040b090105130b03010905030a0801080f0313030326010801020c01140405030301150c02040507050a0e01020c0307 82
    0x1460300e407525045880e40b594452130101c0f09912554041001d00c40046001d02014581d252090000075140c40c04021040c0303950301141e440070120307a025289403e507000181c40640644c0445908030a00303c000c01001c03102c3d1608000b82c0412101101a40002c0c0c0d000c1816802c211034681c1c0b15038040c2e01ea220006260450032500d0354480d800541d040150100c0020000e040c25100e0512030000d0384070940110b048a044c081158241482244107462100040160f070326202001c0c54404401040480c50440a00c00b00e8050401c000b0b00910906c030008403480083c1d40b01d4181c0381a035003981d0540d69a05c0e81135050660781d00a00c0400514403074032800410001380200ca140d031307004602d400000310390b40300c01c407400c0d4038400d0036071040352640d40018910302c00060030721511582e0f8401e9030074407404c1e04050301c0c0d00317075680814003d80c050592081c685244d11409103058220311039006109000794074240c1b5000340107801c004c0c2000c01103502d40c0030030324882d8004213030303030340e0054001d80200780031072400 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 5174728 1250 5173478 5173499
    0xc0306070207120c0b03070903150504030f0302090301090503030f04020901060c081b010f0903090f061d1c080708070605010803030402010f0503060105040503070807060e09090604171603020601050909010213 91
    0x340b002c076130446074031200041c60811503010303520032035845c0c4901004610b9400e1240c0d06031076082c40420018586020080081d401c803644429400b00c6140044e121000403000c6401440b0204010301540f00110801000c07904920301c06104510035945000e1603640e90405460304076a02030010030383d90b01400010b100304080703421540030320124000030905080d409070030000c880d00120103400240004000703010180d46600c1000081405103040000e00324401c0e402525091003000e60781c801e01c0d80c0d0740c241815055100c0700904060300194041e989003441c4c64590038a90040c2e8048440700e0134000006140030000c410341e4411034040c1c4440244106446003140d1a61008150f181030000c18880131410f034808002030009403942d0030040c0281c5092502c05010741c51400d940b54800c54001003009180300c0d0120b03c560300181d10011a900030b01d400c0300c03500d040b40104402c83c0d0f500729004108a00b85640010502c0c1281c0c0b050716402c04940325070700d0180c02c2c1e10901ca007504c09144110010044030040 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 5175978 1250 5174728 5174759
    0x605090c09091e070207060906090e1602030f03010e09060c19080403031104080109060e010b010c120203040314060a0b0f03032a0102130905060a050f0105030402010c060203090703050c0306070207 86
    0x3050261400300720b0f81520280c3d01016aa4074005a205120038450b640d04528564058034080c00d08500542c90708003061225040184401ca5030b107601c0c460000202c0c000c01c05d640c080c820f42600203032290b0319001d114000c801704540d204600d00c03c000108a0482007481181c80c00f01c41d02e130b5400315010f08450165010f91b4060421000c06a440c901402030f1b001d0003014001078851032002290000440c10240d040c0c80c2c610013000020b0340b43c6841900c1f00d80c1c01c81d4400310030540c8610801c0d0b1001c8406400d03401e5000d02c3d44080c00082d180f82c0440a80000454050b11a14510360104070003003030042840480c1902002e22034266108010b050070002e01e01c80e64121621008851000414001e62040c0c2640c001040e440c1c0405003204080c00742d5103580c01450391004041e6500d601043c6881d000944004030a0311a0341072190000120b029644254103844426821800555a03810a0301d092940c91342140710640c0c081c007076089040480e145c0480c0450042c02d0980c000c05d00c240c01c004c0d40704801c201 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 5177228 1250 5175978 5175991
    0x304060b0f031b010e03070f050d1e060903020f0c0906040f02041203050405030601080d020d030e0a0203010c02100b06090d0215160b01050109080a0507060f02070e16030605090c0909 80
    0x20700720000d074196010030040c440ca00310869004020390342c007000505440a90800705101e908204000d01c42c14019054401c00c455040b02d08240c0d41c45e041c141401d000ba00041000e4080643c6c0841a00b840302da078000000203842582192880c1c0f1030b10030519207908107000c40c19417010781440850141d2900d07070006184801c04e03090040c640b036a0740035500501a0b840b00d00310081803021904200c203240c20301c40c250040145001034450402c0d5414001e40f207200700c4484c0824540c4d64260011107240410035250400d03809002004a000c5800d0041d60f02c2000288481b08181440d28482e51410180107542c4100380107040030325060100e0b820401003841480b10301130f10440500469084415640150125038010f84a02d400382d4182400141500080e030807461050b80442c07013010002e000058000c00301e88881ca8501c11402e060442241000d105078020007c140050062102914101d004201110300d00c0c1c40801001d0340e60018060070306801c98841c401e41d2018000c0c00c40301d04103240c0b107070342c45078 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 5178478 1250 5177228 5177239
    0x9060a0209062208060105150d053601050901090201021504030203070209010b03060306010b09030a0b061c03020102030a05130209070e01050d020a020114150a0501050702040e0d0c060606140304060b 87
    0x70072985110301900048400040d0400c3c000004001c651418064180941b80954003444041549800c021480c40350a500d00785042e03556002440b000d0804488455107c0e108091a10003e000300102c00c80268003051760019500c0c040c0443c42550051290104059068002c1d14001544c0c8010485d5960022f1060b001c0d400104044401aa1040c14441c044c08903810074603180d0a1a40c2414a8007105801c030080c03a4504110f00c008568000a8200310181d1000240030f480d590740011a0303c4440a11030780e01e04544074858941016011b4010354031603401002c0c02c002a6980c00c0400001d5520214003035001484803021942c028803aa800b00d081e00710605286141c40c0454800408036400780d412040140d546240500b0b0092a00341c00341e80202e40244502c18480e008030000310740540034402e03a07040c0b00c80010408215122600900c0c004c29008003500c00041d08480702621110102d0b004031941403a1000201d0068001caa0000300800d40c041c02a00f10740c1e46a03100d10051002e00101e581c0324 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 5179728 1250 5178478 5178487
    0x100801052e0f1e050303040308030105060a0c05030d23041208071107140405060a14040903020a02030a0501050f010e0103050309010309020d020901060f090b031302040b0a0e040309030c0e09060a020906 88
    0x2402d8401d54880106120500240c00c00310941030441d0a25242c4c010f5807180d00200004c0000c41d10083c01d880c152031007102c8440e13075040204001e50350344401140043c050302002c1040180308440e03038048035002c0d91464220009030764962146224100889004058554144a25100318401d2080c240d2242c460706294003c1c0310700f42c450700d00e02215544171102900ca010b2404050f0308007030003210f40140040d07500303210050030082d100080d40b003000700d150b01030f5503030300c40c010f05140c820807500c00380c540c0183c2075843e002518100b0701e01074001240c42d1841c50340b400000080244100001c181282c0c0c07c18007840c14848864011000303090004c401380c0e03008d4907006c04e01c0050703a50010494024103498640080109000348050000040380e8040e00300001c05108202080341f82c04001860303154122000030301020000001036151805410000c0d65901e1542008201074004034040140e80c0200d8000f04915612030f80b0722402da400312980c19540e0041804150038062a8010300031000c401001c3c00c2c140b = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 5180978 1250 5179728 5179739
    0x201020a050703050a03030c0518060901120501080d020d050c10090206040302101206060302040501050921030309010c081303020a150608030a080115030203060607030e0409020406060206100801052e 87
    0xc2c91620b030015103070394004010b00000c01d0340512480d0384410450628604050241c12013880454180780b1281c0100d0340042c4400150384564240541c000b51900108440d5840b020440d0350744d10070700707022030161281c1000700008500a10a50f0075010003400107001c400c0b8401c0c0084003a00b903100080fa0070490502c004030060359148249205600181d9440f04450808186a001d886043d4040b000b403520410081c0030a0340e04c203080f11036002003911013803610107a0007100b18a1862920b402c101d50702010041c0a580101900011605182c82d6038101082d183c918007d005207084881c001d000d40d1120003528005414401ca4503843e400324840080c0d85680e501b05241194012450003000a0555005102036500e501115080182d01d02e0b0450851400c0404215503104d9444043c060005194000c21103236981c1d008500201d50281052241540c0c07520f01035070f03802050b6590b04c9100f100300c1c000b0903a01c03070520440f0700c01c02c0b1001050051008601d42150080b85810903e0000c004601000c1803 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 5182228 1250 5180978 5180983
    0x609050a031e120503060907080112060e030f0f040303030c030b06030103060b0f0603100512060c0901050706020d0606030603020405060906010e1314040f02010f050301060207090e030d090b090f010b06160201020a05 94
    0x4590996131100e5035a8074218040260708000102203a09018040b001440300c50302d419050b080c4d05500c50000540c081c8905021403460060010382d03040300d100000e0b20b001e80760041c0301070300c110ba210382c80501c00c075683d81c43c09400740e410324103265410030000d2004102040740340e0880101c1803805003010040c001e074400411406da204440c00070b12a182c0140800c082d0030a40307400b440d0000d001b0068038032805c14041c401c1d6944182d0f003030181080000f041c0041488043c0e4100d900306541c90004200c5940d64080280c042c001c01e21003644070318074040001c1c0050034001c00c0c280c401e0f40143e565208641e844000c00120b02440030342005282d0b62141038150415403454442d00545c02041c40c0080180240700040106072000c0e00c4000b001002d000400030395400141c00015501108004241c644d811303d5403070f1441c010003400c007240c82d007410890700c140500d662009005400040a5481c0d181d008407485080c0c80000910981100e410880c0901d001d54000301420220710510644142d421651540751 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 5183478 1250 5182228 5182253
    0x30216050105011809050703030e03070905011d0a090c03080315060d02071407080601050d080d0213050301060b0a120209040b03100b040f0e03031b040801020a05130609050a031e 78
    0x1180e41e90346000502c0958a041c0c801c0110340080c3c0c42c14000281c082e501c5945800603032200406211310f41c110369402c1d59091100a002d002004420000d56031b4074040c048003001c03141c0d810090000d51101040c0300740001d00a8206003904a2000c201131455039940d900c035980001e104410680344840781034010740e00c440c0100f403d15015100540c4807442030400140148560b0f1944550750f02403607080108803c00300c0e4450440d00c02315101d051075446410070030494861590b400c40d0a510014001071041141e00310001a524140c3c020000d16441d15102c0d0b9142c42446c0c60140860101d030070f00d554110f801c0d001400300c0c3c0320142011920446400100c0d00d0b000070f81c0310040d180c07074561a0782000c90400307100e55401c1e00e800840611a041c0e44a00c0a034485c803000d4290f01200b9804e03559145a03511860441d070007001c3c004021503880030080c20041080c0c2148400f0404000500c900080ca1427081d1031a8003511401081402c08070324594442c00d0556806c00401c0542d5a440b110340e010450142502e07 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 5184728 1250 5183478 5183483
    0x30c030309071d0408070602070c1502070b0c03040905090f0a030507060e0307030e010302160209090f06100b0307050a09030c0603050105030c040501032001090b03010602150f010b0901050a030216 86
    0x11616814805001d508064642d0042110490b0720b107460b02c11902c08003015a08540c00c003200aa0351045814008084d1041c404054444c81800d0300c00202c850610b010720803150300329030035035100c03d4882d0301503002840f5240303d800c83c6038001c6c03100b4444482d0541c45560000c40080494903440059102a810100e01900942c04500b0200c0c1d800c0c103200030f0313004007901105040d02841c03a080c180c0e03802800208402d41c0c554109640400c3e403032403285480720441d5003d6001003e0105618285640c0c2c0c0c0c6c2e500e80360010711014000e50700800c101040380004041940c80405060b41159200395048405801c003100c0507040201c0c80d900000410b107049000d5024104960340410150305060038107183c0b80c50544141d0181e40340800400200e00c07070a584603007a80d5116014108036004000480350f05105400009500e0380000000903102d8002030002d500c2c9228095006041e50344000014a0005c00d21440181034000c000ba1001c1d580b2079402484102c1080c180141400062015048100e0318038404 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 5185978 1250 5184728 5184733
    0x90203010f06030204030c060c0206070501050a0e0c0a030209060111070f0b040f0b0a02120904020909010e0708071403040f06061e0501031b050f090301140403020606040b0603040201080411010201020903030c 91
    0x511511040707600080290809080c19854075107196506501c805070741c4654002c10082204840440d0b46040c12a040725800200038441424141007040c02041c050010051510841c070f0720501e242004200d490842c1e030000d01c0c001c1d40380d076044010744002d2042841c00681e80528a0f01040940044e40a4000b03080a804c008d51154203101e41040e2142894004195028050040e00f0030150300060903001e030304407035241c2034850440340040b130080d005101100d40d110f40c0140c00841c00b0360210940c40c1c070038180b543c1d5004851f111400145c800307024a8600010003102040001d0200d02d1920407034010b02c0c4038180c009030346540c03003d41e5403a140207841d11700d50203603062504109960389800303004190121031490041c00301002030003030590701c00e01482c40024070001c2400f4140f55030a47c00789400c0c13090f00740c0010031840c0c1450001d40764101114001d10903460b05203418003e00b032400079244100c0d4103031207000c0161280c0d00c82c0944c0c14100d03c10241199003c1001d010707951030900c060100d00064400 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 5187228 1250 5185978 5185981
    0x403140a05030310031a040b060409020a271805030304030e0a090501060206090d0206010f14040902040c0c1703040b06040504060905120a020105090105040807080a0201150b03070806040912030b0a030c090203 91
    0x20803210401115401e442000701006c00d10001c039800b09003a542004088500144800c111701c0480c0e402855a4007100c040c49203641004901003007504100e003200c00000c41000391b040400d000c41442e610482014066034018400540040d02814185028060040c203040c441a51006008207440c0701341c1118006030051030900402c10010001001034000d0740c00a884150b05050800074014681e00c200c480100b0280304c01d4045480301d0740011205a001f4000303003c81c049680d006850410500c0c42101e0417408120100c4608804a0561740581c2d4000402545500d80604110190002a10540e85150f850b107000c80082c004100030800c551281ca4070360b07241c441f5124003030b0841e88010408034060341400100000101c08004035468560310461003600e54105450403801088001c0c00460250003001010460807150f101451190a00ea51140c180c4d07580e02d01071100b9100e103481c0003024420054070010f9064002d82101100c9100500a03062040d642c3e120040480742030340c4900f00d0117030b0000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 5188478 1250 5187228 5187233
    0xc04090b010806092205070902040609080105010506070b04080c100b0414010e060103050c0c0105070207030209070c030e040b150304060213060c080f0901050708131809080403140a0503031003 84
    0xd00c4410000c00d090503009071a06801150305102c3c02014042683d082e111005541000034054846041d0031108445c80103880b0001030000354406c2c011203001c64061390001920000c1401602e05803100904020700746441e41d550790341140c03005007007241c00c0c0a05100201e0071100400900034049110100410522000c0d0103101c00c407030081e44511507035030319030005026513901c50388410340001080ca00041c4681d2160003800441c05400303003030202542060b0a02031a01d500244013000c0d02e00840f820130242d00d60280960310030042940080210b002030401ca241c0e0714099020994165000c0d145054869010034411540c0c0d0089504039540b66000c140c10b6001291042e400300602158200ba68021602da101c028280c0070b192204850018000b80d410303d664414015140c0f2a40c0c412407058481424000d600300d0080603010780c4482581e0018040e0008850707000d502070181d0846056071900b030568036026010a9650071807241c0348100e220182c0001d00c200021803041090020b038031300d00e50452 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 5189728 1250 5188478 5188481
    0xf06070b01180c0504050d0203011b02030304030201060608060310150b070309030b0108010b0306160311030103060c0210060b04061805090405100b0105090a050108040f0c0b0a09050406030507180b03060c0409 91
    0x714040c02d01e520307011100d103002e82c00c01d04030380039943c00b25a20600c0c1401440028003400800307000c0c200c000a440b000c15090794001000d9800307988650028816151200030031906524103c84040d85a800310094803103600c159840b01402d2141e928540301c2c0a034544090f0012035001c03c00031000148a81e40810900500c04103060140460800074404504403400080e9a44005800a910307802c2da8142c0100b940d009902140c0c0311100c10704120340303035a5139040443c01820724034402005801800004692481c0310b226003010f45010180c80c600f441d0411300101e4608810405140083c0e00d1003070003082c00da440038811445248120024603180846100203400d4a0303140c40281d0601a041c0140e403407a944090b01c00080e50020f10741444595202c0c01c08614440d0b00f00e1002d043c10b00e442c82d01081d00d0040748000c0903c040130b502d506503826910030a00048a0203480040e02c0c0fa08040414006130b44500b5124051007080365011500300b00d40c0001a0400d070b41903d03881012030001500300000b007402e = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 5190978 1250 5189728 5189759
    0x408030403140a03091a04030204060b0d0b180106031a060d0204060224160c060504050d0f080609040602090619030506010e060c06070305070302070602030412090503030c15060f06070b01 82
    0x428043c01e10307080b0035980580b07100d82901410f001c1e94120741840b010b08144400b03803401103030002d1060001964960004030550303c8650002c61070b9043c10810400d03401c241c101284420302e401c05080160380703882c108400500200100900d2aa120b0204030421358500d006400902408500166103619041002c0e00c0c0c8041400710b83c42400003c6511501c01000035a041e90203900c2e185c0c02010410310700011901c00c5004000201004d140c0000e0000344040000d10140381031003501d40d07045c003840203801640c4040301140c005030700401c440c00040010301d60303401811054001420309400c05040598807900c1c0c660403001580020b65030020001c4560780406114000300b400e807501403030041800801c540307405000b80b403001855242d1010480c154072941c112001e40c0d810030004c44d224141403900206040e003800c0258000b98200701c01145906d800b200700c0315140700602c020451945490300200c10310100910042d84107551040280c0da6032200380c01840854415070041381c596050500c1540413011 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 5192228 1250 5190978 5191013
    0xe060c09011107120206070c080d03050a05060307050913060b120303040506060a031505070207050d0b18032a0c040c020102030604050702010b0102070501030f060504020403030206090d03021201050f04110408030403 94
    0xea00400035010086401c422030f0717070140c43d41551100030381844800b0b408950b0258985200341019544102e5056200a000e440c00742410310943d2100001c151f55120355004003a80000b006000c120742010421071680201d10500d4041041a03820780090881c5007607102e0006990800000c10007006024002141c0c0444120b89400030203066844aa404454800411078681e55950116614500801c0700320001d110040c900800448a8036150000c52415942d801500307440c0c003d405400c038008019a10054004134900c0f004c103030b0106401a014178031034107601b4103000b134084500c602d450701d00625030b4104464001694a00346075061000b00d80000b0f2075801164909060681ca980e03021039120304550003481d0100300c021619503128018582c035070205601c503100250003c1056004130743c0c140302d0481c04056464048210b90300754240e12900744840003810f8020b005000d1864415540890707000302900009264500240c541580c0e0f00542141c41181e00c045820001c12100c072000c80100781 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 5193478 1250 5192228 5192233
    0xd090503150408030a140a06060801090203070e0607030302090310020a081302010203180609100e03071d010306020714160f050105041505210112030e04150303080603010e060c090111 80
    0x700c22003030080d00007000d8001081c1140001c049511080260410302099070700c04001032080c18007104000082c8007a2042c5800305d0000130000808514520a40e0700c20400c0341c41c1d000b0111900003c00081da84002d01c114280f503824000c420301c5880070021108241002d600043c1e440c500c5c084003a10156004100134064a14254070300700507640402566000840110080600c88842000600a000d890381c82c42c1c10041055000301c629602c180380e490044c10940955800688400300120515802082c8a10600d003034401040001c61603401480c1e6180103640c1500e00c00320303030903083e428601250b040030041c00225200780955940007020400800d0f0900b0a64940740c0781103029820070346084013400c24840082070503859813110700158142074008030720a103015030b12401081140c444944050300029500b89a8980c0f60409100b1b0080300d4442c3c1030496542031441d5821620800010034243d0075548031071113840700040801009000780b102e06642a1150f810304001005000301c40503040055 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 5194728 1250 5193478 5193493
    0x40f0b010c03030b0406031401140105150403020f010903060203040b010504050106110a02090c04080304032604080a02100e0402040303170f060a0b0f120702060402010207080606010509060705150403020d090503 92
    0x6a070080030501810380e0500380462000c9005001500909040e400a131214114441c242c4d036000045d0b008441002100100c40741990303d4605003d21141d0141c1504900d2100304814000b5203071850b03a0000008051414007146034503583c403202640c0080e0303012221139a0850040c040c51406018550162115203040c1500f44514809540e44141c00d04c4040e025120007004180701004060484028060f400c04030307035645580e4608945026202c0030101c0b00134608040e1a1000007010040710100c4031070100400311445103408105c2d00c0e01d2020104410b018010f0400810703602d0f1400540019406034031036101c09910b000d050802d0b140f00521744e10459a00004004507941c4120107501a24040d0003899102d0107802c074441006d200355400c540c0000c01c1c14081208441e400140b1611942c0f003030b8203941a055464038513965403802926858080390040c000f0410b217040c000040c01e04540180d04640e030391103001c481d034080da800a0700c041c4c2c01a0000170364500c500d600684440300400050300100b098 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 5195978 1250 5194728 5194751
    0x102030606040311030a0204020f0406030b0901060f03022802070f0b04030c0315020d0204090b0316060f05180a0e041406040c03140307120f02010c02060603030304030c021f03020702040f 82
    0x58403480c00010900603810300c040c0500c0e1170402007640c0e5240c1c0500115030b1400100301102d00c0b038015105100000b41407200d066070b1824400d0303226040381d0198490110084503002c0550194000c5460703940c4100b03680381c40a019901c0342c0365115281b2010b40142c05c2890400b4000945103100c0d4002c610980e1b02080b081001650400d01402200d0f0400c2803d203001d80311a01020207031041c020704a1015001040120709200135612140c401d500440c11540107081200c0c1071410b00f0214804c0d04e01268010080c01221401100182142c03102441d0740b0340b0300e0f500d80c000203c0350400358000b050a0a56a8100810401c01640128290070264001c0c8110b01d0a903440003002d06080c040144514107141110449110030015145096886045200c0d019600320006000b40d0300c03014800015820801d10042c064000704825000d0840030340950314503a1151400e03140c000b0410720880c1c0010510301400c23480c629075102a0b407550f02c0c558001d40d0758074441c01080159201240f440031524035091600c4c41 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 5197228 1250 5195978 5195989
    0x408070f0302100c03020709020f0306040507022a030a020d05100b0a0b0711010908010c031b0306050913050f030307090303090504020f0904050901020d0903030b1002010501050105030705030a060b0c0d02070801020306 95
    0x10701050f140351540c101c01580c5000c034105410759000907440c5001003002000b4010b030070003071403152000791010852a982d0110880c1d450b0362101a84107072000d404501030b400c500b2140c5e0368044100c06800c941d41840c15501042c140f126a2400703840c07035005814040b2041c40705000e500028442100c1a00c82c00b4180b044124651080650003030509001a100c1c1c1e0082e405142a40003c10fa910020007440a4484024010f4120040d42c002c0710403c40201e000c00c0f901900c540020303075102405c0074010346e850030841c0d544441024002e0340d0602c650389440032049402c01c029803050390b0390b80e07a00d8903180c69442c0203084090280c1006100794018405021148181c038181d8131010011103000c80c25842c3c0001c905c1c0282b05101c0f5005070b84d070400380c0308024190980c0180100d500203555619038150104022800c0350002e00a05001420800100f5502440743c00a50342000c081c120001710700d0768850201e821944800c003081d4851700b009a00214194042c42040c00905115001b035246188c000700055 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 5198478 1250 5197228 5197249
    0x10050102030d02090301060312050304031202040b0702040513050102040f06020c1f0c02010c12050711060405010c030804110301050115030f0e0c010f02010e1209031002070213020703110a03050408070f0302 90
    0x190030720f41c003040401c12a90250008401941c0064695001c2c400441700200951700840b810f801141c3c00000022a001d824400c0300e0032240b4020000d400c0072055400c20003c0d09000d05103c140c465441802d0300421000c1c40200001c0540e100d00c2c064451a089003c1e04010302414918030601c05030b5168040c0920720b100c0e450000049103003840c861a114401a148651030700707005005003074041d001d0141141c000c0024244580114802b40e01e0246050030080781e48500e000f901d0000fa110a01580085d010300314454001c1d10441d060030000040c400070070b00b159403d91058a41c0216005451081501849103070205c4810324018051060046d1009943d10703e6032812074100705041103e82c0245100b03501440761050907a05035407911031000380055041c0c02035200c0c01d2003030085803141c0c8092041c1d842103604595015080700400307842070881d000290482c60041d0103008101c07080b004010814082c0081c000e100e44c0f111612507090801c41c0b480c14181341c0101000b0280c0080902c0565980004030 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 5199728 1250 5198478 5198497
    0xc0c090106020606060d090302031b0105011403030c030403020d0c0305010c05121f050603100e01090c0f02030a09050d020f03100e0c0a06140304030306050604030302030414010504120204050405070513050405061005010203 97
    0x3003001da071a07123012842c51150380205800c0f1601c0010041c015007040d0000c1781250081c0610b00c092040c0d010030980c032031080c00ca41e100c15a0080000700014200507800042044c000c94000e0105903881d12030900b07540d000a9403000007000094841d030800380d2026170350b4000c6d00700c000c410a4003e020b200d281d0801c120b40505407194901000050340780b55070840003c094001110b00b4065940d4912080014024200810000c213156034010314100e8400400d58464110b565112101079141034144100141c42038000e98100f600b050700000b203500c003084030381590045100006440107141c0103079424605180c250b50721448101c0020071081d507002c04e10313445842031100d085541e0703100c515003078005003116804540c1002011900106060f0044050012110100c05200c04c3c0c0c0c1c429401140c90f44180c0c000c2900e160104003025002d400c295220540c441d114008440d4400d403547c0000d00340f00c4800b02c1c104911901e0340704100070000103000c0640c01a05c280c0350400780d03604000c0041e480b4043c59404 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 5200978 1250 5199728 5199731
    0xc040506060c0703050a0c06021507030e010b090408030601080a021806031909080d05010602010c091503112209110304020904050a02090a05010e070c05071503110c0c090106020606060d 81
    0x314a0954900301158000c810b92002c84034156500c0c9030441d1211089070090310002a10600001c449001003890740251450303c8112030244e68020081c0d004024031228404c0641d42c80d403a0f0801c50b111481410b01481c000c1e06004d484c0c0c505180014030300400200300103481c50041c8001868400058071500c00128211120354582d41c0f851030654121508011076038185090911036400d0000c1100107001d211101c030018080c1c0d80c0c880c5800c1c0d00365480410b01c48000744a4500c2044101e8011440c082404843c0c50049003040c00038000000702d030000d010211110700c070705205a541008140c415401008020010b001c0c280e80402090142c0c040104081d0080b030080d0700203803c01038107104c58418158014800105414000030001c002d01c1300b40235481c014003004020920f824020310181036000d074030400a004513410075011010f13118009180105164403040c07148e440c1040076000d444c00340031501c010200740b0714141c00c1101010043e41700d81c0654102c042408903580302e10007111030f14060544c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 5202228 1250 5200978 5200981
    0x8010510030b06040228050307020f060702190f060609060807120503030106051b030d0504030905030105040209010303030e0c030f0a0210050f1204030e09070801050102010c1b1401060f0801020306030106060903050c0405 96
    0x1e9440e264505c03020810281e2800c0c42c4089031707150010040c5000305500c1c0e00312102034442f5213406d0b58520302a196100543d0011a01840c01d000800c039408c43c02c0d100d40f0319001410055601c2d1800d9548541110798011380341c80042c0704d101000c000071802003a5014449000303c86548615444c1d01c07048c000c070350401c42c1c0056640a00414500707442e070040d20007400c6070b9540c0c4100c00b54030001c0605035070440010310300c041c0004903894140604c902554000704906041e910b95542900145402c040200050160346a206003e40c1c1c144880481c4001d480054102c0311030700c0c41044003c03c20305012400340b040500040c0c4099001000f900c1640b55201c101d10b40986036400c01361003d21220200359800400c0b1410000c500340c0c80252281241c4007a0006c0c0110729400c081958040f500340c0d4000070211030080071740c000c1986d00040c40c03903407200700e000099556240c0300148001c549035002807203180c0d000424000d50742400d1140314020119458030300003440c00c5a03180e40d2503440200076a88100c5d1281e0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 5203478 1250 5202228 5202247
    0x6060117011a0c07080705040605060405011d040b030f060901050705030f070e040209130e011b0203070305071a09030301030309050102030913090302010b190503060a05040201050301030210020a12080108010510030b060402 97
    0x1403c448200712400b04072014203984001d1030782d50701c800340606030245051a0001459040c540c0503101903c9058440101c0d02c01e03044c02c2c07916404070307020710365078802d0b00c946000c00745840c04d00a4a40c940d034000c002d0180d0303190440d1114203484016003503008010040081001c4000c102c040f0320340200d140e10700b05000300c1d0440d000501178020040010b920040d074000c01c0706003480581c40441c181c850070009102c908400b0801c012482441d010940141e08200040000284940014508548146003220040d062003503c2d1501800032504400150310010051083c9608130803500000d0009200443c45c00092401203441400f45c2c007552000c1d140c690034000f042600079003107084500c0000e821160004030700c2d5038501904440d40700e05800b81c0180740210f52260450300410b44180e03010b07160503213540d10715400d01c0b03d425401641902140281050340d80028100001c102d045840c50391a001c065050061351403c454002d007002d01c1c040c0354a001000080c00d4518440d0b480751044900684030707a203c4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 5204728 1250 5203478 5203529
    0x1002010e06071d0904170f0408010501060201020c0f010c051902011b0509040b0105030606120702030c030f0301060801060e0a0303050901030204030501020d0203090d0813020405040305091003060501020606011701 93
    0x303008921803405400e04010701580d12440f10444801200c00c0701001100010a1100a0b503007600e0140c10643c04100038921412480010071a2080c10041c06103407654441465086442c2a044180180d400048011050034108120744851111100030040380c000c83e0b0020304548a41c08281c0c00c03402c1e01c180908103243c000c1d4002c002c0d080201004140d00250030100520310b50001d00c07003d2046280c20b084900d03a500c2481a00e110358005859549811105480408902d200829800c2103210400103503c030580309001910081d820764000a4895052030700181c1107c0301600007504114140c80c950030659a09965002140d401d410700c0da0751610140f004030b001e0f100d1a0030180c6a90700015403000410403030703070045201711000c0b0f040d6520b12102c010100d55118007660101d04552a04c0000790140c9419030009404c940300e804c01c11b1801d1108008100b2042035110410b000c00c0c4ea40d08100560358052020a520010901e00040362400c05501114080010302941549624506034440101c2c3c10 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 5205978 1250 5204728 5204741
    0x314160c0305040504090b07020607020f070b0c03070203070b0301090f020711010c05160602100501050102010c020d0f03020d060b0c0708010c1b020a0506070507090c050909010902090103090b07050a17040b0105100201 95
    0x1170301c240101c02e0b00d400d00b081041c40c183d60610040c8038440000303103d03032710103d0b180383e1071800d5401030246145056452444c036000130b00c11a520707010410032a030040c2d50820a0034000e0006294058696140c410a07504894000a4155085004201e10f00000b0700030081c0035407000090030301c040c000145040c50b0703103041820080c0c002c0000c2c00700c0c4040b036202c1e000200e28240c0101080c2c24007550f0380317400049003a942070650510159005c00ba52002c114098000303a807018455190041c2468890509801540c400b43e1045040074000114032800d282c043c0158806854904000d20801340f81e04801000101311049014440250304400130456442d4151072004020007040f145c0c413060a8107000b1744441c080c2c8034030024549813102802c810b5003c0c400383c0316401002840c0170780341c0e0300e4061040060761141405504050781d52000800149091040d07500401e03a594a0070340314040400054082c1c00503511030210b16100b01c0030040090102c3d4085419101d069441081402c1502d006070301400f207 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 5207228 1250 5205978 5205989
    0x6030209070201090209060a080c091806010303030c020c011403010b0904020403020d0302160e0c0301090209030c13020d0f0b0609060a02030c0102040303020a02090105060309060109050903070804030501020a0314160c030504 98
    0x41500902685960541001320074038002c03280740d02c994036880200321000d102482043c1d40fa401c200c00000301403600143d4590b1110a580d4610702d0700f01582406428610242c00407400310f42c0e0f403000d0303032907483d0704002101e0300c003c081c244069400800002c407805400148542d040031600050320b00e250351205e40540b002182d018003a07184090407850041d440e64800c14144410340b0030000c0026110140c0039050b401500748681c040d14603400c00064030702a50101d5030080e018410808860520344800328125000c80f014100107031602c0460580d1030940f5071105909142c6810400d6003d469541c80045540f0541d0440342d06550b800303001001d80c1580907111440649500c049070000515401281285c0428801c4a103c2e10070b80e221410031903540020386000406502c00c42c014481501d10764031003504000c008007200e042080580d100040d59020783c10840b420303500441d40001903505400b6210001d24500300044d514a4034600300490008030302c10110800c216591440b082c1400341003110040c01 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 5208478 1250 5207228 5207239
    0xb0301140103080c0607090308250807050d09080703020a091a0a08011e05040503031605041a0c010c030b0303030406020d02160b060f010203040f0315021b0f12030105130f060302 78
    0x10b07940d0806210f0740e0040c0500200d00d000d5035000580780c0d8400d0f00e588050313a42c440d81075800d01882e504403424100580c94680b2000d00aa600704005c12045070140204611a000606a024000400422100caa5400040700d0380c4030607000e20042e40d500c1036550035075111000010300c00c020000300a0902d084640c0181d0052003811021070203500642000b0070704c1c2d1500740c0150304ca44040000c482215000c0f64080c0441e00180003141002529040a15111080b4901181090740320a05c2c41090380c145207040400c520300044200c4208020b0181072002c0b020303420200a4021400d0120351a071000070001802250300042e40e000800c1e85a055030740651214810310500320441c94066841c041c00d4a01a2180a010110400300d610020454058500b4075000d044054074580d00e25820541107500d506643e90240810781d032440514003d1855000c010008004440c3c0120381035080909000c6070a031140802c00062049490740006003009030000303240003c981d082402c1b4400182080d070002980003 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 5209728 1250 5208478 5208481
    0x11031905040f05060f04090c02070801020a02030d0509060f01030305031f0303030203040233180603090c1302070c05060d020705010c0305060f0406050a0e06060d0603050715110705040b030114 84
    0x556010014009a6400050075402d0340c2e15401042103070301441c02c58044403d020801070040b16202d400a450041c05401121b240e55140d034007003400d9800102d0891b0059101040c481c00d414014040ca5030401c2c0200301804403401c1490304000381501c140006424082c2c00400b04d1418801c1c0c1603a401911050450418086d859290040195105940580c03003400382e520310390031006c03620605070a190703d0f06034140000508907070031001c00e4120740e0b1400c030303019904070b0440040d40701c28008610030303203490001d40585041d100c10821260625080c070800700748140500c0300000c1c07000840e02c0a4410403140b59407501c6000c3c2d44403001c0d10811800030059401c0c0740807041c01c076815400041c01003a003280e080d6035190022060104445280c4a09507000d1912441000890b141403090313900010064406886c1428203100c82e802e0300d00c55481201c440e48517440400c02894907181030b680c0600e15117011500c14003002222550340300580100c51185581d084081102d0742e09602902034020407100c10a1503 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 5210978 1250 5209728 5209777
    0x406180c150305060916080601051b0102070c1a04090b0a090e0c01030606050903190606030c030c050306070804020d11010203041805060a060c030903030507021503040f06060e060d031103 82
    0x2403104001d40301c0828280b03c00720740035141c212201c07480f500f0450300513030311803000007070840d01c80710040d0401c1c0c1030041c20881c0c00d201080300d1600780b03c10b0318800005a513070601442c0580180c1c890350300985203c90701e050807402d0f00c0d99840c02c40741201c01420001c1140700d49400040c603035581c650700c10a2407a15040e083c500c0310501040950450000340ca0802c1416035400042d0b0305031103220500c541c1a040310140d001d600c5000c401c89507139280500000581d0b103840b507541094880654000f81c0e40e04261030b80802841ca81009000e90112451a00040d02d04003a80030400f41c40814400411000f4644031001944c2d108000381c1b001410705000c0c2c014001131420030350000b0041074800038000c0344414000b051082c0100c1c644102c0300d40c56510903489519585040700e03950842c41080b40d000d1550b202a03003d550324140a1400381c0e0084002c041d12a00b103241038800c5806030341c407140402449404001141e82c803c01422801605420202c141c4024001464110310418903100c2030090040c090450 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 5212228 1250 5210978 5210999
    0x1f0506090f0709030b09010209060a0203040816050f130e0601060c0b0a0603080313060204090203040809010314010807060c0305040306050f01030507061409060901050702090132090406180c 83
    0x41100365181411a201e410101aa8450071125080800c40603401000054107141c1455400038109000500340094040010050390140902d0401640007080502c0b996800b030028460794645103890941c0d8601e80b00c00b10f64109070310807549104da10840304004c40c910b80c40d00010440f01d158016110f82d507841c5d12001d85800e9020000750381040107140020310408091003400140d80e000a81182969105025492280d20352581100d919030240030015800d002c40c006140a40c1c403403810a81c036100f1120004048508003840c88001490700401009001400702d100c0080d01e49624005082040f43d080c159641e109951000b0021807500c0300300001e8201c15000d0700c2c180c034801c0003a2000590356000440d002907180300382e000500e00c00c0140481c80c0c58400014600f600c0d0604005040202c2c680000341000000d0b4068031300491680090030507208104c200740a03c0c0d40c10070030051207440380c102040c03001d607000300014110ba603a56221130815406401c11070605500140f6a8a81600c031051500c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 5213478 1250 5212228 5212231
    0xb13051e0402030705090705070501050106030605010809010902010c0204050a020405030a0501020901110f07120201120e060405010e01020403030504050d0206070f121b0203060604110f040603021308060705070f051f05 95
    0x140825103418200490380e00403030205005640040c01860041d007410100074502c2006807180007403210400010000810a005150003050947c8000900e0303450500054014480202080c000741d240580400c0107030b82100c1c0500e0701c6038041d50000361035030f40e00410a00038031454224551601c01d14240a04015054005100d2484280d90390060481d8a007a5039a0340d0005981540c11600009014422004100c00e90407000d40145041640500103650505c201d489206203102181c00c454201303c1800400d0145519004600c0c000b146018515140140f4a0003103000340c510a03120500c0300000e554440c01900c071444e03086032003002100b03014502480d0b000d0000e481e11700031800401c90040012134400c039000503282c0280251070303503684400801c0020080c141c41c00107a8201402410f100d080c0410241c0080c16142e2801681e80c003003550b035094804030603884801e542e40a2801c10008a500c0b40540b1030880e8403014416a4000c2c034640780e41000c084030400340d803001c0031121403400b05500d5007106 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 5214728 1250 5213478 5213491
    0x801150905060a0b0c0a0b160e01050a0e010c0f080f0301030b06030303010513050601030609150810050105030d0c110603070905040c030b0303031602120a0c0b1005010c030f02010b1305 81
    0x1422103503440c440d0106071402155810f0380101800c900b041a602c8400040c20341281141c140d4444500c0e680d20303144190001d90b456209107481030b43c1448603c0e0071480d8522201001d08106042184090000780600a18566581001002505c0500f000b60903800010400da20100182c0c80380e0441c5e88481c2590024030065581548510102e00c1c58200030080368141d40d0094001c03c401d00c100b50f1983d01412000c0c0c0413504040e40c80d20300282100039481000e40154490300804811860102514a81905900c0c04a201489d10004004966000400c1e0a0a200354102240c0420b41401d03d815580c041049958005070000204410103502540140540b04201d40c00c014041c1c44007811011540b80e2401039406500030008120541003c2101180100042c81140d09110100159082d039400c94140c01010407004003a030b2040211400d091607202c1142040b01200740d16000c0000c00307943d400b100240074005c00894400031503100b90003819412101030190700c0c240303160704200700007440200d440c0e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 5215834 1106 5214728 5214761
    0xb09040303050c09040f0501051306050d020d020307030c0b090a06050a090b090409020402070503030603010608060405030904020a0909020309100c030c080a0203090a05060f010303030605010905030d11010e070801 93
    0x7000c0c41006c00d0740002c1030a52501e400d100e40b000700c02c0c01045900382003038403c0c00035894404a11a2070340d0101c3d01e8000a201740c2c00402d0a051b8140c0002e00f4a5140d004003145004d5810014810040309403000c10320260b4526085039240240e40441c1c00040c42180708000e0003400801602c21000700500016904580394000b0341283c0c4042030417510380d000803040110070314081c40745c0d8000b00080300103440d442c50140d490f15120310607032140501c1658003152041d00d10703205591010241a01c900110360342d00341901001c1da2229030b11501d6444600b094500d0513081d1080c0907009001c205071b150460700c0d85440075581d01035000100ba0b0200d62003855115404500304110142c0100c0709007101100b1541107050003403e032032131500098140061190100b05948000507005030403031081c50f185e058007000c000010b0150080d80c104481c94400d8031804582d0041c194420b00141035050031 = true := by decide +kernel

theorem cover : BRFrame.Cov 5035978 5215834 := by
  have h0 := BRFrame.cov_init 5035978
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5035978 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 5035978 ≤ n) (h2 : n < 5215834) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
