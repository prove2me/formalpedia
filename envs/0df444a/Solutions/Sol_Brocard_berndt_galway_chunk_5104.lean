-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5104
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:45:42.545775+00:00
-- url     : https://prove2.me/submissions/60ebd0db-3317-4adb-8544-38193d2b8055

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 917805755 ≤ n < 917985611 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 917807005 1250 917805755 917805761
    0x10051c030519030f06031b08060112030f0c02041401090c0302120a020714160906212d12200a0201080403170916090209090a0e030702030304180c030e0d03 68
    0x246031030900d1346581c4081d4000e0030b02d120f41030056000c2e0180010314400701e814a91440c8458000b010180c210400500c02c0102d2031024103070340703030349840c289036401c007010400c42e01d044203040300944c07080c100502501c40c520252107c6040c0e840000301009080340c0341100750101d20544080714410a03840f00003602d1203006074058495240102140003072001e0a00d9214203207103260344e1261603116600320a00c2000e11a02ca80d20280c080c0e5a01c10100e4488006500d0030702c284120014400c1c4001c07281c030a01d51003441c00158001d40311000c40707090300c591403918111840880d108200000d14501e400c40300244404401007591802201508110805400449800c100100280c4c03d025203034074852581c02880901500c103182d000041e140380400200d22901080c40780c1d00c01500180144807920756643c40d46006900070b00c10200002d10700084001060850044045c0654540000b10700018040300b00c424403803041d580302038104807034034905c0c0080c0c0440b02075007000d4005d070303100300100c40c131040c0294 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 917808255 1250 917807005 917807047
    0x5061804110d08040603060906061409240a0323060a0b0f1306020a0c051509091305061914010608040b0604200a02071a07240510051c0305 61
    0x103422880780c0e4030a6203500f00c1d2540030750302a00010b5901c0c181049108040e200f000040c1030700c1d24150100c00c184503030b0f1099078000e00c1850f500c584130340c0360060703940036691580f001955641101d95071154041c24020f0024205401d00601c000d00c41c45283c0003100540513801e114050091140604038104000107030240c10241c0740f0350700d0a0082148904880150304654010802540200b44c600c43d01d1520b1250070035154404c0d4015170b03840400c816a010792400340d0308200815516400c1c2c984d69000f02d141c0c90b02c07007080003800c03d00403d0244402100114020701c402c4003011001d00c0031181c00da103550540c80e02407007a900014a2400440c00250b0081c0065400083c000c0001c90503009280c80900c07444104024401c140030000381d5003440e240c05001d200b00a1200740c0d000541c4030804111301206200f150401400365209a0781c1d0012200c2840801c0018036816508100620308a99201580c6000d4029079200301c5540f14110040b02428801140132030303043d0b488a08040c0071504202e0300d80001 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 917809505 1250 917808255 917808259
    0x308100b0a0f051653040b040b0403140615010f11060703020307110f07050d08071a070809061608100b0c0607030507090e0f0712140702010506180411 66
    0x8020035150b0b10040c11203140010701481030301803171440b03d407044110703600d164000e08602000061080c1c040c0c0c05541c031a0055003503038a188280b001c0043e1030741030103200300e401c680c59005002c0303804110001801c2c0a48144d920804241c40d02009440120b40c1e50340045aa149000074401040802c5500c00d0030799801541b241e042c01c0940c80034020603141006030844800b000280d01004214603d51300402c903e00300681c1202a10075590000242a101c03e03e5004150140f201d0001a01c02c010400080b51040e03a00014001603520a01c18550072340d54099412400281d620ba021607003e0700c0100741d05014042c0d5180c031003550054580140e0340c0f0f8100502c3d41c0b03481c48045030300060b0000300000400c510144032002c1c10715807808090150490ba0041c0c26001009803404040c00308100307800c08a0b8000000c204801040d0391014405c1b030b4a0340000b80420640c2d420440106d0396100000d0586004000640081c40155038030310910000e49006c0e241c60700c0351407241000c10045001404451812140 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 917810755 1250 917809505 917809507
    0x31404151d01020706090c05040606050d0207051207050d2a0f020301060b0c06010509010e090607140f280305061c1106130303080604090c0b160b0c070308100b0a0f05 73
    0x1101d10481c00c90700b02d2002600c0c9282c4441e4440e040203072107510b00c409050110360410915013003000080450080c030541043c40350b40005c401c07041c880c0810880561424002d00e0950b114a1440d0591b22443e40b401000c01051100402003a0016115000c001d6814541880c07180c1c0111503c8081a0b90500740b800d03078155581d00030116a2050040027882070112810017854203526100600c1561401640000e1a903101c107401d1101041c030100d5542d4100200d450841960143c0c0c007500d0b21148240d010f40d8442701d0000440300290350000c0ba00381591008910703880c0e80741d80c400720241d056810448000c0d03030203000718003035034091664a580d0b05540c1e80200c0c01c4120b54140807010500d60340c85403080c4001c2000d802c0d410800c15078049400c90b480340c4203032000c2c0b040780b144d40c0d1181c40e240d043c1e02a1440749200403d0001c001e400d4403020f040d42d00c1d0400704a1086040404050565500007002507002501c1c14000446000101e8a00411240d25444080c6850b0740507208980444c4440130310310410130 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 917812005 1250 917810755 917810801
    0x611060903032512061202030c03063306041d0702120a1112221401050403060e0f150901110403020603160c08030106120c11060c030613021903140415 66
    0xc1c0b51700c600409886d80c40c4108549803a5070041514098448200c144680e00030320400528152101e034103007204840e03400541003600c0b0b044404504880809040c0d03000480032a00044c10000314050007083c4050245112050315528001ca8036014a5116801110340c10021020060320405e110500020600700b95140000866441d80c11907004d04848002d41d2401442444201c911800100c02407416441c10301030101110000391950045100c00f8160300e40d6280000c18800060040b02202c24120066800d0000c052007251024a015036103030000350720f0300d00724103014046842201d0540750001d0034581140e880b01c1119003804944542c1c2807c000345200b2010003c2e420750f015501800c0c20f030b1154841c42c0480c018a0080707407000c0c034143e1300300306171614150708600300410181c4d04038843c081001d9a0360360b003002090300c140c0b01c9002905c00703c0c400074011a124600c404018406400c65a091140307640341000c8441c070410642d4081c119080d68041c10500003071552010403039540c146101c111000c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 917813255 1250 917812005 917812037
    0x31e01020d051e0106021f09080c061609081f0510080a030509030c0603280e030c1e0a031b051e0d030e03031e0a02070c06110609030325 60
    0x320169080791083c52007500380b0426954665440d4007400192008080808005642c4155021010304003500582d5030440c54051180080c1150b42e8003002c4000c40b20b950400100f00e41e0000782c1d0680100000300c0c4106c02180b998030100d000040c0046100d030030100300030f45021220060401600405440242c02c0380002c0c608414003208907000c1c02502e400c1c0e102e84d20030b014141003000d1205403038410a020010842d07000c3c0144070700c000640d84071898501c0000c2c40d4840c00010610001410454031012814070210900024000c1c8003e01071a00352810300500c10300303030395a00000c10004010030140c4584240e0940300c40c036824072640c021812120410340078121020060050142c80380d10b504103000103a9403503010700035090b115074000c000758514030302824000d080d055500b0000e4410f00109000c207680c1e12598043e6000c954000c00a14452a556800581840744103142c880d80781c000c2c0c0300064140c05c1b010003524410018250300b0250034030100001800d520341e0340030300700622a241c0b03250304900c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 917814505 1250 917813255 917813261
    0x8060702060f0603010501030c031119121106030606461d030316240506190f0b070602070c08011505030a15230703090c06020a02031e01020d 62
    0x5a095801030001800d080aa541c12040d000b003542d4040da042c5401007000405500c209800c0b0307a0031181c10003894580400192840c100480340c044bd03c0210080030071019030042d9040d0300d00748541041c0d40034000300c1c001d000440c001264400d07070000c41400311008030000c07445c2c4c000742088040500e048600e510700380c01c108609090080000c40310840b0300c0740500e40d04a100982014a0708004103400700b410800255288250302100c1e0080e0450500302c81002003009072110000781c50311510a1042400c050b140080c5421541c492064147d01d15400304d03205407098540540f40388200b0071440ca81442240c3c4007682c4981e01c100c8840768200412008680c0000c500c1340a407000900124002c0341e40000501c40d44119006a446500401d607600f000414039083c00c01d80c1030500b60040b800080041c0c495200303003261001001000e504c00e080007022a0300d903000250580c8922021185661945800c80e600c03001410000d40503405505030350207149808050914801181d00094501203030a11b0440c19 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 917815755 1250 917814505 917814511
    0x4050f0a0302070303032a030b03030d0f0903031d030702040b0d02100c020a06032901020a0803090a02130501030206120603210415030b01140703030612140706030501230a0806 77
    0x43c1c014103010700406900d0f0084010b4041c2c8846030f018000a41d990002d2000002008803081c15a10704145045032400c0c0140d900040d0404406c000d402c4084030078501400741c0310002c80001e490903110306d0400c007050080400c6440c0c010000d5081c0312480d03090000030080000301c11391200d5012580001a52803036401c03020020759944001840400b88144034403c00e80c0c0d0000c505060600403129121004559444990600707000b2010044c484800180c0c209622100041c01500e0000208111800d0004040b616648250b41281100d4011890031040300c400307000c000e501602c200116007860703142002e6281c115000a0070384d044080c1000414152580ca10307107010304038901180c1003180710a01c60301c0900b071300c0c0e2a0a0038000407660304002003207403c0b0b450640d086650042240c00505202c9d5014001505109a1a1014148030f0404400100014040046602c07490380c0208225101e8010541201e582000d05031a01c0c0c200240301d660b00d0912803140341c010195600c0007034204001c02803640 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 917817005 1250 917815755 917815757
    0x804030c080d0912050c0a0b1305061608010501170106271d060306040f0b040515010b040503010f2009240c0601080a12030e030c010603030906030e07031104020304050f0a03 76
    0xd042030f1289400b65a0030744005602050082c00d000132819030b0700225241e0310450303101c110305010303940784940015401000c4070007900500c01e590030880030043e840d031500c103080d20300d07203821a542c5c5e40c40f00110381c1d8100d400c10480034901a0307401004083e01805440083c59040c940c071001615070040042c851042d203621800303040204031004106000400071040c1c100000340d003d0100c903d015103131608102c22000004004da020b91000030140325061041c00e40398510707603000c221156900d480c414001e4200313000d46840b951a003001d9100c1480c01d4402c04c2060307400c20003681109603803c000741c071080d0464180103400c2441070103001e007411001411418180020060941c54011001c0701a240c0803058201103103d901004006010070240c5581009200d91460040340150071051018113500510301038207134542c203000010040507007000f0311701c09950f0030b503408006580d070802c01c00303076a0440d030301c070280c51034000034020b007070f1070034035400540c2d005004d10100c4104404030a121031034000300000c00c1d4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 917818255 1250 917817005 917817011
    0xf0409080a090e130b18010501080d0909051e0a0b0d050d0311040612050717070806040c02150a0e0304030506151c05100905011d070801150b0403030804030c080d 71
    0x54606402c0400d00014120342042e2070b0007464025021401096940030113410740c00c61500190800c1c420f22030809822190000a02155958021103945e4200c034100c00d034046210203401152032159840b482c6d108094151000c5800704101070050b000c0039010740031024054407080c0e090005c4d20346015440710355100d14018140108070384001800c449540503803562004080004003c459800001c46480c0c0303103200c50000e500d40364500295603407001c080324160306900301010482c9650300301d0b0a40303210301401d590900101c003d10700100d032a030500b22100007244904d200410104152948241042c0c02040c044916003920780e22214546038044850549a440404400d20745041c00c0c4041d1694640c1c1c0d42814100d510187d846d05d403070b80e80c06208019099604c0403400705215094100903001104000704001c4d0f80c034501e810540b5101e103400343c0e451540c00c0401d265400c401790a2003404464000d0be5142c203040c113513030781100d514a000d031064081042c2e881c110004529544005d043c001c141603400 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 917819505 1250 917818255 917818267
    0x30e0301060503070f060e0406120302012301080a3503090f010b09010b03060a05130c09120b04030f03020409051501120506060301120201050705010903020105101205030a0e0f040908 80
    0x5400c1d94019000b06000e900210810070600c08603103501403d03540c46003800e10060ba07110010800514041c0d019101d01070404c6050300c181034040d81700e518021001d02308090010381c0a4120a46103900303101c1d0b00601e03404a450540803541490030076202c52188891080c00d1030001f00d80f130000c010b00390a0482e292000000b0b006130104200300d081c0900d0100002401114180800101c0200c0144100303003060b140000051141c0d6510304002c0040d00c070083c01120b000c05034901110003072540c1c400302c40100c1c0c4941c9000c1009131040303102d000d03940e9110716801d8850780c0702d507802c886a2120170310080a06d50240302c0401d0020081c00b400b4425000c406900544000441c001003007144000000841d10303103007400b03000154550804aa041d00d6400d4808141c040c09840100c9035071140c03181c003524651800440104040c0d06401003400b590ae0245140c090301e4030b690b4059040003a58a000700308c0c4d84104861902130740240e0390360150744401403203800441d100d80e02060644010ba0000c98206c1c0c00005c0c4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 917820755 1250 917819505 917819509
    0x2131e0909050c090c09040f0204090605030f033106050715020a0816091805060a15020d030f11030a0e0d090b07060e0718020a03110702030c09070219030e 68
    0x1100020400e44a040c40156901d448140c2c6640c3c030010080e000303146140003e6400c14070101102c0c0418005403003089203107002000340c4002d40060055803000d07400c100c0006020300e0005540000d080d0a013020b50b00e070200051800c000040307540c6091822125800c50b100c0641e4440306407500070002d549403103a480700b81c0d1034402030020310303110b4500c00984144081e03440242d100100550084c00302004010100769008151444540d5501404800134081c41c000c011201e190130103806a00f042d41c1030f126003503e07840c041d44a4080719000c0c01c01607000d6041f5203c502e1294100c3c070b44800c980440050403140040e0b880f01c40d46e01c00c4500d43c1180d600c8a04010311103204110700e08031800180303441e005290400500088600c0360002c003a10454981810240603482030050744010103240e6006040040f41c03052500103504110705403804a454400b200b003684401c002155803c0303900038050b004a400d1082080051400030305240114440e002d500000c40c10001c00030840c081c06515492800e103040700c2 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 917822005 1250 917820755 917820809
    0x9011805070804110f061e0919080d0c0213050106020d0e01080c1e090a1e08070b0d050a061a040e060a05240c0a0804030b0f01051c03030213 62
    0x4424410080b82900704004104080d134202c518050440700802414900d9001801500036024483e001800402c521ba0f00325418000410300e8000c150b8004420007010040e20184410360b11840d04960030202010612a1261112002d03241c40102051410042c400350700003240c42c02d0f085100941c0c8203c1518040c260007000d04010598246825400b0345000c20722601180100d40710346600d50013217030b4090304480e88102034607072546c8054424110244e9505d800d0004030010b811400341030741240404600c0d44c2c0081460001d892100140901d00814a800352000300340040a070003100f5134075a008030b41c194889400d000004842868151038608240b03c0092082d405009284109404201089161a160b42841c0002c0c1000c40c40041541024055440d47c450540695454020b40741036a0401a03a00003800689001d0303440307140940d0300e00f441d40240c15001c0c0252640070140701071840010541069980d512072184c54058184509c5070426002d40105400004244200e4604008134441e464 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 917823255 1250 917822005 917822011
    0x501031401060e0d0614090a02010809011a0d0f0f061d0703110402160f03080403080901021309050606070c030b0103020f1816172403120301121109011805 68
    0x40508200c65140800103001c10744081c009038091000311458500b03000056209144030b2443d140c00e2141450b016240c6921615880d134101d011410b003202103608114141300e00c654007038510648806c05a29502000002e81c1d0500c0704682c0e140410408100085894248010452085001080c2e8030060106800c1100c100300c0054601c1c2d2054400300045001c0758a42a04800300b62001603a90340003000710280082c20481c0640803a0400c544a001c040e03014500e5403140d4000d696042507500d501000c1400d0b0b100d80c4820300803140d00c007030040c802c0540c82d910050304001c0082c0040e16042c0d5503aa140f042080302c0c1d10660307510b5a214010405c0d41000d00c0d58150075041103c070086000141402410420800b0308407010200320814200b4046006690300c02c508401c3e0b010b2824203160045030120919107514409078000b6000020405c0ea0138005903081400e1901c5486904580c01c2c034103c5200e252030303c8010707605010603580c00d00c0d580e2202c03c43d00b4040c0501500369402e805007814404140d034009 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 917824505 1250 917823255 917823281
    0x1050f01030c050f07051221060a0e07080702010b0d030e10180b03070504090f09060b15041a04050a0e070212190507022b171e0a02100203070306050103 67
    0x1c07038442e440343c2c003508032600151130000c07007a02d428490901d94036140e07104128843c94040058030406403a080d006a604000407103551a40944c4c0351020b00804041c2403003a803080924000100f41c1443c01540940e510410300d00c0000354401c0040c0005051071030469055000c00d0743c960601c2c14a04050040804549590800d007540f004a6110019803100c9403065108d40300300400440c1182c5e00c62030482d00201001807083c05680c0f54112a68020702d1440701c2115103600d040c3e51040070341407030030240d11070018a003039250401c0d250402400050b100440580005201040003003035603a6440040d801174404403842d902c051421800281c0b400607050303c8c89041044c1445220850111182c0d002c80704e0180d442e019884002e50b2011812000c0800f181c1e84c1c406421680c00c00199400000c2075a82c6800340017102102032402885540780d2107500d8407624412a0021440c5031403400d14010031080356680f045402c02031841800c0d10481c3c02c1074990b400042c1d19a4800c100540e40750080c1d4103031440c1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 917825755 1250 917824505 917824511
    0xf2004031b0501020c060d1509020c2407030e2b09060305040203120d09061b0207140306221403090a05040209100f03180803070212070b0f0a2301050f0103 68
    0x500d00040d42c2d40e01988178881c840d0703000240c003078141f80d00703900001420380714038460b9040c0c1c44d04d03460240080d40204802045512400124540342c551100364010b00c06c5880d0034080c2c3d01d403500e100c102d0103001101590b80f50f42c8201821910080350030070368072200d41d080c9050050f03541541c180c000d002d50180d03800701c4c0426040100b4040540c0e404510380c0f00745841c2c0164560f03506030085444025010380340b0003070500f5107030040c100081c04030051001a6641d070303582030305e40030f540740d10704400250b8007a101c6580542c4110009020200300b001d6100400414041a09507041d041e82d42d003540141c4414501012380010a8284d031505004e801c0001030031040700c003941805c00c01c40c08030301e501c05a684603004002190b008201c0e450f000e076102901d1707401c0b00340714411b002d44d140c24070140a9105441900c0148541115003801c0344a800a4411311036002045c842281c4800003019000c900140440d808150b403050078007406e240c00501c52842e0a0320302c21140c89980b41008000316007a807008002c6c14141 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 917827005 1250 917825755 917825759
    0x241104031407081f0f0b040207060e070b120f150907030204030203070506031312090b0c150609100b2b05070807020d1202030406020d020a0c0b0a0204060e040f2004031b 74
    0x491031209294030802000c0c005014005c01c41c402029150800b40550068400140c0c6418032201d908103c4c11101c210b8201e4000c9a618a8201d030184200b040c1e40340c400b0004000700d10b0140a5801c03454020b03194000b505101103c0c180010b600400648007840404d40c0001c0030000c5040a114200043c0800c031042400c6240c08240e0443e61900b10034020035900d21800c4030080280143d030210054180e0a075240d88945001d010603a48034626264901c04051401c0010054680344000d944904041c450f0b41d1900b62500c3c0e4119100c0d00401d14024105030100500d11500141d00103000060000f01804911801e0009014000c624090466411908105e400080700c80d080741480c8072001842a0040c0d60365a203007020301c000e02400001c03090f06400001c00208441c0e00200140c64203010340c1280e034890f100c040c0040b04070f1190703124030f5002c10705007484050130789455400642c600086480100d042e03a200303080d202d9086000c259103183c4d1031010905005000303407001e0034001c034543c1c00c810501080c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 917828255 1250 917827005 917827033
    0x1a0711010c0c1707020103110d021804050702120a050405091303030c0c0302030301060c031e020f0d0c020a060f0509031204060e012303060d1203090215030424110403140708 76
    0x80c403502d022603c82500060043c0869210358004040180030080c00342d00ca07105130309480042c1d804002e0080180d1051482c0307600034a014803400d80140e485070010070200041c1e2072416030682008100c142440014000050349403260000706100708203080e00e4541d4203d09180107021141c00c0c90308501002005280000060380000403241516241d003003034109a180c910302180d194500c440101e105441514917a940590009a02c0c96012005d0381075035024030300b96208845020180c0e00c060742c00310040340100602801410f041034080224609241780074003034800f0034078100011400c1c0c101503500280820001b85d00c0a91440d1801c400d1038002c142c800301489182c420760980c01600c101500020104159580701070500e140150b01c07290190040300c8541d0068018407600c0320603801600c2540e0410380b02c0500104480c4110350202800103401c1c1c1c080b022103888182924552103865031441360304407480d19407000d00004c40c828030032174480400440c299824100c455204464503030040040c140345c0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 917829505 1250 917828255 917828273
    0x51302040c020d090b1608220e070c0b13120e0906150711030f060a27051e070506040308030a060905010e041502120114040e0f191a0711010c0c 63
    0x19030341c5146181c6c9440500700345404490b54070314002e10740140020402c1d0705103d10f413150302d46182c0c0800301d803036116a503a40c0701108c2c000c12201100003c5100b9481d038000351903030f02d94a802c03815039803c2440070811556840843d00c04c0504210128070680310194082c54281c01c0180d02200a54450070340d00500c0e80400c240e4012410b006003054580c4100c040329840c10801001700150040032180d043c01e210003000010034003c55000780c02c603a5a542c0c21810504c40ca40c0201542e4080d0017400755145092404c2c50303040440038006154010814000b44031baaa08c2d019101960141c07001d00d54a06124690408444150380300d0b03640d181c10700e07004201c15409082c0899019801a139205180c0c2011401c2d04002e111300a60701c000c4000d83c5001040c02074a045c0305060000c0155410001d441260800c0703992041c0000d50381c41d04c1d07488904d102c2031300c54441074119580c070301c2100c0948000d01e203072070010126a0215042000210511211402c41109000d00800d4018900702140304420980b904140 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 917830755 1250 917829505 917829509
    0x60c0d030b040f090f21271503060618080d0f030e0d110c040506311d1011040504180b04080d150510031e051302040c020d09 55
    0x145552025404101c1d00c42e030300f00d0351003125502800c004c041503a01d807810784a80344c00800d1703900500d0300044a16000e02035101e03592002c020f46901c4900070320045030b4192160044581e00c401010b8090010f00410001d40701100c1264030384002c02c10030b08044005103a150125401c40d459510184100310f41200494454032140310b51400c401c03005640c0700c0540107009030340c241140e40d21810000c0d40c20143d104e121404091341040a9813401c803040401c010130760f10142d8106501990381070728511040100c611040413200380c0d8072116400343c0d003002c1c01002c851900a5a5011080e1014041d1140500340a420040c0300c1d4000300300018280c14001c070700d0394091401190300455540784004031a0900e207007401040c0c0d038004075034945131030319180c40310460700810740248000341442202060f9540c940c58501c01e486000e8103241c0404c90f031581c100d0261005400040104e180e480c540091a1000d0143c58440c500215030088001610302c1404112812405010210740100e4140f2104607402000501 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 917832005 1250 917830755 917830757
    0x1801080103120503271b0603161b060207300801120303060801051314120712031407170a021c0b01030e010914060c091f1407150b060c0d 60
    0xe101d58800784145c1d06140101200703a4210940761130a90351540010b002c48140b90500710210141c281c000c1406824081603c0c05c00401300c500c20101003951080100c40b19030602c0c1407d031402180300f9250300b0704030380c086607080e5010f40d10f10401c203034644504d021122059500c62031078010406418801080d00b007041c000c0ea0001618641c4c07010034184a40c01c400080d01300034000b04128206481d4041000856800c21185842c401011001d4208081007170802e802c0c0742c010042c945580ba03a50241c801ca4100c210005042e602c0880180442300e00744250320503021074507520b42964400201c41c1c01090000d041400c21401040001c81d403190741d80d6104100034503044045480b04031070005038040c008601403492345c2e40c80c08040c041407211104150712842001d00943e1141d440b00480000da9104000b401500001182041c049400110b8100608143d140c90703e14524241d10303900c00e8840d0301070034003592800c5006520b9040078501c0d109018042c50200e0341c00d843c040d4046400c0341c40b1200c1c021343d40 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 917833255 1250 917832005 917832007
    0x5120f06091603060e0a0c1d091b09180a0b0f0a0c0c0312060806090a11040b030304120c08071715010303080c1e040b0c1203010b0301030f02061b010218010801031205 73
    0x60716585e420040401285d03032080c41c030340c9400e4541d0841444d900103003071300400d80104500441d454400224179582c40502d1a070018111410343c8082c40921000501150b0741c1001750116802698001e21209032030a114a800c2111130402e074242c20204c84c0040c1c5081000b903c0c00ca0100c95440d040714070310700504e0f4103003800c012102d646c83c00c0b2070090185520a10113030148804100b09805e010480c0550680304008030720440001501340005c56076a001829056401000300b4800c100030200044201449100304024168851040d43d05102e20365201c240f150464000000d06400148489080717000601c0c218031081d17142da20f004040360405045103410180000d03a00f0480d01e5003081103800c0203051011503a85c1c3d43d51308202060341e8030044a02c0d425025032013410051883c44012a03040360310208a1604603429601d0f428034142055004030ba11003020810904006082e5110341c1109c1d44400005842d0f484407400211210012201c641c104500c81006000013007000000e0007080c001460b2407 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 917834505 1250 917833255 917833271
    0x180b0a1e0c05130608011706040506130c0801021204060b190605031e0103050304240909180203100504060b0612150301090213050421170c0405120f0609160306 70
    0x1540d0b03074400c440002900710706140740410800e800c840c0c658102d80032400c40344048250500d9554a070f80c0e09031001007413604801d012880c7c0004006807100494054426403034925624803c05007241e128404103400c9042d000c0400090040d02d03c00c4400c41c0300242c40214440e42c8a1194540e0b011540c0180030500c4804004036803001400180210358a00c80c51207280b00d56103a05105039641c10901c9188a42c060340c000c10340e610040079071407070041d8910781c41e41d0040e02e05180c01003019090200e1262040800410134001503a4100700400d80d074440309200045a003420709190003076826003168540207800c100b160080300901c6a1150794004007900d03a8108039132881c00000d01402803000e020b907101c41c82074502c20718805581c0c032250242d440740c030f500049400c500501140c6424030108140c080350f003513050180c01c40e00300d201c615407051000006619040e10340f030020b03600c0d026448104c49140d10001800348074080c2048802d40000815008100102003d415259a0000c0717000c01051643c5070000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 917835755 1250 917834505 917834507
    0xd1808100903090807090516050a141c02032d01150e030a0501090803190912120608010513060e0604020f0d05030405030a062403150e10180b0a1e0c 65
    0x10031001c2d204000c00e17501e60940d01c00312003001e400c0c00e48200c1d6403901d9030f001c1d49603c85d0040c1d044410395043c80c0c80740e00c00c3c13a241c261440c1c01a00080b000c14942003403550840c4052242d440254802e031140c1104030484292000c00007200944138615802040d0f01c14014001075445007044003101c88503181541c200301001c400b0074204004828002d002e98200043c1c00300304120800554400c844c012045000c04078510040f5041e02c0b04103001400703c041c23080c0e14020b0039202d411905003c04011402184040c0d0f1100032b02c2c2128001c5400c06107403030184d07444000300b206601403204081c40e0302c4c0041510b03042a40000b400d12050407a40c2c0c2c46000d03055100f1041240034402d840c01010020107903040b4000b282418006406212209031540c4c110407136050311030b101400c8441c283c2c0d42148010001c0c000c14812040145594031440d0050710900b024144030403c180200d14024060f0604450840c1e05450501c9009401605581049080000d642c0721400c102c44c0f00000041c10900120303045070308500c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 917837005 1250 917835755 917835767
    0xd1d1e07090e0f10060617010b0d09051c0806042414030a0c06080103110306040f021912060e070605070f02011805040e010e0d0203090f091b07050d1808100903 70
    0x3c0c1c01840307003d0300007102520000c135070002085600c5600c41203602d80342442d01c070840f2807003400f44103103900f01881040e00843d142c0d0300034020b0a2141c4101e9440710000c0841102d152058904540000c821008124403414680a85051300d0700c42c000c0da1001c0c01c0000c418002d01840c2e4083d1120350034001c09440c3c0c0c02d50b405c20904040941001c00c170390705a910740034000c007282070900056a50007480ea08031111030074001002c42c440d603002480240150310356401c00414001c0c400c00c41021000c121030115103140100b00c901140c0784529400907903101400c44290a0070a01d51110007406000e200080c00f184040d03201425050b424604082142e601c000c05e4600345145401040c2c2243c602614030703130942d07415401220941c950808a620131a009001244da91155420094105541c0c003800300081c2011002c80d6048004a441c4038082986000d10b410150803d44054549a0044e0500c01c080e542200f0091a6604080f00c1d958460b820716000c5036403040301d194100e03039103035035a4116401e042c841e072 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 917838255 1250 917837005 917837023
    0x18020603090a4215080a020301141303080c2505010c031407120f02040b090109050f0117090709050c0307090506281e090503060105060702150d020d1d1e07090e 70
    0x5285400441d4403101003556034246c0340d078100c0c025842d201d01188514128610144a506c1000041c40c0500709964100c40e060340151084510b01001d000210401011081ca030205207051102400c108085003003042c00d44102c2c2010700c09062038620804125150201c4117680036605d810094440c0d02c0c4100d80b04000c18140c80d01107030b030b01e101050104001003010001c00e070101d401d03620145110345920030080c005141503140c502180c80f14000c545030011a4034600d500003c0343d01920546507551444c101030301c00403038244400030800810483c0720341e0400103110140c20306a56041c01e0589100d4008442d4890714040c14405001d58045086284100d4500310502040c8215145e210700b1180081c0181000d8001c061281c0129000071401c3d0034403106032400345400400c4880001022540d10456034071000705405400e400704441d01c4140c00a0140c82482001e1003080103007200044100c9041900d1840c5291002d481e400f2005c1910307100041440680b158880c00181d400003244801c1e103000204 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 917839505 1250 917838255 917838281
    0x70302030d0507060f0507020615010c0b0c0304021302090609010305041e0507060f110c0402030c04092d050601020a1b050411040f08120a0318020603090a42 69
    0x50000c10480303500c40b0182400901c5500140528503a00750208192942161120f005900290004e90700214805070340850140605003e242c0410f1a280c00c540c12200322240b0002c114000180411410b142c0c18811020844507c114105009080002c2040c4904850607041640314400300b41407009410b0501c3c5503105902e4038946030455890b209455440754400c2c600460060420303104814010080b4882c0769000e0805005401c89400401000390005040240f142c0b40500010400c2c46040c46035001c0742c3e9100c03040d6001b042141003a003884414140e0038040c2c80b81000c0a00c0010b907000540c0d81907169201006000c0d04c844000c10254003865580542e0b40305080c0403030f00c018112050002c0080c1e0700308a1400c65515121040d0316510304240d412086944010450413a00f2071281d8041440705c11801c1c0512a19003c3d5000900c0c1c541060b5034a4110707820000d20481000110a8012071481c04450710308860615081c0000b0564462800c0181c22081851100300b00f48113070703001303062065030 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 917840755 1250 917839505 917839513
    0x120d050a0818100c08060109140607050c0312070203190b0415110a050c07080a0512030702070b0c060609010e01050d151103090a17030c0301090f0b04020406030c1e02150907030203 79
    0x74250f6a040501940428000401c104a010a2080d40320f00443e40070b80e80c182c62119015a884400c2c004254001d01c000d598034094140c000c007031a50300380480c04810250303010f1652204418010141850040c3c00d666803030000031100c5200242e01048201d511a0300030380801140b000701e00310480906190442030040100008404800a030000003801c403550384881101d120f1610350032807503500d4200c000007922940c007103152a07031400001001183d00c55183e10686040e9903a42e8030610194218620740d41c41500300c1e0b070410503541006050310740100081e5818400b5945440d000c280340c086000c0700502800041d80000d555082940c00400c0482c004020300b582d2807400054503520b5003030708102141d49480b9031022440d0000740707030150f9010342102048603107180d00e40403440d1300a01c81011122441c0b9199950340801d51b541e0720140c0300902040d02c1c003094179014104014158085c000900c1c2000e0440700f003495140c0e50001700d074201c146d001c0c11860860b85441c80c40c640341c840700758002585881 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 917842005 1250 917840755 917840773
    0x20f0d1704030515090c24030c07060b010216140d0c091416050301060f021504032f190804080a05030711030d020a11270402120d050a0818 61
    0x10406004200b00d90084058610203441034240707151000e001d49108500b58428103402015140903d4064400300c1c101503114400c2c11640c2c4448030540003251441000040450307842c05005142c000c007042c242092000e00301d04d020841d540c0880c14481c0c001d0030b400c0c540001150000d501d950903c500030035080a21103260956601a040180140481c2909287d407520040303259071110781c1c002c03400241c090312614116800d01404490004602024000314440d0620341c4d80e14611000446010b80d000342d0302d4004c001da6862461100c1803420769401d1010301d0928615850000c041000c0c0701840704444501400d003258185091640520b030801941030054000354010404000024040c492040c0c14500a0340b07148010161100a00e030700c50b0015800031148107001034031040c0003090154005140361072655046450300324a800e901c1144030b020345800240001d502d000c1e60383d201500c004100420302802006001003081c0a014611003e010f220030111300f4121490029800d411501c2c4101c81c1e0000c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 917843255 1250 917842005 917842043
    0x6080303041101020106060c170331060c0507020306010b160c0603060503010b04050f1801180b09100504120f020a02120c040501080303010501021906060503060c03160e010c020f0d 79
    0x100364142c102c1c00f5601e040e0000131010b0184c0c1c4540155138000c0300c09006400303150301d03007045540b0051400c10000c480c80301c80c0d0462107440100d068141200080c00035404001e20b40030080310000e0a1190501c1001d0013040c1c01070b6400030f034860545010701c91080d12004003a0840d5070300c41c2204401008100340c541c0119040303501d07510581c2200c030300b140284580d1144c101404102c1c1d809545401c150162500003800818081401503140c0799070034000a2584940c6489400c0c80c440600119200e0101500f03200d02980c0402c04c85c1800d1813000f8003001203013081d544400404549034000c1c8140001d0810349000180280100710711b258003c0c0c0481028040300042c0d503101c264042810b40302d80e10300000468600030002c10340f03050f00c006800802503060345902d084020721400404a400c82d80b00c0300081565141802014021101d2086103500d904240c072011f0701321191040c540d801c104074040c0342c04c80c0307a0380300b0b200031842c58050391070810394444100420910703400c219001c0c09504012080910b86 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 917844505 1250 917843255 917843273
    0x60e100309060e06012d05060d0b0a0f0b12090f06040f0804030605010605030a0c090803090f04090f060902130903021c0507052d0a02090609130605070509042a0f030608030304 77
    0x507a542203e1b00f580d018412108640b002c0c64050203400030000e0002c1c0d0080c4099030310059212200520800105555000c0d094061415400c1200c3c03440c0c0203e0084814494007003569006009074000c0c00c12103140000a5a0300c903030080000c0c151101c2d00484405200d80d00c42143c01454101406004039a150a000f43c1030740e00955800c0044e510380100d0b402c1003485220000151904030000e1442c3c820b04600300b0603500304c8024100c0d40542d450009000046610528070030562040d40d0100e1914810300411505018581050030500d00342600103000039030225034807005144190000c0c04060001000b01c3d034502030000024168401e40e800d011441c691078031032144038401300003940b1a00c07500c45070300758a58101180087d00a103c40300420502c0c0b4140048030713800fa00c1d89110380070803411500c44078191441540c0000c082040098461180c0c1003600840748000c01000b89050710012502000085103104444681000700320400952036502c25000300004012120840343c0340d0625042c03201d40 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 917845755 1250 917844505 917844539
    0x5030d05010303091212080c041d0402090705030103110d0f0803100e01050a0b18061309061811120a241d1003171c0b03010501060e100309060e0601 65
    0xc180404c1c40050001d160104041880c3d504c0502e04500b140054004d81d02e2460240c0384401070581408003180c4001031018048550a854100494a04150040c0022104003601d6002008004c10052000c6641c80308030105003e81912450000c440a0604546504000750020120302002050004408a454009080d0340b07061080a8169984008102190059118829402109101004450721403c0300720110b03000c06403c3c00e00d8091030072640100b56a407504145006552520184140b0052203038812055140c040104003441110154507c180641a0003d0349a40361708001506944c850704542c080342c00f03d100608640390601541c1c188140e25000754003600f040c24101e4500c0040b2900040d029003c01600d60040070b00356110741c41d894070030350710244241c8006c0040e281b07a294a203406070442403902c07000041c07071003031f65042609449042e4401c1c0c0070440d11000100340c81e69645440d4020356120b06000400550903c2c2c400041d00e682d40c01502140201c5000007000700c00e9000c5690303 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 917847005 1250 917845755 917845757
    0xf03092309060906010c0f021c050d03060f062a020402030703140c0307090326040e060f030607080a0905011104080606030d0f0e3304172b0c05030d05010303 69
    0x86a90311024040b100b0b0f0102ca03001d0000315140001404210f1190000707541c1c0e070014064001c1640907507000003100c503185008139284c0c0d11021130825141d5151003540060f012081e21a0440b80c60b12070010301071a854005c45044000c00070107210890124440550800d070b003e4820741d203910f44101e0240050a04003800d00d10030740a140011148039001045901c24450358139100c00311401d40d11005102c1030354034400450890107888040304d81e0f03e20300250008002801d034404240c58402d0511803c081c92100d00f078040c0d40600b0070b01c080d160700700981c00d902003e4103400041039080c900b0711901402d0303600c0750418120b10008010442d010041546c901c2450140c0c03c40741c80c0241d5a100302da0015114032a04001440d060384020145800003d21046960f8600310b20f13407268a070b54180002144d180030442040100040400501e010340c09013001110b0500301414860341d8040c004040c0d1210510041e96861400e00d488815500444041c100541c001082340d07154a000f0711118002c02082c04258 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 917848255 1250 917847005 917847019
    0x607030b0604290705010501030b010f0509100b1813060e06060408120307050c1504050d0e090c2206050c0c0a05011d031f0501030c1e030f030923 64
    0x2401800c05104079030490f61001200701c03d080340400609200600644000200303941000840085002401002d0282d8058500101d89500d00030300b600d040101c95015074050621a002c2000e840000c000c2c0701d040341d100d00030242d92242d0f00905558910f00e50b09031f865000345481e01e42e20720101d4980c07261051303ca001681550545503c020040035015038803440880764010b1000040301e201d800301030340c1c004203a4100141010b01070480d00d0304180c0d0320040080010108402c00c02401310402801e22010703030034244001c0000384040170600c1c1010080c0f1481211800003074840c2040043c07491000c3c9800c018410b07179019911032400900c02d500031801050940700742562140765141c01c543c00310842c3c005849202d001810400d10240d1030004101c1e0a9141c01800c01942841020400c80860100a04000a41036056244c041842c41c1960004100c844034031030b112002c0c20b80440c1c1041070301d4025001000d00b1a4a1400f01c1740c11600c2c0d0012903107808284131064071600030103000503030b40ca4100c03065 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 917849505 1250 917848255 917848271
    0xf070908010e01022d0304080906040906060305070f03061214070314030c01060b090a060e03010b06192d081f030c0302030105070c0c05060f0f210f040512090f0a08060703 75
    0x205d00790a110b61000d041010800200c2c0c0003465100c010030003080090507490a1aa5441c0341d4400c8408590203140820740310410080b50582c04440c5489001b950f040804c22a403c10103040c00b405190500100110408520030000d5401041508015940443c0c1e00b0602c0c207004100f00c0e1250454145856150300784007020035841c1ca05801d803214040084e0086100078501101120340d862041400c1e5050f5594a50803c015100e0380c00401001c4900041d407071065003640e10040803100c05d0030455190300d14038010310710f204101c1c065104034000c55141030811a00d0710766030501e80c00b21047c81458800742e1028004200f004e000d40010850b4002c40c000c001954904130142c949040000009090300c907003031014005840d059019216800740d030441c103800d05d1044880d50001d50711000840d1300e850040c400c0c00e100308000c0140c0f1984903882604100403414a8ae5400707544400e0007102c2da000070004501b0350160348400280408081d8010003544113261f44544550315400c0c140c1d00c200c0040d01344211 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 917850755 1250 917849505 917849557
    0x110304051c050102070c05011b1509110a030305210c0a030504031206030506190c0818120d0f11390604122012030a022a0d170f070908010e0102 63
    0x4510032242c00440800d03964a41d000ad110007011880e100310b5501509105220032030301c4101c4100007851080e114250703075026075015032013445164050a4070129901040142e81d443d80010764429601d1418041800d40302c138903055401a03080c4003081b2009142540001c2480800640c180c01070141c1001040c10a410b18a0030042c2c409180810021400f40000f058150509811840c500300b01e110640b12070703090b000292233550380312608a48403107840b40c2d641103803c07959100340c02103a515280e00364900744980144020408142d01c286508003d19051200c0b010b00404411090302c03844429070b401071410b4907000340c000c490306080c00e000526040803a40840740cd602d210428982400003018030500e2202c080440b81d00c001d040341070240c0c081c4004000070f0b01c2d04903201282510000c8000c400c14911841794542414203c6c2c000420040842404031181050300994000c01d4500c10076410365503141b0240d82c94003440d445050598a02000c0c400054810350107443c5140003501003040c1c4e0300d24404 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 917852005 1250 917850755 917850797
    0xa0c060b0405131112031b0c06030420060f22081b090a061205030408120a050d0509070305060a0204030302160305030f0c100204030b040b07110304051c050102070c0501 74
    0x2020030391040e003043c800010424000800130f1003040280034444005148154908580021101c140300d94151254803440f2842800007440c1a40141c1d9a241107240c00c0c2c8402171307040301140c82c90b5038041034200120304e1519001c1c115054051510460382da07510303403155400c80303451000d0401d503d9a044140040350002c004180c0886c62106d440140c981c080c022010040000c2c005000201021760b50708001803540900486862601c3c0100091501c0b0303071901c01c0303050030056401e40303001a450b000c10034036007101e803c83c0580300380700002107000030315995803070402e880c01c0f0301600050828468801006585d1009070020820749100303500b5150940056501601c1c0340360240001400e50f0410301602c101e55000e0006007c0300425a0219140d00c2d04031031a0008aa009030015211035188508000a00956004558001d6034529064500e151207a241c680c42e40145d00a46120320400d510400c10071043c8441c512101790081c2c0210351701c0307089240c0f80c481881c2c2ca205140c0030501038490301d11020100f80d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 917853255 1250 917852005 917852011
    0x61202010e0a0b0f0c070e010803040303090b2b0b3a080901080726040b070507051e0c041506030606080f22080307020c0f0402070812040201050f0a0c060b0405 70
    0x754150400c00c0c80068404e290b00310041003000c92103000c2c000070b2150722403015203000300000b1015555582c1142001000e01696404c401202402084002404140401008001113001401c040110480c58a0402418000000f03560041d0780000c0c640ba12494a035070040f42c0068028007d01944194606e030103980360720f140107490840c05101c80308255003d2580941e1004c1c1d546440d05d0700720001d5181c1d04908504c1142645414106410030041002c10a140c3c2d80080c00c90a1442c1010910ba8074550703201c00c5452021a440034044903440c0014080140c249890707001003081c810b2008803403410203005030510071a0000390600c0d1300050341c2402180303043e00558000700c20f92030039590824482c0000c6e000c00342d48584005485c8980d004901d9050195001e0a559805007031191030403010032010411011125208a20401c84140000c1c417003030465901c44540840c000103136a0740d0005840c0b50040405412850200103440d41580380e02110518206105d49400c0040010000c1800203c3e1011 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 917854505 1250 917853255 917853269
    0xc0602190e03010c0e090a181703100f05130903020309100521040201052d1b010c080105012001060f0e090111040b03010b0315032d01110a051c061202010e0a 69
    0x1b4808180c1c08107013a007100d100c0368424880c0d40369101c0f250799012400440d103200d02e4861240030040c0280d5904d9000b0600082080a041c84000b40c200b170300050800031200c1c21440060b07614410f0501705402807040d5081224005c00c24040c4003140311018090341d01c1070062070070000c010b05c003146c003040120084074010381d0103039601418070480410513820410f04108071040e42d03560a44c1382c1c8a00a110004210341800c2841c207035a0013110b08446429600f118034004103020103080140320300d0b60b004500f02001030300d40901900d00f41c003007203401c4c0c0100090b80001c0e4100020141c0400c0740340c51801c502e030090b0303003040080102500c0d80005004c036001b036014555800300200010000c100d45440510303000680c1c0900d221110031140002440e0442c1185d00031700c0c15485000c0d8100388007003140c05081805c00400240720480b00e050401c0e51303500c41c3c4081c1c1f41c24000c000c2428803110341d6441011107400ca106004014076078455448450040c1908012400240c810b1740035100c1b410511200001c450320 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 917855755 1250 917854505 917854519
    0x9050a0e0604030c0c0504020d060e0f06011d04110403030203041d070e06362b030f0203160b0a0609020a080f150a091b170402010c0602190e03010c0e 66
    0x40b543d003101d024070700380d01c00d9401041c510380c08542692148002e1400c20134041c0c00250303152511002d0400071070010100b1101050b2403040000d81d9030050200002000350b054001e5443c03801d000003400800040d406001d0315500801e0200405400100030025245201803808018001580c4d600a0280407142240041c21002d22407549040c5000034090043e0700949100c001c3c540310350b4961b141200450803041c54102d6200e00503460400000c2d6581159904900e84001c07005031f0f07040c88400d0781004c0c00070200b002c14449000d05601c00c1c0140d50646551031010011a14a42091000b507982030760800c8095280c0000050803607090f10840c0c131400d030310b034a40200036903690b4220b0520590042c0003141c80041c816181031280e9500d503110000c1d000310f140002c1c00e08884102170304001605242e20080c0200e6580c55528911540d1540e036000f0390910b0052841d1681c0d18025010380100031001d40c0d000c0340c022040303610710341024500c081901c00350020400940260344c1110f81c10130586820b504420 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 917857005 1250 917855755 917855761
    0x50a150f08070509070e031614010509090c0a0311070f020108070509130e010b0a0806040606050a1d09010b0405070305060315010f05060702042d050604110a0f02070807080709050a0e06 81
    0xf01445205e6100e441402d10002c1d66020001181c10942c02d1420188800c2c1d01c07900a00c00c203002d07a4034604817100d080c0307082c6080030580303c08268040400b0300340003190f05011803811496031180d000b891000401106164039402a03140103068507003011802c030302280b000380000300d00314030031000d40328504002032280360ba04080494240003014039920310300f165501e8005080b01d503220340324554002c0c40140e00030081c611f000c2c01c000007202c2c00d03500010b2080c40409001c00410004140054802c444500c1c28103558031358040c110700500c44580015001801c120130050b226415620161140c1c0b4258140d402400000700b108000d14024080c0310540e00c031550b010700040c03c0c808090b1503c14400303800010100000506cbc175100884121141068102c1c0300c04440201d070345405284c1d0841420b0301c0a01501c0700141002034280600100c0c0d40c108025000c44510240c800c0090500401281c800d031003200b510340b600c0544a46143c0a80c0e002141494003088056010f842600c0f08880528054840c5132 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 917858255 1250 917857005 917857009
    0x1e0304021c110a1502060903070f03050322060e06090f060a0b13020309070f090204030209010e040602120f1b13052106010b090a150c111201050a150f080705 69
    0x3500402a11580d9001205a0b000e480d0300200348054046032620111070324241e40003e06c0c01c40000c0c00742150b40c105002c0c9900041d44058034040d10740d41070030704c151a40c1d1440d01d44091100714007042e00d4040c0703e002e400070500125030701440018040c0c00955541d07696013a4455904d03160320700350700d18070380c0203034001580e1207542d84c40608181c1c40180f13841c43d41c181188a40c3d041c0d0300305569452075600709600402c41b4496001d0220002c02c01d454003982050300e56000078044240511a002d11440504000703800c1100c282d049610f130b0590110070204a04203e1513030000c900d070469920000c00340708800a403007540031030305480034800e080748440b24490800051003070003500c2c900c1381c0d120404103070202c9450300b100380500c6000c1c1c812580c00c02d8852043d101000030314070082d48524511f020710350009043c2c0f81d01c0f5019040e02d907003243c5181c1400304000d0100f4046901d00303100119a510386401e1205d1030741550402426007079011f900039220b81d2118210b0750601c44c603100d2810540e200324070802c414 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 917859505 1250 917858255 917858299
    0x1406150906040b13050f0306130803060a030f0308040c0b09030a02042403030c0201020601150e0420121e0f0106111009080901020601060f0f031107050d051e030402 72
    0xa00c6020380700c142450380c0e903002400c0300e8210342284100300e00c1600c0c0034400c40c01d0110340140c1070303d0201e00170302c0e003414049680c0c1c82c003861103000a0500c450000c0000c40d40d40b00c3c15400b00065911130300c1c0c0803113880a0b040007030101c40240c40c200c0780c20507940d10000d404807149040e1140c548009001d0a0b22202c95403c000081031080b003c2d000510b40d4088105000003803681500c000d42c06901d55035250301e5244002030a14505070060f15034007020480c00010194410300d4024901c1041d100000c1c0c46c4c8400b40706502440e020807608803040000203a0010070542c4d400c043d405084404203c483e1100c0d00c1c40708404400c811186010070310403500040050900c900b803003950503442002942c03d101d5062107402c0c19240054002c0d1104400058205010f50b41001890300616043ca8502285030342a000240f100d10541610810107442d00c1c902800122403104880c1c400e86c0c800d08a44690031100000b0b03000c0e4104c0f0550f03440d13070718590200400340303126081143d101725030080882013030b01d03100f40855400c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 917860755 1250 917859505 917859517
    0x211b012102071b0312020d081510021c02030c060a0e0a0f061404060203010302100309201201020307030504050706020c0a030204050915090c10031406281206140615 72
    0xf108003400e200e14035151460880001450064818a13860804194060715042020010204000c8184104107131000d40e042981841502203508000c480c110500407403901d01401c102c180754030482490503c0c0d00703400100600c1e05074404410307a845a5580b10000045841012024040b6040608030000080c10360322103811103071140c4800224081c10784c440003d5501c0455084484590010052040d0320b0061001d03003400d010342c50700b803003402d060f50740d81c08070001f024260705c6140c06001c00402c51903a40e402c42c0515603540384021134403031900d100c0080203000c0030755060358240106880421018808294035890750f1014140058184c61507007884010440140f42000741d0003040b8001102880d071070340d0355006000040041c0843c000c60f00400031a0320038407402c0030a2614028031910032414102c8410790090742150140c2c08410444450150080130003074070300c0c10200198011540c000c04445e4185214028482004003408001100588140c25244240d0040d17401012920b030516075402824 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 917862005 1250 917860755 917860763
    0x80624010c0c08030403020120120f0702060d150803040617180d08100f060905090a0e0f060108070f26190303140709060518211b01210207 61
    0x1641075403030301d0305406107055030010b01182e000082c0c10002d643e4000420715094407518240ca1084140091043c3d9902082c1c402c0000a1408150f8030244070052058818142e00500b10690380d81c0c2d00f001003030003409000500424003600607408610507200009a42c252001601c4481c2260360055034124584d80050218648941c4d013952522043d2091002180c0340c0c1c0b0584a60f1500c1c10311124401c40184a07800444009002e200204400e4cd4070030a810101c52056650b4062500c441c01e29030060b01c005011075000744208065051020380000302641295078003029204116119a0ba15410b90b40d640706842841240c00c81004408070345100c040e142c544201d0880c1c4003001c4c1c10400104040750840281d0100e661041781c01001c20610002580c8080e0314601140510b05101c0007130b1190182c404410185900300310501c020340c5552014800072600300e59041029100a03103541e40e14010040c06180c0071006902c1e00c400c03075018840c5500e0644800c207041b000101c119140000070741020f80191 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 917863255 1250 917862005 917862017
    0x14010f0b090d060e0709090809130e03040315090c08070306050f06010e06161b080705120a1b09092d0309060309171b070b0901140d020d0f0b010908062401 68
    0x9040100b40c031a03441d20364401d082c0c80352600b0500c0200703d06d40031240c6440e0342b0f40e07060900c040b0f090800030003160140d0354080002030000c806c01040c0c1d0001c001d103503030060201d8604440418400d4000130b451080303a200d01414031581d52a13460300b00400406481c074a0124031000d83d03160f8646040409841a206807c81110200403561226a601c3c3c1c04440d14894068100d1014086444107120400180509842000c0001c3d00c0780300e01075039491401e202234007540c0d10f14a0003042200101e141030040000311303820b1001803107d04282401c5400800c240c0c0039540180248203102040c2682ca080198158484010f1745241010079800f51500a404444100800c0042d0a04c800801c010b4a200f24800c80481c007280c1c031a103401d43ca4055140c201240382c0506000c0d25216a0f44880c2d100b20007203400a41540303c0d81d04c4180710703000c1c0c081c035450b420045040002c0aa180702c056440541840801d0366000c19081c2d0b40c2540d561950801daa05405c6d144900000070900359012071030f12410351044c5850 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 917864505 1250 917863255 917863259
    0x12110d050f060115090909051209011701061808010507091509170322080a030e040b06310b0304020d140d0503070e0a060e0904060f14010f0b090d060e07 67
    0x45410080c090b008500348003044e164480c007860307000c0400c0c1d001d01143da10401a1050603140c81e85d0302c0842d0b141d8a003200d00c0010b490303452a40f00349079a45181c0d0b0745000144603561a103101811000601c4544001d28040c40400120f03042e050154078001e10403512025425030400410014882e0309601c0c030710602c01a580c000500055001d132858030000c00102940e02e07501c41e03003a4110002201c0064003540001800705004074400810b154103200d905040c1040c0c010350502c049400b03801c40e011950350242010500344154038440011040c024540302c05131441e0741550b01c4071a107c58060150040700c402c103000080042c200444e0b030a0341c42e4080d025204a41c07a003a84010300c0c5c00c03050b011080000d0004414440c2007500200d40400d50102280e01d0703a401400c000c0f00034000b903000e1102501c64071100c3c02240900c90954004010403000041c01d024020004180c0400b0440a100d4441c120600400000d03484c2c50b100c05440ca00304000b0035407442c40e0510b880d40741c06403003210a040118001e00c940 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 917865755 1250 917864505 917864533
    0x4020906070b180a05191b061e1e0e030705060f07030807140930030909010504090308240607110f010c080a1404030c0e1012110d05 58
    0x1c0d0140a1040c4503260305490500000a1104401012000c8540c020000307000040c40c0403441103943c0d4030444075013001a5103410650640400b000310201030050094000c0ba54550120700c40b020200d14141615512081c0c2e07000311881d0242da038040142400f00141c824000e032045030619100080201118207041c0c0711070010700580d0007601b500158150008000e02019080164154401c40714200070102035504140800944a507031101d034890100202d0320314220b4049510b00e001c4071050001001500554021325a41e6400b091000d03206902d61000014540340c140201c5050310b5059680d1071007911508400c802c0401054800d07204c002401104180c4e58440070040c2220a014801c46075100c182c980c1800b44140c03000700c000741000104400e010100c1c5031001102d0105000d407400c141801d04070303080c6020500940e000140100d100c3c074000189100218040c0b402208125010028140e40346110000303d000c591004241c2905c1842d2200b0f58035064100074011070044084e1017601000d091 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 917867005 1250 917865755 917865757
    0x3c131a07020706141303230106060e040608010b0a09020f0705030307031b0215070503100503070b030a0b060a0c0204020a0e061b0705011701030b0414030703080901151401030b04020906 81
    0x5000e8005a1001204114403a44100b0b003406003903002c00c4a915001341c03082d22080b10f44990201604003483c01c200c20700c1c04064514440120381d07052001300030305030721690020329180c040c01c101c9100e80c0c18060041940c44040c4a007030560440102032040c00d626116540e80a50000301540651000500903d00801e40900003503200d4900e0756070000340210581101960305a011781c48804552005083c01e03101c45110407095000422810310544035034a1122201118002c2c0d000150580501c0700002550203440d0055402002c00309828416004a5020700c0030710b0086c20540070000301c00c052540c000d401d050f802864451070500d84940203400da40d01040e03469000740b050782010100e1360035071540a04148202c1c0e0203480c0034039005c05502048024441190010b0002822011070b42d00401c0403c90131000c008815021007040c5d0b80c541c001da0a000e80307050003c591304103081d42044d0b049180e910506510350103070385490b20341c02760040070100110010020300400a4000d035081000350f2656039428 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 917868255 1250 917867005 917867011
    0x1f0e0306060a051c0203031b030904150815100f1e080c01120f060b0406111b061b010b040c1d01172403100911151611093c131a 56
    0xf030000d5035a1110000bc0c08212171000c0c400300e2221450940c1480403000c040f60601d035040385850002c85a894080c480000350300994002040480d130b02c00000355410116a03100c11803c0b00c1d0b0710011509960b108001e8441141811040c0007840580c08610b0701081c036030107003902070400000000c8050310f420240344141c1c000d03000400450760045070603440e201e00b007204000b00003590340d080e0f090301c0c4000c1c0070404a001c0c1401480075103004c80440200c1e010250300200d2100c0c8020814007200c10700030409041d01841d080f001a0802d0000500c4d005540221590324000c041c0960040003a80c0d00180c80d244001c12504100e00d00010b030001c42d4003590100100200d48161840001e400c103460301d4070b07503a28699403640364001e008a070b0600034480d4400055860710011104032600bc0038891800082e1442c1040080d80d20103d01010b00000c1c07002a880010240882442c2200ca411289852004410b403014207050f00c88540c00003c0401400110500c1c1c0301e807080505000d00e1a956410040d244030403 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 917869505 1250 917868255 917868307
    0x6121513060e0c0105092214040b0f07020c01030209120f070914010f092c030306040c020a02030a1403040314013204080304021f0e0306060a051c020303 67
    0xc0e2541440003500c201c2c290040000002d0a03031150140c00a842d074002c200000b41301e1952142c001c6011204414510700c0361405420400c580840b08002e94048101510180d45024071800062100000707640070b1402110590000e1985039a8007004401a5000f12000742e0440020303250040300c1364040043d586030080c0c51026118950030841c5039412110018403c800d1054000c00400495007030032007034015903c1510010510140b8254400c01e00c8030303400e42030081c0d110751380321074000c001001c0301640c05841d04541c24400104c00c1d8400300c0e0741e03041c141400b03549600010056000035040c4210000301100c1712003580d01349642d03071b140c65040391041410420310340d4441001c030080a4007010712190040c1c110314115482018130004202816004100425015000011805541e02d403006c583c085d5070700d085512008141290028110302095120a02a228200101d011751030003411740419248050101c4284100da1810300f40c0100d900c034000d82e05400100210440d21800000c840180f40b00 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 917870755 1250 917869505 917869531
    0x111002181002060a0f06030308011502010e1207020301050a0203060916120e0f150106120f06180c0f050309120d020d0207030f080109110a080a06090614011d09061215 73
    0x20320452005c0c1c1e64801010303072074285482c10170b000003a0400310450640d0b9a40f5030b50044414040c00580c010144100c02803001c1c402c45066100b049109402496124405e600911039034455200240c00d9000a8442c06d070b010443c2c0000a004510a8418440040350340c07408080412039080b2503000ca460488040d001904608000144074104200500170b034502d030b9590050310b62419100804903135040c028121031070b8813803140c048401c0305500100040d007803060800400502d28401200200340c810790b80c00100d071440141d1201c1d6401201075921401410020700070080c041400c036041584108141c0c030041d5801d100b186c0c00114584040c22503984030340c031603119044c8002c03000703810228140d100703100703c41c1803800c40c1c480d10000c4404d40f8070340031040c00c011903c0e0700c601802c00702804164200343ca1141c078080340001c810004c080c0b45056640203803103d507117100e280c03900580c01f0080c074404aa0890190b40c0070030400d00b003c16587c080c0442030001c1d502410210010a80d52540a46d005030b03441d84 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 917872005 1250 917870755 917870761
    0x2120d0b0901050f010c0213061503060e1b04050d0303110301033e04090f050d050910030212010e041a040b0126120d0603060612030e0111100218100206 67
    0x400d0928280500703c200c8115141c4074041c4002060700d415404028040e1454040c81070391304d265500544094501406003c10445c00880002c00902607445400c00604403440825240a00c0039240d03802c00c0011a00d99141604040600000c08188081101056a280c241da404815032001540c082c1d40b003403017100480e0300380c25070142000c500c845034162080c3c04514903000009034046c043d401c140003500e01044001d0981840342082541d104060000c3c040c2401248015510600400d01d42104455440807418480c20071812405082d21003c05400400014400b0501c001c50082d4014807600301d058800c000100c0c002c89003242a10100d41804545005020b0303515180e041c00c0c02005500c56203034190480f80c54a41d81c85501c1447c94441a10014002502c01e010741c000c1c40c0036580008043c42050b642d078000c1011401d624ac3c066000031904203c2c4901503200c0c5001080f0503001100400200002404910007540040442801c818485550003019201c68421414000040e006024185 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 917873255 1250 917872005 917872009
    0x120e0c04020d0b09072c15030412180308031b0c12040f06050f0a0305180f060f060103060b0f03061915081005030a06020309150f0910051308090102120d0b 68
    0x4005d0000010b100c640c1c03540009800c5243c0b400e040780950301c0800103d0080c00300100c1e08145409204406450002042100380302076044400351400391030f0359101c3c2c1203c0c0c0312055011400c050000420300c0c8000c0022941919078154400c2101d40350072802e07807030b00d18807102e06460300000b44400c1e00107141c049130411051000780513000040c610b504049160102c0d504c13502000b88102501c81044c50b5490011903206520030f0400c94211014074121020181c0190030707580d0b1610200e40c0c0004c2c60f984100020242e5110780140c03822546044c401034108204208140325940000b000303280c2055004c42210140c010b480c1c0f254009180c51404403c03103032132000e00140410301c024120351030604030b5902084251000504100c00580181c0c005807039884200340c6500380700c000d446850940d02c2e0b0b00c0038028940c4400c03052074081c2c02c800c4201d5a00c0740b4111842c2043c5c034022141c02030b020301e0b03c00e04100880c241e007008160449051041d181031541600064545400202c0840360302651410280818 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 917874505 1250 917873255 917873269
    0x3070e0f15030115210602041205061f060c030e130b0306071404060516020307031109220b0402310f09050d0e0a0806070302030412030507120e0c04020d0b 68
    0x1c85401d40c0240081035482141082403110b900c2540c1c44100c10303443d4083c081c4217503860381007840d50121003503542e15500e19803030051400c0e008090f80c4e5402500c0124112100240725000191001c0e404c0c402c925281000944003560116400d07414842c0072440c0c0c0c00c05640750541490400300942c400140d1808200501d89024030040c1528181b0103034540c1c010308180590117031000c468691a06c0b9503500c040040c030844044c0c04c103000a4141c071030403c010007040640a50b1485003002503603000d407942d451080e0300607481860b00c90003045005505810300450400c00b140c9500034000790036842603114101030225649070400481000c0d030070310300000c050a0307501d00a94402800f90503061000c01c1040e100c054880200b801040140452140241c07001d4540d0545100200100c0c1c054801317503c0c0108000c3c01035441114125042f08802010b4440c160003403080c50b01500c01c954443c60702c0c95180381010010403c03000c03000c0d0107101d481c1240d51155100e000819080580483c007007030b07540c0c80409200b00 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 917875755 1250 917874505 917874541
    0xb120a0b0f09060601090e1017060108061f0302040c030b0d0506070212040b040e15120a110402030f1618080f011d061b070c03111318030e03070e0f 65
    0x40360f0441014002d09a0740001e011040d542c1d180e91040480c0c07642d41c2ca0440403a1b150380300781c028481202a9040f8298080b402c3c031704a0f000b06040d542e165403070780c04400d4920300e00032044860006140c8288003504040d4455130030036165090014a89043e070340013880c01e80d082d2000300d031541d100d036042007801541400381d0064a203400425900303041c00d14200c01341c1c40c060350081d255084100310010b4030a040700c9259a01c2040081d101e16010358403a910b081c2c0700d000d114002d507144c440c0400b60840c00c2c146442180c3c4641441040c00100b41c070f90003240346452a140d11803100b04640880715184c000314035901d01008204440090071081c03800e48100e404d40c0c2050304c1140031003010480740c41d070f00e42010890035480b4510105800c0d14036440001c3c98542e0140c100e01030318401801c9004010800400e481d0710401c001202c40304000c44400c401e00060b901c1a00d0700c203010620310540040080d019012035280d000000381510902a00c0380103822860001301c402003148101441404803c181c40380308440c0c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 917877005 1250 917875755 917875771
    0x8030a1421012612180609040222050f1318120203040305102c0f0d0309030315060e04020c0c0d05030306090a05070c171909090f06180b120a0b0f 64
    0x11541101030b03100300140910b02411411102c0c801c0005591baa40408030380d04640d00030021900d48440352491b4010719210b03c6c600816520002c40800ca5142440c0c4144021000903c0074004040c80c2610101500150070503002d41c4c01110005000544162103168a00741660300642c0c4580ca1030400c54545110520305030895441c10944da8404070f040d114000f10144103005040c0001d00c0380340e80510b400500032740284c160042c40360441070241d040d0003c11585000755014411000500c46400a2403038911424001c030b015101291068281038002d8901202d5450036101a035138420b0215074070818040702140d403500300208000c4c0c54a405915960000e00300b00c0c04008916000030040e041d507640340005400021202c0641030350550600440d140c0c1c81304202c0c906003c030a40f03503000d4141d9402d4060b2800300e030b05164242490040b9880f4500468248500c8042c040e6110700344600184204100280c2104007103028041e0031600304250a881442110702003000d00c0e1002c041410080701610b509 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 917878255 1250 917877005 917877013
    0x2b060c180e090303040627050106060e0108091f02040302040203010801090317010b071104020c0109050d02071d0a11090913020f0609010c031119050a0c08030a14210126 74
    0x2040282c008103982e0710a40c80040080d0f8054280c0701c05c01c1e81c1d104400200c01d42c003400720401e4100001900028100c0380316888401d0003001d480010b4480180c2141c1d074030b1540d07201c451450030a000b9071b48100448030000c8030061402c2c0d20707600031500b40c0e8401d03040324100361744032042d00d000c05500818558141111440d0001c0f65410f2407600c2289100311440501074082790b64000300c03560380320390407190f4151010000f004028014604603403168283c000004c0940180a0006201e110391a590904102e48544c008019511305e02c51000500c00204500c140741002e00103080c0903220303140e5030740c000d55042001c8010f401c1c0c14410404002c04403562a07000e41c5050119595136600000f04081480e418285401d1000e290341c4190f1030510480c1051301016001a41082401301c04100c450b43c440c0101c010118080d1201c01c02e0f42d8038418841c1c4100003031414180040c801a544015040244906a0100c100304000e000d024681c0421380161898110329447c080c0292041c09030780320000c1400c0060 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 917879505 1250 917878255 917878261
    0x6020a020109090f060f030f02010f08130212120c0703050c0f0f01050c01110307050a1205040302030304240903050a2c19030609080306120c2b060c180e 67
    0x2480c040c103d10846a08540b074004a01003850a500800058510802c0c40d002c115668280b290174411304240c181d010a0b040d07141d0007031141c46209100d01c0740c405510114209000c50b401d2100d4005083d041d03140c180034000e02c60044602680050022005942c0189015415402c1c05820f0401c2514400d20621001403884459101d9251440b509242400c00c1515922441d4006000d072010314640807100c0400002c001d030603a0082c0140944040f9556455882841064084c080364fc06039030240260f0701c00e00014000803120b40d03080c01d000c1e401c00110030402901c505100c2c10380300d90110032000308102040c03142c0308582c0303e042015110300d4590b40d5511280803104540c0102414a8218004c0c141075408420400840040000850b40003204000660443c10901e095070000c1d0303011071041e0b8810a4440c05047e000541d544540401003c0c8000038007480316000b40c2031300c1c55184c0c82c00b8042901e60000860020320403605104d9580d00c03000581074051400386041140b5410501d00190045c040c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 917880755 1250 917879505 917879507
    0xd0506100e100b0c010b03062a070f06051f0b042c0a020c010b09040b040606082103040c051008100b0c07090c0c0209041a0703020901080a05040804170f0706020a0201 73
    0x2104084402160000f540c2c0c1d841c540b00280900702211031a60540700323040500001c0254000540d21071543d000c0308444506408806040030b20402d80040d021021418801010814660200d6004001c2c0300410300c1d044031502c0045c550f4003d551050700c80c10404201080209811007941520250655059900e09800048040c0002001d004240919400b043d989108513095100e2405d0500c0248039500528083c40e040d0b046002c01ca40c101e070a2030904000007820500010354050304100480000d010341d0f0000b900b0603158100400c00e456202400000141ca503c405c154882c03400481e41d6036060070314040110b51607080d80c40d406003000c220100091450f42d88003180000942c0e96404000c110390b410402c04460030400c1e43c0d8042d40c086411802c0c8010840344001c484c6a0001c0d140d2103210541d240b940c250102e001d4402d4107404106030300c0004481003569440300380c4c05485800041e0600b5240d404a0217079044401c0e1210340c0c0d40c8504801c0144440c00c00810009040c2e6200910b07640c001c03940 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 917882005 1250 917880755 917880781
    0x3021018030813031412060a0902090d0b040602071709240f07060b1507050f0c0a030204090302280201140c03120a0605060706021801080907140d020d0506100e 70
    0x780c04061085000143c0c205440b8242100e26503804a0315561070300c00c0c0712600507071250f083d20102d00c2003010b00030000d091032090098075611000148900004040e0382c680c2c9140c034000901c03c884195007009000300003100503049510118440d030415072a400303404140320308590000c040c2120120b0402e5100440f6a80c2000c41d03900c40080c22038651940c24a207000c00c01703811003a82042c2c1c02000302d00c1440980141d10050010b00c1e000d44219441d5403c84025941c8903000a1117994200b12184424000760a2507040741e08054480c0c41100c1c891101407009023a001101200c5101c9851500c5e040d0b015903034004084038500421340200c928080410f54829542e1040c0e201c00726111282000241c55103015a00010043c2405040c0c2c591304d1410b0718011000b540051514090840c80101c0441154800c100c0c85104207a800c0c002c21303850b4208a80241d54446152015034002d00c0f0381100300040e04c074401d01c54010361040004103c03e04180f046041e030050241c0102d11141080010461501d1144d0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 917883255 1250 917882005 917882011
    0x30b0307140415050d080a02061f0614070606141003060e0402040e0a08070503040f09090f0222020409020a0f110303040b070e270108010c0203090402090a12030210180308 75
    0x40d40007600d50038520416964520f1540042e50115590b410b80081c00b80803001014684410b6090702c48596034540b94910000c610410728801e001100020320400380510200360307115001030211401c081c00e0340c0c3c80c807042d95070365041200c440318504005801c500345146841610440c0f81402d21006081005151030f49000410280c4100c1e229280c2c45170030313402401014130494026854a554400380d080007942c95001c4d10821100031940c100010345d035606445220441c0354000c0d51901050550740810016421440c407201c80011203000d441c0ca801a0b61000300300504031070501684075003403030401030001d103070075901c410034072000300c040c040d110750080200c95000381e0003182800d0540710841c0840301c5004d2a2409c5802078404024407000ae50280ea00c40c104440b85107404055030303291141c03d42030f94544005003000d68000c2c042103a90789826000382000d62009070000405a0f6154410341d0094826501035001d070300000d5840b40c411006001d01903445510075045820b0200d2550000d00d460307802 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 917884505 1250 917883255 917883259
    0x6050112110d1104030c0e061e0303192c090a021e0a1202030403030b030c120a03140f190215040b0a18050d02071409010308090d1401050106080601030b030714 70
    0x1841c092034403080010241e80203175811100d0b507110140c44070110f40300b070902641c02e036100d050003030001d07222a4441d003010040810f010b0091400c10000540300402c5400c581c8000d0240090140b0381c0b4035200c901c40443c0b0b40703001000004180e1040c40c2090000e4034202500c001a1140100441640c00d44941d0761442e90880c15041207075503080c1c0940403501da071001c7c04529010744c0000140020325906400240010f503086091b207518002280411000b03540008064855030000c00c002c41c003190248142c004c07103118580d040c030702d028451404c030031140c1e20a03161010000702c0f42c2040ba0300d4a5041003800702c040d0f49811407000905040d1590b2007480c1008020208503502c4000707500070f21212241c1d1151250b07000e41194402e002c5c21308040d49900c121701038003059403282a4403e6907490a080291704980d0090700308c078070b0140c2c20030034400f8203c15110240c40b0b5011401d6071350501d000910501c0d0003810550381d180c00d030b42410030004040c0d40c0c45501132031082d0300020052004000d4101010780c03050342 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 917885755 1250 917884505 917884511
    0x31c0b03122514011508100c02070527091902060f07171c02090d140f120406030e030922090b0405060a0c05070c03030507061e06050112110d 62
    0x1908124844507420799400080c000b02c03286841d0200603005030801c480e0000c1c14001d00080c03c111800000c1000c0300c0c810620345500c042040d254029a9a004a0420400c0e2040e03540759500d400204004140c0040800c1002e0150058a181c0440c5041c00c036030804210005007111801000207204a07003204403019100d0301001400c280411100402c0391145940584203404c080105000ca02d81d542000103299082a84680d0350310a00c142071007202c240d0b02004180800b0710b05991214410744114160610141c13003621980c011418007080403803a0074128465643ea99800d28500500369410040b028a0759441403004098a65480560300325054034551a4200404404007480240100381c00141000111609010a200d008601700d40f04ac1060103080c040c1040b100800c9980344160030002d41100401e90b41480060310410040c6a41400b0b1003001c0f030902071546504c4c90080026180c2e00c045959400104103c0d43c0203504110440f01c030280c10000d000380c0c0b9032107860a1149400040c2c0700c41e6 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 917887005 1250 917885755 917885767
    0xb03040b07050c06042303070c0902031003140309010905010e0112053c1503060109021c05010e0f0c0315010e0604120803100e070c03051803010e031c0b0312 69
    0xb21640c01e4546001401c4126103050400d810003519441e204c210366000700d4200d4588482c0d02c1c400004540000d6444008900c1245c0740c41d40f0b140003508007900072b00c1085134842002001c10440503282003001c480501441e030311640c8200160412039194800c90600c44184200c082983c2c0214614181c0040c0150200e9907a9913200c1c26101001c3c0c01c51805041201400ca50b6000d803078101d450880d1402c030496440c01900e80b6004a2155081c130180d19900d54000401800710030100e801520304e13100ca1803481503803040d6418a800a80d8000d03080f1a041000303210030030011030403400b90540c108024590061a5040c01000104951401854181402030442d500c0380c20b51220350842d0020001c80c3c000d00c5401d0305c20705d8500016401071700c0102e45020950400f00c0d41e0380742400340c40c0c020302c01c94660740070764181640d05943ca60485492114402407045440705251020302640360300c4034050024550300c0354106043e0500f981303185010001c50380750240f07481040e10300003040c0d0030340040d182080d62115 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 917888255 1250 917887005 917887007
    0x5010905060a11070f12060501170d0c052d0d0305190e1f050f090319030c030209091008120301080d0503042603100503061603150b1801030c08010b03040b07 69
    0x41d180d50117000001c3c030041e000203160401d000c085605031b00c07038072003402542d9135a04103001d034071a80040300d000354001c070440b15140380c09240300d01e440c217208800fa175202862146030b401c2651051103440e45142c2c050741004503e80c50034000c509c591070490a0400c010705081e0060848840250307003d500559490101e004d10902c100060507503048910001700e080300c0032400b071901420702500c040b401c4c18480b0000ca203001c240841541c2881c030210030200407000c50100c040700901856100721060581c00c202c180c0c91500c030f14000c42d22401d65401044841071505840e20f141045210003c8207905007800148141000400d140c600421a481e002d5182d0f111401c0040c2c00181c0d03500c00c124200c0c000c1032211405d00d0500301452040d00300f08085103010b80c0d00c01c245511500c00b140c04203c0000070311880c0c881d1030b019030b0101035129000c40d0350300c41050301c9031084041076000203480f40d80120700a020b00303410b40e030501990300000080c0c0742c030b1061540b402c2c110764800c2c080500010020310a507400a6141 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 917889505 1250 917888255 917888263
    0x12031107110f121e0c010203071a070c080a0207030309120503030a0e01151e0b04030323090a0f0f050604050303043312050a020405130e070317031005010905060a11 72
    0x4a00220a4540d0780394104d800d050101912801e2020900078000d09001300d6001000380c400752a00007600174031240041241c0316040500404220500810313401c5c00010810703110140031070074a00d8004040450941c14080d040401c29071003200c0d00d0040c3c9000500084001c0203881e00580c40c0c41001c01c0218030981ca0710302601c0501040043d401c80502d0028030824004000900c45620f010001c4085480d034090707002921682c0806008a01c886d0f060403811001040c900d03000006200c0107904000c401c83c0000c0182c0c10991100b011f80b03060010900c51405908902c1009007001c03112289010300d0304c4007094036800f6510620402d15020b40c5407121200001c6034104014818041152a15801100c0600402c1026a0090110346003e000a990326403910072136003610070081c21003541080c2c1840c06009003061800d040007c2c081e6103400000152030a0941c2c3e0381c1061424401d4a91078080c1c40d46104022070f91046040080b0100b003003260391111400c50303000200c0c0c0d181c40c40e040c0b1086181140341c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 917890755 1250 917889505 917889529
    0x91b0b0706050105061e0711060f030a0501300507050a0b0c010e0307020312070812040803010905161d010519200d090b030406151701060611251212031107110f 70
    0x340000f0f4603a803902c0d164ac0040d0300c96500c0d06020040ca0340c8801342050107404822145c2c08a5066090400240040005103140588a10100c50348140c0300d0003c0f807903035107031030784110442100446c1607507840e003003801030403802c0c14803c0c0110304092080e000250b13948078640c030a0420301d800003501024429030744200c40886662480141d03c90505140c88100c5500903c102051149000080b0706242d0900001d85482c540782d58924507411101500e0240724021035990a050001c20400f80e105460465a444c00341003268844500a244024000d032140c2031681c807038112a00802c0c042007549070461044001e9448441600351a070766540351000040200390040551032100b400e00240e81c0701e02c0d68070340029150141c000e02c1921742d29041600da00c418020b104290742c001110001e2601004640f0b54131a102c1c40a4181c1000d82d43da018511a00c2c1c00d0505075600b81000811b06e201d02c0d0903010312880c10712094070b094a80061b0380c0340c0704202c100400505205041003004052156640044061 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 917892005 1250 917890755 917890759
    0x291801141c0506061e0f0636030c0a150c03090b0313060612230c090c090321220503030d020405091018091b0b0706050105061e0711 58
    0x440a040c03410403998444046802d00c0c03244580d00043d041c00d45e00034069414942c401740281b258040032404115080c2c00c11003589003c24000c150a2101141d2030041401c60b028240885040c0340422080c5428071b0307200c5500ca401154006020058a00d947e001d1840d403001a02d40b000c0000da041c0340844490946030301c003103200c036804001d120074184124418240d081c442c18041021035a9604941c4001929075005003a000f0b51070030001d05a50410860286202a001a15072004805000407000e100c140d4a02c0405400426601107034142041104940405404000d46110141c0320b803035120700c01c0c10b00d0322030a100705010348000c0518842e0000c000c0c14000303041d6501d441081001000a4100f44a650b01c02c0490340b000c10424807101d000c11082c2c86014140c000e080d0748030301e41680903101c00502141c0100b4400400807158145070a005d0203070420443c0700340d64860609282e0161030042e0800c0e4450070080000c0c4103040455007104400d8600a003e0a4032003490303041116051110640d426 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 917893255 1250 917892005 917892049
    0x221060d020d0605061e010507020d0c03021017060604420e0a05040c05030f1812070209070914010f020c0a0b0a0921150b0429180114 59
    0x40400c43d01c0c0c1c2010307124800a45d10040400307241e1081c502d00d60f4210070841c0c0130030070411031940503062401898600318050187c4880c02d40e90795001c56000e803180d075004000a10206200100e00d9111101d0030303003003802122114203160a00c10160301a44e51045d4426484942c1c030000800740c0e0300e84016080384200400c1000340e0403134000e0b000d003181070202011489000e80780004501803500d03100c1c1c00b803201c3d200d58405e421682d68082e081d20045024020502415050303015001107042000310085d5085004203258440c090352041c440458805000c14080c0268460103115100c0e1221107915000d0003441c12180c02c01d04101c0036400d02000e4181107411058610b0301003172000030302c402884801220741c0e80181860303403004c0a80d00f4401078848020b001c24070000c00404610789028400c1c140c44a0781d40050311000f2480000c0c00c441c071000b441c81c025840c2190004600061102d403444804040d82c641c1903203200c440340501d595805000300c03c0ca001a2903043d25035070b103406031200c031480c5480c4409 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 917894505 1250 917893255 917893279
    0x10e07060906021219030b0118080a02120d020c100504090e03030702060f0c030714210109110f03061003060f030b010f060c03020c040e1f0b0f040221060d02 69
    0x284548640d006950240c82040c11303400c00c941002e000c0b10aa100d03030075401030a03003810304c1c001c9010300300080005040000f00c0c050410205a03c181c060020410306005202d00b410f288184809482e01e40141074480d0860b80c03945800c00e0300801d10000e0900110340e8550302c64006603054030203018a411496032245410901c03001d00304004021030044a41e43c088400a6503000c4040d4080c0508583c4c1000d07050050002c1a00e09025181d00900c04880b10803041c02c0510300300327111105081003143c1c00840c95106c0010002c00c4001c1c414a5980341400da034080c07604c820300d503c12099100c040c0c8440c0c0204001021030640b00d00c2580030001074240c03402880811030f6a410403043d100d40030f000c1c61182242c0c2100006900340a15280f81841c0e0b0700d5000303400d10614030710401c00140075180c00324400d40070720041d8020304142c4541050390004013a4001074800c070110709110100d809031030094000c510400c06190010041c4044a0700b0341804490070503103940300ba021a0100d030450000a4104080e00301e8 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 917895755 1250 917894505 917894507
    0x801021801090b1c0e0f06010e0a0603020117040203071701020a111614030c09090a03121506031505030d02010e120a0e0d0f05031201080c090106210b060c160f05150309010e0706 78
    0x70241c1252076027110803c0c5500c1c0c0d84030701001c998280c13000038041009100090b5810381c03008030a03581b15000400741c030041542c3c1c1c00c10303400b040c41c0c10001007144d0b5400900c219056401501c0c40300c143c0c0c0444024100715450000350b0660643c64001d954019045404079000303950300308000200050060040000790612a10441e41c40300c3c81d580440108043c010119050034203846040c03241010451603540c501d180c0002038004080d29010001e441441c04804100c54404204001c10f00016034000a00c0d0180d540c40c0509041081c0001003c1d04400c005070800f0980c8100140800740c0121070010030140c240c9004c00170740e41d0314000240140000b003080a518594201c8081c126050b0909840070551000e0810454100c2400b50784081984114145c008c0c403450f480e40171480446179800603412560900050796078004607580c074480d80c880c0310040b01c2c0150b41d1411000401e00c1c0024422240d060400248034054070b072004c0c414207080800000d600c840c003500004180003a000c2a82ca4031915040 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 917897005 1250 917895755 917895763
    0x1404050d061512020901090506060c150612030c0607050c071a1b011404080d1401080f210d0c0c06181403210912040801021801090b1c0e0f 61
    0x442c0c50004021000c001189160b6000001502d54010320035a50f580c2048080b8009110142034560400c82c2800b141540d28401c1141c50b000203603103902c01d4820314080c001c018502c41d0340e031440d55441d00306101e810005440082c246070826510709004c3e84a140010b00f072454800554001da02c0403030302c94075085840203110000e12030600380e038800c82804038803400390600340c0d2800403258200003072a50000d000b0031601f401402154034a99008161a9540c07a00c02500d0a030030b801120079504004100c07048210b0420007040d03441d40e4031030f0540700c400e000d04160403940586156240c0c1e10341c072000035600451040d8100801030340d0050341080102042010703405079040f400021603082054600c5403124010000548030b1041e00904e4000141c1c240840100401c80c0c0a4811401c0e442001e500c1c1c10f8000c00e00f0060009840b100c000107881d401c03c2c40030f02d0540e40500c4241e43c10300c00e1210b8240002041e8204950f41100c0c842d00107089041c0d000030308402403804c3c0619400900441c004621203ca01003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 917898255 1250 917897005 917897021
    0x61c05040c0e090a11030f030d1d0c0604061d040f0c0207060212090f0a270b0a1a2d0903070b090904150f09060c0f0314071404050d06 59
    0x950400c01d41c40d805941c0c0c81010a403440c0246500200032072000680c090448203c21074040c007514034000c4164900c900c0c5400c048900c0c0442501c03001e20f0b00c0250040d5503511005064140104004003000c0049859031069002d142e04101804084085a24100400158040d0043c0003007100800d02c8120385c00426000301403900500440c100000e049200040140c2240002984903150982000c100f102c5600c5040320305401100001000640c2c0416040b082100f48408034040c40f4003608042400454141000e910700c6410140801d0003d400202e0022092444c408030b40355031240ca0b0107050081e940411080c24a40500088548843e00c0ea5405404400016070440f05130319192100e02070740780610039030a500061480c2c0020042843d110140741c05170105040000c407801031020020584602140c2035030400e448090f0610800d5002da81440c01460a1908100c40d0032890b841010340340d0080d1042c0100220b4540403040381c0000011100208001401110402200d14003400502100 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 917899505 1250 917898255 917898263
    0x20702150a03050921091315170712030f2304080d110a060902150f040314060708180313080715050a02060601081909030c05010b04091709061c0504 65
    0x101164415000040c2e80e00c005e400380032640c0d100141c15032400201d800100340caaa210310780c1030f0003d124030f801d8031850754440d810940c1e802d00350b800c003c000c0c51000f8000b109520503501c001c0c2c0421030030490f03820f081c03c0103601d8905030704080340e04c050440e480e40041e5500002e80d080c54039082058900b02005000b01c44c0f01c0300984091262100090320303001c80c04440310549401039110240012026030285000610080c034040104054540303040030780c5c00007840710303a00c41e80000d0240248014644444426900180203001c207262800c2c0040002c0c001030001294208040820b80b1000400e0056075a21345101c2c07079040c02141d44400e000d41c3d03800c0a124080d210448588002d4400744200c0864400c0310b4a40c00a040c9900c600004441400c40101400d89020f80c1c000c40c1403200025000e404250b40c000d0f540c0c0602d041180c105a800c4031204940300f4426440d119007180001c088080107000c029450080c592a8104079001c188644201045480450300320280312000303803034592046001d5801 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 917900755 1250 917899505 917899511
    0x7020105040320030d0e010e030a02100f0204051c02030319020102030f09060c0307180506070f0203160f21060509070f060206100506180306090a0b06030102030103030c0b0a020702150a03 82
    0x1d4288442603d000c40c044600280c00800041d000264180c00c07403609600048000030301d070f00c4a0310b01c2a0550b000341c07140c01e0050f000316a510355009000c3c0114802811100c108502d400c0c501400203095004044e5810741d00720381c0c102d8003400e40d43c01b4000e80c0e60340c009040346441c1008240c44002c0c000c0d030040304c0c99507084800a0206041c0c48000402910621640a00c0b07807a5441e54802500c000e901d01c80b5030a81d84004690200340c5498000240524078810700b00c140d402240c62040500308a503251585100b8224a001001200a43e082e59400c8420118010b8001000e0441c2d2501010201001400300c50400081c420307150000540030049810000843c40b50755158000bc80e210001610300c0500301c0c0c40314006014a180c060014580758413503844500c0c44501c560046401c11108989403021500b00c06006001c1c131200070581d07580303e98106d00071031940d0705642d00503000520b081805042c5103401800240002c480c4d82c102e83c0d050f40c000700310241c0039100100c02c3e03d19900c68080300b800242 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 917902005 1250 917900755 917900777
    0x1209050301051e01150e010c060b0d0f060509161a07020406030809010206090c06091509030109080d0605010c08070f0309093b06180a080309030406030606050a0c0312090b070201050403 81
    0x10b500d492100c02c4103007603586d0b0b820b0600907800441381c03943d54440581303080d95140309030b0403103542d400f2980055920030b14000c80151424108003048400007407182a042d045582010586503200b40c110043d560401514558000c150341901058011244000d41003840d1281c08000d0ac04810040e000300d240c245e00700c0d54660b43d21003203e5114030b42d440310690845018400d030b60f568070f0300002031030301e1030051450a401d01083e000064259240759600791001400010310000d01515405880090700080c204038540c0c00c2591350b0440507202d088000790012180388141e8080500c9120072300001c100501003070142da0f0340c015900c002c2880b007107900c002d2003801c142802c0b0200c00888516a21540d0f080181c4003580e16281d0000344040c050780c2c00c4c0c0755401340e000071000040300c44014501031f0a07031200840e1200d0030070102500300d03200c5401480500074288a01500c156101c42c83c00c1d003d40c1d140c60188080e4521031030000c040e10005000030074440f2058208281e07144e05502c414421345c004d99450b41e4081c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 917903255 1250 917902005 917902019
    0x18030f0304180c031e05160c05030f09151b1501231507060b09090102041802161212060b0906070803091626060709031209050301051e01 60
    0x101c10351065010a400005084020788081d90000c2d20b005854200072815080408184601d030100783c00d20100c140c0c0e15030500c241d40496100d60a80d032041c03800e102d01d100103a1340300e159480c001e101c001c144e201c3c80002e44d0030f4103885908501041c1d80000381c400c3c0d110340039410365000015803000044d1262040c42100441460700040c1e080c1295903102000c200d11020507080d0030481035020385039030040244100f60030311141700001480c1d0140a0340001503140d21071010440e400c0d40182584200b0781c018403051191200800812240e506403000040c0d03100b65411249650000c80d200160101858111104099400c200c2480765010000010012903895180e01a81405441c41064101da014442400001e10303a8004640050002040307924181c00340441209040311500110030b10b103511f81d005da01403448002c1603032034802004040c000c2840c00355070003000070100d0302c0701500707007501804044103881c09840342002030140500240f1480c0350103000e44520b811803000c102110007264000003014 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 917904505 1250 917903255 917903257
    0x6011712040902160b090a0b010e09030a0c1a0a0b0415030b06060d020702030109031e0306061409040e151609081203041e3806130f0218030f03 63
    0x103160003054590819041c0412a0000d410540c4405a40c01c103003140d14000c12040942144601d205000509020b41c444c0362041d082c60040e8400762485079400c0a000c8520f5010050302c800b50228944000c0702c061900348220100204100c191040d0192000d12440c0941504100201e0720250303003d1041c101c01c86591079044a2038440541018000004078009107020340041103060890040581400b106400103800c41c1c407003d03011404030301d51f0504041c0b030b14828411134145902c40c0c1410041c60386410301c0a00700b141c2d41c10862001c3c440000740d014081e9142e1344507412090810003120704903061440c0700030144205072222505480106114000030303100f503c0301c41c2500c507164007030b10800701e4290311400705e07820160045640e220180607811043c4010440158002d0007007507101421403a10000003000500b0b1041e110002250800c10b00c4007070102e505e081d803c120241c511411140c88a03e5002c008c0030042d07d900e003518000600507217010030800c40c245a480044042c0d44600040040869503 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 917905755 1250 917904505 917904523
    0x40b0708070c0303181505010905060a03110405180f0c0a080706170603030f03040c0f09020f07030809010608190c09050112030c02030c090705070b09010c0c141608060117 75
    0xe60b4103030240700024825004940120041c0c8802e8161180390f0307407107002d00070540e826003140700d80d504010001d01d0298050b60350403003070035140c10600d9410b41c0c070340305144a064206036000300e882e407000c42d00b6580c042181490350319255059440b021900305005844410494006108544115000c00d102da4080f51034012110962500c0f0031754102e074885094690401041c80f90305002c2070040e4000c0410110040d84541d20400c890142e4a04200180e0400c1d0a103412100f999881400703174a00b41504001140d01107605810b15442d0b43c0d85040d801405071442d0b801155190184404044000d0b0101a60115071849409000750303041c0c44040311030490b28244902c80d80f400301c5d00900e902080c0031704034000c1024009410742e40300d600c40340041840403e0a84a010000381c0c0041c01d04140040304c05035503003020750724000740300c42d00c1c40c0320001307103076088a00300900500590070f000b1961200802807802020700d103214000c10b040e941d10040703031114400d10584484429504c05055491004541c1c040 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 917907005 1250 917905755 917905757
    0x30506011b14010501030c08070b1206093318091e03040e010609060e0301090302060a1a10170108010504080403030f0302120117120f03010e1b0d05040b070807 70
    0x100310880c8119200402207021020360308154407103542156040280070b540e02a60161603ca00c0a0740381043d164075000441e0f02841c500003060052582503420040401e03042030b0115020f1030103490700c4400c0c092014500007585c90214a07000903101c4104003248801100d40c040760300d41e81e50485c0a501703803c00b807401c0b203c24001d0b400c2000c90103149401a030003840a1050542101c0c146501c2d07014505c1302c20020780248010800038042044101c0e48011013100441d400e5009100240007903078041c1d80c50b00c0c045c040300301054030703103d40421000c191440c2d0006150000c0c04081440201e041c05058080b4105600703941d66107580c004680ba100500405000d02e904c0600316140600c0c548041703a042080c07042d04010550200480c07608034880d02e66041c040c03c201500d0312480041041d0301417401008810708000004144050008196800140c0c0d0441c2c50f40195044195644250008025090000e030030703101e5408280f010300031000340c1c0310300d02c40c6111f00d5600e009902c0d807150a9560f0f460449e1444 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 917908255 1250 917907005 917907017
    0x30b0d08090909030d020403061e0e06070e030120041d130204110702090f0115090b09040c090803040902031021021228060b06040515070c030f050c0a050103050601 72
    0x90072a0400d40009640301d140c003030541c2e042c00700c50b80301081642d00a40c001c3d1420740d1030f50f241a010742460001e04004103400c180c00c0100401d00c03e401034890f103000700410248a18140f03900000e0303c081d00802c42c0b049101c10034a0550007403c40c00c0155401501806c040d0000002d4003001424080340424000c0b50866a0010200503590805c4082c0030020100780403107006100d00001619600e0000d40600084004400030307605200b006d0400900c0c11007550200b04040a003040800303200411501c04400c191008640762140c1d075003c0d00c03c0d64240d800304100380300009001964030056805140030341d20308541584001e9448000411402c071180c08103942c42012810f56005260582c6542c2480400005541400c039a01c00802c121035290f44101d1200c1c5042000d5004024042c451440740080c120b8029040c1410800824820039040314087d1081c071001a03d41c5c1802099107500006562240e000160042c041c9419611181c0c020b44a50145140050129166000703018281c40342d00c06948131 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 917909505 1250 917908255 917908267
    0x812040b0d0c05040f030302060403170709050906060c0d1805030703020a120510051e090609061b0903032a062a190302070c06140a0f020c130c030b0d08 67
    0x2000042003602c00000610030104000036402c03258480001c02513000b5009400355180c1030802402da80b101c0c0070718500d0303500d0501c1003113040f9030000614001e07138406581c9450a0f50b11400410024030600c000c1100520840c0031483c52540d105500c0c0c01403003025001028001d68071800e15685101600009600c01203409081c0401c034103110b000c030b42d403500032012983c00c484448204411560165441c0030904403a440000300001c08982e02170704801c6480050000e45030112039a502c0b580098071010113640f1038210740c854080714600b526580d034402400d481d0b5400c4903e90b401c24020b02c442c1040516030311003501c41c03039000c008500144070300107501d04041200c03410080c4100060b040300308419614401d0160340442c0182c800111031060460f100107a9413805400d102e581084a6030007201003240d0380e8107118000000e103040c1c5031480703107500300404001991007080e81450b2031300391344a41125104005018281c1160000c0d100d440c40c5450401044440006100340c0300c00e02040038040706410401 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 917910755 1250 917909505 917909527
    0x705040506060d0c0f090b132117030a11120721020f03150306070f030b0f03060907060306090902061213020d0f150902030a11012001060812040b 64
    0x4219802080209050b1602c1c0c80300e51103200f1030781100700b0400050a2142d0400c0c4d00e0b40c10042c800080c000c14800f850400091000f403100d01d00c1180145001d100c4e4a103200c952038500e498409c210f166001c2013007801400000b0840c20706410440c4c0f44c0c150181425240380010406c1c604a408061200f050801c65644550050354010445252005000122074000224070030502c080d2910020103021641c3d2410400750104c9a6100325030064483d0700480d00740041a0313000001d00810000758100840c0051080000075000c0309030310035041d0140503400c100b101418001c140001541d482d80c4041190503120000c0d50100c4110110003500701d94200711172600f2080014216502c080301c201e610700ca11510380d012558034100c0c00340441d01d44c50703410032160400001c0018002c01c403400b24810001c004c03003500000ea49020018018108490100c0d00c404240d00c103081c03200b800c044001940c81c4409451420764004d141a201e048114024030002008081104044401302c42c1e00095084c1400f0418103 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 917912005 1250 917910755 917910761
    0xb070309030c1b0f140310050c180607060c030b03061501020304050111070906080d02062a07060912022401351212070806030304120501090803280c02070504 69
    0xd090301d41010f2400000741401440c40c03104080c004464603060012100070505181200d80b5545031409400c180070016403c40a0703055a050200083d19943c5e031926900c081486c620403103001506041c101459440c4503074141c1c005001c01c20050707044984036981c42e081d03400301110880701f1301d0040c0c00411081080b58803070709000c9081b18402e02130f03403c0d1503600c0506808581e03542e4000c0d0910307001030307807660a10750f014007030541c1c040c2c0c02d0030b03030005110341000307000345013201c40540b8035403000d000325500c4284200c41d400f4032a541d601407031103900c10981d444047c0d640c0e142200001200340c08100361610384100307101c2a90484401c45d6041058a080c610112081d00101d0107100c0c21040700000320300b20000400600003070700703104800540d84a407200c6a01c4803084004040b40b00307010018003032002549001044070100c9685210761001d003441c5140c4035001d4060654042c05000001c0148005483e41c4405401d0700341e81c020b880d000066801078034009440352501c00501580040008000700c1c20190 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 917913255 1250 917912005 917912033
    0x901050f0a090201050c010c0f08070504082d060414010e0f03030f060315040807030e03010219110c0a0906090b030a05060a050c07021914040603080f0717040b03040b070309030c 78
    0x418202d041440c0991b0340c5003140c40301d10440340042c003081080e035010303034205ca40f49402000c1c61504070303d420304018a05a951800014980c5070200c82c0e0714074134a00ca45810b8000c16425010203890310342c00c0a090860181c249005540b41d194a05010600e90340000907051078880301d888041c41c21966654840c0910039401041d80750540141c0c0702da011040101d50380d06104501c1224040d845419a003401401d00c80715003141c5000703070300c10048040000c0c002e40d1102da40002e00c0ca0885010703400b09020798140030910803034982008400c200442c2400b42c94010f4070640d001d00d1800c20913030003100101030356180400009059a0808400715501601941000d81e02203110b00302c03030f49441c145502240d17188284d020f545102141d64a400c0c007203071640c21400442003404135400d01260781151903071034940c0718115004140d0040021f00c84e04000c003204501c0400c1641c0f0180385c0c1c94503516800c0c1002d940c03007120202d030b8080d401000505100d010b44a01d00500d501550380b0039000040e03075920120b101c804 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 917914505 1250 917913255 917913257
    0xa02250312080702060604050108190c0f0b04030515101509120b06040b030c01140d0b0a030c093b1006121104020711013002120901050f0a090201 64
    0x2040080085121904090021001c0d6aa44500391030070941c02410284060a182d115074140001044074010000e21840858540c4070002009545032030103c91152542d44110030300b03209a440050002e0220010703100b10380c0240c046d60341564503030980540a100c1110090700024858034284142407a40c070750407440d10024201084515190515103200b926503d80032250701d0791100070070500d070400380115079800109400900707a0040c0341c000605140fa4441c0e90401000011450b405e480015421142d00c0000141c1842c92654880c102105111040d01035418401d09040e44100f0b54001c607821040c050040c03c1d001c0aa040030300041e4400704548010300c40c00351040704440d000d044950301c21003006003075000701844400400e103405442e141c0035600c140c1c41584148603080c00b04461030b259442d08a805d282c581c8540e40340c8510b44d240e24070700c1035202040c1e0317031503030002c06070030650313500408403d21440d07906041640d130a58403074280c4000b00c6041c0c020042a0020880185d0903801401c185441 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 917915755 1250 917914505 917914573
    0x7031211120105120604050c040e150103030801030b0711070b0c0c150a0f031404020f01140a080708161218050105040c030210090f150306170618030a02 67
    0x1100000303542088541841650492004000e58680b62500c400303040d1015005d01007078907140d2512074a6007012010b13503001d81e848501a00c410715051114032204a05c0755171306401d5503140d090042c4180002d0004850000d401004103034601d004950a9030740da00c01e60f00800803e0304000c110001074001c4c40e2000400c0c450f111141449030f0359880502c410802d03601000f5200c01c20160700400c89490041504140340c82d0110b0b81d10b50000900308075500c1a0162004030045414400403100c1014200f030b00c60701d0341c00120303286168590107141640120f26550305c2100741c4c1c47e50504201c05445124601c008180c440b44d901d0803034000c603045200241c5083e0355425800c41c050701d0741030944d0750454003100d81e500041024000c51802c0c181c41d0441e8109881d02c2c81c070803820580c44045440481c003a201e4090707503800e140a1001c0c071a40081000e0104000400740c600b500f0a6907581c0c0e1501659408a001b6500d40031184080002096800300401d56000781944030383c1c400e40a14401480303c0081f4101c030 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 917917005 1250 917915755 917915771
    0x18080c0d1a04050f0c1c0b130f060c0f050901080a1a22050a05040c090b030c041a120d1403041e0503041409010e04021e03010515091b070312 62
    0x10441d042440307680944044c000011070310842a042c284e1000500744034550058241d80b401c0301503010040c0f516480004034080b5200c400c07010044034546d240062517202c0c80008038017002a1074110115103000c50f11610140010700105988034040c89022600003031903400000c2d048030590b000f4003551213050b4913a0703064660031404560030f8542642c00d5503502608030030902c1070520718816240d004086650070005400d183d07071030400212081c030031a905542c44030715a40260350305225641c060000140108003810021030740c0c1080c2d00d440003009125001c2c0d500c83c01180c0030081071201c03141c65180e50711061210300c1d03881103c01e604050000c1d10105a4000d0941103035004495210440c2d0061000b541c48030720300803904040117010800c080c0213500c40e42c0104561100444841d401903411035842180b100e0849552910505c440c1606505600f82002c1c448040e0b00e6406a186020083da450030041ea501c8481490458545201c02c40c401c00420101c03000c244201d1001004405920003c00d92803 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 917918255 1250 917917005 917917043
    0x70e0f090108030c0f01021608070302070929040b0109050d03090308040e18010c0e011b020301150503120c1915050f0a140412030b0301020f040b0a18080c0d 69
    0x400c0c01d07044442264000641c5050401c010070482000000e1040294a0034104079800300c103180c11500c0061420b5004112901054001d010100250016110170404c1880b5040a5424188803c115404190313090762407080318185400349003100b080c10303101ca54940340780000340410461080790030f50401080b840c0202c00210305100420042ca02c8103145285810107004080400078003049103000c0c0e80c507258180c80c400746c100c01e5041c0401000d0a050043d0311210b050441c01d0495450700030740c50751810090755040d40001c01400c1c00c0d20b01c2681207914030a00c510103440e4a10034000080741960009585421041e190107031914040d124041f00303600000e200b0100350580354251403807400341c040d410400c048411036214480403c280e0911702005801c040d211482040510f8034810101a1216540384c000e0314250104c4034600c924800c015990b541e51154501203030050203281c00065200c0141424000c0100980c10960384040094041600e00c05c08100001590070011205042031201c0c0c1076841c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 917919505 1250 917918255 917918269
    0xe1f0e0904060903090b120408180d03020a030909020f18271603141506130e060f040b280f06050a0f110a140703020402030408040f09060b03070e0f 65
    0x41c0e11400d4003040003030345460042c0c909500c2d5004030340b0041e0b0501c60003c8240460448a8209410601d6203994602141000209442c00004127800101c0003848008140d400035180c1e000501a40d60405c4841d242c500700c41c16885101c1d9650740c00c40c0c0602214510030340c84500b00c040b90000a1031141607442101ca10041c01410000c08038440140d0350400c800007011072100b510340500342c0390400c00b4800750b003c2c8940801c00540f207401c010048445011b141d403541d004840c0c0100310035044140c0b20350349400304c9400d41001c807101d03406007000550405980c1014040c1c0c0200d0b0360001d001d42c1e00d486480001c0c07050140360440c5000c015030358000002e00c01c03407502200c0c0090041944c6296603030b0018080984000f0591401e0b00402c5031500d01205c2c54000404c08171f505640c4003940101445009480790310b0000681c2000e940f01c1d1001081c4410408020000c1c821150810303030124a1603500c28080301250943d2290045110381040051181031190358a25030382c13840140700301d11500001000c6108 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 917920755 1250 917919505 917919511
    0x4240b13080d0504060f11100b01031a0d030c1b060f080915070e150c0601030c08030307050f07020423090c03160b030c04080a060f0506010e1f0e09 65
    0x11841002034901040391455000303402614050000380201c02c0040002049440b80344240c4082210f039664002c0f07000d20030600c3d01222118542154200120110b140000b0140041c1080c0464a40460011024804c64036160003003401090741d115100c0984068868101c4ac000844511841c104003844181048102401404e07640c0e0380c0c4151203020712409010b04601a08036440c6034003a018003070a2032800d0078403030360000c81031506440d050201e001184401c43d2403c0d100705500c5012500b0720780c550700068032a040302c0c05003a03101c03205599400075540b207100c244e40d402e0005500b080708c2504035800c00018102103102800018a0101040c1c00ca25000020107401032480c5241040c81454441003001c241643d40032006888030030003a01d84a04d0600c2c140c82102d102c000b000c00003800e000d100d0006c2d03c0042c031115081e40c0300c12280d403402d1002000d0000b1040d99092800740401c1f400d500c11403481882c402c000d0001103007400700181e442070150554442000b00150350300d5200c00c1d500c1c1c2c2c0d2034581c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 917922005 1250 917920755 917920769
    0x313030f0b070c171c0515030d1d0603041e0510110414040902120f0c0112110306130209030d050405030c010c050d03180f230304060e0424 61
    0x10300d060180c034000c0d440460203001001006000c4440c4404145403855504000c50b4040e00b00383d40340c020880b10b9030b14201c95441514118504402c00c2510040461460021b1400300c09030364107450000070030307604803c451582441e0034290501d01c1401c1c0c140134004541060050f828020420800c403000315080003581c0d03040b90250045141c1001d00c003a10f000c0d108070300d1407407500241032a003010a402c0141809c544000e2042d42c43d081c0203415504c0709001804444000c901f0394100b88200c4000380d0755817044210a9001902a111200004450b071140d0140d10014448031859500c0b4101000444800482405842e95080104200315682081000c1d1140542d88a403030711280383c00105810400d5054100e41400750f42407180002a1010820b203244102074100010300381101000099001400d0700d001b04611202612941071107020321403548040c000d241c1c40a24422044681500c1e401184a0103010500910181a8a02e0560401c0c020003210f8404480b00706185286074001d030134290301c0741e0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 917923255 1250 917922005 917922023
    0x102030f0f0d0615020c0d14030705071d37180201030f0504080702060f161103010b030d020601060309110d120f2c24040f080c13020c031303 62
    0x21980b64043e000f603a00505000d0141040b0f94180c04010303440b1a0600e442610500d4544020300c2000100318a4502401c0a602243d80b2071129241c0350390358544501848550b034140568400d903400c0c205400b5442424002e1003e1400b02e13901d12098640900e10340b143d200303100c0e11070030891001c1c940e116101c0c030808285441130000722580005001ca40003400b40124143c244801c00c0046103424040721901581500c0380d5641d424100340517003103070003070311040003480f030414a00a0034005414120002d000044000b0232861034540100b50707594003902c4581025800200042101c540a540040f000600079000c2c5060781c00740900191000c0d004d80800c845141e030204458200ca9800282541240c4250801030030070288401e40c2601d00201038626030030124424461140d42c2c0714181c8402c00c103100716903595080f1031851883e540c035810601030040800250f000001d0b80440000c2c458140c48000f4066060380300c030b036a8480c40a90b0065440130002e100c1003094501400b4559014001540129508 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 917924505 1250 917923255 917923267
    0x9010f0c0516060e4204080d110105040203060609090705090f040303050f0f190222090c0302090d060c030605060a09330e04060f030b0f130807110102030f0f 69
    0x2404410440340d035180107030060400306500b100880da400002031141c200c0348816145408600394450324581191032174410100b00003910080c00602c003112400591103041c000200c0780c403010300301ca80c102c8019505911450110f403450802c0c4d03840580145004040d10700309501c86011440742c80090700c5c041000d045040400081c15454801d054011180c0001c8026034203203400085052840a030903095030340e00b2120b014400301d0107507041b141510512034022180f42c0502c0c2c1451602511441110942804c111580301014840e100320b44401030024078005001b0016240e107001807007034903480c1d03062540c1c1d0b45010030640d036004050100d240882e83c40d804a6801c1c070b40060110b195203003c188001641c0880d03c010300c240611804070080f56803401e0040c0302070501c00100a022154410b1141303840307890000c4148502100154030840c0300911aa0071511349820032000039038032910141c500e0a05021100001d41c110030780c0e142405052040341d0510b2907505c03800302260b01034200f45100d8000040e407 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 917925755 1250 917924505 917924507
    0x10218090a0c020a0312061a030901112104020a050a03050303160e060f03070e040c2a0c0308030c0c0d0509041a031e01090f0308060109090b030309010f0c051606 71
    0x110340d5000c81503010a000340300310000040e5441100c00e10050500a86500081000c002540320b90014108640551400d5135542c400181075030051300c10b06d116508200081a07101581812101c034240c498407940d141d1540300034071030000d102c058000c03a4003c170150380015895071000406000740d80540c010b1562814800c215000d004580001030051150307079805004160b80741303070070381d003903216440c03001c99903981c5500f000c80e40c070100c80c40702d10742c418500011f400350664800c4414400701c0f008080400e030300c000006d82e10900510003400a0440d0900403041c00012481d0b4081c58018414001c9a8101007914641d9810034108801080c0007410204481c01603203810300410030b100700c190300c011080c540144003107a2140340321201801c0003258008184115002540a1006a9003040d40002c541c40140307002440b051085c4d0300540040d40322013001c600300700940300c0d1510514008004510b0181c41c10015202e45182546c0001404419110680414018004507010b43e4049110003101e81c10260 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 917927005 1250 917925755 917925769
    0x3030a050a082202040207150905061008030903071401021c08241302031305120a03060602190b0403050403021309170c0a022b0503040504060b0910030c030e010218 72
    0x100750f100012882400000c1d400d44407456000f54042c1c81c00750b9285041d003010502c101a0035442e4008900e01501042441408100c2c1130003903102010844250740e071003103502c2e50780c0541e501191341a04000780400500608030b20032448060180151103000314420502d10700e540104045a0110701340300c00b0084042030210404400d00c80d03451480b0925074200d00840c6044208004c0e081041e41e0000c00315820a000c8440b8503445035100c8111200c200300100340000d903801c00c40389640881d081c0079000c03a99500103c0c1c1501201040309940c4865034151f02c42c0c0c4685171000e00240c0038004c003000301001684419035036840c0e202c106e81020401c6070b1149404480005203041028034002c050094004051020a0781190f60303404903400300e252013150009415440d1040400115107000100882c100900880035104a5400311410020b141e650f541100d0540303c3c80c070312654011200c0d0004c0346854003e6200d160350700d00c2458002461524a07480c2422a40036980707400c800c2001248288c2d00c0d2602c03d03 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 917928255 1250 917927005 917927011
    0xc0c090905030702040905030f0403061d060121150608160509010b1b010204090e0703110d02090f10050301110c0106140303030f070c0503031302120d020304090e07030203030a050a08 80
    0x104080140042649485882c0c0c09107003c000d10464a506c8003405201040043e2517400c0101817540d07a03a280d0b24600100207002d1509103110001000700e0039411190701240b0507048503452507007548401c1184400c241c4c440d80c0300c10212968402000c080340c04002500c1050042c1072203000805240c051103c50514105040c0e01c580e11903080100180880003981003613a5070981e0b0303c0c148140b80102c00d541d090182c051904201146c514003401c0d40c1812030000392000444e40200c0b801102c0001d907805110002680603800f0390445194000b00d014a50302604495112a00c011402c0c4881e44400000317095a002c0c00b840c00d21904041903480042201384560030091138007181e400d6000c151100400c0d120300004002c8690134082800044843c0e0048201341405584542034941d03e1a0540c0120500501c11a0980c05006103009255000310006140322940686400840c10a03103440b24540140055086c102c3c080c4c020100000010303281003002c1e10b4490016164039807205810b0b0001801c411000b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 917929505 1250 917928255 917928269
    0x11090c25050f0d0207050f040f051e010e0106050304031209170c0d0806130b0a0e1f080a030801030b060d05030f09040506150f0304030302070219090e0114011715070c0c 74
    0xba00b144180c013500003c104d02146c105955026212800e90700140040c02115403030410b080c140400c03c40740c010a84025400c02c8144002d410150b41c0707030414a0810042401000040341d420000b0501281c01155001020b51441102040450b000d94071141d100b40845010390000d5000714800160b070b4018401c40c102c0c14010b140100c2149004c00c00100350b102082400005150341e840d50102903194101c2082c041c0420066034001401c01086100c5000c3c52940c1c1014484d050600104080c0710100e6101001501b40d5581c561503425500c40007850000a48020352140c5150720100004000703002800351074469103070707458136042e042c0c00307210036250020b1006210752450900326441c04ea2030b00907242404c012083c501d03184d13900c0d0325081d4005d1181c0b2001030b600610b24140d000308c406801e05010140d418007841400b2000d40b204640c1d0070388122024514141140d90300510040b04500b0003020240e00c90812141d200080b02c603c1c044840d41500c50600242d1142580805e0000c11301d80e0b04014944 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 917930755 1250 917929505 917929513
    0x706020114060405150303130f060f0c3314010605040303021506210a02040f02190e0310060609080c01050307050a050319050c0d05100311090c25050f 66
    0x9440720507062030024546841295640081a0b251400c07400303407100d03420040c1c00c40b0b40d103442025080d581c0c1d01c500d00c99682da0007107042001c10094400c20544030341074400e8544164200317040c4d82e1320810070301c004200003401c0710300800007149a1040c0510602c2114000d4002083c00c14410f0005980c581608003d0510408010400000340e001403644079481e0503072103080d0651112000035a42410a031014100011403c0014011172800304207110a00d00c201c404101000f0f40c01d44100c08c0e4010381d5800b100644590401c40d11403070040150b030100c9440201603c1450303074000f014104542194001c1c03400204200701c240300340d14040001e1490f202e002d0a01600314030740003900400521070401c012082280200101340d90442d040b03492a2000c490700d00034044d03450092607406150b00800b0440200b54140700102d48940d107400003c0080e81c0d04002100d0420740040180404000041c00140301c0700400c00c074220400c2c0140c03480307500030700031203901413851080c03030510618160b5003104002c00347e08 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 917932005 1250 917930755 917930771
    0x803071110050f0c1602030604440a0c020406030c030212060603070332031909031104090812240315010312030608060907081203310f050c010207060201 67
    0x1450b20003c0b41c0c40f00c884205560b441409401a041e803083c0103000a4040c865002404100898031150540b0009450500f92480d80c00200c4114611600c1d910003a400021ba04060740d4240004001d22030302c8001d0900300002c601645c080340444840c5d80c016108408504018021803174a641c03003811144401c00142038a0400c0710020780c4800080c84000c0c2811000c03080c030f40a00e42624501310500c120000456642400e9001003a180e84c44401d1000854401903e030308611802100d5001c152074100c145103951a91080610000348540da0055400400c21f02040000084801d081c40c4589650800f04503e4281104081c022005000c400c170721075013202120038620071703c200040d41100c3e0022080d1040c640c0080054000741b0468119401074010101003080148002800804451003031048034000082001040e09900050300c0c250b40400d000101520810040d5010107040045584003001e255440c0d981d0702c200440b0f01c14101e1b0613401108032160075680522450b0300520036030000b401441 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 917933255 1250 917932005 917932021
    0x102220f140a0e0a0506010801051002031210030804090903020d080f34080411060301030c12050c1f1d030309010c0f050d2706120f09080307111005 65
    0x81401000d56251010301c00c000703140d0380c07074111900400002080034400e042c4042840007400c82218070700d000c50148400050b0b40d00b0320710480d0750480300d19406981041e101c80c00100319504090802c0810ac0725500e8007002242c14a0020802840000c0c8000352800035464045d0a0104241c451024003410f5010010101c814003d0749901044142d01805241e040100c4041c5e14842840507501c54003e041c401a0b005400c00c0b00e1034080c0b801181000382c3c00c0c009000700314851100b404000c03d81215103908000c50482d040017990141c0c45802600e40711200080851140007000004800c0141c4000c1000c640301d4003c101803121510011003405050210782c0400c0e80c0e0f104011005c3c1c10019410000750500c136909086034445a800021358a00c854111070081100380701c422000101d50003081001c29034a007110b0284100d07109900c800614034041035041e00105400222000140d40b500f5807240002c0c02c841c01584a01070ba0b869100140310f00e000560b1900388140b4003044400d01d0a02406414 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 917934505 1250 917933255 917933279
    0x1b0304050a090b012a0224070b040f02060a090509100506040b0904110a031b1106220b092a090c0f1c0b0f010f0905040c0e0909010222 59
    0x241d104550b0200d4005a007000480300d203140141ea0000d40c880d04182551000300000090380c00742e00888000c1d00d401c6250000c814445080020742c03a03d0242044540000380c1134008242d44540079140650b0007000365004655250300414185c40000c0c9050800e0102d0718000041c80e80000c00341d0710b645075144c10031000c100360344610f000c0ca007043c3d180491102d20541c0c60ba00403d80100605062513119490010041c3c00f070900141c0348200051511211f03103940c0d03c0b80c580c6400b03000324840207001640380c0502d22001d59101141403084000d00c1d860f0000070030745c40340e40380c0d02070128071005044174203c41c1001300002d4203103102c01038122194040304415a65075040660081c8408130740a50750031460108101d18800c60004010b00440600310030761111407980081140e0500344d0300c28042020340c400451300f10610280c6800492445001449542444d40c4a40c000071043e003404050b18400900040202204803466980740e900054002c2c4110002102e00d07480b038804c00d002070340c1141402c0f000f80300 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 917935755 1250 917934505 917934509
    0x605010e0601210e070e040203010c0503040b06062a060103050d0914090901021b01021e03011539060c030213092003040809240d0b03070312051b0304050a 68
    0x4021000c03842d0034906256001403800311444d030854a07425603500c0c000c1001541180c0680c0309501e003a4070030f00c0d4580200101c9200300e9101d420780301d0540d0360001b0402c16400c05845543c0499400c076100300d4102c11048800605450140180855032461030710314a0000ca00c10b41500b0002c08120802600c0d450202c0c0d40e03040c1ea0115460b400d16541c4407200c60080c09061510300202014000310103064406600814541c1182040d0403044203a85c01c11842c584001c0c81040420f5501e00c2613041060b210f001008403104040d480d00c4030701c030303030814004c02540d00a034640b4102e100040038480800c100c900c94020303464103a080c1541841400084040e018500e841140d4610341c6550300c0320716030302d400c618046400d49255106600d908040c20700d246660441481c0740d00a07004000d00d036500c088100107103400004098881031412615002e40b00c00348c008030217500c0d01441045130100c0003c0856000307a1040c205035407050f8a4100c103c842c9064020040183c0000d50020401400191244018041 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 917937005 1250 917935755 917935787
    0x7090f140a020f090d050312160210021c0f14100e101203050d061802041d0105100e0604050301050f1e071209110406090b011205150f120f010203040605010e0601 71
    0x1c10901e171800d10310b09511810380201030001c6000e04000110301400d1070050f03288840e500711801800c405114400301d02c0781c2c500c40d402850303025403c82d14150158002c040c1d038000d0490042600c500c0c00280c04001c1d80c7c1038591008c0e44040c24020320661260803400b660008030b0240d070403015407801c3c444c4074840c1d5000c5009001c00c807001921021035011600190000c18070425070f00f280030750020302503000b500719004011242014042c00308091042044040c1070703450040c0300340600595010f0a0b00d44d501c2041c030403a0417140034000000d1540d002c1c441c2c0381c416131600b40c04103420311300603404982d07925080380f074844641886414002c64075071040c2428103e1b0040c41000030706409900340800201d48141c1e0790fa40c018104440459000303450b8000b802e1210080e01c60031070b285e5901b240e100c1581d608a03241174014400342c0d0035008518129030707901a4200d0150180d601840210509400e04400901040d9141c3d000018070042012600c43c1d18010a42d60740c2d04842402d00c0e5000130060450480d01d0f40f = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 917938255 1250 917937005 917937019
    0x5070f150f11120414060108150a1b1812050607140c0a0314190f09290a09080a08182b02011806020f06010503070b0a1107090f140a020f09 61
    0x74100200d01c4a12001030151100722011503a568090a42e100c280329140039a070348000700400c0c0c4100b00c0740a190202e007140030410780358141240084481c2d0143360007540ca030035507685002900551403507a08951901990280110b4a89030102401c11508058855200b0100f04080d202c11080400c00080c81a41890b261300840241410502107008a499401040d540da204040f41f43c0c0e0000b610303820a851a4650141b8036694400c01c0c2c254030b461a0084900000484151190b8182980101000401410b10f010400d450318901c07803070400c25000440701203000082100b0b00c0300e04070340701d8001c3c8a0110303203401c5a100c040da0062111025440c1c3d404111701125581c00840e8014401141200b660910a80070161703100d070000c1d51040039615004041c082c52001003421b04003ca07900c8195900641d5440c5410400c210444510307001104000340340c0144a000b0881c9045070141070880445030001282198048121245060703000d04034a41061040120350314140300042604c066030001c450103 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 917939505 1250 917938255 917938261
    0x9090c0a0c02040f0c14030105151b030310031a1009051003050d0c0303050a050601170c0408070308091c031d060408010e0303070807081003110105070f150f1112 71
    0x180c0e007507403041400035441410403403460300d9907246922105456019940342202019501c440d80d201e44402c3c0549504000300045054105a916009180c040080e5681c403029042c5442902d00b160010380d913403800c16844180800038004103000c0626460780d2155940e010341880000342144180c203110b100a081c1d255000200d4039804507640c0310041d50030074141e0b07601102c0100001c24010100100301c1c0420720307000201d082c2c10041e2144a00c1260181c6179100000e05050240010101c0141348650940c070810000c219503409012a000031440f410006032a1003c170b07010805019480c1c40c440321202c064402e003002095002c2a0000b2104041c0d05c01900c0201d1900801e4030781c032881d08010701e15800c00200e801d00800010041d48904120303a00c554554031010012102d114060f22001d0510410007000d0020a0801c07019034689101410807500e010826a10740ca9001c44c2c6400541e400400c0f00c04010045002d0f00552548014250040281c0c01ca15426061036003d80d68450302d42c00342140c00 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 917940755 1250 917939505 917939507
    0xa090206090a0920030c0301030201030207050a41120d0603020901140a05010c050606191701050106080a0e19050304120501050103150902010509010e06090604080c041109090c0a 78
    0x100d07800203402501145a841e110303507041d00504162100d4008140301c2903c4042030700392003001e07030b4000d200300b181041c5140d00e1600110044d4100071800d58a600a017802000090040240031101d141d11a0851110100244245840100000301141c01517041840c524010602182043c0e140c80020b11140e01e42c590100f00340020040f940009400000300e2002080003415525154103c2c3c80c00c843d019581da032a40011a8158110781c4010300d00d40c020804141d65103864088544080e100c5c1882d0b00da1980d4480c807443c4c40d0040580b4120550350750301c005020703107640410315960281800c1c0d03042c00080c5000c07100aaa4480159400c400e001616544004100c8140121030040c07049450b510520101410528001c210a20046440307031006110001070800600030351510b01d030140c541f10b04007180500152003044907401c4040c0c0c80841005141000d80c1d540000d07101030100030005101301c088110601048480c04500c0040b175038801c2c8910062a03480070261a07010f5010400281c0700c03c01848 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 917942005 1250 917940755 917940757
    0x18140c0403023d020615060c06041509060c0e0909070605070305071a1602070503210c01140a0c02012403080a210209011d101b0210030b030f010c080a090206 69
    0x52001c40d44211246450040d50001d000b46c000d250184507007501718040c00401c4000d114980c0e600e003072a0051030006010a02c9100040c098440c0140042484c03030182d03440c0c0c01212102c280142c0414440444000307070782030917024180d01860740001002924180200600940544100102080000104401004032512800d801d039280030090f449241411071048078240c861412a00040c0310b101d030006101d14000900e00400010310846a82c030885100e41c46000d131740440d500d00780e550340301c2e40940102d80c0296096842100c011070000b41001c8200402402d40d6041100000c0b0b1504080741607080b0f1502840041c00caa40c0102025a0303401c210100362044030110361420841c2d040308110300c031750381d03000d8004000c100303400d90b942e41e0360440384d001020804145030003032178020713a4031074070341e40c000b80102c5207281c1003040c0c5034034503150752074583c0040c02c0c01c1d08100300b00b40069151104c2c81818141048418102c0038010000d2206a000800040600f4030003800d03413034607a07119283c48042d0b4840e04 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 917943255 1250 917942005 917942089
    0x24061e091502030a020f0723180f06031027032a11010216090e030f0c1005090303090a0b0402010504080a06150501030606020a1b18140c040302 63
    0x207080044141c5041601030f40b281c12400660f40940030320706198517891004585402682e00a07100d0000040900f030000310302c04009011560003404a40b00c0c4502c01445045a070701c200c01340c80c502c203423500d8000240742c100070240c0246102107081c00925100107884840e21880c3d2010702012110448d00c505086031b40b122020202080d480700b840d9010305441c07152076002665802440301c030188040501c012a91040c02c1c107c47c040103258154240071440d4030390008009010854100e0b81007084240c2c8601e05035000c01c88201403903002d40140300300c0401d03c0c052541e12524003009941546008815140c94500040b0300038140104940010116070107a011340d0080c1c0341c201c2c110703281021a46080c40040001010340e030034508424a00043d1588a8040e20b420358029034060815110300340d44a40410005000c85a04101c0f074520200d01160f11950641c50304100210118640b420039000b041006000b40400c007a8a208020074405a1900e40c0301c03644554007005400c0007681d0020b100e003041140c503 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 917944505 1250 917943255 917943269
    0x60e0f0913020d35031b13121226040302070312080901051b0a1b1227030f080a0315080f25051002030903010207030324061e09 56
    0xd10202d0604c2140c13800407520b00b01c1c134046104107843d01080214001400d0144802d00802000068480780c0034180e403015103103141180900b07000c0041d030445003c941c00d800115004040f03016072400d001d0001e003c003034141828200200c4425030104081c6c03091a000c0300d4054864820b002003020113208100307480003141c0100c03810386a100085c0c0018925942540e000c2c00741d42c00c1601003110740c1508c00030070f45030500c0380d004586041e083d140c00740d8100d0360f207241320b402c111200d21070b9002241d0a407415180d000c0c80ca50b50307200703000c00c4440e0541410744103440c00364400c2c40c9220140000759559010f10390b050740001c800d03034444401c07074000c5001c1c20000c80e00480602000c2030004141034001a06a030400b04d40d030a40310341700c05100484219240080c1c8000d010588107a08200605100c0802c0807072a42600c10340b458044c80c0000b003826603104032000c600080d41c7d200c4007400c09050040700340004c0102212501700070703e0900002d000c5010183c070800d45070300040c000d081e09070050031680014041 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 917945755 1250 917944505 917944519
    0xe061b0702040f0212090f2802150301030507091b03020c0a0c140a0b0906030f10030b090c01110115140a0f0f140108011203080402131a0a060e0f091302 67
    0x140703c0052019410511280e4000030308880480e41c00e0501103920b2104401c810700034014501202c1101080955403510031980ca1044d480800240e04c540700d40f10044808020056030341c2d4950300c3c0103480d00d2050b9000c416002c6c94031603100c050366402d1030101c0700e25106107005a101d14024202074140200120010810000c00000044014807050344040300c07641100c424141a690f070f203101030207110354030701c1e254000c004200207031248500e60142d68029801c81d0002d444c7d01e0322941c4802d000d1034180e54203c00ca512044180a01d581d0043c680c14800480e0313402800a003688400825080f44140503060007014240000411521503c0390030b801440481d04078141c0c6a0741c0e5107105030307005013400794036032204200c242c018003940280800d0f8100d0f88400e25200b07000b05251803c545518010380b003283e2011000c401c03030b04d840f1203600500c40c485901c40406e90394415007034208602c540180c0d100300c0034403075000c082103540d0390b60160500c2c0c04030080c1c40249003903079004004c482d9452005c5e0001d500c000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 917947005 1250 917945755 917945771
    0xe1e0a080d0b0402071b0b070201120903020102121005030105130203060411031212060a0e0103052e02030a0b0f031c05070503090d0b1009020702101d04050c07060f0e061b070204 78
    0x3014901e042c4046c180c44000d00c50b031210300c20f03d41485000300190108001c01d80c1d110079440d040d44140c040c00d000b4400141088100044910380d01401c2d9a03128821200040a10080c5020302c941600f00c601e60100364400d1000b035021075113400e8024005080c503a40449540c0e03060b00c041c031151219900c4610055544c1058425025000b40c09a41550003251504004520401071070000c85c10b880e005801000d04482c1014411074244034146880750b03d00383c144c6a02d988491600145006401e8040080707800c0a02c00c0502048222840003144242c0c0aa001a0701880380d000d503280f00c8003510300e4000d54408a9060292540c8503800c150b0b0b0b04680906507160034003040c1006140200f80340001461030658800000050b40514400654046404000880c0c0c0364003442d0542d41c00a08101500f44803902c00000904407902183c9403080744200080c0c4c80e003007007407034894a9429040100100491840034403808d0360350300000c003100e0b511440e000300081600c0c480d00c03e56449540c014003d00c02c5031 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 917948255 1250 917947005 917947013
    0x1110f0706110703021c11041e050906151207030818150408030d0b0f0301060906050117100605160b0901060306061202090402040209061c0e1e0a080d0b040207 70
    0x20065100700c0e40091260b9800060711200801c1c4407040302e80042040b0035141d5500f90a5040161640d0200c0d1421940c0c980d0440320340f07a6010f41004511241800340030711008410b45402d40c1c1c4003d24803a6950441410454450183c6c041e842080301c0c20b41d07080a00401d05e610052400c00f8940000e4040603021407408400007001c500d00f45c1c440c00030b603070174034800c02500b6a048840c0a02d0013202c000b83c0081c0b103d00c015400c142c2c00b4540c8140024504040d250002c0042402c41d05907402804907242c84810902c410358000041d10f42440039003490484525200580f07940c031207401e00520080107000141f03003c0d1402580c04942085800c80c4004a0500303345000d280284190300c0110742a500305200042c0080c4105041c6503a20703005024802070365525800c200c000c0d4401400d031a03229005120100700e010300c1000c1c003030010a50205c00180000002819450212290304002822200d01f000a40e4200042600d9807041d40c80300140b615140c0c00481c1102901c0040701b004e82081c40401c650b4180 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 917949505 1250 917948255 917948263
    0xd0207170a1b0b0712020714101505090a0504060b030d02010606020d08040b3702040e0a060506041520060402100503060d1502091801080f010b0d0201030b01110f 71
    0x45140d22460aa9144404407090302c5410302c00140a19407000001041c2c14010301c000c42140340c1c591001403800c001d90703644900c04c881030015480e50b548640c1010f42c61525901c911300c0c1120a00d8141ea041900e00303c00616041c10042140000c42e48500c0840c040044035004050450001001e5860481100400900a025611440c0300521565640c050361901403181e450059400011303070085686c0d500c5060029100d07042c24480501d0402e80460070b00c869145a41100080310400581d0f90f519081130440e42c004003401503101d0350314220f000c00081d034550044034111200a5030400100080400542c2e2554900410700d00b0007480c1c0510001540022a42d90b01c102c1c0b003101c1d081c00c0b8100c0280103c40301e0104866040d0003881811501780410782c41080c10100e00d2003008094900702d82000403541000c4802072000d65030005000512020346e041c0044006200c408000700110100100080c564015810019060651721800c08100b40d2082d540701481401c03990880700000b054010703003599 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 917950755 1250 917949505 917949517
    0xd1506031403031e0606040905090c0303040f0f0914042411030601110d020d050702030709020406020a14030307021209040e0a03120e0c0a26060903041d19020d020717 73
    0x9004000e8107950b50313030901c81c500640d8060710b6281082c0c10300420380001c02000c2c0c0300007442c3c8201e0105198580e41040180301500440e9180c120417454481254041c5030075800101c2c002e81490102e84005a1a40b10654001e4006072015038030b400412621209240c4407903008491400e081c0c80d1801d5001660045004180a903640d85946101c180fa442d1160540c0c221400107030807650102e072020b807082003e040c0c40b034001170035149501d980e51503e00881e40242c0c08000544c000b0130303484085c004103841c18141b1003094400b95195107070a0344000e4440441503176001c21440b01003158042512107a000715045882602141c01c04149810068403120f4003001c04110181014120240b414000c100d40d075000c00064484162035040070325504200700110b145003000390062070310342054902009a14010725032038000e941e581d802d00c0ca60001c90f4560100d0454411030440500201141401c40c40341541b1040c2d10040e207030840c0c6c6030740300003a1061840240a181c10010f01c00303c0d0f400c1d41001020 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 917952005 1250 917950755 917950771
    0x1404120516120f0f1e0f0e0402161e050c0402160501020a170603010204030f0f0201020f0a0c03030201150e060d0203070801090c091b02030d0209030c12011a040b0d150603140303 78
    0x100500e540c11085894030858843c207034190280d4401840c40e0f071b00502c0544200c1e107590804400c2c4407840030100b41240c0002e82d0a0f454200c40403904070510100311840c042204c800c0c2007095a21815480d0345646081d1030315424012540060000d1183d007003001c1c059201a4824025541c4080290b4001e0011400c03224100200794140d0201d0083d107014802c441c02c490b44114201c14605164460100c101200b00e02030381036001300480312110000902c0082c3c55580300712542003001d8114100242140e4600c640c420303804080c040280103c505907850030340e000f0801c98245255045920101e03041103807a0f440800319608044071a8104242e030280c1c0c50607500c06010410101181d01e000030480440171072030b280543c20801044010304620340042458010260864103444004130104803100295011060280d545000c481c6007000c048031b200c0c0f00341c1411907060024400260004d24590700840d0010403010303c4244051002d001074004000940d00062013007054503042c14000e4881d8400c0341c01030 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 917953255 1250 917952005 917952017
    0x28061b020f011a040203060d0f08071103160b1605121c060506070201080408091309060b0411090409050106081c12061d09030702100f031404120516120f 67
    0x250030500148501d0b40b2a860f100b011694101d54041480001d60001e4165a0010541002400411461201000d02d6071056144640d5030301142003100318031900d040f08a01c030750000745030880d070741707206603007201c16200050074503640d80d00e82d1404084d28044142000b810383c0203078091041ca503a0310390041d1406c0c4e1841076030014040c29160f45881159082d0058a5210105110304000365102d480034582c0144200003240c81c21107124001800413a90301002c50300da40c0c8450f44182000340d24026540244019a0306124014480e01020301900909402500131035036040381c038007400000d40000d4000c107120000c1e00c800311040000020b8540d120101c450100740629084002804203204000460f40c0040d4250000c01e44a09240c1241071b001e8135032602ca200c240200740141c4ea9210b41c240d401412a22400313480011040082d051300c908004505d030324440c403020400840d0143c40c00c0070100d1380c83c1c58190340d02d00e00442d8403145d5903484000900907003440440c507101c254106881c008403150744d440798 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 917954505 1250 917953255 917953273
    0xc04090605090d09080d030b01050705190c08060609011e03020a08030409140f07050a030230010909030c08070c0b04060309060f05041a19020c011e0c0228061b02 71
    0x1d0b02c80844c207105080c040d034060000400c04501c42d43c0461071000c070514003d4a090340603120301d8606195404a0152044134a680741704005c1000100c10040030010040c005501d00b00c0300203040024144202c3c00610000c98050229901e19070092025690041c60900b1450320f80b400f0300d039030b0740090007600c56407482e04803091001c44403110350b10b10a08402946c1506a40d5101c000c54243d048405081d040c1a02444100c03200d841d1212034100c0c55107112260300c2c41c0b41d00b14000701d85695069105184261803c2c4860307011a60000c00038441c1504040910780d5642240740c4102039030b099601048241d500428085030869140d00610016409207209225000041c0d550714115081a5001010708504407542107007200190421580b14040070f1a20090030501c484850a03030384106014800c41c1d568684040b0140060700c8401d11584200b44104071506c1c81d150080c3d030720042d000d030000310310000c440c8100740710503240440b0703440c00c0c1d000b00203001120303414000c03811084405c0c1009015000d04022 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 917955755 1250 917954505 917954507
    0x6051c05010b0d0c0b0906190c15020f0702060c03120106050c0d0f0f0f023408010c08040b15040c1d10080a0b030f0f030415080405030d0b030c04090605090d 69
    0xd0200d003d500407040c000814649801c00300581c0c040104660403070f0040c02004020030003452034644d480e4294680f04500c808514001d81402890803402004620510101ca0340580b084150341c0c03400d60503226a591039020340b28451840c0214244510001c0d101d5001081d40b503801406456034800c0c01081381c0c0300003181d00d4152802000c40c200040020340c0703010007490321480344814022009050041d0361855008610310070407802e00314480e01269400c100c841c4045058849290000c10450000b0032078401c02910040c215a8051710141514403c0c1020030a03440241e181013040d003000400400040f100c01e40007030035450003000c54413200800d07940418050f0402013010001264540d50314107255a403040c0030002001c1d0300c1503007034151040369003180039070408000181c0400d101400031902c0c0ca1a0924580c0c520361140310a004000c3c0650910000410000132388031060750446011450b1030f00c00c00403c1c0741a80131900345d039229050000c603205000160f07001078001c000c2c46060340e0080e094520 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 917957005 1250 917955755 917955769
    0x20301141c02030d0309081e0a0f020114070e0315010f0510030912032c0604050f24190513060b01020a0803060f06070c0603060807090e0607080a06051c05010b 70
    0x14001c0d416402c001300c140b0710544030740e010300b00c090b04c0745d1103c074142a098107100f1104010611001c00350075000807011001034201c90701c1e0010045510007407000864401201c003043c6405000d000a00c200e081030100140d0f01070014880c0d10f01c0d03003031145076150794070360740002e4208152280074040c0c009002001c8003144240644070120790042e00c214011a018242100280342c112400c0300a01611104c03200c84140403076102011b48175081c0200381c50304147c2405410000142230210381540001c494405000c103111035581c0708649064107400c80c0e80c50241d00500c941d84d6000c503e60403031400041110729a494450903a545000e8501000301022000040e03076203c059407000b4155510030700005003d803030291001c0c481c10002602d00390829040b95103000d2841a2504280b0210f03440785000d0200b010b0800c45240103107030300d46d0244010802c8511154039068040c068108000a01c80000c2600c041074101000420307000d02050255601c50b00c9442518401b01401c0b1081d500b0301b0b1610000e0f00d800a = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 917958255 1250 917957005 917957059
    0x4020f01050c03070b04110a08060405010f0603050607032c0a0b01092f0405030d08040501050f0103030c060e210408120c120a02240711010c140a05090402030114 71
    0xb001140350181d552244400d4000040003265003070311082809400751a81c07840320005000d64402003001c1e0505140440c207681c1c03d2201500201e03c3d204003040441c0c00012480d4200d036030f6080000e26011850320b403004450b101c3d04004007180c5000ca0039102da00000440940c890b005082015447c0d80303500c01801900d2044d040040d5048045442c2100034518065580d00700450301001c41c9416950004242491300598400b00804c1c4840308000611100713001c0c4c158091540f040750300d10780d81140e602900f81001860041c2006d540c5a02c19481d28508010b2034070025810103202007442d01c80080012183c3c41030003821800d009003950b0340c0028500c10b069524060445019000e1b500c0e01401060301d5820000c208401c40c1725640085004014840750352030307200311540d02020f161038200c0c409883d95142d000304140c1685858205288264840e8003480140026816556661f0b0784000c03c54441c02901041075001d4400000025a1544802c00104e002c400391407100d4088403060700606080b00c10 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 917959505 1250 917958255 917958277
    0x6180d0e0108070f020a150e0d0e0607200a0308040807092703210c0f1d0108090307211115060f13140615130e280504020f0105 56
    0x400803410f4140200011080e15035540304643c03545100c0d850340d50011440003500c1d8402a610a600c01015009020b8100c6070500b074245100303000c41c2640401e00500c40c0100180200250a80040c01c2001a4604075a517040040108124076140c3c20408902e60042c0f044800b50301c61148005507400d458098034544590341c2031403902c0038001c1d290b03900508846601c1102040030812084840c00004901c5003c42050080001801c0703c214001420100e00d1040c1d03078081c00b5804000300440003070150a00350a100a03e07004850f62607200c0301d0762840c0290035008000d880c400002889861b100401210580075a58130701d40c0c2c00209428040c1c54800d00492224850181c80020320f99041222100005042c0640309402c11148090110110340b8020542e00040c0309080c240207144c580f2140665162a0309038445180045800003150b1001023845043c235480c0c01a400a00c0784060307140640150f800804401e140c6810105001e4000d00741140c08034030642014000c00c00c00d510403016240c0340251 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 917960755 1250 917959505 917959517
    0x1b0c03020405040314032d060f150f0a0e09010501171807030611210c07030c0f020a06020f0d02070b04122303090f0d0f121106180d0e01 60
    0x85400303200250000800503405e219078040c1e440b805994001c0214458102c580e4500c40300003d10007112002c2c5400b84480c408102901c00340b2000c1e0f138074000b00f190f0180c41103406a14040400e5181d101301d0240301c64100c1c030940080b408010150300034181104130b860440707080e0026078030b442c019529882c0700c880c5969411010000154003541c5e40b899401410000f200f1070342c0c466900e544480944400c0030551150802c0030840c5212000c022543c0611442e44c400030307103054504800c074050075020f080001f40c108030541c03c00e40b0070b20846032103660304c042d001352108400b2030b2a004041e5980c0281c408600380ca01c41d424020048520100381d40003a1650407162618052500b011480d020744e0341c030000e40e2441c80703030009807442040c802c035150b0151003001c1c05152241c0403481000000251910712500416070400d07400001207079030b40181100d0794440e1100040642c489001c547c81080e0b404103600e1032242600b848482600300a031030411f01020000c440004088c882e0450705142250300c42d03408568 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 917962005 1250 917960755 917960759
    0x30d14090307030c14071a12060f100311071a090616090e07050d0501080601050a1d0f070c05010509060a05071b14101d2103040b060a12121b0c 63
    0x2100c0009005104036a1040302c6181e900c030504515200f4060081f00c07103100f030010b540c4100200034025141d00034011508130404c0060240403810f1900c100d070954040542c0c03111220822034100042e541b00942200e402520045007040380c00d0540c0c025a13491101c9e02c0340600144a513810002d1881d80291107070355940d4480d1500d0044490003801030450001d0000910181c2050b156502c035460003410740342c0003882d05501d020700703004186c1c4281d0401c3c00e450700321400c261468194509155007028420391481000c0da03900ba4211840341030010001d1895081000303000301d03c44002200b80c01094952000c00403a20788400603181c40a161901d001c00242425030407011420f8405000f1603c2c036460256581040814000342c1240c160502c00b10b950551207214580e02c2c0e03001c000220585d00362100810040000c642c41040d01c1c00001c00050844c954240001c80c113844100605004105070420380000408920f05802c0d858069500d07000080d5a60810b20322588485603035955a0b03802c103443c0c40f2854 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 917963255 1250 917962005 917962013
    0x210403060c12050a06030201030b03030c0715110d02010605041d19080f0a200721051204030b0609150f0d06020903060c04170c1e0102070503030d14090307030c 70
    0x69060341070510076026040c0c0800c00e1a03001d1540314075810b0303200141c1203096100241c1201d1003071000d94001e178414071032021110f0f40010076800f070f01e5880c1021400c295400d40101c5040074040a4075845000d281803240c28076405401c00029140121810300c54090324140070114411840d44400d0668800c6111040a48001714490341e454010a8400d141140030b10324018a940803030799000c005046204003c90b558443c601e1080c010b940f1030050030301c82c3d1803c0c0c680005101241d80380e2554020303410307401c01000000c0000c14240740e0240b10150301c0d16500d081c001c0a1280451303d99000350706503000150b804180c5548046070b40340040804a851103468148640b40b01c07280003c9400740d908000600c001d680030045c42c1d1144400200041d62a41032055640110420301907100041d0310000c185030705903031005c0031082c1c46403004103640e00304804100101c0ca002c400740c2c803040d00340c000002d6032504101c0c20f0708404100000b0a01e040300d50f444c2d50015558920034a031019001654100c5010001 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 917964505 1250 917963255 917963261
    0x2030c0f07032f0105010801050402091b12070e0f0a031212140408070212010c3e0304360b0a030804090504150902010e040e1e0a030221040306 63
    0xc42c0c0030389400c0d0340d040800b02280d0040c1c6007501842d02c481c0200d0240d050b0500090007400d0140a0450080c490340c101a40451080340c4054005c00c1807034503404010102e68048016680203084031141050309040644c2e02a01081c5044000c81c020041255041c1440c1880c030100c3d07049036030008103110100311540c0c04a4028910308142078199845610705540c501c1d801000ca0301a0b17016103086642c895003441004403054844000e60715a13418658448122034103c140c001d02000b203007103610559a100000038800d1001180040e544204542c5030003c0c442d000405030064903405000c0c60b9030411b1018400c1506038103040300705103040302c030b48912044d024143c0115009a8004d081900750310f0322640c07000d00c1d68006030030410009075103d04001c11302040f03030002030341d54240031001c0003150490307000207200510000d40785c1d000ba81c0703912140c01c591038108a400103081440301c0101640f440d05c8805621101d071390006078010700c0307003550404210010050b0300074000c101164923880e16217550b88000113 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 917965755 1250 917964505 917964517
    0xa1d1c080a11040f08060f01030c0501050715050a0e0d1404052803080d05010b040e07030e0304080d0806031005060907030e03090405150a060f171305030a08010f080102030c0f 77
    0x1c0c640b03407103086281d9079800c4054800b5003c0600098004d80c2071442c0b203450080300500e9003134842001001040820b585051060a4580c00e00e040c55485101e07060014154070070449604943d85000b042040412560f4489004481d400b016650b80c0c0e5480e8104071100160410940d2103810304100401903031407c23040b2032441070002c090700403079000e061040c140d00383d0050b0b03c00d50307980c08001070070b4030b46102c0b038882d65015001d90401941031a080400b0140402070051812062540d42c244c4800403000400c10b850081118400f16017200310303690801044181c0641d00c0d540a0721803d40d070b010000c2c0711401828800e480151401d00e10707994500c411405000c420032201303000e0200b04010340302e0341c40d1405028400c0c07110006800128507030105200080203164841c0b001c001819148000307040d4420700201411042c1c01040c007540c1c0714800740c0000c400c00c4500003081c03840005216454250441c1d5101e0480341000980c441c13503603542c07203ca42030b840100c40c40700035420100882c40b81c00c42d1070700203418 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 917967005 1250 917965755 917965771
    0x90608061e1203190216030b040b0612010e252d030503181c0b010b0c0c06030f061903050307030c0515070201060f050303120a020c030d050a1d1c08 65
    0x44080c2c60940c5070381564803034071000e008481d120759210380c16901080440d641c0c0d0840c4100000b91491034845c064a680b01500c02804d640701c0c2c07004500b4075603408045001341d11448000300050080044419a40d150000960304000584440305c9100315403030034501c00b280c0e61850340700c00008000f8540c0340040c0901444c0c0d842130f41c5150700400440c10400107452028498540035811010200c200308040000b20103403804004000c080da00040c0500c8884cac0c0c1141c03400c01100e40c591882170300c0c0d5030a01c0442070f0308030b8104001000300010a99100c0321030f40200801d451076124910000d08030b0044880750300026000703a10402100002920414040c88124043d40594070010f900e900000041c510685040c2e0041c0c0d100e0300240500800546480c005043c210021450980040d50200005000901021030310b5400300b40c81000f400e00f4001ca0780e03070140f0380702e00b08407900e406102d120080482d1403008203106a50380480d600507000049503e90402c1c40c03202c0c0d03000ca040d000c0045036036140080030030b0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 917968255 1250 917967005 917967019
    0x2010e0607080c0618062806121101031b0c1502040815191a0423070c170c10330306051605041202042a090608061e 51
    0x4400b00c2c0110025205490086000e02000e0038544159890314400003d0540107401484c21f00041c0c600074004081038900498680300c00c00d01e10051031000f01100d602c040035010304409038600300075403401c40800b108000d0320304200380103003104c000070307941141ca031690701240d8207480844c081900201e044994402d4080d01600c0c0c2030704e03541c496050550a010b4a45251401c1060101035903c000036941c0c0348402480400c1200ca00e62820102d0021015031103000d43e80d0382d403040380100032003040ca0301a02c8c030310300b18150507081c0f42200230b0885408210a0f04e0391041010800400340b5100d00319403141032080c0c0200070211002c01014000d066005004441c1d040c04020303501c0080300e4522008080c52110a4000e4031846c508203007064950003020388445104d00584001569004070541c0c040c0c800d00040c101c04100e651001c1001001804480144586e103000703044072500d644286030b04103403425640d1f2590f0315500c1c2419243e0500545031142c0c0414070a01101d00b2050020860b0758640c0014240c0b = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 917969505 1250 917968255 917968267
    0x909040609080715090308150a06050904150b0d0f050c0f0903070f062105010806130c05060d020406030b030d05032809050304061706010203030109050c09030f030d0605120a02010e06 80
    0x310a00007840503800d800c135910f8401d101c05042d08200110785c0800d8040034800f0391900c000005842019502070781003840400b003550700745034880b9403000343c0c00c100e26a00714185540394250320199404c07800250041d54102402c5084100490245034010844040c50707d04000c2c050b8101081c50b003103803d8840d0103100720382c4005803a040c0c009024004042e1500c0300d002c10921400100c0940140f4440080000e040030700401c40c500d00051450f0780906a0921411003403550721b1708200040c2030740d000a80c000300104a43c03890740b00ba6070007001162459101003000318241d2007815110720344c1031220b50124800384006688003000303207410300d42d040c4a186400844041c13444000c003122180c4a054840b580082800d005d45500641c0700502c2041c01c80a10b05c5038a04080000d50f070b403105003c0c1d50030b0552224049070050300c8580c2611b1400360018103440114030142091540c0380c21020b01102c403242003401c0040c0c10704106803520003112005028003401e041e550015030b4028407944000b5000b000412030 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 917970755 1250 917969505 917969513
    0x105151e091f12140f041209031209060306080f0606060a0903050304030602070b010803040e2d09100b042f040f03120e0111030a03150b0714070b09090406090807 71
    0x1404602d1515501d03904038080e2510305070011101d610340b00148461080b0140600d0b04103c0030181e60003031b48001c5801c45200020340440d60f00c0030076880200441040e00c3d001c41240e40000f000310a171201c3c0c0e5001c002e095a690700c0542c1d6800c1e00c007583c602c1900558046409410208000c0c4504a120b041c801616680d90791894556070050380709540d22a40403e451041040300f4158900400c190340045007040d04001079038127151805018042c60201612182c0441c1c0042c002d601740b07401c1000c080000a14018801503155404099005000361800c950a0018a06403143c0a8031142c0324829011425903418403401c104140b036983c841452060000040c440e044a0840d03025503c12100340c1d0f5201c2e06150083c20380707151040110b05008180c5800c0c410440c0000c20784080800178540400c1d62014001e64603a080d03200d811041c1000c80c0003545509010380d2031600041d01c1062801c841c1c1441d03803610841d4044c0185051a94040c2401e404100441e80c6030b00841400c90190829034a00700d21035131 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 917972005 1250 917970755 917970799
    0xd030818030f0a0302210405030f0702130603150e1605061b07030515100b0906030a0e1207030207051207060f020106052e0e03030d090303090b0901050105151e09 71
    0x2165001a400180d1540c80001c54000308907905440c070306c00c8815081c0b594441d03849000303d4882440104000ca00042035585d8542c03245400340f0407440800805440e405d10000d01240d201402201d0307401c02000010300c83c400a014021001c0004980c03a50b5801c0108202859018020140300401c0c03d0300c04c80340c8194103110b0fa0009500c02d000410360692039014410344920300801c2c1841d40c40c01550100100061941115214802128615640d07501c80416400802c00102c0c106401c1c0b08207503000c1070f44c07401c10006202c640c0c020303021a14540d565000300840c00d4021207410801c2d400c02c0304100101401409400d18041d041d000124031507464801244000c0d1101d42ca1704481d410b004104482d44607a503994a810f4819450401d06401ea940080b0b81c3d03034410a00d0441c4255610307102d074818584242d005e0074800740d00c40e50310300b2036060615280c2c0c041e0600b07000b198072816100c20413020481c240400c40d501d02c0c5000e2000d11202078540d000e1552900301c1c810854010101c034001c01c00800b040a = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 917973255 1250 917972005 917972017
    0x30c09090e0a0201110c09061314010308131a0d0e19320a030e030c0d0507050f011b031d060307090e090a0b0109021b03030903180d030818030f 63
    0x110091040c0b50b85800010040082200080590f401017103015840d03488120302d03690700110564030b4880040008805d10020142e004845482110070320021040010407002031124034a06444101641d480e400d035040707141052003000406201c100700d0340d240d800d6140c0001000c0140d1340c042c2c400b458480a803042504248000031501420311009940100d01c440311400b001c2190000c4855460300000320195443e100848083c0034040c807015002d0003a54100040da8100c200940310442c0014036181640e9200658040c06200d80750800054600b541b04442d00e40d07522140d5040082108031944044ea6164100111080780100944000c41d00c0e0701c4241c0154000c20075070b030340c0f154860b28000d02c122091401130510407141e04851052000304404405960545000000060345c2d10340c450543c1ca940d080182d801c100714040481000010134011000d014005502c030742c0003074035810880410104104100e401404a44a00041413940c5400740f451080c1584900480e8902041280d10f5000c0390440 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 917974505 1250 917973255 917973281
    0x40c0b0705060a1b0f0c06020405040609091707031d13090f0c050906060a110304080a05030d0507051215040902030609010606090b0a051902030f180405131101030c0909 74
    0x240082c0048121140315107520050000c004295010b103c05000b081d03200440161720070860580112400d02c401541110010240148200040366031098000c0c01b0700180340040d02c0b0100441c3c4a03001c3c0c10b01c3c0e44112601780d585595440c0e0815518410100c8092218081c10340048113840f0074890000c0794801c9940003805804d00d260200503503d0b04952031300d8581c0283d03000d0b59040301807040c6612142c041d54102c0103e820840001030703a148010b4036601503648805000c0c03044000500610074040028105500d541c8070901c2140d0b1030110a81c0d5910444030030011120b42a4001500407004c02009080c0c00300c002c0002c12011455000a4074011041d158814565580c0004110840c0c0084d0391324000c0145103605c4e070408035040c00292a602030320541c000100707402ca1000d10500e10910880340c41e0b88103000010340f140782413130300c01c100120f048440f0760146240c040801d5040c8030001d500040a9800803c3d03058240d886001140504850041c24040c0b0540420110307507a4494000c0780300c05001 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 917975755 1250 917974505 917974513
    0x1b0a021e0a270e01023a2306030a05031804090b2d06061801030213090e1921020a06020307030f0b120705060d06080307063806030c041e031b05010203090405040c0b0705 74
    0x2111f900131076210000b0b041544240c1c084080c0e040041c102000352034094501d9401035155405080201d0090315403400c008000d002440e0410074101e10300d4084650103000740b031805441142c07040c640d0035081070507290a648141c0a120428803655207003501100c298042c58054101960605d600c81441102c0d04414000c9803180e00100c0e042c8410000384150406860711401034a946484410003840040c0405112101c80c10000d030002c8c0c002c10003002d0310380d80f0240455881c902000e00074000c0511107080b04046d800c0642c2d9586a1800180c0e00c071407034041e50041d0501d14540300401189030f204503881e5200f2600d4071400501a1800d0010384006805003a01090102e00c00010480a8401d90103c00d10000045011002c01a0708280b100240206503034542e40d80d11840446103440c004c507440122084420007481140000707500410003264460040d903030034490390b12114040380f0194056030780140d1040c4a0440140f80a4002541050090030b800c001c141e02e80020b088203500200d019500c544c0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 917977005 1250 917975755 917975801
    0x90510180b010e030309011b020a050603040507050306060a0608070f030b060c01140105060319020a0c0f050a02190b0906130509010b1b0a021e0a270e01023a 69
    0x10300410f01400204044010b586020914030010b451035102c1041e1080300500241c6140031074031010030f901c0141c0b03c0105401e44038580f42c070304259103100754040c140c002c0c015680442c1003810005594000e071240341d01e81c0511640c0b000c001302c446184000c41d18040580740e210584d11070b21a40020658907081c0800840d418000c11079048003030f00b040e03002900504040003080b080c0c004c1809034000c11654508050313544c5440d210211001e42c290180500071354101c0b1160000c1104c00941480150301c2960300034008101c2c420b1802c1e441c2c00e54803c0e0034054004002001061404030020582c9004440c442c510b111b8907100882e051880076040f0750301092000401072905211000c06034030f607a5242c002445c5d134502a80c085054204032943e10385035100d0322003089000e80e0341c07580380318040c1482d280800884000303149403241c80410b098400550317520b0040c5c0805d8104040c001c45125510050340041d84030b40c1002c214104005000110001081d111240024a6814025401c95216180031900c1d065 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 917978255 1250 917977005 917977007
    0x5060f0c161a03150414040b13020a171507110601080f030406120f0c0302031b03041e03050c0304080106051f0f080c21070207050910090510180b01 65
    0x9041007012aa11032401c90100811203000c02402c842c42c4010395207580701c3d1220007250640c14011008541e11a0070122001c80c07806100c215144218051307610f10030181c07950528800c00544800d40650040b0185400b402810034228241d2888400142111206022040c0c00c5040d401e09680c0742000605007151025000030802903280544551405080e45410001c03013295240300303620400c003e021444401c041e13a2061640a09000c440300201840f500e40a101c00600030b5104076800c0402d10031280020b8010300444095070320469005102080c443c1003812100351804080c4030882c00c20100708500801c00509002900003001c152002090f0305042c4020481d0350440d4101c03100ca0321950951070500d2503481010800d2056581c10001100e88410100303400030f20600e0220a0020003414445800c1c8000c0a00c0321302c00d501c9070342900d141d85e03102d03420064281000d45420015042c2d5007003e0059800300e901854001c048292001c60850740c03400d180e1a001c03205554042c15658809082142d5 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 917979505 1250 917978255 917978263
    0xa03050a170c1207530d050a0b0102070b070b1009021209191a06030a02210706050a27121b140102060f09010f0c020c03010f0507021216061e1505090a0903020705060f0c 74
    0x9c80800d00180c560f00342000d41250441c0105007003d03142085c0c40d0081407034414080040005402000015551604409601242c100041d90058803520502c010680c4908000074003c04581d0b0220789055980c440c1205104007071801b5203141c1d41401030840040c010303502c0c200c50070500d540d0310380003440e0001d010114500780301c090340c010818410200503615080380d2007810300c03e072075500a19001381014003021200b081d5400350026182001850714400604c904140c6140464442a0180075065102c1010701c1c0070344c50301002140540e10140210f8991038042141d144d12444441c00001c01201801100054591241040000d600001d0004245090038091880d52003643c1c2e00a000508018000941d9019802000500700d4004030303030b81c082242c800c4040222190400c10521a8444079095031035040e403040b001000c2c0d186030681d902d11003c100e80c041d000b00c0740000d181c4002a5200908100908001d040407000c5000e0400081404e5542c1c070050194059005286910380e8101d1541030301d0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 917980755 1250 917979505 917979521
    0x1b010c0206060a06030c27050901290a17010906050301151a0705010908220e07080c370306050a03050a170c1207530d050a 54
    0x841d000340c8108034880d03c5042070042120030500d000201c02444074070883c0c1d041d42140002250200e01032a12a0740e42544107054251801242c42108a0340e2b04c001c3c602c540e0b405003191107841403001e0340e907004410b42100501700c0c3c2d4602c1c0c02c114028141100d04400d80c0e030300903040383c10a80c1d07540c4c0013400a030400340b044001d00e6074101040406141050b510b000491540c001c0302580010006000b4200300080d0030507140a60701200c5140c40700b12070000392410032203000114011051725400000c100000400c03050161006403601d51154072100c45104083d88030000044140c03086070000544410b2480000c800801c1c20400509050700d01a40102514200d40c880741c86502039400034000316101003030203080240c0c4800c0818801c4030364411409030340181c2165907154040e00ba081d1845024100090910034416a0b102221503150b40803002038900c107280040d8180c01107091803640641c11040300701800000d054100055464540901540c1d00c19101d00307194540303405c20b01c4001601c901071b40070 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 917982005 1250 917980755 917980757
    0x30207030e0402120105100e041a0108160e090402060c19060501090c0203031503070302031615030e030a1404150518030c1503071803050d08010e090d030509010b061b010c 75
    0x21130b1409100f02c41c00d40103c10300800e071042c0345062101d4002c034000c1e80440ca1044018000388034040c080e03d41c0e583d141034000d10403404200c030900096a02c0e400e9152000041c2d0a949800107807110700d0040c0910220018000ca030840c5040240101c0c1501c00c1169541000340c141c0d4070350780c040c940e00d0048242c40040c1d0280320310078104a1098107040e000f00680794030003a00b107600c034581002c003c0041c4c900702580d80043c2d00341c05948034550307a010301e10489000f5039243c000070300c03e60300e5450422421951056a000704940080c0070901c0305a21030b00160101c452a01407440c2015115030030403001000d4488600c01080000980c840041400028000754080441c050104011102c0224101080e200700c815086100003002900711030080a90415002031204810001500d0740ba21942d00c508848890300071406242c00002c40030400f180d07c0e4070070000380c2c0c00f0303002003001e04005401403d00a0a000000d54941c03d1401c0d10f80c8850010345184c050494140c05110b6500b0340d89400c44004001a074 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 917983255 1250 917982005 917982007
    0x501081b0a06211d03041a0a090522020324090405070b0304060f0c050903011503050712030905060c070e0f060a050f040b1f2601140d0c06030207030e0402 68
    0x25580080d070382c0d503040100c3d9184280d10407004071600014540d8104284805900d040d00c81e82501002001d04165aa400300414003400c4100e001215401012810b000041001c402400242064400c00301e031098812501c20000d108441c164041c0d0300100c80c1c0c000034140c2020b07281d0f0b2142c031100c04002201816545c03807105007403c0e1251038861400b070040d80380c00d440000c045420000580d005034120340d20100200030494000900402a900006c2d40600c207600b0400d01c0b0609401c110011303400c9030780c000d00501400b03103403003807005010030142e5055080c01800100014141c440100a224402c07015000c3c02986083c03084407031003100060b201c54010b500080802c1559121040840709981e412219000319440c0200010050f00c0700038151b98001d50b200140c007070b00215403809850443c03c292600200c45040c46014440e180400c141c2c150700701181001000203d0382c0d211081d440032005403031151600c200b0f071030300c0c62907080541c86040042d40c0001c041080c140c0c004e45603030300032104075419 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 917984505 1250 917983255 917983259
    0x4090b041214041d04030203074803020103050a02090a120201020706020d050f0d020d0c030e0706050a17060d0506010e090c2706010302042102030c0603161404090501081b0a 76
    0x38030518032494800c4c07030f0666401000c1400d060003001034170401039201140e0f81c00b42d080c0110391030b400038002240d100210004140c00c005045070f039600a001030032492041001038074680045010704000740c0044119503003000005001c0d02c1d0782013003e000c0c018004465000ca2500d05c002480e1600a5105000b15000203141c0119641d100e41114020264401c1c0c041d2a1120348011400a01c18520038a83c02440d02c0103080e03446405400030101403800790195085e0796035030311090700c40d0722a0030b0505c00024000c0080a420881c00b40f8607030b0300118041e10119100c151a5142c80c504142070300005951584078041000c0f2000411620248490030f07982601c401001d0709610507811000300724400302c0030302c1600055099109074140d40050002001c03102075402c03030b0741c41d03802001002401a80179006485503056641008021240902c0036000c00413465006541e040394030403503030303414100342c0c1404100000c0d15110038064103028064800c090031490f46c1c41c011809a004800030003500880e501001 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 917985611 1106 917984505 917984519
    0x40f11011e0e12012d0e190507080703030807300f060f0f170312180610030507090f0603051204030b100308071104090b04121404 57
    0x108554058011100f58240d400825494408810304403140c00080030b01c92400b044040c5007003000404030840a081030a021186602d1110008075242d014240141400054001c080701c0c1c3c02010032078039641d0701401100000705100305200171011681070803070b1080f1108115401d9440d00840da0071002c000ca07801094030212a400745494418041540761070030303142c9001c3c0c0d26000007854201c0c0c9130904001c0c6402002c0e810000601080c4030b40800d50709a000d099000b0800700c100e000403110b12000301c030700d41040100310b68110b92080c9020800b044010a9020076108481800309801c1c40d030026100c06041c484d0b00040c99807080d580720b903002c1020300340070307100703891080e1026401a21244d4060f0104640d80c000980400e804005440004003584080d002d0031a001d400856205030b40d440b00e0080d07180841f010359131442c013010400c1c8080e90186540c00905d114842c050b0a06090000b = true := by decide +kernel

theorem cover : BRFrame.Cov 917805755 917985611 := by
  have h0 := BRFrame.cov_init 917805755
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917805755 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 917805755 ≤ n) (h2 : n < 917985611) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
